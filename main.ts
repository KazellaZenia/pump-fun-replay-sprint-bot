// Pump.fun replay bot: confirmed-runner momentum only.
//
// Idea, in one paragraph: almost every fresh pump.fun coin dumps within minutes, so this bot
// never touches young coins. It only trades coins that survived at least ~12 minutes, have real
// SOL reserves of 5-85, and have a real crowd behind them. One way in: a runner — the price
// rose at least 12% over about a minute on broad buying (6+ buys, 6+ distinct buyers, 4+ SOL
// net inflow) with accelerating inflow, still near its window high. Positions start small,
// scale into strength only, and leave fast on a tight 3% stop, a 5% trailing stop, fading flow,
// or a 300-slot time limit. A dip-reversion entry was tested on the kit's dev data and lost
// money under every exit setting, so it is deliberately NOT here. Tiny probe round trips keep
// the entry above the 20-coin guardrail when the main signal goes quiet. Everything is
// deterministic: no clock, no randomness, maps iterated in insertion order only.
//
// hello / batch / orders / slot: the harness speaks agent-fun/replay/v2; this file answers one
// batch at a time with the orders decided on that slot.

import { runBot, LAMPORTS_PER_SOL, type Batch, type BotState, type OrderInput, type Pubkey } from './vendor/makefun-bot.ts';

const LAM = 1e9; // lamports per SOL, as a plain number for decision math
const FEE_RATE = 0.0125; // curve fee (protocol + creator) charged on each side
const SELL_SLIP = 10_000;

// --------------------------------------------------------------------------- tunables
// All round numbers, deliberately conservative: the final window is unseen data, so the bot
// must win on shape (established coins, confirmed flow, fast exits), not on a tuned constant.

const MOM = {
  ageMin: 3600, // slots a coin must have lived before we touch it (~13 min)
  tradesMin: 40, // trades seen on the coin before we touch it
  window: 300, // entry lookback, slots (~64 s)
  minNetSol: 4, // net SOL inflow over the window
  minBuys: 6, // buy trades in the window
  minBuyers: 6, // distinct buyers in the window
  minUp: 0.12, // price rise over the window, at least
  maxUp: 0.8, // ... and at most (skip vertical spikes)
  nearHigh: 0.95, // price now vs window high
  accel: 0.8, // newer-half net inflow vs older-half net inflow
  maxBuyerShare: 0.5, // no single wallet may dominate the window's buying
  rqMin: 5, // real SOL reserves at entry, at least
  rqMax: 85, // ... and at most (near completion)
  initialSol: 0.05, // first buy
  addSol: 0.05, // each scale-in buy
  stakeSol: 0.25, // most SOL ever put into one runner
  addStep: 0.03, // price must be this far above the last buy to add
  stopLoss: 0.04, // exit when value falls this far under cost (value is fee-loaded: a 4% value stop is roughly a 1.5% price stop)
  trail: 0.05, // trailing stop off the peak value
  trailArm: 0.02, // ... armed once the peak reached cost * (1 + this)
  maxHold: 300, // exit after this many slots held ...
  holdIfUp: 0.05, // ... unless the position is up at least this much
  fadeWindow: 60, // exit when net flow over this window falls below ...
  fadeNetSol: -0.5,
} as const;

const GLOBAL = {
  maxMain: 4, // main positions at once; the 5th slot is kept for probes
  maxExposureSol: 6, // most SOL at cost across all positions
  cooldown: 200, // slots to wait after an exit before re-entering the same coin
  maxEntries: 3, // most entries per coin over the whole run
  minBuySol: 0.02, // smallest buy worth sending (guardrail needs 0.01 SOL trips)
  buySlipBps: 500, // reject a buy whose fill price ran more than 5% past the decision price
  probeSol: 0.02, // probe round-trip size
  maxProbes: 1, // probe positions open at once
  targetCoins: 25, // guardrail pacing targets
  targetFills: 200,
  paceSecs: 21600, // pace reaches 1 after this many seconds of block time
} as const;

// --------------------------------------------------------------------------- per-coin tape

interface TapeTrade {
  slot: number;
  buy: boolean;
  sol: number;
  user: string;
  price: number; // virtual quote per virtual token, SOL per token
}

interface Tape {
  created: number | null;
  trades: TapeTrade[];
  seen: number; // trades ever seen on this coin
  entries: number;
  lastExit: number;
}

interface OpenPos {
  opened: number;
  peakValue: number; // best close value seen, SOL
  invested: number; // SOL sent in buys (fees included)
  lastAddPrice: number;
  filled: boolean;
  exiting: boolean;
}

const tapes = new Map<Pubkey, Tape>();
const open = new Map<Pubkey, OpenPos>();
const probes = new Map<Pubkey, boolean>(); // false = buying, true = bought, sell pending
let myFills = 0;
const myCoins = new Set<Pubkey>();
let firstBlockTime: number | null = null;
let lastBlockTime: number | null = null;

function tapeOf(mint: Pubkey): Tape {
  let t = tapes.get(mint);
  if (t === undefined) {
    t = { created: null, trades: [], seen: 0, entries: 0, lastExit: -1e12 };
    tapes.set(mint, t);
  }
  return t;
}

/** Net recorded SOL (buys minus sells) on a tape over the last `w` slots. */
function flowOver(t: Tape, now: number, w: number): number {
  let net = 0;
  for (let i = t.trades.length - 1; i >= 0; i--) {
    const tr = t.trades[i]!;
    if (tr.slot <= now - w) break;
    net += tr.buy ? tr.sol : -tr.sol;
  }
  return net;
}

/** Price of a coin now, from its latest known virtual reserves. */
function priceNow(state: BotState, mint: Pubkey): number {
  const c = state.curves.get(mint);
  if (c === undefined) return 0;
  const vt = Number(c.virtual_token_reserves);
  if (vt <= 0) return 0;
  return Number(c.virtual_quote_reserves) / vt;
}

/** Real SOL reserves of a coin now. */
function realSol(state: BotState, mint: Pubkey): number {
  const c = state.curves.get(mint);
  if (c === undefined) return 0;
  return Number(c.real_quote_reserves) / LAM;
}

/** What a held position would fetch if sold now, SOL after curve and tx fees. */
function closeValue(state: BotState, mint: Pubkey, tokens: bigint): number {
  const c = state.curves.get(mint);
  if (c === undefined) return 0;
  const vt = Number(c.virtual_token_reserves);
  const vq = Number(c.virtual_quote_reserves);
  const n = Number(tokens);
  if (vt + n <= 0) return 0;
  const gross = (n * vq) / (vt + n) / LAM;
  return gross * (1 - FEE_RATE) - Number(state.txFeeLamports()) / LAM;
}

// --------------------------------------------------------------------------- signals

/** Runner signal: steady, broad, accelerating buying on an established coin. */
function runnerSignal(t: Tape, now: number): boolean {
  if (t.created === null || now - t.created < MOM.ageMin) return false;
  if (t.seen < MOM.tradesMin) return false;
  const from = now - MOM.window;
  const mid = now - MOM.window / 2;
  let buySol = 0;
  let sellSol = 0;
  let buys = 0;
  let netOld = 0;
  let netNew = 0;
  let startPrice = -1;
  let high = 0;
  let last = 0;
  const buyers = new Map<string, number>();
  for (const tr of t.trades) {
    if (tr.slot <= from) {
      startPrice = tr.price;
      continue;
    }
    if (startPrice < 0) startPrice = tr.price;
    const signed = tr.buy ? tr.sol : -tr.sol;
    if (tr.slot <= mid) netOld += signed;
    else netNew += signed;
    if (tr.buy) {
      buySol += tr.sol;
      buys++;
      buyers.set(tr.user, (buyers.get(tr.user) ?? 0) + tr.sol);
    } else {
      sellSol += tr.sol;
    }
    if (tr.price > high) high = tr.price;
    last = tr.price;
  }
  if (buys < MOM.minBuys || buyers.size < MOM.minBuyers) return false;
  if (buySol - sellSol < MOM.minNetSol) return false;
  if (startPrice <= 0 || last <= 0) return false;
  const up = last / startPrice - 1;
  if (up < MOM.minUp || up > MOM.maxUp) return false;
  if (last < high * MOM.nearHigh) return false;
  if (netNew <= 0 || netNew < MOM.accel * netOld) return false;
  let top = 0;
  for (const v of buyers.values()) if (v > top) top = v;
  if (buySol > 0 && top > MOM.maxBuyerShare * buySol) return false;
  return true;
}

// --------------------------------------------------------------------------- the bot

const bot = {
  onBatch(state: BotState, batch: Batch): OrderInput[] {
    const now = batch.slot;
    const traded = new Set<Pubkey>();
    for (const f of batch.fills) {
      if (f.status === 'filled' && !f.client_id.startsWith('_')) {
        myFills++;
        myCoins.add(f.mint);
      }
    }
    for (const e of batch.events) {
      if (e.block_time !== null) {
        if (firstBlockTime === null) firstBlockTime = e.block_time;
        if (lastBlockTime === null || e.block_time > lastBlockTime) lastBlockTime = e.block_time;
      }
      if (e.event === 'CreateEvent') {
        tapeOf(e.mint).created = e.slot;
      } else if (e.event === 'TradeEvent') {
        const t = tapeOf(e.mint);
        t.seen++;
        t.trades.push({
          slot: e.slot,
          buy: e.is_buy,
          sol: Number(e.sol_amount) / LAM,
          user: e.user,
          price: Number(e.virtual_quote_reserves) / Number(e.virtual_token_reserves),
        });
        traded.add(e.mint);
      }
    }
    // Prune old tape entries on coins that traded this batch.
    const keep = Math.max(MOM.window, MOM.fadeWindow) + 10;
    for (const mint of traded) {
      const t = tapes.get(mint)!;
      let cut = 0;
      while (cut < t.trades.length && t.trades[cut]!.slot <= now - keep) cut++;
      if (cut > 0) t.trades.splice(0, cut);
    }

    const orders: OrderInput[] = [];
    const cap = state.hello.caps.max_orders_per_batch;
    const txSol = Number(state.txFeeLamports()) / LAM;
    const pendingByMint = new Map<Pubkey, number>();
    const sellPending = new Set<Pubkey>();
    for (const po of state.pending.values()) {
      pendingByMint.set(po.order.mint, (pendingByMint.get(po.order.mint) ?? 0) + 1);
      if (po.order.side === 'sell') sellPending.add(po.order.mint);
    }
    const pushSellAll = (mint: Pubkey): boolean => {
      const pos = state.positions.get(mint);
      if (pos === undefined || sellPending.has(mint)) return false;
      if (orders.length >= cap) return false;
      orders.push({ side: 'sell', mint, token_amount: pos.token_amount, max_slippage_bps: SELL_SLIP });
      return true;
    };

    // --- exits first: stops, trailing stops, fading flow, time limits.
    for (const [mint, p] of open) {
      const pos = state.positions.get(mint);
      const curve = state.curves.get(mint);
      if (pos === undefined) {
        if (!pendingByMint.has(mint)) {
          open.delete(mint);
          if (p.filled) tapeOf(mint).lastExit = now;
          else tapeOf(mint).entries--;
        }
        continue;
      }
      p.filled = true;
      if (curve === undefined || curve.complete) continue;
      const value = closeValue(state, mint, BigInt(pos.token_amount));
      const cost = Number(pos.cost_lamports) / LAM;
      if (value > p.peakValue) p.peakValue = value;
      let exit = p.exiting;
      if (!exit && value < cost * (1 - MOM.stopLoss)) exit = true;
      if (!exit && p.peakValue >= cost * (1 + MOM.trailArm) && value < p.peakValue * (1 - MOM.trail)) exit = true;
      if (!exit && flowOver(tapeOf(mint), now, MOM.fadeWindow) < MOM.fadeNetSol) exit = true;
      if (!exit && now - p.opened > MOM.maxHold && value < cost * (1 + MOM.holdIfUp)) exit = true;
      if (!exit) continue;
      p.exiting = true;
      pushSellAll(mint);
    }

    // --- probe sells: a probe is sold whole as soon as its buy has landed.
    for (const [mint] of probes) {
      const pos = state.positions.get(mint);
      const curve = state.curves.get(mint);
      if (pos === undefined) {
        if (!pendingByMint.has(mint)) probes.delete(mint);
        continue;
      }
      if (curve === undefined || curve.complete || pendingByMint.has(mint)) continue;
      if (pushSellAll(mint)) probes.set(mint, true);
    }

    // --- entries and scale-ins, only on coins that traded this batch.
    let free = Number(state.freeCashLamports()) / LAM;
    let slotsLeft = state.hello.caps.max_open_positions - state.committedPositionCount();
    let mainLeft = GLOBAL.maxMain - open.size;
    let exposure = 0;
    for (const [mint, p] of open) {
      const pos = state.positions.get(mint);
      exposure += Math.max(p.invested, pos === undefined ? 0 : Number(pos.cost_lamports) / LAM);
    }
    for (const mint of traded) {
      if (orders.length >= cap) break;
      const curve = state.curves.get(mint);
      if (curve === undefined || curve.complete) continue;
      if (pendingByMint.has(mint) || probes.has(mint)) continue;
      const t = tapes.get(mint)!;
      const p = open.get(mint);
      const rq = realSol(state, mint);
      let want = 0;
      if (p === undefined) {
        if (slotsLeft <= 0 || mainLeft <= 0) continue;
        if (t.entries >= GLOBAL.maxEntries || now - t.lastExit < GLOBAL.cooldown) continue;
        if (rq < MOM.rqMin || rq > MOM.rqMax) continue;
        if (!runnerSignal(t, now)) continue;
        want = MOM.initialSol;
      } else {
        // Scale into strength only: price stepped up from the last buy, position not underwater.
        if (p.exiting || !p.filled) continue;
        if (p.invested >= MOM.stakeSol - GLOBAL.minBuySol) continue;
        const pos = state.positions.get(mint);
        if (pos === undefined) continue;
        const price = priceNow(state, mint);
        if (price < p.lastAddPrice * (1 + MOM.addStep)) continue;
        const cost = Number(pos.cost_lamports) / LAM;
        if (closeValue(state, mint, BigInt(pos.token_amount)) < cost) continue;
        if (flowOver(t, now, MOM.window) < MOM.minNetSol) continue;
        if (rq > MOM.rqMax) continue;
        want = Math.min(MOM.addSol, MOM.stakeSol - p.invested);
      }
      const capSol = Number(state.maxBuyLamports(mint)) / LAM;
      let amount = Math.min(capSol, want, GLOBAL.maxExposureSol - exposure);
      if (amount > free - txSol) amount = free - txSol;
      if (!Number.isFinite(amount)) {
        console.error(`nan-amount slot=${now} mint=${mint} capSol=${capSol} want=${want} exposure=${exposure} free=${free} txSol=${txSol}`);
        continue;
      }
      if (amount < GLOBAL.minBuySol) continue;
      orders.push({
        side: 'buy',
        mint,
        quote_lamports: BigInt(Math.floor(amount * LAM)),
        max_slippage_bps: GLOBAL.buySlipBps,
      });
      free -= amount + txSol;
      exposure += amount;
      if (p === undefined) {
        open.set(mint, {
          opened: now,
          peakValue: 0,
          invested: amount,
          lastAddPrice: priceNow(state, mint),
          filled: false,
          exiting: false,
        });
        t.entries++;
        slotsLeft--;
        mainLeft--;
      } else {
        p.invested += amount;
        p.lastAddPrice = priceNow(state, mint);
      }
    }

    // --- guardrail pacing: probe round trips when fills or coins lag the pace.
    if (probes.size < GLOBAL.maxProbes && slotsLeft > 0 && firstBlockTime !== null && lastBlockTime !== null) {
      const pace = Math.min(1, (lastBlockTime - firstBlockTime) / GLOBAL.paceSecs);
      const needCoins = myCoins.size < Math.ceil(GLOBAL.targetCoins * pace);
      const needFills = myFills < Math.ceil(GLOBAL.targetFills * pace);
      if (needCoins || needFills) {
        for (const mint of traded) {
          if (orders.length >= cap || probes.size >= GLOBAL.maxProbes) break;
          if (open.has(mint) || probes.has(mint) || pendingByMint.has(mint) || state.positions.has(mint)) continue;
          if (myCoins.has(mint)) continue; // a probe always opens a NEW coin; never re-probe one
          const curve = state.curves.get(mint);
          if (curve === undefined || curve.complete) continue;
          const t = tapes.get(mint)!;
          if (t.created === null || now - t.created < 200) continue; // no fresh-coin probes
          if (realSol(state, mint) < 1) continue;
          if (free < GLOBAL.probeSol + 2 * txSol) break;
          orders.push({
            side: 'buy',
            mint,
            quote_lamports: BigInt(Math.floor(GLOBAL.probeSol * LAM)),
            max_slippage_bps: GLOBAL.buySlipBps,
          });
          probes.set(mint, false);
          free -= GLOBAL.probeSol + txSol;
        }
      }
    }
    return orders;
  },
};

await runBot(bot);
