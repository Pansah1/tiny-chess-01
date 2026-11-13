# Tiny chess engine for make.fun tiny-chess-01 (MIT).
# 0x88 board, negamax + alpha-beta + quiescence, transposition table,
# null-move pruning, LMR, killer moves, MVV-LVA ordering, fixed node budget
# (deterministic: no wall clock, no unseeded randomness).
# Pieces: type 1..6 = P N B R Q K, colour bit 8 = black. 0x88: sq = rank*16+file.
import json, os, random, sys, urllib.error, urllib.request

VAL = [0, 100, 320, 330, 500, 900, 20000]
# Piece-square tables, a1..h8 order, white perspective (Michniewski-style).
PP = [0,0,0,0,0,0,0,0, 5,10,10,-20,-20,10,10,5, 5,-5,-10,0,0,-10,-5,5, 0,0,0,20,20,0,0,0, 5,5,10,25,25,10,5,5, 10,10,20,30,30,20,10,10, 50,50,50,50,50,50,50,50, 0,0,0,0,0,0,0,0]
PN = [-50,-40,-30,-30,-30,-30,-40,-50, -40,-20,0,5,5,0,-20,-40, -30,5,10,15,15,10,5,-30, -30,0,15,20,20,15,0,-30, -30,5,15,20,20,15,5,-30, -30,0,10,15,15,10,0,-30, -40,-20,0,0,0,0,-20,-40, -50,-40,-30,-30,-30,-30,-40,-50]
PB = [-20,-10,-10,-10,-10,-10,-10,-20, -10,5,0,0,0,0,5,-10, -10,10,10,10,10,10,10,-10, -10,0,10,10,10,10,0,-10, -10,5,5,10,10,5,5,-10, -10,0,5,10,10,5,0,-10, -10,0,0,0,0,0,0,-10, -20,-10,-10,-10,-10,-10,-10,-20]
PR = [0,0,0,5,5,0,0,0, -5,0,0,0,0,0,0,-5, -5,0,0,0,0,0,0,-5, -5,0,0,0,0,0,0,-5, -5,0,0,0,0,0,0,-5, -5,0,0,0,0,0,0,-5, 5,10,10,10,10,10,10,5, 0,0,0,0,0,0,0,0]
PQ = [-20,-10,-10,-5,-5,-10,-10,-20, -10,0,5,0,0,0,0,-10, -10,5,5,5,5,5,0,-10, 0,0,5,5,5,5,0,-5, -5,0,5,5,5,5,0,-5, -10,0,5,5,5,5,0,-10, -10,0,0,0,0,0,0,-10, -20,-10,-10,-5,-5,-10,-10,-20]
PK = [20,30,10,0,0,10,30,20, 20,20,0,0,0,0,20,20, -10,-20,-20,-20,-20,-20,-20,-10, -20,-30,-30,-40,-40,-30,-30,-20, -30,-40,-40,-50,-50,-40,-40,-30, -30,-40,-40,-50,-50,-40,-40,-30, -30,-40,-40,-50,-50,-40,-40,-30, -30,-40,-40,-50,-50,-40,-40,-30]
PKE = [-50,-30,-30,-30,-30,-30,-30,-50, -30,-30,0,0,0,0,-30,-30, -30,-10,20,30,30,20,-10,-30, -30,-10,30,40,40,30,-10,-30, -30,-10,30,40,40,30,-10,-30, -30,-10,20,30,30,20,-10,-30, -30,-20,-10,0,0,-10,-20,-30, -50,-40,-30,-20,-20,-30,-40,-50]
PST = [None, PP, PN, PB, PR, PQ, PK]
KN = [33, 31, 18, 14, -14, -18, -31, -33]
KI = [1, -1, 16, -16, 15, 17, -15, -17]
BI = [15, 17, -15, -17]
RI = [1, -1, 16, -16]
MATE = 100000
# Node budget per move (fixed: deterministic). Tuned after measuring nps.
NODES = 60000
# Repetition history for the current game: zobrist key -> occurrences.
HIST = {}
HIST_GAME = -1

_R = random.Random(0x5EED)
Z = [[_R.getrandbits(64) for _ in range(128)] for _ in range(16)]
ZS = _R.getrandbits(64)
ZC = [_R.getrandbits(64) for _ in range(16)]
ZE = [_R.getrandbits(64) for _ in range(8)]

# Mutable game state (globals for speed).
B = [0] * 128          # board
SIDE = 0               # 0 white, 8 black
CASTLE = 0             # bits: 1 WK, 2 WQ, 4 BK, 8 BQ
EP = -1                # en passant target square, -1 none
KEY = 0                # zobrist key
N = 0                  # nodes searched
TT = {}                # key -> (depth, score, flag, bestmove)
KILL = [[0, 0] for _ in range(128)]  # killer moves per ply


def sq_name(s):
    return "abcdefgh"[s & 7] + str((s >> 4) + 1)


def sq_num(name):
    return ("abcdefgh".index(name[0])) + (int(name[1]) - 1) * 16


def parse_fen(fen):
    """Load a FEN into the globals. Returns nothing."""
    global SIDE, CASTLE, EP, KEY
    del UNDO[:]
    for i in range(128):
        B[i] = 0
    parts = fen.split()
    rows = parts[0].split("/")
    for r, row in enumerate(rows):
        rank = 7 - r
        f = 0
        for c in row:
            if c.isdigit():
                f += int(c)
            else:
                t = "PNBRQK".index(c.upper()) + 1
                if c.islower():
                    t += 8
                B[rank * 16 + f] = t
                f += 1
    SIDE = 0 if parts[1] == "w" else 8
    CASTLE = 0
    if len(parts) > 2:
        for c in parts[2]:
            CASTLE |= {"K": 1, "Q": 2, "k": 4, "q": 8}.get(c, 0)
    EP = sq_num(parts[3]) if len(parts) > 3 and parts[3] != "-" else -1
    KEY = 0
    for s in range(128):
        p = B[s]
        if p:
            KEY ^= Z[p][s]
    KEY ^= ZS if SIDE else 0
    KEY ^= ZC[CASTLE]
    if EP >= 0:
        KEY ^= ZE[EP & 7]


def attacked(sq, by):
    """True if square sq is attacked by colour by (0 white, 8 black)."""
    if by == 0:
        if sq >= 15 and (B[sq - 15] == 1 or B[sq - 17] == 1):
            return True
    elif sq < 111 and (B[sq + 15] == 9 or B[sq + 17] == 9):
        return True
    for d in KN:
        t = sq + d
        if not t & 0x88 and B[t] == (2 | by):
            return True
    for d in KI:
        t = sq + d
        if not t & 0x88 and B[t] == (6 | by):
            return True
    for d in BI:
        t = sq + d
        while not t & 0x88:
            p = B[t]
            if p:
                if p == (3 | by) or p == (5 | by):
                    return True
                break
            t += d
    for d in RI:
        t = sq + d
        while not t & 0x88:
            p = B[t]
            if p:
                if p == (4 | by) or p == (5 | by):
                    return True
                break
            t += d
    return False


def king_sq(by):
    for s in range(128):
        if B[s] == (6 | by):
            return s
    return -1


def gen_caps():
    """Pseudo-legal captures and promotions for SIDE (quiescence)."""
    ms = []
    for f in range(128):
        if f & 0x88:
            continue
        p = B[f]
        if not p or (p & 8) != SIDE:
            continue
        t = p & 7
        if t == 1:
            d = 16 if SIDE == 0 else -16
            last = 7 if SIDE == 0 else 0
            for dd in (d - 1, d + 1):
                to = f + dd
                if to & 0x88:
                    continue
                q = B[to]
                if q and (q & 8) != SIDE:
                    if (to >> 4) == last:
                        for pr in (5, 4, 3, 2):
                            ms.append(f | (to << 7) | (pr << 14))
                    else:
                        ms.append(f | (to << 7))
                elif to == EP:
                    ms.append(f | (to << 7))
            to = f + d
            if not to & 0x88 and not B[to] and (to >> 4) == last:
                for pr in (5, 4, 3, 2):
                    ms.append(f | (to << 7) | (pr << 14))
        elif t == 2:
            for dd in KN:
                to = f + dd
                if not to & 0x88 and B[to] and (B[to] & 8) != SIDE:
                    ms.append(f | (to << 7))
        elif t == 6:
            for dd in KI:
                to = f + dd
                if not to & 0x88 and B[to] and (B[to] & 8) != SIDE:
                    ms.append(f | (to << 7))
        else:
            ds = BI if t == 3 else RI if t == 4 else BI + RI
            for dd in ds:
                to = f + dd
                while not to & 0x88:
                    q = B[to]
                    if q:
                        if (q & 8) != SIDE:
                            ms.append(f | (to << 7))
                        break
                    to += dd
    return ms


def gen_all():
    """All pseudo-legal moves for SIDE (castling included)."""
    ms = []
    for f in range(128):
        if f & 0x88:
            continue
        p = B[f]
        if not p or (p & 8) != SIDE:
            continue
        t = p & 7
        if t == 1:
            d = 16 if SIDE == 0 else -16
            last = 7 if SIDE == 0 else 0
            start = 1 if SIDE == 0 else 6
            to = f + d
            if not to & 0x88 and not B[to]:
                if (to >> 4) == last:
                    for pr in (5, 4, 3, 2):
                        ms.append(f | (to << 7) | (pr << 14))
                else:
                    ms.append(f | (to << 7))
                    if (f >> 4) == start:
                        to2 = f + 2 * d
                        if not B[to2]:
                            ms.append(f | (to2 << 7))
            for dd in (d - 1, d + 1):
                to = f + dd
                if to & 0x88:
                    continue
                q = B[to]
                if q and (q & 8) != SIDE:
                    if (to >> 4) == last:
                        for pr in (5, 4, 3, 2):
                            ms.append(f | (to << 7) | (pr << 14))
                    else:
                        ms.append(f | (to << 7))
                elif to == EP:
                    ms.append(f | (to << 7))
        elif t == 2:
            for dd in KN:
                to = f + dd
                if not to & 0x88 and (not B[to] or (B[to] & 8) != SIDE):
                    ms.append(f | (to << 7))
        elif t == 6:
            for dd in KI:
                to = f + dd
                if not to & 0x88 and (not B[to] or (B[to] & 8) != SIDE):
                    ms.append(f | (to << 7))
            # castling: king on e1/e8, rights, empty, unattacked path
            if SIDE == 0 and f == 4:
                if CASTLE & 1 and not B[5] and not B[6] and B[7] == 4 and not attacked(4, 8) and not attacked(5, 8) and not attacked(6, 8):
                    ms.append(4 | (6 << 7))
                if CASTLE & 2 and not B[3] and not B[2] and not B[1] and B[0] == 4 and not attacked(4, 8) and not attacked(3, 8) and not attacked(2, 8):
                    ms.append(4 | (2 << 7))
            elif SIDE == 8 and f == 116:
                if CASTLE & 4 and not B[117] and not B[118] and B[119] == 12 and not attacked(116, 0) and not attacked(117, 0) and not attacked(118, 0):
                    ms.append(116 | (118 << 7))
                if CASTLE & 8 and not B[115] and not B[114] and not B[113] and B[112] == 12 and not attacked(116, 0) and not attacked(115, 0) and not attacked(114, 0):
                    ms.append(116 | (114 << 7))
        else:
            ds = BI if t == 3 else RI if t == 4 else BI + RI
            for dd in ds:
                to = f + dd
                while not to & 0x88:
                    q = B[to]
                    if q:
                        if (q & 8) != SIDE:
                            ms.append(f | (to << 7))
                        break
                    ms.append(f | (to << 7))
                    to += dd
    return ms


# Undo stack entries: (captured, captured_sq, castle, ep, key_delta_info...)
# make() updates B, SIDE, CASTLE, EP, KEY; unmake() restores via the entry.
UNDO = []


def make(m):
    global SIDE, CASTLE, EP, KEY
    f = m & 127
    t = (m >> 7) & 127
    pr = (m >> 14) & 7
    pc = B[f]
    cap = B[t]
    cap_sq = t
    KEY ^= Z[pc][f]
    if cap:
        KEY ^= Z[cap][t]
    # en passant capture
    if (pc & 7) == 1 and t == EP and not cap:
        cap_sq = t - 16 if SIDE == 0 else t + 16
        cap = B[cap_sq]
        B[cap_sq] = 0
        KEY ^= Z[cap][cap_sq]
    B[f] = 0
    np = (pr | (pc & 8)) if pr else pc
    B[t] = np
    KEY ^= Z[np][t]
    old_castle = CASTLE
    KEY ^= ZC[CASTLE]
    # castling rights lost by king/rook move or rook capture
    if (pc & 7) == 6:
        CASTLE &= ~(3 if SIDE == 0 else 12)
    if f == 0 or t == 0:
        CASTLE &= ~2
    if f == 7 or t == 7:
        CASTLE &= ~1
    if f == 112 or t == 112:
        CASTLE &= ~8
    if f == 119 or t == 119:
        CASTLE &= ~4
    KEY ^= ZC[CASTLE]
    # castling rook
    if (pc & 7) == 6 and abs(t - f) == 2:
        if t == 6:
            B[7] = 0; B[5] = 4; KEY ^= Z[4][7] ^ Z[4][5]
        elif t == 2:
            B[0] = 0; B[3] = 4; KEY ^= Z[4][0] ^ Z[4][3]
        elif t == 118:
            B[119] = 0; B[117] = 12; KEY ^= Z[12][119] ^ Z[12][117]
        elif t == 114:
            B[112] = 0; B[115] = 12; KEY ^= Z[12][112] ^ Z[12][115]
    # new ep square
    old_ep = EP
    if (pc & 7) == 1 and abs(t - f) == 32:
        EP = (f + t) // 2
    else:
        EP = -1
    if old_ep >= 0:
        KEY ^= ZE[old_ep & 7]
    if EP >= 0:
        KEY ^= ZE[EP & 7]
    KEY ^= ZS
    SIDE ^= 8
    UNDO.append((cap, cap_sq, old_castle, old_ep))
    return cap


def unmake(m):
    global SIDE, CASTLE, EP, KEY
    f = m & 127
    t = (m >> 7) & 127
    pr = (m >> 14) & 7
    cap, cap_sq, old_castle, old_ep = UNDO.pop()
    SIDE ^= 8
    KEY ^= ZS
    if EP >= 0:
        KEY ^= ZE[EP & 7]
    if old_ep >= 0:
        KEY ^= ZE[old_ep & 7]
    EP = old_ep
    KEY ^= ZC[CASTLE]
    CASTLE = old_castle
    KEY ^= ZC[CASTLE]
    pc = B[t]
    KEY ^= Z[pc][t]
    if (pc & 7) == 6 and abs(t - f) == 2:
        if t == 6:
            B[7] = 4; B[5] = 0; KEY ^= Z[4][7] ^ Z[4][5]
        elif t == 2:
            B[0] = 4; B[3] = 0; KEY ^= Z[4][0] ^ Z[4][3]
        elif t == 118:
            B[119] = 12; B[117] = 0; KEY ^= Z[12][119] ^ Z[12][117]
        elif t == 114:
            B[112] = 12; B[115] = 0; KEY ^= Z[12][112] ^ Z[12][115]
    B[t] = 0
    # restore moved piece (for promotions, restore the pawn)
    B[f] = (1 | (pc & 8)) if pr else pc
    KEY ^= Z[B[f]][f]
    if cap:
        B[cap_sq] = cap
        KEY ^= Z[cap][cap_sq]


def evaluate():
    """White-perspective centipawn score, from SIDE's view."""
    s = 0
    npm = 0  # non-pawn material (for endgame detection)
    for sq in range(128):
        if sq & 0x88:
            continue
        p = B[sq]
        if not p:
            continue
        t = p & 7
        v = VAL[t]
        i64 = ((sq >> 4) * 8) + (sq & 7)
        if p & 8:
            v += PST[t][i64 ^ 56]
            s -= v
            if t != 1:
                npm += VAL[t]
        else:
            v += PST[t][i64]
            s += v
            if t != 1:
                npm += VAL[t]
    # bishop pair
    # (counted cheaply: +30 if a side has 2 bishops)
    wb = sum(1 for sq in range(128) if B[sq] == 3)
    bb = sum(1 for sq in range(128) if B[sq] == 11)
    if wb >= 2:
        s += 30
    if bb >= 2:
        s -= 30
    # endgame king table when little material left
    if npm <= 1300:
        for sq in range(128):
            if sq & 0x88:
                continue
            p = B[sq]
            if p and (p & 7) == 6:
                i64 = ((sq >> 4) * 8) + (sq & 7)
                if p & 8:
                    s -= PKE[i64 ^ 56] - PK[i64 ^ 56]
                else:
                    s += PKE[i64] - PK[i64]
    return s if SIDE == 0 else -s


class Timeout(Exception):
    pass


def order(ms, tt_move, ply):
    """Order moves: TT move, captures (MVV-LVA), killers, rest."""
    def score(m):
        if m == tt_move:
            return 1 << 20
        t = (m >> 7) & 127
        v = B[t]
        if v:
            return (1 << 16) + VAL[v & 7] * 16 - VAL[B[m & 127] & 7]
        if m == KILL[ply][0]:
            return 9000
        if m == KILL[ply][1]:
            return 8000
        return 0
    ms.sort(key=score, reverse=True)
    return ms


def qs(alpha, beta, ply):
    global N
    N += 1
    if N > NODES:
        raise Timeout()
    stand = evaluate()
    if stand >= beta:
        return beta
    if stand > alpha:
        alpha = stand
    in_check = attacked(king_sq(SIDE), SIDE ^ 8)
    ms = gen_all() if in_check else gen_caps()
    # legality filter + ordering (captures only in qs)
    legal = []
    for m in ms:
        make(m)
        if not attacked(king_sq(SIDE ^ 8), SIDE):
            legal.append(m)
        unmake(m)
    order(legal, 0, ply)
    if in_check and not legal:
        return -MATE + ply
    for m in legal:
        make(m)
        sc = -qs(-beta, -alpha, ply + 1)
        unmake(m)
        if sc >= beta:
            return beta
        if sc > alpha:
            alpha = sc
    return alpha


def search(alpha, beta, depth, ply):
    global N
    N += 1
    if N > NODES:
        raise Timeout()
    in_check = attacked(king_sq(SIDE), SIDE ^ 8)
    if depth <= 0:
        return qs(alpha, beta, ply)
    # transposition table probe
    ent = TT.get(KEY)
    tt_move = 0
    if ent:
        ed, es, ef, em = ent
        tt_move = em
        if ed >= depth:
            if ef == 0:
                return es
            if ef == 1 and es >= beta:
                return beta
            if ef == 2 and es <= alpha:
                return alpha
    # null-move pruning
    if depth >= 3 and not in_check and evaluate() >= beta:
        make_null()
        sc = -search(-beta, -beta + 1, depth - 3, ply + 1)
        unmake_null()
        if sc >= beta:
            return beta
    ms = gen_all()
    legal = []
    for m in ms:
        make(m)
        if not attacked(king_sq(SIDE ^ 8), SIDE):
            legal.append(m)
        unmake(m)
    if not legal:
        return -MATE + ply if in_check else 0
    order(legal, tt_move, ply)
    best = -MATE - 1
    best_move = 0
    flag = 2
    for i, m in enumerate(legal):
        cap = B[(m >> 7) & 127]
        make(m)
        if i >= 4 and depth >= 3 and not cap and not ((m >> 14) & 7) and not in_check:
            sc = -search(-alpha - 1, -alpha, depth - 2, ply + 1)
            if sc > alpha:
                sc = -search(-beta, -alpha, depth - 1, ply + 1)
        else:
            sc = -search(-beta, -alpha, depth - 1, ply + 1)
        unmake(m)
        if sc > best:
            best = sc
            best_move = m
            if sc > alpha:
                alpha = sc
                flag = 0
                if sc >= beta:
                    flag = 1
                    if not cap:
                        if KILL[ply][0] != m:
                            KILL[ply][1] = KILL[ply][0]
                            KILL[ply][0] = m
                    break
    if abs(best) < MATE - 1000:
        if len(TT) > 300000:
            TT.clear()
        TT[KEY] = (depth, best, flag, best_move)
    return best


def make_null():
    global SIDE, EP, KEY
    old_ep = EP
    if EP >= 0:
        KEY ^= ZE[EP & 7]
    EP = -1
    KEY ^= ZS
    SIDE ^= 8
    UNDO.append((0, -1, CASTLE, old_ep))


def unmake_null():
    global SIDE, EP, KEY
    _, _, _, old_ep = UNDO.pop()
    SIDE ^= 8
    KEY ^= ZS
    EP = old_ep
    if EP >= 0:
        KEY ^= ZE[EP & 7]


def uci(m):
    s = sq_name(m & 127) + sq_name((m >> 7) & 127)
    pr = (m >> 14) & 7
    if pr:
        s += {5: "q", 2: "n", 3: "b", 4: "r"}[pr]
    return s


def move_from_uci(u):
    f = sq_num(u[:2])
    t = sq_num(u[2:4])
    pr = 0
    if len(u) == 5:
        pr = {"q": 5, "n": 2, "b": 3, "r": 4}[u[4]]
    return f | (t << 7) | (pr << 14)


def root(fen, legal_uci, game_no):
    """Iterative deepening under a fixed node budget. Returns a UCI string."""
    global N, HIST_GAME
    if game_no != HIST_GAME:
        HIST.clear()
        HIST_GAME = game_no
    parse_fen(fen)
    HIST[KEY] = HIST.get(KEY, 0) + 1
    root_moves = [move_from_uci(u) for u in legal_uci]
    # order root moves: captures first (stable, deterministic)
    root_moves.sort(key=lambda m: (VAL[B[(m >> 7) & 127] & 7], m), reverse=True)
    best = root_moves[0]
    done_scores = {}
    done_depth = 0
    N = 0
    for p in range(128):
        KILL[p][0] = 0
        KILL[p][1] = 0
    try:
        depth = 1
        while True:
            scores = {}
            alpha = -MATE - 1
            cur_best = best
            cur_score = -MATE - 1
            for i, m in enumerate(root_moves):
                make(m)
                if i == 0:
                    sc = -search(-MATE - 1, MATE + 1, depth - 1, 1)
                else:
                    # PVS: null window tests whether m beats alpha; on
                    # fail-high re-search with a full window for the exact
                    # score (a bound read as a score is the old bug).
                    sc = -search(-alpha - 1, -alpha, depth - 1, 1)
                    if sc > alpha:
                        sc = -search(-MATE - 1, MATE + 1, depth - 1, 1)
                unmake(m)
                scores[m] = sc
                if sc > cur_score:
                    cur_score = sc
                    cur_best = m
                if sc > alpha:
                    alpha = sc
            best = cur_best
            done_scores = scores
            done_depth = depth
            # move best to front for the next iteration
            root_moves.remove(best)
            root_moves.insert(0, best)
            depth += 1
    except Timeout:
        pass
    # The timeout unwinds mid-search, leaving the board mid-move:
    # reload the root position before the repetition check.
    parse_fen(fen)
    scores = done_scores if done_scores else scores
    ranked = sorted(root_moves, key=lambda m: scores.get(m, -MATE - 1), reverse=True)
    best_score = scores.get(ranked[0], -MATE - 1)
    chosen = ranked[0]
    # Lazy verification: the best move's PVS score is exact, so if it does
    # not repeat, play it with no extra work. Only when the best repeats do
    # we need exact scores for the alternatives (their null-window scores
    # are bounds, not exact), so verify the top candidates then.
    for m in ranked:
        sc = scores.get(m, -MATE - 1)
        if sc > MATE - 1000:
            chosen = m
            break
        make(m)
        rep = HIST.get(KEY, 0) >= 2
        unmake(m)
        if not rep:
            if sc >= best_score - 150:
                chosen = m
            break
        # Best (or a better alternative) repeats: verify the top
        # candidates with exact full-window scores before choosing.
        N = 0
        try:
            for v in ranked[:4]:
                make(v)
                scores[v] = -search(-MATE - 1, MATE + 1, max(done_depth - 1, 0), 1)
                unmake(v)
        except Timeout:
            pass
        ranked = sorted(root_moves, key=lambda mm: scores.get(mm, -MATE - 1), reverse=True)
        best_score = scores.get(ranked[0], -MATE - 1)
        for m2 in ranked:
            sc2 = scores.get(m2, -MATE - 1)
            if sc2 > MATE - 1000:
                chosen = m2
                break
            make(m2)
            rep2 = HIST.get(KEY, 0) >= 2
            unmake(m2)
            if not rep2:
                if sc2 >= best_score - 150:
                    chosen = m2
                break
        break
    make(chosen)
    HIST[KEY] = HIST.get(KEY, 0) + 1
    unmake(chosen)
    return uci(chosen)


ENV_URL = os.environ.get("MAKEFUN_ENV_URL") or ""


def post(path, body):
    req = urllib.request.Request(
        ENV_URL + path,
        data=json.dumps(body).encode(),
        headers={"content-type": "application/json"},
    )
    try:
        with urllib.request.urlopen(req) as res:
            return json.load(res)
    except urllib.error.HTTPError as e:
        sys.exit(f"{path}: HTTP {e.code} {e.read().decode(errors='replace')}")


def main():
    if not ENV_URL:
        sys.exit("MAKEFUN_ENV_URL is not set")
    while True:
        g = post("/game", {})
        if g["status"] == "done":
            break
        while g["status"] == "your_move":
            mv = root(g["fen"], g["legal_moves"], g["game"])
            g = post("/move", {"game": g["game"], "move": mv})
        print(f"game {g['game']}: {g['outcome']} by {g['reason']}", file=sys.stderr)
    print(f"done: {g.get('wins')} won, {g.get('draws')} drawn, {g.get('losses')} lost", file=sys.stderr)


if __name__ == "__main__":
    main()
