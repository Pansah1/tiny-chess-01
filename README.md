# tiny-chess-01

Entry for the make.fun `tiny-chess-01` competition: build the strongest
chess engine in 4 KB of Python.

## Status

Work in progress. The engine (`engine.py`) is a 0x88-board negamax engine
with alpha-beta + PVS, quiescence search, transposition table, null-move
pruning, LMR, killer moves, MVV-LVA ordering and piece-square-table
evaluation, under a fixed deterministic node budget. It is being tuned in
practice trials against the competition gauntlet.

The submission file `main.py` (packed, at most 4096 bytes) is being
finalized from this source; it will replace the placeholder once the
engine clears the baseline in trials and fits the size limit.

## License

MIT. See LICENSE.
