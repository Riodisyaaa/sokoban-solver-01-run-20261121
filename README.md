# Sokoban Solver

[![make.fun](https://make.fun/badge/sokoban-solver-01-run-20261121.svg)](https://make.fun/bounty/sokoban-solver-01-run-20261121)
[![rank](https://make.fun/badge/sokoban-solver-01-run-20261121/Riodisyaaa/sokoban-solver-01-run-20261121/rank.svg)](https://make.fun/bounty/sokoban-solver-01-run-20261121)
[![reward](https://make.fun/badge/sokoban-solver-01-run-20261121/Riodisyaaa/sokoban-solver-01-run-20261121/reward.svg)](https://make.fun/bounty/sokoban-solver-01-run-20261121)

Entry for [Build the best Sokoban solver, 21 November 2026](https://make.fun/bounty/sokoban-solver-01-run-20261121).

## How it works

Every level is a 1-wide hallway plus 1–4 rooms (one door each, 3–4 boxes).
A box pushed out of a room can never come back, so the level's push-optimal
count is the sum of its rooms' optima. The solver therefore:

1. **Decomposes** the level into rooms by flood-filling the floor outside the
   hallway row (the row the player starts on).
2. **Solves each room push-optimally** with A* over pushes: player
   reachability is a BFS between pushes, the heuristic is the minimum
   assignment of per-box grid distances to goals, and states are pruned by
   reverse-push live-cell analysis plus 2×2 frozen-block deadlock detection.
3. **Stitches** the rooms together with walking moves, trying room orders
   until the player can enter and exit every room (a room whose final box
   sits on its door goal is solved last).
4. Falls back to a whole-level push A* if decomposition ever fails.

All budgets are by expansion count, never by the wall clock, so two runs
produce byte-identical output. Node 22 only, no dependencies.

## Run

```sh
node main.ts   # reads /input/<id>/level.txt, writes /output/<id>/solution.txt
```
