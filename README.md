# Chess in Lean 4

## Usage

See [Examples.lean](./Chess/Examples.lean)
```lean
theorem morphy_mates_in_two :
    ForcedWin .white
      ╔════════════════╗
      ║░░▓▓░░▓▓♚]♝]░░♜]║
      ║♟]░░▓▓♞]▓▓♟]♟]♟]║
      ║░░▓▓░░▓▓♛]▓▓░░▓▓║
      ║▓▓░░▓▓░░♟]░░♗]░░║
      ║░░▓▓░░▓▓♙]▓▓░░▓▓║
      ║▓▓♕]▓▓░░▓▓░░▓▓░░║
      ║♙]♙]♙]▓▓░░♙]♙]♙]║
      ║▓▓░░♔}♖]▓▓░░▓▓░░║
      ╚════════════════╝ := by
  move "Qb8"
  opponent_move
  move "Rd8"
  checkmate
```

## Dependencies

If you plan to use the `get_next_move` tactic then you need a working python setup, including `python3-venv` and have a stockfish executable available.

### Linux
```bash
sudo apt-get install stockfish python3-venv
```

### Mac
```bash
brew install stockfish
```

### Windows
Download a suitable binary here: https://stockfishchess.org/download/, identify the stockfish binary and set the following environment variable:

```
STOCKFISH_BIN=[path to stockfish binary]
```
Originally developed as part of https://github.com/dwrensha/animate-lean-proofs.
