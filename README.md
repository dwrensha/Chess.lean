# Chess in Lean 4

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

Originally developed as part of https://github.com/dwrensha/animate-lean-proofs.
