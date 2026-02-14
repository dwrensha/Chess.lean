import Chess.Tactics

/-- error: It is Side.black's turn to move, try to use the `move` tactic instead of `opponent_move` -/
#guard_msgs in
theorem black_wins_back_rank :
    ForcedNotLose .black
      ╔════════════════╗
      ║░░▓▓░░▓▓♜]▓▓♚}▓▓║
      ║♟]░░▓▓░░▓▓♟]♟]♟]║
      ║░░▓▓░░▓▓░░▓▓░░▓▓║
      ║▓▓░░▓▓░░▓▓░░▓▓░░║
      ║░░▓▓░░▓▓░░▓▓░░▓▓║
      ║▓▓░░▓▓░░▓▓░░▓▓░░║
      ║♙]♙]♙]▓▓░░♙]♙]♙]║
      ║▓▓░░▓▓░░▓▓░░♔]░░║
      ╚════════════════╝ := by
  opponent_move
  checkmate

/-- error: It is Side.white's turn to move, try to use the `opponent_move` tactic instead of `move` -/
#guard_msgs in
/--
Timman-Short 1990
(from https://en.wikipedia.org/wiki/Smothered_mate)
-/
theorem smothered_mate :
    ForcedNotLose .white
      ╔════════════════╗
      ║▓▓░░▓▓░░♜]░░▓▓♚]║
      ║♟]▓▓♟]♖]♙]▓▓♟]♟]║
      ║▓▓░░♟]░░▓▓░░▓▓░░║
      ║░░▓▓░░▓▓░░♟]♘]▓▓║
      ║▓▓░░♕]░░▓▓░░♞]░░║
      ║♛]▓▓░░▓▓░░▓▓♙]▓▓║
      ║♙]░░▓▓░░♙]♙]▓▓♙]║
      ║░░▓▓░░▓▓░░▓▓♔}▓▓║
      ╚════════════════╝ := by
    move "Nf7"
    move "Nh6"

/-- error: It is Side.white's turn to move, try to use the `move` tactic instead to make a move that checkmates -/
#guard_msgs in
theorem white_wins_promotion_back_rank :
    ForcedNotLose .white
      ╔════════════════╗
      ║░░▓▓░░▓▓░░▓▓♚]▓▓║
      ║♟]░░♙]░░▓▓♟]♟]♟]║
      ║░░▓▓░░▓▓░░▓▓░░▓▓║
      ║▓▓░░▓▓░░▓▓░░▓▓░░║
      ║░░▓▓░░▓▓░░▓▓░░▓▓║
      ║▓▓░░▓▓░░▓▓░░▓▓░░║
      ║♙]♙]░░▓▓░░♙]♙]♙]║
      ║▓▓░░▓▓░░▓▓░░♔}░░║
      ╚════════════════╝ := by
  checkmate
