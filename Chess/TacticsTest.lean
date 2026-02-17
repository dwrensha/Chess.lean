import Chess.Tactics

/-- error:
It is Side.black's turn to move, try to use the `moveNotLose` tactic instead of `opponent_moveNotLose`
-/
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
  opponent_moveNotLose
  checkmateNotLose

/-
Timman-Short 1990
(from https://en.wikipedia.org/wiki/Smothered_mate)
-/
/--
error: It is Side.white's turn to move, try to use the `opponent_moveNotLose` tactic instead of `moveNotLose`
-/
#guard_msgs in
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
    moveNotLose "Nf7"
    moveNotLose "Nh6"

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
  checkmateNotLose
