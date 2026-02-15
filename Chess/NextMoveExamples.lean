import Chess.Basic
import Chess.Tactics
import Chess.Widgets
import Chess.NextMoveTactic


theorem smothered_mate'NotLose :
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
  with_panel_widgets [ForcedNotLoseWidget]
    guess_next_moveNotLose
    opponent_moveNotLose
    guess_next_moveNotLose
    opponent_moveNotLose
    guess_next_moveNotLose
    opponent_moveNotLose
    guess_next_moveNotLose
    checkmateNotLose

theorem smothered_mate' :
    ForcedWin .white
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
  with_panel_widgets [ForcedWinWidget]
    guess_next_move
    opponent_move
    guess_next_move
    opponent_move
    guess_next_move
    opponent_move
    guess_next_move
    checkmate
    all_goals
      exact ne_of_beq_false rfl
