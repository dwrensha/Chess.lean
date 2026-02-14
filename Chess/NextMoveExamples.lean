import Chess.Basic
import Chess.Tactics
import Chess.Widgets
import Chess.NextMoveTactic


theorem smothered_mate' :
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
    guess_next_move
    opponent_move
    guess_next_move
    opponent_move
    guess_next_move
    opponent_move
    guess_next_move
    checkmate
