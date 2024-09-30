import Chess.Basic
import Chess.Tactics
import Chess.Widgets
import Chess.NextMoveTactic


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
