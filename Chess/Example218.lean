import Chess.Basic
import Chess.Tactics
import Chess.Widgets
import Chess.NextMoveTactic

-- https://lichess.org/study/PLtuv3v5/zWPNxbSA
def example_5 :=
    ╔════════════════╗
    ║▓▓░░▓▓♕]▓▓░░▓▓░░║
    ║♔}♕]░░▓▓░░▓▓♕]▓▓║
    ║▓▓░░▓▓░░♕]░░▓▓░░║
    ║♗]▓▓♕]▓▓░░▓▓░░♕]║
    ║♗]░░▓▓░░▓▓♕]▓▓░░║
    ║♘]▓▓░░♕]░░▓▓░░▓▓║
    ║♘]♖]▓▓░░▓▓░░♕]░░║
    ║♚]♝]░░▓▓♖]▓▓░░▓▓║
    ╚════════════════╝

set_option linter.hashCommand false
#widget ChessPositionWidget with { position? := example_5 : ChessPositionWidgetProps }


set_option maxRecDepth 1000
theorem position_with_218_moves :
    ForcedNotLose .black
      example_5 := by
  with_panel_widgets [ForcedNotLoseWidget]
    opponent_moveNotLose -- at this point 218 goals are opened
    all_goals sorry

theorem position_with_218_moves₀ :
    ForcedNotLose .white
      example_5 := by
  with_panel_widgets [ForcedNotLoseWidget]
    moveNotLose "Qc2"
    opponent_moveNotLose
