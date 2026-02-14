import Chess.Basic
import Chess.Tactics
import Chess.Widgets
import Chess.NextMoveTactic

def example_5 :=
    ╔════════════════╗
    ║▓▓░░▓▓░░▓▓░░▓▓░░║
    ║░░▓▓░░▓▓░░▓▓░░▓▓║
    ║▓▓░░▓▓░░▓▓░░▓▓░░║
    ║░░▓▓░░▓▓░░▓▓░░▓▓║
    ║▓▓░░▓▓░░▓▓░░▓▓░░║
    ║♔}♕]░░▓▓░░▓▓░░▓▓║
    ║▓▓░░▓▓░░▓▓░░▓▓░░║
    ║♚]▓▓░░▓▓░░▓▓░░▓▓║
    ╚════════════════╝

def babsonTask :=
      ╔════════════════╗
      ║♗]♛]░░♗]░░♔}░░▓▓║
      ║▓▓░░▓▓♙]♟]♘]▓▓░░║
      ║♙]▓▓░░▓▓♙]♟]░░▓▓║
      ║♙]░░♟]░░▓▓♙]▓▓░░║
      ║░░▓▓♙]♚]░░♝]░░♖]║
      ║▓▓♟]▓▓░░▓▓░░▓▓░░║
      ║♟]♘]░░♙]░░♙]░░▓▓║
      ║♕]♖]▓▓░░▓▓░░▓▓░░║
      ╚════════════════╝

set_option linter.hashCommand false
#widget ChessPositionWidget with { position? := example_5 : ChessPositionWidgetProps }

theorem forcedWinDemo :
    ForcedWin .white
      example_5 := by
  with_panel_widgets [ForcedNotLoseWidget]
    moveNotStalemate "Qb2"
    checkmateNotStalemate
-- TODO: rename "checkmate" to "checkmateNotLose" and "checkmateNotStalemate" to "checkmate"


theorem babsonNotStalemate :
    ForcedWin .white
      babsonTask := by
  with_panel_widgets [ForcedNotLoseWidget]
    moveNotStalemate "a7"
    show ForcedWin _ _
    have := @ForcedWin.Opponent babsonTask

    opponent_moveNotStalemate
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    · exact ne_of_beq_false rfl

theorem babson :
    ForcedNotLose .white
      babsonTask := by
  with_panel_widgets [ForcedNotLoseWidget]
    move "a7"
    show ForcedNotLose .white _
    have := @ForcedWin .white
    --sorry -- valid move exists
    opponent_move
    · move "R×f4"
      checkmate
    · sorry
    sorry
    sorry
    · move "R×f4"
      checkmate
    sorry
    sorry
    · move "R×f4"
      checkmate
    · move "R×f4"
      checkmate
    · move "R×f4"
      checkmate
    sorry
    sorry
    sorry
    sorry
    sorry


set_option maxRecDepth 1000
theorem position_with_218_moves :
    ForcedNotLose .white
      example_5 := by
  with_panel_widgets [ForcedNotLoseWidget]
    move "Qa2"
    checkmate

def example_6 :=
    ╔════════════════╗
    ║▓▓░░▓▓░░▓▓░░▓▓░░║
    ║░░▓▓░░▓▓░░▓▓░░▓▓║
    ║▓▓░░▓▓░░▓▓░░▓▓░░║
    ║░░▓▓░░▓▓░░▓▓░░▓▓║
    ║▓▓░░▓▓░░▓▓░░♖]░░║
    ║♔}▓▓░░▓▓░░▓▓░░♖]║
    ║▓▓░░▓▓░░▓▓░░▓▓░░║
    ║▓▓♚]░░▓▓░░▓▓░░▓▓║
    ╚════════════════╝

set_option maxRecDepth 1000
theorem position :
    ForcedNotLose .white
      example_6 := by
  with_panel_widgets [ForcedNotLoseWidget]
    move "Rg2"
    opponent_move
    all_goals
    · move "Rh1"
      checkmate


def example_7 :=
    ╔════════════════╗
    ║▓▓░░▓▓░░▓▓░░▓▓░░║
    ║░░▓▓░░▓▓░░▓▓░░▓▓║
    ║▓▓░░▓▓░░▓▓░░▓▓░░║
    ║♖]▓▓░░▓▓░░▓▓░░▓▓║
    ║♖]░░▓▓░░▓▓░░▓▓░░║
    ║♔}▓▓░░▓▓░░▓▓░░▓▓║
    ║▓▓░░▓▓░░▓▓░░▓▓░░║
    ║♚]▓▓░░▓▓░░▓▓░░▓▓║
    ╚════════════════╝
#check example_7
def chatGPT_startingPosition :=
      ╔════════════════╗
      ║♜]♞]♝]♛]♚]♝]♞]♜]║
      ║♟]♟]♟]♟]♟]♟]♟]♟]║
      ║░░▓▓░░▓▓░░▓▓░░▓▓║
      ║▓▓░░▓▓░░▓▓░░▓▓░░║
      ║░░▓▓░░▓▓░░▓▓░░▓▓║
      ║▓▓░░▓▓░░▓▓░░▓▓░░║
      ║♙]♙]♙]♙]♙]♙]♙]♙]║
      ║♖]♘]♗]♕]♔}♗]♘]♖]║
      ╚════════════════╝

def canCastle :=
      ╔════════════════╗
      ║♜]░░♝]♛]♚]♝]░░♜]║
      ║♟]♟]♟]♟]♟]♟]♟]♟]║
      ║░░♞]░░▓▓░░♞]░░▓▓║
      ║▓▓░░▓▓░░▓▓░░▓▓░░║
      ║░░▓▓░░▓▓░░▓▓░░▓▓║
      ║▓▓♘]▓▓░░▓▓♘]▓▓░░║
      ║♙]♙]♙]♙]♙]♙]♙]♙]║
      ║♖]░░♗]♕]♔}░░░░♖]║
      ╚════════════════╝

set_option maxRecDepth 1000
theorem white_can_force_win_or_draw :
    ForcedWin .white
      canCastle := by
  with_panel_widgets [ForcedNotLoseWidget]
    unfold canCastle
    -- move "O-O"
    have : 2 + 2 = 4 := by exact rfl
    sorry


theorem white_can_force_win_or_draw' :
    ForcedNotLose .white
      chatGPT_startingPosition := by
  with_panel_widgets [ForcedNotLoseWidget]
    move "e4"
    have : 2 + 2 = 4 := by exact rfl
    opponent_move
    ·
      sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry


set_option maxRecDepth 1000
theorem position7 :
    ForcedNotLose .white
      example_7 := by
  with_panel_widgets [ForcedNotLoseWidget]
    move "Rb4"
    opponent_move -- really, a stalemate!

theorem position7' :
    ForcedWin .white
      example_7 := by
  with_panel_widgets [ForcedNotLoseWidget]
    sorry


theorem position7₀ :
    ForcedNotLose .white
      example_7 := by
  with_panel_widgets [ForcedNotLoseWidget]
    move "Rc4"
    opponent_move
    move "Rd5"
    opponent_move
    move "Rc1"
    checkmate

theorem position7₀_malikProof :
    ForcedNotLose .white
      example_7 := by
  with_panel_widgets [ForcedNotLoseWidget]
    move "Kb3"
    opponent_move
    unfold example_7
    move "Ra1"
    checkmate
