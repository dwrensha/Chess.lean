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
  with_panel_widgets [ForcedWinWidget]
    move "Qb2"
    checkmate

theorem babsonNotStalemate :
    ForcedWin .white
      babsonTask := by
  with_panel_widgets [ForcedNotLoseWidget]
    move "a7"
    show ForcedWin _ _
    have := @ForcedWin.Opponent babsonTask

    opponent_move
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
    moveNotLose "a7"
    show ForcedNotLose .white _
    have := @ForcedWin .white
    --sorry -- valid move exists
    opponent_moveNotLose
    · moveNotLose "R×f4"
      checkmateNotLose
    · sorry
    sorry
    sorry
    · moveNotLose "R×f4"
      checkmateNotLose
    sorry
    sorry
    · moveNotLose "R×f4"
      checkmateNotLose
    · moveNotLose "R×f4"
      checkmateNotLose
    · moveNotLose "R×f4"
      checkmateNotLose
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
    moveNotLose "Qa2"
    checkmateNotLose

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
    moveNotLose "Rg2"
    opponent_moveNotLose
    all_goals
    · moveNotLose "Rh1"
      checkmateNotLose


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
    moveNotLose "e4"
    have : 2 + 2 = 4 := by exact rfl
    opponent_moveNotLose
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
    moveNotLose "Rb4"
    opponent_moveNotLose -- really, a stalemate!

theorem position7' :
    ForcedWin .white
      example_7 := by
  with_panel_widgets [ForcedNotLoseWidget]
    sorry


theorem position7₀ :
    ForcedNotLose .white
      example_7 := by
  with_panel_widgets [ForcedNotLoseWidget]
    moveNotLose "Rc4"
    opponent_moveNotLose
    moveNotLose "Rd5"
    opponent_moveNotLose
    moveNotLose "Rc1"
    checkmateNotLose

theorem position7₀_malikProof :
    ForcedNotLose .white
      example_7 := by
  with_panel_widgets [ForcedNotLoseWidget]
    moveNotLose "Kb3"
    opponent_moveNotLose
    unfold example_7
    moveNotLose "Ra1"
    checkmateNotLose
