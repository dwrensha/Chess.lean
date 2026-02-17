import Chess.Basic
import Chess.Tactics
import Chess.Widgets
import Chess.NextMoveTactic
import Mathlib.Tactic.FinCases
-- import Mathlib.Tactic.FunCases

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
  with_panel_widgets [ForcedWinWidget]
    move "a7"
    opponent_move
    · move "R×f4"
      checkmate
    · move "B×c7"
      opponent_move

      sorry
      sorry
      sorry
      sorry
      sorry
    · sorry
    · sorry
    · move "R×f4"
      checkmate
    · sorry
    · sorry
    · move "R×f4"
      checkmate
    · move "R×f4"
      checkmate
    · move "R×f4"
      checkmate
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
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
    · moveNotLose "B×c7"
      opponent_moveNotLose
      all_goals
        moveNotLose "Q×b1"
        opponent_moveNotLose
        -- stalemate!
    · sorry
    · sorry
    · moveNotLose "R×f4"
      checkmateNotLose
    · sorry
    · sorry
    · moveNotLose "R×f4"
      checkmateNotLose
    · moveNotLose "R×f4"
      checkmateNotLose
    · moveNotLose "R×f4"
      checkmateNotLose
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry


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

theorem position' :
    ForcedWinIn 2 .white
      example_6 := by
  with_panel_widgets [ForcedNotLoseWidget]
    moveIn "Rg2"
    opponent_moveIn
    · moveIn "Rh1"
      checkmateIn
    · moveIn "Rh1"
      checkmateIn
    · exact ne_of_beq_false rfl

theorem position'' :
    ¬ ForcedNotLose' .white
      example_6 := by
  intro hc
  cases hc with
  | Checkmate h g => sorry
  | Opponent h g => sorry
  | Self h m p1 g i => sorry

theorem position''' :
    ¬ IsCheckmate example_6 := by
  decide

set_option maxHeartbeats 0
-- set_option maxRecDepth 10000000
-- theorem babsonProof₀ :
--     ¬ forcedWinIn 0 .white babsonTask := by -- DONE
--   decide

-- theorem babsonProof₁ :
--     ¬ forcedWinIn 1 .white babsonTask := by -- DONE
--   decide

-- theorem babsonProof₂ :
--     ¬ forcedWinIn 2 .white babsonTask := by -- DONE
--   native_decide

-- theorem babsonProof₃ :
--     ¬ forcedWinIn 3 .white babsonTask := by -- DONE
--   native_decide

/-
tactic 'native_decide' evaluated that the proposition
  forcedWinIn 4 Side.white babsonTask = true
is false
-/
-- theorem babsonProof₄ :
--     ¬ forcedWinIn 4 .white babsonTask := by -- DONE
--   native_decide


-- theorem position'''' :
--     ¬ forcedWinIn 2 .white example_6 := by
-- --TODO: make the widgets work with `forcedWinIn`
--   decide

-- theorem position'''' :
--     forcedWinIn 3 .white example_6 := by -- seems we have to count both players' of moves!
-- --TODO: make the widgets work with `forcedWinIn`
--   decide

-- theorem babsonProof₄ :
--     ¬ forcedWinIn 5 .white babsonTask := by
--   native_decide

theorem forcedWinIn_iff_ForcedWinIn (p : Position) (s : Side) (n : Nat) :
    forcedWinIn n s p ↔ ForcedWinIn n s p := by
    constructor
    · induction n with
    | zero =>
        intro h
        -- apply ForcedWinIn.Checkmate
        sorry
    | succ n _ => sorry
    · induction n with
    | zero =>
        intro h
        simp [forcedWinIn]

        sorry
    | succ n _ => sorry


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

theorem forcedWinDemo₁ :
    ForcedWinIn 1 .white
      example_5 := by
  with_panel_widgets [ForcedWinWidget]
    moveIn "Qb2"
    checkmateIn
-- TODO: Write a `ForcedWinIn 2` example.



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
