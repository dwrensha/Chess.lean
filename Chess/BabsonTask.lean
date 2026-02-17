import Chess.Basic
import Chess.Tactics
import Chess.Widgets
import Chess.NextMoveTactic

theorem extracted_4 :
  valid_moves
          ╔════════════════╗
          ║♗]░░▓▓♛]▓▓░░▓▓░░║
          ║♙]▓▓░░♙]♟]♘]♔]▓▓║
          ║▓▓░░▓▓░░♙]♟]▓▓░░║
          ║♙]▓▓♟]▓▓░░♙]░░▓▓║
          ║▓▓░░♙]♚}▓▓♝]▓▓♖]║
          ║░░♟]░░▓▓░░▓▓░░▓▓║
          ║♟]♘]▓▓♙]▓▓♙]▓▓░░║
          ║♕]♖]░░▓▓░░▓▓░░▓▓║
          ╚════════════════╝ ≠
    ∅ := by
    exact ne_of_beq_false rfl

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

theorem extracted_1 :
  ForcedWin
    (match
      match
        match
          match babsonTask.turn with
          | Side.white => Side.black
          | Side.black => Side.white with
        | Side.white => Side.black
        | Side.black => Side.white with
      | Side.white => Side.black
      | Side.black => Side.white with
    | Side.white => Side.black
    | Side.black => Side.white)
        ╔════════════════╗
        ║♗]░░▓▓░░▓▓░░♛]░░║
        ║♙]▓▓░░♙]♟]♘]♔}▓▓║
        ║▓▓░░▓▓░░♙]♟]▓▓░░║
        ║♙]▓▓♟]▓▓░░♙]░░▓▓║
        ║▓▓░░♙]♚]▓▓♝]▓▓♖]║
        ║░░♟]░░▓▓░░▓▓░░▓▓║
        ║♟]♘]▓▓♙]▓▓♙]▓▓░░║
        ║♕]♖]░░▓▓░░▓▓░░▓▓║
        ╚════════════════╝ := by
        move "K×g8"
        opponent_move
        · simp;move "Pd8=Q";checkmate
        · simp;move "Pd8=Q";checkmate
        · simp;move "Pd8=Q";checkmate
        · simp;move "Pd8=Q";checkmate
        · decide

theorem extracted_2 :
  ForcedWin
    (match
      match
        match
          match babsonTask.turn with
          | Side.white => Side.black
          | Side.black => Side.white with
        | Side.white => Side.black
        | Side.black => Side.white with
      | Side.white => Side.black
      | Side.black => Side.white with
    | Side.white => Side.black
    | Side.black => Side.white)
        ╔════════════════╗
        ║♗]░░▓▓░░▓▓░░▓▓♛]║
        ║♙]▓▓░░♙]♟]♘]♔}▓▓║
        ║▓▓░░▓▓░░♙]♟]▓▓░░║
        ║♙]▓▓♟]▓▓░░♙]░░▓▓║
        ║▓▓░░♙]♚]▓▓♝]▓▓♖]║
        ║░░♟]░░▓▓░░▓▓░░▓▓║
        ║♟]♘]▓▓♙]▓▓♙]▓▓░░║
        ║♕]♖]░░▓▓░░▓▓░░▓▓║
        ╚════════════════╝ := by
        move "K×h8"
        opponent_move
        · simp;move "Pd8=Q";checkmate
        · simp;move "Pd8=Q";checkmate
        · simp;move "Pd8=Q";checkmate
        · simp;move "Pd8=Q";checkmate
        · exact ne_of_beq_false rfl

theorem extracted_3 :
  ForcedWin
    (match
      match
        match
          match babsonTask.turn with
          | Side.white => Side.black
          | Side.black => Side.white with
        | Side.white => Side.black
        | Side.black => Side.white with
      | Side.white => Side.black
      | Side.black => Side.white with
    | Side.white => Side.black
    | Side.black => Side.white)
        ╔════════════════╗
        ║♗]░░▓▓░░▓▓♛]▓▓░░║
        ║♙]▓▓░░♙]♟]♘]♔}▓▓║
        ║▓▓░░▓▓░░♙]♟]▓▓░░║
        ║♙]▓▓♟]▓▓░░♙]░░▓▓║
        ║▓▓░░♙]♚]▓▓♝]▓▓♖]║
        ║░░♟]░░▓▓░░▓▓░░▓▓║
        ║♟]♘]▓▓♙]▓▓♙]▓▓░░║
        ║♕]♖]░░▓▓░░▓▓░░▓▓║
        ╚════════════════╝ := by
      with_panel_widgets [ForcedWinWidget]
        move "K×f8"
        opponent_move
        all_goals
            try (simp;move "Pd8=Q";checkmate)
        · exact ne_of_beq_false rfl


set_option maxHeartbeats 0
theorem extracted_4' :
  ForcedWin
    (match
      match babsonTask.turn with
      | Side.white => Side.black
      | Side.black => Side.white with
    | Side.white => Side.black
    | Side.black => Side.white)
        ╔════════════════╗
        ║♗]░░▓▓♛]▓▓♔}▓▓░░║
        ║♙]▓▓░░♙]♟]♘]░░▓▓║
        ║▓▓░░▓▓░░♙]♟]▓▓░░║
        ║♙]▓▓♟]▓▓░░♙]░░▓▓║
        ║▓▓░░♙]♚]▓▓♝]▓▓♖]║
        ║░░♟]░░▓▓░░▓▓░░▓▓║
        ║♟]♘]▓▓♙]▓▓♙]▓▓░░║
        ║♕]♖]░░▓▓░░▓▓░░▓▓║
        ╚════════════════╝ := by
    with_panel_widgets [ForcedWinWidget]
      move "Kg7"
      simp
      opponent_move
      · simp
        move "d8=Q"
        opponent_move
        all_goals try (move "R×f4";checkmate)
        exact ne_of_beq_false rfl
        -- goal 1
      · simp;move "R×f4"
        checkmate
        -- goal 2
      · simp;move "R×f4"
        checkmate
        -- goal 3
      · simp;move "R×f4"
        checkmate
        -- goal 4
      · simp;exact extracted_3 -- goal 5
      · simp;exact extracted_1 -- goal 6
      · simp;exact extracted_2 -- goal 7
      · simp;move "R×f4";checkmate -- goal 8
      · simp;move "R×f4";checkmate -- goal 9
      · simp
        move "d8=Q"
        opponent_move
        all_goals try (move "R×f4";checkmate)
        exact ne_of_beq_false rfl -- goal 10
      · simp
        move "d8=Q"
        opponent_move
        all_goals try (move "R×f4";checkmate)
        simp
        move "Qd3"
        checkmate
        exact ne_of_beq_false rfl -- goal 11
      · simp;move "R×f4";opponent_move
        move "R×e4";checkmate
        exact ne_of_beq_false rfl -- goal 12
      · simp;move "R×f4";checkmate -- goal 13
      · simp;move "R×f4";opponent_move
        move "R×e4";checkmate
        exact ne_of_beq_false rfl -- goal 14
      · simp;move "R×f4";checkmate -- goal 15
      sorry








    --   · have := extracted_4 --exact ne_of_beq_false rfl
        -- convert this
    --   · sorry

-- set_option maxHeartbeats 0
-- theorem babsonNotStalemate :
--     ForcedWin .white
--       babsonTask := by
--   with_panel_widgets [ForcedWinWidget]
--     move "a7"
--     opponent_move
--     · move "R×f4"
--       checkmate
--     · simp;move "B×c7"
--       opponent_move

--       · simp;sorry
--       sorry
--       sorry
--       sorry
--       sorry
--     · simp;sorry
--     · simp;sorry
--     · move "R×f4"
--       checkmate
--     · exact extracted_4
--     · simp;sorry
--     · move "R×f4"
--       checkmate
--     · move "R×f4"
--       checkmate
--     · move "R×f4"
--       checkmate
--     · simp;sorry
--     · simp;sorry
--     · simp;sorry
--     · simp;sorry
--     · simp;sorry
--     · exact ne_of_beq_false rfl
