import Chess.Basic
import Chess.Tactics
import Chess.Widgets
import Chess.NextMoveTactic


lemma practice :
  ForcedWin .white (by
    apply Position.mk
    · unfold Squares
      exact [
        [some (Piece.rook, .white),none,none,none,none,none,none,none],
        [some (Piece.rook, .white),none,none,none,none,none,none,none],
        [some (Piece.rook, .white),none,none,none,none,none,none,none],
        [some (Piece.rook, .white),none,none,none,none,none,none,none],
        [some (Piece.rook, .white),none,none,none,none,none,none,none],
        [some (Piece.rook, .white),none,none,none,none,none,none,none],
        [some (Piece.rook, .white),none,none,none,none,none,none,none],
        [some (Piece.rook, .white),none,none,none,none,none,none,none]]
    · exact .white
    · apply some
      exact {row :=0, col := 0}) := by
  with_panel_widgets [ForcedWinWidget]
      sorry

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

theorem forcedNotLoseDemo :
    ForcedNotLose .white
      example_5 := by
  with_panel_widgets [ForcedNotLoseWidget]
    moveNotLose "Qb2"
    checkmateNotLose

theorem extracted_1 :
  ForcedNotLose
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
        moveNotLose "K×g8"
        opponent_moveNotLose
        all_goals
          simp;moveNotLose "Pd8=Q";checkmateNotLose


theorem extracted_2 :
  ForcedNotLose
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
        moveNotLose "K×h8"
        opponent_moveNotLose
        all_goals
          simp;moveNotLose "Pd8=Q";checkmateNotLose


theorem extracted_3 :
  ForcedNotLose
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
      with_panel_widgets [ForcedNotLoseWidget]
        moveNotLose "K×f8"
        opponent_moveNotLose
        all_goals
            try (simp;moveNotLose "Pd8=Q";checkmateNotLose)




set_option maxHeartbeats 0
theorem extracted_4' :
  ForcedNotLose
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
    with_panel_widgets [ForcedNotLoseWidget]
      moveNotLose "Kg7"
      simp
      opponent_moveNotLose
      all_goals try (moveNotLose "R×f4";checkmateNotLose)
      all_goals try simp
      all_goals try
        moveNotLose "d8=Q"
        opponent_moveNotLose
        all_goals try (moveNotLose "R×f4";checkmateNotLose)
      · exact extracted_3
      · exact extracted_1
      · exact extracted_2
      simp;sorry
      sorry
      sorry

      -- · simp
      --   moveNotLose "d8=Q"
      --   opponent_moveNotLose
      --   all_goals try (moveNotLose "R×f4";checkmateNotLose)
      -- · simp;moveNotLose "R×f4"
      --   checkmateNotLose
      -- · simp;moveNotLose "R×f4"
      --   checkmateNotLose
      -- · simp;moveNotLose "R×f4"
      --   checkmateNotLose

      -- · simp;exact extracted_3
      -- · simp;exact extracted_1
      -- · simp;exact extracted_2
      -- · simp;moveNotLose "R×f4";checkmateNotLose
      -- · simp;moveNotLose "R×f4";checkmateNotLose
      -- · simp
      --   moveNotLose "d8=Q"
      --   -- moveNotLose "b8=Q" -- failed to make moveNotLose
      --   -- moveNotLose "P×b8=Q" -- failed to make moveNotLose
      --   opponent_moveNotLose
      --   all_goals try (moveNotLose "R×f4";checkmateNotLose)
      -- · simp
      --   moveNotLose "d8=Q"
      --   opponent_moveNotLose
      --   all_goals try (moveNotLose "R×f4";checkmateNotLose)
      --   simp
      --   moveNotLose "Qd3"
      --   checkmateNotLose
      -- · simp;moveNotLose "R×f4";opponent_moveNotLose
      --   moveNotLose "R×e4";checkmateNotLose
      -- · simp;moveNotLose "R×f4";checkmateNotLose
      -- · simp;moveNotLose "R×f4";opponent_moveNotLose
      --   moveNotLose "R×e4";checkmateNotLose
      -- · simp;moveNotLose "R×f4";checkmateNotLose
