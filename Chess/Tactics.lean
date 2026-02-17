import Chess.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.CasesM

section tactics

open Lean.Meta Lean.Elab.Tactic

syntax "moveNotLose " term : tactic

elab_rules : tactic | `(tactic| moveNotLose $t:term) => withMainContext do
  let g ← getMainGoal
  let goal_type ← whnfR (← g.getType)
  let .app (.app (.const ``ForcedNotLose _) side) pos := goal_type
    | throwError "moveNotLose' tactic expects ForcedNotLose goal"
  let posTurn ← whnfR (← mkAppM ``Position.turn #[pos])
  if not (← Lean.Meta.isExprDefEq side posTurn) then
    throwError "It is {side}'s turn to move, try to use the `opponent_moveNotLose` tactic instead of `moveNotLose`"
  let t ← Lean.Elab.Term.elabTerm t none
  let cm ← whnf (← mkAppM ``ChessMove.ofString #[t])
  let .app (.app (.const ``Option.some _) _) cm := cm
    | throwError "failed to parse move"

  let pos1 ← whnf (← mkAppM ``make_move #[pos, cm])
  let .app (.app (.const ``Option.some _) _) pos1 := pos1
    | throwError "failed to make move"
  let pos1 ← whnf pos1

  let pos_stx ← Lean.Elab.Term.exprToSyntax pos
  let mv_stx ← Lean.Elab.Term.exprToSyntax cm
  let pos1_stx ← Lean.Elab.Term.exprToSyntax pos1
  evalTactic (← `(tactic| refine ForcedNotLose.Self $pos_stx $mv_stx $pos1_stx (by decide) ?_))
  evalTactic (← `(tactic| dsimp [game_start, Side.other, Position.set]))

syntax "opponent_moveNotLose" : tactic

elab_rules : tactic | `(tactic| opponent_moveNotLose) => withMainContext do
  let g ← getMainGoal
  let goal_type ← whnfR (← g.getType)
  let .app (.app (.const ``ForcedNotLose _) side) pos := goal_type
    | throwError "'opponent_moveNotLose' tactic expects ForcedNotLose goal"
  let pos_stx ← Lean.Elab.Term.exprToSyntax pos
  let posTurn ← whnfR (← mkAppM ``Position.turn #[pos])
  if (← Lean.Meta.isExprDefEq side posTurn) then
    throwError "It is {side}'s turn to move, try to use the `moveNotLose` tactic instead of `opponent_moveNotLose`"
  evalTactic (← `(tactic| apply ForcedNotLose.Opponent $pos_stx))
  evalTactic (← `(tactic| rw [←List.forall_iff_forall_mem]))
  evalTactic (← `(tactic| dsimp [do_simple_move, Side.other, Position.set]))
  evalTactic (← `(tactic| try constructorm* (_ ∧ _)))
  for g in (←get).goals do
    g.setUserName .anonymous

syntax "checkmateNotLose" : tactic

elab_rules : tactic | `(tactic| checkmateNotLose) => withMainContext do
  let g ← getMainGoal
  let goal_type ← whnfR (← g.getType)
  let .app (.app (.const ``ForcedNotLose _) side) pos := goal_type
    | throwError "'checkmateNotLose' tactic expects ForcedNotLose goal"
  let posTurn ← whnfR (← mkAppM ``Position.turn #[pos])
  if (← Lean.Meta.isExprDefEq side posTurn) then
    throwError "It is {side}'s turn to move, try to use the `move` tactic instead to make a move that checkmates"

  let pos_stx ← Lean.Elab.Term.exprToSyntax pos
  evalTactic (← `(tactic| exact ForcedNotLose.Checkmate $pos_stx (by decide)))



syntax "move " term : tactic

elab_rules : tactic | `(tactic| move $t:term) => withMainContext do
  let g ← getMainGoal
  let goal_type ← whnfR (← g.getType)
  let .app (.app (.const ``ForcedWin _) side) pos := goal_type
    | throwError "'move' tactic expects ForcedWin goal"
  let posTurn ← whnfR (← mkAppM ``Position.turn #[pos])
  if not (← Lean.Meta.isExprDefEq side posTurn) then
    throwError "It is {side}'s turn to move, try to use the `opponent_move` tactic instead of `move`"
  let t ← Lean.Elab.Term.elabTerm t none
  let cm ← whnf (← mkAppM ``ChessMove.ofString #[t])
  let .app (.app (.const ``Option.some _) _) cm := cm
    | throwError "failed to parse move"

  let pos1 ← whnf (← mkAppM ``make_move #[pos, cm])
  let .app (.app (.const ``Option.some _) _) pos1 := pos1
    | throwError "failed to make move"
  let pos1 ← whnf pos1

  let pos_stx ← Lean.Elab.Term.exprToSyntax pos
  let mv_stx ← Lean.Elab.Term.exprToSyntax cm
  let pos1_stx ← Lean.Elab.Term.exprToSyntax pos1
  evalTactic (← `(tactic| refine ForcedWin.Self $pos_stx $mv_stx $pos1_stx (by decide) ?_))
  evalTactic (← `(tactic| dsimp [game_start, Side.other, Position.set]))

syntax "moveIn " term : tactic

elab_rules : tactic | `(tactic| moveIn $t:term) => withMainContext do
  let g ← getMainGoal
  let goal_type ← whnfR (← g.getType)
  let .app (.app (.app (.const ``ForcedWinIn _) n) side) pos := goal_type --thanks ChatGPT
    | throwError "'moveIn' tactic expects ForcedWinIn goal"
  let posTurn ← whnfR (← mkAppM ``Position.turn #[pos])
  if not (← Lean.Meta.isExprDefEq side posTurn) then
    throwError "It is {side}'s turn to move, try to use the `opponent_move` tactic instead of `move`"
  let t ← Lean.Elab.Term.elabTerm t none
  let cm ← whnf (← mkAppM ``ChessMove.ofString #[t])
  let .app (.app (.const ``Option.some _) _) cm := cm
    | throwError "failed to parse move"

  let pos1 ← whnf (← mkAppM ``make_move #[pos, cm])
  let .app (.app (.const ``Option.some _) _) pos1 := pos1
    | throwError "failed to make move"
  let pos1 ← whnf pos1
  let nPred ← mkAppM ``Nat.pred #[n]
  let nP ← Lean.Elab.Term.exprToSyntax nPred
  let pos_stx ← Lean.Elab.Term.exprToSyntax pos
  let mv_stx ← Lean.Elab.Term.exprToSyntax cm
  let pos1_stx ← Lean.Elab.Term.exprToSyntax pos1
  evalTactic (← `(tactic| refine ForcedWinIn.Self $nP $pos_stx $mv_stx $pos1_stx (by decide) ?_))
  evalTactic (← `(tactic| dsimp [game_start, Side.other, Position.set]))


syntax "opponent_move" : tactic

elab_rules : tactic | `(tactic| opponent_move) => withMainContext do
  let g ← getMainGoal
  let goal_type ← whnfR (← g.getType)
  let .app (.app (.const ``ForcedWin _) side) pos := goal_type
    | throwError "'opponent_move' tactic expects ForcedWin goal"
  let pos_stx ← Lean.Elab.Term.exprToSyntax pos
  let posTurn ← whnfR (← mkAppM ``Position.turn #[pos])
  if (← Lean.Meta.isExprDefEq side posTurn) then
    throwError "It is {side}'s turn to move, try to use the `move` tactic instead of `opponent_move`"
  evalTactic (← `(tactic| apply ForcedWin.Opponent $pos_stx))
  evalTactic (← `(tactic| rw [←List.forall_iff_forall_mem]))
  evalTactic (← `(tactic| dsimp [do_simple_move, Side.other, Position.set]))
  evalTactic (← `(tactic| try constructorm* (_ ∧ _)))
  for g in (←get).goals do
    g.setUserName .anonymous

syntax "opponent_moveIn" : tactic

elab_rules : tactic | `(tactic| opponent_moveIn) => withMainContext do
  let g ← getMainGoal
  let goal_type ← whnfR (← g.getType)
  let .app (.app (.app (.const ``ForcedWinIn _) n) side) pos := goal_type --thanks ChatGPT
    | throwError "'opponent_moveIn' tactic expects ForcedWinIn goal"
  let nP ← Lean.Elab.Term.exprToSyntax n

  let pos_stx ← Lean.Elab.Term.exprToSyntax pos
  let posTurn ← whnfR (← mkAppM ``Position.turn #[pos])
  if (← Lean.Meta.isExprDefEq side posTurn) then
    throwError "It is {side}'s turn to move, try to use the `move` tactic instead of `opponent_move`"
  evalTactic (← `(tactic| apply ForcedWinIn.Opponent $nP $pos_stx))
  evalTactic (← `(tactic| rw [←List.forall_iff_forall_mem]))
  evalTactic (← `(tactic| dsimp [do_simple_move, Side.other, Position.set]))
  evalTactic (← `(tactic| try constructorm* (_ ∧ _)))
  for g in (←get).goals do
    g.setUserName .anonymous


syntax "checkmate" : tactic

elab_rules : tactic | `(tactic| checkmate) => withMainContext do
  let g ← getMainGoal
  let goal_type ← whnfR (← g.getType)
  let .app (.app (.const ``ForcedWin _) side) pos := goal_type
    | throwError "'checkmate' tactic expects ForcedWin goal"
  let posTurn ← whnfR (← mkAppM ``Position.turn #[pos])
  if (← Lean.Meta.isExprDefEq side posTurn) then
    throwError "It is {side}'s turn to move, try to use the `move` tactic instead to make a move that checkmates"

  let pos_stx ← Lean.Elab.Term.exprToSyntax pos
  evalTactic (← `(tactic| exact ForcedWin.Checkmate $pos_stx (by decide)))

syntax "checkmateIn" : tactic

elab_rules : tactic | `(tactic| checkmateIn) => withMainContext do
  let g ← getMainGoal
  let goal_type ← whnfR (← g.getType)
  let .app (.app (.app (.const ``ForcedWinIn _) _) side) pos := goal_type --thanks ChatGPT
    | throwError "'checkmateIn' tactic expects ForcedWinIn goal"
  let posTurn ← whnfR (← mkAppM ``Position.turn #[pos])
  if (← Lean.Meta.isExprDefEq side posTurn) then
    throwError "It is {side}'s turn to move, try to use the `move` tactic instead to make a move that checkmates"

  -- if n.rawNatLit? ≠ some 0 then
  --   throwError "'checkmateIn' tactic requires n = 0 but received {n.rawNatLit?}"
  -- let nPred ← mkAppM ``Nat.pred #[n]
  -- let nP ← Lean.Elab.Term.exprToSyntax nPred


  let pos_stx ← Lean.Elab.Term.exprToSyntax pos
  evalTactic (← `(tactic| exact ForcedWinIn.Checkmate $pos_stx (by decide)))

end tactics
