module

import Init.Core
import Init.Data.List.Control
import Init.Data.List.TakeDrop
import Purelib.Data.List.Append
import Purelib.Data.List.Reverse

/-!
Bounded parallel evaluation of independent finite computations.  Join the
entire group before returning; callers retain the order of all results.
Lean's core `Task` definitions prove exact equality with sequential evaluation,
including cached witnesses.  No runtime decision is used as proof evidence.
Dedicated workers avoid underfilling Lean's lazily grown shared pool when a
larger group follows a smaller one.  These helpers are for coarse independent
jobs: callers must join a group before starting another, and must not launch
nested parallel groups inside its jobs.  They bound each group's workers, not
the concurrency of unrelated callers or the CPU allocation of the process.
-/

namespace Purelib.Data.Task.Parallel

@[expose] public section

/-- Evaluate two independent jobs on dedicated tasks and join their results in input order.

Both jobs are joined before the pair is returned. The core task equations retain the exact sequential values, including
dependent witnesses; this bounds workers for this group only. -/
def two {α : Type u} {β : Type v} (first : Unit → α) (second : Unit → β) : α × β :=
  let one := Task.spawn first (prio := .dedicated)
  let two := Task.spawn second (prio := .dedicated)
  (one.bind (fun a => two.map (fun b => (a, b)) (sync := true)) (sync := true)).get

/-- The two joined results equal the exact sequential evaluations in input order. -/
theorem two_eq {α : Type u} {β : Type v} (first : Unit → α) (second : Unit → β) :
    two first second = (first (), second ()) := rfl

/-- Evaluate four independent jobs on dedicated tasks and join their results in input order.

The nested synchronous joins finish the whole group before returning its tuple. Jobs must not create nested parallel
groups; the helper bounds this group's workers, not unrelated callers. -/
def four {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
    (first : Unit → α) (second : Unit → β) (third : Unit → γ) (fourth : Unit → δ) :
    α × β × γ × δ :=
  let one := Task.spawn first (prio := .dedicated)
  let two := Task.spawn second (prio := .dedicated)
  let three := Task.spawn third (prio := .dedicated)
  let four := Task.spawn fourth (prio := .dedicated)
  (one.bind (fun a =>
    two.bind (fun b =>
      three.bind (fun c =>
        four.map (fun d => (a, b, c, d)) (sync := true)) (sync := true))
      (sync := true)) (sync := true)).get

/-- The four joined results equal the exact sequential evaluations in input order. -/
theorem four_eq {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
    (first : Unit → α) (second : Unit → β) (third : Unit → γ) (fourth : Unit → δ) :
    four first second third fourth = (first (), second (), third (), fourth ()) := rfl

end

open Purelib.Data.List

/-- An exception traversal retains its supplied reversed prefix before the newly mapped values.

The original accumulator is stored in reverse order. A successful suffix is
appended to that same prefix; any scalar failure keeps the original error.
-/
private theorem mapM_loop_acc {Alpha : Type u} {Beta : Type v} {Error : Type w}
    (function : Alpha → Except Error Beta) (values : List Alpha) (accumulator : List Beta) :
    List.mapM.loop function values accumulator =
      match List.mapM.loop function values [] with
      | .error failure => Except.error failure
      | .ok mapped => .ok (accumulator.reverse ++ mapped) := by
  induction values generalizing accumulator with
  | nil =>
      change Except.ok accumulator.reverse = Except.ok (accumulator.reverse ++ [])
      rewrite [Append.append_nil]
      rfl
  | cons head tail ih =>
      have step (retained : List Beta) :
          List.mapM.loop function (head :: tail) retained = (do
            let value ← function head
            List.mapM.loop function tail (value :: retained)) := rfl
      rewrite [step accumulator, step []]
      cases decoded : function head with
      | error failure => rfl
      | ok value =>
          change List.mapM.loop function tail (value :: accumulator) =
            match List.mapM.loop function tail [value] with
            | .error failure => Except.error failure
            | .ok mapped => .ok (accumulator.reverse ++ mapped)
          rewrite [ih (value :: accumulator), ih [value]]
          cases rest : List.mapM.loop function tail [] with
          | error failure => rfl
          | ok mapped =>
              change Except.ok ((value :: accumulator).reverse ++ mapped) =
                Except.ok (accumulator.reverse ++ ([value].reverse ++ mapped))
              rewrite [Reverse.reverse_cons]
              exact congrArg Except.ok (Append.append_assoc accumulator.reverse [value] mapped)

/-- An exception traversal of a concatenation continues from the complete original left prefix.

The right traversal receives the actual completed left values as its reversed
accumulator. A failed left traversal returns its error before that continuation.
-/
private theorem mapM_loop_append {Alpha : Type u} {Beta : Type v} {Error : Type w}
    (function : Alpha → Except Error Beta) (first second : List Alpha) (accumulator : List Beta) :
    List.mapM.loop function (first ++ second) accumulator =
      match List.mapM.loop function first accumulator with
      | .error failure => Except.error failure
      | .ok mapped => List.mapM.loop function second mapped.reverse := by
  induction first generalizing accumulator with
  | nil =>
      change List.mapM.loop function second accumulator =
        List.mapM.loop function second accumulator.reverse.reverse
      rewrite [Reverse.reverse_reverse]
      rfl
  | cons head tail ih =>
      have step (remaining : List Alpha) (retained : List Beta) :
          List.mapM.loop function (head :: remaining) retained = (do
            let value ← function head
            List.mapM.loop function remaining (value :: retained)) := rfl
      change List.mapM.loop function (head :: (tail ++ second)) accumulator = _
      rewrite [step (tail ++ second) accumulator, step tail accumulator]
      cases decoded : function head with
      | error failure => rfl
      | ok value => exact ih (value :: accumulator)

/-- Combining two ordered exception traversals retains the complete original concatenated result.

The successful lists keep their original order and repeated occurrences. A
failed half retains the original first error of the concatenated traversal.
-/
private theorem mapM_append {Alpha : Type u} {Beta : Type v} {Error : Type w}
    (function : Alpha → Except Error Beta) (first second : List Alpha) :
    (first ++ second).mapM function = (do
      let left ← first.mapM function
      let right ← second.mapM function
      return left ++ right) := by
  have start (values : List Alpha) :
      values.mapM function = List.mapM.loop function values [] := rfl
  rewrite [start (first ++ second), start first, start second]
  rewrite [mapM_loop_append]
  cases firstResult : List.mapM.loop function first [] with
  | error failure => rfl
  | ok left =>
      change List.mapM.loop function second left.reverse = (do
        let right ← List.mapM.loop function second []
        return left ++ right)
      rewrite [mapM_loop_acc, Reverse.reverse_reverse]
      cases secondResult : List.mapM.loop function second [] with
      | error failure => rfl
      | ok right => rfl

/-- Map independent scalar jobs in two joined halves, retaining the original ordered exception result.

Empty and singleton lists use the sequential traversal. Larger lists retain
two contiguous halves and join the complete bounded task group before selecting
the original first error or concatenating its exact values. Scalar jobs must
not start nested parallel groups.
-/
public def mapExcept {Alpha : Type u} {Beta : Type v} {Error : Type w}
    (function : Alpha → Except Error Beta) (values : List Alpha) : Except Error (List Beta) :=
  let middle := values.length / 2
  if middle = 0 then values.mapM function
  else
    let results := two (fun _ => (values.take middle).mapM function)
      (fun _ => (values.drop middle).mapM function)
    do
      let first ← results.1
      let second ← results.2
      return first ++ second

/-- Parallel exception mapping preserves every exact ordered value and the original first typed error.

The retained take/drop decomposition supplies the same complete input list.
Joining the two results changes neither its mapped data nor its error witness.
-/
public theorem mapExcept_eq {Alpha : Type u} {Beta : Type v} {Error : Type w}
    (function : Alpha → Except Error Beta) (values : List Alpha) :
    mapExcept function values = values.mapM function := by
  unfold mapExcept
  dsimp only
  split
  · rfl
  · rewrite [two_eq]
    exact (mapM_append function (values.take (values.length / 2))
      (values.drop (values.length / 2))).symm.trans
      (congrArg (fun source : List Alpha => source.mapM function)
        (List.take_append_drop (values.length / 2) values))

end Purelib.Data.Task.Parallel
