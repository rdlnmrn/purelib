module

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

end Purelib.Data.Task.Parallel
