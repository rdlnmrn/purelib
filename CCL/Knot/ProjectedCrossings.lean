import CCL.Knot.FiniteBraid

/-!
# Certified projected crossings of finite root paths

An Artin generator acts on the left-to-right positions of a chosen planar
projection, whereas finite monodromy transports the persistent owner indices
of root boxes.  Those numberings need not coincide.  This file records their
finite relabelling explicitly and folds atomic projected chamber overlaps into
an executable braid word.

A crossing chart contains only rational root boxes, a signed adjacent
generator, an exact owner-matching law, and a strict height separation of the
two crossing strands.  It is therefore finite certificate data: no completed
root track or configuration space is introduced.  The extraction theorem
proves that evaluating the resulting word gives exactly the chamber-path
transport, expressed in the endpoint projection orders.
-/

namespace CCL.Knot.ProjectedCrossings

open CCL.Knot.FiniteBraid

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Box := RFAP.Boxes.Box
abbrev LocalOwner := CCL.FiniteMonodromy.LocalOwner
abbrev ChamberFrame := CCL.FiniteMonodromy.ChamberFrame
abbrev ChamberOverlap := CCL.FiniteMonodromy.ChamberOverlap
abbrev ChamberPath := CCL.FiniteMonodromy.ChamberPath
abbrev FiniteBijection := CCL.FiniteMonodromy.FiniteBijection

/-! ## Projection-ordered chamber frames -/

/-- A chamber frame equipped with a rationally certified left-to-right root
order.  `orderToOwner` deliberately remains separate from the chamber's
internal owner numbering.  The sampled local owners may be strict refinements
of the chamber owners and hence can resolve a projection even when the
original owner boxes are too coarse to do so. -/
structure ProjectedFrame (strands : Nat) where
  chamber : ChamberFrame
  degree_eq : chamber.degree = strands
  orderToOwner : FiniteBijection strands chamber.degree
  sampleOwner : Fin strands → LocalOwner chamber.polynomial
  sample_refines_owner : ∀ position : Fin strands,
    (sampleOwner position).box.Refines
      (chamber.owner (orderToOwner.forward position)).box
  xOrdered : ∀ left right : Fin strands, left.val < right.val →
    (sampleOwner left).box.xUpper < (sampleOwner right).box.xLower

namespace ProjectedFrame

def ownerIndex {strands : Nat} (frame : ProjectedFrame strands)
    (position : Fin strands) : frame.chamber.Index :=
  frame.orderToOwner.forward position

theorem ownerIndex_injective {strands : Nat}
    (frame : ProjectedFrame strands) : Function.Injective frame.ownerIndex :=
  frame.orderToOwner.forward_injective

theorem adjacent_x_gap {strands : Nat} (frame : ProjectedFrame strands)
    (generator : Generator strands) :
    (frame.sampleOwner generator.left).box.xUpper <
      (frame.sampleOwner generator.right).box.xLower := by
  apply frame.xOrdered
  change generator.index.val < generator.index.val + 1
  omega

end ProjectedFrame

/-! ## Atomic projected events -/

/-- One atomic event is either a projection chart with no crossing or one
signed adjacent crossing. -/
inductive Event (strands : Nat)
  | stationary
  | crossing (generator : Generator strands)
deriving DecidableEq, Repr

namespace Event

def word {strands : Nat} : Event strands → Word strands
  | .stationary => []
  | .crossing generator => [generator]

@[simp] theorem word_stationary (strands : Nat) :
    word (.stationary : Event strands) = [] := rfl

@[simp] theorem word_crossing {strands : Nat}
    (generator : Generator strands) : word (.crossing generator) = [generator] :=
  rfl

def permutation {strands : Nat} (event : Event strands) :
    FiniteBijection strands strands := event.word.permutation

def reverse {strands : Nat} : Event strands → Event strands
  | .stationary => .stationary
  | .crossing generator => .crossing generator.reverse

@[simp] theorem reverse_reverse {strands : Nat} (event : Event strands) :
    event.reverse.reverse = event := by
  cases event with
  | stationary => rfl
  | crossing generator =>
      simp only [reverse, Generator.reverse_reverse]

@[simp] theorem word_reverse {strands : Nat} (event : Event strands) :
    event.reverse.word = event.word.inverse := by
  cases event with
  | stationary => rfl
  | crossing generator => rfl

@[simp] theorem permutation_stationary_forward (strands : Nat)
    (position : Fin strands) :
    (permutation (.stationary : Event strands)).forward position = position :=
  rfl

@[simp] theorem permutation_crossing_forward {strands : Nat}
    (generator : Generator strands) (position : Fin strands) :
    (permutation (.crossing generator)).forward position =
      generator.permutation.forward position := rfl

end Event

/-- Rational geometry distinguishing the over/under choice at one adjacent
projection crossing.  In a positive chart the strand which starts in the
left position lies strictly below the other strand throughout their two
Rouché bridge boxes; a negative chart records the reverse height order.

Together with the adjacent endpoint swap stored by `ProjectedOverlap`, this
is finite signed-crossing data rather than an arbitrary sign annotation. -/
structure CrossingGeometry {strands : Nat}
    (start finish : ProjectedFrame strands)
    (overlap : ChamberOverlap start.chamber finish.chamber)
    (generator : Generator strands) where
  heightSeparated :
    match generator.sign with
    | .positive =>
        (overlap.bridge (start.ownerIndex generator.left)).box.yUpper <
          (overlap.bridge (start.ownerIndex generator.right)).box.yLower
    | .negative =>
        (overlap.bridge (start.ownerIndex generator.right)).box.yUpper <
          (overlap.bridge (start.ownerIndex generator.left)).box.yLower

/-- One certified atomic overlap in projection order.  The matching equation
is the decisive link: it states that persistent owner transport is either the
identity on projection positions or exactly the displayed adjacent swap. -/
inductive ProjectedOverlap {strands : Nat}
    (start finish : ProjectedFrame strands) : Type 2
  | stationary
      (overlap : ChamberOverlap start.chamber finish.chamber)
      (matching_order : ∀ position : Fin strands,
        overlap.matching.forward (start.ownerIndex position) =
          finish.ownerIndex position)
  | crossing
      (overlap : ChamberOverlap start.chamber finish.chamber)
      (generator : Generator strands)
      (geometry : CrossingGeometry start finish overlap generator)
      (matching_order : ∀ position : Fin strands,
        overlap.matching.forward (start.ownerIndex position) =
          finish.ownerIndex (generator.permutation.forward position))

namespace ProjectedOverlap

def chamberOverlap {strands : Nat} {start finish : ProjectedFrame strands} :
    ProjectedOverlap start finish →
      ChamberOverlap start.chamber finish.chamber
  | .stationary overlap _ => overlap
  | .crossing overlap _ _ _ => overlap

def event {strands : Nat} {start finish : ProjectedFrame strands} :
    ProjectedOverlap start finish → Event strands
  | .stationary _ _ => .stationary
  | .crossing _ generator _ _ => .crossing generator

def word {strands : Nat} {start finish : ProjectedFrame strands}
    (step : ProjectedOverlap start finish) : Word strands :=
  step.event.word

theorem matching_order {strands : Nat}
    {start finish : ProjectedFrame strands}
    (step : ProjectedOverlap start finish) (position : Fin strands) :
    step.chamberOverlap.matching.forward (start.ownerIndex position) =
      finish.ownerIndex (step.event.permutation.forward position) := by
  cases step with
  | stationary overlap law => exact law position
  | crossing overlap generator geometry law => exact law position

theorem crossing_backward_left {strands : Nat}
    {start finish : ProjectedFrame strands}
    (overlap : ChamberOverlap start.chamber finish.chamber)
    (generator : Generator strands)
    (law : ∀ position : Fin strands,
      overlap.matching.forward (start.ownerIndex position) =
        finish.ownerIndex (generator.permutation.forward position)) :
    overlap.matching.backward (finish.ownerIndex generator.left) =
      start.ownerIndex generator.right := by
  have matched := congrArg overlap.matching.backward (law generator.right)
  rw [Generator.permutation, transposition_forward, swapIndices_right,
    overlap.matching.backward_forward] at matched
  exact matched.symm

theorem crossing_backward_right {strands : Nat}
    {start finish : ProjectedFrame strands}
    (overlap : ChamberOverlap start.chamber finish.chamber)
    (generator : Generator strands)
    (law : ∀ position : Fin strands,
      overlap.matching.forward (start.ownerIndex position) =
        finish.ownerIndex (generator.permutation.forward position)) :
    overlap.matching.backward (finish.ownerIndex generator.right) =
      start.ownerIndex generator.left := by
  have matched := congrArg overlap.matching.backward (law generator.left)
  rw [Generator.permutation, transposition_forward, swapIndices_left,
    overlap.matching.backward_forward] at matched
  exact matched.symm

theorem reverseCrossingGeometry {strands : Nat}
    {start finish : ProjectedFrame strands}
    (overlap : ChamberOverlap start.chamber finish.chamber)
    (generator : Generator strands)
    (geometry : CrossingGeometry start finish overlap generator)
    (law : ∀ position : Fin strands,
      overlap.matching.forward (start.ownerIndex position) =
        finish.ownerIndex (generator.permutation.forward position)) :
    CrossingGeometry finish start overlap.reverse generator.reverse := by
  constructor
  have backwardLeft := crossing_backward_left overlap generator law
  have backwardRight := crossing_backward_right overlap generator law
  cases generator with
  | mk index sign =>
      cases sign with
      | positive =>
          change
            (overlap.bridge
              (overlap.matching.backward
                (finish.ownerIndex
                  ({ index := index, sign := CrossingSign.positive } :
                    Generator strands).right))).box.yUpper <
              (overlap.bridge
                (overlap.matching.backward
                  (finish.ownerIndex
                    ({ index := index, sign := CrossingSign.positive } :
                      Generator strands).left))).box.yLower
          rw [backwardRight, backwardLeft]
          exact geometry.heightSeparated
      | negative =>
          change
            (overlap.bridge
              (overlap.matching.backward
                (finish.ownerIndex
                  ({ index := index, sign := CrossingSign.negative } :
                    Generator strands).left))).box.yUpper <
              (overlap.bridge
                (overlap.matching.backward
                  (finish.ownerIndex
                    ({ index := index, sign := CrossingSign.negative } :
                      Generator strands).right))).box.yLower
          rw [backwardLeft, backwardRight]
          exact geometry.heightSeparated

def reverse {strands : Nat} {start finish : ProjectedFrame strands} :
    ProjectedOverlap start finish → ProjectedOverlap finish start
  | .stationary overlap law =>
      .stationary overlap.reverse (by
        intro position
        have matched := congrArg overlap.matching.backward (law position)
        rw [overlap.matching.backward_forward] at matched
        exact matched.symm)
  | .crossing overlap generator geometry law =>
      .crossing overlap.reverse generator.reverse
        (reverseCrossingGeometry overlap generator geometry law) (by
          intro position
          have matched := congrArg overlap.matching.backward
            (law (generator.permutation.forward position))
          rw [Generator.permutation_involutive,
            overlap.matching.backward_forward] at matched
          exact matched.symm)

@[simp] theorem reverse_word {strands : Nat}
    {start finish : ProjectedFrame strands}
    (step : ProjectedOverlap start finish) :
    step.reverse.word = step.word.inverse := by
  cases step with
  | stationary overlap law => rfl
  | crossing overlap generator geometry law => rfl

@[simp] theorem reverse_chamberOverlap {strands : Nat}
    {start finish : ProjectedFrame strands}
    (step : ProjectedOverlap start finish) :
    step.reverse.chamberOverlap = step.chamberOverlap.reverse := by
  cases step with
  | stationary overlap law => rfl
  | crossing overlap generator geometry law => rfl

end ProjectedOverlap

/-! ## Paths and extraction -/

/-- A finite chamber path whose every subdivision cell has a certified
atomic projected event.  Adjacent cells share the same projected frame, so
no endpoint relabelling is hidden between their certificates. -/
inductive ProjectedPath {strands : Nat} :
    (start finish : ProjectedFrame strands) → Type 2
  | nil (frame : ProjectedFrame strands) : ProjectedPath frame frame
  | cons {start middle finish : ProjectedFrame strands}
      (step : ProjectedOverlap start middle)
      (remaining : ProjectedPath middle finish) :
      ProjectedPath start finish

namespace ProjectedPath

def chamberPath {strands : Nat} :
    {start finish : ProjectedFrame strands} →
      ProjectedPath start finish →
        ChamberPath start.chamber finish.chamber
  | _, _, .nil frame => .nil frame.chamber
  | _, _, .cons step remaining =>
      .cons step.chamberOverlap remaining.chamberPath

def word {strands : Nat} :
    {start finish : ProjectedFrame strands} →
      ProjectedPath start finish → Word strands
  | _, _, .nil _ => []
  | _, _, .cons step remaining => step.word ++ remaining.word

def stepCount {strands : Nat} :
    {start finish : ProjectedFrame strands} →
      ProjectedPath start finish → Nat
  | _, _, .nil _ => 0
  | _, _, .cons _ remaining => remaining.stepCount + 1

def append {strands : Nat}
    {start middle finish : ProjectedFrame strands}
    (first : ProjectedPath start middle)
    (second : ProjectedPath middle finish) : ProjectedPath start finish :=
  match first with
  | .nil _ => second
  | .cons step remaining => .cons step (remaining.append second)

def reverse {strands : Nat} :
    {start finish : ProjectedFrame strands} →
      ProjectedPath start finish → ProjectedPath finish start
  | _, _, .nil frame => .nil frame
  | _, _, .cons (start := start) step remaining =>
      remaining.reverse.append (.cons step.reverse (.nil start))

@[simp] theorem chamberPath_append {strands : Nat}
    {start middle finish : ProjectedFrame strands}
    (first : ProjectedPath start middle)
    (second : ProjectedPath middle finish) :
    (first.append second).chamberPath =
      first.chamberPath.append second.chamberPath := by
  induction first with
  | nil frame => rfl
  | cons step remaining inductionHypothesis =>
      simp only [append, chamberPath,
        CCL.FiniteMonodromy.ChamberPath.append, inductionHypothesis]

@[simp] theorem word_append {strands : Nat}
    {start middle finish : ProjectedFrame strands}
    (first : ProjectedPath start middle)
    (second : ProjectedPath middle finish) :
    (first.append second).word = first.word ++ second.word := by
  induction first with
  | nil frame => rfl
  | cons step remaining inductionHypothesis =>
      simp only [append, word, inductionHypothesis, List.append_assoc]

@[simp] theorem chamberPath_reverse {strands : Nat}
    {start finish : ProjectedFrame strands}
    (path : ProjectedPath start finish) :
    path.reverse.chamberPath = path.chamberPath.reverse := by
  induction path with
  | nil frame => rfl
  | cons step remaining inductionHypothesis =>
      simp only [reverse, chamberPath_append, chamberPath,
        inductionHypothesis, ProjectedOverlap.reverse_chamberOverlap,
        CCL.FiniteMonodromy.ChamberPath.reverse]

@[simp] theorem word_reverse {strands : Nat}
    {start finish : ProjectedFrame strands}
    (path : ProjectedPath start finish) :
    path.reverse.word = path.word.inverse := by
  induction path with
  | nil frame => rfl
  | cons step remaining inductionHypothesis =>
      simp only [reverse, word_append, word, inductionHypothesis,
        ProjectedOverlap.reverse_word,
        CCL.Knot.FiniteBraid.Word.inverse_append,
        List.append_nil]

@[simp] theorem stepCount_append {strands : Nat}
    {start middle finish : ProjectedFrame strands}
    (first : ProjectedPath start middle)
    (second : ProjectedPath middle finish) :
    (first.append second).stepCount = first.stepCount + second.stepCount := by
  induction first with
  | nil frame => simp only [append, stepCount, Nat.zero_add]
  | cons step remaining inductionHypothesis =>
      simp only [append, stepCount, inductionHypothesis]
      omega

@[simp] theorem chamberPath_stepCount {strands : Nat}
    {start finish : ProjectedFrame strands}
    (path : ProjectedPath start finish) :
    path.chamberPath.stepCount = path.stepCount := by
  induction path with
  | nil frame => rfl
  | cons step remaining inductionHypothesis =>
      simp only [chamberPath, CCL.FiniteMonodromy.ChamberPath.stepCount,
        stepCount, inductionHypothesis]

/-- Evaluation of the extracted word agrees exactly with owner transport,
after applying the independently certified projection order at each endpoint.
This is the central finite braid-extraction theorem. -/
theorem transport_agrees {strands : Nat}
    {start finish : ProjectedFrame strands}
    (path : ProjectedPath start finish) (position : Fin strands) :
    path.chamberPath.transport.forward (start.ownerIndex position) =
      finish.ownerIndex (path.word.permutation.forward position) := by
  induction path generalizing position with
  | nil frame => rfl
  | @cons start middle finish step remaining inductionHypothesis =>
      calc
        (ProjectedPath.cons step remaining).chamberPath.transport.forward
            (start.ownerIndex position) =
          remaining.chamberPath.transport.forward
            (step.chamberOverlap.matching.forward
              (start.ownerIndex position)) := rfl
        _ = remaining.chamberPath.transport.forward
            (middle.ownerIndex
              (step.event.permutation.forward position)) := by
          rw [step.matching_order position]
        _ = finish.ownerIndex
            (remaining.word.permutation.forward
              (step.event.permutation.forward position)) :=
          inductionHypothesis (step.event.permutation.forward position)
        _ = finish.ownerIndex
            ((step.word ++ remaining.word).permutation.forward position) := by
          rw [CCL.Knot.FiniteBraid.Word.permutation_append]
          rfl

theorem iterate_agrees {strands : Nat} (frame : ProjectedFrame strands)
    (loop : ProjectedPath frame frame) (steps : Nat)
    (position : Fin strands) :
    CCL.FiniteMonodromy.FiniteBijection.iterateForward
        loop.chamberPath.monodromy steps (frame.ownerIndex position) =
      frame.ownerIndex
        (CCL.FiniteMonodromy.FiniteBijection.iterateForward
          loop.word.permutation steps position) := by
  induction steps with
  | zero => rfl
  | succ steps inductionHypothesis =>
      rw [CCL.FiniteMonodromy.FiniteBijection.iterateForward_succ,
        CCL.FiniteMonodromy.FiniteBijection.iterateForward_succ,
        inductionHypothesis]
      exact loop.transport_agrees
        (CCL.FiniteMonodromy.FiniteBijection.iterateForward
          loop.word.permutation steps position)

/-- The finite combinatorial closure extracted from a closed projected root
path. -/
def closure {strands : Nat} (frame : ProjectedFrame strands)
    (loop : ProjectedPath frame frame) : Closure where
  strands := strands
  word := loop.word

/-- A one-cycle owner monodromy remains one cycle after the explicit
projection-order conjugacy.  Thus the extracted finite closure detects knots
independently of the chamber's internal numbering of its owners. -/
theorem closure_isKnot_of_monodromy_isSingleCycle {strands : Nat}
    (frame : ProjectedFrame strands) (loop : ProjectedPath frame frame)
    (single : CCL.FiniteMonodromy.FiniteBijection.IsSingleCycle
      loop.chamberPath.monodromy) :
    (closure frame loop).IsKnot := by
  change CCL.FiniteMonodromy.FiniteBijection.IsSingleCycle
    loop.word.permutation
  refine
    { return_at_count := ?_
      no_early_return := ?_ }
  · intro position
    apply frame.ownerIndex_injective
    have returns :
        CCL.FiniteMonodromy.FiniteBijection.iterateForward
            loop.chamberPath.monodromy strands
              (frame.ownerIndex position) = frame.ownerIndex position := by
      simpa only [frame.degree_eq] using
        single.return_at_count (frame.ownerIndex position)
    rw [iterate_agrees frame loop strands position] at returns
    exact returns
  · intro position steps positive small returned
    apply single.no_early_return (frame.ownerIndex position) steps positive
    · simpa only [frame.degree_eq] using small
    · rw [iterate_agrees frame loop steps position]
      exact congrArg frame.ownerIndex returned

end ProjectedPath

end CCL.Knot.ProjectedCrossings
