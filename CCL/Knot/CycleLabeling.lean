import CCL.Knot.TorusPermutation

/-!
# Constructive orbit labelling of cyclic monodromy

A finite one-cycle permutation can be labelled without any choice principle:
select one displayed base index and enumerate the orbit of the explicit
inverse map.  Bounded preimage search turns that injective enumeration into a
`FiniteBijection`.  With this labelling, the original permutation is exactly
the cyclic predecessor, hence exactly the endpoint action of the positive
Artin band `sigma_1 ... sigma_(d-1)`.
-/

namespace CCL.Knot.CycleLabeling

open CCL.Knot.FiniteBraid

abbrev FiniteBijection := CCL.FiniteMonodromy.FiniteBijection

namespace FiniteBijection

theorem iterateForward_commutes_forward {count : Nat}
    (bijection : FiniteBijection count count) (steps : Nat)
    (index : Fin count) :
    CCL.FiniteMonodromy.FiniteBijection.iterateForward bijection steps
        (bijection.forward index) =
      bijection.forward
        (CCL.FiniteMonodromy.FiniteBijection.iterateForward
          bijection steps index) := by
  induction steps with
  | zero => rfl
  | succ steps inductionHypothesis =>
      rw [CCL.FiniteMonodromy.FiniteBijection.iterateForward_succ,
        CCL.FiniteMonodromy.FiniteBijection.iterateForward_succ,
        inductionHypothesis]

theorem iterateForward_commutes_backward {count : Nat}
    (bijection : FiniteBijection count count) (steps : Nat)
    (index : Fin count) :
    CCL.FiniteMonodromy.FiniteBijection.iterateForward bijection steps
        (bijection.backward index) =
      bijection.backward
        (CCL.FiniteMonodromy.FiniteBijection.iterateForward
          bijection steps index) := by
  induction steps with
  | zero => rfl
  | succ steps inductionHypothesis =>
      rw [CCL.FiniteMonodromy.FiniteBijection.iterateForward_succ,
        CCL.FiniteMonodromy.FiniteBijection.iterateForward_succ,
        inductionHypothesis, bijection.forward_backward,
        bijection.backward_forward]

theorem iterate_reverse_cancel {count : Nat}
    (bijection : FiniteBijection count count) (steps : Nat)
    (index : Fin count) :
    CCL.FiniteMonodromy.FiniteBijection.iterateForward bijection steps
        (CCL.FiniteMonodromy.FiniteBijection.iterateForward
          bijection.reverse steps index) = index := by
  induction steps with
  | zero => rfl
  | succ steps inductionHypothesis =>
      rw [CCL.FiniteMonodromy.FiniteBijection.iterateForward_succ,
        CCL.FiniteMonodromy.FiniteBijection.iterateForward_succ]
      change bijection.forward
          (CCL.FiniteMonodromy.FiniteBijection.iterateForward bijection steps
            (bijection.backward
              (CCL.FiniteMonodromy.FiniteBijection.iterateForward
                bijection.reverse steps index))) = index
      rw [iterateForward_commutes_backward,
        bijection.forward_backward, inductionHypothesis]

/-- The inverse of a displayed finite cycle is again one full cycle. -/
theorem IsSingleCycle.reverse {count : Nat}
    {bijection : FiniteBijection count count}
    (cycle : CCL.FiniteMonodromy.FiniteBijection.IsSingleCycle bijection) :
    CCL.FiniteMonodromy.FiniteBijection.IsSingleCycle bijection.reverse := by
  refine
    { return_at_count := ?_
      no_early_return := ?_ }
  · intro index
    apply (CCL.FiniteMonodromy.FiniteBijection.iterateForward_injective
      bijection count)
    rw [iterate_reverse_cancel, cycle.return_at_count]
  · intro index steps positive small returned
    apply cycle.no_early_return index steps positive small
    have applied := congrArg
      (CCL.FiniteMonodromy.FiniteBijection.iterateForward
        bijection steps) returned
    rw [iterate_reverse_cancel] at applied
    exact applied.symm

/-- The first `count` iterates from a base point are pairwise distinct in a
one-cycle permutation. -/
theorem orbit_injective {count : Nat}
    {bijection : FiniteBijection count count}
    (cycle : CCL.FiniteMonodromy.FiniteBijection.IsSingleCycle bijection)
    (base : Fin count) : Function.Injective
      (fun steps : Fin count =>
        CCL.FiniteMonodromy.FiniteBijection.iterateForward
          bijection steps.val base) := by
  intro left right equal
  by_cases valuesEqual : left.val = right.val
  · exact Fin.ext valuesEqual
  · by_cases leftBefore : left.val < right.val
    · let difference := right.val - left.val
      have differencePositive : 0 < difference := Nat.sub_pos_of_lt leftBefore
      have differenceSmall : difference < count :=
        (Nat.sub_le right.val left.val).trans_lt right.isLt
      have split : left.val + difference = right.val :=
        Nat.add_sub_of_le leftBefore.le
      have returned :
          CCL.FiniteMonodromy.FiniteBijection.iterateForward
              bijection difference
              (CCL.FiniteMonodromy.FiniteBijection.iterateForward
                bijection left.val base) =
            CCL.FiniteMonodromy.FiniteBijection.iterateForward
              bijection left.val base := by
        calc
          _ = CCL.FiniteMonodromy.FiniteBijection.iterateForward
                bijection (left.val + difference) base :=
            (CCL.FiniteMonodromy.FiniteBijection.iterateForward_add
              bijection left.val difference base).symm
          _ = CCL.FiniteMonodromy.FiniteBijection.iterateForward
                bijection right.val base := by rw [split]
          _ = CCL.FiniteMonodromy.FiniteBijection.iterateForward
                bijection left.val base := equal.symm
      exact (cycle.no_early_return _ difference differencePositive
        differenceSmall returned).elim
    · have rightBefore : right.val < left.val :=
        Nat.lt_of_le_of_ne (Nat.le_of_not_gt leftBefore)
          (Ne.symm valuesEqual)
      let difference := left.val - right.val
      have differencePositive : 0 < difference :=
        Nat.sub_pos_of_lt rightBefore
      have differenceSmall : difference < count :=
        (Nat.sub_le left.val right.val).trans_lt left.isLt
      have split : right.val + difference = left.val :=
        Nat.add_sub_of_le rightBefore.le
      have returned :
          CCL.FiniteMonodromy.FiniteBijection.iterateForward
              bijection difference
              (CCL.FiniteMonodromy.FiniteBijection.iterateForward
                bijection right.val base) =
            CCL.FiniteMonodromy.FiniteBijection.iterateForward
              bijection right.val base := by
        calc
          _ = CCL.FiniteMonodromy.FiniteBijection.iterateForward
                bijection (right.val + difference) base :=
            (CCL.FiniteMonodromy.FiniteBijection.iterateForward_add
              bijection right.val difference base).symm
          _ = CCL.FiniteMonodromy.FiniteBijection.iterateForward
                bijection left.val base := by rw [split]
          _ = CCL.FiniteMonodromy.FiniteBijection.iterateForward
                bijection right.val base := equal
      exact (cycle.no_early_return _ difference differencePositive
        differenceSmall returned).elim

/-- Executable inverse-orbit labelling.  Its backward map is obtained by the
bounded finite search in `ofInjectiveEndomap`. -/
def inverseOrbitLabeling {count : Nat}
    (bijection : FiniteBijection count count)
    (cycle : CCL.FiniteMonodromy.FiniteBijection.IsSingleCycle bijection)
    (base : Fin count) : FiniteBijection count count :=
  CCL.FiniteMonodromy.FiniteBijection.ofInjectiveEndomap
    (fun steps : Fin count =>
      CCL.FiniteMonodromy.FiniteBijection.iterateForward
        bijection.reverse steps.val base)
    (orbit_injective (IsSingleCycle.reverse cycle) base)

@[simp] theorem inverseOrbitLabeling_forward {count : Nat}
    (bijection : FiniteBijection count count)
    (cycle : CCL.FiniteMonodromy.FiniteBijection.IsSingleCycle bijection)
    (base position : Fin count) :
    (inverseOrbitLabeling bijection cycle base).forward position =
      CCL.FiniteMonodromy.FiniteBijection.iterateForward
        bijection.reverse position.val base := rfl

/-- In inverse-orbit coordinates, the original cycle is the standard cyclic
predecessor. -/
theorem forward_inverseOrbitLabeling {count : Nat} (positive : 0 < count)
    (bijection : FiniteBijection count count)
    (cycle : CCL.FiniteMonodromy.FiniteBijection.IsSingleCycle bijection)
    (base position : Fin count) :
    bijection.forward
        ((inverseOrbitLabeling bijection cycle base).forward position) =
      (inverseOrbitLabeling bijection cycle base).forward
        (CCL.Knot.TorusPermutation.cyclicPredecessor positive position) := by
  by_cases zero : position.val = 0
  · have positionZero : position = ⟨0, positive⟩ := Fin.ext zero
    subst position
    rw [CCL.Knot.TorusPermutation.cyclicPredecessor_zero,
      inverseOrbitLabeling_forward, inverseOrbitLabeling_forward]
    have reverseReturns :=
      (IsSingleCycle.reverse cycle).return_at_count base
    have successor : count - 1 + 1 = count := Nat.sub_add_cancel positive
    have stepReturns :
        CCL.FiniteMonodromy.FiniteBijection.iterateForward
            bijection.reverse (count - 1 + 1) base = base :=
      (congrArg
        (fun steps : Nat =>
          CCL.FiniteMonodromy.FiniteBijection.iterateForward
            bijection.reverse steps base) successor).trans reverseReturns
    rw [CCL.FiniteMonodromy.FiniteBijection.iterateForward_succ]
      at stepReturns
    change bijection.forward base =
      CCL.FiniteMonodromy.FiniteBijection.iterateForward
        bijection.reverse (count - 1) base
    apply bijection.reverse.forward_injective
    change bijection.backward (bijection.forward base) =
      bijection.backward
        (CCL.FiniteMonodromy.FiniteBijection.iterateForward
          bijection.reverse (count - 1) base)
    rw [bijection.backward_forward]
    exact stepReturns.symm
  · rw [CCL.Knot.TorusPermutation.cyclicPredecessor_of_ne_zero
      positive position zero,
      inverseOrbitLabeling_forward, inverseOrbitLabeling_forward]
    change bijection.forward
        (CCL.FiniteMonodromy.FiniteBijection.iterateForward
          bijection.reverse position.val base) =
      CCL.FiniteMonodromy.FiniteBijection.iterateForward
        bijection.reverse (position.val - 1) base
    have predecessor : position.val - 1 + 1 = position.val :=
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr zero)
    have expanded :
        CCL.FiniteMonodromy.FiniteBijection.iterateForward
            bijection.reverse position.val base =
          bijection.backward
            (CCL.FiniteMonodromy.FiniteBijection.iterateForward
              bijection.reverse (position.val - 1) base) := by
      calc
        _ = CCL.FiniteMonodromy.FiniteBijection.iterateForward
              bijection.reverse (position.val - 1 + 1) base :=
          congrArg
            (fun steps : Nat =>
              CCL.FiniteMonodromy.FiniteBijection.iterateForward
                bijection.reverse steps base) predecessor.symm
        _ = _ := rfl
    rw [expanded]
    rw [bijection.forward_backward]

/-- The positive Artin band has exactly the relabelled endpoint action of any
displayed one-cycle permutation. -/
theorem positiveBand_agrees {count : Nat} (positive : 0 < count)
    (bijection : FiniteBijection count count)
    (cycle : CCL.FiniteMonodromy.FiniteBijection.IsSingleCycle bijection)
    (base position : Fin count) :
    bijection.forward
        ((inverseOrbitLabeling bijection cycle base).forward position) =
      (inverseOrbitLabeling bijection cycle base).forward
        ((CCL.Knot.TorusBraid.positiveBand count).permutation.forward
          position) := by
  rw [CCL.Knot.TorusPermutation.positiveBand_permutation_forward positive]
  exact forward_inverseOrbitLabeling positive bijection cycle base position

end FiniteBijection

/-! ## Closed braids with an explicit owner relabelling -/

/-- A certified loop braid whose word positions are related to the chamber's
internal owner indices by an explicit finite bijection. -/
structure RelabeledLoopBraid
    (frame : CCL.FiniteMonodromy.ChamberFrame)
    (loop : CCL.FiniteMonodromy.ChamberPath frame frame) where
  word : Word frame.degree
  labeling : FiniteBijection frame.degree frame.degree
  agrees : ∀ position : Fin frame.degree,
    loop.monodromy.forward (labeling.forward position) =
      labeling.forward (word.permutation.forward position)

namespace RelabeledLoopBraid

/-- Canonical positive-band representative of a one-cycle loop, using the
inverse orbit of one displayed base owner as its strand labelling. -/
def positiveBandOfSingleCycle
    {frame : CCL.FiniteMonodromy.ChamberFrame}
    {loop : CCL.FiniteMonodromy.ChamberPath frame frame}
    (positive : 0 < frame.degree)
    (cycle : CCL.FiniteMonodromy.FiniteBijection.IsSingleCycle
      loop.monodromy)
    (base : frame.Index) : RelabeledLoopBraid frame loop where
  word := CCL.Knot.TorusBraid.positiveBand frame.degree
  labeling := FiniteBijection.inverseOrbitLabeling
    loop.monodromy cycle base
  agrees := FiniteBijection.positiveBand_agrees positive
    loop.monodromy cycle base

def identity (frame : CCL.FiniteMonodromy.ChamberFrame) :
    RelabeledLoopBraid frame (.nil frame) where
  word := []
  labeling := CCL.FiniteMonodromy.FiniteBijection.identity frame.degree
  agrees := fun _ => rfl

def append {frame : CCL.FiniteMonodromy.ChamberFrame}
    {first second : CCL.FiniteMonodromy.ChamberPath frame frame}
    (firstBraid : RelabeledLoopBraid frame first)
    (secondBraid : RelabeledLoopBraid frame second)
    (sameLabeling : CCL.FiniteMonodromy.FiniteBijection.Same
      firstBraid.labeling secondBraid.labeling) :
    RelabeledLoopBraid frame (first.append second) where
  word := firstBraid.word ++ secondBraid.word
  labeling := firstBraid.labeling
  agrees := by
    intro position
    calc
      (first.append second).monodromy.forward
          (firstBraid.labeling.forward position) =
        second.monodromy.forward
          (first.monodromy.forward
            (firstBraid.labeling.forward position)) :=
        CCL.FiniteMonodromy.ChamberPath.monodromy_append first second _
      _ = second.monodromy.forward
          (firstBraid.labeling.forward
            (firstBraid.word.permutation.forward position)) := by
        rw [firstBraid.agrees]
      _ = second.monodromy.forward
          (secondBraid.labeling.forward
            (firstBraid.word.permutation.forward position)) := by
        rw [sameLabeling]
      _ = secondBraid.labeling.forward
          (secondBraid.word.permutation.forward
            (firstBraid.word.permutation.forward position)) :=
        secondBraid.agrees (firstBraid.word.permutation.forward position)
      _ = firstBraid.labeling.forward
          (secondBraid.word.permutation.forward
            (firstBraid.word.permutation.forward position)) := by
        rw [sameLabeling]
      _ = firstBraid.labeling.forward
          ((firstBraid.word ++ secondBraid.word).permutation.forward
            position) := by
        rw [CCL.Knot.FiniteBraid.Word.permutation_append]
        rfl

def reverse {frame : CCL.FiniteMonodromy.ChamberFrame}
    {loop : CCL.FiniteMonodromy.ChamberPath frame frame}
    (braid : RelabeledLoopBraid frame loop) :
    RelabeledLoopBraid frame loop.reverse where
  word := braid.word.inverse
  labeling := braid.labeling
  agrees := by
    intro position
    calc
      loop.reverse.monodromy.forward (braid.labeling.forward position) =
          loop.monodromy.backward (braid.labeling.forward position) :=
        CCL.FiniteMonodromy.ChamberPath.transport_reverse_forward loop _
      _ = braid.labeling.forward
          (braid.word.inverse.permutation.forward position) := by
        have forwardAt := braid.agrees
          (braid.word.permutation.backward position)
        rw [braid.word.permutation.forward_backward] at forwardAt
        have pulledBack := congrArg loop.monodromy.backward forwardAt
        rw [loop.monodromy.backward_forward] at pulledBack
        rw [braid.word.permutation_inverse position]
        exact pulledBack.symm

theorem iterate_agrees {frame : CCL.FiniteMonodromy.ChamberFrame}
    {loop : CCL.FiniteMonodromy.ChamberPath frame frame}
    (braid : RelabeledLoopBraid frame loop) (steps : Nat)
    (position : Fin frame.degree) :
    CCL.FiniteMonodromy.FiniteBijection.iterateForward loop.monodromy steps
        (braid.labeling.forward position) =
      braid.labeling.forward
        (CCL.FiniteMonodromy.FiniteBijection.iterateForward
          braid.word.permutation steps position) := by
  induction steps with
  | zero => rfl
  | succ steps inductionHypothesis =>
      rw [CCL.FiniteMonodromy.FiniteBijection.iterateForward_succ,
        CCL.FiniteMonodromy.FiniteBijection.iterateForward_succ,
        inductionHypothesis]
      exact braid.agrees _

def closure {frame : CCL.FiniteMonodromy.ChamberFrame}
    {loop : CCL.FiniteMonodromy.ChamberPath frame frame}
    (braid : RelabeledLoopBraid frame loop) : Closure where
  strands := frame.degree
  word := braid.word

theorem closure_isKnot_of_monodromy_isSingleCycle
    {frame : CCL.FiniteMonodromy.ChamberFrame}
    {loop : CCL.FiniteMonodromy.ChamberPath frame frame}
    (braid : RelabeledLoopBraid frame loop)
    (single : CCL.FiniteMonodromy.FiniteBijection.IsSingleCycle
      loop.monodromy) : braid.closure.IsKnot := by
  refine
    { return_at_count := ?_
      no_early_return := ?_ }
  · intro position
    apply braid.labeling.forward_injective
    have returns := single.return_at_count (braid.labeling.forward position)
    rw [braid.iterate_agrees frame.degree position] at returns
    exact returns
  · intro position steps positive small returned
    apply single.no_early_return
      (braid.labeling.forward position) steps positive small
    rw [braid.iterate_agrees steps position]
    exact congrArg braid.labeling.forward returned

end RelabeledLoopBraid

end CCL.Knot.CycleLabeling
