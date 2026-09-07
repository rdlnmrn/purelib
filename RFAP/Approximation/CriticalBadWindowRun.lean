import mathlib.Data.ConstructiveList
import mathlib.Tactic.QuotientFreeOmega
import RFAP.Approximation.CriticalTwoWindowTower
import RFAP.Approximation.DynamicalSharpness

/-!
# Arbitrarily long finite same-source critical runs

This module reindexes the transported Pell normal forms around one explicitly
chosen rational source.  Given a sharper rational threshold, a requested
scale, and a finite count, it returns exactly that many bad windows.  Their
source is definitionally shared and their upper denominator quadrances are
pairwise strictly increasing in list order.

Only the supplied finite list is constructed.  No completed critical source,
infinite orbit, limit, or almost-everywhere assertion is introduced.
-/

namespace RFAP.CriticalBadWindowRun

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Fraction := RFAP.HurwitzRational.Fraction
abbrev BadWindow := RFAP.DynamicalSharpness.BadWindow

open RFAP.BestApproximation

private theorem pairwise_ofFn_direct
    {item : Type} {relation : item → item → Prop} {count : Nat}
    (values : Fin count → item)
    (ordered : ∀ first second, first < second →
      relation (values first) (values second)) :
    (List.ofFn values).Pairwise relation := by
  induction count with
  | zero => exact .nil
  | succ count inductionHypothesis =>
      rw [QuotientFreeList.ofFn_succ, List.pairwise_cons]
      constructor
      · intro value member
        rw [List.mem_ofFn] at member
        rcases member with ⟨index, rfl⟩
        apply ordered (0 : Fin (count + 1)) index.succ
        change 0 < index.val + 1
        exact Nat.zero_lt_succ index.val
      · apply inductionHypothesis (fun index => values index.succ)
        intro first second indexOrder
        apply ordered first.succ second.succ
        exact Fin.succ_lt_succ_iff.mpr indexOrder

/-- A finite list of existing `BadWindow` records indexed by one definitionally
shared source, together with exact length and strict scale-growth data. -/
structure SameSourceBadWindowRun
    (threshold : Coordinate) (requestedScale count : Nat) where
  source : Fraction
  windows : List
    { window : BadWindow threshold requestedScale // window.source = source }
  length_eq : windows.length = count
  scalesStrict : windows.Pairwise fun earlier later =>
    denominatorQuadrance earlier.1.upper <
      denominatorQuadrance later.1.upper

/-- Earliest error-parameter stage used by the finite run. -/
def runBaseStage (threshold : Coordinate) (requestedScale : Nat) : Nat :=
  RFAP.FiniteWindowSharpness.sharpnessStage threshold requestedScale

/-- The common rational source is moved forward by the requested count so
all backward error parameters remain beyond the sharpness stage. -/
def runSourceStage
    (threshold : Coordinate) (requestedScale count : Nat) : Nat :=
  runBaseStage threshold requestedScale + count

/-- Exact transported normal form underlying one bounded offset of the
same-source run. -/
def normalFormAtOffset
    (threshold : Coordinate) (requestedScale count offset : Nat)
    (offsetBound : offset ≤ count) :
    RFAP.CriticalTwoWindowTower.TransportedNormalForm
      (RFAP.FiniteWindowSharpness.criticalSource
        (runSourceStage threshold requestedScale count))
      (runSourceStage threshold requestedScale count - offset)
      (runSourceStage threshold requestedScale count + offset) := by
  let sourceStage := runSourceStage threshold requestedScale count
  have offsetLeSource : offset ≤ sourceStage := by
    dsimp only [sourceStage, runSourceStage, runBaseStage]
    exact offsetBound.trans (Nat.le_add_left count _)
  have sourceIdentity : (sourceStage - offset) + offset = sourceStage :=
    Nat.sub_add_cancel offsetLeSource
  have targetIdentity :
      (sourceStage - offset) + 2 * offset = sourceStage + offset := by
    calc
      (sourceStage - offset) + 2 * offset =
          ((sourceStage - offset) + offset) + offset := by ring1
      _ = sourceStage + offset := by rw [sourceIdentity]
  have normal :=
    RFAP.CriticalTwoWindowTower.transportedNormalForm
      (sourceStage - offset) offset
  rw [sourceIdentity, targetIdentity] at normal
  exact normal

/-- The bad window at one bounded offset of the executable run. -/
def badWindowAtOffset
    {threshold : Coordinate}
    (certificate :
      RFAP.FiniteWindowSharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) (offset : Fin count) :
    { window : BadWindow threshold requestedScale //
      window.source = RFAP.FiniteWindowSharpness.criticalSource
        (runSourceStage threshold requestedScale count) } := by
  let sourceStage := runSourceStage threshold requestedScale count
  let backwardStage := sourceStage - offset.val
  let targetStage := sourceStage + offset.val
  have offsetBound : offset.val ≤ count := Nat.le_of_lt offset.isLt
  have normal :
      RFAP.CriticalTwoWindowTower.TransportedNormalForm
        (RFAP.FiniteWindowSharpness.criticalSource sourceStage)
        backwardStage targetStage := by
    simpa only [sourceStage, backwardStage, targetStage] using
      normalFormAtOffset threshold requestedScale count offset.val offsetBound
  have baseLeBackward :
      runBaseStage threshold requestedScale ≤ backwardStage := by
    dsimp only [backwardStage, sourceStage, runSourceStage]
    apply Nat.le_sub_of_add_le
    exact Nat.add_le_add_left offsetBound _
  have backwardLeTarget : backwardStage ≤ targetStage := by
    dsimp only [backwardStage, targetStage]
    exact (Nat.sub_le sourceStage offset.val).trans
      (Nat.le_add_right sourceStage offset.val)
  have gapStrict :
      RFAP.TwoParameterCylinder.gap
          (RFAP.FiniteWindowSharpness.pellParameter backwardStage)
          (RFAP.FiniteWindowSharpness.pellParameter targetStage) <
        threshold := by
    apply RFAP.CriticalTwoWindowTower.transportedGap_lt_sharperThreshold
      certificate requestedScale backwardStage targetStage
    · simpa only [runBaseStage] using baseLeBackward
    · exact backwardLeTarget
  have baseLeTarget :
      runBaseStage threshold requestedScale ≤ targetStage :=
    baseLeBackward.trans backwardLeTarget
  have beyondScale : requestedScale < denominatorQuadrance
      (RFAP.FiniteWindowSharpness.criticalUpperPair targetStage) :=
    (RFAP.FiniteWindowSharpness.requestedScale_lt_criticalUpperDenominatorQuadrance
      threshold requestedScale).trans_le
      (RFAP.CriticalBranch.criticalUpper_denominatorQuadrance_le_of_le
        (by simpa only [runBaseStage] using baseLeTarget))
  exact
    ⟨{ source := RFAP.FiniteWindowSharpness.criticalSource sourceStage
       lower := RFAP.FiniteWindowSharpness.criticalLowerPair targetStage
       upper := RFAP.FiniteWindowSharpness.criticalUpperPair targetStage
       beyondScale := beyondScale
       consecutive := normal.strictExteriorCertificate.areConsecutiveBest
       violates := normal.one_lt_threshold_mul_window threshold gapStrict }, rfl⟩

@[simp] theorem badWindowAtOffset_upper
    {threshold : Coordinate}
    (certificate :
      RFAP.FiniteWindowSharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) (offset : Fin count) :
    (badWindowAtOffset certificate requestedScale count offset).1.upper =
      RFAP.FiniteWindowSharpness.criticalUpperPair
        (runSourceStage threshold requestedScale count + offset.val) := by
  rfl

@[simp] theorem badWindowAtOffset_lower
    {threshold : Coordinate}
    (certificate :
      RFAP.FiniteWindowSharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) (offset : Fin count) :
    (badWindowAtOffset certificate requestedScale count offset).1.lower =
      RFAP.FiniteWindowSharpness.criticalLowerPair
        (runSourceStage threshold requestedScale count + offset.val) := by
  rfl

/-- Executable arbitrary-length finite analogue of recurrent critical-window
sharpness: all returned bad windows use one rational source, lie beyond the
requested scale, and have strictly increasing upper scales. -/
def criticalBadWindowRun
    {threshold : Coordinate}
    (certificate :
      RFAP.FiniteWindowSharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) :
    SameSourceBadWindowRun threshold requestedScale count := by
  refine
    { source := RFAP.FiniteWindowSharpness.criticalSource
        (runSourceStage threshold requestedScale count)
      windows := List.ofFn
        (badWindowAtOffset certificate requestedScale count)
      length_eq := QuotientFreeList.length_ofFn
      scalesStrict := ?_ }
  apply pairwise_ofFn_direct
  intro first second indexOrder
  rw [badWindowAtOffset_upper, badWindowAtOffset_upper]
  apply RFAP.CriticalBranch.criticalUpper_denominatorQuadrance_lt_of_lt
  exact Nat.add_lt_add_left indexOrder _

@[simp] theorem criticalBadWindowRun_source
    {threshold : Coordinate}
    (certificate :
      RFAP.FiniteWindowSharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) :
    (criticalBadWindowRun certificate requestedScale count).source =
      RFAP.FiniteWindowSharpness.criticalSource
        (runSourceStage threshold requestedScale count) := by
  rfl

end RFAP.CriticalBadWindowRun
