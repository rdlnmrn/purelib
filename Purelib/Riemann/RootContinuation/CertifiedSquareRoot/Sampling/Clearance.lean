module

public import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling
public import Purelib.Geometry.Rational.Box.Outside.Sum
import Purelib.Data.Rat.Fraction.Order.Arithmetic
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Clearance of two actual original root observations

Separate positive norm floors and a positive sum floor concern every
candidate of the two retained observations. The observations, certificates
and accuracy requests remain distinct original owners. A signed-window
construction derives all three floors from the original outside side without
requesting new samples or changing either root's apartness certificate.
-/

public section

namespace Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling

open Purelib
open Purelib.Approximation
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Rational

variable {firstParameter lastParameter : Canonical}
variable {firstRoot : Certificate firstParameter} {lastRoot : Certificate lastParameter}
variable {firstAccuracy lastAccuracy : AccuracyRequest}

set_option genInjectivity false in
/-- Positive candidate and sum margins on the exact two retained original root observations. -/
structure Clearance (first : ResidualObservation firstRoot firstAccuracy)
    (last : ResidualObservation lastRoot lastAccuracy) where
  /-- The quantitative source-candidate norm floor. -/ sourceFloor : Fraction.Rational
  /-- The retained source floor is strictly positive. -/ sourcePositive : 0 < sourceFloor
  /-- Every candidate of the same source observation pays its retained norm floor. -/ sourceLower :
    ∀ {candidate : Canonical}, first.observation.Possible candidate → sourceFloor ≤ Norm.Basic.normSq candidate
  /-- The quantitative target-candidate norm floor. -/ targetFloor : Fraction.Rational
  /-- The retained target floor is strictly positive. -/ targetPositive : 0 < targetFloor
  /-- Every candidate of the distinct target observation pays its retained norm floor. -/ targetLower :
    ∀ {candidate : Canonical}, last.observation.Possible candidate → targetFloor ≤ Norm.Basic.normSq candidate
  /-- The quantitative norm floor of paired source and target candidate sums. -/ sumFloor : Fraction.Rational
  /-- The retained sum floor is strictly positive. -/ sumPositive : 0 < sumFloor
  /-- Every pair of candidates of these identical two observations pays the retained sum margin. -/ sumLower :
    ∀ {source target : Canonical}, first.observation.Possible source → last.observation.Possible target →
      sumFloor ≤ Norm.Basic.normSq (source + target)

constructive_injectivity Clearance

namespace Clearance

variable {first : ResidualObservation firstRoot firstAccuracy} {last : ResidualObservation lastRoot lastAccuracy}

/-- The actual retained source witness pays the same source-candidate margin. -/
theorem source_normSq_lower (clearance : Clearance first last) :
    sourceFloor clearance ≤ Norm.Basic.normSq first.reading :=
  clearance.sourceLower first.observation.witness_possible

/-- The actual retained target witness pays the same target-candidate margin. -/
theorem target_normSq_lower (clearance : Clearance first last) :
    targetFloor clearance ≤ Norm.Basic.normSq last.reading :=
  clearance.targetLower last.observation.witness_possible

/-- The two actual retained witnesses pay the same quantitative sum margin. -/
theorem sum_normSq_lower (clearance : Clearance first last) :
    sumFloor clearance ≤ Norm.Basic.normSq (first.reading + last.reading) :=
  clearance.sumLower first.observation.witness_possible last.observation.witness_possible

/-- The retained source witness is nonzero by its paid candidate margin. -/
theorem source_nonzero (clearance : Clearance first last) : first.reading ≠ 0 := by
  intro zero
  have lower := clearance.source_normSq_lower
  rewrite [zero, Norm.Basic.normSq_zero] at lower
  exact clearance.sourcePositive.2 lower

/-- The retained target witness is nonzero by its distinct paid candidate margin. -/
theorem target_nonzero (clearance : Clearance first last) : last.reading ≠ 0 := by
  intro zero
  have lower := clearance.target_normSq_lower
  rewrite [zero, Norm.Basic.normSq_zero] at lower
  exact clearance.targetPositive.2 lower

/-- The actual retained witness sum is nonzero by the same internally paid sum margin. -/
theorem sum_nonzero (clearance : Clearance first last) : first.reading + last.reading ≠ 0 := by
  intro zero
  have lower := clearance.sum_normSq_lower
  rewrite [zero, Norm.Basic.normSq_zero] at lower
  exact clearance.sumPositive.2 lower

/-- Derive candidate and sum margins from the original signed window of the same actual observations. -/
def ofWindow (first : ResidualObservation firstRoot firstAccuracy) (last : ResidualObservation lastRoot lastAccuracy)
    (window : Box) (side : window.OutsideSide 0)
    (sourceWindow : ∀ {candidate : Canonical}, first.observation.Possible candidate → window.Contains candidate)
    (targetWindow : ∀ {candidate : Canonical}, last.observation.Possible candidate → window.Contains candidate) :
    Clearance first last :=
  { sourceFloor := side.margin
    sourcePositive := side.margin_pos
    sourceLower := fun possible => by
      have lower := side.margin_le_normSq_sub (sourceWindow possible)
      rewrite [Basic.sub_zero] at lower
      exact lower
    targetFloor := side.margin
    targetPositive := side.margin_pos
    targetLower := fun possible => by
      have lower := side.margin_le_normSq_sub (targetWindow possible)
      rewrite [Basic.sub_zero] at lower
      exact lower
    sumFloor := 4 * side.margin
    sumPositive := Fraction.Order.Arithmetic.mul_pos_direct (by decide +kernel) side.margin_pos
    sumLower := fun firstPossible lastPossible => side.sum_normSq_lower
      (sourceWindow firstPossible) (targetWindow lastPossible) }

/-- The window construction retains the original side margin as the source floor. -/
theorem ofWindow_sourceFloor (first : ResidualObservation firstRoot firstAccuracy)
    (last : ResidualObservation lastRoot lastAccuracy) (window : Box) (side : window.OutsideSide 0)
    (sourceWindow : ∀ {candidate : Canonical}, first.observation.Possible candidate → window.Contains candidate)
    (targetWindow : ∀ {candidate : Canonical}, last.observation.Possible candidate → window.Contains candidate) :
    (ofWindow first last window side sourceWindow targetWindow).sourceFloor = side.margin := by
  unfold ofWindow
  rfl

/-- The same window construction retains the original side margin as the target floor. -/
theorem ofWindow_targetFloor (first : ResidualObservation firstRoot firstAccuracy)
    (last : ResidualObservation lastRoot lastAccuracy) (window : Box) (side : window.OutsideSide 0)
    (sourceWindow : ∀ {candidate : Canonical}, first.observation.Possible candidate → window.Contains candidate)
    (targetWindow : ∀ {candidate : Canonical}, last.observation.Possible candidate → window.Contains candidate) :
    (ofWindow first last window side sourceWindow targetWindow).targetFloor = side.margin := by
  unfold ofWindow
  rfl

/-- The window construction retains four times the identical side margin as the paired sum floor. -/
theorem ofWindow_sumFloor (first : ResidualObservation firstRoot firstAccuracy)
    (last : ResidualObservation lastRoot lastAccuracy) (window : Box) (side : window.OutsideSide 0)
    (sourceWindow : ∀ {candidate : Canonical}, first.observation.Possible candidate → window.Contains candidate)
    (targetWindow : ∀ {candidate : Canonical}, last.observation.Possible candidate → window.Contains candidate) :
    (ofWindow first last window side sourceWindow targetWindow).sumFloor = 4 * side.margin := by
  unfold ofWindow
  rfl

end Clearance

end Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling
