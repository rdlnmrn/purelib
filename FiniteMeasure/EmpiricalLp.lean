import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.Empirical
import FiniteMeasure.LpEquivalence
import FiniteMeasure.EssentialMaximumOperations
import FiniteMeasure.EssentialMaximumEquivalence

/-!
# Lp quantities of explicit empirical distributions

A nonempty displayed sample produces exact finite sample averages for every
natural-powered magnitude and distance.  Its executable essential maximum is
the recursively computed maximum over the displayed sample rows.
-/

namespace FiniteMeasure

/-- Recursive rational maximum magnitude over a displayed sample list. -/
def sampleEssentialMaximumMagnitude {α : Type}
    (value : α → Coordinate) : List α → Coordinate
  | [] => 0
  | item :: remaining =>
      max (rationalSeparation (value item) 0)
        (sampleEssentialMaximumMagnitude value remaining)

theorem sampleEssentialMaximumMagnitude_nonnegative {α : Type}
    (value : α → Coordinate) : ∀ samples : List α,
    0 ≤ sampleEssentialMaximumMagnitude value samples
  | [] => le_rfl
  | _ :: remaining =>
      le_max_of_le_right
        (sampleEssentialMaximumMagnitude_nonnegative value remaining)

/-- Recursive rational `L∞` distance over a displayed sample list. -/
def sampleEssentialMaximumDistance {α : Type}
    (left right : α → Coordinate) (samples : List α) : Coordinate :=
  sampleEssentialMaximumMagnitude
    (fun item => left item - right item) samples

theorem sampleEssentialMaximumDistance_nonnegative {α : Type}
    (left right : α → Coordinate) (samples : List α) :
    0 ≤ sampleEssentialMaximumDistance left right samples :=
  sampleEssentialMaximumMagnitude_nonnegative
    (fun item => left item - right item) samples

/-- Counting content evaluates a powered magnitude as the exact displayed
sample sum. -/
theorem countingContent_poweredLp {α : Type} (samples : List α)
    (exponent : Nat) (value : α → Coordinate) :
    (countingContent samples).poweredLp exponent value =
      sumValues samples (fun item =>
        rationalSeparation (value item) 0 ^ exponent) :=
  countingContent_integral samples _

theorem countingContent_poweredLpDistance {α : Type}
    (samples : List α) (exponent : Nat)
    (left right : α → Coordinate) :
    (countingContent samples).poweredLpDistance exponent left right =
      sumValues samples (fun item =>
        rationalSeparation (left item) (right item) ^ exponent) :=
  countingContent_integral samples _

/-- Counting content's computed essential maximum is the explicit recursive
maximum over its displayed sample rows. -/
theorem countingContent_essentialMaximumMagnitude {α : Type}
    (samples : List α) (value : α → Coordinate) :
    (countingContent samples).essentialMaximumMagnitude value =
      sampleEssentialMaximumMagnitude value samples := by
  induction samples with
  | nil => rfl
  | cons item remaining inductionHypothesis =>
      unfold countingContent FiniteContent.essentialMaximumMagnitude
      simp only [unitAtoms, essentialMaximumMagnitudeOn]
      have oneNonzero : (1 : Coordinate) ≠ 0 := by decide
      simp only [oneNonzero, ↓reduceIte]
      change max (rationalSeparation (value item) 0)
          ((countingContent remaining).essentialMaximumMagnitude value) = _
      rw [inductionHypothesis]
      rfl

theorem countingContent_essentialMaximumDistance {α : Type}
    (samples : List α) (left right : α → Coordinate) :
    (countingContent samples).essentialMaximumDistance left right =
      sampleEssentialMaximumDistance left right samples := by
  unfold FiniteContent.essentialMaximumDistance
    sampleEssentialMaximumDistance
  exact countingContent_essentialMaximumMagnitude samples
    (fun item => left item - right item)

/-- Exact empirical natural-powered magnitude as a rational sample average. -/
theorem empiricalDistribution_poweredLp {α : Type}
    (samples : List α) (positiveLength : 0 < samples.length)
    (exponent : Nat) (value : α → Coordinate) :
    (empiricalDistribution samples positiveLength).poweredLp exponent value =
      sumValues samples (fun item =>
        rationalSeparation (value item) 0 ^ exponent) /
          (samples.length : Coordinate) := by
  change (empiricalDistribution samples positiveLength).expectation
    (fun item => rationalSeparation (value item) 0 ^ exponent) = _
  exact empiricalDistribution_expectation samples positiveLength _

/-- Exact empirical natural-powered distance as a rational sample average. -/
theorem empiricalDistribution_poweredLpDistance {α : Type}
    (samples : List α) (positiveLength : 0 < samples.length)
    (exponent : Nat) (left right : α → Coordinate) :
    (empiricalDistribution samples positiveLength).poweredLpDistance
        exponent left right =
      sumValues samples (fun item =>
        rationalSeparation (left item) (right item) ^ exponent) /
          (samples.length : Coordinate) := by
  change (empiricalDistribution samples positiveLength).expectation
    (fun item =>
      rationalSeparation (left item) (right item) ^ exponent) = _
  exact empiricalDistribution_expectation samples positiveLength _

theorem empiricalDistribution_poweredL1 {α : Type}
    (samples : List α) (positiveLength : 0 < samples.length)
    (value : α → Coordinate) :
    (empiricalDistribution samples positiveLength).poweredL1 value =
      sumValues samples (fun item => rationalSeparation (value item) 0) /
        (samples.length : Coordinate) := by
  calc
    (empiricalDistribution samples positiveLength).poweredL1 value =
        (empiricalDistribution samples positiveLength).poweredLp 1 value :=
      ((empiricalDistribution samples positiveLength).poweredLp_one value).symm
    _ = sumValues samples (fun item =>
          rationalSeparation (value item) 0 ^ 1) /
        (samples.length : Coordinate) :=
      empiricalDistribution_poweredLp samples positiveLength 1 value
    _ = sumValues samples (fun item => rationalSeparation (value item) 0) /
        (samples.length : Coordinate) :=
      congrArg (fun total => total / (samples.length : Coordinate))
        (sumValues_congr samples _ _ (fun item => pow_one _))

theorem empiricalDistribution_l1Distance {α : Type}
    (samples : List α) (positiveLength : 0 < samples.length)
    (left right : α → Coordinate) :
    (empiricalDistribution samples positiveLength).l1Distance left right =
      sumValues samples (fun item =>
        rationalSeparation (left item) (right item)) /
          (samples.length : Coordinate) := by
  calc
    (empiricalDistribution samples positiveLength).l1Distance left right =
        (empiricalDistribution samples positiveLength).poweredLpDistance
          1 left right :=
      ((empiricalDistribution samples positiveLength)
        |>.poweredLpDistance_one left right).symm
    _ = sumValues samples (fun item =>
          rationalSeparation (left item) (right item) ^ 1) /
        (samples.length : Coordinate) :=
      empiricalDistribution_poweredLpDistance samples positiveLength
        1 left right
    _ = sumValues samples (fun item =>
          rationalSeparation (left item) (right item)) /
        (samples.length : Coordinate) :=
      congrArg (fun total => total / (samples.length : Coordinate))
        (sumValues_congr samples _ _ (fun item => pow_one _))

theorem empiricalDistribution_poweredL2 {α : Type}
    (samples : List α) (positiveLength : 0 < samples.length)
    (value : α → Coordinate) :
    (empiricalDistribution samples positiveLength).poweredL2 value =
      sumValues samples (fun item => value item ^ 2) /
        (samples.length : Coordinate) := by
  calc
    (empiricalDistribution samples positiveLength).poweredL2 value =
        (empiricalDistribution samples positiveLength).poweredLp 2 value :=
      ((empiricalDistribution samples positiveLength).poweredLp_two value).symm
    _ = sumValues samples (fun item =>
          rationalSeparation (value item) 0 ^ 2) /
        (samples.length : Coordinate) :=
      empiricalDistribution_poweredLp samples positiveLength 2 value
    _ = sumValues samples (fun item => value item ^ 2) /
        (samples.length : Coordinate) :=
      congrArg (fun total => total / (samples.length : Coordinate))
        (sumValues_congr samples _ _ (fun item => by
          rw [rationalSeparation_sq]
          ring1))

/-- Consolidating repeated sample payloads preserves the exact powered-Lp
sample average. -/
theorem empiricalHistogram_poweredLp {α : Type} [DecidableEq α]
    (samples : List α) (positiveLength : 0 < samples.length)
    (exponent : Nat) (value : α → Coordinate) :
    (empiricalHistogram samples positiveLength).poweredLp exponent value =
      sumValues samples (fun item =>
        rationalSeparation (value item) 0 ^ exponent) /
          (samples.length : Coordinate) := by
  calc
    (empiricalHistogram samples positiveLength).poweredLp exponent value =
        (empiricalDistribution samples positiveLength).poweredLp
          exponent value :=
      Distribution.EvaluationEquivalent.poweredLp_eq
        (empiricalHistogram_evaluationEquivalent samples positiveLength)
        exponent value
    _ = _ := empiricalDistribution_poweredLp samples positiveLength
      exponent value

theorem empiricalHistogram_poweredLpDistance
    {α : Type} [DecidableEq α]
    (samples : List α) (positiveLength : 0 < samples.length)
    (exponent : Nat) (left right : α → Coordinate) :
    (empiricalHistogram samples positiveLength).poweredLpDistance
        exponent left right =
      sumValues samples (fun item =>
        rationalSeparation (left item) (right item) ^ exponent) /
          (samples.length : Coordinate) := by
  calc
    (empiricalHistogram samples positiveLength).poweredLpDistance
        exponent left right =
      (empiricalDistribution samples positiveLength).poweredLpDistance
        exponent left right :=
      Distribution.EvaluationEquivalent.poweredLpDistance_eq
        (empiricalHistogram_evaluationEquivalent samples positiveLength)
        exponent left right
    _ = _ := empiricalDistribution_poweredLpDistance samples positiveLength
      exponent left right

/-- Every empirical row has positive common scaling, so empirical `L∞` is
exactly the maximum over the original displayed sample. -/
theorem empiricalDistribution_essentialMaximumMagnitude {α : Type}
    (samples : List α) (positiveLength : 0 < samples.length)
    (value : α → Coordinate) :
    Distribution.essentialMaximumMagnitude
        (empiricalDistribution samples positiveLength) value =
      sampleEssentialMaximumMagnitude value samples := by
  let factor : Coordinate := 1 / (samples.length : Coordinate)
  have lengthPositive : (0 : Coordinate) < (samples.length : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_pos_direct positiveLength
  have factorPositive : 0 < factor :=
    RFAP.ConstructiveFraction.div_pos_direct (by decide) lengthPositive
  have factorNonnegative : 0 ≤ factor := factorPositive.le
  change FiniteContent.essentialMaximumMagnitude
      ((countingContent samples).scale factor factorNonnegative) value =
        sampleEssentialMaximumMagnitude value samples
  rw [(countingContent samples).scale_essentialMaximumMagnitude_of_ne
    factor factorNonnegative factorPositive.ne' value]
  exact countingContent_essentialMaximumMagnitude samples value

theorem empiricalDistribution_essentialMaximumDistance {α : Type}
    (samples : List α) (positiveLength : 0 < samples.length)
    (left right : α → Coordinate) :
    Distribution.essentialMaximumDistance
        (empiricalDistribution samples positiveLength) left right =
      sampleEssentialMaximumDistance left right samples := by
  unfold Distribution.essentialMaximumDistance
    FiniteContent.essentialMaximumDistance sampleEssentialMaximumDistance
  exact empiricalDistribution_essentialMaximumMagnitude
    samples positiveLength (fun item => left item - right item)

theorem empiricalHistogram_essentialMaximumMagnitude
    {α : Type} [DecidableEq α]
    (samples : List α) (positiveLength : 0 < samples.length)
    (value : α → Coordinate) :
    Distribution.essentialMaximumMagnitude
        (empiricalHistogram samples positiveLength) value =
      sampleEssentialMaximumMagnitude value samples := by
  calc
    Distribution.essentialMaximumMagnitude
          (empiricalHistogram samples positiveLength) value =
        Distribution.essentialMaximumMagnitude
          (empiricalDistribution samples positiveLength) value :=
      Distribution.EvaluationEquivalent.essentialMaximumMagnitude_eq
        (empiricalHistogram_evaluationEquivalent samples positiveLength)
        value
    _ = _ := empiricalDistribution_essentialMaximumMagnitude
      samples positiveLength value

theorem empiricalHistogram_essentialMaximumDistance
    {α : Type} [DecidableEq α]
    (samples : List α) (positiveLength : 0 < samples.length)
    (left right : α → Coordinate) :
    Distribution.essentialMaximumDistance
        (empiricalHistogram samples positiveLength) left right =
      sampleEssentialMaximumDistance left right samples := by
  calc
    Distribution.essentialMaximumDistance
          (empiricalHistogram samples positiveLength) left right =
        Distribution.essentialMaximumDistance
          (empiricalDistribution samples positiveLength) left right :=
      Distribution.EvaluationEquivalent.essentialMaximumDistance_eq
        (empiricalHistogram_evaluationEquivalent samples positiveLength)
        left right
    _ = _ := empiricalDistribution_essentialMaximumDistance
      samples positiveLength left right

end FiniteMeasure
