module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Measure.Content.Lp.L1
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Content
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Weighted.Integral
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.PositiveNegativePart

import Purelib.Data.Rat.Distance.Basic
import Purelib.Measure.Event.RationalDistance
public import Purelib.Measure.Weighted.Error
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

section
section
public section

/-!
# Finite rational L1 error

The exact integral of pointwise rational separation gives a finite analogue
of L1 distance.  It supports the metric-style inequalities and controls
expectation error by direct finite summation.  Indicator distance is exactly
the probability or content of an executable symmetric difference.

No function-space completion, equivalence class, convergence mode, or limit
is constructed.
-/

namespace Purelib.Measure
namespace Content
end Content

namespace Distribution

section
open Purelib.Data.Rat
/-- Take the original finite distribution's expectation of pointwise rational separation.

Zero-weight occurrences contribute nothing; the exact ordered atom list determines every weighted reading. -/
@[expose] def l1Distance {α : Type} (distribution : Distribution α)
    (left right : α → Fraction.Rational) : Fraction.Rational :=
  distribution.expectation fun item =>
    Distance.rationalSeparation (left item) (right item)

/-- Expected rational separation is nonnegative. -/
theorem l1Distance_nonneg {α : Type} (distribution : Distribution α)
    (left right : α → Fraction.Rational) :
    0 ≤ distribution.l1Distance left right := by
  apply distribution.expectation_nonneg
  intro atom member
  exact Distance.rationalSeparation_nonneg _ _

/-- An observable's expected separation from itself vanishes. -/
theorem l1Distance_refl {α : Type} (distribution : Distribution α)
    (value : α → Fraction.Rational) :
    distribution.l1Distance value value = 0 := by
  change distribution.toContent.l1Distance value value = 0
  exact distribution.toContent.l1Distance_refl value

/-- Exchanging the observables preserves their expected separation. -/
theorem l1Distance_symm {α : Type} (distribution : Distribution α)
    (left right : α → Fraction.Rational) :
    distribution.l1Distance left right =
      distribution.l1Distance right left := by
  exact distribution.expectation_congr _ _ (fun item =>
    Distance.rationalSeparation_symm _ _)

/-- Expected separation obeys the triangle inequality through the same middle observable. -/
theorem l1Distance_triangle {α : Type} (distribution : Distribution α)
    (left middle right : α → Fraction.Rational) :
    distribution.l1Distance left right ≤
      distribution.l1Distance left middle +
        distribution.l1Distance middle right := by
  change distribution.toContent.l1Distance left right ≤
    distribution.toContent.l1Distance left middle +
      distribution.toContent.l1Distance middle right
  exact distribution.toContent.l1Distance_triangle left middle right

/-- The separation of two expected distances to a common anchor is bounded by the expected distance of their first
observables. -/
theorem l1Distance_reverse_triangle {α : Type}
    (distribution : Distribution α)
    (first second anchor : α → Fraction.Rational) :
    Distance.rationalSeparation (distribution.l1Distance first anchor)
        (distribution.l1Distance second anchor) ≤
      distribution.l1Distance first second :=
  distribution.toContent.l1Distance_reverse_triangle
    first second anchor

/-- Expected pointwise separation bounds both signed differences of the original expectations. -/
theorem expectation_close_l1 {α : Type} (distribution : Distribution α)
    (left right : α → Fraction.Rational) :
    distribution.expectation right - distribution.expectation left ≤
        distribution.l1Distance left right ∧
      distribution.expectation left - distribution.expectation right ≤
        distribution.l1Distance left right := by
  change distribution.toContent.integral right -
        distribution.toContent.integral left ≤
      distribution.toContent.l1Distance left right ∧
    distribution.toContent.integral left -
        distribution.toContent.integral right ≤
      distribution.toContent.l1Distance left right
  exact distribution.toContent.integral_close_l1 left right

/-- The separation of two expectations is bounded by their expected pointwise separation. -/
theorem expectation_separation_le_l1Distance {α : Type}
    (distribution : Distribution α) (left right : α → Fraction.Rational) :
    Distance.rationalSeparation (distribution.expectation left)
        (distribution.expectation right) ≤
      distribution.l1Distance left right := by
  have close := distribution.expectation_close_l1 left right
  unfold Distance.rationalSeparation
  exact Fraction.Order.Basic.max_le close.2 close.1

/-- A uniform symmetric error allowance on original atoms bounds expected pointwise separation. -/
theorem l1Distance_le_of_uniform {α : Type}
    (distribution : Distribution α) (epsilon : Fraction.Rational)
    (left right : α → Fraction.Rational)
    (bounded : SymmetricErrorOn distribution.atoms
      (fun _ => epsilon) left right) :
    distribution.l1Distance left right ≤ epsilon := by
  calc
    distribution.l1Distance left right ≤
        distribution.expectation (fun _ => epsilon) := by
      apply distribution.expectation_mono
      intro atom member
      exact Fraction.Order.Basic.max_le (bounded atom member).2 (bounded atom member).1
    _ = epsilon := distribution.expectation_constant epsilon

end

end Distribution
namespace Content
end Content

namespace Distribution

open Purelib.Data.Rat in
/-- For a positive threshold, probability of separation at least that threshold is bounded by expected separation
divided by the threshold. -/
theorem probability_separationAtLeast_le_l1 {α : Type}
    (distribution : Distribution α) (threshold : Fraction.Rational)
    (positive : 0 < threshold) (left right : α → Fraction.Rational) :
    distribution.probability (separationAtLeast threshold left right) ≤
      distribution.l1Distance left right / threshold := by
  apply distribution.markov_bound
    (separationAtLeast threshold left right)
    (fun item => Distance.rationalSeparation (left item) (right item))
    threshold positive
  · intro atom member
    exact Distance.rationalSeparation_nonneg _ _
  · intro atom member selected
    exact of_decide_eq_true selected

/-- Expected distance of two event indicators equals probability of their symmetric difference. -/
theorem l1Distance_indicator {α : Type} (distribution : Distribution α)
    (first second : α → Bool) :
    distribution.l1Distance (indicator first) (indicator second) =
      distribution.probability (symmetricDifferenceEvent first second) := by
  change distribution.toContent.l1Distance
      (indicator first) (indicator second) =
    distribution.toContent.measure
      (symmetricDifferenceEvent first second)
  exact distribution.toContent.l1Distance_indicator first second

/-- Symmetric-difference probability bounds both signed differences of the original event probabilities. -/
theorem probability_close_symmetricDifference {α : Type}
    (distribution : Distribution α) (first second : α → Bool) :
    distribution.probability second - distribution.probability first ≤
        distribution.probability (symmetricDifferenceEvent first second) ∧
      distribution.probability first - distribution.probability second ≤
        distribution.probability (symmetricDifferenceEvent first second) := by
  have bound := distribution.expectation_close_l1
    (indicator first) (indicator second)
  rw [distribution.expectation_indicator,
    distribution.expectation_indicator,
    distribution.l1Distance_indicator] at bound
  exact bound

end Distribution

end Purelib.Measure

end

end

section
public section

/-!
# Root-free finite Lp bounds

Square roots of rational second moments need not be rational.  The primitive
L2 quantity here is therefore the exact powered norm `integral (f^2)`.  Its
Cauchy--Schwarz inequality is stated after squaring, and so remains wholly
rational and executable.
-/

namespace Purelib.Measure

namespace Distribution

section
open Purelib.Data.Rat
/-- Take the expectation of an observable's rational magnitude in the exact original distribution. -/
@[expose] def poweredL1 {α : Type} (distribution : Distribution α)
    (value : α → Fraction.Rational) : Fraction.Rational :=
  distribution.toContent.poweredL1 value

/-- Expected magnitude is nonnegative. -/
theorem poweredL1_nonnegative {α : Type}
    (distribution : Distribution α) (value : α → Fraction.Rational) :
    0 ≤ distribution.poweredL1 value :=
  distribution.toContent.poweredL1_nonnegative value

end

/-- The zero observable has expected magnitude zero. -/
theorem poweredL1_zero {α : Type} (distribution : Distribution α) :
    distribution.poweredL1 (fun _ => 0) = 0 :=
  distribution.toContent.poweredL1_zero

open Purelib.Data.Rat
/-- A constant observable's expected magnitude is its rational magnitude. -/
theorem poweredL1_constant {α : Type} (distribution : Distribution α)
    (constant : Fraction.Rational) :
    distribution.poweredL1 (fun _ => constant) =
      Distance.rationalSeparation constant 0 := by
  change distribution.toContent.poweredL1 (fun _ => constant) = _
  rw [distribution.toContent.poweredL1_constant,
    distribution.toContent_total, one_mul]

/-- Scaling an observable scales expected magnitude by the factor's magnitude. -/
theorem poweredL1_scale {α : Type} (distribution : Distribution α)
    (factor : Fraction.Rational) (value : α → Fraction.Rational) :
    distribution.poweredL1 (fun item => factor * value item) =
      Distance.rationalSeparation factor 0 * distribution.poweredL1 value :=
  distribution.toContent.poweredL1_scale factor value

/-- Negating an observable preserves expected magnitude. -/
theorem poweredL1_neg {α : Type} (distribution : Distribution α)
    (value : α → Fraction.Rational) :
    distribution.poweredL1 (fun item => -value item) =
      distribution.poweredL1 value :=
  distribution.toContent.poweredL1_neg value

/-- Expected magnitude of a sum is at most the sum of the original expected magnitudes. -/
theorem poweredL1_add_le {α : Type} (distribution : Distribution α)
    (left right : α → Fraction.Rational) :
    distribution.poweredL1 (fun item => left item + right item) ≤
      distribution.poweredL1 left + distribution.poweredL1 right :=
  distribution.toContent.poweredL1_add_le left right

/-- Expected magnitude of a difference is at most the sum of the original expected magnitudes. -/
theorem poweredL1_sub_le {α : Type} (distribution : Distribution α)
    (left right : α → Fraction.Rational) :
    distribution.poweredL1 (fun item => left item - right item) ≤
      distribution.poweredL1 left + distribution.poweredL1 right :=
  distribution.toContent.poweredL1_sub_le left right

/-- Expected magnitude of a difference equals expected separation of the original observables. -/
theorem poweredL1_sub_eq_l1Distance {α : Type}
    (distribution : Distribution α) (left right : α → Fraction.Rational) :
    distribution.poweredL1 (fun item => left item - right item) =
      distribution.l1Distance left right :=
  distribution.toContent.poweredL1_sub_eq_l1Distance left right

/-- The separation of expected magnitudes is bounded by expected separation of the original observables. -/
theorem poweredL1_separation_le_l1Distance {α : Type}
    (distribution : Distribution α) (left right : α → Fraction.Rational) :
    Distance.rationalSeparation (distribution.poweredL1 left)
        (distribution.poweredL1 right) ≤
      distribution.l1Distance left right :=
  distribution.toContent.poweredL1_separation_le_l1Distance left right
end Distribution

end Purelib.Measure

end

section
public section

/-!
# Finite Scheffé identities

Two nonnegative rational densities of expectation one define finite
reweighted probability laws.  The executable event where the first density
dominates the second attains their event-probability discrepancy.  Its mass is
the integral of the positive density difference, which equals the negative
part because both densities normalise.  Consequently atomic total variation
is exactly half the original-law L1 density separation.
-/

namespace Purelib.Measure
namespace Distribution

open Purelib in
open Purelib.Data.Rat in
/-- Expected separation is the sum of expectations of the exact positive and negative parts of the pointwise difference.
-/
theorem l1Distance_eq_expectation_positivePart_add_negativePart
    {α : Type} (source : Distribution α)
    (first second : α → Fraction.Rational) :
    source.l1Distance first second =
      source.expectation (fun item =>
        Data.Rat.positiveWeight (first item - second item)) +
      source.expectation (fun item =>
        Data.Rat.negativeWeight (first item - second item)) := by
  unfold l1Distance
  calc
    source.expectation (fun item => Distance.rationalSeparation
        (first item) (second item)) =
        source.expectation (fun item =>
          Data.Rat.positiveWeight (first item - second item) +
            Data.Rat.negativeWeight (first item - second item)) :=
      source.expectation_congr _ _ (fun item => by
        calc
          Distance.rationalSeparation (first item) (second item) =
              Distance.rationalSeparation (first item - second item) 0 := by
            unfold Distance.rationalSeparation
            congr 1 <;> ring1
          _ = Data.Rat.positiveWeight (first item - second item) +
              Data.Rat.negativeWeight (first item - second item) :=
            Data.Rat.rationalSeparation_zero_eq_parts _)
    _ = source.expectation (fun item =>
          Data.Rat.positiveWeight (first item - second item)) +
        source.expectation (fun item =>
          Data.Rat.negativeWeight (first item - second item)) :=
      source.expectation_add _ _
end Distribution

end Purelib.Measure

end
