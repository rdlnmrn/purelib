module

public import Purelib.Riemann.Normalization.ContinuedInverseRoot
public import Purelib.Geometry.Rational.Box.Enlargement
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot.Bounds
import Purelib.Riemann.Readings.PreparedObservationNeighborhoods
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Monotonicity
import Purelib.Tactic.Ring

/-! # Continued-neighborhood bounds from fixed physical geometry

The original seed residual and a positive radicand floor bound the cached
rootLower from below. The original observation-radius payment bounds every
continued radius by one, including a retained withRadius or accepted grow.
A center in a fixed physical box therefore places the actual neighborhood
inside its one-unit enlargement.
-/

public section

namespace Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood

open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian

/-- A positive original radicand floor computes a positive lower bound for seed-derived rootLower.

The formula uses only the fixed positive floor. It does not select a
seed, root sample, neighborhood or signed continuation owner.
-/
theorem rootFloor_positive {floor : Rational} (positive : 0 < floor) :
    0 < (1 / 4 : Rational) / (2 + 3 / floor) :=
  Order.Field.div_pos_direct (by decide +kernel)
    (Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
      (by decide +kernel : (0 : Rational) ≤ 2)
      (Order.Field.div_pos_direct (by decide +kernel : (0 : Rational) < 3) positive))

/-- The actual cached rootLower has a fixed lower bound from radicand clearance at its original center.

The original Seed.residual_small bounds its same retained value. The
recorded rootLower equation then compares the actual positive denominator
with the fixed scalar ceiling; no seed or root owner is reconstructed.
-/
theorem rootLower_ge {polynomial : CoefficientPolynomial} {count : Nat}
    (patch : ContinuedNeighborhood polynomial count) {floor : Rational}
    (positive : 0 < floor) (lower : floor ≤ Canonical.normSq (polynomial.eval patch.base.site.center)) :
    (1 / 4 : Rational) / (2 + 3 / floor) ≤ patch.rootLower := by
  have seedBound := patch.base.seed.normSq_le positive lower
  have denominator : Canonical.normSq patch.base.seed.value + 1 ≤ 2 + 3 / floor := by
    calc
      _ ≤ (1 + 3 / floor) + 1 := Order.Arithmetic.add_le_add_right_direct seedBound 1
      _ = 2 + 3 / floor := by ring1
  have denominatorPositive : 0 < Canonical.normSq patch.base.seed.value + 1 :=
    Order.Arithmetic.add_pos_of_nonneg_of_pos_direct (Canonical.normSq_nonneg _) (by decide +kernel)
  rewrite [patch.rootLower_eq]
  exact Order.Field.div_le_div_of_nonneg_left_direct
    (by decide +kernel : (0 : Rational) ≤ 1 / 4) denominatorPositive denominator

/-- The actual continued radius is at most one by its original observation-site payment. -/
theorem radius_le_one {polynomial : CoefficientPolynomial} {count : Nat}
    (patch : ContinuedNeighborhood polynomial count) : patch.radius ≤ 1 :=
  patch.radius_le_site.trans patch.base.site.radius_le_one

/-- An actual continued box with center in a fixed physical box refines its one-unit enlargement.

The retained box equation and original radius payment supply all four
endpoint comparisons. This states refinement to the fixed enlargement,
not to a seed box or another independently selected neighborhood.
-/
theorem box_refines_enlarge {polynomial : CoefficientPolynomial} {count : Nat}
    (patch : ContinuedNeighborhood polynomial count) {box : Box}
    (inside : box.Contains patch.base.site.center) :
    patch.box.Refines (box.enlarge 1 (by decide +kernel)) := by
  rewrite [patch.box_eq]
  exact Box.centeredBox_refines_enlarge inside patch.radius_positive.le
    (by decide +kernel) patch.radius_le_one

/-- The same polynomial's retained value and slope folds have fixed enlarged-box ceilings.

Both computations use their original coefficient list. The actual box
refinement controls its finite Horner folds without evaluating a new
point or replacing the continued-neighborhood cache.
-/
theorem horner_le_enlarge {polynomial : CoefficientPolynomial} {count : Nat}
    (patch : ContinuedNeighborhood polynomial count) {box : Box}
    (inside : box.Contains patch.base.site.center) (numerator : CoefficientPolynomial) :
    Bounds.Box.denseEvalNormBound numerator patch.box ≤
        Bounds.Box.denseEvalNormBound numerator (box.enlarge 1 (by decide +kernel)) ∧
      Bounds.Box.denseEvalNormLipschitzBound numerator patch.box ≤
        Bounds.Box.denseEvalNormLipschitzBound numerator (box.enlarge 1 (by decide +kernel)) :=
  Bounds.Box.Monotonicity.denseHornerNormBounds_le_of_refines numerator (patch.box_refines_enlarge inside)

end Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood

end
