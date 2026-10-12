module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Riemann.Readings.PreparedObservationNeighborhoods
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Subdivision
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Substitution.Affine

public import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Tactic.Ring

open Purelib.Riemann.Normalization.InverseRootPolynomial

@[expose] public section

/-!
# Checked larger continuation neighborhoods

Cache the translated polynomial difference `P(center + z) - P(center)` and
its exact finite Horner bound on a proposed radius.  This detects cancellation
before bounding, including zero variation for constant polynomials.  A checked
larger radius reuses the existing seed and polynomial model; failure retains
the already proved default patch.  Generated caches use the same interface.
-/

namespace Purelib.Riemann.Integration.CheckedPrimitiveNeighborhoods

open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.OwnerSeededInverseRoot (SeededNeighborhood)

open Purelib.Data.Gaussian.Basic.Canonical

section
open Purelib.Data
/-- Rational coordinates and squared error bounds. -/
abbrev Coordinate := Rat.Fraction.Rational
/-- Gaussian rational values of the translated polynomial. -/
abbrev Gaussian := Gaussian.Basic.Canonical
end

open Purelib.Polynomial in
/-- Dense polynomials with Gaussian rational coefficients. -/
abbrev Polynomial := Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
open Purelib.Geometry in
/-- Closed rational boxes for polynomial evaluation. -/
abbrev Box := Rational.Box

set_option genInjectivity false in
/-- A retained polynomial representing the change from a fixed center.

Its evaluation at a translated argument is exactly the original polynomial's increment, allowing coefficient
cancellation before a radius bound is computed. -/
structure Variation (polynomial : Polynomial) (center : Gaussian) where
  /-- The cached polynomial in the translated coordinate. -/ value : Polynomial
  /-- Evaluation of the cache equals the original polynomial increment. -/ eval_eq : ∀ point, value.eval (point -
    center) = polynomial.eval point - polynomial.eval center

constructive_injectivity Variation

namespace Variation

open Purelib.Polynomial in
/-- Translate the polynomial, subtract its central value, and normalize the coefficients.

The resulting cache carries an exact evaluation identity for every point. -/
def build (polynomial : Polynomial) (center : Gaussian) : Variation polynomial center where
  value := (Dense.Gaussian.Substitution.Affine.composeLine polynomial center 1 -
    Dense.Basic.DensePolynomial.constant (polynomial.eval center)).normalize
  eval_eq := by
    intro point
    rw [Dense.Basic.DensePolynomial.eval_normalize,
      Dense.Basic.DensePolynomial.eval_sub,
      Dense.Basic.DensePolynomial.eval_constant,
      Dense.Gaussian.Substitution.Affine.eval_composeLineGaussian]
    rw [show center + (point - center) * 1 = point by ring1]

end Variation

open Purelib.Polynomial in
open Purelib.Geometry in
set_option genInjectivity false in
/-- A cached symmetric test box and finite bound for a translated polynomial.

The box and norm bound retain their exact defining equalities at the supplied positive radius. -/
structure RadiusBound {polynomial : Polynomial} {center : Gaussian}
    (variation : Variation polynomial center) (radius : Coordinate) (positive : 0 < radius) where
  /-- The retained symmetric test box. -/ box : Box
  /-- The box is centered at zero with the specified radius. -/ box_eq : box = Rational.Box.symmetric
    radius positive.le
  /-- The cached squared norm bound on the translated polynomial. -/ normBound : Coordinate
  /-- The cache equals the finite coefficient bound on the retained box. -/ normBound_eq : normBound =
    Dense.Gaussian.Bounds.Box.denseEvalNormBound variation.value box

constructive_injectivity RadiusBound

namespace RadiusBound

variable {polynomial : Polynomial} {center : Gaussian} {variation : Variation polynomial center}
  {radius : Coordinate} {positive : 0 < radius}

open Purelib.Polynomial in
open Purelib.Geometry in
/-- Compute and retain the symmetric box and its polynomial norm bound. -/
def build (variation : Variation polynomial center) (radius : Coordinate) (positive : 0 < radius) :
    RadiusBound variation radius positive :=
  let box := Rational.Box.symmetric radius positive.le
  { box := box
    box_eq := rfl
    normBound := Dense.Gaussian.Bounds.Box.denseEvalNormBound variation.value box
    normBound_eq := rfl }

open Purelib.Data in
open Purelib.Geometry in
/-- Translate a point in the centered radius box into the symmetric box at zero. -/
private theorem translated_inside {point : Gaussian}
    (inside : (Rational.Box.Square.Centered.BoxTransport.centeredBox center radius positive.le).Contains point) :
    (Rational.Box.symmetric radius positive.le).Contains (point - center) := by
  have shifted {coordinate value : Coordinate}
      (bounds : coordinate - radius ≤ value ∧ value ≤ coordinate + radius) :
      -radius ≤ value - coordinate ∧ value - coordinate ≤ radius := by
    constructor
    · calc
        -radius = (coordinate - radius) - coordinate := by ring1
        _ ≤ value - coordinate := Rat.Fraction.Order.Arithmetic.sub_le_sub_right_direct bounds.1 _
    · calc
        value - coordinate ≤ (coordinate + radius) - coordinate :=
          Rat.Fraction.Order.Arithmetic.sub_le_sub_right_direct bounds.2 _
        _ = radius := by ring1
  have realBounds := shifted ⟨inside.1, inside.2.1⟩
  have imaginaryBounds := shifted ⟨inside.2.2.1, inside.2.2.2⟩
  exact ⟨realBounds.1, realBounds.2, imaginaryBounds.1, imaginaryBounds.2⟩

open Purelib.Data in
open Purelib.Polynomial in
open Purelib.Geometry in
/-- Bound the polynomial's change from the center by the cached variation bound.

The point must lie in the centered box at the same positive radius. -/
theorem movement_le (bound : RadiusBound variation radius positive) {point : Gaussian}
    (inside : (Rational.Box.Square.Centered.BoxTransport.centeredBox center radius positive.le).Contains point) :
    normSq (polynomial.eval center - polynomial.eval point) ≤ bound.normBound := by
  have deltaInside : bound.box.Contains (point - center) := by
    rw [bound.box_eq]
    exact translated_inside (positive := positive) inside
  have evaluated := Dense.Gaussian.Bounds.Box.normSq_eval_le_denseEvalNormBound variation.value deltaInside
  rw [variation.eval_eq, ← bound.normBound_eq, Gaussian.Norm.Basic.normSq_eq_canonical] at evaluated
  have reverse : polynomial.eval center - polynomial.eval point = -(polynomial.eval point - polynomial.eval center) :=
    by ring1
  rw [reverse, Gaussian.Basic.Canonical.normSq_neg]
  exact evaluated

end RadiusBound

variable {polynomial : Polynomial} {count : Nat}

/-- Replace a continuation radius using a certified polynomial variation bound.

The new positive radius remains within the base model, and its cached variation must be strictly smaller than the
existing continuation allowance. -/
def ofBound (patch : ContinuedNeighborhood polynomial count) {radius : Coordinate} (positive : 0 < radius)
    (baseBound : radius ≤ patch.base.radius)
    {variation : Variation polynomial patch.base.site.center} (bound : RadiusBound variation radius positive)
    (small : bound.normBound < patch.continuationAllowance) : ContinuedNeighborhood polynomial count :=
  patch.withRadius radius positive baseBound (fun _ inside => (bound.movement_le inside).trans_lt small)

/-- Test the base model's radius for a larger continuation neighborhood.

Compute its translated variation once; accept the radius when its bound fits the existing allowance, otherwise retain
the original patch. -/
def grow (patch : ContinuedNeighborhood polynomial count) : ContinuedNeighborhood polynomial count :=
  let variation := Variation.build polynomial patch.base.site.center
  let bound := RadiusBound.build variation patch.base.radius patch.base.radius_positive
  if small : bound.normBound < patch.continuationAllowance then
    ofBound patch patch.base.radius_positive le_rfl bound small
  else patch

/-- The finite growth test never decreases the continuation radius. -/
theorem grow_radius_ge (patch : ContinuedNeighborhood polynomial count) : patch.radius ≤ (grow patch).radius := by
  unfold grow
  dsimp only
  split
  · exact patch.radius_le_base
  · exact le_rfl

/-- The growth test preserves the exact base neighborhood. -/
theorem grow_base (patch : ContinuedNeighborhood polynomial count) : (grow patch).base = patch.base := by
  unfold grow
  dsimp only
  split <;> rfl

/-- The growth test preserves the continuation allowance. -/
theorem grow_allowance (patch : ContinuedNeighborhood polynomial count) :
    (grow patch).continuationAllowance = patch.continuationAllowance := by
  unfold grow
  dsimp only
  split <;> rfl

open Purelib.Riemann in
/-- The original continuation box is contained in the box returned by the growth test. -/
theorem grow_box_refines (patch : ContinuedNeighborhood polynomial count) : patch.box.Refines (grow patch).box := by
  rw [patch.box_eq, (grow patch).box_eq]
  have center := congrArg (fun base : SeededNeighborhood polynomial count => base.site.center) (grow_base patch)
  rw [center]
  exact Readings.PreparedObservationNeighborhoods.centeredBox_refines _ patch.radius_positive.le
    (grow patch).radius_positive.le (grow_radius_ge patch)

end Purelib.Riemann.Integration.CheckedPrimitiveNeighborhoods
