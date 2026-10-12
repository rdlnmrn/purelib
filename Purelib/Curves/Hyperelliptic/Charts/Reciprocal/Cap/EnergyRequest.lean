module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.NatCast
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Approximation.Rational

open Purelib.Approximation.Rational.Geometric

open Purelib.Approximation.Rational.Geometric.Basic

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Data.Rat

@[expose] public section

/-!
# Finite accuracy selection for the reciprocal cap energy

Both finite depth selections use cached bounds for the retained polynomial.
The aggregate allowance pays every original cap triangle and the full
dyadic face count. The later geometric construction consumes this request.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives (Sample)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {collar :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {differential :
    Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus} {index : Nat} {box :
    Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box} {domain :
    Purelib.Geometry.Rational.Box}

set_option genInjectivity false in
/-- A finite spatial-depth request paying the original cap Taylor error and complete triangle count.

The cached tolerance and required depth come from the retained polynomial bounds; later depth synchronization preserves
the same target allocation. -/
structure EnergyRequest (bounds : EnergyBounds sample domain) (count : Nat) (target : Fraction.Rational)
  (minimum : Nat) where
  /-- The original requested aggregate energy error is strictly positive. -/ target_positive : 0 < target
  /-- The cached aggregate factor paying the original triangle count and coefficient ceiling. -/ scale :
    Fraction.Rational
  /-- The scale is 128 times the original count times twice the coefficient ceiling plus four. -/ scale_eq : scale = 128
    * (count : Fraction.Rational) * (2 * bounds.coefficient + 4)
  /-- The retained geometric search index for the aggregate tolerance. -/ toleranceIndex : Nat
  /-- The tolerance index is the original finite quarter-radius search for the scaled target. -/ toleranceIndex_eq :
    toleranceIndex = Search.firstQuarterBelow 1 0 (target / (scale + 1))
  /-- The cached positive local Taylor tolerance. -/ epsilon : Fraction.Rational
  /-- The tolerance is the unit geometric quarter-radius at the retained tolerance index. -/ epsilon_eq : epsilon =
    Geometric.Basic.quarterRadius 1 toleranceIndex
  /-- The cached local tolerance is strictly positive. -/ epsilon_positive : 0 < epsilon
  /-- The cached local tolerance is at most one. -/ epsilon_le_one : epsilon ≤ 1
  /-- The cached minimum spatial depth paying the original Taylor remainder. -/ requiredDepth : Nat
  /-- The required depth is the original finite quarter-radius search with the supplied minimum floor. -/
    requiredDepth_eq : requiredDepth = Search.firstQuarterBelow (64 * bounds.remainder) minimum (epsilon ^ 2)
  /-- The retained actual spatial subdivision depth. -/ depth : Nat
  /-- The actual depth is at least the retained accuracy-required depth. -/ requiredDepth_le : requiredDepth ≤ depth
  /-- The actual spatial depth respects the original requested minimum. -/ minimum_le : minimum ≤ depth
  /-- The cached dyadic squared-diameter bound at the actual depth. -/ diameter : Fraction.Rational
  /-- The diameter is the scale-64 geometric quarter-radius at the retained depth. -/ diameter_eq : diameter =
    Geometric.Basic.quarterRadius 64 depth
  /-- The cached tolerance-scaled local radius. -/ radius : Fraction.Rational
  /-- The radius is exactly the original tolerance times the retained diameter. -/ radius_eq : radius = epsilon *
    diameter
  /-- The retained diameter pays the original primitive's Taylor remainder ceiling. -/ taylor : bounds.remainder *
    diameter ≤ epsilon ^ 2
  /-- The cached aggregate allowance for all original cap triangles. -/ total : Fraction.Rational
  /-- The aggregate allowance equals the retained count scale times its original tolerance. -/ total_eq : total = scale
    * epsilon
  /-- The cached complete allowance is strictly below the original requested target. -/ accurate : total < target

constructive_injectivity EnergyRequest

namespace EnergyRequest

variable {bounds : EnergyBounds sample domain} {count :
  Nat} {target : Purelib.Data.Rat.Fraction.Rational} {minimum : Nat}

/-- Select a positive tolerance and spatial depth paying the polynomial remainder and finite triangle count.

The cached scale determines the tolerance search, and the retained remainder
fixes a spatial depth respecting the supplied minimum. Both searches retain
their exact results and certify the aggregate target payment. -/
def build (bounds : EnergyBounds sample domain) (count : Nat) (target : Fraction.Rational) (positive : 0 <
  target) (minimum : Nat) :
    EnergyRequest bounds count target minimum := by
  let scale := 128 * (count : Fraction.Rational) * (2 * bounds.coefficient + 4)
  have countNonnegative : (0 : Fraction.Rational) ≤ (count : Fraction.Rational) := Fraction.Cast.Order.natCast_le_direct
    (Nat.zero_le count)
  have constantNonnegative : (0 : Fraction.Rational) ≤ 128 := by decide +kernel
  have scaleNonnegative : 0 ≤ scale := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct constantNonnegative countNonnegative)
    (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) bounds.coefficient_nonnegative) (by decide))
  have denominatorPositive : 0 < scale + 1 := Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct scaleNonnegative
    (by decide)
  let toleranceIndex := Search.firstQuarterBelow 1 0 (target / (scale + 1))
  let epsilon := Geometric.Basic.quarterRadius 1 toleranceIndex
  have epsilonPositive : 0 < epsilon := Geometric.Basic.quarterRadius_pos (by decide) toleranceIndex
  have tiny : epsilon < target / (scale + 1) := Search.firstQuarterBelow_accurate 1 (by decide) 0 _
    (Fraction.Order.Field.div_pos_direct positive denominatorPositive)
  have paid : epsilon * (scale + 1) < target := (Fraction.Order.Field.lt_div_iff_pos denominatorPositive).mp tiny
  let depth := Search.firstQuarterBelow (64 * bounds.remainder) minimum (epsilon ^ 2)
  let diameter := Geometric.Basic.quarterRadius 64 depth
  refine ⟨positive, scale, rfl, toleranceIndex, rfl, epsilon, rfl, epsilonPositive,
    Geometric.Basic.quarterRadius_le_scale (by decide) toleranceIndex, depth, rfl, depth, le_rfl,
      Search.firstQuarterBelow_ge _ minimum _, diameter, rfl, epsilon * diameter, rfl,
    ?_, scale * epsilon, rfl, ?_⟩
  · have same : bounds.remainder * diameter = Geometric.Basic.quarterRadius (64 * bounds.remainder) depth := by
      simp only [diameter, Geometric.Basic.quarterRadius, Purelib.Data.Rat.Fraction.Field.div_eq_mul_inv_direct]
      ring1
    rw [same]
    exact (Search.firstQuarterBelow_accurate _ (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Cast.Order.natCast_le_direct (by decide : 0 ≤ 64)) bounds.remainder_nonnegative)
      minimum _ (Fraction.Order.Arithmetic.pow_pos_direct epsilonPositive 2)).le
  · have enlarged : scale ≤ scale + 1 := by
      calc
        scale = scale + 0 := by ring1
        _ ≤ scale + 1 := Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl scale) (by decide)
    exact ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct enlarged epsilonPositive.le).trans_eq (by
      ring1)).trans_lt paid

/-- Synchronize several retained requests without repeating their bound calculation or accuracy search. The smaller
diameter preserves Taylor's estimate and the aggregate allowance, including the larger face count. -/
def atDepth (request : EnergyRequest bounds count target
  minimum) (depth : Nat)
    (later : request.depth ≤ depth) : EnergyRequest bounds
      count target minimum := by
  let diameter := Geometric.Basic.quarterRadius 64 depth
  have smaller : diameter ≤ request.diameter := by
    rw [request.diameter_eq]
    exact quarterRadius_antitone (by decide +kernel) later
  exact { request with
    depth := depth
    requiredDepth_le := request.requiredDepth_le.trans later
    minimum_le := request.minimum_le.trans later
    diameter := diameter
    diameter_eq := rfl
    radius := request.epsilon * diameter
    radius_eq := rfl
    taylor := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct smaller
      bounds.remainder_nonnegative).trans request.taylor }

/-- The retained dyadic squared-diameter bound is strictly positive. -/
theorem diameter_positive (request : EnergyRequest bounds count
  target minimum) : 0 < request.diameter := by
  rw [request.diameter_eq]
  exact Geometric.Basic.quarterRadius_pos (Fraction.Cast.Order.natCast_pos_direct (by decide : 0 < 64)) request.depth

/-- The retained tolerance-scaled radius is strictly positive. -/
theorem radius_positive (request : EnergyRequest bounds count
  target minimum) : 0 < request.radius := by
  rw [request.radius_eq]
  exact Fraction.Order.Arithmetic.mul_pos_direct request.epsilon_positive request.diameter_positive

open Purelib.Algebra in
/-- The fine-face count cancels the squared-diameter factor.

At every retained depth, the count is twice four to that depth and the
squared-diameter allowance is the scale-64 quarter radius. Their product
is exactly 128. -/
theorem face_count_cancel (request : EnergyRequest bounds count
  target minimum) :
    ((2 * 4 ^ request.depth : Nat) : Fraction.Rational) * request.diameter = 128 := by
  rw [request.diameter_eq]
  simp only [NatCast.mul, NatCast.pow, Nat.cast_ofNat, Geometric.Basic.quarterRadius]
  calc
    _ = 2 * ((64 / (4 : Fraction.Rational) ^ request.depth) * (4 : Fraction.Rational) ^ request.depth) := by ring1
    _ = _ := by rw [Fraction.Field.div_mul_cancel_of_ne _ _
      (Fraction.Order.Arithmetic.pow_pos_direct (by decide) request.depth).ne']; ring1

end EnergyRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
