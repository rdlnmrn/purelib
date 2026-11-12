module

public import Purelib.Approximation.Rational.Pi.Polygon
public import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.RationalEmbedding
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-!
# Finite rational polygon approximation to pi

The sampler evaluates the first quarter's signed fan triangles and multiplies
their sum by four. The existing shoelace theorem identifies that computation
with the actual inscribed polygon area at every dyadic stage. Its coherence
and finite refinement use the independently proved endpoint enclosures.
-/

namespace Purelib.Approximation.Gaussian.Pi.Polygon

open Purelib.Approximation
open Purelib.Approximation.Gaussian.Sequence
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Geometry.Gaussian
open Purelib.Integration

/-- The actual dyadic polygon area stays between two and four. -/
public theorem area_bounds (stage : Nat) :
    2 ≤ UnitCircle.Polygon.area (Rational.Pi.Polygon.dyadicExtra stage) ∧
      UnitCircle.Polygon.area (Rational.Pi.Polygon.dyadicExtra stage) ≤ 4 := by
  have nested := Rational.Pi.Polygon.dyadic_frontier_refines (Nat.zero_le stage)
  have inside := nested.contains (Rational.Pi.Polygon.area_in_frontier
    (Rational.Pi.Polygon.dyadicExtra stage))
  have lower : (integralBound (Rational.Pi.Endpoint.frontier 0).cells).lower = 2 := by decide
  have upper : (integralBound (Rational.Pi.Endpoint.frontier 0).cells).upper = 4 := by decide
  change (integralBound (Rational.Pi.Endpoint.frontier 0).cells).lower ≤
      UnitCircle.Polygon.area (Rational.Pi.Polygon.dyadicExtra stage) ∧
    UnitCircle.Polygon.area (Rational.Pi.Polygon.dyadicExtra stage) ≤
      (integralBound (Rational.Pi.Endpoint.frontier 0).cells).upper at inside
  rw [lower] at inside
  rw [upper] at inside
  exact inside

/-- The dyadic observation evaluates the original first-quarter geometry and embeds its real area. -/
@[expose] public def sample (stage : Nat) : Basic.Canonical :=
  RationalEmbedding.realPoint (UnitCircle.Polygon.quarterArea (Rational.Pi.Polygon.dyadicExtra stage))

/-- The optimized sample is the real embedding of the actual full polygon's shoelace area. -/
public theorem sample_eq_area (stage : Nat) :
    sample stage = RationalEmbedding.realPoint
      (UnitCircle.Polygon.area (Rational.Pi.Polygon.dyadicExtra stage)) := by
  rw [sample, UnitCircle.Polygon.quarterArea_eq_area]

/-- Every finite polygon sample has zero imaginary coordinate. -/
public theorem sample_im_zero (stage : Nat) : (sample stage).im = 0 := by
  rw [sample_eq_area, RationalEmbedding.realPoint_im]

/-- Every polygon sample has squared norm at most sixteen. -/
public theorem sample_bounded (stage : Nat) : Norm.Basic.normSq (sample stage) ≤ 16 := by
  rw [sample_eq_area, RationalEmbedding.normSq_realPoint]
  have bounds := area_bounds stage
  have nonnegative : 0 ≤ UnitCircle.Polygon.area (Rational.Pi.Polygon.dyadicExtra stage) :=
    (show (0 : Fraction.Rational) ≤ 2 by decide).trans bounds.1
  have squared := Arithmetic.pow_le_pow_direct nonnegative bounds.2 2
  have fourSquare : (4 : Fraction.Rational) ^ 2 = 16 := by decide
  rw [fourSquare] at squared
  exact squared

/-- The quarter-only polygon sampler carries its finite geometric error and refinement data.

The squared allowance is four times the quarter-power schedule. The bounded
selector preserves the supplied stage floor and pays each positive request. -/
@[expose] public def approximation : ApproximationData where
  sample := sample
  radiusSq := Rational.Geometric.Basic.quarterRadius 4
  radiusSq_nonneg := Rational.Geometric.Basic.quarterRadius_nonneg (by decide)
  later_close := by
    intro earlier later ordered
    rw [sample_eq_area, sample_eq_area, Rational.Geometric.Basic.quarterRadius_eq_mul_pow]
    exact Rational.Pi.Polygon.dyadic_area_normSq_difference_le_quarter ordered
  refineIndex current target _ := Rational.Geometric.Search.firstQuarterBelow 4 current target
  refineIndex_ge current target _ := Rational.Geometric.Search.firstQuarterBelow_ge 4 current target
  refineIndex_accurate := Rational.Geometric.Search.firstQuarterBelow_accurate 4 (by decide)
  centerBound := 16
  centerBound_nonneg := by decide
  sample_bounded := sample_bounded

/-- The independently coherent name whose finite samples are inscribed-polygon areas. -/
@[expose] public def named : Name.Coherent.CoherentNamed :=
  Name.Coherent.CoherentNamed.ofApproximation approximation

end Purelib.Approximation.Gaussian.Pi.Polygon
