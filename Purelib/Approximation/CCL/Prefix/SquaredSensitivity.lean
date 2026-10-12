module
import Purelib.CCL.Measure.Basic
public import Purelib.Approximation.CCL.Cylinder.Spread
import Purelib.Approximation.Rational.Budget.Dyadic
import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Data.CCL.Encoding.Cylinder
import Purelib.Data.CCL.Encoding.Cylinder.Basic
public import Purelib.Data.CCL.Encoding.Cylinder.Projective
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Quadratic.Bounds
public import Purelib.Geometry.Projective.Chordal.Probe.Sensitivity
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Data.Rat.Bounds.Square
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Approximation.CCL

open Purelib.Approximation.Rational

open Purelib.CCL.Measure

open Purelib.Data.CCL.Encoding

open Purelib.Data.CCL.Encoding.Cylinder

open Purelib.Data.CCL.Encoding.Cylinder.Basic

open Purelib.Data.CCL.Encoding.Cylinder.Projective

open Purelib.Data.Rat

open Purelib.Geometry.Projective.Chordal

open Purelib.Geometry.Projective.Line.Basic

section
public section

/-!
# Root-free L2 stability of finite CCL prefix probes

Direct Lipschitz control by `chordalSq` is stronger than is natural for many
nonconstant projective observables.  This module instead accepts the
square-root-free estimate

`rationalSeparation (probe x) (probe y) ^ 2 ≤ factor * chordalSq x y`.

CCL cylinder contraction then controls exact finite powered-L2 distances.
Finite Cauchy--Schwarz transfers that control to squared expectation error,
and a request at the square of a supplied rational tolerance recovers an
ordinary strict expectation-separation theorem.  No square root is selected.
-/

namespace Purelib.Approximation.CCL.Prefix

/-- Canonical CCL realizations inherit the squared probe-separation budget of their completed prefix. -/
theorem realized_probe_separation_sq_le
    {blocks : List Data.CCL.Encoding.Block} {leftPoint rightPoint : Geometry.Projective.Line.GaussianLine}
    (leftRealizes : Cylinder.Basic.Realizes blocks leftPoint)
    (rightRealizes : Cylinder.Basic.Realizes blocks rightPoint)
    (probe : Geometry.Projective.Line.GaussianLine → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : Probe.SquaredProbeSensitive probe factor) :
    Distance.rationalSeparation
        (probe leftPoint) (probe rightPoint) ^ 2 ≤
      factor * Cylinder.cylinderSpread blocks := by
  exact (sensitive leftPoint rightPoint
    (Cylinder.canonicalRealizes_valid leftRealizes)
    (Cylinder.canonicalRealizes_valid rightRealizes)).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Realizes.chordalSq_le_half_pow
        leftRealizes rightRealizes)
      factorNonnegative)

/-- The same squared budget applies to exact projectively rescaled encoder traces. -/
theorem projectiveRealized_probe_separation_sq_le
    {blocks : List Data.CCL.Encoding.Block} {leftPoint rightPoint : Geometry.Projective.Line.GaussianLine}
    (leftRealizes : Projective.ProjectiveRealizes blocks leftPoint)
    (rightRealizes : Projective.ProjectiveRealizes blocks rightPoint)
    (probe : Geometry.Projective.Line.GaussianLine → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : Probe.SquaredProbeSensitive probe factor) :
    Distance.rationalSeparation
        (probe leftPoint) (probe rightPoint) ^ 2 ≤
      factor * Cylinder.cylinderSpread blocks := by
  exact (sensitive leftPoint rightPoint leftRealizes.valid
    rightRealizes.valid).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (ProjectiveRealizes.chordalSq_le_half_pow
        leftRealizes rightRealizes)
      factorNonnegative)

/-- Meeting the squared-probe request makes one sensitivity-scaled cylinder budget at most half the square of the
supplied rational tolerance. -/
theorem scaledCylinderSpread_le_half_sq_of_requested
    {blocks : List Data.CCL.Encoding.Block} (epsilon factor : Coordinate)
    (epsilonPositive : 0 < epsilon) (factorPositive : 0 < factor)
    (enough : Budget.requiredSquaredProbeBlockCount epsilon factor ≤
      blocks.length) :
    factor * Cylinder.cylinderSpread blocks ≤ epsilon ^ 2 / 2 := by
  have squarePositive : 0 < epsilon ^ 2 :=
    Fraction.Order.Arithmetic.pow_pos_direct epsilonPositive 2
  have halfPositive : 0 < epsilon ^ 2 / 2 :=
    Fraction.Order.Field.div_pos_direct squarePositive (by decide)
  have targetPositive : 0 < (epsilon ^ 2 / 2) / factor :=
    Fraction.Order.Field.div_pos_direct halfPositive factorPositive
  have spreadSmall : Cylinder.cylinderSpread blocks <
      (epsilon ^ 2 / 2) / factor :=
    Cylinder.cylinderSpread_lt_of_requiredBlockCount_le targetPositive enough
  calc
    factor * Cylinder.cylinderSpread blocks ≤
        factor * ((epsilon ^ 2 / 2) / factor) :=
      (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
        factorPositive spreadSmall).le
    _ = epsilon ^ 2 / 2 := by
      calc
        factor * ((epsilon ^ 2 / 2) / factor) =
            ((epsilon ^ 2 / 2) / factor) * factor :=
          Fraction.Field.mul_comm _ _
        _ = epsilon ^ 2 / 2 :=
          Fraction.Field.div_mul_cancel_of_ne
            (epsilon ^ 2 / 2) factor factorPositive.ne'

/-- A completed canonical prefix meeting the computed squared-probe request makes every two of its realizations strictly
closer than the supplied positive rational probe tolerance. -/
theorem realizedSquaredProbe_separation_lt_of_requested
    {blocks : List Data.CCL.Encoding.Block} {leftPoint rightPoint : Geometry.Projective.Line.GaussianLine}
    (leftRealizes : Cylinder.Basic.Realizes blocks leftPoint)
    (rightRealizes : Cylinder.Basic.Realizes blocks rightPoint)
    (probe : Geometry.Projective.Line.GaussianLine → Coordinate) (factor : Coordinate)
    (factorPositive : 0 < factor)
    (sensitive : Probe.SquaredProbeSensitive probe factor)
    (epsilon : Coordinate) (epsilonPositive : 0 < epsilon)
    (enough : Budget.requiredSquaredProbeBlockCount epsilon factor ≤
      blocks.length) :
    Distance.rationalSeparation
        (probe leftPoint) (probe rightPoint) < epsilon := by
  have squaredLe := Approximation.CCL.Prefix.realized_probe_separation_sq_le leftRealizes rightRealizes
    probe factor factorPositive.le sensitive
  have budgetLe := Approximation.CCL.Prefix.scaledCylinderSpread_le_half_sq_of_requested epsilon factor
    epsilonPositive factorPositive enough
  have squaresSmall := squaredLe.trans_lt
    (budgetLe.trans_lt (Quadratic.Bounds.half_sq_lt_sq epsilonPositive))
  exact Bounds.Square.lt_of_sq_lt_sq_of_nonneg epsilonPositive.le squaresSmall

/-- Projectively rescaled realizations meeting the same finite request obey the same strict rational probe-separation
bound. -/
theorem projectiveRealizedSquaredProbe_separation_lt_of_requested
    {blocks : List Data.CCL.Encoding.Block} {leftPoint rightPoint : Geometry.Projective.Line.GaussianLine}
    (leftRealizes : Projective.ProjectiveRealizes blocks leftPoint)
    (rightRealizes : Projective.ProjectiveRealizes blocks rightPoint)
    (probe : Geometry.Projective.Line.GaussianLine → Coordinate) (factor : Coordinate)
    (factorPositive : 0 < factor)
    (sensitive : Probe.SquaredProbeSensitive probe factor)
    (epsilon : Coordinate) (epsilonPositive : 0 < epsilon)
    (enough : Budget.requiredSquaredProbeBlockCount epsilon factor ≤
      blocks.length) :
    Distance.rationalSeparation
        (probe leftPoint) (probe rightPoint) < epsilon := by
  have squaredLe := Approximation.CCL.Prefix.projectiveRealized_probe_separation_sq_le
    leftRealizes rightRealizes probe factor factorPositive.le sensitive
  have budgetLe := Approximation.CCL.Prefix.scaledCylinderSpread_le_half_sq_of_requested epsilon factor
    epsilonPositive factorPositive enough
  have squaresSmall := squaredLe.trans_lt
    (budgetLe.trans_lt (Quadratic.Bounds.half_sq_lt_sq epsilonPositive))
  exact Bounds.Square.lt_of_sq_lt_sq_of_nonneg epsilonPositive.le squaresSmall

end Purelib.Approximation.CCL.Prefix

end
