module
import Purelib.Polynomial.Dense.Gaussian.Degree
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Constant
import Purelib.Polynomial.Clearance.Box.Dominance.Anchor
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Residual
import Purelib.Polynomial.Dense.Gaussian.Constants
public import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Winding.Box.Constant
import Purelib.Polynomial.Winding.Box.Rouche
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Evaluation

/-!
# Anchor residuals from nonzero box winding

The same finite anchor variation and boundary-dominance certificates
compare the retained polynomial with its nonzero constant anchor value.
-/

namespace Purelib.Polynomial.Winding.Box.Residual

open Purelib.Data
open Purelib.Geometry.Rational
open Purelib.Polynomial

/-- If the anchor value exceeded the uniform variation, constructive Rouché
would contract the normalized polynomial to a nonzero constant and force raw
winding zero.

The polynomial has positive degree and the proper smaller box refines the
original ambient box. Its retained anchor value strictly dominates the
finite residual variation, so the same boundary-dominance certificate
transfers winding to the nonzero constant polynomial. -/
public theorem quadrupledBoxWinding_eq_zero_of_anchorResidualBound_lt
    (p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) {ambient small : Box}
    (degreePositive : 0 < p.natDegree)
    (refines : small.Refines ambient) (proper : small.Proper)
    (large : Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p ambient small <
      Data.Gaussian.Norm.Basic.normSq (p.eval small.anchor)) :
    Winding.Box.Basic.quadrupledBoxWinding p small = 0 := by
  have polynomialNonzero := Dense.Gaussian.Degree.Global.isZero_false_of_natDegree_pos degreePositive
  have anchorValueNonzero : p.eval small.anchor ≠ 0 := by
    intro zero
    have boundNonnegative := Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound_nonneg p ambient small
    rw [zero, Gaussian.Norm.Basic.normSq_zero] at large
    exact (not_lt_of_ge boundNonnegative) large
  have sumIdentity :
      Dense.Gaussian.Constants.gaussianConstant (p.eval small.anchor) +
          (p.normalize - Dense.Gaussian.Constants.gaussianConstant (p.eval small.anchor)) =
        p.normalize :=
    Dense.Basic.DensePolynomial.constant_add_sub_constant_of_normalized
      (Dense.Basic.DensePolynomial.normalize_normalize p) (by simpa using polynomialNonzero)
      (by simpa using degreePositive) anchorValueNonzero
  have transfer := Winding.Box.Rouche.quadrupledBoxWinding_add_of_boundaryNormDominance
    (Dense.Gaussian.Constants.gaussianConstant (p.eval small.anchor))
    (p.normalize - Dense.Gaussian.Constants.gaussianConstant (p.eval small.anchor)) small proper
    (Clearance.Box.Boundary.Constant.gaussianConstant_boundaryClearance anchorValueNonzero small)
    (Clearance.Box.Dominance.Anchor.anchorBoundaryNormDominance p refines large)
  rw [sumIdentity] at transfer
  calc
    Winding.Box.Basic.quadrupledBoxWinding p small =
        Winding.Box.Basic.quadrupledBoxWinding p.normalize small :=
      (Winding.Box.Basic.quadrupledBoxWinding_normalize p small).symm
    _ = Winding.Box.Basic.quadrupledBoxWinding
          (Dense.Gaussian.Constants.gaussianConstant (p.eval small.anchor)) small := transfer
    _ = 0 := Winding.Box.Constant.quadrupledBoxWinding_gaussianConstant anchorValueNonzero small

/-- Nonzero raw winding forces an explicitly small rational anchor residual.

The original positive-degree polynomial has nonzero raw winding on the
retained proper subbox. Comparing the same anchor quadrance and finite
variation either gives the stated bound directly or contradicts the
constant-polynomial winding transfer. -/
public theorem anchor_residual_le_of_quadrupledBoxWinding_ne_zero
    (p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) {ambient small : Box}
    (degreePositive : 0 < p.natDegree)
    (refines : small.Refines ambient) (proper : small.Proper)
    (windingNonzero : Winding.Box.Basic.quadrupledBoxWinding p small ≠ 0) :
    Data.Gaussian.Norm.Basic.normSq (p.eval small.anchor) ≤
      Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p ambient small := by
  by_cases residualSmall : Data.Gaussian.Norm.Basic.normSq (p.eval small.anchor) ≤
      Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p ambient small
  · exact residualSmall
  · have large : Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p ambient small <
        Data.Gaussian.Norm.Basic.normSq (p.eval small.anchor) := lt_of_not_ge residualSmall
    exact (windingNonzero
      (quadrupledBoxWinding_eq_zero_of_anchorResidualBound_lt
        p degreePositive refines proper large)).elim

end Purelib.Polynomial.Winding.Box.Residual
