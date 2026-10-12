module
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Polynomial.Clearance.Box.Dominance.Basic
public import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Residual
public import Purelib.Polynomial.Dense.Gaussian.Constants
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
@[expose] public section

/-!
# Choice-free local residual extraction

A fixed rational corner of a shrinking box supplies the local sample.  Finite
Horner bounds and the box diagonal bound its residual variation.  If that
sample value were larger than the variation, a finite Rouché contraction to
the nonzero constant path would force raw winding zero.  Thus every proper
nonzero-winding box has an explicitly small rational residual.
-/

namespace Purelib.Polynomial.Clearance.Box.Dominance.Anchor

/-- Positive rational gap available when the anchor residual strictly exceeds
the uniform box variation. -/
def anchorConstantDominanceMargin (p :
  CoefficientPolynomial)
    (ambient small : Box) : Fraction.Rational :=
  Data.Gaussian.Norm.Basic.normSq (p.eval small.anchor) - Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p
    ambient small

/-- An anchor residual above the whole-box variation yields a positive constant-dominance margin. -/
theorem anchorConstantDominanceMargin_pos
    (p : CoefficientPolynomial) (ambient small : Box)
    (large : Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p ambient small <
      Data.Gaussian.Norm.Basic.normSq (p.eval small.anchor)) :
    0 < anchorConstantDominanceMargin p ambient small :=
  Fraction.Order.Arithmetic.sub_pos_direct large

/-- A too-large anchor residual gives one finite norm-dominance certificate
for the constant anchor value over the entire small-box boundary. -/
def anchorBoundaryNormDominance
    (p : CoefficientPolynomial) {ambient small : Box}
    (refines : small.Refines ambient)
    (large : Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p ambient small <
      Data.Gaussian.Norm.Basic.normSq (p.eval small.anchor)) :
    Clearance.Box.Dominance.Basic.BoundaryNormDominance
      (Dense.Gaussian.Constants.gaussianConstant (p.eval small.anchor))
      (p.normalize - Dense.Gaussian.Constants.gaussianConstant (p.eval small.anchor)) small where
  margin := anchorConstantDominanceMargin p ambient small
  positive := anchorConstantDominanceMargin_pos p ambient small large
  lower := by
    intro z boundary
    have variation := Dense.Gaussian.Bounds.Box.Residual.normSq_eval_sub_anchor_le p refines boundary.1
    have dominance := Purelib.Data.Rat.Fraction.Order.Arithmetic.sub_le_sub_left_direct variation
      (Data.Gaussian.Norm.Basic.normSq (p.eval small.anchor))
    simp only [anchorConstantDominanceMargin,
      Dense.Gaussian.Constants.gaussianConstant_eval,
      Dense.Basic.DensePolynomial.eval_sub, Dense.Basic.DensePolynomial.eval_normalize]
    simp only [← Gaussian.Norm.Basic.normSq_eq_canonical]
    exact dominance
end Purelib.Polynomial.Clearance.Box.Dominance.Anchor

end
