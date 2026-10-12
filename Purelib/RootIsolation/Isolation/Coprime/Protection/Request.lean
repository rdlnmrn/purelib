module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Residual
import Purelib.Polynomial.Dense.Gaussian.Constants
import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
import Purelib.Polynomial.Dense.Gaussian.Coprime.Bounds.Box
public import Purelib.Polynomial.Dense.Gaussian.Coprime.Bounds.Protection
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Winding.Box.Constant
import Purelib.Polynomial.Winding.Box.Residual
import Purelib.RootIsolation.State.WindingOne.Basic
public import Purelib.RootIsolation.Track.Basic
import Purelib.RootIsolation.Winding.Bounds.Residual
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Coprime.Basic (CoprimeCertificate)
open Purelib.RootIsolation.State.WindingOne.Basic (WindingOneState)
open Purelib.RootIsolation.Track.Basic (WindingOneTrack)

public section

/-!
# Quantitative finite bounds for two coprime polynomials

This module extracts the reusable two-polynomial content of the squarefree
derivative-margin argument.  A displayed Bézout certificate gives an explicit
threshold below which a small value of the left polynomial forces a positive
lower bound for the right polynomial.  Applying the estimate to every point
of a sufficiently refined winding-one box supplies boundary clearance and
zero winding for the other polynomial.
-/

namespace Purelib.RootIsolation.Isolation.Coprime.Protection.Request

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.RootIsolation

/-! ## Protection at any smaller positive request -/

/-- Refine a winding-one track at an explicitly supplied positive request.

The following lemmas require that request to be no larger than the relevant
Bézout protection radius. -/
@[expose] def protectedStateAt
    {p : CoefficientPolynomial} {pAmbient : Box}
    (track : WindingOneTrack p pAmbient)
    (current : WindingOneState p pAmbient)
    (request : Fraction.Rational) (requestPositive : 0 < request) :
    WindingOneState p pAmbient :=
  track.refine current request requestPositive

section
/-- A positive request below the protection radius has square at most itself. -/
private theorem request_sq_le
    {p q : CoefficientPolynomial} (coprime :
      CoprimeCertificate p q)
    (pAmbient : Box) {request : Fraction.Rational} (requestPositive : 0 < request)
    (requestLe : request ≤ Dense.Gaussian.Coprime.Bounds.Protection.protectionRadius coprime pAmbient) :
    request ^ 2 ≤ request := by
  have requestLeOne : request ≤ 1 :=
    requestLe.trans (Fraction.Order.Basic.min_le_left _ _)
  rw [pow_two]
  exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    requestLeOne requestPositive.le).trans_eq (_root_.one_mul request)
end

/-- The requested protected refinement meets the left polynomial's original residual threshold. -/
theorem protectedStateAt_left_small
    {p q : CoefficientPolynomial} {pAmbient : Box}
    (pDegreePositive : 0 < p.natDegree)
    (coprime : CoprimeCertificate p q)
    (track : WindingOneTrack p pAmbient)
    (current : WindingOneState p pAmbient)
    {request : Fraction.Rational} (requestPositive : 0 < request)
    (requestLe : request ≤ Dense.Gaussian.Coprime.Bounds.Protection.protectionRadius coprime pAmbient)
    {z : Gaussian.Basic.Canonical}
    (inside : (protectedStateAt track current request requestPositive).box.Contains
      z) :
    Data.Gaussian.Norm.Basic.normSq (p.eval z) ≤ Dense.Gaussian.Coprime.Bounds.Box.leftThreshold coprime pAmbient :=
      by
  let state := protectedStateAt track current request requestPositive
  have residual := Winding.Bounds.Residual.normSq_eval_le_four_lipschitz_diagonal
    pDegreePositive state inside
  have diagonal := track.accurate current request requestPositive
  have requestSquare := request_sq_le coprime pAmbient
    requestPositive requestLe
  have radiusBudget : request ≤ Dense.Gaussian.Coprime.Bounds.Box.leftThreshold coprime pAmbient /
      (8 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p pAmbient) :=
    requestLe.trans ((Fraction.Order.Basic.min_le_right (1 : Fraction.Rational) _).trans
      (Fraction.Order.Basic.min_le_left _ _))
  have scaled : request * (8 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p pAmbient) ≤
      Dense.Gaussian.Coprime.Bounds.Box.leftThreshold coprime pAmbient :=
    (Fraction.Order.Field.le_div_iff_pos
      (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
        (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos p pAmbient))).mp radiusBudget
  calc
    Data.Gaussian.Norm.Basic.normSq (p.eval z) ≤
        4 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p pAmbient * state.box.diagonalSq := by simpa only
          [Gaussian.Norm.Basic.normSq_eq_canonical] using residual
    _ ≤ 4 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p pAmbient * request ^ 2 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct diagonal
        (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
          (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos p pAmbient)).le
    _ ≤ 4 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p pAmbient * request :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct requestSquare
        (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
          (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos p pAmbient)).le
    _ ≤ request * (8 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p pAmbient) := by
      have coefficient :
          4 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p pAmbient ≤
            8 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p pAmbient :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (show (4 : Fraction.Rational) ≤ 8 by decide)
          (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos p pAmbient).le
      calc
        4 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p pAmbient * request =
            request * (4 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p pAmbient) := by ring1
        _ ≤ request * (8 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p pAmbient) :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            coefficient requestPositive.le
    _ ≤ Dense.Gaussian.Coprime.Bounds.Box.leftThreshold coprime pAmbient := scaled

/-- The right polynomial has the retained positive Bézout residual margin throughout the requested refined box. -/
theorem protectedStateAt_right_lower
    {p q : CoefficientPolynomial} {pAmbient : Box}
    (pDegreePositive : 0 < p.natDegree)
    (coprime : CoprimeCertificate p q)
    (track : WindingOneTrack p pAmbient)
    (current : WindingOneState p pAmbient)
    {request : Fraction.Rational} (requestPositive : 0 < request)
    (requestLe : request ≤ Dense.Gaussian.Coprime.Bounds.Protection.protectionRadius coprime pAmbient)
    {z : Gaussian.Basic.Canonical}
    (inside : (protectedStateAt track current request requestPositive).box.Contains
      z) :
    Dense.Gaussian.Coprime.Bounds.Box.rightMargin coprime pAmbient ≤ Data.Gaussian.Norm.Basic.normSq (q.eval z) :=
  Dense.Gaussian.Coprime.Bounds.Box.rightMargin_le_of_left_small coprime pAmbient
    ((protectedStateAt track current request
      requestPositive).refinesAmbient.contains
      inside)
    (protectedStateAt_left_small pDegreePositive coprime track current
      requestPositive requestLe inside)

/-- Retain boundary clearance for the right polynomial on the exact requested protected box.

The uniform lower bound is the original coprime Bézout margin, with no new box selection. -/
@[expose] def protectedStateAt_rightBoundaryClearance
    {p q : CoefficientPolynomial} {pAmbient : Box}
    (pDegreePositive : 0 < p.natDegree)
    (coprime : CoprimeCertificate p q)
    (track : WindingOneTrack p pAmbient)
    (current : WindingOneState p pAmbient)
    {request : Fraction.Rational} (requestPositive : 0 < request)
    (requestLe : request ≤ Dense.Gaussian.Coprime.Bounds.Protection.protectionRadius coprime pAmbient) :
    Clearance.Box.Boundary.Basic.BoundaryClearance q
      (protectedStateAt track current request requestPositive).box where
  bound := Dense.Gaussian.Coprime.Bounds.Box.rightMargin coprime pAmbient
  positive := Dense.Gaussian.Coprime.Bounds.Box.rightMargin_pos coprime pAmbient
  lower := fun z boundary => by
    have bound : Dense.Gaussian.Coprime.Bounds.Box.rightMargin coprime pAmbient ≤
        Data.Gaussian.Norm.Basic.normSq (q.eval z) :=
      protectedStateAt_right_lower (z := z)
        pDegreePositive coprime track current requestPositive requestLe boundary.1
    simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using bound

/-- The nonzero right polynomial has zero raw winding on the requested protected box.

The proof separates the constant case from positive degree and uses the retained coprime residual budgets. -/
theorem protectedStateAt_rightWinding_zero
    {p q : CoefficientPolynomial} {pAmbient : Box}
    (pDegreePositive : 0 < p.natDegree)
    (qDegreePositive : 0 < q.natDegree)
    (coprime : CoprimeCertificate p q)
    (track : WindingOneTrack p pAmbient)
    (current : WindingOneState p pAmbient)
    {request : Fraction.Rational} (requestPositive : 0 < request)
    (requestLe : request ≤ Dense.Gaussian.Coprime.Bounds.Protection.protectionRadius coprime pAmbient) :
    Winding.Box.Basic.quadrupledBoxWinding q
      (protectedStateAt track current request requestPositive).box = 0 := by
  let state := protectedStateAt track current request requestPositive
  have requestSquare := request_sq_le coprime pAmbient
    requestPositive requestLe
  have radiusBudget : request ≤ Dense.Gaussian.Coprime.Bounds.Box.rightMargin coprime pAmbient /
      (2 * Dense.Gaussian.Bounds.Box.denseLipschitzBound q pAmbient) :=
    requestLe.trans ((Fraction.Order.Basic.min_le_right (1 : Fraction.Rational) _).trans
      (Fraction.Order.Basic.min_le_right _ _))
  have scaled : request * (2 * Dense.Gaussian.Bounds.Box.denseLipschitzBound q pAmbient) ≤
      Dense.Gaussian.Coprime.Bounds.Box.rightMargin coprime pAmbient :=
    (Fraction.Order.Field.le_div_iff_pos
      (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
        (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos q pAmbient))).mp radiusBudget
  have diagonal := track.accurate current request requestPositive
  have variationStrict : Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound q pAmbient state.box <
      Dense.Gaussian.Coprime.Bounds.Box.rightMargin coprime pAmbient := by
    calc
      Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound q pAmbient state.box =
          Dense.Gaussian.Bounds.Box.denseLipschitzBound q pAmbient * state.box.diagonalSq := rfl
      _ ≤ Dense.Gaussian.Bounds.Box.denseLipschitzBound q pAmbient * request ^ 2 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct diagonal
          (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos q pAmbient).le
      _ ≤ Dense.Gaussian.Bounds.Box.denseLipschitzBound q pAmbient * request :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct requestSquare
          (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos q pAmbient).le
      _ < request * (2 * Dense.Gaussian.Bounds.Box.denseLipschitzBound q pAmbient) := by
        have productPositive : 0 < Dense.Gaussian.Bounds.Box.denseLipschitzBound q pAmbient * request :=
          Fraction.Order.Arithmetic.mul_pos_direct
            (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos q pAmbient) requestPositive
        calc
          Dense.Gaussian.Bounds.Box.denseLipschitzBound q pAmbient * request =
              0 + Dense.Gaussian.Bounds.Box.denseLipschitzBound q pAmbient * request := by ring1
          _ < Dense.Gaussian.Bounds.Box.denseLipschitzBound q pAmbient * request +
              Dense.Gaussian.Bounds.Box.denseLipschitzBound q pAmbient * request :=
            Fraction.Order.Arithmetic.add_lt_add_right_direct productPositive _
          _ = request * (2 * Dense.Gaussian.Bounds.Box.denseLipschitzBound q pAmbient) := by ring1
      _ ≤ Dense.Gaussian.Coprime.Bounds.Box.rightMargin coprime pAmbient := scaled
  have anchorLower : Dense.Gaussian.Coprime.Bounds.Box.rightMargin coprime pAmbient ≤
      Data.Gaussian.Norm.Basic.normSq (q.eval state.box.anchor) :=
    protectedStateAt_right_lower pDegreePositive coprime track current
      requestPositive requestLe state.box.contains_anchor
  exact Winding.Box.Residual.quadrupledBoxWinding_eq_zero_of_anchorResidualBound_lt
    q qDegreePositive state.refinesAmbient state.proper
      (variationStrict.trans_le anchorLower)

/-- The same zero-winding conclusion for every displayed nonzero right
polynomial, with the constant case discharged by its exact normalized
constant winding. -/
theorem protectedStateAt_rightWinding_zero_of_nonzero
    {p q : CoefficientPolynomial} {pAmbient : Box}
    (pDegreePositive : 0 < p.natDegree)
    (qNonzero : q.isZero = false)
    (coprime : CoprimeCertificate p q)
    (track : WindingOneTrack p pAmbient)
    (current : WindingOneState p pAmbient)
    {request : Fraction.Rational} (requestPositive : 0 < request)
    (requestLe : request ≤ Dense.Gaussian.Coprime.Bounds.Protection.protectionRadius coprime pAmbient) :
    Winding.Box.Basic.quadrupledBoxWinding q
      (protectedStateAt track current request requestPositive).box = 0 := by
  by_cases degreeZero : q.natDegree = 0
  · have normalizedConstant : q.normalize =
        Dense.Gaussian.Constants.gaussianConstant q.leadingCoeff :=
      Dense.Basic.DensePolynomial.normalize_eq_constant_leadingCoeff_of_degree_zero
        qNonzero degreeZero
    calc
      Winding.Box.Basic.quadrupledBoxWinding q
          (protectedStateAt track current request requestPositive).box =
          Winding.Box.Basic.quadrupledBoxWinding q.normalize
            (protectedStateAt track current request requestPositive).box :=
        (Winding.Box.Basic.quadrupledBoxWinding_normalize q _).symm
      _ = Winding.Box.Basic.quadrupledBoxWinding
            (Dense.Gaussian.Constants.gaussianConstant q.leadingCoeff)
            (protectedStateAt track current request requestPositive).box := by
        rw [normalizedConstant]
      _ = 0 :=
        Winding.Box.Constant.quadrupledBoxWinding_gaussianConstant
          (Dense.Basic.DensePolynomial.leadingCoeff_ne_zero
            qNonzero) _
  · exact protectedStateAt_rightWinding_zero pDegreePositive
      (Nat.pos_of_ne_zero degreeZero) coprime track current requestPositive
      requestLe

end Purelib.RootIsolation.Isolation.Coprime.Protection.Request

end
