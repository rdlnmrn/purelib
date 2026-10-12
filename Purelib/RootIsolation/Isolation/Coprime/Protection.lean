module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Residual
import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
import Purelib.Polynomial.Dense.Gaussian.Coprime.Bounds.Box
public import Purelib.Polynomial.Dense.Gaussian.Coprime.Bounds.Protection
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Winding.Box.Residual
import Purelib.RootIsolation.State.WindingOne.Basic
public import Purelib.RootIsolation.Track.Basic
import Purelib.RootIsolation.Winding.Bounds.Residual
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Coprime.Basic (CoprimeCertificate)
open Purelib.RootIsolation.State.WindingOne.Basic (WindingOneState)
open Purelib.RootIsolation.Track.Basic (WindingOneTrack)

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
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

namespace Purelib.RootIsolation.Isolation.Coprime.Protection

/-- Refining one track at the explicit protection radius. -/
@[expose] def protectedState
    {p q : CoefficientPolynomial} {pAmbient : Box}
    (coprime : CoprimeCertificate p q)
    (track : WindingOneTrack p pAmbient)
    (current : WindingOneState p pAmbient) :
      WindingOneState p pAmbient :=
  track.refine current (Dense.Gaussian.Coprime.Bounds.Protection.protectionRadius coprime pAmbient)
    (Dense.Gaussian.Coprime.Bounds.Protection.protectionRadius_pos coprime pAmbient)

/-- The protected refinement bounds the left polynomial's squared residual by the original coprime threshold. -/
theorem protectedState_left_small
    {p q : CoefficientPolynomial} {pAmbient : Box}
    (pDegreePositive : 0 < p.natDegree)
    (coprime : CoprimeCertificate p q)
    (track : WindingOneTrack p pAmbient)
    (current : WindingOneState p pAmbient) {z : Gaussian.Basic.Canonical}
    (inside : (protectedState coprime track current).box.Contains z) :
    Data.Gaussian.Norm.Basic.normSq (p.eval z) ≤ Dense.Gaussian.Coprime.Bounds.Box.leftThreshold coprime pAmbient :=
      by
  let radius := Dense.Gaussian.Coprime.Bounds.Protection.protectionRadius coprime pAmbient
  let state := protectedState coprime track current
  have residual := Winding.Bounds.Residual.normSq_eval_le_four_lipschitz_diagonal
    pDegreePositive state inside
  have diagonal := track.accurate current radius
    (Dense.Gaussian.Coprime.Bounds.Protection.protectionRadius_pos coprime pAmbient)
  have radiusSquare := Purelib.Polynomial.Dense.Gaussian.Coprime.Bounds.Protection.protectionRadius_sq_le coprime
    pAmbient
  have radiusBudget : radius ≤ Dense.Gaussian.Coprime.Bounds.Box.leftThreshold coprime pAmbient /
      (8 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p pAmbient) :=
    (Purelib.Data.Rat.Fraction.Order.Basic.min_le_right (1 : Fraction.Rational) _).trans
      (Purelib.Data.Rat.Fraction.Order.Basic.min_le_left _ _)
  have scaled : radius * (8 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p pAmbient) ≤
      Dense.Gaussian.Coprime.Bounds.Box.leftThreshold coprime pAmbient :=
    (Fraction.Order.Field.le_div_iff_pos
      (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
        (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos p pAmbient))).mp radiusBudget
  calc
    Data.Gaussian.Norm.Basic.normSq (p.eval z) ≤
        4 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p pAmbient * state.box.diagonalSq := by simpa only [-eq_self,
          -iff_self, Gaussian.Norm.Basic.normSq_eq_canonical] using residual
    _ ≤ 4 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p pAmbient * radius ^ 2 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct diagonal
        (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
          (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos p pAmbient)).le
    _ ≤ 4 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p pAmbient * radius :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct radiusSquare
        (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
          (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos p pAmbient)).le
    _ ≤ radius * (8 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p pAmbient) := by
      have radiusNonnegative :=
        (Dense.Gaussian.Coprime.Bounds.Protection.protectionRadius_pos coprime pAmbient).le
      have coefficient :
          4 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p pAmbient ≤
            8 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p pAmbient :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (show (4 : Fraction.Rational) ≤ 8 by decide)
          (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos p pAmbient).le
      calc
        4 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p pAmbient * radius =
            radius * (4 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p pAmbient) := by ring1
        _ ≤ radius * (8 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p pAmbient) :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            coefficient radiusNonnegative
    _ ≤ Dense.Gaussian.Coprime.Bounds.Box.leftThreshold coprime pAmbient := by
      simpa only [-eq_self, -iff_self, radius] using scaled

/-- The other coprime polynomial has a uniform positive lower bound on the
whole protected box. -/
theorem protectedState_right_lower
    {p q : CoefficientPolynomial} {pAmbient : Box}
    (pDegreePositive : 0 < p.natDegree)
    (coprime : CoprimeCertificate p q)
    (track : WindingOneTrack p pAmbient)
    (current : WindingOneState p pAmbient) {z : Gaussian.Basic.Canonical}
    (inside : (protectedState coprime track current).box.Contains z) :
    Dense.Gaussian.Coprime.Bounds.Box.rightMargin coprime pAmbient ≤ Data.Gaussian.Norm.Basic.normSq (q.eval z) :=
  Dense.Gaussian.Coprime.Bounds.Box.rightMargin_le_of_left_small coprime pAmbient
    ((protectedState coprime track current).refinesAmbient.contains inside)
    (protectedState_left_small pDegreePositive coprime track current inside)

/-- The forced right margin is in particular a constructive boundary
clearance certificate. -/
@[expose] def protectedState_rightBoundaryClearance
    {p q : CoefficientPolynomial} {pAmbient : Box}
    (pDegreePositive : 0 < p.natDegree)
    (coprime : CoprimeCertificate p q)
    (track : WindingOneTrack p pAmbient)
    (current : WindingOneState p pAmbient) :
    Clearance.Box.Boundary.Basic.BoundaryClearance q (protectedState coprime track
      current).box where
  bound := Dense.Gaussian.Coprime.Bounds.Box.rightMargin coprime pAmbient
  positive := Dense.Gaussian.Coprime.Bounds.Box.rightMargin_pos coprime pAmbient
  lower := fun z boundary => by
    have bound : Dense.Gaussian.Coprime.Bounds.Box.rightMargin coprime pAmbient ≤
        Data.Gaussian.Norm.Basic.normSq (q.eval z) :=
      protectedState_right_lower (z := z) pDegreePositive coprime track current boundary.1
    simpa only [-eq_self, -iff_self, Gaussian.Norm.Basic.normSq_eq_canonical] using bound

/-- On the protected left track, the other positive-degree polynomial has
zero raw winding. -/
theorem protectedState_rightWinding_zero
    {p q : CoefficientPolynomial} {pAmbient : Box}
    (pDegreePositive : 0 < p.natDegree)
    (qDegreePositive : 0 < q.natDegree)
    (coprime : CoprimeCertificate p q)
    (track : WindingOneTrack p pAmbient)
    (current : WindingOneState p pAmbient) :
    Winding.Box.Basic.quadrupledBoxWinding q (protectedState coprime track current).box = 0
      := by
  let radius := Dense.Gaussian.Coprime.Bounds.Protection.protectionRadius coprime pAmbient
  let state := protectedState coprime track current
  have radiusSquare := Purelib.Polynomial.Dense.Gaussian.Coprime.Bounds.Protection.protectionRadius_sq_le coprime
    pAmbient
  have radiusBudget : radius ≤ Dense.Gaussian.Coprime.Bounds.Box.rightMargin coprime pAmbient /
      (2 * Dense.Gaussian.Bounds.Box.denseLipschitzBound q pAmbient) :=
    (Purelib.Data.Rat.Fraction.Order.Basic.min_le_right (1 : Fraction.Rational) _).trans
      (Purelib.Data.Rat.Fraction.Order.Basic.min_le_right _ _)
  have scaled : radius * (2 * Dense.Gaussian.Bounds.Box.denseLipschitzBound q pAmbient) ≤
      Dense.Gaussian.Coprime.Bounds.Box.rightMargin coprime pAmbient :=
    (Fraction.Order.Field.le_div_iff_pos
      (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
        (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos q pAmbient))).mp radiusBudget
  have diagonal := track.accurate current radius
    (Dense.Gaussian.Coprime.Bounds.Protection.protectionRadius_pos coprime pAmbient)
  have variationStrict : Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound q pAmbient state.box <
      Dense.Gaussian.Coprime.Bounds.Box.rightMargin coprime pAmbient := by
    have radiusPositive := Dense.Gaussian.Coprime.Bounds.Protection.protectionRadius_pos coprime pAmbient
    calc
      Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound q pAmbient state.box =
          Dense.Gaussian.Bounds.Box.denseLipschitzBound q pAmbient * state.box.diagonalSq := rfl
      _ ≤ Dense.Gaussian.Bounds.Box.denseLipschitzBound q pAmbient * radius ^ 2 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct diagonal
          (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos q pAmbient).le
      _ ≤ Dense.Gaussian.Bounds.Box.denseLipschitzBound q pAmbient * radius :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct radiusSquare
          (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos q pAmbient).le
      _ < radius * (2 * Dense.Gaussian.Bounds.Box.denseLipschitzBound q pAmbient) := by
        have productPositive : 0 <
            Dense.Gaussian.Bounds.Box.denseLipschitzBound q pAmbient * radius :=
          Fraction.Order.Arithmetic.mul_pos_direct
            (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos q pAmbient) radiusPositive
        calc
          Dense.Gaussian.Bounds.Box.denseLipschitzBound q pAmbient * radius =
              0 + Dense.Gaussian.Bounds.Box.denseLipschitzBound q pAmbient * radius := by ring1
          _ < Dense.Gaussian.Bounds.Box.denseLipschitzBound q pAmbient * radius +
              Dense.Gaussian.Bounds.Box.denseLipschitzBound q pAmbient * radius :=
            Fraction.Order.Arithmetic.add_lt_add_right_direct productPositive _
          _ = radius * (2 * Dense.Gaussian.Bounds.Box.denseLipschitzBound q pAmbient) := by ring1
      _ ≤ Dense.Gaussian.Coprime.Bounds.Box.rightMargin coprime pAmbient := scaled
  have anchorLower : Dense.Gaussian.Coprime.Bounds.Box.rightMargin coprime pAmbient ≤
      Data.Gaussian.Norm.Basic.normSq (q.eval state.box.anchor) :=
    protectedState_right_lower pDegreePositive coprime track current
      state.box.contains_anchor
  exact Winding.Box.Residual.quadrupledBoxWinding_eq_zero_of_anchorResidualBound_lt
    q qDegreePositive state.refinesAmbient state.proper
      (variationStrict.trans_le anchorLower)
end Purelib.RootIsolation.Isolation.Coprime.Protection

end
