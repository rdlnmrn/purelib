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
public import Purelib.RootIsolation.State.WindingOne.Coprime
import Purelib.RootIsolation.Winding.Bounds.Residual
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

open Purelib.Polynomial.Dense.Gaussian.Coprime

open Purelib.Data.Rat.Fraction.Order

open Purelib.Polynomial.Dense.Gaussian

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
  track.refine current (Bounds.Protection.protectionRadius coprime pAmbient)
    (Bounds.Protection.protectionRadius_pos coprime pAmbient)

/-- The protected refinement bounds the left polynomial's squared residual by the original coprime threshold. -/
theorem protectedState_left_small
    {p q : CoefficientPolynomial} {pAmbient : Box}
    (pDegreePositive : 0 < p.natDegree)
    (coprime : CoprimeCertificate p q)
    (track : WindingOneTrack p pAmbient)
    (current : WindingOneState p pAmbient) {z : Gaussian.Basic.Canonical}
    (inside : (protectedState coprime track current).box.Contains z) :
    Gaussian.Norm.Basic.normSq (p.eval z) ≤ Bounds.Box.leftThreshold coprime pAmbient :=
      by
  exact State.WindingOne.Coprime.left_small pDegreePositive coprime
    (protectedState coprime track current) (track.accurate current _ _) inside

/-- The other coprime polynomial has a uniform positive lower bound on the
whole protected box. -/
theorem protectedState_right_lower
    {p q : CoefficientPolynomial} {pAmbient : Box}
    (pDegreePositive : 0 < p.natDegree)
    (coprime : CoprimeCertificate p q)
    (track : WindingOneTrack p pAmbient)
    (current : WindingOneState p pAmbient) {z : Gaussian.Basic.Canonical}
    (inside : (protectedState coprime track current).box.Contains z) :
    Bounds.Box.rightMargin coprime pAmbient ≤ Gaussian.Norm.Basic.normSq (q.eval z) :=
  Bounds.Box.rightMargin_le_of_left_small coprime pAmbient
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
  bound := Bounds.Box.rightMargin coprime pAmbient
  positive := Bounds.Box.rightMargin_pos coprime pAmbient
  lower := fun z boundary => by
    have bound : Bounds.Box.rightMargin coprime pAmbient ≤
        Gaussian.Norm.Basic.normSq (q.eval z) :=
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
  exact State.WindingOne.Coprime.right_winding_zero pDegreePositive qDegreePositive coprime
    (protectedState coprime track current) (track.accurate current _ _)

end Purelib.RootIsolation.Isolation.Coprime.Protection

end
