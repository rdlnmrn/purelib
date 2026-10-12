module
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
import Purelib.Polynomial.Dense.Gaussian.Coprime.Bounds.Box
public import Purelib.RootIsolation.Isolation.Coprime.Protection
public import Purelib.RootIsolation.Isolation.Coprime.UniformResidual
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic

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

namespace Purelib.RootIsolation.Isolation.Coprime.Separation

/-- A left track protected by a Bézout margin is positively separated from a
right track refined below that same margin. -/
theorem protectedState_separated_uniformlySmallState
    {p q : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {pAmbient qAmbient : Box}
    (pDegreePositive : 0 < p.natDegree)
    (qDegreePositive : 0 < q.natDegree)
    (coprime : Dense.Gaussian.Coprime.Basic.CoprimeCertificate p q)
    (pTrack : Track.Basic.WindingOneTrack p pAmbient)
    (pCurrent : State.WindingOne.Basic.WindingOneState p pAmbient)
    (qTrack : Track.Basic.WindingOneTrack q qAmbient)
    (qCurrent : State.WindingOne.Basic.WindingOneState q qAmbient) :
    (Isolation.Coprime.Protection.protectedState coprime pTrack pCurrent).box.Separated
      (Isolation.Coprime.UniformResidual.uniformlySmallState qTrack qCurrent
        (Dense.Gaussian.Coprime.Bounds.Box.rightMargin coprime pAmbient)
        (Dense.Gaussian.Coprime.Bounds.Box.rightMargin_pos coprime pAmbient)).box := open Purelib.Data in by
  let pState := Isolation.Coprime.Protection.protectedState coprime pTrack pCurrent
  let margin := Dense.Gaussian.Coprime.Bounds.Box.rightMargin coprime pAmbient
  let marginPositive := Dense.Gaussian.Coprime.Bounds.Box.rightMargin_pos coprime pAmbient
  let qState := Isolation.Coprime.UniformResidual.uniformlySmallState qTrack qCurrent margin marginPositive
  by_cases separated : pState.box.Separated qState.box
  · exact separated
  · have overlap :=
      Box.contains_overlapPoint_of_not_separated
        separated
    let point := Box.overlapPoint pState.box qState.box
    have lower : margin ≤ Gaussian.Norm.Basic.normSq (q.eval point) := by
      exact Isolation.Coprime.Protection.protectedState_right_lower (z := point) pDegreePositive coprime
        pTrack pCurrent overlap.1
    have upper : Gaussian.Norm.Basic.normSq (q.eval point) < margin := by
      exact Isolation.Coprime.UniformResidual.uniformlySmallState_residual_lt qDegreePositive qTrack qCurrent
        marginPositive overlap.2
    exact (not_lt_of_ge lower upper).elim
end Purelib.RootIsolation.Isolation.Coprime.Separation

end
