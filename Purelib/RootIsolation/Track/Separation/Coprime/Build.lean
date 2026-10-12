module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
import Purelib.Polynomial.Dense.Gaussian.Coprime.Bounds.Box
import Purelib.RootIsolation.Isolation.Coprime.Protection
public import Purelib.RootIsolation.Isolation.Coprime.Separation
import Purelib.RootIsolation.Isolation.Coprime.UniformResidual
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic
public import Purelib.RootIsolation.Track.Separation.Coprime.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Data

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
public section

/-!
# Constructive signed multiplicity sites

A squarefree factor track represents one geometric zero location.  This
module attaches the factor's complete finite multiplicity while protecting
the same box from both the remaining same-side factors and the opposite
rational-function cofactor.  One minimum of two positive rational requests
provides both protections simultaneously.
-/

namespace Purelib.RootIsolation.Track.Separation.Coprime.Build

/-- Refine a retained winding track to exclude a displayed exact root of a coprime polynomial.

The positive-degree track polynomial and original Bézout certificate give a positive lower bound for the other
polynomial throughout the protected box. -/
@[expose] def separateExactFromTrack
    {trackPolynomial exactPolynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box}
    (trackDegreePositive : 0 < trackPolynomial.natDegree)
    (coprime : Dense.Gaussian.Coprime.Basic.CoprimeCertificate trackPolynomial
      exactPolynomial)
    (track : Basic.WindingOneTrack trackPolynomial ambient)
    (current : State.WindingOne.Basic.WindingOneState trackPolynomial ambient)
    (point : Gaussian.Basic.Canonical)
    (exactRoot : exactPolynomial.eval point = 0) :
    Track.Separation.Coprime.Basic.ExactTrackSeparation (exactPolynomial := exactPolynomial)
      track current point := by
  let state := Isolation.Coprime.Protection.protectedState
    coprime track current
  refine ⟨state, ?_⟩
  intro inside
  have lower := Isolation.Coprime.Protection.protectedState_right_lower
    trackDegreePositive coprime track current inside
  rw [exactRoot, Gaussian.Norm.Basic.normSq_zero] at lower
  exact (not_lt_of_ge lower
    (Dense.Gaussian.Coprime.Bounds.Box.rightMargin_pos coprime ambient)).elim

/-- Refine two positive-degree coprime winding tracks to disjoint retained boxes.

One original track supplies a protected box and the other a uniformly small residual box, using the same retained Bézout
margin. -/
@[expose] def separateTracks
    {p q : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {pAmbient qAmbient : Box}
    (pDegreePositive : 0 < p.natDegree)
    (qDegreePositive : 0 < q.natDegree)
    (coprime : Dense.Gaussian.Coprime.Basic.CoprimeCertificate p q)
    (pTrack : Basic.WindingOneTrack p pAmbient)
    (pCurrent : State.WindingOne.Basic.WindingOneState p pAmbient)
    (qTrack : Basic.WindingOneTrack q qAmbient)
    (qCurrent : State.WindingOne.Basic.WindingOneState q qAmbient) :
    Track.Separation.Coprime.Basic.TrackPairSeparation pTrack pCurrent qTrack qCurrent :=
  let left := Isolation.Coprime.Protection.protectedState
    coprime pTrack pCurrent
  let right := Isolation.Coprime.UniformResidual.uniformlySmallState
    qTrack qCurrent
    (Dense.Gaussian.Coprime.Bounds.Box.rightMargin coprime pAmbient)
    (Dense.Gaussian.Coprime.Bounds.Box.rightMargin_pos coprime pAmbient)
  ⟨left, right,
    Isolation.Coprime.Separation.protectedState_separated_uniformlySmallState
      pDegreePositive qDegreePositive coprime pTrack pCurrent qTrack qCurrent⟩

end Purelib.RootIsolation.Track.Separation.Coprime.Build

end
