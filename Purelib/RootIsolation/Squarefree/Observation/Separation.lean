module
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
public import Purelib.Polynomial.Dense.Gaussian.Coprime.Operations
import Purelib.Polynomial.Dense.Gaussian.Coprime.SquarefreeSide
public import Purelib.RootIsolation.Squarefree.Observation.Basic
import Purelib.RootIsolation.Track.Separation.Coprime.Basic
public import Purelib.RootIsolation.Track.Separation.Coprime.Build

import Purelib.Tactic.QuotientFreeOmega
public import Purelib.Polynomial.Dense.Gaussian.Coprime.Roots
import Mathlib.Data.Nat.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Dense.Gaussian.Roots.Certificate
import Purelib.RootIsolation.Exact.Basic
import Purelib.RootIsolation.FTA.Squarefree.Basic
import Purelib.RootIsolation.Track.Basic

open Purelib.Polynomial.Dense.Gaussian.Coprime.SquarefreeSide (SquarefreeSideInput)
open Purelib.RootIsolation.Squarefree.Observation.Basic (SquarefreeObservation)

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Finite constructive rational-function argument principle

This paper-facing addendum combines executable gcd cancellation, the
polynomial box theorem, quantitative coprime separation, and the quotient
winding law.  The first public result below is the higher-degree squarefree
core.  It returns the numerator and denominator track families without
copying the polynomial isolation algorithm.
-/

namespace Purelib.RootIsolation.Squarefree.Observation.Separation

/-- All cross-side combinations are separated using finite Bézout margins;
no selected or completed irrational root is introduced. -/
def SquarefreeObservationsSeparated
    {leftSource leftOpposite rightSource rightOpposite :
      Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {leftInput : SquarefreeSideInput leftSource leftOpposite}
    {rightInput : SquarefreeSideInput rightSource rightOpposite}
    (left : SquarefreeObservation leftInput)
    (right : SquarefreeObservation rightInput) : Type :=
  match left, right with
  | .constant _, _ => PUnit
  | _, .constant _ => PUnit
  | .exact leftRoot _ _, .exact rightRoot _ _ =>
      PLift (leftRoot.point ≠ rightRoot.point)
  | .exact leftRoot _ _, .higher rightBoxes _ =>
      ∀ index : Fin rightSource.natDegree,
        Track.Separation.Coprime.Basic.ExactTrackSeparation
          (exactPolynomial := leftSource)
          (rightBoxes.isolation.trackAt index)
          (rightBoxes.isolation.trackAt index).initial leftRoot.point
  | .higher leftBoxes _, .exact rightRoot _ _ =>
      ∀ index : Fin leftSource.natDegree,
        Track.Separation.Coprime.Basic.ExactTrackSeparation
          (exactPolynomial := rightSource)
          (leftBoxes.isolation.trackAt index)
          (leftBoxes.isolation.trackAt index).initial rightRoot.point
  | .higher leftBoxes _, .higher rightBoxes _ =>
      ∀ (leftIndex : Fin leftSource.natDegree)
        (rightIndex : Fin rightSource.natDegree),
        Track.Separation.Coprime.Basic.TrackPairSeparation
          (leftBoxes.isolation.trackAt leftIndex)
          (leftBoxes.isolation.trackAt leftIndex).initial
          (rightBoxes.isolation.trackAt rightIndex)
          (rightBoxes.isolation.trackAt rightIndex).initial

/-- Separate the retained sites of two original coprime squarefree observations.

Constant sides contribute no sites; exact pairs give unequal points, while mixed and higher pairs retain checked
original-track exclusions or separated refinements. -/
def separateSquarefreeObservations
    {leftSource leftOpposite rightSource rightOpposite :
      Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {leftInput : SquarefreeSideInput leftSource leftOpposite}
    {rightInput : SquarefreeSideInput rightSource rightOpposite}
    (left : SquarefreeObservation leftInput)
    (right : SquarefreeObservation rightInput)
    (coprime : Dense.Gaussian.Coprime.Basic.CoprimeCertificate
      leftSource rightSource) :
    SquarefreeObservationsSeparated left right := by
  cases left with
  | constant => exact PUnit.unit
  | exact leftRoot =>
      cases right with
      | constant => exact PUnit.unit
      | exact rightRoot =>
          exact ⟨Dense.Gaussian.Coprime.Roots.exactPoints_ne coprime
            leftRoot.root rightRoot.root⟩
      | higher rightBoxes rightDegree =>
          intro index
          exact Track.Separation.Coprime.Build.separateExactFromTrack
            ((show (0 : Nat) < 2 by decide).trans_le rightDegree)
            (Dense.Gaussian.Coprime.Operations.CoprimeCertificate.symm coprime)
            (rightBoxes.isolation.trackAt index)
            (rightBoxes.isolation.trackAt index).initial leftRoot.point
            leftRoot.root
  | higher leftBoxes leftDegree =>
      cases right with
      | constant => exact PUnit.unit
      | exact rightRoot =>
          intro index
          exact Track.Separation.Coprime.Build.separateExactFromTrack
            ((show (0 : Nat) < 2 by decide).trans_le leftDegree) coprime
            (leftBoxes.isolation.trackAt index)
            (leftBoxes.isolation.trackAt index).initial rightRoot.point
            rightRoot.root
      | higher rightBoxes rightDegree =>
          intro leftIndex rightIndex
          exact Track.Separation.Coprime.Build.separateTracks
            ((show (0 : Nat) < 2 by decide).trans_le leftDegree)
            ((show (0 : Nat) < 2 by decide).trans_le rightDegree) coprime
            (leftBoxes.isolation.trackAt leftIndex)
            (leftBoxes.isolation.trackAt leftIndex).initial
            (rightBoxes.isolation.trackAt rightIndex)
            (rightBoxes.isolation.trackAt rightIndex).initial
end Purelib.RootIsolation.Squarefree.Observation.Separation

end
