module
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
import Purelib.Polynomial.Dense.Gaussian.Coprime.Operations
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side
public import Purelib.RootIsolation.Multiplicity.Observation.Basic
import Purelib.RootIsolation.Track.Separation.Coprime.Basic
public import Purelib.RootIsolation.Track.Separation.Coprime.Build

import Purelib.Tactic.QuotientFreeOmega
public import Purelib.Polynomial.Dense.Gaussian.Coprime.Roots
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive
import Purelib.Polynomial.Dense.Gaussian.Roots.Certificate
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Part
import Purelib.RootIsolation.Exact.Basic
import Purelib.RootIsolation.FTA.Squarefree.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic

open Purelib.Polynomial

open Purelib.RootIsolation

section
public section

/-!
# Total finite rational-function zero and pole sites

This module packages the signed multiplicity theorem over every finite
degree branch.  Linear factors return only exact displayed Gaussian-rational
zeros or poles.  Higher factors retain shrinking box tracks.  Constants have
no finite sites, and the identically-zero numerator has its own constructor.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side
namespace PositiveSideInput

/-- Pairwise finite separation for all four combinations of exact rational
sites and higher shrinking-track sites. -/
@[expose] def ObservationsSeparated
    {leftSource leftOpposite rightSource rightOpposite : Basic.CanonicalCoefficients.CoefficientPolynomial}
    {leftInput : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput leftSource leftOpposite}
    {rightInput : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput rightSource rightOpposite}
    {leftContext : Context.Basic.PositiveContext
      leftInput.entries}
    {rightContext : Context.Basic.PositiveContext
      rightInput.entries}
    (left : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput.FactorObservation leftInput leftContext)
    (right : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput.FactorObservation rightInput rightContext)
      : Type :=
  match left, right with
  | .exact leftRoot _ _, .exact rightRoot _ _ =>
      PLift (leftRoot.point ≠ rightRoot.point)
  | .exact leftRoot _ _, .higher rightBoxes _ =>
      ∀ index : Fin rightContext.focus.part.polynomial.natDegree,
        Track.Separation.Coprime.Basic.ExactTrackSeparation
          (exactPolynomial := leftContext.focus.part.polynomial)
          (rightBoxes.isolation.trackAt index)
          (rightBoxes.isolation.trackAt index).initial leftRoot.point
  | .higher leftBoxes _, .exact rightRoot _ _ =>
      ∀ index : Fin leftContext.focus.part.polynomial.natDegree,
        Track.Separation.Coprime.Basic.ExactTrackSeparation
          (exactPolynomial := rightContext.focus.part.polynomial)
          (leftBoxes.isolation.trackAt index)
          (leftBoxes.isolation.trackAt index).initial rightRoot.point
  | .higher leftBoxes _, .higher rightBoxes _ =>
      ∀ (leftIndex : Fin leftContext.focus.part.polynomial.natDegree)
        (rightIndex : Fin rightContext.focus.part.polynomial.natDegree),
        Track.Separation.Coprime.Basic.TrackPairSeparation
          (leftBoxes.isolation.trackAt leftIndex)
          (leftBoxes.isolation.trackAt leftIndex).initial
          (rightBoxes.isolation.trackAt rightIndex)
          (rightBoxes.isolation.trackAt rightIndex).initial

/-- Construct separation for two retained factor observations from their original coprime certificate.

Exact roots give point inequality; mixed and higher cases refine the actual original tracks to checked exclusion or
separated-box outputs. -/
@[expose] def separateObservations
    {leftSource leftOpposite rightSource rightOpposite : Basic.CanonicalCoefficients.CoefficientPolynomial}
    {leftInput : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput leftSource leftOpposite}
    {rightInput : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput rightSource rightOpposite}
    {leftContext : Context.Basic.PositiveContext
      leftInput.entries}
    {rightContext : Context.Basic.PositiveContext
      rightInput.entries}
    (left : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput.FactorObservation leftInput leftContext)
    (right : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput.FactorObservation rightInput rightContext)
    (coprime : Dense.Gaussian.Coprime.Basic.CoprimeCertificate leftContext.focus.part.polynomial
      rightContext.focus.part.polynomial) :
    Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput.ObservationsSeparated left right := by
  cases left with
  | exact leftRoot leftDegree _ =>
      cases right with
      | exact rightRoot rightDegree _ =>
          exact ⟨Dense.Gaussian.Coprime.Roots.exactPoints_ne coprime
            leftRoot.root rightRoot.root⟩
      | higher rightBoxes rightDegree =>
          intro index
          exact Track.Separation.Coprime.Build.separateExactFromTrack
            rightContext.focus.degreePositive
            (Dense.Gaussian.Coprime.Operations.CoprimeCertificate.symm coprime)
            (rightBoxes.isolation.trackAt index)
            (rightBoxes.isolation.trackAt index).initial leftRoot.point
            leftRoot.root
  | higher leftBoxes leftDegree =>
      cases right with
      | exact rightRoot rightDegree _ =>
          intro index
          exact Track.Separation.Coprime.Build.separateExactFromTrack
            leftContext.focus.degreePositive coprime
            (leftBoxes.isolation.trackAt index)
            (leftBoxes.isolation.trackAt index).initial rightRoot.point
            rightRoot.root
      | higher rightBoxes rightDegree =>
          intro leftIndex rightIndex
          exact Track.Separation.Coprime.Build.separateTracks
            leftContext.focus.degreePositive rightContext.focus.degreePositive
            coprime (leftBoxes.isolation.trackAt leftIndex)
            (leftBoxes.isolation.trackAt leftIndex).initial
            (rightBoxes.isolation.trackAt rightIndex)
            (rightBoxes.isolation.trackAt rightIndex).initial

/-- Separation already internal to one squarefree factor: an exact branch
has one displayed rational site, while a higher branch carries a pairwise
separated degree-indexed family. -/
@[expose] def ObservationInternallySeparated
    {source opposite : Basic.CanonicalCoefficients.CoefficientPolynomial}
    {input : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput source opposite}
    {context : Context.Basic.PositiveContext input.entries}
    (observation : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput.FactorObservation input context) :
      Type :=
  match observation with
  | .exact _ _ _ => PUnit
  | .higher boxes _ =>
      PLift (∀ left right : Fin context.focus.part.polynomial.natDegree,
        left ≠ right →
          (boxes.isolation.trackAt left).initial.box.Separated
            (boxes.isolation.trackAt right).initial.box)

/-- Read the original observation's internal site separation, retaining the exact higher-family box indices. -/
@[expose] def observationInternallySeparated
    {source opposite : Basic.CanonicalCoefficients.CoefficientPolynomial}
    {input : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput source opposite}
    {context : Context.Basic.PositiveContext input.entries}
    (observation : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput.FactorObservation input context) :
    Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput.ObservationInternallySeparated observation := by
  cases observation with
  | exact => exact PUnit.unit
  | higher boxes _ => exact ⟨boxes.isolation.trackAt_pairwiseSeparated⟩
end PositiveSideInput
end Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side

end
