module
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side
import Purelib.RootIsolation.Exact.Ownership.Basic
public import Purelib.RootIsolation.Multiplicity.Observation.Basic
import Purelib.RootIsolation.Track.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive
import Purelib.Polynomial.Dense.Gaussian.Roots.Certificate
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Part
import Purelib.RootIsolation.Exact.Basic
import Purelib.RootIsolation.FTA.Squarefree.Basic
import Purelib.RootIsolation.State.WindingOne.Basic

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Total finite rational-function zero and pole sites

This module packages the signed multiplicity theorem over every finite
degree branch.  Linear factors return only exact displayed Gaussian-rational
zeros or poles.  Higher factors retain shrinking box tracks.  Constants have
no finite sites, and the identically-zero numerator has its own constructor.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side
namespace PositiveSideInput

/-- Atomic completeness for one factor.  The linear branch retains its exact
rational evaluation certificate.  For a higher branch, every alternative
winding-one track supported by the isolation partition is constructively
refined into a deterministically selected output owner. -/
def
  ObservationAtomicMaximality
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {input : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput source opposite}
    {context : Dense.Gaussian.Multiplicity.Basis.Context.Basic.PositiveContext input.entries}
    (observation : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput.FactorObservation input context) :
      Type :=
  match observation with
  | .exact root _ _ =>
      PLift (context.focus.part.polynomial.eval root.point = 0)
  | .higher boxes _ =>
      ∀ (track : Track.Basic.WindingOneTrack
          context.focus.part.polynomial
          (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox
            context.focus.part.polynomial)),
        track.initial.box.Refines boxes.isolation.support →
          Exact.Ownership.Basic.OwnerSelection boxes.isolation track

/-- Read the retained factor observation's exact-root certificate or original deterministic ownership operation. -/
def
  observationAtomicMaximality
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {input : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput source opposite}
    {context : Dense.Gaussian.Multiplicity.Basis.Context.Basic.PositiveContext input.entries}
    (observation : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput.FactorObservation input context) :
    ObservationAtomicMaximality observation := by
  cases observation with
  | exact root => exact ⟨root.root⟩
  | higher boxes => exact boxes.ownership
end PositiveSideInput
end Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side

end
