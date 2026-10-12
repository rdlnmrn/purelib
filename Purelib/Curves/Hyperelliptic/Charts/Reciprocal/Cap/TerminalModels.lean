module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalCollarTransport
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Riemann.Branches.PreparedPrimitiveSheets
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.InverseModelDifferentialResidual
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.TracedPrimitiveNeighborhood
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PolynomialPullback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Endpoints
import Init.Prelude
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Paths.ClearBoxPaths
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Readings.PreparedObservationNeighborhoods
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Rational

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PolynomialPullback

open Purelib.Riemann.Normalization.ContinuedInverseRoot

open Purelib.Riemann.Topology

@[expose] public section

/-!
# Cap comparison models from retained root neighborhoods

Prepare the local reciprocal model from the supplied retained owner and cache
its differential residual bounds alongside those of the global cap model.
Every later polynomial comparison reuses these initial data and the supplied
cap sample. The retained neighborhood certifies its center and root occurrence.
The collar constructor preserves its actual crossing, and uniform path covers
can supply their already prepared neighborhoods through the same interface.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalModels

open Purelib.Riemann.Normalization
open Purelib.Riemann.Branches
open Purelib.Riemann.Paths
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseModelDifferentialResidual (differentialResidual)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PolynomialPullback (Preparation Sample)
open Purelib.Data.Gaussian.Basic.Canonical

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {collar :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {point : Purelib.Riemann.Normalization.InverseRootPolynomial.Gaussian}

set_option genInjectivity false in
/-- A cap comparison patch retains its source occurrence, including patches prepared by the complete uniform mesh rather
than a single collar fiber. -/
structure Terminal (cap : ReciprocalInnerInverse.Data curve collar)
    (owner : SquareRootContinuationChain.Owner ((HyperellipticReciprocal.polynomial curve).eval point)) (count : Nat)
      where
  /-- The retained primitive neighborhood centered at the original point and operationally attached to its actual owner.
  -/
  neighborhood : TracedPrimitiveNeighborhood.NeighborhoodData
    (HyperellipticReciprocal.polynomial curve) point count (OwnerTraceReadings.ownerName owner)
    (fun patch => OwnerTraceReadings.ownerName patch.base.seed.owner)
  /-- The cached reciprocal and global-cap differential preparations for this exact retained neighborhood. -/
    preparation : PolynomialPullback.Preparation cap neighborhood.patch.base.model

constructive_injectivity Terminal

namespace Terminal

/-- Retain the supplied owner-backed neighborhood and cache the cap polynomial pullback preparation on its original base
model. -/
def ofNeighborhood (cap : ReciprocalInnerInverse.Data curve collar)
    {owner : SquareRootContinuationChain.Owner ((HyperellipticReciprocal.polynomial curve).eval point)} {count : Nat}
    (neighborhood : TracedPrimitiveNeighborhood.NeighborhoodData
      (HyperellipticReciprocal.polynomial curve) point count (OwnerTraceReadings.ownerName owner)
      (fun patch => OwnerTraceReadings.ownerName patch.base.seed.owner)) :
        Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalModels.Terminal cap owner count :=
  ⟨neighborhood, Preparation.build cap neighborhood.patch.base.model⟩

/-- Preserve the actual collar crossing's terminal occurrence. -/
def atBoundary {cap : ReciprocalInnerInverse.Data curve collar} {source : InverseRootPolynomial.Gaussian}
    {fiber : ReciprocalCollarTransport.Fiber collar source} {original : SquareRootContinuationChain.Owner
      (curve.polynomial.eval source)}
    (overlap : RootCoordinates.BoundaryOverlap cap fiber original) (count : Nat) :
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalModels.Terminal cap overlap.collarTrace.finishOwner count :=
  Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalModels.Terminal.ofNeighborhood cap (fiber.terminalNeighborhood
    overlap.collarTrace count)

variable {cap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {owner : Purelib.Riemann.Topology.SquareRootContinuationChain.Owner
    ((Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.polynomial curve).eval point)} {count :
    Nat}
  {differential : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus} {index : Nat} {box :
    Purelib.Geometry.Rational.Box}

/-- The retained original terminal point belongs to its primitive neighborhood. -/
theorem center_inside (terminal : Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalModels.Terminal cap owner count) :
  terminal.neighborhood.patch.box.Contains point := by
  have inside := terminal.neighborhood.patch.center_inside
  rw [terminal.neighborhood.center_eq] at inside
  exact inside

section
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalModels.Terminal
/-- A point certificate at the retained neighborhood center represents the original seed owner channel. -/
private def seedPointEquivalent {polynomial : InverseRootPolynomial.Polynomial} {count : Nat}
    (patch : ContinuedInverseRoot.ContinuedNeighborhood polynomial count) {point : InverseRootPolynomial.Gaussian}
    (equal : patch.base.site.center = point) (sample : ContinuedNeighborhood.Point patch point) :
    Gaussian.Equivalence.NamedEquivalent (OwnerTraceReadings.ownerName patch.base.seed.owner)
      sample.certificate.value.name := by
  cases equal
  exact PreparedPrimitiveSheets.rootEquivalent_of_initial_refines sample.owner.parameterNonzero
    patch.base.seed.owner.track sample.owner.track sample.refines

/-- A point certificate at the retained neighborhood center represents the original seed owner channel. -/
def seedPointEquivalentForTerminal {polynomial : InverseRootPolynomial.Polynomial} {count : Nat}
    (patch : ContinuedInverseRoot.ContinuedNeighborhood polynomial count) {point : InverseRootPolynomial.Gaussian}
    (equal : patch.base.site.center = point) (sample : ContinuedNeighborhood.Point patch point) :
    Gaussian.Equivalence.NamedEquivalent (OwnerTraceReadings.ownerName patch.base.seed.owner)
      sample.certificate.value.name := by
  cases equal
  exact PreparedPrimitiveSheets.rootEquivalent_of_initial_refines sample.owner.parameterNonzero
    patch.base.seed.owner.track sample.owner.track sample.refines

/-- The original terminal owner and its retained center-point certificate are operationally equivalent. -/
def pointEquivalent (terminal : Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalModels.Terminal cap owner count)
    (sample : ContinuedNeighborhood.Point terminal.neighborhood.patch point) :
    Gaussian.Equivalence.NamedEquivalent (OwnerTraceReadings.ownerName owner) sample.certificate.value.name :=
  terminal.neighborhood.seedEquivalent.trans
    (Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalModels.Terminal.seedPointEquivalentForTerminal
      terminal.neighborhood.patch terminal.neighborhood.center_eq sample)

end

/-- Construct a cap pullback sample from the retained terminal preparation and original cap sample. -/
def sample (terminal : Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalModels.Terminal cap owner count)
    (capSample : Primitives.Sample cap differential index box) : PolynomialPullback.Sample terminal.preparation
      capSample :=
  Sample.build terminal.preparation capSample

/-- The retained reciprocal differential residual at the original terminal point satisfies its geometric stage bound. -/
theorem reciprocal_bound (terminal : Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalModels.Terminal cap owner count)
    (capSample : Primitives.Sample cap differential index box) :
    Data.Gaussian.Norm.Basic.normSq (InverseModelDifferentialResidual.differentialResidual
      (HyperellipticReciprocal.polynomial curve)
      (terminal.sample capSample).reciprocal.value point) ≤
        Geometric.Basic.quarterRadius terminal.preparation.reciprocal.bound index :=
  (terminal.sample capSample).reciprocal_differential_bound
    (terminal.neighborhood.patch.box_refines.contains terminal.center_inside)

/-- The retained cap-factor differential residual at an original contained point satisfies its geometric stage bound. -/
theorem regular_bound (terminal : Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalModels.Terminal cap owner count)
    (capSample : Primitives.Sample cap differential index box) (inside : collar.box.Contains point) :
    Data.Gaussian.Norm.Basic.normSq (InverseModelDifferentialResidual.differentialResidual cap.polynomial
      capSample.inverse.value point) ≤
      Geometric.Basic.quarterRadius terminal.preparation.regular.bound index :=
  (terminal.sample capSample).regular_differential_bound inside

end Terminal
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalModels
