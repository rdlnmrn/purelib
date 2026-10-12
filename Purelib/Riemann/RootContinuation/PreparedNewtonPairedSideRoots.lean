module
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Paths.UniformPreparedBoundarySegments
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.RootIsolation.State.Raw

public import Purelib.Riemann.RootContinuation.PreparedNewtonPairedRootBank
public import Purelib.Riemann.RootContinuation.PreparedNewtonPairedSide
import Purelib.Riemann.Integration.UniformPrimitiveNeighborhoods
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.RootIsolation.Newton.Band.Basic
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Gaussian.Field
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore

@[expose] public section

/-! Whole paired-side root chains use the actual retained subdivision owners. -/
namespace Purelib.Riemann.RootContinuation.PreparedNewtonPairedSideRoots
open Purelib.RootIsolation.Newton.Band
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)
open Purelib.Riemann.Topology.PreparedBankRootChains (ownerName)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.RootContinuation.PreparedNewtonPairedSide (PairedBoundarySide)
open Purelib.Riemann.RootContinuation.NewtonBandBounds (Profile)
open Purelib.Riemann.RootContinuation.NewtonBandDifferentials (DifferentialProfile)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples (PreparedBandRequest)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential other :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {ambient : Purelib.Geometry.Rational.Box} {current : Purelib.RootIsolation.State.Raw.RawWindingState
    curve.polynomial ambient}
  {profile : Profile curve.squarefree current.box} {fixed : DifferentialProfile profile differential.exponent}
  {target : Purelib.Data.Rat.Fraction.Rational} {request : PreparedBandRequest fixed target}

open Purelib.Data.Gaussian in
/-- Heterogeneously equal owners at equal parameters have equal root names. -/
public theorem ownerName_heq {firstParameter secondParameter : Basic.Canonical}
    (equal : firstParameter = secondParameter) {first : Owner firstParameter} {second : Owner secondParameter}
    (same : HEq first second) : ownerName first = ownerName second := by
  cases equal
  cases same
  rfl

namespace PairedBoundarySide
variable {start finish : Purelib.Data.Gaussian.Basic.Canonical}
  {segment : Purelib.Polynomial.Geometry.ClearPath.ClearSegment curve.polynomial request.sample.output.box start finish}
  {within : segment.WithinAmbient} {owner : Owner (curve.polynomial.eval start)} {sheet : Fin 2}

open Purelib.Riemann.Paths in
open Purelib.Riemann.Topology in
open Purelib.RootIsolation in
/-- Root chain of the actual covered parents of a paired side.

Transports the original subdivision chain through exact parent and endpoint-owner identities, retaining the side's start
and actual finish owner names. -/
def parentRootChain (side : PairedBoundarySide request other segment within owner sheet) :
    RootChain side.covered.parents (ownerName owner) (ownerName side.finishOwner) := by
  have initial : ownerName (PreparedClearPathModels.ownerAtStart segment owner) = ownerName owner := by
    apply ownerName_heq (congrArg curve.polynomial.eval segment.pointAt_zero)
    unfold PreparedClearPathModels.ownerAtStart
    exact SquareRoot.Owner.Transport.castOwnerParameter_heq _ _
  have terminal : ownerName side.covered.subdivision.terminalOwner = ownerName side.finishOwner := by
    apply ownerName_heq (congrArg curve.polynomial.eval (show
      segment.pointAt side.covered.subdivision.endpoint.parameter = finish from by
        rw [side.covered.endpoint_eq]; exact segment.pointAt_one))
    exact UniformPreparedBoundarySegments.CoveredSegment.finishOwner_heq_terminalOwner side.covered |>.symm
  exact PreparedBankRootChains.RootChain.castNames initial terminal
    (PreparedBankRootChains.RootChain.castChildren side.covered.parents_eq.symm
      (PreparedBankRootChains.subdivisionRootChain curve differential segment within sheet
        side.covered.subdivision side.covered.centers))

open Purelib.Riemann.RootContinuation
/-- Root chain of the first differential's retained refined children.

Refines the actual covered-parent chain through the original paired bank without changing its endpoint names. -/
def firstRootChain (side : PairedBoundarySide request other segment within owner sheet) :
    RootChain (PreparedNewtonPairedRootBank.PairedBoundaryParents.firstChildren side.refined)
      (ownerName owner) (ownerName side.finishOwner) :=
  PreparedNewtonPairedRootBank.PairedBoundaryParents.firstRootChain side.refined
    (PreparedNewtonPairedSideRoots.PairedBoundarySide.parentRootChain side)

/-- Root chain of the second differential's retained refined children.

Uses the original paired-bank refinement and covered-parent chain, preserving the same actual start and finish owner
names. -/
def secondRootChain (side : PairedBoundarySide request other segment within owner sheet) :
    RootChain (PreparedNewtonPairedRootBank.PairedBoundaryParents.secondChildren side.refined)
      (ownerName owner) (ownerName side.finishOwner) :=
  PreparedNewtonPairedRootBank.PairedBoundaryParents.secondRootChain side.refined
    (PreparedNewtonPairedSideRoots.PairedBoundarySide.parentRootChain side)

end PairedBoundarySide
end Purelib.Riemann.RootContinuation.PreparedNewtonPairedSideRoots
