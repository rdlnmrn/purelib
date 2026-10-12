module
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Riemann.RootContinuation.PreparedNewtonBandBoundary
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedBoundary
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedDoubleBoundary
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Winding.Polygon.Basic
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.PreparedPathClosure
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.RootIsolation.State.Raw

public import Purelib.Riemann.RootContinuation.PreparedNewtonPairedBoundaryRoots
public import Purelib.Riemann.RootContinuation.PreparedNewtonPairedSideTrace
public import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.RootIsolation.Newton.Band.Basic
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedSide
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Band.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Clearance.Box.Line.Restriction
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Tactic.Ring

@[expose] public section

/-! Winding and operational return of the actual paired two-lap owners. -/
namespace Purelib.Riemann.RootContinuation
open Purelib.RootIsolation.Newton.Band
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.RootContinuation.NewtonBandBounds (Profile)
open Purelib.Riemann.RootContinuation.NewtonBandDifferentials (DifferentialProfile)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples (PreparedBandRequest)
open Purelib.Riemann.RootContinuation.PreparedNewtonPairedBoundary (PairedBoundaryTraversal)
open Purelib.Riemann.RootContinuation.PreparedNewtonPairedDoubleBoundary (PairedDoubleBoundary)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandBoundary.PreparedBandRequest (bottomSegment rightSegment
  topSegment leftSegment)
open Purelib.Riemann.Paths.PreparedPathWinding.ClearSegment (rawWinding)
open Purelib.Riemann.Topology.PreparedBankRootChains (ownerName)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential other :
  Differential genus}
  {ambient : Purelib.Geometry.Rational.Box} {current : Purelib.RootIsolation.State.Raw.RawWindingState
    curve.polynomial ambient}
  {profile : Profile curve.squarefree current.box} {fixed : DifferentialProfile profile differential.exponent}
  {target : Purelib.Data.Rat.Fraction.Rational} {request : PreparedBandRequest fixed target}
  {owner : Owner (curve.polynomial.eval request.sample.output.box.anchor)} {sheet : Fin 2}

namespace PreparedNewtonPairedBoundary.PairedBoundaryTraversal

open Purelib.Riemann.Paths in
/-- Closed-coordinate owner path of the retained paired boundary.

Appends the actual four bottom/right/top/left side paths, retaining the original anchor, starting owner and final
transported owner. -/
def ownerPath (boundary :
  PairedBoundaryTraversal request other owner sheet) :
    OwnerTracePath.OwnerPath curve.polynomial request.sample.output.box.anchor owner
      request.sample.output.box.anchor boundary.finishOwner :=
  boundary.bottom.ownerPath.append (boundary.right.ownerPath.append
    (boundary.top.ownerPath.append boundary.left.ownerPath))

open Purelib.Polynomial in
open Purelib.Riemann.Paths in
open Purelib.Riemann.RootContinuation in
/-- The retained owner path has raw winding 4.

Uses the exact four bottom/right/top/left side paths and their endpoint identities, preserving the selected Newton band
winding certificate. -/
theorem ownerPath_winding
  (boundary : PairedBoundaryTraversal request other owner sheet) :
    Winding.Polygon.Basic.chainRaw curve.polynomial request.sample.output.box.anchor boundary.ownerPath.vertices = 4 :=
      by
  simp only [PreparedNewtonPairedBoundary.PairedBoundaryTraversal.ownerPath, OwnerTracePath.OwnerPath.append_vertices,
    Winding.Polygon.Basic.chainRaw_append,
    OwnerTracePath.OwnerPath.vertices_terminal, PreparedNewtonPairedSide.PairedBoundarySide.ownerPath_winding_original]
  have equal : rawWinding (bottomSegment request) +
      (rawWinding (rightSegment request) + (rawWinding (topSegment request) + rawWinding (leftSegment request))) =
      Winding.Box.Basic.quadrupledBoxWinding curve.polynomial request.sample.output.box := by
    simp only [PreparedPathWinding.ClearSegment.rawWinding_eq_coordinateWinding,
      bottomSegment, rightSegment, topSegment,
      leftSegment, PreparedPathWinding.ClearSegment.coordinateWinding]
    rw [Winding.Box.Basic.quadrupledBoxWinding_eq]
    ring1
  exact (congrArg (fun last => rawWinding (bottomSegment request) +
    (rawWinding (rightSegment request) + (rawWinding (topSegment request) + last)))
      boundary.left.ownerPath_winding_original).trans (equal.trans request.sample.output.rawWindingFour)

end PreparedNewtonPairedBoundary.PairedBoundaryTraversal
namespace PreparedNewtonPairedDoubleBoundary.PairedDoubleBoundary

open Purelib.Riemann.Paths in
/-- Closed-coordinate owner path of the retained paired boundary.

Appends the actual first and second traversal paths, retaining the original anchor, starting owner and final transported
owner. -/
def ownerPath (boundary
  : PairedDoubleBoundary request other owner sheet) :
    OwnerTracePath.OwnerPath curve.polynomial request.sample.output.box.anchor owner
      request.sample.output.box.anchor boundary.finishOwner :=
  boundary.first.ownerPath.append boundary.second.ownerPath

open Purelib.Polynomial in
open Purelib.Riemann.Paths in
open Purelib.Riemann.RootContinuation in
/-- The retained owner path has raw winding 8.

Uses the exact first and second traversal paths and their endpoint identities, preserving the selected Newton band
winding certificate. -/
theorem
  ownerPath_winding
  (boundary : PairedDoubleBoundary request other owner sheet) :
    Winding.Polygon.Basic.chainRaw curve.polynomial request.sample.output.box.anchor boundary.ownerPath.vertices = 8 :=
      by
  simp only [PreparedNewtonPairedDoubleBoundary.PairedDoubleBoundary.ownerPath,
    OwnerTracePath.OwnerPath.append_vertices, Winding.Polygon.Basic.chainRaw_append,
    OwnerTracePath.OwnerPath.vertices_terminal, PreparedNewtonPairedBoundary.PairedBoundaryTraversal.ownerPath_winding]
  exact (congrArg (fun last : Int => 4 + last) boundary.second.ownerPath_winding).trans (by decide)

open Purelib.Approximation.Gaussian in
open Purelib.Riemann.Paths in
open Purelib.Riemann.RootContinuation in
/-- The double traversal returns an equivalent original root name.

Uses its actual owner path and raw winding eight with the retained Newton branch state to certify even-monodromy
closure. -/
def rootEquivalent
  (boundary : PairedDoubleBoundary request other owner sheet) :
    Equivalence.NamedEquivalent (ownerName boundary.finishOwner) (ownerName owner) :=
  PreparedPathClosure.SquareRootTrace.OwnerPath.rootEquivalent_of_even
    (NewtonPuncturedGrid.NewtonBandBounds.Sample.branchState request.sample)
    boundary.ownerPath 1 boundary.ownerPath_winding

open Purelib.Riemann.Topology
/-- Close the first-differential double-traversal chain at its original root name.

Transports only the final name through the retained even-winding root equivalence. -/
def firstClosedRootChain
  (boundary : PairedDoubleBoundary request other owner sheet) :
    RootChain boundary.firstChildren (ownerName owner) (ownerName owner) :=
  PreparedBankRootChains.RootChain.changeFinish
    boundary.firstRootChain boundary.rootEquivalent

/-- Close the second-differential double-traversal chain at its original root name.

Uses the same actual root equivalence while preserving the separate second-differential child chain. -/
def
  secondClosedRootChain
  (boundary : PairedDoubleBoundary request other owner sheet) :
    RootChain boundary.secondChildren (ownerName owner) (ownerName owner) :=
  PreparedBankRootChains.RootChain.changeFinish
    boundary.secondRootChain boundary.rootEquivalent

end PreparedNewtonPairedDoubleBoundary.PairedDoubleBoundary
end Purelib.Riemann.RootContinuation
