module
import Purelib.Data.List.Map
import Purelib.Data.List.Append
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedBoundary
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedRootBank
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Riemann.Paths.PathArea
import Purelib.RootIsolation.State.Raw
import Purelib.Topology.Polygon.Stokes

public import Purelib.Riemann.RootContinuation.PreparedNewtonPairedDoubleBoundary
public import Purelib.Riemann.RootContinuation.PreparedNewtonPairedSideRoots
import Purelib.RootIsolation.Newton.Band.Basic
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedSide
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
import Purelib.Riemann.RootContinuation.PreparedNewtonBandBoundary
import Purelib.Data.Gaussian.Field
import Purelib.Integration.Path.PairedIncrementArea

open Purelib.Data

public section

/-! Actual root chains through all eight sides of the paired boundary sample. -/
namespace Purelib.Riemann.RootContinuation

open Purelib.RootIsolation.Newton.Band
open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Gaussian.Components.Basic (point)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Paths.PreparedBoundarySegments (SameSide)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples (PreparedBandRequest)
open Purelib.Riemann.RootContinuation.PreparedNewtonPairedBoundary (PairedBoundaryTraversal)
open Purelib.Riemann.RootContinuation.PreparedNewtonPairedDoubleBoundary (PairedDoubleBoundary)
open Purelib.Riemann.RootContinuation.NewtonBandBounds (Profile)
open Purelib.Riemann.RootContinuation.NewtonBandDifferentials (DifferentialProfile)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {ambient : Purelib.Geometry.Rational.Box} {current : Purelib.RootIsolation.State.Raw.RawWindingState
    curve.polynomial ambient}
  {profile : Profile curve.squarefree current.box} {fixed : DifferentialProfile profile differential.exponent}
  {target : Purelib.Data.Rat.Fraction.Rational}

open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)
open Purelib.Riemann.Topology.PreparedBankRootChains (ownerName)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

namespace PreparedNewtonPairedBoundary.PairedBoundaryTraversal
variable {request : PreparedBandRequest fixed target} {other :
  Differential genus}
  {owner : Owner (curve.polynomial.eval request.sample.output.box.anchor)} {sheet : Fin 2}

section
open Purelib.Riemann.RootContinuation
/-- Ordered first-differential children of the retained traversal.

Concatenates the actual bottom, right, top and left side child lists, preserving their original refinement owners. -/
@[expose] def firstChildren
  (boundary : PairedBoundaryTraversal request other owner sheet) : List (CenteredEdge curve differential) :=
  PreparedNewtonPairedRootBank.PairedBoundaryParents.firstChildren boundary.bottom.refined ++
    (PreparedNewtonPairedRootBank.PairedBoundaryParents.firstChildren boundary.right.refined ++
      (PreparedNewtonPairedRootBank.PairedBoundaryParents.firstChildren boundary.top.refined ++
        PreparedNewtonPairedRootBank.PairedBoundaryParents.firstChildren boundary.left.refined))

/-- Compose the first-differential root chain of the retained traversal.

Appends the actual bottom, right, top and left side chains using their existing endpoint owners and the exact retained
child order. -/
@[expose] def
  firstRootChain (boundary
  : PairedBoundaryTraversal request other owner sheet) :
    RootChain boundary.firstChildren (ownerName owner) (ownerName boundary.finishOwner) :=
  (PreparedNewtonPairedSideRoots.PairedBoundarySide.firstRootChain boundary.bottom).append
    ((PreparedNewtonPairedSideRoots.PairedBoundarySide.firstRootChain boundary.right).append
      ((PreparedNewtonPairedSideRoots.PairedBoundarySide.firstRootChain boundary.top).append
        (PreparedNewtonPairedSideRoots.PairedBoundarySide.firstRootChain boundary.left)))

/-- Ordered second-differential children of the retained traversal.

Concatenates the actual bottom, right, top and left side child lists, preserving their original refinement owners. -/
@[expose] def
  secondChildren (boundary
  : PairedBoundaryTraversal request other owner sheet) : List (CenteredEdge curve other) :=
  PreparedNewtonPairedRootBank.PairedBoundaryParents.secondChildren boundary.bottom.refined ++
    (PreparedNewtonPairedRootBank.PairedBoundaryParents.secondChildren boundary.right.refined ++
      (PreparedNewtonPairedRootBank.PairedBoundaryParents.secondChildren boundary.top.refined ++
        PreparedNewtonPairedRootBank.PairedBoundaryParents.secondChildren boundary.left.refined))

/-- Compose the second-differential root chain of the retained traversal.

Appends the actual bottom, right, top and left side chains using their existing endpoint owners and the exact retained
child order. -/
@[expose] def
  secondRootChain (boundary
  : PairedBoundaryTraversal request other owner sheet) :
    RootChain boundary.secondChildren (ownerName owner) (ownerName boundary.finishOwner) :=
  (PreparedNewtonPairedSideRoots.PairedBoundarySide.secondRootChain boundary.bottom).append
    ((PreparedNewtonPairedSideRoots.PairedBoundarySide.secondRootChain boundary.right).append
      ((PreparedNewtonPairedSideRoots.PairedBoundarySide.secondRootChain boundary.top).append
        (PreparedNewtonPairedSideRoots.PairedBoundarySide.secondRootChain boundary.left)))

end

open Purelib.Riemann.RootContinuation
open Purelib.Topology.Polygon
/-- Read the left increment projection as the first-differential child samples.

Uses the retained traversal block identities and preserves the exact concatenated child list. -/
theorem increments_left
  (boundary : PairedBoundaryTraversal request other owner sheet) :
    boundary.increments.map Stokes.PrimitivePoint.left =
      boundary.firstChildren.map (fun child => child.model.integralSample) := by
  simp only [PreparedNewtonPairedBoundary.PairedBoundaryTraversal.increments,
    PreparedNewtonPairedBoundary.PairedBoundaryTraversal.firstChildren, List.flatten_cons, List.flatten_nil,
      List.Append.append_nil,
    List.Map.map_append, PreparedNewtonPairedRootBank.PairedBoundaryParents.increments_left, -eq_self, -iff_self]
  rfl

/-- Read the right increment projection as the second-differential child samples.

Uses the retained traversal block identities and preserves the exact concatenated child list. -/
theorem increments_right
  (boundary : PairedBoundaryTraversal request other owner sheet) :
    boundary.increments.map Stokes.PrimitivePoint.right =
      boundary.secondChildren.map (fun child => child.model.integralSample) := by
  simp only [PreparedNewtonPairedBoundary.PairedBoundaryTraversal.increments,
    PreparedNewtonPairedBoundary.PairedBoundaryTraversal.secondChildren, List.flatten_cons, List.flatten_nil,
      List.Append.append_nil,
    List.Map.map_append, PreparedNewtonPairedRootBank.PairedBoundaryParents.increments_right, -eq_self, -iff_self]
  rfl

end PreparedNewtonPairedBoundary.PairedBoundaryTraversal
namespace PreparedNewtonPairedDoubleBoundary.PairedDoubleBoundary
variable {request : PreparedBandRequest fixed target} {other :
  Differential genus}
  {owner : Owner (curve.polynomial.eval request.sample.output.box.anchor)} {sheet : Fin 2}

/-- Ordered first-differential children of the retained double traversal.

Concatenates the actual first and second traversal child lists, preserving their original refinement owners. -/
@[expose] def
  firstChildren
  (boundary : PairedDoubleBoundary request other owner sheet) : List (CenteredEdge curve differential) :=
  boundary.first.firstChildren ++ boundary.second.firstChildren

/-- Compose the first-differential root chain of the retained double traversal.

Appends the actual first and second traversal chains using their existing endpoint owners and the exact retained child
order. -/
@[expose] def
  firstRootChain
  (boundary : PairedDoubleBoundary request other owner sheet) :
    RootChain boundary.firstChildren (ownerName owner) (ownerName boundary.finishOwner) :=
  boundary.first.firstRootChain.append boundary.second.firstRootChain

/-- Ordered second-differential children of the retained double traversal.

Concatenates the actual first and second traversal child lists, preserving their original refinement owners. -/
@[expose] def
  secondChildren
  (boundary : PairedDoubleBoundary request other owner sheet) : List (CenteredEdge curve other) :=
  boundary.first.secondChildren ++ boundary.second.secondChildren

/-- Compose the second-differential root chain of the retained double traversal.

Appends the actual first and second traversal chains using their existing endpoint owners and the exact retained child
order. -/
@[expose] def
  secondRootChain
  (boundary : PairedDoubleBoundary request other owner sheet) :
    RootChain boundary.secondChildren (ownerName owner) (ownerName boundary.finishOwner) :=
  boundary.first.secondRootChain.append boundary.second.secondRootChain

section
open Purelib.Riemann.RootContinuation
open Purelib.Topology.Polygon
/-- Read the left increment projection as the first-differential child samples.

Uses the retained double traversal block identities and preserves the exact concatenated child list. -/
theorem increments_left
  (boundary : PairedDoubleBoundary request other owner sheet) :
    (boundary.first.increments ++ boundary.second.increments).map Stokes.PrimitivePoint.left =
      boundary.firstChildren.map (fun child => child.model.integralSample) := by
  simp only [-eq_self, -iff_self,
    PreparedNewtonPairedDoubleBoundary.PairedDoubleBoundary.firstChildren,
    List.Map.map_append, PairedBoundaryTraversal.increments_left]
  rfl

/-- Read the right increment projection as the second-differential child samples.

Uses the retained double traversal block identities and preserves the exact concatenated child list. -/
theorem increments_right
  (boundary : PairedDoubleBoundary request other owner sheet) :
    (boundary.first.increments ++ boundary.second.increments).map Stokes.PrimitivePoint.right =
      boundary.secondChildren.map (fun child => child.model.integralSample) := by
  simp only [-eq_self, -iff_self,
    PreparedNewtonPairedDoubleBoundary.PairedDoubleBoundary.secondChildren,
    List.Map.map_append, PairedBoundaryTraversal.increments_right]
  rfl

end

open Purelib.Data.Gaussian
open Purelib.Integration.Polynomial.Gaussian.Path
open Purelib.Riemann.Paths
open Purelib.Topology.Polygon
/-- Read the cached left total as the first child path integral sample.

Uses the original summary total identity and projected increment readback on the exact double-traversal child list. -/
theorem total_left
  (boundary : PairedDoubleBoundary request other owner sheet) :
    boundary.summary.totalValue.left =
      (Basic.PathModel.mk (boundary.firstChildren.map CenteredEdge.model)).integralSample := by
  rw [boundary.summary.total_eq]
  change Data.Gaussian.Norm.Sum.Basic.gaussianSum ((boundary.first.increments ++ boundary.second.increments).map
    Stokes.PrimitivePoint.left) = _
  rw [boundary.increments_left]
  simpa only [PathArea.increments, List.Map.map_map, Function.comp_def] using
    PathArea.increments_sum (Basic.PathModel.mk (boundary.firstChildren.map CenteredEdge.model))

/-- Read the cached right total as the second child path integral sample.

Uses the original summary total identity and projected increment readback on the exact double-traversal child list. -/
theorem total_right
  (boundary : PairedDoubleBoundary request other owner sheet) :
    boundary.summary.totalValue.right =
      (Basic.PathModel.mk (boundary.secondChildren.map CenteredEdge.model)).integralSample := by
  rw [boundary.summary.total_eq]
  change Data.Gaussian.Norm.Sum.Basic.gaussianSum ((boundary.first.increments ++ boundary.second.increments).map
    Stokes.PrimitivePoint.right) = _
  rw [boundary.increments_right]
  simpa only [PathArea.increments, List.Map.map_map, Function.comp_def] using
    PathArea.increments_sum (Basic.PathModel.mk (boundary.secondChildren.map CenteredEdge.model))

end PreparedNewtonPairedDoubleBoundary.PairedDoubleBoundary
end Purelib.Riemann.RootContinuation
