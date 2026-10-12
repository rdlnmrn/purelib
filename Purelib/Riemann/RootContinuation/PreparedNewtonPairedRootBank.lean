module
import Purelib.Data.List.Map
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Riemann.Paths.PathArea
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.RootIsolation.State.Raw
import Purelib.Topology.Polygon.Stokes

public import Purelib.Riemann.RootContinuation.PreparedNewtonPairedBank
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedIncrements
import Purelib.Riemann.Topology.PreparedRecastRootChains
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Integration.PreparedPairedModelAccuracy
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedParent
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedModelAccuracy

public section

/-! Root chains on the actual paired child lists, joined through retained parents. -/
namespace Purelib.Riemann.RootContinuation.PreparedNewtonPairedRootBank

open Purelib
open Purelib.Data.Rat
open Purelib.Riemann.RootContinuation.NewtonBandBounds (Profile)
open Purelib.Riemann.RootContinuation.NewtonBandDifferentials (DifferentialProfile)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples (PreparedBandRequest)
open Purelib.Riemann.RootContinuation.PreparedNewtonPairedBank (PairedBoundaryParents)
open Purelib.Riemann.RootContinuation.PreparedNewtonPairedBank.PairedBoundaryParents (incrementBlocks)
open Purelib.RootIsolation.Newton.Band
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential other :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {ambient : Purelib.Geometry.Rational.Box} {current : Purelib.RootIsolation.State.Raw.RawWindingState
    curve.polynomial ambient}
  {profile : Profile curve.squarefree current.box} {fixed : DifferentialProfile profile differential.exponent}
  {target : Purelib.Data.Rat.Fraction.Rational} {request : PreparedBandRequest fixed target}

namespace PairedBoundaryParents

/-- Concatenate the original first-row child lists in retained parent order. -/
@[expose] def firstChildren : {parents : List (CenteredEdge curve differential)} →
    PairedBoundaryParents request other parents → List (CenteredEdge curve differential)
  | _, .nil => []
  | _, .cons head tail => head.refinement.first.block.children ++
      Purelib.Riemann.RootContinuation.PreparedNewtonPairedRootBank.PairedBoundaryParents.firstChildren tail

/-- Concatenate the original second-row child lists in retained parent order. -/
@[expose] def secondChildren : {parents : List (CenteredEdge curve differential)} →
    PairedBoundaryParents request other parents → List (CenteredEdge curve other)
  | _, .nil => []
  | _, .cons head tail => head.refinement.second.block.children ++
      Purelib.Riemann.RootContinuation.PreparedNewtonPairedRootBank.PairedBoundaryParents.secondChildren tail

section
open Purelib.Riemann.RootContinuation
/-- The exact second child list is the differential recast of the original first child list. -/
theorem children_eq {parents : List (CenteredEdge curve differential)}
    (bank : PairedBoundaryParents request other parents) :
    PreparedNewtonPairedRootBank.PairedBoundaryParents.secondChildren bank =
      (PreparedNewtonPairedRootBank.PairedBoundaryParents.firstChildren bank).map (recastCenteredEdge other) := by
  induction bank with
  | nil => rfl
  | cons head tail ih =>
  simp only [PreparedNewtonPairedRootBank.PairedBoundaryParents.firstChildren,
    PreparedNewtonPairedRootBank.PairedBoundaryParents.secondChildren,
    head.refinement.children_eq, Data.List.Map.map_append, ih, -eq_self, -iff_self]
  rfl

/-- Refine the original root chain through the retained first-row child banks.

The original entry equivalences and terminal names are kept while actual head refinements are appended in parent order.
-/
@[expose] def firstRootChain : ∀ {parents : List (CenteredEdge curve differential)} {first last : Named}
    (bank : PairedBoundaryParents request other parents), RootChain parents first last →
      RootChain (PreparedNewtonPairedRootBank.PairedBoundaryParents.firstChildren bank) first last
  | _, _, _, .nil, .nil equivalent => .nil equivalent
  | _, _, _, .cons head tail, .cons _ entry remaining =>
    (head.refinement.firstRootChain.changeStart entry).append
      (Purelib.Riemann.RootContinuation.PreparedNewtonPairedRootBank.PairedBoundaryParents.firstRootChain tail
        remaining)

end

open Purelib.Riemann.RootContinuation in
open Purelib.Riemann.Topology in
/-- Transport the original refined root chain to the exact second-row child list.

Differential recasting and the retained child-list equality preserve both original endpoint names. -/
@[expose] def secondRootChain {parents : List (CenteredEdge curve differential)} {first last : Named}
    (bank : PairedBoundaryParents request other parents) (roots : RootChain parents first last) :
    RootChain (PreparedNewtonPairedRootBank.PairedBoundaryParents.secondChildren bank) first last :=
  PreparedBankRootChains.RootChain.castChildren
    (PreparedNewtonPairedRootBank.PairedBoundaryParents.children_eq bank).symm
    (PreparedRecastRootChains.RootChain.recast other
      (PreparedNewtonPairedRootBank.PairedBoundaryParents.firstRootChain bank roots))

open Purelib.Riemann.Paths
open Purelib.Riemann.RootContinuation
open Purelib.Topology.Polygon
/-- The first coordinates of the original flattened paired increments read back the first child samples. -/
theorem increments_left {parents : List (CenteredEdge curve differential)}
    (bank : PairedBoundaryParents request other parents) :
    (PreparedNewtonPairedBank.PairedBoundaryParents.incrementBlocks bank).flatten.map Stokes.PrimitivePoint.left =
      (PreparedNewtonPairedRootBank.PairedBoundaryParents.firstChildren bank).map (fun child =>
        child.model.integralSample) := by
  induction bank with
  | nil => rfl
  | cons head tail ih =>
    simp only [PreparedNewtonPairedBank.PairedBoundaryParents.incrementBlocks,
      List.flatten_cons, Data.List.Map.map_append,
      PreparedNewtonPairedIncrements.PairedBoundaryParent.increments_left head,
      PreparedNewtonPairedRootBank.PairedBoundaryParents.firstChildren, ih,
      PathArea.increments, Data.List.Map.map_map, -eq_self, -iff_self]
    rfl

/-- The second coordinates of the original flattened paired increments read back the second child samples. -/
theorem increments_right {parents : List (CenteredEdge curve differential)}
    (bank : PairedBoundaryParents request other parents) :
    (PreparedNewtonPairedBank.PairedBoundaryParents.incrementBlocks bank).flatten.map Stokes.PrimitivePoint.right =
      (PreparedNewtonPairedRootBank.PairedBoundaryParents.secondChildren bank).map (fun child =>
        child.model.integralSample) := by
  induction bank with
  | nil => rfl
  | cons head tail ih =>
    simp only [PreparedNewtonPairedBank.PairedBoundaryParents.incrementBlocks,
      List.flatten_cons, Data.List.Map.map_append,
      PreparedNewtonPairedIncrements.PairedBoundaryParent.increments_right head,
      PreparedNewtonPairedRootBank.PairedBoundaryParents.secondChildren, ih,
      PathArea.increments, Data.List.Map.map_map, -eq_self, -iff_self]
    rfl

end PairedBoundaryParents
end Purelib.Riemann.RootContinuation.PreparedNewtonPairedRootBank
