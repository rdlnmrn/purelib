module
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Topology.PreparedRefinementRootChains
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
import Init.Prelude
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Normalization.InverseRootPolynomial

open Purelib

open Purelib.Approximation

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins

open Purelib.Geometry.Path.Gaussian

open Purelib.Riemann.Integration

open Purelib.Riemann.Topology

@[expose] public section

/-!
# Root-return joins on the actual reciprocal disk parent bank

The source's closed operational root thread identifies the final and initial
retained cap coordinates. Endpoint geometry is read only as erased evidence;
no replacement root or period preparation supplies a closing occurrence.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ClosingJoins

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison (Preparation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins (SideBank)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential} {patch :
    Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
  {data : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count} {cover :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data}

/-- The empty bank has no final occurrence; otherwise select the actual last parent. -/
def LastJoin (target : ParentComparison.Preparation regular cover) : {parents : List
  (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
    {covers : UniformReciprocalCover.ParentCovers parents} → ParentJoins.SideBank regular covers → Type
  | _, _, .nil => PUnit
  | _, _, .cons head .nil => ArcOwners.Join head.boundary.last.point target.boundary.first.point
  | _, _, .cons _ (.cons next tail) => Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ClosingJoins.LastJoin target
    (.cons next tail)

/-- The actual coordinate join from the final retained cap parent back to the first, with no closing occurrence for an
empty bank. -/
def ClosingJoin : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
    {covers : UniformReciprocalCover.ParentCovers parents} → ParentJoins.SideBank regular covers → Type
  | _, _, .nil => PUnit
  | _, _, .cons head tail => Curves.Hyperelliptic.Charts.Reciprocal.Disk.ClosingJoins.LastJoin head (.cons head tail)

/-- The first retained parent begins at the original centered path chain's actual start coordinate. -/
public theorem first_coordinate {parent : PreparedSubdivisionModelCore.CenteredEdge curve differential} {parents : List
  (PreparedSubdivisionModelCore.CenteredEdge curve differential)}
    {first last : Lifted.Basic.LiftedPoint 2}
    (chain : Nonempty (PreparedDirectDyadicRefinements.CenteredPathChain (parent :: parents) (start := first) (finish :=
      last))) :
    parent.edge.point 0 = first.coordinate := by
  obtain ⟨chain⟩ := chain
  cases chain
  exact parent.edge.point_zero

/-- Removing the first retained parent preserves the exact centered path chain on its dependent tail. -/
public theorem remaining_chain {parent : PreparedSubdivisionModelCore.CenteredEdge curve differential} {parents : List
  (PreparedSubdivisionModelCore.CenteredEdge curve differential)}
    {first last : Lifted.Basic.LiftedPoint 2}
    (chain : Nonempty (PreparedDirectDyadicRefinements.CenteredPathChain (parent :: parents) (start := first) (finish :=
      last))) :
    Nonempty (PreparedDirectDyadicRefinements.CenteredPathChain parents
      (start := ⟨parent.edge.segment.pointAt parent.edge.request.endpoint.parameter, parent.edge.sheet⟩) (finish :=
        last)) := by
  obtain ⟨chain⟩ := chain
  cases chain with
  | cons _ tail => exact ⟨tail⟩

/-- The sole retained parent ends at the centered path chain's actual final coordinate. -/
public theorem final_coordinate {parent : PreparedSubdivisionModelCore.CenteredEdge curve differential} {first last :
  Lifted.Basic.LiftedPoint 2}
    (chain : Nonempty (PreparedDirectDyadicRefinements.CenteredPathChain [parent] (start := first) (finish := last))) :
    parent.edge.point 1 = last.coordinate := by
  obtain ⟨chain⟩ := chain
  cases chain with
  | cons _ tail => cases tail; exact parent.edge.point_one

/-- Follow the original root chain to construct the last retained cap-parent join to the supplied target. -/
public def lastJoin (target : ParentComparison.Preparation regular cover) :
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
      UniformReciprocalCover.ParentCovers parents} →
    (bank : ParentJoins.SideBank regular covers) → {first last : PreparedRefinementRootChains.Named} →
      PreparedRefinementRootChains.RootChain parents first last →
    {start finish : Lifted.Basic.LiftedPoint 2} → Nonempty (PreparedDirectDyadicRefinements.CenteredPathChain parents
      (start := start) (finish := finish)) →
    finish.coordinate = parent.edge.point 0 → Gaussian.Equivalence.NamedEquivalent last (parent.edge.rootName 0
      parent.edge.baseInside) → Curves.Hyperelliptic.Charts.Reciprocal.Disk.ClosingJoins.LastJoin target bank
  | _, _, .nil, _, _, _, _, _, _, _, _ => ⟨⟩
  | _, _, .cons head .nil, _, _, .cons _ _ (.nil returned), _, _, chain, pointEq, roots =>
      Preparation.join head target ((Curves.Hyperelliptic.Charts.Reciprocal.Disk.ClosingJoins.final_coordinate
        chain).trans pointEq) (returned.trans roots)
  | _, _, .cons _ (.cons next tail), _, _, .cons _ _ remaining, _, _, chain, pointEq, roots =>
      Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ClosingJoins.lastJoin target (.cons next tail) remaining
        (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ClosingJoins.remaining_chain chain) pointEq roots

/-- Root return and geometry come from the same cached source parent list. -/
def ClosingJoin.build : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
    {covers : UniformReciprocalCover.ParentCovers parents} → (bank : ParentJoins.SideBank regular covers) →
    {first last : PreparedRefinementRootChains.Named} → PreparedRefinementRootChains.RootChain parents first last →
    {start finish : Lifted.Basic.LiftedPoint 2} → Nonempty (PreparedDirectDyadicRefinements.CenteredPathChain parents
      (start := start) (finish := finish)) →
    start.coordinate = finish.coordinate → Gaussian.Equivalence.NamedEquivalent last first →
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ClosingJoins.ClosingJoin bank
  | _, _, .nil, _, _, _, _, _, _, _, _ => ⟨⟩
  | _, _, .cons head tail, _, _, roots@(.cons _ entry _), _, _, chain, pointEq, returned =>
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ClosingJoins.lastJoin head (.cons head tail) roots chain
        (pointEq.symm.trans (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ClosingJoins.first_coordinate
        chain).symm) (returned.trans entry)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ClosingJoins
