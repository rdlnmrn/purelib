module
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Topology.PreparedRefinementRootChains
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins
import Init.Prelude
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBoundary
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.RestorationJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Budget.Trace.Restoration
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedEdgeRecasting

open Purelib

open Purelib.Approximation

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins.BasisCommonParentBank

open Purelib.Geometry.Path.Gaussian

open Purelib.Riemann.Integration

open Purelib.Riemann.Topology

public section

/-! Schedule closing comparisons for the actual common-parent root thread. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonClosingJoins

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (ParentCovers Cover)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse (UniformBounds)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds (BasisBounds)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank (BasisCommonParentEntry
  BasisCommonParentBank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins.BasisCommonParentBank (Junction)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers
  BasisParentSourceCovers)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners (Join)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (DirectPathChain)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

variable {genus count otherCount : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
  {differential : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {bounds :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential} {patch :
    Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
  {data : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count} {cover :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data} {sources :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers parent}
  {otherParent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential} {otherPatch :
    Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch otherParent}
  {otherData : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data otherPatch otherCount}
    {otherCover : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover otherData}
  {otherSources : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers
    otherParent}
  {basis : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {allowance coefficientTarget : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {coverFloor floor :
    Nat}

namespace BasisCommonParentBank

open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named)

/-- The last actual parent joins the original first parent's common owner. -/
@[expose] def LastJunction (target : CommonParentBank.BasisCommonParentEntry cover sources basis allowance
  coefficientTarget coverFloor floor) :
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → (anchors :
      UniformReciprocalCover.ParentCovers parents) →
    (sources : SourceLocations.BasisParentSourceCovers parents) →
    CommonParentBank.BasisCommonParentBank anchors sources basis allowance coefficientTarget coverFloor floor → Type
  | _, .nil, _, _ => PUnit
  | _, .cons _ _ _ .nil, _, bank => BasisCommonParentBank.Junction bank.1 target
  | _, .cons _ _ _ (.cons _ _ _ tail), sources, bank =>
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonClosingJoins.BasisCommonParentBank.LastJunction
    target (.cons _ _ _ tail) sources.tail bank.2

/-- The retained final-to-first physical root join for a complete common-parent bank. -/
@[expose] def ClosingJunction : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
    (anchors : UniformReciprocalCover.ParentCovers parents) → (sources : SourceLocations.BasisParentSourceCovers
      parents) →
    CommonParentBank.BasisCommonParentBank anchors sources basis allowance coefficientTarget coverFloor floor → Type
  | _, .nil, _, _ => PUnit
  | _, (.cons patch data cover tail), sources, bank =>
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonClosingJoins.BasisCommonParentBank.LastJunction bank.1
    (.cons patch data cover tail) sources bank

/-- The first original parent starts at the retained centered path-chain coordinate. -/
theorem first_coordinate {parent : PreparedSubdivisionModelCore.CenteredEdge curve differential} {parents : List
  (PreparedSubdivisionModelCore.CenteredEdge curve differential)}
    {first last : Lifted.Basic.LiftedPoint 2}
    (chain : Nonempty (PreparedDirectDyadicRefinements.CenteredPathChain (parent :: parents) (start := first) (finish :=
      last))) :
    parent.edge.point 0 = first.coordinate := by
  obtain ⟨chain⟩ := chain
  cases chain
  exact parent.edge.point_zero

/-- Removing the first original parent retains the centered path chain from its actual endpoint. -/
theorem remaining_chain {parent : PreparedSubdivisionModelCore.CenteredEdge curve differential} {parents : List
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

/-- A singleton original parent ends at the retained centered path-chain coordinate. -/
theorem final_coordinate {parent : PreparedSubdivisionModelCore.CenteredEdge curve differential} {first last :
  Lifted.Basic.LiftedPoint 2}
    (chain : Nonempty (PreparedDirectDyadicRefinements.CenteredPathChain [parent] (start := first) (finish := last))) :
    parent.edge.point 1 = last.coordinate := by
  obtain ⟨chain⟩ := chain
  cases chain with
  | cons _ tail => cases tail; exact parent.edge.point_one

/-- Construct the last-parent join to the supplied original target entry.

The original physical path chain and named-root chain supply the endpoint equality and root return without acquiring
replacement parents. -/
@[expose] def lastJunction (target : CommonParentBank.BasisCommonParentEntry cover sources basis allowance
  coefficientTarget coverFloor floor) :
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → (anchors :
      UniformReciprocalCover.ParentCovers parents) →
    (sources : SourceLocations.BasisParentSourceCovers parents) →
    (bank : CommonParentBank.BasisCommonParentBank anchors sources basis allowance coefficientTarget coverFloor floor) →
    {first last : PreparedRefinementRootChains.Named} → PreparedRefinementRootChains.RootChain parents first last →
    {start finish : Lifted.Basic.LiftedPoint 2} → Nonempty (PreparedDirectDyadicRefinements.CenteredPathChain parents
      (start := start) (finish := finish)) →
    finish.coordinate = parent.edge.point 0 → Gaussian.Equivalence.NamedEquivalent last (parent.edge.rootName 0
      parent.edge.baseInside) →
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonClosingJoins.BasisCommonParentBank.LastJunction target
      anchors sources bank
  | _, .nil, _, _, _, _, _, _, _, _, _, _ => PUnit.unit
  | _, .cons _ _ _ .nil, _, bank, _, _, .cons _ _ (.nil returned), _, _, chain, pointEq, roots =>
      Junction.build bank.1 target
        ((Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonClosingJoins.BasisCommonParentBank.final_coordinate
        chain).trans pointEq) (returned.trans roots)
  | _, .cons _ _ _ (.cons _ _ _ _), _, bank, _, _, .cons _ _ remaining, _, _, chain, pointEq, roots =>
      Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonClosingJoins.BasisCommonParentBank.lastJunction
        target _ _ bank.2 remaining
        (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonClosingJoins.BasisCommonParentBank.remaining_chain
        chain) pointEq roots

/-- Geometry and root return are consumed from the very same cached parent chain used by the component acquisition.
Empty banks need no closing request. -/
@[expose] def ClosingJunction.build : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
    (anchors : UniformReciprocalCover.ParentCovers parents) → (sources : SourceLocations.BasisParentSourceCovers
      parents) →
    (bank : CommonParentBank.BasisCommonParentBank anchors sources basis allowance coefficientTarget coverFloor floor) →
    {first last : PreparedRefinementRootChains.Named} → PreparedRefinementRootChains.RootChain parents first last →
    {start finish : Lifted.Basic.LiftedPoint 2} → Nonempty (PreparedDirectDyadicRefinements.CenteredPathChain parents
      (start := start) (finish := finish)) →
    start.coordinate = finish.coordinate → Gaussian.Equivalence.NamedEquivalent last first →
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonClosingJoins.BasisCommonParentBank.ClosingJunction anchors
      sources bank
  | _, .nil, _, _, _, _, _, _, _, _, _, _ => PUnit.unit
  | _, (.cons patch data cover tail), sources, bank, _, _, roots@(.cons _ entry _), _, _, chain, pointEq, returned =>
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonClosingJoins.BasisCommonParentBank.lastJunction bank.1
        (.cons patch data cover tail) sources bank roots chain
        (pointEq.symm.trans
          (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonClosingJoins.BasisCommonParentBank.first_coordinate
          chain).symm) (returned.trans entry)

/-- The retained final-parent join threshold, or zero for an empty bank. -/
@[expose] def LastJunction.stage (target : CommonParentBank.BasisCommonParentEntry cover sources basis allowance
  coefficientTarget coverFloor floor) :
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → (anchors :
      UniformReciprocalCover.ParentCovers parents) →
    (sources : SourceLocations.BasisParentSourceCovers parents) →
    (bank : CommonParentBank.BasisCommonParentBank anchors sources basis allowance coefficientTarget coverFloor floor) →
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonClosingJoins.BasisCommonParentBank.LastJunction target
      anchors sources bank → Nat
  | _, .nil, _, _, _ => 0
  | _, .cons _ _ _ .nil, _, _, closing => closing.request.index
  | _, .cons _ _ _ (.cons _ _ _ _), _, bank, closing => stage target _ _ bank.2 closing

/-- The retained closing comparison's actual stage threshold. -/
@[expose] def ClosingJunction.stage : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
    (anchors : UniformReciprocalCover.ParentCovers parents) → (sources : SourceLocations.BasisParentSourceCovers
      parents) →
    (bank : CommonParentBank.BasisCommonParentBank anchors sources basis allowance coefficientTarget coverFloor floor) →
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonClosingJoins.BasisCommonParentBank.ClosingJunction anchors
      sources bank → Nat
  | _, .nil, _, _, _ => 0
  | _, (.cons patch data cover tail), sources, bank, closing =>
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonClosingJoins.BasisCommonParentBank.LastJunction.stage bank.1
    (.cons patch data cover tail) sources bank closing

end BasisCommonParentBank
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonClosingJoins
