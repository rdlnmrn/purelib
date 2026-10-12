module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBoundary
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
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.RestorationJoins
import Purelib.Riemann.RootContinuation.PreparedCachedParentRoots
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Budget.Trace.Restoration
import Purelib.Integration.Path.IncrementArea
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Paths.PreparedPathGluing
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Topology.PreparedBankRootChains

open Purelib

open Purelib.Approximation

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBoundary

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.RestorationJoins

open Purelib.Geometry

open Purelib.Geometry.Path.Gaussian

open Purelib.Polynomial.Geometry

open Purelib.Riemann.Integration

open Purelib.Riemann.Normalization

open Purelib.Riemann.Paths.PreparedPathParentCaches

open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels

open Purelib.Riemann.Paths.PreparedPathPrimitiveCover

open Purelib.Riemann.RootContinuation.PreparedCachedParentRoots

open Purelib.Riemann.Topology

public section

/-! Schedule each physical join of the retained common-parent bank. The
original path and operational root chain supply adjacency; no replacement
parent list or root acquisition is introduced. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (ParentCovers Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers
  BasisParentSourceCovers)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners (Join)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank (BasisCommonParentEntry
  BasisCommonParentBank)
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

set_option genInjectivity false in
/-- A physical join between two retained common-parent requests and its paid restoration request.

Both endpoint owners come from the original requests, and the next parent supplies the restoration target. -/
structure Junction
    (first : CommonParentBank.BasisCommonParentEntry cover sources basis allowance coefficientTarget coverFloor floor)
    (last : CommonParentBank.BasisCommonParentEntry otherCover otherSources basis allowance coefficientTarget coverFloor
      floor) where
  /-- The retained physical root join between the first parent's last owner and the next parent's first owner. -/ joined
    : ArcOwners.Join (BasisCommonParentRequest.lastView first.request).point (BasisCommonParentRequest.firstView
    last.request).point
  /-- The restoration request on that exact join and next-parent target. -/ request :
    RestorationJoins.BasisRestorationRequest basis joined last.request.restoration.target floor

constructive_injectivity Junction

/-- Construct a common-parent junction from physical endpoint equality and the original named-root agreement. -/
@[expose] def Junction.build
    (first : CommonParentBank.BasisCommonParentEntry cover sources basis allowance coefficientTarget coverFloor floor)
    (last : CommonParentBank.BasisCommonParentEntry otherCover otherSources basis allowance coefficientTarget coverFloor
      floor)
    (same : parent.edge.point 1 = otherParent.edge.point 0)
    (roots : Gaussian.Equivalence.NamedEquivalent (parent.edge.rootName 1 (by decide)) (otherParent.edge.rootName 0
      otherParent.edge.baseInside)) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins.BasisCommonParentBank.Junction first last :=
  let joined := BasisCommonParentRequest.join first.request last.request same roots
  ⟨joined, BasisRestorationRequest.build basis joined last.request.restoration.target last.request.restoration.positive
    floor⟩

/-- The complete dependent spine of junctions between consecutive retained common-parent entries. -/
@[expose] def Junctions : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
    (anchors : UniformReciprocalCover.ParentCovers parents) → (sources : SourceLocations.BasisParentSourceCovers
      parents) →
    CommonParentBank.BasisCommonParentBank anchors sources basis allowance coefficientTarget coverFloor floor → Type 2
  | _, .nil, _, _ => PUnit
  | _, .cons _ _ _ .nil, _, _ => PUnit
  | _, .cons _ _ _ (.cons _ _ _ _), _, bank =>
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins.BasisCommonParentBank.Junction bank.1 bank.2.1
        × Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins.BasisCommonParentBank.Junctions _
        _ bank.2

/-- Consecutive original parent edges share their physical endpoint coordinates. -/
@[expose] def PhysicalJoins : List (PreparedSubdivisionModelCore.CenteredEdge curve differential) → Prop
  | [] => True
  | [_] => True
  | first :: next :: remaining => first.edge.point 1 = next.edge.point 0 ∧
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins.BasisCommonParentBank.PhysicalJoins
    (next :: remaining)

/-- The start coordinate of a nonempty direct path chain is the first parent's start coordinate. -/
private theorem chain_start {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} {parent :
  PreparedSubdivisionModelCore.CenteredEdge curve differential}
    {start finish : Lifted.Basic.LiftedPoint 2} (chain : PreparedDirectDyadicRefinements.DirectPathChain (parent ::
      parents) (start := start) (finish := finish)) :
    start.coordinate = parent.edge.point 0 := by
  cases chain
  exact parent.edge.point_zero.symm

/-- An original direct path chain supplies every consecutive physical endpoint equality. -/
private theorem physicalJoins {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} {start
  finish : Lifted.Basic.LiftedPoint 2}
    (chain : PreparedDirectDyadicRefinements.DirectPathChain parents (start := start) (finish := finish)) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins.BasisCommonParentBank.PhysicalJoins parents :=
      by
  induction chain with
  | nil => trivial
  | @cons parent remaining finish tail ih =>
      cases remaining with
      | nil => trivial
      | cons next remaining =>
        exact ⟨parent.edge.point_one.trans
          (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins.BasisCommonParentBank.chain_start tail),
          ih⟩

/-- Read the original named-root agreement at the first retained parent junction. -/
@[expose] def root_head {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} {parent next :
  PreparedSubdivisionModelCore.CenteredEdge curve differential}
    {first last : Gaussian.Name.Basic.Named} (roots : PreparedRefinementRootChains.RootChain (parent :: next :: parents)
      first last) :
    Gaussian.Equivalence.NamedEquivalent (parent.edge.rootName 1 (by decide)) (next.edge.rootName 0
      next.edge.baseInside) :=
  match roots with
  | .cons _ _ (.cons _ entry _) => entry

/-- Retain the original root-chain tail starting at the first parent's endpoint root. -/
@[expose] def root_tail {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} {parent :
  PreparedSubdivisionModelCore.CenteredEdge curve differential}
    {first last : Gaussian.Name.Basic.Named} (roots : PreparedRefinementRootChains.RootChain (parent :: parents) first
      last) :
    PreparedRefinementRootChains.RootChain parents (parent.edge.rootName 1 (by decide)) last :=
  match roots with
  | .cons _ _ tail => tail

/-- Build all common-parent junctions from the supplied physical equalities and original root chain. -/
@[expose] def junctionsOfJoins : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
    (anchors : UniformReciprocalCover.ParentCovers parents) → (sources : SourceLocations.BasisParentSourceCovers
      parents) →
    (bank : CommonParentBank.BasisCommonParentBank anchors sources basis allowance coefficientTarget coverFloor floor) →
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins.BasisCommonParentBank.PhysicalJoins parents →
      {first last : Gaussian.Name.Basic.Named} →
    PreparedRefinementRootChains.RootChain parents first last →
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins.BasisCommonParentBank.Junctions anchors
      sources bank
  | _, .nil, _, _, _, _, _, _ => PUnit.unit
  | _, .cons _ _ _ .nil, _, _, _, _, _, _ => PUnit.unit
  | _, .cons _ _ _ (.cons _ _ _ _), _, bank, physical, _, _, roots =>
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins.BasisCommonParentBank.Junction.build bank.1
        bank.2.1 physical.1
        (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins.BasisCommonParentBank.root_head roots),

          junctionsOfJoins
          _ _ bank.2 physical.2
          (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins.BasisCommonParentBank.root_tail roots))

/-- Build the retained junction spine using the original direct path and operational root chains. -/
@[expose] def junctions {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)}
    (anchors : UniformReciprocalCover.ParentCovers parents) (sources : SourceLocations.BasisParentSourceCovers parents)
    (bank : CommonParentBank.BasisCommonParentBank anchors sources basis allowance coefficientTarget coverFloor floor)
    {start finish : Lifted.Basic.LiftedPoint 2}
    (chain : Nonempty (PreparedDirectDyadicRefinements.DirectPathChain parents (start := start) (finish := finish)))
    {first last : Gaussian.Name.Basic.Named} (roots : PreparedRefinementRootChains.RootChain parents first last) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins.BasisCommonParentBank.Junctions anchors
      sources bank :=
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins.BasisCommonParentBank.junctionsOfJoins anchors
    sources bank (by obtain ⟨chain⟩ := chain; exact
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins.BasisCommonParentBank.physicalJoins chain) roots

/-- Shared reading stages must include these joins in addition to each parent's own acquisition plan. -/
@[expose] def Junctions.stage : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
    (anchors : UniformReciprocalCover.ParentCovers parents) → (sources : SourceLocations.BasisParentSourceCovers
      parents) →
    (bank : CommonParentBank.BasisCommonParentBank anchors sources basis allowance coefficientTarget coverFloor floor) →
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins.BasisCommonParentBank.Junctions anchors sources
      bank → Nat
  | _, .nil, _, _, _ => 0
  | _, .cons _ _ _ .nil, _, _, _ => 0
  | _, .cons _ _ _ (.cons _ _ _ _), _, bank, joins =>
      max joins.1.request.index (stage _ _ bank.2 joins.2)

set_option genInjectivity false in
/-- The complete common-parent request bank, junctions and shared polynomial threshold.

Both cover banks retain the original parent list, and the cached threshold pays every parent and join. -/
structure Schedule {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)}
    (anchors : UniformReciprocalCover.ParentCovers parents) (sources : SourceLocations.BasisParentSourceCovers parents)
    (basis : ReciprocalPaddedBasisBounds.BasisBounds bounds)
    (allowance coefficientTarget : InverseRootPolynomial.Coordinate) (coverFloor floor : Nat) where
  /-- The complete retained common-parent request bank. -/ bank : CommonParentBank.BasisCommonParentBank anchors sources
    basis allowance coefficientTarget coverFloor floor
  /-- The junction spine on those exact retained parent entries. -/ joins :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins.BasisCommonParentBank.Junctions anchors sources
    bank
  /-- The cached common parent and junction threshold. -/ index : Nat
  /-- The threshold is exactly the maximum of the retained parent-bank and junction stages. -/ index_eq : index = max
    (BasisCommonParentBank.index anchors sources bank) (joins.stage anchors sources bank)

constructive_injectivity Schedule

namespace Schedule

/-- Use the cache's original parent and root chains. Both input cover banks are indexed by that same retained parent
list. -/
@[expose] def ofCache {ambient : Rational.Box} {start finish : InverseRootPolynomial.Gaussian}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)}
    {covered : PreparedClearPathModels.CoveredTracedPath path owner} {sheet : Fin 2}
    (cache : PreparedClearPathModels.ParentCache covered differential sheet)
    (anchors : UniformReciprocalCover.ParentCovers cache.parents) (sources : SourceLocations.BasisParentSourceCovers
      cache.parents)
    (basis : ReciprocalPaddedBasisBounds.BasisBounds bounds)
    (allowance coefficientTarget : InverseRootPolynomial.Coordinate) (positive : 0 < allowance) (coefficientPositive : 0
      < coefficientTarget)
    (coverFloor floor : Nat) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins.BasisCommonParentBank.Schedule anchors sources
      basis allowance coefficientTarget coverFloor floor :=
  let bank := BasisCommonParentBank.build basis allowance coefficientTarget positive coefficientPositive coverFloor
    floor anchors sources
  let joins := Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins.BasisCommonParentBank.junctions
    anchors sources bank (start := ⟨start, sheet⟩) (finish := ⟨finish, sheet⟩)
    (by obtain ⟨chain⟩ := (ParentCache.chain cache); exact ⟨chain.toDirectPathChain⟩) (ParentCache.rootChain cache)
  ⟨bank, joins, max (BasisCommonParentBank.index anchors sources bank) (joins.stage anchors sources bank), rfl⟩

variable {parents : List (Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)}
  {anchors : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents} {sources :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisParentSourceCovers parents}

/-- Every parent-bank threshold is paid by the retained schedule. -/
theorem parents_le (schedule :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins.BasisCommonParentBank.Schedule anchors sources
  basis allowance coefficientTarget coverFloor floor) :
    BasisCommonParentBank.index anchors sources schedule.bank ≤ schedule.index :=
  (Purelib.Data.Nat.Order.le_max_left ..).trans_eq schedule.index_eq.symm

/-- Every junction threshold is paid by the retained schedule. -/
theorem joins_le (schedule :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins.BasisCommonParentBank.Schedule anchors sources
  basis allowance coefficientTarget coverFloor floor) :
    schedule.joins.stage anchors sources schedule.bank ≤ schedule.index :=
  (Purelib.Data.Nat.Order.le_max_right ..).trans_eq schedule.index_eq.symm

end Schedule

end BasisCommonParentBank
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins
