module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedBoundarySegments
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSourceRootJoins
public import Purelib.Riemann.RootContinuation.PreparedCachedParentRoots
import Init.Prelude
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.Paths.PreparedPathGluing
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.PreparedBankRootChains

open Purelib

open Purelib.Approximation

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSourceRootJoins

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover

open Purelib.Geometry

open Purelib.Geometry.Path.Gaussian

open Purelib.Polynomial.Geometry

open Purelib.Riemann.Branches

open Purelib.Riemann.Integration

open Purelib.Riemann.Normalization

open Purelib.Riemann.Paths

open Purelib.Riemann.Paths.PreparedPathParentCaches

open Purelib.Riemann.Paths.PreparedPathPrimitiveCover

open Purelib.Riemann.RootContinuation.PreparedCachedParentRoots

open Purelib.Riemann.Topology

@[expose] public section

/-!
# Actual cap joins between complete exterior parents

The prepared source path supplies both endpoint adjacency and its retained
root chain. These are consumed to join the cached last/first cap owners of
each pair of complete parent comparisons.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (DirectPathChain)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison (Preparation)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {regular : RegularBounds.Data cap}
  {parent : CenteredEdge curve differential} {patch :
    UniformPrimitiveSheetCompatibility.PreparedPatch parent}
  {data : UniformReciprocalModels.Data patch count} {cover :
    Cover data}
  {otherCount : Nat} {otherParent : CenteredEdge curve
    differential} {otherPatch : UniformPrimitiveSheetCompatibility.PreparedPatch otherParent}
  {otherData : UniformReciprocalModels.Data otherPatch otherCount}
    {otherCover : Cover otherData}

/-- Join two retained cap-parent endpoint owners using the prepared source adjacency and its operational root
equivalence. -/
def Preparation.join (first : Preparation regular cover) (last : Preparation regular
  otherCover)
    (same : parent.edge.point 1 = otherParent.edge.point 0)
    (roots : NamedEquivalent (parent.edge.rootName 1 (by decide)) (otherParent.edge.rootName 0
      otherParent.edge.baseInside)) :
    Join first.boundary.last.point last.boundary.first.point :=
  let source := SourceJoin.build first.boundary.last.point.root last.boundary.first.point.root
    (parent.edge.point 1) rfl same.symm roots
  Join.ofRoots first.boundary.last.point last.boundary.first.point same
    (SourceJoin.rootEquivalent
      (first := first.boundary.last.point.root) (last := last.boundary.first.point.root) source)

set_option genInjectivity false in
/-- Comparison preparations indexed by the exact retained list of exterior parent covers. -/
inductive SideBank (regular : RegularBounds.Data cap) :
    {parents : List (CenteredEdge curve differential)} →
      ParentCovers parents → Type 2
  /-- The empty retained comparison or join bank. -/ | nil :
    ParentJoins.SideBank regular .nil
  /-- Retain the first cover's comparison preparation and the bank for the exact remaining covers. -/ | cons {parent :
    CenteredEdge curve differential} {parents : List
    (CenteredEdge curve differential)}
      {patch : UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data : UniformReciprocalModels.Data patch
        genus}
      {cover : Cover data} {covers : ParentCovers parents}
      (head : Preparation regular cover) (tail :
        ParentJoins.SideBank regular covers) :
        ParentJoins.SideBank regular (.cons patch data cover covers)

constructive_injectivity SideBank

namespace SideBank

/-- Prepare each exact retained exterior cover and cache the resulting ordered comparison bank. -/
def build (regular : RegularBounds.Data cap) : {parents : List (CenteredEdge curve
  differential)} →
    (covers : ParentCovers parents) →
      SideBank regular covers
  | _, .nil => .nil
  | _, .cons _ _ cover remaining => .cons (Preparation.build regular cover)
    (SideBank.build regular remaining)

/-- Consecutive retained parents have equal actual physical endpoint coordinates. -/
public def PhysicalJoins : List (CenteredEdge curve differential) → Prop
  | [] => True
  | [_] => True
  | first :: next :: remaining => first.edge.point 1 = next.edge.point 0 ∧
    SideBank.PhysicalJoins (next :: remaining)

/-- The start coordinate of a nonempty direct path chain is the first retained parent's initial point. -/
public theorem chain_start {parents : List (CenteredEdge curve differential)} {parent :
  CenteredEdge curve differential}
    {start finish : Lifted.Basic.LiftedPoint 2} (chain : DirectPathChain (parent ::
      parents) (start := start) (finish := finish)) :
    start.coordinate = parent.edge.point 0 := by
  cases chain
  exact parent.edge.point_zero.symm

/-- A retained direct path chain certifies adjacency of all actual consecutive parent endpoints. -/
public theorem physicalJoins {parents : List (CenteredEdge curve differential)} {start
  finish : Lifted.Basic.LiftedPoint 2}
    (chain : DirectPathChain parents (start := start) (finish := finish)) :
      PhysicalJoins parents := by
  induction chain with
  | nil => trivial
  | @cons parent remaining finish tail ih =>
      cases remaining with
      | nil => trivial
      | cons next remaining =>
        exact ⟨parent.edge.point_one.trans (chain_start
          tail), ih⟩

/-- Read the operational root-name equivalence at the first retained parent junction. -/
public def root_head {parents : List (CenteredEdge curve differential)} {parent next :
  CenteredEdge curve differential}
    {first last : Gaussian.Name.Basic.Named} (roots : RootChain (parent :: next :: parents)
      first last) :
    NamedEquivalent (parent.edge.rootName 1 (by decide)) (next.edge.rootName 0
      next.edge.baseInside) :=
  match roots with
  | .cons _ _ (.cons _ entry _) => entry

/-- Read the retained root-chain tail beginning at the first parent's final root name. -/
public def root_tail {parents : List (CenteredEdge curve differential)} {parent :
  CenteredEdge curve differential}
    {first last : Gaussian.Name.Basic.Named} (roots : RootChain (parent :: parents) first
      last) :
    RootChain parents (parent.edge.rootName 1 (by decide)) last :=
  match roots with
  | .cons _ _ tail => tail

set_option genInjectivity false in
/-- Operational coordinate joins between the actual consecutive cap-parent endpoint owners. -/
inductive Links : {parents : List (CenteredEdge curve differential)} → {covers :
  ParentCovers parents} →
    SideBank regular covers → Type 2
  /-- The empty retained comparison or join bank. -/ | nil :
    SideBank.Links .nil
  /-- A singleton parent bank has no internal junction to compare. -/ | one {parent :
    CenteredEdge curve differential} {patch :
    UniformPrimitiveSheetCompatibility.PreparedPatch parent}
      {data : UniformReciprocalModels.Data patch genus} {cover : Cover data}
      (head : Preparation regular cover) :
        SideBank.Links (.cons head .nil)
  /-- Retain the coordinate join from the first parent's last endpoint to the next parent's first endpoint, together
    with the remaining joins. -/ | cons {parent next : CenteredEdge curve differential}
    {parents : List (CenteredEdge curve differential)}
      {patch : UniformPrimitiveSheetCompatibility.PreparedPatch parent} {nextPatch :
        UniformPrimitiveSheetCompatibility.PreparedPatch next}
      {data : UniformReciprocalModels.Data patch genus} {nextData : UniformReciprocalModels.Data nextPatch genus}
      {cover : Cover data} {nextCover : Cover nextData}
      {covers : ParentCovers parents}
      {head : Preparation regular cover} {nextHead : Preparation regular nextCover}
        {tail : SideBank regular covers}
      (joined : Join head.boundary.last.point nextHead.boundary.first.point)
      (remaining : SideBank.Links (.cons nextHead tail))
        : SideBank.Links (.cons head (.cons nextHead
        tail))

constructive_injectivity Links

set_option genInjectivity false in
/-- Operational primitive-name equivalences at every junction of the exact retained cap-parent bank. -/
inductive PrimitiveLinks {index : Nat} {box : Rational.Box}
    (sample : Primitives.Sample cap differential index box) :
    {parents : List (CenteredEdge curve differential)} → {covers :
      ParentCovers parents} →
    SideBank regular covers → Type 2
  /-- The empty retained comparison or join bank. -/ | nil :
    SideBank.PrimitiveLinks sample .nil
  /-- A singleton parent bank has no internal junction to compare. -/ | one {parent :
    CenteredEdge curve differential} {patch :
    UniformPrimitiveSheetCompatibility.PreparedPatch parent}
      {data : UniformReciprocalModels.Data patch genus} {cover : Cover data}
      (head : Preparation regular cover) :
        SideBank.PrimitiveLinks sample (.cons head .nil)
  /-- Retain the actual primitive-name equivalence at the first parent boundary and the exact tail of comparisons. -/ |
    cons {parent next : CenteredEdge curve differential} {parents : List
    (CenteredEdge curve differential)}
      {patch : UniformPrimitiveSheetCompatibility.PreparedPatch parent} {nextPatch :
        UniformPrimitiveSheetCompatibility.PreparedPatch next}
      {data : UniformReciprocalModels.Data patch genus} {nextData : UniformReciprocalModels.Data nextPatch genus}
      {cover : Cover data} {nextCover : Cover nextData}
      {covers : ParentCovers parents}
      {head : Preparation regular cover} {nextHead : Preparation regular nextCover}
        {tail : SideBank regular covers}
      (agreement : NamedEquivalent (head.boundary.last.point.coordinates.chartPrimitive
        sample).name
        (nextHead.boundary.first.point.coordinates.chartPrimitive sample).name)
      (remaining : SideBank.PrimitiveLinks sample (.cons
        nextHead tail)) : SideBank.PrimitiveLinks sample
        (.cons head (.cons nextHead tail))

constructive_injectivity PrimitiveLinks

/-- Read the primitive-name equivalences from the retained coordinate joins at the supplied cap sample. -/
def Links.primitives {index : Nat} {box : Rational.Box} (sample : Primitives.Sample cap differential
  index box) :
    {parents : List (CenteredEdge curve differential)} → {covers :
      ParentCovers parents} →
    {prepared : SideBank regular covers} →
      Links prepared →
      PrimitiveLinks sample prepared
  | _, _, _, .nil => .nil
  | _, _, _, .one head => .one head
  | _, _, _, .cons joined remaining => .cons (joined.primitiveEquivalent sample) (primitives sample remaining)

/-- Combine the retained physical endpoint equalities and executable root chain into actual cap-parent coordinate joins.
-/
public def linksOfJoins : {parents : List (CenteredEdge curve differential)} → {covers :
  ParentCovers parents} →
    (prepared : SideBank regular covers) →
      PhysicalJoins parents → {first last :
      Gaussian.Name.Basic.Named} →
    RootChain parents first last →
      Links prepared
  | _, _, .nil, _, _, _, _ => .nil
  | _, _, .cons head .nil, _, _, _, _ => .one head
  | _, _, .cons head (.cons next tail), physical, _, _, roots =>
      .cons (Preparation.join head next physical.1
        (root_head roots))
        (SideBank.linksOfJoins (.cons next tail)
        physical.2 (root_tail roots))

/-- The retained joins between the actual consecutive comparison endpoint owners. -/
def links {parents : List (CenteredEdge curve differential)} {covers :
  ParentCovers parents}
    (prepared : SideBank regular covers) {start finish :
      Lifted.Basic.LiftedPoint 2}
    (chain : Nonempty (DirectPathChain parents (start := start) (finish := finish)))
    {first last : Gaussian.Name.Basic.Named} (roots : RootChain parents first last) :
      Links prepared :=
  linksOfJoins prepared (by
      obtain ⟨chain⟩ := chain;
      exact physicalJoins chain) roots

end SideBank

namespace Path

set_option genInjectivity false in
/-- A complete retained exterior path may cross ambient corners. Its covers, properness and internal root joins all
refer to the same parent list. -/
structure Preparation (regular : RegularBounds.Data cap) (parents : List (CenteredEdge
  curve differential)) where
  /-- The retained reciprocal covers indexed by this exact parent list. -/ covers : ParentCovers
    parents
  /-- The cached comparison preparations for these exact covers. -/ bank :
    SideBank regular covers
  /-- The retained joins between the actual consecutive comparison endpoint owners. -/ links :
    SideBank.Links bank
  /-- Every retained parent satisfies the original properness condition. -/ proper :
    PreparedDyadicRefinements.AllParentsProper parents

constructive_injectivity Preparation

/-- Consume the existing cache and certified reciprocal covers. -/
def Preparation.ofCache {ambient : Rational.Box} {start finish : Gaussian}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)}
    {covered : PreparedClearPathModels.CoveredTracedPath path owner} {sheet : Fin 2}
    (regular : RegularBounds.Data cap)
    (cache : PreparedClearPathModels.ParentCache covered differential sheet)
    (covers : ParentCovers cache.parents) :
      Preparation regular cache.parents :=
  let bank := SideBank.build regular covers
  ⟨covers, bank, bank.links (start := ⟨start, sheet⟩) (finish := ⟨finish, sheet⟩)
    (by obtain ⟨chain⟩ := cache.chain; exact ⟨chain.toDirectPathChain⟩)
    (ParentCache.rootChain cache), cache.proper⟩

end Path

namespace Segment

open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)
open Purelib.Riemann.Paths.PreparedPathDecomposition (CoveredSegment)
open Purelib.Riemann.Paths.PreparedBoundarySegments (SameSide)
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)

variable {start finish : Gaussian} {segment :
  ClearPath.ClearSegment curve.polynomial
  (Ambient curve) start finish}
  {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {piece :
    CoveredSegment segment owner} {sheet : Fin 2}

/-- Prepare the retained segment's cap comparison bank from its existing parent cache and certified ambient side. -/
def prepare (regular : RegularBounds.Data cap) (cache : ParentCache piece.path differential
  sheet)
    (side : SameSide (Ambient curve) start finish) :
      Path.Preparation regular cache.parents :=
  Path.Preparation.ofCache regular cache (Segment.acquire cache
    side)

end Segment
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
