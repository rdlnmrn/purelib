module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage
public import Purelib.Riemann.Integration.PreparedCoveredParentLists
import Purelib.Data.List.Append

/-! # Ordered append of the original covered source preparations

Both inputs retain the same original Targets and their actual patch/endpoint
caches. The operation joins their stored source products with no new request,
model, vertex, observation, patch or allocation. Every six-channel cell list
has the original ordered append equation on the actual centered chain.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count floor : Nat}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets original stage}

/-- Cover-index transport retains the complete original ordered vertex bank. -/
private theorem requestBank_castCover {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered replacement : CoveredParents count parents}
    (prepared : PreparedParents covered floor targets) (equal : covered = replacement) :
    requestBank replacement (prepared.castCover equal) = requestBank covered prepared := by
  cases equal
  rfl

/-- Cover-index transport retains the complete original source path on the same centered chain. -/
private theorem sources_castCover {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered replacement : CoveredParents count parents}
    (prepared : PreparedParents covered floor targets) (equal : covered = replacement)
    {start finish : LiftedPoint 2} (chain : CenteredPathChain parents (start := start) (finish := finish)) :
    sources replacement (prepared.castCover equal) chain = sources covered prepared chain := by
  cases equal
  rfl

/-- The one actual bank on the joined source family keeps every original signed occurrence in append order.

Repeated keys remain separate entries. This is a literal equation for the
original requestBank factory; it supplies no key injectivity or operational
agreement between distinct visits.
-/
theorem append_bank : {first last : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (firstCover : CoveredParents count first) → (lastCover : CoveredParents count last) →
    (firstPrepared : PreparedParents firstCover floor targets) →
    (lastPrepared : PreparedParents lastCover floor targets) →
    requestBank (PreparedCoveredParentLists.CoveredParents.append firstCover lastCover)
      (append firstCover lastCover firstPrepared lastPrepared) =
      requestBank firstCover firstPrepared ++ requestBank lastCover lastPrepared
  | [], _, .nil, lastCover, _, lastPrepared =>
      requestBank_castCover lastPrepared (PreparedCoveredParentLists.CoveredParents.append_nil lastCover).symm
  | _ :: _, _, .cons patch inside remaining, lastCover, firstPrepared, lastPrepared => by
      rcases firstPrepared with ⟨head, tail⟩
      have bank := requestBank_castCover
        (covered := CoveredParents.cons patch inside
          (PreparedCoveredParentLists.CoveredParents.append remaining lastCover))
        (⟨head, append remaining lastCover tail lastPrepared⟩ :
          PreparedParents (CoveredParents.cons patch inside
            (PreparedCoveredParentLists.CoveredParents.append remaining lastCover)) floor targets)
        (PreparedCoveredParentLists.CoveredParents.append_cons patch inside remaining lastCover).symm
      exact bank.trans (congrArg (List.cons
        (Vertex.Entry.request head.firstVertex.val targets.endpoint targets.endpoint_positive))
        (append_bank remaining lastCover tail lastPrepared))

/-- Every selected actual source-cell list preserves the exact original left/right append order.

The proof follows the same retained centered chain and source-product tail.
It establishes literal list equality for all six selectors without selecting
new source models, replacing caches or supplying an aggregate estimate.
-/
theorem append_cells : {first last : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (firstCover : CoveredParents count first) → (lastCover : CoveredParents count last) →
    (firstPrepared : PreparedParents firstCover floor targets) →
    (lastPrepared : PreparedParents lastCover floor targets) → {start middle finish : LiftedPoint 2} →
    (firstChain : CenteredPathChain first (start := start) (finish := middle)) →
    (lastChain : CenteredPathChain last (start := middle) (finish := finish)) → (channel : Fin 6) →
    (sources (PreparedCoveredParentLists.CoveredParents.append firstCover lastCover)
      (append firstCover lastCover firstPrepared lastPrepared) (firstChain.append lastChain)).cells channel =
      (sources firstCover firstPrepared firstChain).cells channel ++
        (sources lastCover lastPrepared lastChain).cells channel
  | [], _, .nil, lastCover, _, lastPrepared, _, _, _, .nil point, lastChain, channel => by
      change (sources _ (lastPrepared.castCover
        (PreparedCoveredParentLists.CoveredParents.append_nil lastCover).symm) lastChain).cells channel = _
      rewrite [sources_castCover]
      change (sources lastCover lastPrepared lastChain).cells channel =
        (Path.nil (parameter := parameter) point).cells channel ++ _
      rewrite [Path.cells_nil]
      rfl
  | _ :: _, _, .cons patch inside remaining, lastCover, firstPrepared, lastPrepared, _, _, _,
      .cons _ firstChain, lastChain, channel => by
      rcases firstPrepared with ⟨head, tail⟩
      have source := sources_castCover
        (covered := CoveredParents.cons patch inside
          (PreparedCoveredParentLists.CoveredParents.append remaining lastCover))
        (⟨head, append remaining lastCover tail lastPrepared⟩ :
          PreparedParents (CoveredParents.cons patch inside
            (PreparedCoveredParentLists.CoveredParents.append remaining lastCover)) floor targets)
        (PreparedCoveredParentLists.CoveredParents.append_cons patch inside remaining lastCover).symm
        (CenteredPathChain.cons _ (firstChain.append lastChain))
      have joined := congrArg (fun retained => retained.cells channel) source
      have headSource := congrArg (fun retained => retained.cells channel)
        (sources_cons patch inside (PreparedCoveredParentLists.CoveredParents.append remaining lastCover)
          head (append remaining lastCover tail lastPrepared) (firstChain.append lastChain))
      have headCells := headSource.trans
        (Path.cells_cons head.preparation.cell
          (sources (PreparedCoveredParentLists.CoveredParents.append remaining lastCover)
            (append remaining lastCover tail lastPrepared) (firstChain.append lastChain)) channel)
      have following := append_cells remaining lastCover tail lastPrepared firstChain lastChain channel
      have left := congrArg (List.cons (head.preparation.cell.models.cell channel)) following
      have first := congrArg (fun retained => retained.cells channel)
        (sources_cons patch inside remaining head tail firstChain)
      have firstCells := first.trans
        (Path.cells_cons head.preparation.cell (sources remaining tail firstChain) channel)
      have right := congrArg (fun cells => cells ++ (sources lastCover lastPrepared lastChain).cells channel) firstCells
      exact joined.trans (headCells.trans (left.trans right.symm))

/-- Equal original bounded occurrences retain the same entire preparation cache.

Only the original index equality is eliminated. Neither the covering patch
nor the complete source preparation is rebuilt or selected by a point key.
-/
theorem entry_congr {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count parents) (prepared : PreparedParents covered floor targets)
    {first last : Fin parents.length} (equal : first = last) :
    HEq (prepared.entry first) (prepared.entry last) := by
  cases equal
  rfl

/-- A left append occurrence preserves the complete original retained preparation at its SAME bounded index. -/
theorem append_entry_left : {first last : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (firstCover : CoveredParents count first) → (lastCover : CoveredParents count last) →
    (firstPrepared : PreparedParents firstCover floor targets) →
    (lastPrepared : PreparedParents lastCover floor targets) →
    (index : Fin first.length) → (bound : index.val < (first ++ last).length) →
    HEq ((append firstCover lastCover firstPrepared lastPrepared).entry ⟨index.val, bound⟩)
      (firstPrepared.entry index)
  | [], _, .nil, _, _, _, index, _ => Fin.elim0 index
  | _ :: _, _, .cons patch inside remaining, lastCover, firstPrepared, lastPrepared, ⟨0, _⟩, bound =>
      entry_castCover
        (covered := CoveredParents.cons patch inside
          (PreparedCoveredParentLists.CoveredParents.append remaining lastCover))
        (⟨firstPrepared.1, append remaining lastCover firstPrepared.2 lastPrepared⟩ :
          PreparedParents (CoveredParents.cons patch inside
            (PreparedCoveredParentLists.CoveredParents.append remaining lastCover)) floor targets)
        (PreparedCoveredParentLists.CoveredParents.append_cons patch inside remaining lastCover).symm
        ⟨0, bound⟩
  | _ :: _, _, .cons patch inside remaining, lastCover, firstPrepared, lastPrepared,
      ⟨index + 1, bounded⟩, bound =>
      (entry_castCover
        (covered := CoveredParents.cons patch inside
          (PreparedCoveredParentLists.CoveredParents.append remaining lastCover))
        (⟨firstPrepared.1, append remaining lastCover firstPrepared.2 lastPrepared⟩ :
          PreparedParents (CoveredParents.cons patch inside
            (PreparedCoveredParentLists.CoveredParents.append remaining lastCover)) floor targets)
        (PreparedCoveredParentLists.CoveredParents.append_cons patch inside remaining lastCover).symm
        ⟨index + 1, bound⟩).trans
          (append_entry_left remaining lastCover firstPrepared.2 lastPrepared
            ⟨index, Nat.lt_of_succ_lt_succ bounded⟩ (Nat.lt_of_succ_lt_succ bound))

/-- A right append occurrence preserves the SAME entire source preparation after the original left-prefix offset. -/
theorem append_entry_right : {first last : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (firstCover : CoveredParents count first) → (lastCover : CoveredParents count last) →
    (firstPrepared : PreparedParents firstCover floor targets) →
    (lastPrepared : PreparedParents lastCover floor targets) →
    (index : Fin last.length) → (bound : first.length + index.val < (first ++ last).length) →
    HEq ((append firstCover lastCover firstPrepared lastPrepared).entry ⟨first.length + index.val, bound⟩)
      (lastPrepared.entry index)
  | [], _, .nil, lastCover, _, lastPrepared, index, bound =>
      (entry_castCover lastPrepared (PreparedCoveredParentLists.CoveredParents.append_nil lastCover).symm
        ⟨0 + index.val, bound⟩).trans
          (entry_congr lastCover lastPrepared (first := ⟨0 + index.val, bound⟩) (last := index)
            (Fin.ext (Nat.zero_add index.val)))
  | parent :: first, last, .cons patch inside remaining, lastCover, firstPrepared, lastPrepared,
      index, bound => by
      have shift : (parent :: first).length + index.val = (first.length + index.val) + 1 :=
        Nat.succ_add first.length index.val
      have shifted : (first.length + index.val) + 1 < (first ++ last).length + 1 :=
        Eq.mp (congrArg (fun value => value < (first ++ last).length + 1) shift) bound
      have small : first.length + index.val < (first ++ last).length := Nat.lt_of_succ_lt_succ shifted
      have indices : (⟨(parent :: first).length + index.val, bound⟩ : Fin ((parent :: first) ++ last).length) =
          (⟨first.length + index.val, small⟩ : Fin (first ++ last).length).succ := Fin.ext shift
      have retained := entry_castCover
        (covered := CoveredParents.cons patch inside
          (PreparedCoveredParentLists.CoveredParents.append remaining lastCover))
        (⟨firstPrepared.1, append remaining lastCover firstPrepared.2 lastPrepared⟩ :
          PreparedParents (CoveredParents.cons patch inside
            (PreparedCoveredParentLists.CoveredParents.append remaining lastCover)) floor targets)
        (PreparedCoveredParentLists.CoveredParents.append_cons patch inside remaining lastCover).symm
        (⟨first.length + index.val, small⟩ : Fin (first ++ last).length).succ
      exact (entry_congr
        (PreparedCoveredParentLists.CoveredParents.append (CoveredParents.cons patch inside remaining) lastCover)
        (append (CoveredParents.cons patch inside remaining) lastCover firstPrepared lastPrepared) indices).trans
          (retained.trans
            (append_entry_right remaining lastCover firstPrepared.2 lastPrepared index small))

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

end
