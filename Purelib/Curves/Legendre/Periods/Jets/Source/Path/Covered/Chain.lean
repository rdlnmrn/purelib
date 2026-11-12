module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered
public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic

/-! # Ordered source paths consuming the retained covered-parent caches

The original centered geometric chain determines the exact lifted path.
The stored dependent parent product supplies each original source cell.
The operation only joins those retained cells in the original parent order;
it invokes no patch, point, vertex, request or model producer.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count floor : Nat}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets original stage}

/-- Exact cover transport preserves the original stored source-cell list. -/
theorem cells_castCover {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered replacement : CoveredParents count parents}
    (prepared : PreparedParents covered floor targets) (equal : covered = replacement) (channel : Fin 6) :
    cells (prepared.castCover equal) channel = cells prepared channel := by
  cases equal
  rfl

/-- Concatenating the SAME supplied preparation products appends their literal stored source-cell lists. -/
theorem cells_append (channel : Fin 6) :
    {first last : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (firstCovered : CoveredParents count first) → (lastCovered : CoveredParents count last) →
    (prepared : PreparedParents firstCovered floor targets) →
    (remaining : PreparedParents lastCovered floor targets) →
      cells (covered := firstCovered.append lastCovered)
        (append firstCovered lastCovered prepared remaining) channel =
        cells (covered := firstCovered) prepared channel ++ cells (covered := lastCovered) remaining channel
  | [], _, .nil, lastCovered, empty, remaining => by
      cases empty
      rewrite [cells_nil]
      unfold append
      exact cells_castCover remaining
        (PreparedCoveredParentLists.CoveredParents.append_nil lastCovered).symm channel
  | _ :: _, _, .cons patch inside covered, lastCovered, prepared, remaining => by
      let joined : PreparedParents (CoveredParents.cons patch inside
          (PreparedCoveredParentLists.CoveredParents.append covered lastCovered)) floor targets :=
        ⟨prepared.1, append covered lastCovered prepared.2 remaining⟩
      have factory := congrArg (fun value => cells value channel)
        (append_cons patch inside covered lastCovered prepared.1 prepared.2 remaining)
      have transported := cells_castCover joined
        (PreparedCoveredParentLists.CoveredParents.append_cons patch inside covered lastCovered).symm channel
      have head := cells_cons patch inside
        (PreparedCoveredParentLists.CoveredParents.append covered lastCovered)
        prepared.1 (append covered lastCovered prepared.2 remaining) channel
      have tail := congrArg (List.cons (prepared.1.preparation.cell.models.cell channel))
        (cells_append channel covered lastCovered prepared.2 remaining)
      have original := congrArg (fun values => values ++ cells remaining channel)
        (cells_cons patch inside covered prepared.1 prepared.2 channel).symm
      exact factory.trans (transported.trans (head.trans (tail.trans original)))

/-- Join the identical retained source cells along the original centered-parent geometric path.

The dependent original list, covering spine and endpoint indices are
consumed together. Each step reads its existing complete Preparation.cell;
the same stored tail is passed to the recursive call without resampling.
-/
@[expose] def sources : {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (covered : CoveredParents count parents) → PreparedParents covered floor targets →
    {start finish : LiftedPoint 2} →
    (chain : CenteredPathChain parents (start := start) (finish := finish)) → Path parameter chain.path
  | [], .nil, _, _, _, .nil point => .nil point
  | _ :: _, .cons _ _ covered, prepared, _, _, .cons _ chain =>
      .cons prepared.1.preparation.cell (sources covered prepared.2 chain)

/-- The literal stored cell-list reader agrees with the SAME source path on its actual supplied centered chain. -/
theorem cells_eq_sources (channel : Fin 6) :
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (covered : CoveredParents count parents) → (prepared : PreparedParents covered floor targets) →
    {start finish : LiftedPoint 2} →
    (chain : CenteredPathChain parents (start := start) (finish := finish)) →
      cells (covered := covered) prepared channel = (sources covered prepared chain).cells channel
  | [], .nil, empty, _, _, .nil point => by
      cases empty
      rewrite [cells_nil]
      exact (Path.cells_nil point channel).symm
  | _ :: _, .cons patch inside covered, prepared, _, _, .cons _ chain =>
      (cells_cons patch inside covered prepared.1 prepared.2 channel).trans
        ((congrArg (List.cons (prepared.1.preparation.cell.models.cell channel))
          (cells_eq_sources channel covered prepared.2 chain)).trans
            (Path.cells_cons prepared.1.preparation.cell (sources covered prepared.2 chain) channel).symm)
termination_by structural _ covered _ _ _ _ => covered

/-- Exact target-index transport preserves the entire original ordered source chain.

Both sides consume the same preparation product and unchanged centered
chain. The equality identifies complete original source records, including
all selected requests and polynomial caches, without replaying their factories.
-/
theorem sources_castTargets {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count parents) {replacement : CellEndpoints.Targets original stage}
    (prepared : PreparedParents covered floor targets) (equal : targets = replacement)
    {start finish : LiftedPoint 2} (chain : CenteredPathChain parents (start := start) (finish := finish)) :
    sources covered (prepared.castTargets equal) chain = sources covered prepared chain := by
  cases equal
  rfl

/-- The original empty centered path contributes no source cells or endpoint requests. -/
theorem sources_nil (point : LiftedPoint 2) :
    sources (targets := targets) (floor := floor) (CoveredParents.nil (count := count)) PUnit.unit
      (CenteredPathChain.nil (curve := Fibre.frameCurve frame) (differential := basis) point) = Path.nil point := by rfl

/-- A joined source retains the exact original head cell and complete unchanged covered tail. -/
theorem sources_cons {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (patch : PreparedPatch parent) (inside : (patch.neighborhood count).box.Contains (parent.edge.point 1))
    (covered : CoveredParents count parents) (head : PreparedParent patch count floor inside targets)
    (remaining : PreparedParents covered floor targets) {finish : LiftedPoint 2}
    (chain : CenteredPathChain parents (start := PreparedParent.finishPoint parent) (finish := finish)) :
    sources (CoveredParents.cons patch inside covered) ⟨head, remaining⟩ (CenteredPathChain.cons parent chain) =
      Path.cons head.preparation.cell (sources covered remaining chain) := by rfl

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

end
