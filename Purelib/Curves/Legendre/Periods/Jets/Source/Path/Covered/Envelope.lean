module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered
public import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Joint.Bounds.Envelope
import Purelib.Data.Rat.List.Maximum
import Purelib.Data.List.OfFn.Basic

/-! # One envelope ceiling from the same original prepared source caches

The finite table reads actual retained Cell.patch caches in original parent
order. Their complete Cell factory equations identify the original covering
neighborhoods. The same scalar maximum therefore works at every Targets
stage on this fixed covered family, without growing a neighborhood again.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data
open Purelib.Data.List (DependentProduct)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Step (Joint)

namespace PreparedParent

/-- The actual retained source Cell has exactly its original covering neighborhood's physical box. -/
theorem queryBox_eq {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count floor : Nat}
    {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage} (prepared : PreparedParent patch count floor covered targets) :
    prepared.preparation.cell.patch.box = (patch.neighborhood count).box :=
  congrArg (fun cell : Cell (parameter := parameter) (liftedCell parent) => cell.patch.box)
    prepared.preparation.cell_eq

/-- The envelope computation reads the exact original neighborhood retained by this source Cell's whole factory. -/
theorem envelopeCeiling_eq {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count floor : Nat}
    {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage} (prepared : PreparedParent patch count floor covered targets) :
    Joint.shiftedEnvelopeCeiling (parameter := parameter) prepared.preparation.cell.patch =
      Joint.shiftedEnvelopeCeiling (parameter := parameter) (patch.neighborhood count) :=
  congrArg (fun cell : Cell (parameter := parameter) (liftedCell parent) =>
    Joint.shiftedEnvelopeCeiling (parameter := parameter) cell.patch) prepared.preparation.cell_eq

end PreparedParent

namespace PreparedParents

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {count : Nat} {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count parents} {floor : Nat}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}

/-- Cache the identity ancestral-box assignment from every original source's retained endpoint memberships.

The existing dependent product stores the same original occurrence index
and both endpoint proofs in its original covering box, identified with
the actual retained Cell.patch.box by its whole factory. It neither grows a
neighborhood nor replaces the source Cell or its original geometry.
-/
def initialEndpoints (prepared : PreparedParents covered floor targets) :
    DependentProduct parents (fun index =>
      { ancestor : Fin parents.length //
        ((covered.entry ancestor).val.neighborhood count).box.Contains
            (PreparedParent.startPoint (parents[index.val]'index.isLt)).coordinate ∧
          ((covered.entry ancestor).val.neighborhood count).box.Contains
            (PreparedParent.finishPoint (parents[index.val]'index.isLt)).coordinate }) :=
  DependentProduct.ofFn parents (fun index =>
    ⟨index, Eq.mp (congrArg (fun box => box.Contains
        (PreparedParent.startPoint (parents[index.val]'index.isLt)).coordinate)
      (prepared.entry index).queryBox_eq) (prepared.entry index).preparation.cell.startInside,
      Eq.mp (congrArg (fun box => box.Contains
        (PreparedParent.finishPoint (parents[index.val]'index.isLt)).coordinate)
      (prepared.entry index).queryBox_eq) (prepared.entry index).preparation.cell.finishInside⟩)

/-- The identity ancestry product retains the exact original index and both whole endpoint transport proofs. -/
theorem initialEndpoints_entry (prepared : PreparedParents covered floor targets) (index : Fin parents.length) :
    DependentProduct.get parents prepared.initialEndpoints index =
      ⟨index, Eq.mp (congrArg (fun box => box.Contains
          (PreparedParent.startPoint (parents[index.val]'index.isLt)).coordinate)
        (prepared.entry index).queryBox_eq) (prepared.entry index).preparation.cell.startInside,
        Eq.mp (congrArg (fun box => box.Contains
          (PreparedParent.finishPoint (parents[index.val]'index.isLt)).coordinate)
        (prepared.entry index).queryBox_eq) (prepared.entry index).preparation.cell.finishInside⟩ :=
  DependentProduct.get_ofFn parents _ index

/-- Compute one finite maximum from the actual original neighborhood caches in the retained preparation product.

The table contains only scalar computations on existing Cell.patch values.
Its original parent occurrence order is preserved; no source, neighborhood,
query, Targets, root sample or signed owner is constructed or substituted.
-/
def envelopeCeiling (prepared : PreparedParents covered floor targets) : Rational :=
  let values := List.ofFn (fun index : Fin parents.length =>
    Joint.shiftedEnvelopeCeiling (parameter := parameter) (prepared.entry index).preparation.cell.patch)
  Rat.List.Maximum.nonnegativeMaximum values

/-- The retained preparation's computed finite envelope scale is nonnegative, including the empty parent list. -/
theorem envelopeCeiling_nonnegative (prepared : PreparedParents covered floor targets) :
    0 ≤ prepared.envelopeCeiling := Rat.List.Maximum.nonnegativeMaximum_nonneg _

/-- Every exact original covering occurrence is bounded by the maximum computed from the same retained source caches. -/
theorem entry_envelopeCeiling_le (prepared : PreparedParents covered floor targets) (index : Fin parents.length) :
    Joint.shiftedEnvelopeCeiling (parameter := parameter) ((covered.entry index).val.neighborhood count) ≤
      prepared.envelopeCeiling := by
  have member : Joint.shiftedEnvelopeCeiling (parameter := parameter) (prepared.entry index).preparation.cell.patch ∈
      List.ofFn (fun selected : Fin parents.length =>
        Joint.shiftedEnvelopeCeiling (parameter := parameter) (prepared.entry selected).preparation.cell.patch) :=
    List.OfFn.Basic.mem_ofFn.mpr ⟨index, rfl⟩
  exact (prepared.entry index).envelopeCeiling_eq.symm.trans_le
    (Rat.List.Maximum.le_nonnegativeMaximum_of_mem member)

/-- Changing Targets stages on the same original covered family preserves the complete computed envelope ceiling.

Both retained preparation products remain distinct inputs with their own
observations and requests. Their original Cell factory equations identify
only these scalar computations on the same covering neighborhoods.
-/
theorem envelopeCeiling_eq (first : PreparedParents covered floor targets)
    {lastStart lastFinish : LiftedPoint 2} {lastPath : LiftedPath 2 lastStart lastFinish}
    {lastStage lastFloor : Nat} {lastTargets : CellEndpoints.Targets lastPath lastStage}
    (last : PreparedParents covered lastFloor lastTargets) : first.envelopeCeiling = last.envelopeCeiling := by
  have table := List.OfFn.Basic.ofFn_congr (fun index : Fin parents.length =>
    (first.entry index).envelopeCeiling_eq.trans (last.entry index).envelopeCeiling_eq.symm)
  exact congrArg Rat.List.Maximum.nonnegativeMaximum table

end PreparedParents

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell

end
