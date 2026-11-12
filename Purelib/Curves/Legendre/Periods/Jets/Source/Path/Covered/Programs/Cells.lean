module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Programs.Variation
public import Purelib.Integration.Polynomial.Gaussian.Path.Basic.Variation
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Cells
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Data.Gaussian.Basic
import Purelib.Algebra.FiniteSum.Fin

/-! # Physical displacement and variation of the same prepared source cells

Each original six-channel model retains the identical centered parent's
physical endpoints. Exact bounded cell-list readbacks transport this
scalar geometry to the same finite source path at any actual allocation.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell

open Purelib
open Purelib.Algebra.FiniteSum.Fin (sumFin_congr)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

namespace PreparedParent

/-- Every original prepared channel retains the exact scalar physical parent displacement. -/
theorem cell_displacement
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count floor : Nat}
    {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    (prepared : PreparedParent patch count floor covered targets) (channel : Fin 6) :
    (prepared.preparation.cell.models.cell channel).displacement =
      (finishPoint parent).coordinate - (startPoint parent).coordinate := by
  rewrite [prepared.preparation.cell_eq]
  change (prepared.preparation.models.cell channel).finish - (prepared.preparation.models.cell channel).start = _
  exact congrArg₂ (fun finish start : Canonical => finish - start)
    (prepared.preparation.models.cell_finish channel) (prepared.preparation.models.cell_start channel)

end PreparedParent

namespace PreparedParents

/-- The same original source-list variation equals the physical parent variation at every actual preparation stage. -/
theorem variation_sources
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count floor : Nat}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    (covered : CoveredParents count parents) (prepared : PreparedParents covered floor targets)
    {start finish : LiftedPoint 2} (chain : CenteredPathChain parents (start := start) (finish := finish))
    (channel : Fin 6) :
    (PathModel.mk ((sources covered prepared chain).cells channel)).variation = variation parents :=
  (congrArg (fun cells => (PathModel.mk cells).variation)
    (cells_eq_ofFn covered prepared chain channel)).trans
      ((PathModel.variation_ofFn (fun index => (prepared.entry index).preparation.cell.models.cell channel)).trans
        (sumFin_congr (fun index => congrArg Norm.Components.maximum
          ((prepared.entry index).cell_displacement channel))))

end PreparedParents

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell

end
