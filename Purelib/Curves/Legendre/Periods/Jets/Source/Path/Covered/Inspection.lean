module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered
public import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.Coverage
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Normalization.ContinuedInverseRoot

/-! # Original sources on the same actually inspected primitive neighborhoods

Successful coverage keeps the original patch at each parent occurrence.
The actual neighborhood remains the checker input to source preparation,
with a whole factory proof to the same nominal patch. No neighborhood,
root owner or inspection is replayed. The original source branch builds
each actual six-channel cache once on that GIVEN neighborhood.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List (DependentProduct)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}

/-- Prepare every original source once using its SAME inspected neighborhood and actual successful coverage.

The covering patch's exact occurrence identity and the stored whole
neighborhood factory derive its original nominal index. The shared
fromNeighborhood constructor runs on the GIVEN cached neighborhood;
only the completed source tuple is transported afterward. Existing
targets, stages, endpoint roles and all six requests remain unchanged.
-/
def fromInspection (inspected : CoveredParents.Inspection (count := count) parents)
    (covered : CoveredParents.Inspection.Success inspected) (floor : Nat)
    (targets : CellEndpoints.Targets original stage) : PreparedParents covered.val floor targets :=
  DependentProduct.ofFn parents (fun index =>
    let coveredEntry := covered.val.entry index
    let selected := inspected.entry index
    have patchEq : coveredEntry.val = selected.patch := CoveredParents.Inspection.Success.entry covered index
    have factory : selected.neighborhood = coveredEntry.val.neighborhood count :=
      selected.neighborhood_eq.trans
        (congrArg (fun patch : PreparedPatch (parents[index.val]'index.isLt) => patch.neighborhood count) patchEq.symm)
    PreparedParent.fromNeighborhood coveredEntry.val count floor selected.neighborhood factory
      coveredEntry.property targets)

/-- Every stored preparation is the original shared constructor on that occurrence's SAME inspected neighborhood. -/
theorem fromInspection_entry (inspected : CoveredParents.Inspection (count := count) parents)
    (covered : CoveredParents.Inspection.Success inspected) (floor : Nat)
    (targets : CellEndpoints.Targets original stage) (index : Fin parents.length) :
    (fromInspection inspected covered floor targets).entry index =
      let coveredEntry := covered.val.entry index
      let selected := inspected.entry index
      have patchEq : coveredEntry.val = selected.patch := CoveredParents.Inspection.Success.entry covered index
      have factory : selected.neighborhood = coveredEntry.val.neighborhood count :=
        selected.neighborhood_eq.trans
          (congrArg (fun patch : PreparedPatch (parents[index.val]'index.isLt) =>
            patch.neighborhood count) patchEq.symm)
      PreparedParent.fromNeighborhood coveredEntry.val count floor selected.neighborhood factory
        coveredEntry.property targets :=
  DependentProduct.get_ofFn parents (fun index =>
    let coveredEntry := covered.val.entry index
    let selected := inspected.entry index
    have patchEq : coveredEntry.val = selected.patch := CoveredParents.Inspection.Success.entry covered index
    have factory : selected.neighborhood = coveredEntry.val.neighborhood count :=
      selected.neighborhood_eq.trans
        (congrArg (fun patch : PreparedPatch (parents[index.val]'index.isLt) => patch.neighborhood count) patchEq.symm)
    PreparedParent.fromNeighborhood coveredEntry.val count floor selected.neighborhood factory
      coveredEntry.property targets) index

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

end
