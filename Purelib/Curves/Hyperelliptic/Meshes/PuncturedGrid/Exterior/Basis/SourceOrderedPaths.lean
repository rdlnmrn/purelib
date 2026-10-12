module
import Purelib.Data.List.Reverse
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.OfFn.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedParentOrder
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedReverseOrder
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
public import Purelib.Integration.Path.PairedAreaReversal
import Purelib.Integration.Path.PairedReverseBlocks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedRuns
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches

public section
/-! Retain the complete physical word when indexing groups in source order. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedPaths

open Purelib.Curves
open Purelib.Integration
open Purelib
open Purelib.Riemann

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {program : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram lifted differential} {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
    regular domains program}

variable (retained : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation prepared)
  {index : Nat} (inputs : retained.Inputs index)
  (outer : Fin prepared.occurrences.length) {faceIndex : Nat}
  (data : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.RowData
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences outer) faceIndex)
  (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)

variable {retained inputs outer data coefficients}

/-- Flattening each retained run before concatenating yields the same complete physical path as flattening the original
fragment pairs first. -/
private theorem physical_flatten (runs : List
  (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedRun retained inputs outer data
  coefficients)) :
    (runs.map (fun run => ((run.fragments.map
      Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.pair).map
      Prod.fst).flatten)).flatten =
      (((runs.map (fun run => run.fragments.map
        OwnedFragments.OwnedFragment.pair)).flatten).map
        Prod.fst).flatten := by
  induction runs with
  | nil => rfl
  | cons first rest ih =>
    simp only [List.map_cons, List.flatten_cons, Data.List.Map.map_append, Data.List.Flatten.flatten_append, ih,
      -eq_self, -iff_self]
    rfl

namespace IndexedGrouping
variable {items : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.IndexedFragment retained
  inputs outer data coefficients)}

/-- Reading every source position preserves the full forward physical word. -/
theorem source_order_physical (grouped :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedGrouping retained inputs outer data
  coefficients items)
    (word : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedParentOrder.IndexedFragment.ParentWord items) :
    (List.ofFn (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedRuns.IndexedGrouping.inSourceOrder
      grouped word).physical).flatten =
      ((items.map Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.IndexedFragment.pair).map
        Prod.fst).flatten := by
  rw [(Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedRuns.IndexedGrouping.inSourceOrder grouped
    word).physical_all]
  exact (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedPaths.physical_flatten grouped.runs).trans
    (congrArg (fun pairs => (pairs.map Prod.fst).flatten) grouped.pairs_eq)

/-- Source order reverses both the descending group list and the path inside
each group; all cross-parent joins remain part of the complete reversed word. -/
theorem reverse_source_order_physical (grouped :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping.IndexedGrouping retained inputs outer data
  coefficients items)
    (word : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.GroupedReverseOrder.IndexedFragment.ReverseParentWord
      items) :
    (List.ofFn (fun position => Path.PairedAreaReversal.reverseIncrements
      ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedRuns.IndexedGrouping.reverseInSourceOrder grouped
        word).physical position))).flatten =
      Path.PairedAreaReversal.reverseIncrements ((items.map
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments.IndexedFragment.pair).map Prod.fst).flatten
        := by
  have entries := congrArg (fun paths : List (List Topology.Polygon.Stokes.PrimitivePoint) =>
    (paths.map Path.PairedAreaReversal.reverseIncrements).flatten)
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedRuns.IndexedGrouping.reverseInSourceOrder grouped
      word).physical_all
  rw [Data.List.OfFn.Basic.map_ofFn] at entries
  apply entries.trans
  change ((grouped.runs.reverse.map (fun run =>
    ((run.fragments.map Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.pair).map
      Prod.fst).flatten)).map
      Path.PairedAreaReversal.reverseIncrements).flatten = _
  rw [Data.List.Reverse.map_reverse, ← Path.PairedAreaReversal.reverseIncrements_flatten]
  exact congrArg Path.PairedAreaReversal.reverseIncrements
    ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedPaths.physical_flatten grouped.runs).trans
      (congrArg (fun pairs => (pairs.map Prod.fst).flatten) grouped.pairs_eq))

end IndexedGrouping
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedPaths
