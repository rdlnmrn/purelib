module
import Purelib.Data.List.Membership
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.Map
import Purelib.Data.Vector.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.GeneratorValuation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ValuationAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedSheetReplay
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Tactic.Ring
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ClosedBranchExcursions

open Purelib.Curves

open Purelib.Data

open Purelib

open Purelib.Riemann

public section

/-! Physical ending terms and full excursion cancellation for the retained paired programs. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Topology.Polygon.Stokes

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin 2}
  {values : Data.Vector Gaussian.Basic.Canonical lifted.cutBoundaryWord.alphabet.count}
  (data : Cut.GeneratorValuation lifted values)

namespace OrderedBranchPairs.EndingTours

/-- A closed total original ending word has zero exterior area correction. -/
theorem exteriorArea_zero {ending : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.PairEnding
  (Hyperelliptic.Branches.BranchIsolation.Data.Index branches)}
    (tours : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.EndingTours bank sheet ending) (value :
      Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) (total :
      Gaussian.Basic.Canonical)
    (closed : total + Topology.Surface.Sewing.SewingRetraction.wordValue value tours.word = 0) : tours.exteriorArea
      value total = 0 := open Purelib.Integration in by
  cases tours with
  | odd => rfl
  | even index last reference terminal =>
      change Path.BoundaryRibbon.area (Topology.Surface.Sewing.SewingRetraction.wordValue value terminal.outward.indexed
        + total) (total + Topology.Surface.Sewing.SewingRetraction.wordValue value terminal.closed.indexed) = 0
      exact (congrArg (Path.BoundaryRibbon.area (Topology.Surface.Sewing.SewingRetraction.wordValue value
        terminal.outward.indexed + total)) closed).trans
        (Path.IncrementArea.area_zero_right _)

/-- The original ending excursion area changes sign on the opposite retained sheet. -/
theorem internalArea_other {ending : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.PairEnding
  (Hyperelliptic.Branches.BranchIsolation.Data.Index branches)}
    (tours : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.EndingTours bank sheet ending)
    (other : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.EndingTours bank
      (Hyperelliptic.Branches.BranchCutLifts.otherSheet sheet) ending) :
    other.internalArea data.value = -tours.internalArea data.value := by
  cases tours with
  | odd index reference =>
      cases other with
      | odd _ otherReference =>
          change Topology.Mesh.RetracingWords.wordArea data.value otherReference.outward.indexed =
            -Topology.Mesh.RetracingWords.wordArea data.value reference.outward.indexed
          rw [otherReference.outward_eq, reference.outward_eq]
          exact data.loop_area_other bank index sheet
  | even index last reference terminal =>
      cases other with
      | even _ _ otherReference otherTerminal =>
          change Topology.Mesh.RetracingWords.wordArea data.value otherTerminal.outward.indexed +
            Topology.Mesh.RetracingWords.wordArea data.value otherTerminal.returning.indexed =
            -(Topology.Mesh.RetracingWords.wordArea data.value terminal.outward.indexed +
              Topology.Mesh.RetracingWords.wordArea data.value terminal.returning.indexed)
          rw [otherTerminal.outward_eq, otherTerminal.returning_indexed, terminal.outward_eq,
            terminal.returning_indexed,
            data.loop_area_other bank index sheet, data.loop_area_other bank last
              (Hyperelliptic.Branches.BranchCutLifts.otherSheet sheet)]
          ring1

end OrderedBranchPairs.EndingTours
section Ordered
variable (ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank
  sheet)

/-- The actual regular-face correction has zero reading under the retained generator valuation. -/
private theorem OrderedBranchPairs.Ordered.faceValue_zero (terms : List
  (Topology.Surface.Sewing.SewingRetraction.FaceTerm
  lifted.mesh.triangles.length)) :
    Topology.Surface.Sewing.SewingRetraction.faceValue lifted.mesh.triangulation.faces data.value terms = 0 := by
  induction terms with
  | nil => rfl
  | cons term rest ih =>
      change (term.1 : Gaussian.Basic.Canonical) * Topology.Surface.Sewing.SewingRetraction.wordValue data.value
        (lifted.mesh.triangulation.faces term.2).boundary + _ = 0
      rw [data.face_zero, mul_zero, ih, zero_add]

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered in
/-- The actual exterior word is zero after paying its exact regular-face correction. -/
theorem
  BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered.word_value_zero
  :
    Topology.Surface.Sewing.SewingRetraction.wordValue data.value ordered.word = 0 := by
  have equal := ordered.exterior_values data.value data.value_reverse
  rw [Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.faceValue_zero data, add_zero] at equal
  exact equal.symm.trans (Hyperelliptic.Meshes.PuncturedGrid.Cut.ValuationAreas.exterior_value_zero data sheet)

namespace OrderedBranchPairs.Ordered.Paired
variable {ordered} (paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered)

/-- This removes the even ending term using the whole ordered word, not just a reference period. -/
theorem ending_exterior_zero : paired.ending.exteriorArea data.value (Topology.Surface.Sewing.SewingRetraction.wordValue
  data.value paired.rows.word) = 0 := by
  apply paired.ending.exteriorArea_zero
  rw [← Topology.Surface.Sewing.SewingRetraction.wordValue_append, ← paired.branch_word]
  exact ordered.word_value_zero data

/-- Only internal excursion areas and the actual regular correction remain. -/
theorem area_closed : paired.rows.correctedArea data.value =
    paired.rows.internalArea data.value + paired.ending.internalArea data.value +
      Topology.Mesh.RetracingWords.AreaTerm.total data.value ordered.prepared.compiled.areaTerms := open
        Purelib.Integration in by
  have equal := paired.area_formula data.value data.value_reverse
  have retained : paired.reference.hole ∈ base.faces.holes := by
    rw [← paired.reference.indexed]
    exact List.getElem_mem paired.reference.index.isLt
  have boundaryMember : paired.reference.hole.liftedBoundary lifted.vertices lifted.edges ∈ lifted.boundaryLoops :=
    Data.List.Membership.mem_append.mpr (Or.inr (Data.List.Map.mem_map_of_mem retained))
  have exterior := Hyperelliptic.Meshes.PuncturedGrid.Cut.ValuationAreas.exterior_area_zero data sheet
  change lifted.edges.chainArea lifted.vertices data.value base.bank.exterior sheet = 0 at exterior
  rw [exterior, zero_add, data.boundary_zero _ boundaryMember, neg_zero, Path.IncrementArea.area_zero_right,
    paired.ending_exterior_zero data, add_zero, add_zero] at equal
  exact equal

end OrderedBranchPairs.Ordered.Paired
end Ordered
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
