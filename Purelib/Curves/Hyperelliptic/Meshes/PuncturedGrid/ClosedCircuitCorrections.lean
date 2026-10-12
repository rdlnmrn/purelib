module
import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.GeneratorValuation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.RowCircuitOrder
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ValuationAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchFaceCorrections
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree

public section

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchFaceCorrections.CircuitPartition
open Purelib.Integration.Path
open Purelib.Polynomial.Geometry.Grid
open Purelib.Riemann.Meshes
open Purelib.RootIsolation.SquareRoot.Grid
open Purelib.RootIsolation.SquareRoot.Grid.EdgeBank
open Purelib.Topology.Mesh
open Purelib.Topology.Mesh.RetracingWords
open Purelib.Topology.Polygon
open Purelib.Topology.Surface.Sewing

/-! Closed test valuations remove cross corrections while retaining every regular polygon area. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ClosedCircuitCorrections.CircuitPartition

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Mesh.RetracingWords (wordArea AreaTerm)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue faceValue)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank (CircuitPartition)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition
  (RegularOccurrence Compiled)
open Purelib.Integration.Path.IncrementArea (area_zero_left area_zero_right)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {faces : PuncturedFaces bank} {frames :
    RootIsolation.SquareRoot.Grid.RootFrames bank.grid}
  {vertices : Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {base : Canonical}

/-- The zero is obtained from the two located original mesh faces. -/
theorem RegularOccurrence.value_zero (occurrence : CircuitPartition.RegularOccurrence faces vertices edges)
    (mesh : GridLiftedMesh.LiftedMesh vertices edges faces) (value : Stokes.OrientedEdge vertices.count →
      Data.Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge)
    (closed : ∀ index, SewingRetraction.wordValue value (mesh.triangulation.faces index).boundary = 0) :
    SewingRetraction.wordValue value occurrence.word = 0 := by
  let correction := RegularOccurrence.faceCorrection occurrence mesh
  rw [correction.values value anti, correction.terms_eq]
  change (1 : Data.Gaussian.Basic.Canonical) * SewingRetraction.wordValue value (mesh.triangulation.faces
    correction.located.occurrence.first).boundary +
    ((1 : Data.Gaussian.Basic.Canonical) * SewingRetraction.wordValue value (mesh.triangulation.faces
      correction.located.occurrence.second).boundary + 0) = 0
  rw [closed, closed]
  simp only [mul_zero, add_zero, -eq_self, -iff_self]
  rfl

/-- If every original regular occurrence has zero total valuation, their retained compiled regular word also has zero
total. -/
theorem Compiled.regularWord_zero {tree : RowCircuitOrder.CellCircuits bank.grid base} {partition :
  BranchCellBank.CircuitPartition faces tree}
    {sheet : Fin 2} (compiled : CircuitPartition.Compiled partition edges vertices sheet)
    (value : Stokes.OrientedEdge vertices.count → Data.Gaussian.Basic.Canonical)
    (closed : ∀ occurrence : CircuitPartition.RegularOccurrence faces vertices edges, SewingRetraction.wordValue value
      occurrence.word = 0) :
    SewingRetraction.wordValue value compiled.regularWord = 0 := by
  rw [compiled.regularWord_values]
  have zero (items : List (CircuitPartition.RegularOccurrence faces vertices edges)) :
      CellBoundary.sumValues (fun occurrence => SewingRetraction.wordValue value occurrence.word) items = 0 := by
    induction items with
    | nil => rfl
    | cons occurrence rest ih => exact (congrArg₂ (· + ·) (closed occurrence) ih).trans (add_zero _)
  exact zero compiled.regulars

/-- The canonical compiler retains exactly the regular areas after the cross terms vanish. -/
theorem compile_area_closed {tree : RowCircuitOrder.CellCircuits bank.grid base} (partition :
  BranchCellBank.CircuitPartition faces tree)
    (edges : RootEdgeBank frames) (vertices : LiftedVertices.VertexBank bank.grid)
    (value : Stokes.OrientedEdge vertices.count → Data.Gaussian.Basic.Canonical)
    (closed : ∀ occurrence : CircuitPartition.RegularOccurrence faces vertices edges, SewingRetraction.wordValue value
      occurrence.word = 0)
    (sheet : Fin 2) :
    AreaTerm.total value (partition.compile edges vertices sheet).areaTerms =
      CellBoundary.sumValues (fun occurrence => RetracingWords.wordArea value occurrence.word) (partition.compile edges
        vertices sheet).regulars := by
  induction partition generalizing sheet with
  | nil => rfl
  | @regular cell member stem location =>
      let word := edges.indexedEdges vertices (CellBoundary.Cell.boundaryWalk cell member) (RootEdgeBank.target edges
        stem sheet)
      have zero := closed ⟨cell, member, location, RootEdgeBank.target edges stem sheet, word, rfl⟩
      change SewingRetraction.wordValue value word = 0 at zero
      change RetracingWords.wordArea value word + (2 * BoundaryRibbon.area
        (SewingRetraction.wordValue value (edges.indexedEdges vertices stem sheet)) (SewingRetraction.wordValue value
          word) + 0) = RetracingWords.wordArea value word + 0
      rw [zero, IncrementArea.area_zero_right, mul_zero, add_zero]
  | hole => rfl
  | append first last ihFirst ihLast =>
      let initial := first.compile edges vertices sheet
      let final := last.compile edges vertices initial.finish
      change AreaTerm.total value (initial.areaTerms ++ final.areaTerms ++
        [.cross 1 initial.word final.regularWord, .cross 1 initial.regularWord final.word,
          .cross 1 initial.regularWord final.regularWord]) =
        CellBoundary.sumValues (fun occurrence => RetracingWords.wordArea value occurrence.word) (initial.regulars ++
          final.regulars)
      rw [AreaTerm.total_append, AreaTerm.total_append, CellBoundary.sumValues_append]
      have firstZero :=
        Curves.Hyperelliptic.Meshes.PuncturedGrid.ClosedCircuitCorrections.CircuitPartition.Compiled.regularWord_zero
        initial value closed
      have lastZero :=
        Curves.Hyperelliptic.Meshes.PuncturedGrid.ClosedCircuitCorrections.CircuitPartition.Compiled.regularWord_zero
        final value closed
      simp only [AreaTerm.total, AreaTerm.evaluate, firstZero, lastZero,
        IncrementArea.area_zero_left, IncrementArea.area_zero_right, mul_zero, add_zero, -eq_self, -iff_self]
      exact congrArg₂ (· + ·) (ihFirst sheet) (ihLast initial.finish)

/-- The compiler's existing area certificate identifies its correction value with the canonical compilation. -/
theorem Compiled.areaTerms_eq_compile {tree : RowCircuitOrder.CellCircuits bank.grid base}
    {partition : BranchCellBank.CircuitPartition faces tree} {sheet : Fin 2}
    (compiled : CircuitPartition.Compiled partition edges vertices sheet)
    (value : Stokes.OrientedEdge vertices.count → Data.Gaussian.Basic.Canonical) (anti : ∀ edge, value edge.reverse =
      -value edge) :
    AreaTerm.total value compiled.areaTerms = AreaTerm.total value (partition.compile edges vertices sheet).areaTerms :=
      by
  have equal := (compiled.areas value anti).symm.trans ((partition.compile edges vertices sheet).areas value anti)
  have words := compiled.word_eq.trans (partition.compile edges vertices sheet).word_eq.symm
  rw [words] at equal
  exact add_left_cancel equal

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ClosedCircuitCorrections.CircuitPartition

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ClosedCircuitCorrections.GeneratorValuation
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
open Purelib.Polynomial.Geometry.Grid

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Mesh.RetracingWords (wordArea AreaTerm)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut (GeneratorValuation)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank (CircuitPartition)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition (Compiled)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base}
  {values : Data.Vector Canonical
    lifted.cutBoundaryWord.alphabet.count}
  (data : Cut.GeneratorValuation lifted values)

/-- Every cross correction is discharged on the same actual closed valuation; regular areas remain. -/
theorem regular_correction_areas {start : Data.Gaussian.Basic.Canonical} {tree : RowCircuitOrder.CellCircuits
  base.bank.grid start}
    {partition : BranchCellBank.CircuitPartition base.faces tree} {sheet : Fin 2}
    (compiled : CircuitPartition.Compiled partition lifted.edges lifted.vertices sheet) :
    AreaTerm.total data.value compiled.areaTerms =
      CellBoundary.sumValues (fun occurrence => RetracingWords.wordArea data.value occurrence.word)
        (partition.compile lifted.edges lifted.vertices sheet).regulars :=
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.ClosedCircuitCorrections.CircuitPartition.Compiled.areaTerms_eq_compile
    compiled data.value data.value_reverse).trans
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.ClosedCircuitCorrections.CircuitPartition.compile_area_closed partition
      lifted.edges lifted.vertices data.value
      (fun occurrence =>
        Curves.Hyperelliptic.Meshes.PuncturedGrid.ClosedCircuitCorrections.CircuitPartition.RegularOccurrence.value_zero
        occurrence lifted.mesh data.value data.value_reverse data.face_zero) sheet)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ClosedCircuitCorrections.GeneratorValuation
