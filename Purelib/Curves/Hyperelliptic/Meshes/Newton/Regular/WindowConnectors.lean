module
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.PeriodMatrix
public import Purelib.Riemann.RootContinuation.NewtonOriginalRegularFaces
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.WindowCircuits
import Purelib.RootIsolation.SquareRoot.Grid.Subdivision.Self
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedConnectors
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.RootIsolation.SquareRoot.Grid.Inclusion.CellPolygon

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

open Purelib.Riemann

open Purelib

public section

/-! Requested connector decay for the fine circuit inside an original
regular cell, retaining the actual arriving sheets and every cell polygon. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.WindowConnectors

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition
open Purelib.Riemann.Periods
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target radius :
    Fraction.Rational}
  {grid : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius} {face :
    Meshes.PuncturedGridFaces.RegularFace original}
  {current : Meshes.LiftedPuncturedGrid grid.punctured}

/-- The existing fine-window order supplies the partition; the named owner
keeps the dependent compiler signatures small. -/
@[expose] def fineOrder (region : RootContinuation.NewtonOriginalRegularFaces.OriginalRegularFaces grid face) (sheet :
  Fin 2) :=
  Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.Window.prepareBranches grid.faces region.window current.edges
    current.vertices sheet

/-- Compile the original fine window circuits using their identity coordinate inclusion.

The compiler retains the current edges and vertices, original face anchor and branch partition, and the reference
readings of that same grid. -/
@[expose] def fineCompiler (region : RootContinuation.NewtonOriginalRegularFaces.OriginalRegularFaces grid face) (sheet
  : Fin 2) :
    Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitCompiled
      (Geometry.Grid.Extension.CoordinateInclusion.refl grid.punctured.bank.grid) current.edges current.vertices
      (grid.shrunk.included.vertex (face.cell.anchor_mem face.member))
      (Hyperelliptic.Meshes.Newton.Regular.WindowConnectors.fineOrder (current := current) region sheet).partition sheet
        :=
  Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.compileResplit _
    current.edges current.vertices
    (fun point member => (Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt
      grid.punctured.bank.toBranchCellBank point member).toLoop) _
    (Hyperelliptic.Meshes.Newton.Regular.WindowConnectors.fineOrder (current := current) region sheet).partition sheet

/-- The self-subdivision compiler represents the very same original-cell
polygon. No new branch area is introduced by the compiler adapter. -/
theorem fineCompiler_area (region : RootContinuation.NewtonOriginalRegularFaces.OriginalRegularFaces grid face) (sheet :
  Fin 2)
    (value : Topology.Polygon.Stokes.OrientedEdge current.vertices.count → Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    current.edges.chainArea current.vertices value
      (grid.shrunk.included.resplit face.boundary (face.cell.anchor_mem face.member)) sheet =
      Topology.Mesh.RetracingWords.AreaTerm.total value
        (Hyperelliptic.Meshes.Newton.Regular.WindowConnectors.fineCompiler (current := current) region sheet).areaTerms
        := by
  let order := Hyperelliptic.Meshes.Newton.Regular.WindowConnectors.fineOrder (current := current) region sheet
  let compiled := Hyperelliptic.Meshes.Newton.Regular.WindowConnectors.fineCompiler (current := current) region sheet
  let reference := fun point member => (Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt
    grid.punctured.bank.toBranchCellBank point member).toLoop
  have boundary := grid.shrunk.included.cell_boundary_comparison face.cell face.member region.window
    current.edges current.vertices reference
  have ordered := order.ordered.comparison.areas value anti sheet
  rw [order.ordered.product_eq] at ordered
  have self := Polynomial.Geometry.Grid.ClearGrid.self_resplit_comparison current.edges current.vertices reference
    order.ordered.tree.product
    (grid.shrunk.included.vertex (face.cell.anchor_mem face.member))
  have word : compiled.word = [] := by
    exact compiled.word_eq.trans (congrArg (fun walk => current.edges.indexedEdges current.vertices
      ((Geometry.Grid.Extension.CoordinateInclusion.refl grid.punctured.bank.grid).resplit walk
        (grid.shrunk.included.vertex (face.cell.anchor_mem face.member))) sheet)
          (Hyperelliptic.Meshes.Newton.Regular.WindowCircuits.fine_kept_empty region order))
  have areas := compiled.areas value anti
  rw [word] at areas
  exact (boundary.areas value anti sheet).trans
    (ordered.symm.trans ((self.areas value anti sheet).symm.trans (areas.trans (zero_add _))))

variable {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank current.frames
  grid.faces.regulars} {i j : Fin genus}

/-- All connector requests are constructed from the two magnitude banks.
The actual fine-cell polygons remain; this is not their vanishing theorem. -/
theorem fine_polygons_accurate (region : RootContinuation.NewtonOriginalRegularFaces.OriginalRegularFaces grid face)
  (sheet : Fin 2)
    (first : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential i))
    (second : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential j))
    (error : Fraction.Rational) (positive : 0 < error) (floor : Nat) :
    let compiled := Hyperelliptic.Meshes.Newton.Regular.WindowConnectors.fineCompiler (current := current) region sheet
    let request := Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedConnectors.PolarizedConnectorRequest.build
      compiled current.mesh first second error positive floor
    let threshold := max floor request.index
    floor ≤ threshold ∧ ∀ stage (leftBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential i) stage domains)
      (rightBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
        (Periods.PeriodMatrix.standardDifferential j) stage domains)
      (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings leftBank current.mesh)
        (right : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings rightBank current.mesh),
      threshold ≤ stage →
      Data.Gaussian.Norm.Basic.normSq
        (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
        let value := Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix
          (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh left.values)
          (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh right.values) coefficient
        current.edges.chainArea current.vertices value
          (grid.shrunk.included.resplit face.boundary (face.cell.anchor_mem face.member)) sheet -
        Geometry.Grid.CellBoundary.sumValues (fun occurrence => Topology.Mesh.RetracingWords.wordArea value
          occurrence.word) compiled.regulars)) ≤ error := by
  intro compiled request threshold
  constructor
  · exact Nat.Order.le_max_left _ _
  intro stage leftBank rightBank left right later
  have equal (coefficient : Gaussian.Basic.Canonical) :
      let value := Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh left.values)
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh right.values) coefficient
      current.edges.chainArea current.vertices value
        (grid.shrunk.included.resplit face.boundary (face.cell.anchor_mem face.member)) sheet =
        Topology.Mesh.RetracingWords.AreaTerm.total value compiled.areaTerms := by
    intro value
    apply Hyperelliptic.Meshes.Newton.Regular.WindowConnectors.fineCompiler_area region sheet value
    exact Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix_reverse _ _
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation_reverse current.mesh left.values)
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation_reverse current.mesh right.values)
        coefficient
  have extracted := Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract_congr (fun
    coefficient =>
    congrArg (fun area => area - Geometry.Grid.CellBoundary.sumValues (fun occurrence =>
      Topology.Mesh.RetracingWords.wordArea
      (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh left.values)
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh right.values) coefficient)
          occurrence.word) compiled.regulars)
      (equal coefficient))
  exact (congrArg Data.Gaussian.Norm.Basic.normSq extracted).trans_le (request.accurate left right
    ((Nat.Order.le_max_right _ _).trans later))

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.WindowConnectors
