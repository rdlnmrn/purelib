module
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Topology.Mesh.RetracingWords
public import Purelib.Riemann.RootContinuation.NewtonBandWindowCircuits
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedConnectors
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitAreas
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

open Purelib.Riemann

open Purelib

public section

/-! Requested connector decay inside an Newton-band window.
The retained hole polygon remains subtracted from the outer boundary. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.BandWindowConnectors

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition
open Purelib.Riemann.Periods
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target radius :
    Fraction.Rational}
  {grid : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius} {index :
    Hyperelliptic.Branches.BranchIsolation.Data.Index branches}
  {current : Meshes.LiftedPuncturedGrid grid.punctured}

variable {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank current.frames
  grid.faces.regulars} {i j : Fin genus}

/-- All connector requests are constructed from the two magnitude banks.
The hole and fine-cell polygons both remain in the comparison. -/
theorem fine_polygons_accurate (region : Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces grid index) (sheet : Fin
  2)
    (first : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential i))
    (second : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential j))
    (error : Fraction.Rational) (positive : 0 < error) (floor : Nat) :
    let compiled := RootContinuation.NewtonBandWindowCircuits.fineCompiler (current := current) region sheet
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
          region.boundary sheet - Topology.Mesh.RetracingWords.wordArea value compiled.word -
        Geometry.Grid.CellBoundary.sumValues (fun occurrence => Topology.Mesh.RetracingWords.wordArea value
          occurrence.word) compiled.regulars)) ≤ error := by
  intro compiled request threshold
  constructor
  · exact Data.Nat.Order.le_max_left _ _
  intro stage leftBank rightBank left right later
  have equal (coefficient : Gaussian.Basic.Canonical) :
      let value := Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh left.values)
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh right.values) coefficient
      current.edges.chainArea current.vertices value
        region.boundary sheet - Topology.Mesh.RetracingWords.wordArea value compiled.word =
        Topology.Mesh.RetracingWords.AreaTerm.total value compiled.areaTerms := by
    intro value
    have same := RootContinuation.NewtonBandWindowCircuits.fineCompiler_area region sheet value
      (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix_reverse _ _
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation_reverse current.mesh left.values)
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation_reverse current.mesh right.values)
        coefficient)
    change _ = Topology.Mesh.RetracingWords.wordArea value compiled.word + Topology.Mesh.RetracingWords.AreaTerm.total
      value compiled.areaTerms at same
    rw [same]
    ring1
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
    ((Data.Nat.Order.le_max_right _ _).trans later))

end Purelib.Curves.Hyperelliptic.Meshes.Newton.BandWindowConnectors
