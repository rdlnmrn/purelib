module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.EndpointPolygonPreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.JoinedCenteredArea
import Purelib.Integration.Path.JoinedTrace
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.RectangularPairedEndpointReadings
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.EndpointPolygonAreaRequest
import Purelib.Integration.Path.CenteredAreaDifference
import Purelib.Riemann.Periods.PeriodMatrix
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Path.PairedEndpointPolygon
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring

public section

/-! One coefficient-independent tail controls every energy combination on
the retained endpoint polygon, including its distinct left and right owners. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.EndpointPolygonEnergy

open Purelib
open Purelib.Algebra
open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.EndpointPolygonAreaRequest
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.EndpointPolygonAreaRequest.EndpointPolygonPreparation
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Data.Vector
open Purelib.Integration.Path
open Purelib.Riemann.Integration
open Purelib.Riemann.Normalization
open Purelib.Riemann.Periods
open Purelib.Data.Rat

open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.EndpointPolygonAreaRequest.EndpointPolygonPreparation
  (AreaRequest)
open Purelib.Integration.Path.JoinedCenteredArea (endpointPolygon)

open Purelib.Riemann.Readings.RectangularSeamBounds (boundarySlope)

attribute [local congr] Algebra.FiniteSum.Fin.sumFin_congr

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Curves.Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {firstFace lastFace :
    Riemann.Meshes.PuncturedGridFaces.RegularFace bank}
  {firstModels : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels frames
    firstFace} {lastModels : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels
    frames lastFace}
  {start : Data.Gaussian.Basic.Canonical} {owner : Riemann.Topology.SquareRootContinuationChain.Owner
    (curve.polynomial.eval start)}
  {leftEntry : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry firstModels start owner}
    {rightEntry : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry lastModels start owner}
  {leftDomain : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain firstModels leftEntry.sheet}
    {rightDomain : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain lastModels rightEntry.sheet}
  {firstDifferential secondDifferential : Curves.Hyperelliptic.Differentials.Basic.Differential genus} {firstSheet
    secondSheet : Fin 2}

open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Riemann.Readings.RectangularSeamBounds (boundarySlope)
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator)

open Purelib.Riemann.Integration.RectangularOwnedTriangulation (OwnedVertex)
open Purelib.Riemann.Readings.RectangularPairedEndpointReadings (PairedEndpointReadingsGeometry)

variable {count : Nat}
  {first : Fin (count + 1) → Purelib.Integration.Path.JoinedTrace.VertexTrace
    (Riemann.Integration.RectangularOwnedTriangulation.OwnedVertex leftDomain.geometry)}
  {last : Fin (count + 1) → Purelib.Integration.Path.JoinedTrace.VertexTrace
    (Riemann.Integration.RectangularOwnedTriangulation.OwnedVertex rightDomain.geometry)}
  {geometry : Riemann.Readings.RectangularPairedEndpointReadings.PairedEndpointReadingsGeometry first last}

namespace EndpointPolygonPreparation

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)
open _root_.Purelib.Data.Gaussian.Basic (conj)
open Purelib.Data.Gaussian.Norm.Basic (normSq_conj)

variable {preparation : EndpointPolygonPreparation
  (leftEntry := leftEntry) (rightEntry := rightEntry) geometry}
  {target : Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

/-- The original matrix of endpoint-polygon area requests for every standard basis pair. -/
@[expose] def EnergyPairs (preparation : EndpointPolygonPreparation (leftEntry := leftEntry)
  (rightEntry := rightEntry) geometry)
    (target : InverseRootPolynomial.Coordinate) (floor : Nat) :=
  Data.Vector.DependentVector (fun i : Fin genus => Data.Vector.DependentVector (fun j : Fin genus =>
    EndpointPolygonPreparation.AreaRequest preparation (PeriodMatrix.standardDifferential i)
      (PeriodMatrix.standardDifferential j) 0 0 target floor))

/-- The supplied common stage pays every retained original endpoint-polygon pair request. -/
@[expose] def EnergyPairs.IndexBound (entries :
  EnergyPairs preparation
  target floor) (index : Nat) : Prop :=
  ∀ i j, ((entries.get i).get j).index ≤ index

set_option genInjectivity false in
/-- One coefficient-independent common tail for all original endpoint-polygon energy pairs.

The dependent request matrix retains the distinct original left and right endpoint owners and the supplied minimum
stage. -/
structure EnergyRequest (preparation : EndpointPolygonPreparation (leftEntry := leftEntry)
  (rightEntry := rightEntry) geometry)
    (target : InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The retained original matrix of endpoint-polygon basis-pair requests. -/ entries :
    EnergyPairs preparation
    target floor
  /-- The cached common stage paying every original basis pair. -/ index : Nat
  /-- The common stage retains the supplied original minimum floor. -/ floor_le : floor ≤ index
  /-- Every actual retained pair request is ready at the common stage. -/ index_ge : entries.IndexBound index

constructive_injectivity EnergyRequest

namespace EnergyRequest

/-- Prepare all original endpoint-polygon basis pairs and cache their maximum stage above the supplied floor. -/
@[expose] def build (preparation : EndpointPolygonPreparation (leftEntry := leftEntry)
  (rightEntry := rightEntry) geometry)
    (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) (floor : Nat) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.EndpointPolygonEnergy.EndpointPolygonPreparation.EnergyRequest
      preparation target floor := by
  let entries : Curves.Hyperelliptic.Meshes.PuncturedGrid.EndpointPolygonEnergy.EndpointPolygonPreparation.EnergyPairs
    preparation target floor := DependentVector.ofFn fun i => DependentVector.ofFn fun j =>
    AreaRequest.build preparation (PeriodMatrix.standardDifferential i) (PeriodMatrix.standardDifferential j) 0 0 target
      positive floor
  let maximum := entries.maximum (fun _ row => row.maximum fun _ request => request.index)
  refine ⟨entries, max floor maximum, Data.Nat.Order.le_max_left _ _, ?_⟩
  intro i j
  exact ((entries.get i).get_le_maximum (fun _ request => request.index) j).trans
    ((entries.get_le_maximum (fun _ row => row.maximum fun _ request => request.index) i).trans
      (Data.Nat.Order.le_max_right _ _))

/-- Every original coefficient combination of the retained matched endpoint readings satisfies the homogeneous energy
discrepancy bound. -/
theorem accurate (request :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.EndpointPolygonEnergy.EndpointPolygonPreparation.EnergyRequest preparation
  target floor) {stage : Nat} (later : request.index ≤ stage)
    (leftData : (i : Fin genus) → PrimitiveData.DomainPrimitives leftDomain (PeriodMatrix.standardDifferential i) stage)
    (rightData : (i : Fin genus) → PrimitiveData.DomainPrimitives rightDomain (PeriodMatrix.standardDifferential i)
      stage)
    (coefficients : Fin genus → Data.Gaussian.Basic.Canonical)
    (leftPairs : (i j : Fin genus) → CenteredBilinearPath.Sample (fun vertex =>
      ⟨conj ((geometry.leftReadings (leftData i).anchors (leftData i).offsets).values vertex),
        (geometry.leftReadings (leftData j).anchors (leftData j).offsets).values vertex⟩))
    (rightPairs : (i j : Fin genus) → CenteredBilinearPath.Sample (fun vertex =>
      ⟨conj ((geometry.rightReadings (rightData i).anchors (rightData i).offsets).values vertex),
        (geometry.rightReadings (rightData j).anchors (rightData j).offsets).values vertex⟩))
    (left : CenteredBilinearPath.Sample (fun vertex =>
      ⟨sumFin (fun i => Data.Gaussian.Basic.conj (coefficients i) * Data.Gaussian.Basic.conj
        ((geometry.leftReadings (leftData i).anchors (leftData i).offsets).values vertex)),
        FiniteSum.Fin.sumFin (fun i => coefficients i * (geometry.leftReadings (leftData i).anchors (leftData
          i).offsets).values vertex)⟩))
    (right : CenteredBilinearPath.Sample (fun vertex =>
      ⟨sumFin (fun i => Data.Gaussian.Basic.conj (coefficients i) * Data.Gaussian.Basic.conj
        ((geometry.rightReadings (rightData i).anchors (rightData i).offsets).values vertex)),
        FiniteSum.Fin.sumFin (fun i => coefficients i * (geometry.rightReadings (rightData i).anchors (rightData
          i).offsets).values vertex)⟩)) :
    Data.Gaussian.Norm.Basic.normSq (left.centeredArea - right.centeredArea) ≤
      (genus : InverseRootPolynomial.Coordinate)^2 * (FiniteSum.Fin.sumFin (fun i =>
        Data.Gaussian.Norm.Basic.normSq (coefficients i)))^2 * target := by
  have pairs (i j : Fin genus) : Data.Gaussian.Norm.Basic.normSq ((leftPairs i j).centeredArea - (rightPairs i
    j).centeredArea) ≤ target := by
    have bound := ((request.entries.get i).get j).conjugate_accurate ((request.index_ge i j).trans later)
      (leftData i) (rightData i) (leftData j) (rightData j) (leftPairs i j) (rightPairs i j)
    exact bound.le
  have bound := CenteredAreaDifference.Sample.centeredArea_difference_bound (fun i => Data.Gaussian.Basic.conj
    (coefficients i)) coefficients
    (fun i vertex => Data.Gaussian.Basic.conj ((geometry.leftReadings (leftData i).anchors (leftData
      i).offsets).values vertex))
    (fun i vertex => Data.Gaussian.Basic.conj ((geometry.rightReadings (rightData i).anchors (rightData
      i).offsets).values vertex))
    (fun i vertex => (geometry.leftReadings (leftData i).anchors (leftData i).offsets).values vertex)
    (fun i vertex => (geometry.rightReadings (rightData i).anchors (rightData i).offsets).values vertex)
    left right leftPairs rightPairs pairs
  have norms : FiniteSum.Fin.sumFin (fun i => Data.Gaussian.Norm.Basic.normSq
    (Data.Gaussian.Basic.conj (coefficients i))) = FiniteSum.Fin.sumFin (fun i =>
    Data.Gaussian.Norm.Basic.normSq (coefficients i)) :=
    FiniteSum.Fin.sumFin_congr fun i => Data.Gaussian.Norm.Basic.normSq_conj (coefficients i)
  rw [norms] at bound
  exact bound.trans_eq (by ring1)

/-- Read the primitive at the original owned endpoint's retained cell and coordinate. -/
@[expose] def ownerValue {stage : Nat} {differential : Differentials.Basic.Differential genus}
    (data : PrimitiveData.DomainPrimitives leftDomain differential stage) (owner :
      RectangularOwnedTriangulation.OwnedVertex leftDomain.geometry) : Gaussian :=
  data.anchors.alignedValue data.offsets owner.column owner.row owner.point

/-- The two actual original endpoint polygons satisfy the homogeneous energy discrepancy estimate on the common
requested tail.

Distinct vertex owners and independently retained pair samples are preserved throughout the comparison. -/
theorem original_accurate (request :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.EndpointPolygonEnergy.EndpointPolygonPreparation.EnergyRequest preparation
  target floor) {stage : Nat} (later : request.index ≤ stage)
    (leftData : (i : Fin genus) → PrimitiveData.DomainPrimitives leftDomain (PeriodMatrix.standardDifferential i) stage)
    (rightData : (i : Fin genus) → PrimitiveData.DomainPrimitives rightDomain (PeriodMatrix.standardDifferential i)
      stage)
    (coefficients : Fin genus → Data.Gaussian.Basic.Canonical)
    (leftPairs : (i j : Fin genus) → CenteredBilinearPath.Sample (fun vertex =>
      ⟨conj ((geometry.leftReadings (leftData i).anchors (leftData i).offsets).values vertex),
        (geometry.leftReadings (leftData j).anchors (leftData j).offsets).values vertex⟩))
    (rightPairs : (i j : Fin genus) → CenteredBilinearPath.Sample (fun vertex =>
      ⟨conj ((geometry.rightReadings (rightData i).anchors (rightData i).offsets).values vertex),
        (geometry.rightReadings (rightData j).anchors (rightData j).offsets).values vertex⟩))
    (leftPolygons : (i j : Fin genus) → CenteredBilinearPath.Sample (fun vertex => AreaRequest.energyValues (leftData i)
      (leftData j)
      ((JoinedCenteredArea.endpointPolygon first).indexed vertex)))
    (rightPolygons : (i j : Fin genus) → CenteredBilinearPath.Sample (fun vertex => AreaRequest.energyValues (rightData
      i) (rightData j)
      ((JoinedCenteredArea.endpointPolygon last).indexed vertex)))
    (left : CenteredBilinearPath.Sample (fun vertex =>
      ⟨sumFin (fun i => Data.Gaussian.Basic.conj (coefficients i) * Data.Gaussian.Basic.conj
        (ownerValue
        (leftData i) ((JoinedCenteredArea.endpointPolygon first).indexed vertex))),
        FiniteSum.Fin.sumFin (fun i => coefficients i *
          ownerValue
          (leftData i) ((JoinedCenteredArea.endpointPolygon first).indexed vertex))⟩))
    (right : CenteredBilinearPath.Sample (fun vertex =>
      ⟨sumFin (fun i => Data.Gaussian.Basic.conj (coefficients i) * Data.Gaussian.Basic.conj
        (ownerValue
        (rightData i) ((JoinedCenteredArea.endpointPolygon last).indexed vertex))),
        FiniteSum.Fin.sumFin (fun i => coefficients i *
          ownerValue
          (rightData i) ((JoinedCenteredArea.endpointPolygon last).indexed vertex))⟩)) :
    Data.Gaussian.Norm.Basic.normSq (left.centeredArea - right.centeredArea) ≤
      (genus : InverseRootPolynomial.Coordinate)^2 * (FiniteSum.Fin.sumFin (fun i =>
        Data.Gaussian.Norm.Basic.normSq (coefficients i)))^2 * target := by
  have pairs (i j : Fin genus) : Data.Gaussian.Norm.Basic.normSq ((leftPolygons i j).centeredArea -
    (rightPolygons i j).centeredArea) ≤ target :=
    (((request.entries.get i).get j).original_polygons_accurate ((request.index_ge i j).trans later)
      (leftData i) (rightData i) (leftData j) (rightData j) (leftPairs i j) (rightPairs i j)
      (leftPolygons i j) (rightPolygons i j)).le
  have bound := CenteredAreaDifference.Sample.centeredArea_difference_bound (fun i => Data.Gaussian.Basic.conj
    (coefficients i)) coefficients
    (fun i vertex => Data.Gaussian.Basic.conj
      (ownerValue
      (leftData i) ((JoinedCenteredArea.endpointPolygon first).indexed vertex)))
    (fun i vertex => Data.Gaussian.Basic.conj
      (ownerValue
      (rightData i) ((JoinedCenteredArea.endpointPolygon last).indexed vertex)))
    (fun i vertex =>
      ownerValue
      (leftData i) ((JoinedCenteredArea.endpointPolygon first).indexed vertex))
    (fun i vertex =>
      ownerValue
      (rightData i) ((JoinedCenteredArea.endpointPolygon last).indexed vertex))
    left right leftPolygons rightPolygons pairs
  have norms : FiniteSum.Fin.sumFin (fun i => Data.Gaussian.Norm.Basic.normSq
    (Data.Gaussian.Basic.conj (coefficients i))) = FiniteSum.Fin.sumFin (fun i =>
    Data.Gaussian.Norm.Basic.normSq (coefficients i)) :=
    FiniteSum.Fin.sumFin_congr fun i => Data.Gaussian.Norm.Basic.normSq_conj (coefficients i)
  rw [norms] at bound
  exact bound.trans_eq (by ring1)

end EnergyRequest
end EndpointPolygonPreparation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.EndpointPolygonEnergy
