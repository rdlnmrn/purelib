module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalSideAreaRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalSidePreparation
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.RectangularMatchedObservationSides
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalConjugateRequest
import Purelib.Integration.Path.CenteredAreaDifference
import Purelib.Riemann.Periods.PeriodMatrix
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Path.JoinedTrace
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry

open Purelib.Riemann

open Purelib.RootIsolation

public section

/-! One coefficient-independent contact request controls every basis pair
on an actual matched side, and hence every homogeneous energy combination. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalConjugateEnergy

attribute [local congr] FiniteSum.Fin.sumFin_congr

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {firstFace lastFace :
      Meshes.PuncturedGridFaces.RegularFace
    bank}
  {firstModels : Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels frames firstFace}
    {lastModels : Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels frames lastFace}
  {start : Gaussian.Basic.Canonical} {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)}
  {leftEntry : Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry firstModels start owner} {rightEntry :
    Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry lastModels start owner}
  {leftDomain : Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain firstModels leftEntry.sheet} {rightDomain :
    Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain lastModels rightEntry.sheet}
  {firstDifferential secondDifferential : Hyperelliptic.Differentials.Basic.Differential genus} {firstSheet secondSheet
    : Fin 2}

variable {leftBox rightBox : Rational.Box}
  {leftMesh : Meshes.RectangularObservationMesh.ObservationMesh leftDomain.cuts leftBox}
  {rightMesh : Meshes.RectangularObservationMesh.ObservationMesh rightDomain.cuts rightBox}
  {leftColumn : Fin leftMesh.partition.x.intervals.length} {rightColumn : Fin rightMesh.partition.x.intervals.length}
  {horizontal : Fraction.Rational} {depth : Nat}
  {side : Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide leftMesh rightMesh leftColumn
    rightColumn horizontal}
  {trace : side.Trace depth}

namespace MatchedVerticalSidePreparation

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)
open _root_.Purelib.Data.Gaussian.Basic (conj)

variable {preparation :
  Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalSidePreparation.MatchedVerticalSidePreparation trace}
  {target : Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

/-- The actual conjugate area requests for every standard-differential pair on the retained vertical side. -/
@[expose] def EnergyPairs (preparation :
  Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalSidePreparation.MatchedVerticalSidePreparation trace)
    (target : Normalization.InverseRootPolynomial.Coordinate) (floor : Nat) :=
  Data.Vector.DependentVector (fun i : Fin genus => Data.Vector.DependentVector (fun j : Fin genus =>
    Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalSideAreaRequest.MatchedVerticalSidePreparation.AreaRequest
      preparation (Periods.PeriodMatrix.standardDifferential i) (Periods.PeriodMatrix.standardDifferential j) 0 0 target
      floor))

/-- Every original basis-pair request index is bounded by the supplied stage. -/
@[expose] def EnergyPairs.IndexBound (entries :
  Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalConjugateEnergy.MatchedVerticalSidePreparation.EnergyPairs
  preparation target floor) (index : Nat) : Prop :=
  ∀ i j, ((entries.get i).get j).index ≤ index

set_option genInjectivity false in
/-- A coefficient-independent common request for all basis pairs on the original matched vertical side.

The retained maximum stage also meets the requested floor. -/
structure EnergyRequest (preparation :
  Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalSidePreparation.MatchedVerticalSidePreparation trace)
    (target : Normalization.InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The actual retained original basis-pair requests. -/ entries :
    Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalConjugateEnergy.MatchedVerticalSidePreparation.EnergyPairs
    preparation target floor
  /-- The common sufficient reading stage. -/ index : Nat
  /-- The common stage meets the original requested floor. -/ floor_le : floor ≤ index
  /-- The common stage meets every retained original basis-pair request. -/ index_ge : entries.IndexBound index

constructive_injectivity EnergyRequest

namespace EnergyRequest

/-- Prepare every original basis pair and cache the maximum of their stages and the requested floor. -/
@[expose] def build (preparation :
  Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalSidePreparation.MatchedVerticalSidePreparation trace)
    (target : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < target) (floor : Nat) :
      Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalConjugateEnergy.MatchedVerticalSidePreparation.EnergyRequest
      preparation target floor := by
  let entries :
    Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalConjugateEnergy.MatchedVerticalSidePreparation.EnergyPairs
    preparation target floor := Data.Vector.DependentVector.ofFn fun i => Data.Vector.DependentVector.ofFn fun j =>
    Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalSideAreaRequest.MatchedVerticalSidePreparation.AreaRequest.build
      preparation (Periods.PeriodMatrix.standardDifferential i) (Periods.PeriodMatrix.standardDifferential j) 0 0 target
      positive floor
  let maximum := entries.maximum (fun _ row => row.maximum fun _ request => request.index)
  refine ⟨entries, max floor maximum, Nat.Order.le_max_left _ _, ?_⟩
  intro i j
  exact ((entries.get i).get_le_maximum (fun _ request => request.index) j).trans
    ((entries.get_le_maximum (fun _ row => row.maximum fun _ request => request.index) i).trans
      (Nat.Order.le_max_right _ _))

/-- The actual homogeneous centered-energy difference is bounded by genus squared times the squared coefficient norm and
retained target. -/
theorem accurate (request :
  Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalConjugateEnergy.MatchedVerticalSidePreparation.EnergyRequest
  preparation target floor) {stage : Nat} (later : request.index ≤ stage)
    (leftData : (i : Fin genus) → Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives leftDomain
      (Periods.PeriodMatrix.standardDifferential i) stage)
    (rightData : (i : Fin genus) → Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives rightDomain
      (Periods.PeriodMatrix.standardDifferential i) stage)
    (coefficients : Fin genus → Gaussian.Basic.Canonical)
    (leftPairs : (i j : Fin genus) → Periods.CenteredBilinearPath.Sample (fun vertex =>
      ⟨conj ((trace.leftReadings (leftData i).anchors (leftData i).offsets).values vertex),
        (trace.leftReadings (leftData j).anchors (leftData j).offsets).values vertex⟩))
    (rightPairs : (i j : Fin genus) → Periods.CenteredBilinearPath.Sample (fun vertex =>
      ⟨conj ((trace.rightReadings (rightData i).anchors (rightData i).offsets).values vertex),
        (trace.rightReadings (rightData j).anchors (rightData j).offsets).values vertex⟩))
    (left : Periods.CenteredBilinearPath.Sample (fun vertex =>
      ⟨sumFin (fun i => Data.Gaussian.Basic.conj (coefficients i) * Data.Gaussian.Basic.conj
        ((trace.leftReadings (leftData i).anchors (leftData i).offsets).values vertex)),
        FiniteSum.Fin.sumFin (fun i => coefficients i * (trace.leftReadings (leftData i).anchors (leftData
          i).offsets).values vertex)⟩))
    (right : Periods.CenteredBilinearPath.Sample (fun vertex =>
      ⟨sumFin (fun i => Data.Gaussian.Basic.conj (coefficients i) * Data.Gaussian.Basic.conj
        ((trace.rightReadings (rightData i).anchors (rightData i).offsets).values vertex)),
        FiniteSum.Fin.sumFin (fun i => coefficients i * (trace.rightReadings (rightData i).anchors (rightData
          i).offsets).values vertex)⟩)) :
    Data.Gaussian.Norm.Basic.normSq (left.centeredArea - right.centeredArea) ≤
      (genus : Normalization.InverseRootPolynomial.Coordinate)^2 * (FiniteSum.Fin.sumFin (fun i =>
        Data.Gaussian.Norm.Basic.normSq (coefficients i)))^2 * target := open Purelib.Integration in by
  have pairs (i j : Fin genus) : Data.Gaussian.Norm.Basic.normSq ((leftPairs i j).centeredArea - (rightPairs i
    j).centeredArea) ≤ target := by
    have bound :=
      VerticalConjugateRequest.MatchedVerticalSidePreparation.AreaRequest.conjugate_accurate
      ((request.entries.get i).get j) ((request.index_ge i j).trans later)
      (leftData i) (rightData i) (leftData j) (rightData j) (leftPairs i j) (rightPairs i j)
    have equal : ((leftPairs i j).originalArea - (rightPairs i j).originalArea) -
        ((leftPairs i j).endpoint - (rightPairs i j).endpoint) =
        (leftPairs i j).centeredArea - (rightPairs i j).centeredArea := by
      rw [(leftPairs i j).decomposition, (rightPairs i j).decomposition]
      ring1
    rw [equal] at bound
    exact bound.le
  have bound := Path.CenteredAreaDifference.Sample.centeredArea_difference_bound
    (fun i => Data.Gaussian.Basic.conj (coefficients i)) coefficients
    (fun i vertex => Data.Gaussian.Basic.conj ((trace.leftReadings (leftData i).anchors (leftData i).offsets).values
      vertex))
    (fun i vertex => Data.Gaussian.Basic.conj ((trace.rightReadings (rightData i).anchors (rightData
      i).offsets).values vertex))
    (fun i vertex => (trace.leftReadings (leftData i).anchors (leftData i).offsets).values vertex)
    (fun i vertex => (trace.rightReadings (rightData i).anchors (rightData i).offsets).values vertex)
    left right leftPairs rightPairs pairs
  have norms : FiniteSum.Fin.sumFin (fun i => Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Basic.conj
    (coefficients i))) = FiniteSum.Fin.sumFin (fun i => Data.Gaussian.Norm.Basic.normSq (coefficients i)) :=
    FiniteSum.Fin.sumFin_congr fun i => Gaussian.Norm.Basic.normSq_conj (coefficients i)
  rw [norms] at bound
  exact bound.trans_eq (by ring1)

end EnergyRequest
end MatchedVerticalSidePreparation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalConjugateEnergy
