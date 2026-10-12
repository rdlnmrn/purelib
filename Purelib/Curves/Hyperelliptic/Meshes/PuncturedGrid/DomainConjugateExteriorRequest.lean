module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Energy.Polygon

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Periods.BilinearCombination
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.Readings.RectangularSeamBounds
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReadingCaps
import Purelib.Riemann.Integration.RectangularClippedConjugateSeams
import Purelib.Integration.Polynomial.Rectangle.ClippedExteriorCombination
import Purelib.Riemann.Readings.RectangularBoundaryTranslations
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Polynomial.Rectangle.ClippedExteriorTolerance
import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularClippedLocalBoundary
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

open Purelib.RootIsolation

public section

/-!
# Requested conjugate energy comparison with stitched piece exteriors

The retained exterior includes the joining edges between local model
owners. A fixed slope ceiling chooses an overlap request which pays all
corrected seams and corner polygons, independently of the dyadic depth.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainConjugateExteriorRequest

open _root_.Purelib.Data.Gaussian.Basic (conj)

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face : Meshes.PuncturedGridFaces.RegularFace bank}
      {models
    : Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels frames face} {sheet : Fin 2}
  {domain : Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain models sheet} {box :
    Rational.Box}

set_option genInjectivity false in
/-- A coefficient-independent request comparing the original conjugate local energy with its stitched exterior.

The fixed face slope allocates a retained reading cap, and the model request uses that exact cap on the same prepared
mesh. -/
structure ConjugateExteriorRequest (preflight : Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds.EnergyPreflight
  domain)
    (mesh : Meshes.RectangularObservationMesh.ObservationMesh domain.cuts box) (target : Fraction.Rational) where
  /-- The original face's cached common slope and exterior-reading cap. -/ tolerance :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReadingCaps.DomainPrimitives.FaceExteriorTolerance preflight mesh target
  /-- The original basis model request at the exact retained cap. -/ models :
    Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds.EnergyPreflight.Request preflight tolerance.budget.cap

constructive_injectivity ConjugateExteriorRequest

namespace ConjugateExteriorRequest

variable {preflight : Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds.EnergyPreflight domain} {mesh :
  Meshes.RectangularObservationMesh.ObservationMesh domain.cuts box} {target : Fraction.Rational}

/-- Prepare the original face tolerance and request every basis model at that same retained positive cap. -/
@[expose] def build (preflight : Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds.EnergyPreflight domain) (mesh :
  Meshes.RectangularObservationMesh.ObservationMesh domain.cuts box)
    (target : Fraction.Rational) (positive : 0 < target) :
      Hyperelliptic.Meshes.PuncturedGrid.DomainConjugateExteriorRequest.ConjugateExteriorRequest preflight mesh target
      :=
  let tolerance := Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReadingCaps.DomainPrimitives.FaceExteriorTolerance.build
    preflight mesh target positive
  ⟨tolerance, Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds.EnergyPreflight.Request.build preflight
    tolerance.budget.cap tolerance.budget.positive⟩

variable {stage : Nat}

/-- Every original conjugate basis-pair local-minus-exterior area satisfies the requested bound at a sufficient shared
model stage. -/
theorem pair_bound (request : Hyperelliptic.Meshes.PuncturedGrid.DomainConjugateExteriorRequest.ConjugateExteriorRequest
  preflight mesh target) (later : request.models.index ≤ stage)
    (cached : (row : Fin genus) → Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives domain
      (Periods.PeriodMatrix.standardDifferential row) stage)
    (first second : Fin genus)
    (assembly : Readings.RectangularObservationAssembly.ObservationMesh.ClippedAssembly mesh (fun column row point =>
      ⟨conj ((cached first).anchors.alignedValue (cached first).offsets column row point),
        (cached second).anchors.alignedValue (cached second).offsets column row point⟩)) :
    Data.Gaussian.Norm.Basic.normSq (assembly.localTotal - assembly.exterior) ≤ target := by
  let left := request.models.rowAtStage stage later first
  let right := request.models.rowAtStage stage later second
  have estimate :=
    Integration.RectangularClippedConjugateSeams.ObservationMesh.ClippedAssembly.conjugate_local_sub_exterior_bound left
    right
    (cached first).anchors (cached second).anchors (cached first).offsets (cached second).offsets
      domain.patch.cell_refines assembly
  have slopeNonnegative : 0 ≤ Readings.RectangularSeamBounds.boundarySlope (preflight.overlaps.get first) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (preflight.overlaps.get first).numeratorUpper_nonnegative
        (preflight.overlaps.get first).inverseUpper_positive.le)) face.cell.box.diagonalSq_nonneg
  exact estimate.trans (request.tolerance.budget.pair_bound
    (left.edgeBound_nonnegative.trans left.edgeBound_le_globalBound) left.accurate.le right.accurate.le
    slopeNonnegative (request.tolerance.row_le first) (request.tolerance.row_le second))

/-- The conjugated coefficient expansion keeps a compact dependent assembly
type while referring to precisely the retained aligned primitive bank. -/
@[expose] def EnergyAssembly
    (cached : (row : Fin genus) → Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives domain
      (Periods.PeriodMatrix.standardDifferential row) stage)
    (mesh : Meshes.RectangularObservationMesh.ObservationMesh domain.cuts box) (coefficients :
      LinearAlgebra.Gaussian.Energy.GaussianVector genus) :=
  Readings.RectangularObservationAssembly.ObservationMesh.ClippedAssembly mesh (fun column row point =>
    ⟨sumFin (fun i => Data.Gaussian.Basic.conj (coefficients i) * Data.Gaussian.Basic.conj ((cached
      i).anchors.alignedValue (cached i).offsets column row point)),
      FiniteSum.Fin.sumFin (fun i => coefficients i * (cached i).anchors.alignedValue (cached i).offsets column row
        point)⟩)

/-- Conjugation distributes through a finite Gaussian coefficient combination. -/
private theorem conjugate_combination {count : Nat} (coefficients values : Fin count → Gaussian.Basic.Canonical) :
    Data.Gaussian.Basic.conj (FiniteSum.Fin.sumFin (fun i => coefficients i * values i)) = FiniteSum.Fin.sumFin (fun
      i => Data.Gaussian.Basic.conj (coefficients i) * Data.Gaussian.Basic.conj (values i)) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [FiniteSum.Fin.sumFin_succ, Gaussian.Basic.conj_add,
        Gaussian.Basic.conj_mul, ih, FiniteSum.Fin.sumFin_succ]

/-- Alignment adds a constant on each retained model rectangle. Its closed
energy boundary is unchanged, including the conjugated component. -/
theorem EnergyAssembly.raw_localTotal_eq
    (cached : (row : Fin genus) → Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives domain
      (Periods.PeriodMatrix.standardDifferential row) stage)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (assembly :
      Hyperelliptic.Meshes.PuncturedGrid.DomainConjugateExteriorRequest.ConjugateExteriorRequest.EnergyAssembly cached
      mesh coefficients) :
    assembly.localTotal = mesh.pieces.localBoundary (fun column row point => Energy.Polygon.energyPrimitivePoint
      (FiniteSum.Fin.sumFin (fun i => coefficients i * (cached i).primitives.value column row point))) mesh.depth := by
  rw [assembly.localTotal_eq]
  let raw := fun column row point => Energy.Polygon.energyPrimitivePoint
    (FiniteSum.Fin.sumFin (fun i => coefficients i * (cached i).primitives.value column row point))
  let aligned := fun column row point => (⟨
    FiniteSum.Fin.sumFin (fun i => Data.Gaussian.Basic.conj (coefficients i) * Data.Gaussian.Basic.conj ((cached
      i).anchors.alignedValue (cached i).offsets column row point)),
    FiniteSum.Fin.sumFin (fun i => coefficients i * (cached i).anchors.alignedValue (cached i).offsets column row
      point)⟩ : Topology.Polygon.Stokes.PrimitivePoint)
  let offsets := fun column row => Energy.Polygon.energyPrimitivePoint
    (FiniteSum.Fin.sumFin (fun i => coefficients i * (cached i).offsets.values column row))
  apply mesh.pieces.localBoundary_eq_of_translation raw aligned offsets
  intro column row point
  have alignedSum : FiniteSum.Fin.sumFin (fun i => coefficients i * (cached i).anchors.alignedValue (cached i).offsets
    column row point) =
      FiniteSum.Fin.sumFin (fun i => coefficients i * (cached i).primitives.value column row point) +
        FiniteSum.Fin.sumFin (fun i => coefficients i * (cached i).offsets.values column row) := by
    rw [FiniteSum.Fin.sumFin_congr (fun i => show coefficients i * (cached i).anchors.alignedValue (cached i).offsets
      column row point =
      coefficients i * (cached i).primitives.value column row point + coefficients i * (cached i).offsets.values column
        row from by
        rw [Integration.RectangularPrimitiveGluing.PrimitiveAnchors.alignedValue]; ring1), FiniteSum.Fin.sumFin_add]
  dsimp only [raw, aligned, offsets, Energy.Polygon.energyPrimitivePoint, Topology.Polygon.Stokes.PrimitivePoint.add]
  rw [← Hyperelliptic.Meshes.PuncturedGrid.DomainConjugateExteriorRequest.ConjugateExteriorRequest.conjugate_combination
    coefficients (fun i => (cached i).anchors.alignedValue (cached i).offsets column row point),
    alignedSum, Gaussian.Basic.conj_add]

/-- The actual combined energy's local-minus-exterior discrepancy is bounded homogeneously by genus squared, coefficient
norm squared and the retained target. -/
theorem weighted_bound (request :
  Hyperelliptic.Meshes.PuncturedGrid.DomainConjugateExteriorRequest.ConjugateExteriorRequest preflight mesh target)
  (later : request.models.index ≤ stage)
    (cached : (row : Fin genus) → Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives domain
      (Periods.PeriodMatrix.standardDifferential row) stage)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (assembly :
      Hyperelliptic.Meshes.PuncturedGrid.DomainConjugateExteriorRequest.ConjugateExteriorRequest.EnergyAssembly cached
      mesh coefficients) :
    Data.Gaussian.Norm.Basic.normSq (assembly.localTotal - assembly.exterior) ≤
      (genus : Fraction.Rational) ^ 2 * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 *
        target := by
  let pairs := fun first second : Fin genus =>
    Readings.RectangularObservationAssembly.ObservationMesh.ClippedAssembly.build mesh
    (fun column row point => ⟨conj ((cached first).anchors.alignedValue (cached first).offsets column row point),
      (cached second).anchors.alignedValue (cached second).offsets column row point⟩)
  have expanded := assembly.local_sub_exterior_combination (fun i => Data.Gaussian.Basic.conj (coefficients i))
    coefficients
    (fun i column row point => Data.Gaussian.Basic.conj ((cached i).anchors.alignedValue (cached i).offsets column
      row point))
    (fun i column row point => (cached i).anchors.alignedValue (cached i).offsets column row point) pairs
  rw [expanded]
  have estimate := Periods.BilinearCombination.combination_bound (fun i => Data.Gaussian.Basic.conj (coefficients
    i)) coefficients
    (fun first second => (pairs first second).localTotal - (pairs first second).exterior)
    (fun first second => request.pair_bound later cached first second (pairs first second))
  rw [FiniteSum.Fin.sumFin_congr (fun i => Gaussian.Norm.Basic.normSq_conj (coefficients i))] at estimate
  have coefficientNorm := FiniteSum.Fin.sumFin_congr
    (fun row : Fin genus => Gaussian.Norm.Basic.normSq_eq_canonical (coefficients row))
  rw [coefficientNorm] at estimate
  exact estimate.trans_eq (by unfold Readings.PreparedObservationCoercivity.coefficientNormSq; ring1)

end ConjugateExteriorRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainConjugateExteriorRequest
