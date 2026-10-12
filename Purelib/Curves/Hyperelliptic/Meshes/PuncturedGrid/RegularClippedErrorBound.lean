module
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBilinearAssembly
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.Readings.RectangularSeamBounds
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularClippedAssembly
import Purelib.Integration.Polynomial.Rectangle.ClippedExteriorCombination
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularClippedRequest
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Riemann

open Purelib.RootIsolation

@[expose] public section

/-! Weighted local-to-exterior errors for the actual two-sheet face assemblies.
Every basis pair uses the supplied numerical bank and its retained request. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularClippedErrorBound.TwoSheetRequest

attribute [local congr] FiniteSum.Fin.sumFin_congr

open Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh.ClippedAssembly
  (local_sub_exterior_combination)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {faces : List (Meshes.PuncturedGridFaces.RegularFace
      bank)}
    {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces}
  {coarse : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes domains sheet}
  {fixed : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains
    sheet} {target : Fraction.Rational}

/-- The explicit original seam and corner bound for one retained basis pair, sheet and face at a sufficient stage. -/
def pairExteriorBound (energy : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest coarse fixed
  target) (stage : Nat) (later : energy.index ≤ stage)
    (sheet : Fin 2) (position : Fin faces.length) (first second : Fin genus) : Fraction.Rational :=
  let entry := (energy.entries.get sheet).entries.get position
  let mesh := (energy.entries.get sheet).meshes.entries.get position
  let rowLater := ((energy.entries.get sheet).index_ge position).trans ((energy.index_ge sheet).trans later)
  let left := entry.modelRequest.rowAtStage stage rowLater first
  let right := entry.modelRequest.rowAtStage stage rowLater second
  let overlaps := ((fixed sheet).get position).get.overlaps
  let seam := 8 * max (4 * left.globalBound) (4 * right.globalBound) *
    (4 * max (Readings.RectangularSeamBounds.boundarySlope (overlaps.get first))
      (Readings.RectangularSeamBounds.boundarySlope (overlaps.get second)) +
      max (4 * Readings.RectangularSeamBounds.boundarySlope (overlaps.get first)) (4 *
        Readings.RectangularSeamBounds.boundarySlope (overlaps.get second)))
  4 * ((mesh.boundaryColumns : Fraction.Rational) ^ 2 * ((mesh.boundaryRows + 1 : Nat) : Fraction.Rational) ^ 2 +
    ((mesh.boundaryColumns + 1 : Nat) : Fraction.Rational) ^ 2 * (mesh.boundaryRows : Fraction.Rational) ^ 2) * seam +
    512 * ((mesh.boundaryColumns : Fraction.Rational) * (mesh.boundaryRows : Fraction.Rational)) ^ 2 *
      (max left.globalBound right.globalBound) ^ 2

/-- The actual weighted local-minus-exterior reading is bounded by the original pairwise face errors with their
homogeneous coefficient weights. -/
theorem FaceAssembly.local_sub_exterior_bound {energy :
  Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest coarse fixed target}
    {stage : Nat} {cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage}
      {left right : LinearAlgebra.Gaussian.Energy.GaussianVector genus}
    {sheet : Fin 2} {position : Fin faces.length} (later : energy.index ≤ stage)
    (assembly : Hyperelliptic.Meshes.PuncturedGrid.RegularClippedAssembly.TwoSheetRequest.FaceAssembly energy cache left
      right sheet position) :
    Data.Gaussian.Norm.Basic.normSq (assembly.localTotal - assembly.exterior) ≤
      ((genus : Fraction.Rational) * (genus : Fraction.Rational)) *
        FiniteSum.Fin.sumFin (fun first => FiniteSum.Fin.sumFin (fun second => Data.Gaussian.Norm.Basic.normSq (left
          first) * Data.Gaussian.Norm.Basic.normSq (right second) *
          Hyperelliptic.Meshes.PuncturedGrid.RegularClippedErrorBound.TwoSheetRequest.pairExteriorBound energy stage
            later sheet position first second)) := by
  let mesh := (energy.entries.get sheet).meshes.entries.get position
  let values := fun (i : Fin genus) column row point =>
    (cache.atDomain position sheet i).anchors.alignedValue (cache.atDomain position sheet i).offsets column row point
  let pairs := fun (i j : Fin genus) => Readings.RectangularObservationAssembly.ObservationMesh.ClippedAssembly.build
    mesh
    (fun column row point => ⟨values i column row point, values j column row point⟩)
  have bounded (i j : Fin genus) : Data.Gaussian.Norm.Basic.normSq ((pairs i j).localTotal - (pairs i j).exterior) ≤
      Hyperelliptic.Meshes.PuncturedGrid.RegularClippedErrorBound.TwoSheetRequest.pairExteriorBound energy stage later
        sheet position i j := by
    exact
      Hyperelliptic.Meshes.PuncturedGrid.DomainBilinearAssembly.EnergyPreflight.Request.clipped_local_sub_exterior_bound
      ((energy.entries.get sheet).entries.get position).modelRequest
      (((energy.entries.get sheet).index_ge position).trans ((energy.index_ge sheet).trans later))
      (cache.atDomain position sheet) i j (pairs i j)
  rw [assembly.local_sub_exterior_combination left right values values pairs]
  have weighted (i j : Fin genus) :
      Data.Gaussian.Norm.Basic.normSq (left i * right j * ((pairs i j).localTotal - (pairs i j).exterior)) ≤
        Data.Gaussian.Norm.Basic.normSq (left i) * Data.Gaussian.Norm.Basic.normSq (right j) *
          Hyperelliptic.Meshes.PuncturedGrid.RegularClippedErrorBound.TwoSheetRequest.pairExteriorBound energy stage
          later sheet position i j := by
    rw [Gaussian.Norm.Basic.normSq_mul, Gaussian.Norm.Basic.normSq_mul]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (bounded i j)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (Gaussian.Norm.Basic.normSq_nonneg _)
        (Gaussian.Norm.Basic.normSq_nonneg _))
  have inner (i : Fin genus) := Gaussian.Norm.Sum.Indexed.normSq_sumFin_le_count_mul_sumFin
    (fun j => left i * right j * ((pairs i j).localTotal - (pairs i j).exterior))
    (fun j => Data.Gaussian.Norm.Basic.normSq (left i) * Data.Gaussian.Norm.Basic.normSq (right j) *
      Hyperelliptic.Meshes.PuncturedGrid.RegularClippedErrorBound.TwoSheetRequest.pairExteriorBound energy stage later
      sheet position i j) (weighted i)
  have estimate := Gaussian.Norm.Sum.Indexed.normSq_sumFin_le_count_mul_sumFin
    (fun i => FiniteSum.Fin.sumFin (fun j => left i * right j * ((pairs i j).localTotal - (pairs i j).exterior)))
    (fun i => (genus : Fraction.Rational) * FiniteSum.Fin.sumFin (fun j => Data.Gaussian.Norm.Basic.normSq (left i)
      * Data.Gaussian.Norm.Basic.normSq (right j) *
      Hyperelliptic.Meshes.PuncturedGrid.RegularClippedErrorBound.TwoSheetRequest.pairExteriorBound energy stage later
        sheet position i j)) inner
  exact estimate.trans_eq (by rw [FiniteSum.Fin.sumFin_mul_left]; ring1)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularClippedErrorBound.TwoSheetRequest

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularClippedErrorBound.LocalBoundaryRequest

attribute [local congr] FiniteSum.Fin.sumFin_congr

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {faces : List (Meshes.PuncturedGridFaces.RegularFace
      bank)}
    {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces}
  {coarse : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes domains sheet}
  {fixed : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains
    sheet} {target : Fraction.Rational}

/-- The existing small local boundary now controls the stitched exteriors,
with every actual face error paid on both sheets. -/
theorem exterior_bound (request : Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryRequest.LocalBoundaryRequest
  coarse fixed target)
    {stage : Nat} {cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage}
      (later : request.ownership.index ≤ stage)
    (samples : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest.Samples request.energy cache)
    (left right : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (assemblies : Hyperelliptic.Meshes.PuncturedGrid.RegularClippedAssembly.TwoSheetRequest.Assemblies
      request.energy cache left right) :
    let energyLater := request.ownership.energy_le.trans later
    let faceBound := fun sheet position => ((genus : Fraction.Rational) * (genus : Fraction.Rational)) *
      FiniteSum.Fin.sumFin (fun first => FiniteSum.Fin.sumFin (fun second => Data.Gaussian.Norm.Basic.normSq (left
        first) * Data.Gaussian.Norm.Basic.normSq (right second) *
        Hyperelliptic.Meshes.PuncturedGrid.RegularClippedErrorBound.TwoSheetRequest.pairExteriorBound
          request.energy stage energyLater sheet position first second))
    Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun sheet : Fin 2 => FiniteSum.Fin.sumFin (fun position :
      Fin faces.length =>
      ((assemblies.get sheet).get position).exterior))) ≤
      2 * (Readings.PreparedObservationCoercivity.coefficientNormSq left *
        Readings.PreparedObservationCoercivity.coefficientNormSq right * target +
        2 * FiniteSum.Fin.sumFin (fun sheet : Fin 2 => (faces.length : Fraction.Rational) * FiniteSum.Fin.sumFin (fun
          position : Fin faces.length =>
          faceBound sheet position))) := by
  dsimp only
  let energyLater := request.ownership.energy_le.trans later
  let faceBound := fun (sheet : Fin 2) (position : Fin faces.length) => ((genus : Fraction.Rational) * (genus :
    Fraction.Rational)) *
    FiniteSum.Fin.sumFin (fun first => FiniteSum.Fin.sumFin (fun second => Data.Gaussian.Norm.Basic.normSq (left
      first) * Data.Gaussian.Norm.Basic.normSq (right second) *
      Hyperelliptic.Meshes.PuncturedGrid.RegularClippedErrorBound.TwoSheetRequest.pairExteriorBound
        request.energy stage energyLater sheet position first second))
  have inner (sheet : Fin 2) := Gaussian.Norm.Sum.Indexed.normSq_sumFin_le_count_mul_sumFin
    (fun position => ((assemblies.get sheet).get position).localTotal - ((assemblies.get sheet).get position).exterior)
    (faceBound sheet) (fun position =>
      Hyperelliptic.Meshes.PuncturedGrid.RegularClippedErrorBound.TwoSheetRequest.FaceAssembly.local_sub_exterior_bound
      energyLater
      ((assemblies.get sheet).get position))
  have errorBound := Gaussian.Norm.Sum.Indexed.normSq_sumFin_le_count_mul_sumFin
    (fun sheet : Fin 2 => FiniteSum.Fin.sumFin (fun position : Fin faces.length =>
      ((assemblies.get sheet).get position).localTotal - ((assemblies.get sheet).get position).exterior))
    (fun sheet : Fin 2 => (faces.length : Fraction.Rational) * FiniteSum.Fin.sumFin (faceBound sheet)) inner
  have localBound := Hyperelliptic.Meshes.PuncturedGrid.RegularClippedAssembly.LocalBoundaryRequest.assembled_bound
    request later samples left right assemblies
  have locals := FiniteSum.Fin.sumFin_congr (fun sheet : Fin 2 => FiniteSum.Fin.sumFin_congr (fun position : Fin
    faces.length =>
    ((assemblies.get sheet).get position).decomposition.symm))
  rw [locals] at localBound
  have equal :
      FiniteSum.Fin.sumFin (fun sheet : Fin 2 => FiniteSum.Fin.sumFin (fun position : Fin faces.length =>
        ((assemblies.get sheet).get position).exterior)) =
      FiniteSum.Fin.sumFin (fun sheet : Fin 2 => FiniteSum.Fin.sumFin (fun position : Fin faces.length =>
        ((assemblies.get sheet).get position).localTotal)) -
        FiniteSum.Fin.sumFin (fun sheet : Fin 2 => FiniteSum.Fin.sumFin (fun position : Fin faces.length =>
          ((assemblies.get sheet).get position).localTotal - ((assemblies.get sheet).get position).exterior)) := by
    simp only [FiniteSum.Fin.sumFin_sub]
    ring1
  rw [equal]
  exact (Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add localBound errorBound) (by decide))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularClippedErrorBound.LocalBoundaryRequest
