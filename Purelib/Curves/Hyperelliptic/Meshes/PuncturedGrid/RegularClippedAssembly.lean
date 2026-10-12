module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBilinearAssembly
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryBound
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
public import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.Readings.RectangularBoundaryTranslations
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryRequest
import Mathlib.Algebra.Ring.Defs
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
import Purelib.Geometry.Rational.Box.Sample
import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
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
import Purelib.Tactic.Ring

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Riemann

open Purelib.RootIsolation

@[expose] public section

/-! The requested local bound applies to the cached exterior and all seam
terms of the actual clipped, owner-dependent face boundaries. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularClippedAssembly

attribute [local congr] FiniteSum.Fin.sumFin_congr

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryRequest.LocalBoundaryRequest (bound)
open Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh.ClippedAssembly

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {faces : List (Meshes.PuncturedGridFaces.RegularFace
      bank)}
    {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces}
  {coarse : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes domains sheet}
  {fixed : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains
    sheet} {target : Fraction.Rational}

namespace TwoSheetRequest

variable {energyTarget : Fraction.Rational}

/-- The actual clipped assembly of homogeneous primitive readings on one original sheet and face observation mesh. -/
abbrev FaceAssembly (energy : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest coarse fixed
  energyTarget) {stage : Nat} (cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics
  domains stage)
    (left right : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (sheet : Fin 2) (position : Fin
      faces.length) :=
  Readings.RectangularObservationAssembly.ObservationMesh.ClippedAssembly ((energy.entries.get sheet).meshes.entries.get
    position)
    (fun column row point =>
      ⟨sumFin (fun i => left i * (cache.atDomain position sheet i).anchors.alignedValue (cache.atDomain position sheet
        i).offsets column row point),
        FiniteSum.Fin.sumFin (fun j => right j * (cache.atDomain position sheet j).anchors.alignedValue (cache.atDomain
          position sheet j).offsets column row point)⟩)

/-- The retained clipped assemblies for every original face on both sheets. -/
abbrev Assemblies (energy : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest coarse fixed
  energyTarget) {stage : Nat} (cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics
  domains stage)
    (left right : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :=
  Data.Vector.DependentVector (fun sheet : Fin 2 => Data.Vector.DependentVector (fun position : Fin faces.length =>
    Hyperelliptic.Meshes.PuncturedGrid.RegularClippedAssembly.TwoSheetRequest.FaceAssembly energy cache left right sheet
      position))

/-- Build the actual clipped assemblies from the shared original primitive cache and coefficient vectors. -/
def assemblies (energy : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest coarse fixed
  energyTarget) {stage : Nat} (cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics
  domains stage)
    (left right : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
      Hyperelliptic.Meshes.PuncturedGrid.RegularClippedAssembly.TwoSheetRequest.Assemblies energy cache left right :=
  Data.Vector.DependentVector.ofFn fun sheet : Fin 2 => Data.Vector.DependentVector.ofFn fun position : Fin faces.length
    =>
    Readings.RectangularObservationAssembly.ObservationMesh.ClippedAssembly.build
      ((energy.entries.get sheet).meshes.entries.get position)
      (fun column row point =>
        ⟨sumFin (fun i => left i * (cache.atDomain position sheet i).anchors.alignedValue (cache.atDomain position sheet
          i).offsets column row point),
          FiniteSum.Fin.sumFin (fun j => right j * (cache.atDomain position sheet j).anchors.alignedValue
            (cache.atDomain position sheet j).offsets column row point)⟩)

/-- The same energy request controls the actual weighted corner polygons on
both sheets, with all basis pairs and clipped junctions included. -/
theorem FaceAssembly.corner_bound {energy : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest
  coarse fixed energyTarget}
    {stage : Nat} {cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage}
    {left right : LinearAlgebra.Gaussian.Energy.GaussianVector genus} {sheet : Fin 2} {position : Fin
      faces.length}
    (later : energy.index ≤ stage) (assembly :
      Hyperelliptic.Meshes.PuncturedGrid.RegularClippedAssembly.TwoSheetRequest.FaceAssembly energy cache left right
      sheet position) :
    let mesh := (energy.entries.get sheet).meshes.entries.get position
    let entry := (energy.entries.get sheet).entries.get position
    Data.Gaussian.Norm.Basic.normSq assembly.cornerTotal ≤
      ((genus : Fraction.Rational) * (genus : Fraction.Rational)) *
        Readings.PreparedObservationCoercivity.coefficientNormSq left *
          Readings.PreparedObservationCoercivity.coefficientNormSq right *
        (256 * ((mesh.boundaryColumns : Fraction.Rational) * (mesh.boundaryRows : Fraction.Rational)) ^ 2 *
          entry.readingTarget ^ 2) := by
  have scalar :=
    Hyperelliptic.Meshes.PuncturedGrid.DomainBilinearAssembly.EnergyPreflight.Request.weighted_clipped_cornerTotal_bound
    ((energy.entries.get sheet).entries.get position).modelRequest
    (((energy.entries.get sheet).index_ge position).trans ((energy.index_ge sheet).trans later))
    (cache.atDomain position sheet) left right assembly
  have leftNorm := FiniteSum.Fin.sumFin_congr
    (fun row : Fin genus => Gaussian.Norm.Basic.normSq_eq_canonical (left row))
  have rightNorm := FiniteSum.Fin.sumFin_congr
    (fun row : Fin genus => Gaussian.Norm.Basic.normSq_eq_canonical (right row))
  rw [leftNorm, rightNorm] at scalar
  simpa only [Readings.PreparedObservationCoercivity.coefficientNormSq] using scalar

/-- The original local boundary equals its actual clipped exterior, seam and corner contributions, including the
retained primitive translations. -/
theorem FaceAssembly.local_eq {energy : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest
  coarse fixed energyTarget} {stage : Nat} {cache :
  Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage}
    {left right : LinearAlgebra.Gaussian.Energy.GaussianVector genus} {sheet : Fin 2} {position : Fin
      faces.length}
    (assembly : Hyperelliptic.Meshes.PuncturedGrid.RegularClippedAssembly.TwoSheetRequest.FaceAssembly energy cache left
      right sheet position) :
    Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryBound.localBoundary (energy := energy)
      cache left right sheet position = assembly.exterior + assembly.seams + assembly.cornerTotal :=
by
  let mesh := (energy.entries.get sheet).meshes.entries.get position
  let raw := fun column row point =>
    (⟨sumFin (fun i : Fin genus => left i * (cache.atDomain position sheet i).primitives.value column row point),
      FiniteSum.Fin.sumFin (fun j : Fin genus => right j * (cache.atDomain position sheet j).primitives.value column row
        point)⟩ : Topology.Polygon.Stokes.PrimitivePoint)
  let aligned := fun column row point =>
    (⟨sumFin (fun i : Fin genus => left i * (cache.atDomain position sheet i).anchors.alignedValue
        (cache.atDomain position sheet i).offsets column row point),
      FiniteSum.Fin.sumFin (fun j : Fin genus => right j * (cache.atDomain position sheet j).anchors.alignedValue
        (cache.atDomain position sheet j).offsets column row point)⟩ : Topology.Polygon.Stokes.PrimitivePoint)
  let offsets := fun column row =>
    (⟨sumFin (fun i : Fin genus => left i * (cache.atDomain position sheet i).offsets.values column row),
      FiniteSum.Fin.sumFin (fun j : Fin genus => right j * (cache.atDomain position sheet j).offsets.values column row)⟩
        : Topology.Polygon.Stokes.PrimitivePoint)
  have translated : mesh.pieces.localBoundary aligned mesh.depth = mesh.pieces.localBoundary raw mesh.depth := by
    apply mesh.pieces.localBoundary_eq_of_translation raw aligned offsets
    intro column row point
    dsimp only [raw, aligned, offsets]
    simp only [Integration.RectangularPrimitiveGluing.PrimitiveAnchors.alignedValue,
      mul_add, FiniteSum.Fin.sumFin_add, Topology.Polygon.Stokes.PrimitivePoint.add]
    congr 1 <;> ring1
  exact translated.symm.trans (assembly.localTotal_eq.symm.trans assembly.decomposition)

end TwoSheetRequest

namespace LocalBoundaryRequest

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryRequest.LocalBoundaryRequest in
/-- The retained local-boundary request bounds the sum of the actual exterior, seam and corner contributions on both
sheets with the original coefficient factor. -/
theorem assembled_bound (request : Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryRequest.LocalBoundaryRequest
  coarse fixed target) {stage : Nat} {cache :
  Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage}
    (later : request.ownership.index ≤ stage) (samples :
      Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest.Samples request.energy cache)
    (left right : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (assemblies :
      Hyperelliptic.Meshes.PuncturedGrid.RegularClippedAssembly.TwoSheetRequest.Assemblies request.energy cache left
      right) :
    Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun sheet : Fin 2 => FiniteSum.Fin.sumFin (fun position :
      Fin faces.length =>
      ((assemblies.get sheet).get position).exterior + ((assemblies.get sheet).get position).seams +
        ((assemblies.get sheet).get position).cornerTotal))) ≤
      Readings.PreparedObservationCoercivity.coefficientNormSq left *
        Readings.PreparedObservationCoercivity.coefficientNormSq right * target := by
  have bound := Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryRequest.LocalBoundaryRequest.bound
    request later samples left right
  have equal := FiniteSum.Fin.sumFin_congr (fun sheet : Fin 2 => FiniteSum.Fin.sumFin_congr (fun position : Fin
    faces.length =>
    Hyperelliptic.Meshes.PuncturedGrid.RegularClippedAssembly.TwoSheetRequest.FaceAssembly.local_eq ((assemblies.get
      sheet).get position)))
  rw [equal] at bound
  exact bound

end LocalBoundaryRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularClippedAssembly
