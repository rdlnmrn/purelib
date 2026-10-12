module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisSourceCuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisAggregate
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalArcAggregation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshPerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPhysicalComponents
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.Dyadic.RadialTriangles
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshReindex
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisEnergy
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ConjugateFacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisAccuracy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring

public section

/-! Transfer the regular cap bound to the actual physical perimeter energy.
The signed difference between cap and physical endpoint chords stays explicit. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshRequest

open Purelib.Algebra
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib
open Purelib.Geometry
open Purelib.Integration
open Purelib.Riemann

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {fixed : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains
    sheet} {surfaceTarget target : Fraction.Rational}
  {minimum floor stage depth coarseDepth : Nat} {box : Rational.Box}
  {basis : PhysicalBasisRequest regular domains target
    minimum floor}
  {previous : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains} (selected :
    BasisSourceCuts basis.preparations previous)
  {initial : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest (fun sheet =>
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains selected.cuts sheet coarseDepth)
    fixed surfaceTarget}
  {request : PhysicalMeshRequest basis initial} {cache :
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage}
  {polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap stage box}

section PhysicalMeshRequest

namespace Readings
variable (entries : request.Readings cache) (retained : request.Perimeters cache)
  (evaluated : basis.Evaluations polynomials depth)
  (later : request.index ≤ stage) (spatial : basis.depth ≤ depth)

/-- Each assembled basis-row pair reads the full retained perimeter area plus its original endpoint correction. -/
theorem assembled_pair (first second : Fin genus) :
    (((entries.assemble selected evaluated later spatial).get first).get second).correctedArea =
      retained.area first second + entries.endpointCorrection polynomials first second := by
  let pair := fun first second =>
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisSamples.PhysicalBasisArcSample.ofSamples
    (basis.preparations.get first) ((basis.entries.get first).get second)
    (basis.pieceCounts first second) ((basis.schedules.get first).get second)
    ((evaluated.get first).get second) ((basis.depth_ge first second).trans spatial)
    (entries.counts first second) (entries.values first second)
    ((entries.samples.get first).get second) (entries.accurate selected evaluated later spatial first second)
  have outer := Data.Vector.DependentVector.ofFn_get
    (fun first => Data.Vector.DependentVector.ofFn fun second => pair first second) first
  have inner := Data.Vector.DependentVector.ofFn_get (fun second => pair first second) second
  have readback := (congrArg (fun row => (row.get second).correctedArea) outer).trans
    (congrArg (fun sample => sample.correctedArea) inner)
  apply readback.trans
  change FiniteSum.Fin.sumFin (fun i =>
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalArcAggregation.physicalArcValue ((basis.preparations.get
    first).occurrences[i.val]'i.isLt)
    (polynomials.get first) (polynomials.get second)
    (((entries.samples.get first).get second).get i).centeredArea) = _
  unfold Perimeters.area
    endpointCorrection
  rw [← FiniteSum.Fin.sumFin_add]
  apply FiniteSum.Fin.sumFin_congr
  intro i
  have equal := (((entries.get first).get second).get i).corrected_area
    (((retained.get first).get second).get i) polynomials
  simpa only [samples,
    Data.Vector.DependentVector.ofFn_get, -eq_self, -iff_self] using equal

end Readings

namespace Perimeters
variable {selected}

/-- Form the conjugate coefficient-weighted double sum of the retained physical perimeter areas. -/
@[expose] def energy (retained : request.Perimeters cache) (coefficients :
  LinearAlgebra.Gaussian.Energy.GaussianVector genus) : Gaussian :=
  FiniteSum.Fin.sumFin fun first => FiniteSum.Fin.sumFin fun second => Data.Gaussian.Basic.conj (coefficients first)
    * coefficients second * retained.area first second

end Perimeters

namespace FacePerimeterBank
variable {selected}

/-- Form the conjugate coefficient-weighted exterior component energy selected by the original face-neighbor
classification. -/
@[expose] def componentEnergy (faces : request.FacePerimeterBank cache)
    (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank base.faces) (coefficients :
      LinearAlgebra.Gaussian.Energy.GaussianVector genus) : Gaussian :=
  FiniteSum.Fin.sumFin fun first => FiniteSum.Fin.sumFin fun second => Data.Gaussian.Basic.conj (coefficients first)
    * coefficients second *
    Hyperelliptic.Meshes.PuncturedGrid.SelectedPhysicalComponents.componentEvaluation neighbors (fun _ => true)
      (fun side position => FiniteSum.Fin.sumFin (fun sheet => ((faces.get first).get second).area position sheet side))
        .exterior

/-- Reindexing the retained face perimeters by their original occurrences preserves the full exterior component energy.
-/
theorem occurrences_energy (faces : request.FacePerimeterBank cache)
    (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank base.faces) (coefficients :
      LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    faces.occurrences.energy coefficients = faces.componentEnergy neighbors coefficients := by
  unfold Perimeters.energy
    componentEnergy
  apply FiniteSum.Fin.sumFin_congr
  intro first
  apply FiniteSum.Fin.sumFin_congr
  intro second
  exact congrArg (fun value => Data.Gaussian.Basic.conj (coefficients first) * coefficients second * value)
    (faces.area_eq_component neighbors first second)

end FacePerimeterBank

namespace Readings
variable {selected}

/-- Form the conjugate coefficient-weighted sum of the retained cap-versus-physical endpoint corrections. -/
@[expose] def endpointEnergy (entries : request.Readings cache) (polynomials :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap stage box)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) : Gaussian :=
  FiniteSum.Fin.sumFin fun first => FiniteSum.Fin.sumFin fun second => Data.Gaussian.Basic.conj (coefficients first)
    * coefficients second *
    entries.endpointCorrection polynomials first second

variable (selected)

/-- The assembled physical basis energy equals the retained perimeter energy plus its exact endpoint correction. -/
theorem assembled_energy (entries : request.Readings cache) (retained : request.Perimeters cache)
    (evaluated : basis.Evaluations polynomials depth)
    (later : request.index ≤ stage) (spatial : basis.depth ≤ depth)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    (entries.assemble selected evaluated later spatial).energy coefficients =
      retained.energy coefficients + entries.endpointEnergy polynomials coefficients := by
  unfold Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisSamples.PhysicalBasisArcSamples.energy
    Perimeters.energy
    endpointEnergy
  rw [← FiniteSum.Fin.sumFin_add]
  apply FiniteSum.Fin.sumFin_congr
  intro first
  rw [← FiniteSum.Fin.sumFin_add]
  apply FiniteSum.Fin.sumFin_congr
  intro second
  rw [entries.assembled_pair selected retained evaluated later spatial first second]
  ring1

variable {prepared :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential}
  (attached : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment prepared)
  {bounds : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds.RegularBasisBounds polynomials}
  {capTarget : Fraction.Rational} {capMinimum : Nat}
  (capRequest : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest.RegularBasisRequest bounds
    attached.caps.length capTarget capMinimum)
  {geometry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry
    attached}
  {parameters : Path.Dyadic.RadialTriangles.Parameters capRequest.depth}

/-- Bound the actual complete perimeter plus its exact endpoint correction.
No physical or cap chord is silently identified with zero or with the other. -/
theorem perimeter_energy_upper (entries : request.Readings cache) (retained : request.Perimeters cache)
    (evaluated : basis.Evaluations polynomials capRequest.depth)
    (later : request.index ≤ stage) (spatial : basis.depth ≤ capRequest.depth)
    (caps : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisAggregate.RegularBasisCap geometry parameters
      polynomials)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (capSample : (capRequest.certify caps).Evaluation coefficients)
    (allowance : Fraction.Rational) (nonnegative : 0 ≤ allowance)
    (paid : (genus : Fraction.Rational) ^ 2 * target ≤ 16 * allowance ^ 2) :
    (retained.energy coefficients + entries.endpointEnergy polynomials coefficients).im / 4 ≤
      (capTarget + allowance) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := by
  have bound := Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisEnergy.PhysicalBasisArcSamples.energy_upper
    attached capRequest caps coefficients capSample
    (entries.assemble selected evaluated later spatial) allowance nonnegative paid
  rw [entries.assembled_energy selected retained evaluated later spatial coefficients] at bound
  exact bound

/-- The same upper bound now names the original face-neighbor exterior
component, with the retained endpoint correction still displayed. -/
theorem component_energy_upper (entries : request.Readings cache) (faces : request.FacePerimeterBank cache)
    (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank base.faces)
    (evaluated : basis.Evaluations polynomials capRequest.depth)
    (later : request.index ≤ stage) (spatial : basis.depth ≤ capRequest.depth)
    (caps : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisAggregate.RegularBasisCap geometry parameters
      polynomials)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (capSample : (capRequest.certify caps).Evaluation coefficients)
    (allowance : Fraction.Rational) (nonnegative : 0 ≤ allowance)
    (paid : (genus : Fraction.Rational) ^ 2 * target ≤ 16 * allowance ^ 2) :
    (faces.componentEnergy neighbors coefficients + entries.endpointEnergy polynomials coefficients).im / 4 ≤
      (capTarget + allowance) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := by
  have bound := entries.perimeter_energy_upper selected attached capRequest faces.occurrences
    evaluated later spatial caps coefficients capSample allowance nonnegative paid
  rw [faces.occurrences_energy neighbors coefficients] at bound
  exact bound

end Readings
end PhysicalMeshRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshRequest
