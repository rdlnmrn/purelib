module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateArcFamily
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalArcAggregation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Readings.RectangularObservationAssembly
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshSamples
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalPerimeterReadback
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Integration.Path.ConjugateIncrementComparison
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.RectangularStitchedPerimeter
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Tactic.Ring

public section

/-! Read physical samples back to their complete retained perimeters, keeping
both the physical endpoint subtraction and the cap endpoint restoration. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshRequest

open Purelib.Algebra
open Purelib.Curves
open Purelib.Data.Rat
open Purelib
open Purelib.Geometry
open Purelib.Riemann

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalPerimeterReadback
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateArcFamily

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {coarse : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes domains sheet}
  {fixed : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains
    sheet} {surfaceTarget target : Fraction.Rational}
  {minimum floor stage : Nat} {box : Rational.Box}
  {basis : PhysicalBasisRequest regular domains target
    minimum floor}
  {initial : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest coarse fixed surfaceTarget}

variable (request : PhysicalMeshRequest basis initial)

set_option genInjectivity false in
/-- A perimeter assembled from the same mesh and shared primitive values as
its physical sample. Existing assemblies can be supplied directly. -/
structure OccurrencePerimeter (cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics
  domains stage) (first second : Fin genus)
    (i : Fin (basis.preparations.get first).occurrences.length) where
  /-- The retained clipped assembly uses the original occurrence mesh and its shared primitive values. -/ assembly :
    Readings.RectangularObservationAssembly.ObservationMesh.ClippedAssembly (request.mesh first i)

      (SharedPhysicalPerimeterReadback.SharedPhysicalPerimeterReadings.gridValues
      (occurrence := (basis.preparations.get first).occurrences[i.val]'i.isLt)
      (cache.get first) (cache.get second))
  /-- The complete perimeter of that same retained clipped assembly. -/ perimeter : assembly.Perimeter

constructive_injectivity OccurrencePerimeter

namespace OccurrencePerimeter

variable {request} {cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage}
  {first second : Fin genus}
  {i : Fin (basis.preparations.get first).occurrences.length}

/-- Read the retained perimeter area on the side selected by its original surface occurrence. -/
@[expose] def area (retained : request.OccurrencePerimeter cache first second i) : Gaussian :=
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalPerimeterReadback.SharedPhysicalPerimeterReadings.sideArea
    retained.perimeter
    ((basis.preparations.get first).occurrences[i.val]'i.isLt).sideOccurrence.side

end OccurrencePerimeter

namespace OccurrenceReadings
variable {request} {cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage}
  {first second : Fin genus}
  {i : Fin (basis.preparations.get first).occurrences.length}
  (entry : request.OccurrenceReadings cache first second i)

/-- This is the complete physical side, before subtracting its endpoint chord. -/
theorem centered_add_endpoint (retained : request.OccurrencePerimeter cache first second i) :
    entry.original.centeredArea + entry.original.endpoint = retained.area :=

    SharedPhysicalPerimeterReadback.SharedPhysicalPerimeterReadings.centered_add_endpoint
    entry.traces entry.readings retained.assembly retained.perimeter

/-- The cap restoration uses cap values, not physical endpoint values. -/
@[expose] def endpointCorrection (polynomials :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap stage box) : Gaussian :=
  let occurrence := (basis.preparations.get first).occurrences[i.val]'i.isLt
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateArcFamily.PairedArcRequest.conjugateChordValue occurrence
    (polynomials.get first) (polynomials.get second) -
    (if occurrence.sourceForward then entry.original.endpoint else -entry.original.endpoint)

/-- The physical arc value equals its oriented full perimeter area plus the original cap endpoint correction. -/
theorem corrected_area (retained : request.OccurrencePerimeter cache first second i)
    (polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap stage box) :
    let occurrence := (basis.preparations.get first).occurrences[i.val]'i.isLt
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalArcAggregation.physicalArcValue occurrence (polynomials.get
      first) (polynomials.get second) entry.original.centeredArea =
      (if occurrence.sourceForward then retained.area else -retained.area) + entry.endpointCorrection polynomials := by
  intro occurrence
  change Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalArcAggregation.physicalArcValue occurrence (polynomials.get
    first) (polynomials.get second) entry.original.centeredArea =
    (if occurrence.sourceForward then retained.area else -retained.area) +
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateArcFamily.PairedArcRequest.conjugateChordValue occurrence
        (polynomials.get first) (polynomials.get second) -
        (if occurrence.sourceForward then entry.original.endpoint else -entry.original.endpoint))
  have decomposition := entry.centered_add_endpoint retained
  rw [← decomposition]
  cases direction : occurrence.sourceForward <;>
    simp only [Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalArcAggregation.physicalArcValue, direction, if_pos
      (rfl : true = true), if_neg (by decide : false ≠ true), -eq_self, -iff_self] <;> ring1

end OccurrenceReadings

/-- A perimeter retained for every basis-row pair and original occurrence.

Each dependent entry uses the same mesh and shared primitive values as its physical sample. -/
@[expose] def Perimeters (cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains
  stage) :=
  Data.Vector.DependentVector (fun first : Fin genus => Data.Vector.DependentVector (fun second : Fin genus =>
    Data.Vector.DependentVector (fun i : Fin (basis.preparations.get first).occurrences.length =>
      request.OccurrencePerimeter cache first second i)))

namespace Readings
variable {request} {cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage}
  (entries : request.Readings cache)

/-- Sum the retained cap-versus-physical endpoint corrections for one original pair of basis rows. -/
@[expose] def endpointCorrection (polynomials :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap stage box) (first second : Fin
  genus) : Gaussian :=
  FiniteSum.Fin.sumFin fun i => (((entries.get first).get second).get i).endpointCorrection polynomials

end Readings

namespace Perimeters
variable {request} {cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage}
  (retained : request.Perimeters cache)

/-- Sum the retained physical perimeter areas with the directions of their original source occurrences. -/
@[expose] def area (first second : Fin genus) : Gaussian := FiniteSum.Fin.sumFin fun i =>
  let occurrence := (basis.preparations.get first).occurrences[i.val]'i.isLt
  let value := (((retained.get first).get second).get i).area
  if occurrence.sourceForward then value else -value

end Perimeters
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshRequest
