module
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisSourceCuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalArcAggregation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalPerimeterCapArc
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshSamples
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalSourceRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.ConjugateIncrementComparison
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Periods.PeriodMatrix

public section

/-! Certify the actual shared perimeter samples using their scheduled source
owners, retained common cuts, and automatically selected refinement bounds. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshRequest

open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib
open Purelib.Geometry
open Purelib.Riemann

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {fixed : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains
    sheet} {surfaceTarget target : Fraction.Rational}
  {minimum floor stage depth coarseDepth : Nat} {box : Rational.Box}
  {basis : PhysicalBasisRequest regular domains target
    minimum floor}
  {previous : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains}
  (selected : BasisSourceCuts basis.preparations previous)
  {initial : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest (fun sheet =>
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains selected.cuts sheet coarseDepth)
    fixed surfaceTarget}
  {request : PhysicalMeshRequest basis initial} {cache :
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage}
  {polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap stage box}

namespace OccurrenceReadings

/-- The retained physical occurrence sample meets its scheduled cap-arc error allowance.

The supplied source evaluation is taken after the retained owner stage and at sufficient spatial depth; its common-cut
source bank pays the existing physical sample without reacquiring it. -/
theorem accurate {first second : Fin genus}
    {i : Fin (basis.preparations.get first).occurrences.length}
    (entry : request.OccurrenceReadings cache first second i)
    (evaluated : basis.Evaluations polynomials depth)
    (later : request.index ≤ stage) (spatial : basis.depth ≤ depth) :
    Data.Gaussian.Norm.Basic.normSq
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalArcAggregation.physicalArcError ((basis.preparations.get
      first).occurrences[i.val]'i.isLt)
      (polynomials.get first) (polynomials.get second) depth entry.original.centeredArea) <
      ((basis.entries.get first).get second).allowance := by
  let occurrence := (basis.preparations.get first).occurrences[i.val]'i.isLt
  let schedule := (basis.schedules.get first).get second
  let prepared := (schedule.entries.get i).sources
  let source := ((evaluated.get first).get second).get i
  let sources := Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry.sourceBank
    (selected.select first) (List.getElem_mem i.isLt)
    request.surface source
  have ownerLater := (schedule.owner_ge i).trans
    ((basis.index_ge first second).trans (request.basis_le.trans later))
  have sourceLater := (Data.Nat.Order.le_max_left _ _).trans ((schedule.source_ge i).trans
    ((basis.index_ge first second).trans (request.basis_le.trans later)))
  have depthEq : schedule.physicalDepth = (request.mesh first i).depth :=
    (basis.physicalDepth_eq first second).trans (request.depth_eq.symm.trans
      (request.surface.mesh_depth occurrence.sideOccurrence.sheet occurrence.sideOccurrence.position).symm)
  have bound :=
    SharedPhysicalPerimeterCapArc.SharedPhysicalPerimeterReadings.cap_accurate
    entry.traces rfl rfl entry.readings
    ((basis.entries.get first).get second).positive (request.pieceCounts_eq first second i) depthEq
    (schedule.entries.get i).budget (schedule.owners.get i) ownerLater prepared sources sourceLater
    (schedule.entries.get i).refinement (schedule.physical_refined i)
    (schedule.source_refined ((basis.depth_ge first second).trans spatial) i) (le_refl _)
  rw [schedule.arc_depth ((basis.depth_ge first second).trans spatial) i] at bound
  exact bound

end OccurrenceReadings

namespace Readings

/-- All retained physical occurrence readings meet the original basis accuracy request at the supplied later stage and
depth. -/
theorem accurate (entries : request.Readings cache)
    (evaluated : basis.Evaluations polynomials depth)
    (later : request.index ≤ stage) (spatial : basis.depth ≤ depth) :
    basis.Accurate polynomials depth entries.samples := by
  intro first second i
  have bound := (((entries.get first).get second).get i).accurate selected evaluated later spatial
  simpa only [samples,
    Data.Vector.DependentVector.ofFn_get, -eq_self, -iff_self] using bound

/-- Assemble the physical basis matrix with internally proved occurrence
accuracy, using the already retained samples and query-refined source bank. -/
@[expose] def assemble (entries : request.Readings cache)
    (evaluated : basis.Evaluations polynomials depth)
    (later : request.index ≤ stage) (spatial : basis.depth ≤ depth) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisSamples.PhysicalBasisArcSamples (regular := regular)
      (domains := domains) polynomials target minimum floor depth :=
  PhysicalBasisRequest.assemble
    basis polynomials evaluated spatial entries.counts entries.values entries.samples
    (entries.accurate selected evaluated later spatial)

end Readings
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshRequest
