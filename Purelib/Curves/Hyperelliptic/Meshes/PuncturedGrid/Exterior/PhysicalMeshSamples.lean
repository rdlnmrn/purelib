module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Topology.Polygon.Stokes

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalPerimeterReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.ConjugateIncrementComparison
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.Periods.CenteredBilinearPath
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisSourceCuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalPerimeterCapArc
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Periods.PeriodMatrix
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalPerimeterReadings

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes

open Purelib.Data.Vector

open Purelib.Integration.Path

open Purelib.Riemann.Paths

open Purelib.Riemann.Paths.RectangularPerimeterTraces

open Purelib.Riemann.Periods

open Purelib.Topology.Polygon

public section

/-! Build every exterior occurrence sample from the shared complete-surface
meshes and primitive bank, retaining its trace and owner readings. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshRequest
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics Preflights)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior (PhysicalBasisRequest)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior (PhysicalMeshRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence)
open
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalPerimeterReadings
  (Entries count values original)
open Purelib.Riemann.Paths.RectangularPerimeterTraces (PerimeterTraces)
open Purelib.Riemann.Normalization
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {coarse : (sheet : Fin 2) → RegularMeshes
    domains sheet}
  {fixed : (sheet : Fin 2) →
    Preflights domains sheet}
    {surfaceTarget target : Rational}
  {minimum floor stage depth : Nat} {box : Purelib.Geometry.Rational.Box}
  {basis : PhysicalBasisRequest regular
    domains target minimum floor}
  {initial : TwoSheetRequest coarse fixed
    surfaceTarget}

variable (request : PhysicalMeshRequest
  basis initial)

/-- Select the original retained surface mesh for the indexed basis occurrence and its sheet. -/
@[expose] def mesh (first : Fin genus) (i : Fin (basis.preparations.get first).occurrences.length) :=
  let occurrence := (basis.preparations.get first).occurrences[i.val]'i.isLt
  (request.surface.entries.get occurrence.sideOccurrence.sheet).meshes.entries.get occurrence.sideOccurrence.position

set_option genInjectivity false in
/-- The shared physical perimeter readings for one original basis occurrence and ordered row pair.

The retained perimeter traces belong to the occurrence's exact surface mesh, and the readings use both original
numerical row caches on its selected side. -/
structure OccurrenceReadings (cache : RegularMeshes.Numerics domains stage) (first second : Fin genus)
    (i : Fin (basis.preparations.get first).occurrences.length) where
  /-- The retained complete perimeter traces of the occurrence's original surface mesh. -/ traces :
    RectangularPerimeterTraces.PerimeterTraces (request.mesh first i)
  /-- The shared original row-pair readings on the occurrence's selected perimeter side. -/ readings :
    SharedPhysicalPerimeterReadings.Entries
    (occurrence := (basis.preparations.get first).occurrences[i.val]'i.isLt)
    traces (cache.get first) (cache.get second)
    ((basis.preparations.get first).occurrences[i.val]'i.isLt).sideOccurrence.side

constructive_injectivity OccurrenceReadings

namespace OccurrenceReadings

/-- Cache the original occurrence's perimeter traces and shared row-pair readings on its retained mesh. -/
@[expose] def build (cache : RegularMeshes.Numerics domains stage) (first second : Fin genus)
    (i : Fin (basis.preparations.get first).occurrences.length) : request.OccurrenceReadings cache first second i :=
  let traces := PerimeterTraces.build (request.mesh first i)
  ⟨traces, SharedPhysicalPerimeterReadings.build
    (occurrence := (basis.preparations.get first).occurrences[i.val]'i.isLt)
    traces (cache.get first) (cache.get second) _⟩

variable {request} {cache : Numerics
  domains stage} {first second : Fin genus}
  {i : Fin (basis.preparations.get first).occurrences.length}
  (entry : request.OccurrenceReadings cache first second i)

/-- Read the physical step count of the original occurrence's selected perimeter side. -/
@[expose] def count : Nat := SharedPhysicalPerimeterReadings.count entry.traces
  ((basis.preparations.get first).occurrences[i.val]'i.isLt).sideOccurrence.side

/-- Read the original ordered row-pair values at every retained physical side vertex. -/
@[expose] def values : Fin (entry.count + 1) → Stokes.PrimitivePoint :=
  SharedPhysicalPerimeterReadings.values
    (occurrence := (basis.preparations.get first).occurrences[i.val]'i.isLt)
    entry.traces (cache.get first) (cache.get second)
    ((basis.preparations.get first).occurrences[i.val]'i.isLt).sideOccurrence.side

/-- Read the cached centered bilinear sample on the exact original physical side values. -/
@[expose] def original : CenteredBilinearPath.Sample
    (fun vertex => ConjugateIncrementComparison.conjugateFirst (entry.values vertex)) :=
  SharedPhysicalPerimeterReadings.original entry.traces entry.readings

end OccurrenceReadings

/-- The complete dependent bank of original occurrence readings, indexed by both basis rows and each retained
occurrence. -/
@[expose] def Readings (cache : RegularMeshes.Numerics domains stage) :=
  Data.Vector.DependentVector (fun first : Fin genus => Data.Vector.DependentVector (fun second : Fin genus =>
    Data.Vector.DependentVector (fun i : Fin (basis.preparations.get first).occurrences.length =>
      request.OccurrenceReadings cache first second i)))

/-- Build the complete dependent bank of original occurrence readings from the shared numerical cache. -/
@[expose] def readings (cache : RegularMeshes.Numerics domains stage) : request.Readings cache :=
  DependentVector.ofFn fun first => DependentVector.ofFn fun second =>
    DependentVector.ofFn fun i =>
      OccurrenceReadings.build
      request cache first second i

namespace Readings
variable {request} {cache : Numerics
  domains stage} (entries : request.Readings cache)

/-- Read every original physical step count from the retained occurrence bank. -/
@[expose] def counts : basis.Counts := fun first second i => (((entries.get first).get second).get i).count

/-- Read every original physical value sequence from the retained occurrence bank. -/
@[expose] def values : basis.Values entries.counts := fun first second i => (((entries.get first).get second).get
  i).values

/-- Retain each cached centered area; do not resample to assemble the matrix. -/
@[expose] def samples : basis.Samples entries.values :=
  DependentVector.ofFn fun first => DependentVector.ofFn fun second =>
    DependentVector.ofFn fun i => (((entries.get first).get second).get i).original

end Readings
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshRequest
