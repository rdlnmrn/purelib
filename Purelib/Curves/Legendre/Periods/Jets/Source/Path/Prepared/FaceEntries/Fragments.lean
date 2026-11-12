module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Query
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells.Comparison.Endpoints
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Comparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Interior
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Integration.Path.Primitive.Cells.Targets
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.Query
import Purelib.Riemann.Integration.PreparedConstantModels.Query
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Readings.UniformPreparedRequests.Query
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames

/-! # Physical fractional Points on one retained regular fragment's original sheet

One operation retains the two physical-patch Points at the literal parent
fractions. A separate operation compares those exact caches through the
supplied lower and retained upper Queries, then acquires two same-model
Entries. Their sheet relations follow from those operational comparisons;
no Point, Query, domain, split or path cache is recovered from a type index.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells (PrimitiveFragmentCell)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells.PrimitiveFragmentCell (RegularRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Geometry.Rectangle (AxisPartition)
open Purelib.Geometry.Rectangle.Partition
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces RegularLocation)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent}
variable {physicalCount floor : Nat}
variable {covered : (patch.neighborhood physicalCount).box.Contains (parent.edge.point 1)}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets original stage}
variable {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
variable {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
variable {bank : BranchCellBank (Fibre.frameCurve frame) branches higher} {faces : PuncturedFaces bank}
variable {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {axes : PrimitiveAxes bank.grid}
variable {cuts : List Rational} {partition : AxisPartition 0 1 cuts}
variable {interval : PreparedAxisPartitions.Interval}

/-- Two independent complete physical Points at one exact fragment's original parent fractions.

Each subtype retains the whole sampleAt result. The tuple has no root
relation or sheet field. Endpoint parameters reuse their old physical
Points; strict parameters acquire genuine new Points on the same patch.
-/
@[expose] def FragmentSamples (prepared : PreparedParent patch physicalCount floor covered targets)
    (fragment : PrimitiveFragmentCell axes parent partition interval) :=
  {value : ContinuedNeighborhood.Point (patch.neighborhood physicalCount) (parent.edge.point interval.lower) //
    value = prepared.sampleAt interval.lower fragment.lower_inside} ×
  {value : ContinuedNeighborhood.Point (patch.neighborhood physicalCount) (parent.edge.point interval.upper) //
    value = prepared.sampleAt interval.upper fragment.upper_inside}

namespace FragmentSamples

/-- Materialize each physical fractional Point once, preserving lower-before-upper order. -/
def build (prepared : PreparedParent patch physicalCount floor covered targets)
    (fragment : PrimitiveFragmentCell axes parent partition interval) : FragmentSamples prepared fragment :=
  let first := prepared.sampleAt interval.lower fragment.lower_inside
  let last := prepared.sampleAt interval.upper fragment.upper_inside
  ⟨⟨first, rfl⟩, ⟨last, rfl⟩⟩

variable {prepared : PreparedParent patch physicalCount floor covered targets}
variable {fragment : PrimitiveFragmentCell axes parent partition interval}
variable (samples : FragmentSamples prepared fragment)

/-- Read the complete retained physical lower Point at the literal original parent fraction. -/
abbrev first : ContinuedNeighborhood.Point (patch.neighborhood physicalCount) (parent.edge.point interval.lower) :=
  samples.1.val

/-- Read the independent physical upper Point without equating repeated coordinates. -/
abbrev last : ContinuedNeighborhood.Point (patch.neighborhood physicalCount) (parent.edge.point interval.upper) :=
  samples.2.val

/-- The whole lower Point is its original sampleAt result on this SAME source parent and fragment. -/
theorem first_eq : samples.first = prepared.sampleAt interval.lower fragment.lower_inside := samples.1.property

/-- The whole upper Point is its independent original sampleAt result. -/
theorem last_eq : samples.last = prepared.sampleAt interval.upper fragment.upper_inside := samples.2.property

/-- The original lower regular endpoint contains the actual parent-fraction coordinate. -/
theorem first_inside (location : RegularLocation faces.regulars fragment.cell) :
    location.face.cell.box.Contains (parent.edge.point interval.lower) :=
  Eq.mp (congrArg location.face.cell.box.Contains fragment.first_eq) (fragment.regular_endpoints location).1

/-- The original upper regular endpoint contains the independent actual upper fraction. -/
theorem last_inside (location : RegularLocation faces.regulars fragment.cell) :
    location.face.cell.box.Contains (parent.edge.point interval.upper) :=
  Eq.mp (congrArg location.face.cell.box.Contains fragment.last_eq) (fragment.regular_endpoints location).2

variable {localCount : Nat} {target : Rational} {request : LocalRequest parent localCount target}
variable {domains : FaceDomainBank frames faces.regulars}
variable {location : RegularLocation faces.regulars fragment.cell}
variable (regular : RegularRequest domains request fragment location) (upper : regular.UpperEndpoint)
variable (query : PreparedEdge.Query parent.edge interval.lower fragment.lower_inside)

/-- Actual Query-to-physical and regular-to-physical comparisons on the same four Point occurrences.

The two products retain both roles of the operational evidence. The first
attaches the supplied crop Query Owners; the second compares independent
regular and physical Points without identifying their primitive constants.
-/
@[expose] def Comparisons :=
  (NamedEquivalent (ownerName query.owner) (ownerName samples.first.owner) ×
    NamedEquivalent (ownerName upper.query.owner) (ownerName samples.last.owner)) ×
  (NamedEquivalent (ownerName regular.sample.owner) (ownerName samples.first.owner) ×
    NamedEquivalent (ownerName upper.sample.owner) (ownerName samples.last.owner))

/-- Compare both Point pairs through the original direct Queries and retain the Query comparisons separately.

The lower request and physical patch consume one supplied lower Query.
The upper side consumes upper.query and its existing queryEquivalent.
All Points, both patches and both Queries keep their own Owners; only
the exact parent rootName at the same fraction is the common middle name.
-/
def queryComparisons : samples.Comparisons regular upper query :=
  let firstPhysical := patch.retainedQueryEquivalent physicalCount interval.lower fragment.lower_inside query rfl
    (sample_inside (frame := frame) (basis := basis) (parent := parent) (patch := patch)
      (count := physicalCount) (covered := covered) fragment.lower_inside) samples.first
  let firstRegular := request.retainedQueryEquivalent interval.lower fragment.lower_inside query fragment.first_eq.symm
    (fragment.request_endpoints request).1 regular.sample
  let lastPhysical := patch.retainedQueryEquivalent physicalCount interval.upper fragment.upper_inside upper.query rfl
    (sample_inside (frame := frame) (basis := basis) (parent := parent) (patch := patch)
      (count := physicalCount) (covered := covered) fragment.upper_inside) samples.last
  let lastRegular := NamedEquivalent.transport upper.query.name_eq.symm rfl upper.queryEquivalent
  let queries := (NamedEquivalent.transport query.name_eq rfl firstPhysical,
    NamedEquivalent.transport upper.query.name_eq rfl lastPhysical)
  let points := (firstRegular.symm.trans firstPhysical, lastRegular.symm.trans lastPhysical)
  ⟨queries, points⟩

/-- Both comparison roles and two actual physical-Owner Entry acquisitions on the SAME old face models.

The samples remain a separate input tuple. This product retains each
whole new acquisition, the complete comparison pair and the derived
old-domain sheet indices. It creates no domain, split or stationary join.
-/
@[expose] def FaceEntries :=
  {values :
      samples.Comparisons regular upper query ×
      Entry.Acquisition regular.compared.shared.models (first_inside location) samples.first.owner ×
      Entry.Acquisition regular.compared.shared.models (last_inside location) samples.last.owner //
    values.1 = samples.queryComparisons regular upper query ∧
    values.2.1 = Entry.Acquisition.build regular.compared.shared.models (first_inside location) samples.first.owner ∧
    values.2.2 = Entry.Acquisition.build regular.compared.shared.models (last_inside location) samples.last.owner ∧
    values.2.1.entry.sheet = regular.compared.acquired.entry.sheet ∧
    values.2.2.entry.sheet = regular.compared.acquired.entry.sheet}

namespace FaceEntries

/-- Retain abstract original comparison/acquisition caches and derive their two actual old-sheet readbacks.

The complete factory equations enter only the retained result predicate.
Sheet uniqueness consumes the supplied actual caches, without reducing a
computed acquisition to recover either Point Owner or endpoint Entry.
-/
private def ofAcquisitions (compared : samples.Comparisons regular upper query)
    (compared_eq : compared = samples.queryComparisons regular upper query)
    (first : Entry.Acquisition regular.compared.shared.models (first_inside location) samples.first.owner)
    (first_eq : first =
      Entry.Acquisition.build regular.compared.shared.models (first_inside location) samples.first.owner)
    (last : Entry.Acquisition regular.compared.shared.models (last_inside location) samples.last.owner)
    (last_eq : last =
      Entry.Acquisition.build regular.compared.shared.models (last_inside location) samples.last.owner) :
    samples.FaceEntries regular upper query :=
  have firstSheet := regular.compared.acquired.entry.sheet_eq_of_equivalent first.entry fragment.first_eq
    compared.2.1 (fragment.regular_endpoints location).1
  have lastSheet := upper.acquired.entry.sheet_eq_of_equivalent last.entry fragment.last_eq
    compared.2.2 (fragment.regular_endpoints location).2
  ⟨⟨compared, first, last⟩, compared_eq, first_eq, last_eq,
    firstSheet.symm, lastSheet.symm.trans upper.sheet_eq.symm⟩

/-- Compare the retained Points, acquire both physical-Owner Entries once, and derive their actual old sheets. -/
def build : samples.FaceEntries regular upper query :=
  let compared := samples.queryComparisons regular upper query
  let first := Entry.Acquisition.build regular.compared.shared.models (first_inside location) samples.first.owner
  let last := Entry.Acquisition.build regular.compared.shared.models (last_inside location) samples.last.owner
  ofAcquisitions samples regular upper query compared rfl first rfl last rfl

variable {samples regular upper query}
variable (entries : samples.FaceEntries regular upper query)

/-- Read the whole retained comparison product, preserving its Query and independent Point roles. -/
abbrev compared : samples.Comparisons regular upper query := entries.val.1

/-- Read actual lower/upper Query-to-physical-Point relations for the SAME separately retained crop. -/
abbrev queries : NamedEquivalent (ownerName query.owner) (ownerName samples.first.owner) ×
    NamedEquivalent (ownerName upper.query.owner) (ownerName samples.last.owner) := entries.compared.1

/-- Read regular-to-physical Point relations without identifying either Point cache or primitive constants. -/
abbrev points : NamedEquivalent (ownerName regular.sample.owner) (ownerName samples.first.owner) ×
    NamedEquivalent (ownerName upper.sample.owner) (ownerName samples.last.owner) := entries.compared.2

/-- Read the complete lower physical-Owner Entry acquisition, including its two paths and selector. -/
abbrev first : Entry.Acquisition regular.compared.shared.models (first_inside location) samples.first.owner :=
  entries.val.2.1

/-- Read the independent upper acquisition on that SAME retained model cache. -/
abbrev last : Entry.Acquisition regular.compared.shared.models (last_inside location) samples.last.owner :=
  entries.val.2.2

/-- The complete comparison pair is the original same-query procedure on those SAME retained Points. -/
theorem compared_eq : entries.compared = samples.queryComparisons regular upper query := entries.property.1

/-- The entire lower acquisition is its original constructor on the actual retained physical Point Owner. -/
theorem first_eq : entries.first =
    Entry.Acquisition.build regular.compared.shared.models (first_inside location) samples.first.owner :=
  entries.property.2.1

/-- The entire upper acquisition is its original constructor on the independent upper physical Point Owner. -/
theorem last_eq : entries.last =
    Entry.Acquisition.build regular.compared.shared.models (last_inside location) samples.last.owner :=
  entries.property.2.2.1

/-- The physical lower Entry selects the original retained lower numerical domain's sheet. -/
theorem first_sheet : entries.first.entry.sheet = regular.compared.acquired.entry.sheet := entries.property.2.2.2.1

/-- The physical upper Entry selects that SAME old domain through the actual retained split's nearest-sign law. -/
theorem last_sheet : entries.last.entry.sheet = regular.compared.acquired.entry.sheet := entries.property.2.2.2.2

end FaceEntries

end FragmentSamples

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent

end
