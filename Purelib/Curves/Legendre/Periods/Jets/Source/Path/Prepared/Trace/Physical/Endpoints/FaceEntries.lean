module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Physical.Endpoints
public import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.Parents.Grid.Endpoints
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells.Comparison.Endpoints
import Purelib.Approximation.AccuracyRequest
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Comparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Interior
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Legendre.Periods.Jets.Source.Row
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedConstantModels.Query
import Purelib.Riemann.Readings.UniformPreparedRequests.Query
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Spine
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames

/-! # Physical endpoint Points on their original regular-request sheets

The SAME retained endpoint Queries compare the distinct original Point
Owners. Their exact endpoint roles identify the original parent fractions;
clear-face Entry uniqueness derives the shared sheet without a new join,
Point, Query, face acquisition or primitive-domain preparation.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical.Comparison

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells (PrimitiveFragmentCell)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularLocation)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {ambient : Geometry.Rational.Box} {start finish : Canonical}
variable {segment : ClearSegment (Paths.polynomial parameter) ambient start finish} {within : segment.WithinAmbient}
variable {sourceOwner : Owner ((Paths.polynomial parameter).eval start)} {widthRequest : AccuracyRequest}
variable {count floor : Nat} {sheet : Fin 2}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets original stage} {accuracy : AccuracyRequest} {row : Row}
variable {retained : Acquisition.Segment (segment := segment) (within := within) (owner := sourceOwner) widthRequest}
variable {parents : Acquisition.Segment.Parents (curve := Fibre.frameCurve frame) basis sheet count retained}
variable {prepared : PreparedParents (frame := frame) (basis := basis) parents.coveredParents floor targets}
variable {allocation : targets.endpoint = 4 * accuracy.tolerance}
variable {observed : Primitive.Spine (row.expression parameter) accuracy retained.traced.trace.get}
variable (compared : Physical.Comparison (frame := frame) (basis := basis) (count := count) (floor := floor)
  (sheet := sheet) row retained parents prepared allocation observed)
variable (index : Fin parents.covered.parents.length)
variable (firstQuery : PreparedEdge.Query (parents.covered.parents[index.val]'index.isLt).edge 0
  (parents.covered.parents[index.val]'index.isLt).edge.baseInside)
variable (lastQuery : PreparedEdge.Query (parents.covered.parents[index.val]'index.isLt).edge
  1 (of_decide_eq_true rfl))

namespace EndpointPoints

variable {compared index firstQuery lastQuery}
variable (kept : EndpointPoints (frame := frame) (basis := basis) compared index firstQuery lastQuery)
variable {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
variable {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
variable {base : FramedPuncturedGrid (Fibre.frameCurve frame) branches higher}
variable {axes : PrimitiveAxes base.bank.grid}
variable {first : (Cuts.Ambient (Fibre.frameCurve frame)).Contains start}
variable {last : (Cuts.Ambient (Fibre.frameCurve frame)).Contains finish}
variable {grid : Acquisition.Segment.Parents.GridFragments base axes parents first last}
variable {frames : RootFrames base.bank.grid} {domains : FaceDomainBank frames base.faces.regulars}
variable {requestCount : Nat} {target : Rational}
variable {request : LocalRequest (parents.covered.parents[index.val]'index.isLt) requestCount target}

section First

variable (located : grid.Endpoint index false)
variable {location : RegularLocation base.faces.regulars located.fragment.cell}
variable (regular : PrimitiveFragmentCell.RegularRequest domains request located.fragment location)

/-- Compare the regular lower Point to the independent physical first Point through their SAME retained zero Query.

The endpoint role gives parameter zero, including a stationary parent.
The original request comparison consumes that Query and the cached lower
Point; the physical side reuses its stored EndpointPoints comparison.
This lower request comparison is new; the physical comparison is reused.
No sample, query or root-owner factory is rerun.
-/
def firstSampleEquivalent : NamedEquivalent (ownerName regular.sample.owner)
    (ownerName kept.entry.firstSample.owner) :=
  let pointEq := located.fragment.first_eq.trans
    (congrArg (parents.covered.parents[index.val]'index.isLt).edge.point located.lower_eq_zero)
  let onRequest := request.retainedQueryEquivalent 0
    (parents.covered.parents[index.val]'index.isLt).edge.baseInside firstQuery pointEq.symm
    (located.fragment.request_endpoints request).1 regular.sample
  let throughQuery := NamedEquivalent.transport firstQuery.name_eq rfl onRequest
  throughQuery.symm.trans kept.firstEquivalent

/-- The retained physical first Point Entry selects the original regular lower domain's actual sheet.

Only the coordinate index is transported along the literal zero-role
readback. The preceding operational comparison propagates the original
regular Entry to the physical Owner before clear-face uniqueness is used.
-/
theorem first_sheet
    (actual : Entry regular.compared.shared.models
      (PreparedParent.startPoint (frame := frame) (basis := basis)
        (parents.covered.parents[index.val]'index.isLt)).coordinate kept.entry.firstSample.owner) :
    actual.sheet = regular.compared.acquired.entry.sheet := by
  have samePoint := located.first_eq.trans (parents.covered.parents[index.val]'index.isLt).edge.point_zero
  exact (regular.compared.acquired.entry.sheet_eq_of_equivalent actual samePoint
    (kept.firstSampleEquivalent located regular) (located.fragment.regular_endpoints location).1).symm

end First

section Last

variable (located : grid.Endpoint index true)
variable {location : RegularLocation base.faces.regulars located.fragment.cell}
variable {regular : PrimitiveFragmentCell.RegularRequest domains request located.fragment location}
variable (upper : regular.UpperEndpoint)

/-- Compare the retained upper Point to the independent physical last Point using both original Query caches.

The actual unit-role interval readback transports upper.queryEquivalent
through the original parent rootName at parameter one. The physical side
reads its cached lastEquivalent; no Query or Point producer is run.
-/
def lastSampleEquivalent : NamedEquivalent (ownerName upper.sample.owner)
    (ownerName kept.entry.lastSample.owner) :=
  let fromUpper := NamedEquivalent.transport upper.query.name_eq.symm rfl upper.queryEquivalent
  let atOne := (parents.covered.parents[index.val]'index.isLt).edge.rootName_eq
    (firstInside := located.fragment.upper_inside)
    (lastInside := (of_decide_eq_true rfl)) located.upper_eq_one
  let throughQuery := NamedEquivalent.transport (atOne.trans lastQuery.name_eq) rfl fromUpper
  throughQuery.symm.trans kept.lastEquivalent

include upper in
/-- The independent physical last Point Entry has the original retained lower domain's actual sheet.

The cached upper Query comparison identifies its own Entry sheet with
this physical Point. The original split-finish nearest-sign certificate,
upper.sheet_eq, then supplies its relation to the retained lower sheet.
Primitive anchors, offsets and observations remain independent inputs.
-/
theorem last_sheet
    (actual : Entry regular.compared.shared.models
      (PreparedParent.finishPoint (frame := frame) (basis := basis)
        (parents.covered.parents[index.val]'index.isLt)).coordinate kept.entry.lastSample.owner) :
    actual.sheet = regular.compared.acquired.entry.sheet := by
  have samePoint := located.last_eq.trans (parents.covered.parents[index.val]'index.isLt).edge.point_one
  have sameSheet := upper.acquired.entry.sheet_eq_of_equivalent actual samePoint
    (kept.lastSampleEquivalent located upper) (located.fragment.regular_endpoints location).2
  exact sameSheet.symm.trans upper.sheet_eq.symm

end Last

end EndpointPoints

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical.Comparison

end
