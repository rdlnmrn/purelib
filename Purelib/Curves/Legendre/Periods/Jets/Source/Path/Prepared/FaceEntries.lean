module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared
public import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.Parents.Grid.Endpoints
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Interior
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames

/-! # Actual physical endpoint Owners in their retained regular grid faces

The two independent original Point caches remain in PreparedParent. The
same paid grid-fragment cache supplies their actual endpoint occurrences.
A regular branch and an already retained complete face-domain cache permit
one genuine Entry acquisition on each unchanged Point Owner. Hole payloads
remain in the endpoint cache; no Point, Query, domain or lazy bank is built.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomains)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Geometry.Rational (Box)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularLocation)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {ambient : Box} {start finish : Canonical}
variable {segment : ClearSegment (Paths.polynomial parameter) ambient start finish} {within : segment.WithinAmbient}
variable {sourceOwner : Owner ((Paths.polynomial parameter).eval start)} {widthRequest : AccuracyRequest}
variable {parentCount : Nat} {sheet : Fin 2}
variable {retained : Acquisition.Segment (segment := segment) (within := within) (owner := sourceOwner) widthRequest}
variable {parents : Acquisition.Segment.Parents (curve := Fibre.frameCurve frame) basis sheet parentCount retained}
variable {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
variable {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
variable {base : FramedPuncturedGrid (Fibre.frameCurve frame) branches higher}
variable {axes : PrimitiveAxes base.bank.grid}
variable {first : (Cuts.Ambient (Fibre.frameCurve frame)).Contains start}
variable {last : (Cuts.Ambient (Fibre.frameCurve frame)).Contains finish}
variable {cached : Acquisition.Segment.Parents.GridFragments base axes parents first last}
variable {index : Fin parents.covered.parents.length}
variable {count floor : Nat} {patch : PreparedPatch (parents.covered.parents[index.val]'index.isLt)}
variable {covered : (patch.neighborhood count).box.Contains
  ((parents.covered.parents[index.val]'index.isLt).edge.point 1)}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets original stage}
variable {frames : RootFrames base.bank.grid}
variable (prepared : PreparedParent (frame := frame) (basis := basis) patch count floor covered targets)

/-- The zero-role fragment contains the literal coordinate of the SAME original first Point. -/
theorem first_face_inside (located : cached.Endpoint index false)
    (location : RegularLocation base.faces.regulars located.fragment.cell) :
    location.face.cell.box.Contains
      (startPoint (frame := frame) (basis := basis) (parents.covered.parents[index.val]'index.isLt)).coordinate := by
  have cellInside : location.face.cell.box.Contains located.fragment.first :=
    Eq.mpr (congrArg (fun cell => cell.box.Contains located.fragment.first) location.cell_eq)
      located.fragment.first_inside
  have coordinate : located.fragment.first =
      (startPoint (frame := frame) (basis := basis) (parents.covered.parents[index.val]'index.isLt)).coordinate :=
    located.first_eq.trans (parents.covered.parents[index.val]'index.isLt).edge.point_zero
  exact Eq.mp (congrArg location.face.cell.box.Contains coordinate) cellInside

/-- The unit-role fragment contains the distinct retained last Point without identifying it with the first. -/
theorem last_face_inside (located : cached.Endpoint index true)
    (location : RegularLocation base.faces.regulars located.fragment.cell) :
    location.face.cell.box.Contains
      (finishPoint (frame := frame) (basis := basis) (parents.covered.parents[index.val]'index.isLt)).coordinate := by
  have cellInside : location.face.cell.box.Contains located.fragment.last :=
    Eq.mpr (congrArg (fun cell => cell.box.Contains located.fragment.last) location.cell_eq)
      located.fragment.last_inside
  have coordinate : located.fragment.last =
      (finishPoint (frame := frame) (basis := basis) (parents.covered.parents[index.val]'index.isLt)).coordinate :=
    located.last_eq.trans (parents.covered.parents[index.val]'index.isLt).edge.point_one
  exact Eq.mp (congrArg location.face.cell.box.Contains coordinate) cellInside

/-- Acquire the actual first Point's Entry using its cached regular outcome and an existing whole face-domain cache.

The classification equation is the regular branch's readback, not a
signed relation. Only Entry.Acquisition.build is new work; its complete
frame, both routes/transports, selector and Entry remain cached together.
-/
def firstFaceEntry (located : cached.Endpoint index false)
    {location : RegularLocation base.faces.regulars located.fragment.cell}
    (regular : located.classification = .regular location) (shared : FaceDomains frames location.face) :
    {value : Entry.Acquisition shared.models
        (first_face_inside (frame := frame) (basis := basis) located location)
        (firstSample (frame := frame) (basis := basis) prepared).owner //
      value = Entry.Acquisition.build shared.models
        (first_face_inside (frame := frame) (basis := basis) located location)
        (firstSample (frame := frame) (basis := basis) prepared).owner ∧
      located.classification = .regular location} :=
  let acquired := Entry.Acquisition.build shared.models
    (first_face_inside (frame := frame) (basis := basis) located location)
    (firstSample (frame := frame) (basis := basis) prepared).owner
  ⟨acquired, ⟨rfl, regular⟩⟩

/-- Acquire the independent last Point's Entry without rerunning its Point, Query or lower acquisition. -/
def lastFaceEntry (located : cached.Endpoint index true)
    {location : RegularLocation base.faces.regulars located.fragment.cell}
    (regular : located.classification = .regular location) (shared : FaceDomains frames location.face) :
    {value : Entry.Acquisition shared.models
        (last_face_inside (frame := frame) (basis := basis) located location)
        (lastSample (frame := frame) (basis := basis) prepared).owner //
      value = Entry.Acquisition.build shared.models
        (last_face_inside (frame := frame) (basis := basis) located location)
        (lastSample (frame := frame) (basis := basis) prepared).owner ∧
      located.classification = .regular location} :=
  let acquired := Entry.Acquisition.build shared.models
    (last_face_inside (frame := frame) (basis := basis) located location)
    (lastSample (frame := frame) (basis := basis) prepared).owner
  ⟨acquired, ⟨rfl, regular⟩⟩

/-- The complete first acquisition is the original factory on the unchanged retained first Point Owner. -/
theorem firstFaceEntry_eq (located : cached.Endpoint index false)
    {location : RegularLocation base.faces.regulars located.fragment.cell}
    (regular : located.classification = .regular location) (shared : FaceDomains frames location.face) :
    (prepared.firstFaceEntry located regular shared).val =
      Entry.Acquisition.build shared.models
        (first_face_inside (frame := frame) (basis := basis) located location)
        (firstSample (frame := frame) (basis := basis) prepared).owner :=
  (prepared.firstFaceEntry located regular shared).property.1

/-- The complete last acquisition retains its own original Point Owner and same selected face model. -/
theorem lastFaceEntry_eq (located : cached.Endpoint index true)
    {location : RegularLocation base.faces.regulars located.fragment.cell}
    (regular : located.classification = .regular location) (shared : FaceDomains frames location.face) :
    (prepared.lastFaceEntry located regular shared).val =
      Entry.Acquisition.build shared.models
        (last_face_inside (frame := frame) (basis := basis) located location)
        (lastSample (frame := frame) (basis := basis) prepared).owner :=
  (prepared.lastFaceEntry located regular shared).property.1

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent

end
