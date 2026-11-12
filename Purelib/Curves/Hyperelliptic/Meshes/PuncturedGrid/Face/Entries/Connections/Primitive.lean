module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Connections
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths.Points
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.RootContinuation.RootPathTransport

/-! # Actual source-connection requests on retained old primitive data

A new covered numerical trace remains distinct from the original source
connection. Its actual parent mesh determines the request floor, while
both original endpoint Owners and every old primitive constant survive.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry.TracedPoint

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths (EnteredPath)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes (Reached)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Paths.ClearBoxPaths (Route)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath OwnerLink)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName OwnerJoin)
open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame)
open Purelib.Riemann.RootContinuation.RootPathTransport (TransportRow)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
variable {frames : RootFrames bank.grid} {face : RegularFace bank} {models : FaceModels frames face}
variable {sheet : Fin 2} {point : Canonical} {inside : face.cell.box.Contains point}
variable {count : Nat} {targetFrame : OwnerFrame (curve.polynomial.eval point)}
variable (cached : TracedPoint models sheet point inside count targetFrame)
variable {source : Canonical} {sourceFrame : OwnerFrame (curve.polynomial.eval source)} {index : Fin 2}
variable (sourceEntry : Entry models source (sourceFrame.owners index))
variable (same : sourceEntry.sheet = sheet) (sourceInside : face.cell.box.Contains source)

variable (connected : cached.Connection sourceEntry same sourceInside)
variable (domain : PeriodDomain models sheet) (differential : Differential genus) (parentSheet : Fin 2)

/-- Retain the complete old connection and a distinct numerical preparation on its literal contained route.

The numerical trace, parent cache and target-frame row are built once.
The original Entry's derived sheet equality only transports its erased
reachability certificate; no new face classification is performed.
-/
abbrev PrimitivePreparation :=
  {value : TracedPoint models sheet point inside count targetFrame ×
      Entry models source (sourceFrame.owners index) × cached.Connection sourceEntry same sourceInside //
    value = (cached, sourceEntry, connected)} ×
  (Σ covered : {value : CoveredTracedPath connected.route.path (sourceFrame.owners index) //
    value = CoveredTracedPath.build connected.route.path connected.route.within (sourceFrame.owners index)},
  Σ parents : {value : ParentCache covered.val differential parentSheet //
    value = ParentCache.build covered.val differential parentSheet},
  Σ row : {value : TransportRow connected.route.path sourceFrame cached.frame index //
    value = TransportRow.ofTraced cached.frame covered.val.traced},
  {value : NamedEquivalent (ownerName row.val.traced.finishOwner) (ownerName cached.sample.owner) //
    value = cached.sourceEquivalent sourceEntry same sourceInside connected.route row.val} ×
  {value : EnteredPath models covered.val differential parentSheet //
    value = EnteredPath.ofEntry
      (⟨sheet, Eq.mp (congrArg (fun selected =>
        Reached face.cell.box (models.frame.owners selected) (sourceFrame.owners index)) same)
          sourceEntry.reached⟩ : Entry models source (sourceFrame.owners index))
      domain covered.val (Polynomial.Geometry.ClearPath.InBox.ofWithin connected.route.path
        connected.route.within sourceInside) differential parentSheet parents.val})

/-- Materialize proper numerical parents and an entered mesh before any new numerical request is paid.

This is genuinely new covered preparation. The old Point, Entry,
connection trace, join and path are retained verbatim as inputs, and the
new finish-to-Point comparison is derived from the actual new selection.
-/
def preparePrimitives : cached.PrimitivePreparation sourceEntry same sourceInside connected domain
    differential parentSheet :=
  let covered := CoveredTracedPath.build connected.route.path connected.route.within (sourceFrame.owners index)
  let parents := ParentCache.build covered differential parentSheet
  let row := TransportRow.ofTraced cached.frame covered.traced
  let equivalent := cached.sourceEquivalent sourceEntry same sourceInside connected.route row
  let starting : Entry models source (sourceFrame.owners index) :=
    ⟨sheet, Eq.mp (congrArg (fun selected =>
      Reached face.cell.box (models.frame.owners selected) (sourceFrame.owners index)) same) sourceEntry.reached⟩
  let entered := EnteredPath.ofEntry starting domain covered
    (Polynomial.Geometry.ClearPath.InBox.ofWithin connected.route.path connected.route.within sourceInside)
    differential parentSheet parents
  (⟨(cached, sourceEntry, connected), rfl⟩,
    ⟨⟨covered, rfl⟩, ⟨parents, rfl⟩, ⟨row, rfl⟩, ⟨equivalent, rfl⟩, ⟨entered, rfl⟩⟩)

namespace PrimitivePreparation

variable {cached sourceEntry same sourceInside connected domain differential parentSheet}
variable (prepared : cached.PrimitivePreparation sourceEntry same sourceInside connected domain
  differential parentSheet)

/-- Read all three complete original input caches, including the old connection's literal stationary join. -/
def original : TracedPoint models sheet point inside count targetFrame ×
    Entry models source (sourceFrame.owners index) × cached.Connection sourceEntry same sourceInside :=
  prepared.1.val

/-- Read the whole new numerical covered trace. -/
def covered : CoveredTracedPath connected.route.path (sourceFrame.owners index) := prepared.2.1.val

/-- Read the actual new proper parent list and its complete original coverage cache. -/
def parents : ParentCache prepared.covered differential parentSheet := prepared.2.2.1.val

/-- Read the actual new target-frame row; the original source row remains in original. -/
def row : TransportRow connected.route.path sourceFrame cached.frame index := prepared.2.2.2.1.val

/-- Read the derived comparison from the new row's actual finish to the SAME retained Point. -/
def pointEquivalent : NamedEquivalent (ownerName prepared.row.traced.finishOwner)
    (ownerName cached.sample.owner) := prepared.2.2.2.2.1.val

/-- Read the whole entered-path mesh retaining the old face domain and the new numerical parent cache. -/
def entered : EnteredPath models prepared.covered differential parentSheet := prepared.2.2.2.2.2.val

/-- All old input caches remain the original complete values. -/
theorem original_eq : prepared.original = (cached, sourceEntry, connected) := prepared.1.property

/-- The complete new covered trace retains its exact original factory. -/
theorem covered_eq : prepared.covered =
    CoveredTracedPath.build connected.route.path connected.route.within (sourceFrame.owners index) :=
  prepared.2.1.property

/-- The complete new parent cache is built from the SAME retained numerical trace. -/
theorem parents_eq : prepared.parents = ParentCache.build prepared.covered differential parentSheet :=
  prepared.2.2.1.property

/-- The new row is the original transport-row constructor on this SAME numerical trace. -/
theorem row_eq : prepared.row = TransportRow.ofTraced cached.frame prepared.covered.traced :=
  prepared.2.2.2.1.property

/-- The new endpoint comparison is the original source Entry comparison, not a supplied signed relation. -/
theorem pointEquivalent_eq : prepared.pointEquivalent =
    cached.sourceEquivalent sourceEntry same sourceInside connected.route prepared.row := prepared.2.2.2.2.1.property

/-- The actual new and old source finishes compare through the SAME retained Point, while remaining distinct Owners. -/
def previousEquivalent : NamedEquivalent (ownerName prepared.row.traced.finishOwner)
    (ownerName connected.row.traced.finishOwner) := prepared.pointEquivalent.trans connected.equivalent.symm

/-- The entered mesh retains its whole original factory, with only the source Entry's derived sheet transport. -/
theorem entered_eq : prepared.entered = EnteredPath.ofEntry
    (⟨sheet, Eq.mp (congrArg (fun selected =>
      Reached face.cell.box (models.frame.owners selected) (sourceFrame.owners index)) same)
        sourceEntry.reached⟩ : Entry models source (sourceFrame.owners index))
    domain prepared.covered (Polynomial.Geometry.ClearPath.InBox.ofWithin connected.route.path
      connected.route.within sourceInside) differential parentSheet prepared.parents := prepared.2.2.2.2.2.property

section Readings

variable {stage size : Nat} {points : Fin size → Canonical}
variable (data : DomainPrimitives domain differential stage) (observed : PointReadings data.anchors data.offsets points)

/-- Transport the SAME old primitives and PointReadings together into the retained entered mesh's dependent type.

The equality is used toward the retained entered value. It never replaces
that value by an ofEntry execution in a subsequent request producer.
-/
def pointData : prepared.entered.PointData stage points :=
  EnteredPath.castPointData stage points prepared.entered_eq.symm ⟨data, observed⟩

/-- Whole entered-path transport leaves every original sampled primitive value unchanged. -/
theorem pointData_values : (prepared.pointData data observed).2.values = observed.values :=
  EnteredPath.castPointData_values stage points prepared.entered_eq.symm ⟨data, observed⟩

/-- One transported old-data cache and its exact finite request attempt on the actual entered mesh. -/
abbrev Requests (target : Rational) (positive : 0 < target) :=
  Σ pointData : {value : prepared.entered.PointData stage points // value = prepared.pointData data observed},
    pointData.val.RequestAttempt positive

/-- Compute the actual new mesh floor and pay requests only when the SAME old primitive stage suffices. -/
def request (target : Rational) (positive : 0 < target) : prepared.Requests data observed target positive :=
  let pointData := prepared.pointData data observed
  let attempted := pointData.attempt target positive
  ⟨⟨pointData, rfl⟩, attempted⟩

namespace Requests

variable {prepared data observed} {target : Rational} {positive : 0 < target}
variable (requested : prepared.Requests data observed target positive)

/-- The actual transported cache in this request retains every old sampled primitive value. -/
theorem values_eq : requested.1.val.2.values = observed.values :=
  (congrArg (fun value : prepared.entered.PointData stage points => value.2.values) requested.1.property).trans
    (prepared.pointData_values data observed)

/-- A successful request pays the original old-data point increment on its actual cached numerical parents.

The request is an original requestShared result on the retained data in
this exact attempt. The only remaining scalar stage requirement is the
computed budget floor; no final analytic or signed comparison is an input.
-/
theorem accurate
    (budget : Integration.Polynomial.Rectangle.Accuracy.Fragment.FragmentAccuracy prepared.entered.globalBounds
      prepared.entered.domain.steps prepared.entered.mesh.splits.pieceCount (target / 4))
    (later : budget.grid.index ≤ stage)
    (paid : requested.1.val.Request budget later)
    (first last : Fin size) (firstEq : points first = source) (lastEq : points last = point) :
    Data.Gaussian.Norm.Basic.normSq ((observed.values last - observed.values first) -
      paid.val.request.primitiveSum) < target := by
  have bound := EnteredPath.PointData.Request.accurate paid first last firstEq lastEq
  rw [requested.values_eq] at bound
  exact bound

end Requests

end Readings

end PrimitivePreparation

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry.TracedPoint

end
