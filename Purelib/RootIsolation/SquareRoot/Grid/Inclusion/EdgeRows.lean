module

public import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Polynomial.Geometry.Grid.Winding
public import Purelib.Riemann.RootContinuation.ClearBoxRootTransport
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.OwnerTraceReadings
public import Purelib.Data.Vector.Dependent.Subtype

/-! # Retained old edge rows and their actual refined subdivisions

The new grid may have a different ambient box. Its frame bank extends the
whole old entry prefix, so old endpoint frames are reused literally. New
local edge rows and their joined paths are materialized separately. The
original winding-one reference compares the two retained finish selections.
-/

public section

namespace Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Vector (DependentVector)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Polynomial.Geometry.ClearPath (GaussianPolynomial)
open Purelib.Polynomial.Geometry.Grid (ClearGrid)
open Purelib.Polynomial.Geometry.Grid.FromStates (ContainsVertex)
open Purelib.Polynomial.Geometry.Grid.Walks (Edge Walk splitSegment)
open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame OwnerSelection)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Riemann.Paths
open Purelib.Riemann.RootContinuation

variable {polynomial : GaussianPolynomial} {ambient small : Box}
variable {original : ClearGrid polynomial ambient} {fine : ClearGrid polynomial small}
variable {oldFrames : RootFrames original} {fineFrames : RootFrames fine}

/-- The complete retained extension law reads an old endpoint's whole original frame. -/
private theorem frame_eq (factory : fineFrames = oldFrames.extend fine) (base : Canonical)
    (onFine : ContainsVertex fine base) (onOld : ContainsVertex original base) :
    fineFrames.frameAt base onFine = oldFrames.frameAt base onOld :=
  (congrArg (fun value : RootFrames fine => value.frameAt base onFine) factory).trans
    (oldFrames.extend_frameAt fine base onFine onOld)

section Edge

variable (old : RootEdgeBank oldFrames)
variable {start finish : Canonical} (edge : Edge original start finish)
variable (first : ContainsVertex fine start) (last : ContainsVertex fine finish)

/-- One old connection and its once-subdivided refined walk retain their whole original factories. -/
abbrev EdgeSubdivision :=
  Σ connection : {value : RootEdges.RootEdge (ambient := ambient)
      (oldFrames.frameAt start edge.vertices.1) (oldFrames.frameAt finish edge.vertices.2) //
      value = old.edge edge},
  {value : Walk fine start finish // value = splitSegment fine connection.val.forwardSegment first last}

/-- Read one old cached connection and split its actual clear segment on the new refined grid once. -/
def subdivideEdge : old.EdgeSubdivision edge first last :=
  let connection := old.edge edge
  let walk := splitSegment fine connection.forwardSegment first last
  ⟨⟨connection, rfl⟩, ⟨walk, rfl⟩⟩

namespace EdgeSubdivision

variable {old edge first last}
variable {refined : RootEdgeBank fineFrames}
variable (subdivided : old.EdgeSubdivision edge first last)

/-- Read the whole original ambient-indexed cached edge connection. -/
def connection : RootEdges.RootEdge (ambient := ambient)
    (oldFrames.frameAt start edge.vertices.1) (oldFrames.frameAt finish edge.vertices.2) := subdivided.1.val

/-- Read the actual retained refined walk, preserving every oriented adjacent interval. -/
def walk : Walk fine start finish := subdivided.2.val

/-- The selected old edge is the complete original cached connection. -/
theorem connection_eq : subdivided.connection = old.edge edge := subdivided.1.property

/-- The refined walk is the complete original split of that SAME cached connection's segment. -/
theorem walk_eq : subdivided.walk = splitSegment fine subdivided.connection.forwardSegment first last :=
  subdivided.2.property

/-- Read the actual fine-bank target at the original source sheet. -/
abbrev target (refined : RootEdgeBank fineFrames) (sheet : Fin 2) : Fin 2 :=
  EdgeBank.RootEdgeBank.target refined subdivided.walk sheet

/-- Reindex only the original source frame of a retained refined owner path.

The source equality comes from the whole frame-extension law. Its terminal
owner remains the actual new refined bank owner, not an old-owner substitute.
-/
def fromOldSource (factory : fineFrames = oldFrames.extend fine) (sheet : Fin 2)
    (path : OwnerPath polynomial start ((fineFrames.frameAt start first).owners sheet)
      finish ((fineFrames.frameAt finish last).owners (subdivided.target refined sheet))) :
    OwnerPath polynomial start ((oldFrames.frameAt start edge.vertices.1).owners sheet)
      finish ((fineFrames.frameAt finish last).owners (subdivided.target refined sheet)) :=
  path.reindexOwners (congrArg (fun frame : OwnerFrame (polynomial.eval start) => frame.owners sheet)
    (frame_eq factory start first edge.vertices.1)) rfl

/-- The actual new refined finish owner selects its SAME original terminal-frame index. -/
def terminalSelection (refined : RootEdgeBank fineFrames)
    (factory : fineFrames = oldFrames.extend fine) (sheet : Fin 2) :
    OwnerSelection (oldFrames.frameAt finish edge.vertices.2).owners
      ((fineFrames.frameAt finish last).owners (subdivided.target refined sheet)) :=
  ⟨subdivided.target refined sheet, NamedEquivalent.transport rfl
    (congrArg (fun frame : OwnerFrame (polynomial.eval finish) =>
      ownerName (frame.owners (subdivided.target refined sheet)))
      (frame_eq factory finish last edge.vertices.2))
    (NamedEquivalent.refl _)⟩

/-- The old single-segment path remains inside its original ambient box. -/
theorem within :
    (ClearPath.cons subdivided.connection.forwardSegment (.nil finish)).WithinAmbient :=
  .cons (subdivided.connection.forwardSegment.withinAmbient_of_start edge.vertices.1.inside) (.nil finish)

/-- The new path keeps the exact winding of the original cached clear segment. -/
theorem winding (refined : RootEdgeBank fineFrames)
    (factory : fineFrames = oldFrames.extend fine) (sheet : Fin 2)
    (path : OwnerPath polynomial start ((fineFrames.frameAt start first).owners sheet)
      finish ((fineFrames.frameAt finish last).owners (subdivided.target refined sheet)))
    (path_eq : path = EdgeBank.RootEdgeBank.trace refined subdivided.walk first last sheet) :
    PreparedPathWinding.ClearPath.rawWinding
      (ClearPath.cons subdivided.connection.forwardSegment (.nil finish)) =
      Polynomial.Winding.Polygon.Basic.chainRaw polynomial start
        (subdivided.fromOldSource factory sheet path).vertices := by
  rewrite [fromOldSource, OwnerPath.reindexOwners_vertices]
  have original := congrArg (fun value : OwnerPath polynomial start
    ((fineFrames.frameAt start first).owners sheet) finish
      ((fineFrames.frameAt finish last).owners (subdivided.target refined sheet)) =>
    Polynomial.Winding.Polygon.Basic.chainRaw polynomial start value.vertices) path_eq
  have walked := original.trans (EdgeBank.RootEdgeBank.trace_winding refined subdivided.walk first last sheet)
  have split := (congrArg (fun value : Walk fine start finish =>
    PreparedPathWinding.ClearPath.rawWinding value.path) subdivided.walk_eq).trans
      (Polynomial.Geometry.Grid.Winding.splitSegment_winding fine
        subdivided.connection.forwardSegment first last)
  exact (Int.add_zero _).trans (walked.trans split).symm

/-- One new refined owner path retains its whole factory and the derived old-row comparison and target index.

Materializing this path performs the original fine-bank joined-trace work,
including its genuine stationary endpoint joins. Their expression-observation
payments are separate from the root comparison and from primitive constants.
-/
abbrev SheetComparison (refined : RootEdgeBank fineFrames)
    (factory : fineFrames = oldFrames.extend fine) (reference : WindingOneLoop polynomial start) (sheet : Fin 2) :=
  Σ path : {value : OwnerPath polynomial start ((fineFrames.frameAt start first).owners sheet)
      finish ((fineFrames.frameAt finish last).owners (subdivided.target refined sheet)) //
      value = EdgeBank.RootEdgeBank.trace refined subdivided.walk first last sheet},
  {value : NamedEquivalent (ownerName (subdivided.connection.forward.row sheet).traced.finishOwner)
      (ownerName ((fineFrames.frameAt finish last).owners (subdivided.target refined sheet))) //
    value = ClearBoxRootTransport.TracedPath.equivalentOfOwnerPathSelections reference subdivided.within
      (subdivided.connection.forward.row sheet).traced
      (subdivided.fromOldSource factory sheet path.val) (oldFrames.frameAt finish edge.vertices.2)
      (subdivided.connection.forward.row sheet).selected (subdivided.terminalSelection refined factory sheet)
      (subdivided.winding refined factory sheet path.val path.property) ∧
    subdivided.connection.forward.target sheet = subdivided.target refined sheet}

/-- Materialize one refined joined path and compare its actual finish to the retained original forward row. -/
def compareSheet (refined : RootEdgeBank fineFrames)
    (factory : fineFrames = oldFrames.extend fine) (reference : WindingOneLoop polynomial start) (sheet : Fin 2) :
    subdivided.SheetComparison refined factory reference sheet :=
  let path := EdgeBank.RootEdgeBank.trace refined subdivided.walk first last sheet
  let compared := ClearBoxRootTransport.TracedPath.equivalentOfOwnerPathSelections reference subdivided.within
    (subdivided.connection.forward.row sheet).traced
    (subdivided.fromOldSource factory sheet path) (oldFrames.frameAt finish edge.vertices.2)
    (subdivided.connection.forward.row sheet).selected (subdivided.terminalSelection refined factory sheet)
    (subdivided.winding refined factory sheet path rfl)
  have targets := ClearBoxRootTransport.TracedPath.selection_eq_of_ownerPath reference subdivided.within
    (subdivided.connection.forward.row sheet).traced
    (subdivided.fromOldSource factory sheet path) (oldFrames.frameAt finish edge.vertices.2)
    (subdivided.connection.forward.row sheet).selected (subdivided.terminalSelection refined factory sheet)
    (subdivided.winding refined factory sheet path rfl)
  ⟨⟨path, rfl⟩, ⟨compared, rfl, targets⟩⟩

/-- Materialize and retain both original-sheet comparisons on the SAME cached edge subdivision. -/
def compareSheets (refined : RootEdgeBank fineFrames)
    (factory : fineFrames = oldFrames.extend fine) (reference : WindingOneLoop polynomial start) :
    DependentVector (fun sheet : Fin 2 =>
      {value : subdivided.SheetComparison refined factory reference sheet //
        value = subdivided.compareSheet refined factory reference sheet}) :=
  Data.Vector.DependentVector.ofFnWithEq (fun sheet => subdivided.compareSheet refined factory reference sheet)

namespace SheetComparison

variable {refined : RootEdgeBank fineFrames} {factory : fineFrames = oldFrames.extend fine}
variable {reference : WindingOneLoop polynomial start} {sheet : Fin 2}
variable (compared : subdivided.SheetComparison refined factory reference sheet)

/-- Read the SAME newly materialized local path and all its original joined occurrences. -/
def path : OwnerPath polynomial start ((fineFrames.frameAt start first).owners sheet)
    finish ((fineFrames.frameAt finish last).owners (subdivided.target refined sheet)) := compared.1.val

/-- Read the operational old-row finish to actual new terminal-owner comparison. -/
def equivalent : NamedEquivalent (ownerName (subdivided.connection.forward.row sheet).traced.finishOwner)
    (ownerName ((fineFrames.frameAt finish last).owners (subdivided.target refined sheet))) := compared.2.val

/-- The retained new owner path is its whole original fine-bank trace factory. -/
theorem path_eq : compared.path = EdgeBank.RootEdgeBank.trace refined subdivided.walk first last sheet :=
  compared.1.property

include compared

/-- The old row and actual new walk select exactly the same original-sheet index. -/
theorem target_eq : subdivided.connection.forward.target sheet = subdivided.target refined sheet :=
  compared.2.property.2

end SheetComparison

end EdgeSubdivision

/-- A complete one-edge comparison retains the subdivision and both actual sheet paths with whole factory laws. -/
abbrev EdgeComparison (refined : RootEdgeBank fineFrames) (factory : fineFrames = oldFrames.extend fine)
    (reference : WindingOneLoop polynomial start) :=
  Σ subdivided : {value : old.EdgeSubdivision edge first last // value = old.subdivideEdge edge first last},
  {value : DependentVector (fun sheet : Fin 2 =>
      {entry : subdivided.val.SheetComparison refined factory reference sheet //
        entry = subdivided.val.compareSheet refined factory reference sheet}) //
    value = subdivided.val.compareSheets refined factory reference}

/-- Materialize the original edge subdivision once, then both signed local comparisons once. -/
def compareEdge (refined : RootEdgeBank fineFrames) (factory : fineFrames = oldFrames.extend fine)
    (reference : WindingOneLoop polynomial start) : old.EdgeComparison edge first last refined factory reference :=
  let subdivided := old.subdivideEdge edge first last
  let compared := subdivided.compareSheets refined factory reference
  ⟨⟨subdivided, rfl⟩, ⟨compared, rfl⟩⟩

namespace EdgeComparison

variable {old edge first last} {refined : RootEdgeBank fineFrames}
variable {factory : fineFrames = oldFrames.extend fine} {reference : WindingOneLoop polynomial start}
variable (compared : old.EdgeComparison edge first last refined factory reference)

/-- Read the SAME cached original edge connection and local subdivision. -/
def subdivision : old.EdgeSubdivision edge first last := compared.1.val

/-- The retained subdivision is its whole original one-edge factory. -/
theorem subdivision_eq : compared.subdivision = old.subdivideEdge edge first last := compared.1.property

/-- Read one stored signed comparison without materializing its path again. -/
def sheet (index : Fin 2) : compared.subdivision.SheetComparison refined factory reference index :=
  Data.Vector.DependentVector.getSubtypeValue compared.2.val index

/-- The stored sheet comparison keeps the complete original comparison factory. -/
theorem sheet_eq (index : Fin 2) :
    compared.sheet index = compared.subdivision.compareSheet refined factory reference index :=
  Data.Vector.DependentVector.getSubtypeValue_property compared.2.val index

end EdgeComparison

end Edge

end Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
