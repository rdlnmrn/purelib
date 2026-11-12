module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
public import Purelib.Riemann.Paths.OwnerTraceReadings.Comparison
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Transport
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedEdges
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Tactic.QuotientFreeOmega

/-! # Whole face reindexing and uniqueness of the original signed Entry

The retained frame and Entry transport only along an equality of their
actual face owner. Two original entries of the same supplied Owner in one
clear face have the same selected sheet: their actual reachability paths
form an even loop. No new root relation is admitted.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
variable {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {first last : RegularFace bank}

/-- Reindex the complete original model cache along equality of its actual face owner. -/
@[expose] def castFace (same : first = last) (models : FaceModels frames first) : FaceModels frames last := by
  cases same
  exact models

/-- Exact face reindexing retains the entire original model and frame cache. -/
theorem castFace_heq (same : first = last) (models : FaceModels frames first) :
    HEq (models.castFace same) models := by
  cases same
  rfl

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes (Reached)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Paths.OwnerLoopMonodromy
open Purelib.Riemann.Paths.OwnerTraceReadings (OwnerJoin ownerName)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
variable {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {firstFace lastFace : RegularFace bank}
variable {models : FaceModels frames firstFace} {point : Canonical}
variable {owner : Owner (curve.polynomial.eval point)}

/-- Reindex the complete original Entry with the same whole model transport along actual face equality. -/
@[expose] def castFace (same : firstFace = lastFace) (entry : Entry models point owner) :
    Entry (models.castFace same) point owner := by
  cases same
  exact entry

/-- Exact face reindexing retains the complete original Entry, including its actual reachability witness. -/
theorem castFace_heq (same : firstFace = lastFace) (entry : Entry models point owner) :
    HEq (entry.castFace same) entry := by
  cases same
  rfl

/-- Whole Entry reindexing preserves the original sheet index. -/
theorem castFace_sheet (same : firstFace = lastFace) (entry : Entry models point owner) :
    (entry.castFace same).sheet = entry.sheet := by
  cases same
  rfl

/-- Reindex one complete Entry along actual point and whole Owner identities.

Both supplied identities concern the same retained Owner and Entry. The
coordinate equality alone identifies no root Owners or their sheets; all
reachability data is transported together without another acquisition.
-/
@[expose] def castPoint {first last : Canonical}
    {firstOwner : Owner (curve.polynomial.eval first)} {lastOwner : Owner (curve.polynomial.eval last)}
    (samePoint : first = last) (sameOwner : HEq firstOwner lastOwner)
    (entry : Entry models first firstOwner) : Entry models last lastOwner := by
  cases samePoint
  have owners : firstOwner = lastOwner := eq_of_heq sameOwner
  cases owners
  exact entry

/-- Point and whole-Owner reindexing retains the complete original Entry heterogeneously. -/
theorem castPoint_heq {first last : Canonical}
    {firstOwner : Owner (curve.polynomial.eval first)} {lastOwner : Owner (curve.polynomial.eval last)}
    (samePoint : first = last) (sameOwner : HEq firstOwner lastOwner)
    (entry : Entry models first firstOwner) : HEq (entry.castPoint samePoint sameOwner) entry := by
  cases samePoint
  have owners : firstOwner = lastOwner := eq_of_heq sameOwner
  cases owners
  rfl

/-- Whole point and Owner reindexing preserves the retained face sheet. -/
theorem castPoint_sheet {first last : Canonical}
    {firstOwner : Owner (curve.polynomial.eval first)} {lastOwner : Owner (curve.polynomial.eval last)}
    (samePoint : first = last) (sameOwner : HEq firstOwner lastOwner)
    (entry : Entry models first firstOwner) : (entry.castPoint samePoint sameOwner).sheet = entry.sheet := by
  cases samePoint
  have owners : firstOwner = lastOwner := eq_of_heq sameOwner
  cases owners
  rfl

/-- Reindex the complete original Entry along equality of two indices in the SAME supplied frame. -/
def castIndex (frame : OwnerFrame (curve.polynomial.eval point)) {first last : Fin 2} (same : first = last)
    (entry : Entry models point (frame.owners first)) : Entry models point (frame.owners last) :=
  Eq.mp (congrArg (fun index => Entry models point (frame.owners index)) same) entry

/-- Frame-index transport retains the whole original Entry heterogeneously. -/
theorem castIndex_heq (frame : OwnerFrame (curve.polynomial.eval point)) {first last : Fin 2} (same : first = last)
    (entry : Entry models point (frame.owners first)) : HEq (castIndex frame same entry) entry := by
  cases same
  rfl

/-- Frame-index transport preserves the actual original old-face sheet. -/
theorem castIndex_sheet (frame : OwnerFrame (curve.polynomial.eval point)) {first last : Fin 2} (same : first = last)
    (entry : Entry models point (frame.owners first)) : (castIndex frame same entry).sheet = entry.sheet := by
  cases same
  rfl

/-- Two actual entries of the SAME supplied Owner in a regular face select the same original sheet.

The retained reachability witnesses are concatenated through a clear
return inside that face. Their zero winding compares the original frame
Owners, and its owned distinction law identifies the two indices. All
auxiliary paths here belong to erased proof evidence, not a new paid trace.
-/
theorem sheet_unique (first last : Entry models point owner) (inside : firstFace.cell.box.Contains point) :
    first.sheet = last.sheet := by
  let reference := (LoopMonodromy.BranchCellBank.referenceAt bank firstFace.cell.box.anchor
    (firstFace.cell.anchor_mem firstFace.member)).toLoop
  have backward := LiftedEdges.Reached.reverse_in_clear_box firstFace.clearance (BranchIsolation.degreePositive curve)
    reference firstFace.cell.box.contains_anchor inside last.reached
  obtain ⟨loop, winding⟩ := first.reached.append backward
  have even : Polynomial.Winding.Polygon.Basic.chainRaw curve.polynomial firstFace.cell.box.anchor loop.vertices =
      8 * (0 : Int) := by
    rewrite [winding]
    omega0
  have equivalent := OwnerPath.rootEquivalent_of_even_with_reference reference loop 0 even
  exact (models.frame.distinguish last.sheet first.sheet equivalent).symm

/-- Operationally equivalent actual Owners have the same original face sheet at one reindexed point.

The coordinate equation transports only the dependent point index. The
supplied operational relation propagates the first actual Entry to the
second Owner; original clear-face uniqueness then identifies the sheets.
No stationary join, observation, frame selection or acquisition is built.
-/
theorem sheet_eq_of_equivalent {otherPoint : Canonical}
    {otherOwner : Owner (curve.polynomial.eval otherPoint)}
    (first : Entry models point owner) (last : Entry models otherPoint otherOwner)
    (samePoint : point = otherPoint)
    (equivalent : NamedEquivalent (ownerName owner) (ownerName otherOwner))
    (inside : firstFace.cell.box.Contains point) : first.sheet = last.sheet := by
  cases samePoint
  let followed := first.followEquivalent equivalent
  exact (first.followEquivalent_sheet equivalent).symm.trans (followed.sheet_unique last inside)

/-- A SAME literal OwnerJoin identifies the selected sheets of two entries in one original face.

The two model/mesh caches remain distinct. Only their shared original
frame readbacks identify the exact frame Owners; the supplied join's
retained relation then connects the actual point Owners. Primitive offsets
and constants are not identified by this root-sheet statement.
-/
theorem sheet_eq_of_join {otherModels : FaceModels frames firstFace}
    {otherOwner : Owner (curve.polynomial.eval point)}
    (first : Entry models point owner) (last : Entry otherModels point otherOwner)
    (join : OwnerJoin owner otherOwner) (inside : firstFace.cell.box.Contains point) :
    first.sheet = last.sheet := by
  have sameFrame : models.frame = otherModels.frame := models.frame_eq.trans otherModels.frame_eq.symm
  have reached : Reached firstFace.cell.box (models.frame.owners last.sheet) otherOwner :=
    Eq.mp (congrArg (fun frame : OwnerFrame (curve.polynomial.eval firstFace.cell.box.anchor) =>
      Reached firstFace.cell.box (frame.owners last.sheet) otherOwner) sameFrame).symm last.reached
  let fromLast : Entry models point owner :=
    ⟨last.sheet, reached.append (Reached.ofEquivalent join.equivalent.symm)⟩
  exact first.sheet_unique fromLast inside

/-- Spell an actually checked original sheet index while transporting the SAME original reachability proof.

This operation does not choose a sheet or compare roots. The owner and
Entry remain whole-value equal to the supplied cache; the new spelling
allows a dependent old domain to reduce at its already checked index.
-/
@[expose] def withSheet (entry : Entry models point owner) (sheet : Fin 2) (same : entry.sheet = sheet) :
    Entry models point owner :=
  ⟨sheet, Eq.mp (congrArg (fun index => Reached firstFace.cell.box (models.frame.owners index) owner) same)
    entry.reached⟩

/-- Checked sheet spelling preserves the complete actual original Entry and its unchanged owner. -/
theorem withSheet_eq (entry : Entry models point owner) (sheet : Fin 2) (same : entry.sheet = sheet) :
    entry.withSheet sheet same = entry := by
  cases entry
  cases same
  rfl

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry

end
