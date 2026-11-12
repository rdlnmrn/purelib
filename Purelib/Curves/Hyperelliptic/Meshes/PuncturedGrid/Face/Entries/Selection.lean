module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Interior
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Comparison
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames

/-! # A second actual Owner classified in the SAME retained Entry route banks

The original point frame, two routes and both complete transport banks are
reused literally. Only the original point-frame selector and original Entry
factory are applied to the new supplied Owner, once each and in that order.
The original acquisition stays a separate input and is never overwritten.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry.Acquisition

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame OwnerSelection)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
variable {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face : RegularFace bank}
variable {models : FaceModels frames face} {point : Canonical}
variable {inside : face.cell.box.Contains point} {owner : Owner (curve.polynomial.eval point)}

/-- Retain a supplied original frame selection with all five unchanged acquisition geometry and transport caches.

The selector and its whole original factory equation are given retained
values. Only ofRoundTrip constructs the new Entry. This operation neither
runs the selector again nor prepares a frame, route or transport bank.
-/
@[expose] def ofSelection (acquired : Acquisition models inside owner)
    (next : Owner (curve.polynomial.eval point))
    (selected : OwnerSelection acquired.pointFrame.owners next)
    (selected_eq : selected = acquired.pointFrame.select next) : Acquisition models inside next :=
  let entry := ofRoundTrip models inside acquired.pointFrame acquired.outward acquired.inward acquired.forward
    acquired.backward selected
  ⟨⟨acquired.pointFrame, acquired.pointFrame_eq⟩,
    ⟨acquired.outward, acquired.outward_eq⟩, ⟨acquired.inward, acquired.inward_eq⟩,
    ⟨acquired.forward, acquired.forward_eq⟩, ⟨acquired.backward, acquired.backward_eq⟩,
    ⟨selected, selected_eq⟩, ⟨entry, rfl⟩⟩

/-- Classify a supplied second actual Owner in the SAME cached point frame and two-way route banks.

The original seven-cache Acquisition already expresses the required
invariant. All five geometry/transport caches and their whole factory
identities are retained; only its last two original factories execute.
The frame's original nonzero proof is proof-irrelevant at this same exact
polynomial parameter, which does not identify the two actual Owners.
-/
@[expose] def selectOwner (acquired : Acquisition models inside owner) (next : Owner (curve.polynomial.eval point)) :
    Acquisition models inside next :=
  let selected := acquired.pointFrame.select next
  ofSelection acquired next selected rfl

/-- Reclassification is the complete original seven-cache construction on the retained input. -/
private theorem selectOwner_factory (acquired : Acquisition models inside owner)
    (next : Owner (curve.polynomial.eval point)) : selectOwner acquired next =
  let selected := acquired.pointFrame.select next
  let entry := ofRoundTrip models inside acquired.pointFrame acquired.outward acquired.inward acquired.forward
    acquired.backward selected
  ⟨⟨acquired.pointFrame, acquired.pointFrame_eq⟩,
    ⟨acquired.outward, acquired.outward_eq⟩, ⟨acquired.inward, acquired.inward_eq⟩,
    ⟨acquired.forward, acquired.forward_eq⟩, ⟨acquired.backward, acquired.backward_eq⟩,
    ⟨selected, rfl⟩, ⟨entry, rfl⟩⟩ := rfl

/-- The complete forward view reads the literal retained bank with its original dependent parents. -/
private theorem forward_readback (acquired : Acquisition models inside owner) :
    HEq acquired.forward acquired.2.2.2.1.val := HEq.refl acquired.2.2.2.1.val

/-- The target permutation reads that same original retained forward bank. -/
private theorem forward_target_readback (acquired : Acquisition models inside owner) (sheet : Fin 2) :
    acquired.forward.target sheet = acquired.2.2.2.1.val.target sheet := rfl

variable (acquired : Acquisition models inside owner) (next : Owner (curve.polynomial.eval point))

/-- Supplying the retained actual selector yields the complete original selectOwner value.

Equality elimination changes no cache. The statement records the whole
acquisition, including its original selector and Entry factory fields.
-/
theorem ofSelection_eq_selectOwner (selected : OwnerSelection acquired.pointFrame.owners next)
    (selected_eq : selected = acquired.pointFrame.select next) :
    ofSelection acquired next selected selected_eq = acquired.selectOwner next := by
  cases selected_eq
  rfl

/-- Reclassification reuses the complete original point frame, rather than executing isolation again. -/
theorem selectOwner_pointFrame : (acquired.selectOwner next).pointFrame = acquired.pointFrame :=
  Eq.trans (acquired.selectOwner next).pointFrame_eq (Eq.symm acquired.pointFrame_eq)

/-- Reclassification reuses the SAME full forward bank at its exact original route/frame indices. -/
theorem selectOwner_forward : HEq (acquired.selectOwner next).forward acquired.forward :=
  let rebuilt : HEq (acquired.selectOwner next).2.2.2.1.val acquired.forward :=
    Eq.mpr (congrArg (fun value : Acquisition models inside next =>
        HEq value.2.2.2.1.val acquired.forward) (selectOwner_factory acquired next))
      (HEq.refl acquired.forward)
  HEq.trans (forward_readback (acquired.selectOwner next)) rebuilt

/-- Reclassification retains the original forward target permutation on every exact sheet index. -/
theorem selectOwner_forward_target (sheet : Fin 2) :
    (acquired.selectOwner next).forward.target sheet = acquired.forward.target sheet :=
  let rebuilt : (acquired.selectOwner next).2.2.2.1.val.target sheet = acquired.forward.target sheet :=
    Eq.mpr (congrArg (fun value : Acquisition models inside next =>
        value.2.2.2.1.val.target sheet = acquired.forward.target sheet) (selectOwner_factory acquired next))
      (Eq.refl (acquired.forward.target sheet))
  Eq.trans (forward_target_readback (acquired.selectOwner next) sheet) rebuilt

/-- A retained reclassification selects the old frame occurrence through an actual same-sheet face Entry.

The Entry belongs to the supplied second Owner, and its sheet equation
comes from that Owner's original continued lineage. Uniqueness compares
it to the retained reclassification's actual Entry. The two cached
round-trip laws then identify their original point-frame indices; no
root relation is inferred from coordinates or from a bare sheet label.
-/
theorem selectOwner_index (selected : Acquisition models inside next)
    (selected_eq : selected = acquired.selectOwner next)
    (entry : Entry models point next) (same : entry.sheet = acquired.entry.sheet) :
    selected.selected.index = acquired.selected.index := by
  have sheet : selected.entry.sheet = acquired.entry.sheet :=
    (selected.entry.sheet_unique entry inside).trans same
  have target : selected.forward.target selected.entry.sheet = acquired.forward.target selected.entry.sheet := by
    cases selected_eq
    exact acquired.selectOwner_forward_target next _
  exact selected.target_eq.symm.trans (target.trans
    ((congrArg acquired.forward.target sheet).trans acquired.target_eq))

/-- Compare two original Owners through their actual retained selectors and the same face Entry lineage.

The supplied reclassification is kept with its whole selectOwner factory
equation. The complete point-frame readback and the derived equality of
actual selected indices transport its original comparison, which is then
composed with the old selector's inverse. Neither selector, frame, route,
transport bank, Point nor numerical reading is prepared again.
-/
def equivalentOfEntry (selected : Acquisition models inside next)
    (selected_eq : selected = acquired.selectOwner next)
    (entry : Entry models point next) (same : entry.sheet = acquired.entry.sheet) :
    NamedEquivalent (ownerName next) (ownerName owner) := by
  have index : selected.selected.index = acquired.selected.index :=
    acquired.selectOwner_index next selected selected_eq entry same
  have frame : selected.pointFrame = acquired.pointFrame :=
    (congrArg (fun current : Acquisition models inside next => current.pointFrame) selected_eq).trans
      (acquired.selectOwner_pointFrame next)
  have name := (congrArg (fun current : OwnerFrame (curve.polynomial.eval point) =>
    ownerName (current.owners selected.selected.index)) frame).trans
      (congrArg (fun current => ownerName (acquired.pointFrame.owners current)) index)
  exact (NamedEquivalent.transport rfl name selected.selected.equivalent).trans acquired.selected.equivalent.symm

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry.Acquisition

end
