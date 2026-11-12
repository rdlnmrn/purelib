module

public import Purelib.Riemann.RootContinuation.RootContinuationCongruence
import Purelib.Riemann.Branches.PreparedPrimitiveSheets
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Geometry.Rational.Box.Refinement

/-! # Actual advances compared with retained target Owners on the same box

The source and target have their own nonzero radicands and complete Owners.
Their exact initial-box equality transports the actual advance's refinement
into the retained target box. The original track comparison then keeps both
target names without constructing another fixed-budget reference Owner.
-/

public section

namespace Purelib.Riemann.RootContinuation.RootContinuationCongruence

open Purelib
open Purelib.Data.Gaussian
open Purelib.Riemann.Branches
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)

variable {source target : Gaussian} (first : Owner source) (last : Owner target)
    (boxes : first.track.initial.box = last.track.initial.box)
    (small : Norm.Basic.normSq (source - target) < first.track.initial.clearance.bound)

include boxes in
/-- The actual advanced Owner refines the GIVEN target Owner's exact initial box. -/
theorem advance_refines_target (moved : Owner target)
    (factory : moved = first.advance last.parameterNonzero small) :
    moved.track.initial.box.Refines last.track.initial.box := by
  have original := first.advance_initial_box_refines last.parameterNonzero small
  have retained := Eq.mpr (congrArg (fun value : Owner target =>
    value.track.initial.box.Refines first.track.initial.box) factory) original
  exact Eq.mp (congrArg (fun box => moved.track.initial.box.Refines box) boxes) retained

/-- One actual advance and the original comparison with the GIVEN retained target Owner, with both whole factories. -/
@[expose] def Advance :=
  (moved : { value : Owner target // value = first.advance last.parameterNonzero small }) ×
    { compared : NamedEquivalent (ownerRootName moved.val.parameterNonzero moved.val)
        (ownerRootName last.parameterNonzero last) //
      compared = (PreparedPrimitiveSheets.rootEquivalent_of_initial_refines
        last.parameterNonzero last.track moved.val.track
        (advance_refines_target first last boxes small moved.val moved.property)).symm }

/-- Bind one genuine Owner.advance result and compare it once with the SAME supplied target Owner.

The original comparison refines the actual inner track and retains its
operational sampling procedures. No Budget.ownerAt, independent root
selection or desired root-name agreement is used by this constructor.
-/
def advanceTo : Advance first last boxes small :=
  let moved := first.advance last.parameterNonzero small
  let compared := (PreparedPrimitiveSheets.rootEquivalent_of_initial_refines
    last.parameterNonzero last.track moved.track
    (advance_refines_target first last boxes small moved rfl)).symm
  ⟨⟨moved, rfl⟩, ⟨compared, rfl⟩⟩

namespace Advance

variable {first last boxes small} (retained : Advance first last boxes small)

/-- Read the SAME original advanced Owner without running its constructor again. -/
@[expose] def moved : Owner target := retained.1.val

/-- The retained advanced Owner keeps its whole original Owner.advance factory. -/
theorem moved_eq : retained.moved = first.advance last.parameterNonzero small := retained.1.property

/-- Read the SAME operational comparison from the advanced root to the GIVEN target root. -/
@[expose] def compared : NamedEquivalent (ownerRootName retained.moved.parameterNonzero retained.moved)
    (ownerRootName last.parameterNonzero last) := retained.2.val

/-- The comparison keeps its whole original initial-refinement construction factory. -/
theorem compared_eq : retained.compared =
    (PreparedPrimitiveSheets.rootEquivalent_of_initial_refines last.parameterNonzero last.track
      retained.moved.track
      (advance_refines_target first last boxes small retained.moved retained.moved_eq)).symm := retained.2.property

end Advance

end Purelib.Riemann.RootContinuation.RootContinuationCongruence

end
