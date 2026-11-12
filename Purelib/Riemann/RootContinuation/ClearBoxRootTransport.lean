module
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathTrace
public import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Winding.Polygon.Basic
public import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Riemann.Paths.PreparedPathClosure
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Polynomial.Clearance.Box.Region

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
public import Purelib.Riemann.Paths.ClearBoxPathWinding
import Purelib.Riemann.RootContinuation.RootPathTransport
import Purelib.Riemann.RootContinuation.RootPathTransport.RoundTrip
import Purelib.Data.Int.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Vector.Basic
import Purelib.Tactic.QuotientFreeOmega

@[expose] public section

/-!
# Operational path independence on a cleared face

Equal winding forces equal endpoint occurrences for two actual traced paths
from the same owner. One winding-one reference at their common source is
enough: a reverse transport has a right inverse on the finite two-owner frame,
and therefore is injective. Auxiliary transports occur only in that proof.
The returned operational comparison consumes the checked endpoint selections.
Full-box clearance discharges winding equality for all contained routes,
including routes presented in different ambient boxes.
-/

namespace Purelib.Riemann.RootContinuation.ClearBoxRootTransport

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients renaming CoefficientPolynomial -> Dense

open _root_.Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Geometry.Rational (Box)
open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame OwnerSelection)
open Purelib.Riemann.RootContinuation.RootPathTransport (PathTransport)

/-- A two-sheet index equals its first or second retained coordinate.

Natural constructor cases use the original strict bound to exclude every
further successor, retaining the same finite carrier and coordinate numerals. -/
private theorem two_cases (index : Fin 2) : index = 0 ∨ index = 1 := by
  rcases index with ⟨value, bound⟩
  cases value with
  | zero => exact Or.inl rfl
  | succ value =>
      cases value with
      | zero => exact Or.inr rfl
      | succ value =>
          exact False.elim (Nat.not_lt_zero value
            (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ bound)))

/-- A left inverse between two-sheet maps is also a right inverse.

The two original images are distinct by the supplied inverse equations. Their
finite coordinate cases identify both images and the returned original index. -/
private theorem two_right_inverse (forward backward : Fin 2 → Fin 2)
    (undo : ∀ index, backward (forward index) = index) (index : Fin 2) :
    forward (backward index) = index := by
  have first := undo 0
  have second := undo 1
  rcases two_cases (forward 0) with firstImage | firstImage <;>
    rcases two_cases (forward 1) with secondImage | secondImage
  · rw [firstImage] at first
    rw [secondImage, first] at second
    have impossible := congrArg Fin.val second
    change 0 = 1 at impossible
    cases impossible
  · rw [firstImage] at first
    rw [secondImage] at second
    rcases two_cases index with equal | equal
    · rw [equal, first, firstImage]
    · rw [equal, second, secondImage]
  · rw [firstImage] at first
    rw [secondImage] at second
    rcases two_cases index with equal | equal
    · rw [equal, second, secondImage]
    · rw [equal, first, firstImage]
  · rw [firstImage] at first
    rw [secondImage, first] at second
    have impossible := congrArg Fin.val second
    change 0 = 1 at impossible
    cases impossible

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Paths in
open Purelib.Riemann.RootContinuation in
/-- The retained zero-winding return transport recovers the original selected source-frame index. -/
private theorem return_index {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {returnAmbient : Box}
    {start finish : Basic.Canonical}
    {backPath : Polynomial.Geometry.ClearPath polynomial returnAmbient finish start} {owner : Owner (polynomial.eval
      start)}
    {last : Owner (polynomial.eval finish)}
    (reference : WindingOneLoop polynomial start) (traced : OwnerPath polynomial start owner finish last)
    (firstFrame : OwnerFrame (polynomial.eval start)) (lastFrame : OwnerFrame (polynomial.eval finish))
    (source : OwnerSelection firstFrame.owners owner)
    (selected : OwnerSelection lastFrame.owners last)
    (backward : PathTransport backPath lastFrame firstFrame)
    (cancel : Winding.Polygon.Basic.chainRaw polynomial start traced.vertices + PreparedPathWinding.ClearPath.rawWinding
      backPath = 0) :
    backward.target selected.index = source.index := by
  let joined := traced.append
    ((RootPathTransport.OwnerPath.join polynomial finish last (lastFrame.owners selected.index)
      selected.equivalent).append
      (backward.row selected.index).joined)
  have winding : Winding.Polygon.Basic.chainRaw polynomial start joined.vertices = 8 * (0 : Int) := by
    rw [RootPathTransport.OwnerPath.append_winding, RootPathTransport.OwnerPath.append_winding,
      RootPathTransport.OwnerPath.join_winding, RootPathTransport.TransportRow.joined_winding]
    omega
  let returned := OwnerLoopMonodromy.OwnerPath.rootEquivalent_of_even_with_reference reference joined 0 winding
  exact firstFrame.distinguish _ _ (returned.trans source.equivalent)

end Purelib.Riemann.RootContinuation.ClearBoxRootTransport

namespace Purelib.Riemann.RootContinuation.ClearBoxRootTransport.TracedPath

open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)
open Purelib.Riemann.RootContinuation.RootPathTransport (PathTransport)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame OwnerSelection)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame OwnerSelection)
open Purelib.Riemann.RootContinuation.RootPathTransport (PathTransport)

variable {polynomial : Purelib.Polynomial.Geometry.ClearPath.GaussianPolynomial} {firstAmbient secondAmbient :
  Purelib.Geometry.Rational.Box} {start finish : Purelib.Data.Gaussian.Basic.Canonical}
  {firstPath : Polynomial.Geometry.ClearPath polynomial firstAmbient start finish}
  {secondPath : Polynomial.Geometry.ClearPath polynomial secondAmbient start finish} {owner : Owner
    (polynomial.eval start)}

open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.Polynomial in
open Purelib.Riemann.Paths in
/-- Equal raw winding forces the original traced and owner-path finishes to select the same frame index.

Both paths keep the same initial owner; a retained reference loop and the actual reverse clear-path transport certify
equality of their selected final sheets. -/
theorem selection_eq_of_ownerPath (reference : WindingOneLoop polynomial start)
    (within : firstPath.WithinAmbient) (first : TracedPath firstPath owner)
    {last : Owner (polynomial.eval finish)} (second : OwnerPath polynomial start owner finish last)
    (frame : OwnerFrame (polynomial.eval finish))
    (left : OwnerSelection frame.owners first.finishOwner) (right : OwnerSelection frame.owners last)
    (winding : PreparedPathWinding.ClearPath.rawWinding firstPath = Winding.Polygon.Basic.chainRaw polynomial start
      second.vertices) :
    left.index = right.index := by
  let sourceFrame := OwnerFrame.build owner.parameterNonzero
  let source := sourceFrame.select owner
  let backward := PathTransport.build (BranchCutLifts.ClearPath.reverse firstPath)
    (BranchCutLifts.ClearPath.reverse_withinAmbient firstPath within) frame sourceFrame
  let forward := PathTransport.build firstPath within sourceFrame frame
  have cancel : PreparedPathWinding.ClearPath.rawWinding firstPath + PreparedPathWinding.ClearPath.rawWinding
    (BranchCutLifts.ClearPath.reverse firstPath) = 0 := by
    rw [PreparedPathClosure.ClearPath.rawWinding_reverse]
    omega
  have firstReturn := return_index reference first.trace.get sourceFrame frame source left backward (by
    rw [PreparedPathWinding.PreparedClearPathModels.TracedPath.winding_original first]
    exact cancel)
  have secondReturn := return_index reference second sourceFrame frame source right backward (by
    rw [← winding]
    exact cancel)
  have undo (index : Fin 2) : backward.target (forward.target index) = index :=
    forward.roundTrip_index reference backward cancel index
  have leftUndo := two_right_inverse forward.target backward.target undo left.index
  have rightUndo := two_right_inverse forward.target backward.target undo right.index
  rw [firstReturn] at leftUndo
  rw [secondReturn] at rightUndo
  exact leftUndo.symm.trans rightUndo

open Purelib.Approximation.Gaussian in
open Purelib.Polynomial in
open Purelib.Riemann.Paths in
/-- Compare original finish-owner names through equal-winding selections in the same retained frame. -/
def equivalentOfOwnerPathSelections (reference : WindingOneLoop polynomial start)
    (within : firstPath.WithinAmbient) (first : TracedPath firstPath owner)
    {last : Owner (polynomial.eval finish)} (second : OwnerPath polynomial start owner finish last)
    (frame : OwnerFrame (polynomial.eval finish))
    (left : OwnerSelection frame.owners first.finishOwner) (right : OwnerSelection frame.owners last)
    (winding : PreparedPathWinding.ClearPath.rawWinding firstPath = Winding.Polygon.Basic.chainRaw polynomial start
      second.vertices) :
    Equivalence.NamedEquivalent (ownerName first.finishOwner) (ownerName last) :=
  left.equivalent.trans (by
    rw [selection_eq_of_ownerPath reference within first second frame left right winding]
    exact right.equivalent.symm)

open Purelib.Approximation.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Clearance.Box in
open Purelib.Riemann.Paths in
/-- Compare the original finish owners of two clear paths contained in one certified clear box.

The paths retain their shared initial owner and endpoints; positive polynomial degree and the original winding-one
reference prove matching winding and target-frame selections. -/
def equivalentOfInBox {box : Box} (clearance : Region.RegionClearance polynomial box)
    (degreePositive : 0 < polynomial.natDegree) (reference : WindingOneLoop polynomial start)
    (within : firstPath.WithinAmbient) (first : TracedPath firstPath owner) (second : TracedPath secondPath owner)
    (firstInside : Polynomial.Geometry.ClearPath.InBox box firstPath) (secondInside :
      Polynomial.Geometry.ClearPath.InBox
      box secondPath)
    (frame : OwnerFrame (polynomial.eval finish)) :
    Equivalence.NamedEquivalent (ownerName first.finishOwner) (ownerName second.finishOwner) :=
  equivalentOfOwnerPathSelections reference within first second.trace.get frame
    (frame.select first.finishOwner) (frame.select second.finishOwner) (by
      rw [PreparedPathWinding.PreparedClearPathModels.TracedPath.winding_original second]
      exact ClearBoxPathWinding.ClearPath.rawWinding_eq_of_inBox clearance degreePositive firstPath secondPath
        firstInside secondInside)

end Purelib.Riemann.RootContinuation.ClearBoxRootTransport.TracedPath

end

public section

namespace Purelib.Riemann.RootContinuation.ClearBoxRootTransport

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Winding.Polygon.Basic (chainRaw)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame OwnerSelection)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

/-- An even return loop compares its actual endpoint readings through their original retained frame selections.

The two original owner paths meet through the supplied stationary root
comparison. Their combined winding and original reference identify the
saved frame indices. The returned operational comparison consumes those
same selections without classifying either endpoint owner again.
-/
def equivalentOfReturnSelections {polynomial : CoefficientPolynomial} {start middle : Canonical}
    {first : Owner (polynomial.eval start)} {returnedOwner enteredOwner : Owner (polynomial.eval middle)}
    {last : Owner (polynomial.eval start)}
    (reference : WindingOneLoop polynomial start)
    (returned : OwnerPath polynomial start first middle returnedOwner)
    (handoff : NamedEquivalent (ownerName returnedOwner) (ownerName enteredOwner))
    (entered : OwnerPath polynomial middle enteredOwner start last)
    (frame : OwnerFrame (polynomial.eval start))
    (before : OwnerSelection frame.owners first) (after : OwnerSelection frame.owners last)
    (turns : Int)
    (winding : chainRaw polynomial start returned.vertices +
      chainRaw polynomial middle entered.vertices = 8 * turns) :
    NamedEquivalent (ownerName last) (ownerName first) := by
  let joined := returned.append
    ((RootPathTransport.OwnerPath.join polynomial middle returnedOwner enteredOwner handoff).append entered)
  have joinedWinding : chainRaw polynomial start joined.vertices = 8 * turns := by
    rewrite [RootPathTransport.OwnerPath.append_winding, RootPathTransport.OwnerPath.append_winding,
      RootPathTransport.OwnerPath.join_winding, Data.Int.Arithmetic.zero_add]
    exact winding
  let automatic := OwnerLoopMonodromy.OwnerPath.rootEquivalent_of_even_with_reference
    reference joined turns joinedWinding
  have same : after.index = before.index := frame.distinguish _ _
    (NamedEquivalent.trans (left := ownerName (frame.owners after.index))
      (middle := ownerName last) (right := ownerName (frame.owners before.index))
      (NamedEquivalent.symm (left := ownerName last)
        (right := ownerName (frame.owners after.index)) after.equivalent)
      (NamedEquivalent.trans (left := ownerName last) (middle := ownerName first)
        (right := ownerName (frame.owners before.index)) automatic before.equivalent))
  let backward : NamedEquivalent (ownerName (frame.owners before.index)) (ownerName first) :=
    NamedEquivalent.symm (left := ownerName first)
      (right := ownerName (frame.owners before.index)) before.equivalent
  let aligned : NamedEquivalent (ownerName (frame.owners after.index)) (ownerName first) :=
    NamedEquivalent.transport
      (congrArg (fun index : Fin 2 => ownerName (frame.owners index)) same.symm) rfl backward
  exact NamedEquivalent.trans (left := ownerName last)
    (middle := ownerName (frame.owners after.index)) (right := ownerName first) after.equivalent aligned

end Purelib.Riemann.RootContinuation.ClearBoxRootTransport

end

public section

open Purelib.Riemann.Paths

namespace Purelib.Riemann.RootContinuation.ClearBoxRootTransport.TracedPath

open Purelib
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients renaming CoefficientPolynomial -> Dense
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Polynomial.Winding.Polygon.Basic (chainRaw)
open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame OwnerSelection)
open Purelib.Riemann.RootContinuation.RootPathTransport (PathTransport)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {polynomial : Dense} {ambient : Box} {start finish : Canonical}
variable {path : ClearPath polynomial ambient start finish} {owner : Owner (polynomial.eval start)}

/-- Equal winding identifies actual finish selections from the retained opposite-endpoint reference.

The original trace and supplied owner path keep their identical starting
Owner. Both actual finish selections are read in the same supplied frame.
The mixed-row inverse argument uses the original target reference; no
reference at the possibly interior initial point is assumed.
-/
theorem selection_eq_of_ownerPath_from_finish (reference : WindingOneLoop polynomial finish)
    (within : path.WithinAmbient) (first : TracedPath path owner)
    {last : Owner (polynomial.eval finish)} (second : OwnerPath polynomial start owner finish last)
    (frame : OwnerFrame (polynomial.eval finish))
    (left : OwnerSelection frame.owners first.finishOwner) (right : OwnerSelection frame.owners last)
    (winding : PreparedPathWinding.ClearPath.rawWinding path = chainRaw polynomial start second.vertices) :
    left.index = right.index := by
  let sourceFrame := OwnerFrame.build owner.parameterNonzero
  let source := sourceFrame.select owner
  let forward := PathTransport.build path within sourceFrame frame
  let backward := PathTransport.build (BranchCutLifts.ClearPath.reverse path)
    (BranchCutLifts.ClearPath.reverse_withinAmbient path within) frame sourceFrame
  have targetIndex {actual : Owner (polynomial.eval finish)}
      (traced : OwnerPath polynomial start owner finish actual) (selected : OwnerSelection frame.owners actual)
      (paid : chainRaw polynomial start traced.vertices = PreparedPathWinding.ClearPath.rawWinding path) :
      selected.index = forward.target source.index := by
    let canonical :=
      (RootPathTransport.OwnerPath.join polynomial start (sourceFrame.owners source.index) owner
        source.equivalent.symm).append
        (traced.append (RootPathTransport.OwnerPath.join polynomial finish actual
          (frame.owners selected.index) selected.equivalent))
    have canonicalWinding : chainRaw polynomial start canonical.vertices =
        PreparedPathWinding.ClearPath.rawWinding path := by
      dsimp only [canonical]
      rewrite [RootPathTransport.OwnerPath.append_winding, RootPathTransport.OwnerPath.join_winding,
        RootPathTransport.OwnerPath.append_winding, RootPathTransport.OwnerPath.join_winding,
        Data.Int.Arithmetic.zero_add, Int.add_zero]
      exact paid
    exact RootPathTransport.OwnerPath.target_index sourceFrame frame reference forward.target backward.target
      (fun index => (forward.row index).joined) (fun index => (backward.row index).joined)
      (PreparedPathWinding.ClearPath.rawWinding path)
      (fun index => (forward.row index).joined_winding)
      (fun index => (backward.row index).joined_winding.trans
        (Paths.PreparedPathClosure.ClearPath.rawWinding_reverse path))
      source.index selected.index canonical canonicalWinding
  exact (targetIndex first.trace.get left
    (Paths.PreparedPathWinding.PreparedClearPathModels.TracedPath.winding_original first)).trans
      (targetIndex second right winding.symm).symm

/-- Compare original finish names through the same selections and an opposite-endpoint reference.

The returned Type-valued comparison consumes the two supplied selections.
Its proof uses the original actual trace and owner path, including all
connector windings; it neither identifies those paths nor replaces their
primitive observations.
-/
def equivalentOfOwnerPathSelectionsFromFinish (reference : WindingOneLoop polynomial finish)
    (within : path.WithinAmbient) (first : TracedPath path owner)
    {last : Owner (polynomial.eval finish)} (second : OwnerPath polynomial start owner finish last)
    (frame : OwnerFrame (polynomial.eval finish))
    (left : OwnerSelection frame.owners first.finishOwner) (right : OwnerSelection frame.owners last)
    (winding : PreparedPathWinding.ClearPath.rawWinding path = chainRaw polynomial start second.vertices) :
    NamedEquivalent (ownerName first.finishOwner) (ownerName last) :=
  left.equivalent.trans (by
    rewrite [selection_eq_of_ownerPath_from_finish reference within first second frame left right winding]
    exact right.equivalent.symm)

/-- The actual reversed trace returns an equivalent original root from the retained far-end reference.

The displayed forward trace remains unchanged. Both finite transport maps
are built on the same original path and its reverse, while their inverse
proof uses only the reference at the actual far endpoint. The returned
comparison retains the original initial and actual returned root names.
-/
def reverseEquivalentFromFinish (reference : WindingOneLoop polynomial finish)
    (within : path.WithinAmbient) (first : TracedPath path owner)
    (returned : TracedPath (BranchCutLifts.ClearPath.reverse path) first.finishOwner) :
    NamedEquivalent (ownerName returned.finishOwner) (ownerName owner) := by
  let sourceFrame := OwnerFrame.build owner.parameterNonzero
  let targetFrame := OwnerFrame.build first.finishOwner.parameterNonzero
  let source := sourceFrame.select owner
  let entered := targetFrame.select first.finishOwner
  let selected := sourceFrame.select returned.finishOwner
  let forward := PathTransport.build path within sourceFrame targetFrame
  let backward := PathTransport.build (BranchCutLifts.ClearPath.reverse path)
    (BranchCutLifts.ClearPath.reverse_withinAmbient path within) targetFrame sourceFrame
  let outward := (RootPathTransport.OwnerPath.join polynomial start owner
    (sourceFrame.owners source.index) source.equivalent).append (forward.row source.index).joined
  have outwardWinding : PreparedPathWinding.ClearPath.rawWinding path =
      chainRaw polynomial start outward.vertices := by
    dsimp only [outward]
    rewrite [RootPathTransport.OwnerPath.append_winding, RootPathTransport.OwnerPath.join_winding,
      RootPathTransport.TransportRow.joined_winding, Data.Int.Arithmetic.zero_add]
    rfl
  have forwardIndex := selection_eq_of_ownerPath_from_finish reference within first outward targetFrame entered
    ⟨forward.target source.index, NamedEquivalent.refl _⟩ outwardWinding
  let inward := (RootPathTransport.OwnerPath.join polynomial finish first.finishOwner
    (targetFrame.owners entered.index) entered.equivalent).append (backward.row entered.index).joined
  have inwardWinding : PreparedPathWinding.ClearPath.rawWinding (BranchCutLifts.ClearPath.reverse path) =
      chainRaw polynomial finish inward.vertices := by
    dsimp only [inward]
    rewrite [RootPathTransport.OwnerPath.append_winding, RootPathTransport.OwnerPath.join_winding,
      RootPathTransport.TransportRow.joined_winding, Data.Int.Arithmetic.zero_add]
    rfl
  have backwardIndex := selection_eq_of_ownerPath reference
    (BranchCutLifts.ClearPath.reverse_withinAmbient path within) returned inward sourceFrame selected
    ⟨backward.target entered.index, NamedEquivalent.refl _⟩ inwardWinding
  have inverse := backward.reverseRoundTrip_index reference forward (by
    rewrite [Paths.PreparedPathClosure.ClearPath.rawWinding_reverse]
    omega0) source.index
  have same : selected.index = source.index :=
    backwardIndex.trans ((congrArg backward.target forwardIndex).trans inverse)
  exact selected.equivalent.trans (NamedEquivalent.transport
    (congrArg (fun index => ownerName (sourceFrame.owners index)) same).symm rfl source.equivalent.symm)

end Purelib.Riemann.RootContinuation.ClearBoxRootTransport.TracedPath

end
