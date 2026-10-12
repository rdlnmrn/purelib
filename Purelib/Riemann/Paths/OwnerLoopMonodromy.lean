module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.RootContinuation.SquareRootReconditioning
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Winding.Polygon.Basic
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Paths.PreparedPathWinding

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
public import Purelib.Riemann.Paths.PreparedPathClosure
import Purelib.RootIsolation.Track.Basic
import Purelib.RootIsolation.Exact.Ownership.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Data.Gaussian.Field
import Purelib.RootIsolation.Residual.Global.Assignment
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.FTA.Squarefree.Prepare
import Purelib.Polynomial.Dense.Evaluation
import Purelib.RootIsolation.Exact.Basic
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# Root monodromy at an arbitrary base with a winding-one reference loop

The existing branch-anchor return theorem does not cover arbitrary grid
vertices.  A retained clear loop of winding one provides the missing local
reference.  Canonical assignments then follow the parity of every actual
closed owner trace.  The auxiliary reference preparation is proof-only;
reading the monodromy bit does not execute another root continuation.
-/

namespace Purelib.Riemann.Paths.OwnerLoopMonodromy

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients renaming CoefficientPolynomial -> Dense

open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Geometry.Rational (Box)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.RootContinuation

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Paths in
set_option genInjectivity false in
/-- An original cleared loop at the retained base point with raw winding four.

The loop keeps its own ambient box and containment certificate, providing a finite reference for the two-sheet monodromy
comparison. -/
structure WindingOneLoop (polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
  (base : Basic.Canonical) where
  /-- The original ambient box containing the retained reference loop. -/ ambient : Box
  /-- The exact original cleared loop based at the retained point. -/ path : Polynomial.Geometry.ClearPath polynomial
    ambient base base
  /-- Every original loop segment lies in its retained ambient box. -/ within : path.WithinAmbient
  /-- The retained reference loop has exact raw winding four. -/ winding : PreparedPathWinding.ClearPath.rawWinding path
    = 4

constructive_injectivity WindingOneLoop

open Purelib.Curves.Hyperelliptic.Branches in
/-- Act on the original two-element sheet index by the parity of an integer winding.

Even winding retains the supplied sheet; odd winding uses the exact original other-sheet operation. -/
@[expose] def windingSheet (winding : Int) (sheet : Fin 2) : Fin 2 :=
  if winding % 2 = 0 then sheet else BranchCutLifts.otherSheet sheet

/-- Zero winding preserves the original sheet index. -/
theorem windingSheet_zero (sheet : Fin 2) : windingSheet 0 sheet = sheet := rfl

open Purelib.Curves.Hyperelliptic.Branches in
/-- Winding one selects the original opposite sheet. -/
theorem windingSheet_one (sheet : Fin 2) : windingSheet 1 sheet = BranchCutLifts.otherSheet sheet := rfl

/-- The retained sheet value is its original value plus the winding modulo two. -/
theorem windingSheet_val (winding : Int) (sheet : Fin 2) :
    ((windingSheet winding sheet).val : Int) = ((sheet.val : Int) + winding) % 2 := by
  have bound := sheet.isLt
  unfold windingSheet
  split
  · omega
  · change ((1 - sheet.val : Nat) : Int) = _
    omega

/-- Adding integer windings composes their actions on the original sheet index. -/
theorem windingSheet_add (first second : Int) (sheet : Fin 2) :
    windingSheet (first + second) sheet = windingSheet second (windingSheet first sheet) := by
  apply Fin.ext
  have left := windingSheet_val (first + second) sheet
  have right := windingSheet_val second (windingSheet first sheet)
  have middle := windingSheet_val first sheet
  omega

open Purelib.Curves.Hyperelliptic.Branches in
/-- Applying the same winding action twice restores the original sheet index. -/
theorem windingSheet_twice (winding : Int) (sheet : Fin 2) :
    windingSheet winding (windingSheet winding sheet) = sheet := by
  by_cases even : winding % 2 = 0
  · rw [windingSheet, if_pos even, windingSheet, if_pos even]
  · rw [windingSheet, if_neg even, windingSheet, if_neg even, BranchCutLifts.otherSheet_other]

/-- Negating the winding preserves its action on the original two-element sheet index. -/
theorem windingSheet_neg (winding : Int) (sheet : Fin 2) :
    windingSheet (-winding) sheet = windingSheet winding sheet := by
  apply Fin.ext
  have left := windingSheet_val (-winding) sheet
  have right := windingSheet_val winding sheet
  omega

namespace OwnerPath

variable {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {base :
  Purelib.Data.Gaussian.Basic.Canonical}
  {first last : Owner (polynomial.eval base)}

section
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Polynomial
open Purelib.Riemann.Paths
/-- An original owner loop of odd winding swaps its two retained canonical root assignments. -/
theorem assignment_swaps_of_odd (path : OwnerPath polynomial base first base last) (turns : Int)
    (odd : Winding.Polygon.Basic.chainRaw polynomial base path.vertices = 4 * (2 * turns + 1)) :
    (SquareRootReconditioning.assignment first.parameterNonzero last).owner.owner =
      BranchCutLifts.otherSheet (SquareRootReconditioning.assignment first.parameterNonzero first).owner.owner := by
  let firstIndex : Fin 2 := (SquareRootReconditioning.assignment first.parameterNonzero first).owner.owner
  let lastIndex : Fin 2 := (SquareRootReconditioning.assignment first.parameterNonzero last).owner.owner
  have different : lastIndex ≠ firstIndex := by
    intro equal
    exact path.not_odd_of_return (PreparedPathClosure.SquareRootTrace.rootEquivalent_of_assignment_eq
      first.parameterNonzero first last equal)
      turns ((PreparedPathClosure.SquareRootTrace.OwnerPath.closedRaw_eq_chainRaw path).trans odd)
  have values : lastIndex.val ≠ firstIndex.val := fun equal => different (Fin.ext equal)
  have firstBound : firstIndex.val < 2 := firstIndex.isLt
  have lastBound : lastIndex.val < 2 := lastIndex.isLt
  apply Fin.ext
  change lastIndex.val = 1 - firstIndex.val
  omega

/-- Even winding preserves canonical endpoint assignments when an original winding-one reference loop is retained.

If the assignments differed, appending the traced reference loop would produce an odd owner loop returning to an
equivalent root name. -/
theorem assignment_eq_of_even_with_reference (reference : WindingOneLoop polynomial base)
    (path : OwnerPath polynomial base first base last) (turns : Int)
    (even : Winding.Polygon.Basic.chainRaw polynomial base path.vertices = 8 * turns) :
    (SquareRootReconditioning.assignment first.parameterNonzero last).owner.owner =
      (SquareRootReconditioning.assignment first.parameterNonzero first).owner.owner := by
  by_cases equal : (SquareRootReconditioning.assignment first.parameterNonzero last).owner.owner =
      (SquareRootReconditioning.assignment first.parameterNonzero first).owner.owner
  · exact equal
  · let boundary := PreparedPathTrace.TracedPath.build reference.path reference.within last
    let firstIndex : Fin 2 := (SquareRootReconditioning.assignment first.parameterNonzero first).owner.owner
    let lastIndex : Fin 2 := (SquareRootReconditioning.assignment first.parameterNonzero last).owner.owner
    have swapped : (SquareRootReconditioning.assignment first.parameterNonzero boundary.finishOwner).owner.owner =
        BranchCutLifts.otherSheet lastIndex :=
      assignment_swaps_of_odd boundary.trace.get 0
        ((PreparedPathWinding.PreparedClearPathModels.TracedPath.winding_original boundary).trans reference.winding)
    have opposite : BranchCutLifts.otherSheet lastIndex = firstIndex := by
      have different : lastIndex.val ≠ firstIndex.val := fun same => equal (Fin.ext same)
      have firstBound : firstIndex.val < 2 := firstIndex.isLt
      have lastBound : lastIndex.val < 2 := lastIndex.isLt
      apply Fin.ext
      change 1 - lastIndex.val = firstIndex.val
      omega
    let returned := PreparedPathClosure.SquareRootTrace.rootEquivalent_of_assignment_eq first.parameterNonzero first
      boundary.finishOwner (swapped.trans opposite)
    let joined := path.append boundary.trace.get
    have odd : Winding.Polygon.Basic.closedRaw polynomial base joined.vertices = 4 * (2 * turns + 1) := by
      rw [PreparedPathClosure.SquareRootTrace.OwnerPath.closedRaw_eq_chainRaw joined,
        OwnerTracePath.OwnerPath.append_vertices, Winding.Polygon.Basic.chainRaw_append,
        path.vertices_terminal, even, PreparedPathWinding.PreparedClearPathModels.TracedPath.winding_original boundary,
          reference.winding]
      omega
    exact (joined.not_odd_of_return returned turns odd).elim

end

open Purelib.Polynomial in
/-- The original owner-loop endpoint assignment is the initial assignment acted on by its exact winding parity. -/
theorem assignment_windingSheet (reference : WindingOneLoop polynomial base)
    (path : OwnerPath polynomial base first base last) (winding : Int)
    (raw : Winding.Polygon.Basic.chainRaw polynomial base path.vertices = 4 * winding) :
    (SquareRootReconditioning.assignment first.parameterNonzero last).owner.owner =
      windingSheet winding (SquareRootReconditioning.assignment first.parameterNonzero first).owner.owner := by
  by_cases even : winding % 2 = 0
  · rw [windingSheet, if_pos even]
    apply assignment_eq_of_even_with_reference reference path (winding / 2)
    omega
  · rw [windingSheet, if_neg even]
    apply assignment_swaps_of_odd path (winding / 2)
    omega

open Purelib.Approximation.Gaussian in
open Purelib.Polynomial in
open Purelib.Riemann.Paths in
/-- Compare the original endpoint root names of an even owner loop using its retained winding-one reference.

The exact canonical-assignment equality is transported through the original reconditioning bridges. -/
@[expose] def rootEquivalent_of_even_with_reference (reference : WindingOneLoop polynomial base)
    (path : OwnerPath polynomial base first base last) (turns : Int)
    (even : Winding.Polygon.Basic.chainRaw polynomial base path.vertices = 8 * turns) :
    Equivalence.NamedEquivalent (ownerName last) (ownerName first) :=
  PreparedPathClosure.SquareRootTrace.rootEquivalent_of_assignment_eq first.parameterNonzero first last
    (assignment_eq_of_even_with_reference reference path turns even)

end OwnerPath

end Purelib.Riemann.Paths.OwnerLoopMonodromy
