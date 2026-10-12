module
import Purelib.Data.Int.Arithmetic
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.RootContinuation.SquareRootReconditioning
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Winding.Polygon.Basic
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Polynomial.Winding.Polygon.Stationary

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
public import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RootIsolation.Track.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.RootIsolation.Exact.Ownership.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Data.Gaussian.Field
import Purelib.RootIsolation.Residual.Global.Assignment
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.FTA.Squarefree.Prepare
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Polynomial.Dense.Evaluation
import Purelib.RootIsolation.Exact.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Tactic.QuotientFreeOmega

/-!
# Operational closure of even-winding prepared root paths

The two executable canonical owners exhaust the square roots of a nonzero
parameter.  An even-winding path cannot change its canonical owner: appending
a winding-one branch boundary would otherwise produce an odd-winding return.
The positive return witness is built from the existing finite owner bridges,
not from an equality of sheet labels or a completed square root.
-/

namespace Purelib.Riemann.Paths.PreparedPathClosure

open Purelib.Data

public section

namespace ClearSegment

open Purelib.Riemann.Paths.PreparedPathWinding.ClearSegment (rawWinding rawWinding_eq_coordinateWinding)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Paths.PreparedClearPathModels (GaussianPolynomial Box)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
/-- Reversing the original cleared segment negates its raw winding. -/
theorem rawWinding_reverse {polynomial : Basic.GaussianPolynomial} {ambient : Purelib.Geometry.Rational.Box} {start
  finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) :
    rawWinding (BranchCutLifts.ClearSegment.reverse segment) = -rawWinding segment := by
  rw [rawWinding_eq_coordinateWinding, rawWinding_eq_coordinateWinding]
  cases segment <;> exact Dense.Rational.CauchyIndex.Basic.cauchyIndex2_reverse _ _ _ _

end ClearSegment

namespace ClearPath

open Purelib.Riemann.Paths.PreparedPathWinding.ClearPath (rawWinding)
open Purelib.Riemann.Paths.PreparedPathWinding.ClearSegment (rawWinding)
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.Paths.PreparedClearPathModels (GaussianPolynomial Box)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Paths in
/-- Appending original cleared paths adds their raw windings in order.

The original segment and tail order is unchanged. Direct integer associativity
combines their contributions across the retained common endpoint. -/
theorem rawWinding_append {polynomial : Basic.GaussianPolynomial} {ambient : Purelib.Geometry.Rational.Box} :
    ∀ {start middle finish : Basic.Canonical} (first : Polynomial.Geometry.ClearPath polynomial ambient start middle)
      (second : Polynomial.Geometry.ClearPath polynomial ambient middle finish),
      PreparedPathWinding.ClearPath.rawWinding (first.append second) =
        PreparedPathWinding.ClearPath.rawWinding first +
          PreparedPathWinding.ClearPath.rawWinding second
  | _, _, _, .nil _, _ => (Int.Arithmetic.zero_add _).symm
  | _, _, _, .cons head tail, second => by
      change PreparedPathWinding.ClearSegment.rawWinding head +
        PreparedPathWinding.ClearPath.rawWinding (tail.append second) = _
      rw [rawWinding_append tail second]
      exact (Int.Arithmetic.add_assoc _ _ _).symm

open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Paths in
/-- Reversing an original cleared path negates its total raw winding.

The reversed segment order and each original segment's negated winding combine through exact finite path concatenation.
-/
theorem rawWinding_reverse {polynomial : Basic.GaussianPolynomial} {ambient : Purelib.Geometry.Rational.Box} :
    ∀ {start finish : Basic.Canonical} (path : Polynomial.Geometry.ClearPath polynomial ambient start finish),
      PreparedPathWinding.ClearPath.rawWinding
        (BranchCutLifts.ClearPath.reverse path) =
          -PreparedPathWinding.ClearPath.rawWinding path
  | _, _, .nil _ => rfl
  | _, _, .cons head tail => by
      change PreparedPathWinding.ClearPath.rawWinding
        ((BranchCutLifts.ClearPath.reverse tail).append
        (.cons (BranchCutLifts.ClearSegment.reverse head) (.nil _))) = _
      rw [rawWinding_append, rawWinding_reverse tail]
      change -PreparedPathWinding.ClearPath.rawWinding tail +
        (PreparedPathWinding.ClearSegment.rawWinding
          (BranchCutLifts.ClearSegment.reverse head) + 0) =
        -(PreparedPathWinding.ClearSegment.rawWinding head +
          PreparedPathWinding.ClearPath.rawWinding tail)
      rw [PreparedPathClosure.ClearSegment.rawWinding_reverse head]
      omega

end ClearPath

namespace SquareRootTrace

open Purelib.Riemann.RootContinuation
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients renaming CoefficientPolynomial -> Dense
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner ownerName)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Geometry.Rational (Box)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

open Purelib.Approximation.Gaussian in
open Purelib.Data.Gaussian in
/-- Compare the original endpoint root names when their retained canonical assignments agree.

The exact reconditioning bridges identify both original names with the same canonical owner, yielding their retained
name equivalence. -/
@[expose] def rootEquivalent_of_assignment_eq {parameter : Basic.Canonical} (nonzero : parameter ≠ 0)
    (first last : Owner parameter)
    (equal : (SquareRootReconditioning.assignment nonzero last).owner.owner =
      (SquareRootReconditioning.assignment nonzero first).owner.owner) :
    Equivalence.NamedEquivalent (ownerName last) (ownerName first) := by
  have freshEqual : SquareRootReconditioning.freshOwner nonzero last =
      SquareRootReconditioning.freshOwner nonzero first := by
    rw [SquareRootReconditioning.freshOwner_eq_canonicalOwner,
      SquareRootReconditioning.freshOwner_eq_canonicalOwner]
    exact congrArg (SquareRootReconditioning.canonicalOwner nonzero) equal
  let firstEquivalent := SquareRootTrackEquivalence.rootEquivalent_of_bridge nonzero first
    (SquareRootReconditioning.bridge nonzero first)
  let lastEquivalent := SquareRootTrackEquivalence.rootEquivalent_of_bridge nonzero last
    (SquareRootReconditioning.bridge nonzero last)
  rw [freshEqual] at lastEquivalent
  exact Equivalence.NamedEquivalent.trans lastEquivalent firstEquivalent.symm

namespace OwnerPath

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
/-- Closing an original owner path at its exact base point adds zero to its raw chain winding.

The final stationary segment contributes zero because the retained base owner
certifies nonvanishing there; the original moving chain remains unchanged. -/
theorem closedRaw_eq_chainRaw {polynomial : Basic.GaussianPolynomial} {base : Basic.Canonical}
    {first last : Owner (polynomial.eval base)} (path : OwnerPath polynomial base first base last) :
    Winding.Polygon.Basic.closedRaw polynomial base path.vertices =
      Winding.Polygon.Basic.chainRaw polynomial base path.vertices := by
  rw [Winding.Polygon.Basic.closedRaw, Winding.Polygon.Basic.chainRaw_append,
    path.vertices_terminal, Winding.Polygon.Basic.chainRaw,
    Winding.Polygon.Stationary.segment_self_doubledWinding polynomial base first.parameterNonzero,
    Winding.Polygon.Basic.chainRaw, Int.Arithmetic.zero_add, Int.add_zero]

open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Paths in
open Purelib.RootIsolation in
/-- Even original owner-loop winding rules out distinct canonical endpoint assignments when a winding-one reference is
retained.

Appending the original reference boundary would otherwise give an odd loop returning to an equivalent root,
contradicting the finite root-trace winding certificate. -/
private theorem not_different_of_even {polynomial : Basic.GaussianPolynomial} {ambient : Purelib.Geometry.Rational.Box}
    (reference : State.WindingOne.Basic.WindingOneState polynomial ambient)
    {first last : Owner (polynomial.eval reference.box.anchor)}
    (path : OwnerPath polynomial reference.box.anchor first reference.box.anchor last)
    (turns : Int)
    (even : Winding.Polygon.Basic.chainRaw polynomial reference.box.anchor path.vertices = 8 * turns) :
    (SquareRootReconditioning.assignment first.parameterNonzero last).owner.owner ≠
      (SquareRootReconditioning.assignment first.parameterNonzero first).owner.owner → False := by
  intro different
  let boundary := PreparedPathWinding.TracedPath.ownerBoundary reference last
  let firstIndex : Fin 2 := (SquareRootReconditioning.assignment first.parameterNonzero first).owner.owner
  let lastIndex : Fin 2 := (SquareRootReconditioning.assignment first.parameterNonzero last).owner.owner
  have swapped : (SquareRootReconditioning.assignment first.parameterNonzero
      boundary.finishOwner).owner.owner = BranchCutLifts.otherSheet lastIndex :=
    PreparedPathWinding.TracedPath.ownerBoundary_assignment_swaps reference last
  have opposite : BranchCutLifts.otherSheet lastIndex = firstIndex := by
    have valueDifferent : lastIndex.val ≠ firstIndex.val := fun equal => different (Fin.ext equal)
    have firstBound : firstIndex.val < 2 := firstIndex.isLt
    have lastBound : lastIndex.val < 2 := lastIndex.isLt
    apply Fin.ext
    change 1 - lastIndex.val = firstIndex.val
    omega
  let returned := rootEquivalent_of_assignment_eq first.parameterNonzero first boundary.finishOwner
    (swapped.trans opposite)
  let joined := path.append boundary.trace.get
  have odd : Winding.Polygon.Basic.closedRaw polynomial reference.box.anchor joined.vertices =
      4 * (2 * turns + 1) := by
    rw [closedRaw_eq_chainRaw joined,
      OwnerTracePath.OwnerPath.append_vertices,
      Winding.Polygon.Basic.chainRaw_append,
      path.vertices_terminal, even, PreparedPathWinding.PreparedClearPathModels.TracedPath.winding_original boundary,
        PreparedPathWinding.BranchCutLifts.ownerBoundaryPath_rawWinding]
    omega
  exact joined.not_odd_of_return returned turns odd

open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.RootIsolation in
/-- An original owner loop of even winding has equal canonical endpoint assignments relative to the retained winding-one
reference. -/
theorem assignment_eq_of_even {polynomial : Basic.GaussianPolynomial} {ambient : Purelib.Geometry.Rational.Box}
    (reference : State.WindingOne.Basic.WindingOneState polynomial ambient)
    {first last : Owner (polynomial.eval reference.box.anchor)}
    (path : OwnerPath polynomial reference.box.anchor first reference.box.anchor last)
    (turns : Int)
    (even : Winding.Polygon.Basic.chainRaw polynomial reference.box.anchor path.vertices = 8 * turns) :
    (SquareRootReconditioning.assignment first.parameterNonzero last).owner.owner =
      (SquareRootReconditioning.assignment first.parameterNonzero first).owner.owner := by
  by_cases equal : (SquareRootReconditioning.assignment first.parameterNonzero last).owner.owner =
      (SquareRootReconditioning.assignment first.parameterNonzero first).owner.owner
  · exact equal
  · exact (not_different_of_even reference path turns even equal).elim

open Purelib.Approximation.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.RootIsolation in
/-- Construct equivalence of the original endpoint root names from even winding and a retained winding-one reference. -/
@[expose] def rootEquivalent_of_even {polynomial : Basic.GaussianPolynomial} {ambient : Purelib.Geometry.Rational.Box}
    (reference : State.WindingOne.Basic.WindingOneState polynomial ambient)
    {first last : Owner (polynomial.eval reference.box.anchor)}
    (path : OwnerPath polynomial reference.box.anchor first reference.box.anchor last)
    (turns : Int)
    (even : Winding.Polygon.Basic.chainRaw polynomial reference.box.anchor path.vertices = 8 * turns) :
    Equivalence.NamedEquivalent (ownerName last) (ownerName first) :=
  rootEquivalent_of_assignment_eq first.parameterNonzero first last
    (assignment_eq_of_even reference path turns even)

end OwnerPath

end SquareRootTrace

namespace TracedPath

open Purelib.Riemann.Paths.PreparedClearPathModels (GaussianPolynomial Box Owner)
open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)

open Purelib.Approximation.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Paths in
open Purelib.RootIsolation in
/-- An original traced cleared loop of even winding returns an equivalent root name relative to the retained winding-one
reference.

The exact traced-path winding equation transfers the original path's winding to its retained owner trace before forming
the endpoint comparison. -/
@[expose] def rootEquivalent_of_original_even {polynomial : Basic.GaussianPolynomial} {ambient referenceAmbient :
  Purelib.Geometry.Rational.Box}
    (reference : State.WindingOne.Basic.WindingOneState polynomial referenceAmbient)
    {path : Polynomial.Geometry.ClearPath polynomial ambient reference.box.anchor reference.box.anchor}
    {owner : Owner (polynomial.eval reference.box.anchor)} (traced : TracedPath path owner)
    (turns : Int) (even : PreparedPathWinding.ClearPath.rawWinding path = 8 * turns) :
    Equivalence.NamedEquivalent
      (OwnerTraceReadings.ownerName traced.finishOwner)
      (OwnerTraceReadings.ownerName owner) :=
  PreparedPathClosure.SquareRootTrace.OwnerPath.rootEquivalent_of_even
    reference traced.trace.get turns ((PreparedPathWinding.PreparedClearPathModels.TracedPath.winding_original
      traced).trans even)

end TracedPath

end

end Purelib.Riemann.Paths.PreparedPathClosure
