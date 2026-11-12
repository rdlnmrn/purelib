module

public import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance

/-! # One retained direct query Owner of the original prepared edge

The complete original direct-query factory is executed once and retained.
Exact physical-point transports preserve that same Owner and its original
name. This independent cache does not replace any old source query, sample
or arithmetic observation at the same physical point.
-/

public section

namespace Purelib.Riemann.Integration.PreparedConstantModels.PreparedEdge

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Branches
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.RootIsolation.SquareRoot.Owner.Transport (castOwnerParameter castOwnerParameter_initial_box)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
    (edge : PreparedEdge curve differential) (time : Rational) (inside : 0 ≤ time ∧ time ≤ 1)

/-- Exact rational fraction equality preserves the original prepared-edge root generator and its admitted bounds. -/
theorem rootName_eq {first last : Rational}
    {firstInside : 0 ≤ first ∧ first ≤ 1} {lastInside : 0 ≤ last ∧ last ≤ 1} (equal : first = last) :
    edge.rootName first firstInside = edge.rootName last lastInside := by
  cases equal
  rfl

/-- The original affine edge point is exactly its original segment's interpolated accepted-request point. -/
theorem directQueryParameter_eq :
    curve.polynomial.eval (edge.segment.pointAt (PreparedSheetContinuation.parameterAt edge.left edge.request time)) =
      curve.polynomial.eval (edge.point time) := by
  have same := PreparedSheetContinuation.pointAt_parameterAt edge.segment edge.within edge.left edge.request time
  change edge.segment.pointAt (PreparedSheetContinuation.parameterAt edge.left edge.request time) =
    edge.point time at same
  exact congrArg curve.polynomial.eval same

/-- One complete actual original direct-query Owner, retained with its whole original factory equation. -/
@[expose] def Query :=
  { actual : Owner (curve.polynomial.eval
      (edge.segment.pointAt (PreparedSheetContinuation.parameterAt edge.left edge.request time))) //
    actual = edge.directQueryOwner time inside }

namespace Query

variable {edge time inside}

/-- Construct and retain the original direct-query Owner once, without another source preparation or advancement. -/
def build (edge : PreparedEdge curve differential) (time : Rational) (inside : 0 ≤ time ∧ time ≤ 1) :
    Query edge time inside :=
  let actual := edge.directQueryOwner time inside
  ⟨actual, rfl⟩

variable (query : Query edge time inside)

/-- Read the complete actual original Owner at its literal direct-query parameter. -/
@[expose] def direct := query.val

/-- The whole retained Owner is the original direct-query factory on the same cached prepared source. -/
theorem direct_eq : query.direct = edge.directQueryOwner time inside := query.property

/-- Reindex that same retained Owner to the identical original physical edge point. -/
@[expose] def owner : Owner (curve.polynomial.eval (edge.point time)) :=
  castOwnerParameter (edge.directQueryParameter_eq time) query.direct

/-- The original evaluator name is exactly the retained same-query Owner name after physical-index transport. -/
theorem name_eq : edge.rootName time inside = ownerRootName query.owner.parameterNonzero query.owner := by
  have original := edge.rootName_eq_directQueryOwnerRootName time inside
  have cached := congrArg (fun owner => ownerRootName owner.parameterNonzero owner) query.direct_eq
  have reindexed := Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName_castOwnerParameter
    (edge.directQueryParameter_eq time) query.direct
  exact original.trans (cached.symm.trans reindexed.symm)

/-- The actual original query Owner refines the SAME cached prepared-source box, including every reserved branch. -/
theorem refines : query.owner.track.initial.box.Refines edge.cached.preparedOwner.track.initial.box := by
  unfold owner
  rewrite [castOwnerParameter_initial_box, query.direct_eq]
  unfold directQueryOwner
  exact RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance.reservedTransport_initial_box_refines
    edge.cached.preparedOwner _ _ _

/-- The same whole direct query Owner refines the original cached prepared-source box before physical-index transport.

The existing physical query refinement and original cast-box readback
remove only the parameter reindexing. The direct Owner, source cache and
reserved transport outcome are unchanged; no query is executed again.
-/
theorem direct_refines : query.direct.track.initial.box.Refines edge.cached.preparedOwner.track.initial.box := by
  have retained := query.refines
  unfold owner at retained
  rewrite [castOwnerParameter_initial_box] at retained
  exact retained

end Query

end Purelib.Riemann.Integration.PreparedConstantModels.PreparedEdge

end
