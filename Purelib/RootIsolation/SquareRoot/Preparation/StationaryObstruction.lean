module
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Winding.Polygon.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Polynomial.Winding.Polygon.Stationary

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.RootContinuation.SquareRootReconditioning
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Riemann.Paths.PreparedPathClosure
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Approximation.Gaussian

open Purelib

open Purelib.Data

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

@[expose] public section

/-!
# A stationary base path cannot switch an actual square-root sheet

The zero-displacement integral certificate of a labelled switch does not
provide a root-continuation certificate.  At the anchor of any winding-one
branch box, every stationary owner trace has winding zero and returns to its
initial operational root.  Consequently no such trace can connect the two
different canonical square-root owners.
-/

namespace Purelib.RootIsolation.SquareRoot.Preparation.StationaryObstruction

open Purelib.Riemann.RootContinuation

/-- A finite polygonal chain whose vertices all equal a nonzero base point has raw winding zero. -/
private theorem stationary_chainRaw (polynomial :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (base : Gaussian.Basic.Canonical)
    (nonzero : polynomial.eval base ≠ 0) : ∀ (vertices : List Gaussian.Basic.Canonical),
    (∀ point ∈ vertices, point = base) → Winding.Polygon.Basic.chainRaw polynomial base vertices = 0
  | [], _ => rfl
  | point :: remaining, same => by
      have equal := same point (List.mem_cons_self)
      subst point
      rw [Winding.Polygon.Stationary.chainRaw_cons_self polynomial base nonzero]
      exact Purelib.RootIsolation.SquareRoot.Preparation.StationaryObstruction.stationary_chainRaw polynomial base
        nonzero remaining
        (fun point member => same point (List.mem_cons_of_mem _ member))

namespace OwnerPath

/-- Stationarity is checked on the actual stored base vertices, not on an
independent labelled path. -/
theorem winding_zero_of_stationary {polynomial :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {base : Gaussian.Basic.Canonical}
    {first last : Riemann.Topology.SquareRootContinuationChain.Owner (polynomial.eval base)} (path :
      Riemann.Paths.OwnerTracePath.OwnerPath polynomial base first base last)
    (stationary : ∀ point ∈ path.vertices, point = base) :
    Winding.Polygon.Basic.chainRaw polynomial base path.vertices = 0 :=
  SquareRoot.Preparation.StationaryObstruction.stationary_chainRaw polynomial base first.parameterNonzero path.vertices
    stationary

/-- A stationary owner trace has an executable operational return. -/
def rootEquivalent_of_stationary {polynomial :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (reference : State.WindingOne.Basic.WindingOneState polynomial ambient)
    {first last : Riemann.Topology.SquareRootContinuationChain.Owner (polynomial.eval reference.box.anchor)}
    (path : Riemann.Paths.OwnerTracePath.OwnerPath polynomial reference.box.anchor first reference.box.anchor last)
    (stationary : ∀ point ∈ path.vertices, point = reference.box.anchor) :
    Equivalence.NamedEquivalent (Riemann.Paths.OwnerTraceReadings.ownerName last)
      (Riemann.Paths.OwnerTraceReadings.ownerName first) :=
  Riemann.Paths.PreparedPathClosure.SquareRootTrace.OwnerPath.rootEquivalent_of_even reference path 0
    (SquareRoot.Preparation.StationaryObstruction.OwnerPath.winding_zero_of_stationary path stationary)

end OwnerPath

/-- The opposite sheet of a two-sheet index is distinct from the original sheet. -/
private theorem otherSheet_ne_self (sheet : Fin 2) : Curves.Hyperelliptic.Branches.BranchCutLifts.otherSheet sheet ≠
  sheet := by
  intro equal
  have values := congrArg Fin.val equal
  have bound : sheet.val < 2 := sheet.isLt
  change 1 - sheet.val = sheet.val at values
  omega

/-- The boundary anchor is a regular point of the curve, not its enclosed
ramification point. -/
theorem branchAnchor_nonzero {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {ambient : Box}
    (reference : State.WindingOne.Basic.WindingOneState polynomial ambient) :
    polynomial.eval reference.box.anchor ≠ 0 :=
  reference.clearance.eval_ne_zero ⟨reference.box.contains_anchor, Or.inl rfl⟩

/-- Formal obstruction to interpreting a labelled stationary sheet swap as
actual root continuation at a branch-box anchor.  This excludes a trace of
any finite length, not only one stationary chord. -/
theorem no_stationary_canonical_swap {polynomial :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (reference : State.WindingOne.Basic.WindingOneState polynomial ambient) (sheet : Fin 2)
    (path : Riemann.Paths.OwnerTracePath.OwnerPath polynomial reference.box.anchor
      (Riemann.RootContinuation.SquareRootReconditioning.canonicalOwner
        (SquareRoot.Preparation.StationaryObstruction.branchAnchor_nonzero reference) sheet)
      reference.box.anchor
      (Riemann.RootContinuation.SquareRootReconditioning.canonicalOwner
        (SquareRoot.Preparation.StationaryObstruction.branchAnchor_nonzero reference)
        (Curves.Hyperelliptic.Branches.BranchCutLifts.otherSheet sheet)))
    (stationary : ∀ point ∈ path.vertices, point = reference.box.anchor) : False := by
  let returned := SquareRoot.Preparation.StationaryObstruction.OwnerPath.rootEquivalent_of_stationary reference path
    stationary
  have same := Riemann.RootContinuation.SquareRootTrackEquivalence.canonicalOwner_index_eq_of_rootEquivalent
    (SquareRoot.Preparation.StationaryObstruction.branchAnchor_nonzero reference)
      (Curves.Hyperelliptic.Branches.BranchCutLifts.otherSheet sheet) sheet returned
  exact SquareRoot.Preparation.StationaryObstruction.otherSheet_ne_self sheet same

end Purelib.RootIsolation.SquareRoot.Preparation.StationaryObstruction
