module
import Purelib.RootIsolation.FTA.Squarefree.Build
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.RootIsolation.Exact.Basic
import Purelib.RootIsolation.Exact.Ownership.Prepare
import Purelib.RootIsolation.FTA.Positive.Build
import Purelib.RootIsolation.FTA.Positive.CCL.Basic
import Purelib.RootIsolation.FTA.Positive.CCL.Build
import Purelib.RootIsolation.FTA.Squarefree.Basic
import Purelib.RootIsolation.FTA.Squarefree.Input
import Purelib.RootIsolation.Roots.CCL.Terminal.Basic

import Purelib.Riemann.RootContinuation.CoherentRoot
public import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Init.Prelude
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.RootIsolation.FTA.Positive.Basic
import Purelib.RootIsolation.FTA.Squarefree.Approximation
import Purelib.RootIsolation.FTA.Squarefree.Prepare
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Polynomial

open Purelib.Polynomial.Dense.Gaussian.Bounds

open Purelib.Riemann.RootContinuation

open Purelib.RootIsolation

open Purelib.RootIsolation.Exact.Ownership

open Purelib.RootIsolation.FTA

open Purelib.RootIsolation.FTA.Positive

open Purelib.RootIsolation.FTA.Positive.CCL.Basic

open Purelib.RootIsolation.FTA.Squarefree

open Purelib.RootIsolation.Roots.CCL

public section

/-!
# Canonical branch data from a restored exact isolation

The restored ordered isolation retains the original track constructors and
remainder partition.  Rebuild the same ownership/name interfaces around it;
valid boxes alone are not a replacement for the exact-isolation equation.
The Paper-I isolation modules remain independent of this CCL bridge.
-/

namespace Purelib.Curves.Hyperelliptic.Branches.BranchIsolationReplay

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)

/-- A retained successor equality reduces the natural-number case eliminator to its successor branch. -/
private theorem cases_succ {α : Sort u} (n k : Nat) (same : n = k + 1)
    (zero : n = 0 → α) (succ : (k : Nat) → n = k + 1 → α) :
    Nat.casesAuxOn (motive := fun value => n = value → α) n zero succ rfl = succ k same := by
  cases same
  rfl

/-- Transporting the equality-indexed function and applying reflexivity is evaluation at the reversed retained equality.
-/
private theorem transport_apply {α : Sort u} {β : Sort v} {a b : α}
    (back : b = a) (value : a = b → β) :
    Eq.rec (motive := fun target (_ : b = target) => a = target → β) value back rfl = value back.symm := by
  cases back
  rfl

open Purelib.Curves.Hyperelliptic.Branches.BranchIsolationReplay in
/-- A retained higher-degree result equality reduces the positive-result eliminator to its higher-degree branch. -/
private theorem cases_higher {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {α :
  Sort u}
    (value : CCL.Basic.PositiveResult p) (boxes : Squarefree.AdapterResult p)
    (higher : 2 ≤ p.natDegree) (same : value = .higher boxes higher)
    (terminalCase : (terminal : RootIsolation.Roots.CCL.Terminal p) → (degree : p.natDegree = 1) →
      value = .terminal terminal degree → α)
    (higherCase : (boxes : Squarefree.AdapterResult p) → (degree : 2 ≤ p.natDegree) →
      value = .higher boxes degree → α) :
    PositiveResult.casesOn (motive := fun result => value = result → α)
      value terminalCase higherCase rfl = higherCase boxes higher same := by
  cases same
  rfl

variable {genus : Nat} (curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
  (higher : 1 < curve.polynomial.natDegree)

/-- Package the original curve squarefree certificate and higher-degree witness as an isolation input. -/
@[expose] def input : RootIsolation.FTA.Squarefree.Input curve.polynomial := ⟨curve.squarefree, higher⟩

/-- Reconstruct ownership interfaces around the supplied exact isolation output.

The original squarefree elimination and finite maximality bound certify the same retained tracks without replacing the
supplied isolation. -/
@[expose] def boxes (isolation : Exact.Basic.Output curve.polynomial
    (RootRadius.Box.largeSquareBox curve.polynomial) curve.polynomial.natDegree) :
    Squarefree.AdapterResult curve.polynomial :=
  ⟨{ isolation := isolation
     ownership := fun track supported => Prepare.selectOutputOwner higher curve.squarefree
       (Curves.Hyperelliptic.Branches.BranchIsolationReplay.input curve higher).elimination isolation track supported
     maximality := (Curves.Hyperelliptic.Branches.BranchIsolationReplay.input curve higher).familyCardLe }⟩

open Purelib.Curves.Hyperelliptic.Branches.BranchIsolationReplay in
/-- An isolation equal to the canonical one yields exactly the canonical retained box result. -/
theorem boxes_eq (isolation : Exact.Basic.Output curve.polynomial
    (RootRadius.Box.largeSquareBox curve.polynomial) curve.polynomial.natDegree)
    (same : isolation = (Curves.Hyperelliptic.Branches.BranchIsolationReplay.input curve higher).isolation) :
    boxes curve higher isolation = Build.Box.prove (Curves.Hyperelliptic.Branches.BranchIsolationReplay.input curve
      higher) := by
  cases same
  rfl

/-- A higher-degree curve selects the canonical higher branch of positive root isolation. -/
theorem canonical_higher : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.branchIsolation curve =
    .higher (Build.Box.prove (Curves.Hyperelliptic.Branches.BranchIsolationReplay.input curve higher)) higher := by
  let degree := curve.polynomial.natDegree - 2
  have degreeEq' : curve.polynomial.natDegree = degree + 1 + 1 := by omega0
  unfold BranchIsolation.branchIsolation CCL.Build.provePositive Build.provePositive
  rw [Curves.Hyperelliptic.Branches.BranchIsolationReplay.cases_succ _ _ degreeEq']
  simp only [Curves.Hyperelliptic.Branches.BranchIsolationReplay.transport_apply, Nat.casesAuxOn]
  rfl

open Purelib.Curves.Hyperelliptic.Branches.BranchIsolationReplay in
/-- Build the complete retained branch-name interface around the supplied exact isolation.

Names, coherent tracks, anchors and pairwise separation all come from the same restored ownership result. -/
@[expose] def data (isolation : Exact.Basic.Output curve.polynomial
    (RootRadius.Box.largeSquareBox curve.polynomial) curve.polynomial.natDegree) :
    BranchIsolation.Data curve :=
  let restored := boxes curve higher isolation
  { siteCount := curve.polynomial.natDegree
    count_eq := rfl
    nameAt := restored.arithmeticNameAt
    coherentNameAt := fun index => CoherentRoot.named (restored.trackAt index)
    anchorAt := fun index => (restored.trackAt index).initial.box.anchor
    trackAt := fun _ index => restored.trackAt index
    track_anchor_eq := fun _ _ => rfl
    trackAt_pairwiseSeparated := fun _ left right different =>
      restored.trackAt_pairwiseSeparated left right different }

/-- Equality of the complete branch interface, not only the anchors. The original isolation need not be evaluated to
construct this interface. -/
theorem data_eq (isolation : Exact.Basic.Output curve.polynomial
    (RootRadius.Box.largeSquareBox curve.polynomial) curve.polynomial.natDegree)
    (same : isolation = (Curves.Hyperelliptic.Branches.BranchIsolationReplay.input curve higher).isolation) :
    Purelib.Curves.Hyperelliptic.Branches.BranchIsolationReplay.data curve higher isolation =
      Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.data curve := by
  cases same
  unfold BranchIsolationReplay.data BranchIsolation.data
  rw [Curves.Hyperelliptic.Branches.BranchIsolationReplay.cases_higher _ _ _
    (Curves.Hyperelliptic.Branches.BranchIsolationReplay.canonical_higher curve higher)]
  simp only [Curves.Hyperelliptic.Branches.BranchIsolationReplay.transport_apply]
  rfl

end Purelib.Curves.Hyperelliptic.Branches.BranchIsolationReplay

end
