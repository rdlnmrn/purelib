module

public import Purelib.Curves.Legendre.Degeneration.UnitRoot
public import Purelib.Riemann.RootContinuation.FixedRootBoxBudget
import Purelib.Riemann.Branches.PreparedPrimitiveSheets
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.RootIsolation.Owner.Local.Track
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Data.Fin.Two
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Segment
import Purelib.Geometry.Rational.Affine
import Purelib.Polynomial.Dense.Gaussian.Linear.Translated
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

/-!
# Uniform cofactor-root budgets and retained continuation agreement

The original critical cofactor value supplies one signed source owner with
clearance 9/16. A cached movement allowance 1/2 covers the whole spatial patch.
Actual accepted continuation moves and chains retain a root box refining that
same signed square, and their endpoint readings agree operationally with the
independently constructed original cofactor owner.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.UnitRoot.Transport

open Purelib.Approximation.Gaussian

open Purelib
open Purelib.Data
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Geometry.Rational
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Topology
open Purelib.RootIsolation
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)

/-- The original reference cofactor value has a nonzero retained square. -/
private theorem source_nonzero (site : Fin 2) : seed site ^ 2 ≠ 0 := by
  rcases Fin.Two.finTwo_cases site with zero | one
  · subst site
    decide +kernel
  · subst site
    decide +kernel

/-- Construct the signed reference owner directly from the original split-pair state.

This retains the reference state's original clearance and all four ambient
line certificates. It performs no zero-length perturbation that would replace
the reference clearance by a smaller derived bound.
-/
def source (site : Fin 2) : SquareRootContinuationChain.Owner (seed site ^ 2) :=
  SquareRootContinuationChain.Owner.ofState (source_nonzero site) (sourceOwner site).initialState

/-- The reference owner retains the original signed reference-root square. -/
theorem source_box (site : Fin 2) : (source site).track.initial.box = box site := by
  unfold source
  rewrite [SquareRootContinuationChain.Owner.ofState_initial]
  exact sourceOwner_box site

/-- The reference owner retains the original split-pair clearance nine sixteenths. -/
theorem source_bound (site : Fin 2) : (source site).track.initial.clearance.bound = 9 / 16 := by
  unfold source
  rewrite [SquareRootContinuationChain.Owner.ofState_initial]
  exact sourceOwner_bound site

attribute [local irreducible] source

/-- Cache a uniform whole-patch parameter budget on the original signed reference owner.

The half-quadrance movement is strictly below the retained reference
clearance. The existing finite Horner-majorant constructor computes a single
positive target clearance on that original box for every admitted cofactor.
-/
def budget (site : Fin 2) : FixedRootBoxBudget.Budget (source site) :=
  FixedRootBoxBudget.Budget.acquire (source site) (1 / 2) (by decide +kernel) (by
    rewrite [source_bound]
    decide +kernel)

/-- The cached uniform movement allowance is exactly one half. -/
theorem budget_movement (site : Fin 2) : (budget site).movement = 1 / 2 := by
  unfold budget
  rfl

/-- Original spatial-patch admission pays the same cached reference-owner movement budget. -/
theorem movement (site : Fin 2) {point : Canonical} (inside : (spatialBox site).Contains point) :
    (seed site ^ 2 - (unitPolynomial site).eval point).normSq ≤ (budget site).movement := by
  rewrite [budget_movement]
  have bound := variation_bound site inside
  rewrite [Norm.Basic.normSq_eq_canonical] at bound
  exact bound

/-- Construct the cofactor root on the original reference box with the cached uniform clearance.

The original cofactor parameter, nonvanishing and paid movement determine
this budget reading. Its comparison with the independent patch owner keeps
both actual tracks rather than identifying their records.
-/
def reading (site : Fin 2) (point : Canonical) (inside : (spatialBox site).Contains point) :
    SquareRootContinuationChain.Owner ((unitPolynomial site).eval point) :=
  (budget site).ownerAt (unit_ne_zero site inside) (movement site inside)

/-- Every uniform-budget reading retains the original signed root square. -/
theorem reading_box (site : Fin 2) (point : Canonical) (inside : (spatialBox site).Contains point) :
    (reading site point inside).track.initial.box = box site := by
  unfold reading
  rewrite [FixedRootBoxBudget.Budget.ownerAt_box]
  exact source_box site

/-- Every budget reading uses the same cached positive target clearance. -/
theorem reading_clearance (site : Fin 2) (point : Canonical) (inside : (spatialBox site).Contains point) :
    (reading site point inside).track.initial.clearance.bound = (budget site).clearance := by
  unfold reading
  exact FixedRootBoxBudget.Budget.ownerAt_clearance _ _ _

/-- Compare the actual uniform-budget cofactor reading with the independently constructed original patch owner. -/
def reading_agrees (site : Fin 2) (point : Canonical) (inside : (spatialBox site).Contains point) :
    Equivalence.NamedEquivalent
      (ownerRootName (reading site point inside).parameterNonzero (reading site point inside))
      (ownerRootName (owner site point inside).parameterNonzero (owner site point inside)) := by
  unfold reading
  apply (budget site).retainedEquivalent _ _ (owner site point inside)
  rewrite [owner_initial_box, source_box]
  exact Box.refines_refl _

/-- An actual accepted move from the original signed patch owner agrees with the independent target reading.

The original source-to-target clearance payment permits genuine owner
advancement. Its retained target box refines the same original signed square;
the existing initial-box comparison proves agreement with the target owner.
-/
def advance_agrees (site : Fin 2) (first last : Canonical)
    (firstInside : (spatialBox site).Contains first) (lastInside : (spatialBox site).Contains last)
    (small : Norm.Basic.normSq ((unitPolynomial site).eval first - (unitPolynomial site).eval last) <
      (owner site first firstInside).track.initial.clearance.bound) :
    Equivalence.NamedEquivalent
      (ownerRootName (unit_ne_zero site lastInside)
        ((owner site first firstInside).advance (unit_ne_zero site lastInside) small))
      (ownerRootName (owner site last lastInside).parameterNonzero (owner site last lastInside)) := by
  apply Equivalence.NamedEquivalent.symm
  apply Riemann.Branches.PreparedPrimitiveSheets.rootEquivalent_of_initial_refines (unit_ne_zero site lastInside)
  have nested := (owner site first firstInside).advance_initial_box_refines (unit_ne_zero site lastInside) small
  rewrite [owner_initial_box site first firstInside, ← owner_initial_box site last lastInside] at nested
  exact nested

/-- Compare any original cofactor owner refining the signed patch square with the independent patch reading. -/
def retained_agrees (site : Fin 2) (point : Canonical) (inside : (spatialBox site).Contains point)
    (retained : SquareRootContinuationChain.Owner ((unitPolynomial site).eval point))
    (within : retained.track.initial.box.Refines (box site)) :
    Equivalence.NamedEquivalent
      (ownerRootName retained.parameterNonzero retained)
      (ownerRootName (owner site point inside).parameterNonzero (owner site point inside)) := by
  apply Equivalence.NamedEquivalent.symm
  apply Riemann.Branches.PreparedPrimitiveSheets.rootEquivalent_of_initial_refines retained.parameterNonzero
  rewrite [owner_initial_box]
  exact within

/-- Continue the original critical cofactor root to any admitted spatial-patch point.

The internally computed half-quadrance variation is strictly below the
original reference clearance. This invokes actual owner advancement from
that retained reference occurrence, without a supplied successful search,
movement inequality or target root.
-/
def fromSource (site : Fin 2) (point : Canonical) (inside : (spatialBox site).Contains point) :
    SquareRootContinuationChain.Owner ((unitPolynomial site).eval point) :=
  (source site).advance (unit_ne_zero site inside) (by
    rewrite [source_bound]
    exact (variation_bound site inside).trans_lt (by decide +kernel))

/-- Actual reference-to-patch advancement retains a box refining the same original signed root square. -/
theorem fromSource_box (site : Fin 2) (point : Canonical) (inside : (spatialBox site).Contains point) :
    (fromSource site point inside).track.initial.box.Refines (box site) := by
  unfold fromSource
  have nested := (source site).advance_initial_box_refines (unit_ne_zero site inside) (by
    rewrite [source_bound]
    exact (variation_bound site inside).trans_lt (by decide +kernel))
  exact Eq.mp (congrArg (fun targetBox =>
    (fromSource site point inside).track.initial.box.Refines targetBox) (source_box site)) nested

/-- The original spatial radial segment from the critical coordinate to the admitted point. -/
@[expose] def radialPoint (site : Fin 2) (point : Canonical) (time : Rat.Fraction.Rational) : Canonical :=
  Affine.line (criticalValue site) (point - criticalValue site) time

/-- Every unit-interval radial point remains inside the original spatial collision patch. -/
theorem radial_inside (site : Fin 2) (point : Canonical) (inside : (spatialBox site).Contains point)
    {time : Rat.Fraction.Rational} (timeInside : 0 ≤ time ∧ time ≤ 1) :
    (spatialBox site).Contains (radialPoint site point time) :=
  Box.contains_line (Box.Square.Centered.centeredSquare_contains_center (criticalValue site) (1 / 2)
    (by decide +kernel : (0 : Rat.Fraction.Rational) ≤ 1 / 2)) inside timeInside

/-- The entire radial segment has nonzero original cofactor value, including between its endpoints. -/
theorem radial_nonzero (site : Fin 2) (point : Canonical) (inside : (spatialBox site).Contains point)
    {time : Rat.Fraction.Rational} (timeInside : 0 ≤ time ∧ time ≤ 1) :
    (unitPolynomial site).eval (radialPoint site point time) ≠ 0 :=
  unit_ne_zero site (radial_inside site point inside timeInside)

/-- Original cofactor evaluation carries the spatial radial segment to the actual reference-to-target parameter line. -/
theorem radial_value (site : Fin 2) (point : Canonical) (time : Rat.Fraction.Rational) :
    (unitPolynomial site).eval (radialPoint site point time) =
      Affine.line (seed site ^ 2) ((unitPolynomial site).eval point - seed site ^ 2) time := by
  rewrite [seed_square]
  simp only [unitPolynomial, radialPoint, Polynomial.Dense.Gaussian.Linear.Translated.translatedCoordinate_eval,
    Affine.line, -eq_self, -iff_self]
  ring1

/-- Actual reference-to-patch continuation agrees with the independently constructed original cofactor reading. -/
def fromSource_agrees (site : Fin 2) (point : Canonical) (inside : (spatialBox site).Contains point) :
    Equivalence.NamedEquivalent
      (ownerRootName (fromSource site point inside).parameterNonzero (fromSource site point inside))
      (ownerRootName (owner site point inside).parameterNonzero (owner site point inside)) :=
  retained_agrees site point inside (fromSource site point inside) (fromSource_box site point inside)

/-- Compare an actual accepted continuation chain's retained endpoint with the independent cofactor reading.

The source is the original signed patch owner, and the displayed endpoint
equation identifies the actual terminal radicand. Parameter reindexing
retains that complete terminal owner; the chain's computed box refinement
supplies the operational endpoint comparison without another isolation.
-/
def chain_agrees (site : Fin 2) (first last : Canonical)
    (firstInside : (spatialBox site).Contains first) (lastInside : (spatialBox site).Contains last)
    (chain : SquareRootContinuationChain.Chain
      ⟨(unitPolynomial site).eval first, owner site first firstInside⟩)
    (endpoint : chain.endpoint.parameter = (unitPolynomial site).eval last) :
    Equivalence.NamedEquivalent
      (ownerRootName
        (SquareRoot.Owner.Transport.castOwnerParameter endpoint chain.endpoint.owner).parameterNonzero
        (SquareRoot.Owner.Transport.castOwnerParameter endpoint chain.endpoint.owner))
      (ownerRootName (owner site last lastInside).parameterNonzero (owner site last lastInside)) := by
  apply retained_agrees site last lastInside
  rewrite [SquareRoot.Owner.Transport.castOwnerParameter_initial_box]
  have nested := chain.endpoint_initial_box_refines
  change chain.endpoint.owner.track.initial.box.Refines (owner site first firstInside).track.initial.box at nested
  rewrite [owner_initial_box] at nested
  exact nested

end Purelib.Curves.Legendre.Degeneration.UnitRoot.Transport
