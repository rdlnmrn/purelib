module

public import Purelib.Riemann.RootContinuation.FixedRootBoxBudget
public import Purelib.Riemann.RootContinuation.CoherentRoot
import Purelib.Polynomial.Power.Gaussian
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring

/-! # Paid root queries in an original fixed-box budget

One query retains its exact target owner, the certified root's original
64-entry state-thunk prefix, a finite residual selection and the actual cached
state and anchor. Containment and residual laws read those same caches.
-/

public section

namespace Purelib.Riemann.RootContinuation.FixedRootBoxBudget.Budget

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Approximation.Rational.Geometric
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)
open Purelib.Approximation.Rational.Geometric.Search (Selection)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Polynomial

variable {source : Canonical} {original : Owner source} (budget : Budget original)

/-- The original square-root polynomial has strictly positive degree at every retained parameter. -/
theorem degree_positive (parameter : Canonical) :
    0 < (Power.Gaussian.rootPolynomial parameter SquareRootDegree.degreeTwo).natDegree := by
  rewrite [Power.Gaussian.rootPolynomial_degree]
  exact SquareRootDegree.degreeTwo.positive

/-- One paid query retains the original target owner, certified name, scale, selection, state and anchor. -/
@[expose] def Query (parameter : Canonical) (nonzero : parameter ≠ 0)
    (movement : Canonical.normSq (source - parameter) ≤ budget.movement)
    (floor : Nat) (target : Rational) (positive : 0 < target) : Type _ :=
  (owner : { value : Owner parameter // value = budget.ownerAt nonzero movement }) ×
  (root : { value : CoherentRoot.CertifiedName owner.val.track //
    value = CoherentRoot.certifiedName owner.val.track (degree_positive parameter) }) ×
  (scale : { value : Rational // value = CoherentRoot.residualScale
    (Power.Gaussian.rootPolynomial parameter SquareRootDegree.degreeTwo) owner.val.ambient owner.val.track }) ×
  (selected : { value : Selection scale.val floor target // value = Selection.build scale.val
    (scale.property.symm ▸ CoherentRoot.residualScale_nonneg _ _ owner.val.track) floor target positive }) ×
  (state : { value : CoherentRoot.WindingOneState
      (Power.Gaussian.rootPolynomial parameter SquareRootDegree.degreeTwo) owner.val.ambient //
    value = root.val.stateAt selected.val.stage }) ×
  { value : Canonical // value = state.val.box.anchor }

namespace Query

variable {budget} {parameter : Canonical} {nonzero : parameter ≠ 0}
    {movement : Canonical.normSq (source - parameter) ≤ budget.movement}
    {floor : Nat} {target : Rational} {positive : 0 < target}
    (query : Query budget parameter nonzero movement floor target positive)

/-- Read the same cached target owner. -/
@[expose] def owner : Owner parameter := query.1.val

/-- Read the same certified name and its retained original state-thunk prefix. -/
@[expose] def root : CoherentRoot.CertifiedName query.owner.track := query.2.1.val

/-- Read the same cached residual scale. -/
@[expose] def scale : Rational := query.2.2.1.val

/-- Read the same paid residual selection. -/
@[expose] def selected : Selection query.scale floor target := query.2.2.2.1.val

/-- Read the same queried original root state. -/
@[expose] def state : CoherentRoot.WindingOneState
    (Power.Gaussian.rootPolynomial parameter SquareRootDegree.degreeTwo) query.owner.ambient := query.2.2.2.2.1.val

/-- Read the same cached anchor. -/
@[expose] def value : Canonical := query.2.2.2.2.2.val

/-- The cached owner keeps the exact initial source box. -/
theorem owner_box : query.owner.track.initial.box = original.track.initial.box :=
  (congrArg (fun value : Owner parameter => value.track.initial.box) query.1.property).trans
    (budget.ownerAt_box nonzero movement)

/-- The cached anchor is the sample of the SAME retained root approximation at its actual paid stage. -/
theorem value_sample : query.value = query.root.approximation.sample query.selected.stage :=
  query.2.2.2.2.2.property.trans
    ((congrArg (fun value : CoherentRoot.WindingOneState
      (Power.Gaussian.rootPolynomial parameter SquareRootDegree.degreeTwo) query.owner.ambient => value.box.anchor)
      query.2.2.2.2.1.property).trans (query.root.sample_stateAt query.selected.stage).symm)

/-- The actual queried anchor remains in the original source owner's initial box. -/
theorem inside : original.track.initial.box.Contains query.value := by
  have retained := query.root.sample_initial_inside query.selected.stage
  rewrite [← query.value_sample, query.owner_box] at retained
  exact retained

/-- The same original queried anchor has square residual strictly below the retained positive request. -/
theorem residual : Norm.Basic.normSq (query.value * query.value - parameter) < target := by
  have retained := query.root.residual query.selected.stage
  rewrite [← query.root.approximation_eq, ← query.value_sample] at retained
  rewrite [Power.Gaussian.rootPolynomial_eval, SquareRootDegree.degreeTwo_value, pow_two] at retained
  have scaleEq : query.scale = CoherentRoot.residualScale
      (Power.Gaussian.rootPolynomial parameter SquareRootDegree.degreeTwo) query.owner.ambient query.owner.track :=
    query.2.2.1.property
  rewrite [← scaleEq] at retained
  exact retained.trans_lt (query.selected.later_accurate (Nat.le_refl _))

/-- The queried root stage does not precede the requested original floor. -/
theorem floor_le : floor ≤ query.selected.stage := query.selected.lower

end Query

/-- Execute one original target-owner construction, one certified cache, one finite selection and one state query. -/
def query (parameter : Canonical) (nonzero : parameter ≠ 0)
    (movement : Canonical.normSq (source - parameter) ≤ budget.movement)
    (floor : Nat) (target : Rational) (positive : 0 < target) :
    Query budget parameter nonzero movement floor target positive := by
  let owner := budget.ownerAt nonzero movement
  let root := CoherentRoot.certifiedName owner.track (degree_positive parameter)
  let scale := CoherentRoot.residualScale
    (Power.Gaussian.rootPolynomial parameter SquareRootDegree.degreeTwo) owner.ambient owner.track
  let selected := Selection.build scale (CoherentRoot.residualScale_nonneg _ _ owner.track) floor target positive
  let state := root.stateAt selected.stage
  let value := state.box.anchor
  exact ⟨⟨owner, rfl⟩, ⟨root, rfl⟩, ⟨scale, rfl⟩, ⟨selected, rfl⟩, ⟨state, rfl⟩, ⟨value, rfl⟩⟩

end Purelib.Riemann.RootContinuation.FixedRootBoxBudget.Budget

end
