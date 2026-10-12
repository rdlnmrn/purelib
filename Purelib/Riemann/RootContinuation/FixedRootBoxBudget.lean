module

meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.RootContinuation.SquareRootReconditioning
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Polynomial.Power.Gaussian.Perturbation
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.RootIsolation.Owner.Local.Basic
import Purelib.RootIsolation.Owner.Local.Track
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Dominance.Basic
import Purelib.Polynomial.Clearance.Box.Dominance.Majorant
public import Purelib.Riemann.Branches.PreparedPrimitiveSheets
import Purelib.Riemann.RootContinuation.SquareRootContinuation
import Purelib.Riemann.Topology.SquareRootContinuationChain

import Purelib.Riemann.RootContinuation.RootContinuationCongruence
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Geometry.Rational.Box.Basic
import Purelib.RootIsolation.FTA.Squarefree.Input
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Polynomial.Power.Gaussian
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.RootIsolation.Track.Basic
import Mathlib.Order.Basic

public section

/-!
# Uniform clearance for one retained root box

A fixed upper bound on the accepted radicand movement leaves a positive
Rouché margin on the original owner box.  A cached finite Horner majorant
turns that margin into one positive clearance valid at every intermediate
radicand.  Child depth can therefore be selected before extracting children.
The construction does not require a new canonical owner or a successful scan.
-/

namespace Purelib.Riemann.RootContinuation.FixedRootBoxBudget

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence

open Purelib.Data.Rat in
/-- The exact rational carrier for fixed root-box movement and clearance budgets. -/
abbrev Coordinate := Fraction.Rational
open Purelib.Data.Gaussian in
/-- The canonical Gaussian rational carrier for original root parameters. -/
abbrev Gaussian := Basic.Canonical
/-- The original winding-one quadratic root owner indexed by its exact parameter. -/
abbrev Owner := Purelib.Riemann.Topology.SquareRootContinuationChain.Owner
/-- The original operational equivalence certificate between retained Gaussian names. -/
abbrev NamedEquivalent := Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent

set_option genInjectivity false in
open Purelib.Polynomial.Dense.Gaussian in
/-- Cached movement and target-clearance bounds for the exact initial box of an original root owner.

The nonnegative movement lies below the original contour clearance. Exact equations retain the polynomial norm majorant,
remaining margin and squared-margin clearance used at every permitted target. -/
structure Budget {source : Gaussian} (owner : Owner source) where
  /-- The retained upper bound on squared source-to-target parameter movement. -/ movement : Coordinate
  /-- The original movement allowance is nonnegative. -/ movement_nonnegative : 0 ≤ movement
  /-- The movement allowance is strictly smaller than the original source contour clearance. -/ movement_lt : movement <
    owner.track.initial.clearance.bound
  /-- The cached contour clearance of the original source owner's initial box. -/ sourceClearance : Coordinate
  /-- The cache equals the exact original initial contour-clearance bound. -/ sourceClearance_eq : sourceClearance =
    owner.track.initial.clearance.bound
  /-- The cached dense squared-norm majorant of the original source root polynomial on its initial box. -/ majorant :
    Coordinate
  /-- The cache equals the exact original dense polynomial box majorant. -/ majorant_eq : majorant =
    Bounds.Box.denseEvalNormMajorant
    (SquareRootReconditioning.rootPolynomial source) owner.track.initial.box
  /-- The retained boundary margin after paying the full movement allowance. -/ margin : Coordinate
  /-- The margin equals the cached source clearance minus the retained movement. -/ margin_eq : margin = sourceClearance
    - movement
  /-- The retained common positive target-clearance bound on the original fixed box. -/ clearance : Coordinate
  /-- The target clearance equals the squared retained margin divided by four times the original majorant. -/
    clearance_eq : clearance = margin ^ 2 / (4 * majorant)

constructive_injectivity Budget

namespace Budget

variable {source : Gaussian} {owner : Owner source}

section
open Purelib.Polynomial.Dense.Gaussian
/-- Cache a fixed-box budget from a nonnegative movement strictly below the original owner's contour clearance.

The original source clearance and dense polynomial box majorant determine the retained margin and target-clearance
formula without replacing the owner or box. -/
@[expose] def acquire (owner : Owner source) (movement : Coordinate)
    (nonnegative : 0 ≤ movement) (small : movement < owner.track.initial.clearance.bound) : Budget owner :=
  let sourceClearance := owner.track.initial.clearance.bound
  let majorant := Bounds.Box.denseEvalNormMajorant
    (SquareRootReconditioning.rootPolynomial source) owner.track.initial.box
  let margin := sourceClearance - movement
  let clearance := margin ^ 2 / (4 * majorant)
  ⟨movement, nonnegative, small, sourceClearance, rfl, majorant, rfl, margin, rfl, clearance, rfl⟩

/-- The cached dense polynomial squared-norm majorant is strictly positive. -/
theorem majorant_positive (budget : Budget owner) : 0 < budget.majorant := by
  rw [budget.majorant_eq]
  exact Bounds.Box.denseEvalNormMajorant_pos _ _

end

section
open Purelib.Data.Rat
/-- The retained source clearance minus the permitted movement is strictly positive. -/
theorem margin_positive (budget : Budget owner) : 0 < budget.margin := by
  rw [budget.margin_eq, budget.sourceClearance_eq]
  exact Fraction.Order.Arithmetic.sub_pos_direct budget.movement_lt

/-- The retained squared-margin target-clearance bound is strictly positive. -/
theorem clearance_positive (budget : Budget owner) : 0 < budget.clearance := by
  rw [budget.clearance_eq]
  exact Fraction.Order.Field.div_pos_direct
    (Fraction.Order.Arithmetic.pow_pos_direct budget.margin_positive 2)
    (Fraction.Order.Arithmetic.mul_pos_direct (by decide) budget.majorant_positive)

end

open Purelib.Data.Rat in
open Purelib.Polynomial.Clearance.Box in
open Purelib.Polynomial.Power in
/-- Certify boundary dominance of the original root polynomial over a permitted parameter perturbation using the
retained margin. -/
private def dominance (budget : Budget owner) (target : Gaussian)
    (movement : normSq (source - target) ≤ budget.movement) :
    Dominance.Basic.BoundaryNormDominance
      (SquareRootReconditioning.rootPolynomial source)
      (Gaussian.Perturbation.parameterPerturbation source target) owner.track.initial.box where
  margin := budget.margin
  positive := budget.margin_positive
  lower := by
    intro point boundary
    rw [budget.margin_eq, budget.sourceClearance_eq, Gaussian.Perturbation.parameterPerturbation_eval]
    exact Fraction.Order.Arithmetic.sub_le_sub_direct (owner.track.initial.clearance.lower point boundary) movement

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial.Clearance.Box in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Polynomial.Power in
open Purelib.Riemann.RootContinuation in
/-- Certify the target root polynomial's clearance on the exact original initial box using the cached budget.

The target movement is bounded by the retained allowance. The original source majorant and boundary dominance give the
exact cached positive target bound. -/
@[expose] def targetClearance (budget : Budget owner) (target : Gaussian)
    (movement : normSq (source - target) ≤ budget.movement) :
    Boundary.Basic.BoundaryClearance (SquareRootReconditioning.rootPolynomial target)
      owner.track.initial.box where
  bound := budget.clearance
  positive := budget.clearance_positive
  lower := by
    intro point boundary
    have upper : ∀ z : Gaussian, Box.Boundary.OnBoxBoundary owner.track.initial.box z →
        normSq ((SquareRootReconditioning.rootPolynomial source).eval z) ≤ budget.majorant := by
      intro z inside
      rw [budget.majorant_eq]
      simpa only [Norm.Basic.normSq_eq_canonical] using
        Bounds.Box.normSq_eval_le_denseEvalNormMajorant
          (SquareRootReconditioning.rootPolynomial source) inside.1
    have lower := (Dominance.Majorant.boundaryClearance_add_of_dominance_with_majorant
      (SquareRootReconditioning.rootPolynomial source) (Gaussian.Perturbation.parameterPerturbation source target)
      owner.track.initial.box (budget.dominance target movement) budget.majorant budget.majorant_positive upper).lower
        point boundary
    rw [budget.clearance_eq]
    change budget.margin ^ 2 / (4 * budget.majorant) ≤ _ at lower
    have polynomialEq : SquareRootReconditioning.rootPolynomial target =
        SquareRootReconditioning.rootPolynomial source + Gaussian.Perturbation.parameterPerturbation source target :=
      Gaussian.Perturbation.polynomial_target_eq_add_perturbation source target SquareRootDegree.degreeTwo
    rw [← polynomialEq] at lower
    exact lower

open Purelib.Data.Gaussian in
open Purelib.Riemann.RootContinuation in
open Purelib.RootIsolation in
/-- Construct a target root owner on the exact original initial box with the retained budget clearance.

The target is nonzero and its movement satisfies the original budget. Transported winding data and the original
quadratic isolation input construct the target track without changing the retained box. -/
@[expose] def ownerAt (budget : Budget owner) {target : Gaussian} (nonzero : target ≠ 0)
    (movement : normSq (source - target) ≤ budget.movement) : Owner target :=
  let localOwner : Owner.Local.Basic.LocalOwner (SquareRootReconditioning.rootPolynomial target) :=
    { box := owner.track.initial.box
      proper := owner.track.initial.proper
      clearance := budget.targetClearance target movement
      rawWindingFour :=
        (SquareRootContinuation.transportedOwner owner.track.initial (by
            simpa only [Norm.Basic.normSq_eq_canonical]
              using movement.trans_lt budget.movement_lt)).rawWindingFour }
  ⟨nonzero, owner.track.initial.box,
    localOwner.track (SquareRootReconditioning.isolationInput nonzero).degreeAtLeastTwo
      (SquareRootReconditioning.isolationInput nonzero).squarefree⟩

/-- The budget's target owner keeps exactly the original source owner's initial box. -/
@[simp] theorem ownerAt_box (budget : Budget owner) {target : Gaussian} (nonzero : target ≠ 0)
    (movement : normSq (source - target) ≤ budget.movement) :
    (budget.ownerAt nonzero movement).track.initial.box = owner.track.initial.box := rfl

/-- The budget's target owner keeps exactly the retained target-clearance bound. -/
@[simp] theorem ownerAt_clearance (budget : Budget owner) {target : Gaussian} (nonzero : target ≠ 0)
    (movement : normSq (source - target) ≤ budget.movement) :
    (budget.ownerAt nonzero movement).track.initial.clearance.bound = budget.clearance := rfl

open Purelib.Riemann.Branches in
/-- Compare the budget's target root name with a supplied target owner refining the original fixed box.

The target satisfies the original movement budget, and both retained names refer to the same exact nonzero parameter. -/
@[expose] def retainedEquivalent (budget : Budget owner) {target : Gaussian} (nonzero : target ≠ 0)
    (movement : normSq (source - target) ≤ budget.movement) (reading : Owner target)
    (refines : reading.track.initial.box.Refines owner.track.initial.box) :
    NamedEquivalent (ownerRootName nonzero (budget.ownerAt nonzero movement)) (ownerRootName nonzero reading) :=
  PreparedPrimitiveSheets.rootEquivalent_of_initial_refines nonzero
    (budget.ownerAt nonzero movement).track reading.track refines

end Budget

end Purelib.Riemann.RootContinuation.FixedRootBoxBudget

end
