module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic

public import Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds
import Purelib.Riemann.Topology.PreparedRecastRootChains
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.Integration.PreparedEdgeRecasting
public import Purelib.Riemann.Periods.PreparedRootSafePeriodPrograms
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-!
# A computed spatial decay rate against the actual period scheduler

The fixed primitive bank has two independent errors: a polynomial coefficient
floor and a quarter-decaying spatial/model term.  The latter uses the existing
period stages, including their growing cell count.  Selecting a finer spatial
stage does not claim to remove the polynomial floor.
-/

namespace Purelib.Riemann.Periods.PreparedPeriodPrimitiveDecay

open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Topology.PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints
  (RootClosedState)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named)
open Purelib.Riemann.Readings.UniformPreparedRequests (RequestedParents)
open Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds
  (remainderMaximum coefficientMaximum remainderMaximum_nonnegative
    coefficientMaximum_nonnegative refinement_error_bound)
open Purelib.Riemann.Periods.PreparedRootSafePeriodPrograms.RootClosedState
  (flatModel flatAllowance_le)
open Purelib.Riemann.Integration.PreparedRefinementMovement (movementMass movementMass_nonnegative movementMass_recast)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_nonneg quarterRadius_antitone)

open Purelib.Data.Rat in
/-- The rational coordinate carrier of the retained primitive decay budget. -/
private abbrev Coordinate := Fraction.Rational

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus} {target : Purelib.Data.Rat.Fraction.Rational}

open Purelib.Data.Rat in
set_option genInjectivity false in
/-- Cached primitive-error coefficients tied to the exact original request family and movement mass.

The polynomial floor is coefficient times mass, while the spatial scale combines remainder times mass and the
five-halves allowance factor at the retained schedule base. -/
structure DecayBudget {parents : List (CenteredEdge curve differential)}
    (requests : RequestedParents count target parents) (base : Fraction.Rational) where
  /-- The cached original parent movement mass. -/ mass : Fraction.Rational
  /-- Exact equality with the original request family's parent movement mass. -/ mass_eq : mass = movementMass parents
  /-- The cached original primitive remainder maximum. -/ remainder : Fraction.Rational
  /-- Exact equality with this retained request family's remainder maximum. -/ remainder_eq : remainder =
    remainderMaximum requests
  /-- The cached original local inverse-error coefficient maximum. -/ coefficient : Fraction.Rational
  /-- Exact equality with this retained request family's coefficient maximum. -/ coefficient_eq : coefficient =
    coefficientMaximum requests
  /-- The retained coefficient-times-mass error floor. -/ polynomialFloor : Fraction.Rational
  /-- The original floor is exactly the retained coefficient times mass. -/ polynomialFloor_eq : polynomialFloor =
    coefficient * mass
  /-- The retained spatial decay scale at this schedule base. -/ spatialScale : Fraction.Rational
  /-- The exact remainder-mass and five-halves allowance formula for the spatial scale. -/ spatialScale_eq :
    spatialScale = (remainder * mass + 5 / 2) * base

constructive_injectivity DecayBudget

namespace DecayBudget

variable {parents : List (CenteredEdge curve differential)} {requests : RequestedParents count target parents} {base :
  Purelib.Data.Rat.Fraction.Rational}

open Purelib.Data.Rat in
/-- Construct the decay budget from a supplied exact original movement-mass cache. -/
def ofMass (requests : RequestedParents count target parents) (base mass : Fraction.Rational)
    (massEq : mass = movementMass parents) : DecayBudget requests base :=
  let remainder := remainderMaximum requests
  let coefficient := coefficientMaximum requests
  { mass := mass
    mass_eq := massEq
    remainder := remainder
    remainder_eq := rfl
    coefficient := coefficient
    coefficient_eq := rfl
    polynomialFloor := coefficient * mass
    polynomialFloor_eq := rfl
    spatialScale := (remainder * mass + 5 / 2) * base
    spatialScale_eq := rfl }

/-- The retained original movement mass is nonnegative. -/
theorem mass_nonnegative (budget : DecayBudget requests base) : 0 ≤ budget.mass := by
  rw [budget.mass_eq]
  exact movementMass_nonnegative _

/-- The retained original remainder maximum is nonnegative. -/
theorem remainder_nonnegative (budget : DecayBudget requests base) : 0 ≤ budget.remainder := by
  rw [budget.remainder_eq]
  exact remainderMaximum_nonnegative requests

/-- The retained original local coefficient maximum is nonnegative. -/
theorem coefficient_nonnegative (budget : DecayBudget requests base) : 0 ≤ budget.coefficient := by
  rw [budget.coefficient_eq]
  exact coefficientMaximum_nonnegative requests

section
open Purelib.Data.Rat
/-- The retained coefficient-times-mass floor is nonnegative. -/
theorem polynomialFloor_nonnegative (budget : DecayBudget requests base) : 0 ≤ budget.polynomialFloor := by
  rw [budget.polynomialFloor_eq]
  exact Fraction.Order.Arithmetic.mul_nonneg_direct budget.coefficient_nonnegative budget.mass_nonnegative

/-- The retained spatial error scale is nonnegative when its original base is nonnegative. -/
theorem spatialScale_nonnegative (budget : DecayBudget requests base) (baseNonnegative : 0 ≤ base) : 0 ≤
  budget.spatialScale := by
  rw [budget.spatialScale_eq]
  exact Fraction.Order.Arithmetic.mul_nonneg_direct
    (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct budget.remainder_nonnegative budget.mass_nonnegative) (by
      decide)) baseNonnegative

end

open Purelib.Approximation.Rational
open Purelib.Data.Rat
/-- Select an executable quarter-radius stage for the retained spatial scale and tolerance. -/
def spatialStage (budget : DecayBudget requests base) (tolerance : Fraction.Rational) : Nat :=
  Geometric.Search.firstQuarterBelow budget.spatialScale 0 tolerance + 1

/-- The selected spatial stage reduces the original spatial error below the positive tolerance. -/
theorem spatialStage_accurate (budget : DecayBudget requests base) (baseNonnegative : 0 ≤ base)
    {tolerance : Fraction.Rational} (positive : 0 < tolerance) :
    Geometric.Basic.quarterRadius budget.spatialScale (budget.spatialStage tolerance) < tolerance :=
  (quarterRadius_antitone (budget.spatialScale_nonnegative baseNonnegative) (Nat.le_succ
    _)).trans_lt
    (Geometric.Search.firstQuarterBelow_accurate budget.spatialScale (budget.spatialScale_nonnegative baseNonnegative) 0
      tolerance positive)

end DecayBudget

open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.List in
open Purelib.Data.Rat in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Topology in
/-- The scheduled period error is bounded by its retained polynomial floor plus decaying spatial charge.

The original initial parents and exact differential recasts determine the request family; retained movement-mass and
allowance bounds pay the same flat model at the next stage. -/
theorem period_error_le {source : Differentials.Basic.Differential genus} {root : Named}
    (initial : RootClosedState curve source root) (targets : List (Differentials.Basic.Differential genus))
    (differential : Differentials.Basic.Differential genus) (member : differential ∈ targets)
    (requests : RequestedParents count target (initial.state.parents.map (recastCenteredEdge differential)))
    (budget : DecayBudget requests (initial.state.scheduleBase targets)) (stage : Nat) :
    normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum requests.increments - (flatModel initial targets differential
      (stage +
      1)).integralSample) ≤
      budget.polynomialFloor + Geometric.Basic.quarterRadius budget.spatialScale (stage + 1) := by
  let current := initial.states targets (stage + 1)
  let children := current.state.parents.map (recastCenteredEdge differential)
  let radius := Geometric.Basic.quarterRadius (initial.state.scheduleBase targets) (stage + 1)
  have radiusNonnegative : 0 ≤ radius := Geometric.Basic.quarterRadius_nonneg (initial.state.scheduleBase_positive
    targets).le _
  have movements : ∀ child ∈ children, child.edge.pointMovement ≤ radius := by
    intro child belongs
    obtain ⟨original, originalMember, rfl⟩ := Map.mem_map.mp belongs
    change original.edge.pointMovement ≤ initial.state.scheduleTarget targets stage
    exact PreparedRefinementMovement.RootClosedState.states_childMovement_le initial targets stage originalMember
  have massBound : movementMass children ≤ budget.mass := by
    rw [budget.mass_eq, movementMass_recast, movementMass_recast]
    exact PreparedRefinementMovement.RootClosedState.states_movementMass_le initial targets (stage + 1)
  have allowance := flatAllowance_le initial targets differential member (stage + 1)
  have bound := refinement_error_bound requests
    (PreparedRecastRootChains.PreparedRefinementRootEndpoints.RootSubedgeRefinement.recast
      differential (initial.statesSubedges targets (stage + 1))) movements
  rw [← budget.remainder_eq, ← budget.coefficient_eq] at bound
  have multiplierNonnegative := add_nonneg
    (Fraction.Order.Arithmetic.mul_nonneg_direct budget.remainder_nonnegative radiusNonnegative)
      budget.coefficient_nonnegative
  have paid := add_le_add (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct massBound multiplierNonnegative)
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct allowance (by decide : (0 : Fraction.Rational) ≤ 5 / 2))
  exact (bound.trans paid).trans_eq (by
    rw [budget.polynomialFloor_eq, budget.spatialScale_eq]
    dsimp only [radius]
    rw [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]
    ring1)

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- At the selected stage, the original period error is below its polynomial floor plus positive tolerance. -/
theorem period_error_lt_at_spatialStage {source : Differentials.Basic.Differential genus} {root : Named}
    (initial : RootClosedState curve source root) (targets : List (Differentials.Basic.Differential genus))
    (differential : Differentials.Basic.Differential genus) (member : differential ∈ targets)
    (requests : RequestedParents count target (initial.state.parents.map (recastCenteredEdge differential)))
    (budget : DecayBudget requests (initial.state.scheduleBase targets))
    (tolerance : Fraction.Rational) (positive : 0 < tolerance) :
    normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum requests.increments -
      (flatModel initial targets differential (budget.spatialStage tolerance)).integralSample) <
        budget.polynomialFloor + tolerance :=
  (period_error_le initial targets differential member requests budget _).trans_lt
    (Fraction.Order.Arithmetic.add_lt_add_left_direct
      (budget.spatialStage_accurate (initial.state.scheduleBase_positive targets).le positive) budget.polynomialFloor)

end Purelib.Riemann.Periods.PreparedPeriodPrimitiveDecay
