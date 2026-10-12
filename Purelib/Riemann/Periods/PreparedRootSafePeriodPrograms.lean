module
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedRefinementProgramCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Path.Gaussian.Lifted.Refinement
import Purelib.Integration.Polynomial.Gaussian.Path.CompatibleRefinement
import Purelib.Integration.Program.Gaussian.Sequential
import Purelib.Riemann.Integration.PreparedOwnerClosedSchedules
import Purelib.Riemann.Periods.PeriodMatrix

public import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Riemann.Readings.PreparedBoundaryClosure
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Riemann.Topology.PreparedCycleModels
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Riemann.Readings.PreparedBoundaryGluing
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Data.Gaussian.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_antitone)

@[expose] public section

/-!
# Certified period programs with root-closed finite stages

The root-safe finite-family refinements supply consecutive integration
comparisons and a quarter-rate allowance bound.  The complete switched
program restores the exact-zero stationary cells and pays their finite
allowance factor.  Every displayed cycle is operationally root closed.
No identification with independently seeded periods or geometric symplectic
intersection theorem is inferred from this construction.
-/

namespace Purelib.Riemann.Periods.PreparedRootSafePeriodPrograms.RootClosedState

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Topology.PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints (RootClosedState)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named)
open Purelib.Data.Rat in
/-- The rational coordinate carrier of root-safe period bounds. -/
private abbrev Coordinate := Fraction.Rational
open Purelib.Riemann.Integration.PreparedSwitchedRefinements (SwitchedPathChain)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
open Purelib.Integration.Program.Gaussian.Sequential (SequentialCompatibleConstantRefinementProgram)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {source :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus} {root : Named}

open Purelib.Data.Rat in
/-- A natural-number count casts to a nonnegative rational coordinate. -/
public theorem natCast_nonnegative (value : Nat) : (0 : Fraction.Rational) ≤ (value : Fraction.Rational) := by
  induction value with
  | zero => exact le_rfl
  | succ value ih =>
      rw [Nat.cast_succ]
      exact add_nonneg ih (by decide)

open Purelib.Curves.Hyperelliptic in
/-- Read the target differential's recast parent model at the retained root-safe stage. -/
def flatModel (initial : RootClosedState curve source root) (targets : List (Differentials.Basic.Differential genus))
    (differential : Differentials.Basic.Differential genus) (index : Nat) : PathModel :=
  ⟨(((initial.states targets index).state.parents.map (recastCenteredEdge differential)).map CenteredEdge.model)⟩

open Purelib.Curves.Hyperelliptic in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The checked compatible refinement between consecutive root-safe flat models. -/
def flatStep (initial : RootClosedState curve source root) (targets : List (Differentials.Basic.Differential genus))
    (differential : Differentials.Basic.Differential genus) (index : Nat) :
    Basic.PathModel.CompatibleConstantPathRefinement (flatModel initial targets differential index).cells
      (flatModel initial targets differential (index + 1)).cells :=
  (initial.scheduledStep targets index).compatible differential

open Purelib.Curves.Hyperelliptic in
/-- A requested differential's initial flat allowance is bounded by the original schedule base. -/
theorem initialAllowance_le (initial : RootClosedState curve source root) (targets : List
  (Differentials.Basic.Differential genus))
    (differential : Differentials.Basic.Differential genus) (member : differential ∈ targets) :
    (flatModel initial targets differential 0).aggregateAllowance ≤ initial.state.scheduleBase targets :=
  initial.state.initialFlatModelAllowance_le_base targets differential member

open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
/-- Every requested root-safe flat model meets its stage's geometric allowance bound. -/
theorem flatAllowance_le (initial : RootClosedState curve source root) (targets : List (Differentials.Basic.Differential
  genus))
    (differential : Differentials.Basic.Differential genus) (member : differential ∈ targets) :
    ∀ index, (flatModel initial targets differential index).aggregateAllowance ≤
      Geometric.Basic.quarterRadius (initial.state.scheduleBase targets) index
  | 0 => by
      simpa only [Geometric.Basic.quarterRadius_eq_mul_pow, pow_zero, Fraction.Field.mul_one_direct] using
        initialAllowance_le initial targets differential member
  | index + 1 => (initial.scheduledStep targets index).flatAllowance_le differential member

open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Consecutive flat comparisons meet the geometric bound with three times the original schedule base. -/
theorem flatComparison_le (initial : RootClosedState curve source root) (targets : List
  (Differentials.Basic.Differential genus))
    (differential : Differentials.Basic.Differential genus) (member : differential ∈ targets) (index : Nat) :
    (CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.comparisonAllowance (flatStep initial targets
      differential index)) ≤
      Geometric.Basic.quarterRadius (3 * initial.state.scheduleBase targets) index := by
  have compared := (initial.scheduledStep targets index).comparisonAllowance_le differential member
  have parent := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (flatAllowance_le initial targets differential member index) (show (0 : Fraction.Rational) ≤ 2 by decide)
  have later := quarterRadius_antitone
    (initial.state.scheduleBase_positive targets).le (Nat.le_succ index)
  calc
    _ ≤ 2 * (flatModel initial targets differential index).aggregateAllowance +
        initial.state.scheduleTarget targets index := compared
    _ ≤ 2 * Geometric.Basic.quarterRadius (initial.state.scheduleBase targets) index +
        Geometric.Basic.quarterRadius (initial.state.scheduleBase targets) index := add_le_add parent later
    _ = _ := by
      rw [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]
      ring1

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
open Purelib.Integration.Program in
/-- Package the root-safe flat models and consecutive compatible refinements.

The retained original stage sequence supplies all models and witnesses; its comparison scale is three times the initial
state's schedule base. -/
def flatProgram (initial : RootClosedState curve source root) (targets : List (Differentials.Basic.Differential genus))
    (differential : Differentials.Basic.Differential genus) (member : differential ∈ targets) :
      Gaussian.Sequential.SequentialCompatibleConstantRefinementProgram where
  model := flatModel initial targets differential
  steps := flatStep initial targets differential
  stepScale := 3 * initial.state.scheduleBase targets
  stepScale_nonneg := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (initial.state.scheduleBase_positive
    targets).le
  initialAllowance_le := by
    calc
      _ ≤ initial.state.scheduleBase targets := initialAllowance_le initial targets differential member
      _ = 1 * initial.state.scheduleBase targets := by ring1
      _ ≤ 12 * initial.state.scheduleBase targets :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (show (1 : Fraction.Rational) ≤ 12 by decide)
          (initial.state.scheduleBase_positive targets).le
      _ = _ := by ring1
  comparisonAllowance_le := flatComparison_le initial targets differential member

open Purelib.Curves.Hyperelliptic in
/-- The switched root-safe model has exactly the same sample as its flat parent model. -/
theorem sample_eq_flat (initial : RootClosedState curve source root) (targets : List (Differentials.Basic.Differential
  genus))
    (differential : Differentials.Basic.Differential genus) (index : Nat) :
    ((initial.states targets index).state.model differential).integralSample =
      (flatModel initial targets differential index).integralSample :=
  SwitchedPathChain.recastCells_integralSample differential (initial.states targets index).state.chain

open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
/-- The period refinement program of the exact root-safe switched stages.

The stationary-switch factor scales the flat error payments while the identical flat samples supply later closeness and
the uniform center bound. -/
def period (initial : RootClosedState curve source root) (targets : List (Differentials.Basic.Differential genus))
    (differential : Differentials.Basic.Differential genus) (member : differential ∈ targets) : RefinementProgram := by
  let flat := (flatProgram initial targets differential member).toRefinementProgram
  let factor := initial.state.chain.switchFactor
  have factorPositive : 0 < factor := initial.state.chain.switchFactor_positive
  have oneLeFactor : (1 : Fraction.Rational) ≤ factor := by
    unfold factor SwitchedPathChain.switchFactor
    exact le_add_of_nonneg_left (natCast_nonnegative initial.state.chain.switchCount)
  exact
    { model := fun index => (initial.states targets index).state.model differential
      errorScale := factor * flat.errorScale
      errorScale_nonneg := Fraction.Order.Arithmetic.mul_nonneg_direct factorPositive.le flat.errorScale_nonneg
      modelAllowance_le := by
        intro index
        have bound := SwitchedPathChain.recastCells_aggregateAllowance_le_switchFactor
          differential (initial.states targets index).state.chain
        have factorEq : (initial.states targets index).state.chain.switchFactor = factor :=
          congrArg (fun count : Nat => (count : Fraction.Rational) + 1) (initial.states_switchCount targets index)
        rw [factorEq] at bound
        calc
          _ ≤ factor * (flatModel initial targets differential index).aggregateAllowance := bound
          _ ≤ factor * Geometric.Basic.quarterRadius flat.errorScale index :=
            Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (flat.modelAllowance_le index) factorPositive.le
          _ = _ := by
            rw [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]
            ring1
      later_close := by
        intro earlier later order
        rw [sample_eq_flat initial targets differential, sample_eq_flat initial targets differential]
        calc
          _ ≤ Geometric.Basic.quarterRadius flat.errorScale earlier := flat.later_close order
          _ = 1 * Geometric.Basic.quarterRadius flat.errorScale earlier := by ring1
          _ ≤ factor * Geometric.Basic.quarterRadius flat.errorScale earlier :=
            Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct oneLeFactor
              (Geometric.Basic.quarterRadius_nonneg flat.errorScale_nonneg earlier)
          _ = _ := by
            rw [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]
            ring1
      centerBound := flat.centerBound
      centerBound_nonneg := flat.centerBound_nonneg
      sample_bounded := by
        intro index
        rw [sample_eq_flat initial targets differential]
        exact flat.sample_bounded index }

open Purelib.Curves.Hyperelliptic in
open Purelib.Geometry.Path.Gaussian in
/-- Read the closed lifted-cycle sequence from the retained root-safe states. -/
def cycle (initial : RootClosedState curve source root) (targets : List (Differentials.Basic.Differential genus)) :
    Lifted.Refinement.LiftedCycleRefinement 2 where
  liftedPath := fun index => (initial.states targets index).state.closedLift (initial.states targets index).closed

open Purelib.Curves.Hyperelliptic in
open Purelib.Curves.Hyperelliptic.Integration in
/-- Certify the target differential integral on the exact retained root-safe cycle sequence. -/
def certifiedPeriodProgram (initial : RootClosedState curve source root) (targets : List
  (Differentials.Basic.Differential genus))
    (differential : Differentials.Basic.Differential genus) (member : differential ∈ targets) :
    Algebraic.Period.Basis.CertifiedPeriodProgram curve differential (cycle initial targets) where
  integral := period initial targets differential member
  certificates := fun index =>
    ((initial.states targets index).state.certifiedClosedModel (initial.states targets index).closed
      differential).certificates

end Purelib.Riemann.Periods.PreparedRootSafePeriodPrograms.RootClosedState

namespace Purelib.Riemann.Periods.PreparedRootSafePeriodPrograms.PreparedRefinementPrograms

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Riemann.Integration.PreparedRefinementProgramCore (standardDifferentials
  standardDifferential_mem_standardDifferentials)
open Purelib.Riemann.Readings.PreparedBoundaryClosure (ClosedBoundaryDoublePath)

open Purelib.Curves.Hyperelliptic in
open Purelib.Geometry.Path.Gaussian in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Periods in
open Purelib.Riemann.Topology in
/-- The root-safe A-cycle sequence from the original canonical owner-closed seed. -/
def ownerClosedARootCycle {genus : Nat} (curve : Basic.HyperellipticCurve genus) (cycleIndex : Fin genus) :
    Lifted.Refinement.LiftedCycleRefinement 2 :=
  PreparedRootSafePeriodPrograms.RootClosedState.cycle
    (PreparedRootSafeCycleStates.ClosedBoundaryDoublePath.rootClosedInitial
      (PreparedOwnerClosedSchedules.PreparedRefinementPrograms.ownerClosedASeed curve cycleIndex)
      (PeriodMatrix.standardDifferential cycleIndex))
    (standardDifferentials genus)

open Purelib.Curves.Hyperelliptic in
open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Periods in
open Purelib.Riemann.Topology in
/-- The requested standard differential's certified period on the original root-safe A cycle. -/
def ownerClosedARootPeriodProgram {genus : Nat} (curve : Basic.HyperellipticCurve genus)
    (cycleIndex differentialIndex : Fin genus) :
    Algebraic.Period.Basis.CertifiedPeriodProgram curve (PeriodMatrix.standardDifferential differentialIndex)
      (ownerClosedARootCycle curve cycleIndex) :=
  PreparedRootSafePeriodPrograms.RootClosedState.certifiedPeriodProgram
    (PreparedRootSafeCycleStates.ClosedBoundaryDoublePath.rootClosedInitial
      (PreparedOwnerClosedSchedules.PreparedRefinementPrograms.ownerClosedASeed curve cycleIndex)
      (PeriodMatrix.standardDifferential cycleIndex))
    (standardDifferentials genus) (PeriodMatrix.standardDifferential differentialIndex)
    (standardDifferential_mem_standardDifferentials differentialIndex)

end Purelib.Riemann.Periods.PreparedRootSafePeriodPrograms.PreparedRefinementPrograms
