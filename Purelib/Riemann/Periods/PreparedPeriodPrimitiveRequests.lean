module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

public import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Tactic.Ring

/-!
# Requested primitive comparisons with arbitrarily late period samples

The polynomial and spatial budgets are both paid internally.  A caller may
request a minimum period stage; the selected stage is at least that large.
This is a finite comparison with the existing period program, not a new
integration program or an assumed global cut-surface theorem.
-/

namespace Purelib.Riemann.Periods.PreparedPeriodPrimitiveRequests

open Purelib.Data
open Purelib.Curves
open Purelib.Approximation

public section

open Purelib.Data.Nat

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Topology.PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints (RootClosedState)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named)
open Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests (ControlledSumRequest)
open Purelib.Riemann.Periods.PreparedPeriodPrimitiveDecay (DecayBudget period_error_le)
open Purelib.Riemann.Periods.PreparedRootSafePeriodPrograms.RootClosedState (flatModel)
open Purelib.Riemann.Readings.PreparedPrimitiveRequests (Coordinate)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_antitone)

/-- The canonical Gaussian rational scalar type. -/
abbrev Gaussian := Gaussian.Basic.Canonical

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {source :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus} {root : Named}
  {target : Coordinate}

set_option genInjectivity false in
/-- Retain a computed comparison budget and a certified tail of the original period schedule.

The chosen stage meets the requested minimum and pays the spatial half-target before numerical sampling, so a finite
family can synchronize stages first. -/
structure PeriodTail (initial : RootClosedState curve source root) (targets : List
  (Hyperelliptic.Differentials.Basic.Differential genus))
    (differential : Hyperelliptic.Differentials.Basic.Differential genus)
    (request : ControlledSumRequest (initial.state.parents.map (recastCenteredEdge differential)) count target)
    (minimumStage : Nat) where
  /-- The retained decay budget from the original controlled primitive requests and schedule scale. -/ budget :
    DecayBudget request.requests (initial.state.scheduleBase targets)
  /-- The computed floor of the certified period tail. -/ stage : Nat
  /-- The certified tail floor meets the requested minimum stage. -/ stage_ge : minimumStage ≤ stage
  /-- The certified tail floor is strictly positive. -/ stage_positive : 0 < stage
  /-- The retained tail floor pays the spatial error strictly within half the target. -/ spatial_small :
    Rational.Geometric.Basic.quarterRadius budget.spatialScale stage < target / 2

constructive_injectivity PeriodTail

set_option genInjectivity false in
/-- Retain one actual period sample together with its certified tail budget.

The numerical value has an exact readback to the original flat model and a strict comparison with the same controlled
primitive sum. -/
structure PeriodSample (initial : RootClosedState curve source root) (targets : List
  (Hyperelliptic.Differentials.Basic.Differential genus))
    (differential : Hyperelliptic.Differentials.Basic.Differential genus)
    (request : ControlledSumRequest (initial.state.parents.map (recastCenteredEdge differential)) count target)
    (minimumStage : Nat) extends PeriodTail initial targets differential request minimumStage where
  /-- The cached numerical Gaussian sample of the original period model. -/ sample : Gaussian
  /-- The cached sample is exactly the original flat model's integral sample at the retained stage. -/ sample_eq :
    sample = (flatModel initial targets differential stage).integralSample
  /-- The primitive sum and cached period sample differ by less than the requested squared-error target. -/ accurate :
    normSq (request.primitiveSum - sample) < target

constructive_injectivity PeriodSample

namespace PeriodTail

/-- Compute a certified comparison tail beyond the supplied minimum stage.

The original request mass supplies the decay budget, and an explicit quarter-radius search pays the spatial half-target
without acquiring a numerical sample. -/
@[expose] def acquire (initial : RootClosedState curve source root) (targets : List
  (Hyperelliptic.Differentials.Basic.Differential genus))
    (differential : Hyperelliptic.Differentials.Basic.Differential genus)
    (request : ControlledSumRequest (initial.state.parents.map (recastCenteredEdge differential)) count target)
    (minimumStage : Nat) : PeriodTail initial targets differential request minimumStage := by
  let budget := DecayBudget.ofMass request.requests (initial.state.scheduleBase targets) request.mass request.mass_eq
  let half := target / 2
  have halfPositive : 0 < half := Rat.Fraction.Order.Field.div_pos_direct request.target_positive (by decide)
  let first := Rational.Geometric.Search.firstQuarterBelow budget.spatialScale 0 half
  let stage := max minimumStage first + 1
  have spatialSmall : Rational.Geometric.Basic.quarterRadius budget.spatialScale stage < half :=
    (quarterRadius_antitone
      (budget.spatialScale_nonnegative (initial.state.scheduleBase_positive targets).le)
      (Nat.le_trans (((congrArg (Nat.le _) (Order.max_eq_natMax _ _)).mpr (Order.le_max_right _ _))) (Nat.le_succ
        _))).trans_lt
        (Rational.Geometric.Search.firstQuarterBelow_accurate budget.spatialScale
          (budget.spatialScale_nonnegative (initial.state.scheduleBase_positive targets).le) 0 half halfPositive)
  exact
    { budget := budget
      stage := stage
      stage_ge := Nat.le_trans (((congrArg (Nat.le _) (Order.max_eq_natMax _ _)).mpr (Order.le_max_left _ _)))
        (Nat.le_succ _)
      stage_positive := Nat.zero_lt_succ _
      spatial_small := spatialSmall }

variable {initial : RootClosedState curve source root} {targets : List
  (Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus)}
  {differential : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {request : ControlledSumRequest (initial.state.parents.map (recastCenteredEdge differential)) count target}
  {minimumStage : Nat}

/-- Every later original period sample satisfies the requested primitive comparison.

Membership of the differential in the retained target family gives the original period-error bound, with polynomial and
spatial half-targets paid separately. -/
theorem accurate (tail : PeriodTail initial targets differential request minimumStage)
    (member : differential ∈ targets) (stage : Nat) (later : tail.stage ≤ stage) :
    normSq (request.primitiveSum - (flatModel initial targets differential stage).integralSample) < target := by
  have spatialSmall : Rational.Geometric.Basic.quarterRadius tail.budget.spatialScale stage < target / 2 :=
    (quarterRadius_antitone
      (tail.budget.spatialScale_nonnegative (initial.state.scheduleBase_positive targets).le) later).trans_lt
        tail.spatial_small
  have stagePositive := tail.stage_positive.trans_le later
  cases stage with
  | zero => exact (Nat.not_lt_zero _ stagePositive).elim
  | succ stage =>
      rw [request.primitiveSum_eq, request.increments_eq]
      have bounded := period_error_le initial targets differential member request.requests tail.budget stage
      have strict := bounded.trans_lt
        (Rat.Fraction.Order.Arithmetic.add_lt_add_left_direct spatialSmall tail.budget.polynomialFloor)
      have upper := Rat.Fraction.Order.Arithmetic.add_lt_add_right_direct (request.polynomialFloor_lt tail.budget)
        (target / 2)
      have paid : target / 2 + target / 2 = target := by
        calc
          _ = (target / 2) * 2 := by ring1
          _ = target := Rat.Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
      exact strict.trans (upper.trans_eq paid)

/-- Evaluate the original period model once at a chosen permitted common stage.

The request mass and retained decay budget are reused, and the cached tail-integral reading carries both its exact
readback and strict target certificate. -/
@[expose] def sampleAt (tail : PeriodTail initial targets differential request minimumStage)
    (member : differential ∈ targets) (stage : Nat) (later : tail.stage ≤ stage) :
    PeriodSample initial targets differential request minimumStage :=
  let path := flatModel initial targets differential stage
  { budget := tail.budget
    stage := stage
    stage_ge := tail.stage_ge.trans later
    stage_positive := tail.stage_positive.trans_le later
    spatial_small := (quarterRadius_antitone
      (tail.budget.spatialScale_nonnegative (initial.state.scheduleBase_positive targets).le) later).trans_lt
        tail.spatial_small
    sample := path.tailIntegralSample
    sample_eq := path.integralSample_eq_tailIntegralSample.symm
    accurate := by rw [← path.integralSample_eq_tailIntegralSample]; exact tail.accurate member stage later }

/-- Sampling at a supplied permitted stage retains exactly that stage. -/
theorem sampleAt_stage (tail : PeriodTail initial targets differential request minimumStage)
    (member : differential ∈ targets) (stage : Nat) (later : tail.stage ≤ stage) :
    (tail.sampleAt member stage later).stage = stage := rfl

end PeriodTail

namespace PeriodSample

/-- Acquire one requested period sample from the retained tail preparation.

The computed tail floor is used as the numerical stage, retaining the same budget and all-later comparison certificate.
-/
@[expose] def acquire (initial : RootClosedState curve source root) (targets : List
  (Hyperelliptic.Differentials.Basic.Differential genus))
    (differential : Hyperelliptic.Differentials.Basic.Differential genus) (member : differential ∈ targets)
    (request : ControlledSumRequest (initial.state.parents.map (recastCenteredEdge differential)) count target)
    (minimumStage : Nat) : PeriodSample initial targets differential request minimumStage :=
  let tail := PeriodTail.acquire initial targets differential request minimumStage
  tail.sampleAt member tail.stage (Nat.le_refl _)

end PeriodSample

end

end Purelib.Riemann.Periods.PreparedPeriodPrimitiveRequests
