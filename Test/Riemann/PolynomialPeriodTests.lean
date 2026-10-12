module
import Purelib.Riemann.Periods.PreparedRootSafePeriodPrograms
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Riemann.Integration.PreparedRefinementProgramCore
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.PeriodPolicies
import Purelib.Riemann.Periods.PeriodReplay

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank
public import Purelib.Riemann.Periods.PolynomialPeriodObservation
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Curves.Hyperelliptic.Preparation.Polynomial
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Nat.Schedule.PositiveStride
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Refinement
import Purelib.Integration.CertifiedProgram
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Integration.Program.Gaussian.Cached.Allocation
import Purelib.Integration.Program.Gaussian.Cached.Policy
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.SquareFactor.Basic
import Purelib.Riemann.Periods.PolynomialPeriodInput

open Purelib.Curves

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank

open Purelib.Polynomial.Dense.Gaussian.Basic

open Purelib.Riemann.Integration

open Purelib.Riemann.Periods

open Purelib.Riemann.Periods.PreparedRootSafePeriodPrograms

@[expose] public section

/-!
Kernel regressions for the polynomial-first input boundary.  Accepted-input
tests do not force their lazy period program, and rejected-observation tests
perform no root isolation or numerical period observation.
-/

namespace Test.Riemann.PolynomialPeriodTests

open _root_.Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients renaming CoefficientPolynomial ->
  GaussianPolynomial
open Purelib.Riemann.Periods.PolynomialPeriodInput

/-- Canonical replay uses the corrected bank's retained initial states for both genus-two columns and both cycle rows.
This checks full program ownership, not numerical coincidence with the former raw tours. -/
theorem corrected_replay_initial_programs
    (curve : Hyperelliptic.Basic.HyperellipticCurve 2) (differential index : Fin 2) :
    let bank := PairedPeriodBank.ofCurve curve
    let initial := bank.initialRow index
    RootClosedState.period initial.a
        (PreparedRefinementProgramCore.standardDifferentials 2)
        (PeriodMatrix.standardDifferential differential)
        (PreparedRefinementProgramCore.standardDifferential_mem_standardDifferentials differential) =
      (PeriodReplay.canonical curve (.a differential index)).program.integral ∧
    RootClosedState.period initial.b
        (PreparedRefinementProgramCore.standardDifferentials 2)
        (PeriodMatrix.standardDifferential differential)
        (PreparedRefinementProgramCore.standardDifferential_mem_standardDifferentials differential) =
      (PeriodReplay.canonical curve (.b differential index)).program.integral :=
  ⟨((PairedPeriodBank.ofCurve curve).initialRow index).a_program differential,
    ((PairedPeriodBank.ofCurve curve).initialRow index).b_program differential⟩

/-- Classify exact polynomial-period input failure as zero, constant, square-times-constant or an invalid
differential/cycle index. -/
public def failureTag {polynomial :
  Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {selection : Selection} :
    Failure polynomial selection → Nat
  | .zero _ => 0
  | .constantInput .. => 1
  | .squareTimesConstant .. => 2
  | .invalidIndex _ (.differential _) => 3
  | .invalidIndex _ (.cycle ..) => 4

/-- Prepare the original polynomial and period selection, retaining the exact failure class or an accepted-input tag. -/
public def inputTag (polynomial : Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
  (selection : Selection) : Nat
  :=
  match prepare polynomial selection with
  | .error failure => failureTag failure
  | .ok _ => 5

/-- Zero, constant and square-times-constant polynomial inputs have distinct retained preparation failures. -/
theorem degenerate_inputs :
    inputTag ⟨[0, 0]⟩ ⟨.a, 0, 0⟩ = 0 ∧
      inputTag ⟨[2]⟩ ⟨.a, 0, 0⟩ = 1 ∧
      inputTag ⟨[1, -2, 1]⟩ ⟨.a, 0, 0⟩ = 2 := by
  decide +kernel

/-- Regular genus-zero inputs reject the requested standard differential index. -/
theorem genus_zero_has_no_standard_entry :
    inputTag ⟨[1, 1]⟩ ⟨.a, 0, 0⟩ = 3 ∧
      inputTag ⟨[1, 0, 1]⟩ ⟨.b, 0, 0⟩ = 3 := by
  decide +kernel

/-- Check both selections against the reduced genus, not the original degree-five equation's apparent genus. -/
theorem reduced_genus_controls_indices :
    inputTag ⟨[2, -4, 0, 2, 2, -2]⟩ ⟨.a, 0, 0⟩ = 5 ∧
      inputTag ⟨[2, -4, 0, 2, 2, -2]⟩ ⟨.b, 0, 0⟩ = 5 ∧
      inputTag ⟨[2, -4, 0, 2, 2, -2]⟩ ⟨.a, 1, 0⟩ = 3 ∧
      inputTag ⟨[2, -4, 0, 2, 2, -2]⟩ ⟨.b, 0, 1⟩ = 4 := by
  decide +kernel

/-- The retained zero-floor period-observation policy with an empty refinement schedule. -/
public def policy : PeriodPolicies.Policy := ⟨⟨0, 0⟩, ⟨0, []⟩⟩

/-- The retained period request at index zero with positive allowance one. -/
public def request : PeriodPolicies.Request := ⟨0, 1, by decide⟩

/-- A nonzero bit request_public with an invalid index is rejected before a source program is forced; this is not a
successful numerical-observation test. -/
theorem observation_rejects_invalid_index :
    (match PolynomialPeriodObservation.observe
        ⟨[1, 0, -1, -1]⟩ ⟨.a, 1, 0⟩ policy request 2 with
      | .error failure => failureTag failure
      | .ok _ => 5) = 3 := by
  decide +kernel

/-- The period-comparison input check rejects the invalid cycle index before numerical observation. -/
theorem comparison_rejects_invalid_index :
    (match PolynomialPeriodObservation.canonical_period_contract
        ⟨[1, 0, -1, -1]⟩ ⟨.b, 0, 1⟩ policy policy request 2 with
      | .error failure => failureTag failure
      | .ok _ => 5) = 4 := by
  decide +kernel

/-- The exact input boundary supplies a witness for every finite request_public, not only a preselected observation.
This theorem does not execute the canonical numerical run and therefore does not replace its runtime gate. -/
theorem repeated_factor_observation_exists (side : Side)
    (observationPolicy : PeriodPolicies.Policy)
    (query : PeriodPolicies.Request) (count : Nat) :
    ∃ observed, PolynomialPeriodObservation.observe
      ⟨[2, -4, 0, 2, 2, -2]⟩ ⟨side, 0, 0⟩ observationPolicy query count = .ok observed := by
  apply (PolynomialPeriodObservation.observe_success_iff _ _ _ _ _).mpr
  refine ⟨1, ?_, Nat.zero_lt_succ 0, Nat.zero_lt_succ 0⟩
  decide +kernel

/-- Two arbitrary supported policies share that same coefficient-only completeness boundary; no caller supplies either
successful observation. -/
theorem repeated_factor_comparison_exists (side : Side)
    (left right : PeriodPolicies.Policy)
    (query : PeriodPolicies.Request) (count : Nat) :
    ∃ compared, PolynomialPeriodObservation.canonical_period_contract
      ⟨[2, -4, 0, 2, 2, -2]⟩ ⟨side, 0, 0⟩ left right query count = .ok compared := by
  apply (PolynomialPeriodObservation.canonical_period_contract_success_iff _ _ _ _ _ _).mpr
  refine ⟨1, ?_, Nat.zero_lt_succ 0, Nat.zero_lt_succ 0⟩
  decide +kernel

end Test.Riemann.PolynomialPeriodTests
