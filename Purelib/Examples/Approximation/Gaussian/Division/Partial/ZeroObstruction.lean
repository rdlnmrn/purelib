module
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Division.Partial.Run
import Purelib.Approximation.Gaussian.Division.Partial.ZeroObstruction
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Inspection
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
public import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Zero
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Process.Coherence.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic

@[expose] public section

/-!
# Zero obstruction with permanently positive enclosure radii

Every finite candidate is exactly zero, but no displayed ball has radius
zero. The symbolic invariant, not a zero-width numerical observation,
certifies that every finite division attempt remains unready.
-/

namespace Purelib.Examples.Approximation.Gaussian.Division.Partial.ZeroObstruction

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)

open Purelib.Approximation.Rational
open Purelib.Data.Rat
open Purelib.Examples
open Purelib.Approximation.Gaussian.Process
open Purelib.Data.Gaussian
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Coherent.Refinement
open Purelib.Approximation.Gaussian.Division

/-- The positive quarter-geometric squared-radius schedule starting from one. -/
def radius (index : Nat) :
  Rational := Geometric.Basic.quarterRadius 1 index

/-- Every finite radius in the padded-zero schedule is positive. -/
theorem radius_positive (index : Nat) :
  0 < radius index :=
  Geometric.Basic.quarterRadius_pos (by decide) index

/-- A Gaussian zero process whose certified balls remain nonexact.

Retains the natural-number refinement index and searches the quarter-geometric schedule for the requested accuracy; zero
is its only possible value. -/
def paddedZeroProcess :
    Approximation.Gaussian.Process
  where
  State := Nat
  ball index :=
    { center := 0
      radiusSq := radius index
      radiusSq_nonneg := (radius_positive index).le }
  Possible _ value := value = 0
  witness _ := ⟨0, rfl⟩
  possible_inside := by
    intro index value equal
    subst value
    change Norm.Basic.normSq (0 - 0) ≤ radius
      index
    simpa only [Basic.sub_self,
      Norm.Basic.normSq_zero] using (radius_positive index).le
  refine index target _ := Geometric.Search.firstQuarterBelow 1 index target
  refine_persists := by intro index target positive value possible; exact possible
  accurate index target positive :=
    Geometric.Search.firstQuarterBelow_accurate 1 (by decide) index target positive
  centerBound := 0
  centerBound_nonneg := le_rfl
  center_bounded := by
    intro index
    change Norm.Basic.normSq (0 : Basic.Canonical) ≤ (0 : Rational)
    decide

/-- Coherence data for the padded-zero process.

Uses the same positive quarter-radius allowance at each retained index and the original finite geometric search. -/
def paddedZeroCoherent :
  Coherence.Basic.Coherent paddedZeroProcess where
  allowance := radius
  allowance_nonneg index := (radius_positive index).le
  ball_radius_le _ := le_rfl
  possible_close := by
    intro left right leftValue rightValue leftZero rightZero
    subst leftValue
    subst rightValue
    rw [Basic.sub_self,
      Norm.Basic.normSq_zero]
    exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg (radius_positive left).le
        (radius_positive right).le)
  accuracyRequest target := target
  accuracyRequest_pos positive := positive
  refine_accurate := by
    intro index target positive request requestPositive small
    exact (Geometric.Search.firstQuarterBelow_accurate 1 (by decide) index
      request requestPositive).trans small

/-- The padded-zero coherent name at its initial index. -/
def paddedZero : CoherentNamed
  where
  name := { process := paddedZeroProcess, state := (0 : Nat) }
  coherent := paddedZeroCoherent

/-- Every possible value of a retained padded-zero state is zero. -/
theorem zero_candidates (state :
  Refinement.State
      paddedZero) : Zero.ZeroCandidates
  paddedZero state :=
  fun possible => possible

/-- Every retained padded-zero ball has strictly positive squared radius. -/
theorem balls_never_exact (state :
  Refinement.State
      paddedZero) :
    0 < (paddedZero.name.process.ball state.source).radiusSq :=
      radius_positive state.source

/-- Every finite division attempt against padded zero exhausts its budget.

Returns the actual final state and its reachability witness, using the original zero-candidate obstruction. -/
theorem all_budgets_exhaust (numerator :
  CoherentNamed) (state : Refinement.State
      paddedZero) (fuel
  : Nat) :
    ∃ final reachable, Partial.Run.attempt numerator paddedZero
      state fuel = .exhausted final reachable :=
  Partial.ZeroObstruction.ZeroCandidates.attempt_exhausts numerator state
    (zero_candidates state) fuel

/-- Requested refinement preserves the padded denominator's zero candidates. -/
theorem requested_preserves_zero (state
  : Refinement.State
      paddedZero) (target : Rational)
  (positive : 0 < target) :
    Zero.ZeroCandidates paddedZero
      (Inspection.request state target positive).retained :=
  Zero.ZeroCandidates.requested (zero_candidates state) _

end Purelib.Examples.Approximation.Gaussian.Division.Partial.ZeroObstruction

end
