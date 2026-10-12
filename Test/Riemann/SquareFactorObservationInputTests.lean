module

import Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
import Purelib.Integration.Algebraic.SquareFactor.PathInput
public import Purelib.Integration.Algebraic.SquareFactor.ObservationInput
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Squarefree.SquareFactor.Basic
import Purelib.Polynomial.Geometry.PolynomialPathDiagnostics

open Purelib.Curves.Hyperelliptic.Differentials

@[expose] public section

/-!
Kernel regressions of the coefficient-first observation input boundary.
These inspect its typed decisions without forcing the lazy numerical source;
they are not substitutes for an actual nonempty integration observation.
-/

namespace Test.Riemann.SquareFactorObservationInputTests

open Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
open Purelib.Integration.Algebraic.SquareFactor.PathInput (Segment)
open Purelib.Integration.Algebraic.SquareFactor.ObservationInput (Domain)
open Purelib.Integration.Algebraic.SquareFactor

/-- Encode each preparation outcome by its distinct regression tag. -/
public def tag (polynomial : SquareFactor.GaussianPolynomial) (request : SquareFactor.Request) (segment :
  PathInput.Segment) (domain : ObservationInput.Domain) : Nat :=
  match ObservationInput.prepare polynomial request segment 0 domain with
  | .ok _ => 0
  | .error (.zero _) => 1
  | .error (.endpointObstruction _ _ _ (.weightPole ..)) => 2
  | .error (.endpointObstruction _ _ _ (.branchPoint ..)) => 3
  | .error (.inconclusive ..) => 4
  | .error (.originalCoordinateUncertified ..) => 5
  | .error (.originalCoordinateObstruction ..) => 6

/-- The original square-factor integral accepts either orientation of the segment. -/
theorem original_integral_accepts_both_orientations :
    tag ⟨[1, 1, 0, 0]⟩ (.original 0) ⟨2, ⟨9/4, 0⟩⟩ .originalCoordinate = 0 ∧
      tag ⟨[1, 1, 0, 0]⟩ (.original 0) ⟨⟨9/4, 0⟩, 2⟩ .originalCoordinate = 0 := by
  constructor <;> decide +kernel

/-- Cancellation does not silently turn an undefined original-coordinate quotient into an accepted original integral.
Extension is a separate request. -/
theorem cancelled_extension_requires_explicit_selection :
    tag ⟨[1, 1, 0, 0]⟩ (.original 1) ⟨0, ⟨1/4, 0⟩⟩ .originalCoordinate = 6 ∧
      tag ⟨[1, 1, 0, 0]⟩ (.original 1) ⟨0, ⟨1/4, 0⟩⟩ .cancelledExpression = 0 := by
  constructor <;> decide +kernel

/-- A rejected cancellation proposal remains distinct from a certified original pole. -/
theorem failed_proposal_is_not_a_pole_certificate :
    tag ⟨[1, 0, -2]⟩ (.original 0) ⟨-2, 2⟩ .originalCoordinate = 4 ∧
      tag ⟨[1, 1, 0, 0]⟩ (.original 0) ⟨0, ⟨1/4, 0⟩⟩ .cancelledExpression = 2 := by
  constructor <;> decide +kernel

/-- An exact original-coordinate endpoint failure takes precedence over an unresolved interior radicand bound.
Cancellation is still an explicit, different request and does not certify the interior branch clearance. -/
theorem exact_domain_obstruction_precedes_inconclusive_margin :
    tag ⟨[1, 0, -2, 0, 0]⟩ (.original 1) ⟨0, 2⟩ .originalCoordinate = 6 ∧
      tag ⟨[1, 0, -2, 0, 0]⟩ (.original 1) ⟨2, 0⟩ .originalCoordinate = 6 ∧
      tag ⟨[1, 0, -2, 0, 0]⟩ (.original 1) ⟨0, 2⟩ .cancelledExpression = 4 := by
  decide +kernel

/-- Preparation constructs the required quadratic clearance certificate. -/
theorem quadratic_clearance_is_generated :
    tag ⟨[1, 0, 1]⟩ (.original 0) ⟨-2, 2⟩ .originalCoordinate = 0 ∧
      tag ⟨[1, 0, 1]⟩ (.original 0) ⟨2, -2⟩ .originalCoordinate = 0 := by
  constructor <;> decide +kernel

/-- Preparation constructs clearance for the higher-degree and complex examples. -/
theorem higher_degree_and_complex_clearance_are_generated :
    tag ⟨[1, 0, -1, 0, 1]⟩ (.original 0) ⟨-1, 1⟩ .originalCoordinate = 0 ∧
      tag ⟨[⟨1, -1⟩, ⟨0, 1⟩]⟩ (.original 0) ⟨0, 1⟩ .originalCoordinate = 0 := by
  constructor <;> decide +kernel

/-- Better generated enclosures expand acceptance without asking for a manual denominator witness or forcing the
numerical source. -/
theorem wide_original_integral_is_now_accepted :
    tag ⟨[1, 1, 0, 0]⟩ (.original 0) ⟨2, 100⟩ .originalCoordinate = 0 ∧
      tag ⟨[1, 1, 0, 0]⟩ (.original 0) ⟨100, 2⟩ .originalCoordinate = 0 := by
  constructor <;> decide +kernel

/-- Zero and branch obstructions retain their respective typed failure outcomes. -/
theorem zero_and_branch_obstructions_are_typed :
    tag ⟨[0]⟩ (.original 0) ⟨0, 1⟩ .originalCoordinate = 1 ∧
      tag ⟨[1, 1, 0, 0]⟩ (.original 0) ⟨-1, ⟨-3/4, 0⟩⟩ .cancelledExpression = 3 := by
  constructor <;> decide +kernel

end Test.Riemann.SquareFactorObservationInputTests
