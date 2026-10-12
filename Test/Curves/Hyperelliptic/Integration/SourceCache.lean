module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Examples.Curves.Legendre.LoopBaseBranches

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Init.Prelude
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore

open Purelib.Curves

open Purelib.Curves.Hyperelliptic

open Purelib.Data.Rat

open Purelib.Examples.Curves.Legendre

section
@[expose] public section

/-!
# Certificate-free source-state cache regressions

Two stationary sheet switches exercise the actual source-only recurrence,
cache hits, misses and chunked extension without any root isolation or
generated coefficient bank.  These are cache/ownership regressions, not
substitutes for the nonstationary Legendre period acceptance tests.
-/

namespace Test.Curves.Hyperelliptic.Integration.SourceCache

open Purelib.Riemann.Curves.AlgebraicDifferentials
open Purelib.Riemann.Integration.PreparedSwitchedRefinements
open DirectSwitchedState

variable {genus : Nat}

/-- A source state with two stationary sheet switches and no geometric parent cells.

Its retained chain switches sheets at the same point twice, and every requested differential has zero initial allowance.
-/
def stationaryState (curve :
  Hyperelliptic.Basic.HyperellipticCurve genus) (source : Differentials.Basic.Differential genus) :
    DirectSwitchedState curve source where
  start := ⟨0, 0⟩
  finish := ⟨0, 0⟩
  parents := []
  proper := True.intro
  chain := .stationary 0 0 (.stationary 0 1 (.nil ⟨0, 0⟩))
  initialAllowanceBound := fun _ => 0
  initialAllowance_le := by
    intro target
    change (0 : Fraction.Rational) * 0 ≤ 0
    rw [Fraction.Field.mul_zero_direct]

open Test.Curves.Hyperelliptic.Integration.SourceCache (stationaryState)

/-- Cache the canonical source recurrence of the stationary two-switch state through the requested finite prefix. -/
def cache (curve : Hyperelliptic.Basic.HyperellipticCurve
  genus) (source : Differentials.Basic.Differential genus) (count : Nat) :=
  SourceCache.canonical (⟨fun _ => stationaryState curve source⟩ : Thunk _) count

/-- Read the cached parent count, switch count, model-cell count, integral and aggregate allowance at the requested
stage. -/
def profile {curve : Hyperelliptic.Basic.HyperellipticCurve
  genus} {source : Differentials.Basic.Differential genus}
    (retained : SourceCache curve source) (index : Nat) :=
  let state := retained.state index
  let model := retained.model index
  (state.parents.length, state.chain.switchCount, model.cells.length,
    model.integralSample, model.aggregateAllowance)

/-- The exact retained genus-one curve of the branch-loop regression. -/
abbrev testCurve := LoopBaseBranches.baseCurve

/-- The zero polynomial differential on the retained genus-one test curve. -/
def testSource : Differentials.Basic.Differential 1 := ⟨0⟩

/-- The first cached stage retains two switches and two zero-valued model cells with no geometric parents. -/
theorem initial_profile :
    profile (cache
      testCurve
      testSource 1) 0 = (0, 2, 2, 0, 0) := by decide +kernel

/-- Empty allocation uses the original total source recurrence. -/
theorem empty_fallback :
    profile (cache
      testCurve
      testSource 0) 2 = (0, 2, 2, 0, 0) := by decide +kernel

/-- A retained successor stage has the same exact stationary two-switch profile. -/
theorem cached_successor :
    profile (cache
      testCurve
      testSource 4) 3 = (0, 2, 2, 0, 0) := by decide +kernel

/-- Requesting beyond the cached prefix preserves the exact stationary recurrence profile. -/
theorem beyond_prefix :
    profile (cache
      testCurve
      testSource 2) 3 = (0, 2, 2, 0, 0) := by decide +kernel

/-- Extending the original cache in two chunks retains the same exact stationary successor profile. -/
theorem chunked_successor :
    profile (((cache
      testCurve
      testSource 0).extend 1).extend 3) 3 = (0, 2, 2, 0, 0) := by
      decide +kernel
end Test.Curves.Hyperelliptic.Integration.SourceCache

end
