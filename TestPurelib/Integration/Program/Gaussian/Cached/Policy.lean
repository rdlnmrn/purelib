module
import Purelib.Examples.Integration.Program.Gaussian.Cached.Policy.WorkedExamples
import Purelib.Integration.Program.Gaussian.Cached.Policy
import Purelib.Integration.Program.Gaussian.Cached.Prefix

import Purelib.Examples.Integration.Program.Gaussian.Cached.Constant.WorkedExamples
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Nat.Schedule.PositiveStride
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Integration.CCL.Program
import Purelib.Integration.CertifiedProgram
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Cached.Allocation

/-! Regression checks for the retained integration program gaussian cached policy contracts. -/

namespace TestPurelib.Integration.Program.Gaussian.Cached.Policy

open Purelib.Examples.Integration.Program.Gaussian.Cached.Policy.WorkedExamples

open Purelib.Integration.Program.Gaussian.Cached

open Purelib.Examples
open Purelib.Integration

/-- The displayed policies allocate five and six source states respectively. -/
theorem allocation_sizes :
    ((left.allocation.compile
      source).count,
      (right.allocation.compile
      source).count) = (5, 6) := by decide

/-- Extending a finite cache preserves each original stored thunk at its retained bounded index. -/
theorem original_thunk_retained
  (program : Program.Gaussian.Cached.Basic.CachedProgram) (count extra index : Nat) (within : index < count) :
    ((Prefix.Cache.canonical program count).extend extra).get index (within.trans_le
      (Nat.le_add_right _ _)) =
      (Prefix.Cache.canonical program count).get index within :=
  (Prefix.Cache.canonical program count).get_extend extra index within

/-- Lookup in an empty cache uses the original source stage. -/
theorem empty_cache_fallback (program
  : Program.Gaussian.Cached.Basic.CachedProgram) (index : Nat) :
    (Prefix.Cache.canonical program 0).lookup index = program.stage index :=
  (Prefix.Cache.canonical program 0).lookup_eq index

/-- The second allocated program reads exactly source stage `2 + 2 * index`. -/
theorem allocated_source_owner (index
  : Nat) :
    (right.program
      source).stage index =
      source.stage (2 + 2 * index) :=
      right.stage_eq
      source index

end TestPurelib.Integration.Program.Gaussian.Cached.Policy
