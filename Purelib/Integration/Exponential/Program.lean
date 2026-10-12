module
public import Purelib.Integration.Program.Gaussian.Cached.Prefix.Program
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Exponential.Horner.Sample
import Purelib.Approximation.Gaussian.Exponential.Taylor.Integral
import Purelib.Approximation.Gaussian.Exponential.Taylor.Integral.Bounds
import Purelib.Data.Nat.Schedule.PositiveStride
import Purelib.Integration.Exponential.Path
import Purelib.Integration.Exponential.Selection
public import Purelib.Integration.Exponential.Selection.Cache
public import Purelib.Integration.Exponential.Selection.Snapshot
import Purelib.Integration.Exponential.Geometry.Policy
import Purelib.Integration.Program.Gaussian.Cached.Prefix
import Purelib.Integration.CertifiedProgram
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Gaussian.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Nat.Schedule (PositiveStride)
open Purelib.Integration.Exponential.Geometry (Policy)

open Purelib.Integration.Exponential (Selection)

open Purelib.Integration

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_antitone)

public section

/-!
# Automatically deepened finite exponential integration

The existing finite partition-policy syntax specifies geometry on one unit
segment.  Its polynomial is replaced at each selected degree.  Geometry and
its actual amplification are cached before degree selection, and each output
stage retains its compiled polynomial model, sample and allowance.

The previous selected depth, the positive-stride request and the current
geometric allowance all constrain the next selection.  No bound on partition
growth, analytic antiderivative or caller coherence proof is required.
-/

namespace Purelib.Integration.Exponential.Program

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Rational
open Purelib.Data.Nat
open Purelib.Data.Rat
open Purelib.Integration.Exponential
open Purelib.Integration.Exponential.Selection
open Purelib.Integration.Polynomial
open Purelib.Integration.Program.Gaussian
open Purelib.Integration.Program.Gaussian.Cached

/-- Subtracting two Horner samples shifted by one cancels their common shift.

The same scalar shift occurs in both finite samples. Direct Gaussian arithmetic
retains their original sample indices while cancelling that common term. -/
theorem shifted_samples_cancel (left right : Nat) :
    Exponential.Horner.Sample.sample 1 left - 1 - (Exponential.Horner.Sample.sample 1 right - 1) =
      Exponential.Horner.Sample.sample 1 left - Exponential.Horner.Sample.sample 1 right := by ring1

/-- Build a certified exponential program using the retained selection-cache entries for its stage snapshots.

The program keeps geometric error scale ten and center bound 22, preserving each original policy, schedule and extra
observation depth. -/
@[expose] def selectedProgram (policy : Policy) (schedule :
  PositiveStride) (extraDepth : Nat)
    (entries : List (Cache.SelectionCache.Entry policy schedule)) : Cached.Basic.CachedProgram where
  stage index := (Cache.SelectionCache.read policy schedule index entries).snapshot extraDepth
  errorScale := 10
  errorScale_nonneg := by decide
  modelAllowance_le := fun index => (Selection.snapshot_allowance _ extraDepth).le
  later_close := by
    intro earlier later order
    simp only [Cache.SelectionCache.read_eq]
    rw [Selection.snapshot_sample, Selection.snapshot_sample, shifted_samples_cancel]
    exact (Exponential.Horner.Sample.sample_later_close 1 (by decide)
      (Nat.add_le_add_right (Integration.Exponential.Selection.selection_monotone policy schedule order) 1)).trans
        (quarterRadius_antitone (by decide : (0 : Fraction.Rational) ≤ 10)
          ((Integration.Exponential.Selection.selection policy schedule earlier).stage_le_depth.trans (Nat.le_succ _)))
  centerBound := 22
  centerBound_nonneg := by decide
  sample_bounded := by
    intro index
    simp only [Cache.SelectionCache.read_eq]
    rw [Selection.snapshot_sample, ← Exponential.Taylor.Integral.integral_polynomial]
    exact Exponential.Taylor.Integral.Bounds.integral_bounded _

/-- The selected program's stage is the snapshot of its exact original canonical selection.

The stage reads the retained selection cache at the same index. Its exact lookup certificate transports that cached
value to canonical selection. -/
private theorem selectedProgram_stage (policy : Policy)
  (schedule : PositiveStride)
    (extraDepth : Nat) (entries : List (Cache.SelectionCache.Entry policy schedule)) (index : Nat) :
    (selectedProgram policy schedule extraDepth entries).stage index =
      (Integration.Exponential.Selection.selection policy schedule index).snapshot extraDepth :=
  congrArg (fun selected : Selection index => selected.snapshot extraDepth)
    (Cache.SelectionCache.read_eq policy schedule index entries)

/-- Build an exponential integration program with retained prefixes of 64 selection entries and 64 model snapshots.

The lazy selection chain reuses previous retained depths; subsequent stage queries use the retained model cache with its
canonical fallback. -/
@[expose] def program (policy : Policy) (schedule :
  PositiveStride) (extraDepth : Nat) : Cached.Basic.CachedProgram :=
  let selections := Cache.SelectionCache.buildPrefix 64 (Cache.SelectionCache.first policy schedule)
  let source := selectedProgram policy schedule extraDepth selections
  (Prefix.Cache.program (Prefix.Cache.canonical source 64))

/-- Each cached program stage equals the exact original canonical selection snapshot.

The original selection prefix and model prefix retain the same canonical stage. Lookup transport preserves both cache
owners and the supplied stage index. -/
theorem program_stage (policy : Policy) (schedule :
  PositiveStride) (extraDepth index : Nat) :
    (program policy schedule extraDepth).stage index =
      (Integration.Exponential.Selection.selection policy schedule index).snapshot extraDepth := by
  let selections := Cache.SelectionCache.buildPrefix 64 (Cache.SelectionCache.first policy schedule)
  exact (Prefix.Cache.lookup_eq
    (Prefix.Cache.canonical (selectedProgram policy schedule extraDepth selections) 64) index).trans
      (selectedProgram_stage policy schedule extraDepth selections index)

/-- The program approximation reads the selected Horner sample at depth plus one, minus one.

The cached stage is the snapshot of the retained selection. Its sample readback uses that same selected source depth and
finite Horner table. -/
theorem program_sample (policy : Policy) (schedule :
  PositiveStride) (extraDepth index : Nat) :
    (program policy schedule extraDepth).approximation.sample index =
      Exponential.Horner.Sample.sample 1 ((Integration.Exponential.Selection.selection policy schedule index).depth + 1)
        - 1 := by
  change ((program policy schedule extraDepth).stage index).sample = _
  rw [program_stage]
  exact Selection.snapshot_sample _ extraDepth

/-- Every model cell in an exponential program stage retains exactly two observations.

Each cached stage retains the ordered observed polynomial cells. Their original endpoint observation pair remains
attached to the same interval and restriction. -/
theorem program_observations (policy : Policy) (schedule :
  PositiveStride) (extraDepth index : Nat) :
    ∀ model ∈ ((program policy schedule extraDepth).stage index).model.cells,
      model.observations.length = 2 := by
  rw [program_stage]
  exact Path.cells_observations extraDepth _ _
end Purelib.Integration.Exponential.Program
end
