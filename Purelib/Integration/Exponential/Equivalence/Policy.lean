module
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Exponential.Horner.Sequence
import Purelib.Data.Nat.Schedule.PositiveStride
public import Purelib.Integration.Exponential.Program
import Purelib.Integration.Exponential.Selection
import Purelib.Integration.Exponential.Geometry.Policy
import Purelib.Integration.CCL.Program
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Data.Gaussian.Basic
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Equivalence.Sampling
import Purelib.Integration.CertifiedProgram
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

open Purelib.Integration

section
@[expose] public section

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

namespace Purelib.Integration.Exponential.Equivalence.Policy

open Purelib in
open Purelib.Approximation.Gaussian in
open Purelib.Data.Nat in
open Purelib.Integration.Exponential in
open Purelib.Integration.Polynomial in
/-- Compare exponential programs with separate original partition policies, schedules and observation depths.

The finite comparison retains both requested starting indices and certifies all later samples using their exact
selected-depth floors. -/
def programs_equivalent (left right :
  Exponential.Geometry.Policy) (leftSchedule rightSchedule :
  Data.Nat.Schedule.PositiveStride)
    (leftExtra rightExtra : Nat) : Equivalence.Equivalent
      (Program.program left leftSchedule leftExtra).approximation
      (Program.program right rightSchedule rightExtra).approximation where
  compare := by
    intro leftStart rightStart target positive
    let comparison := (Equivalence.Equivalent.refl
      (Exponential.Horner.Sequence.approximation 1 (by decide))).compare leftStart rightStart target positive
    exact
      { leftIndex := comparison.leftIndex
        rightIndex := comparison.rightIndex
        left_ge := comparison.left_ge
        right_ge := comparison.right_ge
        close := by
          intro leftLater rightLater leftOrder rightOrder
          rw [Program.program_sample, Program.program_sample, Program.shifted_samples_cancel]
          exact comparison.close
            (leftOrder.trans ((Integration.Exponential.Selection.selection left leftSchedule
              leftLater).stage_le_depth.trans (Nat.le_succ _)))
            (rightOrder.trans ((Integration.Exponential.Selection.selection right rightSchedule
              rightLater).stage_le_depth.trans (Nat.le_succ _))) }

open Purelib.Approximation.Gaussian in
open Purelib.Data.Nat in
open Purelib.Integration.Exponential in
open Purelib.Integration.Polynomial in
/-- The coherent outputs of the two original policy-controlled exponential programs are equivalent. -/
def outputs_equivalent (left right :
  Exponential.Geometry.Policy) (leftSchedule rightSchedule :
  Data.Nat.Schedule.PositiveStride)
    (leftExtra rightExtra : Nat) : Equivalence.NamedEquivalent
      (Program.program left leftSchedule leftExtra).output.name
      (Program.program right rightSchedule rightExtra).output.name :=
  (programs_equivalent left right leftSchedule rightSchedule leftExtra rightExtra).toNamed

end Purelib.Integration.Exponential.Equivalence.Policy

end
