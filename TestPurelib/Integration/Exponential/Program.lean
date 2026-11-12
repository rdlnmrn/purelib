module
import Purelib.Examples.Integration.Exponential.CCL.Replay.WorkedExamples
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Exponential.Taylor.Integral.Bounds
import Purelib.Data.CCL.Transducer.Initial.Observation
import Purelib.Data.CCL.Transducer.Machine.Advance
import Purelib.Integration.CertifiedProgram
import Purelib.Integration.Exponential.Program
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Record
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Replay
import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Examples.Integration.Exponential.Program.WorkedExamples
import Purelib.Approximation.Gaussian.Name.CCL.Output
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.CCL.Program
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Basic
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Nat.Schedule.PositiveStride
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Integration.Exponential.Cached
import Purelib.Integration.Exponential.Equivalence.Policy
import Purelib.Integration.Exponential.Geometry.Policy
import Purelib.Integration.Exponential.Selection
import Purelib.Integration.Partition.QuadraticWeight

import Purelib.Data.Rat.Fraction.Order
import Purelib.Integration.Exponential.Equivalence.Existing
import Purelib.Integration.Exponential.Equivalence.Reference
import Purelib.Integration.Exponential.Uniform
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Sequence
import Purelib.CCL.Progressive.IntegrationPrograms
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Integration.Exponential.Polynomial.Source
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Integration.Polynomial.Gaussian.Segment.Basic

open Purelib.Integration.Exponential.Geometry

/-! Regression checks for the retained integration exponential program contracts. -/

namespace TestPurelib.Integration.Exponential.Program

open Purelib.Examples.Integration.Exponential.Program.WorkedExamples

open Purelib.Data.Nat.Schedule (PositiveStride)

open Purelib.Integration
open Purelib.Approximation
open Purelib.Data
open Purelib
open Purelib.Data.Rat
open Purelib.Examples

/-- The first two reference subtraction samples use source indices three and four. -/
theorem existing_subtraction_sampler_indices :
    [Exponential.Equivalence.Reference.referenceSourceIndex 0,
      Exponential.Equivalence.Reference.referenceSourceIndex 1] = [3, 4] := by decide +kernel

end TestPurelib.Integration.Exponential.Program

namespace TestPurelib.Integration.Exponential.Program.Replay

open Purelib.Examples.Integration.Exponential.CCL.Replay.WorkedExamples

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Examples.Integration.Exponential
open Purelib.Integration.Program.Gaussian.CCL.Replay.Observation

open Purelib.CCL
open Purelib
open Purelib.Examples
open Purelib.Integration

/-- The exponential observation's first bit is true.

The retained sample's norm lower bound determines the initial transducer decision. -/
theorem actual_first_bit :
  recorded.observation.word = [true] := open Purelib.Approximation in
  open Purelib.Data in open Purelib.Data.Rat in by
  rw [recorded,
    Record.recorded_prefix]
  apply Data.CCL.Transducer.Initial.Observation.advance_one_large
  change (13 / 6 : Rational) < Data.Gaussian.Norm.Basic.normSq
    (Program.WorkedExamples.fixedProgram.approximation.sample _)
  rw [Program.WorkedExamples.fixedProgram, Exponential.Program.program_sample]
  exact (show (13 / 6 : Rational) < 9 / 4 from by decide).trans_le
    (Gaussian.Exponential.Taylor.Integral.Bounds.integral_norm_lower _)

end TestPurelib.Integration.Exponential.Program.Replay
