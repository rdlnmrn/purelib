module
import Purelib.Examples.Integration.Program.Gaussian.Query.Chart.WorkedExamples
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Sequence.Process
import Purelib.Approximation.Gaussian.Process.Recipe.Request
import Purelib.Approximation.Gaussian.Process.Recipe.Basic
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Enclosure.Ball.Data
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Approximation.Gaussian.Process.Apart.Preparation
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Process.Division
import Purelib.Approximation.Gaussian.Process.Multiplication
import Purelib.Approximation.Gaussian.Process.Translation
import Purelib.Examples.Integration.Polynomial.Gaussian.Transport.WorkedExamples
import Purelib.Integration.Program.Gaussian.Query.Recipe
import Purelib.Integration.Program.Gaussian.Query.Representation
import Purelib.Computation.Query.Basic
import Purelib.Computation.Query.Computation

import Purelib.CCL.Progressive.IntegrationQueries
import Mathlib.Algebra.Ring.Defs
import Purelib.Computation.Query.Replay
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.CertifiedProgram
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic

/-! Regression checks for the retained integration program gaussian query chart contracts. -/

namespace TestPurelib.Integration.Program.Gaussian.Query.Chart

open Purelib.Examples.Integration.Program.Gaussian.Query.Chart.WorkedExamples

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Approximation.Gaussian (Process)
open Purelib.Examples.Integration.Polynomial.Gaussian

open Purelib.Approximation
open Purelib.CCL
open Purelib
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Examples
open Purelib.Integration

/-- The observation records exactly one source request, at index seven. -/
theorem observed_source_queries :
    (observed.run
      program.stage).trace.map
      Computation.Query.Basic.Exchange.query = [7] := by
  rw [observed,
      Process.Recipe.ball_trace]
  rfl

/-- An empty observation trace is rejected as missing index seven. -/
theorem replay_missing : observed.replayExact [] = .error
  (.missing 7) := by decide +kernel

/-- A reply tagged with index eight is rejected when index seven is requested. -/
theorem replay_mismatched :
    observed.replayExact [⟨8,
      program.stage 7⟩] = .error (.mismatch 7 8 (by decide)) :=
      by decide +kernel

end TestPurelib.Integration.Program.Gaussian.Query.Chart
