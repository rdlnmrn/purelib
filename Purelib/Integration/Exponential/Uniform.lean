module
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Integration.Exponential.Cached
public import Purelib.Integration.Exponential.Geometry.Policy
import Purelib.Integration.Partition.QuadraticWeight
import Purelib.Integration.Partition.Unit.Basic

import Purelib.CCL.Progressive.IntegrationPrograms
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Partition.Uniform.QuadraticWeight
import Purelib.Integration.Polynomial.Gaussian.Segment.Basic
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Integration.CertifiedProgram
import Purelib.Integration.Exponential.Polynomial.Source
import Purelib.Data.Rat.Fraction
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

public section

/-!
# Exact allowance amplification of every finite uniform partition

This theorem concerns the existing `uniformCuts` constructor and its actual
normalization and interval generation, not a hypothesis that the supplied
intervals happen to have equal widths.  Arbitrary positive cell counts are
covered; all arithmetic is on the finite rational grid.
-/

namespace Purelib.Integration.Exponential.Uniform

open Purelib.Integration.Exponential in
open Purelib.Integration.Partition in
/-- Every retained stage of the original uniform partition policy has quadratic amplification exactly one. -/
theorem uniform_policy_amplification (initialExtra growth stage : Nat) :
    QuadraticWeight.amplification (Geometry.Policy.partitions (.uniform initialExtra growth) stage) = 1 :=
  Uniform.QuadraticWeight.uniform_amplification (initialExtra + growth * stage)

open Purelib.Approximation.Rational in
open Purelib.CCL.Progressive in
open Purelib.Data.Rat in
open Purelib.Integration.Exponential in
open Purelib.Integration.Partition in
/-- A uniformly partitioned exponential compilation has allowance exactly its original polynomial-depth quarter radius.
-/
theorem uniform_compiled_allowance (depth extra extraDepth : Nat) :
    (Cached.compile depth
      (Partition.Unit.Normalized.ofRequest (IntegrationPrograms.uniformCuts extra)) extraDepth).allowance =
        Geometric.Basic.quarterRadius 10 depth := by
  rw [Cached.compile_allowance, Uniform.QuadraticWeight.uniform_amplification,
    Fraction.Field.one_mul]

end Purelib.Integration.Exponential.Uniform
