module
import Purelib.Data.Rat.Fraction
public import Purelib.CCL.Progressive.IntegrationPrograms
import Purelib.Integration.Partition.Unit.Basic
import Purelib.Data.Gaussian.Basic
public import Purelib.Integration.Exponential.Polynomial.Source
import Purelib.Integration.Polynomial.Gaussian.Segment.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Integration.Polynomial.Gaussian.Partition.Source
import Purelib.Data.Nat.Factorial.Basic
import Purelib.Integration.Polynomial.Gaussian.Partition.Request
import Purelib.Polynomial.Ascending.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Cast

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

namespace Purelib.Integration.Exponential.Geometry

/-- The finite partition-policy syntax for the singleton depth-zero exponential polynomial source. -/
abbrev Policy :=
  Purelib.CCL.Progressive.IntegrationPrograms.PartitionPolicy
    [Purelib.Integration.Exponential.Polynomial.Source.source 0]

namespace Policy

open Purelib.Data.Rat in
open Purelib.Integration.Polynomial in
/-- Construct the exact singleton-source fixed partition policy from the supplied cut request. -/
def fixedCuts (cuts : List Fraction.Rational) :
  Exponential.Geometry.Policy := .fixed (.cons cuts .nil)

open Purelib in
open Purelib.Integration.Partition in
open Purelib.Integration.Polynomial in
/-- Read the unit partition selected by a retained policy at the supplied stage.

Fixed cuts are normalized once, uniform policies compute their retained linear stage count, and alternating policies
select the original left or right policy by stage parity. -/
def partitions :
  Exponential.Geometry.Policy → Nat → Integration.Partition.Unit.Normalized
  | .fixed (.cons cuts .nil) =>
      let partition := Integration.Partition.Unit.Normalized.ofRequest cuts
      fun _ => partition
  | .uniform initialExtra growth => fun stage =>
      Integration.Partition.Unit.Normalized.ofRequest
        (CCL.Progressive.IntegrationPrograms.uniformCuts (initialExtra + growth * stage))
  | .alternating left right =>
      let leftPartitions := Purelib.Integration.Exponential.Geometry.Policy.partitions left
      let rightPartitions := Purelib.Integration.Exponential.Geometry.Policy.partitions right
      fun stage => if stage % 2 = 0 then leftPartitions stage else rightPartitions stage
end Policy
end Purelib.Integration.Exponential.Geometry

end
