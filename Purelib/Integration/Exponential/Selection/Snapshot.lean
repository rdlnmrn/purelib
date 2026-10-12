module
import Purelib.Approximation.Gaussian.Exponential.Horner.Sample
import Purelib.Approximation.Rational.Geometric.Basic
public import Purelib.Integration.Exponential.Path
import Purelib.Integration.Exponential.Polynomial.Source
public import Purelib.Integration.Exponential.Selection
import Purelib.Integration.Polynomial.Gaussian.Partition.Segment
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Integration.CertifiedProgram
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Partition.QuadraticWeight.Cache
import Purelib.Data.Rat.Fraction
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

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

namespace Purelib.Integration.Exponential.Selection

open Purelib in
open Purelib.Approximation.Rational in
open Purelib.Integration.Exponential in
open Purelib.Integration.Polynomial in
open Purelib.Integration.Program.Gaussian.Cached in
/-- Compile the selected exponential geometry and retain its observed model, exact sample and amplified allowance.

The selected partition and polynomial depth remain fixed; the extra depth changes endpoint observations while both cache
equalities certify their model readbacks. -/
def snapshot {stage : Nat} (selected :
  Selection stage) (extraDepth : Nat) : Basic.CachedModel :=
  let compiled := Gaussian.Partition.Segment.CompiledSegment.ofPartition
    (Polynomial.Source.source selected.depth) selected.geometry.partition
  { model := Path.path compiled extraDepth
    sample := compiled.sample
    sample_eq := (Path.path_sample compiled extraDepth).symm
    allowance := selected.geometry.factor * Geometric.Basic.quarterRadius 10 selected.depth
    allowance_eq := by
      change selected.geometry.factor * Geometric.Basic.quarterRadius 10 selected.depth =
        (Path.path compiled extraDepth).aggregateAllowance
      rw [Path.path_allowance, selected.geometry.factor_eq]
      rfl }

open Purelib in
open Purelib.Approximation.Gaussian in
open Purelib.Integration.Exponential in
open Purelib.Integration.Polynomial in
/-- The retained snapshot sample is the Horner sample at selected depth plus one, minus one. -/
theorem snapshot_sample {stage : Nat} (selected :
  Selection stage) (extraDepth : Nat) :
    (selected.snapshot extraDepth).sample = Exponential.Horner.Sample.sample 1 (selected.depth + 1) - 1 := by
  change (Gaussian.Partition.Segment.CompiledSegment.ofPartition
    (Polynomial.Source.source selected.depth) selected.geometry.partition).sample = _
  rw [Gaussian.Partition.Segment.CompiledSegment.sample_source, Polynomial.Source.source_integral]

open Purelib in
open Purelib.Approximation.Rational in
/-- The retained snapshot allowance is strictly below the original selection stage's quarter-radius target. -/
theorem snapshot_allowance {stage : Nat} (selected :
  Selection stage) (extraDepth : Nat) :
    (selected.snapshot extraDepth).allowance < Geometric.Basic.quarterRadius 10 stage := selected.allowance_small
end Purelib.Integration.Exponential.Selection

end
