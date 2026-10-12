module
public import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Approximation.Gaussian.Exponential.Horner.Sample
import Purelib.Approximation.Rational.Geometric.Basic
public import Purelib.Integration.Exponential.Path
import Purelib.Integration.Exponential.Polynomial.Source
import Purelib.Integration.Partition.QuadraticWeight
import Purelib.Integration.Partition.Unit.Basic
import Purelib.Integration.Polynomial.Gaussian.Partition.Segment
import Purelib.Data.Rat.Fraction.Field
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Integration.CertifiedProgram
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic

open Purelib.Integration.Partition.Unit (Normalized)
open Purelib.Integration.Polynomial.Gaussian.Partition.Segment (CompiledSegment)

section
@[expose] public section

/-!
# Observed, cached exponential polynomial cells

Every cell retains its generated affine coefficient restriction and exact
integral sample.  The observations are actual later finite exponential
readings at displayed rational parameters; they are not evidence about an
unspecified integrand.  Endpoint observations make each generated list
nonempty, and the general constructor supports every displayed unit parameter.
-/

namespace Purelib.Integration.Exponential.Cached

open Purelib.Approximation.Rational in
open Purelib.Integration.Exponential in
open Purelib.Integration.Partition in
open Purelib.Integration.Polynomial in
open Purelib.Integration.Program.Gaussian.Cached in
/-- Retain an observed exponential path with its original compiled sample and exact amplified allowance.

The original compiled partition and restrictions are reused; the sample and allowance caches remain linked to this exact
model by their readback equations. -/
def cached {depth : Nat} (compiled :
  CompiledSegment (Polynomial.Source.source depth)) (extraDepth : Nat) :
    Basic.CachedModel :=
  { model := Path.path compiled extraDepth
    sample := compiled.sample
    sample_eq := (Path.path_sample compiled extraDepth).symm
    allowance := QuadraticWeight.amplification compiled.partition * Geometric.Basic.quarterRadius 10 depth
    allowance_eq := (Path.path_allowance compiled extraDepth).symm }

open Purelib.Approximation.Gaussian in
open Purelib.Integration.Exponential in
open Purelib.Integration.Polynomial in
/-- The retained exponential snapshot sample is the original depth-plus-one Horner value at one, minus one. -/
theorem cached_sample {depth : Nat} (compiled :
  CompiledSegment (Polynomial.Source.source depth)) (extraDepth : Nat) :
    (cached compiled extraDepth).sample = Exponential.Horner.Sample.sample 1 (depth + 1) - 1 := by
  change compiled.sample = _
  rw [compiled.sample_source, Polynomial.Source.source_integral]

open Purelib.Integration.Exponential in
open Purelib.Integration.Partition in
open Purelib.Integration.Polynomial in
open Purelib.Integration.Program.Gaussian.Cached in
/-- Compile the supplied partition of the original exponential polynomial and retain its observed model and caches. -/
def compile (depth : Nat) (partition :
  Normalized) (extraDepth :
  Nat) : Basic.CachedModel :=
  cached (CompiledSegment.ofPartition (Polynomial.Source.source depth) partition)
    extraDepth

open Purelib.Approximation.Gaussian in
open Purelib.Integration.Exponential in
open Purelib.Integration.Partition in
/-- The compiled exponential sample is the original depth-plus-one Horner value at one, minus one. -/
theorem compile_sample (depth : Nat) (partition :
  Normalized)
  (extraDepth : Nat) :
    (compile depth partition extraDepth).sample = Exponential.Horner.Sample.sample 1 (depth + 1) - 1 :=
  cached_sample _ extraDepth

open Purelib.Approximation.Rational in
open Purelib.Integration.Exponential in
open Purelib.Integration.Partition in
/-- The compiled allowance is the exact supplied partition amplification times the polynomial-depth quarter radius. -/
theorem compile_allowance (depth : Nat) (partition :
  Normalized)
  (extraDepth : Nat) :
    (compile depth partition extraDepth).allowance = QuadraticWeight.amplification partition *
      Geometric.Basic.quarterRadius 10 depth := rfl

open Purelib.Integration.Exponential in
open Purelib.Integration.Partition in
/-- Every cell in the compiled exponential model retains exactly two observations. -/
theorem compile_observations (depth : Nat) (partition :
  Normalized) (extraDepth : Nat) :
    ∀ model ∈ (compile depth partition extraDepth).model.cells, model.observations.length = 2 :=
  Path.cells_observations extraDepth _ _

end Purelib.Integration.Exponential.Cached

end
