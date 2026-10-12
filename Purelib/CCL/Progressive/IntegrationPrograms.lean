module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Equivalence.Sampling
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Integration.Polynomial.Gaussian.Partition.Compiled
import Purelib.Integration.Polynomial.Gaussian.Partition.Request
import Purelib.Integration.Polynomial.Gaussian.Partition.Source
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic
public import Purelib.Integration.Program.Gaussian.Exact
import Purelib.Polynomial.Ascending.Gaussian.Basic
import Purelib.Polynomial.Ascending.Gaussian.Integral
public import Purelib.Integration.Program.Gaussian.Name
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Integration.CCL.Program
import Purelib.Tactic.Ring

public section

/-!
# Cached generated integration programs

The numerical path reads retained samples and aggregate allowances; its
semantic projection is an ordinary Gaussian `RefinementProgram` on the actual
stored polynomial cells.  Cache equalities are finite computational
certificates, not independent analytic or comparison assumptions.

The generic cached program still carries the usual coherence hypotheses.
The public polynomial constructor below derives all of them from its shared
finite source, and takes only a finite partition-policy description.
-/

namespace Purelib.CCL.Progressive.IntegrationPrograms

open Purelib.Data.Rat in
/-- The canonical rational scalar type. -/
abbrev Coordinate := Fraction.Rational
open Purelib in
/-- The canonical Gaussian rational type. -/
abbrev Gaussian := Data.Gaussian.Basic.Canonical
open Purelib.Integration.Polynomial.Gaussian in
/-- A retained finite polynomial path model. -/
abbrev PathModel := Path.Basic.PathModel
open Purelib in
/-- A Gaussian integration refinement program. -/
abbrev RefinementProgram := Integration.Program.Gaussian.Basic.RefinementProgram
section
open Purelib.Approximation.Gaussian
/-- Gaussian approximation data indexed by finite stages. -/
abbrev Approximation := Sequence.ApproximationData
/-- A Gaussian name with retained coherence evidence. -/
abbrev CoherentNamed := Name.Coherent.CoherentNamed

end

open Purelib.Integration.Program.Gaussian.Cached.Basic (CachedModel CachedProgram)

open Purelib.Data.Gaussian.Basic.Canonical

namespace CachedModel

open Purelib.Integration.Polynomial.Gaussian in
open Purelib.Integration.Program.Gaussian in
/-- Retain a compiled partition's model, sample and zero allowance.

The cache uses the compiled sample itself. Its stored equalities identify that sample with the model integral and the
model allowance with zero. -/
@[expose] def ofPartition {source : Partition.Source.PolynomialPath} (compiled : Partition.Compiled.CompiledPartition
  source) : Cached.Basic.CachedModel :=
  { model := compiled.model
    sample := compiled.sample
    sample_eq := compiled.sample_model
    allowance := 0
    allowance_eq := compiled.allowance_zero.symm }

end CachedModel

open Purelib.Integration.Polynomial.Gaussian in
set_option genInjectivity false in
/-- Finite syntax for selecting polynomial partitions at each stage.

A fixed request, uniform count progression or parity-based alternation determines the compiled partition of the same
retained source. Uniform partitions always have at least one cell. -/
inductive PartitionPolicy (source : Partition.Source.PolynomialPath) where
  /-- Reuse one supplied cut request at every stage. -/ | fixed (request : Partition.Request.CutRequest source)
  /-- Use initialExtra + growth × stage interior uniform cuts. -/ | uniform (initialExtra growth : Nat)
  /-- Select the left policy at even stages and the right policy at odd stages. -/ | alternating (left right :
    PartitionPolicy source)

constructive_injectivity PartitionPolicy

open Purelib.Data.Rat in
/-- Construct the interior cuts of a uniform partition into extra + 1 cells.

The finite list contains (index + 1)/(extra + 1) for indices below extra, in increasing order; extra zero gives no
interior cuts. -/
@[expose] def uniformCuts (extra : Nat) : List Fraction.Rational :=
  (List.range extra).map fun index => ((index + 1 : Nat) : Fraction.Rational) / ((extra + 1 : Nat) : Fraction.Rational)

open Purelib.Integration.Polynomial.Gaussian in
/-- Compile a finite partition policy into stage-indexed retained partitions.

Fixed requests compile once outside the stage function. Uniform requests use the displayed count at each stage, while
alternating policies retain both compiled branches and select by parity. -/
@[expose] def compilePolicy {source : Partition.Source.PolynomialPath} : PartitionPolicy source → Nat →
  Partition.Compiled.CompiledPartition source
  | .fixed request =>
      let compiled := Partition.Compiled.compilePartition source request
      fun _ => compiled
  | .uniform initialExtra growth => fun index =>
      Partition.Compiled.compilePartition source (Partition.Request.CutRequest.every (uniformCuts (initialExtra + growth
        * index)) source)
  | .alternating left right =>
      let leftCompiled := compilePolicy left
      let rightCompiled := compilePolicy right
      fun index => if index % 2 = 0 then leftCompiled index else rightCompiled index

open Purelib.Integration.Polynomial.Gaussian in
open Purelib.Integration.Program.Gaussian in
open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib in
/-- Build a cached integration program from a polynomial source and partition policy.

Every stage retains its compiled model and exact source sample, with zero allowance. Coherence follows from equality of
those samples, and the squared norm of the source sample supplies the center bound. -/
@[expose] def polynomialProgram (source : Partition.Source.PolynomialPath) (policy : PartitionPolicy source) :
  Cached.Basic.CachedProgram :=
  let compiled := compilePolicy policy
  let integral := Partition.Source.sourceSample source
  { stage := fun index => CachedModel.ofPartition (compiled index)
    errorScale := 0
    errorScale_nonneg := le_rfl
    modelAllowance_le := by
      intro index
      change 0 ≤ Geometric.Basic.quarterRadius 0 index
      exact Geometric.Basic.quarterRadius_nonneg le_rfl index
    later_close := by
      intro earlier later _
      change Norm.Basic.normSq ((compiled later).sample - (compiled earlier).sample) ≤
        Geometric.Basic.quarterRadius 0 earlier
      rw [(compiled later).sample_source, (compiled earlier).sample_source, Data.Gaussian.Basic.sub_self,
        Norm.Basic.normSq_zero]
      exact Geometric.Basic.quarterRadius_nonneg le_rfl earlier
    centerBound := normSq integral
    centerBound_nonneg := Data.Gaussian.Basic.Canonical.normSq_nonneg integral
    sample_bounded := by
      intro index
      change Norm.Basic.normSq (compiled index).sample ≤ normSq integral
      rw [Norm.Basic.normSq_eq_canonical, (compiled index).sample_source] }

open Purelib.Integration.Polynomial.Gaussian in
/-- Every stage of a polynomial program returns the source's exact integral sample.

The compiled stage retains the same nominal polynomial source. Its cached
sample reads back to that source independently of the supplied cut policy. -/
theorem polynomialProgram_sample (source : Partition.Source.PolynomialPath) (policy : PartitionPolicy source) (index :
  Nat) :
    (polynomialProgram source policy).approximation.sample index = Partition.Source.sourceSample source :=
  (compilePolicy policy index).sample_source

open Purelib.Integration.Polynomial.Gaussian in
open Purelib.Approximation.Gaussian in
/-- Two partition policies for the same polynomial source produce equivalent Gaussian names.

The certificate compares every pair of sufficiently late stages, using their shared exact sample even when their
displayed partitions differ. -/
@[expose] def polynomial_outputs_equivalent (source : Partition.Source.PolynomialPath) (left right : PartitionPolicy
  source) :
    Equivalence.NamedEquivalent
      (polynomialProgram source left).output.name (polynomialProgram source right).output.name :=
  (Equivalence.Equivalent.of_constant_samples _ _ (Partition.Source.sourceSample source)
    (polynomialProgram_sample source left) (polynomialProgram_sample source right)).toNamed

open Purelib.Integration.Polynomial.Gaussian in
open Purelib.Approximation.Gaussian in
open Purelib in
open Purelib.Polynomial in
/-- A polynomial program is equivalent to the exact constant-integral program at its source sample.

The comparison retains the partitioned program and the constant polynomial program as separate names, with equality of
all their samples supplying the equivalence. -/
@[expose] def polynomial_exact_integral_equivalent (source : Partition.Source.PolynomialPath) (policy : PartitionPolicy
  source) :
    Equivalence.NamedEquivalent (polynomialProgram source policy).output.name
      (Integration.Program.Gaussian.Basic.RefinementProgram.exactPolynomial 0 1
        (Ascending.Gaussian.Basic.constant (Partition.Source.sourceSample source))).output.name := by
  apply Equivalence.Equivalent.toNamed
  apply Equivalence.Equivalent.of_constant_samples _ _ (Partition.Source.sourceSample source)
  · exact polynomialProgram_sample source policy
  · intro index
    change (1 - 0 : Gaussian) * Ascending.Gaussian.Integral.definiteIntegral
      (Ascending.Gaussian.Basic.constant (Partition.Source.sourceSample source)) 0 1 + 0 = Partition.Source.sourceSample
        source
    rw [Ascending.Gaussian.Integral.definiteIntegral_constant]
    ring1

end Purelib.CCL.Progressive.IntegrationPrograms
