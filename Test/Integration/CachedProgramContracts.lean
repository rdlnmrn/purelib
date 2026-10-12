module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Sequence
public import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic

import Purelib.Integration.CCL.Program
import Purelib.Integration.Program.Gaussian.Approximation
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
public import Purelib.Integration.Polynomial.Gaussian.Path.Allowance

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Rational

open Purelib.Approximation.Rational.Geometric

open Purelib.Data.Rat

open Purelib.Integration

open Purelib.Integration.Polynomial.Gaussian

open Purelib.Integration.Program.Gaussian

/-! Cached-program readbacks preserve finite models, samples and allowances.
The reference views check cache identities, refinement semantics and geometric
certificates against the certified program interface. -/

namespace Test.Integration.CachedProgramContracts

/-- The exact canonical rational scalar type. -/
private abbrev Coordinate := Fraction.Rational
/-- The exact canonical Gaussian-rational carrier. -/
private abbrev Gaussian := Data.Gaussian.Basic.Canonical
/-- The reference finite polynomial path model type. -/
private abbrev PathModel := Path.Basic.PathModel
/-- The reference certified Gaussian path-refinement program type. -/
private abbrev RefinementProgram := Program.Gaussian.Basic.RefinementProgram
/-- The finite Gaussian approximation sequence with its retained bounds. -/
private abbrev Approximation := Gaussian.Sequence.ApproximationData
/-- The current cached Gaussian refinement-program type. -/
private abbrev ActualProgram := Cached.Basic.CachedProgram

open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

set_option genInjectivity false in
/-- The reference finite path model with cached integral sample and aggregate allowance readbacks.

Both cached readings remain linked to the same finite path model by
exact sample and allowance equalities. These fields retain the reference layout. -/
private structure RetainedModel where
  /-- The reference retained finite path model. -/ model : PathModel
  /-- The cached exact Gaussian integral sample. -/ sample : Gaussian
  /-- The cached sample is exactly the reference model's integral sample. -/ sample_eq : sample = model.integralSample
  /-- The cached reference aggregate allowance. -/ allowance : Coordinate
  /-- The allowance is exactly the reference model's aggregate allowance. -/ allowance_eq : allowance =
    model.aggregateAllowance

constructive_injectivity RetainedModel

set_option genInjectivity false in
/-- The reference cached stage sequence with geometric error, cross-stage closeness and sample magnitude certificates.

The reference stage sequence supplies each retained model and cache.
Separate geometric, pairwise-distance and magnitude certificates accompany it. -/
private structure RetainedProgram where
  /-- The retained finite path model and scalar caches at each reference stage. -/ stage : Nat → RetainedModel
  /-- The reference nonnegative scale of the geometric squared-error allowance. -/ errorScale : Coordinate
  /-- The retained error scale is nonnegative. -/ errorScale_nonneg : 0 ≤ errorScale
  /-- Every cached stage allowance fits its reference geometric quarter-radius bound. -/ modelAllowance_le : ∀ index,
    (stage index).allowance ≤ Geometric.Basic.quarterRadius errorScale index
  /-- Later cached samples remain within the earlier stage's retained squared-error bound. -/ later_close : ∀ {earlier
    later : Nat}, earlier ≤ later →
    Data.Gaussian.Norm.Basic.normSq ((stage later).sample - (stage earlier).sample) ≤
      Geometric.Basic.quarterRadius errorScale earlier
  /-- The reference common bound on squared sample magnitude. -/ centerBound : Coordinate
  /-- The retained sample-magnitude bound is nonnegative. -/ centerBound_nonneg : 0 ≤ centerBound
  /-- Every reference cached sample satisfies the retained magnitude bound. -/ sample_bounded : ∀ index,
    Data.Gaussian.Norm.Basic.normSq (stage index).sample ≤ centerBound

constructive_injectivity RetainedProgram

/-- Read the current cached program into the exact retained reference layout, preserving every cache and certificate. -/
private def retainProgram (program : ActualProgram) : RetainedProgram where
  stage index :=
    { model := (program.stage index).model
      sample := (program.stage index).sample
      sample_eq := (program.stage index).sample_eq
      allowance := (program.stage index).allowance
      allowance_eq := (program.stage index).allowance_eq }
  errorScale := program.errorScale
  errorScale_nonneg := program.errorScale_nonneg
  modelAllowance_le := program.modelAllowance_le
  later_close := program.later_close
  centerBound := program.centerBound
  centerBound_nonneg := program.centerBound_nonneg
  sample_bounded := program.sample_bounded

/-- Cache one reference finite path model's integral sample and aggregate allowance with reflexive readbacks. -/
private def retainedCanonical (model : PathModel) : RetainedModel :=
  { model := model
    sample := model.integralSample
    sample_eq := rfl
    allowance := model.aggregateAllowance
    allowance_eq := rfl }

/-- Expose the retained cached samples as their reference geometrically bounded approximation sequence. -/
private def retainedApproximation (program : RetainedProgram) : Approximation where
  sample index := (program.stage index).sample
  radiusSq := Geometric.Basic.quarterRadius program.errorScale
  radiusSq_nonneg := Geometric.Basic.quarterRadius_nonneg program.errorScale_nonneg
  later_close := program.later_close
  refineIndex current target _ := Search.firstQuarterBelow program.errorScale current target
  refineIndex_ge current target _ := Search.firstQuarterBelow_ge program.errorScale current target
  refineIndex_accurate := Search.firstQuarterBelow_accurate program.errorScale program.errorScale_nonneg
  centerBound := program.centerBound
  centerBound_nonneg := program.centerBound_nonneg
  sample_bounded := program.sample_bounded

/-- The cached sample readbacks transport cross-stage closeness to the exact reference finite-model integrals. -/
private theorem retainedLaterClose (program : RetainedProgram)
    {earlier later : Nat} (order : earlier ≤ later) :
    Data.Gaussian.Basic.Canonical.normSq
      ((program.stage later).model.integralSample -
        (program.stage earlier).model.integralSample) ≤
      Geometric.Basic.quarterRadius program.errorScale earlier := by
  rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical,
    ← (program.stage later).sample_eq, ← (program.stage earlier).sample_eq]
  exact program.later_close (earlier := earlier) (later := later) order

/-- Recover the reference refinement program from its retained model sequence and cache certificates. -/
private def retainedSemantics (program : RetainedProgram) : RefinementProgram where
  model index := (program.stage index).model
  errorScale := program.errorScale
  errorScale_nonneg := program.errorScale_nonneg
  modelAllowance_le := by
    intro index
    rw [← (program.stage index).allowance_eq]
    exact program.modelAllowance_le index
  later_close := retainedLaterClose program
  centerBound := program.centerBound
  centerBound_nonneg := program.centerBound_nonneg
  sample_bounded := by
    intro index
    rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical,
      ← (program.stage index).sample_eq]
    exact program.sample_bounded index

/-- The retained approximation sample equals the refinement program's exact model-integral sample. -/
private theorem retainedSampleSemantics (program : RetainedProgram) (index : Nat) :
    (retainedApproximation program).sample index = (retainedSemantics program).approximation.sample index :=
  (program.stage index).sample_eq

/-- Cache the reference refinement program's selected finite models without changing their integral samples or
allowances. -/
private def retainedOfProgram (program : RefinementProgram) : RetainedProgram where
  stage index := retainedCanonical (program.model index)
  errorScale := program.errorScale
  errorScale_nonneg := program.errorScale_nonneg
  modelAllowance_le := program.modelAllowance_le
  later_close := by
    intro earlier later order
    change Data.Gaussian.Norm.Basic.normSq
      ((program.model later).integralSample - (program.model earlier).integralSample) ≤
        Geometric.Basic.quarterRadius program.errorScale earlier
    exact (Data.Gaussian.Norm.Basic.normSq_eq_canonical _).trans_le
      (program.later_close (earlier := earlier) (later := later) order)
  centerBound := program.centerBound
  centerBound_nonneg := program.centerBound_nonneg
  sample_bounded := by
    intro index
    change Data.Gaussian.Norm.Basic.normSq
      (program.model index).integralSample ≤ program.centerBound
    exact (Data.Gaussian.Norm.Basic.normSq_eq_canonical _).trans_le
      (program.sample_bounded index)

-- The reverse adapter exposes exactly the cache's actual selected model.
/-- Retaining the cached program and recovering its semantics preserves the exact referencely selected finite model. -/
example (program : ActualProgram) (index : Nat) :
    (retainedSemantics (retainProgram program)).model index = (program.stage index).model := rfl

-- The old semantic sample equality is precisely the retained cache readback.
/-- The cached program and recovered semantics expose the same exact approximation sample. -/
example (program : ActualProgram) (index : Nat) :
    program.approximation.sample index =
      (retainedSemantics (retainProgram program)).approximation.sample index :=
  retainedSampleSemantics (retainProgram program) index

/-- The retained reference program layout preserves the exact cached allowance. -/
example (program : ActualProgram) (index : Nat) :
    ((retainProgram program).stage index).allowance = (program.stage index).allowance := rfl

-- The new view retains the same producer and reference model/sample/allowance.
/-- The certified cached view retains the identical reference refinement producer. -/
example (program : RefinementProgram) : program.certifiedView.producer = program := rfl

/-- The retained reference adapter and current certified view select the same finite model. -/
example (program : RefinementProgram) (index : Nat) :
    ((retainedOfProgram program).stage index).model =
      (program.certifiedView.program.stage index).model := rfl

/-- The retained reference adapter and current certified view retain the same cached sample. -/
example (program : RefinementProgram) (index : Nat) :
    ((retainedOfProgram program).stage index).sample =
      (program.certifiedView.program.stage index).sample := rfl

/-- The retained reference adapter and current certified view retain the same cached allowance. -/
example (program : RefinementProgram) (index : Nat) :
    ((retainedOfProgram program).stage index).allowance =
      (program.certifiedView.program.stage index).allowance := rfl

/-- The retained reference adapter and current certified view preserve the same geometric error scale. -/
example (program : RefinementProgram) :
    (retainedOfProgram program).errorScale = program.certifiedView.program.errorScale := rfl

/-- Caching and recovering a refinement program preserves its exact selected model at each reference index. -/
example (program : RefinementProgram) (index : Nat) :
    (retainedSemantics (retainedOfProgram program)).model index = program.model index := rfl

end Test.Integration.CachedProgramContracts
