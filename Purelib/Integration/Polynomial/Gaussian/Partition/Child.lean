module

import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.RationalEmbedding
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Integration.Partition.Interval
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
public import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
public import Purelib.Integration.Polynomial.Gaussian.Segment.Basic
import Purelib.Polynomial.Ascending.Gaussian.Antiderivative
import Purelib.Polynomial.Ascending.Gaussian.Evaluation
import Purelib.Polynomial.Ascending.Gaussian.Integral
public import Purelib.Polynomial.Ascending.Gaussian.Restriction.Cached
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Allowance
import Purelib.Data.Rat.Fraction.Arithmetic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Source-indexed Gaussian polynomial partitions

The ordered source segments retain their cut requests, child restrictions and
cached integral samples. Compilation and comparison preserve the nominal
source owners, dependent indices and exact ordered model readbacks.
-/

public section
namespace Purelib.Integration.Polynomial.Gaussian.Partition

open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Integration.Partition
open Purelib.Integration.Polynomial.Gaussian
open Purelib.Polynomial

open Purelib.Integration.Polynomial.Gaussian.Segment.Basic (PolynomialSegment)
set_option genInjectivity false in
/-- A retained subinterval, exact polynomial restriction, cell model and cached sample of one original polynomial
segment.

The restriction remains indexed by the original polynomial and embedded parameter endpoints; model and sample caches
retain their exact construction equalities. -/
structure Child (source : PolynomialSegment) where
  /-- The exact retained parameter subinterval. -/ interval : Partition.Interval
  /-- The cached restriction of the original segment polynomial to the embedded subinterval endpoints. -/ restriction :
    Polynomial.Ascending.Gaussian.Restriction.Cached source.polynomial (RationalEmbedding.parameter interval.start)
    (RationalEmbedding.parameter interval.finish)
  /-- The retained exact polynomial integration cell. -/ model : Cell.Basic.CellModel
  /-- The model uses the original segment endpoints and the exact cached restriction polynomial. -/ model_eq : model =
    Cell.Basic.CellModel.exact
    (source.point interval.start) (source.point interval.finish) restriction.polynomial
  /-- The cached transported integral sample. -/ sample : Basic.Canonical
  /-- The sample equals original child displacement times the retained restriction sample. -/ sample_eq : sample =
    (source.point interval.finish - source.point interval.start) * restriction.sample

constructive_injectivity Child

namespace Child.mk

end Child.mk

namespace Child.mk

end Child.mk

namespace Child

/-- Compute the original segment's exact restriction once and retain its cell model and transported sample.

The construction retains its supplied source and parameters. Cached data is computed once from those inputs and its
defining equalities retain that construction. -/
@[expose] def canonical (source : PolynomialSegment) (interval : Partition.Interval) : Child source :=
  let restriction := Polynomial.Ascending.Gaussian.Restriction.Cached.canonical source.polynomial
    (RationalEmbedding.parameter interval.start) (RationalEmbedding.parameter interval.finish)
  let start := source.point interval.start
  let finish := source.point interval.finish
  { interval := interval
    restriction := restriction
    model := Cell.Basic.CellModel.exact start finish restriction.polynomial
    model_eq := rfl
    sample := (finish - start) * restriction.sample
    sample_eq := rfl }

end Child

namespace Child

/-- The retained child sample is exactly its retained model's integral sample.

The sample and model remain caches of the same retained compilation. Their defining equalities transport the exact
scalar readback. -/
theorem sample_model {source : PolynomialSegment} (child : Child source) :
    child.sample = child.model.integralSample := by
  rw [child.sample_eq, child.model_eq, child.restriction.sample_eq]
  rfl

end Child

namespace Child

/-- The retained child sample is the original segment displacement times its polynomial integral over the original
subinterval.

The same polynomial restriction and embedded parameter endpoints determine this transport. Its Jacobian uses the source
displacement exactly once. -/
theorem transported_sample {source : PolynomialSegment} (child : Child source) :
    child.sample = source.displacement * Ascending.Gaussian.Integral.definiteIntegral source.polynomial
      (RationalEmbedding.parameter child.interval.start) (RationalEmbedding.parameter child.interval.finish) := by
  rw [child.sample_eq, source.point_displacement, mul_assoc, child.restriction.transported_sample]

end Child

namespace Child

/-- An exact retained child model has zero weighted allowance.

The retained cell model is exact, so its allowance is zero without changing its polynomial or geometric endpoints. -/
theorem weightedAllowance_zero {source : PolynomialSegment} (child : Child source) :
    child.model.weightedAllowance = 0 := by
  rw [child.model_eq]
  exact Fraction.Field.mul_zero_direct _

end Child

namespace Child

/-- Sum the retained child samples in their original list order.

Each head sample is added to the sum of the unchanged tail. Empty lists contribute zero. -/
@[expose] def childSum {source : PolynomialSegment} : List (Child source) → Basic.Canonical
  | [] => 0
  | child :: rest => child.sample + childSum rest

end Child

namespace Child

/-- Read the ordered retained child models as one polynomial path model.

The list order and exact cell models are preserved in the nominal path-model construction. -/
@[expose] def childModels {source : PolynomialSegment} (children : List (Child source)) :
  Path.Basic.PathModel :=
  ⟨children.map model⟩

end Child

namespace Child

/-- Summing retained child samples equals the integral sample of their exact ordered model path.

The ordered sample sum uses the same head and tail models as the path-model integral readback. -/
theorem childSum_eq_model {source : PolynomialSegment} : ∀ children : List (Child source),
    Child.childSum children = (Child.childModels children).integralSample
  | [] => rfl
  | child :: rest => by
      change child.sample + Child.childSum rest = child.model.integralSample +
        (Child.childModels rest).integralSample
      rw [child.sample_model, childSum_eq_model]

end Child

namespace Child

/-- The path of exact retained child models has zero total weighted allowance.

Every retained child is an exact model with zero weighted allowance; the ordered finite sum therefore vanishes. -/
theorem childModels_totalAllowance {source : PolynomialSegment} :
    ∀ children : List (Child source), (Child.childModels children).totalWeightedAllowance = 0
  | [] => rfl
  | child :: rest => by
      change child.model.weightedAllowance + (Child.childModels rest).totalWeightedAllowance = 0
      rw [child.weightedAllowance_zero,
        childModels_totalAllowance,
        Fraction.Field.zero_add]

end Child

namespace Child

/-- The path of exact retained child models has zero aggregate allowance.

The aggregate allowance multiplies the same retained total weighted allowance, which vanishes for exact child models. -/
theorem childModels_allowance {source : PolynomialSegment} (children : List (Child source)) :
    (Child.childModels children).aggregateAllowance = 0 := by
  unfold Path.Basic.PathModel.aggregateAllowance
  rw [Child.childModels_totalAllowance, Fraction.Field.mul_zero_direct]

end Child

namespace Child

/-- A retained interval chain's canonical child samples sum to the original segment's integral over its exact chain
endpoints.

The ordered interval chain supplies endpoint continuity; the original polynomial and displacement remain fixed
throughout the telescoping sum. -/
theorem childSum_chain (source : PolynomialSegment) {start finish : Fraction.Rational}
    {intervals : List Partition.Interval} (chain : Interval.Chain start finish intervals) :
    Child.childSum (intervals.map (canonical source)) =
      source.displacement * Ascending.Gaussian.Integral.definiteIntegral source.polynomial (RationalEmbedding.parameter
        start) (RationalEmbedding.parameter finish) := by
  induction chain with
  | nil point =>
      change 0 = source.displacement *
        (Ascending.Gaussian.Evaluation.eval (Ascending.Gaussian.Antiderivative.antiderivative source.polynomial)
          (RationalEmbedding.parameter point) -
          Ascending.Gaussian.Evaluation.eval (Ascending.Gaussian.Antiderivative.antiderivative source.polynomial)
            (RationalEmbedding.parameter point))
      rw [sub_self, Basic.mul_zero]
  | @cons start middle finish tail chain inductionHypothesis =>
      change (canonical source ⟨start, middle⟩).sample +
        Child.childSum (tail.map (canonical source)) = _
      rw [transported_sample, inductionHypothesis, ← mul_add]
      exact congrArg (source.displacement * ·)
        (Ascending.Gaussian.Integral.definiteIntegral_concat source.polynomial (RationalEmbedding.parameter start)
          (RationalEmbedding.parameter middle) (RationalEmbedding.parameter finish)).symm

end Child

end Purelib.Integration.Polynomial.Gaussian.Partition
end
