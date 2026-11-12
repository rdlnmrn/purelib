module

public import Purelib.Riemann.Normalization.ContinuedInverseRoot.Primitive.Comparison
public import Purelib.Approximation.AccuracyRequest
import Purelib.Algebra.Quadratic.Pair.Polynomial.Gaussian.Comparison
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Finite comparisons at an unchanged source-model stage

A retained source primitive reading and an independently retained channel
observation have their actual operational comparison. The original source
residual and this comparison's computed finite bound pay the resulting
polynomial-to-observation error without requesting a new source stage.
-/

public section

namespace Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.Point.PrimitiveValue

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients Expression)
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Polynomial.Dense.Power (OddPowers)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Model)

variable {polynomial : Coefficients} {count : Nat} {patch : ContinuedNeighborhood polynomial count}
variable {point : Canonical} {sample : Point patch point} {depth : Nat} {model : Model polynomial patch.base.box}
variable {powers : OddPowers model.value} {reading : PrimitiveReading sample depth model powers}
variable {pairs : Fin 3} {numerator : Coefficients} {original : PrimitiveDenotation sample pairs numerator}
variable {source : Coefficients} {bank : CoherentNamed}
variable (value : PrimitiveValue reading pairs numerator original source)
variable (observed : Observation.Reading bank) (request : AccuracyRequest)

/-- The actual local source observation and its finite comparison with the unchanged external observation.

The subtype keeps the source's exact cached linear value. The original
source primitive, external reading and independent tail request remain
indices; the existing generic Comparison stores both actual states/radii
and its selected finite comparison samples.
-/
@[expose] def ReadingComparison :=
  Σ retained : {localReading : Observation.Reading original.channel // localReading.value = value.linear},
    Observation.Comparison retained.val observed request.tolerance

/-- Compare the unchanged actual source-model reading with an original external observation.

The existing source root witness supplies a possible local reading. Only
its operational channel comparison is new work. No model stage, primitive
polynomial, point, root request or old external observation is replaced.
-/
def compareReading (equivalent : NamedEquivalent original.channel.name bank.name) :
    ReadingComparison value observed request := by
  have possible := original.reading_possible reading.state reading.root reading.possible
  rewrite [← value.linear_readback] at possible
  let localReading := Observation.Reading.retain original.channel
    (original.readingState reading.state) value.linear possible
  let compared := Observation.Comparison.build localReading observed equivalent request.tolerance request.positive
  exact ⟨⟨localReading, rfl⟩, compared⟩

/-- Compare the unchanged source reading with another denotation using separate coordinate and generator evidence.

Coordinate transport aligns the two primitive expressions' point indices.
The original whole denotations derive their channel relation; neither root
agreement nor additive-constant normalization follows from the coordinate.
-/
def compareAt {otherPoint : Canonical} {otherRoot : CoherentNamed}
    (other : Expression.Denotation (Expression.oddReciprocal polynomial pairs.val numerator) otherPoint otherRoot)
    (otherReading : Observation.Reading other.channel) (pointEq : point = otherPoint)
    (roots : NamedEquivalent sample.certificate.value.name otherRoot.name) (request : AccuracyRequest) :
    ReadingComparison value otherReading request := by
  cases pointEq
  exact compareReading value otherReading request (original.equivalent other roots)

namespace ReadingComparison

variable {value observed request}
variable (compared : ReadingComparison value observed request)

/-- Read the unchanged source's actual local coefficient observation. -/
abbrev localReading := compared.1.val

/-- Read the retained actual generic comparison and its computed finite payment. -/
abbrev operational := compared.2

/-- The computed endpoint ceiling keeps the actual source residual and actual observation-comparison bound separate. -/
abbrev bound : Rational := 2 * (Norm.Basic.normSq value.residual + compared.operational.bound)

/-- Both original error components derive the actual source-polynomial-to-observation endpoint estimate. -/
theorem error_le : Norm.Basic.normSq (value.value - observed.value) ≤ compared.bound := by
  have operational := compared.operational.residual_le
  rewrite [compared.operational.residual_eq, compared.1.property] at operational
  have decomposition : value.value - observed.value = value.residual + (value.linear - observed.value) := by
    rewrite [value.residual_eq]
    ring1
  rewrite [decomposition]
  exact (Norm.Bounds.normSq_add_le_two _ _).trans
    (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Order.Arithmetic.add_le_add_direct (Order.Basic.le_refl _) operational)
      (of_decide_eq_true rfl : (0 : Rational) ≤ 2))

/-- The same payment belongs to the exact original spatial primitive polynomial, rather than a substituted reading. -/
theorem source_error_le : Norm.Basic.normSq (source.eval point - observed.value) ≤ compared.bound := by
  have same : value.value = source.eval point :=
    value.value_eq.trans (congrArg (fun polynomial : Coefficients => polynomial.eval point) value.polynomial_eq)
  rewrite [← same]
  exact compared.error_le

end ReadingComparison

end Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.Point.PrimitiveValue

end
