import FTA.CauchyProduct
import FTA.CCLPathIntersection
import FTA.SquarefreeFactorization

/-!
# Simultaneous Sturm guards for CCL box intersections

The four box-membership sign polynomials may contain an identically zero
coordinate or repeated/shared factors.  Their simultaneous guard therefore
skips zero polynomials and then uses the degree-recursive squarefree
factorization already verified for the Sturm layer.  Every returned factor
receives its total finite event partition on a clear rational interval.  A
single bounded central-third guard cut is also proved clear for every nonzero
box condition.  This is the finite event data feeding the quantitative
intersection sampler in Theorem 10.2.
-/

namespace FTA
namespace CCLIntersectionGuard

open FTA.ComputablePolynomial
open FTA.ComputablePolynomial.DensePolynomial
open FTA.CCLPathIntersection
open FTA.CauchyProduct
open FTA.SafeCandidates
open FTA.SquarefreeFactorization
open FTA.SturmTransducer

abbrev RatPolynomial := DensePolynomial ℚ
abbrev RationalInterval := FTA.SturmTransducer.RationalInterval

def conditionPolynomials (conditions : BoxConditions) : List RatPolynomial :=
  [conditions.xLower, conditions.xUpper,
    conditions.yLower, conditions.yUpper]

/-- Product of exactly the nonzero box-condition polynomials. -/
def conditionGuard (conditions : BoxConditions) : RatPolynomial :=
  nonzeroPolynomialProduct (conditionPolynomials conditions)

theorem conditionGuard_isZero_false (conditions : BoxConditions) :
    (conditionGuard conditions).isZero = false :=
  nonzeroPolynomialProduct_isZero_false _

theorem condition_eval_ne_zero_of_guard
    {conditions : BoxConditions} {polynomial : RatPolynomial} {t : ℚ}
    (member : polynomial ∈ conditionPolynomials conditions)
    (nonzero : polynomial.isZero = false)
    (guardClear : (conditionGuard conditions).eval t ≠ 0) :
    polynomial.eval t ≠ 0 :=
  eval_ne_zero_of_mem_nonzeroPolynomialProduct member nonzero guardClear

/-- Bounded central-third search avoiding every nonzero box condition at
once. -/
def conditionCut? (conditions : BoxConditions) (a b : ℚ) : Option ℚ :=
  centralSearch (conditionGuard conditions) a b
    (conditionGuard conditions).natDegree

def conditionCut (conditions : BoxConditions) (a b : ℚ) : ℚ :=
  (conditionCut? conditions a b).getD ((a + b) / 2)

theorem conditionCut_search_succeeds
    (conditions : BoxConditions) {a b : ℚ} (proper : a < b) :
    ∃ cut, conditionCut? conditions a b = some cut := by
  apply centralSearch_succeeds (conditionGuard conditions)
    (conditionGuard conditions).natDegree proper
    (toPolynomial_ne_zero_of_isZero_false
      (conditionGuard_isZero_false conditions))
  rw [natDegree_toPolynomial (conditionGuard_isZero_false conditions)]

theorem conditionCut_spec
    (conditions : BoxConditions) {a b : ℚ} (proper : a < b) :
    (conditionGuard conditions).eval (conditionCut conditions a b) ≠ 0 ∧
      centralLeft a b < conditionCut conditions a b ∧
      conditionCut conditions a b < centralRight a b := by
  rcases conditionCut_search_succeeds conditions proper with ⟨cut, search⟩
  rcases centralSearch_some_spec proper search with
    ⟨_member, clear, left, right⟩
  have value : conditionCut conditions a b = cut := by
    simp [conditionCut, search]
  rw [value]
  exact ⟨clear, left, right⟩

theorem conditionCut_geometry
    (conditions : BoxConditions) {a b : ℚ} (proper : a < b) :
    a < conditionCut conditions a b ∧
      conditionCut conditions a b < b ∧
      conditionCut conditions a b - a < (2 / 3 : ℚ) * (b - a) ∧
      b - conditionCut conditions a b < (2 / 3 : ℚ) * (b - a) := by
  have specification := conditionCut_spec conditions proper
  rcases specification with ⟨_clear, left, right⟩
  dsimp [centralLeft, centralRight] at left right
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem conditionCut_clears_member
    (conditions : BoxConditions) {polynomial : RatPolynomial} {a b : ℚ}
    (proper : a < b) (member : polynomial ∈ conditionPolynomials conditions)
    (nonzero : polynomial.isZero = false) :
    polynomial.eval (conditionCut conditions a b) ≠ 0 := by
  exact condition_eval_ne_zero_of_guard member nonzero
    (conditionCut_spec conditions proper).1

/-! ## Total squarefree event partitions of the simultaneous guard -/

/-- The constant guard case has no events; the nonconstant case retains the
complete degree-recursive factorization. -/
inductive GuardFactorization (conditions : BoxConditions) where
  | constant (degreeZero : (conditionGuard conditions).natDegree = 0)
  | nonconstant
      (decomposition : Decomposition (conditionGuard conditions))

def factorGuard (conditions : BoxConditions) : GuardFactorization conditions := by
  if degreeZero : (conditionGuard conditions).natDegree = 0 then
    exact .constant degreeZero
  else
    exact .nonconstant (decompose (conditionGuard conditions)
      (conditionGuard_isZero_false conditions) degreeZero)

/-- One finite event partition for every squarefree factor, all over the same
rational interval. -/
inductive FactorPartitions (interval : RationalInterval) : List Factor → Type
  | nil : FactorPartitions interval []
  | cons {factor : Factor} {factors : List Factor}
      (head : EventPartition factor.polynomial interval)
      (tail : FactorPartitions interval factors) :
      FactorPartitions interval (factor :: factors)

private def factorPartitionsOfProduct :
    (factors : List Factor) → (interval : RationalInterval) → interval.Proper →
      (factorProduct factors).eval interval.lower ≠ 0 →
      (factorProduct factors).eval interval.upper ≠ 0 →
      FactorPartitions interval factors
  | [], interval, _proper, _lowerClear, _upperClear => .nil
  | factor :: factors, interval, proper, lowerClear, upperClear => by
      have headLower : factor.polynomial.eval interval.lower ≠ 0 := by
        intro zero
        apply lowerClear
        simp [factorProduct, zero]
      have headUpper : factor.polynomial.eval interval.upper ≠ 0 := by
        intro zero
        apply upperClear
        simp [factorProduct, zero]
      have tailLower : (factorProduct factors).eval interval.lower ≠ 0 := by
        intro zero
        apply lowerClear
        simp [factorProduct, zero]
      have tailUpper : (factorProduct factors).eval interval.upper ≠ 0 := by
        intro zero
        apply upperClear
        simp [factorProduct, zero]
      let headPartition := (computedEventPartitionProgram factor.input).run
        interval.lower interval.upper proper headLower headUpper
      exact .cons headPartition
        (factorPartitionsOfProduct factors interval proper tailLower tailUpper)

/-- A nonconstant guard with clear endpoints constructively returns all
finite squarefree-factor event partitions. -/
def buildFactorPartitions
    {conditions : BoxConditions}
    (decomposition : Decomposition (conditionGuard conditions))
    (interval : RationalInterval) (proper : interval.Proper)
    (lowerClear : (conditionGuard conditions).eval interval.lower ≠ 0)
    (upperClear : (conditionGuard conditions).eval interval.upper ≠ 0) :
    FactorPartitions interval decomposition.factors := by
  have productLower :
      (factorProduct decomposition.factors).eval interval.lower ≠ 0 :=
    factorProduct_eval_ne_zero_of_decomposition_eval_ne_zero
      decomposition lowerClear
  have productUpper :
      (factorProduct decomposition.factors).eval interval.upper ≠ 0 :=
    factorProduct_eval_ne_zero_of_decomposition_eval_ne_zero
      decomposition upperClear
  exact factorPartitionsOfProduct decomposition.factors interval proper
    productLower productUpper

/-- Complete simultaneous-guard event plan: either the guard is a nonzero
constant or every factor carries its computed finite Sturm partition. -/
inductive GuardEventPlan
    (conditions : BoxConditions) (interval : RationalInterval) where
  | constant (degreeZero : (conditionGuard conditions).natDegree = 0)
  | factored
      (decomposition : Decomposition (conditionGuard conditions))
      (partitions : FactorPartitions interval decomposition.factors)

def buildGuardEventPlan
    (conditions : BoxConditions) (interval : RationalInterval)
    (proper : interval.Proper)
    (lowerClear : (conditionGuard conditions).eval interval.lower ≠ 0)
    (upperClear : (conditionGuard conditions).eval interval.upper ≠ 0) :
    GuardEventPlan conditions interval :=
  match factorGuard conditions with
  | .constant degreeZero => .constant degreeZero
  | .nonconstant decomposition =>
      .factored decomposition
        (buildFactorPartitions decomposition interval proper lowerClear upperClear)

end CCLIntersectionGuard
end FTA
