module

import Purelib.Algebra.Field.Ratio
public import Purelib.Geometry.Triangles.Congruence.Basic
public import Purelib.Geometry.Triangles.NonNull.Spread
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField

import Purelib.Geometry.Triangles.NonNull.Basic
import Purelib.Geometry.Triangles.Quadrea.Basic
import Purelib.Geometry.Triangles.Similarity.Entries
import Purelib.LinearAlgebra.Coordinates3.Vector
import Purelib.LinearAlgebra.Coordinates3.Vector.Permutation
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Geometry.Triangles

open Purelib.Geometry.Triangles.NonNull.Basic

open Purelib.Geometry.Triangles.Similarity

open Purelib.LinearAlgebra

open Purelib.LinearAlgebra.Coordinates3.Vector

open Purelib.LinearAlgebra.Coordinates3.Vector.Permutation

section
@[expose] public section
namespace Purelib.Geometry.Triangles.NonNull.Basic.NonNullTriangle
variable {K : Type*} [ExplicitField K]
section
variable [DecidableEq K]

/-- The book's definition of similarity: equality of the unordered triple of vertex spreads. -/
def Similar (left right : NonNull.Basic.NonNullTriangle
  K) : Prop :=
  Permutation.SameEntries left.spreads right.spreads
end
end Purelib.Geometry.Triangles.NonNull.Basic.NonNullTriangle

end

section
@[expose] public section
namespace Purelib.Geometry.Triangles.NonNull.Basic.NonNullTriangle
variable {K : Type*} [ExplicitField K]
section
variable [DecidableEq K]

/-- The source's observation following the definition of similarity: congruent non-null triangles are similar. -/
theorem congruent_triangles_are_similar
    (left right : NonNull.Basic.NonNullTriangle K) (twoNonzero : (2 : K) ≠ 0)
    (congruent : left.Congruent right) : left.Similar right := by
  have quadrancesSame :
      Permutation.SameEntries left.quadrances right.quadrances :=
    congruent
  have denominatorsSame :=
    Entries.spreadDenominators_sameEntries quadrancesSame
  have areaEqual :
      Quadrea.Basic.quadrea left.first left.second left.third =
        Quadrea.Basic.quadrea right.first right.second right.third := by
    change (Entries.archimedesValue left.quadrances) =
      (Entries.archimedesValue right.quadrances)
    exact Entries.archimedesValue_eq_of_sameEntries quadrancesSame
  have leftProducts := left.quadrea_spread_products
  have rightProducts := right.quadrea_spread_products
  have leftDenominatorsNonzero := left.spreadDenominatorsNonzero twoNonzero
  have spreadEqual
      (leftDenominator rightDenominator leftSpread rightSpread : K)
      (leftDenominatorNonzero : leftDenominator ≠ 0)
      (leftProduct :
        Quadrea.Basic.quadrea left.first left.second left.third =
          leftDenominator * leftSpread)
      (rightProduct :
        Quadrea.Basic.quadrea right.first right.second right.third =
          rightDenominator * rightSpread)
      (denominatorsEqual : leftDenominator = rightDenominator) :
      leftSpread = rightSpread := by
    apply ExplicitField.eq_of_mul_eq_mul_left leftDenominatorNonzero
    calc
      leftDenominator * leftSpread =
          Quadrea.Basic.quadrea left.first left.second left.third := leftProduct.symm
      _ = Quadrea.Basic.quadrea right.first right.second right.third := areaEqual
      _ = rightDenominator * rightSpread := rightProduct
      _ = leftDenominator * rightSpread := by rw [denominatorsEqual]
  unfold Similar
  rcases denominatorsSame with
    ⟨first, second, third⟩ | ⟨first, second, third⟩ |
    ⟨first, second, third⟩ | ⟨first, second, third⟩ |
    ⟨first, second, third⟩ | ⟨first, second, third⟩
  · apply SameEntries.abc
    · exact spreadEqual _ _ _ _ leftDenominatorsNonzero.1
        leftProducts.1 rightProducts.1 first
    · exact spreadEqual _ _ _ _ leftDenominatorsNonzero.2.1
        leftProducts.2.1 rightProducts.2.1 second
    · exact spreadEqual _ _ _ _ leftDenominatorsNonzero.2.2
        leftProducts.2.2 rightProducts.2.2 third
  · apply SameEntries.acb
    · exact spreadEqual _ _ _ _ leftDenominatorsNonzero.1
        leftProducts.1 rightProducts.1 first
    · exact spreadEqual _ _ _ _ leftDenominatorsNonzero.2.1
        leftProducts.2.1 rightProducts.2.2 second
    · exact spreadEqual _ _ _ _ leftDenominatorsNonzero.2.2
        leftProducts.2.2 rightProducts.2.1 third
  · apply SameEntries.bac
    · exact spreadEqual _ _ _ _ leftDenominatorsNonzero.1
        leftProducts.1 rightProducts.2.1 first
    · exact spreadEqual _ _ _ _ leftDenominatorsNonzero.2.1
        leftProducts.2.1 rightProducts.1 second
    · exact spreadEqual _ _ _ _ leftDenominatorsNonzero.2.2
        leftProducts.2.2 rightProducts.2.2 third
  · apply SameEntries.bca
    · exact spreadEqual _ _ _ _ leftDenominatorsNonzero.1
        leftProducts.1 rightProducts.2.1 first
    · exact spreadEqual _ _ _ _ leftDenominatorsNonzero.2.1
        leftProducts.2.1 rightProducts.2.2 second
    · exact spreadEqual _ _ _ _ leftDenominatorsNonzero.2.2
        leftProducts.2.2 rightProducts.1 third
  · apply SameEntries.cab
    · exact spreadEqual _ _ _ _ leftDenominatorsNonzero.1
        leftProducts.1 rightProducts.2.2 first
    · exact spreadEqual _ _ _ _ leftDenominatorsNonzero.2.1
        leftProducts.2.1 rightProducts.1 second
    · exact spreadEqual _ _ _ _ leftDenominatorsNonzero.2.2
        leftProducts.2.2 rightProducts.2.1 third
  · apply SameEntries.cba
    · exact spreadEqual _ _ _ _ leftDenominatorsNonzero.1
        leftProducts.1 rightProducts.2.2 first
    · exact spreadEqual _ _ _ _ leftDenominatorsNonzero.2.1
        leftProducts.2.1 rightProducts.2.1 second
    · exact spreadEqual _ _ _ _ leftDenominatorsNonzero.2.2
        leftProducts.2.2 rightProducts.1 third
end
end Purelib.Geometry.Triangles.NonNull.Basic.NonNullTriangle

end

section
@[expose] public section
namespace Purelib.Geometry.Triangles.NonNull.Basic.NonNullTriangle
variable {K : Type*} [ExplicitField K]
section
variable [DecidableEq K]

/-- Exercise 10.9. Similar non-null, noncollinear triangles have quadrance triples differing by one explicit nonzero
scale. The matching remains one of the same six finite side permutations used by the similarity witness. -/
theorem exercise_10_9 [Nontrivial K] (left right :
  NonNull.Basic.NonNullTriangle K)
    (twoNonzero : (2 : K) ≠ 0) (similar : left.Similar right) :
    ∃ factor : K, factor ≠ 0 ∧
      Permutation.SameEntries left.quadrances
        (Coordinates3.Vector.scale factor right.quadrances) := by
  let factor := right.commonSpreadRatio / left.commonSpreadRatio
  have leftRatioNonzero := left.commonSpreadRatioNonzero twoNonzero
  have rightRatioNonzero := right.commonSpreadRatioNonzero twoNonzero
  have factorNonzero : factor ≠ 0 :=
    ExplicitField.div_ne_zero rightRatioNonzero leftRatioNonzero
  have leftFactors := left.spreads_eq_commonRatio_mul_quadrances twoNonzero
  have rightFactors := right.spreads_eq_commonRatio_mul_quadrances twoNonzero
  have entryScale (leftSpread rightSpread leftQuadrance rightQuadrance : K)
      (leftFactor : leftSpread = left.commonSpreadRatio * leftQuadrance)
      (rightFactor : rightSpread = right.commonSpreadRatio * rightQuadrance)
      (spreadsEqual : leftSpread = rightSpread) :
      leftQuadrance = factor * rightQuadrance := by
    exact Purelib.Algebra.Field.Ratio.scale_eq_of_equal_products left.commonSpreadRatio
      right.commonSpreadRatio leftSpread rightSpread leftQuadrance
      rightQuadrance leftRatioNonzero leftFactor rightFactor spreadsEqual
  refine ⟨factor, factorNonzero, ?_⟩
  rcases similar with
    ⟨first, second, third⟩ | ⟨first, second, third⟩ |
    ⟨first, second, third⟩ | ⟨first, second, third⟩ |
    ⟨first, second, third⟩ | ⟨first, second, third⟩
  · apply SameEntries.abc
    · exact entryScale left.spreads.t right.spreads.t
        left.quadrances.t right.quadrances.t leftFactors.1
        rightFactors.1 first
    · exact entryScale left.spreads.r right.spreads.r
        left.quadrances.r right.quadrances.r leftFactors.2.1
        rightFactors.2.1 second
    · exact entryScale left.spreads.s right.spreads.s
        left.quadrances.s right.quadrances.s leftFactors.2.2
        rightFactors.2.2 third
  · apply SameEntries.acb
    · exact entryScale left.spreads.t right.spreads.t
        left.quadrances.t right.quadrances.t leftFactors.1
        rightFactors.1 first
    · exact entryScale left.spreads.r right.spreads.s
        left.quadrances.r right.quadrances.s leftFactors.2.1
        rightFactors.2.2 second
    · exact entryScale left.spreads.s right.spreads.r
        left.quadrances.s right.quadrances.r leftFactors.2.2
        rightFactors.2.1 third
  · apply SameEntries.bac
    · exact entryScale left.spreads.t right.spreads.r
        left.quadrances.t right.quadrances.r leftFactors.1
        rightFactors.2.1 first
    · exact entryScale left.spreads.r right.spreads.t
        left.quadrances.r right.quadrances.t leftFactors.2.1
        rightFactors.1 second
    · exact entryScale left.spreads.s right.spreads.s
        left.quadrances.s right.quadrances.s leftFactors.2.2
        rightFactors.2.2 third
  · apply SameEntries.bca
    · exact entryScale left.spreads.t right.spreads.r
        left.quadrances.t right.quadrances.r leftFactors.1
        rightFactors.2.1 first
    · exact entryScale left.spreads.r right.spreads.s
        left.quadrances.r right.quadrances.s leftFactors.2.1
        rightFactors.2.2 second
    · exact entryScale left.spreads.s right.spreads.t
        left.quadrances.s right.quadrances.t leftFactors.2.2
        rightFactors.1 third
  · apply SameEntries.cab
    · exact entryScale left.spreads.t right.spreads.s
        left.quadrances.t right.quadrances.s leftFactors.1
        rightFactors.2.2 first
    · exact entryScale left.spreads.r right.spreads.t
        left.quadrances.r right.quadrances.t leftFactors.2.1
        rightFactors.1 second
    · exact entryScale left.spreads.s right.spreads.r
        left.quadrances.s right.quadrances.r leftFactors.2.2
        rightFactors.2.1 third
  · apply SameEntries.cba
    · exact entryScale left.spreads.t right.spreads.s
        left.quadrances.t right.quadrances.s leftFactors.1
        rightFactors.2.2 first
    · exact entryScale left.spreads.r right.spreads.r
        left.quadrances.r right.quadrances.r leftFactors.2.1
        rightFactors.2.1 second
    · exact entryScale left.spreads.s right.spreads.t
        left.quadrances.s right.quadrances.t leftFactors.2.2
        rightFactors.1 third

end
end Purelib.Geometry.Triangles.NonNull.Basic.NonNullTriangle

end
