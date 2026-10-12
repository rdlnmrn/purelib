module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Line.Null
public import Purelib.Geometry.Plane.Line.Spread
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
public import Purelib.Geometry.Triangles.Medial.Basic
import Purelib.Geometry.Triangles.Medial.Quadrance
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init

open Purelib.Geometry

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Line.Basic

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Triangles

open Purelib.Geometry.Triangles.Medial

section
@[expose] public section

/-!
# Divine Proportions, Chapter 10: the median triangle

All three midpoint sides are retained as displayed lines.  Their distinctness,
parallelism, and non-nullity are proved explicitly, so the final similarity
statement is a finite triple of spread equalities over any explicit field of
characteristic different from two.
-/

namespace Purelib.Geometry.Triangles.Medial.Similarity

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The medial triangle has quarter quadrances, parallel corresponding sides and equal corresponding spreads.

The original vertices are distinct, all three sides are non-null and two is nonzero. The conclusion retains non-nullness
certificates for the three medial sides. -/
theorem median_triangle [DecidableEq K]
    (first second third : Plane.Point K)
    (firstSecondDistinct : first ≠ second)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (twoNonzero : (2 : K) ≠ 0)
    (side₁₂NonNull :
      ¬ (Incidence.lineThrough first second firstSecondDistinct).IsNull)
    (side₁₃NonNull :
      ¬ (Incidence.lineThrough first third firstThirdDistinct).IsNull)
    (side₂₃NonNull :
      ¬ (Incidence.lineThrough second third secondThirdDistinct).IsNull) :
    Quadrance.quadrance (Medial.Basic.sideMidpointOppositeFirst first second third)
        (Medial.Basic.sideMidpointOppositeSecond first second third) = Quadrance.quadrance first second / 4 ∧
      Quadrance.quadrance (Medial.Basic.sideMidpointOppositeSecond first second third)
        (Medial.Basic.sideMidpointOppositeThird first second third) = Quadrance.quadrance second third / 4 ∧
      Quadrance.quadrance (Medial.Basic.sideMidpointOppositeFirst first second third)
        (Medial.Basic.sideMidpointOppositeThird first second third) = Quadrance.quadrance first third / 4 ∧
      (Medial.Basic.medianSide₁₂ first second third firstSecondDistinct
          twoNonzero).Parallel
        (Incidence.lineThrough first second firstSecondDistinct) ∧
      (Medial.Basic.medianSide₂₃ first second third secondThirdDistinct
          twoNonzero).Parallel
        (Incidence.lineThrough second third secondThirdDistinct) ∧
      (Medial.Basic.medianSide₁₃ first second third firstThirdDistinct
          twoNonzero).Parallel
        (Incidence.lineThrough first third firstThirdDistinct) ∧
      ∃ (medianSide₁₂NonNull :
            ¬ (Medial.Basic.medianSide₁₂ first second third firstSecondDistinct
              twoNonzero).IsNull)
          (medianSide₁₃NonNull :
            ¬ (Medial.Basic.medianSide₁₃ first second third firstThirdDistinct
              twoNonzero).IsNull)
          (medianSide₂₃NonNull :
            ¬ (Medial.Basic.medianSide₂₃ first second third secondThirdDistinct
              twoNonzero).IsNull),
        Spread.spread
            (Medial.Basic.medianSide₁₂ first second third firstSecondDistinct twoNonzero)
            (Medial.Basic.medianSide₁₃ first second third firstThirdDistinct twoNonzero)
            medianSide₁₂NonNull medianSide₁₃NonNull =
          Spread.spread (Incidence.lineThrough first second firstSecondDistinct)
            (Incidence.lineThrough first third firstThirdDistinct)
            side₁₂NonNull side₁₃NonNull ∧
        Spread.spread
            (Medial.Basic.medianSide₁₂ first second third firstSecondDistinct twoNonzero)
            (Medial.Basic.medianSide₂₃ first second third secondThirdDistinct twoNonzero)
            medianSide₁₂NonNull medianSide₂₃NonNull =
          Spread.spread (Incidence.lineThrough first second firstSecondDistinct)
            (Incidence.lineThrough second third secondThirdDistinct)
            side₁₂NonNull side₂₃NonNull ∧
        Spread.spread
            (Medial.Basic.medianSide₁₃ first second third firstThirdDistinct twoNonzero)
            (Medial.Basic.medianSide₂₃ first second third secondThirdDistinct twoNonzero)
            medianSide₁₃NonNull medianSide₂₃NonNull =
          Spread.spread (Incidence.lineThrough first third firstThirdDistinct)
            (Incidence.lineThrough second third secondThirdDistinct)
            side₁₃NonNull side₂₃NonNull := by
  have parallel₁₂ := Medial.Basic.median_side₁₂_parallel first second third
    firstSecondDistinct twoNonzero
  have parallel₁₃ := Medial.Basic.median_side₁₃_parallel first second third
    firstThirdDistinct twoNonzero
  have parallel₂₃ := Medial.Basic.median_side₂₃_parallel first second third
    secondThirdDistinct twoNonzero
  have medianSide₁₂NonNull := Null.nonNull_of_parallel
    (Incidence.lineThrough first second firstSecondDistinct)
    (Medial.Basic.medianSide₁₂ first second third firstSecondDistinct twoNonzero)
    side₁₂NonNull (Plane.Line.parallel_symm parallel₁₂)
  have medianSide₁₃NonNull := Null.nonNull_of_parallel
    (Incidence.lineThrough first third firstThirdDistinct)
    (Medial.Basic.medianSide₁₃ first second third firstThirdDistinct twoNonzero)
    side₁₃NonNull (Plane.Line.parallel_symm parallel₁₃)
  have medianSide₂₃NonNull := Null.nonNull_of_parallel
    (Incidence.lineThrough second third secondThirdDistinct)
    (Medial.Basic.medianSide₂₃ first second third secondThirdDistinct twoNonzero)
    side₂₃NonNull (Plane.Line.parallel_symm parallel₂₃)
  refine ⟨Quadrance.median_side₁₂_quadrance first second third twoNonzero,
    Quadrance.median_side₂₃_quadrance first second third twoNonzero,
    Quadrance.median_side₁₃_quadrance first second third twoNonzero,
    parallel₁₂, parallel₂₃, parallel₁₃,
    medianSide₁₂NonNull, medianSide₁₃NonNull, medianSide₂₃NonNull,
    ?_, ?_, ?_⟩
  · exact (Spread.spread_eq_of_parallel_pairs
      (Incidence.lineThrough first second firstSecondDistinct)
      (Incidence.lineThrough first third firstThirdDistinct)
      (Medial.Basic.medianSide₁₂ first second third firstSecondDistinct twoNonzero)
      (Medial.Basic.medianSide₁₃ first second third firstThirdDistinct twoNonzero)
      side₁₂NonNull side₁₃NonNull medianSide₁₂NonNull
      medianSide₁₃NonNull (Plane.Line.parallel_symm parallel₁₂)
      (Plane.Line.parallel_symm parallel₁₃)).symm
  · exact (Spread.spread_eq_of_parallel_pairs
      (Incidence.lineThrough first second firstSecondDistinct)
      (Incidence.lineThrough second third secondThirdDistinct)
      (Medial.Basic.medianSide₁₂ first second third firstSecondDistinct twoNonzero)
      (Medial.Basic.medianSide₂₃ first second third secondThirdDistinct twoNonzero)
      side₁₂NonNull side₂₃NonNull medianSide₁₂NonNull
      medianSide₂₃NonNull (Plane.Line.parallel_symm parallel₁₂)
      (Plane.Line.parallel_symm parallel₂₃)).symm
  · exact (Spread.spread_eq_of_parallel_pairs
      (Incidence.lineThrough first third firstThirdDistinct)
      (Incidence.lineThrough second third secondThirdDistinct)
      (Medial.Basic.medianSide₁₃ first second third firstThirdDistinct twoNonzero)
      (Medial.Basic.medianSide₂₃ first second third secondThirdDistinct twoNonzero)
      side₁₃NonNull side₂₃NonNull medianSide₁₃NonNull
      medianSide₂₃NonNull (Plane.Line.parallel_symm parallel₁₃)
      (Plane.Line.parallel_symm parallel₂₃)).symm

end Purelib.Geometry.Triangles.Medial.Similarity

end
