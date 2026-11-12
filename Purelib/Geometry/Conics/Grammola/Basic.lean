module

import formalisations.DivineProportions.Chapters.Examples.ChapterSix
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Curves.Plane.Conic.Basic
import Purelib.Geometry.Plane.Line.Basic
public import Purelib.Geometry.Plane.Line.Quadrance
import Purelib.Geometry.Plane.Point.Basic
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib.Algebra.Field

open Purelib

open Purelib.Curves.Plane

open Purelib.Geometry

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

section
@[expose] public section

/-!
# Divine Proportions, §15.5: grammolas

A grammola is retained through its two explicit non-null diagonal lines and
associated quadrance.  Multiplying by the two line norms clears exactly the
two finite divisions and produces an executable conic.  The intersection of
the diagonals is then an explicit center.
-/

namespace Purelib.Geometry

namespace Conics.Grammola

variable {K : Type*} [ExplicitField K]

/-- Nondegeneracy conditions for a grammola presentation.

The two diagonal lines are non-null, neither parallel nor perpendicular, and the associated quadrance is nonzero. -/
structure Presentation (firstDiagonal secondDiagonal :
  Line K)
    (associatedQuadrance : K) : Prop where
  /-- The first diagonal has nonzero squared normal norm. -/
    firstNonNull : ¬ firstDiagonal.IsNull
  /-- The second diagonal has nonzero squared normal norm. -/
    secondNonNull : ¬ secondDiagonal.IsNull
  /-- The diagonal directions are not parallel. -/ notParallel : ¬ firstDiagonal.Parallel secondDiagonal
  /-- The diagonal directions are not perpendicular. -/ notPerpendicular : ¬ firstDiagonal.Perpendicular secondDiagonal
  /-- The associated quadrance is nonzero. -/ associatedNonzero : associatedQuadrance ≠ 0

/-- The metrical grammola equation before its two denominators are cleared. -/
def Contains (firstDiagonal secondDiagonal : Line K)
    (firstNonNull : ¬ firstDiagonal.IsNull)
    (secondNonNull : ¬ secondDiagonal.IsNull)
    (associatedQuadrance : K) (point : Point K) : Prop :=
  Quadrance.pointLineQuadrance point firstDiagonal firstNonNull +
      Quadrance.pointLineQuadrance point secondDiagonal secondNonNull =
    associatedQuadrance

/-- The denominator-cleared grammola polynomial. -/
def clearedEvaluate (firstDiagonal secondDiagonal :
  Line K)
    (associatedQuadrance : K) (point : Point K) : K :=
  Basic.lineNorm secondDiagonal * Basic.lineValue firstDiagonal point ^ 2 +
    Basic.lineNorm firstDiagonal * Basic.lineValue secondDiagonal point ^ 2 -
    associatedQuadrance * Basic.lineNorm firstDiagonal * Basic.lineNorm secondDiagonal

/-- Coefficient of `x²` in the denominator-cleared grammola equation. -/
def conicD (firstDiagonal secondDiagonal : Line K) : K
  :=
  Basic.lineNorm secondDiagonal * firstDiagonal.a ^ 2 +
    Basic.lineNorm firstDiagonal * secondDiagonal.a ^ 2

/-- Coefficient of `xy` in the denominator-cleared grammola equation. -/
def conicE (firstDiagonal secondDiagonal : Line K) : K
  :=
  2 * (Basic.lineNorm secondDiagonal * firstDiagonal.a * firstDiagonal.b +
    Basic.lineNorm firstDiagonal * secondDiagonal.a * secondDiagonal.b)

/-- Coefficient of `y²` in the denominator-cleared grammola equation. -/
def conicF (firstDiagonal secondDiagonal : Line K) : K
  :=
  Basic.lineNorm secondDiagonal * firstDiagonal.b ^ 2 +
    Basic.lineNorm firstDiagonal * secondDiagonal.b ^ 2

/-- Coefficient of `x` in the denominator-cleared grammola equation. -/
def conicA (firstDiagonal secondDiagonal : Line K) : K
  :=
  2 * (Basic.lineNorm secondDiagonal * firstDiagonal.a * firstDiagonal.c +
    Basic.lineNorm firstDiagonal * secondDiagonal.a * secondDiagonal.c)

/-- Coefficient of `y` in the denominator-cleared grammola equation. -/
def conicB (firstDiagonal secondDiagonal : Line K) : K
  :=
  2 * (Basic.lineNorm secondDiagonal * firstDiagonal.b * firstDiagonal.c +
    Basic.lineNorm firstDiagonal * secondDiagonal.b * secondDiagonal.c)

/-- Constant coefficient in the denominator-cleared grammola equation. -/
def conicC (firstDiagonal secondDiagonal : Line K)
    (associatedQuadrance : K) : K :=
  Basic.lineNorm secondDiagonal * firstDiagonal.c ^ 2 +
    Basic.lineNorm firstDiagonal * secondDiagonal.c ^ 2 -
    associatedQuadrance * Basic.lineNorm firstDiagonal * Basic.lineNorm secondDiagonal

end Conics.Grammola
end Purelib.Geometry

section
variable {K : Type*} [ExplicitField K]

namespace Purelib.Geometry.Conics.Grammola

/-- The cleared grammola equation has a nonzero quadratic coefficient.

The two non-null diagonal norms and nonzero two make the sum of its square coefficients nonzero. -/
private theorem conic_quadratic_nonzero
  [DecidableEq K]
    (firstDiagonal secondDiagonal : Line K)
    (firstNonNull : ¬ firstDiagonal.IsNull)
    (secondNonNull : ¬ secondDiagonal.IsNull)
    (twoNonzero : (2 : K) ≠ 0) :
    conicD firstDiagonal secondDiagonal ≠ 0 ∨
      conicE firstDiagonal secondDiagonal ≠ 0 ∨
      conicF firstDiagonal secondDiagonal ≠ 0 := by
  by_cases dNonzero : conicD firstDiagonal secondDiagonal ≠ 0
  · exact Or.inl dNonzero
  · right
    right
    intro fZero
    have dZero : conicD firstDiagonal secondDiagonal = 0 := by
      by_cases dZero : conicD firstDiagonal secondDiagonal = 0
      · exact dZero
      · exact False.elim (dNonzero dZero)
    have normProductNonzero :
        Basic.lineNorm firstDiagonal * Basic.lineNorm secondDiagonal ≠ 0 :=
      ExplicitField.mul_ne_zero firstNonNull secondNonNull
    have twiceProductNonzero :
        (2 : K) *
            (Basic.lineNorm firstDiagonal * Basic.lineNorm secondDiagonal) ≠ 0 :=
      ExplicitField.mul_ne_zero twoNonzero normProductNonzero
    apply twiceProductNonzero
    calc
      (2 : K) * (Basic.lineNorm firstDiagonal * Basic.lineNorm secondDiagonal) =
          conicD firstDiagonal secondDiagonal +
            conicF firstDiagonal secondDiagonal := by
        unfold conicD conicF Basic.lineNorm
        ring1
      _ = 0 := by rw [dZero, fZero]; ring1
end Purelib.Geometry.Conics.Grammola
end

namespace Purelib.Geometry

namespace Conics.Grammola

variable {K : Type*} [ExplicitField K]

/-- The explicit six-coefficient conic obtained by clearing the two line norms in the grammola equation. -/
def conic [DecidableEq K]
    (firstDiagonal secondDiagonal : Line K)
    (firstNonNull : ¬ firstDiagonal.IsNull)
    (secondNonNull : ¬ secondDiagonal.IsNull)
    (associatedQuadrance : K) (twoNonzero : (2 : K) ≠ 0) : Conic K where
  d := conicD firstDiagonal secondDiagonal
  e := conicE firstDiagonal secondDiagonal
  f := conicF firstDiagonal secondDiagonal
  a := conicA firstDiagonal secondDiagonal
  b := conicB firstDiagonal secondDiagonal
  c := conicC firstDiagonal secondDiagonal associatedQuadrance
  quadratic_nonzero := by
    by_cases dNonzero : conicD firstDiagonal secondDiagonal ≠ 0
    · exact Or.inl dNonzero
    · right
      right
      intro fZero
      have dZero : conicD firstDiagonal secondDiagonal = 0 := by
        by_cases dZero : conicD firstDiagonal secondDiagonal = 0
        · exact dZero
        · exact False.elim (dNonzero dZero)
      have normProductNonzero :
          Basic.lineNorm firstDiagonal * Basic.lineNorm
            secondDiagonal ≠ 0 :=
        ExplicitField.mul_ne_zero firstNonNull secondNonNull
      have twiceProductNonzero :
          (2 : K) *
              (Basic.lineNorm firstDiagonal * Basic.lineNorm
                secondDiagonal) ≠ 0 :=
        ExplicitField.mul_ne_zero twoNonzero normProductNonzero
      apply twiceProductNonzero
      calc
        (2 : K) * (Basic.lineNorm firstDiagonal * Basic.lineNorm
          secondDiagonal) =
            conicD firstDiagonal secondDiagonal +
              conicF firstDiagonal secondDiagonal := by
          unfold conicD
            conicF Basic.lineNorm
          ring1
        _ = 0 := by rw [dZero, fZero]; ring1

/-- The sum of the two square coefficients is twice the product of the two line norms. In particular, it cannot vanish
for a valid grammola outside characteristic two. -/
theorem conic_trace [DecidableEq K]
    (firstDiagonal secondDiagonal : Line K)
    (firstNonNull : ¬ firstDiagonal.IsNull)
    (secondNonNull : ¬ secondDiagonal.IsNull)
    (associatedQuadrance : K) (twoNonzero : (2 : K) ≠ 0) :
    (conic firstDiagonal secondDiagonal firstNonNull secondNonNull
        associatedQuadrance twoNonzero).d +
      (conic firstDiagonal secondDiagonal firstNonNull secondNonNull
        associatedQuadrance twoNonzero).f =
      2 * Basic.lineNorm firstDiagonal * Basic.lineNorm secondDiagonal := by
  unfold conic conicD
    conicF Basic.lineNorm
  ring1

/-- The sum of the grammola square coefficients is nonzero.

It equals twice the product of the non-null diagonal norms, with two explicitly assumed nonzero. -/
theorem conic_trace_nonzero [DecidableEq K]
    (firstDiagonal secondDiagonal : Line K)
    (firstNonNull : ¬ firstDiagonal.IsNull)
    (secondNonNull : ¬ secondDiagonal.IsNull)
    (associatedQuadrance : K) (twoNonzero : (2 : K) ≠ 0) :
    (conic firstDiagonal secondDiagonal firstNonNull secondNonNull
        associatedQuadrance twoNonzero).d +
      (conic firstDiagonal secondDiagonal firstNonNull secondNonNull
        associatedQuadrance twoNonzero).f ≠ 0 := by
  rw [conic_trace]
  exact ExplicitField.mul_ne_zero
    (ExplicitField.mul_ne_zero twoNonzero firstNonNull) secondNonNull

/-- Expansion of the explicit grammola conic is exactly the cleared metric polynomial. -/
theorem conic_evaluate [DecidableEq K]
    (firstDiagonal secondDiagonal : Line K)
    (firstNonNull : ¬ firstDiagonal.IsNull)
    (secondNonNull : ¬ secondDiagonal.IsNull)
    (associatedQuadrance : K) (twoNonzero : (2 : K) ≠ 0)
    (point : Point K) :
    (conic firstDiagonal secondDiagonal firstNonNull secondNonNull
      associatedQuadrance twoNonzero).evaluate point =
        clearedEvaluate firstDiagonal secondDiagonal associatedQuadrance
          point := by
  unfold conic Conic.evaluate clearedEvaluate
    Basic.lineValue conicD conicE
    conicF
    conicA conicB
      conicC
  ring1

/-- The cleared conic has exactly the original metrical grammola locus. -/
theorem conic_contains_iff [DecidableEq K]
    (firstDiagonal secondDiagonal : Line K)
    (firstNonNull : ¬ firstDiagonal.IsNull)
    (secondNonNull : ¬ secondDiagonal.IsNull)
    (associatedQuadrance : K) (twoNonzero : (2 : K) ≠ 0)
    (point : Point K) :
    (conic firstDiagonal secondDiagonal firstNonNull secondNonNull
        associatedQuadrance twoNonzero).Contains point ↔
      Contains firstDiagonal secondDiagonal firstNonNull secondNonNull
        associatedQuadrance point := by
  have firstCancel :
      Basic.lineNorm firstDiagonal * (Basic.lineNorm firstDiagonal)⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel _ firstNonNull
  have secondCancel :
      Basic.lineNorm secondDiagonal * (Basic.lineNorm secondDiagonal)⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel _ secondNonNull
  have normProductNonzero :
      Basic.lineNorm firstDiagonal * Basic.lineNorm secondDiagonal ≠ 0 :=
    ExplicitField.mul_ne_zero firstNonNull secondNonNull
  have clearedFactor : ∀ source : Point K,
      clearedEvaluate firstDiagonal secondDiagonal associatedQuadrance source =
        (Basic.lineNorm firstDiagonal * Basic.lineNorm secondDiagonal) *
          (Quadrance.pointLineQuadrance source firstDiagonal firstNonNull +
            Quadrance.pointLineQuadrance source secondDiagonal secondNonNull -
            associatedQuadrance) := by
    intro source
    rw [Quadrance.pointLineQuadrance_formula, Quadrance.pointLineQuadrance_formula]
    simp only [ExplicitField.div_eq_mul_inv]
    unfold clearedEvaluate Basic.lineValue
    calc
      Basic.lineNorm secondDiagonal *
              (firstDiagonal.a * source.x + firstDiagonal.b * source.y +
                firstDiagonal.c) ^ 2 +
            Basic.lineNorm firstDiagonal *
              (secondDiagonal.a * source.x + secondDiagonal.b * source.y +
                secondDiagonal.c) ^ 2 -
            associatedQuadrance * Basic.lineNorm firstDiagonal *
              Basic.lineNorm secondDiagonal =
          Basic.lineNorm secondDiagonal *
              (firstDiagonal.a * source.x + firstDiagonal.b * source.y +
                firstDiagonal.c) ^ 2 *
                (Basic.lineNorm firstDiagonal * (Basic.lineNorm firstDiagonal)⁻¹) +
            Basic.lineNorm firstDiagonal *
              (secondDiagonal.a * source.x + secondDiagonal.b * source.y +
                secondDiagonal.c) ^ 2 *
                (Basic.lineNorm secondDiagonal * (Basic.lineNorm secondDiagonal)⁻¹) -
            associatedQuadrance * Basic.lineNorm firstDiagonal *
              Basic.lineNorm secondDiagonal := by
        rw [firstCancel, secondCancel]
        ring1
      _ = Basic.lineNorm firstDiagonal * Basic.lineNorm secondDiagonal *
          ((firstDiagonal.a * source.x + firstDiagonal.b * source.y +
                firstDiagonal.c) ^ 2 * (Basic.lineNorm firstDiagonal)⁻¹ +
            (secondDiagonal.a * source.x + secondDiagonal.b * source.y +
                secondDiagonal.c) ^ 2 * (Basic.lineNorm secondDiagonal)⁻¹ -
            associatedQuadrance) := by ring1
  constructor
  · intro onConic
    unfold Conic.Contains at onConic
    rw [conic_evaluate, clearedFactor] at onConic
    have differenceZero :=
      ExplicitField.eq_zero_of_mul_eq_zero_left normProductNonzero onConic
    unfold Contains
    calc
      Quadrance.pointLineQuadrance point firstDiagonal firstNonNull +
          Quadrance.pointLineQuadrance point secondDiagonal secondNonNull =
        (Quadrance.pointLineQuadrance point firstDiagonal firstNonNull +
            Quadrance.pointLineQuadrance point secondDiagonal secondNonNull -
            associatedQuadrance) + associatedQuadrance := by ring1
      _ = associatedQuadrance := by rw [differenceZero]; ring1
  · intro metricEquation
    unfold Conic.Contains
    rw [conic_evaluate, clearedFactor]
    unfold Contains at metricEquation
    have differenceZero :
        Quadrance.pointLineQuadrance point firstDiagonal firstNonNull +
            Quadrance.pointLineQuadrance point secondDiagonal secondNonNull -
            associatedQuadrance = 0 := by
      rw [metricEquation]
      ring1
    rw [differenceZero]
    ring1
end Conics.Grammola

end Purelib.Geometry

end
