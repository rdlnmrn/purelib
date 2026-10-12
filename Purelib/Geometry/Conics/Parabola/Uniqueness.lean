module

import Purelib.Algebra.Field.Characteristic.Nonzero
import Purelib.Algebra.Field.Inverse

import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Curves.Plane.Conic.Basic
public import Purelib.Geometry.Conics.Parabola.Basic
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Point.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Curves.Plane

open Purelib.Geometry

open Purelib.Geometry.Plane

section
public section

/-!
# Divine Proportions, §15.3: parabolas

The six coefficient equations below are the denominator-cleared expansion of
`Q(X,F) = Q(X,l)`.  An explicit nonzero scale retains the source's proportional
conic notation without a quotient or a selected representative.
-/

namespace Purelib.Curves.Plane.Conic

variable {K : Type*} [ExplicitField K]

section

set_option genInjectivity false in
/-- Normalized focus/directrix data for the chart with nonzero directrix x-normal.

The record keeps the directrix ratios, nondegeneracy conditions and conic coefficient equations divided by the nonzero
`y²` coefficient. -/
private structure ParabolaAChart (conic : Conic K) (focus :
  Plane.Point K)
    (directrix : Plane.Line K) where
  /-- Ratio of the directrix y-normal to its x-normal. -/ beta : K
  /-- Ratio of the directrix constant to its x-normal. -/ gamma : K
  /-- The conic `y²` coefficient is nonzero and can normalize the remaining coefficients. -/ conicFNonzero : conic.f ≠ 0
  /-- The normalized direction ratio reconstructs the directrix y-normal. -/ lineB : directrix.b = beta * directrix.a
  /-- The normalized offset reconstructs the directrix constant. -/ lineC : directrix.c = gamma * directrix.a
  /-- The normalized directrix squared norm is nonzero. -/ normalizedNormNonzero : 1 + beta ^ 2 ≠ 0
  /-- The focus has nonzero evaluation on the normalized directrix. -/ normalizedFocusOff : focus.x + beta * focus.y +
    gamma ≠ 0
  /-- The normalized mixed coefficient determines minus twice the direction ratio. -/ eNormalized : conic.e / conic.f =
    -2 * beta
  /-- The normalized x-coefficient records the directrix offset and focus x-coordinate. -/ aNormalized : conic.a /
    conic.f =
    -2 * gamma - 2 * (1 + beta ^ 2) * focus.x
  /-- The normalized y-coefficient records the direction ratio, offset and focus y-coordinate. -/ bNormalized : conic.b
    / conic.f =
    -2 * beta * gamma - 2 * (1 + beta ^ 2) * focus.y
  /-- The normalized constant records the focus squared norm and squared directrix offset. -/ cNormalized : conic.c /
    conic.f =
    (1 + beta ^ 2) * (focus.x ^ 2 + focus.y ^ 2) - gamma ^ 2

constructive_injectivity ParabolaAChart

/-- Construct the normalized `a ≠ 0` chart by explicit division. -/
private def parabolaAChart (conic : Conic K) (focus :
  Plane.Point K)
    (directrix : Plane.Line K)
    (presentation : Conic.ParabolaPresentationData conic focus directrix)
    (directrixANonzero : directrix.a ≠ 0) :
    ParabolaAChart conic focus directrix := by
  let beta := directrix.b / directrix.a
  let gamma := directrix.c / directrix.a
  have lineB : directrix.b = beta * directrix.a := by
    calc
      directrix.b =
          (directrix.b / directrix.a) * directrix.a :=
        (ExplicitField.div_mul_cancel directrix.b
          directrixANonzero).symm
      _ = beta * directrix.a := rfl
  have lineC : directrix.c = gamma * directrix.a := by
    calc
      directrix.c =
          (directrix.c / directrix.a) * directrix.a :=
        (ExplicitField.div_mul_cancel directrix.c
          directrixANonzero).symm
      _ = gamma * directrix.a := rfl
  have aSquareNonzero : directrix.a ^ 2 ≠ 0 := by
    simpa only [pow_two] using
      ExplicitField.mul_ne_zero directrixANonzero directrixANonzero
  have conicFNonzero : conic.f ≠ 0 := by
    rw [presentation.fEquation]
    exact ExplicitField.mul_ne_zero presentation.scaleNonzero
      aSquareNonzero
  have normalizedNormNonzero : 1 + beta ^ 2 ≠ 0 := by
    intro normalizedNormZero
    apply presentation.directrixNonNull
    unfold Plane.Line.IsNull
    calc
      directrix.a ^ 2 + directrix.b ^ 2 =
          directrix.a ^ 2 * (1 + beta ^ 2) := by
        rw [lineB]
        ring1
      _ = 0 := by rw [normalizedNormZero]; ring1
  have normalizedFocusOff :
      focus.x + beta * focus.y + gamma ≠ 0 := by
    intro normalizedIncidence
    apply presentation.focusNotOnDirectrix
    unfold Plane.Line.Contains
    calc
      directrix.a * focus.x + directrix.b * focus.y + directrix.c =
          directrix.a * (focus.x + beta * focus.y + gamma) := by
        rw [lineB, lineC]
        ring1
      _ = 0 := by rw [normalizedIncidence]; ring1
  refine
    { beta := beta
      gamma := gamma
      conicFNonzero := conicFNonzero
      lineB := lineB
      lineC := lineC
      normalizedNormNonzero := normalizedNormNonzero
      normalizedFocusOff := normalizedFocusOff
      eNormalized := ?_
      aNormalized := ?_
      bNormalized := ?_
      cNormalized := ?_ }
  · apply Purelib.Algebra.Field.Inverse.div_eq_of_eq_mul_right conicFNonzero
    calc
      conic.e = presentation.scale *
          (-2 * directrix.a * directrix.b) := presentation.eEquation
      _ = conic.f * (-2 * beta) := by
        rw [presentation.fEquation, lineB]
        ring1
  · apply Purelib.Algebra.Field.Inverse.div_eq_of_eq_mul_right conicFNonzero
    calc
      conic.a = presentation.scale *
          (-2 * directrix.a * directrix.c -
            2 * Line.Basic.lineNorm directrix * focus.x) := presentation.aEquation
      _ = conic.f *
          (-2 * gamma - 2 * (1 + beta ^ 2) * focus.x) := by
        rw [presentation.fEquation]
        unfold Line.Basic.lineNorm
        rw [lineB, lineC]
        ring1
  · apply Purelib.Algebra.Field.Inverse.div_eq_of_eq_mul_right conicFNonzero
    calc
      conic.b = presentation.scale *
          (-2 * directrix.b * directrix.c -
            2 * Line.Basic.lineNorm directrix * focus.y) := presentation.bEquation
      _ = conic.f *
          (-2 * beta * gamma -
            2 * (1 + beta ^ 2) * focus.y) := by
        rw [presentation.fEquation]
        unfold Line.Basic.lineNorm
        rw [lineB, lineC]
        ring1
  · apply Purelib.Algebra.Field.Inverse.div_eq_of_eq_mul_right conicFNonzero
    calc
      conic.c = presentation.scale *
          (Line.Basic.lineNorm directrix * (focus.x ^ 2 + focus.y ^ 2) -
            directrix.c ^ 2) := presentation.cEquation
      _ = conic.f *
          ((1 + beta ^ 2) * (focus.x ^ 2 + focus.y ^ 2) -
            gamma ^ 2) := by
        rw [presentation.fEquation]
        unfold Line.Basic.lineNorm
        rw [lineB, lineC]
        ring1

/-- Uniqueness of the source's recovered data in the `a ≠ 0` chart. -/
private theorem parabolaACharts_unique
    (conic : Conic K) (focus otherFocus : Plane.Point K)
    (directrix otherDirectrix : Plane.Line K) (twoNonzero : (2 : K) ≠ 0)
    (first : ParabolaAChart conic focus directrix)
    (second : ParabolaAChart conic otherFocus otherDirectrix) :
    focus = otherFocus ∧ first.beta = second.beta ∧
      first.gamma = second.gamma := by
  have betaEqual : first.beta = second.beta := by
    apply ExplicitField.eq_of_mul_eq_mul_left
      (Purelib.Algebra.Field.Characteristic.Nonzero.negative_two_nonzero twoNonzero)
    calc
      (-2 : K) * first.beta = conic.e / conic.f :=
        first.eNormalized.symm
      _ = (-2 : K) * second.beta := second.eNormalized
  have secondANormalized :
      conic.a / conic.f =
        -2 * second.gamma -
          2 * (1 + first.beta ^ 2) * otherFocus.x := by
    simpa only [← betaEqual] using second.aNormalized
  have secondBNormalized :
      conic.b / conic.f =
        -2 * first.beta * second.gamma -
          2 * (1 + first.beta ^ 2) * otherFocus.y := by
    simpa only [← betaEqual] using second.bNormalized
  have secondCNormalized :
      conic.c / conic.f =
        (1 + first.beta ^ 2) *
            (otherFocus.x ^ 2 + otherFocus.y ^ 2) -
          second.gamma ^ 2 := by
    simpa only [← betaEqual] using second.cNormalized
  have firstIdentity :
      (conic.a / conic.f) ^ 2 + (conic.b / conic.f) ^ 2 +
          4 * (conic.a / conic.f +
            (conic.b / conic.f) * first.beta) * first.gamma =
        4 * (1 + first.beta ^ 2) * (conic.c / conic.f) := by
    rw [first.aNormalized, first.bNormalized, first.cNormalized]
    ring1
  have secondIdentity :
      (conic.a / conic.f) ^ 2 + (conic.b / conic.f) ^ 2 +
          4 * (conic.a / conic.f +
            (conic.b / conic.f) * first.beta) * second.gamma =
        4 * (1 + first.beta ^ 2) * (conic.c / conic.f) := by
    rw [secondANormalized, secondBNormalized, secondCNormalized]
    ring1
  have linearFormula :
      conic.a / conic.f + (conic.b / conic.f) * first.beta =
        -2 * (1 + first.beta ^ 2) *
          (focus.x + first.beta * focus.y + first.gamma) := by
    rw [first.aNormalized, first.bNormalized]
    ring1
  have linearNonzero :
      conic.a / conic.f + (conic.b / conic.f) * first.beta ≠ 0 := by
    have productNonzero :
        (-2 : K) * (1 + first.beta ^ 2) *
            (focus.x + first.beta * focus.y + first.gamma) ≠ 0 :=
      ExplicitField.mul_ne_zero
        (ExplicitField.mul_ne_zero
          (Purelib.Algebra.Field.Characteristic.Nonzero.negative_two_nonzero twoNonzero)
          first.normalizedNormNonzero)
        first.normalizedFocusOff
    intro linearZero
    apply productNonzero
    calc
      (-2 : K) * (1 + first.beta ^ 2) *
          (focus.x + first.beta * focus.y + first.gamma) =
        conic.a / conic.f + (conic.b / conic.f) * first.beta :=
          linearFormula.symm
      _ = 0 := linearZero
  have fourNonzero : (4 : K) ≠ 0 := by
    have twoTimesTwoNonzero : (2 : K) * 2 ≠ 0 :=
      ExplicitField.mul_ne_zero twoNonzero twoNonzero
    intro fourZero
    apply twoTimesTwoNonzero
    calc
      (2 : K) * 2 = 4 := by ring1
      _ = 0 := fourZero
  have gammaFactorNonzero :
      4 * (conic.a / conic.f +
        (conic.b / conic.f) * first.beta) ≠ 0 :=
    ExplicitField.mul_ne_zero fourNonzero linearNonzero
  have gammaProductsEqual :
      4 * (conic.a / conic.f +
          (conic.b / conic.f) * first.beta) * first.gamma =
        4 * (conic.a / conic.f +
          (conic.b / conic.f) * first.beta) * second.gamma := by
    calc
      4 * (conic.a / conic.f +
            (conic.b / conic.f) * first.beta) * first.gamma =
        ((conic.a / conic.f) ^ 2 + (conic.b / conic.f) ^ 2 +
            4 * (conic.a / conic.f +
              (conic.b / conic.f) * first.beta) * first.gamma) -
          ((conic.a / conic.f) ^ 2 + (conic.b / conic.f) ^ 2) := by
            ring1
      _ = 4 * (1 + first.beta ^ 2) * (conic.c / conic.f) -
          ((conic.a / conic.f) ^ 2 + (conic.b / conic.f) ^ 2) := by
        rw [firstIdentity]
      _ = ((conic.a / conic.f) ^ 2 + (conic.b / conic.f) ^ 2 +
            4 * (conic.a / conic.f +
              (conic.b / conic.f) * first.beta) * second.gamma) -
          ((conic.a / conic.f) ^ 2 + (conic.b / conic.f) ^ 2) := by
        rw [secondIdentity]
      _ = 4 * (conic.a / conic.f +
          (conic.b / conic.f) * first.beta) * second.gamma := by ring1
  have gammaEqual : first.gamma = second.gamma :=
    ExplicitField.eq_of_mul_eq_mul_left gammaFactorNonzero gammaProductsEqual
  have coordinateFactorNonzero :
      2 * (1 + first.beta ^ 2) ≠ 0 :=
    ExplicitField.mul_ne_zero twoNonzero
      first.normalizedNormNonzero
  have xProductsEqual :
      2 * (1 + first.beta ^ 2) * focus.x =
        2 * (1 + first.beta ^ 2) * otherFocus.x := by
    calc
      2 * (1 + first.beta ^ 2) * focus.x =
          -2 * first.gamma - conic.a / conic.f := by
        rw [first.aNormalized]
        ring1
      _ = -2 * second.gamma - conic.a / conic.f := by rw [gammaEqual]
      _ = 2 * (1 + first.beta ^ 2) * otherFocus.x := by
        rw [secondANormalized]
        ring1
  have yProductsEqual :
      2 * (1 + first.beta ^ 2) * focus.y =
        2 * (1 + first.beta ^ 2) * otherFocus.y := by
    calc
      2 * (1 + first.beta ^ 2) * focus.y =
          -2 * first.beta * first.gamma - conic.b / conic.f := by
        rw [first.bNormalized]
        ring1
      _ = -2 * first.beta * second.gamma - conic.b / conic.f := by
        rw [gammaEqual]
      _ = 2 * (1 + first.beta ^ 2) * otherFocus.y := by
        rw [secondBNormalized]
        ring1
  have xEqual :=
    ExplicitField.eq_of_mul_eq_mul_left coordinateFactorNonzero xProductsEqual
  have yEqual :=
    ExplicitField.eq_of_mul_eq_mul_left coordinateFactorNonzero yProductsEqual
  exact ⟨Plane.Point.ext xEqual yEqual, betaEqual, gammaEqual⟩

set_option genInjectivity false in
/-- Normalized focus/directrix data for a horizontal directrix.

Its x-normal vanishes; the retained offset ratio and conic equations use the nonzero `x²` coefficient. -/
private structure ParabolaBChart (conic : Conic K) (focus :
  Plane.Point K)
    (directrix : Plane.Line K) where
  /-- Ratio of the horizontal directrix constant to its y-normal. -/ delta : K
  /-- The directrix x-normal vanishes. -/ lineAZero : directrix.a = 0
  /-- The conic `x²` coefficient is nonzero and can normalize the remaining coefficients. -/ conicDNonzero : conic.d ≠ 0
  /-- The normalized offset reconstructs the horizontal directrix constant. -/ lineC : directrix.c = delta * directrix.b
  /-- The focus has nonzero evaluation on the normalized horizontal directrix. -/ normalizedFocusOff : focus.y + delta ≠
    0
  /-- The normalized x-coefficient determines minus twice the focus x-coordinate. -/ aNormalized : conic.a / conic.d =
    -2 * focus.x
  /-- The normalized y-coefficient determines minus twice the sum of the offset and focus y-coordinate. -/ bNormalized :
    conic.b / conic.d = -2 * delta - 2 * focus.y
  /-- The normalized constant is the focus squared norm minus the squared directrix offset. -/ cNormalized : conic.c /
    conic.d =
    focus.x ^ 2 + focus.y ^ 2 - delta ^ 2

constructive_injectivity ParabolaBChart

/-- Construct the normalized horizontal-directrix chart by explicit division. -/
private def parabolaBChart (conic : Conic K) (focus :
  Plane.Point K)
    (directrix : Plane.Line K)
    (presentation : Conic.ParabolaPresentationData conic focus directrix)
    (directrixAZero : directrix.a = 0) :
    ParabolaBChart conic focus directrix := by
  have directrixBNonzero : directrix.b ≠ 0 := by
    rcases directrix.direction_nonzero with aNonzero | bNonzero
    · exact False.elim (aNonzero directrixAZero)
    · exact bNonzero
  let delta := directrix.c / directrix.b
  have lineC : directrix.c = delta * directrix.b := by
    calc
      directrix.c =
          (directrix.c / directrix.b) * directrix.b :=
        (ExplicitField.div_mul_cancel directrix.c
          directrixBNonzero).symm
      _ = delta * directrix.b := rfl
  have bSquareNonzero : directrix.b ^ 2 ≠ 0 := by
    simpa only [pow_two] using
      ExplicitField.mul_ne_zero directrixBNonzero directrixBNonzero
  have conicDNonzero : conic.d ≠ 0 := by
    rw [presentation.dEquation]
    exact ExplicitField.mul_ne_zero presentation.scaleNonzero
      bSquareNonzero
  have normalizedFocusOff : focus.y + delta ≠ 0 := by
    intro normalizedIncidence
    apply presentation.focusNotOnDirectrix
    unfold Plane.Line.Contains
    calc
      directrix.a * focus.x + directrix.b * focus.y + directrix.c =
          directrix.b * (focus.y + delta) := by
        rw [directrixAZero, lineC]
        ring1
      _ = 0 := by rw [normalizedIncidence]; ring1
  refine
    { delta := delta
      lineAZero := directrixAZero
      conicDNonzero := conicDNonzero
      lineC := lineC
      normalizedFocusOff := normalizedFocusOff
      aNormalized := ?_
      bNormalized := ?_
      cNormalized := ?_ }
  · apply Purelib.Algebra.Field.Inverse.div_eq_of_eq_mul_right conicDNonzero
    calc
      conic.a = presentation.scale *
          (-2 * directrix.a * directrix.c -
            2 * Line.Basic.lineNorm directrix * focus.x) := presentation.aEquation
      _ = conic.d * (-2 * focus.x) := by
        rw [presentation.dEquation]
        unfold Line.Basic.lineNorm
        rw [directrixAZero]
        ring1
  · apply Purelib.Algebra.Field.Inverse.div_eq_of_eq_mul_right conicDNonzero
    calc
      conic.b = presentation.scale *
          (-2 * directrix.b * directrix.c -
            2 * Line.Basic.lineNorm directrix * focus.y) := presentation.bEquation
      _ = conic.d * (-2 * delta - 2 * focus.y) := by
        rw [presentation.dEquation]
        unfold Line.Basic.lineNorm
        rw [directrixAZero, lineC]
        ring1
  · apply Purelib.Algebra.Field.Inverse.div_eq_of_eq_mul_right conicDNonzero
    calc
      conic.c = presentation.scale *
          (Line.Basic.lineNorm directrix * (focus.x ^ 2 + focus.y ^ 2) -
            directrix.c ^ 2) := presentation.cEquation
      _ = conic.d *
          (focus.x ^ 2 + focus.y ^ 2 - delta ^ 2) := by
        rw [presentation.dEquation]
        unfold Line.Basic.lineNorm
        rw [directrixAZero, lineC]
        ring1

/-- Uniqueness of the recovered data in the `a = 0` chart. -/
private theorem parabolaBCharts_unique
    (conic : Conic K) (focus otherFocus : Plane.Point K)
    (directrix otherDirectrix : Plane.Line K) (twoNonzero : (2 : K) ≠ 0)
    (first : ParabolaBChart conic focus directrix)
    (second : ParabolaBChart conic otherFocus otherDirectrix) :
    focus = otherFocus ∧ first.delta = second.delta := by
  have xProductsEqual :
      (-2 : K) * focus.x = (-2 : K) * otherFocus.x := by
    calc
      (-2 : K) * focus.x = conic.a / conic.d :=
        first.aNormalized.symm
      _ = (-2 : K) * otherFocus.x := second.aNormalized
  have xEqual : focus.x = otherFocus.x :=
    ExplicitField.eq_of_mul_eq_mul_left (Purelib.Algebra.Field.Characteristic.Nonzero.negative_two_nonzero
      twoNonzero)
      xProductsEqual
  have sumProductsEqual :
      (-2 : K) * (focus.y + first.delta) =
        (-2 : K) * (otherFocus.y + second.delta) := by
    calc
      (-2 : K) * (focus.y + first.delta) = conic.b / conic.d := by
        rw [first.bNormalized]
        ring1
      _ = (-2 : K) * (otherFocus.y + second.delta) := by
        rw [second.bNormalized]
        ring1
  have sumEqual : focus.y + first.delta =
      otherFocus.y + second.delta :=
    ExplicitField.eq_of_mul_eq_mul_left (Purelib.Algebra.Field.Characteristic.Nonzero.negative_two_nonzero
      twoNonzero)
      sumProductsEqual
  have squareDifferenceEqual :
      focus.y ^ 2 - first.delta ^ 2 =
        otherFocus.y ^ 2 - second.delta ^ 2 := by
    calc
      focus.y ^ 2 - first.delta ^ 2 =
          conic.c / conic.d - focus.x ^ 2 := by
        rw [first.cNormalized]
        ring1
      _ = conic.c / conic.d - otherFocus.x ^ 2 := by rw [xEqual]
      _ = otherFocus.y ^ 2 - second.delta ^ 2 := by
        rw [second.cNormalized]
        ring1
  have differenceProductsEqual :
      (focus.y + first.delta) * (focus.y - first.delta) =
        (focus.y + first.delta) *
          (otherFocus.y - second.delta) := by
    calc
      (focus.y + first.delta) * (focus.y - first.delta) =
          focus.y ^ 2 - first.delta ^ 2 := by ring1
      _ = otherFocus.y ^ 2 - second.delta ^ 2 := squareDifferenceEqual
      _ = (otherFocus.y + second.delta) *
          (otherFocus.y - second.delta) := by ring1
      _ = (focus.y + first.delta) *
          (otherFocus.y - second.delta) := by rw [← sumEqual]
  have differenceEqual :
      focus.y - first.delta = otherFocus.y - second.delta :=
    ExplicitField.eq_of_mul_eq_mul_left first.normalizedFocusOff differenceProductsEqual
  have yProductsEqual : (2 : K) * focus.y = 2 * otherFocus.y := by
    calc
      (2 : K) * focus.y =
          (focus.y + first.delta) + (focus.y - first.delta) := by ring1
      _ = (otherFocus.y + second.delta) +
          (otherFocus.y - second.delta) := by
        rw [sumEqual, differenceEqual]
      _ = 2 * otherFocus.y := by ring1
  have yEqual : focus.y = otherFocus.y :=
    ExplicitField.eq_of_mul_eq_mul_left twoNonzero yProductsEqual
  have deltaEqual : first.delta = second.delta := by
    calc
      first.delta = (focus.y + first.delta) - focus.y := by ring1
      _ = (otherFocus.y + second.delta) - focus.y := by rw [sumEqual]
      _ = second.delta := by rw [yEqual]; ring1
  exact ⟨Plane.Point.ext xEqual yEqual, deltaEqual⟩

/-- Theorem 101 (Parabola uniqueness): the focus is equal as a point and the two displayed directrix triples represent
the same line. -/
theorem parabola_uniqueness [DecidableEq K] (conic : Conic K)
    (twoNonzero : (2 : K) ≠ 0)
    {focus otherFocus : Plane.Point K} {directrix otherDirectrix : Plane.Line K}
    (presentation : conic.IsParabolaPresentation focus directrix)
    (otherPresentation :
      conic.IsParabolaPresentation otherFocus otherDirectrix) :
    focus = otherFocus ∧ directrix.Equivalent otherDirectrix := by
  rcases presentation with ⟨presentation⟩
  rcases otherPresentation with ⟨otherPresentation⟩
  by_cases directrixAZero : directrix.a = 0
  · have conicFZero : conic.f = 0 := by
      calc
        conic.f = presentation.scale * directrix.a ^ 2 :=
          presentation.fEquation
        _ = 0 := by rw [directrixAZero]; ring1
    have otherDirectrixAZero : otherDirectrix.a = 0 := by
      by_cases otherDirectrixAZero : otherDirectrix.a = 0
      · exact otherDirectrixAZero
      · have otherASquareNonzero : otherDirectrix.a ^ 2 ≠ 0 := by
          simpa only [pow_two] using
            ExplicitField.mul_ne_zero otherDirectrixAZero
              otherDirectrixAZero
        have productNonzero :
            otherPresentation.scale * otherDirectrix.a ^ 2 ≠ 0 :=
          ExplicitField.mul_ne_zero otherPresentation.scaleNonzero
            otherASquareNonzero
        exact False.elim (productNonzero (by
          calc
            otherPresentation.scale * otherDirectrix.a ^ 2 = conic.f :=
              otherPresentation.fEquation.symm
            _ = 0 := conicFZero))
    let firstChart := parabolaBChart conic focus directrix presentation
      directrixAZero
    let secondChart := parabolaBChart conic otherFocus otherDirectrix
      otherPresentation otherDirectrixAZero
    rcases parabolaBCharts_unique conic focus otherFocus directrix
        otherDirectrix twoNonzero firstChart secondChart with
      ⟨focusEqual, deltaEqual⟩
    refine ⟨focusEqual, ?_⟩
    unfold Plane.Line.Equivalent
    constructor
    · rw [directrixAZero, otherDirectrixAZero]
      ring1
    · constructor
      · rw [directrixAZero, otherDirectrixAZero]
        ring1
      · calc
          directrix.b * otherDirectrix.c =
              directrix.b * (secondChart.delta * otherDirectrix.b) := by
            rw [secondChart.lineC]
          _ = directrix.b * (firstChart.delta * otherDirectrix.b) := by
            rw [deltaEqual]
          _ = otherDirectrix.b * directrix.c := by
            rw [firstChart.lineC]
            ring1
  · have otherDirectrixANonzero : otherDirectrix.a ≠ 0 := by
      have firstChart :=
        parabolaAChart conic focus directrix presentation directrixAZero
      by_cases otherDirectrixANonzero : otherDirectrix.a = 0
      · apply False.elim
        apply firstChart.conicFNonzero
        calc
          conic.f = otherPresentation.scale * otherDirectrix.a ^ 2 :=
            otherPresentation.fEquation
          _ = 0 := by rw [otherDirectrixANonzero]; ring1
      · exact otherDirectrixANonzero
    let firstChart :=
      parabolaAChart conic focus directrix presentation directrixAZero
    let secondChart :=
      parabolaAChart conic otherFocus otherDirectrix otherPresentation
        otherDirectrixANonzero
    rcases parabolaACharts_unique conic focus otherFocus directrix
        otherDirectrix twoNonzero firstChart secondChart with
      ⟨focusEqual, betaEqual, gammaEqual⟩
    refine ⟨focusEqual, ?_⟩
    unfold Plane.Line.Equivalent
    constructor
    · calc
        directrix.a * otherDirectrix.b =
            directrix.a * (secondChart.beta * otherDirectrix.a) := by
          rw [secondChart.lineB]
        _ = directrix.a * (firstChart.beta * otherDirectrix.a) := by
          rw [betaEqual]
        _ = otherDirectrix.a * directrix.b := by
          rw [firstChart.lineB]
          ring1
    · constructor
      · calc
          directrix.a * otherDirectrix.c =
              directrix.a * (secondChart.gamma * otherDirectrix.a) := by
            rw [secondChart.lineC]
          _ = directrix.a * (firstChart.gamma * otherDirectrix.a) := by
            rw [gammaEqual]
          _ = otherDirectrix.a * directrix.c := by
            rw [firstChart.lineC]
            ring1
      · calc
          directrix.b * otherDirectrix.c =
              (firstChart.beta * directrix.a) *
                (secondChart.gamma * otherDirectrix.a) := by
            rw [firstChart.lineB, secondChart.lineC]
          _ = (secondChart.beta * otherDirectrix.a) *
              (firstChart.gamma * directrix.a) := by
            rw [betaEqual, gammaEqual]
            ring1
          _ = otherDirectrix.b * directrix.c := by
            rw [secondChart.lineB, firstChart.lineC]

/-- Theorem 101 packaged as unique existence from the definition of parabola. -/
theorem parabola_has_unique_focus_directrix [DecidableEq K]
    (conic : Conic K) (twoNonzero : (2 : K) ≠ 0)
    (isParabola : conic.IsParabola) :
    ∃ focus : Plane.Point K, ∃ directrix : Plane.Line K,
      conic.IsParabolaPresentation focus directrix ∧
        ∀ otherFocus : Plane.Point K, ∀ otherDirectrix : Plane.Line K,
          conic.IsParabolaPresentation otherFocus otherDirectrix →
            otherFocus = focus ∧ otherDirectrix.Equivalent directrix := by
  rcases isParabola with ⟨focus, directrix, presentation⟩
  refine ⟨focus, directrix, presentation, ?_⟩
  intro otherFocus otherDirectrix otherPresentation
  exact parabola_uniqueness conic twoNonzero otherPresentation presentation
end

end Purelib.Curves.Plane.Conic

end
