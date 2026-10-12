module

import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Curves.Plane.Conic.Basic
import Purelib.Geometry.Plane.Line.Basic
public import Purelib.Geometry.Plane.Line.Quadrance
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
import Init.Prelude
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Curves.Plane

open Purelib.Geometry

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Point

section
public section

/-!
# Divine Proportions, §15.3: parabolas

The six coefficient equations below are the denominator-cleared expansion of
`Q(X,F) = Q(X,l)`.  An explicit nonzero scale retains the source's proportional
conic notation without a quotient or a selected representative.
-/

section

variable {K : Type*} [ExplicitField K]

section

namespace Purelib.Curves.Plane.Conic

/-- The denominator-cleared conic associated with a focus and directrix. -/
@[expose] def parabolaConic [DecidableEq K] (focus :
  Plane.Point K)
    (directrix : Plane.Line K) : Conic K where
  d := directrix.b ^ 2
  e := -2 * directrix.a * directrix.b
  f := directrix.a ^ 2
  a := -2 * directrix.a * directrix.c -
    2 * Line.Basic.lineNorm directrix * focus.x
  b := -2 * directrix.b * directrix.c -
    2 * Line.Basic.lineNorm directrix * focus.y
  c := Line.Basic.lineNorm directrix * (focus.x ^ 2 + focus.y ^ 2) -
    directrix.c ^ 2
  quadratic_nonzero := by
    by_cases aZero : directrix.a = 0
    · rcases directrix.direction_nonzero with aNonzero | bNonzero
      · exact False.elim (aNonzero aZero)
      · exact Or.inl (by
          simpa only [pow_two] using
            ExplicitField.mul_ne_zero bNonzero bNonzero)
    · exact Or.inr (Or.inr
        (by
          simpa only [pow_two] using
            ExplicitField.mul_ne_zero aZero aZero))

set_option genInjectivity false in
/-- A scaled coefficient presentation of a focus/directrix parabola.

The directrix is non-null, the focus lies off it, and one nonzero scale relates all six conic coefficients to the
cleared equality of focal and directrix quadrances. -/
structure ParabolaPresentationData (conic : Conic K) (focus :
  Plane.Point K)
    (directrix : Plane.Line K) where
  /-- The directrix has nonzero squared normal norm. -/ directrixNonNull : ¬ directrix.IsNull
  /-- The focus does not lie on the directrix. -/ focusNotOnDirectrix : ¬ directrix.Contains focus
  /-- Common scale from the canonical focus/directrix coefficients to this conic. -/ scale : K
  /-- The common coefficient scale is nonzero. -/ scaleNonzero : scale ≠ 0
  /-- The conic `x²` coefficient is the scaled square of the directrix y-normal. -/ dEquation : conic.d = scale *
    directrix.b ^ 2
  /-- The conic `xy` coefficient is minus twice the scaled product of the directrix normal coordinates. -/ eEquation :
    conic.e = scale * (-2 * directrix.a * directrix.b)
  /-- The conic `y²` coefficient is the scaled square of the directrix x-normal. -/ fEquation : conic.f = scale *
    directrix.a ^ 2
  /-- The conic `x` coefficient retains the scaled directrix constant and focus x-coordinate terms. -/ aEquation :
    conic.a = scale *
    (-2 * directrix.a * directrix.c -
      2 * Line.Basic.lineNorm directrix * focus.x)
  /-- The conic `y` coefficient retains the scaled directrix constant and focus y-coordinate terms. -/ bEquation :
    conic.b = scale *
    (-2 * directrix.b * directrix.c -
      2 * Line.Basic.lineNorm directrix * focus.y)
  /-- The conic constant retains the scaled focus norm and squared directrix constant. -/ cEquation : conic.c = scale *
    (Line.Basic.lineNorm directrix * (focus.x ^ 2 + focus.y ^ 2) -
      directrix.c ^ 2)

-- Preserve the original constructor certificate names of this unchanged nominal datatype.

constructive_injectivity ParabolaPresentationData

/-- The proposition asserting an explicitly witnessed scaled presentation. -/
@[expose] def IsParabolaPresentation (conic : Conic K) (focus
  : Plane.Point K)
    (directrix : Plane.Line K) : Prop :=
  Nonempty (ParabolaPresentationData conic focus directrix)

/-- A parabola is a conic with an explicitly exhibited valid focus/directrix presentation. -/
@[expose] def IsParabola (conic : Conic K) : Prop :=
  ∃ focus : Plane.Point K, ∃ directrix : Plane.Line K,
    conic.IsParabolaPresentation focus directrix

/-- The unscaled construction has the evident presentation. -/
theorem parabolaConic_isParabolaPresentation [DecidableEq K] [Nontrivial
  K]
    (focus : Plane.Point K) (directrix : Plane.Line K)
    (directrixNonNull : ¬ directrix.IsNull)
    (focusNotOnDirectrix : ¬ directrix.Contains focus) :
    (parabolaConic focus directrix).IsParabolaPresentation
      focus directrix := by
  refine ⟨
    { directrixNonNull := directrixNonNull
      focusNotOnDirectrix := focusNotOnDirectrix
      scale := 1
      scaleNonzero := one_ne_zero
      dEquation := ?_
      eEquation := ?_
      fEquation := ?_
      aEquation := ?_
      bEquation := ?_
      cEquation := ?_ }⟩
  all_goals (unfold parabolaConic; ring1)

/-- Direct expansion of the denominator-cleared focus/directrix equation. -/
theorem parabolaConic_evaluate [DecidableEq K]
    (focus point : Plane.Point K) (directrix : Plane.Line K) :
    (parabolaConic focus directrix).evaluate point =
      Basic.lineNorm directrix * Quadrance.quadrance point focus -
        (directrix.a * point.x + directrix.b * point.y + directrix.c) ^ 2 := by
  unfold parabolaConic Conic.evaluate Basic.lineNorm Quadrance.quadrance
  ring1

/-- The constructed conic has precisely the source equation `Q(X,F) = Q(X,l)`. -/
theorem parabolaConic_contains_iff_equal_quadrances [DecidableEq K]
    (focus point : Plane.Point K) (directrix : Line K)
    (directrixNonNull : ¬ directrix.IsNull) :
    (parabolaConic focus directrix).Contains point ↔
      Quadrance.quadrance point focus =
        Quadrance.pointLineQuadrance point directrix directrixNonNull := by
  have normNonzero : Line.Basic.lineNorm directrix ≠ 0 := directrixNonNull
  have normCancel :
      Line.Basic.lineNorm directrix * (Line.Basic.lineNorm directrix)⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel _ normNonzero
  rw [Conic.Contains, parabolaConic_evaluate]
  rw [Quadrance.pointLineQuadrance_formula]
  simp only [ExplicitField.div_eq_mul_inv]
  constructor
  · intro clearedEquation
    have scaledDifferenceZero :
        Line.Basic.lineNorm directrix *
          (Quadrance.quadrance point focus -
            (directrix.a * point.x + directrix.b * point.y + directrix.c) ^ 2 *
              (Line.Basic.lineNorm directrix)⁻¹) = 0 := by
      calc
        Line.Basic.lineNorm directrix *
            (Quadrance.quadrance point focus -
              (directrix.a * point.x + directrix.b * point.y +
                  directrix.c) ^ 2 * (Line.Basic.lineNorm directrix)⁻¹) =
          Line.Basic.lineNorm directrix * Quadrance.quadrance point focus -
            (directrix.a * point.x + directrix.b * point.y +
                directrix.c) ^ 2 *
              (Line.Basic.lineNorm directrix * (Line.Basic.lineNorm directrix)⁻¹) := by ring1
        _ = 0 := by
          rw [normCancel]
          simpa only [mul_one] using clearedEquation
    have differenceZero :=
      ExplicitField.eq_zero_of_mul_eq_zero_left normNonzero scaledDifferenceZero
    calc
      Quadrance.quadrance point focus =
          (Quadrance.quadrance point focus -
              (directrix.a * point.x + directrix.b * point.y +
                  directrix.c) ^ 2 * (Line.Basic.lineNorm directrix)⁻¹) +
            (directrix.a * point.x + directrix.b * point.y +
                directrix.c) ^ 2 * (Line.Basic.lineNorm directrix)⁻¹ := by ring1
      _ = (directrix.a * point.x + directrix.b * point.y +
          directrix.c) ^ 2 * (Line.Basic.lineNorm directrix)⁻¹ := by
        rw [differenceZero]
        ring1
  · intro equality
    calc
      Line.Basic.lineNorm directrix * Quadrance.quadrance point focus -
          (directrix.a * point.x + directrix.b * point.y + directrix.c) ^ 2 =
        Line.Basic.lineNorm directrix *
            ((directrix.a * point.x + directrix.b * point.y +
                directrix.c) ^ 2 * (Line.Basic.lineNorm directrix)⁻¹) -
          (directrix.a * point.x + directrix.b * point.y + directrix.c) ^ 2 := by
            rw [equality]
      _ = (directrix.a * point.x + directrix.b * point.y +
          directrix.c) ^ 2 *
            (Line.Basic.lineNorm directrix * (Line.Basic.lineNorm directrix)⁻¹ - 1) := by ring1
      _ = 0 := by rw [normCancel]; ring1

end Purelib.Curves.Plane.Conic

end

end

end

section
public section

/-!
# Divine Proportions, Exercises 15.8 and 15.9

This module constructs a parabola's axis from its focus and directrix, proves
that equation preservation characterizes that axis up to the project's
quotient-free line equivalence, and constructs the unique vertex as the
midpoint of the focus and its altitude foot on the directrix.
-/

section

variable {K : Type*} [ExplicitField K]

section

namespace Purelib.Geometry.Conics.Parabola.Basic.Conic.ParabolaPresentationData

/-- A scaled parabola presentation evaluates as its scale times the canonical focus/directrix conic. -/
theorem evaluate_eq_scale_mul [DecidableEq
  K]
    {conic : Conic K} {focus : Plane.Point K} {directrix : Plane.Line K}
    (presentation : Purelib.Curves.Plane.Conic.ParabolaPresentationData conic focus directrix)
    (point : Plane.Point K) :
    conic.evaluate point =
      presentation.scale * (Conic.parabolaConic focus directrix).evaluate point := by
  unfold Conic.evaluate Conic.parabolaConic
  rw [presentation.dEquation, presentation.eEquation,
    presentation.fEquation, presentation.aEquation,
    presentation.bEquation, presentation.cEquation]
  unfold Basic.lineNorm
  ring1

end Purelib.Geometry.Conics.Parabola.Basic.Conic.ParabolaPresentationData

namespace Purelib.Curves.Plane.Conic

/-- Incidence with any scaled presentation is exactly equality of quadrance to the focus and quadrance to the directrix.
-/
theorem contains_iff_equal_quadrances_of_presentation [DecidableEq K]
    {conic : Conic K} {focus point : Plane.Point K} {directrix : Plane.Line K}
    (presentation : ParabolaPresentationData conic focus directrix) :
    conic.Contains point ↔
      Quadrance.quadrance point focus =
        Quadrance.pointLineQuadrance point directrix presentation.directrixNonNull := by
  have canonicalEquivalence :=
    parabolaConic_contains_iff_equal_quadrances focus point directrix
      presentation.directrixNonNull
  constructor
  · intro contains
    have scaledZero :
        presentation.scale *
          (parabolaConic focus directrix).evaluate point = 0 := by
      calc
        presentation.scale *
            (parabolaConic focus directrix).evaluate point =
          conic.evaluate point :=
            ((Purelib.Geometry.Conics.Parabola.Basic.Conic.ParabolaPresentationData.evaluate_eq_scale_mul presentation)
              point).symm
        _ = 0 := contains
    have canonicalContains :
        (parabolaConic focus directrix).Contains point :=
      ExplicitField.eq_zero_of_mul_eq_zero_left presentation.scaleNonzero scaledZero
    exact canonicalEquivalence.1 canonicalContains
  · intro equalQuadrances
    have canonicalContains :
        (parabolaConic focus directrix).Contains point :=
      canonicalEquivalence.2 equalQuadrances
    unfold Conic.Contains at canonicalContains ⊢
    rw [(Purelib.Geometry.Conics.Parabola.Basic.Conic.ParabolaPresentationData.evaluate_eq_scale_mul presentation),
      canonicalContains]
    ring1

end Purelib.Curves.Plane.Conic

end

end

end
