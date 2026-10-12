module

public import Purelib.Curves.Plane.Conic.Center
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Curves.Plane.Conic.Basic
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
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Curves.Plane

open Purelib.Geometry

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

section
public section

/-!
# Divine Proportions, Exercise 15.6: ribbons

A ribbon is kept as finite coefficient data for the cleared equation
`(ax+by+c)² = K(a²+b²)`.  The presentation retains its arbitrary nonzero
conic scale, while equality of displayed lines remains the quotient-free
relation `Line.Equivalent`.
-/

namespace Purelib.Geometry

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

namespace Conics.Ribbon

/-- The cleared conic attached to `Q(X,l)=K`. -/
@[expose] def conic (line : Plane.Line K) (ribbonQuadrance : K)
  : Conic K where
  d := line.a ^ 2
  e := 2 * line.a * line.b
  f := line.b ^ 2
  a := 2 * line.a * line.c
  b := 2 * line.b * line.c
  c := line.c ^ 2 - ribbonQuadrance * Line.Basic.lineNorm line
  quadratic_nonzero := by
    rcases line.direction_nonzero with lineANonzero | lineBNonzero
    · exact Or.inl (by
        simpa only [pow_two] using
          Algebra.Field.ExplicitField.mul_ne_zero lineANonzero lineANonzero)
    · exact Or.inr (Or.inr (by
        simpa only [pow_two] using
          Algebra.Field.ExplicitField.mul_ne_zero lineBNonzero lineBNonzero))

set_option genInjectivity false in
/-- A scaled coefficient presentation of a ribbon conic.

It retains a non-null defining line, a nonzero common scale and all six equations for the cleared point-to-line
quadrance locus. -/
structure PresentationData (source : Conic K) (line :
  Plane.Line K)
    (ribbonQuadrance : K) where
  /-- The defining line has nonzero squared normal norm. -/ lineNonNull : ¬ line.IsNull
  /-- Common scale from the canonical ribbon coefficients to the source conic. -/ scale : K
  /-- The common coefficient scale is nonzero. -/ scaleNonzero : scale ≠ 0
  /-- The source `x²` coefficient is the scaled square of the line normal x-coordinate. -/ dEquation : source.d = scale
    * line.a ^ 2
  /-- The source `xy` coefficient is the scaled product of the line normal coordinates, multiplied by two. -/ eEquation
    : source.e = scale * (2 * line.a * line.b)
  /-- The source `y²` coefficient is the scaled square of the line normal y-coordinate. -/ fEquation : source.f = scale
    * line.b ^ 2
  /-- The source `x` coefficient is the scaled product of the line x-coordinate and constant, multiplied by two. -/
    aEquation : source.a = scale * (2 * line.a * line.c)
  /-- The source `y` coefficient is the scaled product of the line y-coordinate and constant, multiplied by two. -/
    bEquation : source.b = scale * (2 * line.b * line.c)
  /-- The source constant is the scaled squared line constant minus the ribbon quadrance times the line norm. -/
    cEquation : source.c =
    scale * (line.c ^ 2 - ribbonQuadrance * Line.Basic.lineNorm line)

-- Preserve the original constructor certificate names of this unchanged nominal datatype.

constructive_injectivity PresentationData

namespace PresentationData.mk

end PresentationData.mk

/-- The proposition asserting an explicitly witnessed ribbon presentation. -/
@[expose] def IsPresentation (source : Conic K) (line :
  Plane.Line K)
    (ribbonQuadrance : K) : Prop :=
  Nonempty (PresentationData source line ribbonQuadrance)

/-- A ribbon is a conic with one explicitly exhibited valid presentation. -/
@[expose] def IsRibbon (source : Conic K) : Prop :=
  ∃ line : Plane.Line K, ∃ ribbonQuadrance : K,
    IsPresentation source line ribbonQuadrance

/-- The canonical cleared coefficient record has scale one. -/
theorem conic_isPresentation [Nontrivial K]
    (line : Plane.Line K) (ribbonQuadrance : K)
    (lineNonNull : ¬ line.IsNull) :
    IsPresentation (conic line ribbonQuadrance) line
      ribbonQuadrance := by
  refine ⟨
    { lineNonNull := lineNonNull
      scale := 1
      scaleNonzero := one_ne_zero
      dEquation := ?_
      eEquation := ?_
      fEquation := ?_
      aEquation := ?_
      bEquation := ?_
      cEquation := ?_ }⟩
  all_goals (unfold conic; ring1)

/-- Direct expansion of the cleared ribbon equation. -/
theorem conic_evaluate (line : Plane.Line K) (ribbonQuadrance :
  K)
    (point : Plane.Point K) :
    (conic line ribbonQuadrance).evaluate point =
      (line.a * point.x + line.b * point.y + line.c) ^ 2 -
        ribbonQuadrance * Basic.lineNorm line := by
  unfold conic Conic.evaluate Basic.lineNorm
  ring1

namespace PresentationData

/-- Expansion of an arbitrarily scaled ribbon presentation. -/
theorem evaluate {source : Conic K}
  {line : Plane.Line K}
    {ribbonQuadrance : K}
    (presentation : PresentationData source line ribbonQuadrance)
    (point : Plane.Point K) :
    source.evaluate point =
      presentation.scale *
        ((line.a * point.x + line.b * point.y + line.c) ^ 2 -
          ribbonQuadrance * Line.Basic.lineNorm line) := by
  unfold Conic.evaluate
  rw [presentation.dEquation, presentation.eEquation,
    presentation.fEquation, presentation.aEquation,
    presentation.bEquation, presentation.cEquation]
  ring1

end PresentationData

/-- The canonical conic has exactly the metric locus `Q(X,l)=K`. -/
theorem conic_contains_iff [DecidableEq K]
    (line : Plane.Line K) (ribbonQuadrance : K)
    (lineNonNull : ¬ line.IsNull) (point : Plane.Point K) :
    (conic line ribbonQuadrance).Contains point ↔
      Quadrance.pointLineQuadrance point line lineNonNull = ribbonQuadrance := by
  have normNonzero : Line.Basic.lineNorm line ≠ 0 := lineNonNull
  have normCancel : Line.Basic.lineNorm line * (Line.Basic.lineNorm line)⁻¹ = (1 : K) :=
    Algebra.Field.ExplicitField.mul_inv_cancel _ normNonzero
  rw [Conic.Contains, conic_evaluate,
    Quadrance.pointLineQuadrance_formula point line lineNonNull]
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
  let numerator :=
    (line.a * point.x + line.b * point.y + line.c) ^ 2
  change numerator - ribbonQuadrance * Line.Basic.lineNorm line = 0 ↔
    numerator * (Line.Basic.lineNorm line)⁻¹ = ribbonQuadrance
  constructor
  · intro clearedEquation
    calc
      numerator * (Line.Basic.lineNorm line)⁻¹ =
          (numerator - ribbonQuadrance * Line.Basic.lineNorm line) *
              (Line.Basic.lineNorm line)⁻¹ +
            ribbonQuadrance *
              (Line.Basic.lineNorm line * (Line.Basic.lineNorm line)⁻¹) := by ring1
      _ = ribbonQuadrance := by rw [clearedEquation, normCancel]; ring1
  · intro quotientEquation
    have numeratorEquation :
        numerator = ribbonQuadrance * Line.Basic.lineNorm line := by
      calc
        numerator = numerator *
            (Line.Basic.lineNorm line * (Line.Basic.lineNorm line)⁻¹) := by rw [normCancel]; ring1
        _ = (numerator * (Line.Basic.lineNorm line)⁻¹) * Line.Basic.lineNorm line := by ring1
        _ = ribbonQuadrance * Line.Basic.lineNorm line := by rw [quotientEquation]
    rw [numeratorEquation]
    ring1

namespace PresentationData

/-- Every scaled ribbon presentation recovers the source's metric equation. -/
theorem contains_iff [DecidableEq K]
    {source : Conic K} {line : Plane.Line K} {ribbonQuadrance : K}
    (presentation : PresentationData source line ribbonQuadrance)
    (point : Plane.Point K) :
    source.Contains point ↔
      Quadrance.pointLineQuadrance point line presentation.lineNonNull =
        ribbonQuadrance := by
  constructor
  · intro sourceContains
    have scaledZero :
        presentation.scale *
          ((line.a * point.x + line.b * point.y + line.c) ^ 2 -
            ribbonQuadrance * Line.Basic.lineNorm line) = 0 := by
      calc
        presentation.scale *
            ((line.a * point.x + line.b * point.y + line.c) ^ 2 -
              ribbonQuadrance * Line.Basic.lineNorm line) = source.evaluate point :=
          (presentation.evaluate point).symm
        _ = 0 := sourceContains
    have clearedZero :=
      Algebra.Field.ExplicitField.eq_zero_of_mul_eq_zero_left presentation.scaleNonzero scaledZero
    apply (conic_contains_iff line ribbonQuadrance
      presentation.lineNonNull point).1
    unfold Conic.Contains
    rw [conic_evaluate]
    exact clearedZero
  · intro metricEquation
    have canonicalContains :=
      (conic_contains_iff line ribbonQuadrance
        presentation.lineNonNull point).2 metricEquation
    have clearedZero :
        (line.a * point.x + line.b * point.y + line.c) ^ 2 -
            ribbonQuadrance * Line.Basic.lineNorm line = 0 := by
      unfold Conic.Contains at canonicalContains
      rw [conic_evaluate] at canonicalContains
      exact canonicalContains
    unfold Conic.Contains
    rw [presentation.evaluate, clearedZero]
    ring1

/-- The centers of a presented ribbon are exactly the points on its defining line. This strengthens the last clause of
Exercise 15.6 to an equivalence. -/
theorem isCenter_iff_contains
    {source : Conic K} {line : Plane.Line K} {ribbonQuadrance : K}
    (presentation : PresentationData source line ribbonQuadrance)
    (twoNonzero : (2 : K) ≠ 0) (point : Plane.Point K) :
    source.IsCenter point ↔ line.Contains point := by
  let lineValue := line.a * point.x + line.b * point.y + line.c
  have firstIdentity :
      2 * source.d * point.x + source.e * point.y + source.a =
        2 * presentation.scale * line.a * lineValue := by
    rw [presentation.dEquation, presentation.eEquation,
      presentation.aEquation]
    unfold lineValue
    ring1
  have secondIdentity :
      source.e * point.x + 2 * source.f * point.y + source.b =
        2 * presentation.scale * line.b * lineValue := by
    rw [presentation.eEquation, presentation.fEquation,
      presentation.bEquation]
    unfold lineValue
    ring1
  change
    (2 * source.d * point.x + source.e * point.y + source.a = 0 ∧
      source.e * point.x + 2 * source.f * point.y + source.b = 0) ↔
        lineValue = 0
  constructor
  · intro centerEquations
    rcases line.direction_nonzero with lineANonzero | lineBNonzero
    · apply Algebra.Field.ExplicitField.eq_zero_of_mul_eq_zero_left
        (Algebra.Field.ExplicitField.mul_ne_zero
          (Algebra.Field.ExplicitField.mul_ne_zero twoNonzero
            presentation.scaleNonzero) lineANonzero)
      calc
        2 * presentation.scale * line.a * lineValue =
            2 * source.d * point.x + source.e * point.y + source.a :=
          firstIdentity.symm
        _ = 0 := centerEquations.1
    · apply Algebra.Field.ExplicitField.eq_zero_of_mul_eq_zero_left
        (Algebra.Field.ExplicitField.mul_ne_zero
          (Algebra.Field.ExplicitField.mul_ne_zero twoNonzero
            presentation.scaleNonzero) lineBNonzero)
      calc
        2 * presentation.scale * line.b * lineValue =
            source.e * point.x + 2 * source.f * point.y + source.b :=
          secondIdentity.symm
        _ = 0 := centerEquations.2
  · intro onLine
    constructor
    · calc
        2 * source.d * point.x + source.e * point.y + source.a =
            2 * presentation.scale * line.a * lineValue := firstIdentity
        _ = 0 := by rw [onLine]; ring1
    · calc
        source.e * point.x + 2 * source.f * point.y + source.b =
            2 * presentation.scale * line.b * lineValue := secondIdentity
        _ = 0 := by rw [onLine]; ring1

end PresentationData

end Conics.Ribbon

end Purelib.Geometry

end
