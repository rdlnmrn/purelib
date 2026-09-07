import DivineProportions.Conics.Tangent

/-!
# Divine Proportions, §19.3: higher-order curves and tangents

A cubic remains a finite ten-coefficient record.  Its Taylor coefficients are
explicit polynomials in the displayed base point.  First- and second-order
non-singularity are constructive disjunctions, used directly to build the
tangent line and tangent conic.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- A displayed cubic
`⟨g:h:i:j:d:e:f:a:b:c⟩`, with a genuinely nonzero cubic part. -/
structure CubicCurve (K : Type*) [Zero K] where
  g : K
  h : K
  i : K
  j : K
  d : K
  e : K
  f : K
  a : K
  b : K
  c : K
  cubic_nonzero : g ≠ 0 ∨ h ≠ 0 ∨ i ≠ 0 ∨ j ≠ 0

namespace CubicCurve

/-- Evaluation of the displayed cubic polynomial. -/
def evaluate (curve : CubicCurve K) (point : Point K) : K :=
  curve.g * point.x ^ 3 + curve.h * point.x ^ 2 * point.y +
    curve.i * point.x * point.y ^ 2 + curve.j * point.y ^ 3 +
    curve.d * point.x ^ 2 + curve.e * point.x * point.y +
    curve.f * point.y ^ 2 + curve.a * point.x +
    curve.b * point.y + curve.c

/-- Incidence with a cubic is one finite polynomial equation. -/
def Contains (curve : CubicCurve K) (point : Point K) : Prop :=
  curve.evaluate point = 0

/-- The `x²` coefficient in the Taylor curve at `A`. -/
def taylorD (curve : CubicCurve K) (point : Point K) : K :=
  curve.d + 3 * curve.g * point.x + curve.h * point.y

/-- The `xy` coefficient in the Taylor curve at `A`. -/
def taylorE (curve : CubicCurve K) (point : Point K) : K :=
  curve.e + 2 * curve.h * point.x + 2 * curve.i * point.y

/-- The `y²` coefficient in the Taylor curve at `A`. -/
def taylorF (curve : CubicCurve K) (point : Point K) : K :=
  curve.f + curve.i * point.x + 3 * curve.j * point.y

/-- The `x` coefficient in the Taylor curve at `A`. -/
def taylorA (curve : CubicCurve K) (point : Point K) : K :=
  curve.a + 2 * curve.d * point.x + curve.e * point.y +
    3 * curve.g * point.x ^ 2 + 2 * curve.h * point.x * point.y +
    curve.i * point.y ^ 2

/-- The `y` coefficient in the Taylor curve at `A`. -/
def taylorB (curve : CubicCurve K) (point : Point K) : K :=
  curve.b + curve.e * point.x + 2 * curve.f * point.y +
    curve.h * point.x ^ 2 + 2 * curve.i * point.x * point.y +
    3 * curve.j * point.y ^ 2

/-- Exact finite Taylor expansion after substituting `X+A`. -/
theorem taylor_expansion
    (curve : CubicCurve K) (point localPoint : Point K) :
    curve.evaluate (translationPoint point.x point.y localPoint) =
      curve.g * localPoint.x ^ 3 +
        curve.h * localPoint.x ^ 2 * localPoint.y +
        curve.i * localPoint.x * localPoint.y ^ 2 +
        curve.j * localPoint.y ^ 3 +
        taylorD curve point * localPoint.x ^ 2 +
        taylorE curve point * localPoint.x * localPoint.y +
        taylorF curve point * localPoint.y ^ 2 +
        taylorA curve point * localPoint.x +
        taylorB curve point * localPoint.y + curve.evaluate point := by
  unfold evaluate translationPoint taylorD taylorE taylorF taylorA taylorB
  ring1

/-- At an incident base point the Taylor curve has zero constant term. -/
theorem taylor_expansion_of_contains
    (curve : CubicCurve K) (point localPoint : Point K)
    (onCurve : curve.Contains point) :
    curve.evaluate (translationPoint point.x point.y localPoint) =
      curve.g * localPoint.x ^ 3 +
        curve.h * localPoint.x ^ 2 * localPoint.y +
        curve.i * localPoint.x * localPoint.y ^ 2 +
        curve.j * localPoint.y ^ 3 +
        taylorD curve point * localPoint.x ^ 2 +
        taylorE curve point * localPoint.x * localPoint.y +
        taylorF curve point * localPoint.y ^ 2 +
        taylorA curve point * localPoint.x +
        taylorB curve point * localPoint.y := by
  rw [taylor_expansion]
  unfold Contains at onCurve
  rw [onCurve]
  ring1

/-- First-order non-singularity is nonvanishing of the Taylor linear part. -/
def IsFirstOrderNonSingularAt
    (curve : CubicCurve K) (point : Point K) : Prop :=
  taylorA curve point ≠ 0 ∨ taylorB curve point ≠ 0

/-- Second-order non-singularity is nonvanishing of the Taylor quadratic
part. -/
def IsSecondOrderNonSingularAt
    (curve : CubicCurve K) (point : Point K) : Prop :=
  taylorD curve point ≠ 0 ∨ taylorE curve point ≠ 0 ∨
    taylorF curve point ≠ 0

/-- The first-order tangent line obtained by translating the Taylor linear
part back to the base point. -/
def tangentLine
    (curve : CubicCurve K) (point : Point K)
    (nonSingular : curve.IsFirstOrderNonSingularAt point) : Line K where
  a := taylorA curve point
  b := taylorB curve point
  c := -taylorA curve point * point.x - taylorB curve point * point.y
  direction_nonzero := nonSingular

/-- The degree-at-most-two truncation of the Taylor curve at the origin. -/
def standardTangentConic
    (curve : CubicCurve K) (point : Point K)
    (secondOrderNonSingular : curve.IsSecondOrderNonSingularAt point) :
    Conic K where
  d := taylorD curve point
  e := taylorE curve point
  f := taylorF curve point
  a := taylorA curve point
  b := taylorB curve point
  c := 0
  quadratic_nonzero := secondOrderNonSingular

/-- The second-order tangent conic translated back to the base point. -/
def tangentConic
    (curve : CubicCurve K) (point : Point K)
    (secondOrderNonSingular : curve.IsSecondOrderNonSingularAt point) :
    Conic K :=
  Conic.translateConic
    (standardTangentConic curve point secondOrderNonSingular) point

/-- The first-order tangent line contains its base point. -/
theorem tangentLine_contains
    (curve : CubicCurve K) (point : Point K)
    (nonSingular : curve.IsFirstOrderNonSingularAt point) :
    (tangentLine curve point nonSingular).Contains point := by
  unfold tangentLine Line.Contains
  ring1

/-- The second-order tangent conic contains its base point. -/
theorem tangentConic_contains
    (curve : CubicCurve K) (point : Point K)
    (secondOrderNonSingular : curve.IsSecondOrderNonSingularAt point) :
    (tangentConic curve point secondOrderNonSingular).Contains point := by
  unfold Conic.Contains tangentConic
  calc
    (Conic.translateConic
        (standardTangentConic curve point secondOrderNonSingular) point).evaluate
          point =
      (standardTangentConic curve point secondOrderNonSingular).evaluate
        ⟨0, 0⟩ := by
      have translated := Conic.translateConic_evaluate
        (standardTangentConic curve point secondOrderNonSingular) point
        ⟨0, 0⟩
      simpa only [translationPoint, zero_add] using translated
    _ = 0 := by
      unfold standardTangentConic Conic.evaluate
      ring1

/-- First-order non-singularity transfers from the cubic to its tangent conic
at the same point. -/
theorem tangentConic_nonSingularAt
    (curve : CubicCurve K) (point : Point K)
    (firstOrderNonSingular : curve.IsFirstOrderNonSingularAt point)
    (secondOrderNonSingular : curve.IsSecondOrderNonSingularAt point) :
    (tangentConic curve point secondOrderNonSingular).IsNonSingularAt point := by
  unfold Conic.IsNonSingularAt tangentConic Conic.translateConic
    standardTangentConic
  dsimp only
  rcases firstOrderNonSingular with firstNonzero | secondNonzero
  · left
    intro expandedZero
    apply firstNonzero
    calc
      taylorA curve point =
          taylorA curve point - 2 * taylorD curve point * point.x -
            taylorE curve point * point.y +
            2 * taylorD curve point * point.x +
            taylorE curve point * point.y := by
        ring1
      _ = 0 := expandedZero
  · right
    intro expandedZero
    apply secondNonzero
    calc
      taylorB curve point =
          taylorB curve point - 2 * taylorF curve point * point.y -
            taylorE curve point * point.x +
            taylorE curve point * point.x +
            2 * taylorF curve point * point.y := by
        ring1
      _ = 0 := expandedZero

/-- The source's compatibility claim: the first-order tangent to the cubic is
also the tangent to its second-order tangent conic at the base point. -/
theorem tangentLine_is_tangent_to_tangentConic
    (curve : CubicCurve K) (point : Point K)
    (firstOrderNonSingular : curve.IsFirstOrderNonSingularAt point)
    (secondOrderNonSingular : curve.IsSecondOrderNonSingularAt point) :
    (tangentLine curve point firstOrderNonSingular).Equivalent
      (Conic.tangentLine (tangentConic curve point secondOrderNonSingular)
        point (tangentConic_nonSingularAt curve point firstOrderNonSingular
          secondOrderNonSingular)) := by
  unfold tangentLine Conic.tangentLine tangentConic Conic.translateConic
    standardTangentConic Line.Equivalent
  exact ⟨by ring1, by ring1, by ring1⟩

end CubicCurve

end DivineProportions
