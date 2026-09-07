import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Isometries.Models

/-!
# Divine Proportions, Theorem 94: classification of isometries

Every isometry is split constructively into translation by its displayed image
of the origin and an isometry fixing the origin.  The factorization and its
uniqueness are pointwise finite coordinate equalities.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

namespace PlaneIsometry

/-- The canonical translation factor, read directly from the image of the
origin. -/
def translationComponent (isometry : PlaneIsometry K) : PlaneIsometry K :=
  translation (isometry planeOrigin).x (isometry planeOrigin).y

/-- Translate the image of the origin back to zero; this is the canonical
orthogonality factor. -/
def orthogonalityComponent (isometry : PlaneIsometry K) : PlaneIsometry K :=
  (translation (-(isometry planeOrigin).x) (-(isometry planeOrigin).y)).comp
    isometry

/-- The canonical second factor fixes the origin. -/
theorem orthogonalityComponent_fixesOrigin (isometry : PlaneIsometry K) :
    (isometry.orthogonalityComponent).IsOrthogonality := by
  unfold IsOrthogonality orthogonalityComponent PlaneIsometry.comp
    translation planeOrigin translationPoint
  apply Point.ext <;>
    ring1

/-- The canonical factors multiply back to the original isometry. -/
theorem translation_orthogonality_decomposition
    (isometry : PlaneIsometry K) (point : Point K) :
    isometry point =
      isometry.translationComponent
        (isometry.orthogonalityComponent point) := by
  apply Point.ext <;>
    unfold translationComponent orthogonalityComponent PlaneIsometry.comp
      translation translationPoint <;>
    ring1

/-- Any translation-orthogonality factorization has the canonical translation
parameters and the canonical orthogonality point map. -/
theorem translation_orthogonality_unique
    (isometry orthogonality : PlaneIsometry K) (u v : K)
    (fixesOrigin : orthogonality.IsOrthogonality)
    (decomposition : ∀ point : Point K,
      isometry point = translation u v (orthogonality point)) :
    u = (isometry planeOrigin).x ∧
      v = (isometry planeOrigin).y ∧
      ∀ point : Point K,
        orthogonality point = isometry.orthogonalityComponent point := by
  have atOrigin := decomposition planeOrigin
  have uCanonical : u = (isometry planeOrigin).x := by
    have xEquality := congrArg Point.x atOrigin
    unfold IsOrthogonality at fixesOrigin
    rw [fixesOrigin] at xEquality
    simpa [translation, translationPoint, planeOrigin] using xEquality.symm
  have vCanonical : v = (isometry planeOrigin).y := by
    have yEquality := congrArg Point.y atOrigin
    unfold IsOrthogonality at fixesOrigin
    rw [fixesOrigin] at yEquality
    simpa [translation, translationPoint, planeOrigin] using yEquality.symm
  refine ⟨uCanonical, vCanonical, ?_⟩
  intro point
  have atPoint := decomposition point
  apply Point.ext
  · have xEquality := congrArg Point.x atPoint
    change
      (orthogonality point).x =
        (isometry point).x + -(isometry planeOrigin).x
    change
      (isometry point).x = (orthogonality point).x + u
      at xEquality
    calc
      (orthogonality point).x = (isometry point).x - u := by
        rw [xEquality]
        ring1
      _ = (isometry point).x + -(isometry planeOrigin).x := by
        rw [uCanonical]
        ring1
  · have yEquality := congrArg Point.y atPoint
    change
      (orthogonality point).y =
        (isometry point).y + -(isometry planeOrigin).y
    change
      (isometry point).y = (orthogonality point).y + v
      at yEquality
    calc
      (orthogonality point).y = (isometry point).y - v := by
        rw [yEquality]
        ring1
      _ = (isometry point).y + -(isometry planeOrigin).y := by
        rw [vCanonical]
        ring1

/-- Theorem 94 (Classification of isometries): existence and uniqueness of
the translation-orthogonality factorization.  Equality of stored isometries is
expressed pointwise, avoiding irrelevant equality of inverse proof fields. -/
theorem isometryClassification (isometry : PlaneIsometry K) :
    ∃ u v : K, ∃ orthogonality : PlaneIsometry K,
      orthogonality.IsOrthogonality ∧
      (∀ point : Point K,
        isometry point = translation u v (orthogonality point)) ∧
      ∀ u' v' : K, ∀ orthogonality' : PlaneIsometry K,
        orthogonality'.IsOrthogonality →
        (∀ point : Point K,
          isometry point = translation u' v' (orthogonality' point)) →
        u' = u ∧ v' = v ∧
          ∀ point : Point K, orthogonality' point = orthogonality point := by
  let u := (isometry planeOrigin).x
  let v := (isometry planeOrigin).y
  let orthogonality := isometry.orthogonalityComponent
  refine ⟨u, v, orthogonality,
    isometry.orthogonalityComponent_fixesOrigin, ?_, ?_⟩
  · intro point
    exact isometry.translation_orthogonality_decomposition point
  · intro u' v' orthogonality' fixesOrigin decomposition
    have unique := isometry.translation_orthogonality_unique
      orthogonality' u' v' fixesOrigin decomposition
    exact ⟨unique.1, unique.2.1, unique.2.2⟩

end PlaneIsometry

/-- Exercise 13.6: rotation in the origin is the central rotation with unit
parameters `[-1,0]`. -/
theorem rotationInOrigin_eq_centralRotationPoint (point : Point K) :
    rotateInPoint planeOrigin point = centralRotationPoint (-1) 0 point := by
  apply Point.ext <;>
    unfold rotateInPoint planeOrigin centralRotationPoint <;>
    ring1

/-- Exercise 13.6: rotation in an arbitrary point is rotation in the origin
followed by translation by the image of the origin. -/
theorem rotationInPoint_decomposition (center point : Point K) :
    rotateInPoint center point =
      translationPoint
        (rotateInPoint center planeOrigin).x
        (rotateInPoint center planeOrigin).y
        (rotateInPoint planeOrigin point) := by
  apply Point.ext <;>
    unfold rotateInPoint planeOrigin translationPoint <;>
    ring1

/-- Replace the constant term of a line by zero, producing the central line
`k ≡ ⟨a:b:0⟩` from Exercise 13.7. -/
def centralLine (line : Line K) : Line K where
  a := line.a
  b := line.b
  c := 0
  direction_nonzero := line.direction_nonzero

/-- Centralizing a line preserves its non-null direction pair. -/
theorem centralLine_nonNull (line : Line K) (nonNull : ¬ line.IsNull) :
    ¬ (centralLine line).IsNull := by
  intro centralNull
  apply nonNull
  exact centralNull

/-- The translation point `B = σ_l(O)` displayed in Exercise 13.7. -/
def reflectionTranslationPoint (line : Line K) : Point K :=
  ⟨(-2 * line.a * line.c) / lineNorm line,
    (-2 * line.b * line.c) / lineNorm line⟩

/-- Exercise 13.7: the printed formula for reflection in the associated
central line `k ≡ ⟨a:b:0⟩`. -/
theorem centralLine_reflection_formula (line : Line K)
    (nonNull : ¬ line.IsNull) (point : Point K) :
    reflectPoint (centralLine line) (centralLine_nonNull line nonNull) point =
      ⟨(((line.b ^ 2 - line.a ^ 2) * point.x -
          2 * line.a * line.b * point.y) / lineNorm line),
        ((-2 * line.a * line.b * point.x +
          (line.a ^ 2 - line.b ^ 2) * point.y) / lineNorm line)⟩ := by
  rw [reflectPoint_formula]
  apply Point.ext <;>
    simp only [reflectionFormula, centralLine, lineNorm, mul_zero, sub_zero]

/-- Exercise 13.7: reflection in `l` is reflection in its associated central
line followed by translation by `B = σ_l(O)`. -/
theorem lineReflection_decomposition (line : Line K)
    (nonNull : ¬ line.IsNull) (point : Point K) :
    reflectPoint line nonNull point =
      translationPoint
        (reflectionTranslationPoint line).x
        (reflectionTranslationPoint line).y
        (reflectPoint (centralLine line)
          (centralLine_nonNull line nonNull) point) := by
  rw [reflectPoint_formula, reflectPoint_formula]
  apply Point.ext <;>
    simp only [reflectionFormula, reflectionTranslationPoint, translationPoint,
      centralLine, lineNorm] <;>
    simp only [RFAP.ExplicitField.div_eq_mul_inv] <;>
    ring1

end DivineProportions
