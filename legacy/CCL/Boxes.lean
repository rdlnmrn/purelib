import CCL.Gaussian
import CCL.Prefix
import CCL.Geometry.Projective

/-!
# Rational boxes and operational boxed names

Formal finite data for Section 7.4.  A `ProgressiveName` is a total Lean
function answering one requested positive rational accuracy at a time; it does
not contain, or assert the existence of, a completed infinite stream or point.
-/

namespace CCL

open GaussianRat

/-- An axis-aligned rational box with certified endpoint order. -/
structure RatBox where
  xLower : ℚ
  xUpper : ℚ
  yLower : ℚ
  yUpper : ℚ
  x_valid : xLower ≤ xUpper
  y_valid : yLower ≤ yUpper
deriving Repr

namespace RatBox

/-- Exact rational box membership. -/
def Contains (B : RatBox) (z : GaussianRat) : Prop :=
  B.xLower ≤ z.re ∧ z.re ≤ B.xUpper ∧
  B.yLower ≤ z.im ∧ z.im ≤ B.yUpper

instance containsDecidable (B : RatBox) (z : GaussianRat) :
    Decidable (B.Contains z) := by
  unfold Contains
  infer_instance

/-- Strict membership in all four rational sides. -/
def StrictContains (B : RatBox) (z : GaussianRat) : Prop :=
  B.xLower < z.re ∧ z.re < B.xUpper ∧
  B.yLower < z.im ∧ z.im < B.yUpper

theorem StrictContains.contains {B : RatBox} {z : GaussianRat}
    (strict : B.StrictContains z) : B.Contains z :=
  ⟨strict.1.le, strict.2.1.le, strict.2.2.1.le, strict.2.2.2.le⟩

/-- The rational squared diagonal `Δ²(B)`. -/
def diagonalSq (B : RatBox) : ℚ :=
  (B.xUpper - B.xLower) ^ 2 + (B.yUpper - B.yLower) ^ 2

/-- `C ⊑ B`: all four rational endpoint comparisons. -/
def Refines (C B : RatBox) : Prop :=
  B.xLower ≤ C.xLower ∧ C.xUpper ≤ B.xUpper ∧
  B.yLower ≤ C.yLower ∧ C.yUpper ≤ B.yUpper

theorem refines_refl (B : RatBox) : B.Refines B := by
  exact ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩

theorem Refines.trans {A B C : RatBox} (hAB : A.Refines B) (hBC : B.Refines C) :
    A.Refines C := by
  rcases hAB with ⟨hx₀, hx₁, hy₀, hy₁⟩
  rcases hBC with ⟨hx₀', hx₁', hy₀', hy₁'⟩
  exact ⟨hx₀'.trans hx₀, hx₁.trans hx₁', hy₀'.trans hy₀, hy₁.trans hy₁'⟩

theorem Refines.contains {C B : RatBox} {z : GaussianRat}
    (hCB : C.Refines B) (hz : C.Contains z) : B.Contains z := by
  rcases hCB with ⟨hx₀, hx₁, hy₀, hy₁⟩
  rcases hz with ⟨hzx₀, hzx₁, hzy₀, hzy₁⟩
  exact ⟨hx₀.trans hzx₀, hzx₁.trans hx₁, hy₀.trans hzy₀, hzy₁.trans hy₁⟩

theorem diagonalSq_nonneg (B : RatBox) : 0 ≤ B.diagonalSq := by
  dsimp [diagonalSq]
  positivity

/-- The symmetric box `[-R,R] × [-R,R]`. -/
def symmetric (R : ℚ) (hR : 0 ≤ R) : RatBox where
  xLower := -R
  xUpper := R
  yLower := -R
  yUpper := R
  x_valid := by linarith
  y_valid := by linarith

/-- A finite rational absolute-coordinate bound for a box. -/
def coordinateRadius (B : RatBox) : ℚ :=
  max (max |B.xLower| |B.xUpper|) (max |B.yLower| |B.yUpper|)

theorem coordinateRadius_nonneg (B : RatBox) : 0 ≤ B.coordinateRadius := by
  exact le_max_of_le_left (le_max_of_le_left (abs_nonneg _))

theorem abs_coordinates_le_radius {B : RatBox} {z : GaussianRat}
    (hz : B.Contains z) :
    |z.re| ≤ B.coordinateRadius ∧ |z.im| ≤ B.coordinateRadius := by
  rcases hz with ⟨hx₀, hx₁, hy₀, hy₁⟩
  have hxl : |B.xLower| ≤ B.coordinateRadius :=
    (le_max_left _ _).trans (le_max_left _ _)
  have hxu : |B.xUpper| ≤ B.coordinateRadius :=
    (le_max_right _ _).trans (le_max_left _ _)
  have hyl : |B.yLower| ≤ B.coordinateRadius :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hyu : |B.yUpper| ≤ B.coordinateRadius :=
    (le_max_right _ _).trans (le_max_right _ _)
  rcases (abs_le.mp hxl) with ⟨hxl₀, hxl₁⟩
  rcases (abs_le.mp hxu) with ⟨hxu₀, hxu₁⟩
  rcases (abs_le.mp hyl) with ⟨hyl₀, hyl₁⟩
  rcases (abs_le.mp hyu) with ⟨hyu₀, hyu₁⟩
  constructor
  · exact abs_le.mpr ⟨hxl₀.trans hx₀, hx₁.trans hxu₁⟩
  · exact abs_le.mpr ⟨hyl₀.trans hy₀, hy₁.trans hyu₁⟩

/-- Coordinate bounds for the affine numerator `az+b`. -/
def affineRealBound (a b : GaussianRat) (B : RatBox) : ℚ :=
  (|a.re| + |a.im|) * B.coordinateRadius + |b.re|

def affineImagBound (a b : GaussianRat) (B : RatBox) : ℚ :=
  (|a.re| + |a.im|) * B.coordinateRadius + |b.im|

/-- A finite rational squared-norm bound for `az+b` over `B`. -/
def affineNormBound (a b : GaussianRat) (B : RatBox) : ℚ :=
  affineRealBound a b B ^ 2 + affineImagBound a b B ^ 2

theorem affineRealBound_nonneg (a b : GaussianRat) (B : RatBox) :
    0 ≤ affineRealBound a b B := by
  dsimp [affineRealBound]
  exact add_nonneg
    (mul_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) B.coordinateRadius_nonneg)
    (abs_nonneg _)

theorem affineImagBound_nonneg (a b : GaussianRat) (B : RatBox) :
    0 ≤ affineImagBound a b B := by
  dsimp [affineImagBound]
  exact add_nonneg
    (mul_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) B.coordinateRadius_nonneg)
    (abs_nonneg _)

theorem affineNormBound_nonneg (a b : GaussianRat) (B : RatBox) :
    0 ≤ affineNormBound a b B := by
  dsimp [affineNormBound]
  positivity

theorem normSq_affine_le_bound (a b : GaussianRat) {B : RatBox} {z : GaussianRat}
    (hz : B.Contains z) : normSq (a * z + b) ≤ affineNormBound a b B := by
  rcases abs_coordinates_le_radius hz with ⟨hx, hy⟩
  have har : |a.re * z.re| ≤ |a.re| * B.coordinateRadius := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)
  have hai : |a.im * z.im| ≤ |a.im| * B.coordinateRadius := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hy (abs_nonneg _)
  have hay : |a.re * z.im| ≤ |a.re| * B.coordinateRadius := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hy (abs_nonneg _)
  have hax : |a.im * z.re| ≤ |a.im| * B.coordinateRadius := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)
  have hre : |(a * z + b).re| ≤ affineRealBound a b B := by
    calc
      |(a * z + b).re| = |a.re * z.re - a.im * z.im + b.re| := rfl
      _ ≤ |a.re * z.re - a.im * z.im| + |b.re| := abs_add_le _ _
      _ ≤ (|a.re * z.re| + |a.im * z.im|) + |b.re| := by
        gcongr
        exact abs_sub _ _
      _ ≤ (|a.re| * B.coordinateRadius + |a.im| * B.coordinateRadius) +
          |b.re| := by gcongr
      _ = affineRealBound a b B := by
        dsimp [affineRealBound]
        ring
  have him : |(a * z + b).im| ≤ affineImagBound a b B := by
    calc
      |(a * z + b).im| = |a.re * z.im + a.im * z.re + b.im| := rfl
      _ ≤ |a.re * z.im + a.im * z.re| + |b.im| := abs_add_le _ _
      _ ≤ (|a.re * z.im| + |a.im * z.re|) + |b.im| := by
        gcongr
        exact abs_add_le _ _
      _ ≤ (|a.re| * B.coordinateRadius + |a.im| * B.coordinateRadius) +
          |b.im| := by gcongr
      _ = affineImagBound a b B := by
        dsimp [affineImagBound]
        ring
  have hreSq : (a * z + b).re ^ 2 ≤ affineRealBound a b B ^ 2 := by
    have hp := mul_nonneg (sub_nonneg.mpr hre)
      (add_nonneg (abs_nonneg (a * z + b).re) (affineRealBound_nonneg a b B))
    have habs : |(a * z + b).re| ^ 2 = (a * z + b).re ^ 2 := sq_abs _
    nlinarith
  have himSq : (a * z + b).im ^ 2 ≤ affineImagBound a b B ^ 2 := by
    have hp := mul_nonneg (sub_nonneg.mpr him)
      (add_nonneg (abs_nonneg (a * z + b).im) (affineImagBound_nonneg a b B))
    have habs : |(a * z + b).im| ^ 2 = (a * z + b).im ^ 2 := sq_abs _
    nlinarith
  exact add_le_add hreSq himSq

/-- Exact affine homographic evaluation used by Lemma 7.5. -/
def homographic (M : Mat2 GaussianRat) (t : GaussianRat) : GaussianRat :=
  (M.a * t + M.b) * inv (M.c * t + M.d)

/-- A computable output radius for rational box transport. -/
def transportRadius (M : Mat2 GaussianRat) (T : RatBox) (δ : ℚ) : ℚ :=
  affineNormBound M.a M.b T / δ + 1

/-- The concrete rational box computed by the transport lemma. -/
def transport (M : Mat2 GaussianRat) (T : RatBox) (δ : ℚ) (hδ : 0 < δ) : RatBox :=
  symmetric (transportRadius M T δ) (by
    dsimp [transportRadius]
    exact add_nonneg
      (div_nonneg (affineNormBound_nonneg M.a M.b T) hδ.le) (by norm_num))

/-- A norm upper bound gives the paper's coarse symmetric enclosure. -/
theorem contains_symmetric_of_norm_lt {z : GaussianRat} {R : ℚ}
    (hR : 1 ≤ R) (hz : normSq z < R) : (symmetric R (by linarith)).Contains z := by
  have hxUpper : z.re ≤ R := by
    by_contra h
    have hprod : 0 ≤ z.re * (z.re - R) :=
      mul_nonneg (by linarith) (by linarith)
    dsimp [normSq] at hz
    nlinarith [sq_nonneg z.im]
  have hxLower : -R ≤ z.re := by
    by_contra h
    have hprod : 0 ≤ (-z.re) * (-z.re - R) :=
      mul_nonneg (by linarith) (by linarith)
    dsimp [normSq] at hz
    nlinarith [sq_nonneg z.im]
  have hyUpper : z.im ≤ R := by
    by_contra h
    have hprod : 0 ≤ z.im * (z.im - R) :=
      mul_nonneg (by linarith) (by linarith)
    dsimp [normSq] at hz
    nlinarith [sq_nonneg z.re]
  have hyLower : -R ≤ z.im := by
    by_contra h
    have hprod : 0 ≤ (-z.im) * (-z.im - R) :=
      mul_nonneg (by linarith) (by linarith)
    dsimp [normSq] at hz
    nlinarith [sq_nonneg z.re]
  exact ⟨hxLower, hxUpper, hyLower, hyUpper⟩

/-- Lemma 7.5: finite rational data computes a sound box for a homographic
image whenever the denominator norm has a positive rational separation. -/
theorem transport_contains (M : Mat2 GaussianRat) (T : RatBox) (δ : ℚ)
    (hδ : 0 < δ) {t : GaussianRat} (ht : T.Contains t)
    (hsep : δ ≤ normSq (M.c * t + M.d)) :
    (transport M T δ hδ).Contains (homographic M t) := by
  let num := M.a * t + M.b
  let den := M.c * t + M.d
  let U := affineNormBound M.a M.b T
  have hU : 0 ≤ U := affineNormBound_nonneg M.a M.b T
  have hnum : normSq num ≤ U := normSq_affine_le_bound M.a M.b ht
  have hdenPos : 0 < normSq den := hδ.trans_le hsep
  have hden : den ≠ 0 := by
    intro h
    rw [h, normSq_zero] at hdenPos
    linarith
  have hcross : normSq num * δ ≤ U * normSq den := by
    calc
      normSq num * δ ≤ U * δ := mul_le_mul_of_nonneg_right hnum hδ.le
      _ ≤ U * normSq den := mul_le_mul_of_nonneg_left hsep hU
  have hratio : normSq num / normSq den ≤ U / δ :=
    (div_le_div_iff₀ hdenPos hδ).2 hcross
  apply contains_symmetric_of_norm_lt
  · dsimp [transport, transportRadius]
    have : 0 ≤ affineNormBound M.a M.b T / δ := div_nonneg hU hδ.le
    linarith
  · rw [homographic, normSq_mul, normSq_inv _ hden]
    rw [div_eq_mul_inv] at hratio
    dsimp only [num, den, U] at hratio
    dsimp only [den, transportRadius]
    simp only [one_div]
    exact hratio.trans_lt (lt_add_of_pos_right _ zero_lt_one)

/-- Coordinatewise intersection, made constructively nonempty by a witness in both boxes. -/
def intersect (B C : RatBox) (q : GaussianRat)
    (hB : B.Contains q) (hC : C.Contains q) : RatBox where
  xLower := max B.xLower C.xLower
  xUpper := min B.xUpper C.xUpper
  yLower := max B.yLower C.yLower
  yUpper := min B.yUpper C.yUpper
  x_valid := by
    rcases hB with ⟨hBx₀, hBx₁, -, -⟩
    rcases hC with ⟨hCx₀, hCx₁, -, -⟩
    exact (max_le hBx₀ hCx₀).trans (le_min hBx₁ hCx₁)
  y_valid := by
    rcases hB with ⟨-, -, hBy₀, hBy₁⟩
    rcases hC with ⟨-, -, hCy₀, hCy₁⟩
    exact (max_le hBy₀ hCy₀).trans (le_min hBy₁ hCy₁)

theorem intersect_contains (B C : RatBox) (q : GaussianRat)
    (hB : B.Contains q) (hC : C.Contains q) :
    (intersect B C q hB hC).Contains q := by
  rcases hB with ⟨hBx₀, hBx₁, hBy₀, hBy₁⟩
  rcases hC with ⟨hCx₀, hCx₁, hCy₀, hCy₁⟩
  exact ⟨max_le hBx₀ hCx₀, le_min hBx₁ hCx₁,
    max_le hBy₀ hCy₀, le_min hBy₁ hCy₁⟩

theorem intersect_refines_left (B C : RatBox) (q : GaussianRat)
    (hB : B.Contains q) (hC : C.Contains q) :
    (intersect B C q hB hC).Refines B := by
  exact ⟨le_max_left _ _, min_le_left _ _, le_max_left _ _, min_le_left _ _⟩

theorem intersect_refines_right (B C : RatBox) (q : GaussianRat)
    (hB : B.Contains q) (hC : C.Contains q) :
    (intersect B C q hB hC).Refines C := by
  exact ⟨le_max_right _ _, min_le_right _ _, le_max_right _ _, min_le_right _ _⟩

/-- Equation (7.8): two points in one box differ by at most its squared diagonal. -/
theorem normSq_sub_le_diagonalSq {B : RatBox} {z w : GaussianRat}
    (hz : B.Contains z) (hw : B.Contains w) :
    normSq (z - w) ≤ B.diagonalSq := by
  rcases hz with ⟨hzx₀, hzx₁, hzy₀, hzy₁⟩
  rcases hw with ⟨hwx₀, hwx₁, hwy₀, hwy₁⟩
  have hx₀ : -(B.xUpper - B.xLower) ≤ z.re - w.re := by linarith
  have hx₁ : z.re - w.re ≤ B.xUpper - B.xLower := by linarith
  have hy₀ : -(B.yUpper - B.yLower) ≤ z.im - w.im := by linarith
  have hy₁ : z.im - w.im ≤ B.yUpper - B.yLower := by linarith
  have hxprod : 0 ≤ (B.xUpper - B.xLower - (z.re - w.re)) *
      (B.xUpper - B.xLower + (z.re - w.re)) :=
    mul_nonneg (by linarith) (by linarith)
  have hyprod : 0 ≤ (B.yUpper - B.yLower - (z.im - w.im)) *
      (B.yUpper - B.yLower + (z.im - w.im)) :=
    mul_nonneg (by linarith) (by linarith)
  dsimp [normSq, diagonalSq]
  nlinarith

end RatBox

/-- A finite cylinder predicate together with prefix monotonicity (7.6). -/
structure CylinderSystem where
  Holds : Prefix.Word → GaussianRat → Prop
  prefix_mono : ∀ {w v z}, w <+: v → Holds v z → Holds w z

/-- Definition 7.4, including the required nonzero rational witness. -/
structure BoxedCertificate (C : CylinderSystem) where
  word : Prefix.Word
  box : RatBox
  witness : GaussianRat
  witness_ne : witness ≠ 0
  witness_compatible : C.Holds word witness
  sound : ∀ z, z ≠ 0 → C.Holds word z → box.Contains z

namespace BoxedCertificate

/-- Finite refinement of boxed prefix certificates. -/
def Refines {C : CylinderSystem} (new old : BoxedCertificate C) : Prop :=
  old.word <+: new.word ∧ new.box.Refines old.box

theorem witness_in_box {C : CylinderSystem} (c : BoxedCertificate C) :
    c.box.Contains c.witness :=
  c.sound c.witness c.witness_ne c.witness_compatible

theorem old_contains_new_witness {C : CylinderSystem}
    {new old : BoxedCertificate C} (h : new.Refines old) :
    old.box.Contains new.witness := by
  apply old.sound new.witness new.witness_ne
  exact C.prefix_mono h.1 new.witness_compatible

/-- The certified Cauchy step bound (7.8) for a refinement. -/
theorem witness_step_bound {C : CylinderSystem}
    {new old : BoxedCertificate C} (h : new.Refines old) :
    normSq (new.witness - old.witness) ≤ old.box.diagonalSq :=
  RatBox.normSq_sub_le_diagonalSq (old_contains_new_witness h) old.witness_in_box

end BoxedCertificate

/-- Definition 7.6 as a total finite-precision interface. -/
structure ProgressiveName (C : CylinderSystem) where
  initial : BoxedCertificate C
  refine : (current : BoxedCertificate C) → (ε : ℚ) → 0 < ε → BoxedCertificate C
  refines : ∀ current ε hε, (refine current ε hε).Refines current
  accurate : ∀ current ε hε, (refine current ε hε).box.diagonalSq ≤ ε ^ 2

end CCL
