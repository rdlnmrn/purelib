import FTA.SafeCandidates
import FTA.BoxGeometry

/-!
# Certified central-third box cuts

The safe-candidate search is lifted to vertical and horizontal box cuts.  A
successful search supplies the exact nonzero polynomial evaluation used by the
later resultant certificate, while the central-third location supplies closed
child boxes, refinement/cover properties, and the `2/3` side contraction from
Lemma 5.2.  Combining one cut in each direction contracts every child squared
diagonal by `4/9`.
-/

namespace FTA.SafeCuts

open CCL
open FTA.ComputablePolynomial
open FTA.SafeCandidates

abbrev RatPolynomial := ComputablePolynomial.DensePolynomial ℚ

theorem centralLeft_inside {a b : ℚ} (hab : a < b) :
    a < centralLeft a b := by
  dsimp [centralLeft]
  linarith

theorem centralRight_inside {a b : ℚ} (hab : a < b) :
    centralRight a b < b := by
  dsimp [centralRight]
  linarith

def verticalSearch (p : RatPolynomial) (B : RatBox) (D : ℕ) : Option ℚ :=
  centralSearch p B.xLower B.xUpper D

def horizontalSearch (p : RatPolynomial) (B : RatBox) (D : ℕ) : Option ℚ :=
  centralSearch p B.yLower B.yUpper D

theorem verticalSearch_succeeds (p : RatPolynomial) {B : RatBox} (D : ℕ)
    (hB : B.Proper) (hp : p.toPolynomial ≠ 0)
    (hdegree : p.toPolynomial.natDegree ≤ D) :
    ∃ c, verticalSearch p B D = some c :=
  centralSearch_succeeds p D hB.1 hp hdegree

theorem horizontalSearch_succeeds (p : RatPolynomial) {B : RatBox} (D : ℕ)
    (hB : B.Proper) (hp : p.toPolynomial ≠ 0)
    (hdegree : p.toPolynomial.natDegree ≤ D) :
    ∃ c, horizontalSearch p B D = some c :=
  centralSearch_succeeds p D hB.2 hp hdegree

theorem verticalSearch_some_spec {p : RatPolynomial} {B : RatBox} {D : ℕ}
    (hB : B.Proper) {c : ℚ} (hc : verticalSearch p B D = some c) :
    p.eval c ≠ 0 ∧ B.xLower < c ∧ c < B.xUpper ∧
      c - B.xLower < (2 / 3 : ℚ) * B.widthX ∧
      B.xUpper - c < (2 / 3 : ℚ) * B.widthX := by
  rcases centralSearch_some_spec hB.1 hc with ⟨-, hp, hleft, hright⟩
  have hxl : B.xLower < c := (centralLeft_inside hB.1).trans hleft
  have hxu : c < B.xUpper := hright.trans (centralRight_inside hB.1)
  dsimp [centralLeft] at hleft
  dsimp [centralRight] at hright
  dsimp [RatBox.widthX]
  exact ⟨hp, hxl, hxu, by linarith, by linarith⟩

theorem horizontalSearch_some_spec {p : RatPolynomial} {B : RatBox} {D : ℕ}
    (hB : B.Proper) {c : ℚ} (hc : horizontalSearch p B D = some c) :
    p.eval c ≠ 0 ∧ B.yLower < c ∧ c < B.yUpper ∧
      c - B.yLower < (2 / 3 : ℚ) * B.widthY ∧
      B.yUpper - c < (2 / 3 : ℚ) * B.widthY := by
  rcases centralSearch_some_spec hB.2 hc with ⟨-, hp, hleft, hright⟩
  have hyl : B.yLower < c := (centralLeft_inside hB.2).trans hleft
  have hyu : c < B.yUpper := hright.trans (centralRight_inside hB.2)
  dsimp [centralLeft] at hleft
  dsimp [centralRight] at hright
  dsimp [RatBox.widthY]
  exact ⟨hp, hyl, hyu, by linarith, by linarith⟩

theorem verticalLeft_widthX_lt {B : RatBox} {c : ℚ}
    (hc : B.xLower ≤ c ∧ c ≤ B.xUpper)
    (hcentral : c - B.xLower < (2 / 3 : ℚ) * B.widthX) :
    (B.verticalLeft c hc).widthX < (2 / 3 : ℚ) * B.widthX := by
  simpa [RatBox.verticalLeft, RatBox.widthX] using hcentral

theorem verticalRight_widthX_lt {B : RatBox} {c : ℚ}
    (hc : B.xLower ≤ c ∧ c ≤ B.xUpper)
    (hcentral : B.xUpper - c < (2 / 3 : ℚ) * B.widthX) :
    (B.verticalRight c hc).widthX < (2 / 3 : ℚ) * B.widthX := by
  simpa [RatBox.verticalRight, RatBox.widthX] using hcentral

theorem horizontalLower_widthY_lt {B : RatBox} {c : ℚ}
    (hc : B.yLower ≤ c ∧ c ≤ B.yUpper)
    (hcentral : c - B.yLower < (2 / 3 : ℚ) * B.widthY) :
    (B.horizontalLower c hc).widthY < (2 / 3 : ℚ) * B.widthY := by
  simpa [RatBox.horizontalLower, RatBox.widthY] using hcentral

theorem horizontalUpper_widthY_lt {B : RatBox} {c : ℚ}
    (hc : B.yLower ≤ c ∧ c ≤ B.yUpper)
    (hcentral : B.yUpper - c < (2 / 3 : ℚ) * B.widthY) :
    (B.horizontalUpper c hc).widthY < (2 / 3 : ℚ) * B.widthY := by
  simpa [RatBox.horizontalUpper, RatBox.widthY] using hcentral

/-- Scaling both nonnegative side lengths by at most `2/3` scales the squared
diagonal by at most `4/9`. -/
theorem diagonalSq_le_four_ninths {C B : RatBox}
    (hx : C.widthX ≤ (2 / 3 : ℚ) * B.widthX)
    (hy : C.widthY ≤ (2 / 3 : ℚ) * B.widthY) :
    C.diagonalSq ≤ (4 / 9 : ℚ) * B.diagonalSq := by
  have hCx := C.widthX_nonneg
  have hCy := C.widthY_nonneg
  have hBx := B.widthX_nonneg
  have hBy := B.widthY_nonneg
  have hsx : 0 ≤ (2 / 3 : ℚ) * B.widthX := mul_nonneg (by norm_num) hBx
  have hsy : 0 ≤ (2 / 3 : ℚ) * B.widthY := mul_nonneg (by norm_num) hBy
  have hxprod := mul_nonneg (sub_nonneg.mpr hx) (add_nonneg hCx hsx)
  have hyprod := mul_nonneg (sub_nonneg.mpr hy) (add_nonneg hCy hsy)
  rw [C.diagonalSq_eq, B.diagonalSq_eq]
  nlinarith

/-- One central vertical and one central horizontal cut produce four boxes;
each has squared diagonal at most `4/9` of the parent. -/
theorem four_child_diagonal_contraction {B : RatBox} {cx cy : ℚ}
    (hcx : B.xLower ≤ cx ∧ cx ≤ B.xUpper)
    (hcy : B.yLower ≤ cy ∧ cy ≤ B.yUpper)
    (hxl : cx - B.xLower ≤ (2 / 3 : ℚ) * B.widthX)
    (hxr : B.xUpper - cx ≤ (2 / 3 : ℚ) * B.widthX)
    (hyl : cy - B.yLower ≤ (2 / 3 : ℚ) * B.widthY)
    (hyu : B.yUpper - cy ≤ (2 / 3 : ℚ) * B.widthY) :
    let L := B.verticalLeft cx hcx
    let R := B.verticalRight cx hcx
    let hcyL : L.yLower ≤ cy ∧ cy ≤ L.yUpper := hcy
    let hcyR : R.yLower ≤ cy ∧ cy ≤ R.yUpper := hcy
    (L.horizontalLower cy hcyL).diagonalSq ≤ (4 / 9 : ℚ) * B.diagonalSq ∧
    (L.horizontalUpper cy hcyL).diagonalSq ≤ (4 / 9 : ℚ) * B.diagonalSq ∧
    (R.horizontalLower cy hcyR).diagonalSq ≤ (4 / 9 : ℚ) * B.diagonalSq ∧
    (R.horizontalUpper cy hcyR).diagonalSq ≤ (4 / 9 : ℚ) * B.diagonalSq := by
  dsimp only
  constructor
  · apply diagonalSq_le_four_ninths
    · simpa [RatBox.horizontalLower, RatBox.verticalLeft, RatBox.widthX]
        using hxl
    · simpa [RatBox.horizontalLower, RatBox.verticalLeft, RatBox.widthY]
        using hyl
  constructor
  · apply diagonalSq_le_four_ninths
    · simpa [RatBox.horizontalUpper, RatBox.verticalLeft, RatBox.widthX]
        using hxl
    · simpa [RatBox.horizontalUpper, RatBox.verticalLeft, RatBox.widthY]
        using hyu
  constructor
  · apply diagonalSq_le_four_ninths
    · simpa [RatBox.horizontalLower, RatBox.verticalRight, RatBox.widthX]
        using hxr
    · simpa [RatBox.horizontalLower, RatBox.verticalRight, RatBox.widthY]
        using hyl
  · apply diagonalSq_le_four_ninths
    · simpa [RatBox.horizontalUpper, RatBox.verticalRight, RatBox.widthX]
        using hxr
    · simpa [RatBox.horizontalUpper, RatBox.verticalRight, RatBox.widthY]
        using hyu

end FTA.SafeCuts
