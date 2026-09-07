import FTA.RootTrackSeparation

/-!
# Finite mesh packing of separated root tracks

This module formalizes Corollary 8.3.  A coefficient-computed square mesh of
the global rational square has finitely many cells.  Refining each
winding-one track below one quarter of the mesh side assigns it to the cell
containing its rational center.  Two tracks assigned to one cell would be
supported in a common box below the separation radius, contradicting
Theorem 8.2.  Finite pigeonhole induction therefore gives an explicit natural
packing bound.
-/

namespace FTA.FinitePacking

open CCL CCL.GaussianRat
open FTA.PathPolynomial
open FTA.LocalExtraction
open FTA.RootTrackSeparation
open FTA.GaussianDifferenceResultant

/-- A positive rational mesh side small enough that the coarse enlarged-cell
diagonal lies below `σ²`. -/
def meshSide (σ : ℚ) : ℚ := min 1 (σ / 4)

theorem meshSide_pos {σ : ℚ} (hσ : 0 < σ) : 0 < meshSide σ := by
  apply lt_min
  · norm_num
  · positivity

theorem eight_mul_meshSide_sq_lt {σ : ℚ} (hσ : 0 < σ) :
    8 * meshSide σ ^ 2 < σ ^ 2 := by
  have hsPos : 0 < meshSide σ := meshSide_pos hσ
  have hsLe : meshSide σ ≤ σ / 4 := min_le_right _ _
  have hfour : 4 * meshSide σ ≤ σ := by linarith
  have hproduct :
      0 ≤ (σ - 4 * meshSide σ) * (σ + 4 * meshSide σ) :=
    mul_nonneg (sub_nonneg.mpr hfour) (by positivity)
  nlinarith [sq_pos_of_pos hσ]

/-- Number of mesh intervals needed in one coordinate direction. -/
def meshIntervals (R σ : ℚ) : ℕ := ⌈2 * R / meshSide σ⌉₊

theorem mesh_covers_radius {R σ : ℚ} (_hR : 0 ≤ R) (hσ : 0 < σ) :
    2 * R ≤ (meshIntervals R σ : ℚ) * meshSide σ := by
  have hsPos : 0 < meshSide σ := meshSide_pos hσ
  have hceil := Nat.le_ceil (2 * R / meshSide σ)
  exact (div_le_iff₀ hsPos).mp hceil

/-- The explicit natural packing bound: one slot for every pair of coordinate
mesh indices. -/
def packingBound (R σ : ℚ) : ℕ := (meshIntervals R σ + 1) ^ 2

/-- Finite coordinate index of a point in the symmetric square.  The extra
last index handles points on the closed upper boundary. -/
def coordinateIndex
    (R σ : ℚ) (hR : 0 ≤ R) (hσ : 0 < σ)
    (x : ℚ) (_hxLower : -R ≤ x) (hxUpper : x ≤ R) :
    Fin (meshIntervals R σ + 1) :=
  ⟨⌊(x + R) / meshSide σ⌋₊, by
    apply Nat.lt_succ_of_le
    apply Nat.floor_le_of_le
    have hsPos : 0 < meshSide σ := meshSide_pos hσ
    rw [div_le_iff₀ hsPos]
    exact (by
      have hcover := mesh_covers_radius hR hσ
      exact (by linarith : x + R ≤
        (meshIntervals R σ : ℚ) * meshSide σ))⟩

/-- Pair of finite mesh indices for a point in the symmetric square. -/
def cellIndex
    (R σ : ℚ) (hR : 0 ≤ R) (hσ : 0 < σ)
    (z : QI) (hz : (CCL.RatBox.symmetric R hR).Contains z) :
    Fin (meshIntervals R σ + 1) × Fin (meshIntervals R σ + 1) :=
  (coordinateIndex R σ hR hσ z.re hz.1 hz.2.1,
    coordinateIndex R σ hR hσ z.im hz.2.2.1 hz.2.2.2)

theorem coordinate_mem_floor_cell
    {R σ x : ℚ} (hσ : 0 < σ) (hxLower : -R ≤ x) :
    -R + (⌊(x + R) / meshSide σ⌋₊ : ℚ) * meshSide σ ≤ x ∧
      x < -R + ((⌊(x + R) / meshSide σ⌋₊ : ℚ) + 1) *
        meshSide σ := by
  have hsPos : 0 < meshSide σ := meshSide_pos hσ
  have hquotientNonneg : 0 ≤ (x + R) / meshSide σ :=
    div_nonneg (by linarith) hsPos.le
  have hlower := Nat.floor_le hquotientNonneg
  have hupper := Nat.lt_floor_add_one ((x + R) / meshSide σ)
  constructor
  · have hscaled := (le_div_iff₀ hsPos).mp hlower
    linarith
  · have hscaled := (div_lt_iff₀ hsPos).mp hupper
    linarith

/-- Cell enlarged by one quarter mesh side in every coordinate. -/
def enlargedCell
    (R σ : ℚ) (hσ : 0 < σ)
    (i j : Fin (meshIntervals R σ + 1)) : CCL.RatBox where
  xLower := -R + (i : ℕ) * meshSide σ - meshSide σ / 4
  xUpper := -R + ((i : ℕ) + 1) * meshSide σ + meshSide σ / 4
  yLower := -R + (j : ℕ) * meshSide σ - meshSide σ / 4
  yUpper := -R + ((j : ℕ) + 1) * meshSide σ + meshSide σ / 4
  x_valid := by
    have := meshSide_pos hσ
    linarith
  y_valid := by
    have := meshSide_pos hσ
    linarith

theorem enlargedCell_diagonalSq_lt_eight_mul
    (R σ : ℚ) (hσ : 0 < σ)
    (i j : Fin (meshIntervals R σ + 1)) :
    (enlargedCell R σ hσ i j).diagonalSq < 8 * meshSide σ ^ 2 := by
  have hsPos := meshSide_pos hσ
  dsimp [enlargedCell, CCL.RatBox.diagonalSq]
  nlinarith [sq_pos_of_pos hsPos]

theorem widthX_le_quarter_meshSide_of_diagonal
    {σ : ℚ} (hσ : 0 < σ) {B : CCL.RatBox}
    (hdiagonal : B.diagonalSq ≤ (meshSide σ / 4) ^ 2) :
    B.widthX ≤ meshSide σ / 4 := by
  have hxNonneg := B.widthX_nonneg
  have hySqNonneg := sq_nonneg B.widthY
  have hsPos := meshSide_pos hσ
  rw [B.diagonalSq_eq] at hdiagonal
  nlinarith

theorem widthY_le_quarter_meshSide_of_diagonal
    {σ : ℚ} (hσ : 0 < σ) {B : CCL.RatBox}
    (hdiagonal : B.diagonalSq ≤ (meshSide σ / 4) ^ 2) :
    B.widthY ≤ meshSide σ / 4 := by
  have hyNonneg := B.widthY_nonneg
  have hxSqNonneg := sq_nonneg B.widthX
  have hsPos := meshSide_pos hσ
  rw [B.diagonalSq_eq] at hdiagonal
  nlinarith

/-- A sufficiently narrow box is contained in the enlarged cell assigned to
its center. -/
theorem box_refines_center_enlargedCell
    {R σ : ℚ} (hR : 0 ≤ R) (hσ : 0 < σ)
    (B : CCL.RatBox)
    (hcenter : (CCL.RatBox.symmetric R hR).Contains B.center)
    (hdiagonal : B.diagonalSq ≤ (meshSide σ / 4) ^ 2) :
    B.Refines (enlargedCell R σ hσ
      (cellIndex R σ hR hσ B.center hcenter).1
      (cellIndex R σ hR hσ B.center hcenter).2) := by
  have hxWidth := widthX_le_quarter_meshSide_of_diagonal hσ hdiagonal
  have hyWidth := widthY_le_quarter_meshSide_of_diagonal hσ hdiagonal
  have hxCell := coordinate_mem_floor_cell hσ hcenter.1
  have hyCell := coordinate_mem_floor_cell hσ hcenter.2.2.1
  rcases hxCell with ⟨hxCellLower, hxCellUpper⟩
  rcases hyCell with ⟨hyCellLower, hyCellUpper⟩
  dsimp [enlargedCell, cellIndex, coordinateIndex]
  constructor
  · dsimp [CCL.RatBox.center, CCL.RatBox.widthX] at hxCellLower hxWidth
    linarith
  constructor
  · dsimp [CCL.RatBox.center, CCL.RatBox.widthX] at hxCellUpper hxWidth
    push_cast
    linarith
  constructor
  · dsimp [CCL.RatBox.center, CCL.RatBox.widthY] at hyCellLower hyWidth
    linarith
  · dsimp [CCL.RatBox.center, CCL.RatBox.widthY] at hyCellUpper hyWidth
    push_cast
    linarith

/-- Corollary 8.3: every finite pairwise separated family of nonterminal
winding-one tracks in the global square is bounded by the explicit mesh cell
count. -/
theorem finite_family_card_le_packingBound
    (p : GaussianPolynomial) (R : ℚ) (hR : 0 ≤ R)
    (squarefree : GaussianSquarefreeCertificate p)
    (hdegree : p.toPolynomial.natDegree ≠ 0)
    {count : ℕ}
    (tracks : Fin count →
      WindingOneTrack p (CCL.RatBox.symmetric R hR))
    (states : (i : Fin count) →
      WindingOneState p (CCL.RatBox.symmetric R hR))
    (pairwiseSeparated : ∀ i j, i ≠ j →
      (states i).box.Separated (states j).box) :
    count ≤ packingBound R
      (squarefreeSeparationRadius
        (sparseSquarefreeCertificate squarefree)) := by
  let sparseCertificate := sparseSquarefreeCertificate squarefree
  let σ := squarefreeSeparationRadius sparseCertificate
  have hσ : 0 < σ := squarefreeSeparationRadius_pos sparseCertificate
  let ε := meshSide σ / 4
  have hε : 0 < ε := div_pos (meshSide_pos hσ) (by norm_num)
  let refined : (i : Fin count) →
      WindingOneState p (CCL.RatBox.symmetric R hR) :=
    fun i => (tracks i).refine (states i) ε hε
  have hrefinedDiagonal (i : Fin count) :
      (refined i).box.diagonalSq ≤ (meshSide σ / 4) ^ 2 := by
    exact (tracks i).accurate (states i) ε hε
  have hrefinedCenter (i : Fin count) :
      (CCL.RatBox.symmetric R hR).Contains (refined i).box.center :=
    (refined i).refinesAmbient.contains (refined i).box.contains_center
  let cell : Fin count →
      Fin (meshIntervals R σ + 1) × Fin (meshIntervals R σ + 1) :=
    fun i => cellIndex R σ hR hσ (refined i).box.center
      (hrefinedCenter i)
  have hcellInjective : Function.Injective cell := by
    intro i j hij
    by_contra hne
    have hsepOriginal := pairwiseSeparated i j hne
    have hsepRefined := hsepOriginal.of_refines
      ((tracks i).nested (states i) ε hε)
      ((tracks j).nested (states j) ε hε)
    have hfirst : (cell i).1 = (cell j).1 := congrArg Prod.fst hij
    have hsecond : (cell i).2 = (cell j).2 := congrArg Prod.snd hij
    let common := enlargedCell R σ hσ (cell i).1 (cell i).2
    have hiCommon : (refined i).box.Refines common := by
      have h := box_refines_center_enlargedCell hR hσ (refined i).box
        (hrefinedCenter i) (hrefinedDiagonal i)
      simpa only [cell, common] using h
    have hjCommon : (refined j).box.Refines common := by
      have h := box_refines_center_enlargedCell hR hσ (refined j).box
        (hrefinedCenter j) (hrefinedDiagonal j)
      rw [← hfirst, ← hsecond] at h
      simpa only [cell, common] using h
    have hcommonSmall : common.diagonalSq < σ ^ 2 :=
      (enlargedCell_diagonalSq_lt_eight_mul R σ hσ
        (cell i).1 (cell i).2).trans (eight_mul_meshSide_sq_lt hσ)
    exact separated_tracks_not_supported_in_small_common_box
      p (CCL.RatBox.symmetric R hR) squarefree hdegree
      (tracks i) (tracks j) (refined i) (refined j) hsepRefined
      common hiCommon hjCommon hcommonSmall
  have hcard := Fintype.card_le_of_injective cell hcellInjective
  simpa [Fintype.card_prod, packingBound, pow_two, σ,
    sparseCertificate] using hcard

end FTA.FinitePacking
