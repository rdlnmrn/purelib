import CCL.Gaussian

/-!
# The finite eight-sector table

Formalization of (6.1), Lemma 6.1, and Lemma 6.2.  Selection is a deterministic
nest of rational comparisons.  The contraction proof has exactly the two
canonical polynomial cases from the paper; the other six cases are finite
coordinate/sign symmetries.
-/

namespace CCL

open GaussianRat

/-- The eight entries of the sector table, in the paper's displayed order. -/
inductive Sector where
  | east | northEast | north | northWest
  | west | southWest | south | southEast
deriving DecidableEq, Repr

namespace Sector

/-- The three raw bits attached to a sector representative. -/
def code : Sector → List Bool
  | east => [false, false, false]
  | northEast => [false, false, true]
  | north => [false, true, false]
  | northWest => [false, true, true]
  | west => [true, false, false]
  | southWest => [true, false, true]
  | south => [true, true, false]
  | southEast => [true, true, true]

@[simp] theorem code_length (s : Sector) : s.code.length = 3 := by cases s <;> rfl

/-- The Gaussian-rational representative selected by a row. -/
def rep : Sector → GaussianRat
  | east => ⟨1, 0⟩
  | northEast => ⟨1, 1⟩
  | north => ⟨0, 1⟩
  | northWest => ⟨-1, 1⟩
  | west => ⟨-1, 0⟩
  | southWest => ⟨-1, -1⟩
  | south => ⟨0, -1⟩
  | southEast => ⟨1, -1⟩

/-- The exact rational predicate in the corresponding row of table (6.1). -/
def Holds : Sector → GaussianRat → Prop
  | east, z => 1 / 2 ≤ z.re ∧ -1 / 2 < z.im ∧ z.im < 1 / 2
  | northEast, z => 1 / 2 ≤ z.re ∧ 1 / 2 ≤ z.im
  | north, z => -1 / 2 < z.re ∧ z.re < 1 / 2 ∧ 1 / 2 ≤ z.im
  | northWest, z => z.re ≤ -1 / 2 ∧ 1 / 2 ≤ z.im
  | west, z => z.re ≤ -1 / 2 ∧ -1 / 2 < z.im ∧ z.im < 1 / 2
  | southWest, z => z.re ≤ -1 / 2 ∧ z.im ≤ -1 / 2
  | south, z => -1 / 2 < z.re ∧ z.re < 1 / 2 ∧ z.im ≤ -1 / 2
  | southEast, z => 1 / 2 ≤ z.re ∧ z.im ≤ -1 / 2

/-- Deterministic sector selection by the boundary convention in (6.1). -/
def select (z : GaussianRat) : Sector :=
  if 1 / 2 ≤ z.re then
    if 1 / 2 ≤ z.im then northEast
    else if z.im ≤ -1 / 2 then southEast
    else east
  else if z.re ≤ -1 / 2 then
    if 1 / 2 ≤ z.im then northWest
    else if z.im ≤ -1 / 2 then southWest
    else west
  else if 1 / 2 ≤ z.im then north
  else if z.im ≤ -1 / 2 then south
  else east

/-- The three named norm predicates from Section 6.1. -/
def Band (z : GaussianRat) : Prop := 1 ≤ normSq z ∧ normSq z ≤ 2
def Entry (z : GaussianRat) : Prop := 1 ≤ normSq z ∧ normSq z < 2
def Loop (z : GaussianRat) : Prop := 1 < normSq z ∧ normSq z ≤ 2

private theorem norm_lt_one_of_central (z : GaussianRat)
    (hx₀ : -1 / 2 < z.re) (hx₁ : z.re < 1 / 2)
    (hy₀ : -1 / 2 < z.im) (hy₁ : z.im < 1 / 2) : normSq z < 1 := by
  have hx : 0 < (z.re + 1 / 2) * (1 / 2 - z.re) :=
    mul_pos (by linarith) (by linarith)
  have hy : 0 < (z.im + 1 / 2) * (1 / 2 - z.im) :=
    mul_pos (by linarith) (by linarith)
  dsimp [normSq]
  nlinarith

/-- Lemma 6.1, existence: the selected row holds whenever `N(z) ≥ 1`. -/
theorem select_spec (z : GaussianRat) (hz : 1 ≤ normSq z) : Holds (select z) z := by
  unfold select
  split_ifs <;> simp_all [Holds]
  exfalso
  apply (not_lt_of_ge hz)
  apply norm_lt_one_of_central z <;> linarith

/-- Lemma 6.1, uniqueness: two rows cannot hold simultaneously. -/
theorem holds_unique {r s : Sector} {z : GaussianRat}
    (hr : Holds r z) (hs : Holds s z) : r = s := by
  cases r <;> cases s <;> simp_all only [Holds]
  all_goals exfalso; linarith

/-- Lemma 6.1 in exactly-one form. -/
theorem partition (z : GaussianRat) (hz : 1 ≤ normSq z) :
    ∃! s : Sector, Holds s z := by
  refine ⟨select z, select_spec z hz, ?_⟩
  intro s hs
  exact holds_unique hs (select_spec z hz)

private theorem axial_contraction (x y : ℚ)
    (hx : 1 / 2 ≤ x) (hy₀ : -1 / 2 < y) (hy₁ : y < 1 / 2)
    (hn : x ^ 2 + y ^ 2 ≤ 2) : (x - 1) ^ 2 + y ^ 2 < 1 / 2 := by
  have hxlt : x < 3 / 2 := by
    by_contra h
    have hx0 : 0 ≤ x := by linarith
    have hprod : 0 ≤ x * (x - 3 / 2) :=
      mul_nonneg hx0 (by linarith)
    nlinarith [sq_nonneg y]
  have hxb : 0 ≤ (x - 1 / 2) * (3 / 2 - x) :=
    mul_nonneg (by linarith) (by linarith)
  have hyb : 0 < (y + 1 / 2) * (1 / 2 - y) :=
    mul_pos (by linarith) (by linarith)
  nlinarith

private theorem diagonal_contraction (x y : ℚ)
    (hx : 1 / 2 ≤ x) (hy : 1 / 2 ≤ y)
    (hn₀ : 1 ≤ x ^ 2 + y ^ 2) (hn₁ : x ^ 2 + y ^ 2 ≤ 2) :
    (x - 1) ^ 2 + (y - 1) ^ 2 < 1 / 2 := by
  let a := x - 1 / 2
  let b := y - 1 / 2
  let p := a + b
  let q := a ^ 2 + b ^ 2
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hb : 0 ≤ b := by dsimp [b]; linarith
  have hpq₀ : 1 / 2 ≤ p + q := by
    dsimp [p, q, a, b]
    nlinarith
  have hpq₁ : p + q ≤ 3 / 2 := by
    dsimp [p, q, a, b]
    nlinarith
  have hqle : q ≤ p ^ 2 := by
    dsimp [q, p]
    nlinarith [mul_nonneg ha hb]
  have hp : 0 < p := by
    by_contra h
    have hp0 : p = 0 := le_antisymm (le_of_not_gt h) (by
      dsimp [p]
      linarith)
    have ha0 : a = 0 := by dsimp [p] at hp0; linarith
    have hb0 : b = 0 := by dsimp [p] at hp0; linarith
    dsimp [q] at hpq₀
    nlinarith
  have hqp : q < p := by
    by_contra h
    have hpq : p ≤ q := le_of_not_gt h
    have hp1 : 1 ≤ p := by
      by_contra h'
      have hplt : p < 1 := lt_of_not_ge h'
      have hmul : p ^ 2 < p := by
        nlinarith [mul_pos hp (sub_pos.mpr hplt)]
      nlinarith
    nlinarith
  dsimp [p, q, a, b] at hqp
  nlinarith

/-- Lemma 6.2: the chosen representative contracts the whole closed band. -/
theorem contraction {z : GaussianRat} (hz : Band z) (s : Sector)
    (hs : Holds s z) : normSq (z - rep s) < 1 / 2 := by
  rcases hz with ⟨hz₀, hz₁⟩
  cases s with
  | east =>
      rcases hs with ⟨hx, hy₀, hy₁⟩
      have h := axial_contraction z.re z.im hx hy₀ hy₁ hz₁
      simp only [normSq, sub_re, sub_im, rep]
      nlinarith
  | northEast =>
      rcases hs with ⟨hx, hy⟩
      have h := diagonal_contraction z.re z.im hx hy hz₀ hz₁
      simpa only [normSq, sub_re, sub_im, rep] using h
  | north =>
      rcases hs with ⟨hx₀, hx₁, hy⟩
      have h := axial_contraction z.im (-z.re) hy (by linarith) (by linarith) (by
        dsimp [normSq] at hz₁
        nlinarith)
      simp only [normSq, sub_re, sub_im, rep]
      nlinarith
  | northWest =>
      rcases hs with ⟨hx, hy⟩
      have h := diagonal_contraction z.im (-z.re) hy (by linarith) (by
        dsimp [normSq] at hz₀
        nlinarith) (by
        dsimp [normSq] at hz₁
        nlinarith)
      simp only [normSq, sub_re, sub_im, rep]
      nlinarith
  | west =>
      rcases hs with ⟨hx, hy₀, hy₁⟩
      have h := axial_contraction (-z.re) (-z.im) (by linarith) (by linarith)
        (by linarith) (by
          dsimp [normSq] at hz₁
          nlinarith)
      simp only [normSq, sub_re, sub_im, rep]
      nlinarith
  | southWest =>
      rcases hs with ⟨hx, hy⟩
      have h := diagonal_contraction (-z.re) (-z.im) (by linarith) (by linarith)
        (by dsimp [normSq] at hz₀; nlinarith)
        (by dsimp [normSq] at hz₁; nlinarith)
      simp only [normSq, sub_re, sub_im, rep]
      nlinarith
  | south =>
      rcases hs with ⟨hx₀, hx₁, hy⟩
      have h := axial_contraction (-z.im) z.re (by linarith) hx₀ hx₁ (by
        dsimp [normSq] at hz₁
        nlinarith)
      simp only [normSq, sub_re, sub_im, rep]
      nlinarith
  | southEast =>
      rcases hs with ⟨hx, hy⟩
      have h := diagonal_contraction (-z.im) z.re (by linarith) hx (by
        dsimp [normSq] at hz₀
        nlinarith) (by
        dsimp [normSq] at hz₁
        nlinarith)
      simp only [normSq, sub_re, sub_im, rep]
      nlinarith

/-- Lemma 6.2 specialized to the deterministic table selector. -/
theorem select_contraction {z : GaussianRat} (hz : Band z) :
    normSq (z - rep (select z)) < 1 / 2 :=
  contraction hz (select z) (select_spec z hz.1)

end Sector

end CCL
