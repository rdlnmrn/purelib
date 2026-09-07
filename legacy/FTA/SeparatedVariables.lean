import FTA.FiniteResultant

/-!
# Nonvanishing for separated-variable resultants

This module isolates the algebraic core of the safe-axis resultant argument.
For nonconstant polynomials `p(Z)` and `q(W)` over a characteristic-zero
field, regard `Z` as the main variable and put `W = 2T-Z`.  Their Sylvester
resultant in `Z` is a nonzero polynomial in the remaining parameter `T`.

The proof reads the coefficient of degree `deg(p) * deg(q)` directly from the
finite Sylvester determinant.  The first block contributes the top coefficient
of `q(2T-Z)` and the second contributes the leading coefficient of `p`; the
resulting coefficient matrix is triangular with a nonzero diagonal.  No roots,
splitting field, or infinite carrier enters the proof.
-/

namespace FTA.SeparatedVariables

section

variable {K : Type*} [Field K]

abbrev Bivariate (K : Type*) [Field K] := Polynomial (Polynomial K)

local macro "liftSpec(" p:term ")" : term =>
  `(($p).map Polynomial.C)

local macro "reflectedSpec(" q:term ")" : term =>
  `((liftSpec($q)).comp
    (Polynomial.C ((Polynomial.C 2) * Polynomial.X) - Polynomial.X))

private theorem coeff_prod_at_sum_of_natDegree_le
    {R ι : Type*} [CommRing R] [DecidableEq ι]
    (s : Finset ι) (f : ι → Polynomial R) (bound : ι → ℕ)
    (h : ∀ i ∈ s, (f i).natDegree ≤ bound i) :
    (∏ i ∈ s, f i).coeff (∑ i ∈ s, bound i) =
      ∏ i ∈ s, (f i).coeff (bound i) := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha,
        Finset.prod_insert ha]
      rw [Polynomial.coeff_mul_add_eq_of_natDegree_le
        (h a (Finset.mem_insert_self a s))]
      · exact congrArg ((f a).coeff (bound a) * ·)
          (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))
      · exact (Polynomial.natDegree_prod_le
          (s := s) (f := f)).trans
            (Finset.sum_le_sum fun i hi =>
              h i (Finset.mem_insert_of_mem hi))

private theorem coeff_det_at_sum_of_column_bounds
    {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (Polynomial R))
    (bound : Fin n → ℕ)
    (h : ∀ i j, (M i j).natDegree ≤ bound j) :
    M.det.coeff (∑ j, bound j) =
      Matrix.det ((fun i j => (M i j).coeff (bound j)) :
        Matrix (Fin n) (Fin n) R) := by
  rw [Matrix.det_apply, Polynomial.finsetSum_coeff, Matrix.det_apply]
  refine Finset.sum_congr rfl ?_
  intro permutation _
  rw [Polynomial.coeff_smul]
  rw [coeff_prod_at_sum_of_natDegree_le]
  intro i _
  exact h (permutation i) i

private theorem det_of_upperTriangular_fin
    {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, j < i → M i j = 0) :
    M.det = ∏ i, M i i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
      have htail :
          (∑ i : Fin n,
            (-1 : R) ^ (i.succ : ℕ) * M i.succ 0 *
              Matrix.det (M.submatrix i.succ.succAbove Fin.succ)) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        rw [h i.succ 0 (Fin.succ_pos i)]
        simp
      rw [htail, add_zero]
      simp only [Fin.val_zero, pow_zero, one_mul]
      rw [ih]
      · rw [Fin.prod_univ_succ]
        simp only [Matrix.submatrix_apply, Fin.succAbove_zero_apply]
      · intro i j hji
        exact h i.succ j.succ (Fin.succ_lt_succ_iff.mpr hji)

@[simp] theorem natDegree_lift (p : Polynomial K) :
    (liftSpec(p)).natDegree = p.natDegree := by
  exact Polynomial.natDegree_map_eq_of_injective Polynomial.C_injective p

@[simp] theorem natDegree_reflected [CharZero K] (q : Polynomial K) :
    (reflectedSpec(q)).natDegree = q.natDegree := by
  rw [Polynomial.natDegree_comp, natDegree_lift]
  have hinner :
      (Polynomial.C ((Polynomial.C (2 : K)) * Polynomial.X) -
        Polynomial.X : Bivariate K).natDegree = 1 := by
    have hidentity :
        (Polynomial.C ((Polynomial.C (2 : K)) * Polynomial.X) -
            Polynomial.X : Bivariate K) =
          -(Polynomial.X -
            Polynomial.C ((Polynomial.C (2 : K)) * Polynomial.X)) := by ring
    rw [hidentity, Polynomial.natDegree_neg,
      Polynomial.natDegree_X_sub_C]
  rw [hinner, mul_one]

local notation "constants" =>
  (Polynomial.C.comp Polynomial.C : K →+* Bivariate K)

local notation "innerVariableToOuter" =>
  Polynomial.eval₂RingHom constants Polynomial.X

local notation "swapVariables" =>
  Polynomial.eval₂RingHom innerVariableToOuter (Polynomial.C Polynomial.X)

@[simp] private theorem swapVariables_X :
    swapVariables Polynomial.X = Polynomial.C Polynomial.X := by
  simp

@[simp] private theorem swapVariables_C_X :
    swapVariables (Polynomial.C Polynomial.X) = Polynomial.X := by
  simp

@[simp] private theorem swapVariables_C_C (r : K) :
    swapVariables (Polynomial.C (Polynomial.C r)) =
      Polynomial.C (Polynomial.C r) := by
  simp

@[simp] private theorem swapVariables_monomial_monomial
    (n m : ℕ) (r : K) :
    swapVariables (Polynomial.monomial n (Polynomial.monomial m r)) =
      Polynomial.monomial m (Polynomial.monomial n r) := by
  change Polynomial.eval₂ innerVariableToOuter
      (Polynomial.C Polynomial.X)
      (Polynomial.monomial n (Polynomial.monomial m r)) = _
  rw [Polynomial.eval₂_monomial]
  change Polynomial.eval₂ constants Polynomial.X
      (Polynomial.monomial m r) * Polynomial.C Polynomial.X ^ n = _
  rw [Polynomial.eval₂_monomial]
  simp [← map_pow, Polynomial.C_mul_X_pow_eq_monomial]

private theorem coeff_coeff_swap (q : Bivariate K) (i j : ℕ) :
    ((swapVariables q).coeff j).coeff i = (q.coeff i).coeff j := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add]
      simp only [Polynomial.coeff_add, hp, hq]
  | monomial n a =>
      induction a using Polynomial.induction_on' with
      | add p q hp hq =>
          rw [map_add (Polynomial.monomial n) p q, map_add]
          simp only [Polynomial.coeff_add, hp, hq]
      | monomial m r =>
          rw [swapVariables_monomial_monomial]
          simp only [Polynomial.coeff_monomial]
          split_ifs <;> simp_all [Polynomial.coeff_monomial]

private theorem swap_reflected (q : Polynomial K) :
    swapVariables (reflectedSpec(q)) =
      (liftSpec(q)).comp
        ((Polynomial.C 2) * Polynomial.X - Polynomial.C Polynomial.X) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [Polynomial.map_add, Polynomial.add_comp, map_add, hp, hq]
  | monomial n a =>
      rw [Polynomial.map_monomial,
        ← Polynomial.C_mul_X_pow_eq_monomial]
      simp only [Polynomial.mul_comp, Polynomial.C_comp,
        Polynomial.pow_comp, Polynomial.X_comp]
      change swapVariables
          (Polynomial.C (Polynomial.C a) *
            (Polynomial.C ((Polynomial.C 2) * Polynomial.X) -
              Polynomial.X) ^ n) =
        Polynomial.C (Polynomial.C a) *
          ((Polynomial.C 2) * Polynomial.X -
            Polynomial.C Polynomial.X) ^ n
      have hbase :
          swapVariables
              (Polynomial.C ((Polynomial.C 2) * Polynomial.X) -
                Polynomial.X) =
            (Polynomial.C 2) * Polynomial.X -
              Polynomial.C Polynomial.X := by
        have htwo : Polynomial.C (2 : K) = (2 : Polynomial K) :=
          map_ofNat Polynomial.C 2
        have houter : Polynomial.C (2 : Polynomial K) =
            (2 : Bivariate K) := map_ofNat Polynomial.C 2
        simp [htwo, houter]
      rw [map_mul, swapVariables_C_C, map_pow, hbase]

private theorem swappedInner_natDegree [CharZero K] :
    ((Polynomial.C 2) * Polynomial.X -
      Polynomial.C Polynomial.X : Bivariate K).natDegree = 1 := by
  have hfirst :
      ((Polynomial.C 2) * Polynomial.X : Bivariate K).natDegree = 1 := by
    rw [Polynomial.natDegree_C_mul, Polynomial.natDegree_X]
    norm_num
  rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt, hfirst]
  simp [hfirst]

private theorem natDegree_swapped_reflected [CharZero K]
    (q : Polynomial K) :
    ((liftSpec(q)).comp
      ((Polynomial.C 2) * Polynomial.X -
        Polynomial.C Polynomial.X)).natDegree = q.natDegree := by
  rw [Polynomial.natDegree_comp, natDegree_lift,
    swappedInner_natDegree, mul_one]

private theorem leadingCoeff_lift (q : Polynomial K) :
    (liftSpec(q)).leadingCoeff = Polynomial.C q.leadingCoeff := by
  rw [Polynomial.leadingCoeff, natDegree_lift,
    Polynomial.coeff_map, Polynomial.leadingCoeff]

private theorem leadingCoeff_swappedInner [CharZero K] :
    ((Polynomial.C 2) * Polynomial.X -
      Polynomial.C Polynomial.X : Bivariate K).leadingCoeff =
        Polynomial.C (2 : K) := by
  rw [Polynomial.leadingCoeff, swappedInner_natDegree]
  simp
  exact (map_ofNat Polynomial.C 2).symm

private theorem reflected_coeff_natDegree_le [CharZero K]
    (q : Polynomial K) (i : ℕ) :
    ((reflectedSpec(q)).coeff i).natDegree ≤ q.natDegree := by
  by_cases hcoeff : (reflectedSpec(q)).coeff i = 0
  · rw [hcoeff]
    exact Nat.zero_le _
  · have hleading :
        ((reflectedSpec(q)).coeff i).coeff
            ((reflectedSpec(q)).coeff i).natDegree ≠ 0 :=
      Polynomial.leadingCoeff_ne_zero.mpr hcoeff
    rw [← coeff_coeff_swap] at hleading
    rw [← natDegree_swapped_reflected q, ← swap_reflected]
    apply Polynomial.le_natDegree_of_ne_zero
    intro hzero
    rw [hzero] at hleading
    exact hleading (by simp)

private theorem reflected_coeff_top_of_pos [CharZero K]
    (q : Polynomial K) {i : ℕ} (hi : 0 < i) :
    ((reflectedSpec(q)).coeff i).coeff q.natDegree = 0 := by
  rw [← coeff_coeff_swap, swap_reflected,
    ← natDegree_swapped_reflected q, Polynomial.coeff_natDegree,
    Polynomial.leadingCoeff_comp (by
      rw [swappedInner_natDegree]
      exact Nat.one_ne_zero),
    leadingCoeff_lift, leadingCoeff_swappedInner, natDegree_lift]
  change (Polynomial.C q.leadingCoeff *
      Polynomial.C (2 : K) ^ q.natDegree).coeff i = 0
  have hconstant :
      Polynomial.C q.leadingCoeff *
          Polynomial.C (2 : K) ^ q.natDegree =
        Polynomial.C (q.leadingCoeff * 2 ^ q.natDegree) := by
    rw [← Polynomial.C_pow, ← Polynomial.C_mul]
  rw [hconstant]
  simp only [Polynomial.coeff_C, if_neg hi.ne']

private theorem reflected_coeff_zero_top [CharZero K]
    (q : Polynomial K) :
    ((reflectedSpec(q)).coeff 0).coeff q.natDegree =
      q.leadingCoeff * 2 ^ q.natDegree := by
  have eval_lift (r : Polynomial K) :
      (liftSpec(q)).eval r = q.comp r := by
    rw [Polynomial.eval_map]
    rfl
  have heval :
      (reflectedSpec(q)).eval 0 =
        q.comp (Polynomial.C 2 * Polynomial.X) := by
    rw [Polynomial.eval_comp, eval_lift]
    congr 1
    simp
  have hcoeffzero :
      (reflectedSpec(q)).coeff 0 =
        q.comp (Polynomial.C 2 * Polynomial.X) := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    exact heval
  rw [hcoeffzero]
  have htop := Polynomial.coeff_comp_degree_mul_degree
    (p := q) (q := Polynomial.C 2 * Polynomial.X) (by simp)
  have hinnerDegree :
      (Polynomial.C 2 * Polynomial.X : Polynomial K).natDegree = 1 := by
    rw [Polynomial.natDegree_C_mul, Polynomial.natDegree_X]
    norm_num
  have hinnerLeading :
      (Polynomial.C 2 * Polynomial.X : Polynomial K).leadingCoeff = 2 := by
    rw [Polynomial.leadingCoeff, hinnerDegree]
    simp
  rw [hinnerDegree, mul_one, hinnerLeading] at htop
  exact htop

private theorem pairedResultant_top_coeff [CharZero K]
    (p q : Polynomial K) :
    ((liftSpec(p)).resultant (reflectedSpec(q))
        p.natDegree q.natDegree).coeff
          (p.natDegree * q.natDegree) =
      (q.leadingCoeff * 2 ^ q.natDegree) ^ p.natDegree *
        p.leadingCoeff ^ q.natDegree := by
  let m := p.natDegree
  let n := q.natDegree
  let M := Polynomial.sylvester (liftSpec(p)) (reflectedSpec(q)) m n
  let bound : Fin (m + n) → ℕ := fun j =>
    j.addCases (fun _ => n) (fun _ => 0)
  have hbound : ∀ i j, (M i j).natDegree ≤ bound j := by
    intro i j
    induction j using Fin.addCases with
    | left j =>
        simp only [M, bound, Polynomial.sylvester,
          Matrix.of_apply, Fin.addCases_left]
        split
        · exact reflected_coeff_natDegree_le q _
        · simp
    | right j =>
        simp only [M, bound, Polynomial.sylvester,
          Matrix.of_apply, Fin.addCases_right]
        split
        · simp
        · simp
  have hsum : (∑ j, bound j) = m * n := by
    rw [Fin.sum_univ_add]
    simp [bound]
  have hcoeff := coeff_det_at_sum_of_column_bounds M bound hbound
  rw [hsum] at hcoeff
  let top : Matrix (Fin (m + n)) (Fin (m + n)) K :=
    fun i j => (M i j).coeff (bound j)
  have hupper : ∀ i j, j < i → top i j = 0 := by
    intro i j hji
    induction j using Fin.addCases with
    | left j =>
        simp only [top, M, bound, Polynomial.sylvester,
          Matrix.of_apply, Fin.addCases_left]
        split
        · apply reflected_coeff_top_of_pos q
          exact Nat.sub_pos_of_lt hji
        · simp
    | right j =>
        simp only [top, M, bound, Polynomial.sylvester,
          Matrix.of_apply, Fin.addCases_right]
        split
        · rw [Polynomial.coeff_map]
          have hdegree : p.natDegree < i - j := by
            change m + (j : ℕ) < (i : ℕ) at hji
            omega
          rw [Polynomial.coeff_eq_zero_of_natDegree_lt hdegree]
          simp
        · simp
  have hdiag : ∀ i, top i i =
      i.addCases
        (fun _ => q.leadingCoeff * 2 ^ q.natDegree)
        (fun _ => p.leadingCoeff) := by
    intro i
    induction i using Fin.addCases with
    | left i =>
        simp only [top, M, bound, Polynomial.sylvester,
          Matrix.of_apply, Fin.addCases_left]
        have hmem : (i : ℕ) ∈ Set.Icc (i : ℕ) (i + n) := by
          constructor <;> omega
        have hmem' : ((Fin.castAdd n i : Fin (m + n)) : ℕ) ∈
            Set.Icc (i : ℕ) (i + n) := by
          change (i : ℕ) ∈ Set.Icc (i : ℕ) (i + n)
          exact hmem
        rw [if_pos hmem']
        have hsub : ((Fin.castAdd n i : Fin (m + n)) : ℕ) - i = 0 := by
          simp
        rw [hsub]
        exact reflected_coeff_zero_top q
    | right i =>
        simp only [top, M, bound, Polynomial.sylvester,
          Matrix.of_apply, Fin.addCases_right]
        have hmem : (m + (i : ℕ)) ∈
            Set.Icc (i : ℕ) (i + m) := by
          constructor <;> omega
        have hmem' : ((Fin.natAdd m i : Fin (m + n)) : ℕ) ∈
            Set.Icc (i : ℕ) (i + m) := by
          change m + (i : ℕ) ∈ Set.Icc (i : ℕ) (i + m)
          exact hmem
        rw [if_pos hmem']
        have hsub : ((Fin.natAdd m i : Fin (m + n)) : ℕ) - i = m := by
          simp
        rw [hsub, Polynomial.coeff_map]
        rw [Polynomial.coeff_C_zero]
        rfl
  change M.det.coeff (m * n) = _
  rw [hcoeff]
  change top.det = _
  rw [det_of_upperTriangular_fin top hupper, Fin.prod_univ_add]
  simp_rw [hdiag]
  simp [m, n]

theorem pairedResultant_ne_zero
    [CharZero K]
    (p q : Polynomial K) (hp : p ≠ 0) (hqDegree : 0 < q.natDegree) :
    (liftSpec(p)).resultant (reflectedSpec(q)) p.natDegree q.natDegree ≠ 0 := by
  intro hzero
  have htop := pairedResultant_top_coeff p q
  rw [hzero] at htop
  have hq : q ≠ 0 := by
    intro hq
    rw [hq, Polynomial.natDegree_zero] at hqDegree
    exact Nat.lt_asymm hqDegree hqDegree
  have hqTop : q.leadingCoeff * 2 ^ q.natDegree ≠ 0 :=
    mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hq) (pow_ne_zero _ (by norm_num))
  have hpTop : p.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hp
  exact mul_ne_zero (pow_ne_zero _ hqTop) (pow_ne_zero _ hpTop) htop.symm

/-- After embedding the parameter polynomial ring into a field, the
separated-variable pair is coprime.  The fraction-field instance is the form
used by axis elimination. -/
theorem isCoprime_map_lift_reflected
    [CharZero K]
    {L : Type*} [Field L] (φ : Polynomial K →+* L)
    (hφ : Function.Injective φ)
    (p q : Polynomial K) (hp : p ≠ 0) (hqDegree : 0 < q.natDegree) :
    IsCoprime ((liftSpec(p)).map φ) ((reflectedSpec(q)).map φ) := by
  have hresultant := pairedResultant_ne_zero p q hp hqDegree
  have hmapped :
      ((liftSpec(p)).map φ).resultant ((reflectedSpec(q)).map φ)
        p.natDegree q.natDegree ≠ 0 := by
    rw [Polynomial.resultant_map_map]
    simpa using hφ.ne hresultant
  have hφresultant :
      φ ((liftSpec(p)).resultant (reflectedSpec(q))
        p.natDegree q.natDegree) ≠ 0 :=
    by simpa using hφ.ne hresultant
  have hliftDegree : ((liftSpec(p)).map φ).natDegree = p.natDegree := by
    rw [Polynomial.natDegree_map_eq_of_injective hφ, natDegree_lift]
  have hreflectedDegree :
      ((reflectedSpec(q)).map φ).natDegree = q.natDegree := by
    rw [Polynomial.natDegree_map_eq_of_injective hφ, natDegree_reflected]
  obtain ⟨a, b, _ha, _hb, hbezout⟩ :=
    Polynomial.exists_mul_add_mul_eq_C_resultant
      ((liftSpec(p)).map φ) ((reflectedSpec(q)).map φ)
      hliftDegree.le hreflectedDegree.le
      (Or.inr (Nat.ne_of_gt hqDegree))
  refine ⟨Polynomial.C (((liftSpec(p)).map φ).resultant
      ((reflectedSpec(q)).map φ) p.natDegree q.natDegree)⁻¹ * a,
    Polynomial.C (((liftSpec(p)).map φ).resultant
      ((reflectedSpec(q)).map φ) p.natDegree q.natDegree)⁻¹ * b, ?_⟩
  calc
    (Polynomial.C (((liftSpec(p)).map φ).resultant
          ((reflectedSpec(q)).map φ) p.natDegree q.natDegree)⁻¹ * a) *
        (liftSpec(p)).map φ +
      (Polynomial.C (((liftSpec(p)).map φ).resultant
          ((reflectedSpec(q)).map φ) p.natDegree q.natDegree)⁻¹ * b) *
        (reflectedSpec(q)).map φ =
      Polynomial.C (((liftSpec(p)).map φ).resultant
          ((reflectedSpec(q)).map φ) p.natDegree q.natDegree)⁻¹ *
        (((liftSpec(p)).map φ) * a + ((reflectedSpec(q)).map φ) * b) := by ring
    _ = Polynomial.C (((liftSpec(p)).map φ).resultant
          ((reflectedSpec(q)).map φ) p.natDegree q.natDegree)⁻¹ *
        Polynomial.C (((liftSpec(p)).map φ).resultant
          ((reflectedSpec(q)).map φ) p.natDegree q.natDegree) := by
      rw [hbezout]
    _ = 1 := by
      rw [← Polynomial.C_mul]
      simp [hφresultant]

end

end FTA.SeparatedVariables
