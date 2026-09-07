import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Finite nonvanishing for polynomial resultants

This module proves resultant nonvanishing from an explicit coprimality
certificate by finite Euclidean descent.  It replaces Mathlib's more general
root-product route for this implication: the proof normalizes the smaller
polynomial, divides by that monic polynomial, and recurses on the strictly
smaller remainder degree.  It does not introduce roots, a splitting field, or
an infinite carrier.
-/

namespace FTA.FiniteResultant

open Polynomial

/-- Coprime polynomials over a field have nonzero Sylvester determinant.  The
proof is the finite Euclidean algorithm, rather than a product over roots. -/
theorem resultant_ne_zero_of_isCoprime
    {K : Type*} [Field K] (f g : Polynomial K) (H : IsCoprime f g) :
    f.resultant g ≠ 0 := by
  generalize hd : f.natDegree + g.natDegree = d
  induction d using Nat.strong_induction_on generalizing f g with
  | h d ih =>
      have oriented (F G : Polynomial K) (hcoprime : IsCoprime F G)
          (hdegree : G.natDegree ≤ F.natDegree)
          (hmeasure : F.natDegree + G.natDegree = d) :
          F.resultant G ≠ 0 := by
        obtain rfl | hF := eq_or_ne F 0
        · have hunitG : IsUnit G := isCoprime_zero_left.mp hcoprime
          rcases Polynomial.isUnit_iff.mp hunitG with ⟨c, _hc, rfl⟩
          simp
        obtain rfl | hG := eq_or_ne G 0
        · have hunitF : IsUnit F := isCoprime_zero_right.mp hcoprime
          rcases Polynomial.isUnit_iff.mp hunitF with ⟨c, _hc, rfl⟩
          simp
        let Gm := Polynomial.C G.leadingCoeff⁻¹ * G
        have hleading : G.leadingCoeff ≠ 0 :=
          Polynomial.leadingCoeff_ne_zero.mpr hG
        have hunit : IsUnit (Polynomial.C G.leadingCoeff⁻¹) :=
          Polynomial.isUnit_C.mpr
            (isUnit_iff_ne_zero.mpr (inv_ne_zero hleading))
        have hGmDegree : Gm.natDegree = G.natDegree := by
          dsimp only [Gm]
          rw [Polynomial.natDegree_C_mul]
          simpa
        have hGm : Gm.Monic := by
          dsimp only [Gm]
          rw [Polynomial.Monic, Polynomial.leadingCoeff,
            Polynomial.natDegree_C_mul (by simpa),
            Polynomial.coeff_C_mul, Polynomial.leadingCoeff]
          exact inv_mul_cancel₀ hleading
        have hcoprimeNorm : IsCoprime F Gm := by
          exact (isCoprime_mul_unit_left_right hunit F G).mpr hcoprime
        let r := F %ₘ Gm
        let q := F /ₘ Gm
        have hdivision : r + Gm * q = F := by
          exact Polynomial.modByMonic_add_div F Gm
        have hscale := Polynomial.resultant_C_mul_right
          (f := F) (g := G) (r := G.leadingCoeff⁻¹)
          (m := F.natDegree) (n := G.natDegree)
        change F.resultant Gm F.natDegree G.natDegree = _ at hscale
        have hnormalized : F.resultant Gm F.natDegree Gm.natDegree ≠ 0 := by
          by_cases hr : r = 0
          · have hGmUnit : IsUnit Gm := by
              rcases hcoprimeNorm with ⟨u, v, huv⟩
              apply isUnit_iff_exists_inv'.mpr
              refine ⟨u * q + v, ?_⟩
              calc
                (u * q + v) * Gm = u * (Gm * q) + v * Gm := by ring
                _ = u * F + v * Gm := by rw [← hdivision, hr, zero_add]
                _ = 1 := huv
            have hGmOne : Gm = 1 := hGm.eq_one_of_isUnit hGmUnit
            rw [hGmOne]
            simp
          · have hGmNeOne : Gm ≠ 1 := by
              intro hone
              apply hr
              simp [r, hone]
            have hrDegree : r.natDegree < Gm.natDegree := by
              dsimp only [r]
              exact Polynomial.natDegree_modByMonic_lt F hGm hGmNeOne
            have hcoprimeRem : IsCoprime Gm r := by
              rcases hcoprimeNorm with ⟨u, v, huv⟩
              refine ⟨u * q + v, u, ?_⟩
              calc
                (u * q + v) * Gm + u * r =
                    u * (r + Gm * q) + v * Gm := by ring
                _ = u * F + v * Gm := by rw [hdivision]
                _ = 1 := huv
            have hsmaller : Gm.natDegree + r.natDegree < d := by
              rw [hGmDegree, ← hmeasure]
              omega
            have hrecursive : Gm.resultant r ≠ 0 :=
              ih _ hsmaller Gm r hcoprimeRem rfl
            have hsmall :
                r.resultant Gm r.natDegree Gm.natDegree ≠ 0 := by
              rw [Polynomial.resultant_comm]
              exact mul_ne_zero (by simp) hrecursive
            have hrLe : r.natDegree ≤ F.natDegree := by
              exact hrDegree.le.trans (hGmDegree.trans_le hdegree)
            have hraised :
                r.resultant Gm F.natDegree Gm.natDegree ≠ 0 := by
              have hraise := Polynomial.resultant_add_left_deg
                (f := r) (g := Gm) (m := r.natDegree)
                (n := Gm.natDegree) (k := F.natDegree - r.natDegree)
                le_rfl
              have hsum : r.natDegree + (F.natDegree - r.natDegree) =
                  F.natDegree := Nat.add_sub_of_le hrLe
              rw [hsum] at hraise
              have hcoeff : Gm.coeff Gm.natDegree = 1 :=
                hGm.coeff_natDegree
              rw [hcoeff] at hraise
              rw [hraise]
              exact mul_ne_zero (by simp) hsmall
            have hqDegree : q.natDegree + Gm.natDegree ≤ F.natDegree := by
              dsimp only [q]
              rw [Polynomial.natDegree_divByMonic F hGm, hGmDegree]
              omega
            have hadd := Polynomial.resultant_add_mul_left
              (f := r) (g := Gm) (p := q)
              (m := F.natDegree) (n := Gm.natDegree)
              hqDegree le_rfl
            rw [hdivision] at hadd
            rw [hadd]
            exact hraised
        have hnormalizedSized :
            F.resultant Gm F.natDegree G.natDegree ≠ 0 := by
          simpa [hGmDegree] using hnormalized
        intro hzero
        apply hnormalizedSized
        rw [hscale, hzero, mul_zero]
      by_cases hdegree : g.natDegree ≤ f.natDegree
      · exact oriented f g H hdegree hd
      · have hswap := oriented g f H.symm
          (Nat.le_of_lt (Nat.lt_of_not_ge hdegree)) (by omega)
        rw [Polynomial.resultant_comm]
        exact mul_ne_zero (by simp) hswap

end FTA.FiniteResultant
