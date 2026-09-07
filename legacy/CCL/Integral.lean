import CCL.Gaussian
import CCL.Geometry.Projective
import CCL.Encoding.Sectors
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-!
# Uncancelled Gaussian-integer fractions

The termination arguments in Sections 5–6 carry numerator/denominator pairs
in `ℤ[i]` without cancellation.  This module connects mathlib's Gaussian
integers to the paper's exact Gaussian-rational coordinate model.
-/

namespace CCL

open GaussianRat

namespace Integral

abbrev GI := GaussianInt

/-- Coordinatewise embedding `ℤ[i] → ℚ(i)`. -/
def toRat (z : GI) : GaussianRat := ⟨z.re, z.im⟩

@[simp] theorem toRat_zero : toRat 0 = 0 := rfl
@[simp] theorem toRat_one : toRat 1 = 1 := rfl

@[simp] theorem toRat_add (z w : GI) : toRat (z + w) = toRat z + toRat w := by
  ext <;> simp [toRat]

@[simp] theorem toRat_neg (z : GI) : toRat (-z) = -toRat z := by
  ext <;> simp [toRat]

@[simp] theorem toRat_sub (z w : GI) : toRat (z - w) = toRat z - toRat w := by
  ext <;> simp [toRat]

@[simp] theorem toRat_mul (z w : GI) : toRat (z * w) = toRat z * toRat w := by
  apply GaussianRat.ext
  · simp [toRat]
    ring
  · simp [toRat]

theorem toRat_injective : Function.Injective toRat := by
  intro z w h
  apply Zsqrtd.ext
  · have hr : (z.re : ℚ) = w.re := by simpa [toRat] using congrArg GaussianRat.re h
    exact_mod_cast hr
  · have hi : (z.im : ℚ) = w.im := by simpa [toRat] using congrArg GaussianRat.im h
    exact_mod_cast hi

@[simp] theorem toRat_eq_zero {z : GI} : toRat z = 0 ↔ z = 0 := by
  constructor
  · exact fun h => toRat_injective (h.trans toRat_zero.symm)
  · rintro rfl
    exact toRat_zero

/-- The natural-valued Gaussian norm used as the recursion measure. -/
def normNat (z : GI) : ℕ := z.norm.natAbs

theorem normNat_pos {z : GI} (hz : z ≠ 0) : 0 < normNat z := by
  rw [normNat, Int.natAbs_pos]
  exact ne_of_gt (GaussianInt.norm_pos.mpr hz)

@[simp] theorem normNat_mul (z w : GI) : normNat (z * w) = normNat z * normNat w := by
  simp [normNat, Zsqrtd.norm_mul, Int.natAbs_mul]

/-- `1+i` as a Gaussian integer. -/
def gammaInt : GI := ⟨1, 1⟩

@[simp] theorem toRat_gammaInt : toRat gammaInt = gamma := rfl
@[simp] theorem normNat_gammaInt : normNat gammaInt = 2 := by norm_num [normNat, gammaInt, Zsqrtd.norm]

@[simp] theorem normNat_gammaInt_pow (k : ℕ) : normNat (gammaInt ^ k) = 2 ^ k := by
  induction k with
  | zero => simp [normNat]
  | succ k ih => simp [pow_succ, ih]

@[simp] theorem toRat_gammaInt_pow (k : ℕ) :
    toRat (gammaInt ^ k) = natPow gamma k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [pow_succ, natPow_succ, ih]

/-- The representative table, now in `ℤ[i]`. -/
def sectorInt : Sector → GI
  | .east => ⟨1, 0⟩
  | .northEast => ⟨1, 1⟩
  | .north => ⟨0, 1⟩
  | .northWest => ⟨-1, 1⟩
  | .west => ⟨-1, 0⟩
  | .southWest => ⟨-1, -1⟩
  | .south => ⟨0, -1⟩
  | .southEast => ⟨1, -1⟩

@[simp] theorem toRat_sectorInt (s : Sector) : toRat (sectorInt s) = s.rep := by
  cases s <;> rfl

/-- Coordinatewise embedding of an integral projective pair. -/
def mapProj (x : Proj GI) : Proj GaussianRat := ⟨toRat x.p, toRat x.q⟩

/-- Coordinatewise embedding of an integral decoder matrix. -/
def mapMat (M : Mat2 GI) : Mat2 GaussianRat :=
  ⟨toRat M.a, toRat M.b, toRat M.c, toRat M.d⟩

@[simp] theorem mapProj_omega :
    mapProj (Proj.omega : Proj GI) = (Proj.omega : Proj GaussianRat) := rfl

@[simp] theorem mapProj_act (M : Mat2 GI) (x : Proj GI) :
    mapProj (Mat2.act M x) = Mat2.act (mapMat M) (mapProj x) := by
  ext <;> simp [mapProj, mapMat, Mat2.act]

theorem mapProj_equivalent {x y : Proj GI} (h : x.Equivalent y) :
    (mapProj x).Equivalent (mapProj y) := by
  dsimp [Proj.Equivalent, mapProj] at h ⊢
  simpa using congrArg toRat h

/-- Compatibility of the natural integer norm with the rational norm. -/
theorem normSq_toRat (z : GI) : normSq (toRat z) = (normNat z : ℚ) := by
  change (z.re : ℚ) ^ 2 + (z.im : ℚ) ^ 2 = (z.norm.natAbs : ℚ)
  rw [GaussianInt.natCast_natAbs_norm]
  simp only [Zsqrtd.norm]
  push_cast
  ring

/-- An uncancelled nonzero-denominator Gaussian-integer fraction. -/
structure Frac where
  num : GI
  den : GI
  den_ne : den ≠ 0
deriving Repr

namespace Frac

/-- Exact Gaussian-rational value of an uncancelled fraction. -/
def value (f : Frac) : GaussianRat := toRat f.num * inv (toRat f.den)

theorem den_toRat_ne (f : Frac) : toRat f.den ≠ 0 := by
  simpa using f.den_ne

/-- Cross-multiplied value identity `P = (P/Q)Q`. -/
theorem value_mul_den (f : Frac) : f.value * toRat f.den = toRat f.num := by
  dsimp [value]
  rw [mul_assoc, inv_mul _ f.den_toRat_ne, mul_one]

/-- Exact norm quotient for an uncancelled fraction. -/
theorem normSq_value (f : Frac) :
    normSq f.value = (normNat f.num : ℚ) / normNat f.den := by
  rw [value, normSq_mul, normSq_inv _ f.den_toRat_ne, normSq_toRat, normSq_toRat]
  ring

theorem value_ne_zero (f : Frac) (hnum : f.num ≠ 0) : f.value ≠ 0 := by
  intro h
  have hnorm := congrArg normSq h
  rw [normSq_value, normSq_zero] at hnorm
  have hn := normNat_pos hnum
  have hd := normNat_pos f.den_ne
  norm_num at hnorm
  rcases hnorm with hnorm | hnorm
  · exact (Nat.ne_of_gt hn) hnorm
  · exact (Nat.ne_of_gt hd) hnorm

end Frac

end Integral

end CCL
