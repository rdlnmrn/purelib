import mathlib.Tactic.QuotientFreeRing
import CCL.Geometry.Chordal
import CCL.Encoding.Sectors

/-!
# Choice-free completed CCL blocks

Raw words, decoder matrices, determinants, and the strict post-inversion norm
estimate are all finite computations over constructive Gaussian fractions.
-/

namespace CCL.Decoder

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Sector := CCL.Sectors.Sector
abbrev Proj := CCL.GaussianProjective.Proj
abbrev Mat2 := CCL.GaussianProjective.Mat2
abbrev Word := List Bool

open RFAP.ConstructiveGaussian.Gaussian
open CCL.Sectors

/-- Raw syntax `[k,s] = 1ᵏ 0 β(s)`. -/
def regularWord (exponent : Nat) (sector : Sector) : Word :=
  List.replicate exponent true ++ false :: sector.code

/-- Raw syntax `0[m,s]` for an initial low block. -/
def lowWord (exponent : Nat) (sector : Sector) : Word :=
  false :: regularWord exponent sector

@[simp] theorem regularWord_length (exponent : Nat) (sector : Sector) :
    (regularWord exponent sector).length = exponent + 4 := by
  simp [regularWord]

@[simp] theorem lowWord_length (exponent : Nat) (sector : Sector) :
    (lowWord exponent sector).length = exponent + 5 := by
  simp [lowWord]

/-- Formula (6.2), a completed regular block. -/
def regularBlock (exponent : Nat) (sector : Sector) : Mat2 :=
  ⟨natPow gamma (exponent + 1) * sector.rep,
    natPow gamma exponent, gamma, 0⟩

/-- The diagonal factor used by the initial low branch. -/
def lowScale (exponent : Nat) : Mat2 :=
  ⟨1, 0, 0, natPow gamma exponent⟩

/-- Formula (6.3), a completed initial low block. -/
def lowBlock (exponent : Nat) (sector : Sector) : Mat2 :=
  ⟨gamma * sector.rep, 1, natPow gamma (exponent + 1), 0⟩

/-- Finite factorization `B(k,s) = S_{γᵏ} T_s I_γ`. -/
theorem regularBlock_factorization (exponent : Nat) (sector : Sector) :
    CCL.Mat2.mul
        (CCL.Mat2.mul (CCL.Mat2.scale (natPow gamma exponent))
          (CCL.Mat2.translate sector.rep))
        (CCL.Mat2.invert gamma) =
      regularBlock exponent sector := by
  apply CCL.Mat2.ext <;>
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [CCL.Mat2.mul, CCL.Mat2.scale, CCL.Mat2.translate,
      CCL.Mat2.invert, regularBlock, natPow_succ, add_re, add_im,
      mul_re, mul_im, zero_re, zero_im, one_re, one_im, gamma] <;>
    ring1

/-- Finite factorization `L(m,s) = E⁻ᵐ T_s I_γ`. -/
theorem lowBlock_factorization (exponent : Nat) (sector : Sector) :
    CCL.Mat2.mul
        (CCL.Mat2.mul (lowScale exponent) (CCL.Mat2.translate sector.rep))
        (CCL.Mat2.invert gamma) =
      lowBlock exponent sector := by
  apply CCL.Mat2.ext <;>
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [CCL.Mat2.mul, CCL.Mat2.translate, CCL.Mat2.invert,
      lowScale, lowBlock, natPow_succ, add_re, add_im, mul_re, mul_im,
      zero_re, zero_im, one_re, one_im, gamma] <;>
    ring1

theorem regularBlock_det (exponent : Nat) (sector : Sector) :
    CCL.Chordal.Mat2.det (regularBlock exponent sector) =
      -natPow gamma (exponent + 1) := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [CCL.Chordal.Mat2.det, regularBlock, natPow_succ,
      sub_re, sub_im, mul_re, mul_im, neg_re, neg_im, zero_re, zero_im,
      gamma] <;>
    ring1

theorem lowBlock_det (exponent : Nat) (sector : Sector) :
    CCL.Chordal.Mat2.det (lowBlock exponent sector) =
      -natPow gamma (exponent + 1) := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [CCL.Chordal.Mat2.det, lowBlock, sub_re, sub_im,
      mul_re, mul_im, neg_re, neg_im, zero_re, zero_im, one_re, one_im] <;>
    ring1

/-- Lemma 6.4 over an uncancelled constructive Gaussian fraction. -/
theorem inversion_stage_descent {value numerator denominator : Gaussian}
    (denominatorNonzero : denominator ≠ 0)
    (band : Sector.Band value) (sector : Sector)
    (holds : sector.Holds value)
    (numeratorIdentity : numerator = value * denominator) :
    normSq (gamma * (numerator - sector.rep * denominator)) <
      normSq denominator := by
  have differenceIdentity :
      numerator - sector.rep * denominator =
        (value - sector.rep) * denominator := by
    rw [numeratorIdentity]
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [sub_re, sub_im, mul_re, mul_im] <;> ring1
  have sectorContraction := Sector.contraction band sector holds
  have factorContraction :
      2 * normSq (value - sector.rep) < (1 : Coordinate) := by
    calc
      2 * normSq (value - sector.rep) < 2 * (1 / 2 : Coordinate) :=
        RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
          (by decide) sectorContraction
      _ = 1 := by decide
  have denominatorPositive := normSq_pos denominatorNonzero
  calc
    normSq (gamma * (numerator - sector.rep * denominator)) =
        (2 * normSq (value - sector.rep)) * normSq denominator := by
      rw [differenceIdentity, normSq_mul, normSq_mul, normSq_gamma]
      ring1
    _ < 1 * normSq denominator :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
        factorContraction denominatorPositive
    _ = normSq denominator := RFAP.ConstructiveFraction.one_mul _

/-- After nonterminal sector subtraction and inversion, the next value lies
strictly outside the unit norm. -/
theorem postInversion_norm_gt_one {value : Gaussian}
    (band : Sector.Band value) (sector : Sector)
    (holds : sector.Holds value) (residualNonzero : value - sector.rep ≠ 0) :
    1 < normSq ((gamma * (value - sector.rep))⁻¹) := by
  have gammaNonzero : gamma ≠ 0 := by decide
  have productNonzero : gamma * (value - sector.rep) ≠ 0 :=
    mul_ne_zero_direct gammaNonzero residualNonzero
  have sectorContraction := Sector.contraction band sector holds
  have productNormPositive := normSq_pos productNonzero
  have productNormLtOne :
      normSq (gamma * (value - sector.rep)) < 1 := by
    rw [normSq_mul, normSq_gamma]
    calc
      2 * normSq (value - sector.rep) < 2 * (1 / 2 : Coordinate) :=
        RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
          (by decide) sectorContraction
      _ = 1 := by decide
  rw [inv_eq, normSq_inv _ productNonzero]
  apply RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
    (c := normSq (gamma * (value - sector.rep))) _ productNormPositive
  calc
    1 * normSq (gamma * (value - sector.rep)) =
        normSq (gamma * (value - sector.rep)) :=
      RFAP.ConstructiveFraction.one_mul _
    _ < 1 := productNormLtOne
    _ = (normSq (gamma * (value - sector.rep)))⁻¹ *
          normSq (gamma * (value - sector.rep)) :=
      (RFAP.ConstructiveFraction.inv_mul_cancel _ productNormPositive.ne').symm

/-- Norm accounting after the bounded loop normalization. -/
theorem normalized_denominator_descent (exponent : Nat)
    {postDenominator oldDenominator : Gaussian}
    (scaled : (2 : Coordinate) ^ exponent * normSq postDenominator <
      normSq oldDenominator) :
    normSq (natPow gamma exponent * postDenominator) <
      normSq oldDenominator := by
  rw [normSq_gamma_pow_mul]
  exact scaled

end CCL.Decoder
