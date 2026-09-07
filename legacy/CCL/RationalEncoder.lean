import CCL.EncoderParserBridge
import Mathlib.RingTheory.EuclideanDomain

/-!
# Terminating CCL encoding of arbitrary Gaussian rationals

The core encoder carries a Gaussian-integer fraction.  This module converts
every Gaussian rational to such a fraction by a finite common-denominator
computation, cancels its Gaussian-integer gcd before encoding, proves exact
value preservation, and exposes the terminating encoder directly on `ℚ(i)`.
The cancellation is important computationally: without it, equal coordinate
denominators are multiplied twice and make the encoder's Euclidean measure
artificially quadratic.  This is the verification endpoint used by the
compatible-sample search in Lemma 10.4.
-/

namespace CCL
namespace RationalEncoder

open GaussianRat
open Integral

abbrev QI := GaussianRat
abbrev GI := GaussianInt

/-- Common-denominator Gaussian-integer numerator before cancellation. -/
def rawNumerator (z : QI) : GI :=
  ⟨z.re.num * z.im.den, z.im.num * z.re.den⟩

/-- Positive real Gaussian-integer denominator before cancellation. -/
def rawDenominator (z : QI) : GI :=
  ⟨z.re.den * z.im.den, 0⟩

theorem rawDenominator_ne (z : QI) : rawDenominator z ≠ 0 := by
  intro hzero
  have hre := congrArg (fun value : GI => value.re) hzero
  simp [rawDenominator] at hre

theorem toRat_rawNumerator (z : QI) :
    toRat (rawNumerator z) = z * toRat (rawDenominator z) := by
  have hreDen : (z.re.den : ℚ) ≠ 0 := by exact_mod_cast z.re.den_nz
  have himDen : (z.im.den : ℚ) ≠ 0 := by exact_mod_cast z.im.den_nz
  have hreCross : z.re * (z.re.den : ℚ) = (z.re.num : ℚ) := by
    calc
      z.re * (z.re.den : ℚ) =
          ((z.re.num : ℚ) / (z.re.den : ℚ)) * (z.re.den : ℚ) := by
        congr 1
        exact z.re.num_div_den.symm
      _ = (z.re.num : ℚ) := by field_simp [hreDen]
  have himCross : z.im * (z.im.den : ℚ) = (z.im.num : ℚ) := by
    calc
      z.im * (z.im.den : ℚ) =
          ((z.im.num : ℚ) / (z.im.den : ℚ)) * (z.im.den : ℚ) := by
        congr 1
        exact z.im.num_div_den.symm
      _ = (z.im.num : ℚ) := by field_simp [himDen]
  apply GaussianRat.ext
  · simp only [rawNumerator, rawDenominator, toRat, mul_re]
    push_cast
    calc
      (z.re.num : ℚ) * (z.im.den : ℚ) =
          (z.re * (z.re.den : ℚ)) * (z.im.den : ℚ) := by rw [hreCross]
      _ = z.re * ((z.re.den : ℚ) * (z.im.den : ℚ)) - z.im * 0 := by ring
  · simp only [rawNumerator, rawDenominator, toRat, mul_im]
    push_cast
    calc
      (z.im.num : ℚ) * (z.re.den : ℚ) =
          (z.im * (z.im.den : ℚ)) * (z.re.den : ℚ) := by rw [himCross]
      _ = z.re * 0 + z.im * ((z.re.den : ℚ) * (z.im.den : ℚ)) := by ring

/-- Gaussian-integer common factor removed before the Euclidean encoder runs. -/
def commonDivisor (z : QI) : GI :=
  EuclideanDomain.gcd (rawNumerator z) (rawDenominator z)

theorem commonDivisor_ne (z : QI) : commonDivisor z ≠ 0 := by
  intro hzero
  have bothZero := EuclideanDomain.gcd_eq_zero_iff.mp hzero
  exact rawDenominator_ne z bothZero.2

/-- Reduced Gaussian-integer numerator used by the encoder. -/
def numerator (z : QI) : GI :=
  rawNumerator z / commonDivisor z

/-- Reduced Gaussian-integer denominator used by the encoder. -/
def denominator (z : QI) : GI :=
  rawDenominator z / commonDivisor z

theorem commonDivisor_mul_numerator (z : QI) :
    commonDivisor z * numerator z = rawNumerator z := by
  exact EuclideanDomain.mul_div_cancel' (commonDivisor_ne z)
    (EuclideanDomain.gcd_dvd_left (rawNumerator z) (rawDenominator z))

theorem commonDivisor_mul_denominator (z : QI) :
    commonDivisor z * denominator z = rawDenominator z := by
  exact EuclideanDomain.mul_div_cancel' (commonDivisor_ne z)
    (EuclideanDomain.gcd_dvd_right (rawNumerator z) (rawDenominator z))

theorem denominator_ne (z : QI) : denominator z ≠ 0 := by
  intro hzero
  apply rawDenominator_ne z
  rw [← commonDivisor_mul_denominator z]
  simp [hzero]

/-- Cancelling the Euclidean gcd really leaves a coprime numerator and
denominator, not merely a smaller projectively equivalent pair. -/
theorem numerator_denominator_isCoprime (z : QI) :
    IsCoprime (numerator z) (denominator z) := by
  letI := EuclideanDomain.gcdMonoid GI
  exact isCoprime_div_gcd_div_gcd_of_gcd_ne_zero (commonDivisor_ne z)

theorem toRat_numerator (z : QI) :
    toRat (numerator z) = z * toRat (denominator z) := by
  apply GaussianRat.mul_right_cancel_of_ne
    (show toRat (commonDivisor z) ≠ 0 by simpa using commonDivisor_ne z)
  calc
    toRat (numerator z) * toRat (commonDivisor z) =
        toRat (commonDivisor z * numerator z) := by
          rw [toRat_mul, GaussianRat.mul_comm]
    _ = toRat (rawNumerator z) := by rw [commonDivisor_mul_numerator]
    _ = z * toRat (rawDenominator z) := toRat_rawNumerator z
    _ = z * toRat (commonDivisor z * denominator z) := by
      rw [commonDivisor_mul_denominator]
    _ = (z * toRat (denominator z)) * toRat (commonDivisor z) := by
      rw [toRat_mul]
      ac_rfl

/-- Executable reduced fraction representing an arbitrary Gaussian rational. -/
def fraction (z : QI) : Frac :=
  ⟨numerator z, denominator z, denominator_ne z⟩

theorem fraction_value (z : QI) : (fraction z).value = z := by
  rw [Frac.value, fraction, toRat_numerator]
  have hden : toRat (denominator z) ≠ 0 := by
    simpa using denominator_ne z
  rw [mul_assoc, mul_inv _ hden, mul_one]

theorem numerator_ne_of_ne {z : QI} (nonzero : z ≠ 0) : numerator z ≠ 0 := by
  intro hzero
  apply nonzero
  rw [← fraction_value z]
  simp [fraction, Frac.value, hzero]

/-- Complete finite raw CCL word of an arbitrary nonzero Gaussian rational. -/
def encode (z : QI) (nonzero : z ≠ 0) : Prefix.Word :=
  CCLEncoder.encode (fraction z) (numerator_ne_of_ne nonzero)

/-- The finite decoder product returned with the Gaussian-rational encoding. -/
def encodeResult (z : QI) (nonzero : z ≠ 0) : CCLEncoder.Encoding (fraction z) :=
  CCLEncoder.encodeResult (fraction z) (numerator_ne_of_ne nonzero)

theorem encode_reconstruct (z : QI) (nonzero : z ≠ 0) :
    (Mat2.act (Integral.mapMat (encodeResult z nonzero).matrix)
      (Proj.omega : Proj QI)).Equivalent (Proj.affine z) := by
  simpa only [encodeResult, fraction_value] using
    CCLEncoder.encode_reconstruct (fraction z) (numerator_ne_of_ne nonzero)

theorem encode_prefix_tower (z : QI) (nonzero : z ≠ 0) (n : ℕ) :
    (encode z nonzero).take n <+: (encode z nonzero).take (n + 1) ∧
      (encode z nonzero).take n <+: encode z nonzero := by
  exact CCLEncoder.encode_prefix_tower (fraction z)
    (numerator_ne_of_ne nonzero) n

/-- For an arbitrary nonzero Gaussian rational, the raw parser's affine
semantics recognizes exactly the proper prefixes of its terminating CCL
encoding. -/
theorem represented_iff_strictPrefix_encode
    (z : QI) (nonzero : z ≠ 0) (word : Prefix.Word) :
    RawParserSemantics.Represented word z ↔
      word <+: encode z nonzero ∧ word ≠ encode z nonzero := by
  simpa only [encode, fraction_value] using
    EncoderParserBridge.represented_iff_strictPrefix_encode
      (fraction z) (numerator_ne_of_ne nonzero) word

/-- Executable one-bit outcome for a represented rational prefix.  The final
bit is separated from ordinary affine continuation because it completes the
projective terminating word. -/
inductive Advance (z : QI) (nonzero : z ≠ 0) (word : Prefix.Word) where
  | next (bit : Bool)
      (represented : RawParserSemantics.Represented (word ++ [bit]) z)
  | terminal (bit : Bool) (complete : word ++ [bit] = encode z nonzero)

/-- Read the next actual encoder bit of a represented Gaussian-rational
prefix and decide, by one finite length comparison, whether it is another
affine parser step or the terminal projective bit. -/
def advance (z : QI) (nonzero : z ≠ 0) (word : Prefix.Word)
    (represented : RawParserSemantics.Represented word z) :
    Advance z nonzero word := by
  have bridge :=
    (represented_iff_strictPrefix_encode z nonzero word).1 represented
  let index := word.length
  have lengthLt : index < (encode z nonzero).length := by
    exact lt_of_le_of_ne bridge.1.length_le (fun lengthEq =>
      bridge.2 (bridge.1.eq_of_length lengthEq))
  let bit : Bool := (encode z nonzero)[index]'lengthLt
  have prefixEq : word = (encode z nonzero).take index :=
    List.prefix_iff_eq_take.mp bridge.1
  have childEq :
      word ++ [bit] = (encode z nonzero).take (index + 1) := by
    rw [prefixEq]
    exact (List.take_succ_eq_append_getElem lengthLt).symm
  by_cases completeLength : index + 1 = (encode z nonzero).length
  · refine Advance.terminal bit ?_
    calc
      word ++ [bit] = (encode z nonzero).take (index + 1) := childEq
      _ = encode z nonzero := by rw [completeLength]; simp
  · refine Advance.next bit ?_
    apply (represented_iff_strictPrefix_encode z nonzero
      (word ++ [bit])).2
    constructor
    · rw [childEq]
      exact List.take_prefix (index + 1) (encode z nonzero)
    · intro complete
      have lengthEq := congrArg List.length complete
      simp only [List.length_append, List.length_singleton] at lengthEq
      exact completeLength (by simpa [index] using lengthEq)

end RationalEncoder
end CCL
