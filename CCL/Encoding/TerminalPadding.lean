import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import CCL.Arithmetic.RedundantBlockContraction
import CCL.Encoding.RawParser
import CCL.Boundary.Pullback

/-!
# Productive unary padding at a projective CCL terminal

An arithmetic transducer cannot in general decide that opaque nonterminating
inputs have combined to an exact Gaussian rational.  The canonical finite
encoder remains unchanged.  This module supplies a separate projective
continuation convention: after a completed sector, an unresolved zero
residual may remain at `omega`, and every further unary `1` fixes that formal
coordinate while strengthening the finite large-tail predicate.
-/

namespace CCL.TerminalPadding

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Proj := CCL.GaussianProjective.Proj
abbrev Mat2 := CCL.GaussianProjective.Mat2
abbrev Word := List Bool

open RFAP.ConstructiveGaussian.Gaussian
open CCL.Chordal
open CCL.RawParser

/-- Append a finite observation of the non-return unary tail. -/
def pad (word : Word) (count : Nat) : Word :=
  word ++ List.replicate count true

private theorem foldl_true_loop (count start : Nat)
    (matrix : Mat2) (history : List Constraint) :
    (List.replicate count true).foldl step
        ⟨.loopUnary start, matrix, history⟩ =
      ⟨.loopUnary (start + count), matrix, history⟩ := by
  induction count generalizing start with
  | zero => simp
  | succ count inductionHypothesis =>
      rw [List.replicate_succ, List.foldl_cons]
      simp only [step, if_pos]
      rw [inductionHypothesis]
      congr 2
      ring1

/-- Padding a parser state which is reading a subsequent unary header changes
only its finite unary counter.  In particular the decoder matrix and all
completed historical constraints remain unchanged. -/
theorem parse_pad_of_loop
    {word : Word} {start : Nat} {matrix : Mat2}
    {history : List Constraint}
    (parsed : parse word = ⟨.loopUnary start, matrix, history⟩)
    (count : Nat) :
    parse (pad word count) =
      ⟨.loopUnary (start + count), matrix, history⟩ := by
  rw [pad, parse_append, parsed]
  exact foldl_true_loop count start matrix history

/-- Hence every finite unary padding observation has exactly the same
canonical projective truncation. -/
theorem truncation_parse_pad_of_loop
    {word : Word} {start : Nat} {matrix : Mat2}
    {history : List Constraint}
    (parsed : parse word = ⟨.loopUnary start, matrix, history⟩)
    (count : Nat) :
    (parse (pad word count)).truncation =
      CCL.Mat2.act matrix CCL.Proj.omega := by
  rw [parse_pad_of_loop parsed count]
  rfl

/-- Projective meanings admitted by an unresolved loop-unary fragment.  The
`omega` constructor is the exact residual-zero case; affine tails retain the
ordinary strict unary inequality. -/
inductive LoopTail (count : Nat) where
  | omega
  | affine (tail : Gaussian) (large : (2 : Coordinate) ^ count < normSq tail)

namespace LoopTail

def point {count : Nat} : LoopTail count → Proj
  | .omega => CCL.Proj.omega
  | .affine tail _ => CCL.Proj.affine tail

theorem valid {count : Nat} (tail : LoopTail count) :
    Proj.HasNonzeroCoordinate tail.point := by
  cases tail with
  | omega => exact Proj.omega_hasNonzeroCoordinate
  | affine value large => exact Proj.affine_hasNonzeroCoordinate value

/-- An unresolved unary tail approaches `omega` with a completely rational
dyadic squared-chordal estimate. -/
theorem chordalSq_omega_le {count : Nat} (tail : LoopTail count) :
    chordalSq tail.point CCL.Proj.omega ≤
      1 / (1 + (2 : Coordinate) ^ count) := by
  cases tail with
  | omega =>
      change chordalSq (CCL.Proj.omega : Proj) CCL.Proj.omega ≤ _
      rw [chordalSq_eq_zero_of_equivalent (CCL.Proj.Equivalent.refl _)]
      exact RFAP.ConstructiveFraction.div_nonneg_direct (by decide)
        (add_nonneg (by decide)
          (RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) count))
  | affine value large =>
      rw [point, chordalSq_omega]
      have denominatorPositive :
          0 < 1 + (2 : Coordinate) ^ count :=
        add_pos_of_pos_of_nonneg (by decide)
          (RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) count)
      have denominatorOrder :
          1 + (2 : Coordinate) ^ count ≤ 1 + normSq value :=
        add_le_add le_rfl large.le
      exact RFAP.ConstructiveFraction.div_le_div_of_nonneg_left_direct
        (by decide) denominatorPositive denominatorOrder

end LoopTail

/-! ## The analogous no-return name for exact zero -/

/-- Meanings admitted after the initial low selector followed by `count + 1`
unary one bits.  The affine predicate is exactly the parser inequality
`2^count * N(value) < 1`; the extra constructor supplies the exact zero which
the finite nonzero encoder deliberately excludes. -/
inductive ZeroTail (count : Nat) where
  | zero
  | affine (value : Gaussian)
      (small : (2 : Coordinate) ^ count * normSq value < 1)

namespace ZeroTail

def point {count : Nat} : ZeroTail count → Proj
  | .zero => CCL.Proj.affine 0
  | .affine value _ => CCL.Proj.affine value

theorem valid {count : Nat} (tail : ZeroTail count) :
    Proj.HasNonzeroCoordinate tail.point := by
  cases tail with
  | zero => exact Proj.affine_hasNonzeroCoordinate 0
  | affine value small => exact Proj.affine_hasNonzeroCoordinate value

/-- Initial low unary padding converges to zero at the reciprocal dyadic
rate, again entirely in squared rational quantities. -/
theorem chordalSq_zero_lt {count : Nat} (tail : ZeroTail count) :
    chordalSq tail.point (CCL.Proj.affine 0) <
      1 / (2 : Coordinate) ^ count := by
  cases tail with
  | zero =>
      change chordalSq (CCL.Proj.affine 0) (CCL.Proj.affine 0) < _
      rw [chordalSq_eq_zero_of_equivalent (CCL.Proj.Equivalent.refl _)]
      exact RFAP.ConstructiveFraction.div_pos_direct (by decide)
        (RFAP.ConstructiveFraction.pow_pos_direct (by decide) count)
  | affine value small =>
      have powerPositive : 0 < (2 : Coordinate) ^ count :=
        RFAP.ConstructiveFraction.pow_pos_direct (by decide) count
      have normSmall : normSq value < 1 / (2 : Coordinate) ^ count := by
        apply (RFAP.ConstructiveFraction.lt_div_iff_pos powerPositive).2
        calc
          normSq value * (2 : Coordinate) ^ count =
              (2 : Coordinate) ^ count * normSq value :=
            RFAP.ConstructiveFraction.mul_comm _ _
          _ < 1 := small
      have chordalBound := chordalSq_affine_le_normSq value 0
      have differenceNorm : normSq (value - 0) = normSq value := by
        congr 1
        exact RFAP.ConstructiveGaussian.Gaussian.sub_zero value
      rw [differenceNorm] at chordalBound
      exact chordalBound.trans_lt normSmall

end ZeroTail

/-! ## Transport of the unary estimate through a finite decoder -/

private theorem adjugate_act_act (matrix : Mat2) (point : Proj) :
    CCL.Mat2.act (CCL.CCLPullback.adjugate matrix)
        (CCL.Mat2.act matrix point) =
      CCL.Chordal.Proj.scale
        (CCL.CCLPullback.determinant matrix) point := by
  apply CCL.Proj.ext <;>
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [CCL.Mat2.act, CCL.CCLPullback.adjugate,
        CCL.CCLPullback.determinant,
        CCL.Chordal.Mat2.det,
        CCL.Chordal.Proj.scale,
        add_re, add_im, sub_re, sub_im, mul_re, mul_im, neg_re, neg_im] <;>
      ring1

/-- Applying an invertible displayed decoder cannot reduce projective weight
below this explicit adjugate-coefficient estimate. -/
theorem determinant_mul_weight_le_act_weight
    (matrix : Mat2) (point : Proj) :
    normSq (CCL.CCLPullback.determinant matrix) *
        CCL.Chordal.Proj.weight point ≤
      CCL.Chordal.Mat2.actionWeightCoefficient
          (CCL.CCLPullback.adjugate matrix) *
        CCL.Chordal.Proj.weight (CCL.Mat2.act matrix point) := by
  let inverse := CCL.CCLPullback.adjugate matrix
  let image := CCL.Mat2.act matrix point
  have upper := CCL.Chordal.Mat2.act_weight_le inverse image
  calc
    normSq (CCL.CCLPullback.determinant matrix) *
        CCL.Chordal.Proj.weight point =
        CCL.Chordal.Proj.weight
          (CCL.Chordal.Proj.scale
            (CCL.CCLPullback.determinant matrix) point) :=
      (CCL.Chordal.Proj.weight_scale _ _).symm
    _ = CCL.Chordal.Proj.weight
        (CCL.Mat2.act inverse image) := by
      rw [adjugate_act_act]
    _ ≤ CCL.Chordal.Mat2.actionWeightCoefficient inverse *
        CCL.Chordal.Proj.weight image := upper

/-- A finite condition-number coefficient for transporting arbitrary
projective two-point error through one invertible displayed decoder. -/
def transportCoefficient (matrix : Mat2) : Coordinate :=
  let coefficient :=
    CCL.Chordal.Mat2.actionWeightCoefficient
      (CCL.CCLPullback.adjugate matrix)
  coefficient ^ 2 /
    normSq (CCL.CCLPullback.determinant matrix)

theorem transportCoefficient_pos (matrix : Mat2)
    (determinantNonzero :
      CCL.CCLPullback.determinant matrix ≠ 0) :
    0 < transportCoefficient matrix := by
  exact RFAP.ConstructiveFraction.div_pos_direct
    (RFAP.ConstructiveFraction.pow_pos_direct
      (CCL.Chordal.Mat2.actionWeightCoefficient_pos
        (CCL.CCLPullback.adjugate matrix)) 2)
    (normSq_pos determinantNonzero)

/-- Any one finite invertible decoder can enlarge squared-chordal error by at
most its displayed rational condition coefficient.  This is the accounting
needed before later half-contracting blocks make up for one annulus-free
initial arithmetic digit. -/
theorem chordalSq_act_le_transportCoefficient
    (matrix : Mat2)
    (determinantNonzero :
      CCL.CCLPullback.determinant matrix ≠ 0)
    (left right : Proj)
    (leftValid : CCL.Chordal.Proj.HasNonzeroCoordinate left)
    (rightValid : CCL.Chordal.Proj.HasNonzeroCoordinate right) :
    CCL.Chordal.chordalSq
        (CCL.Mat2.act matrix left) (CCL.Mat2.act matrix right) ≤
      transportCoefficient matrix *
        CCL.Chordal.chordalSq left right := by
  let determinantNorm :=
    normSq (CCL.CCLPullback.determinant matrix)
  let coefficient :=
    CCL.Chordal.Mat2.actionWeightCoefficient
      (CCL.CCLPullback.adjugate matrix)
  let numerator := normSq (CCL.Chordal.Proj.cross left right)
  let inputDenominator :=
    CCL.Chordal.Proj.weight left *
      CCL.Chordal.Proj.weight right
  let outputDenominator :=
    CCL.Chordal.Proj.weight (CCL.Mat2.act matrix left) *
      CCL.Chordal.Proj.weight (CCL.Mat2.act matrix right)
  have determinantPositive : 0 < determinantNorm :=
    normSq_pos determinantNonzero
  have coefficientPositive : 0 < coefficient :=
    CCL.Chordal.Mat2.actionWeightCoefficient_pos _
  have inputDenominatorPositive : 0 < inputDenominator :=
    RFAP.ConstructiveFraction.mul_pos_direct
      (CCL.Chordal.Proj.weight_pos leftValid)
      (CCL.Chordal.Proj.weight_pos rightValid)
  have leftImageValid :=
    CCL.Chordal.Mat2.act_hasNonzeroCoordinate
      determinantNonzero leftValid
  have rightImageValid :=
    CCL.Chordal.Mat2.act_hasNonzeroCoordinate
      determinantNonzero rightValid
  have outputDenominatorPositive : 0 < outputDenominator :=
    RFAP.ConstructiveFraction.mul_pos_direct
      (CCL.Chordal.Proj.weight_pos leftImageValid)
      (CCL.Chordal.Proj.weight_pos rightImageValid)
  have leftWeight := determinant_mul_weight_le_act_weight matrix left
  have rightWeight := determinant_mul_weight_le_act_weight matrix right
  have denominatorOrder :
      determinantNorm ^ 2 * inputDenominator ≤
        coefficient ^ 2 * outputDenominator := by
    have productOrder := RFAP.ConstructiveFraction.mul_le_mul_direct
      leftWeight rightWeight
      (RFAP.ConstructiveFraction.mul_nonneg_direct determinantPositive.le
        (CCL.Chordal.Proj.weight_pos rightValid).le)
      (RFAP.ConstructiveFraction.mul_nonneg_direct coefficientPositive.le
        (CCL.Chordal.Proj.weight_pos leftImageValid).le)
    calc
      determinantNorm ^ 2 * inputDenominator =
          (determinantNorm *
              CCL.Chordal.Proj.weight left) *
            (determinantNorm *
              CCL.Chordal.Proj.weight right) := by
        dsimp only [inputDenominator]
        ring1
      _ ≤ (coefficient * CCL.Chordal.Proj.weight
              (CCL.Mat2.act matrix left)) *
            (coefficient * CCL.Chordal.Proj.weight
              (CCL.Mat2.act matrix right)) := productOrder
      _ = coefficient ^ 2 * outputDenominator := by
        dsimp only [outputDenominator]
        ring1
  have numeratorNonnegative : 0 ≤ numerator := normSq_nonneg _
  have denominatorProductPositive :
      0 < determinantNorm * inputDenominator :=
    RFAP.ConstructiveFraction.mul_pos_direct determinantPositive
      inputDenominatorPositive
  rw [CCL.Chordal.Mat2.chordalSq_act]
  simp only [CCL.Chordal.chordalSq_eq_cross]
  change determinantNorm * numerator / outputDenominator ≤
    (coefficient ^ 2 / determinantNorm) *
      (numerator / inputDenominator)
  have quotientProduct :
      (coefficient ^ 2 / determinantNorm) *
          (numerator / inputDenominator) =
        (coefficient ^ 2 * numerator) /
          (determinantNorm * inputDenominator) :=
    RFAP.ConstructiveFraction.div_mul_div_direct _ _ _ _
  rw [quotientProduct]
  apply (RFAP.ConstructiveFraction.div_le_iff_pos
    outputDenominatorPositive).2
  have rightIdentity :
      ((coefficient ^ 2 * numerator) /
          (determinantNorm * inputDenominator)) * outputDenominator =
        (coefficient ^ 2 * numerator * outputDenominator) /
          (determinantNorm * inputDenominator) := by
    calc
      ((coefficient ^ 2 * numerator) /
          (determinantNorm * inputDenominator)) * outputDenominator =
          ((coefficient ^ 2 * numerator) /
            (determinantNorm * inputDenominator)) *
              (outputDenominator / 1) := by
        congr 1
        calc
          outputDenominator =
              (outputDenominator / 1) * 1 :=
            (RFAP.ConstructiveFraction.div_mul_cancel_of_ne
              outputDenominator 1 (by decide)).symm
          _ = outputDenominator / 1 :=
            RFAP.ConstructiveFraction.mul_one_direct _
      _ = ((coefficient ^ 2 * numerator) * outputDenominator) /
          ((determinantNorm * inputDenominator) * 1) :=
        RFAP.ConstructiveFraction.div_mul_div_direct _ _ _ _
      _ = (coefficient ^ 2 * numerator * outputDenominator) /
          (determinantNorm * inputDenominator) := by
        rw [RFAP.ConstructiveFraction.mul_one_direct]
  rw [rightIdentity]
  apply (RFAP.ConstructiveFraction.le_div_iff_pos
    denominatorProductPositive).2
  have scaledOrder :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      denominatorOrder numeratorNonnegative
  calc
    determinantNorm * numerator *
        (determinantNorm * inputDenominator) =
        numerator * (determinantNorm ^ 2 * inputDenominator) := by ring1
    _ ≤ numerator * (coefficient ^ 2 * outputDenominator) := scaledOrder
    _ = coefficient ^ 2 * numerator * outputDenominator := by ring1

/-- A fixed finite decoder prefix followed by `n` certified redundant blocks
has squared-chordal diameter at most `K(matrix) * 2⁻ⁿ`.  Thus any finite
annulus-free prefix distortion is absorbed by sufficiently many later
half-contracting blocks; the original raw bitstream and parser are unchanged. -/
theorem chordalSq_act_realizes_le_transportCoefficient_half_pow
    (matrix : Mat2)
    (determinantNonzero :
      CCL.CCLPullback.determinant matrix ≠ 0)
    {blocks : List CCL.RedundantBlockContraction.Block}
    {left right : Proj}
    (leftRealizes :
      CCL.RedundantBlockContraction.Realizes blocks left)
    (rightRealizes :
      CCL.RedundantBlockContraction.Realizes blocks right) :
    chordalSq (CCL.Mat2.act matrix left) (CCL.Mat2.act matrix right) ≤
      transportCoefficient matrix *
        (1 / 2 : Coordinate) ^ blocks.length := by
  calc
    chordalSq (CCL.Mat2.act matrix left) (CCL.Mat2.act matrix right) ≤
        transportCoefficient matrix * chordalSq left right :=
      chordalSq_act_le_transportCoefficient matrix determinantNonzero
        left right leftRealizes.valid rightRealizes.valid
    _ ≤ transportCoefficient matrix *
        (1 / 2 : Coordinate) ^ blocks.length :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (CCL.RedundantBlockContraction.Realizes.chordalSq_le_half_pow
          leftRealizes rightRealizes)
        (transportCoefficient_pos matrix determinantNonzero).le

/-- Trace-friendly form of the transported dyadic bound.  Successive
homogeneous residual representatives may differ projectively from the local
affine-or-`omega` contraction witnesses. -/
theorem chordalSq_act_projectiveRealizes_le_transportCoefficient_half_pow
    (matrix : Mat2)
    (determinantNonzero :
      CCL.CCLPullback.determinant matrix ≠ 0)
    {blocks : List CCL.RedundantBlockContraction.Block}
    {left right : Proj}
    (leftRealizes :
      CCL.RedundantBlockContraction.ProjectiveRealizes
        blocks left)
    (rightRealizes :
      CCL.RedundantBlockContraction.ProjectiveRealizes
        blocks right) :
    chordalSq (CCL.Mat2.act matrix left) (CCL.Mat2.act matrix right) ≤
      transportCoefficient matrix *
        (1 / 2 : Coordinate) ^ blocks.length := by
  calc
    chordalSq (CCL.Mat2.act matrix left) (CCL.Mat2.act matrix right) ≤
        transportCoefficient matrix * chordalSq left right :=
      chordalSq_act_le_transportCoefficient matrix determinantNonzero
        left right leftRealizes.valid rightRealizes.valid
    _ ≤ transportCoefficient matrix *
        (1 / 2 : Coordinate) ^ blocks.length :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (CCL.RedundantBlockContraction.ProjectiveRealizes.chordalSq_le_half_pow
          leftRealizes rightRealizes)
        (transportCoefficient_pos matrix determinantNonzero).le

/-- Coefficient displayed in the transported no-return bound. -/
def terminalCoefficient (matrix : Mat2) : Coordinate :=
  CCL.Chordal.Mat2.actionWeightCoefficient
      (CCL.CCLPullback.adjugate matrix) /
    CCL.Chordal.Proj.weight
      (CCL.Mat2.act matrix CCL.Proj.omega)

theorem terminalCoefficient_pos (matrix : Mat2)
    (determinantNonzero :
      CCL.CCLPullback.determinant matrix ≠ 0) :
    0 < terminalCoefficient matrix := by
  have imageValid := CCL.Chordal.Mat2.act_hasNonzeroCoordinate
    determinantNonzero Proj.omega_hasNonzeroCoordinate
  exact RFAP.ConstructiveFraction.div_pos_direct
    (CCL.Chordal.Mat2.actionWeightCoefficient_pos
      (CCL.CCLPullback.adjugate matrix))
    (CCL.Chordal.Proj.weight_pos imageValid)

/-- A large affine tail remains close to the decoder's terminal coordinate.
The constant depends only on the already displayed finite decoder matrix. -/
theorem chordalSq_act_affine_omega_le
    (matrix : Mat2)
    (determinantNonzero :
      CCL.CCLPullback.determinant matrix ≠ 0)
    (tail : Gaussian) :
    chordalSq
        (CCL.Mat2.act matrix (CCL.Proj.affine tail))
        (CCL.Mat2.act matrix CCL.Proj.omega) ≤
      terminalCoefficient matrix / (1 + normSq tail) := by
  let determinantNorm :=
    normSq (CCL.CCLPullback.determinant matrix)
  let coefficient :=
    CCL.Chordal.Mat2.actionWeightCoefficient
      (CCL.CCLPullback.adjugate matrix)
  let omegaWeight := CCL.Chordal.Proj.weight
    (CCL.Mat2.act matrix CCL.Proj.omega)
  let affineWeight :=
    CCL.Chordal.Proj.weight
      (CCL.Mat2.act matrix (CCL.Proj.affine tail))
  let tailWeight := 1 + normSq tail
  have determinantPositive : 0 < determinantNorm :=
    normSq_pos determinantNonzero
  have coefficientPositive : 0 < coefficient :=
    CCL.Chordal.Mat2.actionWeightCoefficient_pos _
  have omegaValid := CCL.Chordal.Mat2.act_hasNonzeroCoordinate
    determinantNonzero Proj.omega_hasNonzeroCoordinate
  have affineValid := CCL.Chordal.Mat2.act_hasNonzeroCoordinate
    determinantNonzero (Proj.affine_hasNonzeroCoordinate tail)
  have omegaPositive : 0 < omegaWeight :=
    CCL.Chordal.Proj.weight_pos omegaValid
  have affinePositive : 0 < affineWeight :=
    CCL.Chordal.Proj.weight_pos affineValid
  have tailPositive : 0 < tailWeight :=
    add_pos_of_pos_of_nonneg (by decide) (normSq_nonneg tail)
  have affineLower : determinantNorm * tailWeight ≤
      coefficient * affineWeight := by
    have lower := determinant_mul_weight_le_act_weight matrix
      (CCL.Proj.affine tail)
    simpa only [determinantNorm, coefficient, affineWeight, tailWeight,
      CCL.Chordal.Proj.weight, CCL.Proj.affine, normSq_one,
      RFAP.ConstructiveFraction.add_comm] using lower
  have denominatorOrder :
      omegaWeight * (determinantNorm * tailWeight) ≤
        coefficient * (omegaWeight * affineWeight) := by
    calc
      omegaWeight * (determinantNorm * tailWeight) ≤
          omegaWeight * (coefficient * affineWeight) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          affineLower omegaPositive.le
      _ = coefficient * (omegaWeight * affineWeight) := by ring1
  have smallDenominatorPositive :
      0 < omegaWeight * (determinantNorm * tailWeight) :=
    RFAP.ConstructiveFraction.mul_pos_direct omegaPositive
      (RFAP.ConstructiveFraction.mul_pos_direct determinantPositive
        tailPositive)
  have numeratorNonnegative : 0 ≤ coefficient * determinantNorm :=
    RFAP.ConstructiveFraction.mul_nonneg_direct coefficientPositive.le
      determinantPositive.le
  rw [CCL.Chordal.Mat2.chordalSq_truncation]
  rw [show normSq (CCL.Chordal.Mat2.det matrix) =
      determinantNorm by rfl]
  rw [show normSq matrix.a + normSq matrix.c = omegaWeight by
    dsimp only [omegaWeight]
    simp only [CCL.Chordal.Proj.weight, CCL.Mat2.act,
      CCL.Proj.omega, RFAP.ConstructiveGaussian.Gaussian.mul_one,
      RFAP.ConstructiveGaussian.Gaussian.mul_zero,
      RFAP.ConstructiveGaussian.Gaussian.add_zero]]
  rw [show
      normSq (matrix.a * tail + matrix.b) +
          normSq (matrix.c * tail + matrix.d) = affineWeight by
    dsimp only [affineWeight, CCL.Chordal.Proj.weight,
      CCL.Mat2.act, CCL.Proj.affine]
    simp only [RFAP.ConstructiveGaussian.Gaussian.mul_one]]
  change determinantNorm / (omegaWeight * affineWeight) ≤
    (coefficient / omegaWeight) / tailWeight
  calc
    determinantNorm / (omegaWeight * affineWeight) =
        (coefficient * determinantNorm) /
          (coefficient * (omegaWeight * affineWeight)) := by
      exact (RFAP.ConstructiveFraction.mul_div_mul_left_direct
        coefficient determinantNorm (omegaWeight * affineWeight)
        coefficientPositive.ne').symm
    _ ≤ (coefficient * determinantNorm) /
        (omegaWeight * (determinantNorm * tailWeight)) :=
      RFAP.ConstructiveFraction.div_le_div_of_nonneg_left_direct
        numeratorNonnegative smallDenominatorPositive denominatorOrder
    _ = coefficient / (omegaWeight * tailWeight) := by
      rw [show coefficient * determinantNorm =
          determinantNorm * coefficient by ring1,
        show omegaWeight * (determinantNorm * tailWeight) =
          determinantNorm * (omegaWeight * tailWeight) by ring1]
      exact RFAP.ConstructiveFraction.mul_div_mul_left_direct
        determinantNorm coefficient (omegaWeight * tailWeight)
        determinantPositive.ne'
    _ = (coefficient / omegaWeight) / tailWeight := by
      change coefficient / (omegaWeight * tailWeight) =
        (coefficient / omegaWeight) * tailWeight⁻¹
      calc
        coefficient / (omegaWeight * tailWeight) =
            (coefficient * 1) / (omegaWeight * tailWeight) := by
          rw [RFAP.ConstructiveFraction.mul_one_direct]
        _ = (coefficient / omegaWeight) * (1 / tailWeight) :=
          (RFAP.ConstructiveFraction.div_mul_div_direct
            coefficient omegaWeight 1 tailWeight).symm
        _ = (coefficient / omegaWeight) * tailWeight⁻¹ := by
          have oneDiv : (1 : Coordinate) / tailWeight = tailWeight⁻¹ := by
            rw [RFAP.ExplicitField.div_eq_mul_inv]
            exact RFAP.ConstructiveFraction.one_mul _
          rw [oneDiv]

/-- Full finite no-return estimate, including the exact `omega` case. -/
theorem chordalSq_act_loopTail_le
    (matrix : Mat2)
    (determinantNonzero :
      CCL.CCLPullback.determinant matrix ≠ 0)
    {count : Nat} (tail : LoopTail count) :
    chordalSq (CCL.Mat2.act matrix tail.point)
        (CCL.Mat2.act matrix CCL.Proj.omega) ≤
      terminalCoefficient matrix /
        (1 + (2 : Coordinate) ^ count) := by
  cases tail with
  | omega =>
      change chordalSq
          (CCL.Mat2.act matrix (CCL.Proj.omega : Proj))
          (CCL.Mat2.act matrix CCL.Proj.omega) ≤ _
      rw [chordalSq_eq_zero_of_equivalent (CCL.Proj.Equivalent.refl _)]
      exact RFAP.ConstructiveFraction.div_nonneg_direct
        (terminalCoefficient_pos matrix determinantNonzero).le
        (add_nonneg (by decide)
          (RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) count))
  | affine value large =>
      have transported := chordalSq_act_affine_omega_le matrix
        determinantNonzero value
      have coefficientNonnegative :=
        (terminalCoefficient_pos matrix determinantNonzero).le
      have smallPositive : 0 < 1 + (2 : Coordinate) ^ count :=
        add_pos_of_pos_of_nonneg (by decide)
          (RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) count)
      have denominatorOrder :
          1 + (2 : Coordinate) ^ count ≤ 1 + normSq value :=
        add_le_add le_rfl large.le
      exact transported.trans
        (RFAP.ConstructiveFraction.div_le_div_of_nonneg_left_direct
          coefficientNonnegative smallPositive denominatorOrder)

end CCL.TerminalPadding
