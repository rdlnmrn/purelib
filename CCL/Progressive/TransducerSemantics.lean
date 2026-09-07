import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import CCL.Encoding.ParserStep
import CCL.Progressive.Transducer
import CCL.Arithmetic.RedundantBlockContraction

/-!
# Exact semantics of redundant progressive CCL blocks

The arithmetic controller is allowed to select an overlapping safe sector
outside the canonical half-open annulus table.  This file proves that doing
so does not alter the represented point.  Local safety alone gives both the
exact inverse chart and the strict lower norm needed by the following loop.

The zero-residual case is kept projective.  It maps exactly to the completed
block's `omega` tail and can therefore emit the productive unary padding of
`TerminalPadding` without deciding equality.
-/

namespace CCL.ProgressiveTransducerSemantics

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Sector := CCL.Sectors.Sector
abbrev Proj := CCL.GaussianProjective.Proj

open RFAP.ConstructiveGaussian.Gaussian
open CCL.RawParser

/-- The enlarged safe cell, not canonical annulus membership, is the exact
local hypothesis needed for a nonterminal redundant block. -/
theorem safeBlock_sufficient
    (kind : BlockKind) (exponent : Nat) (sector : Sector) (value : Gaussian)
    (safe : CCL.RedundantSectors.Safe sector
      (normalizedValue kind exponent value))
    (residualNonzero :
      normalizedValue kind exponent value - sector.rep ≠ 0) :
    homographic (blockMatrix kind exponent sector)
        ((gamma *
          (normalizedValue kind exponent value - sector.rep))⁻¹) = value ∧
      1 < normSq
        ((gamma *
          (normalizedValue kind exponent value - sector.rep))⁻¹) :=
  ⟨CCL.ParserStep.block_homographic_inverse
      kind exponent sector value residualNonzero,
    CCL.RedundantSectors.postInversion_norm_gt_one
      safe residualNonzero⟩

/-- Total projective continuation of one redundant safe block.  The
construction uses `ω` exactly when the displayed rational residual is zero
and otherwise uses the ordinary affine inverse tail. -/
def safeBlockTail
    (kind : BlockKind) (exponent : Nat) (sector : Sector) (value : Gaussian)
    (normLower : 1 ≤ normSq (normalizedValue kind exponent value))
    (safe : CCL.RedundantSectors.Safe sector
      (normalizedValue kind exponent value)) :
    CCL.RedundantBlockContraction.Tail sector :=
  CCL.RedundantBlockContraction.Tail.ofSafe sector
    (normalizedValue kind exponent value) normLower safe

theorem safeBlockTail_models
    (kind : BlockKind) (exponent : Nat) (sector : Sector) (value : Gaussian)
    (normLower : 1 ≤ normSq (normalizedValue kind exponent value))
    (safe : CCL.RedundantSectors.Safe sector
      (normalizedValue kind exponent value)) :
    (safeBlockTail kind exponent sector value normLower safe).ModelsValue
      (normalizedValue kind exponent value) :=
  CCL.RedundantBlockContraction.Tail.ofSafe_models sector
    (normalizedValue kind exponent value) normLower safe

/-- The total affine-or-`ω` redundant tail reconstructs the pre-block value
exactly through the unchanged ordinary CCL block matrix. -/
theorem safeBlockTail_exact
    (kind : BlockKind) (exponent : Nat) (sector : Sector) (value : Gaussian)
    (normLower : 1 ≤ normSq (normalizedValue kind exponent value))
    (safe : CCL.RedundantSectors.Safe sector
      (normalizedValue kind exponent value)) :
    CCL.Proj.Equivalent
      (CCL.Mat2.act (blockMatrix kind exponent sector)
        (safeBlockTail kind exponent sector value normLower safe).point)
      (CCL.Proj.affine value) := by
  let tail := safeBlockTail kind exponent sector value normLower safe
  have models : tail.ModelsValue (normalizedValue kind exponent value) :=
    safeBlockTail_models kind exponent sector value normLower safe
  cases kind with
  | initialLow =>
      exact
        CCL.RedundantBlockContraction.Tail.lowBlock_act_equivalent
          exponent tail (normalizedValue .initialLow exponent value) value
          models rfl
  | initialHigh | loop =>
      have gammaNonzero : gamma ≠ 0 := by decide
      let power := natPow gamma exponent
      have powerNonzero : power ≠ 0 :=
        natPow_ne_zero_direct gamma gammaNonzero exponent
      have cancellation : power⁻¹ * power = 1 := by
        exact RFAP.CanonicalGaussian.Gaussian.inv_mul_cancel
          power powerNonzero
      have targetIdentity :
          power * normalizedValue .initialHigh exponent value = value := by
        simp only [normalizedValue, power]
        calc
          power * (value * power⁻¹) = value * (power⁻¹ * power) := by
            apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
              simp only [mul_re, mul_im] <;> ring1
          _ = value := by
            rw [cancellation, RFAP.ConstructiveGaussian.Gaussian.mul_one]
      simpa only [blockMatrix] using
        CCL.RedundantBlockContraction.Tail.regularBlock_act_equivalent
          exponent tail (normalizedValue .initialHigh exponent value) value
          models targetIdentity

/-- A completed ordinary block reconstructs its input from the single
homogeneous residual formula.  Safety and a radial lower bound are needed
for contraction, but not for this algebraic identity. -/
theorem blockHomogeneous_exact
    (kind : BlockKind) (exponent : Nat) (sector : Sector) (value : Gaussian) :
    CCL.Proj.Equivalent
      (CCL.Mat2.act (blockMatrix kind exponent sector)
        ⟨1, gamma * (normalizedValue kind exponent value - sector.rep)⟩)
      (CCL.Proj.affine value) := by
  cases kind with
  | initialHigh | loop =>
      let power := natPow gamma exponent
      have powerNonzero : power ≠ 0 :=
        natPow_ne_zero_direct gamma (by decide) exponent
      have cancellation : power * power⁻¹ = 1 :=
        RFAP.CanonicalGaussian.Gaussian.mul_inv_cancel power powerNonzero
      simp only [blockMatrix, CCL.Decoder.regularBlock,
        CCL.Mat2.act, CCL.Proj.Equivalent, CCL.Proj.affine,
        normalizedValue, natPow_succ,
        RFAP.ConstructiveGaussian.Gaussian.mul_one,
        RFAP.ConstructiveGaussian.Gaussian.zero_mul,
        RFAP.ConstructiveGaussian.Gaussian.add_zero]
      change power * gamma * sector.rep +
          power * (gamma * (value * power⁻¹ - sector.rep)) = value * gamma
      calc
        power * gamma * sector.rep +
            power * (gamma * (value * power⁻¹ - sector.rep)) =
            (power * power⁻¹) * (value * gamma) := by
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [add_re, add_im, sub_re, sub_im, mul_re, mul_im] <;>
            ring1
        _ = value * gamma := by
          rw [cancellation, RFAP.ConstructiveGaussian.Gaussian.one_mul]
  | initialLow =>
      let power := natPow gamma exponent
      simp only [blockMatrix, CCL.Decoder.lowBlock,
        CCL.Mat2.act, CCL.Proj.Equivalent, CCL.Proj.affine,
        normalizedValue, natPow_succ,
        RFAP.ConstructiveGaussian.Gaussian.mul_one,
        RFAP.ConstructiveGaussian.Gaussian.one_mul,
        RFAP.ConstructiveGaussian.Gaussian.zero_mul,
        RFAP.ConstructiveGaussian.Gaussian.add_zero]
      change gamma * sector.rep + gamma * (power * value - sector.rep) =
        value * (power * gamma)
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [add_re, add_im, sub_re, sub_im, mul_re, mul_im] <;>
        ring1

/-- The same total safe-block semantics in the homogeneous residual form
carried by a progressive residual mode.  This statement deliberately does
not decide whether the residual is zero. -/
theorem safeBlockHomogeneous_exact
    (kind : BlockKind) (exponent : Nat) (sector : Sector) (value : Gaussian)
    (normLower : 1 ≤ normSq (normalizedValue kind exponent value))
    (safe : CCL.RedundantSectors.Safe sector
      (normalizedValue kind exponent value)) :
    CCL.Proj.Equivalent
      (CCL.Mat2.act (blockMatrix kind exponent sector)
        ⟨1, gamma * (normalizedValue kind exponent value - sector.rep)⟩)
      (CCL.Proj.affine value) := by
  let tail := safeBlockTail kind exponent sector value normLower safe
  have tailToHomogeneous : tail.point.Equivalent
      ⟨1, gamma * (normalizedValue kind exponent value - sector.rep)⟩ :=
    CCL.RedundantBlockContraction.Tail.ofSafe_point_equivalent_homogeneous
      sector (normalizedValue kind exponent value) normLower safe
  have homogeneousToTail := CCL.Mat2.act_respects_equivalent
    (blockMatrix kind exponent sector) tailToHomogeneous.symm
  have exact := safeBlockTail_exact kind exponent sector value normLower safe
  exact CCL.Chordal.Proj.equivalent_trans
    homogeneousToTail exact
    (CCL.Chordal.Mat2.act_hasNonzeroCoordinate
      (CCL.RawParser.blockMatrix_det_ne kind exponent sector)
      tail.point_valid)
    (CCL.Chordal.Proj.affine_hasNonzeroCoordinate value)

/-- Ordinary syntax kind corresponding to the weakened redundant block
predicate.  Both high/loop blocks retain the ordinary regular matrix. -/
def redundantBlock (kind : BlockKind) (exponent : Nat) (sector : Sector) :
    CCL.RedundantBlockContraction.Block :=
  { kind := match kind with
      | .initialLow => .initialLow
      | .initialHigh | .loop => .regular
    exponent := exponent
    sector := sector }

@[simp] theorem redundantBlock_matrix
    (kind : BlockKind) (exponent : Nat) (sector : Sector) :
    (redundantBlock kind exponent sector).matrix =
      blockMatrix kind exponent sector := by
  cases kind <;> rfl

/-- Any two total projective continuations justified by the same redundant
digit lie in the same half-contracting ordinary CCL block cylinder. -/
theorem safeBlockTail_pair_contraction
    (kind : BlockKind) (exponent : Nat) (sector : Sector)
    (left right : Gaussian)
    (leftNorm : 1 ≤ normSq (normalizedValue kind exponent left))
    (rightNorm : 1 ≤ normSq (normalizedValue kind exponent right))
    (leftSafe : CCL.RedundantSectors.Safe sector
      (normalizedValue kind exponent left))
    (rightSafe : CCL.RedundantSectors.Safe sector
      (normalizedValue kind exponent right)) :
    CCL.Chordal.chordalSq
        (CCL.Mat2.act (blockMatrix kind exponent sector)
          (safeBlockTail kind exponent sector left leftNorm leftSafe).point)
        (CCL.Mat2.act (blockMatrix kind exponent sector)
          (safeBlockTail kind exponent sector right rightNorm rightSafe).point) ≤
      (1 / 2 : Coordinate) *
        CCL.Chordal.chordalSq
          (safeBlockTail kind exponent sector left leftNorm leftSafe).point
          (safeBlockTail kind exponent sector right rightNorm rightSafe).point := by
  rw [← redundantBlock_matrix kind exponent sector]
  exact (redundantBlock kind exponent sector).contraction_half
    (safeBlockTail kind exponent sector left leftNorm leftSafe)
    (safeBlockTail kind exponent sector right rightNorm rightSafe)

/-- The same half contraction stated directly for the homogeneous residual
tails carried by the progressive machine.  This removes the implementation
branch between an affine reciprocal and `omega` from quantitative clients. -/
theorem safeBlockHomogeneous_pair_contraction
    (kind : BlockKind) (exponent : Nat) (sector : Sector)
    (left right : Gaussian)
    (leftNorm : 1 ≤ normSq (normalizedValue kind exponent left))
    (rightNorm : 1 ≤ normSq (normalizedValue kind exponent right))
    (leftSafe : CCL.RedundantSectors.Safe sector
      (normalizedValue kind exponent left))
    (rightSafe : CCL.RedundantSectors.Safe sector
      (normalizedValue kind exponent right)) :
    let leftHomogeneous : CCL.GaussianProjective.Proj :=
      ⟨1, gamma * (normalizedValue kind exponent left - sector.rep)⟩
    let rightHomogeneous : CCL.GaussianProjective.Proj :=
      ⟨1, gamma * (normalizedValue kind exponent right - sector.rep)⟩
    CCL.Chordal.chordalSq
        (CCL.Mat2.act (blockMatrix kind exponent sector) leftHomogeneous)
        (CCL.Mat2.act (blockMatrix kind exponent sector) rightHomogeneous) ≤
      (1 / 2 : Coordinate) *
        CCL.Chordal.chordalSq
          leftHomogeneous rightHomogeneous := by
  dsimp only
  let leftTail :=
    safeBlockTail kind exponent sector left leftNorm leftSafe
  let rightTail :=
    safeBlockTail kind exponent sector right rightNorm rightSafe
  let leftHomogeneous : CCL.GaussianProjective.Proj :=
    ⟨1, gamma * (normalizedValue kind exponent left - sector.rep)⟩
  let rightHomogeneous : CCL.GaussianProjective.Proj :=
    ⟨1, gamma * (normalizedValue kind exponent right - sector.rep)⟩
  have leftEquivalent : leftTail.point.Equivalent leftHomogeneous := by
    exact
      CCL.RedundantBlockContraction.Tail.ofSafe_point_equivalent_homogeneous sector
          (normalizedValue kind exponent left) leftNorm leftSafe
  have rightEquivalent : rightTail.point.Equivalent rightHomogeneous := by
    exact
      CCL.RedundantBlockContraction.Tail.ofSafe_point_equivalent_homogeneous sector
          (normalizedValue kind exponent right) rightNorm rightSafe
  have leftTailValid := leftTail.point_valid
  have rightTailValid := rightTail.point_valid
  have leftHomogeneousValid :
      CCL.Chordal.Proj.HasNonzeroCoordinate leftHomogeneous :=
    by
      change (1 : Gaussian) ≠ 0 ∨ _
      exact Or.inl one_ne_zero
  have rightHomogeneousValid :
      CCL.Chordal.Proj.HasNonzeroCoordinate rightHomogeneous :=
    by
      change (1 : Gaussian) ≠ 0 ∨ _
      exact Or.inl one_ne_zero
  have determinantNonzero :=
    CCL.RawParser.blockMatrix_det_ne kind exponent sector
  have leftActEquivalent := CCL.Mat2.act_respects_equivalent
    (blockMatrix kind exponent sector) leftEquivalent
  have rightActEquivalent := CCL.Mat2.act_respects_equivalent
    (blockMatrix kind exponent sector) rightEquivalent
  have leftTailImageValid :=
    CCL.Chordal.Mat2.act_hasNonzeroCoordinate
      determinantNonzero leftTailValid
  have rightTailImageValid :=
    CCL.Chordal.Mat2.act_hasNonzeroCoordinate
      determinantNonzero rightTailValid
  have leftHomogeneousImageValid :=
    CCL.Chordal.Mat2.act_hasNonzeroCoordinate
      determinantNonzero leftHomogeneousValid
  have rightHomogeneousImageValid :=
    CCL.Chordal.Mat2.act_hasNonzeroCoordinate
      determinantNonzero rightHomogeneousValid
  have inputIdentity :
      CCL.Chordal.chordalSq leftTail.point rightTail.point =
        CCL.Chordal.chordalSq
          leftHomogeneous rightHomogeneous := by
    calc
      CCL.Chordal.chordalSq leftTail.point rightTail.point =
          CCL.Chordal.chordalSq
            leftHomogeneous rightTail.point :=
        CCL.Chordal.chordalSq_eq_of_equivalent_left
          leftTailValid leftHomogeneousValid leftEquivalent rightTail.point
      _ = CCL.Chordal.chordalSq
          leftHomogeneous rightHomogeneous :=
        CCL.Chordal.chordalSq_eq_of_equivalent_right
          rightTailValid rightHomogeneousValid rightEquivalent leftHomogeneous
  have outputIdentity :
      CCL.Chordal.chordalSq
          (CCL.Mat2.act (blockMatrix kind exponent sector) leftTail.point)
          (CCL.Mat2.act (blockMatrix kind exponent sector) rightTail.point) =
        CCL.Chordal.chordalSq
          (CCL.Mat2.act (blockMatrix kind exponent sector) leftHomogeneous)
          (CCL.Mat2.act (blockMatrix kind exponent sector)
            rightHomogeneous) := by
    calc
      CCL.Chordal.chordalSq
          (CCL.Mat2.act (blockMatrix kind exponent sector) leftTail.point)
          (CCL.Mat2.act (blockMatrix kind exponent sector) rightTail.point) =
          CCL.Chordal.chordalSq
            (CCL.Mat2.act (blockMatrix kind exponent sector) leftHomogeneous)
            (CCL.Mat2.act (blockMatrix kind exponent sector) rightTail.point) :=
        CCL.Chordal.chordalSq_eq_of_equivalent_left
          leftTailImageValid leftHomogeneousImageValid leftActEquivalent _
      _ = CCL.Chordal.chordalSq
          (CCL.Mat2.act (blockMatrix kind exponent sector) leftHomogeneous)
          (CCL.Mat2.act (blockMatrix kind exponent sector)
            rightHomogeneous) :=
        CCL.Chordal.chordalSq_eq_of_equivalent_right
          rightTailImageValid rightHomogeneousImageValid rightActEquivalent _
  rw [← outputIdentity, ← inputIdentity]
  exact safeBlockTail_pair_contraction kind exponent sector left right
    leftNorm rightNorm leftSafe rightSafe

/-- A zero normalized residual is represented exactly by the completed
block's projective `omega` tail.  This is the no-return arithmetic case; it
does not assert or decide that an opaque completed input equals a rational. -/
theorem terminalBlock_exact
    (kind : BlockKind) (exponent : Nat) (sector : Sector) (value : Gaussian)
    (residualZero :
      normalizedValue kind exponent value - sector.rep = 0) :
    CCL.Proj.Equivalent
      (CCL.Mat2.act (blockMatrix kind exponent sector) CCL.Proj.omega)
      (CCL.Proj.affine value) := by
  have normalizedEqual :
      normalizedValue kind exponent value = sector.rep :=
    sub_eq_zero.mp residualZero
  have gammaNonzero : gamma ≠ 0 := by decide
  cases kind with
  | initialHigh | loop =>
      let power := natPow gamma exponent
      have powerNonzero : power ≠ 0 :=
        natPow_ne_zero_direct gamma gammaNonzero exponent
      have scaled : value * power⁻¹ = sector.rep := by
        simpa only [normalizedValue, power] using normalizedEqual
      have valueIdentity : value = power * sector.rep := by
        have cancellation : power⁻¹ * power = 1 := by
          exact RFAP.CanonicalGaussian.Gaussian.inv_mul_cancel
            power powerNonzero
        calc
          value = value * (power⁻¹ * power) := by
            rw [cancellation,
              RFAP.ConstructiveGaussian.Gaussian.mul_one]
          _ = (value * power⁻¹) * power :=
            (RFAP.ConstructiveGaussian.Gaussian.mul_assoc _ _ _).symm
          _ = sector.rep * power := by rw [scaled]
          _ = power * sector.rep :=
            RFAP.ConstructiveGaussian.Gaussian.mul_comm _ _
      simp only [blockMatrix, CCL.Decoder.regularBlock,
        CCL.Mat2.act, CCL.Proj.omega, CCL.Proj.affine,
        CCL.Proj.Equivalent,
        RFAP.ConstructiveGaussian.Gaussian.mul_one,
        RFAP.ConstructiveGaussian.Gaussian.mul_zero,
        RFAP.ConstructiveGaussian.Gaussian.add_zero]
      rw [natPow_succ, valueIdentity]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [mul_re, mul_im] <;> ring1
  | initialLow =>
      let power := natPow gamma exponent
      have scaled : power * value = sector.rep := by
        simpa only [normalizedValue, power] using normalizedEqual
      simp only [blockMatrix, CCL.Decoder.lowBlock,
        CCL.Mat2.act, CCL.Proj.omega, CCL.Proj.affine,
        CCL.Proj.Equivalent,
        RFAP.ConstructiveGaussian.Gaussian.mul_one,
        RFAP.ConstructiveGaussian.Gaussian.mul_zero,
        RFAP.ConstructiveGaussian.Gaussian.add_zero]
      rw [natPow_succ, ← scaled]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [mul_re, mul_im] <;> ring1

/-- The affine evaluation of a matrix is projectively identical to its
homographic value whenever the displayed denominator is nonzero. -/
theorem actAffine_equivalent_homographic
    (matrix : CCL.GaussianProjective.Mat2) (tail value : Gaussian)
    (denominatorNonzero : denominator matrix tail ≠ 0)
    (evaluates : homographic matrix tail = value) :
    CCL.Proj.Equivalent
      (CCL.Mat2.act matrix (CCL.Proj.affine tail))
      (CCL.Proj.affine value) := by
  have cancellation :
      homographic matrix tail * denominator matrix tail =
        numerator matrix tail := by
    unfold homographic
    rw [RFAP.ConstructiveGaussian.Gaussian.mul_assoc, inv_eq,
      inv_mul _ denominatorNonzero,
      RFAP.ConstructiveGaussian.Gaussian.mul_one]
  rw [evaluates] at cancellation
  dsimp only [CCL.Proj.Equivalent, CCL.Mat2.act, CCL.Proj.affine,
    numerator, denominator]
  simp only [RFAP.ConstructiveGaussian.Gaussian.mul_one]
  exact cancellation.symm

/-- In the exact-zero residual case the completed block reconstructs exactly
from `omega`, and every requested no-return padding length has the explicit
dyadic chordal estimate. -/
theorem terminalBlock_exact_and_bounded
    (kind : BlockKind) (exponent count : Nat) (sector : Sector)
    (value : Gaussian)
    (residualZero : normalizedValue kind exponent value - sector.rep = 0) :
    CCL.Proj.Equivalent
        (CCL.Mat2.act (blockMatrix kind exponent sector) CCL.Proj.omega)
        (CCL.Proj.affine value) ∧
      CCL.Chordal.chordalSq CCL.Proj.omega CCL.Proj.omega ≤
        1 / (1 + (2 : Coordinate) ^ count) :=
  And.intro (terminalBlock_exact kind exponent sector value residualZero)
    (CCL.TerminalPadding.LoopTail.chordalSq_omega_le
      (CCL.TerminalPadding.LoopTail.omega (count := count)))

/-- In the nonzero residual case a finite small-ball certificate supplies the
same dyadic estimate for the exact affine inverse tail. -/
theorem affineSmallResidual_exact_and_bounded
    (kind : BlockKind) (exponent count : Nat) (sector : Sector)
    (value : Gaussian) (ball : CCL.ArithmeticEnclosures.Ball)
    (small : CCL.ResidualDecision.SmallBall ball
      (CCL.ResidualDecision.paddingTarget count))
    (inside : ball.Contains
      (normalizedValue kind exponent value - sector.rep))
    (residualNonzero :
      normalizedValue kind exponent value - sector.rep ≠ 0) :
    let tail := (gamma *
      (normalizedValue kind exponent value - sector.rep))⁻¹
    CCL.Proj.Equivalent
        (CCL.Mat2.act (blockMatrix kind exponent sector)
          (CCL.Proj.affine tail))
        (CCL.Proj.affine value) ∧
      CCL.Chordal.chordalSq
          (CCL.Proj.affine tail) CCL.Proj.omega ≤
        1 / (1 + (2 : Coordinate) ^ count) := by
  let residual := normalizedValue kind exponent value - sector.rep
  let tail := (gamma * residual)⁻¹
  have denominatorNonzero :=
    CCL.ParserStep.block_inverse_denominator_ne
      kind exponent sector value residualNonzero
  have evaluation := CCL.ParserStep.block_homographic_inverse
    kind exponent sector value residualNonzero
  have exactAffine := actAffine_equivalent_homographic
    (blockMatrix kind exponent sector) tail value denominatorNonzero evaluation
  have large := CCL.ResidualDecision.inverseTail_large
    residualNonzero
      (CCL.ResidualDecision.normSq_lt_of_contains small inside)
  exact And.intro exactAffine
    (CCL.TerminalPadding.LoopTail.chordalSq_omega_le
      (CCL.TerminalPadding.LoopTail.affine tail large))

end CCL.ProgressiveTransducerSemantics
