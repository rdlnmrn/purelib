import mathlib.Tactic.QuotientFreeRing
import CCL.Arithmetic.Bihomographic
import CCL.Progressive.Enclosures

/-!
# Bihomographic semantics of progressive arithmetic

The enclosure implementation computes `+`, `-`, `*`, and `/` directly on
finite rational balls.  This module proves that its candidate predicates are
the affine instances of the paper's bihomographic initial matrices and that
all input/output decoder substitutions compose exactly.  Thus the direct
implementation and the matrix account are two certified views of the same
finite arithmetic step.
-/

namespace CCL.ProgressiveBihomographic

abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Proj := CCL.GaussianProjective.Proj
abbrev Mat2 := CCL.GaussianProjective.Mat2
abbrev Process := CCL.ProgressiveEnclosures.Process
abbrev State := CCL.Bihomographic.State

open RFAP.ConstructiveGaussian.Gaussian
open CCL.Bihomographic

/-- The homogeneous division pair `[x:y]` is projectively the affine
quotient whenever the explicitly supplied denominator is nonzero. -/
theorem initial_div_equivalent (x y : Gaussian) (yNonzero : y ≠ 0) :
    CCL.Proj.Equivalent ((initial .div).affineMap x y)
      (CCL.Proj.affine (x / y)) := by
  rw [initial_div]
  unfold CCL.Proj.Equivalent CCL.Proj.affine
  simp only [RFAP.ConstructiveGaussian.Gaussian.mul_one]
  symm
  rw [RFAP.ExplicitField.div_eq_mul_inv,
    RFAP.ConstructiveGaussian.Gaussian.mul_assoc, inv_eq,
    inv_mul y yNonzero, RFAP.ConstructiveGaussian.Gaussian.mul_one]

/-- Progressive addition candidates have exactly the initial bihomographic
semantics. -/
theorem add_candidate
    (left right : Process) {state : (left.add right).State}
    {value : Gaussian} (possible : (left.add right).Possible state value) :
    ∃ x y : Gaussian,
      left.Possible state.1 x ∧ right.Possible state.2 y ∧
        CCL.Proj.Equivalent ((initial .add).affineMap x y)
          (CCL.Proj.affine value) := by
  rcases possible with ⟨x, y, xPossible, yPossible, valueEqual⟩
  refine ⟨x, y, xPossible, yPossible, ?_⟩
  rw [valueEqual, initial_add]
  exact CCL.Proj.Equivalent.refl _

/-- Progressive subtraction candidates have exactly the initial
bihomographic semantics. -/
theorem sub_candidate
    (left right : Process) {state : (left.sub right).State}
    {value : Gaussian} (possible : (left.sub right).Possible state value) :
    ∃ x y : Gaussian,
      left.Possible state.1 x ∧ right.Possible state.2 y ∧
        CCL.Proj.Equivalent ((initial .sub).affineMap x y)
          (CCL.Proj.affine value) := by
  rcases possible with
    ⟨x, negativeY, xPossible, ⟨y, yPossible, negativeEqual⟩, valueEqual⟩
  refine ⟨x, y, xPossible, yPossible, ?_⟩
  have subtraction : x + -y = x - y := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [add_re, add_im, neg_re, neg_im, sub_re, sub_im] <;> ring1
  rw [negativeEqual, subtraction] at valueEqual
  rw [valueEqual, initial_sub]
  exact CCL.Proj.Equivalent.refl _

/-- Progressive multiplication candidates have exactly the initial
bihomographic semantics. -/
theorem mul_candidate
    (left right : Process) {state : (left.mul right).State}
    {value : Gaussian} (possible : (left.mul right).Possible state value) :
    ∃ x y : Gaussian,
      left.Possible state.1 x ∧ right.Possible state.2 y ∧
        CCL.Proj.Equivalent ((initial .mul).affineMap x y)
          (CCL.Proj.affine value) := by
  rcases possible with ⟨x, y, xPossible, yPossible, valueEqual⟩
  refine ⟨x, y, xPossible, yPossible, ?_⟩
  rw [valueEqual, initial_mul]
  exact CCL.Proj.Equivalent.refl _

/-- Apartness-certified progressive division candidates have exactly the
projective initial division semantics and an affine quotient. -/
theorem div_candidate
    (left right : Process)
    (apart : CCL.ProgressiveEnclosures.Process.Apart right)
    {state : (left.div right apart).State} {value : Gaussian}
    (possible : (left.div right apart).Possible state value) :
    ∃ x y : Gaussian,
      left.Possible state.1 x ∧ right.Possible state.2 y ∧ y ≠ 0 ∧
        CCL.Proj.Equivalent ((initial .div).affineMap x y)
          (CCL.Proj.affine value) := by
  rcases possible with ⟨x, y, xPossible, yPossible, valueEqual⟩
  have lower := apart.lower state.2 (right.possible_inside yPossible)
  have normPositive : 0 < normSq y := apart.positive.trans_le lower
  have yNonzero : y ≠ 0 := by
    intro yZero
    rw [yZero, normSq_zero] at normPositive
    exact (lt_irrefl _ normPositive).elim
  refine ⟨x, y, xPossible, yPossible, yNonzero, ?_⟩
  rw [valueEqual]
  exact initial_div_equivalent x y yNonzero

/-- Consuming one matrix from each input is exact, independent of the
elementary operation represented by the eight coefficients. -/
theorem map_precompose_both (state : State) (left right : Mat2)
    (x y : Proj) :
    ((state.precomposeLeft left).precomposeRight right).map x y =
      state.map (CCL.Mat2.act left x) (CCL.Mat2.act right y) := by
  rw [State.map_precomposeRight, State.map_precomposeLeft]

/-- Input consumption followed by an output chart change is one exact
projective identity. -/
theorem map_full_substitution (state : State) (left right output : Mat2)
    (x y : Proj) :
    (((state.precomposeLeft left).precomposeRight right).postcompose output).map
        x y =
      CCL.Mat2.act output
        (state.map (CCL.Mat2.act left x) (CCL.Mat2.act right y)) := by
  rw [State.map_postcompose, map_precompose_both]

/-- In particular, emitting an output decoder block uses its explicit
adjugate while input blocks are precomposed in their respective variables. -/
theorem map_after_emitted_block (state : State) (left right block : Mat2)
    (x y : Proj) :
    (((state.precomposeLeft left).precomposeRight right).postcompose
        (CCL.CCLPullback.adjugate block)).map x y =
      CCL.Mat2.act (CCL.CCLPullback.adjugate block)
        (state.map (CCL.Mat2.act left x) (CCL.Mat2.act right y)) :=
  map_full_substitution state left right
    (CCL.CCLPullback.adjugate block) x y

end CCL.ProgressiveBihomographic
