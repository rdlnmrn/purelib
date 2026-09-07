import mathlib.Tactic.QuotientFreeRing
import CCL.Calculus.Logarithmic

/-!
# Executable first jets and forward differentiation

A `FirstJet` is just two displayed Gaussian rationals: a value and its
first-order coefficient.  It is not a function graph, germ, infinitesimal,
or equivalence class.  The operations below are finite programs implementing
the sum, product, chain, reciprocal, and quotient rules.

`JetExpression` is finite syntax.  Its evaluator computes the value and
first-order coefficient together.  Exponential and logarithm nodes call the
finite sample programs from the preceding calculus modules at the requested
natural depth.
-/

namespace CCL.FirstOrderJet

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Equivalent := CCL.OperationalEquivalence.Equivalent

open RFAP.ConstructiveGaussian.Gaussian

/-- A displayed value and one displayed first-order coefficient. -/
structure FirstJet where
  value : Gaussian
  slope : Gaussian
deriving DecidableEq

namespace FirstJet

def constant (value : Gaussian) : FirstJet := ⟨value, 0⟩

def independent (value : Gaussian) : FirstJet := ⟨value, 1⟩

def add (left right : FirstJet) : FirstJet :=
  ⟨left.value + right.value, left.slope + right.slope⟩

def neg (jet : FirstJet) : FirstJet := ⟨-jet.value, -jet.slope⟩

def sub (left right : FirstJet) : FirstJet := add left (neg right)

/-- The finite product rule. -/
def mul (left right : FirstJet) : FirstJet :=
  ⟨left.value * right.value,
    left.slope * right.value + left.value * right.slope⟩

/-- The finite reciprocal rule.  Semantic use is guarded by a displayed
nonzero certificate, although Gaussian-rational inversion itself is total. -/
def reciprocal (jet : FirstJet) : FirstJet :=
  ⟨jet.value⁻¹, -(jet.slope * (jet.value⁻¹ * jet.value⁻¹))⟩

def div (numerator denominator : FirstJet) : FirstJet :=
  mul numerator (reciprocal denominator)

/-- The finite chain rule.  `outer` has already been evaluated at the inner
value, so only the two displayed coefficients are multiplied. -/
def compose (outer inner : FirstJet) : FirstJet :=
  ⟨outer.value, inner.slope * outer.slope⟩

@[simp] theorem constant_value (value : Gaussian) :
    (constant value).value = value := rfl

@[simp] theorem constant_slope (value : Gaussian) :
    (constant value).slope = 0 := rfl

@[simp] theorem independent_value (value : Gaussian) :
    (independent value).value = value := rfl

@[simp] theorem independent_slope (value : Gaussian) :
    (independent value).slope = 1 := rfl

@[simp] theorem add_slope (left right : FirstJet) :
    (add left right).slope = left.slope + right.slope := rfl

@[simp] theorem neg_slope (jet : FirstJet) :
    (neg jet).slope = -jet.slope := rfl

@[simp] theorem mul_slope (left right : FirstJet) :
    (mul left right).slope =
      left.slope * right.value + left.value * right.slope := rfl

@[simp] theorem reciprocal_slope (jet : FirstJet) :
    jet.reciprocal.slope =
      -(jet.slope * (jet.value⁻¹ * jet.value⁻¹)) := rfl

@[simp] theorem compose_slope (outer inner : FirstJet) :
    (compose outer inner).slope = inner.slope * outer.slope := rfl

/-- The reciprocal coefficient cancels to the negative input coefficient
after multiplication by the displayed denominator square. -/
theorem reciprocal_slope_mul_square (jet : FirstJet)
    (nonzero : jet.value ≠ 0) :
    jet.reciprocal.slope * jet.value ^ 2 = -jet.slope := by
  have inverseCancel : jet.value⁻¹ * jet.value = 1 := by
    simpa only [RFAP.ConstructiveGaussian.Gaussian.inv_eq] using
      RFAP.ConstructiveGaussian.Gaussian.inv_mul jet.value nonzero
  rw [reciprocal_slope, pow_two]
  calc
    -(jet.slope * (jet.value⁻¹ * jet.value⁻¹)) *
          (jet.value * jet.value) =
        -jet.slope *
          ((jet.value⁻¹ * jet.value) *
            (jet.value⁻¹ * jet.value)) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [neg_re, neg_im, mul_re, mul_im] <;> ring1
    _ = -jet.slope := by
      rw [inverseCancel, RFAP.ConstructiveGaussian.Gaussian.one_mul,
        RFAP.ConstructiveGaussian.Gaussian.mul_one]

end FirstJet

/-! ## Finite expression syntax and one-pass differentiation -/

inductive JetExpression where
  | constant : Gaussian → JetExpression
  | input : JetExpression
  | add : JetExpression → JetExpression → JetExpression
  | neg : JetExpression → JetExpression
  | mul : JetExpression → JetExpression → JetExpression
  | reciprocal : JetExpression → JetExpression
  | exponential : JetExpression → JetExpression
  | logarithm1p : JetExpression → JetExpression
deriving DecidableEq

namespace JetExpression

/-- Ordinary finite-depth value evaluation. -/
def eval : JetExpression → Gaussian → Nat → Gaussian
  | .constant value, _, _ => value
  | .input, point, _ => point
  | .add left right, point, index =>
      left.eval point index + right.eval point index
  | .neg expression, point, index => -expression.eval point index
  | .mul left right, point, index =>
      left.eval point index * right.eval point index
  | .reciprocal expression, point, index =>
      (expression.eval point index)⁻¹
  | .exponential expression, point, index =>
      CCL.FiniteExp.sample (expression.eval point index) index
  | .logarithm1p expression, point, index =>
      CCL.LogarithmicCalculus.log1pSample
        (expression.eval point index) index

/-- Forward automatic differentiation.  The recursive call returns exactly
two Gaussian rationals, and no function-valued derivative is constructed. -/
def jet : JetExpression → Gaussian → Nat → FirstJet
  | .constant value, _, _ => FirstJet.constant value
  | .input, point, _ => FirstJet.independent point
  | .add left right, point, index =>
      FirstJet.add (left.jet point index) (right.jet point index)
  | .neg expression, point, index =>
      FirstJet.neg (expression.jet point index)
  | .mul left right, point, index =>
      FirstJet.mul (left.jet point index) (right.jet point index)
  | .reciprocal expression, point, index =>
      FirstJet.reciprocal (expression.jet point index)
  | .exponential expression, point, index =>
      let inner := expression.jet point index
      FirstJet.compose
        ⟨CCL.FiniteExp.sample inner.value index,
          CCL.FiniteExp.sample inner.value index⟩ inner
  | .logarithm1p expression, point, index =>
      let inner := expression.jet point index
      FirstJet.compose
        ⟨CCL.LogarithmicCalculus.log1pSample inner.value index,
          CCL.LogarithmicCalculus.log1pDerivativeSample
            inner.value index⟩ inner

/-- Forward differentiation leaves the ordinary displayed value unchanged. -/
theorem jet_value (expression : JetExpression) (point : Gaussian)
    (index : Nat) :
    (expression.jet point index).value = expression.eval point index := by
  induction expression with
  | constant value => rfl
  | input => rfl
  | add left right leftInduction rightInduction =>
      simp only [jet, eval, FirstJet.add]
      rw [leftInduction, rightInduction]
  | neg expression inductionHypothesis =>
      simp only [jet, eval, FirstJet.neg]
      rw [inductionHypothesis]
  | mul left right leftInduction rightInduction =>
      simp only [jet, eval, FirstJet.mul]
      rw [leftInduction, rightInduction]
  | reciprocal expression inductionHypothesis =>
      simp only [jet, eval, FirstJet.reciprocal]
      rw [inductionHypothesis]
  | exponential expression inductionHypothesis =>
      simp only [jet, eval, FirstJet.compose]
      rw [inductionHypothesis]
  | logarithm1p expression inductionHypothesis =>
      simp only [jet, eval, FirstJet.compose]
      rw [inductionHypothesis]

@[simp] theorem jet_add_slope (left right : JetExpression)
    (input : Gaussian) (index : Nat) :
    ((left.add right).jet input index).slope =
      (left.jet input index).slope + (right.jet input index).slope := rfl

@[simp] theorem jet_mul_slope (left right : JetExpression)
    (input : Gaussian) (index : Nat) :
    ((left.mul right).jet input index).slope =
      (left.jet input index).slope * right.eval input index +
        left.eval input index * (right.jet input index).slope := by
  simp only [jet, FirstJet.mul]
  rw [jet_value, jet_value]

@[simp] theorem jet_reciprocal_slope (expression : JetExpression)
    (input : Gaussian) (index : Nat) :
    (expression.reciprocal.jet input index).slope =
      -((expression.jet input index).slope *
        ((expression.eval input index)⁻¹ *
          (expression.eval input index)⁻¹)) := by
  simp only [jet, FirstJet.reciprocal]
  rw [jet_value]

/-- The exponential node uses precisely the diagonal exponential secant
factor proved by the finite `exprel` construction. -/
theorem jet_exponential_slope (expression : JetExpression)
    (input : Gaussian) (index : Nat) :
    (expression.exponential.jet input index).slope =
      (expression.jet input index).slope *
        CCL.FiniteExp.sample
          (expression.eval input index) index := by
  simp only [jet, FirstJet.compose]
  rw [jet_value]

/-- The local logarithm node uses the finite geometric derivative program.
The separate operational theorem below identifies it with the reciprocal. -/
theorem jet_logarithm1p_slope (expression : JetExpression)
    (input : Gaussian) (index : Nat) :
    (expression.logarithm1p.jet input index).slope =
      (expression.jet input index).slope *
        CCL.LogarithmicCalculus.log1pDerivativeSample
          (expression.eval input index) index := by
  simp only [jet, FirstJet.compose]
  rw [jet_value]

/-- At any displayed admissible inner value, the primitive derivative used
by a logarithm node is operationally the exact reciprocal target. -/
def logarithm1p_primitive_derivative_equivalent
    (expression : JetExpression) (input : Gaussian) (index : Nat)
    (disk : normSq (expression.eval input index) ≤ 1 / 4) :
    Equivalent
      (CCL.LogarithmicCalculus.log1pDerivativeApproximation
        (expression.eval input index) disk)
      (CCL.TranscendentalLaws.constantApproximation
        ((1 + expression.eval input index)⁻¹)) :=
  CCL.LogarithmicCalculus.log1p_derivative_equivalent_inverse
    (expression.eval input index) disk

/-- Every domain check needed by one finite evaluation is decidable from its
displayed rational subexpression values. -/
def admissible : JetExpression → Gaussian → Nat → Bool
  | .constant _, _, _ => true
  | .input, _, _ => true
  | .add left right, point, index =>
      left.admissible point index && right.admissible point index
  | .neg expression, point, index => expression.admissible point index
  | .mul left right, point, index =>
      left.admissible point index && right.admissible point index
  | .reciprocal expression, point, index =>
      expression.admissible point index &&
        decide (expression.eval point index ≠ 0)
  | .exponential expression, point, index =>
      expression.admissible point index &&
        decide (normSq (expression.eval point index) ≤ 1)
  | .logarithm1p expression, point, index =>
      expression.admissible point index &&
        decide (normSq (expression.eval point index) ≤ 1 / 4)

end JetExpression

end CCL.FirstOrderJet
