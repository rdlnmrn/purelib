import mathlib.Tactic.QuotientFreeRing
import CCL.Boundary.Curve.BoxConditions
import CCL.Boundary.Formula
import CCL.Boundary.Curve.CoordinateFactorization

/-!
# CCL formulas cleared along rational boundary curves

Every Hermitian atom pulled back to a rational curve is compiled to one
explicit univariate rational polynomial.  Its value is the original atom
form multiplied by the positive quadrance of the curve denominator, so all
six parser sign tests are preserved at every displayed non-pole parameter.

This finite compiler lets the event layer feed all atoms of a candidate
one-bit formula into the existing equality/apart gcd profiler.  No affine
point, polynomial root, or limiting value is introduced by the translation.
-/

namespace CCL.CCLCurveFormula

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev RationalCurve := CCL.RationalCurve.RationalCurve
abbrev Polynomial :=
  RFAP.ComputablePolynomial.DensePolynomial Coordinate
abbrev HermitianForm := CCL.CCLGeometry.HermitianForm
abbrev SignTest := CCL.CCLFormula.SignTest
abbrev Atom := CCL.CCLFormula.Atom
abbrev Formula := CCL.CCLFormula.Formula

open RFAP.ConstructiveGaussian.Gaussian
open RFAP.ComputablePolynomial.DensePolynomial

/-- Polynomial quadrance of the homogeneous curve numerator. -/
def numeratorNormSq (curve : RationalCurve) : Polynomial :=
  CCL.CurveBoxConditions.numeratorReal curve *
      CCL.CurveBoxConditions.numeratorReal curve +
    CCL.CurveBoxConditions.numeratorImaginary curve *
      CCL.CurveBoxConditions.numeratorImaginary curve

@[simp] theorem eval_numeratorNormSq
    (curve : RationalCurve) (parameter : Coordinate) :
    (numeratorNormSq curve).eval parameter =
      normSq (curve.numeratorAt parameter) := by
  simp only [numeratorNormSq,
    CCL.CurveBoxConditions.numeratorReal,
    CCL.CurveBoxConditions.numeratorImaginary,
    eval_add, eval_mul,
    RFAP.PathPolynomial.eval_realPart,
    RFAP.PathPolynomial.eval_imagPart,
    CCL.RationalCurve.RationalCurve.numeratorAt, normSq]
  ring1

/-- Denominator-cleared evaluation polynomial of one Hermitian form. -/
def clearedForm (curve : RationalCurve) (form : HermitianForm) : Polynomial :=
  scale form.radial (numeratorNormSq curve) +
    scale form.realLinear
      (CCL.CurveBoxConditions.affineRealNumerator curve) +
    scale form.imagLinear
      (CCL.CurveBoxConditions.affineImaginaryNumerator curve) +
    scale form.constant
      (CCL.CurveBoxConditions.denominatorNormSq curve)

/-- Clearing multiplies the affine Hermitian value by exactly the positive
denominator quadrance. -/
theorem eval_clearedForm
    (curve : RationalCurve) (form : HermitianForm)
    (parameter : Coordinate)
    (denominatorNonzero : curve.denominatorAt parameter ≠ 0) :
    (clearedForm curve form).eval parameter =
      normSq (curve.denominatorAt parameter) *
        form.eval (curve.point parameter) := by
  have numeratorIdentity :=
    curve.numeratorAt_eq_point_mul_denominatorAt parameter
      denominatorNonzero
  have normIdentity := congrArg normSq numeratorIdentity
  rw [normSq_mul] at normIdentity
  simp only [clearedForm, eval_add, eval_scale,
    eval_numeratorNormSq,
    CCL.CurveBoxConditions.eval_affineRealNumerator_eq_point_mul_normSq
      curve parameter denominatorNonzero,
    CCL.CurveBoxConditions.eval_affineImaginaryNumerator_eq_point_mul_normSq
      curve parameter denominatorNonzero,
    CCL.CurveBoxConditions.eval_denominatorNormSq,
    CCL.CCLGeometry.HermitianForm.eval]
  rw [normIdentity]
  ring1

/-- One rational-polynomial sign atom obtained from a Hermitian atom. -/
structure PolynomialAtom where
  polynomial : Polynomial
  sign : SignTest
deriving DecidableEq

namespace PolynomialAtom

def Holds (atom : PolynomialAtom) (parameter : Coordinate) : Prop :=
  atom.sign.Holds (atom.polynomial.eval parameter)

instance (atom : PolynomialAtom) (parameter : Coordinate) :
    Decidable (atom.Holds parameter) := by
  unfold Holds
  infer_instance

end PolynomialAtom

/-- Compile one Hermitian atom along a displayed rational curve. -/
def clearedAtom (curve : RationalCurve) (atom : Atom) : PolynomialAtom :=
  ⟨clearedForm curve atom.form, atom.sign⟩

/-- At a non-pole parameter, the cleared polynomial atom has exactly the
same truth value as the original affine Hermitian atom. -/
theorem clearedAtom_holds_iff
    (curve : RationalCurve) (atom : Atom) (parameter : Coordinate)
    (denominatorNonzero : curve.denominatorAt parameter ≠ 0) :
    (clearedAtom curve atom).Holds parameter ↔
      atom.Holds (curve.point parameter) := by
  unfold PolynomialAtom.Holds CCL.CCLFormula.Atom.Holds
    clearedAtom
  rw [eval_clearedForm curve atom.form parameter denominatorNonzero]
  exact CCL.CCLFormula.SignTest.holds_mul_pos_iff atom.sign
    (normSq (curve.denominatorAt parameter))
    (atom.form.eval (curve.point parameter))
    (normSq_pos denominatorNonzero)

/-- Finite Boolean formulas over univariate rational-polynomial atoms. -/
inductive PolynomialFormula where
  | truth
  | falsity
  | atom (value : PolynomialAtom)
  | and (left right : PolynomialFormula)
  | or (left right : PolynomialFormula)
deriving DecidableEq

namespace PolynomialFormula

def Holds : PolynomialFormula → Coordinate → Prop
  | .truth, _ => True
  | .falsity, _ => False
  | .atom value, parameter => value.Holds parameter
  | .and left right, parameter =>
      left.Holds parameter ∧ right.Holds parameter
  | .or left right, parameter =>
      left.Holds parameter ∨ right.Holds parameter

def holdsDecidable : (formula : PolynomialFormula) →
    (parameter : Coordinate) → Decidable (formula.Holds parameter)
  | .truth, _ => isTrue True.intro
  | .falsity, _ => isFalse id
  | .atom value, parameter => by
      change Decidable (value.Holds parameter)
      exact inferInstance
  | .and left right, parameter =>
      @instDecidableAnd (left.Holds parameter) (right.Holds parameter)
        (holdsDecidable left parameter) (holdsDecidable right parameter)
  | .or left right, parameter =>
      @instDecidableOr (left.Holds parameter) (right.Holds parameter)
        (holdsDecidable left parameter) (holdsDecidable right parameter)

instance (formula : PolynomialFormula) (parameter : Coordinate) :
    Decidable (formula.Holds parameter) :=
  holdsDecidable formula parameter

def atoms : PolynomialFormula → List PolynomialAtom
  | .truth | .falsity => []
  | .atom value => [value]
  | .and left right | .or left right => left.atoms ++ right.atoms

def polynomials (formula : PolynomialFormula) : List Polynomial :=
  formula.atoms.map fun atom => atom.polynomial

end PolynomialFormula

/-- Structural compilation of a complete finite CCL formula along a curve. -/
def clear (curve : RationalCurve) : Formula → PolynomialFormula
  | .truth => .truth
  | .falsity => .falsity
  | .atom atom => .atom (clearedAtom curve atom)
  | .and left right => .and (clear curve left) (clear curve right)
  | .or left right => .or (clear curve left) (clear curve right)

/-- Formula truth is preserved exactly by the finite curve compiler at every
explicit non-pole rational parameter. -/
theorem clear_holds_iff
    (curve : RationalCurve) (formula : Formula) (parameter : Coordinate)
    (denominatorNonzero : curve.denominatorAt parameter ≠ 0) :
    (clear curve formula).Holds parameter ↔
      formula.Holds (curve.point parameter) := by
  induction formula with
  | truth =>
      change True ↔ True
      exact iff_of_true True.intro True.intro
  | falsity =>
      change False ↔ False
      exact iff_of_false id id
  | atom value =>
      change (clearedAtom curve value).Holds parameter ↔
        value.Holds (curve.point parameter)
      exact clearedAtom_holds_iff curve value parameter denominatorNonzero
  | and left right leftHypothesis rightHypothesis =>
      change
        ((clear curve left).Holds parameter ∧
          (clear curve right).Holds parameter) ↔
        (left.Holds (curve.point parameter) ∧
          right.Holds (curve.point parameter))
      exact and_congr leftHypothesis rightHypothesis
  | or left right leftHypothesis rightHypothesis =>
      change
        ((clear curve left).Holds parameter ∨
          (clear curve right).Holds parameter) ↔
        (left.Holds (curve.point parameter) ∨
          right.Holds (curve.point parameter))
      exact or_congr leftHypothesis rightHypothesis

@[simp] theorem clear_atoms
    (curve : RationalCurve) (formula : Formula) :
    (clear curve formula).atoms =
      formula.atoms.map (clearedAtom curve) := by
  induction formula with
  | truth | falsity =>
      change ([] : List PolynomialAtom) = []
      rfl
  | atom value =>
      change [clearedAtom curve value] = [clearedAtom curve value]
      rfl
  | and left right leftHypothesis rightHypothesis =>
      simp only [clear, PolynomialFormula.atoms,
        CCL.CCLFormula.Formula.atoms, List.map_append,
        leftHypothesis, rightHypothesis]
  | or left right leftHypothesis rightHypothesis =>
      simp only [clear, PolynomialFormula.atoms,
        CCL.CCLFormula.Formula.atoms, List.map_append,
        leftHypothesis, rightHypothesis]

/-- The exact finite condition list to pass to the gcd profile splitter. -/
def conditionPolynomials
    (curve : RationalCurve) (formula : Formula) : List Polynomial :=
  (clear curve formula).polynomials

@[simp] theorem conditionPolynomials_eq_map
    (curve : RationalCurve) (formula : Formula) :
    conditionPolynomials curve formula =
      formula.atoms.map fun atom => clearedForm curve atom.form := by
  rw [conditionPolynomials, PolynomialFormula.polynomials, clear_atoms,
    List.map_map]
  rfl

/-! ## Finite formula refinement of an existing event profile -/

/-- Extend an already denominator/box-classified event profile by every
cleared atom polynomial of one candidate CCL formula.  Existing relations are
descended through the new gcd pieces, so the denominator and box certificates
are retained alongside the new formula relations. -/
def extendProfile
    {source : CCL.CoordinateFactorization.Factor}
    {existing : List Polynomial}
    (curve : RationalCurve) (formula : Formula)
    (profile : CCL.CoordinateFactorization.ConditionProfile
      source existing) :
    CCL.CoordinateFactorization.ConditionProfileExtensions
      profile (conditionPolynomials curve formula) :=
  CCL.CoordinateFactorization.extendProfileConditions profile
    (conditionPolynomials curve formula)

/-- The formula extension is finite and nonempty. -/
theorem extendProfile_nonempty
    {source : CCL.CoordinateFactorization.Factor}
    {existing : List Polynomial}
    (curve : RationalCurve) (formula : Formula)
    (profile : CCL.CoordinateFactorization.ConditionProfile
      source existing) :
    (extendProfile curve formula profile).profiles ≠ [] :=
  (extendProfile curve formula profile).nonempty

/-- A separately supplied rational zero of the old profile factor is covered
by one extended formula profile, and conversely.  No zero is produced by this
statement. -/
theorem extendProfile_rootCoverage
    {source : CCL.CoordinateFactorization.Factor}
    {existing : List Polynomial}
    (curve : RationalCurve) (formula : Formula)
    (profile : CCL.CoordinateFactorization.ConditionProfile
      source existing)
    (parameter : Coordinate) :
    profile.factor.polynomial.eval parameter = 0 ↔
      ∃ next ∈ (extendProfile curve formula profile).profiles,
        next.factor.polynomial.eval parameter = 0 :=
  (extendProfile curve formula profile).rootCoverage parameter

end CCL.CCLCurveFormula
