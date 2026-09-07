import RationalRotations.TernaryCaps
import RationalRotations.MinkowskiClifford

/-!
# Completed finite theory for general ternary rotations

This module packages the separate constructive components of Problem 71 into
one public result.  The general package includes the quotient-free projective
Clifford correspondence, the cached axis/chart/spread interface for every
rotation, and the affine Cayley product.  The rational Minkowski package adds
the explicit two-by-two matrix algebra, complete null-conic parametrization,
parabolic families, and the evaluated zero-handedness example.
-/

namespace RationalRotations

variable {K : Type*} [RFAP.ExplicitField K]

namespace TernaryForm

/-- The complete finite-coordinate rotation theory attached to one displayed
symmetric nondegenerate ternary form in characteristic different from two. -/
structure GeneralRotationTheory (form : TernaryForm K)
    (twoNonzero : (2 : K) ≠ 0) where
  projective : ProjectiveCliffordCorrespondence form twoNonzero
  axisSpread : (rotation : form.SpecialOrthogonal) →
    RotationAxisSpreadWitness form rotation
  capInjective : ∀ left right : Vector K,
    (leftDefined : form.cayleyDenominator left ≠ 0) →
    (rightDefined : form.cayleyDenominator right ≠ 0) →
    form.capRotation left leftDefined =
      form.capRotation right rightDefined → left = right
  capProduct : ∀ left right : Vector K,
    (leftDefined : form.cayleyDenominator left ≠ 0) →
    (rightDefined : form.cayleyDenominator right ≠ 0) →
    (productDefined : form.anchorProductDenominator left right ≠ 0) →
    SpecialOrthogonal.mul
        (form.capRotation left leftDefined)
        (form.capRotation right rightDefined) =
      form.capRotation (form.anchorProduct left right productDefined)
        (form.cayleyDenominator_anchorProduct_ne_zero left right
          leftDefined rightDefined productDefined)

/-- Assemble the projective, affine-chart, and geometric-spread layers for an
arbitrary displayed ternary form. -/
def generalRotationTheory [DecidableEq K]
    (form : TernaryForm K) (twoNonzero : (2 : K) ≠ 0) :
    GeneralRotationTheory form twoNonzero where
  projective := form.projectiveCliffordCorrespondence twoNonzero
  axisSpread := fun rotation =>
    form.rotationAxisSpreadWitness rotation twoNonzero
  capInjective := fun left right leftDefined rightDefined equal =>
    form.capRotation_injective left right leftDefined rightDefined
      twoNonzero equal
  capProduct := fun left right leftDefined rightDefined productDefined =>
    form.capRotation_mul left right leftDefined rightDefined productDefined

end TernaryForm

namespace MinkowskiClifford

private theorem classification_eq_zero_of_nonzero_mul_eq_zero
    {factor value : K} (factorNonzero : factor ≠ 0)
    (productZero : factor * value = 0) : value = 0 := by
  have cancel := RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    value = (factor * factor⁻¹) * value := by rw [cancel, one_mul]
    _ = factor⁻¹ * (factor * value) := by ring1
    _ = 0 := by rw [productZero, mul_zero]

/-- Complete normal-form data for one nonidentity half-spread-zero rotation
of the split ternary form.  The selected Clifford preimage is normalized to
scalar coordinate one, its nonzero null vector is parametrized by the rational
null-conic formula, and the remaining displayed scalar is the parameter in the
corresponding additive parabolic family. -/
structure ParabolicClassification [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (rotation : (TernaryForm.minkowski oneNonzero).SpecialOrthogonal) where
  representative :
    (TernaryForm.minkowski oneNonzero).NonNullEvenClifford
  represents : representative.actionRotation = rotation
  representativeScalarNonzero : representative.toEvenClifford.scalar ≠ 0
  axis : Vector K
  axis_eq : axis = Vector.scale representative.toEvenClifford.scalar⁻¹
    representative.toEvenClifford.vector
  axisNull : (TernaryForm.minkowski oneNonzero).IsNull axis
  axisNonzero : axis ≠ Vector.zero
  coordinates : NullParameterWitness axis
  parameter : K
  parameterNonzero : parameter ≠ 0
  rotation_eq :
    rotation = parabolicRotationAt oneNonzero
      (nullParameter coordinates.first coordinates.second)
      (nullParameter_isNull oneNonzero coordinates.first coordinates.second)
      parameter
  fixedAxis :
    rotation.act (nullParameter coordinates.first coordinates.second) =
      nullParameter coordinates.first coordinates.second
  characteristicUnipotent : ∀ X : K,
    Matrix3.characteristicValue rotation.matrix X = (X - 1) ^ 3
  handednessZero : ∀ transversal : Vector K,
    (TernaryForm.minkowski oneNonzero).Perpendicular transversal
      (nullParameter coordinates.first coordinates.second) →
    handednessDet (nullParameter coordinates.first coordinates.second)
      transversal rotation.matrix = 0

/-- For a displayed special-orthogonal matrix, the usual unipotent
characteristic polynomial forces trace half spread zero.  Evaluations at
`1` and `-1` recover the trace without polynomial extensionality or an
infinite-root argument. -/
theorem rotationHalfSpread_eq_zero_of_characteristicUnipotent
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (rotation : (TernaryForm.minkowski oneNonzero).SpecialOrthogonal)
    (characteristic : ∀ X : K,
      Matrix3.characteristicValue rotation.matrix X = (X - 1) ^ 3) :
    (TernaryForm.minkowski oneNonzero).rotationHalfSpread rotation = 0 := by
  have atOne := characteristic 1
  rw [Matrix3.characteristicValue_expansion,
    rotation.determinantOne] at atOne
  have principalEqTrace :
      Matrix3.principalTrace rotation.matrix =
        Matrix3.trace rotation.matrix := by
    calc
      Matrix3.principalTrace rotation.matrix =
          (1 ^ 3 - Matrix3.trace rotation.matrix * 1 ^ 2 +
              Matrix3.principalTrace rotation.matrix * 1 - 1) +
            Matrix3.trace rotation.matrix := by ring1
      _ = (1 - 1) ^ 3 + Matrix3.trace rotation.matrix := by
        rw [atOne]
      _ = Matrix3.trace rotation.matrix := by ring1
  have atNegativeOne := characteristic (-1)
  rw [Matrix3.characteristicValue_expansion,
    rotation.determinantOne] at atNegativeOne
  have tracePlusPrincipal :
      Matrix3.trace rotation.matrix +
          Matrix3.principalTrace rotation.matrix = 6 := by
    calc
      Matrix3.trace rotation.matrix +
          Matrix3.principalTrace rotation.matrix =
        -((-1) ^ 3 - Matrix3.trace rotation.matrix * (-1) ^ 2 +
            Matrix3.principalTrace rotation.matrix * (-1) - 1) - 2 := by
          ring1
      _ = -((-1 - 1) ^ 3) - 2 := by rw [atNegativeOne]
      _ = 6 := by ring1
  have twiceTrace : 2 * Matrix3.trace rotation.matrix = 6 := by
    calc
      2 * Matrix3.trace rotation.matrix =
          Matrix3.trace rotation.matrix +
            Matrix3.principalTrace rotation.matrix := by
        rw [principalEqTrace]
        ring1
      _ = 6 := tracePlusPrincipal
  have traceDifferenceZero : Matrix3.trace rotation.matrix - 3 = 0 := by
    apply classification_eq_zero_of_nonzero_mul_eq_zero twoNonzero
    calc
      2 * (Matrix3.trace rotation.matrix - 3) =
          2 * Matrix3.trace rotation.matrix - 6 := by ring1
      _ = 0 := by rw [twiceTrace]; ring1
  have traceEqThree : Matrix3.trace rotation.matrix = 3 := by
    calc
      Matrix3.trace rotation.matrix =
          (Matrix3.trace rotation.matrix - 3) + 3 := by ring1
      _ = 0 + 3 := by rw [traceDifferenceZero]
      _ = 3 := by ring1
  unfold TernaryForm.rotationHalfSpread
  rw [traceEqThree]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  ring1

/-- Every nonidentity half-spread-zero rotation of the displayed Minkowski
form is constructively classified by a nonzero rational-conic parameter pair
and a nonzero scalar in its null-axis parabolic family. -/
def parabolicClassification [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (rotation : (TernaryForm.minkowski oneNonzero).SpecialOrthogonal)
    (spreadZero :
      (TernaryForm.minkowski oneNonzero).rotationHalfSpread rotation = 0)
    (nonidentity : rotation.matrix ≠ Matrix3.identity) :
    ParabolicClassification oneNonzero twoNonzero rotation := by
  let form := TernaryForm.minkowski oneNonzero
  let correspondence := form.projectiveCliffordCorrespondence twoNonzero
  let representative := correspondence.preimage rotation
  have represents : representative.actionRotation = rotation :=
    correspondence.action_preimage rotation
  have halfSpreadFormula :=
    representative.rotationHalfSpread_actionRotation twoNonzero
  rw [represents, spreadZero] at halfSpreadFormula
  have productZero :
      form.determinant *
          form.quadrance representative.toEvenClifford.vector *
          representative.toEvenClifford.norm⁻¹ = 0 := by
    simpa only [RFAP.ExplicitField.div_eq_mul_inv] using
      halfSpreadFormula.symm
  have determinantQuadranceZero :
      form.determinant *
          form.quadrance representative.toEvenClifford.vector = 0 := by
    apply classification_eq_zero_of_nonzero_mul_eq_zero
      (RFAP.ExplicitField.inv_ne_zero representative.normNonzero)
    calc
      representative.toEvenClifford.norm⁻¹ *
          (form.determinant *
            form.quadrance representative.toEvenClifford.vector) =
        form.determinant *
          form.quadrance representative.toEvenClifford.vector *
          representative.toEvenClifford.norm⁻¹ := by ring1
      _ = 0 := productZero
  have vectorNull :
      form.IsNull representative.toEvenClifford.vector := by
    exact classification_eq_zero_of_nonzero_mul_eq_zero
      form.determinantNonzero determinantQuadranceZero
  have scalarNonzero : representative.toEvenClifford.scalar ≠ 0 := by
    intro scalarZero
    apply representative.normNonzero
    unfold TernaryForm.EvenClifford.norm
    rw [scalarZero, vectorNull]
    ring1
  have vectorNonzero :
      representative.toEvenClifford.vector ≠ Vector.zero := by
    intro vectorZero
    have equivalentIdentity :=
      (TernaryForm.NonNullEvenClifford.equivalent_identity_iff_vector_eq_zero
        representative).2 vectorZero
    have representativeIdentity :=
      (TernaryForm.NonNullEvenClifford.actionRotation_eq_identity_iff_equivalent_identity
          representative twoNonzero).2 equivalentIdentity
    apply nonidentity
    have rotationIdentity :
        rotation = TernaryForm.SpecialOrthogonal.identity form := by
      calc
        rotation = representative.actionRotation := represents.symm
        _ = TernaryForm.SpecialOrthogonal.identity form :=
          representativeIdentity
    exact congrArg
      (fun value : form.SpecialOrthogonal => value.matrix) rotationIdentity
  let axis := Vector.scale representative.toEvenClifford.scalar⁻¹
    representative.toEvenClifford.vector
  have axisNull : form.IsNull axis :=
    form.isNull_scale representative.toEvenClifford.scalar⁻¹
      representative.toEvenClifford.vector vectorNull
  have inverseScalarNonzero :
      representative.toEvenClifford.scalar⁻¹ ≠ 0 :=
    RFAP.ExplicitField.inv_ne_zero scalarNonzero
  have axisNonzero : axis ≠ Vector.zero := by
    intro axisZero
    apply vectorNonzero
    apply Vector.ext
    · apply classification_eq_zero_of_nonzero_mul_eq_zero
        inverseScalarNonzero
      exact congrArg Vector.t axisZero
    · apply classification_eq_zero_of_nonzero_mul_eq_zero
        inverseScalarNonzero
      exact congrArg Vector.r axisZero
    · apply classification_eq_zero_of_nonzero_mul_eq_zero
        inverseScalarNonzero
      exact congrArg Vector.s axisZero
  let coordinates := nullParameterWitness oneNonzero twoNonzero
    axis axisNull axisNonzero
  let parameter := coordinates.factor⁻¹
  have parameterNonzero : parameter ≠ 0 :=
    RFAP.ExplicitField.inv_ne_zero coordinates.factorNonzero
  let parameterAxis := nullParameter coordinates.first coordinates.second
  let parameterAxisNull :=
    nullParameter_isNull oneNonzero coordinates.first coordinates.second
  let parabolic := parabolicAt oneNonzero parameterAxis parameterAxisNull
    parameter
  have factorCancel := RFAP.ExplicitField.mul_inv_cancel
    coordinates.factor coordinates.factorNonzero
  have inverseFactorCancel : coordinates.factor⁻¹ * coordinates.factor = 1 := by
    calc
      coordinates.factor⁻¹ * coordinates.factor =
          coordinates.factor * coordinates.factor⁻¹ := by ring1
      _ = 1 := factorCancel
  have equivalent : representative.Equivalent parabolic := by
    refine ⟨representative.toEvenClifford.scalar⁻¹,
      inverseScalarNonzero, ?_⟩
    apply TernaryForm.EvenClifford.ext
    · change 1 = representative.toEvenClifford.scalar⁻¹ *
        representative.toEvenClifford.scalar
      calc
        (1 : K) = representative.toEvenClifford.scalar *
            representative.toEvenClifford.scalar⁻¹ :=
          (RFAP.ExplicitField.mul_inv_cancel
            representative.toEvenClifford.scalar scalarNonzero).symm
        _ = representative.toEvenClifford.scalar⁻¹ *
            representative.toEvenClifford.scalar := by ring1
    · change Vector.scale parameter parameterAxis =
        Vector.scale representative.toEvenClifford.scalar⁻¹
          representative.toEvenClifford.vector
      unfold parameterAxis
      rw [coordinates.parameter_spec]
      unfold parameter axis
      rw [Vector.scale_scale, inverseFactorCancel, Vector.one_scale]
  have rotationEq :
      rotation = parabolicRotationAt oneNonzero parameterAxis
        parameterAxisNull parameter := by
    calc
      rotation = representative.actionRotation := represents.symm
      _ = parabolic.actionRotation :=
        TernaryForm.NonNullEvenClifford.actionRotation_respects_equivalent
          equivalent
      _ = parabolicRotationAt oneNonzero parameterAxis
          parameterAxisNull parameter := rfl
  refine
    { representative := representative
      represents := represents
      representativeScalarNonzero := scalarNonzero
      axis := axis
      axis_eq := rfl
      axisNull := axisNull
      axisNonzero := axisNonzero
      coordinates := coordinates
      parameter := parameter
      parameterNonzero := parameterNonzero
      rotation_eq := rotationEq
      fixedAxis := ?_
      characteristicUnipotent := ?_
      handednessZero := ?_ }
  · rw [rotationEq]
    exact parabolicRotationAt_fixedAxis oneNonzero parameterAxis
      parameterAxisNull parameter
  · intro X
    rw [rotationEq]
    exact parabolicRotationAt_characteristic oneNonzero parameterAxis
      parameterAxisNull parameter X
  · intro transversal perpendicular
    rw [rotationEq]
    exact parabolicRotationAt_handedness_zero oneNonzero parameterAxis
      transversal parameterAxisNull perpendicular parameter

/-- Characteristic-polynomial form of the complete classifier.  This is the
direct converse to `parabolicRotationAt_characteristic`: every nonidentity
rotation with characteristic polynomial `(X-1)^3` is one of the displayed
null-conic parabolic normal forms. -/
def parabolicClassificationOfCharacteristic [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (rotation : (TernaryForm.minkowski oneNonzero).SpecialOrthogonal)
    (characteristic : ∀ X : K,
      Matrix3.characteristicValue rotation.matrix X = (X - 1) ^ 3)
    (nonidentity : rotation.matrix ≠ Matrix3.identity) :
    ParabolicClassification oneNonzero twoNonzero rotation :=
  parabolicClassification oneNonzero twoNonzero rotation
    (rotationHalfSpread_eq_zero_of_characteristicUnipotent oneNonzero
      twoNonzero rotation characteristic)
    nonidentity

end MinkowskiClifford

namespace RationalMinkowski

/-- Exact rational specialization of the complete parabolic normal-form
classifier. -/
def classifyParabolic
    (rotation : form.SpecialOrthogonal)
    (spreadZero : form.rotationHalfSpread rotation = 0)
    (nonidentity : rotation.matrix ≠ Matrix3.identity) :
    MinkowskiClifford.ParabolicClassification oneNonzero twoNonzero rotation :=
  MinkowskiClifford.parabolicClassification oneNonzero twoNonzero rotation
    spreadZero nonidentity

/-- Rational classifier from the paper's characteristic-polynomial
description of a parabolic rotation. -/
def classifyParabolicOfCharacteristic
    (rotation : form.SpecialOrthogonal)
    (characteristic : ∀ X : Scalar,
      Matrix3.characteristicValue rotation.matrix X = (X - 1) ^ 3)
    (nonidentity : rotation.matrix ≠ Matrix3.identity) :
    MinkowskiClifford.ParabolicClassification oneNonzero twoNonzero rotation :=
  MinkowskiClifford.parabolicClassificationOfCharacteristic oneNonzero
    twoNonzero rotation characteristic nonidentity

/-- The rational null axis remains in the affine Cayley chart even though the
Minkowski determinant changes the denominator from `1 + Q` to `1 - Q`. -/
theorem parabolicAxis_cayleyDenominator :
    form.cayleyDenominator parabolicAxis = 1 := by
  unfold TernaryForm.cayleyDenominator
  have nullQuadrance : form.quadrance parabolicAxis = 0 :=
    parabolicAxis_null
  rw [nullQuadrance]
  ring1

theorem parabolicCapDefined : form.cayleyDenominator parabolicAxis ≠ 0 := by
  rw [parabolicAxis_cayleyDenominator]
  exact oneNonzero

/-- The previously evaluated rational unipotent is exactly the new
form-relative Cayley cap of its null anchor. -/
theorem parabolic_capRotation :
    form.capRotation parabolicAxis parabolicCapDefined =
      parabolicValue.actionRotation := by
  apply TernaryForm.SpecialOrthogonal.eq_of_matrix_eq
  rfl

theorem parabolic_cap_halfSpread :
    form.rotationHalfSpread
      (form.capRotation parabolicAxis parabolicCapDefined) = 0 := by
  rw [form.rotationHalfSpread_cap parabolicAxis parabolicCapDefined
    twoNonzero]
  have nullQuadrance : form.quadrance parabolicAxis = 0 :=
    parabolicAxis_null
  rw [nullQuadrance]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  ring1

/-- A concrete rational anchor on the Minkowski unit quadric.  Its affine cap
is excluded because the discriminant-corrected denominator is `1 - Q`. -/
def excludedCapAnchor : Vector Scalar := ⟨1, 0, 0⟩

theorem excludedCapAnchor_cayleyDenominator_zero :
    form.cayleyDenominator excludedCapAnchor = 0 := by
  unfold TernaryForm.cayleyDenominator form
  rw [TernaryForm.minkowski_determinant,
    TernaryForm.quadrance_minkowski]
  unfold excludedCapAnchor
  ring1

/-- The fully instantiated rational split-form theory, including both the
general ternary rotation model and the new rational parabolic phenomenon. -/
structure CompleteTheory where
  general : TernaryForm.GeneralRotationTheory form twoNonzero
  split : MinkowskiClifford.FiniteSplitTheory oneNonzero twoNonzero
  evaluatedParabolic : ParabolicCertificate parabolicValue.actionRotation
  classifyParabolic : ∀ rotation : form.SpecialOrthogonal,
    form.rotationHalfSpread rotation = 0 →
    rotation.matrix ≠ Matrix3.identity →
      MinkowskiClifford.ParabolicClassification oneNonzero twoNonzero rotation
  classifyParabolicCharacteristic : ∀ rotation : form.SpecialOrthogonal,
    (∀ X : Scalar,
      Matrix3.characteristicValue rotation.matrix X = (X - 1) ^ 3) →
    rotation.matrix ≠ Matrix3.identity →
      MinkowskiClifford.ParabolicClassification oneNonzero twoNonzero rotation

/-- Assemble every completed finite clause of the Minkowski specialization. -/
def completeTheory : CompleteTheory where
  general := TernaryForm.generalRotationTheory form twoNonzero
  split := MinkowskiClifford.finiteSplitTheory oneNonzero twoNonzero
  evaluatedParabolic := parabolicCertificate
  classifyParabolic := fun rotation spreadZero nonidentity =>
    classifyParabolic rotation spreadZero nonidentity
  classifyParabolicCharacteristic := fun rotation characteristic nonidentity =>
    classifyParabolicOfCharacteristic rotation characteristic nonidentity

end RationalMinkowski

/-- Final solution record for Problem 71: the requested arbitrary displayed
ternary form is paired with the fully evaluated rational Minkowski model. -/
structure ProblemSeventyOneSolution (form : TernaryForm K)
    (twoNonzero : (2 : K) ≠ 0) where
  general : TernaryForm.GeneralRotationTheory form twoNonzero
  rationalMinkowski : RationalMinkowski.CompleteTheory

/-- Construct the complete Problem 71 package without diagonalization,
quotients, or proposition-derived choices. -/
def problemSeventyOneSolution [DecidableEq K]
    (form : TernaryForm K) (twoNonzero : (2 : K) ≠ 0) :
    ProblemSeventyOneSolution form twoNonzero where
  general := TernaryForm.generalRotationTheory form twoNonzero
  rationalMinkowski := RationalMinkowski.completeTheory

end RationalRotations
