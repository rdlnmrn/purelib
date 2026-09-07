import RationalRotations.TernaryClifford

/-!
# Cayley caps and spreads for displayed ternary forms

This module recovers the affine anchor chart of the Euclidean rotation theory
for an arbitrary displayed symmetric nondegenerate ternary form.  The form
discriminant is visible in every formula: the affine Clifford representative
`(1, u)` has reduced norm `1 + det(M) Q_M(u)`, and the scalar coordinate of
the product of two such representatives is
`1 - det(M) B_M(u, v)`.

All constructions use the already displayed even Clifford coordinates.  No
basis change, diagonalization, quotient representative, or choice principle
is involved.
-/

namespace RationalRotations

variable {K : Type*} [RFAP.ExplicitField K]

namespace TernaryForm

private theorem ternaryCaps_four_ne_zero (twoNonzero : (2 : K) ≠ 0) :
    (4 : K) ≠ 0 := by
  have productNonzero :=
    RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero
  simpa only [show (4 : K) = 2 * 2 by ring1] using productNonzero

private theorem ternaryCaps_square_ne_zero {value : K}
    (valueNonzero : value ≠ 0) : value ^ 2 ≠ 0 := by
  simpa only [pow_two] using
    RFAP.ExplicitField.mul_ne_zero valueNonzero valueNonzero

private theorem ternaryCaps_inverse_product {left right : K}
    (leftNonzero : left ≠ 0) (rightNonzero : right ≠ 0) :
    (left * right)⁻¹ = left⁻¹ * right⁻¹ := by
  have leftCancel := RFAP.ExplicitField.mul_inv_cancel left leftNonzero
  have rightCancel := RFAP.ExplicitField.mul_inv_cancel right rightNonzero
  have productNonzero :=
    RFAP.ExplicitField.mul_ne_zero leftNonzero rightNonzero
  have productCancel := RFAP.ExplicitField.mul_inv_cancel
    (left * right) productNonzero
  calc
    (left * right)⁻¹ = (left * right)⁻¹ * 1 := by rw [mul_one]
    _ = (left * right)⁻¹ *
        ((left * right) * (left⁻¹ * right⁻¹)) := by
      rw [show (left * right) * (left⁻¹ * right⁻¹) = 1 by
        calc
          (left * right) * (left⁻¹ * right⁻¹) =
              (left * left⁻¹) * (right * right⁻¹) := by ring1
          _ = 1 := by rw [leftCancel, rightCancel, one_mul]]
    _ = ((left * right) * (left * right)⁻¹) *
        (left⁻¹ * right⁻¹) := by ring1
    _ = left⁻¹ * right⁻¹ := by rw [productCancel, one_mul]

private theorem ternaryCaps_inverse_square {value : K}
    (valueNonzero : value ≠ 0) :
    (value ^ 2)⁻¹ = value⁻¹ ^ 2 := by
  simpa only [pow_two] using
    ternaryCaps_inverse_product valueNonzero valueNonzero

/-! ## The affine Cayley chart -/

/-- The form-relative cap denominator.  The determinant factor is forced by
the reduced norm convention for the displayed even Clifford algebra. -/
def cayleyDenominator (form : TernaryForm K) (anchor : Vector K) : K :=
  1 + form.determinant * form.quadrance anchor

/-- The unnormalized affine Clifford representative `(1, anchor)`. -/
def capRepresentative (form : TernaryForm K) (anchor : Vector K) :
    form.EvenClifford :=
  ⟨1, anchor⟩

theorem norm_capRepresentative (form : TernaryForm K)
    (anchor : Vector K) :
    (form.capRepresentative anchor).norm = form.cayleyDenominator anchor := by
  unfold capRepresentative EvenClifford.norm cayleyDenominator
  ring1

/-- A defined form-relative Cayley cap, retaining its nonzero denominator as
executable data. -/
def capValue (form : TernaryForm K) (anchor : Vector K)
    (defined : form.cayleyDenominator anchor ≠ 0) :
    form.NonNullEvenClifford where
  toEvenClifford := form.capRepresentative anchor
  normNonzero := by
    rw [form.norm_capRepresentative]
    exact defined

/-- The form-relative Cayley cap as a displayed special-orthogonal
transformation. -/
def capRotation (form : TernaryForm K) (anchor : Vector K)
    (defined : form.cayleyDenominator anchor ≠ 0) :
    form.SpecialOrthogonal :=
  (form.capValue anchor defined).actionRotation

theorem capRotation_act (form : TernaryForm K) (anchor : Vector K)
    (defined : form.cayleyDenominator anchor ≠ 0) (vector : Vector K) :
    (form.capRotation anchor defined).act vector =
      Vector.scale (form.cayleyDenominator anchor)⁻¹
        (Vector.add
          (Vector.add
            (Vector.scale
              (1 - form.determinant * form.quadrance anchor) vector)
            (Vector.scale
              (2 * form.determinant * form.bilinear vector anchor) anchor))
          (Vector.scale (-2) (form.cliffordCross vector anchor))) := by
  unfold capRotation
  rw [NonNullEvenClifford.actionRotation_act]
  unfold NonNullEvenClifford.action
  unfold capValue
  rw [form.norm_capRepresentative]
  unfold capRepresentative EvenClifford.actionNumerator
    cayleyDenominator
  ext <;> unfold Vector.add Vector.scale <;> ring1

/-- Trace of a normalized Clifford action, in the determinant-scaled vector
convention. -/
theorem NonNullEvenClifford.trace_actionMatrix
    {form : TernaryForm K} (value : form.NonNullEvenClifford) :
    Matrix3.trace value.actionMatrix =
      value.toEvenClifford.norm⁻¹ *
        (3 * value.toEvenClifford.scalar ^ 2 -
          form.determinant * form.quadrance value.toEvenClifford.vector) := by
  unfold NonNullEvenClifford.actionMatrix
  rw [Matrix3.trace_scale]
  unfold EvenClifford.actionNumeratorMatrix
  rw [Matrix3.trace_add, Matrix3.trace_add,
    Matrix3.trace_scale, Matrix3.trace_identity,
    Matrix3.trace_scale, Matrix3.trace_outer,
    Matrix3.trace_scale, form.trace_actionSkew]
  change value.toEvenClifford.norm⁻¹ *
      ((value.toEvenClifford.scalar ^ 2 -
          form.determinant * form.quadrance value.toEvenClifford.vector) * 3 +
        (2 * form.determinant) *
          form.quadrance value.toEvenClifford.vector +
        2 * value.toEvenClifford.scalar * 0) = _
  ring1

/-- The trace-defined half spread for a displayed ternary rotation. -/
def rotationHalfSpread (form : TernaryForm K)
    (rotation : form.SpecialOrthogonal) : K :=
  (3 - Matrix3.trace rotation.matrix) / 4

/-- The canonical spread polynomial attached to the trace-defined half
spread. -/
def rotationSpread (form : TernaryForm K)
    (rotation : form.SpecialOrthogonal) : K :=
  4 * form.rotationHalfSpread rotation *
    (1 - form.rotationHalfSpread rotation)

/-- The half spread of a Clifford action is its determinant-weighted vector
quadrance divided by the reduced norm. -/
theorem NonNullEvenClifford.rotationHalfSpread_actionRotation
    {form : TernaryForm K} (value : form.NonNullEvenClifford)
    (twoNonzero : (2 : K) ≠ 0) :
    form.rotationHalfSpread value.actionRotation =
      form.determinant * form.quadrance value.toEvenClifford.vector /
        value.toEvenClifford.norm := by
  have normCancel := RFAP.ExplicitField.mul_inv_cancel
    value.toEvenClifford.norm value.normNonzero
  have fourCancel := RFAP.ExplicitField.mul_inv_cancel 4
    (ternaryCaps_four_ne_zero twoNonzero)
  unfold rotationHalfSpread
  change (3 - Matrix3.trace value.actionMatrix) / 4 = _
  rw [value.trace_actionMatrix]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    (3 - value.toEvenClifford.norm⁻¹ *
        (3 * value.toEvenClifford.scalar ^ 2 -
          form.determinant * form.quadrance value.toEvenClifford.vector)) *
        (4 : K)⁻¹ =
      (3 * (value.toEvenClifford.norm *
          value.toEvenClifford.norm⁻¹) -
        value.toEvenClifford.norm⁻¹ *
          (3 * value.toEvenClifford.scalar ^ 2 -
            form.determinant *
              form.quadrance value.toEvenClifford.vector)) *
        (4 : K)⁻¹ := by rw [normCancel]; ring1
    _ = (4 * form.determinant *
        form.quadrance value.toEvenClifford.vector *
          value.toEvenClifford.norm⁻¹) * (4 : K)⁻¹ := by
      unfold EvenClifford.norm
      ring1
    _ = form.determinant *
        form.quadrance value.toEvenClifford.vector *
          value.toEvenClifford.norm⁻¹ := by
      rw [show (4 * form.determinant *
          form.quadrance value.toEvenClifford.vector *
            value.toEvenClifford.norm⁻¹) * (4 : K)⁻¹ =
          (form.determinant *
            form.quadrance value.toEvenClifford.vector *
              value.toEvenClifford.norm⁻¹) * (4 * (4 : K)⁻¹) by ring1,
        fourCancel, mul_one]

theorem rotationHalfSpread_cap (form : TernaryForm K)
    (anchor : Vector K) (defined : form.cayleyDenominator anchor ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    form.rotationHalfSpread (form.capRotation anchor defined) =
      form.determinant * form.quadrance anchor /
        form.cayleyDenominator anchor := by
  unfold capRotation
  simpa only [capValue, capRepresentative, cayleyDenominator,
    EvenClifford.norm, one_pow] using
      (form.capValue anchor defined).rotationHalfSpread_actionRotation
        twoNonzero

/-! ## Geometric spread on the canonical axis -/

/-- Rotation spread evaluated on a displayed non-null test vector.  Since a
form rotation preserves quadrance, this is the ordinary projective spread of
the test vector and its image with the equal quadrances already cancelled. -/
def rotationSpreadAt (form : TernaryForm K)
    (rotation : form.SpecialOrthogonal) (vector : Vector K)
    (_nonNull : form.quadrance vector ≠ 0) : K :=
  1 - (form.bilinear vector (rotation.act vector) /
    form.quadrance vector) ^ 2

theorem NonNullEvenClifford.bilinear_self_action_of_perpendicular
    {form : TernaryForm K} (value : form.NonNullEvenClifford)
    (vector : Vector K)
    (perpendicular : form.Perpendicular vector value.toEvenClifford.vector) :
    form.bilinear vector (value.action vector) =
      value.toEvenClifford.norm⁻¹ *
        (value.toEvenClifford.scalar ^ 2 -
          form.determinant * form.quadrance value.toEvenClifford.vector) *
        form.quadrance vector := by
  have pairingZero :
      form.bilinear vector value.toEvenClifford.vector = 0 :=
    perpendicular
  have crossZero :
      form.bilinear vector
        (form.cliffordCross vector value.toEvenClifford.vector) = 0 := by
    rw [form.bilinear_comm]
    exact form.cliffordCross_perpendicular_left
      vector value.toEvenClifford.vector
  unfold NonNullEvenClifford.action EvenClifford.actionNumerator
  rw [form.bilinear_scale_right, form.bilinear_add_right,
    form.bilinear_add_right, form.bilinear_scale_right,
    form.bilinear_scale_right, form.bilinear_scale_right,
    pairingZero, crossZero]
  unfold quadrance
  ring1

theorem NonNullEvenClifford.rotationSpreadAt_of_perpendicular
    {form : TernaryForm K} (value : form.NonNullEvenClifford)
    (vector : Vector K) (nonNull : form.quadrance vector ≠ 0)
    (perpendicular : form.Perpendicular vector value.toEvenClifford.vector) :
    form.rotationSpreadAt value.actionRotation vector nonNull =
      4 *
        (form.determinant * form.quadrance value.toEvenClifford.vector /
          value.toEvenClifford.norm) *
        (1 - form.determinant *
          form.quadrance value.toEvenClifford.vector /
            value.toEvenClifford.norm) := by
  have quadranceCancel := RFAP.ExplicitField.mul_inv_cancel
    (form.quadrance vector) nonNull
  have normCancel := RFAP.ExplicitField.mul_inv_cancel
    value.toEvenClifford.norm value.normNonzero
  have split :
      value.toEvenClifford.scalar ^ 2 *
          value.toEvenClifford.norm⁻¹ +
        form.determinant *
          form.quadrance value.toEvenClifford.vector *
            value.toEvenClifford.norm⁻¹ = 1 := by
    calc
      value.toEvenClifford.scalar ^ 2 *
            value.toEvenClifford.norm⁻¹ +
          form.determinant *
            form.quadrance value.toEvenClifford.vector *
              value.toEvenClifford.norm⁻¹ =
        value.toEvenClifford.norm * value.toEvenClifford.norm⁻¹ := by
          unfold EvenClifford.norm
          ring1
      _ = 1 := normCancel
  have complement :
      1 - form.determinant *
          form.quadrance value.toEvenClifford.vector *
            value.toEvenClifford.norm⁻¹ =
        value.toEvenClifford.scalar ^ 2 *
          value.toEvenClifford.norm⁻¹ := by
    rw [← split]
    ring1
  unfold rotationSpreadAt
  rw [NonNullEvenClifford.actionRotation_act,
    value.bilinear_self_action_of_perpendicular vector perpendicular]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  have quotient :
      (value.toEvenClifford.norm⁻¹ *
          (value.toEvenClifford.scalar ^ 2 -
            form.determinant *
              form.quadrance value.toEvenClifford.vector) *
          form.quadrance vector) *
          (form.quadrance vector)⁻¹ =
        value.toEvenClifford.norm⁻¹ *
          (value.toEvenClifford.scalar ^ 2 -
            form.determinant *
              form.quadrance value.toEvenClifford.vector) := by
    calc
      (value.toEvenClifford.norm⁻¹ *
            (value.toEvenClifford.scalar ^ 2 -
              form.determinant *
                form.quadrance value.toEvenClifford.vector) *
            form.quadrance vector) *
            (form.quadrance vector)⁻¹ =
        value.toEvenClifford.norm⁻¹ *
          (value.toEvenClifford.scalar ^ 2 -
            form.determinant *
              form.quadrance value.toEvenClifford.vector) *
          (form.quadrance vector * (form.quadrance vector)⁻¹) := by
            ring1
      _ = _ := by rw [quadranceCancel, mul_one]
  rw [quotient]
  change
    1 - (value.toEvenClifford.norm⁻¹ *
      (value.toEvenClifford.scalar ^ 2 -
        form.determinant *
          form.quadrance value.toEvenClifford.vector)) ^ 2 = _
  calc
    1 - (value.toEvenClifford.norm⁻¹ *
        (value.toEvenClifford.scalar ^ 2 -
          form.determinant *
            form.quadrance value.toEvenClifford.vector)) ^ 2 =
      (value.toEvenClifford.scalar ^ 2 *
          value.toEvenClifford.norm⁻¹ +
        form.determinant *
          form.quadrance value.toEvenClifford.vector *
            value.toEvenClifford.norm⁻¹) ^ 2 -
        (value.toEvenClifford.norm⁻¹ *
          (value.toEvenClifford.scalar ^ 2 -
            form.determinant *
              form.quadrance value.toEvenClifford.vector)) ^ 2 := by
      have oneSquare :
          (1 : K) =
            (value.toEvenClifford.scalar ^ 2 *
                value.toEvenClifford.norm⁻¹ +
              form.determinant *
                form.quadrance value.toEvenClifford.vector *
                  value.toEvenClifford.norm⁻¹) ^ 2 := by
        calc
          (1 : K) = 1 ^ 2 := by ring1
          _ = (value.toEvenClifford.scalar ^ 2 *
                value.toEvenClifford.norm⁻¹ +
              form.determinant *
                form.quadrance value.toEvenClifford.vector *
                  value.toEvenClifford.norm⁻¹) ^ 2 := by rw [split]
      exact congrArg
        (fun scalar : K => scalar -
          (value.toEvenClifford.norm⁻¹ *
            (value.toEvenClifford.scalar ^ 2 -
              form.determinant *
                form.quadrance value.toEvenClifford.vector)) ^ 2)
        oneSquare
    _ =
      4 * value.toEvenClifford.scalar ^ 2 * form.determinant *
        form.quadrance value.toEvenClifford.vector *
          value.toEvenClifford.norm⁻¹ ^ 2 := by
      ring1
    _ = 4 *
        (form.determinant *
          form.quadrance value.toEvenClifford.vector *
            value.toEvenClifford.norm⁻¹) *
        (1 - form.determinant *
          form.quadrance value.toEvenClifford.vector *
            value.toEvenClifford.norm⁻¹) := by
      rw [complement]
      ring1

theorem NonNullEvenClifford.rotationSpreadAt_eq_rotationSpread
    {form : TernaryForm K} (value : form.NonNullEvenClifford)
    (vector : Vector K) (nonNull : form.quadrance vector ≠ 0)
    (perpendicular : form.Perpendicular vector value.toEvenClifford.vector)
    (twoNonzero : (2 : K) ≠ 0) :
    form.rotationSpreadAt value.actionRotation vector nonNull =
      form.rotationSpread value.actionRotation := by
  rw [value.rotationSpreadAt_of_perpendicular vector nonNull perpendicular]
  unfold rotationSpread
  rw [value.rotationHalfSpread_actionRotation twoNonzero]

theorem rotationSpreadAt_cap (form : TernaryForm K)
    (anchor vector : Vector K)
    (defined : form.cayleyDenominator anchor ≠ 0)
    (nonNull : form.quadrance vector ≠ 0)
    (perpendicular : form.Perpendicular vector anchor)
    (twoNonzero : (2 : K) ≠ 0) :
    form.rotationSpreadAt (form.capRotation anchor defined) vector nonNull =
      form.rotationSpread (form.capRotation anchor defined) := by
  exact (form.capValue anchor defined).rotationSpreadAt_eq_rotationSpread
    vector nonNull perpendicular twoNonzero

/-! ## Homogeneous and affine anchor products -/

/-- The total homogeneous anchor product.  This is the even Clifford product
under its geometric name; it remains defined when an affine normalization is
not. -/
def homogeneousAnchorProduct (form : TernaryForm K)
    (left right : form.EvenClifford) : form.EvenClifford :=
  EvenClifford.mul left right

/-- Scalar denominator for the affine product of two anchors. -/
def anchorProductDenominator (form : TernaryForm K)
    (left right : Vector K) : K :=
  1 - form.determinant * form.bilinear left right

/-- Numerator vector for the affine product of two anchors. -/
def anchorProductNumerator (form : TernaryForm K)
    (left right : Vector K) : Vector K :=
  Vector.sub (Vector.add left right) (form.cliffordCross left right)

/-- The normalized form-relative anchor product. -/
def anchorProduct (form : TernaryForm K) (left right : Vector K)
    (_defined : form.anchorProductDenominator left right ≠ 0) : Vector K :=
  Vector.scale (form.anchorProductDenominator left right)⁻¹
    (form.anchorProductNumerator left right)

theorem mul_capRepresentative (form : TernaryForm K)
    (left right : Vector K) :
    EvenClifford.mul (form.capRepresentative left)
        (form.capRepresentative right) =
      ⟨form.anchorProductDenominator left right,
        form.anchorProductNumerator left right⟩ := by
  apply EvenClifford.ext
  · unfold EvenClifford.mul EvenClifford.productScalar capRepresentative
      anchorProductDenominator
    ring1
  · ext <;> unfold EvenClifford.mul EvenClifford.productVector
      capRepresentative anchorProductNumerator Vector.add Vector.sub
      Vector.scale <;> ring1

/-- The exact denominator identity for the affine anchor product. -/
theorem cayleyDenominator_anchorProduct (form : TernaryForm K)
    (left right : Vector K)
    (productDefined : form.anchorProductDenominator left right ≠ 0) :
    form.cayleyDenominator
        (form.anchorProduct left right productDefined) =
      form.cayleyDenominator left * form.cayleyDenominator right /
        form.anchorProductDenominator left right ^ 2 := by
  have denominatorCancel := RFAP.ExplicitField.mul_inv_cancel
    (form.anchorProductDenominator left right) productDefined
  have denominatorSquareCancel :
      form.anchorProductDenominator left right ^ 2 *
          (form.anchorProductDenominator left right)⁻¹ ^ 2 = 1 := by
    calc
      form.anchorProductDenominator left right ^ 2 *
          (form.anchorProductDenominator left right)⁻¹ ^ 2 =
        (form.anchorProductDenominator left right *
          (form.anchorProductDenominator left right)⁻¹) ^ 2 := by ring1
      _ = 1 := by rw [denominatorCancel]; ring1
  have numeratorQuadrance := EvenClifford.quadrance_productVector form
    1 1 left right
  have productVectorEq :
      EvenClifford.productVector form 1 1 left right =
        form.anchorProductNumerator left right := by
    ext <;> unfold EvenClifford.productVector anchorProductNumerator
      Vector.add Vector.sub Vector.scale <;> ring1
  rw [productVectorEq] at numeratorQuadrance
  unfold cayleyDenominator anchorProduct
  rw [form.quadrance_scale]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  rw [numeratorQuadrance]
  unfold anchorProductDenominator
  change
      (1 - form.determinant * form.bilinear left right) ^ 2 *
        (1 - form.determinant * form.bilinear left right)⁻¹ ^ 2 = 1
    at denominatorSquareCancel
  calc
    1 + form.determinant *
        ((1 - form.determinant * form.bilinear left right)⁻¹ ^ 2 *
          (1 ^ 2 * form.quadrance right +
            2 * 1 * 1 * form.bilinear left right +
            1 ^ 2 * form.quadrance left +
            form.determinant *
              (form.quadrance left * form.quadrance right -
                form.bilinear left right ^ 2))) =
      ((1 + form.determinant * form.quadrance left) *
          (1 + form.determinant * form.quadrance right)) *
        ((1 - form.determinant * form.bilinear left right)⁻¹ ^ 2) := by
      let remaining := form.determinant *
        (1 ^ 2 * form.quadrance right +
          2 * 1 * 1 * form.bilinear left right +
          1 ^ 2 * form.quadrance left +
          form.determinant *
            (form.quadrance left * form.quadrance right -
              form.bilinear left right ^ 2)) *
        (1 - form.determinant * form.bilinear left right)⁻¹ ^ 2
      calc
        _ = 1 + remaining := by unfold remaining; ring1
        _ = ((1 - form.determinant * form.bilinear left right) ^ 2 *
              (1 - form.determinant * form.bilinear left right)⁻¹ ^ 2 +
            remaining) := by rw [denominatorSquareCancel]
        _ = _ := by unfold remaining; ring1
    _ = ((1 + form.determinant * form.quadrance left) *
          (1 + form.determinant * form.quadrance right)) *
        ((1 - form.determinant * form.bilinear left right) ^ 2)⁻¹ := by
      have inverseSquare := ternaryCaps_inverse_square productDefined
      change
        ((1 - form.determinant * form.bilinear left right) ^ 2)⁻¹ =
          (1 - form.determinant * form.bilinear left right)⁻¹ ^ 2
        at inverseSquare
      rw [inverseSquare]

/-- Defined input caps and a nonzero affine product denominator constructively
certify the output cap denominator. -/
theorem cayleyDenominator_anchorProduct_ne_zero (form : TernaryForm K)
    (left right : Vector K)
    (leftDefined : form.cayleyDenominator left ≠ 0)
    (rightDefined : form.cayleyDenominator right ≠ 0)
    (productDefined : form.anchorProductDenominator left right ≠ 0) :
    form.cayleyDenominator
      (form.anchorProduct left right productDefined) ≠ 0 := by
  rw [form.cayleyDenominator_anchorProduct left right productDefined]
  exact RFAP.ExplicitField.div_ne_zero
    (RFAP.ExplicitField.mul_ne_zero leftDefined rightDefined)
    (ternaryCaps_square_ne_zero productDefined)

theorem capRepresentative_anchorProduct_scale (form : TernaryForm K)
    (left right : Vector K)
    (productDefined : form.anchorProductDenominator left right ≠ 0) :
    EvenClifford.mul (form.capRepresentative left)
        (form.capRepresentative right) =
      EvenClifford.scale (form.anchorProductDenominator left right)
        (form.capRepresentative
          (form.anchorProduct left right productDefined)) := by
  rw [form.mul_capRepresentative]
  apply EvenClifford.ext
  · unfold EvenClifford.scale capRepresentative
    ring1
  · have cancel := RFAP.ExplicitField.mul_inv_cancel
      (form.anchorProductDenominator left right) productDefined
    apply Vector.ext
    · change (form.anchorProductNumerator left right).t =
        form.anchorProductDenominator left right *
          ((form.anchorProductDenominator left right)⁻¹ *
            (form.anchorProductNumerator left right).t)
      calc
        _ = 1 * (form.anchorProductNumerator left right).t := by rw [one_mul]
        _ = (form.anchorProductDenominator left right *
              (form.anchorProductDenominator left right)⁻¹) *
            (form.anchorProductNumerator left right).t := by rw [cancel]
        _ = _ := by ring1
    · change (form.anchorProductNumerator left right).r =
        form.anchorProductDenominator left right *
          ((form.anchorProductDenominator left right)⁻¹ *
            (form.anchorProductNumerator left right).r)
      calc
        _ = 1 * (form.anchorProductNumerator left right).r := by rw [one_mul]
        _ = (form.anchorProductDenominator left right *
              (form.anchorProductDenominator left right)⁻¹) *
            (form.anchorProductNumerator left right).r := by rw [cancel]
        _ = _ := by ring1
    · change (form.anchorProductNumerator left right).s =
        form.anchorProductDenominator left right *
          ((form.anchorProductDenominator left right)⁻¹ *
            (form.anchorProductNumerator left right).s)
      calc
        _ = 1 * (form.anchorProductNumerator left right).s := by rw [one_mul]
        _ = (form.anchorProductDenominator left right *
              (form.anchorProductDenominator left right)⁻¹) *
            (form.anchorProductNumerator left right).s := by rw [cancel]
        _ = _ := by ring1

/-- Form-relative Theorem 46: whenever all displayed affine denominators are
nonzero, multiplication of caps is the cap of the determinant-corrected
anchor product. -/
theorem capRotation_mul (form : TernaryForm K)
    (left right : Vector K)
    (leftDefined : form.cayleyDenominator left ≠ 0)
    (rightDefined : form.cayleyDenominator right ≠ 0)
    (productDefined : form.anchorProductDenominator left right ≠ 0) :
    SpecialOrthogonal.mul
        (form.capRotation left leftDefined)
        (form.capRotation right rightDefined) =
      form.capRotation (form.anchorProduct left right productDefined)
        (form.cayleyDenominator_anchorProduct_ne_zero left right
          leftDefined rightDefined productDefined) := by
  let outputDefined := form.cayleyDenominator_anchorProduct_ne_zero
    left right leftDefined rightDefined productDefined
  have equivalent :
      (NonNullEvenClifford.mul
        (form.capValue left leftDefined)
        (form.capValue right rightDefined)).Equivalent
          (form.capValue (form.anchorProduct left right productDefined)
            outputDefined) := by
    refine ⟨(form.anchorProductDenominator left right)⁻¹,
      RFAP.ExplicitField.inv_ne_zero productDefined, ?_⟩
    change form.capRepresentative
        (form.anchorProduct left right productDefined) =
      EvenClifford.scale (form.anchorProductDenominator left right)⁻¹
        (EvenClifford.mul (form.capRepresentative left)
          (form.capRepresentative right))
    rw [form.capRepresentative_anchorProduct_scale]
    rw [EvenClifford.scale_scale]
    have cancel := RFAP.ExplicitField.mul_inv_cancel
      (form.anchorProductDenominator left right) productDefined
    have reverseCancel :
        (form.anchorProductDenominator left right)⁻¹ *
          form.anchorProductDenominator left right = 1 := by
      calc
        (form.anchorProductDenominator left right)⁻¹ *
            form.anchorProductDenominator left right =
          form.anchorProductDenominator left right *
            (form.anchorProductDenominator left right)⁻¹ := by ring1
        _ = 1 := cancel
    rw [reverseCancel, EvenClifford.one_scale]
  calc
    SpecialOrthogonal.mul
        (form.capRotation left leftDefined)
        (form.capRotation right rightDefined) =
      (NonNullEvenClifford.mul
        (form.capValue left leftDefined)
        (form.capValue right rightDefined)).actionRotation :=
          (NonNullEvenClifford.actionRotation_mul _ _).symm
    _ = (form.capValue (form.anchorProduct left right productDefined)
          outputDefined).actionRotation :=
      NonNullEvenClifford.actionRotation_respects_equivalent equivalent
    _ = form.capRotation (form.anchorProduct left right productDefined)
        outputDefined := rfl

/-! ## Affine normalization and the projective chart boundary -/

/-- Cached normalization of a non-null Clifford representative whose scalar
coordinate is nonzero. -/
structure CapNormalization (form : TernaryForm K)
    (value : form.NonNullEvenClifford) where
  anchor : Vector K
  defined : form.cayleyDenominator anchor ≠ 0
  equivalent : (form.capValue anchor defined).Equivalent value

/-- Normalize a displayed Clifford representative into the affine cap chart.
The scalar coordinate, anchor, denominator certificate, and projective scale
are all computed explicitly. -/
def capNormalization (form : TernaryForm K)
    (value : form.NonNullEvenClifford)
    (scalarNonzero : value.toEvenClifford.scalar ≠ 0) :
    CapNormalization form value := by
  let anchor := Vector.scale value.toEvenClifford.scalar⁻¹
    value.toEvenClifford.vector
  have scalarCancel := RFAP.ExplicitField.mul_inv_cancel
    value.toEvenClifford.scalar scalarNonzero
  have scaledRepresentative :
      value.toEvenClifford =
        EvenClifford.scale value.toEvenClifford.scalar
          (form.capRepresentative anchor) := by
    apply EvenClifford.ext
    · unfold EvenClifford.scale capRepresentative
      ring1
    · apply Vector.ext
      · change value.toEvenClifford.vector.t =
          value.toEvenClifford.scalar *
            (value.toEvenClifford.scalar⁻¹ *
              value.toEvenClifford.vector.t)
        calc
          _ = 1 * value.toEvenClifford.vector.t := by rw [one_mul]
          _ = (value.toEvenClifford.scalar *
                value.toEvenClifford.scalar⁻¹) *
              value.toEvenClifford.vector.t := by rw [scalarCancel]
          _ = _ := by ring1
      · change value.toEvenClifford.vector.r =
          value.toEvenClifford.scalar *
            (value.toEvenClifford.scalar⁻¹ *
              value.toEvenClifford.vector.r)
        calc
          _ = 1 * value.toEvenClifford.vector.r := by rw [one_mul]
          _ = (value.toEvenClifford.scalar *
                value.toEvenClifford.scalar⁻¹) *
              value.toEvenClifford.vector.r := by rw [scalarCancel]
          _ = _ := by ring1
      · change value.toEvenClifford.vector.s =
          value.toEvenClifford.scalar *
            (value.toEvenClifford.scalar⁻¹ *
              value.toEvenClifford.vector.s)
        calc
          _ = 1 * value.toEvenClifford.vector.s := by rw [one_mul]
          _ = (value.toEvenClifford.scalar *
                value.toEvenClifford.scalar⁻¹) *
              value.toEvenClifford.vector.s := by rw [scalarCancel]
          _ = _ := by ring1
  have defined : form.cayleyDenominator anchor ≠ 0 := by
    intro denominatorZero
    apply value.normNonzero
    calc
      value.toEvenClifford.norm =
          (EvenClifford.scale value.toEvenClifford.scalar
            (form.capRepresentative anchor)).norm := by
              rw [← scaledRepresentative]
      _ = value.toEvenClifford.scalar ^ 2 *
          (form.capRepresentative anchor).norm :=
        EvenClifford.norm_scale _ _
      _ = 0 := by
        rw [form.norm_capRepresentative, denominatorZero, mul_zero]
  exact
    { anchor := anchor
      defined := defined
      equivalent :=
        ⟨value.toEvenClifford.scalar, scalarNonzero,
          scaledRepresentative⟩ }

theorem CapNormalization.actionRotation_eq
    {form : TernaryForm K} {value : form.NonNullEvenClifford}
    (normalization : CapNormalization form value) :
    form.capRotation normalization.anchor normalization.defined =
      value.actionRotation := by
  exact NonNullEvenClifford.actionRotation_respects_equivalent
    normalization.equivalent

/-- A scalar-zero non-null representative has a non-null vector coordinate. -/
theorem NonNullEvenClifford.vectorNonNull_of_scalar_eq_zero
    {form : TernaryForm K} (value : form.NonNullEvenClifford)
    (scalarZero : value.toEvenClifford.scalar = 0) :
    form.quadrance value.toEvenClifford.vector ≠ 0 := by
  intro vectorNull
  apply value.normNonzero
  unfold EvenClifford.norm
  rw [scalarZero, vectorNull]
  ring1

theorem NonNullEvenClifford.actionRotation_eq_halfTurn_of_scalar_eq_zero
    {form : TernaryForm K} (value : form.NonNullEvenClifford)
    (scalarZero : value.toEvenClifford.scalar = 0) :
    value.actionRotation =
      form.halfTurnRotation value.toEvenClifford.vector
        (value.vectorNonNull_of_scalar_eq_zero scalarZero) := by
  let nonNull := value.vectorNonNull_of_scalar_eq_zero scalarZero
  have valueEq :
      value = NonNullEvenClifford.halfTurnValue form
        value.toEvenClifford.vector nonNull := by
    apply NonNullEvenClifford.ext
    · exact scalarZero
    · rfl
  calc
    value.actionRotation =
        (NonNullEvenClifford.halfTurnValue form
          value.toEvenClifford.vector nonNull).actionRotation :=
      congrArg NonNullEvenClifford.actionRotation valueEq
    _ = form.halfTurnRotation value.toEvenClifford.vector nonNull :=
      NonNullEvenClifford.halfTurnValue_actionRotation form
        value.toEvenClifford.vector nonNull

/-- The two constructive charts of a non-null Clifford representative. -/
inductive CliffordChart (form : TernaryForm K)
    (value : form.NonNullEvenClifford) where
  | affine (normalization : CapNormalization form value)
  | atInfinity
      (scalarZero : value.toEvenClifford.scalar = 0)
      (axisNonNull : form.quadrance value.toEvenClifford.vector ≠ 0)
      (action_eq : value.actionRotation =
        form.halfTurnRotation value.toEvenClifford.vector axisNonNull)

/-- Execute the affine/half-turn chart decision once and cache all resulting
denominators and representation certificates. -/
def cliffordChart [DecidableEq K] (form : TernaryForm K)
    (value : form.NonNullEvenClifford) : CliffordChart form value := by
  by_cases scalarZero : value.toEvenClifford.scalar = 0
  · exact CliffordChart.atInfinity scalarZero
      (value.vectorNonNull_of_scalar_eq_zero scalarZero)
      (value.actionRotation_eq_halfTurn_of_scalar_eq_zero scalarZero)
  · exact CliffordChart.affine (form.capNormalization value scalarZero)

theorem rotationHalfSpread_halfTurn (form : TernaryForm K)
    (axis : Vector K) (nonNull : form.quadrance axis ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    form.rotationHalfSpread (form.halfTurnRotation axis nonNull) = 1 := by
  rw [← NonNullEvenClifford.halfTurnValue_actionRotation]
  rw [NonNullEvenClifford.rotationHalfSpread_actionRotation _ twoNonzero]
  rw [NonNullEvenClifford.halfTurnValue_norm]
  have productNonzero := RFAP.ExplicitField.mul_ne_zero
    form.determinantNonzero nonNull
  change form.determinant * form.quadrance axis /
      (form.determinant * form.quadrance axis) = 1
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  exact RFAP.ExplicitField.mul_inv_cancel _ productNonzero

theorem rotationHalfSpread_cap_ne_one (form : TernaryForm K)
    (anchor : Vector K) (defined : form.cayleyDenominator anchor ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    form.rotationHalfSpread (form.capRotation anchor defined) ≠ 1 := by
  intro spreadOne
  have formula := form.rotationHalfSpread_cap anchor defined twoNonzero
  rw [spreadOne] at formula
  have denominatorCancel := RFAP.ExplicitField.mul_inv_cancel
    (form.cayleyDenominator anchor) defined
  simp only [RFAP.ExplicitField.div_eq_mul_inv] at formula
  have weightedQuadranceEq :
      form.determinant * form.quadrance anchor =
        form.cayleyDenominator anchor := by
    calc
      form.determinant * form.quadrance anchor =
          form.determinant * form.quadrance anchor * 1 := by rw [mul_one]
      _ = form.determinant * form.quadrance anchor *
          (form.cayleyDenominator anchor *
            (form.cayleyDenominator anchor)⁻¹) := by rw [denominatorCancel]
      _ = form.cayleyDenominator anchor *
          (form.determinant * form.quadrance anchor *
            (form.cayleyDenominator anchor)⁻¹) := by ring1
      _ = form.cayleyDenominator anchor * 1 := by rw [← formula]
      _ = form.cayleyDenominator anchor := by rw [mul_one]
  have impossible : (1 : K) = 0 := by
    calc
      (1 : K) = form.cayleyDenominator anchor -
          form.determinant * form.quadrance anchor := by
        unfold cayleyDenominator
        ring1
      _ = 0 := by rw [← weightedQuadranceEq]; ring1
  exact form.one_ne_zero impossible

/-- Form-relative cap injectivity.  Projective faithfulness supplies a scale,
and the two scalar coordinates equal to one force that scale to be one. -/
theorem capRotation_injective [DecidableEq K]
    (form : TernaryForm K) (left right : Vector K)
    (leftDefined : form.cayleyDenominator left ≠ 0)
    (rightDefined : form.cayleyDenominator right ≠ 0)
    (twoNonzero : (2 : K) ≠ 0)
    (equal : form.capRotation left leftDefined =
      form.capRotation right rightDefined) :
    left = right := by
  have equivalent :=
    (NonNullEvenClifford.actionRotation_eq_iff_equivalent
      (form.capValue left leftDefined)
      (form.capValue right rightDefined) twoNonzero).1 equal
  rcases equivalent with ⟨factor, factorNonzero, representativeEq⟩
  have scalarEq := congrArg EvenClifford.scalar representativeEq
  have factorOne : factor = 1 := by
    change (1 : K) = factor * 1 at scalarEq
    simpa only [mul_one] using scalarEq.symm
  have vectorEq := congrArg EvenClifford.vector representativeEq
  change right = Vector.scale factor left at vectorEq
  rw [factorOne, Vector.one_scale] at vectorEq
  exact vectorEq.symm

/-! ## A cached canonical axis and spread witness for every rotation -/

/-- Cached representative, chart, factorization, axis, and geometric spread
data for an arbitrary displayed form rotation.  The first half-turn axis from
the constructive factorization is automatically a non-null perpendicular
test direction for the product representative's vector coordinate. -/
structure RotationAxisSpreadWitness (form : TernaryForm K)
    (rotation : form.SpecialOrthogonal) where
  factorization : TwoHalfTurnFactorization form rotation
  representative : form.NonNullEvenClifford
  representative_eq : representative = factorization.cliffordPreimage
  represents : representative.actionRotation = rotation
  axis : Vector K
  axis_eq : axis = representative.toEvenClifford.vector
  perpendicular : Vector K
  perpendicularNonNull : form.quadrance perpendicular ≠ 0
  perpendicularToAxis : form.Perpendicular perpendicular axis
  chart : CliffordChart form representative
  halfSpread_eq :
    form.rotationHalfSpread rotation =
      form.determinant * form.quadrance axis /
        representative.toEvenClifford.norm
  spread_eq :
    form.rotationSpreadAt rotation perpendicular perpendicularNonNull =
      form.rotationSpread rotation

/-- The cached two-half-turn data are simultaneously the paper's
two-reflection factorization: negating both reflection matrices leaves their
product unchanged. -/
theorem TwoHalfTurnFactorization.reflectionProductMatrix
    {form : TernaryForm K} {rotation : form.SpecialOrthogonal}
    (factorization : TwoHalfTurnFactorization form rotation) :
    Matrix3.mul
        (form.reflection factorization.firstAxis factorization.firstNonNull)
        (form.reflection factorization.secondAxis factorization.secondNonNull) =
      rotation.matrix := by
  have rotationMatrix := congrArg
    (fun value : form.SpecialOrthogonal => value.matrix)
    factorization.rotation_eq
  change Matrix3.mul
      (form.halfTurn factorization.firstAxis factorization.firstNonNull)
      (form.halfTurn factorization.secondAxis factorization.secondNonNull) =
    rotation.matrix at rotationMatrix
  unfold halfTurn at rotationMatrix
  rw [Matrix3.mul_neg_neg] at rotationMatrix
  exact rotationMatrix

private theorem TwoHalfTurnFactorization.firstAxis_perpendicular_cliffordPreimage
    {form : TernaryForm K} {rotation : form.SpecialOrthogonal}
    (factorization : TwoHalfTurnFactorization form rotation) :
    form.Perpendicular factorization.firstAxis
      factorization.cliffordPreimage.toEvenClifford.vector := by
  have crossPerpendicular :
      form.Perpendicular factorization.firstAxis
        (form.cliffordCross factorization.firstAxis
          factorization.secondAxis) :=
    (form.perpendicular_comm _ _).2
      (form.cliffordCross_perpendicular_left
        factorization.firstAxis factorization.secondAxis)
  unfold TwoHalfTurnFactorization.cliffordPreimage
    NonNullEvenClifford.mul NonNullEvenClifford.halfTurnValue
    EvenClifford.ofVector EvenClifford.mul EvenClifford.productVector
  change form.Perpendicular factorization.firstAxis
    (Vector.sub
      (Vector.add
        (Vector.scale 0 factorization.secondAxis)
        (Vector.scale 0 factorization.firstAxis))
      (form.cliffordCross factorization.firstAxis
        factorization.secondAxis))
  unfold Perpendicular
  rw [form.bilinear_sub_right, form.bilinear_add_right,
    form.bilinear_scale_right, form.bilinear_scale_right]
  rw [crossPerpendicular]
  ring1

/-- Construct the uniform form-relative axis/spread interface from the same
cached two-half-turn data used by the projective Clifford correspondence. -/
def rotationAxisSpreadWitness [DecidableEq K]
    (form : TernaryForm K) (rotation : form.SpecialOrthogonal)
    (twoNonzero : (2 : K) ≠ 0) :
    RotationAxisSpreadWitness form rotation := by
  let factorization := form.twoHalfTurnFactorization rotation twoNonzero
  let representative := factorization.cliffordPreimage
  have represents : representative.actionRotation = rotation :=
    factorization.cliffordPreimage_actionRotation
  have perpendicularToAxis :
      form.Perpendicular factorization.firstAxis
        representative.toEvenClifford.vector :=
    factorization.firstAxis_perpendicular_cliffordPreimage
  have halfSpreadFormula :=
    representative.rotationHalfSpread_actionRotation twoNonzero
  have spreadFormula :=
    representative.rotationSpreadAt_eq_rotationSpread
      factorization.firstAxis factorization.firstNonNull
      perpendicularToAxis twoNonzero
  rw [represents] at halfSpreadFormula spreadFormula
  exact
    { factorization := factorization
      representative := representative
      representative_eq := rfl
      represents := represents
      axis := representative.toEvenClifford.vector
      axis_eq := rfl
      perpendicular := factorization.firstAxis
      perpendicularNonNull := factorization.firstNonNull
      perpendicularToAxis := perpendicularToAxis
      chart := form.cliffordChart representative
      halfSpread_eq := halfSpreadFormula
      spread_eq := spreadFormula }

/-- Uniform geometric-spread theorem for any other non-null direction
perpendicular to the cached canonical axis. -/
theorem RotationAxisSpreadWitness.spread_independent
    {form : TernaryForm K} {rotation : form.SpecialOrthogonal}
    (witness : RotationAxisSpreadWitness form rotation)
    (vector : Vector K) (nonNull : form.quadrance vector ≠ 0)
    (perpendicular : form.Perpendicular vector witness.axis)
    (twoNonzero : (2 : K) ≠ 0) :
    form.rotationSpreadAt rotation vector nonNull =
      form.rotationSpread rotation := by
  have representativePerpendicular :
      form.Perpendicular vector witness.representative.toEvenClifford.vector := by
    rw [← witness.axis_eq]
    exact perpendicular
  have formula :=
    witness.representative.rotationSpreadAt_eq_rotationSpread
      vector nonNull representativePerpendicular twoNonzero
  rw [witness.represents] at formula
  exact formula

/-- Any rotation whose half spread is not one is recovered as the cap of an
explicit normalized anchor computed from its cached representative. -/
def RotationAxisSpreadWitness.capNormalizationOfHalfSpreadNeOne
    [DecidableEq K] {form : TernaryForm K}
    {rotation : form.SpecialOrthogonal}
    (witness : RotationAxisSpreadWitness form rotation)
    (twoNonzero : (2 : K) ≠ 0)
    (notHalfTurn : form.rotationHalfSpread rotation ≠ 1) :
    CapNormalization form witness.representative := by
  have scalarNonzero :
      witness.representative.toEvenClifford.scalar ≠ 0 := by
    intro scalarZero
    apply notHalfTurn
    have vectorNonNull :=
      witness.representative.vectorNonNull_of_scalar_eq_zero scalarZero
    calc
      form.rotationHalfSpread rotation =
          form.rotationHalfSpread witness.representative.actionRotation := by
        rw [witness.represents]
      _ = form.rotationHalfSpread
          (form.halfTurnRotation
            witness.representative.toEvenClifford.vector vectorNonNull) := by
        rw [witness.representative.actionRotation_eq_halfTurn_of_scalar_eq_zero
          scalarZero]
      _ = 1 := form.rotationHalfSpread_halfTurn _ vectorNonNull twoNonzero
  exact form.capNormalization witness.representative scalarNonzero

theorem RotationAxisSpreadWitness.cap_recovery
    [DecidableEq K] {form : TernaryForm K}
    {rotation : form.SpecialOrthogonal}
    (witness : RotationAxisSpreadWitness form rotation)
    (twoNonzero : (2 : K) ≠ 0)
    (notHalfTurn : form.rotationHalfSpread rotation ≠ 1) :
    form.capRotation
        (witness.capNormalizationOfHalfSpreadNeOne twoNonzero
          notHalfTurn).anchor
        (witness.capNormalizationOfHalfSpreadNeOne twoNonzero
          notHalfTurn).defined = rotation := by
  calc
    form.capRotation
        (witness.capNormalizationOfHalfSpreadNeOne twoNonzero
          notHalfTurn).anchor
        (witness.capNormalizationOfHalfSpreadNeOne twoNonzero
          notHalfTurn).defined =
      witness.representative.actionRotation :=
        (witness.capNormalizationOfHalfSpreadNeOne twoNonzero
          notHalfTurn).actionRotation_eq
    _ = rotation := witness.represents

end TernaryForm

end RationalRotations
