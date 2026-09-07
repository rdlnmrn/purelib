import RationalRotations.Handedness
import RationalRotations.NullVectors
import RationalRotations.QuaternionObstruction

/-!
# Rational rotations, Theorem 65 and Examples 66--67

The square condition for a prescribed axis and half spread is carried by an
explicit nonzero root.  From that root we compute the two opposite anchor
vectors and hence the two inverse rotations.  No square-root operation or
choice principle enters the construction.
-/

namespace RationalRotations

variable {K : Type*} [RFAP.ExplicitField K]

/-- A displayed, executable witness that a field element is a nonzero
square. -/
structure NonzeroSquare (value : K) where
  root : K
  rootNonzero : root ≠ 0
  square : root ^ 2 = value

namespace NonzeroSquare

/-- The opposite root gives the same displayed square. -/
def neg {value : K} (certificate : NonzeroSquare value) :
    NonzeroSquare value where
  root := -certificate.root
  rootNonzero := by
    intro negZero
    apply certificate.rootNonzero
    calc
      certificate.root = -(-certificate.root) := by ring1
      _ = -0 := by rw [negZero]
      _ = 0 := by ring1
  square := by
    calc
      (-certificate.root) ^ 2 = certificate.root ^ 2 := by ring1
      _ = value := certificate.square

end NonzeroSquare

/-- The finite square test occurring in Theorem 65. -/
def prescribedAxisSquareValue (axis : Vector K) (spread : K) : K :=
  axis.quadrance * spread * (1 - spread)

/-- A rotation with prescribed non-half-turn axis line and half spread.
The nonzero scalar explicitly records equality of projective axis lines. -/
structure PrescribedAxisRotation (axis : Vector K) (spread : K) where
  rotation : Rotation K
  notHalfTurn : halfSpread rotation ≠ 1
  halfSpread_eq : halfSpread rotation = spread
  anchorScale : K
  anchorScaleNonzero : anchorScale ≠ 0
  anchor_eq : rotationAnchorVector rotation notHalfTurn =
    Vector.scale anchorScale axis

private theorem one_ne_zero_of_nonzero {value : K} (nonzero : value ≠ 0) :
    (1 : K) ≠ 0 := by
  intro oneZero
  apply nonzero
  calc
    value = value * 1 := by rw [mul_one]
    _ = value * 0 := by rw [oneZero]
    _ = 0 := by rw [mul_zero]

private theorem one_sub_ne_zero_of_ne_one {value : K} (notOne : value ≠ 1) :
    1 - value ≠ 0 := by
  intro differenceZero
  apply notOne
  calc
    value = 1 - (1 - value) := by ring1
    _ = 1 := by rw [differenceZero]; ring1

private theorem inverse_eq_of_mul_eq_one {value candidate : K}
    (valueNonzero : value ≠ 0) (certificate : value * candidate = 1) :
    value⁻¹ = candidate := by
  have cancel := RFAP.ExplicitField.mul_inv_cancel value valueNonzero
  calc
    value⁻¹ = value⁻¹ * 1 := by rw [mul_one]
    _ = value⁻¹ * (value * candidate) := by rw [certificate]
    _ = (value * value⁻¹) * candidate := by ring1
    _ = candidate := by rw [cancel, one_mul]

private theorem eq_div_of_mul_eq {left right denominator : K}
    (denominatorNonzero : denominator ≠ 0)
    (product : left * denominator = right) :
    left = right / denominator := by
  have cancel := RFAP.ExplicitField.mul_inv_cancel denominator
    denominatorNonzero
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    left = left * (denominator * denominator⁻¹) := by rw [cancel, mul_one]
    _ = (left * denominator) * denominator⁻¹ := by ring1
    _ = right * denominator⁻¹ := by rw [product]

private theorem eq_of_mul_right_eq {left right factor : K}
    (factorNonzero : factor ≠ 0) (equal : left * factor = right * factor) :
    left = right := by
  have cancel := RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    left = left * (factor * factor⁻¹) := by rw [cancel, mul_one]
    _ = (left * factor) * factor⁻¹ := by ring1
    _ = (right * factor) * factor⁻¹ := by rw [equal]
    _ = right * (factor * factor⁻¹) := by ring1
    _ = right := by rw [cancel, mul_one]

private theorem eq_zero_of_nonzero_mul_eq_zero {factor value : K}
    (factorNonzero : factor ≠ 0) (productZero : factor * value = 0) :
    value = 0 := by
  have cancel := RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    value = (factor * factor⁻¹) * value := by rw [cancel, one_mul]
    _ = factor⁻¹ * (factor * value) := by ring1
    _ = 0 := by rw [productZero, mul_zero]

private theorem cap_eq_of_vector_eq {left right : Vector K}
    (equal : left = right) (leftDefined : capDenominator left ≠ 0)
    (rightDefined : capDenominator right ≠ 0) :
    cap left leftDefined = cap right rightDefined := by
  subst right
  rfl

/-- Necessity in Theorem 65: a displayed rotation with the requested axis
and nonzero, non-unit half spread supplies a nonzero square root. -/
def PrescribedAxisRotation.squareCertificate
    {axis : Vector K} {spread : K}
    (candidate : PrescribedAxisRotation axis spread)
    (axisNonNull : axis.quadrance ≠ 0)
    (spreadNotOne : spread ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    NonzeroSquare (prescribedAxisSquareValue axis spread) where
  root := candidate.anchorScale * axis.quadrance * (1 - spread)
  rootNonzero := by
    exact RFAP.ExplicitField.mul_ne_zero
      (RFAP.ExplicitField.mul_ne_zero candidate.anchorScaleNonzero axisNonNull)
      (one_sub_ne_zero_of_ne_one spreadNotOne)
  square := by
    have complementNonzero := one_sub_ne_zero_of_ne_one spreadNotOne
    have complementCancel := RFAP.ExplicitField.mul_inv_cancel
      (1 - spread) complementNonzero
    have anchorQuadrance := quadrance_rotationAnchorVector
      candidate.rotation candidate.notHalfTurn twoNonzero
    rw [candidate.halfSpread_eq, candidate.anchor_eq,
      Vector.quadrance_scale] at anchorQuadrance
    unfold prescribedAxisSquareValue
    simp only [RFAP.ExplicitField.div_eq_mul_inv] at anchorQuadrance
    calc
      (candidate.anchorScale * axis.quadrance * (1 - spread)) ^ 2 =
          (candidate.anchorScale ^ 2 * axis.quadrance) *
            (axis.quadrance * (1 - spread) ^ 2) := by ring1
      _ = (spread * (1 - spread)⁻¹) *
            (axis.quadrance * (1 - spread) ^ 2) := by
              rw [anchorQuadrance]
      _ = axis.quadrance * spread * (1 - spread) := by
        calc
          spread * (1 - spread)⁻¹ *
                (axis.quadrance * (1 - spread) ^ 2) =
              axis.quadrance * spread * (1 - spread) *
                ((1 - spread) * (1 - spread)⁻¹) := by ring1
          _ = axis.quadrance * spread * (1 - spread) := by
            rw [complementCancel, mul_one]

/-- The anchor scalar computed from a supplied root of the Theorem 65
condition. -/
def prescribedAnchorScale (axis : Vector K) (spread : K)
    (certificate : NonzeroSquare (prescribedAxisSquareValue axis spread)) : K :=
  certificate.root / (axis.quadrance * (1 - spread))

theorem prescribedAnchorScale_nonzero (axis : Vector K) (spread : K)
    (certificate : NonzeroSquare (prescribedAxisSquareValue axis spread))
    (axisNonNull : axis.quadrance ≠ 0) (spreadNotOne : spread ≠ 1) :
    prescribedAnchorScale axis spread certificate ≠ 0 := by
  unfold prescribedAnchorScale
  exact RFAP.ExplicitField.div_ne_zero certificate.rootNonzero
    (RFAP.ExplicitField.mul_ne_zero axisNonNull
      (one_sub_ne_zero_of_ne_one spreadNotOne))

/-- The computed scalar has exactly the anchor quadrance required by the
half-spread equation. -/
theorem prescribedAnchorScale_quadrance (axis : Vector K) (spread : K)
    (certificate : NonzeroSquare (prescribedAxisSquareValue axis spread))
    (axisNonNull : axis.quadrance ≠ 0) (spreadNotOne : spread ≠ 1) :
    prescribedAnchorScale axis spread certificate ^ 2 * axis.quadrance =
      spread / (1 - spread) := by
  let complement := 1 - spread
  let denominator := axis.quadrance * complement
  have complementNonzero : complement ≠ 0 :=
    one_sub_ne_zero_of_ne_one spreadNotOne
  have denominatorNonzero : denominator ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero axisNonNull complementNonzero
  have denominatorCancel := RFAP.ExplicitField.mul_inv_cancel denominator
    denominatorNonzero
  apply eq_div_of_mul_eq complementNonzero
  unfold prescribedAnchorScale
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  change (certificate.root * denominator⁻¹) ^ 2 * axis.quadrance *
      complement = spread
  calc
    (certificate.root * denominator⁻¹) ^ 2 * axis.quadrance *
          complement =
        certificate.root ^ 2 * denominator⁻¹ *
          (denominator * denominator⁻¹) := by
            unfold denominator
            ring1
    _ = certificate.root ^ 2 * denominator⁻¹ := by
      rw [denominatorCancel, mul_one]
    _ = (axis.quadrance * spread * complement) * denominator⁻¹ := by
      rw [certificate.square]
      rfl
    _ = spread * (denominator * denominator⁻¹) := by
      unfold denominator
      ring1
    _ = spread := by rw [denominatorCancel, mul_one]

private theorem prescribedAnchor_capDenominator_mul
    (axis : Vector K) (spread : K)
    (certificate : NonzeroSquare (prescribedAxisSquareValue axis spread))
    (axisNonNull : axis.quadrance ≠ 0) (spreadNotOne : spread ≠ 1) :
    capDenominator
        (Vector.scale (prescribedAnchorScale axis spread certificate) axis) *
      (1 - spread) = 1 := by
  have quadranceFormula := prescribedAnchorScale_quadrance axis spread
    certificate axisNonNull spreadNotOne
  have complementNonzero := one_sub_ne_zero_of_ne_one spreadNotOne
  have complementCancel := RFAP.ExplicitField.mul_inv_cancel
    (1 - spread) complementNonzero
  unfold capDenominator
  rw [Vector.quadrance_scale, quadranceFormula]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    (1 + spread * (1 - spread)⁻¹) * (1 - spread) =
        (1 - spread) + spread *
          ((1 - spread)⁻¹ * (1 - spread)) := by ring1
    _ = (1 - spread) + spread := by
      rw [show (1 - spread)⁻¹ * (1 - spread) = 1 by
        calc
          (1 - spread)⁻¹ * (1 - spread) =
              (1 - spread) * (1 - spread)⁻¹ := by ring1
          _ = 1 := complementCancel,
        mul_one]
    _ = 1 := by ring1

theorem prescribedAnchor_capDefined (axis : Vector K) (spread : K)
    (certificate : NonzeroSquare (prescribedAxisSquareValue axis spread))
    (axisNonNull : axis.quadrance ≠ 0) (spreadNotOne : spread ≠ 1) :
    capDenominator
      (Vector.scale (prescribedAnchorScale axis spread certificate) axis) ≠ 0 := by
  intro denominatorZero
  have product := prescribedAnchor_capDenominator_mul axis spread certificate
    axisNonNull spreadNotOne
  rw [denominatorZero, zero_mul] at product
  exact (one_ne_zero_of_nonzero axisNonNull) product.symm

theorem halfSpread_prescribedAnchor (axis : Vector K) (spread : K)
    (certificate : NonzeroSquare (prescribedAxisSquareValue axis spread))
    (axisNonNull : axis.quadrance ≠ 0) (spreadNotOne : spread ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    halfSpread
        (capRotation
          (Vector.scale (prescribedAnchorScale axis spread certificate) axis)
          (prescribedAnchor_capDefined axis spread certificate axisNonNull
            spreadNotOne)) = spread := by
  let anchorVector :=
    Vector.scale (prescribedAnchorScale axis spread certificate) axis
  let defined := prescribedAnchor_capDefined axis spread certificate
    axisNonNull spreadNotOne
  let negativeDefined := prescribedAnchor_capDefined axis spread
    certificate.neg axisNonNull spreadNotOne
  have denominatorProduct := prescribedAnchor_capDenominator_mul axis spread
    certificate axisNonNull spreadNotOne
  have denominatorInverse := inverse_eq_of_mul_eq_one defined denominatorProduct
  have quadranceFormula := prescribedAnchorScale_quadrance axis spread
    certificate axisNonNull spreadNotOne
  have complementNonzero := one_sub_ne_zero_of_ne_one spreadNotOne
  have complementCancel := RFAP.ExplicitField.mul_inv_cancel
    (1 - spread) complementNonzero
  rw [halfSpread_cap anchorVector defined twoNonzero]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  rw [denominatorInverse]
  unfold anchorVector
  rw [Vector.quadrance_scale, quadranceFormula]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    spread * (1 - spread)⁻¹ * (1 - spread) =
        spread * ((1 - spread) * (1 - spread)⁻¹) := by ring1
    _ = spread := by rw [complementCancel, mul_one]

/-- Sufficiency in Theorem 65 as an executable construction. -/
def prescribedAxisRotationOfSquare (axis : Vector K) (spread : K)
    (certificate : NonzeroSquare (prescribedAxisSquareValue axis spread))
    (axisNonNull : axis.quadrance ≠ 0) (spreadNotOne : spread ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) : PrescribedAxisRotation axis spread where
  rotation := capRotation
    (Vector.scale (prescribedAnchorScale axis spread certificate) axis)
    (prescribedAnchor_capDefined axis spread certificate axisNonNull
      spreadNotOne)
  notHalfTurn := halfSpread_cap_ne_one _ _ twoNonzero
  halfSpread_eq := halfSpread_prescribedAnchor axis spread certificate
    axisNonNull spreadNotOne twoNonzero
  anchorScale := prescribedAnchorScale axis spread certificate
  anchorScaleNonzero := prescribedAnchorScale_nonzero axis spread certificate
    axisNonNull spreadNotOne
  anchor_eq := by
    unfold rotationAnchorVector
    rw [rotationAnchor_cap _ _ twoNonzero]
    exact anchorVector_anchor _

/-- Theorem 65's existence equivalence, with every square witness retained
as finite data. -/
theorem prescribedAxisRotation_exists_iff
    (axis : Vector K) (spread : K)
    (axisNonNull : axis.quadrance ≠ 0) (_spreadNonzero : spread ≠ 0)
    (spreadNotOne : spread ≠ 1) (twoNonzero : (2 : K) ≠ 0) :
    Nonempty (PrescribedAxisRotation axis spread) ↔
      Nonempty (NonzeroSquare (prescribedAxisSquareValue axis spread)) := by
  constructor
  · rintro ⟨candidate⟩
    exact ⟨candidate.squareCertificate axisNonNull spreadNotOne twoNonzero⟩
  · rintro ⟨certificate⟩
    exact ⟨prescribedAxisRotationOfSquare axis spread certificate axisNonNull
      spreadNotOne twoNonzero⟩

/-- Multiplication by four does not change the existence condition, because
four is the displayed square of two.  This is Theorem 65's equivalent
spread formulation. -/
theorem prescribedAxis_square_iff_spreadSquare
    (axis : Vector K) (spread : K) (twoNonzero : (2 : K) ≠ 0) :
    Nonempty (NonzeroSquare (prescribedAxisSquareValue axis spread)) ↔
      Nonempty
        (NonzeroSquare
          (axis.quadrance * (4 * spread * (1 - spread)))) := by
  constructor
  · rintro ⟨certificate⟩
    refine ⟨{
      root := 2 * certificate.root
      rootNonzero := RFAP.ExplicitField.mul_ne_zero twoNonzero
        certificate.rootNonzero
      square := ?_ }⟩
    unfold prescribedAxisSquareValue at certificate
    calc
      (2 * certificate.root) ^ 2 = 4 * certificate.root ^ 2 := by ring1
      _ = 4 * (axis.quadrance * spread * (1 - spread)) := by
        rw [certificate.square]
      _ = axis.quadrance * (4 * spread * (1 - spread)) := by ring1
  · rintro ⟨certificate⟩
    have twoCancel := RFAP.ExplicitField.mul_inv_cancel (2 : K) twoNonzero
    refine ⟨{
      root := certificate.root / 2
      rootNonzero := RFAP.ExplicitField.div_ne_zero certificate.rootNonzero
        twoNonzero
      square := ?_ }⟩
    unfold prescribedAxisSquareValue
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      (certificate.root * (2 : K)⁻¹) ^ 2 =
          certificate.root ^ 2 * (2 : K)⁻¹ ^ 2 := by ring1
      _ = (axis.quadrance * (4 * spread * (1 - spread))) *
          (2 : K)⁻¹ ^ 2 := by rw [certificate.square]
      _ = axis.quadrance * spread * (1 - spread) *
          (2 * (2 : K)⁻¹) ^ 2 := by ring1
      _ = axis.quadrance * spread * (1 - spread) := by
        rw [twoCancel]
        ring1

theorem prescribedAnchorScale_neg (axis : Vector K) (spread : K)
    (certificate : NonzeroSquare (prescribedAxisSquareValue axis spread)) :
    prescribedAnchorScale axis spread certificate.neg =
      -prescribedAnchorScale axis spread certificate := by
  unfold prescribedAnchorScale NonzeroSquare.neg
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  ring1

theorem prescribedAnchorVector_neg (axis : Vector K) (spread : K)
    (certificate : NonzeroSquare (prescribedAxisSquareValue axis spread)) :
    Vector.scale (prescribedAnchorScale axis spread certificate.neg) axis =
      Vector.neg
        (Vector.scale (prescribedAnchorScale axis spread certificate) axis) := by
  rw [prescribedAnchorScale_neg]
  ext <;> unfold Vector.scale Vector.neg <;> ring1

/-- The two rotations computed from the two square roots are inverse in
both orders. -/
theorem prescribedAxisRotation_pair_inverse
    (axis : Vector K) (spread : K)
    (certificate : NonzeroSquare (prescribedAxisSquareValue axis spread))
    (axisNonNull : axis.quadrance ≠ 0) (spreadNotOne : spread ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    Matrix3.mul
        (prescribedAxisRotationOfSquare axis spread certificate axisNonNull
          spreadNotOne twoNonzero).rotation.matrix
        (prescribedAxisRotationOfSquare axis spread certificate.neg axisNonNull
          spreadNotOne twoNonzero).rotation.matrix = Matrix3.identity ∧
      Matrix3.mul
        (prescribedAxisRotationOfSquare axis spread certificate.neg axisNonNull
          spreadNotOne twoNonzero).rotation.matrix
        (prescribedAxisRotationOfSquare axis spread certificate axisNonNull
          spreadNotOne twoNonzero).rotation.matrix = Matrix3.identity := by
  let anchorVector :=
    Vector.scale (prescribedAnchorScale axis spread certificate) axis
  let defined := prescribedAnchor_capDefined axis spread certificate
    axisNonNull spreadNotOne
  let negativeDefined := prescribedAnchor_capDefined axis spread
    certificate.neg axisNonNull spreadNotOne
  have oppositeAnchor := prescribedAnchorVector_neg axis spread certificate
  have negativeCap :
      cap
          (Vector.scale
            (prescribedAnchorScale axis spread certificate.neg) axis)
          negativeDefined =
        cap (Vector.neg anchorVector) (cap_neg_defined anchorVector defined) :=
    cap_eq_of_vector_eq oppositeAnchor negativeDefined
      (cap_neg_defined anchorVector defined)
  constructor
  · change Matrix3.mul (cap anchorVector defined)
        (cap
          (Vector.scale
            (prescribedAnchorScale axis spread certificate.neg) axis)
          negativeDefined) =
        Matrix3.identity
    rw [negativeCap]
    exact cap_mul_cap_neg anchorVector defined
  · change Matrix3.mul
        (cap
          (Vector.scale
            (prescribedAnchorScale axis spread certificate.neg) axis)
          negativeDefined)
        (cap anchorVector defined) = Matrix3.identity
    rw [negativeCap]
    exact cap_neg_mul_cap anchorVector defined

private theorem prescribedAnchorVector_ne_zero
    (axis : Vector K) (spread : K)
    (certificate : NonzeroSquare (prescribedAxisSquareValue axis spread))
    (axisNonNull : axis.quadrance ≠ 0) (spreadNotOne : spread ≠ 1) :
    Vector.scale (prescribedAnchorScale axis spread certificate) axis ≠
      Vector.zero := by
  intro vectorZero
  have scaledNonNull := Vector.quadrance_scale_ne_zero
    (prescribedAnchorScale axis spread certificate) axis
    (prescribedAnchorScale_nonzero axis spread certificate axisNonNull
      spreadNotOne) axisNonNull
  apply scaledNonNull
  rw [vectorZero, Vector.quadrance_zero]

/-- The two displayed rotations are distinct. -/
theorem prescribedAxisRotation_pair_distinct
    (axis : Vector K) (spread : K)
    (certificate : NonzeroSquare (prescribedAxisSquareValue axis spread))
    (axisNonNull : axis.quadrance ≠ 0) (spreadNotOne : spread ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    (prescribedAxisRotationOfSquare axis spread certificate axisNonNull
      spreadNotOne twoNonzero).rotation.matrix ≠
      (prescribedAxisRotationOfSquare axis spread certificate.neg axisNonNull
        spreadNotOne twoNonzero).rotation.matrix := by
  let anchorVector :=
    Vector.scale (prescribedAnchorScale axis spread certificate) axis
  let defined := prescribedAnchor_capDefined axis spread certificate
    axisNonNull spreadNotOne
  let negativeDefined := prescribedAnchor_capDefined axis spread
    certificate.neg axisNonNull spreadNotOne
  have distinct := cap_ne_cap_neg_of_ne_zero anchorVector defined
    (prescribedAnchorVector_ne_zero axis spread certificate axisNonNull
      spreadNotOne) twoNonzero
  have negativeCap :
      cap
          (Vector.scale
            (prescribedAnchorScale axis spread certificate.neg) axis)
          negativeDefined =
        cap (Vector.neg anchorVector) (cap_neg_defined anchorVector defined) :=
    cap_eq_of_vector_eq
      (prescribedAnchorVector_neg axis spread certificate) negativeDefined
      (cap_neg_defined anchorVector defined)
  change cap anchorVector defined ≠
    cap
      (Vector.scale (prescribedAnchorScale axis spread certificate.neg) axis)
      negativeDefined
  intro equal
  exact distinct (equal.trans negativeCap)

/-- Opposite roots give opposite handedness determinants, measured with the
same first anchor vector and perpendicular transversal. -/
theorem prescribedAxisRotation_pair_oppositeHandedness
    (axis : Vector K) (spread : K)
    (certificate : NonzeroSquare (prescribedAxisSquareValue axis spread))
    (axisNonNull : axis.quadrance ≠ 0) (spreadNotOne : spread ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) (transversal : Vector K)
    (perpendicular : transversal.Perpendicular
      (Vector.scale (prescribedAnchorScale axis spread certificate) axis)) :
    handednessDet
        (Vector.scale (prescribedAnchorScale axis spread certificate) axis)
        transversal
        (prescribedAxisRotationOfSquare axis spread certificate.neg axisNonNull
          spreadNotOne twoNonzero).rotation.matrix =
      -handednessDet
        (Vector.scale (prescribedAnchorScale axis spread certificate) axis)
        transversal
        (prescribedAxisRotationOfSquare axis spread certificate axisNonNull
          spreadNotOne twoNonzero).rotation.matrix := by
  let anchorVector :=
    Vector.scale (prescribedAnchorScale axis spread certificate) axis
  let defined := prescribedAnchor_capDefined axis spread certificate
    axisNonNull spreadNotOne
  let negativeDefined := prescribedAnchor_capDefined axis spread
    certificate.neg axisNonNull spreadNotOne
  have negativeCap :
      cap
          (Vector.scale
            (prescribedAnchorScale axis spread certificate.neg) axis)
          negativeDefined =
        cap (Vector.neg anchorVector) (cap_neg_defined anchorVector defined) :=
    cap_eq_of_vector_eq
      (prescribedAnchorVector_neg axis spread certificate) negativeDefined
      (cap_neg_defined anchorVector defined)
  change handednessDet anchorVector transversal
      (cap
        (Vector.scale (prescribedAnchorScale axis spread certificate.neg) axis)
        negativeDefined) =
      -handednessDet anchorVector transversal (cap anchorVector defined)
  rw [negativeCap,
    handednessDet_cap_neg_sameAxis anchorVector defined transversal
      perpendicular,
    handednessDet_cap anchorVector defined transversal perpendicular]

/-- Any field element with the same square as the computed anchor scalar is
that scalar or its negative. -/
private theorem eq_or_eq_neg_of_square_eq [DecidableEq K]
    {value canonical : K} (equalSquares : value ^ 2 = canonical ^ 2) :
    value = canonical ∨ value = -canonical := by
  by_cases equal : value = canonical
  · exact Or.inl equal
  · have differenceNonzero : value - canonical ≠ 0 := by
      intro differenceZero
      apply equal
      calc
        value = (value - canonical) + canonical := by ring1
        _ = canonical := by rw [differenceZero, zero_add]
    have productZero : (value - canonical) * (value + canonical) = 0 := by
      calc
        (value - canonical) * (value + canonical) =
            value ^ 2 - canonical ^ 2 := by ring1
        _ = 0 := by rw [equalSquares]; ring1
    have sumZero := eq_zero_of_nonzero_mul_eq_zero differenceNonzero productZero
    exact Or.inr (by
      calc
        value = (value + canonical) - canonical := by ring1
        _ = -canonical := by rw [sumZero]; ring1)

/-- The “exactly two” part of Theorem 65: every displayed rotation with the
requested axis line and half spread is one of the two computed matrices. -/
theorem PrescribedAxisRotation.matrix_eq_pair [DecidableEq K]
    {axis : Vector K} {spread : K}
    (candidate : PrescribedAxisRotation axis spread)
    (certificate : NonzeroSquare (prescribedAxisSquareValue axis spread))
    (axisNonNull : axis.quadrance ≠ 0) (spreadNotOne : spread ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    candidate.rotation.matrix =
        (prescribedAxisRotationOfSquare axis spread certificate axisNonNull
          spreadNotOne twoNonzero).rotation.matrix ∨
      candidate.rotation.matrix =
        (prescribedAxisRotationOfSquare axis spread certificate.neg axisNonNull
          spreadNotOne twoNonzero).rotation.matrix := by
  have candidateQuadrance := quadrance_rotationAnchorVector candidate.rotation
    candidate.notHalfTurn twoNonzero
  rw [candidate.halfSpread_eq, candidate.anchor_eq,
    Vector.quadrance_scale] at candidateQuadrance
  have canonicalQuadrance := prescribedAnchorScale_quadrance axis spread
    certificate axisNonNull spreadNotOne
  have scaleSquares : candidate.anchorScale ^ 2 =
      prescribedAnchorScale axis spread certificate ^ 2 :=
    eq_of_mul_right_eq axisNonNull (by
      rw [candidateQuadrance, canonicalQuadrance])
  let recovered := rotationAnchorVector candidate.rotation candidate.notHalfTurn
  let recoveredDefined := rotationAnchorVector_capDefined candidate.rotation
    candidate.notHalfTurn twoNonzero
  let candidateDefined :
      capDenominator (Vector.scale candidate.anchorScale axis) ≠ 0 := by
    rw [← candidate.anchor_eq]
    exact recoveredDefined
  let positiveDefined := prescribedAnchor_capDefined axis spread certificate
    axisNonNull spreadNotOne
  let negativeDefined := prescribedAnchor_capDefined axis spread certificate.neg
    axisNonNull spreadNotOne
  have recoveredCap : cap recovered recoveredDefined =
      cap (Vector.scale candidate.anchorScale axis) candidateDefined :=
    cap_eq_of_vector_eq candidate.anchor_eq recoveredDefined candidateDefined
  rcases eq_or_eq_neg_of_square_eq scaleSquares with scaleEqual | scaleEqual
  · left
    have scaledEqual : Vector.scale candidate.anchorScale axis =
        Vector.scale (prescribedAnchorScale axis spread certificate) axis :=
      congrArg (fun scalar => Vector.scale scalar axis) scaleEqual
    calc
      candidate.rotation.matrix =
          cap recovered recoveredDefined :=
        (cap_rotationAnchor candidate.rotation candidate.notHalfTurn
          twoNonzero).symm
      _ = cap (Vector.scale candidate.anchorScale axis) candidateDefined :=
        recoveredCap
      _ = cap
          (Vector.scale
            (prescribedAnchorScale axis spread certificate) axis)
          positiveDefined :=
        cap_eq_of_vector_eq scaledEqual candidateDefined positiveDefined
      _ = (prescribedAxisRotationOfSquare axis spread certificate axisNonNull
          spreadNotOne twoNonzero).rotation.matrix := rfl
  · right
    have scaledEqual : Vector.scale candidate.anchorScale axis =
        Vector.scale (prescribedAnchorScale axis spread certificate.neg) axis := by
      apply congrArg (fun scalar => Vector.scale scalar axis)
      calc
        candidate.anchorScale =
            -prescribedAnchorScale axis spread certificate := scaleEqual
        _ = prescribedAnchorScale axis spread certificate.neg :=
          (prescribedAnchorScale_neg axis spread certificate).symm
    calc
      candidate.rotation.matrix =
          cap recovered recoveredDefined :=
        (cap_rotationAnchor candidate.rotation candidate.notHalfTurn
          twoNonzero).symm
      _ = cap (Vector.scale candidate.anchorScale axis) candidateDefined :=
        recoveredCap
      _ = cap
          (Vector.scale
            (prescribedAnchorScale axis spread certificate.neg) axis)
          negativeDefined :=
        cap_eq_of_vector_eq scaledEqual candidateDefined negativeDefined
      _ = (prescribedAxisRotationOfSquare axis spread certificate.neg
          axisNonNull spreadNotOne twoNonzero).rotation.matrix := rfl

/-- The endpoint `p=1`: the canonical half turn about the supplied non-null
axis has half spread one. -/
theorem prescribedAxis_halfTurn_halfSpread (axis : Vector K)
    (axisNonNull : axis.quadrance ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    halfSpread (halfTurnRotation axis axisNonNull) = 1 :=
  halfSpread_halfTurn axis axisNonNull twoNonzero

/-- The endpoint `p=1` is unique on the projective axis line: replacing the
axis by any nonzero scalar multiple gives the same half-turn matrix. -/
theorem prescribedAxis_halfTurn_unique (axis : Vector K)
    (axisNonNull : axis.quadrance ≠ 0) (scalar : K)
    (scalarNonzero : scalar ≠ 0) :
    (halfTurnRotation (Vector.scale scalar axis)
      (Vector.quadrance_scale_ne_zero scalar axis scalarNonzero axisNonNull)).matrix =
      (halfTurnRotation axis axisNonNull).matrix :=
  halfTurn_scale scalar axis scalarNonzero axisNonNull

/-- The endpoint `p=0`: in a field whose only null vector is zero, a
half-spread-zero rotation is the identity matrix. -/
theorem rotation_eq_identity_of_halfSpread_zero
    (separation : SumSquaresSeparate K) (rotation : Rotation K)
    (spreadZero : halfSpread rotation = 0) (twoNonzero : (2 : K) ≠ 0) :
    rotation.matrix = Matrix3.identity := by
  have oneNonzero : (1 : K) ≠ 0 := one_ne_zero_of_nonzero twoNonzero
  have notHalfTurn : halfSpread rotation ≠ 1 := by
    intro spreadOne
    apply oneNonzero
    calc
      (1 : K) = halfSpread rotation := spreadOne.symm
      _ = 0 := spreadZero
  let recovered := rotationAnchorVector rotation notHalfTurn
  let recoveredDefined := rotationAnchorVector_capDefined rotation notHalfTurn
    twoNonzero
  have recoveredNull : recovered.IsNull := by
    have quadranceFormula := quadrance_rotationAnchorVector rotation
      notHalfTurn twoNonzero
    rw [spreadZero] at quadranceFormula
    simp only [sub_zero, RFAP.ExplicitField.zero_div] at quadranceFormula
    exact quadranceFormula
  have recoveredZero := only_zero_null_vector separation recovered recoveredNull
  let zeroDefined : capDenominator (Vector.zero : Vector K) ≠ 0 := by
    unfold capDenominator
    rw [Vector.quadrance_zero, add_zero]
    exact oneNonzero
  calc
    rotation.matrix = cap recovered recoveredDefined :=
      (cap_rotationAnchor rotation notHalfTurn twoNonzero).symm
    _ = cap Vector.zero zeroDefined :=
      cap_eq_of_vector_eq recoveredZero recoveredDefined zeroDefined
    _ = Matrix3.identity := by
      ext <;> unfold cap Matrix3.add Matrix3.scale Matrix3.identity
        Matrix3.mul anchor Vector.zero <;> ring1

namespace ExampleSixtySix

abbrev Scalar := RFAP.ConstructiveFraction.Rational

def coordinateAxis : Vector Scalar := ⟨1, 0, 0⟩

theorem coordinateAxis_quadrance : coordinateAxis.quadrance = 1 := by
  unfold coordinateAxis Vector.quadrance Vector.dot
  ring1

/-- The rational parameter in Example 66. -/
def parameterHalfSpread (parameter : Scalar) : Scalar :=
  parameter ^ 2 / (1 + parameter ^ 2)

/-- The square root of `p(1-p)` supplied by the same parameter. -/
def parameterConditionRoot (parameter : Scalar) : Scalar :=
  parameter / (1 + parameter ^ 2)

theorem parameter_condition (parameter : Scalar)
    (denominatorNonzero : 1 + parameter ^ 2 ≠ 0) :
    prescribedAxisSquareValue coordinateAxis
        (parameterHalfSpread parameter) =
      parameterConditionRoot parameter ^ 2 := by
  have cancel := RFAP.ExplicitField.mul_inv_cancel
    (1 + parameter ^ 2) denominatorNonzero
  unfold prescribedAxisSquareValue parameterHalfSpread parameterConditionRoot
  rw [coordinateAxis_quadrance]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    1 * (parameter ^ 2 * (1 + parameter ^ 2)⁻¹) *
          (1 - parameter ^ 2 * (1 + parameter ^ 2)⁻¹) =
        parameter ^ 2 * (1 + parameter ^ 2)⁻¹ *
          ((1 + parameter ^ 2) * (1 + parameter ^ 2)⁻¹ -
            parameter ^ 2 * (1 + parameter ^ 2)⁻¹) := by
      rw [cancel]
      ring1
    _ = (parameter * (1 + parameter ^ 2)⁻¹) ^ 2 := by ring1

theorem parameter_one_sub_two_halfSpread (parameter : Scalar)
    (denominatorNonzero : 1 + parameter ^ 2 ≠ 0) :
    1 - 2 * parameterHalfSpread parameter =
      (1 - parameter ^ 2) / (1 + parameter ^ 2) := by
  have cancel := RFAP.ExplicitField.mul_inv_cancel
    (1 + parameter ^ 2) denominatorNonzero
  unfold parameterHalfSpread
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    1 - 2 * (parameter ^ 2 * (1 + parameter ^ 2)⁻¹) =
        (1 + parameter ^ 2) * (1 + parameter ^ 2)⁻¹ -
          2 * parameter ^ 2 * (1 + parameter ^ 2)⁻¹ := by
      rw [cancel]
      ring1
    _ = (1 - parameter ^ 2) * (1 + parameter ^ 2)⁻¹ := by ring1

/-- The displayed rational parameter gives a normalized Pythagorean triple. -/
theorem parameter_pythagorean (parameter : Scalar)
    (denominatorNonzero : 1 + parameter ^ 2 ≠ 0) :
    ((1 - parameter ^ 2) / (1 + parameter ^ 2)) ^ 2 +
        ((2 * parameter) / (1 + parameter ^ 2)) ^ 2 = 1 := by
  have cancel := RFAP.ExplicitField.mul_inv_cancel
    (1 + parameter ^ 2) denominatorNonzero
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    ((1 - parameter ^ 2) * (1 + parameter ^ 2)⁻¹) ^ 2 +
          ((2 * parameter) * (1 + parameter ^ 2)⁻¹) ^ 2 =
        ((1 + parameter ^ 2) * (1 + parameter ^ 2)⁻¹) ^ 2 := by
      ring1
    _ = 1 := by rw [cancel]; ring1

/-- The parameter recovered from a supplied nonzero square root. -/
def parameterOfCondition (spread : Scalar)
    (certificate :
      NonzeroSquare (prescribedAxisSquareValue coordinateAxis spread)) :
    Scalar := spread / certificate.root

private theorem condition_root_square (spread : Scalar)
    (certificate :
      NonzeroSquare (prescribedAxisSquareValue coordinateAxis spread)) :
    certificate.root ^ 2 = spread * (1 - spread) := by
  simpa only [prescribedAxisSquareValue, coordinateAxis_quadrance, one_mul]
    using certificate.square

theorem parameterOfCondition_nonzero (spread : Scalar)
    (certificate :
      NonzeroSquare (prescribedAxisSquareValue coordinateAxis spread))
    (spreadNonzero : spread ≠ 0) :
    parameterOfCondition spread certificate ≠ 0 :=
  RFAP.ExplicitField.div_ne_zero spreadNonzero certificate.rootNonzero

private theorem parameterOfCondition_square (spread : Scalar)
    (certificate :
      NonzeroSquare (prescribedAxisSquareValue coordinateAxis spread))
    (spreadNotOne : spread ≠ 1) :
    parameterOfCondition spread certificate ^ 2 =
      spread / (1 - spread) := by
  have complementNonzero := one_sub_ne_zero_of_ne_one spreadNotOne
  have rootCancel := RFAP.ExplicitField.mul_inv_cancel certificate.root
    certificate.rootNonzero
  apply eq_div_of_mul_eq complementNonzero
  unfold parameterOfCondition
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    (spread * certificate.root⁻¹) ^ 2 * (1 - spread) =
        spread * (spread * (1 - spread)) * certificate.root⁻¹ ^ 2 := by
      ring1
    _ = spread * certificate.root ^ 2 * certificate.root⁻¹ ^ 2 := by
      rw [condition_root_square spread certificate]
    _ = spread * (certificate.root * certificate.root⁻¹) ^ 2 := by
      ring1
    _ = spread := by rw [rootCancel]; ring1

private theorem parameterOfCondition_denominator_nonzero (spread : Scalar)
    (certificate :
      NonzeroSquare (prescribedAxisSquareValue coordinateAxis spread))
    (spreadNotOne : spread ≠ 1) :
    1 + parameterOfCondition spread certificate ^ 2 ≠ 0 := by
  have complementNonzero := one_sub_ne_zero_of_ne_one spreadNotOne
  have complementCancel := RFAP.ExplicitField.mul_inv_cancel
    (1 - spread) complementNonzero
  intro denominatorZero
  have product :
      (1 + parameterOfCondition spread certificate ^ 2) *
          (1 - spread) = 1 := by
    rw [parameterOfCondition_square spread certificate spreadNotOne]
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      (1 + spread * (1 - spread)⁻¹) * (1 - spread) =
          (1 - spread) + spread *
            ((1 - spread)⁻¹ * (1 - spread)) := by ring1
      _ = 1 := by
        rw [show (1 - spread)⁻¹ * (1 - spread) = 1 by
          calc
            (1 - spread)⁻¹ * (1 - spread) =
                (1 - spread) * (1 - spread)⁻¹ := by ring1
            _ = 1 := complementCancel]
        ring1
  rw [denominatorZero, zero_mul] at product
  exact (one_ne_zero_of_nonzero certificate.rootNonzero) product.symm

theorem parameterOfCondition_recovers (spread : Scalar)
    (certificate :
      NonzeroSquare (prescribedAxisSquareValue coordinateAxis spread))
    (spreadNotOne : spread ≠ 1) :
    parameterHalfSpread (parameterOfCondition spread certificate) = spread := by
  let parameter := parameterOfCondition spread certificate
  have parameterSquare := parameterOfCondition_square spread certificate
    spreadNotOne
  have denominatorNonzero := parameterOfCondition_denominator_nonzero spread
    certificate spreadNotOne
  have complementNonzero := one_sub_ne_zero_of_ne_one spreadNotOne
  have complementCancel := RFAP.ExplicitField.mul_inv_cancel
    (1 - spread) complementNonzero
  have denominatorProduct :
      (1 + parameter ^ 2) * (1 - spread) = 1 := by
    rw [parameterSquare]
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      (1 + spread * (1 - spread)⁻¹) * (1 - spread) =
          (1 - spread) + spread *
            ((1 - spread)⁻¹ * (1 - spread)) := by ring1
      _ = 1 := by
        rw [show (1 - spread)⁻¹ * (1 - spread) = 1 by
          calc
            (1 - spread)⁻¹ * (1 - spread) =
                (1 - spread) * (1 - spread)⁻¹ := by ring1
            _ = 1 := complementCancel]
        ring1
  have denominatorInverse := inverse_eq_of_mul_eq_one denominatorNonzero
    denominatorProduct
  unfold parameterHalfSpread
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  rw [denominatorInverse, parameterSquare]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    spread * (1 - spread)⁻¹ * (1 - spread) =
        spread * ((1 - spread) * (1 - spread)⁻¹) := by ring1
    _ = spread := by rw [complementCancel, mul_one]

/-- Example 66's exact parametrization of all non-endpoint coordinate-axis
half spreads satisfying the square condition. -/
theorem coordinateAxis_condition_iff_parameter (spread : Scalar)
    (spreadNonzero : spread ≠ 0) (spreadNotOne : spread ≠ 1) :
    Nonempty
        (NonzeroSquare (prescribedAxisSquareValue coordinateAxis spread)) ↔
      ∃ parameter : Scalar, parameter ≠ 0 ∧
        1 + parameter ^ 2 ≠ 0 ∧
        spread = parameterHalfSpread parameter := by
  constructor
  · rintro ⟨certificate⟩
    refine ⟨parameterOfCondition spread certificate,
      parameterOfCondition_nonzero spread certificate spreadNonzero,
      parameterOfCondition_denominator_nonzero spread certificate spreadNotOne,
      ?_⟩
    exact (parameterOfCondition_recovers spread certificate spreadNotOne).symm
  · rintro ⟨parameter, parameterNonzero, denominatorNonzero, spreadFormula⟩
    refine ⟨{
      root := parameterConditionRoot parameter
      rootNonzero := RFAP.ExplicitField.div_ne_zero parameterNonzero
        denominatorNonzero
      square := ?_ }⟩
    rw [spreadFormula, parameter_condition parameter denominatorNonzero]

theorem quarterTurn_parameter : parameterHalfSpread 1 = (1 : Scalar) / 2 := by
  decide

theorem threeFourFive_parameter :
    parameterHalfSpread ((1 : Scalar) / 2) = (1 : Scalar) / 5 := by
  decide

end ExampleSixtySix

namespace ExampleSixtySeven

abbrev Scalar := RFAP.ConstructiveFraction.Rational

def diagonalAxis : Vector Scalar := ⟨1, 1, 1⟩

theorem diagonalAxis_quadrance : diagonalAxis.quadrance = 3 := by
  unfold diagonalAxis Vector.quadrance Vector.dot
  ring1

theorem diagonalAxis_nonNull : diagonalAxis.quadrance ≠ 0 := by
  rw [diagonalAxis_quadrance]
  decide

private theorem twoNonzero : (2 : Scalar) ≠ 0 := by decide

theorem quarter_condition_value :
    prescribedAxisSquareValue diagonalAxis ((1 : Scalar) / 2) = 3 / 4 := by
  unfold prescribedAxisSquareValue
  rw [diagonalAxis_quadrance]
  decide

/-- The square condition for a diagonal quarter turn would make three a
rational square. -/
theorem quarter_condition_not_square :
    ¬ Nonempty
      (NonzeroSquare
        (prescribedAxisSquareValue diagonalAxis ((1 : Scalar) / 2))) := by
  rintro ⟨certificate⟩
  have rootSquare : certificate.root ^ 2 = (3 : Scalar) / 4 := by
    rw [← quarter_condition_value]
    exact certificate.square
  apply RFAP.ConstructiveFraction.square_ne_three (2 * certificate.root)
  calc
    (2 * certificate.root) ^ 2 = 4 * certificate.root ^ 2 := by ring1
    _ = 4 * ((3 : Scalar) / 4) := by rw [rootSquare]
    _ = 3 := by decide

/-- Example 67: no rational rotation has the diagonal axis and half spread
one half. -/
theorem no_rational_quarter_turn :
    ¬ Nonempty
      (PrescribedAxisRotation diagonalAxis ((1 : Scalar) / 2)) := by
  intro candidate
  have condition :=
    (prescribedAxisRotation_exists_iff diagonalAxis ((1 : Scalar) / 2)
      diagonalAxis_nonNull (by decide) (by decide) twoNonzero).1 candidate
  exact quarter_condition_not_square condition

theorem threeQuarter_condition_value :
    prescribedAxisSquareValue diagonalAxis ((3 : Scalar) / 4) = 9 / 16 := by
  unfold prescribedAxisSquareValue
  rw [diagonalAxis_quadrance]
  decide

/-- The displayed root `3/4` certifies the attainable diagonal rotation of
half spread `3/4`. -/
def threeQuarterCertificate :
    NonzeroSquare
      (prescribedAxisSquareValue diagonalAxis ((3 : Scalar) / 4)) where
  root := 3 / 4
  rootNonzero := by decide
  square := by
    rw [threeQuarter_condition_value]
    decide

theorem threeQuarter_anchorScale :
    prescribedAnchorScale diagonalAxis ((3 : Scalar) / 4)
      threeQuarterCertificate = 1 := by
  change ((3 : Scalar) / 4) /
      (diagonalAxis.quadrance * (1 - (3 : Scalar) / 4)) = 1
  rw [diagonalAxis_quadrance]
  decide

theorem diagonalCapDefined : capDenominator diagonalAxis ≠ 0 := by
  unfold capDenominator
  rw [diagonalAxis_quadrance]
  decide

/-- The attainable example is the cap of `A_(1,1,1)` itself. -/
def diagonalRotation : Rotation Scalar :=
  capRotation diagonalAxis diagonalCapDefined

theorem diagonalRotation_halfSpread :
    halfSpread diagonalRotation = (3 : Scalar) / 4 := by
  unfold diagonalRotation
  rw [halfSpread_cap diagonalAxis diagonalCapDefined twoNonzero]
  unfold capDenominator
  rw [diagonalAxis_quadrance]
  decide

theorem constructed_threeQuarter_eq_diagonalRotation :
    (prescribedAxisRotationOfSquare diagonalAxis ((3 : Scalar) / 4)
      threeQuarterCertificate diagonalAxis_nonNull (by decide)
      twoNonzero).rotation.matrix = diagonalRotation.matrix := by
  let constructedVector := Vector.scale
    (prescribedAnchorScale diagonalAxis ((3 : Scalar) / 4)
      threeQuarterCertificate) diagonalAxis
  let constructedDefined := prescribedAnchor_capDefined diagonalAxis
    ((3 : Scalar) / 4) threeQuarterCertificate diagonalAxis_nonNull
    (by decide)
  have vectorEqual : constructedVector = diagonalAxis := by
    unfold constructedVector
    rw [threeQuarter_anchorScale, Vector.one_scale]
  change cap constructedVector constructedDefined =
    cap diagonalAxis diagonalCapDefined
  exact cap_eq_of_vector_eq vectorEqual constructedDefined diagonalCapDefined

/-- The half twist of the displayed anchor is three. -/
theorem diagonalRotation_halfTwist : diagonalAxis.quadrance = 3 :=
  diagonalAxis_quadrance

end ExampleSixtySeven

end RationalRotations
