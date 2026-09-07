import RationalRotations.TernaryClifford
import RationalRotations.Handedness
import mathlib.RFAP.CanonicalFractionField

/-!
# The split ternary Clifford algebra as two-by-two matrices

For the Minkowski form `t²+r²-s²`, the explicit even Clifford algebra is
identified constructively with displayed two-by-two matrices.  The inverse
coordinate map records the necessary characteristic-not-two hypothesis.
-/

namespace RationalRotations

variable {K : Type*} [RFAP.ExplicitField K]

/-- A transparent two-by-two matrix, kept independent of the CCL parser and
projective-geometry layers. -/
@[ext]
structure Matrix2 (K : Type*) where
  tt : K
  tr : K
  rt : K
  rr : K
deriving DecidableEq, Repr

namespace Matrix2

def identity : Matrix2 K := ⟨1, 0, 0, 1⟩

def mul (left right : Matrix2 K) : Matrix2 K :=
  ⟨left.tt * right.tt + left.tr * right.rt,
    left.tt * right.tr + left.tr * right.rr,
    left.rt * right.tt + left.rr * right.rt,
    left.rt * right.tr + left.rr * right.rr⟩

def scale (factor : K) (matrix : Matrix2 K) : Matrix2 K :=
  ⟨factor * matrix.tt, factor * matrix.tr,
    factor * matrix.rt, factor * matrix.rr⟩

def determinant (matrix : Matrix2 K) : K :=
  matrix.tt * matrix.rr - matrix.tr * matrix.rt

def adjugate (matrix : Matrix2 K) : Matrix2 K :=
  ⟨matrix.rr, -matrix.tr, -matrix.rt, matrix.tt⟩

@[simp] theorem identity_mul (matrix : Matrix2 K) :
    mul identity matrix = matrix := by
  ext <;> unfold mul identity <;> ring1

@[simp] theorem mul_identity (matrix : Matrix2 K) :
    mul matrix identity = matrix := by
  ext <;> unfold mul identity <;> ring1

theorem mul_assoc (first second third : Matrix2 K) :
    mul (mul first second) third = mul first (mul second third) := by
  ext <;> unfold mul <;> ring1

theorem determinant_mul (left right : Matrix2 K) :
    determinant (mul left right) = determinant left * determinant right := by
  unfold determinant mul
  ring1

theorem determinant_adjugate (matrix : Matrix2 K) :
    determinant matrix.adjugate = determinant matrix := by
  unfold determinant adjugate
  ring1

theorem mul_adjugate (matrix : Matrix2 K) :
    mul matrix matrix.adjugate = scale matrix.determinant identity := by
  ext <;> unfold mul adjugate scale determinant identity <;> ring1

theorem adjugate_mul (matrix : Matrix2 K) :
    mul matrix.adjugate matrix = scale matrix.determinant identity := by
  ext <;> unfold mul adjugate scale determinant identity <;> ring1

end Matrix2

namespace MinkowskiClifford

/-- Split-quaternion coordinates as the two-by-two matrix algebra anticipated
in Problem 71. -/
def toMatrix (oneNonzero : (1 : K) ≠ 0)
    (value : (TernaryForm.minkowski oneNonzero).EvenClifford) : Matrix2 K :=
  ⟨value.scalar + value.vector.t,
    value.vector.r - value.vector.s,
    value.vector.r + value.vector.s,
    value.scalar - value.vector.t⟩

/-- The inverse split-quaternion coordinate map. -/
def fromMatrix (oneNonzero : (1 : K) ≠ 0) (matrix : Matrix2 K) :
    (TernaryForm.minkowski oneNonzero).EvenClifford :=
  ⟨(2 : K)⁻¹ * (matrix.tt + matrix.rr),
    ⟨(2 : K)⁻¹ * (matrix.tt - matrix.rr),
      (2 : K)⁻¹ * (matrix.tr + matrix.rt),
      (2 : K)⁻¹ * (matrix.rt - matrix.tr)⟩⟩

theorem toMatrix_fromMatrix (oneNonzero : (1 : K) ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) (matrix : Matrix2 K) :
    toMatrix oneNonzero (fromMatrix oneNonzero matrix) = matrix := by
  have cancel := RFAP.ExplicitField.mul_inv_cancel (2 : K) twoNonzero
  have reverseCancel : (2 : K)⁻¹ * 2 = 1 := by
    calc
      (2 : K)⁻¹ * 2 = 2 * (2 : K)⁻¹ := by ring1
      _ = 1 := cancel
  have halfDouble (entry : K) :
      (2 : K)⁻¹ * (entry + entry) = entry := by
    calc
      (2 : K)⁻¹ * (entry + entry) =
          ((2 : K)⁻¹ * 2) * entry := by ring1
      _ = entry := by rw [reverseCancel, one_mul]
  apply Matrix2.ext
  · unfold toMatrix fromMatrix
    calc
      (2 : K)⁻¹ * (matrix.tt + matrix.rr) +
          (2 : K)⁻¹ * (matrix.tt - matrix.rr) =
        (2 : K)⁻¹ * (matrix.tt + matrix.tt) := by ring1
      _ = matrix.tt := halfDouble matrix.tt
  · unfold toMatrix fromMatrix
    calc
      (2 : K)⁻¹ * (matrix.tr + matrix.rt) -
          (2 : K)⁻¹ * (matrix.rt - matrix.tr) =
        (2 : K)⁻¹ * (matrix.tr + matrix.tr) := by ring1
      _ = matrix.tr := halfDouble matrix.tr
  · unfold toMatrix fromMatrix
    calc
      (2 : K)⁻¹ * (matrix.tr + matrix.rt) +
          (2 : K)⁻¹ * (matrix.rt - matrix.tr) =
        (2 : K)⁻¹ * (matrix.rt + matrix.rt) := by ring1
      _ = matrix.rt := halfDouble matrix.rt
  · unfold toMatrix fromMatrix
    calc
      (2 : K)⁻¹ * (matrix.tt + matrix.rr) -
          (2 : K)⁻¹ * (matrix.tt - matrix.rr) =
        (2 : K)⁻¹ * (matrix.rr + matrix.rr) := by ring1
      _ = matrix.rr := halfDouble matrix.rr

theorem fromMatrix_toMatrix (oneNonzero : (1 : K) ≠ 0)
    (twoNonzero : (2 : K) ≠ 0)
    (value : (TernaryForm.minkowski oneNonzero).EvenClifford) :
    fromMatrix oneNonzero (toMatrix oneNonzero value) = value := by
  have cancel := RFAP.ExplicitField.mul_inv_cancel (2 : K) twoNonzero
  have reverseCancel : (2 : K)⁻¹ * 2 = 1 := by
    calc
      (2 : K)⁻¹ * 2 = 2 * (2 : K)⁻¹ := by ring1
      _ = 1 := cancel
  have halfDouble (entry : K) :
      (2 : K)⁻¹ * (entry + entry) = entry := by
    calc
      (2 : K)⁻¹ * (entry + entry) =
          ((2 : K)⁻¹ * 2) * entry := by ring1
      _ = entry := by rw [reverseCancel, one_mul]
  apply TernaryForm.EvenClifford.ext
  · unfold fromMatrix toMatrix
    calc
      (2 : K)⁻¹ *
          ((value.scalar + value.vector.t) +
            (value.scalar - value.vector.t)) =
        (2 : K)⁻¹ * (value.scalar + value.scalar) := by ring1
      _ = value.scalar := halfDouble value.scalar
  · apply Vector.ext
    · unfold fromMatrix toMatrix
      calc
        (2 : K)⁻¹ *
            ((value.scalar + value.vector.t) -
              (value.scalar - value.vector.t)) =
          (2 : K)⁻¹ * (value.vector.t + value.vector.t) := by ring1
        _ = value.vector.t := halfDouble value.vector.t
    · unfold fromMatrix toMatrix
      calc
        (2 : K)⁻¹ *
            ((value.vector.r - value.vector.s) +
              (value.vector.r + value.vector.s)) =
          (2 : K)⁻¹ * (value.vector.r + value.vector.r) := by ring1
        _ = value.vector.r := halfDouble value.vector.r
    · unfold fromMatrix toMatrix
      calc
        (2 : K)⁻¹ *
            ((value.vector.r + value.vector.s) -
              (value.vector.r - value.vector.s)) =
          (2 : K)⁻¹ * (value.vector.s + value.vector.s) := by ring1
        _ = value.vector.s := halfDouble value.vector.s

theorem toMatrix_injective (oneNonzero : (1 : K) ≠ 0)
    (twoNonzero : (2 : K) ≠ 0)
    {left right : (TernaryForm.minkowski oneNonzero).EvenClifford}
    (equal : toMatrix oneNonzero left = toMatrix oneNonzero right) :
    left = right := by
  have mapped := congrArg (fromMatrix oneNonzero) equal
  rw [fromMatrix_toMatrix oneNonzero twoNonzero,
    fromMatrix_toMatrix oneNonzero twoNonzero] at mapped
  exact mapped

/-- The split coordinate map preserves multiplication exactly. -/
theorem toMatrix_mul (oneNonzero : (1 : K) ≠ 0)
    (left right : (TernaryForm.minkowski oneNonzero).EvenClifford) :
    toMatrix oneNonzero (TernaryForm.EvenClifford.mul left right) =
      Matrix2.mul (toMatrix oneNonzero left) (toMatrix oneNonzero right) := by
  ext <;> unfold toMatrix Matrix2.mul TernaryForm.EvenClifford.mul
    TernaryForm.EvenClifford.productScalar
    TernaryForm.EvenClifford.productVector TernaryForm.cliffordCross
    TernaryForm.bilinear TernaryForm.minkowski TernaryForm.ofMatrix
    Matrix3.adjugate Matrix3.determinant Matrix3.rowMul Vector.dot
    Vector.cross Vector.add Vector.sub Vector.scale <;> ring1

/-- Matrix determinant is precisely the split Clifford reduced norm. -/
theorem determinant_toMatrix (oneNonzero : (1 : K) ≠ 0)
    (value : (TernaryForm.minkowski oneNonzero).EvenClifford) :
    Matrix2.determinant (toMatrix oneNonzero value) = value.norm := by
  unfold Matrix2.determinant toMatrix TernaryForm.EvenClifford.norm
  rw [TernaryForm.minkowski_determinant,
    TernaryForm.quadrance_minkowski]
  ring1

/-- Clifford conjugation becomes the ordinary two-by-two adjugate. -/
theorem toMatrix_conjugate (oneNonzero : (1 : K) ≠ 0)
    (value : (TernaryForm.minkowski oneNonzero).EvenClifford) :
    toMatrix oneNonzero value.conjugate =
      Matrix2.adjugate (toMatrix oneNonzero value) := by
  ext <;> unfold toMatrix TernaryForm.EvenClifford.conjugate
    Matrix2.adjugate Vector.neg <;> ring1

/-- Trace-zero matrix corresponding to a Minkowski vector. -/
def vectorMatrix (vector : Vector K) : Matrix2 K :=
  ⟨vector.t, vector.r - vector.s,
    vector.r + vector.s, -vector.t⟩

theorem toMatrix_ofVector (oneNonzero : (1 : K) ≠ 0)
    (vector : Vector K) :
    toMatrix oneNonzero
        (TernaryForm.EvenClifford.ofVector
          (TernaryForm.minkowski oneNonzero) vector) =
      vectorMatrix vector := by
  ext <;> unfold toMatrix TernaryForm.EvenClifford.ofVector vectorMatrix <;>
    ring1

theorem vectorMatrix_scale (factor : K) (vector : Vector K) :
    vectorMatrix (Vector.scale factor vector) =
      Matrix2.scale factor (vectorMatrix vector) := by
  ext <;> unfold vectorMatrix Matrix2.scale Vector.scale <;> ring1

/-- Homogeneous parametrization of the split null conic. -/
def nullParameter (first second : K) : Vector K :=
  ⟨first ^ 2 - second ^ 2,
    2 * first * second,
    first ^ 2 + second ^ 2⟩

theorem nullParameter_isNull (oneNonzero : (1 : K) ≠ 0)
    (first second : K) :
    (TernaryForm.minkowski oneNonzero).IsNull
      (nullParameter first second) := by
  unfold TernaryForm.IsNull
  rw [TernaryForm.quadrance_minkowski]
  unfold nullParameter
  ring1

/-- Explicit projective coordinates for a nonzero null direction.  The
parameter vector is tied to the input by a displayed nonzero scale. -/
structure NullParameterWitness (vector : Vector K) where
  first : K
  second : K
  factor : K
  parametersNonzero : first ≠ 0 ∨ second ≠ 0
  factorNonzero : factor ≠ 0
  parameter_spec :
    nullParameter first second = Vector.scale factor vector

private theorem eq_zero_of_square_eq_zero [DecidableEq K] (value : K)
    (squareZero : value ^ 2 = 0) : value = 0 := by
  by_cases valueZero : value = 0
  · exact valueZero
  · have squareNonzero : value ^ 2 ≠ 0 := by
      simpa only [pow_two] using
        RFAP.ExplicitField.mul_ne_zero valueZero valueZero
    exact (squareNonzero squareZero).elim

private theorem eq_zero_of_nonzero_mul_eq_zero {factor value : K}
    (factorNonzero : factor ≠ 0) (productZero : factor * value = 0) :
    value = 0 := by
  have cancel := RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    value = (factor * factor⁻¹) * value := by rw [cancel, one_mul]
    _ = factor⁻¹ * (factor * value) := by ring1
    _ = 0 := by rw [productZero, mul_zero]

theorem nullParameter_nonzero [DecidableEq K]
    (twoNonzero : (2 : K) ≠ 0) (first second : K)
    (parametersNonzero : first ≠ 0 ∨ second ≠ 0) :
    nullParameter first second ≠ Vector.zero := by
  intro parameterZero
  have firstCoordinate := congrArg Vector.t parameterZero
  have thirdCoordinate := congrArg Vector.s parameterZero
  change first ^ 2 - second ^ 2 = 0 at firstCoordinate
  change first ^ 2 + second ^ 2 = 0 at thirdCoordinate
  have twiceFirstSquare : 2 * first ^ 2 = 0 := by
    calc
      2 * first ^ 2 =
          (first ^ 2 - second ^ 2) +
            (first ^ 2 + second ^ 2) := by ring1
      _ = 0 := by rw [firstCoordinate, thirdCoordinate, add_zero]
  have twiceSecondSquare : 2 * second ^ 2 = 0 := by
    calc
      2 * second ^ 2 =
          (first ^ 2 + second ^ 2) -
            (first ^ 2 - second ^ 2) := by ring1
      _ = 0 := by rw [firstCoordinate, thirdCoordinate]; ring1
  have firstSquareZero := eq_zero_of_nonzero_mul_eq_zero
    twoNonzero twiceFirstSquare
  have secondSquareZero := eq_zero_of_nonzero_mul_eq_zero
    twoNonzero twiceSecondSquare
  have firstZero := eq_zero_of_square_eq_zero first firstSquareZero
  have secondZero := eq_zero_of_square_eq_zero second secondSquareZero
  rcases parametersNonzero with firstNonzero | secondNonzero
  · exact firstNonzero firstZero
  · exact secondNonzero secondZero

/-- Every nonzero null vector lies on the homogeneous parametrization, by one
decidable two-chart split and without choosing roots. -/
def nullParameterWitness [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (vector : Vector K)
    (null : (TernaryForm.minkowski oneNonzero).IsNull vector)
    (nonzero : vector ≠ Vector.zero) : NullParameterWitness vector := by
  have nullEquation :
      vector.t ^ 2 + vector.r ^ 2 - vector.s ^ 2 = 0 := by
    unfold TernaryForm.IsNull at null
    rw [TernaryForm.quadrance_minkowski] at null
    exact null
  by_cases chartZero : vector.s + vector.t = 0
  · have sEq : vector.s = -vector.t := by
      calc
        vector.s = vector.s + vector.t - vector.t := by ring1
        _ = -vector.t := by rw [chartZero]; ring1
    have rSquareZero : vector.r ^ 2 = 0 := by
      calc
        vector.r ^ 2 =
            vector.t ^ 2 + vector.r ^ 2 - vector.s ^ 2 := by
          rw [sEq]
          ring1
        _ = 0 := nullEquation
    have rZero := eq_zero_of_square_eq_zero vector.r rSquareZero
    have tNonzero : vector.t ≠ 0 := by
      intro tZero
      apply nonzero
      apply Vector.ext
      · change vector.t = 0
        exact tZero
      · change vector.r = 0
        exact rZero
      · change vector.s = 0
        rw [sEq, tZero]
        ring1
    have negTNonzero : -vector.t ≠ 0 := by
      intro negTZero
      apply tNonzero
      calc
        vector.t = -(-vector.t) := by ring1
        _ = -0 := by rw [negTZero]
        _ = 0 := by ring1
    exact
      { first := 0
        second := vector.t
        factor := -vector.t
        parametersNonzero := Or.inr tNonzero
        factorNonzero := negTNonzero
        parameter_spec := by
          apply Vector.ext
          · change 0 ^ 2 - vector.t ^ 2 =
              -vector.t * vector.t
            ring1
          · change 2 * 0 * vector.t = -vector.t * vector.r
            rw [rZero]
            ring1
          · change 0 ^ 2 + vector.t ^ 2 =
              -vector.t * vector.s
            rw [sEq]
            ring1 }
  · have factorNonzero : 2 * (vector.s + vector.t) ≠ 0 :=
      RFAP.ExplicitField.mul_ne_zero twoNonzero chartZero
    exact
      { first := vector.s + vector.t
        second := vector.r
        factor := 2 * (vector.s + vector.t)
        parametersNonzero := Or.inl chartZero
        factorNonzero := factorNonzero
        parameter_spec := by
          apply Vector.ext
          · change
              (vector.s + vector.t) ^ 2 - vector.r ^ 2 =
                2 * (vector.s + vector.t) * vector.t
            calc
              (vector.s + vector.t) ^ 2 - vector.r ^ 2 =
                  2 * (vector.s + vector.t) * vector.t -
                    (vector.t ^ 2 + vector.r ^ 2 - vector.s ^ 2) := by
                ring1
              _ = 2 * (vector.s + vector.t) * vector.t := by
                rw [nullEquation]
                ring1
          · change
              2 * (vector.s + vector.t) * vector.r =
                2 * (vector.s + vector.t) * vector.r
            rfl
          · change
              (vector.s + vector.t) ^ 2 + vector.r ^ 2 =
                2 * (vector.s + vector.t) * vector.s
            calc
              (vector.s + vector.t) ^ 2 + vector.r ^ 2 =
                  2 * (vector.s + vector.t) * vector.s +
                    (vector.t ^ 2 + vector.r ^ 2 - vector.s ^ 2) := by
                ring1
              _ = 2 * (vector.s + vector.t) * vector.s := by
                rw [nullEquation]
                ring1 }

/-- Both directions of the constructive projective parametrization of the
Minkowski null conic, packaged for direct downstream use. -/
structure NullConicParametrization [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0) where
  parameterNull : ∀ first second : K,
    (TernaryForm.minkowski oneNonzero).IsNull
      (nullParameter first second)
  parameterNonzero : ∀ first second : K,
    first ≠ 0 ∨ second ≠ 0 →
      nullParameter first second ≠ Vector.zero
  covers : ∀ vector : Vector K,
    (TernaryForm.minkowski oneNonzero).IsNull vector →
      vector ≠ Vector.zero → NullParameterWitness vector

def nullConicParametrization [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    NullConicParametrization oneNonzero twoNonzero where
  parameterNull := nullParameter_isNull oneNonzero
  parameterNonzero := nullParameter_nonzero twoNonzero
  covers := nullParameterWitness oneNonzero twoNonzero

/-- Norm-one split Clifford representative attached to a null axis. -/
def parabolicRaw (oneNonzero : (1 : K) ≠ 0) (axis : Vector K) :
    (TernaryForm.minkowski oneNonzero).EvenClifford :=
  ⟨1, axis⟩

theorem parabolicRaw_norm (oneNonzero : (1 : K) ≠ 0)
    (axis : Vector K)
    (null : (TernaryForm.minkowski oneNonzero).IsNull axis) :
    (parabolicRaw oneNonzero axis).norm = 1 := by
  unfold parabolicRaw TernaryForm.EvenClifford.norm
  unfold TernaryForm.IsNull at null
  rw [null]
  ring1

/-- The total non-null representative, with norm-one certificate cached. -/
def parabolicValue (oneNonzero : (1 : K) ≠ 0) (axis : Vector K)
    (null : (TernaryForm.minkowski oneNonzero).IsNull axis) :
    (TernaryForm.minkowski oneNonzero).NonNullEvenClifford where
  toEvenClifford := parabolicRaw oneNonzero axis
  normNonzero := by
    rw [parabolicRaw_norm oneNonzero axis null]
    exact oneNonzero

/-- Explicit action formula for the null-axis, scalar-one family. -/
theorem parabolic_action (oneNonzero : (1 : K) ≠ 0)
    (axis vector : Vector K)
    (null : (TernaryForm.minkowski oneNonzero).IsNull axis) :
    (parabolicValue oneNonzero axis null).action vector =
      Vector.add
        (Vector.add vector
          (Vector.scale
            (-2 *
              (TernaryForm.minkowski oneNonzero).bilinear vector axis)
            axis))
        (Vector.scale (-2)
          ((TernaryForm.minkowski oneNonzero).cliffordCross vector axis)) := by
  have oneInverse : (1 : K)⁻¹ = 1 := by
    have cancel := RFAP.ExplicitField.mul_inv_cancel (1 : K) oneNonzero
    simpa only [one_mul] using cancel
  have nullQuadrance :
      (TernaryForm.minkowski oneNonzero).quadrance axis = 0 := null
  unfold TernaryForm.NonNullEvenClifford.action
  change
    Vector.scale (parabolicRaw oneNonzero axis).norm⁻¹
        ((parabolicRaw oneNonzero axis).actionNumerator vector) = _
  rw [parabolicRaw_norm oneNonzero axis null, oneInverse,
    Vector.one_scale]
  unfold TernaryForm.EvenClifford.actionNumerator parabolicRaw
  rw [nullQuadrance, TernaryForm.minkowski_determinant]
  ext <;> unfold Vector.add Vector.scale <;> ring1

theorem parabolic_fixedAxis (oneNonzero : (1 : K) ≠ 0)
    (axis : Vector K)
    (null : (TernaryForm.minkowski oneNonzero).IsNull axis) :
    (parabolicValue oneNonzero axis null).action axis = axis := by
  rw [parabolic_action]
  have nullQuadrance :
      (TernaryForm.minkowski oneNonzero).quadrance axis = 0 := null
  have nullBilinear :
      (TernaryForm.minkowski oneNonzero).bilinear axis axis = 0 :=
    nullQuadrance
  rw [nullBilinear,
    TernaryForm.cliffordCross_self,
    Vector.scale_zero, Vector.add_zero]
  ext <;> unfold Vector.add Vector.scale <;> ring1

/-- The action on the first coordinate vector exposes all three axis
coordinates and is used to certify that a nonzero null axis is nontrivial. -/
theorem parabolic_action_firstBasis (oneNonzero : (1 : K) ≠ 0)
    (axis : Vector K)
    (null : (TernaryForm.minkowski oneNonzero).IsNull axis) :
    (parabolicValue oneNonzero axis null).action
        (⟨1, 0, 0⟩ : Vector K) =
      ⟨1 - 2 * axis.t ^ 2,
        -2 * axis.t * axis.r - 2 * axis.s,
        -2 * axis.t * axis.s - 2 * axis.r⟩ := by
  rw [parabolic_action]
  ext <;> unfold TernaryForm.bilinear TernaryForm.minkowski
    TernaryForm.ofMatrix TernaryForm.cliffordCross Matrix3.adjugate
    Matrix3.rowMul Vector.dot Vector.cross Vector.add Vector.scale <;> ring1

/-- A nonzero null axis gives a nonidentity parabolic action in
characteristic different from two. -/
theorem parabolic_nonidentity [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (axis : Vector K)
    (null : (TernaryForm.minkowski oneNonzero).IsNull axis)
    (axisNonzero : axis ≠ Vector.zero) :
    (parabolicValue oneNonzero axis null).actionMatrix ≠
      Matrix3.identity := by
  intro identityAction
  have firstBasisFixed :
      (parabolicValue oneNonzero axis null).action
          (⟨1, 0, 0⟩ : Vector K) =
        (⟨1, 0, 0⟩ : Vector K) := by
    calc
      (parabolicValue oneNonzero axis null).action ⟨1, 0, 0⟩ =
          Matrix3.rowMul (⟨1, 0, 0⟩ : Vector K)
            (parabolicValue oneNonzero axis null).actionMatrix :=
        ((parabolicValue oneNonzero axis null).rowMul_actionMatrix
          ⟨1, 0, 0⟩).symm
      _ = Matrix3.rowMul (⟨1, 0, 0⟩ : Vector K)
          Matrix3.identity := by rw [identityAction]
      _ = ⟨1, 0, 0⟩ := Matrix3.rowMul_identity ⟨1, 0, 0⟩
  rw [parabolic_action_firstBasis] at firstBasisFixed
  have firstEq := congrArg Vector.t firstBasisFixed
  have secondEq := congrArg Vector.r firstBasisFixed
  have thirdEq := congrArg Vector.s firstBasisFixed
  change 1 - 2 * axis.t ^ 2 = 1 at firstEq
  change -2 * axis.t * axis.r - 2 * axis.s = 0 at secondEq
  change -2 * axis.t * axis.s - 2 * axis.r = 0 at thirdEq
  have twiceTSquare : 2 * axis.t ^ 2 = 0 := by
    calc
      2 * axis.t ^ 2 = 1 - (1 - 2 * axis.t ^ 2) := by ring1
      _ = 0 := by rw [firstEq]; ring1
  have tSquareZero := eq_zero_of_nonzero_mul_eq_zero
    twoNonzero twiceTSquare
  have tZero := eq_zero_of_square_eq_zero axis.t tSquareZero
  have twiceS : 2 * axis.s = 0 := by rw [tZero] at secondEq; simpa using secondEq
  have twiceR : 2 * axis.r = 0 := by rw [tZero] at thirdEq; simpa using thirdEq
  have sZero := eq_zero_of_nonzero_mul_eq_zero twoNonzero twiceS
  have rZero := eq_zero_of_nonzero_mul_eq_zero twoNonzero twiceR
  apply axisNonzero
  apply Vector.ext
  · exact tZero
  · exact rZero
  · exact sZero

theorem parabolic_trace (oneNonzero : (1 : K) ≠ 0)
    (axis : Vector K)
    (null : (TernaryForm.minkowski oneNonzero).IsNull axis) :
    Matrix3.trace (parabolicValue oneNonzero axis null).actionMatrix = 3 := by
  have oneInverse : (1 : K)⁻¹ = 1 := by
    have cancel := RFAP.ExplicitField.mul_inv_cancel (1 : K) oneNonzero
    simpa only [one_mul] using cancel
  have nullQuadrance :
      (TernaryForm.minkowski oneNonzero).quadrance axis = 0 := null
  have nullBilinear :
      (TernaryForm.minkowski oneNonzero).bilinear axis axis = 0 :=
    nullQuadrance
  unfold TernaryForm.NonNullEvenClifford.actionMatrix
  change Matrix3.trace
    (Matrix3.scale (parabolicRaw oneNonzero axis).norm⁻¹
      (parabolicRaw oneNonzero axis).actionNumeratorMatrix) = 3
  rw [parabolicRaw_norm oneNonzero axis null, oneInverse,
    Matrix3.one_scale]
  unfold TernaryForm.EvenClifford.actionNumeratorMatrix parabolicRaw
  rw [Matrix3.trace_add, Matrix3.trace_add,
    Matrix3.trace_scale, Matrix3.trace_identity,
    Matrix3.trace_scale, Matrix3.trace_outer,
    Vector.dot_comm, ← TernaryForm.bilinear_eq_dot_dual,
    Matrix3.trace_scale,
    TernaryForm.trace_actionSkew,
    nullQuadrance, nullBilinear,
    TernaryForm.minkowski_determinant]
  ring1

/-- The null-axis family is unipotent: its displayed characteristic
polynomial is `(X-1)³`. -/
theorem parabolic_characteristic (oneNonzero : (1 : K) ≠ 0)
    (axis : Vector K)
    (null : (TernaryForm.minkowski oneNonzero).IsNull axis) (X : K) :
    Matrix3.characteristicValue
        (parabolicValue oneNonzero axis null).actionMatrix X =
      (X - 1) ^ 3 := by
  let form := TernaryForm.minkowski oneNonzero
  let value := parabolicValue oneNonzero axis null
  have negNull : form.IsNull (Vector.neg axis) := by
    unfold form TernaryForm.IsNull TernaryForm.quadrance
    rw [TernaryForm.bilinear_neg_left,
      TernaryForm.bilinear_neg_right]
    calc
      - -(TernaryForm.minkowski oneNonzero).bilinear axis axis =
          (TernaryForm.minkowski oneNonzero).bilinear axis axis := by
        ring1
      _ = 0 := null
  have conjugateEq :
      value.conjugate = parabolicValue oneNonzero (Vector.neg axis) negNull := by
    apply TernaryForm.NonNullEvenClifford.ext
    · rfl
    · rfl
  have inverseMatrixEq := congrArg
    (fun rotation : form.SpecialOrthogonal => rotation.matrix)
    value.actionRotation_conjugate
  change value.conjugate.actionMatrix = value.actionInverseMatrix at inverseMatrixEq
  have matrixAdjugate :
      Matrix3.mul value.actionMatrix
          (Matrix3.adjugate value.actionMatrix) = Matrix3.identity := by
    rw [Matrix3.mul_adjugate, value.determinant_actionMatrix,
      Matrix3.one_scale]
  have adjugateEq :
      Matrix3.adjugate value.actionMatrix = value.actionInverseMatrix := by
    calc
      Matrix3.adjugate value.actionMatrix =
          Matrix3.mul Matrix3.identity
            (Matrix3.adjugate value.actionMatrix) :=
        (Matrix3.identity_mul (Matrix3.adjugate value.actionMatrix)).symm
      _ = Matrix3.mul
          (Matrix3.mul value.actionInverseMatrix value.actionMatrix)
          (Matrix3.adjugate value.actionMatrix) := by
        rw [value.actionInverseMatrix_mul_actionMatrix]
      _ = Matrix3.mul value.actionInverseMatrix
          (Matrix3.mul value.actionMatrix
            (Matrix3.adjugate value.actionMatrix)) := by
        rw [Matrix3.mul_assoc]
      _ = Matrix3.mul value.actionInverseMatrix Matrix3.identity := by
        rw [matrixAdjugate]
      _ = value.actionInverseMatrix :=
        Matrix3.mul_identity value.actionInverseMatrix
  have inverseTrace : Matrix3.trace value.actionInverseMatrix = 3 := by
    calc
      Matrix3.trace value.actionInverseMatrix =
          Matrix3.trace value.conjugate.actionMatrix := by
        rw [inverseMatrixEq]
      _ = Matrix3.trace
          (parabolicValue oneNonzero (Vector.neg axis) negNull).actionMatrix := by
        rw [conjugateEq]
      _ = 3 := parabolic_trace oneNonzero (Vector.neg axis) negNull
  rw [Matrix3.characteristicValue_expansion,
    parabolic_trace oneNonzero axis null]
  unfold Matrix3.principalTrace
  rw [adjugateEq, inverseTrace, value.determinant_actionMatrix]
  ring1

/-- Every perpendicular transversal has zero frame-handedness for the
null-axis family. -/
theorem parabolic_handedness_zero (oneNonzero : (1 : K) ≠ 0)
    (axis transversal : Vector K)
    (null : (TernaryForm.minkowski oneNonzero).IsNull axis)
    (perpendicular :
      (TernaryForm.minkowski oneNonzero).Perpendicular transversal axis) :
    handednessDet axis transversal
      (parabolicValue oneNonzero axis null).actionMatrix = 0 := by
  let form := TernaryForm.minkowski oneNonzero
  have crossQuadrance := form.quadrance_cliffordCross transversal axis
  have nullQuadrance : form.quadrance axis = 0 := null
  have perpendicularBilinear : form.bilinear transversal axis = 0 :=
    perpendicular
  rw [nullQuadrance, perpendicularBilinear] at crossQuadrance
  have crossQuadranceZero :
      form.quadrance (form.cliffordCross transversal axis) = 0 := by
    calc
      form.quadrance (form.cliffordCross transversal axis) =
          form.determinant *
            (form.quadrance transversal * 0 - 0 ^ 2) := crossQuadrance
      _ = 0 := by ring1
  have triple := form.bilinear_cliffordCross axis transversal
    (form.cliffordCross transversal axis)
  rw [form.cliffordCross_anticomm axis transversal,
    form.bilinear_neg_left] at triple
  unfold TernaryForm.quadrance at crossQuadranceZero
  rw [crossQuadranceZero, TernaryForm.minkowski_determinant] at triple
  rw [neg_zero] at triple
  have determinantZero :
      Vector.determinant axis transversal
        (form.cliffordCross transversal axis) = 0 := by
    calc
      Vector.determinant axis transversal
          (form.cliffordCross transversal axis) =
          -((-1 : K) * Vector.determinant axis transversal
            (form.cliffordCross transversal axis)) := by ring1
      _ = -0 := by rw [← triple]
      _ = 0 := by ring1
  unfold handednessDet
  rw [(parabolicValue oneNonzero axis null).rowMul_actionMatrix,
    parabolic_action]
  unfold TernaryForm.Perpendicular at perpendicular
  rw [perpendicular, mul_zero, Vector.zero_scale,
    Vector.add_zero, Vector.determinant_add_third,
    Vector.determinant_repeat_second,
    Vector.determinant_scale_third, determinantZero]
  ring1

/-- Cached finite invariants of one nonzero null-axis parabolic. -/
structure ParabolicCertificate (oneNonzero : (1 : K) ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) where
  axis : Vector K
  axisNull : (TernaryForm.minkowski oneNonzero).IsNull axis
  axisNonzero : axis ≠ Vector.zero
  rotation : (TernaryForm.minkowski oneNonzero).SpecialOrthogonal
  rotation_spec :
    rotation = (parabolicValue oneNonzero axis axisNull).actionRotation
  fixedAxis : rotation.act axis = axis
  nonidentityMatrix : rotation.matrix ≠ Matrix3.identity
  characteristicUnipotent : ∀ X : K,
    Matrix3.characteristicValue rotation.matrix X = (X - 1) ^ 3
  handednessZero : ∀ transversal : Vector K,
    (TernaryForm.minkowski oneNonzero).Perpendicular transversal axis →
      handednessDet axis transversal rotation.matrix = 0

def parabolicCertificate [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (axis : Vector K)
    (null : (TernaryForm.minkowski oneNonzero).IsNull axis)
    (nonzero : axis ≠ Vector.zero) :
    ParabolicCertificate oneNonzero twoNonzero where
  axis := axis
  axisNull := null
  axisNonzero := nonzero
  rotation := (parabolicValue oneNonzero axis null).actionRotation
  rotation_spec := rfl
  fixedAxis := by
    rw [TernaryForm.NonNullEvenClifford.actionRotation_act]
    exact parabolic_fixedAxis oneNonzero axis null
  nonidentityMatrix :=
    parabolic_nonidentity oneNonzero twoNonzero axis null nonzero
  characteristicUnipotent :=
    parabolic_characteristic oneNonzero axis null
  handednessZero := fun transversal perpendicular =>
    parabolic_handedness_zero oneNonzero axis transversal null perpendicular

/-- Norm-one parabolic representative at a scalar parameter on a fixed null
axis.  Parameter zero is the Clifford identity. -/
def parabolicAt (oneNonzero : (1 : K) ≠ 0) (axis : Vector K)
    (null : (TernaryForm.minkowski oneNonzero).IsNull axis)
    (parameter : K) :
    (TernaryForm.minkowski oneNonzero).NonNullEvenClifford :=
  parabolicValue oneNonzero (Vector.scale parameter axis)
    ((TernaryForm.minkowski oneNonzero).isNull_scale parameter axis null)

/-- Multiplication on one null line is addition of its scalar parameters. -/
theorem parabolicAt_mul (oneNonzero : (1 : K) ≠ 0)
    (axis : Vector K)
    (null : (TernaryForm.minkowski oneNonzero).IsNull axis)
    (left right : K) :
    TernaryForm.NonNullEvenClifford.mul
        (parabolicAt oneNonzero axis null left)
        (parabolicAt oneNonzero axis null right) =
      parabolicAt oneNonzero axis null (left + right) := by
  let form := TernaryForm.minkowski oneNonzero
  have nullBilinear : form.bilinear axis axis = 0 := by
    exact null
  have raw :
      TernaryForm.EvenClifford.mul
          (parabolicRaw oneNonzero (Vector.scale left axis))
          (parabolicRaw oneNonzero (Vector.scale right axis)) =
        parabolicRaw oneNonzero (Vector.scale (left + right) axis) := by
    apply TernaryForm.EvenClifford.ext
    · unfold TernaryForm.EvenClifford.mul
        TernaryForm.EvenClifford.productScalar parabolicRaw
      rw [form.bilinear_scale_left, form.bilinear_scale_right]
      change 1 * 1 - form.determinant *
        (left * (right * form.bilinear axis axis)) = 1
      rw [nullBilinear]
      ring1
    · unfold TernaryForm.EvenClifford.mul
        TernaryForm.EvenClifford.productVector parabolicRaw
      rw [form.cliffordCross_scale_left,
        form.cliffordCross_scale_right,
        form.cliffordCross_self, Vector.scale_zero]
      ext <;> unfold Vector.sub Vector.add Vector.scale Vector.zero <;> ring1
  apply TernaryForm.NonNullEvenClifford.ext
  · exact congrArg TernaryForm.EvenClifford.scalar raw
  · exact congrArg TernaryForm.EvenClifford.vector raw

@[simp] theorem parabolicAt_zero (oneNonzero : (1 : K) ≠ 0)
    (axis : Vector K)
    (null : (TernaryForm.minkowski oneNonzero).IsNull axis) :
    parabolicAt oneNonzero axis null 0 =
      TernaryForm.NonNullEvenClifford.identity
        (TernaryForm.minkowski oneNonzero) := by
  apply TernaryForm.NonNullEvenClifford.ext
  · rfl
  · exact Vector.zero_scale axis

theorem parabolicAt_conjugate (oneNonzero : (1 : K) ≠ 0)
    (axis : Vector K)
    (null : (TernaryForm.minkowski oneNonzero).IsNull axis)
    (parameter : K) :
    (parabolicAt oneNonzero axis null parameter).conjugate =
      parabolicAt oneNonzero axis null (-parameter) := by
  apply TernaryForm.NonNullEvenClifford.ext
  · rfl
  · ext <;> unfold parabolicAt parabolicValue parabolicRaw
      TernaryForm.NonNullEvenClifford.conjugate
      TernaryForm.EvenClifford.conjugate Vector.neg Vector.scale <;> ring1

/-- The special-orthogonal member at one scalar parameter. -/
def parabolicRotationAt (oneNonzero : (1 : K) ≠ 0)
    (axis : Vector K)
    (null : (TernaryForm.minkowski oneNonzero).IsNull axis)
    (parameter : K) :
    (TernaryForm.minkowski oneNonzero).SpecialOrthogonal :=
  (parabolicAt oneNonzero axis null parameter).actionRotation

@[simp] theorem parabolicRotationAt_zero (oneNonzero : (1 : K) ≠ 0)
    (axis : Vector K)
    (null : (TernaryForm.minkowski oneNonzero).IsNull axis) :
    parabolicRotationAt oneNonzero axis null 0 =
      TernaryForm.SpecialOrthogonal.identity
        (TernaryForm.minkowski oneNonzero) := by
  unfold parabolicRotationAt
  rw [parabolicAt_zero,
    TernaryForm.NonNullEvenClifford.actionRotation_identity]

theorem parabolicRotationAt_add (oneNonzero : (1 : K) ≠ 0)
    (axis : Vector K)
    (null : (TernaryForm.minkowski oneNonzero).IsNull axis)
    (left right : K) :
    parabolicRotationAt oneNonzero axis null (left + right) =
      TernaryForm.SpecialOrthogonal.mul
        (parabolicRotationAt oneNonzero axis null left)
        (parabolicRotationAt oneNonzero axis null right) := by
  unfold parabolicRotationAt
  calc
    (parabolicAt oneNonzero axis null (left + right)).actionRotation =
        (TernaryForm.NonNullEvenClifford.mul
          (parabolicAt oneNonzero axis null left)
          (parabolicAt oneNonzero axis null right)).actionRotation :=
      congrArg TernaryForm.NonNullEvenClifford.actionRotation
        (parabolicAt_mul oneNonzero axis null left right).symm
    _ = _ := TernaryForm.NonNullEvenClifford.actionRotation_mul _ _

theorem parabolicRotationAt_neg (oneNonzero : (1 : K) ≠ 0)
    (axis : Vector K)
    (null : (TernaryForm.minkowski oneNonzero).IsNull axis)
    (parameter : K) :
    parabolicRotationAt oneNonzero axis null (-parameter) =
      TernaryForm.SpecialOrthogonal.inverse
        (parabolicRotationAt oneNonzero axis null parameter) := by
  unfold parabolicRotationAt
  calc
    (parabolicAt oneNonzero axis null (-parameter)).actionRotation =
        (parabolicAt oneNonzero axis null parameter).conjugate.actionRotation :=
      congrArg TernaryForm.NonNullEvenClifford.actionRotation
        (parabolicAt_conjugate oneNonzero axis null parameter).symm
    _ = _ :=
      TernaryForm.NonNullEvenClifford.actionRotation_conjugate _

theorem parabolicRotationAt_fixedAxis (oneNonzero : (1 : K) ≠ 0)
    (axis : Vector K)
    (null : (TernaryForm.minkowski oneNonzero).IsNull axis)
    (parameter : K) :
    (parabolicRotationAt oneNonzero axis null parameter).act axis = axis := by
  unfold parabolicRotationAt
  rw [TernaryForm.NonNullEvenClifford.actionRotation_act]
  unfold parabolicAt
  rw [parabolic_action]
  have nullBilinear :
      (TernaryForm.minkowski oneNonzero).bilinear axis axis = 0 := null
  rw [(TernaryForm.minkowski oneNonzero).bilinear_scale_right,
    nullBilinear, mul_zero,
    (TernaryForm.minkowski oneNonzero).cliffordCross_scale_right,
    (TernaryForm.minkowski oneNonzero).cliffordCross_self]
  ext <;> unfold Vector.add Vector.scale Vector.zero <;> ring1

theorem parabolicRotationAt_characteristic (oneNonzero : (1 : K) ≠ 0)
    (axis : Vector K)
    (null : (TernaryForm.minkowski oneNonzero).IsNull axis)
    (parameter X : K) :
    Matrix3.characteristicValue
        (parabolicRotationAt oneNonzero axis null parameter).matrix X =
      (X - 1) ^ 3 :=
  parabolic_characteristic oneNonzero (Vector.scale parameter axis)
    ((TernaryForm.minkowski oneNonzero).isNull_scale parameter axis null) X

theorem parabolicRotationAt_handedness_zero [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0)
    (axis transversal : Vector K)
    (null : (TernaryForm.minkowski oneNonzero).IsNull axis)
    (perpendicular :
      (TernaryForm.minkowski oneNonzero).Perpendicular transversal axis)
    (parameter : K) :
    handednessDet axis transversal
      (parabolicRotationAt oneNonzero axis null parameter).matrix = 0 := by
  by_cases parameterZero : parameter = 0
  · subst parameter
    rw [parabolicRotationAt_zero]
    unfold handednessDet TernaryForm.SpecialOrthogonal.identity
      TernaryForm.Isometry.identity
    rw [Matrix3.rowMul_identity, Vector.determinant_repeat_second]
  · have scaledNull :=
      (TernaryForm.minkowski oneNonzero).isNull_scale parameter axis null
    have scaledPerpendicular :=
      (TernaryForm.minkowski oneNonzero).perpendicular_scale_right
        parameter transversal axis perpendicular
    have scaledZero := parabolic_handedness_zero oneNonzero
      (Vector.scale parameter axis) transversal scaledNull scaledPerpendicular
    have factor :
        handednessDet (Vector.scale parameter axis) transversal
            (parabolicRotationAt oneNonzero axis null parameter).matrix =
          parameter * handednessDet axis transversal
            (parabolicRotationAt oneNonzero axis null parameter).matrix := by
      unfold handednessDet Vector.determinant Vector.scale
      ring1
    apply eq_zero_of_nonzero_mul_eq_zero parameterZero
    rw [← factor]
    exact scaledZero

theorem parabolicRotationAt_nonidentity [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (axis : Vector K)
    (null : (TernaryForm.minkowski oneNonzero).IsNull axis)
    (axisNonzero : axis ≠ Vector.zero)
    (parameter : K) (parameterNonzero : parameter ≠ 0) :
    (parabolicRotationAt oneNonzero axis null parameter).matrix ≠
      Matrix3.identity := by
  apply parabolic_nonidentity oneNonzero twoNonzero
    (Vector.scale parameter axis)
    ((TernaryForm.minkowski oneNonzero).isNull_scale parameter axis null)
  intro scaledZero
  apply axisNonzero
  apply Vector.ext
  · have coordinate := congrArg Vector.t scaledZero
    exact eq_zero_of_nonzero_mul_eq_zero parameterNonzero coordinate
  · have coordinate := congrArg Vector.r scaledZero
    exact eq_zero_of_nonzero_mul_eq_zero parameterNonzero coordinate
  · have coordinate := congrArg Vector.s scaledZero
    exact eq_zero_of_nonzero_mul_eq_zero parameterNonzero coordinate

theorem parabolicRotationAt_injective [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (axis : Vector K)
    (null : (TernaryForm.minkowski oneNonzero).IsNull axis)
    (axisNonzero : axis ≠ Vector.zero) :
    Function.Injective (parabolicRotationAt oneNonzero axis null) := by
  intro left right rotationsEqual
  by_cases parametersEqual : left = right
  · exact parametersEqual
  · have differenceNonzero : left + (-right) ≠ 0 := by
      intro differenceZero
      apply parametersEqual
      calc
        left = (left + (-right)) + right := by ring1
        _ = 0 + right := by rw [differenceZero]
        _ = right := by ring1
    have differenceIdentity :
        parabolicRotationAt oneNonzero axis null (left + (-right)) =
          TernaryForm.SpecialOrthogonal.identity
            (TernaryForm.minkowski oneNonzero) := by
      calc
        parabolicRotationAt oneNonzero axis null (left + (-right)) =
            TernaryForm.SpecialOrthogonal.mul
              (parabolicRotationAt oneNonzero axis null left)
              (parabolicRotationAt oneNonzero axis null (-right)) :=
          parabolicRotationAt_add oneNonzero axis null left (-right)
        _ = TernaryForm.SpecialOrthogonal.mul
              (parabolicRotationAt oneNonzero axis null right)
              (TernaryForm.SpecialOrthogonal.inverse
                (parabolicRotationAt oneNonzero axis null right)) := by
          rw [rotationsEqual,
            parabolicRotationAt_neg oneNonzero axis null right]
        _ = TernaryForm.SpecialOrthogonal.identity
              (TernaryForm.minkowski oneNonzero) :=
          TernaryForm.SpecialOrthogonal.mul_inverse _
    have differenceMatrixIdentity := congrArg
      (fun rotation :
        (TernaryForm.minkowski oneNonzero).SpecialOrthogonal =>
          rotation.matrix)
      differenceIdentity
    exact False.elim
      ((parabolicRotationAt_nonidentity oneNonzero twoNonzero axis null
        axisNonzero (left + (-right)) differenceNonzero)
        differenceMatrixIdentity)

/-- An explicit additive one-parameter subgroup on a fixed nonzero null axis. -/
structure NullAxisParabolicFamily [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0) where
  axis : Vector K
  axisNull : (TernaryForm.minkowski oneNonzero).IsNull axis
  axisNonzero : axis ≠ Vector.zero
  rotation : K → (TernaryForm.minkowski oneNonzero).SpecialOrthogonal
  rotation_spec : ∀ parameter : K,
    rotation parameter = parabolicRotationAt oneNonzero axis axisNull parameter
  rotation_zero : rotation 0 =
    TernaryForm.SpecialOrthogonal.identity
      (TernaryForm.minkowski oneNonzero)
  rotation_add : ∀ left right : K,
    rotation (left + right) =
      TernaryForm.SpecialOrthogonal.mul (rotation left) (rotation right)
  rotation_neg : ∀ parameter : K,
    rotation (-parameter) =
      TernaryForm.SpecialOrthogonal.inverse (rotation parameter)
  fixedAxis : ∀ parameter : K, (rotation parameter).act axis = axis
  characteristicUnipotent : ∀ parameter X : K,
    Matrix3.characteristicValue (rotation parameter).matrix X = (X - 1) ^ 3
  handednessZero : ∀ (parameter : K) (transversal : Vector K),
    (TernaryForm.minkowski oneNonzero).Perpendicular transversal axis →
      handednessDet axis transversal (rotation parameter).matrix = 0
  nonidentity : ∀ parameter : K, parameter ≠ 0 →
    (rotation parameter).matrix ≠ Matrix3.identity
  injective : Function.Injective rotation

def nullAxisParabolicFamily [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (axis : Vector K)
    (null : (TernaryForm.minkowski oneNonzero).IsNull axis)
    (nonzero : axis ≠ Vector.zero) :
    NullAxisParabolicFamily oneNonzero twoNonzero where
  axis := axis
  axisNull := null
  axisNonzero := nonzero
  rotation := parabolicRotationAt oneNonzero axis null
  rotation_spec := fun _ => rfl
  rotation_zero := parabolicRotationAt_zero oneNonzero axis null
  rotation_add := parabolicRotationAt_add oneNonzero axis null
  rotation_neg := parabolicRotationAt_neg oneNonzero axis null
  fixedAxis := parabolicRotationAt_fixedAxis oneNonzero axis null
  characteristicUnipotent :=
    parabolicRotationAt_characteristic oneNonzero axis null
  handednessZero := fun parameter transversal perpendicular =>
    parabolicRotationAt_handedness_zero oneNonzero axis transversal null
      perpendicular parameter
  nonidentity :=
    parabolicRotationAt_nonidentity oneNonzero twoNonzero axis null nonzero
  injective :=
    parabolicRotationAt_injective oneNonzero twoNonzero axis null nonzero

/-- The Clifford action is the adjugate sandwich on trace-zero matrices. -/
theorem actionNumerator_compatibility (oneNonzero : (1 : K) ≠ 0)
    (value : (TernaryForm.minkowski oneNonzero).EvenClifford)
    (vector : Vector K) :
    vectorMatrix (value.actionNumerator vector) =
      Matrix2.mul
        (Matrix2.mul
          (Matrix2.adjugate (toMatrix oneNonzero value))
          (vectorMatrix vector))
        (toMatrix oneNonzero value) := by
  calc
    vectorMatrix (value.actionNumerator vector) =
        toMatrix oneNonzero
          (TernaryForm.EvenClifford.ofVector
            (TernaryForm.minkowski oneNonzero)
            (value.actionNumerator vector)) :=
      (toMatrix_ofVector oneNonzero (value.actionNumerator vector)).symm
    _ = toMatrix oneNonzero
        (TernaryForm.EvenClifford.mul
          (TernaryForm.EvenClifford.mul value.conjugate
            (TernaryForm.EvenClifford.ofVector
              (TernaryForm.minkowski oneNonzero) vector))
          value) := by
      rw [TernaryForm.EvenClifford.conjugate_mul_ofVector_mul]
    _ = Matrix2.mul
        (Matrix2.mul
          (toMatrix oneNonzero value.conjugate)
          (toMatrix oneNonzero
            (TernaryForm.EvenClifford.ofVector
              (TernaryForm.minkowski oneNonzero) vector)))
        (toMatrix oneNonzero value) := by
      rw [toMatrix_mul, toMatrix_mul]
    _ = Matrix2.mul
        (Matrix2.mul
          (Matrix2.adjugate (toMatrix oneNonzero value))
          (vectorMatrix vector))
        (toMatrix oneNonzero value) := by
      rw [toMatrix_conjugate, toMatrix_ofVector]

/-- The normalized special-orthogonal action is the determinant-normalized
two-by-two adjugate sandwich. -/
theorem action_compatibility (oneNonzero : (1 : K) ≠ 0)
    (value : (TernaryForm.minkowski oneNonzero).NonNullEvenClifford)
    (vector : Vector K) :
    vectorMatrix (value.action vector) =
      Matrix2.scale value.toEvenClifford.norm⁻¹
        (Matrix2.mul
          (Matrix2.mul
            (Matrix2.adjugate
              (toMatrix oneNonzero value.toEvenClifford))
            (vectorMatrix vector))
          (toMatrix oneNonzero value.toEvenClifford)) := by
  unfold TernaryForm.NonNullEvenClifford.action
  rw [vectorMatrix_scale,
    actionNumerator_compatibility]

/-- The full executable split-algebra equivalence, with its inverse and all
compatibility certificates cached for downstream use. -/
structure AlgebraEquivalence (oneNonzero : (1 : K) ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) where
  forward : (TernaryForm.minkowski oneNonzero).EvenClifford → Matrix2 K
  backward : Matrix2 K →
    (TernaryForm.minkowski oneNonzero).EvenClifford
  forward_backward : ∀ matrix : Matrix2 K,
    forward (backward matrix) = matrix
  backward_forward : ∀ value :
      (TernaryForm.minkowski oneNonzero).EvenClifford,
    backward (forward value) = value
  map_mul : ∀ left right :
      (TernaryForm.minkowski oneNonzero).EvenClifford,
    forward (TernaryForm.EvenClifford.mul left right) =
      Matrix2.mul (forward left) (forward right)
  map_determinant : ∀ value :
      (TernaryForm.minkowski oneNonzero).EvenClifford,
    Matrix2.determinant (forward value) = value.norm
  map_conjugate : ∀ value :
      (TernaryForm.minkowski oneNonzero).EvenClifford,
    forward value.conjugate = Matrix2.adjugate (forward value)
  normalizedAction : ∀
      (value : (TernaryForm.minkowski oneNonzero).NonNullEvenClifford)
      (vector : Vector K),
    vectorMatrix (value.action vector) =
      Matrix2.scale value.toEvenClifford.norm⁻¹
        (Matrix2.mul
          (Matrix2.mul
            (Matrix2.adjugate (forward value.toEvenClifford))
            (vectorMatrix vector))
          (forward value.toEvenClifford))

/-- Canonical finite-coordinate equivalence between the split even Clifford
algebra and displayed two-by-two matrices. -/
def algebraEquivalence (oneNonzero : (1 : K) ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    AlgebraEquivalence oneNonzero twoNonzero where
  forward := toMatrix oneNonzero
  backward := fromMatrix oneNonzero
  forward_backward := toMatrix_fromMatrix oneNonzero twoNonzero
  backward_forward := fromMatrix_toMatrix oneNonzero twoNonzero
  map_mul := toMatrix_mul oneNonzero
  map_determinant := determinant_toMatrix oneNonzero
  map_conjugate := toMatrix_conjugate oneNonzero
  normalizedAction := action_compatibility oneNonzero

/-- The completed finite split-form package: explicit matrix equivalence,
projective null-conic coverage, and certified parabolics on every nonzero null
axis. -/
structure FiniteSplitTheory [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0) where
  algebra : AlgebraEquivalence oneNonzero twoNonzero
  nullConic : NullConicParametrization oneNonzero twoNonzero
  parabolic : ∀ axis : Vector K,
    (null : (TernaryForm.minkowski oneNonzero).IsNull axis) →
      axis ≠ Vector.zero → ParabolicCertificate oneNonzero twoNonzero
  parabolicFamily : ∀ axis : Vector K,
    (null : (TernaryForm.minkowski oneNonzero).IsNull axis) →
      axis ≠ Vector.zero → NullAxisParabolicFamily oneNonzero twoNonzero

def finiteSplitTheory [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    FiniteSplitTheory oneNonzero twoNonzero where
  algebra := algebraEquivalence oneNonzero twoNonzero
  nullConic := nullConicParametrization oneNonzero twoNonzero
  parabolic := parabolicCertificate oneNonzero twoNonzero
  parabolicFamily := nullAxisParabolicFamily oneNonzero twoNonzero

end MinkowskiClifford

/-! ## Exact rational specialization -/

namespace RationalMinkowski

abbrev Scalar := RFAP.CanonicalFraction.Rational

theorem oneNonzero : (1 : Scalar) ≠ 0 := by decide

theorem twoNonzero : (2 : Scalar) ≠ 0 := by decide

/-- The rational Minkowski form used by the split-matrix specialization. -/
def form : TernaryForm Scalar := TernaryForm.minkowski oneNonzero

theorem quadrance (vector : Vector Scalar) :
    form.quadrance vector =
      vector.t ^ 2 + vector.r ^ 2 - vector.s ^ 2 := by
  exact TernaryForm.quadrance_minkowski oneNonzero vector

/-- A rational null axis for a nonidentity unipotent transformation. -/
def parabolicAxis : Vector Scalar := ⟨0, 1, -1⟩

theorem parabolicAxis_null : form.IsNull parabolicAxis := by
  unfold TernaryForm.IsNull
  rw [quadrance]
  unfold parabolicAxis
  ring1

theorem parabolicAxis_nonzero : parabolicAxis ≠ Vector.zero := by decide

/-- The norm-one split Clifford representative corresponding to the upper
unipotent matrix `[[1,2],[0,1]]`. -/
def parabolicValueRaw : form.EvenClifford :=
  ⟨1, parabolicAxis⟩

theorem parabolicValueRaw_norm : parabolicValueRaw.norm = 1 := by
  unfold parabolicValueRaw TernaryForm.EvenClifford.norm form
  rw [TernaryForm.minkowski_determinant,
    TernaryForm.quadrance_minkowski]
  unfold parabolicAxis
  ring1

def parabolicValue : form.NonNullEvenClifford where
  toEvenClifford := parabolicValueRaw
  normNonzero := by
    rw [parabolicValueRaw_norm]
    exact oneNonzero

theorem parabolicValue_matrix2 :
    MinkowskiClifford.toMatrix oneNonzero parabolicValueRaw =
      (⟨1, 2, 0, 1⟩ : Matrix2 Scalar) := by
  apply Matrix2.ext <;> decide

def parabolicDisplayed : Matrix3 Scalar :=
  ⟨1, 2, -2, -2, -1, 2, -2, -2, 3⟩

theorem parabolic_actionMatrix :
    parabolicValue.actionMatrix = parabolicDisplayed := by decide

theorem parabolic_fixedAxis :
    Matrix3.rowMul parabolicAxis parabolicValue.actionMatrix =
      parabolicAxis := by
  rw [parabolic_actionMatrix]
  apply Vector.ext <;> decide

theorem parabolic_nonidentity :
    parabolicValue.actionMatrix ≠ Matrix3.identity := by
  rw [parabolic_actionMatrix]
  decide

theorem parabolic_characteristic (X : Scalar) :
    Matrix3.characteristicValue parabolicValue.actionMatrix X =
      (X - 1) ^ 3 := by
  rw [parabolic_actionMatrix]
  unfold Matrix3.characteristicValue Matrix3.determinant Matrix3.sub
    Matrix3.scale Matrix3.identity parabolicDisplayed
  ring1

def parabolicTransversal : Vector Scalar := ⟨1, 0, 0⟩

theorem parabolicTransversal_perpendicular :
    form.Perpendicular parabolicTransversal parabolicAxis := by
  unfold TernaryForm.Perpendicular TernaryForm.bilinear form
    TernaryForm.minkowski TernaryForm.ofMatrix Matrix3.rowMul Vector.dot
    parabolicTransversal parabolicAxis
  ring1

/-- The paper's displayed frame determinant vanishes rationally for this
nonidentity parabolic transformation. -/
theorem parabolic_handedness_zero :
    handednessDet parabolicAxis parabolicTransversal
      parabolicValue.actionMatrix = 0 := by
  rw [parabolic_actionMatrix]
  unfold handednessDet parabolicAxis parabolicTransversal
    parabolicDisplayed Vector.determinant Matrix3.rowMul
  ring1

/-- A finite certificate of the rational parabolic and zero-handedness
phenomena requested in Problem 71. -/
structure ParabolicCertificate
    (rotation : form.SpecialOrthogonal) where
  axis : Vector Scalar
  transversal : Vector Scalar
  axisNull : form.IsNull axis
  axisNonzero : axis ≠ Vector.zero
  transversalPerpendicular : form.Perpendicular transversal axis
  axisFixed : Matrix3.rowMul axis rotation.matrix = axis
  nonidentityMatrix : rotation.matrix ≠ Matrix3.identity
  characteristicUnipotent : ∀ X : Scalar,
    Matrix3.characteristicValue rotation.matrix X = (X - 1) ^ 3
  handednessZero : handednessDet axis transversal rotation.matrix = 0

def parabolicCertificate : ParabolicCertificate parabolicValue.actionRotation where
  axis := parabolicAxis
  transversal := parabolicTransversal
  axisNull := parabolicAxis_null
  axisNonzero := parabolicAxis_nonzero
  transversalPerpendicular := parabolicTransversal_perpendicular
  axisFixed := parabolic_fixedAxis
  nonidentityMatrix := parabolic_nonidentity
  characteristicUnipotent := parabolic_characteristic
  handednessZero := parabolic_handedness_zero

end RationalMinkowski

end RationalRotations
