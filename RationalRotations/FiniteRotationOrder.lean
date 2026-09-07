import RationalRotations.FiniteRotationProfiles
import RationalRotations.PrescribedAxes

/-!
# Finite-order rational rotations

Finite order is supplied by an explicit positive exponent and a checked
finite matrix-power equation.  The trace calculation below is a direct
three-coordinate Cayley--Hamilton recurrence.  It forms no collection of all
torsion rotations and uses neither complex roots nor cyclotomic polynomials.
-/

namespace RationalRotations

namespace FiniteRotationOrder

abbrev Scalar := RFAP.ConstructiveFraction.Rational

/-- Fixed-coordinate matrix powers, kept separate from the proof-carrying
rotation wrapper so recurrence evaluation does not unfold certificates. -/
def matrixPow (matrix : Matrix3 Scalar) : Nat → Matrix3 Scalar
  | 0 => Matrix3.identity
  | exponent + 1 => Matrix3.mul (matrixPow matrix exponent) matrix

@[simp] theorem matrixPow_zero (matrix : Matrix3 Scalar) :
    matrixPow matrix 0 = Matrix3.identity := rfl

@[simp] theorem matrixPow_succ (matrix : Matrix3 Scalar) (exponent : Nat) :
    matrixPow matrix (exponent + 1) =
      Matrix3.mul (matrixPow matrix exponent) matrix := rfl

theorem matrixPow_add (matrix : Matrix3 Scalar) (left : Nat) :
    ∀ right : Nat,
      matrixPow matrix (left + right) =
        Matrix3.mul (matrixPow matrix left) (matrixPow matrix right)
  | 0 => by rw [Nat.add_zero, matrixPow_zero, Matrix3.mul_identity]
  | right + 1 => by
      rw [Nat.add_succ, matrixPow_succ, matrixPow_succ,
        matrixPow_add matrix left right, Matrix3.mul_assoc]

theorem matrixPow_one (matrix : Matrix3 Scalar) :
    matrixPow matrix 1 = matrix := by
  rw [show 1 = 0 + 1 by decide, matrixPow_succ, matrixPow_zero,
    Matrix3.identity_mul]

theorem matrixPow_two (matrix : Matrix3 Scalar) :
    matrixPow matrix 2 = Matrix3.mul matrix matrix := by
  rw [show 2 = 1 + 1 by decide, matrixPow_succ, matrixPow_one]

theorem matrixPow_three (matrix : Matrix3 Scalar) :
    matrixPow matrix 3 = Matrix3.mul (Matrix3.mul matrix matrix) matrix := by
  rw [show 3 = 2 + 1 by decide, matrixPow_succ, matrixPow_two]

/-- The identity in the stored rotation structure. -/
def identityRotation : Rotation Scalar where
  matrix := Matrix3.identity
  orthogonal := by
    unfold Matrix3.IsOrthogonal
    rw [Matrix3.transpose_identity, Matrix3.identity_mul]
  determinantOne := Matrix3.determinant_identity

/-- Finite recursive powers of one displayed rational rotation. -/
def rotationPow (rotation : Rotation Scalar) : Nat → Rotation Scalar
  | 0 => identityRotation
  | exponent + 1 => rotationProduct (rotationPow rotation exponent) rotation

@[simp] theorem rotationPow_zero (rotation : Rotation Scalar) :
    (rotationPow rotation 0).matrix = Matrix3.identity := rfl

@[simp] theorem rotationPow_succ (rotation : Rotation Scalar)
    (exponent : Nat) :
    (rotationPow rotation (exponent + 1)).matrix =
      Matrix3.mul (rotationPow rotation exponent).matrix rotation.matrix :=
  rfl

theorem rotationPow_add_matrix (rotation : Rotation Scalar) (left : Nat) :
    ∀ right : Nat,
      (rotationPow rotation (left + right)).matrix =
        Matrix3.mul (rotationPow rotation left).matrix
          (rotationPow rotation right).matrix
  | 0 => by
      simp only [Nat.add_zero, rotationPow_zero, Matrix3.mul_identity]
  | right + 1 => by
      rw [Nat.add_succ, rotationPow_succ, rotationPow_succ,
        rotationPow_add_matrix rotation left right, Matrix3.mul_assoc]

theorem rotationPow_matrix (rotation : Rotation Scalar) :
    ∀ exponent : Nat,
      (rotationPow rotation exponent).matrix =
        matrixPow rotation.matrix exponent
  | 0 => rfl
  | exponent + 1 => by
      rw [rotationPow_succ, matrixPow_succ, rotationPow_matrix]

/-- The rational trace parameter of the nontrivial quadratic factor of the
rotation characteristic polynomial. -/
def traceParameter (rotation : Rotation Scalar) : Scalar :=
  Matrix3.trace rotation.matrix - 1

/-- The finite Lucas trace recurrence for the quadratic factor
`X^2 - trace*X + 1`. -/
def traceLucas : Nat → Scalar → Scalar
  | 0, _trace => 2
  | 1, trace => trace
  | index + 2, trace =>
      trace * traceLucas (index + 1) trace - traceLucas index trace

@[simp] theorem traceLucas_zero (trace : Scalar) :
    traceLucas 0 trace = 2 := rfl

@[simp] theorem traceLucas_one (trace : Scalar) :
    traceLucas 1 trace = trace := rfl

theorem traceLucas_succ_succ (index : Nat) (trace : Scalar) :
    traceLucas (index + 2) trace =
      trace * traceLucas (index + 1) trace - traceLucas index trace :=
  rfl

theorem traceLucas_two (trace : Scalar) :
    traceLucas 2 trace = trace ^ 2 - 2 := by
  rw [show 2 = 0 + 2 by decide, traceLucas_succ_succ]
  simp only [traceLucas_zero]
  change trace * trace - 2 = trace ^ 2 - 2
  ring1

theorem traceLucas_third (index : Nat) (trace : Scalar) :
    traceLucas (index + 3) trace =
      (trace + 1) * traceLucas (index + 2) trace -
        (trace + 1) * traceLucas (index + 1) trace +
          traceLucas index trace := by
  rw [show index + 3 = (index + 1) + 2 by omega,
    traceLucas_succ_succ, traceLucas_succ_succ]
  ring1

private theorem trace_sub (left right : Matrix3 Scalar) :
    Matrix3.trace (Matrix3.sub left right) =
      Matrix3.trace left - Matrix3.trace right := by
  unfold Matrix3.trace Matrix3.sub
  ring1

/-- Cayley--Hamilton for a rotation, written as a displayed cubic matrix
identity and derived from the stored transpose inverse. -/
theorem rotation_cube (rotation : Rotation Scalar) :
    matrixPow rotation.matrix 3 =
      Matrix3.add
        (Matrix3.sub
          (Matrix3.scale (Matrix3.trace rotation.matrix)
            (matrixPow rotation.matrix 2))
          (Matrix3.scale (Matrix3.trace rotation.matrix) rotation.matrix))
        Matrix3.identity := by
  have multiplied := congrArg
    (fun matrix => Matrix3.mul matrix rotation.matrix)
    (rotation_square_sub_transpose rotation)
  have differenceIdentity :
      Matrix3.sub (matrixPow rotation.matrix 3) Matrix3.identity =
        Matrix3.scale (Matrix3.trace rotation.matrix)
          (Matrix3.sub (matrixPow rotation.matrix 2) rotation.matrix) := by
    calc
      Matrix3.sub (matrixPow rotation.matrix 3) Matrix3.identity =
          Matrix3.mul
            (Matrix3.sub
              (Matrix3.mul rotation.matrix rotation.matrix)
              (Matrix3.transpose rotation.matrix)) rotation.matrix := by
        rw [Matrix3.mul_sub_left, transpose_mul_rotation]
        rw [matrixPow_three]
      _ = Matrix3.mul
          (Matrix3.scale (Matrix3.trace rotation.matrix)
            (Matrix3.sub rotation.matrix Matrix3.identity))
          rotation.matrix := multiplied
      _ = Matrix3.scale (Matrix3.trace rotation.matrix)
          (Matrix3.sub (matrixPow rotation.matrix 2) rotation.matrix) := by
        rw [Matrix3.mul_scale_left, Matrix3.mul_sub_left,
          Matrix3.identity_mul]
        rw [matrixPow_two]
  calc
    matrixPow rotation.matrix 3 =
        Matrix3.add
          (Matrix3.sub (matrixPow rotation.matrix 3) Matrix3.identity)
          Matrix3.identity := by
      apply Matrix3.ext <;>
        unfold Matrix3.add Matrix3.sub Matrix3.identity <;> ring1
    _ = Matrix3.add
        (Matrix3.scale (Matrix3.trace rotation.matrix)
          (Matrix3.sub (matrixPow rotation.matrix 2) rotation.matrix))
        Matrix3.identity := by rw [differenceIdentity]
    _ = Matrix3.add
        (Matrix3.sub
          (Matrix3.scale (Matrix3.trace rotation.matrix)
            (matrixPow rotation.matrix 2))
          (Matrix3.scale (Matrix3.trace rotation.matrix) rotation.matrix))
        Matrix3.identity := by
      apply Matrix3.ext <;>
        unfold Matrix3.add Matrix3.sub Matrix3.scale <;> ring1

theorem rotationPow_third_recurrence (rotation : Rotation Scalar)
    (index : Nat) :
    matrixPow rotation.matrix (index + 3) =
      Matrix3.add
        (Matrix3.sub
          (Matrix3.scale (Matrix3.trace rotation.matrix)
            (matrixPow rotation.matrix (index + 2)))
          (Matrix3.scale (Matrix3.trace rotation.matrix)
            (matrixPow rotation.matrix (index + 1))))
        (matrixPow rotation.matrix index) := by
  calc
    matrixPow rotation.matrix (index + 3) =
        Matrix3.mul (matrixPow rotation.matrix index)
          (matrixPow rotation.matrix 3) := by
      exact matrixPow_add rotation.matrix index 3
    _ = Matrix3.mul (matrixPow rotation.matrix index)
        (Matrix3.add
          (Matrix3.sub
            (Matrix3.scale (Matrix3.trace rotation.matrix)
              (matrixPow rotation.matrix 2))
            (Matrix3.scale (Matrix3.trace rotation.matrix) rotation.matrix))
          Matrix3.identity) := by rw [rotation_cube]
    _ = Matrix3.add
        (Matrix3.sub
          (Matrix3.scale (Matrix3.trace rotation.matrix)
            (matrixPow rotation.matrix (index + 2)))
          (Matrix3.scale (Matrix3.trace rotation.matrix)
            (matrixPow rotation.matrix (index + 1))))
        (matrixPow rotation.matrix index) := by
      rw [Matrix3.mul_add_right, Matrix3.mul_sub_right,
        Matrix3.mul_scale_right, Matrix3.mul_scale_right,
        Matrix3.mul_identity,
        ← matrixPow_add rotation.matrix index 2,
        ← matrixPow_succ rotation.matrix index]

theorem trace_rotationPow_recurrence (rotation : Rotation Scalar)
    (index : Nat) :
    Matrix3.trace (matrixPow rotation.matrix (index + 3)) =
      Matrix3.trace rotation.matrix *
          Matrix3.trace (matrixPow rotation.matrix (index + 2)) -
        Matrix3.trace rotation.matrix *
          Matrix3.trace (matrixPow rotation.matrix (index + 1)) +
        Matrix3.trace (matrixPow rotation.matrix index) := by
  rw [rotationPow_third_recurrence, Matrix3.trace_add, trace_sub,
    Matrix3.trace_scale, Matrix3.trace_scale]

/-- The trace of every supplied finite power is `1` plus the finite Lucas
recurrence of the quadratic trace parameter. -/
theorem trace_rotationPow (rotation : Rotation Scalar) :
    ∀ exponent : Nat,
      Matrix3.trace (matrixPow rotation.matrix exponent) =
        1 + traceLucas exponent (traceParameter rotation) := by
  intro exponent
  induction exponent using Nat.strong_induction_on with
  | h exponent inductionHypothesis =>
      rcases exponent with _ | _ | index
      · simp only [matrixPow_zero, Matrix3.trace_identity,
          traceLucas_zero]
        ring1
      · simp only [matrixPow_succ, matrixPow_zero,
          Matrix3.identity_mul, traceParameter]
        change Matrix3.trace rotation.matrix =
          1 + (Matrix3.trace rotation.matrix - 1)
        ring1
      · rcases index with _ | index
        · rw [matrixPow_succ, matrixPow_succ, matrixPow_zero,
            Matrix3.identity_mul, Matrix3.trace_square,
            principalTrace_rotation]
          change Matrix3.trace rotation.matrix ^ 2 -
              2 * Matrix3.trace rotation.matrix =
            1 + traceLucas 2 (traceParameter rotation)
          rw [traceLucas_two]
          unfold traceParameter
          ring1
        · have atIndex := inductionHypothesis index (by omega)
          have atFirst := inductionHypothesis (index + 1) (by omega)
          have atSecond := inductionHypothesis (index + 2) (by omega)
          rw [trace_rotationPow_recurrence rotation index,
            atIndex, atFirst, atSecond,
            traceLucas_third index (traceParameter rotation)]
          unfold traceParameter
          ring1

/-- A supplied exact-order certificate retains the finite power table below
the positive exponent as executable data. -/
structure ExactFiniteOrderCertificate (rotation : Rotation Scalar)
    (order : Nat) where
  orderPositive : 0 < order
  power : Rotation Scalar
  power_eq : power = rotationPow rotation order
  power_identity : power.matrix = Matrix3.identity
  smallerPowers : List (Rotation Scalar)
  smallerPowers_eq :
    smallerPowers = (List.range order).map (rotationPow rotation)
  smaller_nonidentity : ∀ exponent, 0 < exponent → exponent < order →
    (rotationPow rotation exponent).matrix ≠ Matrix3.identity

theorem ExactFiniteOrderCertificate.power_matrix_identity
    {rotation : Rotation Scalar} {order : Nat}
    (certificate : ExactFiniteOrderCertificate rotation order) :
    (rotationPow rotation order).matrix = Matrix3.identity := by
  rw [← certificate.power_eq]
  exact certificate.power_identity

/-- A supplied identity power forces the finite quadratic trace recurrence
to return the trace `2` of the two non-axis coordinates. -/
theorem ExactFiniteOrderCertificate.traceLucas_eq_two
    {rotation : Rotation Scalar} {order : Nat}
    (certificate : ExactFiniteOrderCertificate rotation order) :
    traceLucas order (traceParameter rotation) = 2 := by
  have traced := congrArg Matrix3.trace certificate.power_matrix_identity
  rw [rotationPow_matrix, trace_rotationPow,
    Matrix3.trace_identity] at traced
  exact add_left_cancel (by
    calc
      1 + traceLucas order (traceParameter rotation) = 3 := traced
      _ = 1 + 2 := by ring1)

/-! ## Direct finite denominator clearance -/

/-- Integer homogeneous form of `traceLucas`.  Its two cached inputs are the
numerator and denominator of one displayed canonical rational; no polynomial
root collection is formed. -/
def homogeneousTraceLucas (numerator : Int) (denominator : Nat) : Nat → Int
  | 0 => 2
  | 1 => numerator
  | index + 2 =>
      numerator * homogeneousTraceLucas numerator denominator (index + 1) -
        (denominator : Int) ^ 2 *
          homogeneousTraceLucas numerator denominator index

@[simp] theorem homogeneousTraceLucas_zero (numerator : Int)
    (denominator : Nat) :
    homogeneousTraceLucas numerator denominator 0 = 2 := rfl

@[simp] theorem homogeneousTraceLucas_one (numerator : Int)
    (denominator : Nat) :
    homogeneousTraceLucas numerator denominator 1 = numerator := rfl

theorem homogeneousTraceLucas_succ_succ (numerator : Int)
    (denominator : Nat) (index : Nat) :
    homogeneousTraceLucas numerator denominator (index + 2) =
      numerator * homogeneousTraceLucas numerator denominator (index + 1) -
        (denominator : Int) ^ 2 *
          homogeneousTraceLucas numerator denominator index := rfl

/-- Clearing the one canonical denominator commutes with the finite trace
recurrence. -/
theorem homogeneousTraceLucas_cast (trace : Scalar)
    (numerator : Int) (denominator : Nat)
    (cleared : trace * (denominator : Scalar) = (numerator : Scalar)) :
    ∀ exponent : Nat,
      (homogeneousTraceLucas numerator denominator exponent : Scalar) =
        (denominator : Scalar) ^ exponent * traceLucas exponent trace := by
  intro exponent
  induction exponent using Nat.strong_induction_on with
  | h exponent inductionHypothesis =>
      rcases exponent with _ | _ | index
      · simp only [homogeneousTraceLucas_zero, traceLucas_zero, pow_zero,
          one_mul, Int.cast_ofNat]
      · rw [show 0 + 1 = 1 by decide, homogeneousTraceLucas_one,
          traceLucas_one, pow_one]
        calc
          (numerator : Scalar) = trace * (denominator : Scalar) :=
            cleared.symm
          _ = (denominator : Scalar) * trace := by ring1
      · have previous := inductionHypothesis index (by omega)
        have next := inductionHypothesis (index + 1) (by omega)
        rw [homogeneousTraceLucas_succ_succ, traceLucas_succ_succ,
          Int.cast_sub, QuotientFreeRing.intCast_mul,
          QuotientFreeRing.intCast_mul, QuotientFreeRing.intCast_pow,
          Int.cast_natCast, previous, next]
        rw [show index + 2 = (index + 1) + 1 by omega,
          pow_succ, pow_succ]
        rw [← cleared]
        ring1

/-- Modulo the displayed denominator, every positive homogeneous Lucas value
is the corresponding numerator power.  This is a finite induction on the
supplied exponent. -/
theorem denominator_dvd_homogeneousTraceLucas_sub_pow
    (numerator : Int) (denominator : Nat) :
    ∀ exponent : Nat, 0 < exponent →
      (denominator : Int) ∣
        homogeneousTraceLucas numerator denominator exponent -
          numerator ^ exponent := by
  intro exponent positive
  induction exponent using Nat.strong_induction_on with
  | h exponent inductionHypothesis =>
      rcases exponent with _ | _ | index
      · omega
      · refine ⟨0, ?_⟩
        rw [show 0 + 1 = 1 by decide, homogeneousTraceLucas_one, pow_one]
        ring1
      · rcases inductionHypothesis (index + 1) (by omega) (by omega) with
          ⟨factor, factorEquation⟩
        have nextEquation :
            homogeneousTraceLucas numerator denominator (index + 1) =
              numerator ^ (index + 1) + (denominator : Int) * factor := by
          calc
            homogeneousTraceLucas numerator denominator (index + 1) =
                (homogeneousTraceLucas numerator denominator (index + 1) -
                    numerator ^ (index + 1)) +
                  numerator ^ (index + 1) := by ring1
            _ = (denominator : Int) * factor +
                numerator ^ (index + 1) := by rw [factorEquation]
            _ = numerator ^ (index + 1) +
                (denominator : Int) * factor := by ring1
        refine ⟨numerator * factor -
          (denominator : Int) *
            homogeneousTraceLucas numerator denominator index, ?_⟩
        rw [homogeneousTraceLucas_succ_succ, nextEquation]
        rw [show index + 2 = (index + 1) + 1 by omega, pow_succ]
        ring1

private theorem natAbs_dvd_natAbs_of_dvd {left right : Int}
    (divides : left ∣ right) : left.natAbs ∣ right.natAbs := by
  rcases divides with ⟨factor, rfl⟩
  refine ⟨factor.natAbs, ?_⟩
  exact Int.natAbs_mul left factor

/-- The rational trace parameter of a supplied finite-order rotation is an
integer.  The proof uses only the supplied exponent, the finite recurrence,
and the Bézout certificate already stored in the canonical rational. -/
theorem ExactFiniteOrderCertificate.traceParameter_isInteger
    {rotation : Rotation Scalar} {order : Nat}
    (certificate : ExactFiniteOrderCertificate rotation order) :
    ∃ numerator : Int, traceParameter rotation = (numerator : Scalar) := by
  let trace := traceParameter rotation
  let numerator := (RFAP.ConstructiveFraction.representative trace).num
  let denominator := (RFAP.ConstructiveFraction.representative trace).den
  have cleared := RFAP.ConstructiveFraction.representative_mul_den trace
  change trace * (denominator : Scalar) = (numerator : Scalar) at cleared
  have homogeneousCast := homogeneousTraceLucas_cast trace numerator
    denominator cleared order
  have recurrenceRoot : traceLucas order trace = 2 :=
    certificate.traceLucas_eq_two
  rw [recurrenceRoot] at homogeneousCast
  have homogeneousEquation :
      homogeneousTraceLucas numerator denominator order =
        2 * (denominator : Int) ^ order := by
    apply RFAP.ConstructiveFraction.intCast_injective_direct
    rw [QuotientFreeRing.intCast_mul, QuotientFreeRing.intCast_pow,
      Int.cast_natCast]
    calc
      (homogeneousTraceLucas numerator denominator order : Scalar) =
          (denominator : Scalar) ^ order * 2 := homogeneousCast
      _ = 2 * (denominator : Scalar) ^ order := by ring1
  have denominatorDividesHomogeneous :
      (denominator : Int) ∣
        homogeneousTraceLucas numerator denominator order := by
    rcases order with _ | previous
    · exact (Nat.not_lt_zero 0 certificate.orderPositive).elim
    · refine ⟨2 * (denominator : Int) ^ previous, ?_⟩
      rw [homogeneousEquation, pow_succ]
      ring1
  have congruence := denominator_dvd_homogeneousTraceLucas_sub_pow
    numerator denominator order certificate.orderPositive
  have denominatorDividesNumeratorPowerInteger :
      (denominator : Int) ∣ numerator ^ order := by
    have difference := Int.dvd_sub denominatorDividesHomogeneous congruence
    have differenceValue :
        homogeneousTraceLucas numerator denominator order -
            (homogeneousTraceLucas numerator denominator order -
              numerator ^ order) = numerator ^ order := by ring1
    rw [differenceValue] at difference
    exact difference
  have denominatorDividesNumeratorPower :
      denominator ∣ numerator.natAbs ^ order := by
    have absolute := natAbs_dvd_natAbs_of_dvd
      denominatorDividesNumeratorPowerInteger
    simpa only [Int.natAbs_natCast, Int.natAbs_pow] using absolute
  have denominatorDividesOne : denominator ∣ 1 := by
    rcases (RFAP.ConstructiveFraction.representative trace).reduced with
      ⟨coprime⟩
    apply coprime.symm.dvd_of_dvd_mul_right_pow order
    simpa only [Nat.one_mul] using denominatorDividesNumeratorPower
  have denominatorOne : denominator = 1 :=
    Nat.eq_one_of_dvd_one denominatorDividesOne
  refine ⟨numerator, ?_⟩
  simpa only [denominatorOne, Nat.cast_one, mul_one] using cleared

/-! ## Exact rational trace bounds -/

private theorem vectorQuadrance_nonnegative (vector : Vector Scalar) :
    0 ≤ vector.quadrance := by
  have tNonnegative :=
    RFAP.ConstructiveFraction.sq_nonneg_direct vector.t
  have rNonnegative :=
    RFAP.ConstructiveFraction.sq_nonneg_direct vector.r
  have sNonnegative :=
    RFAP.ConstructiveFraction.sq_nonneg_direct vector.s
  unfold Vector.quadrance Vector.dot
  simpa only [pow_two] using
    add_nonneg (add_nonneg tNonnegative rNonnegative) sNonnegative

private theorem ofRotation_halfSpread (rotation : Rotation Scalar) :
    halfSpread
        (RotationProportion.ofRotation rotation (by decide)).rotation =
      halfSpread rotation := by
  let twoNonzero : (2 : Scalar) ≠ 0 := by decide
  have matrixEqual :=
    RotationProportion.ofRotation_rotationMatrix rotation twoNonzero
  change
    (RotationProportion.ofRotation rotation twoNonzero).rotation.matrix =
      rotation.matrix at matrixEqual
  unfold halfSpread
  rw [matrixEqual]

/-- The half spread of a rational rotation is nonnegative, proved directly
from the three displayed rational squares in its canonical projective
representative. -/
theorem halfSpread_nonnegative (rotation : Rotation Scalar) :
    0 ≤ halfSpread rotation := by
  let proportion := RotationProportion.ofRotation rotation (by decide)
  have quotientNonnegative :
      0 ≤ proportion.vector.quadrance /
        proportion.toProportion.norm :=
    RFAP.ConstructiveFraction.div_nonneg_direct
      (vectorQuadrance_nonnegative proportion.vector)
      (TheoremSixtyTwo.nonNullProportion_norm_positive proportion).le
  calc
    0 ≤ halfSpread proportion.rotation := by
      rw [NonNullProportion.halfSpread_rotation proportion (by decide)]
      exact quotientNonnegative
    _ = halfSpread rotation := ofRotation_halfSpread rotation

/-- The complementary half spread is nonnegative, again from one displayed
rational square and the positive cached norm. -/
theorem one_sub_halfSpread_nonnegative (rotation : Rotation Scalar) :
    0 ≤ 1 - halfSpread rotation := by
  let proportion := RotationProportion.ofRotation rotation (by decide)
  have quotientNonnegative :
      0 ≤ proportion.scalar ^ 2 /
        proportion.toProportion.norm :=
    RFAP.ConstructiveFraction.div_nonneg_direct
      (RFAP.ConstructiveFraction.sq_nonneg_direct proportion.scalar)
      (TheoremSixtyTwo.nonNullProportion_norm_positive proportion).le
  calc
    0 ≤ 1 - halfSpread proportion.rotation := by
      rw [NonNullProportion.one_sub_halfSpread_rotation proportion
        (by decide)]
      exact quotientNonnegative
    _ = 1 - halfSpread rotation := by
      rw [ofRotation_halfSpread rotation]

/-- The quadratic trace parameter is the affine half-spread coordinate
`2(1-2h)`. -/
theorem traceParameter_eq_halfSpread (rotation : Rotation Scalar) :
    traceParameter rotation = 2 * (1 - 2 * halfSpread rotation) := by
  have relation := one_add_trace_eq_four_mul_one_sub_halfSpread rotation
    (by decide)
  unfold traceParameter
  calc
    Matrix3.trace rotation.matrix - 1 =
        (1 + Matrix3.trace rotation.matrix) - 2 := by ring1
    _ = 4 * (1 - halfSpread rotation) - 2 := by rw [relation]
    _ = 2 * (1 - 2 * halfSpread rotation) := by ring1

/-- Exact rational bounds for the trace parameter, with no transfer through
the reals. -/
theorem traceParameter_bounds (rotation : Rotation Scalar) :
    (-2 : Scalar) ≤ traceParameter rotation ∧
      traceParameter rotation ≤ 2 := by
  have spreadNonnegative := halfSpread_nonnegative rotation
  have complementNonnegative := one_sub_halfSpread_nonnegative rotation
  constructor
  · apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    rw [traceParameter_eq_halfSpread]
    have scaled :
        0 ≤ (4 : Scalar) * (1 - halfSpread rotation) :=
      RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        complementNonnegative
    convert scaled using 1
    all_goals ring1
  · apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    rw [traceParameter_eq_halfSpread]
    have scaled : 0 ≤ (4 : Scalar) * halfSpread rotation :=
      RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        spreadNonnegative
    convert scaled using 1
    all_goals ring1

/-- A finite-order certificate reduces the integral trace parameter to five
explicit values. -/
theorem ExactFiniteOrderCertificate.traceParameter_five_cases
    {rotation : Rotation Scalar} {order : Nat}
    (certificate : ExactFiniteOrderCertificate rotation order) :
    ∃ numerator : Int,
      traceParameter rotation = (numerator : Scalar) ∧
        (numerator = -2 ∨ numerator = -1 ∨ numerator = 0 ∨
          numerator = 1 ∨ numerator = 2) := by
  rcases certificate.traceParameter_isInteger with ⟨numerator, traceEq⟩
  have bounds := traceParameter_bounds rotation
  have lowerCast : ((-2 : Int) : Scalar) ≤ (numerator : Scalar) := by
    calc
      ((-2 : Int) : Scalar) = (-2 : Scalar) := by ring1
      _ ≤ traceParameter rotation := bounds.1
      _ = (numerator : Scalar) := traceEq
  have upperCast : (numerator : Scalar) ≤ ((2 : Int) : Scalar) := by
    calc
      (numerator : Scalar) = traceParameter rotation := traceEq.symm
      _ ≤ (2 : Scalar) := bounds.2
      _ = ((2 : Int) : Scalar) := by ring1
  have lower : (-2 : Int) ≤ numerator :=
    (RFAP.ConstructiveFraction.intCast_le_intCast_iff_direct (-2) numerator).mp
      lowerCast
  have upper : numerator ≤ (2 : Int) :=
    (RFAP.ConstructiveFraction.intCast_le_intCast_iff_direct numerator 2).mp
      upperCast
  refine ⟨numerator, traceEq, ?_⟩
  omega

/-! ## Five exact finite orders -/

/-- If the finite Lucas recurrence returns `2`, the corresponding displayed
matrix power is the identity.  The final separation step is the rational
three-square theorem, not a complex eigenvalue argument. -/
theorem matrixPow_eq_identity_of_traceLucas_eq_two
    (rotation : Rotation Scalar) (exponent : Nat)
    (root : traceLucas exponent (traceParameter rotation) = 2) :
    matrixPow rotation.matrix exponent = Matrix3.identity := by
  have spreadZero : halfSpread (rotationPow rotation exponent) = 0 := by
    unfold halfSpread
    rw [rotationPow_matrix, trace_rotationPow, root]
    decide
  have identity := rotation_eq_identity_of_halfSpread_zero
    rationalSumSquaresSeparate (rotationPow rotation exponent) spreadZero
      (by decide)
  rwa [rotationPow_matrix] at identity

/-- Exact minimality bounds the stored order by every other positive identity
exponent. -/
theorem ExactFiniteOrderCertificate.order_le_of_power_identity
    {rotation : Rotation Scalar} {order candidate : Nat}
    (certificate : ExactFiniteOrderCertificate rotation order)
    (candidatePositive : 0 < candidate)
    (candidateIdentity :
      matrixPow rotation.matrix candidate = Matrix3.identity) :
    order ≤ candidate := by
  by_cases candidateSmaller : candidate < order
  · have nonidentity := certificate.smaller_nonidentity candidate
      candidatePositive candidateSmaller
    rw [rotationPow_matrix] at nonidentity
    exact (nonidentity candidateIdentity).elim
  · omega

private theorem exactOrder_eq_one_of_traceParameter_eq_two
    {rotation : Rotation Scalar} {order : Nat}
    (certificate : ExactFiniteOrderCertificate rotation order)
    (traceEq : traceParameter rotation = (2 : Scalar)) : order = 1 := by
  have candidateRoot : traceLucas 1 (traceParameter rotation) = 2 := by
    rw [traceEq]
    decide
  have orderUpper : order ≤ 1 :=
    certificate.order_le_of_power_identity (by decide)
    (matrixPow_eq_identity_of_traceLucas_eq_two rotation 1 candidateRoot)
  have orderPositive : 0 < order := certificate.orderPositive
  omega

private theorem exactOrder_eq_two_of_traceParameter_eq_neg_two
    {rotation : Rotation Scalar} {order : Nat}
    (certificate : ExactFiniteOrderCertificate rotation order)
    (traceEq : traceParameter rotation = (-2 : Scalar)) : order = 2 := by
  have candidateRoot : traceLucas 2 (traceParameter rotation) = 2 := by
    rw [traceEq]
    decide
  have orderUpper : order ≤ 2 :=
    certificate.order_le_of_power_identity (by decide)
    (matrixPow_eq_identity_of_traceLucas_eq_two rotation 2 candidateRoot)
  have orderPositive : 0 < order := certificate.orderPositive
  have actualRoot := certificate.traceLucas_eq_two
  have orderCases : order = 1 ∨ order = 2 := by omega
  rcases orderCases with orderOne | orderTwo
  · subst order
    rw [traceLucas_one, traceEq] at actualRoot
    exact ((by decide : (-2 : Scalar) ≠ 2) actualRoot).elim
  · exact orderTwo

private theorem exactOrder_eq_three_of_traceParameter_eq_neg_one
    {rotation : Rotation Scalar} {order : Nat}
    (certificate : ExactFiniteOrderCertificate rotation order)
    (traceEq : traceParameter rotation = (-1 : Scalar)) : order = 3 := by
  have candidateRoot : traceLucas 3 (traceParameter rotation) = 2 := by
    rw [traceEq]
    decide
  have orderUpper : order ≤ 3 :=
    certificate.order_le_of_power_identity (by decide)
    (matrixPow_eq_identity_of_traceLucas_eq_two rotation 3 candidateRoot)
  have orderPositive : 0 < order := certificate.orderPositive
  have actualRoot := certificate.traceLucas_eq_two
  have orderCases : order = 1 ∨ order = 2 ∨ order = 3 := by omega
  rcases orderCases with orderOne | orderTwo | orderThree
  · subst order
    rw [traceEq] at actualRoot
    exact ((by decide : traceLucas 1 (-1 : Scalar) ≠ 2) actualRoot).elim
  · subst order
    rw [traceEq] at actualRoot
    exact ((by decide : traceLucas 2 (-1 : Scalar) ≠ 2) actualRoot).elim
  · exact orderThree

private theorem exactOrder_eq_four_of_traceParameter_eq_zero
    {rotation : Rotation Scalar} {order : Nat}
    (certificate : ExactFiniteOrderCertificate rotation order)
    (traceEq : traceParameter rotation = (0 : Scalar)) : order = 4 := by
  have candidateRoot : traceLucas 4 (traceParameter rotation) = 2 := by
    rw [traceEq]
    decide
  have orderUpper : order ≤ 4 :=
    certificate.order_le_of_power_identity (by decide)
    (matrixPow_eq_identity_of_traceLucas_eq_two rotation 4 candidateRoot)
  have orderPositive : 0 < order := certificate.orderPositive
  have actualRoot := certificate.traceLucas_eq_two
  have orderCases : order = 1 ∨ order = 2 ∨ order = 3 ∨ order = 4 := by
    omega
  rcases orderCases with orderOne | orderTwo | orderThree | orderFour
  · subst order
    rw [traceEq] at actualRoot
    exact ((by decide : traceLucas 1 (0 : Scalar) ≠ 2) actualRoot).elim
  · subst order
    rw [traceEq] at actualRoot
    exact ((by decide : traceLucas 2 (0 : Scalar) ≠ 2) actualRoot).elim
  · subst order
    rw [traceEq] at actualRoot
    exact ((by decide : traceLucas 3 (0 : Scalar) ≠ 2) actualRoot).elim
  · exact orderFour

private theorem exactOrder_eq_six_of_traceParameter_eq_one
    {rotation : Rotation Scalar} {order : Nat}
    (certificate : ExactFiniteOrderCertificate rotation order)
    (traceEq : traceParameter rotation = (1 : Scalar)) : order = 6 := by
  have candidateRoot : traceLucas 6 (traceParameter rotation) = 2 := by
    rw [traceEq]
    decide
  have orderUpper : order ≤ 6 :=
    certificate.order_le_of_power_identity (by decide)
    (matrixPow_eq_identity_of_traceLucas_eq_two rotation 6 candidateRoot)
  have orderPositive : 0 < order := certificate.orderPositive
  have actualRoot := certificate.traceLucas_eq_two
  have orderCases : order = 1 ∨ order = 2 ∨ order = 3 ∨ order = 4 ∨
      order = 5 ∨ order = 6 := by omega
  rcases orderCases with orderOne | orderTwo | orderThree | orderFour |
      orderFive | orderSix
  · subst order
    rw [traceEq] at actualRoot
    exact ((by decide : traceLucas 1 (1 : Scalar) ≠ 2) actualRoot).elim
  · subst order
    rw [traceEq] at actualRoot
    exact ((by decide : traceLucas 2 (1 : Scalar) ≠ 2) actualRoot).elim
  · subst order
    rw [traceEq] at actualRoot
    exact ((by decide : traceLucas 3 (1 : Scalar) ≠ 2) actualRoot).elim
  · subst order
    rw [traceEq] at actualRoot
    exact ((by decide : traceLucas 4 (1 : Scalar) ≠ 2) actualRoot).elim
  · subst order
    rw [traceEq] at actualRoot
    exact ((by decide : traceLucas 5 (1 : Scalar) ≠ 2) actualRoot).elim
  · exact orderSix

/-- No completed torsion carrier is needed: every supplied exact finite-order
certificate has one of the five possible positive exponents. -/
theorem ExactFiniteOrderCertificate.order_five_cases
    {rotation : Rotation Scalar} {order : Nat}
    (certificate : ExactFiniteOrderCertificate rotation order) :
    order = 1 ∨ order = 2 ∨ order = 3 ∨ order = 4 ∨ order = 6 := by
  rcases certificate.traceParameter_five_cases with
    ⟨numerator, traceEq, numeratorCases⟩
  rcases numeratorCases with negativeTwo | negativeOne | zero | one | two
  · subst numerator
    have literalTrace : traceParameter rotation = (-2 : Scalar) := by
      calc
        traceParameter rotation = ((-2 : Int) : Scalar) := traceEq
        _ = (-2 : Scalar) := by ring1
    exact Or.inr (Or.inl
      (exactOrder_eq_two_of_traceParameter_eq_neg_two certificate literalTrace))
  · subst numerator
    have literalTrace : traceParameter rotation = (-1 : Scalar) := by
      calc
        traceParameter rotation = ((-1 : Int) : Scalar) := traceEq
        _ = (-1 : Scalar) := by ring1
    exact Or.inr (Or.inr (Or.inl
      (exactOrder_eq_three_of_traceParameter_eq_neg_one certificate literalTrace)))
  · subst numerator
    have literalTrace : traceParameter rotation = (0 : Scalar) := by
      calc
        traceParameter rotation = ((0 : Int) : Scalar) := traceEq
        _ = (0 : Scalar) := by ring1
    exact Or.inr (Or.inr (Or.inr (Or.inl
      (exactOrder_eq_four_of_traceParameter_eq_zero certificate literalTrace))))
  · subst numerator
    have literalTrace : traceParameter rotation = (1 : Scalar) := by
      calc
        traceParameter rotation = ((1 : Int) : Scalar) := traceEq
        _ = (1 : Scalar) := by ring1
    exact Or.inr (Or.inr (Or.inr (Or.inr
      (exactOrder_eq_six_of_traceParameter_eq_one certificate literalTrace))))
  · subst numerator
    have literalTrace : traceParameter rotation = (2 : Scalar) := by
      calc
        traceParameter rotation = ((2 : Int) : Scalar) := traceEq
        _ = (2 : Scalar) := by ring1
    exact Or.inl
      (exactOrder_eq_one_of_traceParameter_eq_two certificate literalTrace)

/-! ## Executable value classifier -/

private theorem rationalTwoNonzero : (2 : Scalar) ≠ 0 := by decide

/-- The one canonical projective representative consumed by the value table. -/
def canonicalProportion (rotation : Rotation Scalar) :
    NonNullProportion Scalar :=
  RotationProportion.ofRotation rotation rationalTwoNonzero

theorem canonicalProportion_rotationMatrix (rotation : Rotation Scalar) :
    (canonicalProportion rotation).rotation.matrix = rotation.matrix := by
  exact RotationProportion.ofRotation_rotationMatrix rotation
    rationalTwoNonzero

theorem canonicalProportion_halfSpread (rotation : Rotation Scalar) :
    halfSpread (canonicalProportion rotation).rotation =
      halfSpread rotation := by
  unfold halfSpread
  rw [canonicalProportion_rotationMatrix]

/-- Solving the defining trace equation for one displayed trace parameter. -/
theorem halfSpread_eq_of_traceParameter_eq (rotation : Rotation Scalar)
    (value : Scalar) (traceEq : traceParameter rotation = value) :
    halfSpread rotation = (2 - value) / 4 := by
  have matrixTrace : Matrix3.trace rotation.matrix = value + 1 := by
    calc
      Matrix3.trace rotation.matrix =
          (Matrix3.trace rotation.matrix - 1) + 1 := by ring1
      _ = value + 1 := by rw [← traceEq]; rfl
  unfold halfSpread
  rw [matrixTrace]
  apply congrArg (fun numerator : Scalar => numerator / 4)
  ring1

private theorem canonicalQuadranceClass_equivalent_of_halfSpread
    (rotation : Rotation Scalar) (spread factor : Scalar)
    (target : SquareClassRepresentative Scalar)
    (spreadEq : halfSpread rotation = spread)
    (spreadNotOne : spread ≠ 1) (factorNonzero : factor ≠ 0)
    (targetValue : target.value = factor ^ 2 * (1 - spread)) :
    (canonicalProportion rotation).quadranceClass.Equivalent target := by
  let proportion := canonicalProportion rotation
  have proportionSpread : halfSpread proportion.rotation = spread :=
    (canonicalProportion_halfSpread rotation).trans spreadEq
  have scalarNonzero : proportion.scalar ≠ 0 := by
    intro scalarZero
    have spreadOne :=
      (NonNullProportion.halfSpread_rotation_eq_one_iff proportion
        rationalTwoNonzero).2 scalarZero
    apply spreadNotOne
    exact proportionSpread.symm.trans spreadOne
  have affine :=
    NonNullProportion.quadranceClass_equivalent_one_sub_halfSpread
      proportion scalarNonzero rationalTwoNonzero
  apply SquareClassRepresentative.equivalent_trans affine
  refine ⟨factor, factorNonzero, ?_⟩
  change target.value = factor ^ 2 * (1 - halfSpread proportion.rotation)
  rw [proportionSpread]
  exact targetValue

/-- The five branches cache the exact order, trace parameter, half spread,
and quotient-free quadrance-class value.  The half-turn branch retains the
displayed canonical axis quadrance rather than claiming an unsupported
three-square image classification. -/
inductive Classification (rotation : Rotation Scalar) (order : Nat) : Type
  | orderOne
      (order_eq : order = 1)
      (traceParameter_eq : traceParameter rotation = 2)
      (halfSpread_eq : halfSpread rotation = 0)
      (quadranceClass_equivalent :
        (canonicalProportion rotation).quadranceClass.Equivalent
          (PositiveSquareClassSignatures.positiveNaturalClass 1 (by decide)))
  | orderTwo
      (order_eq : order = 2)
      (traceParameter_eq : traceParameter rotation = -2)
      (halfSpread_eq : halfSpread rotation = 1)
      (canonicalScalar_eq_zero :
        (canonicalProportion rotation).scalar = 0)
      (quadranceClass_value_eq_axisQuadrance :
        (canonicalProportion rotation).quadranceClass.value =
          (canonicalProportion rotation).vector.quadrance)
  | orderThree
      (order_eq : order = 3)
      (traceParameter_eq : traceParameter rotation = -1)
      (halfSpread_eq : halfSpread rotation = 3 / 4)
      (quadranceClass_equivalent :
        (canonicalProportion rotation).quadranceClass.Equivalent
          (PositiveSquareClassSignatures.positiveNaturalClass 1 (by decide)))
  | orderFour
      (order_eq : order = 4)
      (traceParameter_eq : traceParameter rotation = 0)
      (halfSpread_eq : halfSpread rotation = 1 / 2)
      (quadranceClass_equivalent :
        (canonicalProportion rotation).quadranceClass.Equivalent
          (PositiveSquareClassSignatures.positiveNaturalClass 2 (by decide)))
  | orderSix
      (order_eq : order = 6)
      (traceParameter_eq : traceParameter rotation = 1)
      (halfSpread_eq : halfSpread rotation = 1 / 4)
      (quadranceClass_equivalent :
        (canonicalProportion rotation).quadranceClass.Equivalent
          (PositiveSquareClassSignatures.positiveNaturalClass 3 (by decide)))

/-- Total finite-order value classification from one supplied exact finite
power/minimality certificate. -/
def classify {rotation : Rotation Scalar} {order : Nat}
    (certificate : ExactFiniteOrderCertificate rotation order) :
    Classification rotation order := by
  by_cases negativeTwo : traceParameter rotation = (-2 : Scalar)
  · have literalTrace := negativeTwo
    have orderEq :=
      exactOrder_eq_two_of_traceParameter_eq_neg_two certificate literalTrace
    have spreadFormula :=
      halfSpread_eq_of_traceParameter_eq rotation (-2) literalTrace
    have spreadEq : halfSpread rotation = (1 : Scalar) := by
      calc
        halfSpread rotation = (2 - (-2 : Scalar)) / 4 := spreadFormula
        _ = 1 := by decide
    have proportionSpread :
        halfSpread (canonicalProportion rotation).rotation = 1 :=
      (canonicalProportion_halfSpread rotation).trans spreadEq
    have scalarZero :=
      (NonNullProportion.halfSpread_rotation_eq_one_iff
        (canonicalProportion rotation) rationalTwoNonzero).1 proportionSpread
    have axisClass := NonNullProportion.quadranceClass_at_infinity
      (canonicalProportion rotation) scalarZero
    exact Classification.orderTwo orderEq literalTrace spreadEq scalarZero
      axisClass
  · by_cases negativeOne : traceParameter rotation = (-1 : Scalar)
    · have literalTrace := negativeOne
      have orderEq :=
        exactOrder_eq_three_of_traceParameter_eq_neg_one certificate literalTrace
      have spreadFormula :=
        halfSpread_eq_of_traceParameter_eq rotation (-1) literalTrace
      have spreadEq : halfSpread rotation = (3 / 4 : Scalar) := by
        calc
          halfSpread rotation = (2 - (-1 : Scalar)) / 4 := spreadFormula
          _ = 3 / 4 := by decide
      have classEq := canonicalQuadranceClass_equivalent_of_halfSpread rotation
        (3 / 4) 2
        (PositiveSquareClassSignatures.positiveNaturalClass 1 (by decide))
        spreadEq (by decide) (by decide) (by decide)
      exact Classification.orderThree orderEq literalTrace spreadEq classEq
    · by_cases zero : traceParameter rotation = (0 : Scalar)
      · have literalTrace := zero
        have orderEq :=
          exactOrder_eq_four_of_traceParameter_eq_zero certificate literalTrace
        have spreadFormula :=
          halfSpread_eq_of_traceParameter_eq rotation 0 literalTrace
        have spreadEq : halfSpread rotation = (1 / 2 : Scalar) := by
          calc
            halfSpread rotation = (2 - (0 : Scalar)) / 4 := spreadFormula
            _ = 1 / 2 := by decide
        have classEq := canonicalQuadranceClass_equivalent_of_halfSpread rotation
          (1 / 2) 2
          (PositiveSquareClassSignatures.positiveNaturalClass 2 (by decide))
          spreadEq (by decide) (by decide) (by decide)
        exact Classification.orderFour orderEq literalTrace spreadEq classEq
      · by_cases one : traceParameter rotation = (1 : Scalar)
        · have literalTrace := one
          have orderEq :=
            exactOrder_eq_six_of_traceParameter_eq_one certificate literalTrace
          have spreadFormula :=
            halfSpread_eq_of_traceParameter_eq rotation 1 literalTrace
          have spreadEq : halfSpread rotation = (1 / 4 : Scalar) := by
            calc
              halfSpread rotation = (2 - (1 : Scalar)) / 4 := spreadFormula
              _ = 1 / 4 := by decide
          have classEq :=
            canonicalQuadranceClass_equivalent_of_halfSpread rotation
              (1 / 4) 2
              (PositiveSquareClassSignatures.positiveNaturalClass 3 (by decide))
              spreadEq (by decide) (by decide) (by decide)
          exact Classification.orderSix orderEq literalTrace spreadEq classEq
        · by_cases two : traceParameter rotation = (2 : Scalar)
          · have literalTrace := two
            have orderEq :=
              exactOrder_eq_one_of_traceParameter_eq_two certificate literalTrace
            have spreadFormula :=
              halfSpread_eq_of_traceParameter_eq rotation 2 literalTrace
            have spreadEq : halfSpread rotation = (0 : Scalar) := by
              calc
                halfSpread rotation = (2 - (2 : Scalar)) / 4 := spreadFormula
                _ = 0 := by decide
            have classEq :=
              canonicalQuadranceClass_equivalent_of_halfSpread rotation 0 1
                (PositiveSquareClassSignatures.positiveNaturalClass 1
                  (by decide))
                spreadEq (by decide) (by decide) (by decide)
            exact Classification.orderOne orderEq literalTrace spreadEq classEq
          · have impossible : False := by
              rcases certificate.traceParameter_five_cases with
                ⟨numerator, traceEq, numeratorCases⟩
              rcases numeratorCases with negTwo | negOne | numeratorZero |
                  numeratorOne | numeratorTwo
              · subst numerator
                apply negativeTwo
                calc
                  traceParameter rotation = ((-2 : Int) : Scalar) := traceEq
                  _ = (-2 : Scalar) := by ring1
              · subst numerator
                apply negativeOne
                calc
                  traceParameter rotation = ((-1 : Int) : Scalar) := traceEq
                  _ = (-1 : Scalar) := by ring1
              · subst numerator
                apply zero
                calc
                  traceParameter rotation = ((0 : Int) : Scalar) := traceEq
                  _ = (0 : Scalar) := by ring1
              · subst numerator
                apply one
                calc
                  traceParameter rotation = ((1 : Int) : Scalar) := traceEq
                  _ = (1 : Scalar) := by ring1
              · subst numerator
                apply two
                calc
                  traceParameter rotation = ((2 : Int) : Scalar) := traceEq
                  _ = (2 : Scalar) := by ring1
            exact impossible.elim

end FiniteRotationOrder

end RationalRotations
