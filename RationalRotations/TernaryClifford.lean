import RationalRotations.Anchors
import RationalRotations.TernaryForms

/-!
# Explicit even Clifford algebra of a ternary form

The four coordinates are stored as one scalar and one displayed vector.  The
product uses the cached adjugate of the form matrix, so it is polynomial in
the supplied finite data and performs no fresh matrix inversion.
-/

namespace RationalRotations

variable {K : Type*} [RFAP.ExplicitField K]

namespace TernaryForm

private theorem scalar_eq_zero_of_nonzero_mul_eq_zero
    {factor value : K} (factorNonzero : factor ≠ 0)
    (productZero : factor * value = 0) : value = 0 := by
  have cancel := RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    value = (factor * factor⁻¹) * value := by rw [cancel, one_mul]
    _ = factor⁻¹ * (factor * value) := by ring1
    _ = 0 := by rw [productZero, mul_zero]

private theorem scalar_eq_of_nonzero_mul_eq_mul {factor left right : K}
    (factorNonzero : factor ≠ 0)
    (equal : factor * left = factor * right) : left = right := by
  have cancel := RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    left = (factor * factor⁻¹) * left := by rw [cancel, one_mul]
    _ = factor⁻¹ * (factor * left) := by ring1
    _ = factor⁻¹ * (factor * right) := by rw [equal]
    _ = (factor * factor⁻¹) * right := by ring1
    _ = right := by rw [cancel, one_mul]

/-- The denominator-free cross term used by the even Clifford product. -/
def cliffordCross (form : TernaryForm K) (left right : Vector K) : Vector K :=
  Matrix3.rowMul (Vector.cross left right) form.adjugate

/-- The adjugate cross is the determinant-scaled form-relative cross. -/
theorem cliffordCross_eq_scale_cross (form : TernaryForm K)
    (left right : Vector K) :
    form.cliffordCross left right =
      Vector.scale form.determinant (form.cross left right) := by
  have cancel : form.determinant * form.determinant⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel form.determinant
      form.determinantNonzero
  unfold cliffordCross cross
  rw [form.inverse_eq_scale_adjugate]
  rw [Matrix3.rowMul_scale]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  rw [Vector.scale_scale]
  have coefficient : form.determinant * (1 * form.determinant⁻¹) =
      (1 : K) := by
    calc
      form.determinant * (1 * form.determinant⁻¹) =
          form.determinant * form.determinant⁻¹ := by ring1
      _ = 1 := cancel
  rw [coefficient, Vector.one_scale]

/-- Multiplying the denominator-free relative cross by the form matrix
recovers the ordinary cross, scaled only by the cached determinant. -/
theorem rowMul_cliffordCross_matrix (form : TernaryForm K)
    (left right : Vector K) :
    Matrix3.rowMul (form.cliffordCross left right) form.matrix =
      Vector.scale form.determinant (Vector.cross left right) := by
  unfold cliffordCross
  rw [Matrix3.rowMul_mul, form.adjugate_mul_matrix,
    Matrix3.rowMul_scale, Matrix3.rowMul_identity]

/-- A displayed vector whose denominator-free Clifford cross with every test
vector vanishes is zero.  The coordinate tests make the nondegeneracy
argument executable and require no selected basis extension. -/
theorem eq_zero_of_cliffordCross_right_eq_zero (form : TernaryForm K)
    (axis : Vector K)
    (annihilated : ∀ vector : Vector K,
      form.cliffordCross vector axis = Vector.zero) :
    axis = Vector.zero := by
  have ordinaryCrossZero : ∀ vector : Vector K,
      Vector.cross vector axis = Vector.zero := by
    intro vector
    have scaledCrossZero :
        Vector.scale form.determinant (Vector.cross vector axis) =
          Vector.zero := by
      calc
        Vector.scale form.determinant (Vector.cross vector axis) =
            Matrix3.rowMul (form.cliffordCross vector axis) form.matrix :=
          (form.rowMul_cliffordCross_matrix vector axis).symm
        _ = Matrix3.rowMul Vector.zero form.matrix := by
          rw [annihilated vector]
        _ = Vector.zero := by
          ext <;> unfold Matrix3.rowMul Vector.zero <;> ring1
    apply Vector.ext
    · apply scalar_eq_zero_of_nonzero_mul_eq_zero
        form.determinantNonzero
      simpa only [Vector.scale_t, Vector.zero_t] using
        congrArg Vector.t scaledCrossZero
    · apply scalar_eq_zero_of_nonzero_mul_eq_zero
        form.determinantNonzero
      simpa only [Vector.scale_r, Vector.zero_r] using
        congrArg Vector.r scaledCrossZero
    · apply scalar_eq_zero_of_nonzero_mul_eq_zero
        form.determinantNonzero
      simpa only [Vector.scale_s, Vector.zero_s] using
        congrArg Vector.s scaledCrossZero
  have first := ordinaryCrossZero (⟨1, 0, 0⟩ : Vector K)
  have second := ordinaryCrossZero (⟨0, 1, 0⟩ : Vector K)
  have axisS : axis.s = 0 := by
    have coordinate := congrArg Vector.r first
    simpa only [Vector.cross, Vector.zero_r, zero_mul, mul_zero, one_mul, mul_one,
      sub_zero, zero_sub, neg_eq_zero] using coordinate
  have axisR : axis.r = 0 := by
    have coordinate := congrArg Vector.s first
    simpa only [Vector.cross, Vector.zero_s, zero_mul, mul_zero, one_mul,
      sub_zero] using coordinate
  have axisT : axis.t = 0 := by
    have coordinate := congrArg Vector.s second
    simpa only [Vector.cross, Vector.zero_s, zero_mul, mul_zero, one_mul, mul_one,
      sub_zero, zero_sub, neg_eq_zero] using coordinate
  apply Vector.ext
  · exact axisT
  · exact axisR
  · exact axisS

@[simp] theorem cliffordCross_zero_left (form : TernaryForm K)
    (vector : Vector K) :
    form.cliffordCross Vector.zero vector = Vector.zero := by
  ext <;> unfold cliffordCross Vector.cross Vector.zero Matrix3.rowMul <;>
    ring1

@[simp] theorem cliffordCross_zero_right (form : TernaryForm K)
    (vector : Vector K) :
    form.cliffordCross vector Vector.zero = Vector.zero := by
  ext <;> unfold cliffordCross Vector.cross Vector.zero Matrix3.rowMul <;>
    ring1

@[simp] theorem cliffordCross_self (form : TernaryForm K)
    (vector : Vector K) :
    form.cliffordCross vector vector = Vector.zero := by
  ext <;> unfold cliffordCross Vector.cross Matrix3.rowMul Vector.zero <;>
    ring1

theorem cliffordCross_anticomm (form : TernaryForm K)
    (left right : Vector K) :
    form.cliffordCross left right =
      Vector.neg (form.cliffordCross right left) := by
  ext <;> unfold cliffordCross Vector.cross Matrix3.rowMul Vector.neg <;>
    ring1

theorem cliffordCross_add_left (form : TernaryForm K)
    (first second third : Vector K) :
    form.cliffordCross (Vector.add first second) third =
      Vector.add (form.cliffordCross first third)
        (form.cliffordCross second third) := by
  ext <;> unfold cliffordCross Vector.cross Vector.add Matrix3.rowMul <;>
    ring1

theorem cliffordCross_add_right (form : TernaryForm K)
    (first second third : Vector K) :
    form.cliffordCross first (Vector.add second third) =
      Vector.add (form.cliffordCross first second)
        (form.cliffordCross first third) := by
  ext <;> unfold cliffordCross Vector.cross Vector.add Matrix3.rowMul <;>
    ring1

theorem cliffordCross_sub_left (form : TernaryForm K)
    (first second third : Vector K) :
    form.cliffordCross (Vector.sub first second) third =
      Vector.sub (form.cliffordCross first third)
        (form.cliffordCross second third) := by
  ext <;> unfold cliffordCross Vector.cross Vector.sub Matrix3.rowMul <;>
    ring1

theorem cliffordCross_sub_right (form : TernaryForm K)
    (first second third : Vector K) :
    form.cliffordCross first (Vector.sub second third) =
      Vector.sub (form.cliffordCross first second)
        (form.cliffordCross first third) := by
  ext <;> unfold cliffordCross Vector.cross Vector.sub Matrix3.rowMul <;>
    ring1

theorem cliffordCross_scale_left (form : TernaryForm K) (scalar : K)
    (left right : Vector K) :
    form.cliffordCross (Vector.scale scalar left) right =
      Vector.scale scalar (form.cliffordCross left right) := by
  ext <;> unfold cliffordCross Vector.cross Vector.scale Matrix3.rowMul <;>
    ring1

theorem cliffordCross_scale_right (form : TernaryForm K) (scalar : K)
    (left right : Vector K) :
    form.cliffordCross left (Vector.scale scalar right) =
      Vector.scale scalar (form.cliffordCross left right) := by
  ext <;> unfold cliffordCross Vector.cross Vector.scale Matrix3.rowMul <;>
    ring1

theorem cliffordCross_neg_left (form : TernaryForm K)
    (left right : Vector K) :
    form.cliffordCross (Vector.neg left) right =
      Vector.neg (form.cliffordCross left right) := by
  ext <;> unfold cliffordCross Vector.cross Vector.neg Matrix3.rowMul <;>
    ring1

theorem cliffordCross_neg_right (form : TernaryForm K)
    (left right : Vector K) :
    form.cliffordCross left (Vector.neg right) =
      Vector.neg (form.cliffordCross left right) := by
  ext <;> unfold cliffordCross Vector.cross Vector.neg Matrix3.rowMul <;>
    ring1

/-- The adjugate cross has the determinant-scaled scalar triple product. -/
theorem bilinear_cliffordCross (form : TernaryForm K)
    (first second third : Vector K) :
    form.bilinear (form.cliffordCross first second) third =
      form.determinant * Vector.determinant first second third := by
  rw [form.cliffordCross_eq_scale_cross,
    form.bilinear_scale_left, form.bilinear_cross]

theorem bilinear_cliffordCross_cyclic (form : TernaryForm K)
    (first second third : Vector K) :
    form.bilinear (form.cliffordCross first second) third =
      form.bilinear first (form.cliffordCross second third) := by
  rw [form.bilinear_cliffordCross,
    form.bilinear_comm first (form.cliffordCross second third),
    form.bilinear_cliffordCross]
  congr 1
  unfold Vector.determinant
  ring1

theorem cliffordCross_perpendicular_left (form : TernaryForm K)
    (left right : Vector K) :
    form.Perpendicular (form.cliffordCross left right) left := by
  rw [form.cliffordCross_eq_scale_cross]
  exact form.perpendicular_scale_left form.determinant
    (form.cross left right) left (form.cross_perpendicular_left left right)

theorem cliffordCross_perpendicular_right (form : TernaryForm K)
    (left right : Vector K) :
    form.Perpendicular (form.cliffordCross left right) right := by
  rw [form.cliffordCross_eq_scale_cross]
  exact form.perpendicular_scale_left form.determinant
    (form.cross left right) right (form.cross_perpendicular_right left right)

/-- The adjugate cross has the determinant-scaled Lagrange quadrance. -/
theorem quadrance_cliffordCross (form : TernaryForm K)
    (left right : Vector K) :
    form.quadrance (form.cliffordCross left right) =
      form.determinant *
        (form.quadrance left * form.quadrance right -
          form.bilinear left right ^ 2) := by
  have lagrange := form.lagrange left right
  have remainder :
      form.determinant * form.quadrance (form.cross left right) =
        form.quadrance left * form.quadrance right -
          form.bilinear left right ^ 2 := by
    calc
      form.determinant * form.quadrance (form.cross left right) =
          form.bilinear left right ^ 2 +
              form.determinant * form.quadrance (form.cross left right) -
            form.bilinear left right ^ 2 := by ring1
      _ = form.quadrance left * form.quadrance right -
          form.bilinear left right ^ 2 := by rw [lagrange]
  rw [form.cliffordCross_eq_scale_cross, form.quadrance_scale]
  calc
    form.determinant ^ 2 * form.quadrance (form.cross left right) =
        form.determinant *
          (form.determinant * form.quadrance (form.cross left right)) := by
      ring1
    _ = form.determinant *
        (form.quadrance left * form.quadrance right -
          form.bilinear left right ^ 2) := by rw [remainder]

/-- Determinant-scaled Binet--Cauchy for two adjugate crosses. -/
theorem bilinear_cliffordCross_pair (form : TernaryForm K)
    (first second third fourth : Vector K) :
    form.bilinear (form.cliffordCross first second)
        (form.cliffordCross third fourth) =
      form.determinant *
        (form.bilinear first third * form.bilinear second fourth -
          form.bilinear first fourth * form.bilinear second third) := by
  have binet := form.binet_cauchy first second third fourth
  rw [form.cliffordCross_eq_scale_cross,
    form.cliffordCross_eq_scale_cross,
    form.bilinear_scale_left, form.bilinear_scale_right]
  calc
    form.determinant *
        (form.determinant *
          form.bilinear (form.cross first second)
            (form.cross third fourth)) =
      form.determinant *
        (form.bilinear first third * form.bilinear second fourth -
          form.bilinear first fourth * form.bilinear second third) := by
      rw [binet]

/-- The mixed adjugate-cross terms in the Clifford action cancel. -/
theorem bilinear_cliffordCross_swap (form : TernaryForm K)
    (first second axis : Vector K) :
    form.bilinear first (form.cliffordCross second axis) =
      -form.bilinear (form.cliffordCross first axis) second := by
  rw [form.bilinear_comm first (form.cliffordCross second axis),
    form.bilinear_cliffordCross, form.bilinear_cliffordCross]
  unfold Vector.determinant
  ring1

/-- Right-nested adjugate cross identity. -/
theorem cliffordCross_vector_triple (form : TernaryForm K)
    (first second third : Vector K) :
    form.cliffordCross first (form.cliffordCross second third) =
      Vector.sub
        (Vector.scale
          (form.determinant * form.bilinear first third) second)
        (Vector.scale
          (form.determinant * form.bilinear first second) third) := by
  calc
    form.cliffordCross first (form.cliffordCross second third) =
      Vector.scale form.determinant
        (form.cross first (form.cliffordCross second third)) :=
      form.cliffordCross_eq_scale_cross first
        (form.cliffordCross second third)
    _ = Vector.scale form.determinant
        (form.cross first
          (Vector.scale form.determinant (form.cross second third))) := by
      rw [form.cliffordCross_eq_scale_cross]
    _ = Vector.scale form.determinant
        (Vector.scale form.determinant
          (form.cross first (form.cross second third))) := by
      rw [form.cross_scale_right]
    _ = Vector.scale form.determinant
        (Vector.sub
          (Vector.scale (form.bilinear first third) second)
          (Vector.scale (form.bilinear first second) third)) := by
      rw [form.vector_triple_product]
    _ = Vector.sub
        (Vector.scale
          (form.determinant * form.bilinear first third) second)
        (Vector.scale
          (form.determinant * form.bilinear first second) third) := by
      ext <;> unfold Vector.scale Vector.sub <;> ring1

/-- Left-nested adjugate cross identity. -/
theorem cliffordCross_left_triple (form : TernaryForm K)
    (first second third : Vector K) :
    form.cliffordCross (form.cliffordCross first second) third =
      Vector.sub
        (Vector.scale
          (form.determinant * form.bilinear first third) second)
        (Vector.scale
          (form.determinant * form.bilinear second third) first) := by
  calc
    form.cliffordCross (form.cliffordCross first second) third =
      Vector.neg
        (form.cliffordCross third (form.cliffordCross first second)) :=
      form.cliffordCross_anticomm _ _
    _ = Vector.neg
        (Vector.sub
          (Vector.scale
            (form.determinant * form.bilinear third second) first)
          (Vector.scale
            (form.determinant * form.bilinear third first) second)) := by
      rw [form.cliffordCross_vector_triple]
    _ = Vector.sub
        (Vector.scale
          (form.determinant * form.bilinear first third) second)
        (Vector.scale
          (form.determinant * form.bilinear second third) first) := by
      rw [form.bilinear_comm third second, form.bilinear_comm third first]
      ext <;> unfold Vector.neg Vector.sub Vector.scale <;> ring1

/-- The form-relative skew matrix occurring in the Clifford action. -/
def actionSkew (form : TernaryForm K) (vector : Vector K) : Matrix3 K :=
  Matrix3.mul (anchor vector) form.adjugate

theorem rowMul_actionSkew (form : TernaryForm K) (axis vector : Vector K) :
    Matrix3.rowMul vector (form.actionSkew axis) =
      form.cliffordCross axis vector := by
  unfold actionSkew cliffordCross
  rw [← Matrix3.rowMul_mul, rowMul_anchor]

/-- Quadratic relation for the skew action, derived from the vector triple
product rather than a coordinate determinant expansion. -/
theorem actionSkew_square (form : TernaryForm K) (axis : Vector K) :
    Matrix3.mul (form.actionSkew axis) (form.actionSkew axis) =
      Matrix3.sub
        (Matrix3.scale form.determinant
          (Matrix3.outer (form.dual axis) axis))
        (Matrix3.scale (form.determinant * form.quadrance axis)
          Matrix3.identity) := by
  apply Matrix3.eq_of_rowMul_eq
  intro vector
  rw [← Matrix3.rowMul_mul, form.rowMul_actionSkew,
    form.rowMul_actionSkew, form.cliffordCross_vector_triple,
    Matrix3.rowMul_sub, Matrix3.rowMul_scale, Matrix3.rowMul_outer,
    Matrix3.rowMul_scale, Matrix3.rowMul_identity,
    ← form.bilinear_eq_dot_dual,
    form.bilinear_comm axis vector]
  unfold quadrance
  ext <;> unfold Vector.sub Vector.scale <;> ring1

theorem trace_actionSkew (form : TernaryForm K) (axis : Vector K) :
    Matrix3.trace (form.actionSkew axis) = 0 := by
  have rt_tr : form.matrix.rt = form.matrix.tr :=
    congrArg Matrix3.tr form.symmetric
  have st_ts : form.matrix.st = form.matrix.ts :=
    congrArg Matrix3.ts form.symmetric
  have sr_rs : form.matrix.sr = form.matrix.rs :=
    congrArg Matrix3.rs form.symmetric
  unfold actionSkew
  rw [form.adjugate_spec]
  unfold Matrix3.trace Matrix3.mul Matrix3.adjugate anchor
  rw [rt_tr, st_ts, sr_rs]
  ring1

theorem principalTrace_actionSkew (form : TernaryForm K)
    (axis : Vector K) :
    Matrix3.principalTrace (form.actionSkew axis) =
      form.determinant * form.quadrance axis := by
  have rt_tr : form.matrix.rt = form.matrix.tr :=
    congrArg Matrix3.tr form.symmetric
  have st_ts : form.matrix.st = form.matrix.ts :=
    congrArg Matrix3.ts form.symmetric
  have sr_rs : form.matrix.sr = form.matrix.rs :=
    congrArg Matrix3.rs form.symmetric
  unfold actionSkew
  rw [form.adjugate_spec, form.determinant_spec]
  unfold Matrix3.principalTrace Matrix3.trace Matrix3.adjugate
    Matrix3.determinant Matrix3.mul anchor quadrance bilinear
    Matrix3.rowMul Vector.dot
  rw [rt_tr, st_ts, sr_rs]
  ring1

@[simp] theorem determinant_actionSkew (form : TernaryForm K)
    (axis : Vector K) :
    Matrix3.determinant (form.actionSkew axis) = 0 := by
  unfold actionSkew
  rw [Matrix3.determinant_mul, determinant_anchor, zero_mul]

/-- In characteristic different from two, a form-relative skew matrix cannot
be nonzero and square to zero.  This is the finite three-dimensional rank
obstruction needed for constructive Cartan--Dieudonne reduction. -/
theorem axis_eq_zero_of_actionSkew_square_eq_zero [DecidableEq K]
    (form : TernaryForm K) (axis : Vector K)
    (twoNonzero : (2 : K) ≠ 0)
    (squareZero :
      Matrix3.mul (form.actionSkew axis) (form.actionSkew axis) =
        Matrix3.zero) :
    axis = Vector.zero := by
  have squareFormula := form.actionSkew_square axis
  rw [squareZero] at squareFormula
  have dualDot :
      (form.dual axis).t * axis.t +
          (form.dual axis).r * axis.r +
          (form.dual axis).s * axis.s =
        form.quadrance axis := by
    unfold dual quadrance bilinear Matrix3.rowMul Vector.dot
    ring1
  have ttFormula := congrArg Matrix3.tt squareFormula
  have rrFormula := congrArg Matrix3.rr squareFormula
  have ssFormula := congrArg Matrix3.ss squareFormula
  simp only [Matrix3.zero, Matrix3.sub, Matrix3.scale, Matrix3.outer,
    Matrix3.identity, mul_one] at ttFormula rrFormula ssFormula
  have ttTerm :
      form.determinant * ((form.dual axis).t * axis.t) =
        form.determinant * form.quadrance axis := by
    calc
      form.determinant * ((form.dual axis).t * axis.t) =
          form.determinant * form.quadrance axis +
            (form.determinant * ((form.dual axis).t * axis.t) -
              form.determinant * form.quadrance axis) := by
        ring1
      _ = form.determinant * form.quadrance axis := by
        rw [← ttFormula, add_zero]
  have rrTerm :
      form.determinant * ((form.dual axis).r * axis.r) =
        form.determinant * form.quadrance axis := by
    calc
      form.determinant * ((form.dual axis).r * axis.r) =
          form.determinant * form.quadrance axis +
            (form.determinant * ((form.dual axis).r * axis.r) -
              form.determinant * form.quadrance axis) := by
        ring1
      _ = form.determinant * form.quadrance axis := by
        rw [← rrFormula, add_zero]
  have ssTerm :
      form.determinant * ((form.dual axis).s * axis.s) =
        form.determinant * form.quadrance axis := by
    calc
      form.determinant * ((form.dual axis).s * axis.s) =
          form.determinant * form.quadrance axis +
            (form.determinant * ((form.dual axis).s * axis.s) -
              form.determinant * form.quadrance axis) := by
        ring1
      _ = form.determinant * form.quadrance axis := by
        rw [← ssFormula, add_zero]
  have twiceDetQuadranceZero :
      2 * (form.determinant * form.quadrance axis) = 0 := by
    calc
      2 * (form.determinant * form.quadrance axis) =
          3 * (form.determinant * form.quadrance axis) -
            form.determinant * form.quadrance axis := by
        ring1
      _ = (form.determinant * ((form.dual axis).t * axis.t) +
              form.determinant * ((form.dual axis).r * axis.r) +
              form.determinant * ((form.dual axis).s * axis.s)) -
            form.determinant * form.quadrance axis := by
        rw [ttTerm, rrTerm, ssTerm]
        ring1
      _ = form.determinant *
            ((form.dual axis).t * axis.t +
              (form.dual axis).r * axis.r +
              (form.dual axis).s * axis.s) -
            form.determinant * form.quadrance axis := by
        ring1
      _ = 0 := by rw [dualDot]; ring1
  have detQuadranceZero :
      form.determinant * form.quadrance axis = 0 :=
    scalar_eq_zero_of_nonzero_mul_eq_zero twoNonzero
      twiceDetQuadranceZero
  have quadranceZero : form.quadrance axis = 0 :=
    scalar_eq_zero_of_nonzero_mul_eq_zero form.determinantNonzero
      detQuadranceZero
  have scaledOuterZero :
      Matrix3.scale form.determinant
          (Matrix3.outer (form.dual axis) axis) =
        Matrix3.zero := by
    have rightZero :
        Matrix3.sub
            (Matrix3.scale form.determinant
              (Matrix3.outer (form.dual axis) axis))
            (Matrix3.scale
              (form.determinant * form.quadrance axis)
              Matrix3.identity) =
          Matrix3.zero :=
      squareFormula.symm
    rw [quadranceZero] at rightZero
    simpa [Matrix3.sub, Matrix3.scale, Matrix3.zero] using rightZero
  have outerZero :
      Matrix3.outer (form.dual axis) axis = Matrix3.zero := by
    apply Matrix3.ext
    all_goals
      apply scalar_eq_zero_of_nonzero_mul_eq_zero form.determinantNonzero
    · simpa [Matrix3.scale, Matrix3.zero] using
        congrArg Matrix3.tt scaledOuterZero
    · simpa [Matrix3.scale, Matrix3.zero] using
        congrArg Matrix3.tr scaledOuterZero
    · simpa [Matrix3.scale, Matrix3.zero] using
        congrArg Matrix3.ts scaledOuterZero
    · simpa [Matrix3.scale, Matrix3.zero] using
        congrArg Matrix3.rt scaledOuterZero
    · simpa [Matrix3.scale, Matrix3.zero] using
        congrArg Matrix3.rr scaledOuterZero
    · simpa [Matrix3.scale, Matrix3.zero] using
        congrArg Matrix3.rs scaledOuterZero
    · simpa [Matrix3.scale, Matrix3.zero] using
        congrArg Matrix3.st scaledOuterZero
    · simpa [Matrix3.scale, Matrix3.zero] using
        congrArg Matrix3.sr scaledOuterZero
    · simpa [Matrix3.scale, Matrix3.zero] using
        congrArg Matrix3.ss scaledOuterZero
  have dualZero : form.dual axis = Vector.zero := by
    by_cases axisTZero : axis.t = 0
    · by_cases axisRZero : axis.r = 0
      · by_cases axisSZero : axis.s = 0
        · have axisZero : axis = Vector.zero := by
            apply Vector.ext
            · exact axisTZero
            · exact axisRZero
            · exact axisSZero
          rw [axisZero]
          ext <;> unfold dual Matrix3.rowMul Vector.zero <;> ring1
        · apply Vector.ext
          · apply scalar_eq_zero_of_nonzero_mul_eq_zero axisSZero
            have coordinate := congrArg Matrix3.ts outerZero
            simpa [Matrix3.outer, Matrix3.zero, mul_comm] using coordinate
          · apply scalar_eq_zero_of_nonzero_mul_eq_zero axisSZero
            have coordinate := congrArg Matrix3.rs outerZero
            simpa [Matrix3.outer, Matrix3.zero, mul_comm] using coordinate
          · apply scalar_eq_zero_of_nonzero_mul_eq_zero axisSZero
            have coordinate := congrArg Matrix3.ss outerZero
            simpa [Matrix3.outer, Matrix3.zero, mul_comm] using coordinate
      · apply Vector.ext
        · apply scalar_eq_zero_of_nonzero_mul_eq_zero axisRZero
          have coordinate := congrArg Matrix3.tr outerZero
          simpa [Matrix3.outer, Matrix3.zero, mul_comm] using coordinate
        · apply scalar_eq_zero_of_nonzero_mul_eq_zero axisRZero
          have coordinate := congrArg Matrix3.rr outerZero
          simpa [Matrix3.outer, Matrix3.zero, mul_comm] using coordinate
        · apply scalar_eq_zero_of_nonzero_mul_eq_zero axisRZero
          have coordinate := congrArg Matrix3.sr outerZero
          simpa [Matrix3.outer, Matrix3.zero, mul_comm] using coordinate
    · apply Vector.ext
      · apply scalar_eq_zero_of_nonzero_mul_eq_zero axisTZero
        have coordinate := congrArg Matrix3.tt outerZero
        simpa [Matrix3.outer, Matrix3.zero, mul_comm] using coordinate
      · apply scalar_eq_zero_of_nonzero_mul_eq_zero axisTZero
        have coordinate := congrArg Matrix3.rt outerZero
        simpa [Matrix3.outer, Matrix3.zero, mul_comm] using coordinate
      · apply scalar_eq_zero_of_nonzero_mul_eq_zero axisTZero
        have coordinate := congrArg Matrix3.st outerZero
        simpa [Matrix3.outer, Matrix3.zero, mul_comm] using coordinate
  exact form.eq_zero_of_rowMul_matrix_eq_zero axis dualZero

/-- A displayed matrix whose form-adjoint is its negative is encoded by the
form-relative skew coordinates.  If it also squares to zero, the
three-dimensional skew obstruction forces the matrix itself to vanish. -/
theorem matrix_eq_zero_of_mul_form_antisymmetric_of_square_eq_zero
    [DecidableEq K] (form : TernaryForm K) (matrix : Matrix3 K)
    (twoNonzero : (2 : K) ≠ 0)
    (antisymmetric :
      Matrix3.IsAntisymmetric (Matrix3.mul matrix form.matrix))
    (squareZero : Matrix3.mul matrix matrix = Matrix3.zero) :
    matrix = Matrix3.zero := by
  let axis := anchorVector (Matrix3.mul matrix form.matrix)
  have encodes :
      anchor axis = Matrix3.mul matrix form.matrix :=
    anchor_anchorVector_of_isAntisymmetric
      (Matrix3.mul matrix form.matrix) twoNonzero antisymmetric
  have actionScale :
      form.actionSkew axis = Matrix3.scale form.determinant matrix := by
    unfold actionSkew
    rw [encodes]
    calc
      Matrix3.mul (Matrix3.mul matrix form.matrix) form.adjugate =
          Matrix3.mul matrix
            (Matrix3.mul form.matrix form.adjugate) :=
        Matrix3.mul_assoc matrix form.matrix form.adjugate
      _ = Matrix3.mul matrix
          (Matrix3.scale form.determinant Matrix3.identity) := by
        rw [form.matrix_mul_adjugate]
      _ = Matrix3.scale form.determinant
          (Matrix3.mul matrix Matrix3.identity) :=
        Matrix3.mul_scale_right form.determinant matrix Matrix3.identity
      _ = Matrix3.scale form.determinant matrix := by
        rw [Matrix3.mul_identity]
  have actionSquareZero :
      Matrix3.mul (form.actionSkew axis) (form.actionSkew axis) =
        Matrix3.zero := by
    rw [actionScale, Matrix3.mul_scale_left,
      Matrix3.mul_scale_right, Matrix3.scale_scale, squareZero]
    ext <;> unfold Matrix3.scale Matrix3.zero <;> ring1
  have axisZero :=
    form.axis_eq_zero_of_actionSkew_square_eq_zero axis twoNonzero
      actionSquareZero
  have matrixFormZero :
      Matrix3.mul matrix form.matrix = Matrix3.zero := by
    calc
      Matrix3.mul matrix form.matrix = anchor axis := encodes.symm
      _ = anchor Vector.zero := by rw [axisZero]
      _ = Matrix3.zero := by
        ext <;> unfold anchor Vector.zero Matrix3.zero <;> ring1
  calc
    matrix = Matrix3.mul matrix Matrix3.identity := by
      rw [Matrix3.mul_identity]
    _ = Matrix3.mul matrix
        (Matrix3.mul form.matrix form.inverse) := by
      rw [form.matrix_mul_inverse]
    _ = Matrix3.mul
        (Matrix3.mul matrix form.matrix) form.inverse :=
      (Matrix3.mul_assoc matrix form.matrix form.inverse).symm
    _ = Matrix3.mul Matrix3.zero form.inverse := by rw [matrixFormZero]
    _ = Matrix3.zero := by
      ext <;> unfold Matrix3.mul Matrix3.zero <;> ring1

/-- A bilinearly skew displayed action has an explicitly antisymmetric
matrix after multiplication by the displayed form matrix. -/
theorem mul_form_isAntisymmetric_of_bilinear_skew
    (form : TernaryForm K) (matrix : Matrix3 K)
    (skew : ∀ left right : Vector K,
      form.bilinear (Matrix3.rowMul left matrix) right =
        -form.bilinear left (Matrix3.rowMul right matrix)) :
    Matrix3.IsAntisymmetric (Matrix3.mul matrix form.matrix) := by
  have rt_tr : form.matrix.rt = form.matrix.tr :=
    congrArg Matrix3.tr form.symmetric
  have st_ts : form.matrix.st = form.matrix.ts :=
    congrArg Matrix3.ts form.symmetric
  have sr_rs : form.matrix.sr = form.matrix.rs :=
    congrArg Matrix3.rs form.symmetric
  unfold Matrix3.IsAntisymmetric
  apply Matrix3.ext
  · simpa [bilinear, Matrix3.transpose, Matrix3.neg, Matrix3.mul,
      Matrix3.rowMul, Vector.dot, rt_tr, st_ts, sr_rs, mul_comm,
      add_comm, add_left_comm, add_assoc] using
      skew (⟨1, 0, 0⟩ : Vector K) (⟨1, 0, 0⟩ : Vector K)
  · simpa [bilinear, Matrix3.transpose, Matrix3.neg, Matrix3.mul,
      Matrix3.rowMul, Vector.dot, rt_tr, st_ts, sr_rs, mul_comm,
      add_comm, add_left_comm, add_assoc] using
      skew (⟨0, 1, 0⟩ : Vector K) (⟨1, 0, 0⟩ : Vector K)
  · simpa [bilinear, Matrix3.transpose, Matrix3.neg, Matrix3.mul,
      Matrix3.rowMul, Vector.dot, rt_tr, st_ts, sr_rs, mul_comm,
      add_comm, add_left_comm, add_assoc] using
      skew (⟨0, 0, 1⟩ : Vector K) (⟨1, 0, 0⟩ : Vector K)
  · simpa [bilinear, Matrix3.transpose, Matrix3.neg, Matrix3.mul,
      Matrix3.rowMul, Vector.dot, rt_tr, st_ts, sr_rs, mul_comm,
      add_comm, add_left_comm, add_assoc] using
      skew (⟨1, 0, 0⟩ : Vector K) (⟨0, 1, 0⟩ : Vector K)
  · simpa [bilinear, Matrix3.transpose, Matrix3.neg, Matrix3.mul,
      Matrix3.rowMul, Vector.dot, rt_tr, st_ts, sr_rs, mul_comm,
      add_comm, add_left_comm, add_assoc] using
      skew (⟨0, 1, 0⟩ : Vector K) (⟨0, 1, 0⟩ : Vector K)
  · simpa [bilinear, Matrix3.transpose, Matrix3.neg, Matrix3.mul,
      Matrix3.rowMul, Vector.dot, rt_tr, st_ts, sr_rs, mul_comm,
      add_comm, add_left_comm, add_assoc] using
      skew (⟨0, 0, 1⟩ : Vector K) (⟨0, 1, 0⟩ : Vector K)
  · simpa [bilinear, Matrix3.transpose, Matrix3.neg, Matrix3.mul,
      Matrix3.rowMul, Vector.dot, rt_tr, st_ts, sr_rs, mul_comm,
      add_comm, add_left_comm, add_assoc] using
      skew (⟨1, 0, 0⟩ : Vector K) (⟨0, 0, 1⟩ : Vector K)
  · simpa [bilinear, Matrix3.transpose, Matrix3.neg, Matrix3.mul,
      Matrix3.rowMul, Vector.dot, rt_tr, st_ts, sr_rs, mul_comm,
      add_comm, add_left_comm, add_assoc] using
      skew (⟨0, 1, 0⟩ : Vector K) (⟨0, 0, 1⟩ : Vector K)
  · simpa [bilinear, Matrix3.transpose, Matrix3.neg, Matrix3.mul,
      Matrix3.rowMul, Vector.dot, rt_tr, st_ts, sr_rs, mul_comm,
      add_comm, add_left_comm, add_assoc] using
      skew (⟨0, 0, 1⟩ : Vector K) (⟨0, 0, 1⟩ : Vector K)

/-- One scalar and three vector coordinates for the even Clifford algebra of
the displayed form. -/
@[ext]
structure EvenClifford (form : TernaryForm K) where
  scalar : K
  vector : Vector K

namespace EvenClifford

/-- Multiplicative identity. -/
def identity (form : TernaryForm K) : form.EvenClifford :=
  ⟨1, Vector.zero⟩

/-- A displayed vector embedded as a pure Clifford element. -/
def ofVector (form : TernaryForm K) (vector : Vector K) :
    form.EvenClifford :=
  ⟨0, vector⟩

/-- Clifford conjugation. -/
def conjugate {form : TernaryForm K} (value : form.EvenClifford) :
    form.EvenClifford :=
  ⟨value.scalar, Vector.neg value.vector⟩

/-- Reduced norm in the determinant-scaled vector convention. -/
def norm {form : TernaryForm K} (value : form.EvenClifford) : K :=
  value.scalar ^ 2 + form.determinant * form.quadrance value.vector

/-- Coordinatewise homogeneous rescaling. -/
def scale {form : TernaryForm K} (factor : K)
    (value : form.EvenClifford) : form.EvenClifford :=
  ⟨factor * value.scalar, Vector.scale factor value.vector⟩

@[simp] theorem one_scale {form : TernaryForm K}
    (value : form.EvenClifford) : scale 1 value = value := by
  apply EvenClifford.ext
  · unfold scale
    ring1
  · exact Vector.one_scale value.vector

theorem scale_scale {form : TernaryForm K} (first second : K)
    (value : form.EvenClifford) :
    scale first (scale second value) = scale (first * second) value := by
  apply EvenClifford.ext
  · unfold scale
    ring1
  · unfold scale
    rw [Vector.scale_scale]

theorem norm_scale {form : TernaryForm K} (factor : K)
    (value : form.EvenClifford) :
    norm (scale factor value) = factor ^ 2 * norm value := by
  unfold norm scale
  rw [form.quadrance_scale]
  ring1

theorem norm_conjugate {form : TernaryForm K}
    (value : form.EvenClifford) : norm value.conjugate = norm value := by
  unfold norm conjugate quadrance bilinear Matrix3.rowMul Vector.dot Vector.neg
  ring1

@[simp] theorem norm_identity (form : TernaryForm K) :
    norm (identity form) = 1 := by
  unfold norm identity
  rw [form.quadrance_zero]
  ring1

/-- Scalar coordinate of the even Clifford product. -/
def productScalar (form : TernaryForm K) (leftScalar rightScalar : K)
    (leftVector rightVector : Vector K) : K :=
  leftScalar * rightScalar -
    form.determinant * form.bilinear leftVector rightVector

/-- Vector coordinate of the even Clifford product. -/
def productVector (form : TernaryForm K) (leftScalar rightScalar : K)
    (leftVector rightVector : Vector K) : Vector K :=
  Vector.sub
    (Vector.add
      (Vector.scale leftScalar rightVector)
      (Vector.scale rightScalar leftVector))
    (form.cliffordCross leftVector rightVector)

/-- Explicit even Clifford multiplication. -/
def mul {form : TernaryForm K} (left right : form.EvenClifford) :
    form.EvenClifford :=
  ⟨productScalar form left.scalar right.scalar left.vector right.vector,
    productVector form left.scalar right.scalar left.vector right.vector⟩

/-- The representative product is bilinear under independent homogeneous
rescalings. -/
theorem mul_scale_both {form : TernaryForm K}
    (leftFactor rightFactor : K) (left right : form.EvenClifford) :
    mul (scale leftFactor left) (scale rightFactor right) =
      scale (leftFactor * rightFactor) (mul left right) := by
  apply EvenClifford.ext
  · simp only [mul, productScalar, scale]
    rw [form.bilinear_scale_left, form.bilinear_scale_right]
    ring1
  · simp only [mul, productVector, scale]
    rw [form.cliffordCross_scale_left, form.cliffordCross_scale_right]
    ext <;> unfold Vector.add Vector.sub Vector.scale <;> ring1

theorem mul_scale_left {form : TernaryForm K} (factor : K)
    (left right : form.EvenClifford) :
    mul (scale factor left) right = scale factor (mul left right) := by
  calc
    mul (scale factor left) right =
        mul (scale factor left) (scale 1 right) := by rw [one_scale]
    _ = scale (factor * 1) (mul left right) :=
      mul_scale_both factor 1 left right
    _ = scale factor (mul left right) := by rw [mul_one]

theorem mul_scale_right {form : TernaryForm K} (factor : K)
    (left right : form.EvenClifford) :
    mul left (scale factor right) = scale factor (mul left right) := by
  calc
    mul left (scale factor right) =
        mul (scale 1 left) (scale factor right) := by rw [one_scale]
    _ = scale (1 * factor) (mul left right) :=
      mul_scale_both 1 factor left right
    _ = scale factor (mul left right) := by rw [one_mul]

theorem ofVector_scale (form : TernaryForm K) (factor : K)
    (vector : Vector K) :
    ofVector form (Vector.scale factor vector) =
      scale factor (ofVector form vector) := by
  apply EvenClifford.ext
  · unfold ofVector scale
    ring1
  · rfl

/-- Cancel a displayed nonzero homogeneous factor from even Clifford
coordinates. -/
theorem eq_of_scale_eq_scale {form : TernaryForm K} (factor : K)
    (factorNonzero : factor ≠ 0) {left right : form.EvenClifford}
    (equal : scale factor left = scale factor right) : left = right := by
  apply EvenClifford.ext
  · apply scalar_eq_of_nonzero_mul_eq_mul factorNonzero
    exact congrArg EvenClifford.scalar equal
  · apply Vector.ext
    · apply scalar_eq_of_nonzero_mul_eq_mul factorNonzero
      exact congrArg (fun value => value.vector.t) equal
    · apply scalar_eq_of_nonzero_mul_eq_mul factorNonzero
      exact congrArg (fun value => value.vector.r) equal
    · apply scalar_eq_of_nonzero_mul_eq_mul factorNonzero
      exact congrArg (fun value => value.vector.s) equal

theorem bilinear_productVector (form : TernaryForm K)
    (leftScalar rightScalar : K) (leftVector rightVector test : Vector K) :
    form.bilinear
        (productVector form leftScalar rightScalar leftVector rightVector)
        test =
      leftScalar * form.bilinear rightVector test +
        rightScalar * form.bilinear leftVector test -
          form.bilinear (form.cliffordCross leftVector rightVector) test := by
  unfold productVector
  rw [form.bilinear_sub_left, form.bilinear_add_left,
    form.bilinear_scale_left, form.bilinear_scale_left]

/-- The vector coordinate has the norm expansion needed for reduced-norm
multiplicativity. -/
theorem quadrance_productVector (form : TernaryForm K)
    (leftScalar rightScalar : K) (leftVector rightVector : Vector K) :
    form.quadrance
        (productVector form leftScalar rightScalar leftVector rightVector) =
      leftScalar ^ 2 * form.quadrance rightVector +
        2 * leftScalar * rightScalar * form.bilinear leftVector rightVector +
        rightScalar ^ 2 * form.quadrance leftVector +
        form.determinant *
          (form.quadrance leftVector * form.quadrance rightVector -
            form.bilinear leftVector rightVector ^ 2) := by
  have leftCross :
      form.bilinear leftVector
          (form.cliffordCross leftVector rightVector) = 0 := by
    rw [form.bilinear_comm]
    exact form.cliffordCross_perpendicular_left leftVector rightVector
  have rightCross :
      form.bilinear rightVector
          (form.cliffordCross leftVector rightVector) = 0 := by
    rw [form.bilinear_comm]
    exact form.cliffordCross_perpendicular_right leftVector rightVector
  unfold productVector
  rw [form.quadrance_sub, form.quadrance_add,
    form.quadrance_scale, form.quadrance_scale,
    form.bilinear_add_left, form.bilinear_scale_left,
    form.bilinear_scale_left, rightCross,
    form.bilinear_scale_left, leftCross,
    form.bilinear_scale_right,
    form.bilinear_comm rightVector leftVector,
    form.quadrance_cliffordCross]
  ring1

@[simp] theorem identity_mul {form : TernaryForm K}
    (value : form.EvenClifford) : mul (identity form) value = value := by
  apply EvenClifford.ext
  · unfold mul identity productScalar
    rw [form.bilinear_zero_left]
    ring1
  · ext <;> unfold mul identity productVector Vector.add Vector.sub Vector.scale
      Vector.zero cliffordCross Vector.cross Matrix3.rowMul <;> ring1

@[simp] theorem mul_identity {form : TernaryForm K}
    (value : form.EvenClifford) : mul value (identity form) = value := by
  apply EvenClifford.ext
  · unfold mul identity productScalar
    rw [form.bilinear_zero_right]
    ring1
  · ext <;> unfold mul identity productVector Vector.add Vector.sub Vector.scale
      Vector.zero cliffordCross Vector.cross Matrix3.rowMul <;> ring1

/-- Multiplication is associative by a direct finite coordinate proof. -/
theorem mul_assoc {form : TernaryForm K}
    (first second third : form.EvenClifford) :
    mul (mul first second) third = mul first (mul second third) := by
  apply EvenClifford.ext
  · simp only [mul, productScalar]
    rw [bilinear_productVector]
    rw [form.bilinear_comm first.vector
      (productVector form second.scalar third.scalar
        second.vector third.vector)]
    rw [bilinear_productVector]
    rw [form.bilinear_comm third.vector first.vector,
      form.bilinear_comm second.vector first.vector,
      form.bilinear_cliffordCross_cyclic,
      form.bilinear_comm first.vector
        (form.cliffordCross second.vector third.vector)]
    ring1
  · simp only [mul, productScalar, productVector]
    simp only [form.cliffordCross_sub_left,
      form.cliffordCross_sub_right,
      form.cliffordCross_add_left,
      form.cliffordCross_add_right,
      form.cliffordCross_scale_left,
      form.cliffordCross_scale_right]
    rw [form.cliffordCross_left_triple,
      form.cliffordCross_vector_triple]
    ext <;> unfold Vector.add Vector.sub Vector.scale <;> ring1

/-- Clifford conjugation reverses the explicit product. -/
theorem conjugate_mul_reverse {form : TernaryForm K}
    (left right : form.EvenClifford) :
    (mul left right).conjugate = mul right.conjugate left.conjugate := by
  apply EvenClifford.ext
  · simp only [conjugate, mul, productScalar]
    rw [form.bilinear_neg_left, form.bilinear_neg_right,
      form.bilinear_comm right.vector left.vector]
    ring1
  · simp only [conjugate, mul, productVector]
    rw [form.cliffordCross_neg_left, form.cliffordCross_neg_right,
      form.cliffordCross_anticomm right.vector left.vector]
    ext <;> unfold Vector.add Vector.sub Vector.scale Vector.neg <;> ring1

theorem mul_conjugate {form : TernaryForm K}
    (value : form.EvenClifford) :
    mul value value.conjugate =
      ⟨value.norm, Vector.zero⟩ := by
  apply EvenClifford.ext
  · unfold mul productScalar conjugate norm quadrance bilinear
      Matrix3.rowMul Vector.dot Vector.neg
    ring1
  · ext <;> unfold mul productVector conjugate cliffordCross Matrix3.rowMul
      Vector.cross Vector.add Vector.sub Vector.scale Vector.neg Vector.zero <;>
      ring1

theorem conjugate_mul {form : TernaryForm K}
    (value : form.EvenClifford) :
    mul value.conjugate value =
      ⟨value.norm, Vector.zero⟩ := by
  apply EvenClifford.ext
  · unfold mul productScalar conjugate norm quadrance bilinear
      Matrix3.rowMul Vector.dot Vector.neg
    ring1
  · ext <;> unfold mul productVector conjugate cliffordCross Matrix3.rowMul
      Vector.cross Vector.add Vector.sub Vector.scale Vector.neg Vector.zero <;>
      ring1

theorem mul_conjugate_eq_scale_identity {form : TernaryForm K}
    (value : form.EvenClifford) :
    mul value value.conjugate = scale value.norm (identity form) := by
  rw [mul_conjugate]
  apply EvenClifford.ext
  · unfold scale identity
    ring1
  · ext <;> unfold scale identity Vector.scale Vector.zero <;> ring1

theorem conjugate_mul_eq_scale_identity {form : TernaryForm K}
    (value : form.EvenClifford) :
    mul value.conjugate value = scale value.norm (identity form) := by
  rw [conjugate_mul]
  apply EvenClifford.ext
  · unfold scale identity
    ring1
  · ext <;> unfold scale identity Vector.scale Vector.zero <;> ring1

/-- Executable inverse of a representative with nonzero reduced norm. -/
def inverse {form : TernaryForm K} (value : form.EvenClifford)
    (_normNonzero : value.norm ≠ 0) : form.EvenClifford :=
  scale value.norm⁻¹ value.conjugate

@[simp] theorem mul_inverse {form : TernaryForm K}
    (value : form.EvenClifford) (normNonzero : value.norm ≠ 0) :
    mul value (inverse value normNonzero) = identity form := by
  have cancel := RFAP.ExplicitField.mul_inv_cancel value.norm normNonzero
  have reverseCancel : value.norm⁻¹ * value.norm = 1 := by
    calc
      value.norm⁻¹ * value.norm = value.norm * value.norm⁻¹ := by ring1
      _ = 1 := cancel
  calc
    mul value (inverse value normNonzero) =
        mul (scale 1 value) (scale value.norm⁻¹ value.conjugate) := by
      rw [one_scale]
      rfl
    _ = scale (1 * value.norm⁻¹) (mul value value.conjugate) :=
      mul_scale_both 1 value.norm⁻¹ value value.conjugate
    _ = scale value.norm⁻¹
        (scale value.norm (identity form)) := by
      rw [one_mul, mul_conjugate_eq_scale_identity]
    _ = scale (value.norm⁻¹ * value.norm) (identity form) := by
      rw [scale_scale]
    _ = identity form := by rw [reverseCancel, one_scale]

@[simp] theorem inverse_mul {form : TernaryForm K}
    (value : form.EvenClifford) (normNonzero : value.norm ≠ 0) :
    mul (inverse value normNonzero) value = identity form := by
  have cancel := RFAP.ExplicitField.mul_inv_cancel value.norm normNonzero
  have reverseCancel : value.norm⁻¹ * value.norm = 1 := by
    calc
      value.norm⁻¹ * value.norm = value.norm * value.norm⁻¹ := by ring1
      _ = 1 := cancel
  calc
    mul (inverse value normNonzero) value =
        mul (scale value.norm⁻¹ value.conjugate) (scale 1 value) := by
      rw [one_scale]
      rfl
    _ = scale (value.norm⁻¹ * 1) (mul value.conjugate value) :=
      mul_scale_both value.norm⁻¹ 1 value.conjugate value
    _ = scale value.norm⁻¹
        (scale value.norm (identity form)) := by
      rw [mul_one, conjugate_mul_eq_scale_identity]
    _ = scale (value.norm⁻¹ * value.norm) (identity form) := by
      rw [scale_scale]
    _ = identity form := by rw [reverseCancel, one_scale]

/-- The reduced norm is multiplicative. -/
theorem norm_mul {form : TernaryForm K}
    (left right : form.EvenClifford) :
    norm (mul left right) = norm left * norm right := by
  simp only [norm, mul, productScalar]
  rw [quadrance_productVector]
  ring1

/-- Denominator-cleared action of an even Clifford representative on a
displayed vector. -/
def actionNumerator {form : TernaryForm K} (value : form.EvenClifford)
    (vector : Vector K) : Vector K :=
  Vector.add
    (Vector.add
      (Vector.scale
        (value.scalar ^ 2 -
          form.determinant * form.quadrance value.vector)
        vector)
      (Vector.scale
        (2 * form.determinant * form.bilinear vector value.vector)
        value.vector))
    (Vector.scale (-2 * value.scalar)
      (form.cliffordCross vector value.vector))

/-- The denominator-cleared action is Clifford conjugation of a pure vector,
with no quotient or chosen basis. -/
theorem conjugate_mul_ofVector_mul {form : TernaryForm K}
    (value : form.EvenClifford) (vector : Vector K) :
    mul (mul value.conjugate (ofVector form vector)) value =
      ofVector form (value.actionNumerator vector) := by
  apply EvenClifford.ext
  · simp only [mul, conjugate, ofVector, productScalar, productVector]
    rw [form.bilinear_neg_left, mul_zero,
      Vector.zero_scale, Vector.add_zero,
      form.cliffordCross_neg_left,
      form.bilinear_sub_left, form.bilinear_scale_left,
      form.bilinear_neg_left,
      form.bilinear_comm vector value.vector]
    have crossPerpendicular :=
      form.cliffordCross_perpendicular_left value.vector vector
    unfold Perpendicular at crossPerpendicular
    rw [crossPerpendicular]
    ring1
  · simp only [mul, conjugate, ofVector, productScalar, productVector]
    rw [form.bilinear_neg_left, mul_zero,
      Vector.zero_scale, Vector.add_zero,
      form.cliffordCross_neg_left,
      form.cliffordCross_sub_left,
      form.cliffordCross_scale_left,
      form.cliffordCross_neg_left,
      form.cliffordCross_left_triple,
      form.bilinear_comm value.vector vector,
      form.cliffordCross_anticomm value.vector vector]
    ext <;> unfold actionNumerator Vector.add Vector.sub Vector.scale
      Vector.neg quadrance <;> ring1

/-- The denominator-cleared action respects Clifford multiplication.  The
order agrees with row-vector matrix multiplication: `left` acts first. -/
theorem actionNumerator_mul {form : TernaryForm K}
    (left right : form.EvenClifford) (vector : Vector K) :
    (mul left right).actionNumerator vector =
      right.actionNumerator (left.actionNumerator vector) := by
  have pureEquality :
      ofVector form ((mul left right).actionNumerator vector) =
        ofVector form
          (right.actionNumerator (left.actionNumerator vector)) := by
    calc
      ofVector form ((mul left right).actionNumerator vector) =
          mul
            (mul (mul left right).conjugate (ofVector form vector))
            (mul left right) :=
        (conjugate_mul_ofVector_mul (mul left right) vector).symm
      _ = mul
          (mul (mul right.conjugate left.conjugate)
            (ofVector form vector))
          (mul left right) := by
        rw [conjugate_mul_reverse]
      _ = mul
          (mul right.conjugate
            (mul (mul left.conjugate (ofVector form vector)) left))
          right := by
        rw [mul_assoc right.conjugate left.conjugate,
          ← mul_assoc
            (mul right.conjugate
              (mul left.conjugate (ofVector form vector)))
            left right,
          mul_assoc right.conjugate
            (mul left.conjugate (ofVector form vector)) left]
      _ = mul
          (mul right.conjugate
            (ofVector form (left.actionNumerator vector)))
          right := by
        rw [conjugate_mul_ofVector_mul]
      _ = ofVector form
          (right.actionNumerator (left.actionNumerator vector)) :=
        conjugate_mul_ofVector_mul right (left.actionNumerator vector)
  exact congrArg EvenClifford.vector pureEquality

theorem actionNumerator_scale_vector {form : TernaryForm K}
    (value : form.EvenClifford) (factor : K) (vector : Vector K) :
    value.actionNumerator (Vector.scale factor vector) =
      Vector.scale factor (value.actionNumerator vector) := by
  unfold actionNumerator
  rw [form.bilinear_scale_left,
    form.cliffordCross_scale_left]
  ext <;> unfold Vector.add Vector.scale <;> ring1

/-- Displayed matrix of the denominator-cleared Clifford action. -/
def actionNumeratorMatrix {form : TernaryForm K}
    (value : form.EvenClifford) : Matrix3 K :=
  Matrix3.add
    (Matrix3.add
      (Matrix3.scale
        (value.scalar ^ 2 -
          form.determinant * form.quadrance value.vector)
        Matrix3.identity)
      (Matrix3.scale (2 * form.determinant)
        (Matrix3.outer (form.dual value.vector) value.vector)))
    (Matrix3.scale (2 * value.scalar)
      (form.actionSkew value.vector))

theorem rowMul_actionNumeratorMatrix {form : TernaryForm K}
    (value : form.EvenClifford) (vector : Vector K) :
    Matrix3.rowMul vector value.actionNumeratorMatrix =
      value.actionNumerator vector := by
  unfold actionNumeratorMatrix actionNumerator
  rw [Matrix3.rowMul_add, Matrix3.rowMul_add,
    Matrix3.rowMul_scale, Matrix3.rowMul_identity,
    Matrix3.rowMul_scale, Matrix3.rowMul_outer,
    ← form.bilinear_eq_dot_dual,
    Matrix3.rowMul_scale, form.rowMul_actionSkew]
  change Vector.add
    (Vector.add
      (Vector.scale
        (value.scalar ^ 2 -
          form.determinant * form.quadrance value.vector) vector)
      (Vector.scale (2 * form.determinant)
        (Vector.scale (form.bilinear vector value.vector) value.vector)))
    (Vector.scale (2 * value.scalar)
      (form.cliffordCross value.vector vector)) = _
  rw [form.cliffordCross_anticomm value.vector vector]
  ext <;> unfold Vector.add Vector.scale Vector.neg <;> ring1

/-- The action numerator is a quadratic polynomial in its relative skew
matrix. -/
theorem actionNumeratorMatrix_eq_quadratic {form : TernaryForm K}
    (value : form.EvenClifford) :
    value.actionNumeratorMatrix =
      Matrix3.add
        (Matrix3.add
          (Matrix3.scale value.norm Matrix3.identity)
          (Matrix3.scale (2 * value.scalar)
            (form.actionSkew value.vector)))
        (Matrix3.scale 2
          (Matrix3.mul (form.actionSkew value.vector)
            (form.actionSkew value.vector))) := by
  rw [form.actionSkew_square]
  ext <;> unfold actionNumeratorMatrix norm Matrix3.add Matrix3.sub
    Matrix3.scale Matrix3.identity <;> ring1

/-- Orientation calculation for the denominator-cleared action. -/
theorem determinant_actionNumeratorMatrix {form : TernaryForm K}
    (value : form.EvenClifford) :
    Matrix3.determinant value.actionNumeratorMatrix = value.norm ^ 3 := by
  rw [value.actionNumeratorMatrix_eq_quadratic,
    Matrix3.determinant_quadratic_polynomial,
    form.trace_actionSkew,
    form.principalTrace_actionSkew,
    form.determinant_actionSkew]
  unfold norm
  ring1

theorem actionNumerator_scale {form : TernaryForm K} (factor : K)
    (value : form.EvenClifford) (vector : Vector K) :
    actionNumerator (scale factor value) vector =
      Vector.scale (factor ^ 2) (actionNumerator value vector) := by
  unfold actionNumerator scale
  rw [form.quadrance_scale, form.bilinear_scale_right,
    form.cliffordCross_scale_right]
  ext <;> unfold Vector.add Vector.scale <;> ring1

@[simp] theorem actionNumerator_identity (form : TernaryForm K)
    (vector : Vector K) :
    actionNumerator (identity form) vector = vector := by
  ext <;> unfold actionNumerator identity Vector.add Vector.scale Vector.zero
    quadrance bilinear cliffordCross Matrix3.rowMul Vector.dot Vector.cross <;>
    ring1

/-- The denominator-cleared Clifford action scales quadrance by the square of
the reduced norm. -/
theorem quadrance_actionNumerator {form : TernaryForm K}
    (value : form.EvenClifford) (vector : Vector K) :
    form.quadrance (actionNumerator value vector) =
      value.norm ^ 2 * form.quadrance vector := by
  have vectorCross :
      form.bilinear vector
          (form.cliffordCross vector value.vector) = 0 := by
    rw [form.bilinear_comm]
    exact form.cliffordCross_perpendicular_left vector value.vector
  have valueCross :
      form.bilinear value.vector
          (form.cliffordCross vector value.vector) = 0 := by
    rw [form.bilinear_comm]
    exact form.cliffordCross_perpendicular_right vector value.vector
  have mixedCross :
      form.bilinear
          (Vector.add
            (Vector.scale
              (value.scalar ^ 2 -
                form.determinant * form.quadrance value.vector)
              vector)
            (Vector.scale
              (2 * form.determinant *
                form.bilinear vector value.vector)
              value.vector))
          (Vector.scale (-2 * value.scalar)
            (form.cliffordCross vector value.vector)) = 0 := by
    rw [form.bilinear_add_left, form.bilinear_scale_left,
      form.bilinear_scale_right, vectorCross,
      form.bilinear_scale_left, form.bilinear_scale_right, valueCross]
    ring1
  have mainQuadrance :
      form.quadrance
          (Vector.add
            (Vector.scale
              (value.scalar ^ 2 -
                form.determinant * form.quadrance value.vector)
              vector)
            (Vector.scale
              (2 * form.determinant *
                form.bilinear vector value.vector)
              value.vector)) =
        (value.scalar ^ 2 -
            form.determinant * form.quadrance value.vector) ^ 2 *
            form.quadrance vector +
          2 *
            (value.scalar ^ 2 -
              form.determinant * form.quadrance value.vector) *
            (2 * form.determinant *
              form.bilinear vector value.vector) *
            form.bilinear vector value.vector +
          (2 * form.determinant *
              form.bilinear vector value.vector) ^ 2 *
            form.quadrance value.vector := by
    rw [form.quadrance_add, form.quadrance_scale,
      form.quadrance_scale, form.bilinear_scale_left,
      form.bilinear_scale_right]
    ring1
  unfold actionNumerator
  rw [form.quadrance_add, mixedCross, mainQuadrance,
    form.quadrance_scale, form.quadrance_cliffordCross]
  unfold norm
  ring1

/-- The denominator-cleared action scales the full bilinear form by the square
of the reduced norm, without using polarization or a characteristic
assumption. -/
theorem bilinear_actionNumerator {form : TernaryForm K}
    (value : form.EvenClifford) (left right : Vector K) :
    form.bilinear (actionNumerator value left)
        (actionNumerator value right) =
      value.norm ^ 2 * form.bilinear left right := by
  have leftAxisCross :
      form.bilinear value.vector
          (form.cliffordCross right value.vector) = 0 := by
    rw [form.bilinear_comm]
    exact form.cliffordCross_perpendicular_right right value.vector
  have rightAxisCross :
      form.bilinear (form.cliffordCross left value.vector)
          value.vector = 0 :=
    form.cliffordCross_perpendicular_right left value.vector
  have core :
      form.bilinear
          (Vector.add
            (Vector.scale
              (value.scalar ^ 2 -
                form.determinant * form.quadrance value.vector)
              left)
            (Vector.scale
              (2 * form.determinant *
                form.bilinear left value.vector)
              value.vector))
          (Vector.add
            (Vector.scale
              (value.scalar ^ 2 -
                form.determinant * form.quadrance value.vector)
              right)
            (Vector.scale
              (2 * form.determinant *
                form.bilinear right value.vector)
              value.vector)) =
        (value.scalar ^ 2 -
            form.determinant * form.quadrance value.vector) ^ 2 *
            form.bilinear left right +
          4 * form.determinant * value.scalar ^ 2 *
            form.bilinear left value.vector *
            form.bilinear right value.vector := by
    rw [form.bilinear_add_left, form.bilinear_add_right,
      form.bilinear_add_right,
      form.bilinear_scale_left, form.bilinear_scale_right,
      form.bilinear_scale_left, form.bilinear_scale_right,
      form.bilinear_scale_left, form.bilinear_scale_right,
      form.bilinear_scale_left, form.bilinear_scale_right]
    rw [form.bilinear_comm value.vector right]
    unfold quadrance
    ring1
  have mixed :
      form.bilinear
          (Vector.add
            (Vector.scale
              (value.scalar ^ 2 -
                form.determinant * form.quadrance value.vector)
              left)
            (Vector.scale
              (2 * form.determinant *
                form.bilinear left value.vector)
              value.vector))
          (Vector.scale (-2 * value.scalar)
            (form.cliffordCross right value.vector)) +
        form.bilinear
          (Vector.scale (-2 * value.scalar)
            (form.cliffordCross left value.vector))
          (Vector.add
            (Vector.scale
              (value.scalar ^ 2 -
                form.determinant * form.quadrance value.vector)
              right)
            (Vector.scale
              (2 * form.determinant *
                form.bilinear right value.vector)
              value.vector)) = 0 := by
    rw [form.bilinear_add_left, form.bilinear_add_right,
      form.bilinear_scale_left, form.bilinear_scale_right,
      form.bilinear_scale_left, form.bilinear_scale_right,
      form.bilinear_scale_left, form.bilinear_scale_right,
      form.bilinear_scale_left, form.bilinear_scale_right,
      leftAxisCross, rightAxisCross,
      form.bilinear_cliffordCross_swap left right value.vector]
    ring1
  have cross :
      form.bilinear
          (Vector.scale (-2 * value.scalar)
            (form.cliffordCross left value.vector))
          (Vector.scale (-2 * value.scalar)
            (form.cliffordCross right value.vector)) =
        4 * value.scalar ^ 2 * form.determinant *
          (form.bilinear left right * form.quadrance value.vector -
            form.bilinear left value.vector *
              form.bilinear right value.vector) := by
    rw [form.bilinear_scale_left, form.bilinear_scale_right,
      form.bilinear_cliffordCross_pair,
      form.bilinear_comm value.vector right]
    unfold quadrance
    ring1
  let leftCore := Vector.add
    (Vector.scale
      (value.scalar ^ 2 -
        form.determinant * form.quadrance value.vector) left)
    (Vector.scale
      (2 * form.determinant * form.bilinear left value.vector)
      value.vector)
  let rightCore := Vector.add
    (Vector.scale
      (value.scalar ^ 2 -
        form.determinant * form.quadrance value.vector) right)
    (Vector.scale
      (2 * form.determinant * form.bilinear right value.vector)
      value.vector)
  let leftCross := Vector.scale (-2 * value.scalar)
    (form.cliffordCross left value.vector)
  let rightCross := Vector.scale (-2 * value.scalar)
    (form.cliffordCross right value.vector)
  change form.bilinear leftCore rightCore = _ at core
  change form.bilinear leftCore rightCross +
    form.bilinear leftCross rightCore = 0 at mixed
  change form.bilinear leftCross rightCross = _ at cross
  change form.bilinear (Vector.add leftCore leftCross)
    (Vector.add rightCore rightCross) = _
  calc
    form.bilinear (Vector.add leftCore leftCross)
        (Vector.add rightCore rightCross) =
      (form.bilinear leftCore rightCore +
        form.bilinear leftCore rightCross) +
      (form.bilinear leftCross rightCore +
        form.bilinear leftCross rightCross) := by
      rw [form.bilinear_add_left,
        form.bilinear_add_right leftCore rightCore rightCross,
        form.bilinear_add_right leftCross rightCore rightCross]
    _ = form.bilinear leftCore rightCore +
        (form.bilinear leftCore rightCross +
          form.bilinear leftCross rightCore) +
        form.bilinear leftCross rightCross := by ring1
    _ = (value.scalar ^ 2 -
          form.determinant * form.quadrance value.vector) ^ 2 *
          form.bilinear left right +
        4 * form.determinant * value.scalar ^ 2 *
          form.bilinear left value.vector *
          form.bilinear right value.vector +
        0 +
        4 * value.scalar ^ 2 * form.determinant *
          (form.bilinear left right * form.quadrance value.vector -
            form.bilinear left value.vector *
              form.bilinear right value.vector) := by
      rw [core, mixed, cross]
    _ = value.norm ^ 2 * form.bilinear left right := by
      unfold norm
      ring1

end EvenClifford

/-- An even Clifford representative with a cached nonzero reduced norm. -/
@[ext]
structure NonNullEvenClifford (form : TernaryForm K)
    extends form.EvenClifford where
  normNonzero : toEvenClifford.norm ≠ 0

namespace NonNullEvenClifford

/-- Explicit homogeneous rescaling with its cached non-null certificate. -/
def scale {form : TernaryForm K} (factor : K) (factorNonzero : factor ≠ 0)
    (value : form.NonNullEvenClifford) : form.NonNullEvenClifford where
  toEvenClifford := EvenClifford.scale factor value.toEvenClifford
  normNonzero := by
    rw [EvenClifford.norm_scale]
    exact RFAP.ExplicitField.mul_ne_zero
      (by
        simpa only [pow_two] using
          RFAP.ExplicitField.mul_ne_zero factorNonzero factorNonzero)
      value.normNonzero

/-- Equality of represented projective Clifford points by an explicit
nonzero homogeneous scale. -/
def Equivalent {form : TernaryForm K}
    (left right : form.NonNullEvenClifford) : Prop :=
  ∃ factor : K, factor ≠ 0 ∧
    right.toEvenClifford = EvenClifford.scale factor left.toEvenClifford

theorem equivalent_refl {form : TernaryForm K}
    (value : form.NonNullEvenClifford) : value.Equivalent value := by
  exact ⟨1, form.one_ne_zero, (EvenClifford.one_scale _).symm⟩

theorem equivalent_symm {form : TernaryForm K}
    {left right : form.NonNullEvenClifford}
    (equivalent : left.Equivalent right) : right.Equivalent left := by
  rcases equivalent with ⟨factor, factorNonzero, rightValue⟩
  have cancel := RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  have reverseCancel : factor⁻¹ * factor = 1 := by
    calc
      factor⁻¹ * factor = factor * factor⁻¹ := by ring1
      _ = 1 := cancel
  refine ⟨factor⁻¹, RFAP.ExplicitField.inv_ne_zero factorNonzero, ?_⟩
  calc
    left.toEvenClifford =
        EvenClifford.scale 1 left.toEvenClifford := by
      rw [EvenClifford.one_scale]
    _ = EvenClifford.scale (factor⁻¹ * factor) left.toEvenClifford := by
      rw [reverseCancel]
    _ = EvenClifford.scale factor⁻¹
        (EvenClifford.scale factor left.toEvenClifford) := by
      rw [EvenClifford.scale_scale]
    _ = EvenClifford.scale factor⁻¹ right.toEvenClifford := by
      rw [← rightValue]

theorem equivalent_trans {form : TernaryForm K}
    {first second third : form.NonNullEvenClifford}
    (firstSecond : first.Equivalent second)
    (secondThird : second.Equivalent third) : first.Equivalent third := by
  rcases firstSecond with
    ⟨firstFactor, firstFactorNonzero, secondValue⟩
  rcases secondThird with
    ⟨secondFactor, secondFactorNonzero, thirdValue⟩
  refine ⟨secondFactor * firstFactor,
    RFAP.ExplicitField.mul_ne_zero secondFactorNonzero firstFactorNonzero, ?_⟩
  calc
    third.toEvenClifford =
        EvenClifford.scale secondFactor second.toEvenClifford := thirdValue
    _ = EvenClifford.scale secondFactor
        (EvenClifford.scale firstFactor first.toEvenClifford) := by
      rw [secondValue]
    _ = EvenClifford.scale (secondFactor * firstFactor)
        first.toEvenClifford := EvenClifford.scale_scale _ _ _

theorem equivalent_scale {form : TernaryForm K} (factor : K)
    (factorNonzero : factor ≠ 0) (value : form.NonNullEvenClifford) :
    value.Equivalent (scale factor factorNonzero value) := by
  exact ⟨factor, factorNonzero, rfl⟩

/-- Total multiplication on representatives with nonzero reduced norm. -/
def mul {form : TernaryForm K} (left right : form.NonNullEvenClifford) :
    form.NonNullEvenClifford where
  toEvenClifford := EvenClifford.mul left.toEvenClifford right.toEvenClifford
  normNonzero := by
    rw [EvenClifford.norm_mul]
    exact RFAP.ExplicitField.mul_ne_zero left.normNonzero right.normNonzero

theorem mul_assoc {form : TernaryForm K}
    (first second third : form.NonNullEvenClifford) :
    mul (mul first second) third = mul first (mul second third) := by
  have raw := EvenClifford.mul_assoc first.toEvenClifford
    second.toEvenClifford third.toEvenClifford
  apply NonNullEvenClifford.ext
  · exact congrArg EvenClifford.scalar raw
  · exact congrArg EvenClifford.vector raw

theorem mul_respects_equivalent {form : TernaryForm K}
    {left left' right right' : form.NonNullEvenClifford}
    (leftEquivalent : left.Equivalent left')
    (rightEquivalent : right.Equivalent right') :
    (mul left right).Equivalent (mul left' right') := by
  rcases leftEquivalent with ⟨leftFactor, leftFactorNonzero, leftValue⟩
  rcases rightEquivalent with
    ⟨rightFactor, rightFactorNonzero, rightValue⟩
  refine ⟨leftFactor * rightFactor,
    RFAP.ExplicitField.mul_ne_zero leftFactorNonzero rightFactorNonzero, ?_⟩
  change EvenClifford.mul left'.toEvenClifford right'.toEvenClifford =
    EvenClifford.scale (leftFactor * rightFactor)
      (EvenClifford.mul left.toEvenClifford right.toEvenClifford)
  rw [leftValue, rightValue, EvenClifford.mul_scale_both]

/-- The non-null Clifford identity representative. -/
def identity (form : TernaryForm K) : form.NonNullEvenClifford where
  toEvenClifford := EvenClifford.identity form
  normNonzero := by
    rw [EvenClifford.norm_identity]
    exact form.one_ne_zero

@[simp] theorem identity_mul {form : TernaryForm K}
    (value : form.NonNullEvenClifford) : mul (identity form) value = value := by
  have raw := EvenClifford.identity_mul value.toEvenClifford
  apply NonNullEvenClifford.ext
  · exact congrArg EvenClifford.scalar raw
  · exact congrArg EvenClifford.vector raw

@[simp] theorem mul_identity {form : TernaryForm K}
    (value : form.NonNullEvenClifford) : mul value (identity form) = value := by
  have raw := EvenClifford.mul_identity value.toEvenClifford
  apply NonNullEvenClifford.ext
  · exact congrArg EvenClifford.scalar raw
  · exact congrArg EvenClifford.vector raw

/-- Conjugation preserves the non-null reduced-norm certificate. -/
def conjugate {form : TernaryForm K} (value : form.NonNullEvenClifford) :
    form.NonNullEvenClifford where
  toEvenClifford := value.toEvenClifford.conjugate
  normNonzero := by
    rw [EvenClifford.norm_conjugate]
    exact value.normNonzero

theorem mul_conjugate_equivalent_identity {form : TernaryForm K}
    (value : form.NonNullEvenClifford) :
    (mul value value.conjugate).Equivalent (identity form) := by
  apply equivalent_symm
  refine ⟨value.toEvenClifford.norm, value.normNonzero, ?_⟩
  exact EvenClifford.mul_conjugate_eq_scale_identity value.toEvenClifford

theorem conjugate_mul_equivalent_identity {form : TernaryForm K}
    (value : form.NonNullEvenClifford) :
    (mul value.conjugate value).Equivalent (identity form) := by
  apply equivalent_symm
  refine ⟨value.toEvenClifford.norm, value.normNonzero, ?_⟩
  exact EvenClifford.conjugate_mul_eq_scale_identity value.toEvenClifford

/-- Normalized action of a nonzero-norm Clifford representative. -/
def action {form : TernaryForm K} (value : form.NonNullEvenClifford)
    (vector : Vector K) : Vector K :=
  Vector.scale value.toEvenClifford.norm⁻¹
    (EvenClifford.actionNumerator value.toEvenClifford vector)

/-- Displayed matrix of the normalized Clifford action. -/
def actionMatrix {form : TernaryForm K}
    (value : form.NonNullEvenClifford) : Matrix3 K :=
  Matrix3.scale value.toEvenClifford.norm⁻¹
    value.toEvenClifford.actionNumeratorMatrix

/-- The normalized Clifford action is orientation preserving. -/
theorem determinant_actionMatrix {form : TernaryForm K}
    (value : form.NonNullEvenClifford) :
    Matrix3.determinant value.actionMatrix = 1 := by
  have cancel := RFAP.ExplicitField.mul_inv_cancel
    value.toEvenClifford.norm value.normNonzero
  have reverseCancel :
      value.toEvenClifford.norm⁻¹ * value.toEvenClifford.norm = 1 := by
    calc
      value.toEvenClifford.norm⁻¹ * value.toEvenClifford.norm =
          value.toEvenClifford.norm * value.toEvenClifford.norm⁻¹ := by
        ring1
      _ = 1 := cancel
  have cubeCancel :
      value.toEvenClifford.norm⁻¹ ^ 3 *
          value.toEvenClifford.norm ^ 3 = 1 := by
    calc
      value.toEvenClifford.norm⁻¹ ^ 3 *
          value.toEvenClifford.norm ^ 3 =
        (value.toEvenClifford.norm⁻¹ *
          value.toEvenClifford.norm) ^ 3 := by
        ring1
      _ = 1 := by rw [reverseCancel]; ring1
  unfold actionMatrix
  rw [Matrix3.determinant_scale,
    EvenClifford.determinant_actionNumeratorMatrix, cubeCancel]

theorem rowMul_actionMatrix {form : TernaryForm K}
    (value : form.NonNullEvenClifford) (vector : Vector K) :
    Matrix3.rowMul vector value.actionMatrix = value.action vector := by
  unfold actionMatrix action
  rw [Matrix3.rowMul_scale,
    EvenClifford.rowMul_actionNumeratorMatrix]

theorem quadrance_action {form : TernaryForm K}
    (value : form.NonNullEvenClifford) (vector : Vector K) :
    form.quadrance (value.action vector) = form.quadrance vector := by
  have cancel := RFAP.ExplicitField.mul_inv_cancel
    value.toEvenClifford.norm value.normNonzero
  have reverseCancel :
      value.toEvenClifford.norm⁻¹ * value.toEvenClifford.norm = 1 := by
    calc
      value.toEvenClifford.norm⁻¹ * value.toEvenClifford.norm =
          value.toEvenClifford.norm * value.toEvenClifford.norm⁻¹ := by
        ring1
      _ = 1 := cancel
  unfold action
  rw [form.quadrance_scale, EvenClifford.quadrance_actionNumerator]
  calc
    value.toEvenClifford.norm⁻¹ ^ 2 *
        (value.toEvenClifford.norm ^ 2 * form.quadrance vector) =
      (value.toEvenClifford.norm⁻¹ *
        value.toEvenClifford.norm) ^ 2 * form.quadrance vector := by
      ring1
    _ = form.quadrance vector := by rw [reverseCancel]; ring1

theorem bilinear_action {form : TernaryForm K}
    (value : form.NonNullEvenClifford) (left right : Vector K) :
    form.bilinear (value.action left) (value.action right) =
      form.bilinear left right := by
  have cancel := RFAP.ExplicitField.mul_inv_cancel
    value.toEvenClifford.norm value.normNonzero
  have reverseCancel :
      value.toEvenClifford.norm⁻¹ * value.toEvenClifford.norm = 1 := by
    calc
      value.toEvenClifford.norm⁻¹ * value.toEvenClifford.norm =
          value.toEvenClifford.norm * value.toEvenClifford.norm⁻¹ := by
        ring1
      _ = 1 := cancel
  unfold action
  rw [form.bilinear_scale_left, form.bilinear_scale_right,
    EvenClifford.bilinear_actionNumerator]
  calc
    value.toEvenClifford.norm⁻¹ *
        (value.toEvenClifford.norm⁻¹ *
          (value.toEvenClifford.norm ^ 2 * form.bilinear left right)) =
      (value.toEvenClifford.norm⁻¹ *
        value.toEvenClifford.norm) ^ 2 * form.bilinear left right := by
      ring1
    _ = form.bilinear left right := by rw [reverseCancel]; ring1

theorem actionMatrix_preservesMatrix {form : TernaryForm K}
    (value : form.NonNullEvenClifford) :
    Matrix3.mul (Matrix3.mul value.actionMatrix form.matrix)
      (Matrix3.transpose value.actionMatrix) = form.matrix := by
  apply form.preservesMatrix_of_bilinear_rowMul
  intro left right
  rw [value.rowMul_actionMatrix, value.rowMul_actionMatrix]
  exact value.bilinear_action left right

/-- Cached inverse matrix obtained from the form matrix, the transpose action,
and the cached inverse form matrix. -/
def actionInverseMatrix {form : TernaryForm K}
    (value : form.NonNullEvenClifford) : Matrix3 K :=
  Matrix3.mul
    (Matrix3.mul form.matrix (Matrix3.transpose value.actionMatrix))
    form.inverse

theorem actionMatrix_mul_actionInverseMatrix {form : TernaryForm K}
    (value : form.NonNullEvenClifford) :
    Matrix3.mul value.actionMatrix value.actionInverseMatrix =
      Matrix3.identity := by
  unfold actionInverseMatrix
  calc
    Matrix3.mul value.actionMatrix
        (Matrix3.mul
          (Matrix3.mul form.matrix
            (Matrix3.transpose value.actionMatrix))
          form.inverse) =
      Matrix3.mul value.actionMatrix
        (Matrix3.mul form.matrix
          (Matrix3.mul (Matrix3.transpose value.actionMatrix)
            form.inverse)) := by
      rw [Matrix3.mul_assoc]
    _ = Matrix3.mul
        (Matrix3.mul value.actionMatrix form.matrix)
        (Matrix3.mul (Matrix3.transpose value.actionMatrix)
          form.inverse) := by
      rw [Matrix3.mul_assoc]
    _ =
      Matrix3.mul
        (Matrix3.mul
          (Matrix3.mul value.actionMatrix form.matrix)
          (Matrix3.transpose value.actionMatrix))
        form.inverse := by
      exact (Matrix3.mul_assoc
        (Matrix3.mul value.actionMatrix form.matrix)
        (Matrix3.transpose value.actionMatrix) form.inverse).symm
    _ = Matrix3.mul form.matrix form.inverse := by
      rw [value.actionMatrix_preservesMatrix]
    _ = Matrix3.identity := form.matrix_mul_inverse

theorem actionInverseMatrix_mul_actionMatrix {form : TernaryForm K}
    (value : form.NonNullEvenClifford) :
    Matrix3.mul value.actionInverseMatrix value.actionMatrix =
      Matrix3.identity :=
  Matrix3.inverse_mul_of_mul_eq_identity form.one_ne_zero
    value.actionMatrix_mul_actionInverseMatrix

/-- The normalized Clifford action packaged with an executable inverse and
the full form-matrix preservation certificate. -/
def actionIsometry {form : TernaryForm K}
    (value : form.NonNullEvenClifford) : form.Isometry where
  matrix := value.actionMatrix
  inverseMatrix := value.actionInverseMatrix
  matrix_mul_inverse := value.actionMatrix_mul_actionInverseMatrix
  inverse_mul_matrix := value.actionInverseMatrix_mul_actionMatrix
  preservesMatrix := value.actionMatrix_preservesMatrix

/-- The normalized Clifford action packaged as an executable member of the
special orthogonal group of the ternary form. -/
def actionRotation {form : TernaryForm K}
    (value : form.NonNullEvenClifford) : form.SpecialOrthogonal where
  toIsometry := value.actionIsometry
  determinantOne := value.determinant_actionMatrix

theorem actionIsometry_act {form : TernaryForm K}
    (value : form.NonNullEvenClifford) (vector : Vector K) :
    value.actionIsometry.act vector = value.action vector := by
  unfold actionIsometry TernaryForm.Isometry.act
  exact value.rowMul_actionMatrix vector

theorem actionRotation_act {form : TernaryForm K}
    (value : form.NonNullEvenClifford) (vector : Vector K) :
    value.actionRotation.act vector = value.action vector := by
  change value.actionIsometry.act vector = value.action vector
  exact value.actionIsometry_act vector

private theorem inverse_product {left right : K}
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

/-- A non-null vector, embedded as a pure even Clifford representative.  Its
normalized action is the form-relative half turn about that vector. -/
def halfTurnValue (form : TernaryForm K) (axis : Vector K)
    (nonNull : form.quadrance axis ≠ 0) : form.NonNullEvenClifford where
  toEvenClifford := EvenClifford.ofVector form axis
  normNonzero := by
    have productNonzero := RFAP.ExplicitField.mul_ne_zero
      form.determinantNonzero nonNull
    intro normZero
    apply productNonzero
    calc
      form.determinant * form.quadrance axis =
          (0 : K) ^ 2 + form.determinant * form.quadrance axis := by ring1
      _ = 0 := normZero

@[simp] theorem halfTurnValue_norm (form : TernaryForm K)
    (axis : Vector K) (nonNull : form.quadrance axis ≠ 0) :
    (halfTurnValue form axis nonNull).toEvenClifford.norm =
      form.determinant * form.quadrance axis := by
  unfold halfTurnValue EvenClifford.ofVector EvenClifford.norm
  ring1

/-- The pure-vector Clifford sandwich is exactly the displayed half-turn
action, with the determinant factors cancelled constructively. -/
theorem halfTurnValue_action (form : TernaryForm K) (axis : Vector K)
    (nonNull : form.quadrance axis ≠ 0) (vector : Vector K) :
    (halfTurnValue form axis nonNull).action vector =
      Matrix3.rowMul vector (form.halfTurn axis nonNull) := by
  have determinantCancel := RFAP.ExplicitField.mul_inv_cancel
    form.determinant form.determinantNonzero
  have reverseDeterminantCancel :
      form.determinant⁻¹ * form.determinant = (1 : K) := by
    calc
      form.determinant⁻¹ * form.determinant =
          form.determinant * form.determinant⁻¹ := by ring1
      _ = 1 := determinantCancel
  have quadranceCancel := RFAP.ExplicitField.mul_inv_cancel
    (form.quadrance axis) nonNull
  have reverseQuadranceCancel :
      (form.quadrance axis)⁻¹ * form.quadrance axis = (1 : K) := by
    calc
      (form.quadrance axis)⁻¹ * form.quadrance axis =
          form.quadrance axis * (form.quadrance axis)⁻¹ := by ring1
      _ = 1 := quadranceCancel
  have vectorCoefficient :
      (form.determinant⁻¹ * (form.quadrance axis)⁻¹) *
          (-form.determinant * form.quadrance axis) = (-1 : K) := by
    calc
      (form.determinant⁻¹ * (form.quadrance axis)⁻¹) *
          (-form.determinant * form.quadrance axis) =
        -(form.determinant⁻¹ * form.determinant) *
          ((form.quadrance axis)⁻¹ * form.quadrance axis) := by ring1
      _ = -1 := by
        rw [reverseDeterminantCancel, reverseQuadranceCancel]
        ring1
  have axisCoefficient :
      (form.determinant⁻¹ * (form.quadrance axis)⁻¹) *
          (2 * form.determinant * form.bilinear vector axis) =
        2 * form.bilinear vector axis * (form.quadrance axis)⁻¹ := by
    calc
      (form.determinant⁻¹ * (form.quadrance axis)⁻¹) *
          (2 * form.determinant * form.bilinear vector axis) =
        (form.determinant⁻¹ * form.determinant) *
          (2 * form.bilinear vector axis * (form.quadrance axis)⁻¹) := by ring1
      _ = 2 * form.bilinear vector axis * (form.quadrance axis)⁻¹ := by
        rw [reverseDeterminantCancel, one_mul]
  unfold action
  rw [halfTurnValue_norm]
  change Vector.scale (form.determinant * form.quadrance axis)⁻¹
      (EvenClifford.actionNumerator (EvenClifford.ofVector form axis) vector) =
    Matrix3.rowMul vector (form.halfTurn axis nonNull)
  unfold EvenClifford.actionNumerator EvenClifford.ofVector
    TernaryForm.halfTurn
  rw [inverse_product form.determinantNonzero nonNull,
    Matrix3.rowMul_neg, form.rowMul_reflection]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  rw [show (0 : K) ^ 2 - form.determinant * form.quadrance axis =
      -form.determinant * form.quadrance axis by ring1,
    show (-2 : K) * 0 = 0 by ring1]
  change Vector.scale (form.determinant⁻¹ * (form.quadrance axis)⁻¹)
      (Vector.add
        (Vector.add
          (Vector.scale (-form.determinant * form.quadrance axis) vector)
          (Vector.scale
            (2 * form.determinant * form.bilinear vector axis) axis))
        (Vector.scale 0 (form.cliffordCross vector axis))) =
    Vector.neg
      (Vector.sub vector
        (Vector.scale
          (2 * form.bilinear vector axis * (form.quadrance axis)⁻¹) axis))
  rw [Vector.zero_scale, Vector.add_zero, Vector.scale_add,
    Vector.scale_scale, Vector.scale_scale,
    vectorCoefficient, axisCoefficient]
  ext <;> unfold Vector.add Vector.sub Vector.scale Vector.neg <;> ring1

theorem halfTurnValue_actionMatrix (form : TernaryForm K)
    (axis : Vector K) (nonNull : form.quadrance axis ≠ 0) :
    (halfTurnValue form axis nonNull).actionMatrix =
      form.halfTurn axis nonNull := by
  apply Matrix3.eq_of_rowMul_eq
  intro vector
  rw [rowMul_actionMatrix, halfTurnValue_action]

/-- The Clifford action contains every displayed form-relative half turn. -/
theorem halfTurnValue_actionRotation (form : TernaryForm K)
    (axis : Vector K) (nonNull : form.quadrance axis ≠ 0) :
    (halfTurnValue form axis nonNull).actionRotation =
      form.halfTurnRotation axis nonNull := by
  apply TernaryForm.SpecialOrthogonal.eq_of_matrix_eq
  exact halfTurnValue_actionMatrix form axis nonNull

/-- The normalized Clifford action is multiplicative.  With displayed row
vectors, the left representative acts first and the right one second. -/
theorem action_mul {form : TernaryForm K}
    (left right : form.NonNullEvenClifford) (vector : Vector K) :
    (mul left right).action vector =
      right.action (left.action vector) := by
  unfold action
  change
    Vector.scale
        (EvenClifford.norm
          (EvenClifford.mul left.toEvenClifford right.toEvenClifford))⁻¹
        (EvenClifford.actionNumerator
          (EvenClifford.mul left.toEvenClifford right.toEvenClifford)
          vector) =
      Vector.scale right.toEvenClifford.norm⁻¹
        (right.toEvenClifford.actionNumerator
          (Vector.scale left.toEvenClifford.norm⁻¹
            (left.toEvenClifford.actionNumerator vector)))
  rw [EvenClifford.norm_mul, EvenClifford.actionNumerator_mul,
    inverse_product left.normNonzero right.normNonzero,
    EvenClifford.actionNumerator_scale_vector,
    Vector.scale_scale]
  ext <;> unfold Vector.scale <;> ring1

/-- Matrix form of multiplicativity of the normalized Clifford action. -/
theorem actionMatrix_mul {form : TernaryForm K}
    (left right : form.NonNullEvenClifford) :
    (mul left right).actionMatrix =
      Matrix3.mul left.actionMatrix right.actionMatrix := by
  apply Matrix3.eq_of_rowMul_eq
  intro vector
  rw [rowMul_actionMatrix, ← Matrix3.rowMul_mul,
    rowMul_actionMatrix, rowMul_actionMatrix, action_mul]

/-- The Clifford action is a homomorphism into the displayed
special-orthogonal group. -/
theorem actionRotation_mul {form : TernaryForm K}
    (left right : form.NonNullEvenClifford) :
    (mul left right).actionRotation =
      TernaryForm.SpecialOrthogonal.mul left.actionRotation
        right.actionRotation := by
  apply TernaryForm.SpecialOrthogonal.eq_of_matrix_eq
  exact actionMatrix_mul left right

/-- Products of displayed form-relative half turns are computed by multiplying
their pure-vector Clifford representatives. -/
theorem halfTurnRotation_mul (form : TernaryForm K)
    (first second : Vector K)
    (firstNonNull : form.quadrance first ≠ 0)
    (secondNonNull : form.quadrance second ≠ 0) :
    TernaryForm.SpecialOrthogonal.mul
        (form.halfTurnRotation first firstNonNull)
        (form.halfTurnRotation second secondNonNull) =
      (mul (halfTurnValue form first firstNonNull)
        (halfTurnValue form second secondNonNull)).actionRotation := by
  calc
    TernaryForm.SpecialOrthogonal.mul
        (form.halfTurnRotation first firstNonNull)
        (form.halfTurnRotation second secondNonNull) =
      TernaryForm.SpecialOrthogonal.mul
        (halfTurnValue form first firstNonNull).actionRotation
        (halfTurnValue form second secondNonNull).actionRotation := by
          rw [halfTurnValue_actionRotation, halfTurnValue_actionRotation]
    _ = (mul (halfTurnValue form first firstNonNull)
        (halfTurnValue form second secondNonNull)).actionRotation :=
      (actionRotation_mul _ _).symm

/-- The normalized action is independent of a nonzero homogeneous rescaling
of its displayed Clifford representative. -/
theorem action_scale {form : TernaryForm K} (factor : K)
    (factorNonzero : factor ≠ 0) (value : form.NonNullEvenClifford)
    (vector : Vector K) :
    (scale factor factorNonzero value).action vector = value.action vector := by
  have squareNonzero : factor ^ 2 ≠ 0 := by
    simpa only [pow_two] using
      RFAP.ExplicitField.mul_ne_zero factorNonzero factorNonzero
  have squareCancel := RFAP.ExplicitField.mul_inv_cancel
    (factor ^ 2) squareNonzero
  have reverseSquareCancel : (factor ^ 2)⁻¹ * factor ^ 2 = 1 := by
    calc
      (factor ^ 2)⁻¹ * factor ^ 2 =
          factor ^ 2 * (factor ^ 2)⁻¹ := by ring1
      _ = 1 := squareCancel
  unfold action scale
  rw [EvenClifford.norm_scale,
    EvenClifford.actionNumerator_scale,
    inverse_product squareNonzero value.normNonzero,
    Vector.scale_scale]
  congr 1
  calc
    ((factor ^ 2)⁻¹ * value.toEvenClifford.norm⁻¹) * factor ^ 2 =
        ((factor ^ 2)⁻¹ * factor ^ 2) *
          value.toEvenClifford.norm⁻¹ := by ring1
    _ = value.toEvenClifford.norm⁻¹ := by
      rw [reverseSquareCancel, one_mul]

theorem actionMatrix_scale {form : TernaryForm K} (factor : K)
    (factorNonzero : factor ≠ 0) (value : form.NonNullEvenClifford) :
    (scale factor factorNonzero value).actionMatrix = value.actionMatrix := by
  apply Matrix3.eq_of_rowMul_eq
  intro vector
  rw [rowMul_actionMatrix, rowMul_actionMatrix, action_scale]

theorem action_respects_equivalent {form : TernaryForm K}
    {left right : form.NonNullEvenClifford}
    (equivalent : left.Equivalent right) (vector : Vector K) :
    left.action vector = right.action vector := by
  rcases equivalent with ⟨factor, factorNonzero, rightValue⟩
  have rightScaled : right = scale factor factorNonzero left := by
    apply NonNullEvenClifford.ext
    · exact congrArg EvenClifford.scalar rightValue
    · exact congrArg EvenClifford.vector rightValue
  rw [rightScaled, action_scale]

theorem actionMatrix_respects_equivalent {form : TernaryForm K}
    {left right : form.NonNullEvenClifford}
    (equivalent : left.Equivalent right) :
    left.actionMatrix = right.actionMatrix := by
  apply Matrix3.eq_of_rowMul_eq
  intro vector
  rw [left.rowMul_actionMatrix, right.rowMul_actionMatrix]
  exact left.action_respects_equivalent equivalent vector

@[simp] theorem action_identity (form : TernaryForm K)
    (vector : Vector K) : (identity form).action vector = vector := by
  unfold action identity
  rw [EvenClifford.norm_identity,
    EvenClifford.actionNumerator_identity]
  have oneInverse : (1 : K)⁻¹ = 1 := by
    have cancel := RFAP.ExplicitField.mul_inv_cancel (1 : K) form.one_ne_zero
    simpa only [one_mul] using cancel
  rw [oneInverse, Vector.one_scale]

@[simp] theorem actionMatrix_identity (form : TernaryForm K) :
    (identity form).actionMatrix = Matrix3.identity := by
  apply Matrix3.eq_of_rowMul_eq
  intro vector
  rw [rowMul_actionMatrix, action_identity, Matrix3.rowMul_identity]

@[simp] theorem actionRotation_identity (form : TernaryForm K) :
    (identity form).actionRotation =
      TernaryForm.SpecialOrthogonal.identity form := by
  apply TernaryForm.SpecialOrthogonal.eq_of_matrix_eq
  exact actionMatrix_identity form

/-- Equivalent projective Clifford representatives determine the same
special-orthogonal transformation. -/
theorem actionRotation_respects_equivalent {form : TernaryForm K}
    {left right : form.NonNullEvenClifford}
    (equivalent : left.Equivalent right) :
    left.actionRotation = right.actionRotation := by
  apply TernaryForm.SpecialOrthogonal.eq_of_matrix_eq
  exact left.actionMatrix_respects_equivalent equivalent

/-- If the normalized action fixes a displayed vector, its
denominator-cleared numerator is the reduced norm times that vector. -/
theorem actionNumerator_eq_scale_norm_of_action_eq
    {form : TernaryForm K} (value : form.NonNullEvenClifford)
    (vector : Vector K) (fixed : value.action vector = vector) :
    value.toEvenClifford.actionNumerator vector =
      Vector.scale value.toEvenClifford.norm vector := by
  have normCancel := RFAP.ExplicitField.mul_inv_cancel
    value.toEvenClifford.norm value.normNonzero
  calc
    value.toEvenClifford.actionNumerator vector =
        Vector.scale 1 (value.toEvenClifford.actionNumerator vector) :=
      (Vector.one_scale _).symm
    _ = Vector.scale
        (value.toEvenClifford.norm * value.toEvenClifford.norm⁻¹)
        (value.toEvenClifford.actionNumerator vector) := by
      rw [normCancel]
    _ = Vector.scale value.toEvenClifford.norm
        (Vector.scale value.toEvenClifford.norm⁻¹
          (value.toEvenClifford.actionNumerator vector)) :=
      (Vector.scale_scale _ _ _).symm
    _ = Vector.scale value.toEvenClifford.norm (value.action vector) := rfl
    _ = Vector.scale value.toEvenClifford.norm vector := by rw [fixed]

/-- A pure vector fixed by the normalized action commutes with the acting
Clifford representative. -/
theorem ofVector_mul_eq_mul_ofVector_of_action_eq
    {form : TernaryForm K} (value : form.NonNullEvenClifford)
    (vector : Vector K) (fixed : value.action vector = vector) :
    EvenClifford.mul (EvenClifford.ofVector form vector)
        value.toEvenClifford =
      EvenClifford.mul value.toEvenClifford
        (EvenClifford.ofVector form vector) := by
  let pure := EvenClifford.ofVector form vector
  have sandwich :
      EvenClifford.mul
          (EvenClifford.mul value.toEvenClifford.conjugate pure)
          value.toEvenClifford =
        EvenClifford.scale value.toEvenClifford.norm pure := by
    calc
      EvenClifford.mul
          (EvenClifford.mul value.toEvenClifford.conjugate pure)
          value.toEvenClifford =
        EvenClifford.ofVector form
          (value.toEvenClifford.actionNumerator vector) :=
        EvenClifford.conjugate_mul_ofVector_mul
          value.toEvenClifford vector
      _ = EvenClifford.ofVector form
          (Vector.scale value.toEvenClifford.norm vector) := by
        rw [value.actionNumerator_eq_scale_norm_of_action_eq vector fixed]
      _ = EvenClifford.scale value.toEvenClifford.norm pure := by
        exact EvenClifford.ofVector_scale form
          value.toEvenClifford.norm vector
  apply EvenClifford.eq_of_scale_eq_scale
    value.toEvenClifford.norm value.normNonzero
  calc
    EvenClifford.scale value.toEvenClifford.norm
        (EvenClifford.mul pure value.toEvenClifford) =
      EvenClifford.mul
        (EvenClifford.scale value.toEvenClifford.norm
          (EvenClifford.identity form))
        (EvenClifford.mul pure value.toEvenClifford) := by
          rw [EvenClifford.mul_scale_left, EvenClifford.identity_mul]
    _ = EvenClifford.mul
        (EvenClifford.mul value.toEvenClifford
          value.toEvenClifford.conjugate)
        (EvenClifford.mul pure value.toEvenClifford) := by
          rw [EvenClifford.mul_conjugate_eq_scale_identity]
    _ = EvenClifford.mul value.toEvenClifford
        (EvenClifford.mul value.toEvenClifford.conjugate
          (EvenClifford.mul pure value.toEvenClifford)) := by
          rw [EvenClifford.mul_assoc]
    _ = EvenClifford.mul value.toEvenClifford
        (EvenClifford.mul
          (EvenClifford.mul value.toEvenClifford.conjugate pure)
          value.toEvenClifford) := by
          rw [← EvenClifford.mul_assoc
            value.toEvenClifford.conjugate pure value.toEvenClifford]
    _ = EvenClifford.mul value.toEvenClifford
        (EvenClifford.scale value.toEvenClifford.norm pure) := by
          rw [sandwich]
    _ = EvenClifford.scale value.toEvenClifford.norm
        (EvenClifford.mul value.toEvenClifford pure) :=
      EvenClifford.mul_scale_right value.toEvenClifford.norm
        value.toEvenClifford pure

/-- In characteristic different from two, a displayed vector fixed by the
normalized action has zero Clifford cross with the representative's vector
coordinate. -/
theorem cliffordCross_eq_zero_of_action_eq
    {form : TernaryForm K} (value : form.NonNullEvenClifford)
    (twoNonzero : (2 : K) ≠ 0) (vector : Vector K)
    (fixed : value.action vector = vector) :
    form.cliffordCross vector value.toEvenClifford.vector = Vector.zero := by
  have commutes :=
    value.ofVector_mul_eq_mul_ofVector_of_action_eq vector fixed
  have vectorEqual := congrArg EvenClifford.vector commutes
  change EvenClifford.productVector form 0 value.toEvenClifford.scalar
      vector value.toEvenClifford.vector =
    EvenClifford.productVector form value.toEvenClifford.scalar 0
      value.toEvenClifford.vector vector at vectorEqual
  unfold EvenClifford.productVector at vectorEqual
  rw [form.cliffordCross_anticomm value.toEvenClifford.vector vector]
    at vectorEqual
  apply Vector.ext
  · apply scalar_eq_zero_of_nonzero_mul_eq_zero twoNonzero
    have coordinate := congrArg Vector.t vectorEqual
    unfold Vector.sub Vector.add Vector.scale Vector.neg at coordinate
    change
      (0 * value.toEvenClifford.vector.t +
          value.toEvenClifford.scalar * vector.t) -
        (form.cliffordCross vector value.toEvenClifford.vector).t =
      (value.toEvenClifford.scalar * vector.t +
          0 * value.toEvenClifford.vector.t) -
        -(form.cliffordCross vector value.toEvenClifford.vector).t
      at coordinate
    calc
      2 * (form.cliffordCross vector value.toEvenClifford.vector).t =
          ((value.toEvenClifford.scalar * vector.t +
              0 * value.toEvenClifford.vector.t) -
            -(form.cliffordCross vector value.toEvenClifford.vector).t) -
          ((0 * value.toEvenClifford.vector.t +
              value.toEvenClifford.scalar * vector.t) -
            (form.cliffordCross vector value.toEvenClifford.vector).t) := by
        ring1
      _ = 0 := by rw [coordinate]; ring1
  · apply scalar_eq_zero_of_nonzero_mul_eq_zero twoNonzero
    have coordinate := congrArg Vector.r vectorEqual
    unfold Vector.sub Vector.add Vector.scale Vector.neg at coordinate
    change
      (0 * value.toEvenClifford.vector.r +
          value.toEvenClifford.scalar * vector.r) -
        (form.cliffordCross vector value.toEvenClifford.vector).r =
      (value.toEvenClifford.scalar * vector.r +
          0 * value.toEvenClifford.vector.r) -
        -(form.cliffordCross vector value.toEvenClifford.vector).r
      at coordinate
    calc
      2 * (form.cliffordCross vector value.toEvenClifford.vector).r =
          ((value.toEvenClifford.scalar * vector.r +
              0 * value.toEvenClifford.vector.r) -
            -(form.cliffordCross vector value.toEvenClifford.vector).r) -
          ((0 * value.toEvenClifford.vector.r +
              value.toEvenClifford.scalar * vector.r) -
            (form.cliffordCross vector value.toEvenClifford.vector).r) := by
        ring1
      _ = 0 := by rw [coordinate]; ring1
  · apply scalar_eq_zero_of_nonzero_mul_eq_zero twoNonzero
    have coordinate := congrArg Vector.s vectorEqual
    unfold Vector.sub Vector.add Vector.scale Vector.neg at coordinate
    change
      (0 * value.toEvenClifford.vector.s +
          value.toEvenClifford.scalar * vector.s) -
        (form.cliffordCross vector value.toEvenClifford.vector).s =
      (value.toEvenClifford.scalar * vector.s +
          0 * value.toEvenClifford.vector.s) -
        -(form.cliffordCross vector value.toEvenClifford.vector).s
      at coordinate
    calc
      2 * (form.cliffordCross vector value.toEvenClifford.vector).s =
          ((value.toEvenClifford.scalar * vector.s +
              0 * value.toEvenClifford.vector.s) -
            -(form.cliffordCross vector value.toEvenClifford.vector).s) -
          ((0 * value.toEvenClifford.vector.s +
              value.toEvenClifford.scalar * vector.s) -
            (form.cliffordCross vector value.toEvenClifford.vector).s) := by
        ring1
      _ = 0 := by rw [coordinate]; ring1

/-- A trivial normalized action has zero vector coordinate.  This is the
finite coordinate heart of the projective Clifford kernel calculation. -/
theorem vector_eq_zero_of_actionMatrix_eq_identity
    {form : TernaryForm K} (value : form.NonNullEvenClifford)
    (twoNonzero : (2 : K) ≠ 0)
    (trivial : value.actionMatrix = Matrix3.identity) :
    value.toEvenClifford.vector = Vector.zero := by
  apply form.eq_zero_of_cliffordCross_right_eq_zero
  intro vector
  apply value.cliffordCross_eq_zero_of_action_eq twoNonzero
  calc
    value.action vector = Matrix3.rowMul vector value.actionMatrix :=
      (value.rowMul_actionMatrix vector).symm
    _ = Matrix3.rowMul vector Matrix3.identity := by rw [trivial]
    _ = vector := Matrix3.rowMul_identity vector

/-- A nonzero-norm Clifford representative is projectively scalar exactly
when its displayed vector coordinate vanishes. -/
theorem equivalent_identity_iff_vector_eq_zero
    {form : TernaryForm K} (value : form.NonNullEvenClifford) :
    (identity form).Equivalent value ↔
      value.toEvenClifford.vector = Vector.zero := by
  constructor
  · intro equivalent
    rcases equivalent with ⟨factor, _factorNonzero, rawEqual⟩
    have vectorEqual := congrArg EvenClifford.vector rawEqual
    change value.toEvenClifford.vector =
      Vector.scale factor Vector.zero at vectorEqual
    rw [Vector.scale_zero] at vectorEqual
    exact vectorEqual
  · intro vectorZero
    have scalarNonzero : value.toEvenClifford.scalar ≠ 0 := by
      intro scalarZero
      apply value.normNonzero
      unfold EvenClifford.norm
      rw [vectorZero, form.quadrance_zero, scalarZero]
      ring1
    refine ⟨value.toEvenClifford.scalar, scalarNonzero, ?_⟩
    apply EvenClifford.ext
    · change value.toEvenClifford.scalar =
        value.toEvenClifford.scalar * 1
      ring1
    · change value.toEvenClifford.vector =
        Vector.scale value.toEvenClifford.scalar Vector.zero
      rw [vectorZero, Vector.scale_zero]

/-- Exact kernel of the projective Clifford action: in characteristic
different from two, the identity rotation is represented precisely by the
nonzero scalar Clifford points. -/
theorem actionRotation_eq_identity_iff_equivalent_identity
    {form : TernaryForm K} (value : form.NonNullEvenClifford)
    (twoNonzero : (2 : K) ≠ 0) :
    value.actionRotation = TernaryForm.SpecialOrthogonal.identity form ↔
      (identity form).Equivalent value := by
  constructor
  · intro rotationEqual
    have matrixEqual := congrArg
      (fun rotation : form.SpecialOrthogonal => rotation.matrix)
      rotationEqual
    change value.actionMatrix = Matrix3.identity at matrixEqual
    apply (equivalent_identity_iff_vector_eq_zero value).2
    exact value.vector_eq_zero_of_actionMatrix_eq_identity
      twoNonzero matrixEqual
  · intro equivalent
    calc
      value.actionRotation = (identity form).actionRotation :=
        (actionRotation_respects_equivalent equivalent).symm
      _ = TernaryForm.SpecialOrthogonal.identity form :=
        actionRotation_identity form

/-- Clifford conjugation maps to inversion in the displayed
special-orthogonal group. -/
theorem actionRotation_conjugate {form : TernaryForm K}
    (value : form.NonNullEvenClifford) :
    value.conjugate.actionRotation =
      TernaryForm.SpecialOrthogonal.inverse value.actionRotation := by
  apply TernaryForm.SpecialOrthogonal.eq_of_matrix_eq
  change value.conjugate.actionMatrix = value.actionInverseMatrix
  have conjugateProduct :
      Matrix3.mul value.conjugate.actionMatrix value.actionMatrix =
        Matrix3.identity := by
    calc
      Matrix3.mul value.conjugate.actionMatrix value.actionMatrix =
          (mul value.conjugate value).actionMatrix :=
        (actionMatrix_mul value.conjugate value).symm
      _ = (identity form).actionMatrix :=
        actionMatrix_respects_equivalent
          value.conjugate_mul_equivalent_identity
      _ = Matrix3.identity := actionMatrix_identity form
  calc
    value.conjugate.actionMatrix =
        Matrix3.mul value.conjugate.actionMatrix Matrix3.identity :=
      (Matrix3.mul_identity value.conjugate.actionMatrix).symm
    _ = Matrix3.mul value.conjugate.actionMatrix
        (Matrix3.mul value.actionMatrix value.actionInverseMatrix) := by
      rw [value.actionMatrix_mul_actionInverseMatrix]
    _ = Matrix3.mul
        (Matrix3.mul value.conjugate.actionMatrix value.actionMatrix)
        value.actionInverseMatrix := by
      rw [Matrix3.mul_assoc]
    _ = Matrix3.mul Matrix3.identity value.actionInverseMatrix := by
      rw [conjugateProduct]
    _ = value.actionInverseMatrix :=
      Matrix3.identity_mul value.actionInverseMatrix

/-- Projective faithfulness of the Clifford action.  Equality of the
displayed special-orthogonal transformations is exactly equality up to an
explicit nonzero homogeneous scale. -/
theorem actionRotation_eq_iff_equivalent
    {form : TernaryForm K} (left right : form.NonNullEvenClifford)
    (twoNonzero : (2 : K) ≠ 0) :
    left.actionRotation = right.actionRotation ↔ left.Equivalent right := by
  constructor
  · intro actionEqual
    have relativeAction :
        (mul left.conjugate right).actionRotation =
          TernaryForm.SpecialOrthogonal.identity form := by
      calc
        (mul left.conjugate right).actionRotation =
            TernaryForm.SpecialOrthogonal.mul
              left.conjugate.actionRotation right.actionRotation :=
          actionRotation_mul left.conjugate right
        _ = TernaryForm.SpecialOrthogonal.mul
              (TernaryForm.SpecialOrthogonal.inverse left.actionRotation)
              right.actionRotation := by
          rw [actionRotation_conjugate]
        _ = TernaryForm.SpecialOrthogonal.mul
              (TernaryForm.SpecialOrthogonal.inverse left.actionRotation)
              left.actionRotation := by rw [← actionEqual]
        _ = TernaryForm.SpecialOrthogonal.identity form :=
          TernaryForm.SpecialOrthogonal.inverse_mul left.actionRotation
    have relativeIdentity :
        (identity form).Equivalent (mul left.conjugate right) :=
      (actionRotation_eq_identity_iff_equivalent_identity
        (mul left.conjugate right) twoNonzero).1 relativeAction
    have leftToRelative :
        left.Equivalent (mul left (mul left.conjugate right)) := by
      have productEquivalent := mul_respects_equivalent
        (equivalent_refl left) relativeIdentity
      simpa only [mul_identity] using productEquivalent
    have relativeToRight :
        (mul left (mul left.conjugate right)).Equivalent right := by
      have productEquivalent := mul_respects_equivalent
        (mul_conjugate_equivalent_identity left) (equivalent_refl right)
      simpa only [mul_assoc, identity_mul] using productEquivalent
    exact equivalent_trans leftToRelative relativeToRight
  · intro equivalent
    exact actionRotation_respects_equivalent equivalent

end NonNullEvenClifford

/-- Applying a displayed matrix to all three rows scales their displayed
determinant by the matrix determinant. -/
theorem determinant_rowMul (first second third : Vector K)
    (matrix : Matrix3 K) :
    Vector.determinant
        (Matrix3.rowMul first matrix)
        (Matrix3.rowMul second matrix)
        (Matrix3.rowMul third matrix) =
      Vector.determinant first second third *
        Matrix3.determinant matrix := by
  unfold Vector.determinant Matrix3.rowMul Matrix3.determinant
  ring1

/-- Explicit reconstruction in a displayed pairwise-orthogonal non-null
frame.  The proof builds the displayed frame matrix and its right inverse,
then uses finite square-matrix cancellation to obtain the left inverse. -/
theorem orthogonalFrame_reconstruct
    (form : TernaryForm K) (first second third : Vector K)
    (firstNonNull : form.quadrance first ≠ 0)
    (secondNonNull : form.quadrance second ≠ 0)
    (thirdNonNull : form.quadrance third ≠ 0)
    (firstSecond : form.Perpendicular first second)
    (firstThird : form.Perpendicular first third)
    (secondThird : form.Perpendicular second third)
    (vector : Vector K) :
    Vector.add
        (Vector.add
          (Vector.scale
            (form.bilinear vector first / form.quadrance first) first)
          (Vector.scale
            (form.bilinear vector second / form.quadrance second) second))
        (Vector.scale
          (form.bilinear vector third / form.quadrance third) third) =
      vector := by
  let basisMatrix : Matrix3 K :=
    ⟨first.t, first.r, first.s,
      second.t, second.r, second.s,
      third.t, third.r, third.s⟩
  let inverseMatrix : Matrix3 K :=
    ⟨(form.dual first).t / form.quadrance first,
      (form.dual second).t / form.quadrance second,
      (form.dual third).t / form.quadrance third,
      (form.dual first).r / form.quadrance first,
      (form.dual second).r / form.quadrance second,
      (form.dual third).r / form.quadrance third,
      (form.dual first).s / form.quadrance first,
      (form.dual second).s / form.quadrance second,
      (form.dual third).s / form.quadrance third⟩
  have rowMulInverse (input : Vector K) :
      Matrix3.rowMul input inverseMatrix =
        (⟨form.bilinear input first / form.quadrance first,
          form.bilinear input second / form.quadrance second,
          form.bilinear input third / form.quadrance third⟩ :
          Vector K) := by
    apply Vector.ext
    · change
        input.t * ((form.dual first).t / form.quadrance first) +
              input.r * ((form.dual first).r / form.quadrance first) +
              input.s * ((form.dual first).s / form.quadrance first) =
          form.bilinear input first / form.quadrance first
      rw [form.bilinear_eq_dot_dual]
      unfold Vector.dot
      simp only [RFAP.ExplicitField.div_eq_mul_inv]
      ring1
    · change
        input.t * ((form.dual second).t / form.quadrance second) +
              input.r * ((form.dual second).r / form.quadrance second) +
              input.s * ((form.dual second).s / form.quadrance second) =
          form.bilinear input second / form.quadrance second
      rw [form.bilinear_eq_dot_dual]
      unfold Vector.dot
      simp only [RFAP.ExplicitField.div_eq_mul_inv]
      ring1
    · change
        input.t * ((form.dual third).t / form.quadrance third) +
              input.r * ((form.dual third).r / form.quadrance third) +
              input.s * ((form.dual third).s / form.quadrance third) =
          form.bilinear input third / form.quadrance third
      rw [form.bilinear_eq_dot_dual]
      unfold Vector.dot
      simp only [RFAP.ExplicitField.div_eq_mul_inv]
      ring1
  have rowMulBasis (coordinates : Vector K) :
      Matrix3.rowMul coordinates basisMatrix =
        Vector.add
          (Vector.add
            (Vector.scale coordinates.t first)
            (Vector.scale coordinates.r second))
          (Vector.scale coordinates.s third) := by
    ext <;> unfold basisMatrix Matrix3.rowMul Vector.add Vector.scale <;>
      ring1
  have firstSecondZero : form.bilinear first second = 0 := firstSecond
  have firstThirdZero : form.bilinear first third = 0 := firstThird
  have secondThirdZero : form.bilinear second third = 0 := secondThird
  have secondFirstZero : form.bilinear second first = 0 := by
    rw [form.bilinear_comm]
    exact firstSecondZero
  have thirdFirstZero : form.bilinear third first = 0 := by
    rw [form.bilinear_comm]
    exact firstThirdZero
  have thirdSecondZero : form.bilinear third second = 0 := by
    rw [form.bilinear_comm]
    exact secondThirdZero
  have firstRatio : form.quadrance first / form.quadrance first = 1 := by
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    exact RFAP.ExplicitField.mul_inv_cancel
      (form.quadrance first) firstNonNull
  have secondRatio : form.quadrance second / form.quadrance second = 1 := by
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    exact RFAP.ExplicitField.mul_inv_cancel
      (form.quadrance second) secondNonNull
  have thirdRatio : form.quadrance third / form.quadrance third = 1 := by
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    exact RFAP.ExplicitField.mul_inv_cancel
      (form.quadrance third) thirdNonNull
  have firstRow :
      Matrix3.rowMul first inverseMatrix = (⟨1, 0, 0⟩ : Vector K) := by
    rw [rowMulInverse]
    apply Vector.ext
    · change form.quadrance first / form.quadrance first = 1
      exact firstRatio
    · change form.bilinear first second / form.quadrance second = 0
      rw [firstSecondZero, RFAP.ExplicitField.zero_div]
    · change form.bilinear first third / form.quadrance third = 0
      rw [firstThirdZero, RFAP.ExplicitField.zero_div]
  have secondRow :
      Matrix3.rowMul second inverseMatrix = (⟨0, 1, 0⟩ : Vector K) := by
    rw [rowMulInverse]
    apply Vector.ext
    · change form.bilinear second first / form.quadrance first = 0
      rw [secondFirstZero, RFAP.ExplicitField.zero_div]
    · change form.quadrance second / form.quadrance second = 1
      exact secondRatio
    · change form.bilinear second third / form.quadrance third = 0
      rw [secondThirdZero, RFAP.ExplicitField.zero_div]
  have thirdRow :
      Matrix3.rowMul third inverseMatrix = (⟨0, 0, 1⟩ : Vector K) := by
    rw [rowMulInverse]
    apply Vector.ext
    · change form.bilinear third first / form.quadrance first = 0
      rw [thirdFirstZero, RFAP.ExplicitField.zero_div]
    · change form.bilinear third second / form.quadrance second = 0
      rw [thirdSecondZero, RFAP.ExplicitField.zero_div]
    · change form.quadrance third / form.quadrance third = 1
      exact thirdRatio
  have rightInverse :
      Matrix3.mul basisMatrix inverseMatrix = Matrix3.identity := by
    apply Matrix3.ext
    · simpa [basisMatrix, Matrix3.mul, Matrix3.rowMul, Matrix3.identity]
        using congrArg Vector.t firstRow
    · simpa [basisMatrix, Matrix3.mul, Matrix3.rowMul, Matrix3.identity]
        using congrArg Vector.r firstRow
    · simpa [basisMatrix, Matrix3.mul, Matrix3.rowMul, Matrix3.identity]
        using congrArg Vector.s firstRow
    · simpa [basisMatrix, Matrix3.mul, Matrix3.rowMul, Matrix3.identity]
        using congrArg Vector.t secondRow
    · simpa [basisMatrix, Matrix3.mul, Matrix3.rowMul, Matrix3.identity]
        using congrArg Vector.r secondRow
    · simpa [basisMatrix, Matrix3.mul, Matrix3.rowMul, Matrix3.identity]
        using congrArg Vector.s secondRow
    · simpa [basisMatrix, Matrix3.mul, Matrix3.rowMul, Matrix3.identity]
        using congrArg Vector.t thirdRow
    · simpa [basisMatrix, Matrix3.mul, Matrix3.rowMul, Matrix3.identity]
        using congrArg Vector.r thirdRow
    · simpa [basisMatrix, Matrix3.mul, Matrix3.rowMul, Matrix3.identity]
        using congrArg Vector.s thirdRow
  have leftInverse :
      Matrix3.mul inverseMatrix basisMatrix = Matrix3.identity :=
    Matrix3.inverse_mul_of_mul_eq_identity form.one_ne_zero rightInverse
  calc
    Vector.add
        (Vector.add
          (Vector.scale
            (form.bilinear vector first / form.quadrance first) first)
          (Vector.scale
            (form.bilinear vector second / form.quadrance second) second))
        (Vector.scale
          (form.bilinear vector third / form.quadrance third) third) =
      Matrix3.rowMul
        (⟨form.bilinear vector first / form.quadrance first,
          form.bilinear vector second / form.quadrance second,
          form.bilinear vector third / form.quadrance third⟩ : Vector K)
        basisMatrix :=
      (rowMulBasis
        (⟨form.bilinear vector first / form.quadrance first,
          form.bilinear vector second / form.quadrance second,
          form.bilinear vector third / form.quadrance third⟩ :
          Vector K)).symm
    _ = Matrix3.rowMul
        (Matrix3.rowMul vector inverseMatrix) basisMatrix := by
      rw [rowMulInverse]
    _ = Matrix3.rowMul vector
        (Matrix3.mul inverseMatrix basisMatrix) :=
      Matrix3.rowMul_mul vector inverseMatrix basisMatrix
    _ = Matrix3.rowMul vector Matrix3.identity := by rw [leftInverse]
    _ = vector := Matrix3.rowMul_identity vector

/-- The relative cross of two perpendicular non-null vectors is non-null. -/
theorem cross_nonNull_of_perpendicular
    (form : TernaryForm K) (first second : Vector K)
    (firstNonNull : form.quadrance first ≠ 0)
    (secondNonNull : form.quadrance second ≠ 0)
    (perpendicular : form.Perpendicular first second) :
    form.quadrance (form.cross first second) ≠ 0 := by
  intro crossZero
  have perpendicularZero : form.bilinear first second = 0 := perpendicular
  have lagrange := form.lagrange first second
  rw [perpendicularZero, crossZero] at lagrange
  have productNonzero :=
    RFAP.ExplicitField.mul_ne_zero firstNonNull secondNonNull
  apply productNonzero
  calc
    form.quadrance first * form.quadrance second =
        0 ^ 2 + form.determinant * 0 := lagrange.symm
    _ = 0 := by ring1

/-- A determinant-one form isometry fixing two perpendicular non-null vectors
is the identity.  The relative cross supplies the third non-null frame vector,
and the determinant fixes its otherwise possible scalar action. -/
theorem Isometry.matrix_eq_identity_of_fixed_orthogonal_pair
    (form : TernaryForm K) (isometry : form.Isometry)
    (first second : Vector K)
    (firstNonNull : form.quadrance first ≠ 0)
    (secondNonNull : form.quadrance second ≠ 0)
    (perpendicular : form.Perpendicular first second)
    (firstFixed : isometry.act first = first)
    (secondFixed : isometry.act second = second)
    (determinantOne : Matrix3.determinant isometry.matrix = 1) :
    isometry.matrix = Matrix3.identity := by
  let third := form.cross first second
  have thirdNonNull : form.quadrance third ≠ 0 :=
    form.cross_nonNull_of_perpendicular first second firstNonNull
      secondNonNull perpendicular
  have firstThird : form.Perpendicular first third := by
    apply (form.perpendicular_comm first third).2
    exact form.cross_perpendicular_left first second
  have secondThird : form.Perpendicular second third := by
    apply (form.perpendicular_comm second third).2
    exact form.cross_perpendicular_right first second
  have thirdActFirstZero :
      form.bilinear (isometry.act third) first = 0 := by
    calc
      form.bilinear (isometry.act third) first =
          form.bilinear (isometry.act third) (isometry.act first) := by
        rw [firstFixed]
      _ = form.bilinear third first :=
        isometry.bilinear_act third first
      _ = 0 := form.cross_perpendicular_left first second
  have thirdActSecondZero :
      form.bilinear (isometry.act third) second = 0 := by
    calc
      form.bilinear (isometry.act third) second =
          form.bilinear (isometry.act third) (isometry.act second) := by
        rw [secondFixed]
      _ = form.bilinear third second :=
        isometry.bilinear_act third second
      _ = 0 := form.cross_perpendicular_right first second
  let thirdCoefficient :=
    form.bilinear (isometry.act third) third / form.quadrance third
  have thirdActScale :
      isometry.act third = Vector.scale thirdCoefficient third := by
    have reconstruction := form.orthogonalFrame_reconstruct
      first second third firstNonNull secondNonNull thirdNonNull
      perpendicular firstThird secondThird (isometry.act third)
    calc
      isometry.act third =
          Vector.add
            (Vector.add
              (Vector.scale
                (form.bilinear (isometry.act third) first /
                  form.quadrance first) first)
              (Vector.scale
                (form.bilinear (isometry.act third) second /
                  form.quadrance second) second))
            (Vector.scale
              (form.bilinear (isometry.act third) third /
                form.quadrance third) third) :=
        reconstruction.symm
      _ = Vector.scale thirdCoefficient third := by
        rw [thirdActFirstZero, thirdActSecondZero,
          RFAP.ExplicitField.zero_div, RFAP.ExplicitField.zero_div]
        ext <;> unfold thirdCoefficient Vector.add Vector.scale <;> ring1
  have frameDeterminant :
      Vector.determinant first second third = form.quadrance third := by
    exact (form.bilinear_cross first second third).symm
  have transformedDeterminant :=
    determinant_rowMul first second third isometry.matrix
  change Vector.determinant
      (isometry.act first) (isometry.act second) (isometry.act third) =
    Vector.determinant first second third *
      Matrix3.determinant isometry.matrix at transformedDeterminant
  rw [firstFixed, secondFixed, thirdActScale, determinantOne,
    mul_one] at transformedDeterminant
  have coefficientFrame :
      thirdCoefficient * Vector.determinant first second third =
        Vector.determinant first second third := by
    calc
      thirdCoefficient * Vector.determinant first second third =
          Vector.determinant first second
            (Vector.scale thirdCoefficient third) := by
        unfold Vector.determinant Vector.scale
        ring1
      _ = Vector.determinant first second third :=
        transformedDeterminant
  have coefficientOne : thirdCoefficient = 1 := by
    apply scalar_eq_of_nonzero_mul_eq_mul thirdNonNull
    calc
      form.quadrance third * thirdCoefficient =
          thirdCoefficient * Vector.determinant first second third := by
        rw [frameDeterminant]
        ring1
      _ = Vector.determinant first second third := coefficientFrame
      _ = form.quadrance third * 1 := by
        rw [frameDeterminant, mul_one]
  have thirdFixed : isometry.act third = third := by
    rw [thirdActScale, coefficientOne, Vector.one_scale]
  apply Matrix3.eq_of_rowMul_eq
  intro vector
  change isometry.act vector =
    Matrix3.rowMul vector Matrix3.identity
  rw [Matrix3.rowMul_identity]
  have reconstruction := form.orthogonalFrame_reconstruct
    first second third firstNonNull secondNonNull thirdNonNull
    perpendicular firstThird secondThird vector
  calc
    isometry.act vector =
        isometry.act
          (Vector.add
            (Vector.add
              (Vector.scale
                (form.bilinear vector first / form.quadrance first) first)
              (Vector.scale
                (form.bilinear vector second / form.quadrance second) second))
            (Vector.scale
              (form.bilinear vector third / form.quadrance third) third)) := by
      rw [reconstruction]
    _ = Vector.add
          (Vector.add
            (Vector.scale
              (form.bilinear vector first / form.quadrance first)
              (isometry.act first))
            (Vector.scale
              (form.bilinear vector second / form.quadrance second)
              (isometry.act second)))
          (Vector.scale
            (form.bilinear vector third / form.quadrance third)
            (isometry.act third)) := by
      ext <;> unfold Isometry.act Matrix3.rowMul Vector.add Vector.scale <;>
        ring1
    _ = Vector.add
          (Vector.add
            (Vector.scale
              (form.bilinear vector first / form.quadrance first) first)
            (Vector.scale
              (form.bilinear vector second / form.quadrance second) second))
          (Vector.scale
            (form.bilinear vector third / form.quadrance third) third) := by
      rw [firstFixed, secondFixed, thirdFixed]
    _ = vector := reconstruction

/-- The displayed linear displacement operator \(R-I\). -/
def SpecialOrthogonal.displacementMatrix {form : TernaryForm K}
    (rotation : form.SpecialOrthogonal) : Matrix3 K :=
  Matrix3.sub rotation.matrix Matrix3.identity

/-- The displacement of a displayed vector under a form rotation. -/
def SpecialOrthogonal.displacement {form : TernaryForm K}
    (rotation : form.SpecialOrthogonal) (vector : Vector K) : Vector K :=
  Vector.sub (rotation.act vector) vector

theorem SpecialOrthogonal.rowMul_displacementMatrix
    {form : TernaryForm K} (rotation : form.SpecialOrthogonal)
    (vector : Vector K) :
    Matrix3.rowMul vector rotation.displacementMatrix =
      rotation.displacement vector := by
  unfold SpecialOrthogonal.displacementMatrix
    SpecialOrthogonal.displacement Isometry.act
  rw [Matrix3.rowMul_sub, Matrix3.rowMul_identity]

theorem SpecialOrthogonal.displacement_add
    {form : TernaryForm K} (rotation : form.SpecialOrthogonal)
    (left right : Vector K) :
    rotation.displacement (Vector.add left right) =
      Vector.add (rotation.displacement left)
        (rotation.displacement right) := by
  ext <;> unfold SpecialOrthogonal.displacement Isometry.act
    Vector.add Vector.sub Matrix3.rowMul <;> ring1

theorem SpecialOrthogonal.displacement_sub
    {form : TernaryForm K} (rotation : form.SpecialOrthogonal)
    (left right : Vector K) :
    rotation.displacement (Vector.sub left right) =
      Vector.sub (rotation.displacement left)
        (rotation.displacement right) := by
  ext <;> unfold SpecialOrthogonal.displacement Isometry.act
    Vector.sub Matrix3.rowMul <;> ring1

/-- The displacement operator commutes with the rotation that defines it. -/
theorem SpecialOrthogonal.displacement_act
    {form : TernaryForm K} (rotation : form.SpecialOrthogonal)
    (vector : Vector K) :
    rotation.displacement (rotation.act vector) =
      rotation.act (rotation.displacement vector) := by
  ext <;> unfold SpecialOrthogonal.displacement Isometry.act
    Vector.sub Matrix3.rowMul <;> ring1

/-- Coordinate expansion of the displacement operator. -/
theorem SpecialOrthogonal.displacement_coordinateExpansion
    {form : TernaryForm K} (rotation : form.SpecialOrthogonal)
    (vector : Vector K) :
    rotation.displacement vector =
      Vector.add
        (Vector.add
          (Vector.scale vector.t
            (rotation.displacement (⟨1, 0, 0⟩ : Vector K)))
          (Vector.scale vector.r
            (rotation.displacement (⟨0, 1, 0⟩ : Vector K))))
        (Vector.scale vector.s
          (rotation.displacement (⟨0, 0, 1⟩ : Vector K))) := by
  ext <;> unfold SpecialOrthogonal.displacement Isometry.act
    Vector.add Vector.sub Vector.scale Matrix3.rowMul <;> ring1

/-- A cached non-null seed whose displacement under a displayed rotation is
also non-null. -/
structure NonNullDisplacementWitness (form : TernaryForm K)
    (rotation : form.SpecialOrthogonal) where
  seed : Vector K
  seedNonNull : form.quadrance seed ≠ 0
  displacementNonNull : form.quadrance (rotation.displacement seed) ≠ 0

/-- Any vector with non-null displacement can be converted into a non-null
seed with non-null displacement.  If the supplied vector is null, test the
sum and difference of it with its image; the parallelogram identity guarantees
that one of their displacements is non-null. -/
def nonNullDisplacementWitnessOf [DecidableEq K]
    (form : TernaryForm K) (rotation : form.SpecialOrthogonal)
    (vector : Vector K)
    (displacementNonNull :
      form.quadrance (rotation.displacement vector) ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    NonNullDisplacementWitness form rotation := by
  by_cases vectorNull : form.quadrance vector = 0
  · let moved := rotation.act vector
    let sum := Vector.add vector moved
    let difference := Vector.sub vector moved
    have movedNull : form.quadrance moved = 0 := by
      unfold moved
      rw [rotation.quadrance_act, vectorNull]
    have sumQuadrance :
        form.quadrance sum =
          -form.quadrance (rotation.displacement vector) := by
      have addition := form.quadrance_add vector moved
      have subtraction := form.quadrance_sub moved vector
      change form.quadrance sum = _ at addition
      change form.quadrance (rotation.displacement vector) = _
        at subtraction
      rw [vectorNull, movedNull] at addition subtraction
      calc
        form.quadrance sum =
            0 + 2 * form.bilinear vector moved + 0 := addition
        _ = -(0 - 2 * form.bilinear moved vector + 0) := by
          rw [form.bilinear_comm moved vector]
          ring1
        _ = -form.quadrance (rotation.displacement vector) := by
          rw [subtraction]
    have differenceQuadrance :
        form.quadrance difference =
          form.quadrance (rotation.displacement vector) := by
      have first := form.quadrance_sub vector moved
      have second := form.quadrance_sub moved vector
      change form.quadrance difference = _ at first
      change form.quadrance (rotation.displacement vector) = _ at second
      rw [vectorNull, movedNull] at first second
      calc
        form.quadrance difference =
            0 - 2 * form.bilinear vector moved + 0 := first
        _ = 0 - 2 * form.bilinear moved vector + 0 := by
          rw [form.bilinear_comm vector moved]
        _ = form.quadrance (rotation.displacement vector) := second.symm
    have sumNonNull : form.quadrance sum ≠ 0 := by
      intro sumZero
      apply displacementNonNull
      have negZero :
          -form.quadrance (rotation.displacement vector) = 0 := by
        rw [← sumQuadrance, sumZero]
      exact neg_eq_zero.mp negZero
    have differenceNonNull : form.quadrance difference ≠ 0 := by
      rw [differenceQuadrance]
      exact displacementNonNull
    have movedDisplacementQuadrance :
        form.quadrance (rotation.displacement moved) =
          form.quadrance (rotation.displacement vector) := by
      unfold moved
      rw [rotation.displacement_act, rotation.quadrance_act]
    have displacementParallelogram :
        form.quadrance (rotation.displacement sum) +
            form.quadrance (rotation.displacement difference) =
          4 * form.quadrance (rotation.displacement vector) := by
      rw [rotation.displacement_add, rotation.displacement_sub,
        form.quadrance_add, form.quadrance_sub,
        movedDisplacementQuadrance]
      ring1
    by_cases sumDisplacementZero :
        form.quadrance (rotation.displacement sum) = 0
    · refine ⟨difference, differenceNonNull, ?_⟩
      intro differenceDisplacementZero
      have fourTimesZero :
          (2 * 2) * form.quadrance (rotation.displacement vector) = 0 := by
        calc
          (2 * 2) * form.quadrance (rotation.displacement vector) =
              4 * form.quadrance (rotation.displacement vector) := by
            ring1
          _ = form.quadrance (rotation.displacement sum) +
                form.quadrance (rotation.displacement difference) :=
            displacementParallelogram.symm
          _ = 0 := by
            rw [sumDisplacementZero, differenceDisplacementZero]
            ring1
      have fourNonzero : (2 : K) * 2 ≠ 0 :=
        RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero
      apply displacementNonNull
      exact scalar_eq_zero_of_nonzero_mul_eq_zero
        fourNonzero fourTimesZero
    · exact ⟨sum, sumNonNull, sumDisplacementZero⟩
  · exact ⟨vector, vectorNull, displacementNonNull⟩

/-- Every nonidentity displayed ternary rotation has a constructively selected
non-null seed with non-null displacement.  Six fixed coordinate tests detect
the displacement quadratic form.  If all six vanished, polarization would
make its image totally null; orthogonality would then make \(R-I\)
form-skew and square-zero, which the explicit three-dimensional skew
calculation rules out. -/
def nonNullDisplacementWitness [DecidableEq K]
    (form : TernaryForm K) (rotation : form.SpecialOrthogonal)
    (rotationNonidentity :
      rotation ≠ SpecialOrthogonal.identity form)
    (twoNonzero : (2 : K) ≠ 0) :
    NonNullDisplacementWitness form rotation := by
  let basisT : Vector K := ⟨1, 0, 0⟩
  let basisR : Vector K := ⟨0, 1, 0⟩
  let basisS : Vector K := ⟨0, 0, 1⟩
  let sumTR := Vector.add basisT basisR
  let sumTS := Vector.add basisT basisS
  let sumRS := Vector.add basisR basisS
  let displacedT := rotation.displacement basisT
  let displacedR := rotation.displacement basisR
  let displacedS := rotation.displacement basisS
  by_cases displacedTZero : form.quadrance displacedT = 0
  · by_cases displacedRZero : form.quadrance displacedR = 0
    · by_cases displacedSZero : form.quadrance displacedS = 0
      · by_cases sumTRZero :
          form.quadrance (rotation.displacement sumTR) = 0
        · by_cases sumTSZero :
            form.quadrance (rotation.displacement sumTS) = 0
          · by_cases sumRSZero :
              form.quadrance (rotation.displacement sumRS) = 0
            · have pairingTR :
                  form.bilinear displacedT displacedR = 0 := by
                apply scalar_eq_zero_of_nonzero_mul_eq_zero twoNonzero
                have addition := form.quadrance_add displacedT displacedR
                rw [displacedTZero, displacedRZero] at addition
                have displacementSum :=
                  rotation.displacement_add basisT basisR
                change rotation.displacement sumTR =
                  Vector.add displacedT displacedR at displacementSum
                calc
                  2 * form.bilinear displacedT displacedR =
                      0 + 2 * form.bilinear displacedT displacedR + 0 := by
                    ring1
                  _ = form.quadrance
                      (Vector.add displacedT displacedR) := addition.symm
                  _ = form.quadrance
                      (rotation.displacement sumTR) := by
                    rw [displacementSum]
                  _ = 0 := sumTRZero
              have pairingTS :
                  form.bilinear displacedT displacedS = 0 := by
                apply scalar_eq_zero_of_nonzero_mul_eq_zero twoNonzero
                have addition := form.quadrance_add displacedT displacedS
                rw [displacedTZero, displacedSZero] at addition
                have displacementSum :=
                  rotation.displacement_add basisT basisS
                change rotation.displacement sumTS =
                  Vector.add displacedT displacedS at displacementSum
                calc
                  2 * form.bilinear displacedT displacedS =
                      0 + 2 * form.bilinear displacedT displacedS + 0 := by
                    ring1
                  _ = form.quadrance
                      (Vector.add displacedT displacedS) := addition.symm
                  _ = form.quadrance
                      (rotation.displacement sumTS) := by
                    rw [displacementSum]
                  _ = 0 := sumTSZero
              have pairingRS :
                  form.bilinear displacedR displacedS = 0 := by
                apply scalar_eq_zero_of_nonzero_mul_eq_zero twoNonzero
                have addition := form.quadrance_add displacedR displacedS
                rw [displacedRZero, displacedSZero] at addition
                have displacementSum :=
                  rotation.displacement_add basisR basisS
                change rotation.displacement sumRS =
                  Vector.add displacedR displacedS at displacementSum
                calc
                  2 * form.bilinear displacedR displacedS =
                      0 + 2 * form.bilinear displacedR displacedS + 0 := by
                    ring1
                  _ = form.quadrance
                      (Vector.add displacedR displacedS) := addition.symm
                  _ = form.quadrance
                      (rotation.displacement sumRS) := by
                    rw [displacementSum]
                  _ = 0 := sumRSZero
              have pairingRT :
                  form.bilinear displacedR displacedT = 0 := by
                rw [form.bilinear_comm]
                exact pairingTR
              have pairingST :
                  form.bilinear displacedS displacedT = 0 := by
                rw [form.bilinear_comm]
                exact pairingTS
              have pairingSR :
                  form.bilinear displacedS displacedR = 0 := by
                rw [form.bilinear_comm]
                exact pairingRS
              have pairingTT :
                  form.bilinear displacedT displacedT = 0 :=
                displacedTZero
              have pairingRR :
                  form.bilinear displacedR displacedR = 0 :=
                displacedRZero
              have pairingSS :
                  form.bilinear displacedS displacedS = 0 :=
                displacedSZero
              change form.bilinear
                (rotation.displacement (⟨1, 0, 0⟩ : Vector K))
                (rotation.displacement (⟨1, 0, 0⟩ : Vector K)) = 0
                at pairingTT
              change form.bilinear
                (rotation.displacement (⟨0, 1, 0⟩ : Vector K))
                (rotation.displacement (⟨0, 1, 0⟩ : Vector K)) = 0
                at pairingRR
              change form.bilinear
                (rotation.displacement (⟨0, 0, 1⟩ : Vector K))
                (rotation.displacement (⟨0, 0, 1⟩ : Vector K)) = 0
                at pairingSS
              change form.bilinear
                (rotation.displacement (⟨1, 0, 0⟩ : Vector K))
                (rotation.displacement (⟨0, 1, 0⟩ : Vector K)) = 0
                at pairingTR
              change form.bilinear
                (rotation.displacement (⟨1, 0, 0⟩ : Vector K))
                (rotation.displacement (⟨0, 0, 1⟩ : Vector K)) = 0
                at pairingTS
              change form.bilinear
                (rotation.displacement (⟨0, 1, 0⟩ : Vector K))
                (rotation.displacement (⟨0, 0, 1⟩ : Vector K)) = 0
                at pairingRS
              change form.bilinear
                (rotation.displacement (⟨0, 1, 0⟩ : Vector K))
                (rotation.displacement (⟨1, 0, 0⟩ : Vector K)) = 0
                at pairingRT
              change form.bilinear
                (rotation.displacement (⟨0, 0, 1⟩ : Vector K))
                (rotation.displacement (⟨1, 0, 0⟩ : Vector K)) = 0
                at pairingST
              change form.bilinear
                (rotation.displacement (⟨0, 0, 1⟩ : Vector K))
                (rotation.displacement (⟨0, 1, 0⟩ : Vector K)) = 0
                at pairingSR
              have imagePairZero : ∀ left right : Vector K,
                  form.bilinear (rotation.displacement left)
                    (rotation.displacement right) = 0 := by
                intro left right
                rw [rotation.displacement_coordinateExpansion left,
                  rotation.displacement_coordinateExpansion right]
                simp only [form.bilinear_add_left,
                  form.bilinear_add_right, form.bilinear_scale_left,
                  form.bilinear_scale_right]
                rw [pairingTT, pairingRR, pairingSS,
                  pairingTR, pairingTS, pairingRS, pairingRT, pairingST,
                  pairingSR]
                ring1
              have reconstruct (vector : Vector K) :
                  rotation.act vector =
                    Vector.add (rotation.displacement vector) vector := by
                ext <;> unfold SpecialOrthogonal.displacement Vector.add
                  Vector.sub <;> ring1
              have skew : ∀ left right : Vector K,
                  form.bilinear (rotation.displacement left) right =
                    -form.bilinear left
                      (rotation.displacement right) := by
                intro left right
                have preserved := rotation.toIsometry.bilinear_act left right
                rw [reconstruct left, reconstruct right,
                  form.bilinear_add_left, form.bilinear_add_right,
                  form.bilinear_add_right, imagePairZero] at preserved
                have crossSumZero :
                    form.bilinear (rotation.displacement left) right +
                        form.bilinear left
                          (rotation.displacement right) = 0 := by
                  calc
                    form.bilinear (rotation.displacement left) right +
                        form.bilinear left
                          (rotation.displacement right) =
                      (form.bilinear
                            (rotation.displacement left)
                            (rotation.displacement right) +
                          form.bilinear
                            (rotation.displacement left) right +
                          (form.bilinear left
                              (rotation.displacement right) +
                            form.bilinear left right)) -
                        form.bilinear left right := by
                          rw [imagePairZero]
                          ring1
                    _ = 0 := by
                      rw [imagePairZero]
                      rw [preserved]
                      ring1
                calc
                  form.bilinear (rotation.displacement left) right =
                      -form.bilinear left
                          (rotation.displacement right) +
                        (form.bilinear
                            (rotation.displacement left) right +
                          form.bilinear left
                            (rotation.displacement right)) := by
                      ring1
                  _ = -form.bilinear left
                      (rotation.displacement right) := by
                    rw [crossSumZero, add_zero]
              let displacementMatrix := rotation.displacementMatrix
              have displacementSquareZero :
                  Matrix3.mul displacementMatrix displacementMatrix =
                    Matrix3.zero := by
                apply Matrix3.eq_of_rowMul_eq
                intro vector
                have twiceZero :
                    rotation.displacement
                        (rotation.displacement vector) = Vector.zero := by
                  apply form.eq_of_bilinear_eq
                  intro test
                  rw [form.bilinear_zero_left]
                  calc
                    form.bilinear
                        (rotation.displacement
                          (rotation.displacement vector)) test =
                      -form.bilinear
                        (rotation.displacement vector)
                        (rotation.displacement test) :=
                      skew (rotation.displacement vector) test
                    _ = 0 := by rw [imagePairZero]; ring1
                calc
                  Matrix3.rowMul vector
                      (Matrix3.mul displacementMatrix
                        displacementMatrix) =
                    Matrix3.rowMul
                      (Matrix3.rowMul vector displacementMatrix)
                      displacementMatrix :=
                    (Matrix3.rowMul_mul vector displacementMatrix
                      displacementMatrix).symm
                  _ = rotation.displacement
                      (rotation.displacement vector) := by
                    unfold displacementMatrix
                    rw [rotation.rowMul_displacementMatrix,
                      rotation.rowMul_displacementMatrix]
                  _ = Vector.zero := twiceZero
                  _ = Matrix3.rowMul vector Matrix3.zero := by
                    ext <;> unfold Vector.zero Matrix3.rowMul Matrix3.zero <;>
                      ring1
              have displacementAntisymmetric :
                  Matrix3.IsAntisymmetric
                    (Matrix3.mul displacementMatrix form.matrix) := by
                apply form.mul_form_isAntisymmetric_of_bilinear_skew
                intro left right
                unfold displacementMatrix
                rw [rotation.rowMul_displacementMatrix,
                  rotation.rowMul_displacementMatrix]
                exact skew left right
              have displacementMatrixZero :
                  displacementMatrix = Matrix3.zero :=
                form.matrix_eq_zero_of_mul_form_antisymmetric_of_square_eq_zero
                  displacementMatrix twoNonzero displacementAntisymmetric
                  displacementSquareZero
              have matrixDifferenceZero :
                  Matrix3.sub rotation.matrix Matrix3.identity =
                    Matrix3.zero := by
                exact displacementMatrixZero
              have rotationMatrixIdentity :
                  rotation.matrix = Matrix3.identity :=
                Matrix3.eq_of_sub_eq_zero matrixDifferenceZero
              have rotationIdentity :
                  rotation = SpecialOrthogonal.identity form := by
                apply SpecialOrthogonal.eq_of_matrix_eq
                exact rotationMatrixIdentity
              exact (rotationNonidentity rotationIdentity).elim
            · exact nonNullDisplacementWitnessOf form rotation sumRS
                sumRSZero twoNonzero
          · exact nonNullDisplacementWitnessOf form rotation sumTS
              sumTSZero twoNonzero
        · exact nonNullDisplacementWitnessOf form rotation sumTR
            sumTRZero twoNonzero
      · exact nonNullDisplacementWitnessOf form rotation basisS
          displacedSZero twoNonzero
    · exact nonNullDisplacementWitnessOf form rotation basisR
        displacedRZero twoNonzero
  · exact nonNullDisplacementWitnessOf form rotation basisT
      displacedTZero twoNonzero

/-- Cached classification of an orientation-reversing isometry fixing a
displayed non-null vector as one reflection in a non-null perpendicular
mirror. -/
structure FixedVectorReflectionClassification (form : TernaryForm K)
    (isometry : form.Isometry) (fixedVector : Vector K) where
  mirror : Vector K
  mirrorNonNull : form.quadrance mirror ≠ 0
  mirrorPerpendicular : form.Perpendicular mirror fixedVector
  matrix_eq : isometry.matrix = form.reflection mirror mirrorNonNull

/-- Constructively classify a determinant-minus-one isometry fixing a
non-null vector.  Select a non-null perpendicular test vector.  If its
displacement is non-null, that displacement is the mirror; if its quadrance
vanishes, orthogonal-frame reconstruction forces the displacement itself to
vanish, and the relative cross supplies the mirror. -/
def classifyFixedVectorReflection [DecidableEq K]
    (form : TernaryForm K) (isometry : form.Isometry)
    (fixedVector : Vector K)
    (fixedVectorNonNull : form.quadrance fixedVector ≠ 0)
    (fixed : isometry.act fixedVector = fixedVector)
    (determinantMinusOne :
      Matrix3.determinant isometry.matrix = -1)
    (twoNonzero : (2 : K) ≠ 0) :
    FixedVectorReflectionClassification form isometry fixedVector := by
  let selected :=
    form.perpendicularNonNullVectorWitness fixedVector
      fixedVectorNonNull twoNonzero
  let test := selected.value
  let difference := Vector.sub (isometry.act test) test
  have testNonNull : form.quadrance test ≠ 0 := selected.nonNull
  have testPerpendicularFixed :
      form.Perpendicular test fixedVector := selected.perpendicular
  have fixedPerpendicularTest :
      form.Perpendicular fixedVector test :=
    (form.perpendicular_comm fixedVector test).2 testPerpendicularFixed
  have actedTestPerpendicularFixed :
      form.Perpendicular (isometry.act test) fixedVector := by
    unfold Perpendicular
    calc
      form.bilinear (isometry.act test) fixedVector =
          form.bilinear (isometry.act test)
            (isometry.act fixedVector) := by
        rw [fixed]
      _ = form.bilinear test fixedVector :=
        isometry.bilinear_act test fixedVector
      _ = 0 := testPerpendicularFixed
  have differencePerpendicularFixed :
      form.Perpendicular difference fixedVector := by
    change form.bilinear (isometry.act test) fixedVector = 0 at actedTestPerpendicularFixed
    change form.bilinear test fixedVector = 0 at testPerpendicularFixed
    change form.bilinear difference fixedVector = 0
    unfold difference
    rw [form.bilinear_sub_left, actedTestPerpendicularFixed,
      testPerpendicularFixed]
    ring1
  have fixedPerpendicularDifference :
      form.Perpendicular fixedVector difference :=
    (form.perpendicular_comm fixedVector difference).2
      differencePerpendicularFixed
  by_cases differenceNull : form.quadrance difference = 0
  · have subtraction := form.quadrance_sub (isometry.act test) test
    change form.quadrance difference = _ at subtraction
    rw [differenceNull, isometry.quadrance_act] at subtraction
    have twicePairing :
        2 * form.bilinear (isometry.act test) test =
          2 * form.quadrance test := by
      calc
        2 * form.bilinear (isometry.act test) test =
            2 * form.quadrance test -
              (form.quadrance test -
                2 * form.bilinear (isometry.act test) test +
                form.quadrance test) := by
          ring1
        _ = 2 * form.quadrance test := by
          rw [← subtraction]
          ring1
    have pairing :
        form.bilinear (isometry.act test) test =
          form.quadrance test :=
      scalar_eq_of_nonzero_mul_eq_mul twoNonzero twicePairing
    have differencePerpendicularTest :
        form.Perpendicular difference test := by
      unfold Perpendicular difference
      rw [form.bilinear_sub_left]
      change form.bilinear (isometry.act test) test -
        form.quadrance test = 0
      rw [pairing]
      ring1
    let third := form.cross fixedVector test
    have thirdNonNull : form.quadrance third ≠ 0 :=
      form.cross_nonNull_of_perpendicular fixedVector test
        fixedVectorNonNull testNonNull fixedPerpendicularTest
    have fixedPerpendicularThird :
        form.Perpendicular fixedVector third := by
      apply (form.perpendicular_comm fixedVector third).2
      exact form.cross_perpendicular_left fixedVector test
    have testPerpendicularThird :
        form.Perpendicular test third := by
      apply (form.perpendicular_comm test third).2
      exact form.cross_perpendicular_right fixedVector test
    let coefficient :=
      form.bilinear difference third / form.quadrance third
    have differenceScale :
        difference = Vector.scale coefficient third := by
      have reconstruction := form.orthogonalFrame_reconstruct
        fixedVector test third fixedVectorNonNull testNonNull thirdNonNull
        fixedPerpendicularTest fixedPerpendicularThird
        testPerpendicularThird difference
      have differenceFixedZero :
          form.bilinear difference fixedVector = 0 :=
        differencePerpendicularFixed
      have differenceTestZero :
          form.bilinear difference test = 0 :=
        differencePerpendicularTest
      calc
        difference =
            Vector.add
              (Vector.add
                (Vector.scale
                  (form.bilinear difference fixedVector /
                    form.quadrance fixedVector) fixedVector)
                (Vector.scale
                  (form.bilinear difference test /
                    form.quadrance test) test))
              (Vector.scale
                (form.bilinear difference third /
                  form.quadrance third) third) :=
          reconstruction.symm
        _ = Vector.scale coefficient third := by
          rw [differenceFixedZero, differenceTestZero,
            RFAP.ExplicitField.zero_div, RFAP.ExplicitField.zero_div]
          ext <;> unfold coefficient Vector.add Vector.scale <;> ring1
    have coefficientSquareTimesZero :
        coefficient ^ 2 * form.quadrance third = 0 := by
      calc
        coefficient ^ 2 * form.quadrance third =
            form.quadrance (Vector.scale coefficient third) :=
          (form.quadrance_scale coefficient third).symm
        _ = form.quadrance difference := by rw [differenceScale]
        _ = 0 := differenceNull
    have coefficientSquareZero : coefficient * coefficient = 0 := by
      apply scalar_eq_zero_of_nonzero_mul_eq_zero thirdNonNull
      calc
        form.quadrance third * (coefficient * coefficient) =
            coefficient ^ 2 * form.quadrance third := by
          ring1
        _ = 0 := coefficientSquareTimesZero
    have coefficientZero : coefficient = 0 := by
      by_cases zero : coefficient = 0
      · exact zero
      · have productNonzero :=
          RFAP.ExplicitField.mul_ne_zero zero zero
        exact (productNonzero coefficientSquareZero).elim
    have differenceIsZero : difference = Vector.zero := by
      rw [differenceScale, coefficientZero, Vector.zero_scale]
    have testFixed : isometry.act test = test := by
      calc
        isometry.act test = Vector.add difference test := by
          ext <;> unfold difference Vector.add Vector.sub <;> ring1
        _ = Vector.add Vector.zero test := by rw [differenceIsZero]
        _ = test := Vector.zero_add test
    let reflection := form.reflectionIsometry third thirdNonNull
    let product := Isometry.mul isometry reflection
    have productDeterminantOne :
        Matrix3.determinant product.matrix = 1 := by
      change Matrix3.determinant
        (Matrix3.mul isometry.matrix
          (form.reflection third thirdNonNull)) = 1
      rw [Matrix3.determinant_mul, determinantMinusOne,
        form.determinant_reflection]
      ring1
    have productFixesFixed : product.act fixedVector = fixedVector := by
      rw [Isometry.act_mul, fixed]
      change Matrix3.rowMul fixedVector
        (form.reflection third thirdNonNull) = fixedVector
      apply form.rowMul_reflection_of_perpendicular
      exact fixedPerpendicularThird
    have productFixesTest : product.act test = test := by
      rw [Isometry.act_mul, testFixed]
      change Matrix3.rowMul test
        (form.reflection third thirdNonNull) = test
      apply form.rowMul_reflection_of_perpendicular
      exact testPerpendicularThird
    have productIdentity :
        product.matrix = Matrix3.identity :=
      Isometry.matrix_eq_identity_of_fixed_orthogonal_pair
        form product fixedVector test fixedVectorNonNull testNonNull
        fixedPerpendicularTest productFixesFixed productFixesTest
        productDeterminantOne
    have matrixEq :
        isometry.matrix = form.reflection third thirdNonNull := by
      calc
        isometry.matrix =
            Matrix3.mul isometry.matrix Matrix3.identity := by
          rw [Matrix3.mul_identity]
        _ = Matrix3.mul isometry.matrix
            (Matrix3.mul
              (form.reflection third thirdNonNull)
              (form.reflection third thirdNonNull)) := by
          rw [form.reflection_square]
        _ = Matrix3.mul
            (Matrix3.mul isometry.matrix
              (form.reflection third thirdNonNull))
            (form.reflection third thirdNonNull) := by
          rw [Matrix3.mul_assoc]
        _ = Matrix3.mul Matrix3.identity
            (form.reflection third thirdNonNull) := by
          exact congrArg
            (fun matrix => Matrix3.mul matrix
              (form.reflection third thirdNonNull))
            productIdentity
        _ = form.reflection third thirdNonNull :=
          Matrix3.identity_mul _
    exact
      { mirror := third
        mirrorNonNull := thirdNonNull
        mirrorPerpendicular :=
          form.cross_perpendicular_left fixedVector test
        matrix_eq := matrixEq }
  · let reflection := form.reflectionIsometry difference differenceNull
    let product := Isometry.mul isometry reflection
    have productDeterminantOne :
        Matrix3.determinant product.matrix = 1 := by
      change Matrix3.determinant
        (Matrix3.mul isometry.matrix
          (form.reflection difference differenceNull)) = 1
      rw [Matrix3.determinant_mul, determinantMinusOne,
        form.determinant_reflection]
      ring1
    have productFixesFixed : product.act fixedVector = fixedVector := by
      rw [Isometry.act_mul, fixed]
      change Matrix3.rowMul fixedVector
        (form.reflection difference differenceNull) = fixedVector
      apply form.rowMul_reflection_of_perpendicular
      exact fixedPerpendicularDifference
    have productFixesTest : product.act test = test := by
      rw [Isometry.act_mul]
      change Matrix3.rowMul (isometry.act test)
        (form.reflection
          (Vector.sub (isometry.act test) test) differenceNull) = test
      apply form.rowMul_reflection_difference
      exact isometry.quadrance_act test
    have productIdentity :
        product.matrix = Matrix3.identity :=
      Isometry.matrix_eq_identity_of_fixed_orthogonal_pair
        form product fixedVector test fixedVectorNonNull testNonNull
        fixedPerpendicularTest productFixesFixed productFixesTest
        productDeterminantOne
    have matrixEq :
        isometry.matrix = form.reflection difference differenceNull := by
      calc
        isometry.matrix =
            Matrix3.mul isometry.matrix Matrix3.identity := by
          rw [Matrix3.mul_identity]
        _ = Matrix3.mul isometry.matrix
            (Matrix3.mul
              (form.reflection difference differenceNull)
              (form.reflection difference differenceNull)) := by
          rw [form.reflection_square]
        _ = Matrix3.mul
            (Matrix3.mul isometry.matrix
              (form.reflection difference differenceNull))
            (form.reflection difference differenceNull) := by
          rw [Matrix3.mul_assoc]
        _ = Matrix3.mul Matrix3.identity
            (form.reflection difference differenceNull) := by
          exact congrArg
            (fun matrix => Matrix3.mul matrix
              (form.reflection difference differenceNull))
            productIdentity
        _ = form.reflection difference differenceNull :=
          Matrix3.identity_mul _
    exact
      { mirror := difference
        mirrorNonNull := differenceNull
        mirrorPerpendicular := differencePerpendicularFixed
        matrix_eq := matrixEq }

/-- Cached factorization of one displayed form rotation into two non-null
form-relative half turns.  This is the finite datum needed by the
Cartan--Dieudonne step of the general ternary theory. -/
structure TwoHalfTurnFactorization (form : TernaryForm K)
    (rotation : form.SpecialOrthogonal) where
  firstAxis : Vector K
  firstNonNull : form.quadrance firstAxis ≠ 0
  secondAxis : Vector K
  secondNonNull : form.quadrance secondAxis ≠ 0
  rotation_eq :
    SpecialOrthogonal.mul
        (form.halfTurnRotation firstAxis firstNonNull)
        (form.halfTurnRotation secondAxis secondNonNull) = rotation

/-- The identity has a canonical executable two-half-turn factorization:
select one of the six certified non-null coordinate candidates and use its
involutive half turn twice. -/
def identityTwoHalfTurnFactorization [DecidableEq K]
    (form : TernaryForm K) (twoNonzero : (2 : K) ≠ 0) :
    TwoHalfTurnFactorization form (SpecialOrthogonal.identity form) := by
  let selected := form.nonNullVectorWitness twoNonzero
  exact
    { firstAxis := selected.value
      firstNonNull := selected.nonNull
      secondAxis := selected.value
      secondNonNull := selected.nonNull
      rotation_eq := by
        apply SpecialOrthogonal.eq_of_matrix_eq
        exact form.halfTurn_square selected.value selected.nonNull }

/-- Every displayed ternary rotation in characteristic different from two
has an executable factorization into two half turns about non-null axes.
For a nonidentity rotation, the first reflection reduction fixes a selected
non-null seed; the fixed-vector classifier supplies the second reflection,
and the two minus signs converting reflections to half turns cancel. -/
def twoHalfTurnFactorization [DecidableEq K]
    (form : TernaryForm K) (rotation : form.SpecialOrthogonal)
    (twoNonzero : (2 : K) ≠ 0) :
    TwoHalfTurnFactorization form rotation := by
  by_cases rotationMatrixIdentity :
      rotation.matrix = Matrix3.identity
  · have rotationIdentity :
        rotation = SpecialOrthogonal.identity form := by
      apply SpecialOrthogonal.eq_of_matrix_eq
      exact rotationMatrixIdentity
    subst rotation
    exact identityTwoHalfTurnFactorization form twoNonzero
  · let displaced :=
      form.nonNullDisplacementWitness rotation (by
        intro rotationIdentity
        apply rotationMatrixIdentity
        exact congrArg (fun value : form.SpecialOrthogonal => value.matrix)
          rotationIdentity) twoNonzero
    let reduction :=
      form.displacementReflectionReduction rotation displaced.seed
        displaced.seedNonNull displaced.displacementNonNull
    let classification :=
      classifyFixedVectorReflection form reduction.reduced reduction.seed
        reduction.seedNonNull reduction.seedFixed
        reduction.determinantMinusOne twoNonzero
    have reducedMatrix :
        reduction.reduced.matrix =
          Matrix3.mul rotation.matrix
            (form.reflection reduction.mirror reduction.mirrorNonNull) := by
      exact congrArg (fun isometry : form.Isometry => isometry.matrix)
        reduction.reduced_eq
    exact
      { firstAxis := classification.mirror
        firstNonNull := classification.mirrorNonNull
        secondAxis := reduction.mirror
        secondNonNull := reduction.mirrorNonNull
        rotation_eq := by
          apply SpecialOrthogonal.eq_of_matrix_eq
          change Matrix3.mul
              (form.halfTurn classification.mirror
                classification.mirrorNonNull)
              (form.halfTurn reduction.mirror reduction.mirrorNonNull) =
            rotation.matrix
          unfold halfTurn
          rw [Matrix3.mul_neg_neg]
          calc
            Matrix3.mul
                (form.reflection classification.mirror
                  classification.mirrorNonNull)
                (form.reflection reduction.mirror reduction.mirrorNonNull) =
              Matrix3.mul reduction.reduced.matrix
                (form.reflection reduction.mirror reduction.mirrorNonNull) := by
                rw [classification.matrix_eq]
            _ = Matrix3.mul
                (Matrix3.mul rotation.matrix
                  (form.reflection reduction.mirror reduction.mirrorNonNull))
                (form.reflection reduction.mirror reduction.mirrorNonNull) := by
              rw [reducedMatrix]
            _ = Matrix3.mul rotation.matrix
                (Matrix3.mul
                  (form.reflection reduction.mirror reduction.mirrorNonNull)
                  (form.reflection reduction.mirror reduction.mirrorNonNull)) := by
              rw [Matrix3.mul_assoc]
            _ = Matrix3.mul rotation.matrix Matrix3.identity := by
              rw [form.reflection_square]
            _ = rotation.matrix := Matrix3.mul_identity rotation.matrix }

namespace TwoHalfTurnFactorization

/-- The product of the two cached pure-vector Clifford representatives. -/
def cliffordPreimage {form : TernaryForm K}
    {rotation : form.SpecialOrthogonal}
    (factorization : TwoHalfTurnFactorization form rotation) :
    form.NonNullEvenClifford :=
  NonNullEvenClifford.mul
    (NonNullEvenClifford.halfTurnValue form factorization.firstAxis
      factorization.firstNonNull)
    (NonNullEvenClifford.halfTurnValue form factorization.secondAxis
      factorization.secondNonNull)

/-- A cached two-half-turn factorization computes an explicit Clifford
preimage of its rotation. -/
theorem cliffordPreimage_actionRotation {form : TernaryForm K}
    {rotation : form.SpecialOrthogonal}
    (factorization : TwoHalfTurnFactorization form rotation) :
    factorization.cliffordPreimage.actionRotation = rotation := by
  calc
    factorization.cliffordPreimage.actionRotation =
        SpecialOrthogonal.mul
          (form.halfTurnRotation factorization.firstAxis
            factorization.firstNonNull)
          (form.halfTurnRotation factorization.secondAxis
            factorization.secondNonNull) :=
      (NonNullEvenClifford.halfTurnRotation_mul form
        factorization.firstAxis factorization.secondAxis
        factorization.firstNonNull factorization.secondNonNull).symm
    _ = rotation := factorization.rotation_eq

theorem identity_cliffordPreimage_equivalent_identity [DecidableEq K]
    (form : TernaryForm K) (twoNonzero : (2 : K) ≠ 0) :
    (identityTwoHalfTurnFactorization form twoNonzero).cliffordPreimage.Equivalent
      (NonNullEvenClifford.identity form) := by
  apply (NonNullEvenClifford.actionRotation_eq_iff_equivalent
    (identityTwoHalfTurnFactorization form twoNonzero).cliffordPreimage
    (NonNullEvenClifford.identity form) twoNonzero).1
  calc
    (identityTwoHalfTurnFactorization form twoNonzero).cliffordPreimage.actionRotation =
        SpecialOrthogonal.identity form :=
      (identityTwoHalfTurnFactorization form twoNonzero).cliffordPreimage_actionRotation
    _ = (NonNullEvenClifford.identity form).actionRotation :=
      (NonNullEvenClifford.actionRotation_identity form).symm

end TwoHalfTurnFactorization

/-- An executable two-half-turn generation algorithm for every displayed
special-orthogonal transformation of a ternary form.  The returned axes and
all denominator certificates are cached in each factorization. -/
structure TwoHalfTurnGeneration (form : TernaryForm K) where
  factor : (rotation : form.SpecialOrthogonal) →
    TwoHalfTurnFactorization form rotation

/-- The unconditional finite two-half-turn generation algorithm obtained by
running the constructive factorization above on every displayed rotation. -/
def twoHalfTurnGeneration [DecidableEq K]
    (form : TernaryForm K) (twoNonzero : (2 : K) ≠ 0) :
    TwoHalfTurnGeneration form where
  factor := fun rotation =>
    twoHalfTurnFactorization form rotation twoNonzero

namespace TwoHalfTurnGeneration

/-- Explicit Clifford representative computed by the cached factorization
algorithm. -/
def cliffordPreimage {form : TernaryForm K}
    (generation : TwoHalfTurnGeneration form)
    (rotation : form.SpecialOrthogonal) : form.NonNullEvenClifford :=
  (generation.factor rotation).cliffordPreimage

theorem cliffordPreimage_actionRotation {form : TernaryForm K}
    (generation : TwoHalfTurnGeneration form)
    (rotation : form.SpecialOrthogonal) :
    (generation.cliffordPreimage rotation).actionRotation = rotation :=
  (generation.factor rotation).cliffordPreimage_actionRotation

end TwoHalfTurnGeneration

/-- The generalized projective rotation correspondence, packaged without a
quotient.  Surjectivity is an executable preimage function, while each fiber
is characterized by a displayed nonzero projective scale. -/
structure ProjectiveCliffordCorrespondence (form : TernaryForm K)
    (twoNonzero : (2 : K) ≠ 0) where
  preimage : form.SpecialOrthogonal → form.NonNullEvenClifford
  action_preimage : ∀ rotation : form.SpecialOrthogonal,
    (preimage rotation).actionRotation = rotation
  action_eq_iff_equivalent :
    ∀ left right : form.NonNullEvenClifford,
      left.actionRotation = right.actionRotation ↔ left.Equivalent right

/-- Once the finite two-half-turn algorithm is supplied, the Clifford action
is constructively surjective and projectively faithful.  This isolates the
remaining general-form work in one explicit factorization interface. -/
def TwoHalfTurnGeneration.projectiveCliffordCorrespondence
    {form : TernaryForm K} (generation : TwoHalfTurnGeneration form)
    (twoNonzero : (2 : K) ≠ 0) :
    ProjectiveCliffordCorrespondence form twoNonzero where
  preimage := generation.cliffordPreimage
  action_preimage := generation.cliffordPreimage_actionRotation
  action_eq_iff_equivalent := fun left right =>
    NonNullEvenClifford.actionRotation_eq_iff_equivalent
      left right twoNonzero

/-- The unconditional generalized projective rotation theorem for every
displayed nondegenerate ternary form in characteristic different from two.
It contains an executable Clifford preimage for every special-orthogonal
matrix and the exact nonzero-scale description of every fiber. -/
def projectiveCliffordCorrespondence [DecidableEq K]
    (form : TernaryForm K) (twoNonzero : (2 : K) ≠ 0) :
    ProjectiveCliffordCorrespondence form twoNonzero :=
  (twoHalfTurnGeneration form twoNonzero).projectiveCliffordCorrespondence
    twoNonzero

/-- Pointwise surjectivity extracted from the constructive projective
Clifford correspondence. -/
theorem cliffordAction_surjective [DecidableEq K]
    (form : TernaryForm K) (twoNonzero : (2 : K) ≠ 0)
    (rotation : form.SpecialOrthogonal) :
    ((projectiveCliffordCorrespondence form twoNonzero).preimage
        rotation).actionRotation = rotation :=
  (projectiveCliffordCorrespondence form twoNonzero).action_preimage rotation

end TernaryForm

end RationalRotations
