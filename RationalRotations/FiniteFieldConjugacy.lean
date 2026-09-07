import RationalRotations.FiniteFieldCounting

/-!
# Constructive conjugacy classification of finite-field parabolics

Problem 69 asks for the parabolic classes over the null directions.  The
counting layer gives unique null-direction and scalar coordinates.  This
module proves the stronger conjugacy-orbit interpretation: over every
displayed odd finite field, all nonidentity parabolic rotations form one
conjugacy class.  The conjugator is built from finitely selected reflections;
no quotient, basis extension, or choice principle is used.
-/

namespace RationalRotations

variable {K : Type*} [RFAP.ExplicitField K]

private theorem finiteConjugacy_eq_zero_of_nonzero_mul_eq_zero
    {factor value : K} (factorNonzero : factor ≠ 0)
    (productZero : factor * value = 0) : value = 0 := by
  have cancel := RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    value = (factor * factor⁻¹) * value := by rw [cancel, one_mul]
    _ = factor⁻¹ * (factor * value) := by ring1
    _ = 0 := by rw [productZero, mul_zero]

private theorem finiteConjugacy_eq_zero_of_square_eq_zero [DecidableEq K]
    {value : K} (squareZero : value ^ 2 = 0) : value = 0 := by
  by_cases valueZero : value = 0
  · exact valueZero
  · have squareNonzero : value ^ 2 ≠ 0 := by
      simpa only [pow_two] using
        RFAP.ExplicitField.mul_ne_zero valueZero valueZero
    exact (squareNonzero squareZero).elim

/-- In a nonisotropic displayed binary direction, an isotropic perpendicular
pair must vanish.  This two-coordinate lemma is the constructive core of the
null-line rigidity argument. -/
private theorem pair_eq_zero_of_null_of_perpendicular [DecidableEq K]
    (first second left right : K)
    (baseNonNull : first ^ 2 + second ^ 2 ≠ 0)
    (perpendicular : first * left + second * right = 0)
    (null : left ^ 2 + right ^ 2 = 0) :
    left = 0 ∧ right = 0 := by
  let determinant := first * right - second * left
  have determinantSquare : determinant ^ 2 = 0 := by
    calc
      determinant ^ 2 =
          (first ^ 2 + second ^ 2) * (left ^ 2 + right ^ 2) -
            (first * left + second * right) ^ 2 := by
        unfold determinant
        ring1
      _ = 0 := by rw [null, perpendicular]; ring1
  have determinantZero : determinant = 0 :=
    finiteConjugacy_eq_zero_of_square_eq_zero determinantSquare
  constructor
  · apply finiteConjugacy_eq_zero_of_nonzero_mul_eq_zero baseNonNull
    calc
      (first ^ 2 + second ^ 2) * left =
          first * (first * left + second * right) -
            second * determinant := by
        unfold determinant
        ring1
      _ = 0 := by rw [perpendicular, determinantZero]; ring1
  · apply finiteConjugacy_eq_zero_of_nonzero_mul_eq_zero baseNonNull
    calc
      (first ^ 2 + second ^ 2) * right =
          second * (first * left + second * right) +
            first * determinant := by
        unfold determinant
        ring1
      _ = 0 := by rw [perpendicular, determinantZero]; ring1

/-- Executable scale data for two vectors on the same displayed line. -/
structure NullLineScale (source target : Vector K) where
  factor : K
  target_eq : target = Vector.scale factor source

/-- Two null vectors perpendicular to one another lie on the same displayed
null line.  The scalar is computed from the first nonzero coordinate of the
source, and the remaining two coordinates are discharged by the binary
rigidity lemma above. -/
def nullLineScaleOfPerpendicular [DecidableEq K]
    (source target : Vector K)
    (sourceNull : source.quadrance = 0)
    (sourceNonzero : source ≠ Vector.zero)
    (targetNull : target.quadrance = 0)
    (perpendicular : Vector.dot source target = 0) :
    NullLineScale source target := by
  by_cases sourceTNonzero : source.t ≠ 0
  · let factor := source.t⁻¹ * target.t
    have sourceTCancel :=
      RFAP.ExplicitField.mul_inv_cancel source.t sourceTNonzero
    have targetT : target.t = factor * source.t := by
      calc
        target.t = 1 * target.t := by ring1
        _ = (source.t * source.t⁻¹) * target.t := by rw [sourceTCancel]
        _ = factor * source.t := by unfold factor; ring1
    let differenceR := target.r - factor * source.r
    let differenceS := target.s - factor * source.s
    have tailNonNull : source.r ^ 2 + source.s ^ 2 ≠ 0 := by
      intro tailZero
      have sourceTSquareZero : source.t ^ 2 = 0 := by
        calc
          source.t ^ 2 = source.quadrance -
              (source.r ^ 2 + source.s ^ 2) := by
            unfold Vector.quadrance Vector.dot
            ring1
          _ = 0 := by rw [sourceNull, tailZero]; ring1
      have sourceTSquareNonzero : source.t ^ 2 ≠ 0 := by
        simpa only [pow_two] using
          RFAP.ExplicitField.mul_ne_zero sourceTNonzero sourceTNonzero
      exact sourceTSquareNonzero sourceTSquareZero
    have tailPerpendicular :
        source.r * differenceR + source.s * differenceS = 0 := by
      calc
        source.r * differenceR + source.s * differenceS =
            (source.t * target.t + source.r * target.r +
              source.s * target.s) -
              factor * (source.t * source.t + source.r * source.r +
                source.s * source.s) -
              source.t * (target.t - factor * source.t) := by
          unfold differenceR differenceS
          ring1
        _ = 0 := by
          change source.t * target.t + source.r * target.r +
            source.s * target.s = 0 at perpendicular
          change source.t * source.t + source.r * source.r +
            source.s * source.s = 0 at sourceNull
          rw [perpendicular, sourceNull, targetT]
          ring1
    have tailNull : differenceR ^ 2 + differenceS ^ 2 = 0 := by
      calc
        differenceR ^ 2 + differenceS ^ 2 =
            (target.t - factor * source.t) ^ 2 +
              differenceR ^ 2 + differenceS ^ 2 := by
          rw [targetT]
          ring1
        _ = (target.t * target.t + target.r * target.r +
              target.s * target.s) -
              2 * factor * (source.t * target.t + source.r * target.r +
                source.s * target.s) +
                factor ^ 2 * (source.t * source.t +
                  source.r * source.r + source.s * source.s) := by
          unfold differenceR differenceS
          ring1
        _ = 0 := by
          change target.t * target.t + target.r * target.r +
            target.s * target.s = 0 at targetNull
          change source.t * target.t + source.r * target.r +
            source.s * target.s = 0 at perpendicular
          change source.t * source.t + source.r * source.r +
            source.s * source.s = 0 at sourceNull
          rw [targetNull, perpendicular, sourceNull]
          ring1
    have tailZero := pair_eq_zero_of_null_of_perpendicular
      source.r source.s differenceR differenceS tailNonNull
      tailPerpendicular tailNull
    refine ⟨factor, ?_⟩
    apply Vector.ext
    · exact targetT
    · change target.r = factor * source.r
      have := tailZero.1
      unfold differenceR at this
      calc
        target.r = (target.r - factor * source.r) +
            factor * source.r := by ring1
        _ = factor * source.r := by rw [this]; ring1
    · change target.s = factor * source.s
      have := tailZero.2
      unfold differenceS at this
      calc
        target.s = (target.s - factor * source.s) +
            factor * source.s := by ring1
        _ = factor * source.s := by rw [this]; ring1

  · have sourceTZero : source.t = 0 := by
      cases (inferInstance : DecidableEq K) source.t 0 with
      | isTrue equal => exact equal
      | isFalse different => exact False.elim (sourceTNonzero different)
    have sourceRNonzero : source.r ≠ 0 := by
      intro sourceRZero
      have sourceSSquareZero : source.s ^ 2 = 0 := by
        calc
          source.s ^ 2 = source.quadrance := by
            unfold Vector.quadrance Vector.dot
            rw [sourceTZero, sourceRZero]
            ring1
          _ = 0 := sourceNull
      have sourceSZero :=
        finiteConjugacy_eq_zero_of_square_eq_zero sourceSSquareZero
      apply sourceNonzero
      apply Vector.ext
      · exact sourceTZero
      · exact sourceRZero
      · exact sourceSZero
    let factor := source.r⁻¹ * target.r
    have sourceRCancel :=
      RFAP.ExplicitField.mul_inv_cancel source.r sourceRNonzero
    have targetR : target.r = factor * source.r := by
      calc
        target.r = 1 * target.r := by ring1
        _ = (source.r * source.r⁻¹) * target.r := by rw [sourceRCancel]
        _ = factor * source.r := by unfold factor; ring1
    let differenceT := target.t - factor * source.t
    let differenceS := target.s - factor * source.s
    have outsideNonNull : source.t ^ 2 + source.s ^ 2 ≠ 0 := by
      intro outsideZero
      have sourceRSquareZero : source.r ^ 2 = 0 := by
        calc
          source.r ^ 2 = source.quadrance -
              (source.t ^ 2 + source.s ^ 2) := by
            unfold Vector.quadrance Vector.dot
            ring1
          _ = 0 := by rw [sourceNull, outsideZero]; ring1
      have sourceRSquareNonzero : source.r ^ 2 ≠ 0 := by
        simpa only [pow_two] using
          RFAP.ExplicitField.mul_ne_zero sourceRNonzero sourceRNonzero
      exact sourceRSquareNonzero sourceRSquareZero
    have outsidePerpendicular :
        source.t * differenceT + source.s * differenceS = 0 := by
      calc
        source.t * differenceT + source.s * differenceS =
            (source.t * target.t + source.r * target.r +
              source.s * target.s) -
              factor * (source.t * source.t + source.r * source.r +
                source.s * source.s) -
              source.r * (target.r - factor * source.r) := by
          unfold differenceT differenceS
          ring1
        _ = 0 := by
          change source.t * target.t + source.r * target.r +
            source.s * target.s = 0 at perpendicular
          change source.t * source.t + source.r * source.r +
            source.s * source.s = 0 at sourceNull
          rw [perpendicular, sourceNull, targetR]
          ring1
    have outsideNull : differenceT ^ 2 + differenceS ^ 2 = 0 := by
      calc
        differenceT ^ 2 + differenceS ^ 2 =
            differenceT ^ 2 +
              (target.r - factor * source.r) ^ 2 +
                differenceS ^ 2 := by
          rw [targetR]
          ring1
        _ = (target.t * target.t + target.r * target.r +
              target.s * target.s) -
              2 * factor * (source.t * target.t + source.r * target.r +
                source.s * target.s) +
                factor ^ 2 * (source.t * source.t +
                  source.r * source.r + source.s * source.s) := by
          unfold differenceT differenceS
          ring1
        _ = 0 := by
          change target.t * target.t + target.r * target.r +
            target.s * target.s = 0 at targetNull
          change source.t * target.t + source.r * target.r +
            source.s * target.s = 0 at perpendicular
          change source.t * source.t + source.r * source.r +
            source.s * source.s = 0 at sourceNull
          rw [targetNull, perpendicular, sourceNull]
          ring1
    have outsideZero := pair_eq_zero_of_null_of_perpendicular
      source.t source.s differenceT differenceS outsideNonNull
      outsidePerpendicular outsideNull
    refine ⟨factor, ?_⟩
    apply Vector.ext
    · change target.t = factor * source.t
      have := outsideZero.1
      unfold differenceT at this
      calc
        target.t = (target.t - factor * source.t) +
            factor * source.t := by ring1
        _ = factor * source.t := by rw [this]; ring1
    · exact targetR
    · change target.s = factor * source.s
      have := outsideZero.2
      unfold differenceS at this
      calc
        target.s = (target.s - factor * source.s) +
            factor * source.s := by ring1
        _ = factor * source.s := by rw [this]; ring1

/-- Propositional form of the executable null-line scale classification. -/
theorem null_eq_scale_of_perpendicular [DecidableEq K]
    (source target : Vector K)
    (sourceNull : source.quadrance = 0)
    (sourceNonzero : source ≠ Vector.zero)
    (targetNull : target.quadrance = 0)
    (perpendicular : Vector.dot source target = 0) :
    ∃ factor : K, target = Vector.scale factor source := by
  let scaling := nullLineScaleOfPerpendicular source target sourceNull
    sourceNonzero targetNull perpendicular
  exact ⟨scaling.factor, scaling.target_eq⟩

/-- A cached null partner with nonzero pairing.  Two explicit sign changes
cover every nonzero null vector in characteristic different from two. -/
structure NullPartner (source : Vector K) where
  value : Vector K
  valueNull : value.quadrance = 0
  pairingNonzero : Vector.dot source value ≠ 0

/-- Construct a null partner by changing the sign of `s` when it is nonzero,
and otherwise changing the sign of `r`. -/
def nullPartner [DecidableEq K]
    (source : Vector K) (sourceNull : source.quadrance = 0)
    (sourceNonzero : source ≠ Vector.zero) (twoNonzero : (2 : K) ≠ 0) :
    NullPartner source := by
  by_cases sourceSNonzero : source.s ≠ 0
  · let partner : Vector K := ⟨source.t, source.r, -source.s⟩
    have sourceEquation : source.t * source.t + source.r * source.r +
        source.s * source.s = 0 := by
      simpa only [Vector.quadrance, Vector.dot] using sourceNull
    refine
      { value := partner
        valueNull := ?_
        pairingNonzero := ?_ }
    · change source.t * source.t + source.r * source.r +
        (-source.s) * (-source.s) = 0
      calc
        source.t * source.t + source.r * source.r +
            (-source.s) * (-source.s) =
          source.t * source.t + source.r * source.r +
            source.s * source.s := by ring1
        _ = 0 := sourceEquation
    · have sourceSSquareNonzero : source.s ^ 2 ≠ 0 := by
        simpa only [pow_two] using
          RFAP.ExplicitField.mul_ne_zero sourceSNonzero sourceSNonzero
      have twiceSquareNonzero : (2 : K) * source.s ^ 2 ≠ 0 :=
        RFAP.ExplicitField.mul_ne_zero twoNonzero sourceSSquareNonzero
      intro pairingZero
      apply twiceSquareNonzero
      calc
        2 * source.s ^ 2 = -Vector.dot source partner := by
          calc
            2 * source.s ^ 2 =
                -(source.t * source.t + source.r * source.r -
                    source.s * source.s) := by
              calc
                2 * source.s ^ 2 = 2 * source.s ^ 2 -
                    (source.t * source.t + source.r * source.r +
                      source.s * source.s) := by
                  rw [sourceEquation]
                  ring1
                _ = -(source.t * source.t + source.r * source.r -
                    source.s * source.s) := by ring1
            _ = -Vector.dot source partner := by
              unfold partner Vector.dot
              ring1
        _ = 0 := by rw [pairingZero]; ring1
  · have sourceSZero : source.s = 0 := by
      cases (inferInstance : DecidableEq K) source.s 0 with
      | isTrue equal => exact equal
      | isFalse different => exact False.elim (sourceSNonzero different)
    have sourceTNonzero : source.t ≠ 0 := by
      intro sourceTZero
      have sourceRSquareZero : source.r ^ 2 = 0 := by
        calc
          source.r ^ 2 = source.quadrance := by
            unfold Vector.quadrance Vector.dot
            rw [sourceTZero, sourceSZero]
            ring1
          _ = 0 := sourceNull
      have sourceRZero :=
        finiteConjugacy_eq_zero_of_square_eq_zero sourceRSquareZero
      apply sourceNonzero
      apply Vector.ext
      · exact sourceTZero
      · exact sourceRZero
      · exact sourceSZero
    let partner : Vector K := ⟨source.t, -source.r, 0⟩
    have sourceEquation : source.t * source.t + source.r * source.r = 0 := by
      change source.t * source.t + source.r * source.r +
        source.s * source.s = 0 at sourceNull
      rw [sourceSZero] at sourceNull
      simpa only [zero_mul, add_zero] using sourceNull
    refine
      { value := partner
        valueNull := ?_
        pairingNonzero := ?_ }
    · change source.t * source.t + (-source.r) * (-source.r) + 0 * 0 = 0
      calc
        source.t * source.t + (-source.r) * (-source.r) + 0 * 0 =
            source.t * source.t + source.r * source.r := by ring1
        _ = 0 := sourceEquation
    · have sourceTSquareNonzero : source.t ^ 2 ≠ 0 := by
        simpa only [pow_two] using
          RFAP.ExplicitField.mul_ne_zero sourceTNonzero sourceTNonzero
      have twiceSquareNonzero : (2 : K) * source.t ^ 2 ≠ 0 :=
        RFAP.ExplicitField.mul_ne_zero twoNonzero sourceTSquareNonzero
      intro pairingZero
      apply twiceSquareNonzero
      calc
        2 * source.t ^ 2 = Vector.dot source partner := by
          calc
            2 * source.t ^ 2 =
                source.t * source.t - source.r * source.r := by
              calc
                2 * source.t ^ 2 = 2 * source.t ^ 2 -
                    (source.t * source.t + source.r * source.r) := by
                  rw [sourceEquation]
                  ring1
                _ = source.t * source.t - source.r * source.r := by
                  ring1
            _ = Vector.dot source partner := by
              unfold partner Vector.dot
              rw [sourceSZero]
              ring1
        _ = 0 := pairingZero

/-- Quadrance of a displayed vector difference. -/
theorem quadrance_sub_expansion (left right : Vector K) :
    (Vector.sub left right).quadrance =
      left.quadrance - 2 * Vector.dot left right + right.quadrance := by
  simp only [Vector.quadrance]
  unfold Vector.dot Vector.sub
  ring1

/-- Reflection in the non-null difference of two equal-quadrance vectors
maps the first vector to the second. -/
theorem rowMul_reflection_difference
    (first second : Vector K)
    (equalQuadrance : first.quadrance = second.quadrance)
    (differenceNonNull :
      (Vector.sub first second).quadrance ≠ 0) :
    Matrix3.rowMul first
        (reflection (Vector.sub first second) differenceNonNull) = second := by
  have twicePairing :
      2 * Vector.dot first (Vector.sub first second) =
        (Vector.sub first second).quadrance := by
    calc
      2 * Vector.dot first (Vector.sub first second) =
          2 * (first.quadrance - Vector.dot first second) := by
        simp only [Vector.quadrance]
        unfold Vector.dot Vector.sub
        ring1
      _ = first.quadrance - 2 * Vector.dot first second +
          second.quadrance := by
        rw [← equalQuadrance]
        ring1
      _ = (Vector.sub first second).quadrance :=
        (quadrance_sub_expansion first second).symm
  have cancel := RFAP.ExplicitField.mul_inv_cancel
    (Vector.sub first second).quadrance differenceNonNull
  have coefficient :
      2 * Vector.dot first (Vector.sub first second) /
          (Vector.sub first second).quadrance = 1 := by
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    rw [twicePairing, cancel]
  rw [rowMul_reflection, coefficient]
  ext <;> unfold Vector.sub Vector.scale <;> ring1

/-- A displayed special-orthogonal transformation carrying one nonzero null
vector to another. -/
structure NullVectorTransport (source target : Vector K) where
  rotation : Rotation K
  maps : Matrix3.rowMul source rotation.matrix = target

/-- Construct a null-vector transport from two reflections.  If the two null
vectors have nonzero pairing, reflection in their difference performs the
move and a perpendicular reflection corrects orientation.  If their pairing
vanishes, null-line rigidity gives the exact scale and a selected null
partner supplies a non-null two-reflection route through its negative. -/
def nullVectorTransport [DecidableEq K]
    (source target : Vector K)
    (sourceNull : source.quadrance = 0)
    (sourceNonzero : source ≠ Vector.zero)
    (targetNull : target.quadrance = 0)
    (targetNonzero : target ≠ Vector.zero)
    (twoNonzero : (2 : K) ≠ 0) :
    NullVectorTransport source target := by
  by_cases pairingNonzero : Vector.dot source target ≠ 0
  · let difference := Vector.sub source target
    have differenceQuadrance : difference.quadrance =
        -2 * Vector.dot source target := by
      unfold difference
      rw [quadrance_sub_expansion, sourceNull, targetNull]
      ring1
    have differenceNonNull : difference.quadrance ≠ 0 := by
      rw [differenceQuadrance]
      exact RFAP.ExplicitField.mul_ne_zero
        (neg_ne_zero.mpr twoNonzero) pairingNonzero
    let perpendicular := perpendicularNonNullWitness target twoNonzero
    have targetPerpendicular :
        target.Perpendicular perpendicular.value := by
      unfold Vector.Perpendicular at perpendicular ⊢
      rw [Vector.dot_comm]
      exact perpendicular.perpendicular
    refine
      { rotation := reflectionProductRotation difference perpendicular.value
          differenceNonNull perpendicular.nonNull
        maps := ?_ }
    change Matrix3.rowMul source
        (Matrix3.mul (reflection difference differenceNonNull)
          (reflection perpendicular.value perpendicular.nonNull)) = target
    rw [← Matrix3.rowMul_mul]
    change Matrix3.rowMul
        (Matrix3.rowMul source
          (reflection (Vector.sub source target) differenceNonNull))
        (reflection perpendicular.value perpendicular.nonNull) = target
    rw [rowMul_reflection_difference source target
      (sourceNull.trans targetNull.symm) differenceNonNull]
    exact (rowMul_reflection_eq_iff_perpendicular perpendicular.value
      perpendicular.nonNull twoNonzero target).2 targetPerpendicular
  · have pairingZero : Vector.dot source target = 0 := by
      cases (inferInstance : DecidableEq K) (Vector.dot source target) 0 with
      | isTrue equal => exact equal
      | isFalse different => exact False.elim (pairingNonzero different)
    let scaling := nullLineScaleOfPerpendicular source target sourceNull
      sourceNonzero targetNull pairingZero
    let factor := scaling.factor
    have targetScale : target = Vector.scale factor source := scaling.target_eq
    have factorNonzero : factor ≠ 0 := by
      intro factorZero
      apply targetNonzero
      calc
        target = Vector.scale factor source := targetScale
        _ = Vector.scale 0 source := by rw [factorZero]
        _ = Vector.zero := Vector.zero_scale source
    let partner := nullPartner source sourceNull sourceNonzero twoNonzero
    let intermediate := Vector.neg partner.value
    let firstMirror := Vector.sub source intermediate
    let secondMirror := Vector.sub intermediate target
    have intermediateNull : intermediate.quadrance = 0 := by
      unfold intermediate
      rw [Vector.quadrance_neg, partner.valueNull]
    have intermediateNonzero : intermediate ≠ Vector.zero := by
      intro intermediateZero
      apply partner.pairingNonzero
      calc
        Vector.dot source partner.value =
            -Vector.dot source intermediate := by
          unfold intermediate
          rw [Vector.dot_neg_right]
          ring1
        _ = 0 := by rw [intermediateZero, Vector.dot_zero_right]; ring1
    have sourceIntermediatePairing :
        Vector.dot source intermediate =
          -Vector.dot source partner.value := by
      unfold intermediate
      rw [Vector.dot_neg_right]
    have intermediateTargetPairing :
        Vector.dot intermediate target =
          -factor * Vector.dot source partner.value := by
      rw [targetScale, Vector.dot_scale_right]
      unfold intermediate
      rw [Vector.dot_neg_left, Vector.dot_comm partner.value source]
      ring1
    have firstMirrorQuadrance : firstMirror.quadrance =
        2 * Vector.dot source partner.value := by
      unfold firstMirror
      rw [quadrance_sub_expansion, sourceNull, intermediateNull,
        sourceIntermediatePairing]
      ring1
    have firstMirrorNonNull : firstMirror.quadrance ≠ 0 := by
      rw [firstMirrorQuadrance]
      exact RFAP.ExplicitField.mul_ne_zero twoNonzero
        partner.pairingNonzero
    have secondMirrorQuadrance : secondMirror.quadrance =
        2 * factor * Vector.dot source partner.value := by
      unfold secondMirror
      rw [quadrance_sub_expansion, intermediateNull, targetNull,
        intermediateTargetPairing]
      ring1
    have secondMirrorNonNull : secondMirror.quadrance ≠ 0 := by
      rw [secondMirrorQuadrance]
      exact RFAP.ExplicitField.mul_ne_zero
        (RFAP.ExplicitField.mul_ne_zero twoNonzero factorNonzero)
        partner.pairingNonzero
    refine
      { rotation := reflectionProductRotation firstMirror secondMirror
          firstMirrorNonNull secondMirrorNonNull
        maps := ?_ }
    change Matrix3.rowMul source
        (Matrix3.mul (reflection firstMirror firstMirrorNonNull)
          (reflection secondMirror secondMirrorNonNull)) = target
    rw [← Matrix3.rowMul_mul]
    change Matrix3.rowMul
        (Matrix3.rowMul source
          (reflection (Vector.sub source intermediate)
            firstMirrorNonNull))
        (reflection (Vector.sub intermediate target)
          secondMirrorNonNull) = target
    rw [rowMul_reflection_difference source intermediate
      (sourceNull.trans intermediateNull.symm) firstMirrorNonNull]
    exact rowMul_reflection_difference intermediate target
      (intermediateNull.trans targetNull.symm) secondMirrorNonNull

/-- The displayed cross-product transformation law for an arbitrary matrix.
The adjugate transpose is the denominator-free inverse-transpose factor. -/
theorem cross_rowMul_matrix (left right : Vector K) (matrix : Matrix3 K) :
    Vector.cross (Matrix3.rowMul left matrix)
        (Matrix3.rowMul right matrix) =
      Matrix3.rowMul (Vector.cross left right)
        (Matrix3.transpose (Matrix3.adjugate matrix)) := by
  ext <;> unfold Vector.cross Matrix3.rowMul Matrix3.transpose
    Matrix3.adjugate <;> ring1

/-- Proper orthogonal matrices preserve the displayed cross product. -/
theorem cross_rowMul_rotation (rotation : Rotation K)
    (left right : Vector K) :
    Vector.cross (Matrix3.rowMul left rotation.matrix)
        (Matrix3.rowMul right rotation.matrix) =
      Matrix3.rowMul (Vector.cross left right) rotation.matrix := by
  rw [cross_rowMul_matrix, adjugate_rotation,
    Matrix3.transpose_transpose]

/-- Conjugating an anchor by a displayed rotation transports its vector by
that rotation. -/
theorem anchor_conjugate_rotation (rotation : Rotation K)
    (vector : Vector K) :
    Matrix3.mul
        (Matrix3.mul (Matrix3.transpose rotation.matrix) (anchor vector))
        rotation.matrix =
      anchor (Matrix3.rowMul vector rotation.matrix) := by
  apply Matrix3.eq_of_rowMul_eq
  intro test
  calc
    Matrix3.rowMul test
        (Matrix3.mul
          (Matrix3.mul (Matrix3.transpose rotation.matrix) (anchor vector))
          rotation.matrix) =
      Matrix3.rowMul
        (Matrix3.rowMul
          (Matrix3.rowMul test (Matrix3.transpose rotation.matrix))
          (anchor vector)) rotation.matrix := by
      ext <;> unfold Matrix3.rowMul Matrix3.mul <;> ring1
    _ = Matrix3.rowMul
        (Vector.cross vector
          (Matrix3.rowMul test (Matrix3.transpose rotation.matrix)))
        rotation.matrix := by
      rw [rowMul_anchor]
    _ = Vector.cross (Matrix3.rowMul vector rotation.matrix)
        (Matrix3.rowMul
          (Matrix3.rowMul test (Matrix3.transpose rotation.matrix))
          rotation.matrix) :=
      (cross_rowMul_rotation rotation vector
        (Matrix3.rowMul test (Matrix3.transpose rotation.matrix))).symm
    _ = Vector.cross (Matrix3.rowMul vector rotation.matrix) test := by
      rw [Matrix3.rowMul_mul, transpose_mul_rotation,
        Matrix3.rowMul_identity]
    _ = Matrix3.rowMul test
        (anchor (Matrix3.rowMul vector rotation.matrix)) :=
      (rowMul_anchor _ _).symm

/-- The cap denominator is invariant under a displayed rotation. -/
theorem capDenominator_rowMul_rotation (rotation : Rotation K)
    (vector : Vector K) :
    capDenominator (Matrix3.rowMul vector rotation.matrix) =
      capDenominator vector := by
  unfold capDenominator
  rw [quadrance_rowMul_rotation]

/-- Cayley caps are equivariant under displayed rotation conjugation. -/
theorem cap_conjugate_rotation (rotation : Rotation K)
    (vector : Vector K) (defined : capDenominator vector ≠ 0)
    (transformedDefined :
      capDenominator (Matrix3.rowMul vector rotation.matrix) ≠ 0) :
    Matrix3.mul
        (Matrix3.mul (Matrix3.transpose rotation.matrix)
          (cap vector defined)) rotation.matrix =
      cap (Matrix3.rowMul vector rotation.matrix) transformedDefined := by
  let matrix := rotation.matrix
  let inverse := Matrix3.transpose rotation.matrix
  let sourceAnchor := anchor vector
  let targetAnchor := anchor (Matrix3.rowMul vector rotation.matrix)
  have inverseMul : Matrix3.mul inverse matrix = Matrix3.identity := by
    unfold inverse matrix
    exact transpose_mul_rotation rotation
  have matrixInverse : Matrix3.mul matrix inverse = Matrix3.identity := by
    unfold inverse matrix
    exact rotation.orthogonal
  have anchorConjugate :
      Matrix3.mul (Matrix3.mul inverse sourceAnchor) matrix =
        targetAnchor := by
    unfold inverse matrix sourceAnchor targetAnchor
    exact anchor_conjugate_rotation rotation vector
  have squareConjugate :
      Matrix3.mul
          (Matrix3.mul inverse
            (Matrix3.mul sourceAnchor sourceAnchor)) matrix =
        Matrix3.mul targetAnchor targetAnchor := by
    calc
      Matrix3.mul
          (Matrix3.mul inverse
            (Matrix3.mul sourceAnchor sourceAnchor)) matrix =
        Matrix3.mul (Matrix3.mul inverse sourceAnchor)
          (Matrix3.mul sourceAnchor matrix) := by
        ext <;> unfold Matrix3.mul <;> ring1
      _ = Matrix3.mul (Matrix3.mul inverse sourceAnchor)
          (Matrix3.mul Matrix3.identity
            (Matrix3.mul sourceAnchor matrix)) := by
        rw [Matrix3.identity_mul]
      _ = Matrix3.mul (Matrix3.mul inverse sourceAnchor)
          (Matrix3.mul (Matrix3.mul matrix inverse)
            (Matrix3.mul sourceAnchor matrix)) := by
        rw [matrixInverse]
      _ = Matrix3.mul
          (Matrix3.mul (Matrix3.mul inverse sourceAnchor) matrix)
          (Matrix3.mul inverse
            (Matrix3.mul sourceAnchor matrix)) := by
        ext <;> unfold Matrix3.mul <;> ring1
      _ = Matrix3.mul
          (Matrix3.mul (Matrix3.mul inverse sourceAnchor) matrix)
          (Matrix3.mul (Matrix3.mul inverse sourceAnchor) matrix) := by
        ext <;> unfold Matrix3.mul <;> ring1
      _ = Matrix3.mul targetAnchor targetAnchor := by
        rw [anchorConjugate]
  have denominatorEq :
      capDenominator (Matrix3.rowMul vector rotation.matrix) =
        capDenominator vector :=
    capDenominator_rowMul_rotation rotation vector
  unfold cap
  rw [denominatorEq]
  calc
    Matrix3.mul
        (Matrix3.mul inverse
          (Matrix3.add Matrix3.identity
            (Matrix3.scale (2 / capDenominator vector)
              (Matrix3.add sourceAnchor
                (Matrix3.mul sourceAnchor sourceAnchor))))) matrix =
      Matrix3.add
        (Matrix3.mul (Matrix3.mul inverse Matrix3.identity) matrix)
        (Matrix3.scale (2 / capDenominator vector)
          (Matrix3.add
            (Matrix3.mul (Matrix3.mul inverse sourceAnchor) matrix)
            (Matrix3.mul
              (Matrix3.mul inverse
                (Matrix3.mul sourceAnchor sourceAnchor)) matrix))) := by
      ext <;> unfold Matrix3.mul Matrix3.add Matrix3.scale <;> ring1
    _ = Matrix3.add Matrix3.identity
        (Matrix3.scale (2 / capDenominator vector)
          (Matrix3.add targetAnchor
            (Matrix3.mul targetAnchor targetAnchor))) := by
      rw [Matrix3.mul_identity, inverseMul, anchorConjugate,
        squareConjugate]

/-- Cap matrices ignore the proof object certifying a fixed vector's
denominator once the vectors themselves are equal. -/
theorem cap_eq_of_vector_eq {left right : Vector K}
    (equal : left = right)
    (leftDefined : capDenominator left ≠ 0)
    (rightDefined : capDenominator right ≠ 0) :
    cap left leftDefined = cap right rightDefined := by
  subst right
  rfl

namespace FiniteOddFieldPresentation

variable (presentation : FiniteOddFieldPresentation K)

private theorem oneNonzero
    (presentation : FiniteOddFieldPresentation K) : (1 : K) ≠ 0 := by
  intro oneZero
  apply presentation.twoNonzero
  calc
    (2 : K) = 1 + 1 := by ring1
    _ = 0 := by rw [oneZero, zero_add]

/-- Cached conjugator between two specified rotations.  The equation uses
the paper's row-vector convention, so the displayed conjugate is
`gᵀ * left * g`. -/
structure ParabolicConjugacyWitness
    (presentation : FiniteOddFieldPresentation K)
    (left right : Rotation K) where
  conjugator : Rotation K
  conjugates :
    Matrix3.mul
        (Matrix3.mul (Matrix3.transpose conjugator.matrix) left.matrix)
        conjugator.matrix = right.matrix

/-- Every two nonidentity half-spread-zero rotations over a displayed odd
finite field are constructively conjugate.  Their unique affine null anchors
are recovered first; the two-reflection null-vector transport then supplies
the displayed conjugator. -/
def parabolicConjugacyWitness
    (left right : Rotation K)
    (leftSpreadZero : halfSpread left = 0)
    (leftNonidentity : left.matrix ≠ Matrix3.identity)
    (rightSpreadZero : halfSpread right = 0)
    (rightNonidentity : right.matrix ≠ Matrix3.identity) :
    presentation.ParabolicConjugacyWitness left right := by
  letI : DecidableEq K := presentation.eqDecidable
  let leftCoordinates := presentation.parabolicDirectionCoordinates left
    leftSpreadZero leftNonidentity
  let rightCoordinates := presentation.parabolicDirectionCoordinates right
    rightSpreadZero rightNonidentity
  let leftAnchor := Vector.scale leftCoordinates.parameter
    leftCoordinates.direction
  let rightAnchor := Vector.scale rightCoordinates.parameter
    rightCoordinates.direction
  have leftParameterNonzero : leftCoordinates.parameter ≠ 0 :=
    (presentation.mem_nonzeroScalars_iff leftCoordinates.parameter).1
      leftCoordinates.parameterMember |>.1
  have rightParameterNonzero : rightCoordinates.parameter ≠ 0 :=
    (presentation.mem_nonzeroScalars_iff rightCoordinates.parameter).1
      rightCoordinates.parameterMember |>.1
  have leftAnchorNonzero : leftAnchor ≠ Vector.zero := by
    intro anchorZero
    apply leftParameterNonzero
    apply presentation.nullDirection_scale_injective
      leftCoordinates.directionMember
    calc
      Vector.scale leftCoordinates.parameter leftCoordinates.direction =
          Vector.zero := anchorZero
      _ = Vector.scale 0 leftCoordinates.direction :=
        (Vector.zero_scale leftCoordinates.direction).symm
  have rightAnchorNonzero : rightAnchor ≠ Vector.zero := by
    intro anchorZero
    apply rightParameterNonzero
    apply presentation.nullDirection_scale_injective
      rightCoordinates.directionMember
    calc
      Vector.scale rightCoordinates.parameter rightCoordinates.direction =
          Vector.zero := anchorZero
      _ = Vector.scale 0 rightCoordinates.direction :=
        (Vector.zero_scale rightCoordinates.direction).symm
  let transport := nullVectorTransport leftAnchor rightAnchor
    leftCoordinates.scaledNull leftAnchorNonzero
    rightCoordinates.scaledNull rightAnchorNonzero presentation.twoNonzero
  have leftDefined : capDenominator leftAnchor ≠ 0 := by
    unfold capDenominator
    rw [leftCoordinates.scaledNull]
    simpa only [add_zero] using presentation.oneNonzero
  have rightDefined : capDenominator rightAnchor ≠ 0 := by
    unfold capDenominator
    rw [rightCoordinates.scaledNull]
    simpa only [add_zero] using presentation.oneNonzero
  have transportedDefined :
      capDenominator
        (Matrix3.rowMul leftAnchor transport.rotation.matrix) ≠ 0 := by
    rw [transport.maps]
    exact rightDefined
  refine
    { conjugator := transport.rotation
      conjugates := ?_ }
  have leftMatrix : left.matrix = cap leftAnchor leftDefined := by
    have rotationEqual := congrArg Rotation.matrix leftCoordinates.rotation_eq
    exact rotationEqual.trans (by rfl)
  have rightMatrix : right.matrix = cap rightAnchor rightDefined := by
    have rotationEqual := congrArg Rotation.matrix rightCoordinates.rotation_eq
    exact rotationEqual.trans (by rfl)
  rw [leftMatrix, rightMatrix]
  calc
    Matrix3.mul
        (Matrix3.mul (Matrix3.transpose transport.rotation.matrix)
          (cap leftAnchor leftDefined)) transport.rotation.matrix =
      cap (Matrix3.rowMul leftAnchor transport.rotation.matrix)
        transportedDefined :=
      cap_conjugate_rotation transport.rotation leftAnchor leftDefined
        transportedDefined
    _ = cap rightAnchor rightDefined :=
      cap_eq_of_vector_eq transport.maps transportedDefined rightDefined

/-- The propositional conjugacy-orbit statement extracted from the executable
classifier. -/
theorem all_nonidentity_parabolics_conjugate
    (presentation : FiniteOddFieldPresentation K)
    (left right : Rotation K)
    (leftSpreadZero : halfSpread left = 0)
    (leftNonidentity : left.matrix ≠ Matrix3.identity)
    (rightSpreadZero : halfSpread right = 0)
    (rightNonidentity : right.matrix ≠ Matrix3.identity) :
    ∃ conjugator : Rotation K,
      Matrix3.mul
          (Matrix3.mul (Matrix3.transpose conjugator.matrix) left.matrix)
          conjugator.matrix = right.matrix := by
  let classification := presentation.parabolicConjugacyWitness left right
    leftSpreadZero leftNonidentity rightSpreadZero rightNonidentity
  exact ⟨classification.conjugator, classification.conjugates⟩

/-- The completed finite classification package: all count and fiber data
from Problem 69 together with the stronger single-conjugacy-class theorem for
its nonidentity parabolic stratum. -/
structure ProblemSixtyNineClassificationSolution where
  counting : presentation.ProblemSixtyNineFiniteSolution
  parabolicConjugacy : ∀ left right : Rotation K,
    halfSpread left = 0 → left.matrix ≠ Matrix3.identity →
    halfSpread right = 0 → right.matrix ≠ Matrix3.identity →
      presentation.ParabolicConjugacyWitness left right

/-- Assemble the complete counting and conjugacy solution of Problem 69. -/
def problemSixtyNineClassificationSolution :
    presentation.ProblemSixtyNineClassificationSolution where
  counting := presentation.problemSixtyNineFiniteSolution
  parabolicConjugacy := fun left right leftSpread leftNonidentity
      rightSpread rightNonidentity =>
    presentation.parabolicConjugacyWitness left right leftSpread
      leftNonidentity rightSpread rightNonidentity

end FiniteOddFieldPresentation

end RationalRotations
