import RationalRotations.MatrixAlgebra

/-!
# Constructive displayed ternary forms

This module begins the finite coordinate-algebra part of Problem 71.  A form
stores its displayed symmetric matrix together with cached determinant,
adjugate, and inverse data.  The certificates connect every cached value to
the canonical fixed-size matrix calculation, so downstream executable code
does not repeat those calculations or recover an inverse by choice.
-/

namespace RationalRotations

variable {K : Type*} [RFAP.ExplicitField K]

/-- A displayed symmetric nondegenerate ternary form, with its determinant,
adjugate, and inverse cached as executable data. -/
structure TernaryForm (K : Type*) [RFAP.ExplicitField K] where
  matrix : Matrix3 K
  symmetric : Matrix3.transpose matrix = matrix
  determinant : K
  determinant_spec : determinant = Matrix3.determinant matrix
  determinantNonzero : determinant ≠ 0
  adjugate : Matrix3 K
  adjugate_spec : adjugate = Matrix3.adjugate matrix
  matrix_mul_adjugate :
    Matrix3.mul matrix adjugate =
      Matrix3.scale determinant Matrix3.identity
  adjugate_mul_matrix :
    Matrix3.mul adjugate matrix =
      Matrix3.scale determinant Matrix3.identity
  inverse : Matrix3 K
  inverse_spec : inverse = Matrix3.inverse matrix (by
    rw [← determinant_spec]
    exact determinantNonzero)
  matrix_mul_inverse : Matrix3.mul matrix inverse = Matrix3.identity
  inverse_mul_matrix : Matrix3.mul inverse matrix = Matrix3.identity

namespace TernaryForm

private theorem scalar_eq_zero_of_nonzero_mul_eq_zero
    {factor value : K} (factorNonzero : factor ≠ 0)
    (productZero : factor * value = 0) : value = 0 := by
  have cancel := RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    value = (factor * factor⁻¹) * value := by rw [cancel, one_mul]
    _ = factor⁻¹ * (factor * value) := by ring1
    _ = 0 := by rw [productZero, mul_zero]

/-- Build the cached form data from one displayed symmetric matrix and its
explicit nonzero-determinant certificate. -/
def ofMatrix (matrix : Matrix3 K)
    (symmetric : Matrix3.transpose matrix = matrix)
    (determinantNonzero : Matrix3.determinant matrix ≠ 0) :
    TernaryForm K where
  matrix := matrix
  symmetric := symmetric
  determinant := Matrix3.determinant matrix
  determinant_spec := rfl
  determinantNonzero := determinantNonzero
  adjugate := Matrix3.adjugate matrix
  adjugate_spec := rfl
  matrix_mul_adjugate := Matrix3.mul_adjugate matrix
  adjugate_mul_matrix := Matrix3.adjugate_mul matrix
  inverse := Matrix3.inverse matrix determinantNonzero
  inverse_spec := rfl
  matrix_mul_inverse := Matrix3.mul_inverse matrix determinantNonzero
  inverse_mul_matrix := Matrix3.inverse_mul matrix determinantNonzero

/-- The cached determinant certifies nondegeneracy of the displayed matrix. -/
theorem matrix_determinant_nonzero (form : TernaryForm K) :
    Matrix3.determinant form.matrix ≠ 0 := by
  rw [← form.determinant_spec]
  exact form.determinantNonzero

/-- A displayed nondegenerate form can exist only over a nontrivial explicit
field. -/
theorem one_ne_zero (form : TernaryForm K) : (1 : K) ≠ 0 := by
  intro oneZero
  apply form.determinantNonzero
  calc
    form.determinant = form.determinant * 1 := by rw [mul_one]
    _ = form.determinant * 0 := by rw [oneZero]
    _ = 0 := by rw [mul_zero]

/-- The cached inverse is tied to the canonical determinant-scaled adjugate
calculation. -/
theorem inverse_eq_scale_adjugate (form : TernaryForm K) :
    form.inverse =
      Matrix3.scale (1 / form.determinant) form.adjugate := by
  calc
    form.inverse = Matrix3.inverse form.matrix
        form.matrix_determinant_nonzero := form.inverse_spec
    _ = Matrix3.scale
        (1 / Matrix3.determinant form.matrix)
        (Matrix3.adjugate form.matrix) := rfl
    _ = Matrix3.scale (1 / form.determinant) form.adjugate := by
      rw [← form.determinant_spec, ← form.adjugate_spec]

/-- The symmetric bilinear form associated with the displayed matrix. -/
def bilinear (form : TernaryForm K) (left right : Vector K) : K :=
  Vector.dot (Matrix3.rowMul left form.matrix) right

/-- Quadrance attached to a displayed ternary form. -/
def quadrance (form : TernaryForm K) (vector : Vector K) : K :=
  form.bilinear vector vector

/-- A vector is null for the displayed form exactly when its quadrance is
zero. -/
def IsNull (form : TernaryForm K) (vector : Vector K) : Prop :=
  form.quadrance vector = 0

/-- Form-relative perpendicularity. -/
def Perpendicular (form : TernaryForm K) (left right : Vector K) : Prop :=
  form.bilinear left right = 0

/-- The corresponding four-coordinate projective norm. -/
def proportionNorm (form : TernaryForm K) (scalar : K)
    (vector : Vector K) : K :=
  scalar ^ 2 + form.quadrance vector

theorem bilinear_comm (form : TernaryForm K) (left right : Vector K) :
    form.bilinear left right = form.bilinear right left := by
  calc
    form.bilinear left right =
        Vector.dot left
          (Matrix3.rowMul right (Matrix3.transpose form.matrix)) :=
      Matrix3.dot_rowMul_transpose left right form.matrix
    _ = Vector.dot left (Matrix3.rowMul right form.matrix) := by
      rw [form.symmetric]
    _ = form.bilinear right left :=
      Vector.dot_comm left (Matrix3.rowMul right form.matrix)

theorem bilinear_add_left (form : TernaryForm K)
    (first second third : Vector K) :
    form.bilinear (Vector.add first second) third =
      form.bilinear first third + form.bilinear second third := by
  unfold bilinear Matrix3.rowMul Vector.dot Vector.add
  ring1

theorem bilinear_add_right (form : TernaryForm K)
    (first second third : Vector K) :
    form.bilinear first (Vector.add second third) =
      form.bilinear first second + form.bilinear first third := by
  unfold bilinear Matrix3.rowMul Vector.dot Vector.add
  ring1

theorem bilinear_sub_left (form : TernaryForm K)
    (first second third : Vector K) :
    form.bilinear (Vector.sub first second) third =
      form.bilinear first third - form.bilinear second third := by
  unfold bilinear Matrix3.rowMul Vector.dot Vector.sub
  ring1

theorem bilinear_sub_right (form : TernaryForm K)
    (first second third : Vector K) :
    form.bilinear first (Vector.sub second third) =
      form.bilinear first second - form.bilinear first third := by
  unfold bilinear Matrix3.rowMul Vector.dot Vector.sub
  ring1

theorem bilinear_scale_left (form : TernaryForm K) (scalar : K)
    (left right : Vector K) :
    form.bilinear (Vector.scale scalar left) right =
      scalar * form.bilinear left right := by
  unfold bilinear Matrix3.rowMul Vector.dot Vector.scale
  ring1

theorem bilinear_scale_right (form : TernaryForm K) (scalar : K)
    (left right : Vector K) :
    form.bilinear left (Vector.scale scalar right) =
      scalar * form.bilinear left right := by
  unfold bilinear Matrix3.rowMul Vector.dot Vector.scale
  ring1

theorem bilinear_neg_left (form : TernaryForm K) (left right : Vector K) :
    form.bilinear (Vector.neg left) right = -form.bilinear left right := by
  unfold bilinear Matrix3.rowMul Vector.dot Vector.neg
  ring1

theorem bilinear_neg_right (form : TernaryForm K) (left right : Vector K) :
    form.bilinear left (Vector.neg right) = -form.bilinear left right := by
  rw [form.bilinear_comm, form.bilinear_neg_left,
    form.bilinear_comm right left]

@[simp] theorem bilinear_zero_left (form : TernaryForm K)
    (vector : Vector K) : form.bilinear Vector.zero vector = 0 := by
  unfold bilinear Matrix3.rowMul Vector.dot Vector.zero
  ring1

@[simp] theorem bilinear_zero_right (form : TernaryForm K)
    (vector : Vector K) : form.bilinear vector Vector.zero = 0 := by
  rw [form.bilinear_comm, form.bilinear_zero_left]

@[simp] theorem quadrance_zero (form : TernaryForm K) :
    form.quadrance Vector.zero = 0 := by
  unfold quadrance
  exact form.bilinear_zero_left Vector.zero

theorem quadrance_scale (form : TernaryForm K) (scalar : K)
    (vector : Vector K) :
    form.quadrance (Vector.scale scalar vector) =
      scalar ^ 2 * form.quadrance vector := by
  unfold quadrance
  rw [form.bilinear_scale_left, form.bilinear_scale_right]
  ring1

theorem quadrance_add (form : TernaryForm K) (left right : Vector K) :
    form.quadrance (Vector.add left right) =
      form.quadrance left + 2 * form.bilinear left right +
        form.quadrance right := by
  unfold quadrance
  rw [form.bilinear_add_left, form.bilinear_add_right,
    form.bilinear_add_right, bilinear_comm form right left]
  ring1

theorem quadrance_sub (form : TernaryForm K) (left right : Vector K) :
    form.quadrance (Vector.sub left right) =
      form.quadrance left - 2 * form.bilinear left right +
        form.quadrance right := by
  unfold quadrance
  rw [form.bilinear_sub_left, form.bilinear_sub_right,
    form.bilinear_sub_right, form.bilinear_comm right left]
  ring1

/-- A cached non-null vector selected from six displayed coordinate
candidates. -/
structure NonNullVectorWitness (form : TernaryForm K) where
  value : Vector K
  nonNull : form.quadrance value ≠ 0

/-- Every displayed nondegenerate ternary form in characteristic different
from two has an executable non-null vector.  The selector tests the three
coordinate rows and their three pairwise sums; if all six quadrances vanished,
symmetry and polarization would force every matrix entry, hence the cached
determinant, to vanish. -/
def nonNullVectorWitness [DecidableEq K] (form : TernaryForm K)
    (twoNonzero : (2 : K) ≠ 0) : NonNullVectorWitness form := by
  let basisT : Vector K := ⟨1, 0, 0⟩
  let basisR : Vector K := ⟨0, 1, 0⟩
  let basisS : Vector K := ⟨0, 0, 1⟩
  let sumTR : Vector K := Vector.add basisT basisR
  let sumTS : Vector K := Vector.add basisT basisS
  let sumRS : Vector K := Vector.add basisR basisS
  by_cases basisTZero : form.quadrance basisT = 0
  · by_cases basisRZero : form.quadrance basisR = 0
    · by_cases basisSZero : form.quadrance basisS = 0
      · by_cases sumTRZero : form.quadrance sumTR = 0
        · by_cases sumTSZero : form.quadrance sumTS = 0
          · by_cases sumRSZero : form.quadrance sumRS = 0
            · have ttZero : form.matrix.tt = 0 := by
                simpa [basisT, quadrance, bilinear, Matrix3.rowMul,
                  Vector.dot] using basisTZero
              have rrZero : form.matrix.rr = 0 := by
                simpa [basisR, quadrance, bilinear, Matrix3.rowMul,
                  Vector.dot] using basisRZero
              have ssZero : form.matrix.ss = 0 := by
                simpa [basisS, quadrance, bilinear, Matrix3.rowMul,
                  Vector.dot] using basisSZero
              have twiceTR :
                  2 * form.bilinear basisT basisR = 0 := by
                have addition := form.quadrance_add basisT basisR
                change form.quadrance sumTR = _ at addition
                rw [sumTRZero, basisTZero, basisRZero] at addition
                calc
                  2 * form.bilinear basisT basisR =
                      0 + 2 * form.bilinear basisT basisR + 0 := by ring1
                  _ = 0 := addition.symm
              have twiceTS :
                  2 * form.bilinear basisT basisS = 0 := by
                have addition := form.quadrance_add basisT basisS
                change form.quadrance sumTS = _ at addition
                rw [sumTSZero, basisTZero, basisSZero] at addition
                calc
                  2 * form.bilinear basisT basisS =
                      0 + 2 * form.bilinear basisT basisS + 0 := by ring1
                  _ = 0 := addition.symm
              have twiceRS :
                  2 * form.bilinear basisR basisS = 0 := by
                have addition := form.quadrance_add basisR basisS
                change form.quadrance sumRS = _ at addition
                rw [sumRSZero, basisRZero, basisSZero] at addition
                calc
                  2 * form.bilinear basisR basisS =
                      0 + 2 * form.bilinear basisR basisS + 0 := by ring1
                  _ = 0 := addition.symm
              have trZero : form.matrix.tr = 0 := by
                apply scalar_eq_zero_of_nonzero_mul_eq_zero twoNonzero
                simpa [basisT, basisR, bilinear, Matrix3.rowMul,
                  Vector.dot] using twiceTR
              have tsZero : form.matrix.ts = 0 := by
                apply scalar_eq_zero_of_nonzero_mul_eq_zero twoNonzero
                simpa [basisT, basisS, bilinear, Matrix3.rowMul,
                  Vector.dot] using twiceTS
              have rsZero : form.matrix.rs = 0 := by
                apply scalar_eq_zero_of_nonzero_mul_eq_zero twoNonzero
                simpa [basisR, basisS, bilinear, Matrix3.rowMul,
                  Vector.dot] using twiceRS
              have rt_tr : form.matrix.rt = form.matrix.tr :=
                congrArg Matrix3.tr form.symmetric
              have st_ts : form.matrix.st = form.matrix.ts :=
                congrArg Matrix3.ts form.symmetric
              have sr_rs : form.matrix.sr = form.matrix.rs :=
                congrArg Matrix3.rs form.symmetric
              have determinantZero : form.determinant = 0 := by
                rw [form.determinant_spec]
                unfold Matrix3.determinant
                rw [ttZero, trZero, tsZero, rt_tr, rrZero, rsZero,
                  st_ts, sr_rs, ssZero]
                ring1
              exact (form.determinantNonzero determinantZero).elim
            · exact ⟨sumRS, sumRSZero⟩
          · exact ⟨sumTS, sumTSZero⟩
        · exact ⟨sumTR, sumTRZero⟩
      · exact ⟨basisS, basisSZero⟩
    · exact ⟨basisR, basisRZero⟩
  · exact ⟨basisT, basisTZero⟩

theorem perpendicular_comm (form : TernaryForm K) (left right : Vector K) :
    form.Perpendicular left right ↔ form.Perpendicular right left := by
  unfold Perpendicular
  rw [form.bilinear_comm]

theorem perpendicular_scale_left (form : TernaryForm K) (scalar : K)
    (left right : Vector K) (perpendicular : form.Perpendicular left right) :
    form.Perpendicular (Vector.scale scalar left) right := by
  unfold Perpendicular at perpendicular ⊢
  rw [form.bilinear_scale_left, perpendicular, mul_zero]

theorem perpendicular_scale_right (form : TernaryForm K) (scalar : K)
    (left right : Vector K) (perpendicular : form.Perpendicular left right) :
    form.Perpendicular left (Vector.scale scalar right) := by
  unfold Perpendicular at perpendicular ⊢
  rw [form.bilinear_scale_right, perpendicular, mul_zero]

theorem isNull_scale (form : TernaryForm K) (scalar : K)
    (vector : Vector K) (null : form.IsNull vector) :
    form.IsNull (Vector.scale scalar vector) := by
  unfold IsNull at null ⊢
  rw [form.quadrance_scale, null, mul_zero]

/-- Simultaneously scaling the scalar and vector coordinates multiplies the
projective norm by the square of the displayed scale. -/
theorem proportionNorm_scale (form : TernaryForm K) (factor scalar : K)
    (vector : Vector K) :
    form.proportionNorm (factor * scalar) (Vector.scale factor vector) =
      factor ^ 2 * form.proportionNorm scalar vector := by
  unfold proportionNorm
  rw [form.quadrance_scale]
  ring1

/-- The cached inverse makes matrix nondegeneracy executable: a vector killed
by the form matrix is the zero vector. -/
theorem eq_zero_of_rowMul_matrix_eq_zero (form : TernaryForm K)
    (vector : Vector K)
    (annihilated : Matrix3.rowMul vector form.matrix = Vector.zero) :
    vector = Vector.zero := by
  calc
    vector = Matrix3.rowMul vector Matrix3.identity := by
      rw [Matrix3.rowMul_identity]
    _ = Matrix3.rowMul vector
        (Matrix3.mul form.matrix form.inverse) := by
      rw [form.matrix_mul_inverse]
    _ = Matrix3.rowMul
        (Matrix3.rowMul vector form.matrix) form.inverse := by
      rw [Matrix3.rowMul_mul]
    _ = Matrix3.rowMul Vector.zero form.inverse := by rw [annihilated]
    _ = Vector.zero := by
      ext <;> unfold Matrix3.rowMul Vector.zero <;> ring1

/-- Right multiplication by the displayed form matrix is injective, with the
cached inverse providing the explicit cancellation path. -/
theorem rowMul_matrix_injective (form : TernaryForm K)
    {left right : Vector K}
    (equal : Matrix3.rowMul left form.matrix =
      Matrix3.rowMul right form.matrix) :
    left = right := by
  calc
    left = Matrix3.rowMul
        (Matrix3.rowMul left form.matrix) form.inverse := by
      rw [Matrix3.rowMul_mul, form.matrix_mul_inverse,
        Matrix3.rowMul_identity]
    _ = Matrix3.rowMul
        (Matrix3.rowMul right form.matrix) form.inverse := by rw [equal]
    _ = right := by
      rw [Matrix3.rowMul_mul, form.matrix_mul_inverse,
        Matrix3.rowMul_identity]

/-- Nondegeneracy in bilinear form: equality against the three displayed
coordinate tests determines the source vector. -/
theorem eq_of_bilinear_eq (form : TernaryForm K) {left right : Vector K}
    (equal : ∀ test : Vector K,
      form.bilinear left test = form.bilinear right test) :
    left = right := by
  apply form.rowMul_matrix_injective
  apply Vector.ext
  · simpa [bilinear, Vector.dot] using
      equal (⟨1, 0, 0⟩ : Vector K)
  · simpa [bilinear, Vector.dot] using
      equal (⟨0, 1, 0⟩ : Vector K)
  · simpa [bilinear, Vector.dot] using
      equal (⟨0, 0, 1⟩ : Vector K)

/-- Denominator-free projection of a displayed test vector to the
perpendicular plane of a non-null axis. -/
def perpendicularProjection (form : TernaryForm K) (axis test : Vector K) :
    Vector K :=
  Vector.sub
    (Vector.scale (form.quadrance axis) test)
    (Vector.scale (form.bilinear test axis) axis)

theorem perpendicularProjection_perpendicular (form : TernaryForm K)
    (axis test : Vector K) :
    form.Perpendicular (form.perpendicularProjection axis test) axis := by
  unfold Perpendicular perpendicularProjection
  rw [form.bilinear_sub_left, form.bilinear_scale_left,
    form.bilinear_scale_left]
  change form.quadrance axis * form.bilinear test axis -
    form.bilinear test axis * form.quadrance axis = 0
  ring1

theorem perpendicularProjection_add (form : TernaryForm K)
    (axis first second : Vector K) :
    form.perpendicularProjection axis (Vector.add first second) =
      Vector.add (form.perpendicularProjection axis first)
        (form.perpendicularProjection axis second) := by
  unfold perpendicularProjection
  rw [form.bilinear_add_left]
  ext <;> unfold Vector.add Vector.sub Vector.scale <;> ring1

/-- The cleared projection reconstructs the quadrance-scaled test vector
after its displayed axis component is restored. -/
theorem perpendicularProjection_reconstruct (form : TernaryForm K)
    (axis test : Vector K) :
    Vector.add (form.perpendicularProjection axis test)
        (Vector.scale (form.bilinear test axis) axis) =
      Vector.scale (form.quadrance axis) test := by
  ext <;> unfold perpendicularProjection Vector.add Vector.sub Vector.scale <;>
    ring1

/-- Coordinate expansion of the cleared projection. -/
theorem perpendicularProjection_coordinateExpansion
    (form : TernaryForm K) (axis test : Vector K) :
    form.perpendicularProjection axis test =
      Vector.add
        (Vector.add
          (Vector.scale test.t
            (form.perpendicularProjection axis (⟨1, 0, 0⟩ : Vector K)))
          (Vector.scale test.r
            (form.perpendicularProjection axis (⟨0, 1, 0⟩ : Vector K))))
        (Vector.scale test.s
          (form.perpendicularProjection axis (⟨0, 0, 1⟩ : Vector K))) := by
  ext <;> unfold perpendicularProjection quadrance bilinear Matrix3.rowMul
    Vector.dot Vector.add Vector.sub Vector.scale <;> ring1

/-- A cached non-null vector in the perpendicular plane of a supplied
non-null axis. -/
structure PerpendicularNonNullVectorWitness (form : TernaryForm K)
    (axis : Vector K) where
  value : Vector K
  perpendicular : form.Perpendicular value axis
  nonNull : form.quadrance value ≠ 0

/-- Select a non-null perpendicular vector by testing the cleared projections
of the three coordinate rows and their three pairwise sums.  The proof that
the six candidates cannot all be null uses only polarization, the explicit
coordinate expansion, and nondegeneracy. -/
def perpendicularNonNullVectorWitness [DecidableEq K]
    (form : TernaryForm K) (axis : Vector K)
    (axisNonNull : form.quadrance axis ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    PerpendicularNonNullVectorWitness form axis := by
  let basisT : Vector K := ⟨1, 0, 0⟩
  let basisR : Vector K := ⟨0, 1, 0⟩
  let basisS : Vector K := ⟨0, 0, 1⟩
  let projectedT := form.perpendicularProjection axis basisT
  let projectedR := form.perpendicularProjection axis basisR
  let projectedS := form.perpendicularProjection axis basisS
  let sumTR := Vector.add projectedT projectedR
  let sumTS := Vector.add projectedT projectedS
  let sumRS := Vector.add projectedR projectedS
  have projectedTPerpendicular : form.Perpendicular projectedT axis :=
    form.perpendicularProjection_perpendicular axis basisT
  have projectedRPerpendicular : form.Perpendicular projectedR axis :=
    form.perpendicularProjection_perpendicular axis basisR
  have projectedSPerpendicular : form.Perpendicular projectedS axis :=
    form.perpendicularProjection_perpendicular axis basisS
  have sumTRPerpendicular : form.Perpendicular sumTR axis := by
    unfold sumTR Perpendicular
    rw [form.bilinear_add_left, projectedTPerpendicular,
      projectedRPerpendicular, add_zero]
  have sumTSPerpendicular : form.Perpendicular sumTS axis := by
    unfold sumTS Perpendicular
    rw [form.bilinear_add_left, projectedTPerpendicular,
      projectedSPerpendicular, add_zero]
  have sumRSPerpendicular : form.Perpendicular sumRS axis := by
    unfold sumRS Perpendicular
    rw [form.bilinear_add_left, projectedRPerpendicular,
      projectedSPerpendicular, add_zero]
  by_cases projectedTZero : form.quadrance projectedT = 0
  · by_cases projectedRZero : form.quadrance projectedR = 0
    · by_cases projectedSZero : form.quadrance projectedS = 0
      · by_cases sumTRZero : form.quadrance sumTR = 0
        · by_cases sumTSZero : form.quadrance sumTS = 0
          · by_cases sumRSZero : form.quadrance sumRS = 0
            · have pairingTR : form.bilinear projectedT projectedR = 0 := by
                apply scalar_eq_zero_of_nonzero_mul_eq_zero twoNonzero
                have addition := form.quadrance_add projectedT projectedR
                change form.quadrance sumTR = _ at addition
                rw [sumTRZero, projectedTZero, projectedRZero] at addition
                calc
                  2 * form.bilinear projectedT projectedR =
                      0 + 2 * form.bilinear projectedT projectedR + 0 := by
                    ring1
                  _ = 0 := addition.symm
              have pairingTS : form.bilinear projectedT projectedS = 0 := by
                apply scalar_eq_zero_of_nonzero_mul_eq_zero twoNonzero
                have addition := form.quadrance_add projectedT projectedS
                change form.quadrance sumTS = _ at addition
                rw [sumTSZero, projectedTZero, projectedSZero] at addition
                calc
                  2 * form.bilinear projectedT projectedS =
                      0 + 2 * form.bilinear projectedT projectedS + 0 := by
                    ring1
                  _ = 0 := addition.symm
              have pairingRS : form.bilinear projectedR projectedS = 0 := by
                apply scalar_eq_zero_of_nonzero_mul_eq_zero twoNonzero
                have addition := form.quadrance_add projectedR projectedS
                change form.quadrance sumRS = _ at addition
                rw [sumRSZero, projectedRZero, projectedSZero] at addition
                calc
                  2 * form.bilinear projectedR projectedS =
                      0 + 2 * form.bilinear projectedR projectedS + 0 := by
                    ring1
                  _ = 0 := addition.symm
              have projectionZero
                  (projected : Vector K)
                  (perpendicular : form.Perpendicular projected axis)
                  (pairT : form.bilinear projected projectedT = 0)
                  (pairR : form.bilinear projected projectedR = 0)
                  (pairS : form.bilinear projected projectedS = 0) :
                  projected = Vector.zero := by
                apply form.eq_of_bilinear_eq
                intro test
                rw [form.bilinear_zero_left]
                apply scalar_eq_zero_of_nonzero_mul_eq_zero axisNonNull
                have projectedExpansion :
                    form.bilinear projected
                      (form.perpendicularProjection axis test) = 0 := by
                  rw [form.perpendicularProjection_coordinateExpansion,
                    form.bilinear_add_right, form.bilinear_add_right,
                    form.bilinear_scale_right, form.bilinear_scale_right,
                    form.bilinear_scale_right, pairT, pairR, pairS]
                  ring1
                unfold Perpendicular at perpendicular
                calc
                  form.quadrance axis * form.bilinear projected test =
                      form.bilinear projected
                        (Vector.scale (form.quadrance axis) test) :=
                    (form.bilinear_scale_right
                      (form.quadrance axis) projected test).symm
                  _ = form.bilinear projected
                      (Vector.add (form.perpendicularProjection axis test)
                        (Vector.scale (form.bilinear test axis) axis)) := by
                    rw [form.perpendicularProjection_reconstruct]
                  _ = form.bilinear projected
                        (form.perpendicularProjection axis test) +
                      form.bilinear projected
                        (Vector.scale (form.bilinear test axis) axis) :=
                    form.bilinear_add_right projected _ _
                  _ = 0 := by
                    rw [projectedExpansion, form.bilinear_scale_right,
                      perpendicular, mul_zero, add_zero]
              have projectedTIsZero : projectedT = Vector.zero := by
                apply projectionZero projectedT projectedTPerpendicular
                · exact projectedTZero
                · exact pairingTR
                · exact pairingTS
              have projectedRIsZero : projectedR = Vector.zero := by
                apply projectionZero projectedR projectedRPerpendicular
                · rw [form.bilinear_comm]
                  exact pairingTR
                · exact projectedRZero
                · exact pairingRS
              have projectedSIsZero : projectedS = Vector.zero := by
                apply projectionZero projectedS projectedSPerpendicular
                · rw [form.bilinear_comm]
                  exact pairingTS
                · rw [form.bilinear_comm]
                  exact pairingRS
                · exact projectedSZero
              have scaledT :
                  Vector.scale (form.quadrance axis) basisT =
                    Vector.scale (form.bilinear basisT axis) axis := by
                calc
                  Vector.scale (form.quadrance axis) basisT =
                      Vector.add projectedT
                        (Vector.scale (form.bilinear basisT axis) axis) :=
                    (form.perpendicularProjection_reconstruct
                      axis basisT).symm
                  _ = Vector.scale (form.bilinear basisT axis) axis := by
                    rw [projectedTIsZero, Vector.zero_add]
              have scaledR :
                  Vector.scale (form.quadrance axis) basisR =
                    Vector.scale (form.bilinear basisR axis) axis := by
                calc
                  Vector.scale (form.quadrance axis) basisR =
                      Vector.add projectedR
                        (Vector.scale (form.bilinear basisR axis) axis) :=
                    (form.perpendicularProjection_reconstruct
                      axis basisR).symm
                  _ = Vector.scale (form.bilinear basisR axis) axis := by
                    rw [projectedRIsZero, Vector.zero_add]
              have crossed := congrArg₂ Vector.cross scaledT scaledR
              have leftCross :
                  Vector.cross
                      (Vector.scale (form.quadrance axis) basisT)
                      (Vector.scale (form.quadrance axis) basisR) =
                    Vector.scale (form.quadrance axis * form.quadrance axis)
                      basisS := by
                ext <;> unfold basisT basisR basisS Vector.cross Vector.scale <;>
                  ring1
              have rightCross :
                  Vector.cross
                      (Vector.scale (form.bilinear basisT axis) axis)
                      (Vector.scale (form.bilinear basisR axis) axis) =
                    Vector.zero := by
                ext <;> unfold Vector.cross Vector.scale Vector.zero <;> ring1
              have scaledBasisSZero :
                  Vector.scale (form.quadrance axis * form.quadrance axis)
                    basisS = Vector.zero := by
                calc
                  Vector.scale (form.quadrance axis * form.quadrance axis)
                      basisS =
                    Vector.cross
                      (Vector.scale (form.quadrance axis) basisT)
                      (Vector.scale (form.quadrance axis) basisR) :=
                    leftCross.symm
                  _ = Vector.cross
                      (Vector.scale (form.bilinear basisT axis) axis)
                      (Vector.scale (form.bilinear basisR axis) axis) := crossed
                  _ = Vector.zero := rightCross
              have quadranceSquareZero :
                  form.quadrance axis * form.quadrance axis = 0 := by
                have coordinate := congrArg Vector.s scaledBasisSZero
                simpa [basisS, Vector.scale] using coordinate
              have quadranceSquareNonzero := RFAP.ExplicitField.mul_ne_zero
                axisNonNull axisNonNull
              exact (quadranceSquareNonzero quadranceSquareZero).elim
            · exact ⟨sumRS, sumRSPerpendicular, sumRSZero⟩
          · exact ⟨sumTS, sumTSPerpendicular, sumTSZero⟩
        · exact ⟨sumTR, sumTRPerpendicular, sumTRZero⟩
      · exact ⟨projectedS, projectedSPerpendicular, projectedSZero⟩
    · exact ⟨projectedR, projectedRPerpendicular, projectedRZero⟩
  · exact ⟨projectedT, projectedTPerpendicular, projectedTZero⟩

/-- A displayed linear action preserving the bilinear form on every pair has
the corresponding finite matrix preservation certificate. -/
theorem preservesMatrix_of_bilinear_rowMul (form : TernaryForm K)
    (matrix : Matrix3 K)
    (preserves : ∀ left right : Vector K,
      form.bilinear (Matrix3.rowMul left matrix)
          (Matrix3.rowMul right matrix) = form.bilinear left right) :
    Matrix3.mul (Matrix3.mul matrix form.matrix)
      (Matrix3.transpose matrix) = form.matrix := by
  apply Matrix3.ext
  · simpa [bilinear, Matrix3.rowMul, Matrix3.mul, Matrix3.transpose,
      Vector.dot] using
      preserves (⟨1, 0, 0⟩ : Vector K) (⟨1, 0, 0⟩ : Vector K)
  · simpa [bilinear, Matrix3.rowMul, Matrix3.mul, Matrix3.transpose,
      Vector.dot] using
      preserves (⟨1, 0, 0⟩ : Vector K) (⟨0, 1, 0⟩ : Vector K)
  · simpa [bilinear, Matrix3.rowMul, Matrix3.mul, Matrix3.transpose,
      Vector.dot] using
      preserves (⟨1, 0, 0⟩ : Vector K) (⟨0, 0, 1⟩ : Vector K)
  · simpa [bilinear, Matrix3.rowMul, Matrix3.mul, Matrix3.transpose,
      Vector.dot] using
      preserves (⟨0, 1, 0⟩ : Vector K) (⟨1, 0, 0⟩ : Vector K)
  · simpa [bilinear, Matrix3.rowMul, Matrix3.mul, Matrix3.transpose,
      Vector.dot] using
      preserves (⟨0, 1, 0⟩ : Vector K) (⟨0, 1, 0⟩ : Vector K)
  · simpa [bilinear, Matrix3.rowMul, Matrix3.mul, Matrix3.transpose,
      Vector.dot] using
      preserves (⟨0, 1, 0⟩ : Vector K) (⟨0, 0, 1⟩ : Vector K)
  · simpa [bilinear, Matrix3.rowMul, Matrix3.mul, Matrix3.transpose,
      Vector.dot] using
      preserves (⟨0, 0, 1⟩ : Vector K) (⟨1, 0, 0⟩ : Vector K)
  · simpa [bilinear, Matrix3.rowMul, Matrix3.mul, Matrix3.transpose,
      Vector.dot] using
      preserves (⟨0, 0, 1⟩ : Vector K) (⟨0, 1, 0⟩ : Vector K)
  · simpa [bilinear, Matrix3.rowMul, Matrix3.mul, Matrix3.transpose,
      Vector.dot] using
      preserves (⟨0, 0, 1⟩ : Vector K) (⟨0, 0, 1⟩ : Vector K)

/-! ## Form-relative isometries and special orthogonal matrices -/

/-- An executable isometry of a displayed ternary form.  Its inverse is
cached together with both multiplication certificates. -/
structure Isometry (form : TernaryForm K) where
  matrix : Matrix3 K
  inverseMatrix : Matrix3 K
  matrix_mul_inverse : Matrix3.mul matrix inverseMatrix = Matrix3.identity
  inverse_mul_matrix : Matrix3.mul inverseMatrix matrix = Matrix3.identity
  preservesMatrix :
    Matrix3.mul (Matrix3.mul matrix form.matrix)
      (Matrix3.transpose matrix) = form.matrix

namespace Isometry

/-- Right action of a form isometry on a displayed row vector. -/
def act {form : TernaryForm K} (isometry : form.Isometry)
    (vector : Vector K) : Vector K :=
  Matrix3.rowMul vector isometry.matrix

/-- Cached inverse data are unique, so displayed isometries are equal when
their forward matrices are equal. -/
theorem eq_of_matrix_eq {form : TernaryForm K}
    (left right : form.Isometry) (matrixEq : left.matrix = right.matrix) :
    left = right := by
  have inverseEq : left.inverseMatrix = right.inverseMatrix := by
    calc
      left.inverseMatrix =
          Matrix3.mul left.inverseMatrix Matrix3.identity :=
        (Matrix3.mul_identity left.inverseMatrix).symm
      _ = Matrix3.mul left.inverseMatrix
          (Matrix3.mul right.matrix right.inverseMatrix) := by
        rw [right.matrix_mul_inverse]
      _ = Matrix3.mul
          (Matrix3.mul left.inverseMatrix right.matrix)
          right.inverseMatrix := by
        rw [Matrix3.mul_assoc]
      _ = Matrix3.mul
          (Matrix3.mul left.inverseMatrix left.matrix)
          right.inverseMatrix := by
        rw [matrixEq]
      _ = Matrix3.mul Matrix3.identity right.inverseMatrix := by
        rw [left.inverse_mul_matrix]
      _ = right.inverseMatrix := Matrix3.identity_mul right.inverseMatrix
  cases left with
  | mk leftMatrix leftInverse leftRight rightLeft leftPreserves =>
      cases right with
      | mk rightMatrix rightInverse rightRight rightLeft' rightPreserves =>
          cases matrixEq
          cases inverseEq
          rfl

theorem bilinear_act {form : TernaryForm K} (isometry : form.Isometry)
    (left right : Vector K) :
    form.bilinear (isometry.act left) (isometry.act right) =
      form.bilinear left right := by
  calc
    form.bilinear (isometry.act left) (isometry.act right) =
        Vector.dot
          (Matrix3.rowMul
            (Matrix3.rowMul left isometry.matrix) form.matrix)
          (Matrix3.rowMul right isometry.matrix) := rfl
    _ = Vector.dot (Matrix3.rowMul right isometry.matrix)
        (Matrix3.rowMul
          (Matrix3.rowMul left isometry.matrix) form.matrix) :=
      Vector.dot_comm _ _
    _ = Vector.dot right
        (Matrix3.rowMul
          (Matrix3.rowMul
            (Matrix3.rowMul left isometry.matrix) form.matrix)
          (Matrix3.transpose isometry.matrix)) :=
      Matrix3.dot_rowMul_transpose right
        (Matrix3.rowMul
          (Matrix3.rowMul left isometry.matrix) form.matrix)
        isometry.matrix
    _ = Vector.dot right
        (Matrix3.rowMul left
          (Matrix3.mul
            (Matrix3.mul isometry.matrix form.matrix)
            (Matrix3.transpose isometry.matrix))) := by
      rw [Matrix3.rowMul_mul, Matrix3.rowMul_mul]
      rw [Matrix3.mul_assoc]
    _ = Vector.dot right (Matrix3.rowMul left form.matrix) := by
      rw [isometry.preservesMatrix]
    _ = form.bilinear left right := Vector.dot_comm _ _

theorem quadrance_act {form : TernaryForm K} (isometry : form.Isometry)
    (vector : Vector K) :
    form.quadrance (isometry.act vector) = form.quadrance vector := by
  unfold quadrance
  exact isometry.bilinear_act vector vector

theorem isNull_act {form : TernaryForm K} (isometry : form.Isometry)
    {vector : Vector K} (null : form.IsNull vector) :
    form.IsNull (isometry.act vector) := by
  unfold TernaryForm.IsNull at null ⊢
  rw [isometry.quadrance_act, null]

theorem perpendicular_act {form : TernaryForm K} (isometry : form.Isometry)
    {left right : Vector K} (perpendicular : form.Perpendicular left right) :
    form.Perpendicular (isometry.act left) (isometry.act right) := by
  unfold TernaryForm.Perpendicular at perpendicular ⊢
  rw [isometry.bilinear_act, perpendicular]

/-- The identity isometry, with no inferred inverse data. -/
def identity (form : TernaryForm K) : form.Isometry where
  matrix := Matrix3.identity
  inverseMatrix := Matrix3.identity
  matrix_mul_inverse := Matrix3.identity_mul Matrix3.identity
  inverse_mul_matrix := Matrix3.identity_mul Matrix3.identity
  preservesMatrix := by
    rw [Matrix3.identity_mul, Matrix3.transpose_identity,
      Matrix3.mul_identity]

/-- Product of two form isometries in the row-action order. -/
def mul {form : TernaryForm K} (left right : form.Isometry) :
    form.Isometry where
  matrix := Matrix3.mul left.matrix right.matrix
  inverseMatrix := Matrix3.mul right.inverseMatrix left.inverseMatrix
  matrix_mul_inverse := by
    calc
      Matrix3.mul (Matrix3.mul left.matrix right.matrix)
          (Matrix3.mul right.inverseMatrix left.inverseMatrix) =
        Matrix3.mul left.matrix
          (Matrix3.mul
            (Matrix3.mul right.matrix right.inverseMatrix)
            left.inverseMatrix) := by
          rw [Matrix3.mul_assoc, Matrix3.mul_assoc]
      _ = Matrix3.mul left.matrix
          (Matrix3.mul Matrix3.identity left.inverseMatrix) := by
        rw [right.matrix_mul_inverse]
      _ = Matrix3.identity := by
        rw [Matrix3.identity_mul, left.matrix_mul_inverse]
  inverse_mul_matrix := by
    calc
      Matrix3.mul (Matrix3.mul right.inverseMatrix left.inverseMatrix)
          (Matrix3.mul left.matrix right.matrix) =
        Matrix3.mul right.inverseMatrix
          (Matrix3.mul
            (Matrix3.mul left.inverseMatrix left.matrix) right.matrix) := by
          rw [Matrix3.mul_assoc, Matrix3.mul_assoc]
      _ = Matrix3.mul right.inverseMatrix
          (Matrix3.mul Matrix3.identity right.matrix) := by
        rw [left.inverse_mul_matrix]
      _ = Matrix3.identity := by
        rw [Matrix3.identity_mul, right.inverse_mul_matrix]
  preservesMatrix := by
    rw [Matrix3.transpose_mul]
    calc
      Matrix3.mul
          (Matrix3.mul (Matrix3.mul left.matrix right.matrix) form.matrix)
          (Matrix3.mul (Matrix3.transpose right.matrix)
            (Matrix3.transpose left.matrix)) =
        Matrix3.mul left.matrix
          (Matrix3.mul
            (Matrix3.mul
              (Matrix3.mul right.matrix form.matrix)
              (Matrix3.transpose right.matrix))
            (Matrix3.transpose left.matrix)) := by
          rw [Matrix3.mul_assoc, Matrix3.mul_assoc, Matrix3.mul_assoc,
            Matrix3.mul_assoc]
      _ = Matrix3.mul left.matrix
          (Matrix3.mul form.matrix (Matrix3.transpose left.matrix)) := by
        rw [right.preservesMatrix]
      _ = Matrix3.mul
          (Matrix3.mul left.matrix form.matrix)
          (Matrix3.transpose left.matrix) := by
        rw [Matrix3.mul_assoc]
      _ = form.matrix := left.preservesMatrix

/-- Inverse form isometry, using the inverse already cached in the input. -/
def inverse {form : TernaryForm K} (isometry : form.Isometry) :
    form.Isometry where
  matrix := isometry.inverseMatrix
  inverseMatrix := isometry.matrix
  matrix_mul_inverse := isometry.inverse_mul_matrix
  inverse_mul_matrix := isometry.matrix_mul_inverse
  preservesMatrix := by
    calc
      Matrix3.mul (Matrix3.mul isometry.inverseMatrix form.matrix)
          (Matrix3.transpose isometry.inverseMatrix) =
        Matrix3.mul
          (Matrix3.mul isometry.inverseMatrix
            (Matrix3.mul
              (Matrix3.mul isometry.matrix form.matrix)
              (Matrix3.transpose isometry.matrix)))
          (Matrix3.transpose isometry.inverseMatrix) := by
            rw [isometry.preservesMatrix]
      _ = Matrix3.mul
          (Matrix3.mul
            (Matrix3.mul isometry.inverseMatrix isometry.matrix) form.matrix)
          (Matrix3.mul (Matrix3.transpose isometry.matrix)
            (Matrix3.transpose isometry.inverseMatrix)) := by
        ext <;> unfold Matrix3.mul <;> ring1
      _ = Matrix3.mul
          (Matrix3.mul Matrix3.identity form.matrix)
          (Matrix3.transpose
            (Matrix3.mul isometry.inverseMatrix isometry.matrix)) := by
        rw [Matrix3.transpose_mul, isometry.inverse_mul_matrix]
      _ = form.matrix := by
        rw [isometry.inverse_mul_matrix, Matrix3.transpose_identity,
          Matrix3.identity_mul, Matrix3.mul_identity]

theorem act_identity (form : TernaryForm K) (vector : Vector K) :
    (identity form).act vector = vector := by
  unfold act identity
  rw [Matrix3.rowMul_identity]

theorem act_mul {form : TernaryForm K} (left right : form.Isometry)
    (vector : Vector K) :
    (mul left right).act vector = right.act (left.act vector) := by
  unfold act mul
  rw [Matrix3.rowMul_mul]

theorem act_inverse_left {form : TernaryForm K} (isometry : form.Isometry)
    (vector : Vector K) :
    (inverse isometry).act (isometry.act vector) = vector := by
  unfold act inverse
  rw [Matrix3.rowMul_mul, isometry.matrix_mul_inverse,
    Matrix3.rowMul_identity]

theorem act_inverse_right {form : TernaryForm K} (isometry : form.Isometry)
    (vector : Vector K) :
    isometry.act ((inverse isometry).act vector) = vector := by
  unfold act inverse
  rw [Matrix3.rowMul_mul, isometry.inverse_mul_matrix,
    Matrix3.rowMul_identity]

end Isometry

/-- A special orthogonal transformation of a displayed ternary form. -/
structure SpecialOrthogonal (form : TernaryForm K) extends form.Isometry where
  determinantOne : Matrix3.determinant matrix = 1

namespace SpecialOrthogonal

/-- A displayed special-orthogonal transformation is determined by its
forward matrix. -/
theorem eq_of_matrix_eq {form : TernaryForm K}
    (left right : form.SpecialOrthogonal)
    (matrixEq : left.matrix = right.matrix) : left = right := by
  have isometryEq := Isometry.eq_of_matrix_eq
    left.toIsometry right.toIsometry matrixEq
  cases left with
  | mk leftIsometry leftDeterminant =>
      cases right with
      | mk rightIsometry rightDeterminant =>
          cases isometryEq
          rfl

/-- The identity special orthogonal transformation. -/
def identity (form : TernaryForm K) : form.SpecialOrthogonal where
  toIsometry := Isometry.identity form
  determinantOne := Matrix3.determinant_identity

/-- Product of special orthogonal transformations. -/
def mul {form : TernaryForm K} (left right : form.SpecialOrthogonal) :
    form.SpecialOrthogonal where
  toIsometry := Isometry.mul left.toIsometry right.toIsometry
  determinantOne := by
    change Matrix3.determinant
      (Matrix3.mul left.matrix right.matrix) = 1
    rw [Matrix3.determinant_mul, left.determinantOne,
      right.determinantOne, one_mul]

/-- Inverse special orthogonal transformation. -/
def inverse {form : TernaryForm K} (rotation : form.SpecialOrthogonal) :
    form.SpecialOrthogonal where
  toIsometry := Isometry.inverse rotation.toIsometry
  determinantOne := by
    have determinantProduct := congrArg Matrix3.determinant
      rotation.inverse_mul_matrix
    change Matrix3.determinant rotation.inverseMatrix = 1
    rw [Matrix3.determinant_mul, rotation.determinantOne,
      Matrix3.determinant_identity, mul_one] at determinantProduct
    exact determinantProduct

@[simp] theorem identity_mul {form : TernaryForm K}
    (rotation : form.SpecialOrthogonal) :
    mul (identity form) rotation = rotation := by
  apply eq_of_matrix_eq
  exact Matrix3.identity_mul rotation.matrix

@[simp] theorem mul_identity {form : TernaryForm K}
    (rotation : form.SpecialOrthogonal) :
    mul rotation (identity form) = rotation := by
  apply eq_of_matrix_eq
  exact Matrix3.mul_identity rotation.matrix

theorem mul_assoc {form : TernaryForm K}
    (first second third : form.SpecialOrthogonal) :
    mul (mul first second) third = mul first (mul second third) := by
  apply eq_of_matrix_eq
  exact Matrix3.mul_assoc first.matrix second.matrix third.matrix

@[simp] theorem mul_inverse {form : TernaryForm K}
    (rotation : form.SpecialOrthogonal) :
    mul rotation (inverse rotation) = identity form := by
  apply eq_of_matrix_eq
  exact rotation.matrix_mul_inverse

@[simp] theorem inverse_mul {form : TernaryForm K}
    (rotation : form.SpecialOrthogonal) :
    mul (inverse rotation) rotation = identity form := by
  apply eq_of_matrix_eq
  exact rotation.inverse_mul_matrix

@[simp] theorem inverse_inverse {form : TernaryForm K}
    (rotation : form.SpecialOrthogonal) :
    inverse (inverse rotation) = rotation := by
  apply eq_of_matrix_eq
  rfl

theorem inverse_mul_reverse {form : TernaryForm K}
    (left right : form.SpecialOrthogonal) :
    inverse (mul left right) = mul (inverse right) (inverse left) := by
  apply eq_of_matrix_eq
  rfl

theorem quadrance_act {form : TernaryForm K}
    (rotation : form.SpecialOrthogonal) (vector : Vector K) :
    form.quadrance (rotation.act vector) = form.quadrance vector :=
  rotation.toIsometry.quadrance_act vector

end SpecialOrthogonal

/-! ## Form-relative reflections and half turns -/

/-- The form-dual row vector of a displayed vector. -/
def dual (form : TernaryForm K) (vector : Vector K) : Vector K :=
  Matrix3.rowMul vector form.matrix

theorem bilinear_eq_dot_dual (form : TernaryForm K)
    (left right : Vector K) :
    form.bilinear left right = Vector.dot left (form.dual right) := by
  calc
    form.bilinear left right =
        Vector.dot left
          (Matrix3.rowMul right (Matrix3.transpose form.matrix)) :=
      Matrix3.dot_rowMul_transpose left right form.matrix
    _ = Vector.dot left (form.dual right) := by
      unfold dual
      rw [form.symmetric]

theorem dual_scale (form : TernaryForm K) (scalar : K)
    (vector : Vector K) :
    form.dual (Vector.scale scalar vector) =
      Vector.scale scalar (form.dual vector) := by
  ext <;> unfold dual Matrix3.rowMul Vector.scale <;> ring1

/-- Form-relative cross product determined by the displayed volume
coordinates and the cached inverse form matrix.  It is characterized by
`B(u ×_M v, w) = det(u,v,w)`. -/
def cross (form : TernaryForm K) (left right : Vector K) : Vector K :=
  Matrix3.rowMul (Vector.cross left right) form.inverse

/-- Applying the form matrix to the relative cross product recovers the
ordinary displayed determinant covector. -/
theorem rowMul_cross_matrix (form : TernaryForm K)
    (left right : Vector K) :
    Matrix3.rowMul (form.cross left right) form.matrix =
      Vector.cross left right := by
  unfold cross
  rw [Matrix3.rowMul_mul, form.inverse_mul_matrix,
    Matrix3.rowMul_identity]

/-- Generalized scalar triple-product identity. -/
theorem bilinear_cross (form : TernaryForm K)
    (first second third : Vector K) :
    form.bilinear (form.cross first second) third =
      Vector.determinant first second third := by
  unfold bilinear
  rw [form.rowMul_cross_matrix]
  exact Vector.scalar_triple_product first second third

@[simp] theorem cross_zero_left (form : TernaryForm K)
    (vector : Vector K) : form.cross Vector.zero vector = Vector.zero := by
  ext <;> unfold cross Vector.cross Vector.zero Matrix3.rowMul <;> ring1

@[simp] theorem cross_zero_right (form : TernaryForm K)
    (vector : Vector K) : form.cross vector Vector.zero = Vector.zero := by
  ext <;> unfold cross Vector.cross Vector.zero Matrix3.rowMul <;> ring1

theorem cross_anticomm (form : TernaryForm K) (left right : Vector K) :
    form.cross left right = Vector.neg (form.cross right left) := by
  ext <;> unfold cross Vector.cross Vector.neg Matrix3.rowMul <;> ring1

theorem cross_add_left (form : TernaryForm K)
    (first second third : Vector K) :
    form.cross (Vector.add first second) third =
      Vector.add (form.cross first third) (form.cross second third) := by
  ext <;> unfold cross Vector.cross Vector.add Matrix3.rowMul <;> ring1

theorem cross_add_right (form : TernaryForm K)
    (first second third : Vector K) :
    form.cross first (Vector.add second third) =
      Vector.add (form.cross first second) (form.cross first third) := by
  ext <;> unfold cross Vector.cross Vector.add Matrix3.rowMul <;> ring1

theorem cross_scale_left (form : TernaryForm K) (scalar : K)
    (left right : Vector K) :
    form.cross (Vector.scale scalar left) right =
      Vector.scale scalar (form.cross left right) := by
  ext <;> unfold cross Vector.cross Vector.scale Matrix3.rowMul <;> ring1

theorem cross_scale_right (form : TernaryForm K) (scalar : K)
    (left right : Vector K) :
    form.cross left (Vector.scale scalar right) =
      Vector.scale scalar (form.cross left right) := by
  ext <;> unfold cross Vector.cross Vector.scale Matrix3.rowMul <;> ring1

theorem cross_perpendicular_left (form : TernaryForm K)
    (left right : Vector K) :
    form.Perpendicular (form.cross left right) left := by
  unfold Perpendicular
  calc
    form.bilinear (form.cross left right) left =
        Vector.determinant left right left :=
      form.bilinear_cross left right left
    _ = Vector.dot (Vector.cross left right) left :=
      (Vector.scalar_triple_product left right left).symm
    _ = 0 := Vector.cross_dot_left left right

theorem cross_perpendicular_right (form : TernaryForm K)
    (left right : Vector K) :
    form.Perpendicular (form.cross left right) right := by
  unfold Perpendicular
  calc
    form.bilinear (form.cross left right) right =
        Vector.determinant left right right :=
      form.bilinear_cross left right right
    _ = Vector.dot (Vector.cross left right) right :=
      (Vector.scalar_triple_product left right right).symm
    _ = 0 := Vector.cross_dot_right left right

/-- The coordinate compound-matrix identity behind the generalized
Binet--Cauchy formula. -/
theorem dot_cross_adjugate_cross (form : TernaryForm K)
    (first second third fourth : Vector K) :
    Vector.dot (Vector.cross first second)
        (Matrix3.rowMul (Vector.cross third fourth) form.adjugate) =
      form.bilinear first third * form.bilinear second fourth -
        form.bilinear first fourth * form.bilinear second third := by
  have rt_tr : form.matrix.rt = form.matrix.tr :=
    congrArg Matrix3.tr form.symmetric
  have st_ts : form.matrix.st = form.matrix.ts :=
    congrArg Matrix3.ts form.symmetric
  have sr_rs : form.matrix.sr = form.matrix.rs :=
    congrArg Matrix3.rs form.symmetric
  rw [form.adjugate_spec]
  unfold bilinear Matrix3.adjugate Matrix3.rowMul Vector.dot Vector.cross
  rw [rt_tr, st_ts, sr_rs]
  ring1

/-- Determinant-weighted Binet--Cauchy identity for the form-relative cross
product. -/
theorem binet_cauchy (form : TernaryForm K)
    (first second third fourth : Vector K) :
    form.determinant *
        form.bilinear (form.cross first second) (form.cross third fourth) =
      form.bilinear first third * form.bilinear second fourth -
        form.bilinear first fourth * form.bilinear second third := by
  have cancel : form.determinant * form.determinant⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel form.determinant
      form.determinantNonzero
  calc
    form.determinant *
        form.bilinear (form.cross first second) (form.cross third fourth) =
      form.determinant *
        Vector.dot (Vector.cross first second) (form.cross third fourth) := by
      unfold bilinear
      rw [form.rowMul_cross_matrix]
    _ = form.determinant *
        Vector.dot (Vector.cross first second)
          (Matrix3.rowMul (Vector.cross third fourth) form.inverse) := rfl
    _ = form.determinant *
        Vector.dot (Vector.cross first second)
          (Matrix3.rowMul (Vector.cross third fourth)
            (Matrix3.scale (1 / form.determinant) form.adjugate)) := by
      rw [form.inverse_eq_scale_adjugate]
    _ = form.determinant *
        ((1 / form.determinant) *
          Vector.dot (Vector.cross first second)
            (Matrix3.rowMul (Vector.cross third fourth) form.adjugate)) := by
      rw [Matrix3.rowMul_scale, Vector.dot_scale_right]
    _ = Vector.dot (Vector.cross first second)
        (Matrix3.rowMul (Vector.cross third fourth) form.adjugate) := by
      simp only [RFAP.ExplicitField.div_eq_mul_inv]
      calc
        form.determinant *
            (1 * form.determinant⁻¹ *
              Vector.dot (Vector.cross first second)
                (Matrix3.rowMul (Vector.cross third fourth) form.adjugate)) =
          (form.determinant * form.determinant⁻¹) *
            Vector.dot (Vector.cross first second)
              (Matrix3.rowMul (Vector.cross third fourth) form.adjugate) := by
            ring1
        _ = Vector.dot (Vector.cross first second)
            (Matrix3.rowMul (Vector.cross third fourth) form.adjugate) := by
          rw [cancel, one_mul]
    _ = form.bilinear first third * form.bilinear second fourth -
        form.bilinear first fourth * form.bilinear second third :=
      form.dot_cross_adjugate_cross first second third fourth

/-- Determinant-weighted Lagrange identity for a general displayed ternary
form. -/
theorem lagrange (form : TernaryForm K) (left right : Vector K) :
    form.bilinear left right ^ 2 +
        form.determinant * form.quadrance (form.cross left right) =
      form.quadrance left * form.quadrance right := by
  have mixed := form.binet_cauchy left right left right
  unfold quadrance at mixed ⊢
  calc
    form.bilinear left right ^ 2 +
        form.determinant *
          form.bilinear (form.cross left right) (form.cross left right) =
      form.bilinear left right ^ 2 +
        (form.bilinear left left * form.bilinear right right -
          form.bilinear left right * form.bilinear right left) := by
        rw [mixed]
    _ = form.bilinear left left * form.bilinear right right := by
      rw [form.bilinear_comm right left]
      ring1

/-- Determinant-weighted vector triple-product identity. -/
theorem vector_triple_product (form : TernaryForm K)
    (first second third : Vector K) :
    Vector.scale form.determinant
        (form.cross first (form.cross second third)) =
      Vector.sub
        (Vector.scale (form.bilinear first third) second)
        (Vector.scale (form.bilinear first second) third) := by
  apply form.eq_of_bilinear_eq
  intro fourth
  have mixed := form.binet_cauchy first fourth second third
  have swapped :
      Vector.determinant first (form.cross second third) fourth =
        -Vector.determinant first fourth (form.cross second third) := by
    unfold Vector.determinant
    ring1
  calc
    form.bilinear
        (Vector.scale form.determinant
          (form.cross first (form.cross second third))) fourth =
      form.determinant *
        form.bilinear (form.cross first (form.cross second third)) fourth :=
      form.bilinear_scale_left form.determinant _ fourth
    _ = form.determinant *
        Vector.determinant first (form.cross second third) fourth := by
      rw [form.bilinear_cross]
    _ = -(form.determinant *
        Vector.determinant first fourth (form.cross second third)) := by
      rw [swapped]
      ring1
    _ = -(form.determinant *
        form.bilinear (form.cross first fourth)
          (form.cross second third)) := by
      rw [form.bilinear_cross]
    _ = -(form.bilinear first second * form.bilinear fourth third -
        form.bilinear first third * form.bilinear fourth second) := by
      rw [mixed]
    _ = form.bilinear
        (Vector.sub
          (Vector.scale (form.bilinear first third) second)
          (Vector.scale (form.bilinear first second) third)) fourth := by
      rw [form.bilinear_sub_left, form.bilinear_scale_left,
        form.bilinear_scale_left, form.bilinear_comm fourth third,
        form.bilinear_comm fourth second]
      ring1

/-- Reflection in the form-perpendicular plane to a non-null vector.  The
first outer-product argument is the form-dual vector; for the Euclidean form
this reduces to the paper's displayed reflection matrix. -/
def reflection (form : TernaryForm K) (vector : Vector K)
    (_nonNull : form.quadrance vector ≠ 0) : Matrix3 K :=
  Matrix3.sub Matrix3.identity
    (Matrix3.scale (2 / form.quadrance vector)
      (Matrix3.outer (form.dual vector) vector))

theorem rowMul_reflection (form : TernaryForm K) (vector : Vector K)
    (nonNull : form.quadrance vector ≠ 0) (other : Vector K) :
    Matrix3.rowMul other (form.reflection vector nonNull) =
      Vector.sub other
        (Vector.scale
          (2 * form.bilinear other vector / form.quadrance vector) vector) := by
  have bilinearDual := form.bilinear_eq_dot_dual other vector
  ext <;> unfold reflection Matrix3.rowMul Matrix3.sub Matrix3.identity
    Matrix3.scale Matrix3.outer Vector.sub Vector.scale <;>
    simp only [RFAP.ExplicitField.div_eq_mul_inv] <;>
    unfold bilinear dual Matrix3.rowMul Vector.dot at bilinearDual ⊢ <;>
    rw [bilinearDual] <;> ring1

/-- If two displayed vectors have the same quadrance and non-null
difference, reflection in that difference maps the first vector to the
second.  This is the finite reduction step in the constructive
Cartan--Dieudonne argument. -/
theorem rowMul_reflection_difference (form : TernaryForm K)
    (first second : Vector K)
    (equalQuadrance : form.quadrance first = form.quadrance second)
    (differenceNonNull :
      form.quadrance (Vector.sub first second) ≠ 0) :
    Matrix3.rowMul first
        (form.reflection (Vector.sub first second) differenceNonNull) =
      second := by
  have twiceBilinear :
      2 * form.bilinear first (Vector.sub first second) =
        form.quadrance (Vector.sub first second) := by
    calc
      2 * form.bilinear first (Vector.sub first second) =
          2 * (form.quadrance first - form.bilinear first second) := by
        rw [form.bilinear_sub_right]
        rfl
      _ = form.quadrance first -
          2 * form.bilinear first second + form.quadrance second := by
        rw [← equalQuadrance]
        ring1
      _ = form.quadrance (Vector.sub first second) :=
        (form.quadrance_sub first second).symm
  have cancel := RFAP.ExplicitField.mul_inv_cancel
    (form.quadrance (Vector.sub first second)) differenceNonNull
  have coefficient :
      2 * form.bilinear first (Vector.sub first second) /
          form.quadrance (Vector.sub first second) = 1 := by
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    rw [twiceBilinear, cancel]
  rw [form.rowMul_reflection, coefficient, Vector.one_scale]
  ext <;> unfold Vector.sub <;> ring1

private theorem reflection_coefficient (form : TernaryForm K)
    (vector : Vector K) (nonNull : form.quadrance vector ≠ 0) :
    (2 / form.quadrance vector) ^ 2 * form.quadrance vector =
      2 * (2 / form.quadrance vector) := by
  have cancel : form.quadrance vector * (form.quadrance vector)⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel (form.quadrance vector) nonNull
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    (2 * (form.quadrance vector)⁻¹) ^ 2 * form.quadrance vector =
        4 * (form.quadrance vector * (form.quadrance vector)⁻¹) *
          (form.quadrance vector)⁻¹ := by ring1
    _ = 2 * (2 * (form.quadrance vector)⁻¹) := by
      rw [cancel]
      ring1

theorem reflection_square (form : TernaryForm K) (vector : Vector K)
    (nonNull : form.quadrance vector ≠ 0) :
    Matrix3.mul (form.reflection vector nonNull)
      (form.reflection vector nonNull) = Matrix3.identity := by
  have coefficientZero :
      (2 / form.quadrance vector) ^ 2 * form.quadrance vector -
        2 * (2 / form.quadrance vector) = 0 := by
    rw [form.reflection_coefficient vector nonNull]
    ring1
  have dualPair : Vector.dot vector (form.dual vector) =
      form.quadrance vector := by
    rw [← form.bilinear_eq_dot_dual]
    rfl
  calc
    Matrix3.mul (form.reflection vector nonNull)
        (form.reflection vector nonNull) =
      Matrix3.add Matrix3.identity
        (Matrix3.scale
          ((2 / form.quadrance vector) ^ 2 *
              Vector.dot vector (form.dual vector) -
            2 * (2 / form.quadrance vector))
          (Matrix3.outer (form.dual vector) vector)) := by
      ext <;> unfold reflection Matrix3.mul Matrix3.sub Matrix3.add
        Matrix3.identity Matrix3.scale Matrix3.outer Vector.dot <;> ring1
    _ =
      Matrix3.add Matrix3.identity
        (Matrix3.scale
          ((2 / form.quadrance vector) ^ 2 * form.quadrance vector -
            2 * (2 / form.quadrance vector))
          (Matrix3.outer (form.dual vector) vector)) := by
      rw [dualPair]
    _ = Matrix3.identity := by
      rw [coefficientZero]
      ext <;> unfold Matrix3.add Matrix3.scale Matrix3.outer
        Matrix3.identity <;> ring1

theorem rowMul_self_reflection (form : TernaryForm K) (vector : Vector K)
    (nonNull : form.quadrance vector ≠ 0) :
    Matrix3.rowMul vector (form.reflection vector nonNull) =
      Vector.neg vector := by
  have cancel : form.quadrance vector * (form.quadrance vector)⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel (form.quadrance vector) nonNull
  have factor :
      2 * form.bilinear vector vector / form.quadrance vector = (2 : K) := by
    change 2 * form.quadrance vector / form.quadrance vector = (2 : K)
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      2 * form.quadrance vector * (form.quadrance vector)⁻¹ =
          2 * (form.quadrance vector * (form.quadrance vector)⁻¹) := by
        ring1
      _ = 2 := by rw [cancel, mul_one]
  rw [form.rowMul_reflection vector nonNull, factor]
  ext <;> unfold Vector.sub Vector.scale Vector.neg <;> ring1

theorem rowMul_reflection_of_perpendicular (form : TernaryForm K)
    (vector : Vector K) (nonNull : form.quadrance vector ≠ 0)
    (other : Vector K) (perpendicular : form.Perpendicular other vector) :
    Matrix3.rowMul other (form.reflection vector nonNull) = other := by
  unfold Perpendicular at perpendicular
  rw [form.rowMul_reflection vector nonNull, perpendicular, mul_zero,
    RFAP.ExplicitField.zero_div]
  ext <;> unfold Vector.sub Vector.scale <;> ring1

theorem determinant_reflection (form : TernaryForm K)
    (vector : Vector K) (nonNull : form.quadrance vector ≠ 0) :
    Matrix3.determinant (form.reflection vector nonNull) = -1 := by
  have cancel : form.quadrance vector * (form.quadrance vector)⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel (form.quadrance vector) nonNull
  have dualPair : Vector.dot vector (form.dual vector) =
      form.quadrance vector := by
    rw [← form.bilinear_eq_dot_dual]
    rfl
  unfold Matrix3.determinant reflection Matrix3.sub Matrix3.identity
    Matrix3.scale Matrix3.outer
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    _ = 1 - 2 * (form.quadrance vector)⁻¹ *
        Vector.dot vector (form.dual vector) := by
      unfold Vector.dot
      ring1
    _ = 1 - 2 *
        (form.quadrance vector * (form.quadrance vector)⁻¹) := by
      rw [dualPair]
      ring1
    _ = -1 := by rw [cancel]; ring1

/-- A bilinear preservation law on all displayed vectors determines the
matrix preservation certificate, proved by the nine coordinate pairs. -/
theorem preservesMatrix_of_bilinear (form : TernaryForm K)
    (matrix : Matrix3 K)
    (preserves : ∀ left right : Vector K,
      form.bilinear (Matrix3.rowMul left matrix)
          (Matrix3.rowMul right matrix) = form.bilinear left right) :
    Matrix3.mul (Matrix3.mul matrix form.matrix)
        (Matrix3.transpose matrix) = form.matrix := by
  let basisT : Vector K := ⟨1, 0, 0⟩
  let basisR : Vector K := ⟨0, 1, 0⟩
  let basisS : Vector K := ⟨0, 0, 1⟩
  apply Matrix3.ext
  · simpa [bilinear, basisT, Matrix3.rowMul, Matrix3.mul,
      Matrix3.transpose, Vector.dot] using preserves basisT basisT
  · simpa [bilinear, basisT, basisR, Matrix3.rowMul, Matrix3.mul,
      Matrix3.transpose, Vector.dot] using preserves basisT basisR
  · simpa [bilinear, basisT, basisS, Matrix3.rowMul, Matrix3.mul,
      Matrix3.transpose, Vector.dot] using preserves basisT basisS
  · simpa [bilinear, basisT, basisR, Matrix3.rowMul, Matrix3.mul,
      Matrix3.transpose, Vector.dot] using preserves basisR basisT
  · simpa [bilinear, basisR, Matrix3.rowMul, Matrix3.mul,
      Matrix3.transpose, Vector.dot] using preserves basisR basisR
  · simpa [bilinear, basisR, basisS, Matrix3.rowMul, Matrix3.mul,
      Matrix3.transpose, Vector.dot] using preserves basisR basisS
  · simpa [bilinear, basisT, basisS, Matrix3.rowMul, Matrix3.mul,
      Matrix3.transpose, Vector.dot] using preserves basisS basisT
  · simpa [bilinear, basisR, basisS, Matrix3.rowMul, Matrix3.mul,
      Matrix3.transpose, Vector.dot] using preserves basisS basisR
  · simpa [bilinear, basisS, Matrix3.rowMul, Matrix3.mul,
      Matrix3.transpose, Vector.dot] using preserves basisS basisS

private theorem bilinear_sub_scale_both (form : TernaryForm K)
    (first second vector : Vector K) (firstScale secondScale : K) :
    form.bilinear
        (Vector.sub first (Vector.scale firstScale vector))
        (Vector.sub second (Vector.scale secondScale vector)) =
      form.bilinear first second -
        secondScale * form.bilinear first vector -
        firstScale * form.bilinear vector second +
        firstScale * secondScale * form.quadrance vector := by
  rw [form.bilinear_sub_left, form.bilinear_sub_right,
    form.bilinear_sub_right, form.bilinear_scale_left,
    form.bilinear_scale_left, form.bilinear_scale_right,
    form.bilinear_scale_right]
  unfold quadrance
  ring1

private theorem reflection_bilinear_scalar
    (base first second quadrance : K) (quadranceNonzero : quadrance ≠ 0) :
    base - (2 * second / quadrance) * first -
        (2 * first / quadrance) * second +
      (2 * first / quadrance) * (2 * second / quadrance) * quadrance =
      base := by
  have cancel : quadrance * quadrance⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel quadrance quadranceNonzero
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    base - (2 * second * quadrance⁻¹) * first -
          (2 * first * quadrance⁻¹) * second +
        (2 * first * quadrance⁻¹) * (2 * second * quadrance⁻¹) * quadrance =
      base + 4 * first * second * quadrance⁻¹ *
          (quadrance * quadrance⁻¹) -
        4 * first * second * quadrance⁻¹ := by ring1
    _ = base := by rw [cancel]; ring1

theorem reflection_preservesMatrix (form : TernaryForm K)
    (vector : Vector K) (nonNull : form.quadrance vector ≠ 0) :
    Matrix3.mul
        (Matrix3.mul (form.reflection vector nonNull) form.matrix)
        (Matrix3.transpose (form.reflection vector nonNull)) =
      form.matrix := by
  apply form.preservesMatrix_of_bilinear
  intro first second
  rw [form.rowMul_reflection vector nonNull,
    form.rowMul_reflection vector nonNull,
    form.bilinear_sub_scale_both]
  rw [form.bilinear_comm vector second]
  exact reflection_bilinear_scalar
    (form.bilinear first second)
    (form.bilinear first vector)
    (form.bilinear second vector)
    (form.quadrance vector) nonNull

/-- The reflection packaged as an executable form isometry. -/
def reflectionIsometry (form : TernaryForm K) (vector : Vector K)
    (nonNull : form.quadrance vector ≠ 0) : form.Isometry where
  matrix := form.reflection vector nonNull
  inverseMatrix := form.reflection vector nonNull
  matrix_mul_inverse := form.reflection_square vector nonNull
  inverse_mul_matrix := form.reflection_square vector nonNull
  preservesMatrix := form.reflection_preservesMatrix vector nonNull

/-- Cached first Cartan--Dieudonne reduction for a displayed rotation.  A
supplied non-null seed with non-null displacement determines a reflection
which sends its image back to the seed; composing on the right therefore
produces an orientation-reversing isometry fixing that seed. -/
structure DisplacementReflectionReduction (form : TernaryForm K)
    (rotation : form.SpecialOrthogonal) where
  seed : Vector K
  seedNonNull : form.quadrance seed ≠ 0
  mirror : Vector K
  mirror_eq : mirror = Vector.sub (rotation.act seed) seed
  mirrorNonNull : form.quadrance mirror ≠ 0
  reduced : form.Isometry
  reduced_eq : reduced = Isometry.mul rotation.toIsometry
    (form.reflectionIsometry mirror mirrorNonNull)
  seedFixed : reduced.act seed = seed
  determinantMinusOne : Matrix3.determinant reduced.matrix = -1

/-- Execute the first reflection reduction from the supplied finite
denominator certificates. -/
def displacementReflectionReduction (form : TernaryForm K)
    (rotation : form.SpecialOrthogonal) (seed : Vector K)
    (seedNonNull : form.quadrance seed ≠ 0)
    (displacementNonNull :
      form.quadrance (Vector.sub (rotation.act seed) seed) ≠ 0) :
    DisplacementReflectionReduction form rotation where
  seed := seed
  seedNonNull := seedNonNull
  mirror := Vector.sub (rotation.act seed) seed
  mirror_eq := rfl
  mirrorNonNull := displacementNonNull
  reduced := Isometry.mul rotation.toIsometry
    (form.reflectionIsometry (Vector.sub (rotation.act seed) seed)
      displacementNonNull)
  reduced_eq := rfl
  seedFixed := by
    rw [Isometry.act_mul]
    change Matrix3.rowMul (rotation.act seed)
      (form.reflection (Vector.sub (rotation.act seed) seed)
        displacementNonNull) = seed
    apply form.rowMul_reflection_difference
    exact rotation.quadrance_act seed
  determinantMinusOne := by
    change Matrix3.determinant
      (Matrix3.mul rotation.matrix
        (form.reflection (Vector.sub (rotation.act seed) seed)
          displacementNonNull)) = -1
    rw [Matrix3.determinant_mul, rotation.determinantOne,
      form.determinant_reflection, one_mul]

/-- Form-relative half turn about a non-null axis. -/
def halfTurn (form : TernaryForm K) (vector : Vector K)
    (nonNull : form.quadrance vector ≠ 0) : Matrix3 K :=
  Matrix3.neg (form.reflection vector nonNull)

theorem halfTurn_square (form : TernaryForm K) (vector : Vector K)
    (nonNull : form.quadrance vector ≠ 0) :
    Matrix3.mul (form.halfTurn vector nonNull)
      (form.halfTurn vector nonNull) = Matrix3.identity := by
  unfold halfTurn
  rw [Matrix3.mul_neg_neg, form.reflection_square]

theorem halfTurn_preservesMatrix (form : TernaryForm K)
    (vector : Vector K) (nonNull : form.quadrance vector ≠ 0) :
    Matrix3.mul (Matrix3.mul (form.halfTurn vector nonNull) form.matrix)
        (Matrix3.transpose (form.halfTurn vector nonNull)) =
      form.matrix := by
  unfold halfTurn
  rw [Matrix3.transpose_neg]
  calc
    Matrix3.mul
        (Matrix3.mul (Matrix3.neg (form.reflection vector nonNull)) form.matrix)
        (Matrix3.neg
          (Matrix3.transpose (form.reflection vector nonNull))) =
      Matrix3.mul
        (Matrix3.mul (form.reflection vector nonNull) form.matrix)
        (Matrix3.transpose (form.reflection vector nonNull)) := by
      ext <;> unfold Matrix3.mul Matrix3.neg <;> ring1
    _ = form.matrix := form.reflection_preservesMatrix vector nonNull

theorem determinant_halfTurn (form : TernaryForm K) (vector : Vector K)
    (nonNull : form.quadrance vector ≠ 0) :
    Matrix3.determinant (form.halfTurn vector nonNull) = 1 := by
  unfold halfTurn
  rw [Matrix3.determinant_neg, form.determinant_reflection]
  ring1

/-- The form-relative half turn packaged as a determinant-one isometry. -/
def halfTurnRotation (form : TernaryForm K) (vector : Vector K)
    (nonNull : form.quadrance vector ≠ 0) : form.SpecialOrthogonal where
  matrix := form.halfTurn vector nonNull
  inverseMatrix := form.halfTurn vector nonNull
  matrix_mul_inverse := form.halfTurn_square vector nonNull
  inverse_mul_matrix := form.halfTurn_square vector nonNull
  preservesMatrix := form.halfTurn_preservesMatrix vector nonNull
  determinantOne := form.determinant_halfTurn vector nonNull

/-- The relativistic form `t²+r²-s²` singled out in Problem 71. -/
def minkowski (oneNonzero : (1 : K) ≠ 0) : TernaryForm K :=
  ofMatrix (⟨1, 0, 0, 0, 1, 0, 0, 0, -1⟩ : Matrix3 K) (by
    ext <;> unfold Matrix3.transpose <;> ring1) (by
    intro determinantZero
    apply oneNonzero
    have negOneZero : (-1 : K) = 0 := by
      calc
        (-1 : K) = Matrix3.determinant
            (⟨1, 0, 0, 0, 1, 0, 0, 0, -1⟩ : Matrix3 K) := by
          unfold Matrix3.determinant
          ring1
        _ = 0 := determinantZero
    calc
      (1 : K) = -(-1) := by ring1
      _ = -0 := by rw [negOneZero]
      _ = 0 := by ring1)

theorem quadrance_minkowski (oneNonzero : (1 : K) ≠ 0)
    (vector : Vector K) :
    (minkowski oneNonzero).quadrance vector =
      vector.t ^ 2 + vector.r ^ 2 - vector.s ^ 2 := by
  unfold quadrance bilinear minkowski ofMatrix Matrix3.rowMul Vector.dot
  ring1

theorem minkowski_determinant (oneNonzero : (1 : K) ≠ 0) :
    (minkowski oneNonzero).determinant = -1 := by
  unfold minkowski ofMatrix Matrix3.determinant
  ring1

theorem minkowski_adjugate (oneNonzero : (1 : K) ≠ 0) :
    (minkowski oneNonzero).adjugate =
      (⟨-1, 0, 0, 0, -1, 0, 0, 0, 1⟩ : Matrix3 K) := by
  unfold minkowski ofMatrix Matrix3.adjugate
  ext <;> ring1

theorem minkowski_inverse (oneNonzero : (1 : K) ≠ 0) :
    (minkowski oneNonzero).inverse =
      (⟨1, 0, 0, 0, 1, 0, 0, 0, -1⟩ : Matrix3 K) := by
  let form := minkowski oneNonzero
  let matrix : Matrix3 K := ⟨1, 0, 0, 0, 1, 0, 0, 0, -1⟩
  have matrixValue : form.matrix = matrix := rfl
  have selfInverse : Matrix3.mul matrix matrix = Matrix3.identity := by
    ext <;> unfold matrix Matrix3.mul Matrix3.identity <;> ring1
  calc
    form.inverse = Matrix3.mul form.inverse Matrix3.identity := by
      rw [Matrix3.mul_identity]
    _ = Matrix3.mul form.inverse (Matrix3.mul form.matrix form.matrix) := by
      rw [matrixValue, selfInverse]
    _ = Matrix3.mul
        (Matrix3.mul form.inverse form.matrix) form.matrix := by
      rw [Matrix3.mul_assoc]
    _ = Matrix3.mul Matrix3.identity form.matrix := by
      rw [form.inverse_mul_matrix]
    _ = form.matrix := by rw [Matrix3.identity_mul]
    _ = matrix := matrixValue

/-- The Minkowski form has the displayed null direction `(1,0,1)` over every
explicit field. -/
theorem minkowski_null_direction (oneNonzero : (1 : K) ≠ 0) :
    (minkowski oneNonzero).IsNull (⟨1, 0, 1⟩ : Vector K) := by
  unfold IsNull
  rw [quadrance_minkowski]
  ring1

/-- Exact coordinate evaluation of a Minkowski half turn. -/
theorem minkowski_coordinate_halfTurn (oneNonzero : (1 : K) ≠ 0) :
    (minkowski oneNonzero).halfTurn (⟨1, 0, 0⟩ : Vector K) (by
      intro quadranceZero
      apply oneNonzero
      calc
        (1 : K) =
            (minkowski oneNonzero).quadrance (⟨1, 0, 0⟩ : Vector K) := by
          rw [quadrance_minkowski]
          ring1
        _ = 0 := quadranceZero) =
      (⟨1, 0, 0, 0, -1, 0, 0, 0, -1⟩ : Matrix3 K) := by
  let axis : Vector K := ⟨1, 0, 0⟩
  have axisQuadrance :
      (minkowski oneNonzero).quadrance axis = (1 : K) := by
    rw [quadrance_minkowski]
    unfold axis
    ring1
  have oneInverse : ((1 : K)⁻¹) = 1 := by
    calc
      (1 : K)⁻¹ = 1 * (1 : K)⁻¹ := by rw [one_mul]
      _ = 1 := RFAP.ExplicitField.mul_inv_cancel 1 oneNonzero
  change (minkowski oneNonzero).halfTurn axis _ = _
  unfold halfTurn reflection
  rw [axisQuadrance]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  rw [oneInverse]
  ext <;> unfold dual minkowski ofMatrix Matrix3.neg Matrix3.sub
    Matrix3.identity Matrix3.scale Matrix3.outer Matrix3.rowMul axis <;> ring1

end TernaryForm

end RationalRotations
