import RationalRotations.TernaryTheory

/-!
# Pairwise conjugacy of rational Minkowski parabolics

The split Clifford algebra is the displayed two-by-two matrix algebra.  For
one nonzero null-conic parameter pair this file constructs a finite basis in
which its nilpotent matrix is the standard upper-triangular nilpotent.  The
basis uses one decidable chart and has determinant `-1`.  Two such bases and
the two supplied nonzero parabolic parameters then give an explicit
invertible transport matrix.
-/

namespace RationalRotations

variable {K : Type*} [RFAP.ExplicitField K]

namespace MinkowskiClifford

namespace ParabolicConjugacy

private theorem eq_zero_of_nonzero_mul_eq_zero {factor value : K}
    (factorNonzero : factor ≠ 0) (productZero : factor * value = 0) :
    value = 0 := by
  have cancel := RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    value = (factor * factor⁻¹) * value := by rw [cancel, one_mul]
    _ = factor⁻¹ * (factor * value) := by ring1
    _ = 0 := by rw [productZero, mul_zero]

private theorem difference_nonzero_of_sum_zero
    (twoNonzero : (2 : K) ≠ 0) (first second : K)
    (parametersNonzero : first ≠ 0 ∨ second ≠ 0)
    (sumZero : first + second = 0) : first - second ≠ 0 := by
  intro differenceZero
  have twiceFirst : 2 * first = 0 := by
    calc
      2 * first = (first + second) + (first - second) := by ring1
      _ = 0 := by rw [sumZero, differenceZero, add_zero]
  have twiceSecond : 2 * second = 0 := by
    calc
      2 * second = (first + second) - (first - second) := by ring1
      _ = 0 := by rw [sumZero, differenceZero]; ring1
  have firstZero := eq_zero_of_nonzero_mul_eq_zero twoNonzero twiceFirst
  have secondZero := eq_zero_of_nonzero_mul_eq_zero twoNonzero twiceSecond
  rcases parametersNonzero with firstNonzero | secondNonzero
  · exact firstNonzero firstZero
  · exact secondNonzero secondZero

/-- The standard rank-one nilpotent and its scalar-one unipotent family. -/
def standardNilpotent : Matrix2 K := ⟨0, 1, 0, 0⟩

def standardParabolic (parameter : K) : Matrix2 K :=
  ⟨1, parameter, 0, 1⟩

/-- A diagonal matrix that changes the standard unipotent parameter from the
left supplied value to the right supplied value. -/
def parameterDiagonal (left right : K) : Matrix2 K :=
  ⟨left, 0, 0, right⟩

theorem standardParabolic_parameterDiagonal (left right : K) :
    Matrix2.mul (standardParabolic left) (parameterDiagonal left right) =
      Matrix2.mul (parameterDiagonal left right)
        (standardParabolic right) := by
  apply Matrix2.ext <;>
    unfold standardParabolic parameterDiagonal Matrix2.mul <;> ring1

theorem parameterDiagonal_determinant (left right : K) :
    Matrix2.determinant (parameterDiagonal left right) = left * right := by
  unfold Matrix2.determinant parameterDiagonal
  ring1

/-- One finite chart turns the null matrix attached to `(first,second)` into
the standard nilpotent.  Its first column spans the null image; the second is
chosen to pair to one with the corresponding covector. -/
def nullBasis [DecidableEq K] (first second : K) : Matrix2 K :=
  if _sumNonzero : first + second ≠ 0 then
    ⟨first - second, (first + second)⁻¹,
      first + second, 0⟩
  else
    ⟨first - second, 0,
      first + second, -(first - second)⁻¹⟩

theorem nullBasis_determinant [DecidableEq K]
    (twoNonzero : (2 : K) ≠ 0) (first second : K)
    (parametersNonzero : first ≠ 0 ∨ second ≠ 0) :
    Matrix2.determinant (nullBasis first second) = -1 := by
  by_cases sumZero : first + second = 0
  · have differenceNonzero := difference_nonzero_of_sum_zero
      twoNonzero first second parametersNonzero sumZero
    have cancel := RFAP.ExplicitField.mul_inv_cancel
      (first - second) differenceNonzero
    rw [nullBasis, dif_neg (fun nonzero => nonzero sumZero)]
    change (first - second) * (-(first - second)⁻¹) -
      0 * (first + second) = -1
    calc
      (first - second) * (-(first - second)⁻¹) -
          0 * (first + second) =
        -((first - second) * (first - second)⁻¹) := by ring1
      _ = -1 := by rw [cancel]
  · have sumNonzero : first + second ≠ 0 := sumZero
    have cancel := RFAP.ExplicitField.mul_inv_cancel
      (first + second) sumNonzero
    have reverseCancel : (first + second)⁻¹ * (first + second) = 1 := by
      calc
        (first + second)⁻¹ * (first + second) =
            (first + second) * (first + second)⁻¹ := by ring1
        _ = 1 := cancel
    rw [nullBasis, dif_pos sumNonzero]
    change (first - second) * 0 -
      (first + second)⁻¹ * (first + second) = -1
    rw [reverseCancel]
    ring1

/-- The split-matrix display of the supplied null-conic parabolic. -/
theorem toMatrix_parabolicAt_nullParameter
    (oneNonzero : (1 : K) ≠ 0) (first second parameter : K) :
    toMatrix oneNonzero
        (parabolicAt oneNonzero (nullParameter first second)
          (nullParameter_isNull oneNonzero first second)
          parameter).toEvenClifford =
      ⟨1 + parameter * (first + second) * (first - second),
        -(parameter * (first - second) ^ 2),
        parameter * (first + second) ^ 2,
        1 - parameter * (first + second) * (first - second)⟩ := by
  apply Matrix2.ext <;>
    unfold toMatrix parabolicAt parabolicValue parabolicRaw nullParameter
      Vector.scale <;> ring1

/-- The chart basis intertwines the displayed parabolic with the standard
upper-triangular unipotent having the same scalar parameter. -/
theorem parabolicMatrix_mul_nullBasis [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (first second parameter : K)
    (parametersNonzero : first ≠ 0 ∨ second ≠ 0) :
    Matrix2.mul
        (toMatrix oneNonzero
          (parabolicAt oneNonzero (nullParameter first second)
            (nullParameter_isNull oneNonzero first second)
            parameter).toEvenClifford)
        (nullBasis first second) =
      Matrix2.mul (nullBasis first second)
        (standardParabolic parameter) := by
  rw [toMatrix_parabolicAt_nullParameter]
  by_cases sumZero : first + second = 0
  · have differenceNonzero := difference_nonzero_of_sum_zero
      twoNonzero first second parametersNonzero sumZero
    have cancel := RFAP.ExplicitField.mul_inv_cancel
      (first - second) differenceNonzero
    have reverseCancel : (first - second)⁻¹ * (first - second) = 1 := by
      calc
        (first - second)⁻¹ * (first - second) =
            (first - second) * (first - second)⁻¹ := by ring1
        _ = 1 := cancel
    rw [nullBasis, dif_neg (fun nonzero => nonzero sumZero)]
    apply Matrix2.ext
    · simp only [Matrix2.mul, standardParabolic]
      rw [sumZero]
      ring1
    · simp only [Matrix2.mul, standardParabolic]
      rw [sumZero]
      calc
        (1 + parameter * 0 * (first - second)) * 0 +
            -(parameter * (first - second) ^ 2) *
              (-(first - second)⁻¹) =
          parameter * (first - second) *
            ((first - second) * (first - second)⁻¹) := by ring1
        _ = parameter * (first - second) := by rw [cancel]; ring1
        _ = (first - second) * parameter + 0 * 1 := by ring1
    · simp only [Matrix2.mul, standardParabolic]
      rw [sumZero]
      ring1
    · simp only [Matrix2.mul, standardParabolic]
      rw [sumZero]
      ring1
  · have sumNonzero : first + second ≠ 0 := sumZero
    have cancel := RFAP.ExplicitField.mul_inv_cancel
      (first + second) sumNonzero
    have reverseCancel : (first + second)⁻¹ * (first + second) = 1 := by
      calc
        (first + second)⁻¹ * (first + second) =
            (first + second) * (first + second)⁻¹ := by ring1
        _ = 1 := cancel
    rw [nullBasis, dif_pos sumNonzero]
    apply Matrix2.ext
    · simp only [Matrix2.mul, standardParabolic]
      ring1
    · simp only [Matrix2.mul, standardParabolic]
      calc
        (1 + parameter * (first + second) * (first - second)) *
              (first + second)⁻¹ +
            -(parameter * (first - second) ^ 2) * 0 =
          (first + second)⁻¹ + parameter * (first - second) *
            ((first + second) * (first + second)⁻¹) := by ring1
        _ = (first + second)⁻¹ +
            parameter * (first - second) := by rw [cancel]; ring1
        _ = (first - second) * parameter +
            (first + second)⁻¹ * 1 := by ring1
    · simp only [Matrix2.mul, standardParabolic]
      ring1
    · simp only [Matrix2.mul, standardParabolic]
      calc
        parameter * (first + second) ^ 2 * (first + second)⁻¹ +
            (1 - parameter * (first + second) * (first - second)) * 0 =
          parameter * (first + second) *
            ((first + second) * (first + second)⁻¹) := by ring1
        _ = parameter * (first + second) := by rw [cancel]; ring1
        _ = (first + second) * parameter + 0 * 1 := by ring1

/-- Finite cached basis data for one parametrized nonzero null direction. -/
structure NullBasisData [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (first second : K) (parametersNonzero : first ≠ 0 ∨ second ≠ 0)
    where
  basis : Matrix2 K
  basis_eq : basis = nullBasis first second
  determinant_eq : Matrix2.determinant basis = -1
  intertwines : ∀ parameter : K,
    Matrix2.mul
        (toMatrix oneNonzero
          (parabolicAt oneNonzero (nullParameter first second)
            (nullParameter_isNull oneNonzero first second)
            parameter).toEvenClifford)
        basis = Matrix2.mul basis (standardParabolic parameter)

def nullBasisData [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (first second : K) (parametersNonzero : first ≠ 0 ∨ second ≠ 0) :
    NullBasisData oneNonzero twoNonzero first second parametersNonzero where
  basis := nullBasis first second
  basis_eq := rfl
  determinant_eq := nullBasis_determinant twoNonzero first second
    parametersNonzero
  intertwines := fun parameter =>
    parabolicMatrix_mul_nullBasis oneNonzero twoNonzero first second
      parameter parametersNonzero

private theorem mul_scale_identity (factor : K) (matrix : Matrix2 K) :
    Matrix2.mul matrix (Matrix2.scale factor Matrix2.identity) =
      Matrix2.scale factor matrix := by
  apply Matrix2.ext <;>
    unfold Matrix2.mul Matrix2.scale Matrix2.identity <;> ring1

private theorem scale_identity_mul (factor : K) (matrix : Matrix2 K) :
    Matrix2.mul (Matrix2.scale factor Matrix2.identity) matrix =
      Matrix2.scale factor matrix := by
  apply Matrix2.ext <;>
    unfold Matrix2.mul Matrix2.scale Matrix2.identity <;> ring1

private theorem scale_neg_one_injective {left right : Matrix2 K}
    (equal : Matrix2.scale (-1) left = Matrix2.scale (-1) right) :
    left = right := by
  apply Matrix2.ext
  · have coordinate := congrArg Matrix2.tt equal
    change (-1 : K) * left.tt = (-1 : K) * right.tt at coordinate
    calc
      left.tt = -((-1 : K) * left.tt) := by ring1
      _ = -((-1 : K) * right.tt) := by rw [coordinate]
      _ = right.tt := by ring1
  · have coordinate := congrArg Matrix2.tr equal
    change (-1 : K) * left.tr = (-1 : K) * right.tr at coordinate
    calc
      left.tr = -((-1 : K) * left.tr) := by ring1
      _ = -((-1 : K) * right.tr) := by rw [coordinate]
      _ = right.tr := by ring1
  · have coordinate := congrArg Matrix2.rt equal
    change (-1 : K) * left.rt = (-1 : K) * right.rt at coordinate
    calc
      left.rt = -((-1 : K) * left.rt) := by ring1
      _ = -((-1 : K) * right.rt) := by rw [coordinate]
      _ = right.rt := by ring1
  · have coordinate := congrArg Matrix2.rr equal
    change (-1 : K) * left.rr = (-1 : K) * right.rr at coordinate
    calc
      left.rr = -((-1 : K) * left.rr) := by ring1
      _ = -((-1 : K) * right.rr) := by rw [coordinate]
      _ = right.rr := by ring1

private theorem mul_right_cancel_of_determinant_eq_neg_one
    (basis left right : Matrix2 K)
    (determinantEq : Matrix2.determinant basis = -1)
    (equal : Matrix2.mul left basis = Matrix2.mul right basis) :
    left = right := by
  have scaled : Matrix2.scale (-1) left = Matrix2.scale (-1) right := by
    calc
      Matrix2.scale (-1) left =
          Matrix2.mul left
            (Matrix2.scale (-1) Matrix2.identity) :=
        (mul_scale_identity (-1) left).symm
      _ = Matrix2.mul left
          (Matrix2.mul basis (Matrix2.adjugate basis)) := by
        rw [Matrix2.mul_adjugate, determinantEq]
      _ = Matrix2.mul (Matrix2.mul left basis)
          (Matrix2.adjugate basis) := by rw [Matrix2.mul_assoc]
      _ = Matrix2.mul (Matrix2.mul right basis)
          (Matrix2.adjugate basis) := by rw [equal]
      _ = Matrix2.mul right
          (Matrix2.mul basis (Matrix2.adjugate basis)) := by
        rw [Matrix2.mul_assoc]
      _ = Matrix2.mul right
          (Matrix2.scale (-1) Matrix2.identity) := by
        rw [Matrix2.mul_adjugate, determinantEq]
      _ = Matrix2.scale (-1) right := mul_scale_identity (-1) right
  exact scale_neg_one_injective scaled

/-- The adjugate basis intertwines in the reverse direction. -/
theorem nullBasis_adjugate_mul_parabolicMatrix [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (first second parameter : K)
    (parametersNonzero : first ≠ 0 ∨ second ≠ 0) :
    Matrix2.mul (Matrix2.adjugate (nullBasis first second))
        (toMatrix oneNonzero
          (parabolicAt oneNonzero (nullParameter first second)
            (nullParameter_isNull oneNonzero first second)
            parameter).toEvenClifford) =
      Matrix2.mul (standardParabolic parameter)
        (Matrix2.adjugate (nullBasis first second)) := by
  let basis := nullBasis first second
  let parabolicMatrix :=
    toMatrix oneNonzero
      (parabolicAt oneNonzero (nullParameter first second)
        (nullParameter_isNull oneNonzero first second)
        parameter).toEvenClifford
  have determinantEq : Matrix2.determinant basis = -1 :=
    nullBasis_determinant twoNonzero first second parametersNonzero
  apply mul_right_cancel_of_determinant_eq_neg_one basis _ _ determinantEq
  calc
    Matrix2.mul
          (Matrix2.mul (Matrix2.adjugate basis) parabolicMatrix) basis =
        Matrix2.mul (Matrix2.adjugate basis)
          (Matrix2.mul parabolicMatrix basis) := by rw [Matrix2.mul_assoc]
    _ = Matrix2.mul (Matrix2.adjugate basis)
        (Matrix2.mul basis (standardParabolic parameter)) := by
      rw [parabolicMatrix_mul_nullBasis oneNonzero twoNonzero first second
        parameter parametersNonzero]
    _ = Matrix2.mul
        (Matrix2.mul (Matrix2.adjugate basis) basis)
        (standardParabolic parameter) := by rw [Matrix2.mul_assoc]
    _ = Matrix2.mul (Matrix2.scale (-1) Matrix2.identity)
        (standardParabolic parameter) := by
      rw [Matrix2.adjugate_mul, determinantEq]
    _ = Matrix2.scale (-1) (standardParabolic parameter) :=
      scale_identity_mul (-1) (standardParabolic parameter)
    _ = Matrix2.mul (standardParabolic parameter)
        (Matrix2.scale (-1) Matrix2.identity) := by
      rw [mul_scale_identity]
    _ = Matrix2.mul (standardParabolic parameter)
        (Matrix2.mul (Matrix2.adjugate basis) basis) := by
      rw [Matrix2.adjugate_mul, determinantEq]
    _ = Matrix2.mul
        (Matrix2.mul (standardParabolic parameter)
          (Matrix2.adjugate basis)) basis := by rw [Matrix2.mul_assoc]

/-- The explicit two-by-two transporter between two parametrized nonzero
parabolics. -/
def transportMatrix [DecidableEq K]
    (leftFirst leftSecond rightFirst rightSecond leftParameter
      rightParameter : K) : Matrix2 K :=
  Matrix2.mul
    (Matrix2.mul (nullBasis leftFirst leftSecond)
      (parameterDiagonal leftParameter rightParameter))
    (Matrix2.adjugate (nullBasis rightFirst rightSecond))

theorem transportMatrix_determinant [DecidableEq K]
    (twoNonzero : (2 : K) ≠ 0)
    (leftFirst leftSecond rightFirst rightSecond leftParameter
      rightParameter : K)
    (leftCoordinatesNonzero : leftFirst ≠ 0 ∨ leftSecond ≠ 0)
    (rightCoordinatesNonzero : rightFirst ≠ 0 ∨ rightSecond ≠ 0) :
    Matrix2.determinant
        (transportMatrix leftFirst leftSecond rightFirst rightSecond
          leftParameter rightParameter) = leftParameter * rightParameter := by
  unfold transportMatrix
  rw [Matrix2.determinant_mul, Matrix2.determinant_mul,
    Matrix2.determinant_adjugate,
    nullBasis_determinant twoNonzero leftFirst leftSecond
      leftCoordinatesNonzero,
    nullBasis_determinant twoNonzero rightFirst rightSecond
      rightCoordinatesNonzero,
    parameterDiagonal_determinant]
  ring1

/-- The cached transport matrix intertwines the two displayed unipotents. -/
theorem parabolicMatrix_mul_transportMatrix [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (leftFirst leftSecond rightFirst rightSecond leftParameter
      rightParameter : K)
    (leftCoordinatesNonzero : leftFirst ≠ 0 ∨ leftSecond ≠ 0)
    (rightCoordinatesNonzero : rightFirst ≠ 0 ∨ rightSecond ≠ 0) :
    Matrix2.mul
        (toMatrix oneNonzero
          (parabolicAt oneNonzero (nullParameter leftFirst leftSecond)
            (nullParameter_isNull oneNonzero leftFirst leftSecond)
            leftParameter).toEvenClifford)
        (transportMatrix leftFirst leftSecond rightFirst rightSecond
          leftParameter rightParameter) =
      Matrix2.mul
        (transportMatrix leftFirst leftSecond rightFirst rightSecond
          leftParameter rightParameter)
        (toMatrix oneNonzero
          (parabolicAt oneNonzero (nullParameter rightFirst rightSecond)
            (nullParameter_isNull oneNonzero rightFirst rightSecond)
            rightParameter).toEvenClifford) := by
  unfold transportMatrix
  calc
    Matrix2.mul
          (toMatrix oneNonzero
            (parabolicAt oneNonzero (nullParameter leftFirst leftSecond)
              (nullParameter_isNull oneNonzero leftFirst leftSecond)
              leftParameter).toEvenClifford)
          (Matrix2.mul
            (Matrix2.mul (nullBasis leftFirst leftSecond)
              (parameterDiagonal leftParameter rightParameter))
            (Matrix2.adjugate (nullBasis rightFirst rightSecond))) =
        Matrix2.mul
          (Matrix2.mul
            (Matrix2.mul
              (toMatrix oneNonzero
                (parabolicAt oneNonzero
                  (nullParameter leftFirst leftSecond)
                  (nullParameter_isNull oneNonzero leftFirst leftSecond)
                  leftParameter).toEvenClifford)
              (nullBasis leftFirst leftSecond))
            (parameterDiagonal leftParameter rightParameter))
          (Matrix2.adjugate (nullBasis rightFirst rightSecond)) := by
      rw [← Matrix2.mul_assoc, ← Matrix2.mul_assoc]
    _ = Matrix2.mul
        (Matrix2.mul
          (Matrix2.mul (nullBasis leftFirst leftSecond)
            (standardParabolic leftParameter))
          (parameterDiagonal leftParameter rightParameter))
        (Matrix2.adjugate (nullBasis rightFirst rightSecond)) := by
      rw [parabolicMatrix_mul_nullBasis oneNonzero twoNonzero leftFirst
        leftSecond leftParameter leftCoordinatesNonzero]
    _ = Matrix2.mul
        (Matrix2.mul (nullBasis leftFirst leftSecond)
          (Matrix2.mul (standardParabolic leftParameter)
            (parameterDiagonal leftParameter rightParameter)))
        (Matrix2.adjugate (nullBasis rightFirst rightSecond)) := by
      exact congrArg
        (fun matrix => Matrix2.mul matrix
          (Matrix2.adjugate (nullBasis rightFirst rightSecond)))
        (Matrix2.mul_assoc (nullBasis leftFirst leftSecond)
          (standardParabolic leftParameter)
          (parameterDiagonal leftParameter rightParameter))
    _ = Matrix2.mul
        (Matrix2.mul (nullBasis leftFirst leftSecond)
          (Matrix2.mul (parameterDiagonal leftParameter rightParameter)
            (standardParabolic rightParameter)))
        (Matrix2.adjugate (nullBasis rightFirst rightSecond)) := by
      rw [standardParabolic_parameterDiagonal]
    _ = Matrix2.mul
        (Matrix2.mul
          (Matrix2.mul (nullBasis leftFirst leftSecond)
            (parameterDiagonal leftParameter rightParameter))
          (standardParabolic rightParameter))
        (Matrix2.adjugate (nullBasis rightFirst rightSecond)) := by
      exact congrArg
        (fun matrix => Matrix2.mul matrix
          (Matrix2.adjugate (nullBasis rightFirst rightSecond)))
        (Matrix2.mul_assoc (nullBasis leftFirst leftSecond)
          (parameterDiagonal leftParameter rightParameter)
          (standardParabolic rightParameter)).symm
    _ = Matrix2.mul
        (Matrix2.mul (nullBasis leftFirst leftSecond)
          (parameterDiagonal leftParameter rightParameter))
        (Matrix2.mul (standardParabolic rightParameter)
          (Matrix2.adjugate (nullBasis rightFirst rightSecond))) := by
      rw [Matrix2.mul_assoc]
    _ = Matrix2.mul
        (Matrix2.mul (nullBasis leftFirst leftSecond)
          (parameterDiagonal leftParameter rightParameter))
        (Matrix2.mul (Matrix2.adjugate (nullBasis rightFirst rightSecond))
          (toMatrix oneNonzero
            (parabolicAt oneNonzero
              (nullParameter rightFirst rightSecond)
              (nullParameter_isNull oneNonzero rightFirst rightSecond)
              rightParameter).toEvenClifford)) := by
      rw [nullBasis_adjugate_mul_parabolicMatrix oneNonzero twoNonzero
        rightFirst rightSecond rightParameter rightCoordinatesNonzero]
    _ = Matrix2.mul
        (Matrix2.mul
          (Matrix2.mul (nullBasis leftFirst leftSecond)
            (parameterDiagonal leftParameter rightParameter))
          (Matrix2.adjugate (nullBasis rightFirst rightSecond)))
        (toMatrix oneNonzero
          (parabolicAt oneNonzero (nullParameter rightFirst rightSecond)
            (nullParameter_isNull oneNonzero rightFirst rightSecond)
            rightParameter).toEvenClifford) := by
      rw [← Matrix2.mul_assoc]

/-- Cached finite transporter data, including its exact determinant and
intertwining equation. -/
structure TransportMatrixData [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (leftFirst leftSecond rightFirst rightSecond leftParameter
      rightParameter : K)
    (leftCoordinatesNonzero : leftFirst ≠ 0 ∨ leftSecond ≠ 0)
    (rightCoordinatesNonzero : rightFirst ≠ 0 ∨ rightSecond ≠ 0)
    (leftParameterNonzero : leftParameter ≠ 0)
    (rightParameterNonzero : rightParameter ≠ 0) where
  matrix : Matrix2 K
  matrix_eq : matrix = transportMatrix leftFirst leftSecond rightFirst
    rightSecond leftParameter rightParameter
  determinant_eq : Matrix2.determinant matrix = leftParameter * rightParameter
  determinant_nonzero : Matrix2.determinant matrix ≠ 0
  intertwines :
    Matrix2.mul
        (toMatrix oneNonzero
          (parabolicAt oneNonzero (nullParameter leftFirst leftSecond)
            (nullParameter_isNull oneNonzero leftFirst leftSecond)
            leftParameter).toEvenClifford) matrix =
      Matrix2.mul matrix
        (toMatrix oneNonzero
          (parabolicAt oneNonzero (nullParameter rightFirst rightSecond)
            (nullParameter_isNull oneNonzero rightFirst rightSecond)
            rightParameter).toEvenClifford)

def transportMatrixData [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (leftFirst leftSecond rightFirst rightSecond leftParameter
      rightParameter : K)
    (leftCoordinatesNonzero : leftFirst ≠ 0 ∨ leftSecond ≠ 0)
    (rightCoordinatesNonzero : rightFirst ≠ 0 ∨ rightSecond ≠ 0)
    (leftParameterNonzero : leftParameter ≠ 0)
    (rightParameterNonzero : rightParameter ≠ 0) :
    TransportMatrixData oneNonzero twoNonzero leftFirst leftSecond rightFirst
      rightSecond leftParameter rightParameter leftCoordinatesNonzero
      rightCoordinatesNonzero leftParameterNonzero rightParameterNonzero := by
  let matrix := transportMatrix leftFirst leftSecond rightFirst rightSecond
    leftParameter rightParameter
  have determinantEq := transportMatrix_determinant twoNonzero leftFirst
    leftSecond rightFirst rightSecond leftParameter rightParameter
    leftCoordinatesNonzero rightCoordinatesNonzero
  exact
    { matrix := matrix
      matrix_eq := rfl
      determinant_eq := determinantEq
      determinant_nonzero := by
        rw [determinantEq]
        exact RFAP.ExplicitField.mul_ne_zero leftParameterNonzero
          rightParameterNonzero
      intertwines := parabolicMatrix_mul_transportMatrix oneNonzero twoNonzero
        leftFirst leftSecond rightFirst rightSecond leftParameter
        rightParameter leftCoordinatesNonzero rightCoordinatesNonzero }

private theorem toMatrix_scale (oneNonzero : (1 : K) ≠ 0)
    (factor : K)
    (value : (TernaryForm.minkowski oneNonzero).EvenClifford) :
    toMatrix oneNonzero (TernaryForm.EvenClifford.scale factor value) =
      Matrix2.scale factor (toMatrix oneNonzero value) := by
  apply Matrix2.ext <;>
    unfold toMatrix TernaryForm.EvenClifford.scale Matrix2.scale
      Vector.scale <;> ring1

/-- Lift an explicitly invertible split matrix to a non-null Clifford value.
The determinant certificate becomes the cached reduced-norm certificate. -/
def nonNullFromMatrix (oneNonzero : (1 : K) ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) (matrix : Matrix2 K)
    (determinantNonzero : Matrix2.determinant matrix ≠ 0) :
    (TernaryForm.minkowski oneNonzero).NonNullEvenClifford where
  toEvenClifford := fromMatrix oneNonzero matrix
  normNonzero := by
    have determinantEq := determinant_toMatrix oneNonzero
      (fromMatrix oneNonzero matrix)
    rw [toMatrix_fromMatrix oneNonzero twoNonzero matrix] at determinantEq
    rw [← determinantEq]
    exact determinantNonzero

theorem toMatrix_nonNullFromMatrix (oneNonzero : (1 : K) ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) (matrix : Matrix2 K)
    (determinantNonzero : Matrix2.determinant matrix ≠ 0) :
    toMatrix oneNonzero
        (nonNullFromMatrix oneNonzero twoNonzero matrix
          determinantNonzero).toEvenClifford = matrix :=
  toMatrix_fromMatrix oneNonzero twoNonzero matrix

/-- The matrix transporter, lifted to a non-null Clifford value, conjugates
the left displayed parabolic to a projectively equivalent representative of
the right displayed parabolic. -/
theorem transported_parabolic_equivalent [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (leftFirst leftSecond rightFirst rightSecond leftParameter
      rightParameter : K)
    (leftCoordinatesNonzero : leftFirst ≠ 0 ∨ leftSecond ≠ 0)
    (rightCoordinatesNonzero : rightFirst ≠ 0 ∨ rightSecond ≠ 0)
    (leftParameterNonzero : leftParameter ≠ 0)
    (rightParameterNonzero : rightParameter ≠ 0) :
    let data := transportMatrixData oneNonzero twoNonzero leftFirst
      leftSecond rightFirst rightSecond leftParameter rightParameter
      leftCoordinatesNonzero rightCoordinatesNonzero leftParameterNonzero
      rightParameterNonzero
    let conjugator := nonNullFromMatrix oneNonzero twoNonzero data.matrix
      data.determinant_nonzero
    let left := parabolicAt oneNonzero
      (nullParameter leftFirst leftSecond)
      (nullParameter_isNull oneNonzero leftFirst leftSecond) leftParameter
    let right := parabolicAt oneNonzero
      (nullParameter rightFirst rightSecond)
      (nullParameter_isNull oneNonzero rightFirst rightSecond) rightParameter
    right.Equivalent
      (TernaryForm.NonNullEvenClifford.mul
        (TernaryForm.NonNullEvenClifford.mul conjugator.conjugate left)
        conjugator) := by
  let data := transportMatrixData oneNonzero twoNonzero leftFirst
    leftSecond rightFirst rightSecond leftParameter rightParameter
    leftCoordinatesNonzero rightCoordinatesNonzero leftParameterNonzero
    rightParameterNonzero
  let conjugator := nonNullFromMatrix oneNonzero twoNonzero data.matrix
    data.determinant_nonzero
  let left := parabolicAt oneNonzero
    (nullParameter leftFirst leftSecond)
    (nullParameter_isNull oneNonzero leftFirst leftSecond) leftParameter
  let right := parabolicAt oneNonzero
    (nullParameter rightFirst rightSecond)
    (nullParameter_isNull oneNonzero rightFirst rightSecond) rightParameter
  change right.Equivalent
    (TernaryForm.NonNullEvenClifford.mul
      (TernaryForm.NonNullEvenClifford.mul conjugator.conjugate left)
      conjugator)
  refine ⟨Matrix2.determinant data.matrix, data.determinant_nonzero, ?_⟩
  change TernaryForm.EvenClifford.mul
      (TernaryForm.EvenClifford.mul
        conjugator.toEvenClifford.conjugate left.toEvenClifford)
      conjugator.toEvenClifford =
    TernaryForm.EvenClifford.scale (Matrix2.determinant data.matrix)
      right.toEvenClifford
  apply toMatrix_injective oneNonzero twoNonzero
  rw [toMatrix_mul, toMatrix_mul, toMatrix_conjugate,
    toMatrix_nonNullFromMatrix, toMatrix_scale]
  calc
    Matrix2.mul
          (Matrix2.mul (Matrix2.adjugate data.matrix)
            (toMatrix oneNonzero left.toEvenClifford)) data.matrix =
        Matrix2.mul (Matrix2.adjugate data.matrix)
          (Matrix2.mul (toMatrix oneNonzero left.toEvenClifford)
            data.matrix) := Matrix2.mul_assoc _ _ _
    _ = Matrix2.mul (Matrix2.adjugate data.matrix)
        (Matrix2.mul data.matrix
          (toMatrix oneNonzero right.toEvenClifford)) := by
      rw [data.intertwines]
    _ = Matrix2.mul
        (Matrix2.mul (Matrix2.adjugate data.matrix) data.matrix)
        (toMatrix oneNonzero right.toEvenClifford) :=
      (Matrix2.mul_assoc _ _ _).symm
    _ = Matrix2.mul
        (Matrix2.scale (Matrix2.determinant data.matrix) Matrix2.identity)
        (toMatrix oneNonzero right.toEvenClifford) := by
      rw [Matrix2.adjugate_mul]
    _ = Matrix2.scale (Matrix2.determinant data.matrix)
        (toMatrix oneNonzero right.toEvenClifford) :=
      scale_identity_mul _ _

/-- Fully cached constructive conjugacy data for two rational parabolic
rotations.  The witness retains the executable split matrix, its determinant
certificate, its Clifford lift, and the resulting special-orthogonal
conjugator. -/
structure ParabolicConjugacyWitness
    (oneNonzero : (1 : K) ≠ 0)
    (left right :
      (TernaryForm.minkowski oneNonzero).SpecialOrthogonal) where
  matrix : Matrix2 K
  determinantNonzero : Matrix2.determinant matrix ≠ 0
  conjugatorValue :
    (TernaryForm.minkowski oneNonzero).NonNullEvenClifford
  conjugatorMatrix :
    toMatrix oneNonzero conjugatorValue.toEvenClifford = matrix
  conjugator : (TernaryForm.minkowski oneNonzero).SpecialOrthogonal
  conjugator_eq : conjugator = conjugatorValue.actionRotation
  conjugates :
    TernaryForm.SpecialOrthogonal.mul
        (TernaryForm.SpecialOrthogonal.mul
          (TernaryForm.SpecialOrthogonal.inverse conjugator) left)
        conjugator = right

/-- Given any two complete parabolic classifications, compute a rational
conjugator between their rotations.  In particular, the nonidentity split
rational parabolics form one conjugacy class; no square-class or infinitary
orbit argument is needed. -/
def parabolicConjugacyWitness [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (leftRotation rightRotation :
      (TernaryForm.minkowski oneNonzero).SpecialOrthogonal)
    (leftClassification :
      ParabolicClassification oneNonzero twoNonzero leftRotation)
    (rightClassification :
      ParabolicClassification oneNonzero twoNonzero rightRotation) :
    ParabolicConjugacyWitness oneNonzero leftRotation rightRotation := by
  let leftFirst := leftClassification.coordinates.first
  let leftSecond := leftClassification.coordinates.second
  let rightFirst := rightClassification.coordinates.first
  let rightSecond := rightClassification.coordinates.second
  let leftParameter := leftClassification.parameter
  let rightParameter := rightClassification.parameter
  let data := transportMatrixData oneNonzero twoNonzero leftFirst leftSecond
    rightFirst rightSecond leftParameter rightParameter
    leftClassification.coordinates.parametersNonzero
    rightClassification.coordinates.parametersNonzero
    leftClassification.parameterNonzero rightClassification.parameterNonzero
  let conjugatorValue := nonNullFromMatrix oneNonzero twoNonzero data.matrix
    data.determinant_nonzero
  let leftNormal := parabolicAt oneNonzero
    (nullParameter leftFirst leftSecond)
    (nullParameter_isNull oneNonzero leftFirst leftSecond) leftParameter
  let rightNormal := parabolicAt oneNonzero
    (nullParameter rightFirst rightSecond)
    (nullParameter_isNull oneNonzero rightFirst rightSecond) rightParameter
  have equivalent : rightNormal.Equivalent
      (TernaryForm.NonNullEvenClifford.mul
        (TernaryForm.NonNullEvenClifford.mul
          conjugatorValue.conjugate leftNormal) conjugatorValue) := by
    exact transported_parabolic_equivalent oneNonzero twoNonzero leftFirst
      leftSecond rightFirst rightSecond leftParameter rightParameter
      leftClassification.coordinates.parametersNonzero
      rightClassification.coordinates.parametersNonzero
      leftClassification.parameterNonzero rightClassification.parameterNonzero
  have leftRotationEq : leftRotation = leftNormal.actionRotation :=
    leftClassification.rotation_eq
  have rightRotationEq : rightRotation = rightNormal.actionRotation :=
    rightClassification.rotation_eq
  have conjugates :
      TernaryForm.SpecialOrthogonal.mul
          (TernaryForm.SpecialOrthogonal.mul
            (TernaryForm.SpecialOrthogonal.inverse
              conjugatorValue.actionRotation) leftRotation)
          conjugatorValue.actionRotation = rightRotation := by
    calc
      TernaryForm.SpecialOrthogonal.mul
            (TernaryForm.SpecialOrthogonal.mul
              (TernaryForm.SpecialOrthogonal.inverse
                conjugatorValue.actionRotation) leftRotation)
            conjugatorValue.actionRotation =
          TernaryForm.SpecialOrthogonal.mul
            (TernaryForm.SpecialOrthogonal.mul
              (TernaryForm.SpecialOrthogonal.inverse
                conjugatorValue.actionRotation) leftNormal.actionRotation)
            conjugatorValue.actionRotation := by
        rw [leftRotationEq]
      _ = TernaryForm.SpecialOrthogonal.mul
          (TernaryForm.SpecialOrthogonal.mul
            conjugatorValue.conjugate.actionRotation
            leftNormal.actionRotation) conjugatorValue.actionRotation := by
        rw [TernaryForm.NonNullEvenClifford.actionRotation_conjugate]
      _ = (TernaryForm.NonNullEvenClifford.mul
          (TernaryForm.NonNullEvenClifford.mul
            conjugatorValue.conjugate leftNormal)
          conjugatorValue).actionRotation := by
        rw [TernaryForm.NonNullEvenClifford.actionRotation_mul,
          TernaryForm.NonNullEvenClifford.actionRotation_mul]
      _ = rightNormal.actionRotation :=
        (TernaryForm.NonNullEvenClifford.actionRotation_respects_equivalent
          equivalent).symm
      _ = rightRotation := rightRotationEq.symm
  exact
    { matrix := data.matrix
      determinantNonzero := data.determinant_nonzero
      conjugatorValue := conjugatorValue
      conjugatorMatrix := toMatrix_nonNullFromMatrix oneNonzero twoNonzero
        data.matrix data.determinant_nonzero
      conjugator := conjugatorValue.actionRotation
      conjugator_eq := rfl
      conjugates := conjugates }

/-- Paper-facing existence statement extracted from the executable witness:
any two classified nonidentity rational parabolics are conjugate inside the
displayed split special-orthogonal group. -/
theorem parabolics_pairwise_conjugate [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (leftRotation rightRotation :
      (TernaryForm.minkowski oneNonzero).SpecialOrthogonal)
    (leftClassification :
      ParabolicClassification oneNonzero twoNonzero leftRotation)
    (rightClassification :
      ParabolicClassification oneNonzero twoNonzero rightRotation) :
    ∃ conjugator :
        (TernaryForm.minkowski oneNonzero).SpecialOrthogonal,
      TernaryForm.SpecialOrthogonal.mul
          (TernaryForm.SpecialOrthogonal.mul
            (TernaryForm.SpecialOrthogonal.inverse conjugator) leftRotation)
          conjugator = rightRotation := by
  let witness := parabolicConjugacyWitness oneNonzero twoNonzero leftRotation
    rightRotation leftClassification rightClassification
  exact ⟨witness.conjugator, witness.conjugates⟩

end ParabolicConjugacy

end MinkowskiClifford

end RationalRotations
