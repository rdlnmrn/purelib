import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import CCL.Transcendental.Laws

/-!
# Low-to-high finite polynomials for transcendental identities

This is a deliberately small, executable polynomial kernel.  A polynomial is
only a displayed finite list of rational coefficients, stored from constant
term upward.  It exists to prove finite Taylor identities without importing a
sparse-polynomial or formal-power-series API.
-/

namespace CCL.FinitePolynomial

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Approximation :=
  CCL.ProgressiveApproximation.Approximation
abbrev Equivalent := CCL.OperationalEquivalence.Equivalent

open RFAP.ConstructiveGaussian.Gaussian

structure Polynomial where
  coefficients : List Coordinate
deriving DecidableEq

def zero : Polynomial := ⟨[]⟩
def one : Polynomial := ⟨[1]⟩
def indeterminate : Polynomial := ⟨[0, 1]⟩
def constant (value : Coordinate) : Polynomial := ⟨[value]⟩

def addCoefficients : List Coordinate → List Coordinate → List Coordinate
  | [], right => right
  | left, [] => left
  | left :: leftTail, right :: rightTail =>
      (left + right) :: addCoefficients leftTail rightTail

theorem addCoefficients_nil_right : ∀ coefficients,
    addCoefficients coefficients [] = coefficients
  | [] => rfl
  | _ :: _ => rfl

def add (left right : Polynomial) : Polynomial :=
  ⟨addCoefficients left.coefficients right.coefficients⟩

def scale (factor : Coordinate) (polynomial : Polynomial) : Polynomial :=
  ⟨polynomial.coefficients.map (factor * ·)⟩

def shift (count : Nat) (polynomial : Polynomial) : Polynomial :=
  ⟨List.replicate count 0 ++ polynomial.coefficients⟩

def mulCoefficients : List Coordinate → List Coordinate → List Coordinate
  | [], _ => []
  | left :: leftTail, right =>
      addCoefficients (right.map (left * ·))
        (0 :: mulCoefficients leftTail right)

def mul (left right : Polynomial) : Polynomial :=
  ⟨mulCoefficients left.coefficients right.coefficients⟩

def pow : Polynomial → Nat → Polynomial
  | _, 0 => one
  | polynomial, exponent + 1 => mul (pow polynomial exponent) polynomial

def truncate (count : Nat) (polynomial : Polynomial) : Polynomial :=
  ⟨polynomial.coefficients.take count⟩

def coefficientCoefficients : List Coordinate → Nat → Coordinate
  | [], _ => 0
  | coefficient :: _, 0 => coefficient
  | _ :: remaining, degree + 1 =>
      coefficientCoefficients remaining degree

def coefficient (polynomial : Polynomial) (degree : Nat) : Coordinate :=
  coefficientCoefficients polynomial.coefficients degree

@[simp] theorem coefficientCoefficients_nil (degree : Nat) :
    coefficientCoefficients [] degree = 0 := by cases degree <;> rfl

@[simp] theorem coefficientCoefficients_cons_zero
    (head : Coordinate) (tail : List Coordinate) :
    coefficientCoefficients (head :: tail) 0 = head := rfl

@[simp] theorem coefficientCoefficients_cons_succ
    (head : Coordinate) (tail : List Coordinate) (degree : Nat) :
    coefficientCoefficients (head :: tail) (degree + 1) =
      coefficientCoefficients tail degree := rfl

theorem coefficientCoefficients_add : ∀ left right degree,
    coefficientCoefficients (addCoefficients left right) degree =
      coefficientCoefficients left degree +
        coefficientCoefficients right degree
  | [], [], degree => by
      simp only [addCoefficients, coefficientCoefficients]
      exact (RFAP.ConstructiveFraction.zero_add _).symm
  | [], _ :: _, degree => by
      rw [addCoefficients]
      exact (RFAP.ConstructiveFraction.zero_add _).symm
  | _ :: _, [], degree => by
      rw [addCoefficients_nil_right]
      rw [coefficientCoefficients_nil]
      ring1
  | left :: leftTail, right :: rightTail, 0 => rfl
  | left :: leftTail, right :: rightTail, degree + 1 => by
      exact coefficientCoefficients_add leftTail rightTail degree

@[simp] theorem coefficient_add (left right : Polynomial) (degree : Nat) :
    coefficient (add left right) degree =
      coefficient left degree + coefficient right degree :=
  coefficientCoefficients_add left.coefficients right.coefficients degree

theorem coefficientCoefficients_map_scale (factor : Coordinate) :
    ∀ coefficients degree,
      coefficientCoefficients (coefficients.map (factor * ·)) degree =
        factor * coefficientCoefficients coefficients degree
  | [], degree => by
      simp only [List.map, coefficientCoefficients,
        RFAP.ConstructiveFraction.mul_zero_direct]
  | coefficient :: remaining, 0 => rfl
  | coefficient :: remaining, degree + 1 =>
      coefficientCoefficients_map_scale factor remaining degree

@[simp] theorem coefficient_scale (factor : Coordinate)
    (polynomial : Polynomial) (degree : Nat) :
    coefficient (scale factor polynomial) degree =
      factor * coefficient polynomial degree :=
  coefficientCoefficients_map_scale factor polynomial.coefficients degree

theorem coefficientCoefficients_replicate_zero_append :
    ∀ count coefficients degree,
      coefficientCoefficients (List.replicate count 0 ++ coefficients)
          (count + degree) =
        coefficientCoefficients coefficients degree
  | 0, coefficients, degree => by
      simp only [List.replicate_zero, List.nil_append, Nat.zero_add]
  | count + 1, coefficients, degree => by
      rw [show count + 1 + degree = count + degree + 1 by
        calc
          count + 1 + degree = count + (1 + degree) :=
            Nat.add_assoc count 1 degree
          _ = count + (degree + 1) :=
            congrArg (count + ·) (Nat.add_comm 1 degree)
          _ = count + degree + 1 :=
            (Nat.add_assoc count degree 1).symm,
        List.replicate_succ, List.cons_append,
        coefficientCoefficients_cons_succ,
        coefficientCoefficients_replicate_zero_append count coefficients degree]

theorem coefficientCoefficients_replicate_zero_append_below :
    ∀ count coefficients degree, degree < count →
      coefficientCoefficients (List.replicate count 0 ++ coefficients) degree = 0
  | 0, coefficients, degree, order => (Nat.not_lt_zero degree order).elim
  | count + 1, coefficients, 0, order => rfl
  | count + 1, coefficients, degree + 1, order => by
      rw [List.replicate_succ, List.cons_append,
        coefficientCoefficients_cons_succ]
      exact coefficientCoefficients_replicate_zero_append_below
        count coefficients degree (by omega)

theorem coefficientCoefficients_mul_zero : ∀ left right,
    coefficientCoefficients (mulCoefficients left right) 0 =
      coefficientCoefficients left 0 * coefficientCoefficients right 0
  | [], right => by
      simp only [mulCoefficients, coefficientCoefficients,
        RFAP.ConstructiveFraction.zero_mul_direct]
  | left :: leftTail, [] => by
      simp only [mulCoefficients, List.map, addCoefficients,
        coefficientCoefficients, RFAP.ConstructiveFraction.mul_zero_direct]
  | left :: leftTail, right :: rightTail => by
      simp only [mulCoefficients, List.map, addCoefficients,
        coefficientCoefficients]
      ring1

theorem coefficientCoefficients_mul_cons_succ
    (left : Coordinate) (leftTail right : List Coordinate) (degree : Nat) :
    coefficientCoefficients
        (mulCoefficients (left :: leftTail) right) (degree + 1) =
      coefficientCoefficients (right.map (left * ·)) (degree + 1) +
        coefficientCoefficients (mulCoefficients leftTail right) degree := by
  rw [mulCoefficients, coefficientCoefficients_add]
  rfl

def derivativeFrom : Nat → List Coordinate → List Coordinate
  | _, [] => []
  | factor, coefficient :: remaining =>
      (factor : Coordinate) * coefficient ::
        derivativeFrom (factor + 1) remaining

def derivative (polynomial : Polynomial) : Polynomial :=
  match polynomial.coefficients with
  | [] => zero
  | _ :: remaining => ⟨derivativeFrom 1 remaining⟩

theorem coefficientCoefficients_derivativeFrom :
    ∀ factor coefficients degree,
      coefficientCoefficients (derivativeFrom factor coefficients) degree =
        ((factor + degree : Nat) : Coordinate) *
          coefficientCoefficients coefficients degree
  | factor, [], degree => by
      simp only [derivativeFrom, coefficientCoefficients,
        RFAP.ConstructiveFraction.mul_zero_direct]
  | factor, coefficient :: remaining, 0 => by
      simp only [derivativeFrom, coefficientCoefficients, Nat.add_zero]
  | factor, coefficient :: remaining, degree + 1 => by
      rw [derivativeFrom, coefficientCoefficients_cons_succ,
        coefficientCoefficients_derivativeFrom]
      congr 1
      congr 1
      calc
        factor + 1 + degree = factor + (1 + degree) :=
          Nat.add_assoc factor 1 degree
        _ = factor + (degree + 1) :=
          congrArg (factor + ·) (Nat.add_comm 1 degree)

theorem coefficient_derivative (polynomial : Polynomial) (degree : Nat) :
    coefficient (derivative polynomial) degree =
      ((degree + 1 : Nat) : Coordinate) * coefficient polynomial (degree + 1) := by
  cases coefficients : polynomial.coefficients with
  | nil =>
      simp only [derivative, coefficients, coefficient, zero,
        coefficientCoefficients, RFAP.ConstructiveFraction.mul_zero_direct]
  | cons head tail =>
      unfold coefficient
      rw [derivative, coefficients,
        coefficientCoefficients_derivativeFrom]
      rw [coefficientCoefficients_cons_succ]
      rw [Nat.add_comm 1 degree]

theorem derivativeFrom_succ_eq_add : ∀ (factor : Nat)
    (coefficients : List Coordinate),
    derivativeFrom (factor + 1) coefficients =
      addCoefficients (derivativeFrom factor coefficients) coefficients
  | factor, [] => rfl
  | factor, coefficient :: remaining => by
      rw [derivativeFrom, derivativeFrom, addCoefficients,
        derivativeFrom_succ_eq_add (factor + 1) remaining]
      congr 1
      rw [Nat.cast_add]
      ring1

def coordinateSum (term : Nat → Coordinate) : Nat → Coordinate
  | 0 => 0
  | count + 1 => coordinateSum term count + term count

@[simp] theorem coordinateSum_zero (term : Nat → Coordinate) :
    coordinateSum term 0 = 0 := rfl

@[simp] theorem coordinateSum_succ (term : Nat → Coordinate) (count : Nat) :
    coordinateSum term (count + 1) =
      coordinateSum term count + term count := rfl

theorem coordinateSum_succ_front (term : Nat → Coordinate) : ∀ count,
    coordinateSum term (count + 1) =
      term 0 + coordinateSum (fun index => term (index + 1)) count
  | 0 => by
      simp only [coordinateSum_succ, coordinateSum_zero]
      ring1
  | count + 1 => by
      calc
        coordinateSum term (count + 1 + 1) =
            coordinateSum term (count + 1) + term (count + 1) := rfl
        _ = (term 0 +
              coordinateSum (fun index => term (index + 1)) count) +
            term (count + 1) := by rw [coordinateSum_succ_front term count]
        _ = term 0 +
            coordinateSum (fun index => term (index + 1)) (count + 1) := by
          rw [coordinateSum_succ]
          ring1

theorem coordinateSum_congr {left right : Nat → Coordinate}
    (equal : ∀ index, left index = right index) : ∀ count,
    coordinateSum left count = coordinateSum right count
  | 0 => rfl
  | count + 1 => by
      rw [coordinateSum_succ, coordinateSum_succ,
        coordinateSum_congr equal count, equal count]

theorem coordinateSum_congr_lt {left right : Nat → Coordinate} : ∀ count,
    (∀ index, index < count → left index = right index) →
      coordinateSum left count = coordinateSum right count
  | 0, equal => rfl
  | count + 1, equal => by
      rw [coordinateSum_succ, coordinateSum_succ,
        coordinateSum_congr_lt count
          (fun index order => equal index (Nat.lt_succ_of_lt order)),
        equal count (Nat.lt_succ_self count)]

theorem coordinateSum_reverse (term : Nat → Coordinate) : ∀ count,
    coordinateSum term count =
      coordinateSum (fun index => term (count - 1 - index)) count
  | 0 => rfl
  | count + 1 => by
      rw [coordinateSum_succ, coordinateSum_succ_front]
      change
        coordinateSum term count + term count =
          term count +
            coordinateSum
              (fun index => term (count - index.succ)) count
      have tails :
          coordinateSum (fun index => term (count - index.succ)) count =
            coordinateSum (fun index => term (count - 1 - index)) count := by
        apply coordinateSum_congr_lt
        intro index order
        rw [show count - index.succ = count - 1 - index by
          calc
            count - index.succ = count - (index + 1) := rfl
            _ = count - (1 + index) :=
              congrArg (count - ·) (Nat.add_comm index 1)
            _ = count - 1 - index := (Nat.sub_sub count 1 index).symm]
      rw [tails, ← coordinateSum_reverse term count]
      ring1

theorem coordinateSum_add (left right : Nat → Coordinate) : ∀ count,
    coordinateSum (fun index => left index + right index) count =
      coordinateSum left count + coordinateSum right count
  | 0 => by
      simp only [coordinateSum_zero]
      ring1
  | count + 1 => by
      rw [coordinateSum_succ, coordinateSum_succ, coordinateSum_succ,
        coordinateSum_add left right count]
      ring1

theorem coordinateSum_scale_left (factor : Coordinate)
    (term : Nat → Coordinate) : ∀ count,
    factor * coordinateSum term count =
      coordinateSum (fun index => factor * term index) count
  | 0 => by
      simp only [coordinateSum_zero,
        RFAP.ConstructiveFraction.mul_zero_direct]
  | count + 1 => by
      rw [coordinateSum_succ, coordinateSum_succ,
        ← coordinateSum_scale_left factor term count]
      ring1

theorem convolution_derivative_identity
    (left right : Nat → Coordinate) (degree : Nat) :
    ((degree + 1 : Nat) : Coordinate) *
        coordinateSum
          (fun leftDegree =>
            left leftDegree * right (degree + 1 - leftDegree))
          (degree + 2) =
      coordinateSum
          (fun index =>
            ((index + 1 : Nat) : Coordinate) * left (index + 1) *
              right (degree - index))
          (degree + 1) +
        coordinateSum
          (fun index =>
            left index * ((degree - index + 1 : Nat) : Coordinate) *
              right (degree - index + 1))
          (degree + 1) := by
  let full : Nat → Coordinate := fun index =>
    left index * right (degree + 1 - index)
  let leftWeighted : Nat → Coordinate := fun index =>
    (index : Coordinate) * full index
  let rightWeighted : Nat → Coordinate := fun index =>
    ((degree + 1 - index : Nat) : Coordinate) * full index
  have leftExpanded :
      coordinateSum leftWeighted (degree + 2) =
        coordinateSum
          (fun index =>
            ((index + 1 : Nat) : Coordinate) * left (index + 1) *
              right (degree - index))
          (degree + 1) := by
    rw [coordinateSum_succ_front]
    have headZero : leftWeighted 0 = 0 := by
      dsimp only [leftWeighted, full]
      rw [Nat.cast_zero, RFAP.ConstructiveFraction.zero_mul_direct]
    rw [headZero, RFAP.ConstructiveFraction.zero_add]
    apply coordinateSum_congr
    intro index
    dsimp only [leftWeighted, full]
    rw [Nat.succ_sub_succ]
    ring1
  have rightExpanded :
      coordinateSum rightWeighted (degree + 2) =
        coordinateSum
          (fun index =>
            left index * ((degree - index + 1 : Nat) : Coordinate) *
              right (degree - index + 1))
          (degree + 1) := by
    rw [coordinateSum_succ]
    have finalZero : rightWeighted (degree + 1) = 0 := by
      dsimp only [rightWeighted, full]
      rw [Nat.sub_self, Nat.cast_zero,
        RFAP.ConstructiveFraction.zero_mul_direct]
    rw [finalZero, RFAP.ConstructiveFraction.add_comm,
      RFAP.ConstructiveFraction.zero_add]
    apply coordinateSum_congr_lt
    intro index order
    dsimp only [rightWeighted, full]
    rw [Nat.succ_sub (Nat.le_of_lt_succ order)]
    ring1
  rw [← leftExpanded, ← rightExpanded, ← coordinateSum_add,
    coordinateSum_scale_left]
  apply coordinateSum_congr_lt
  intro index order
  dsimp only [leftWeighted, rightWeighted, full]
  have indexLe : index ≤ degree + 1 := Nat.le_of_lt_succ order
  have castSplit :
      (index : Coordinate) + ((degree + 1 - index : Nat) : Coordinate) =
        ((degree + 1 : Nat) : Coordinate) := by
    rw [← Nat.cast_add, Nat.add_sub_cancel' indexLe]
  rw [← castSplit]
  ring1

theorem coefficientCoefficients_mul (left right : List Coordinate) :
    ∀ degree,
      coefficientCoefficients (mulCoefficients left right) degree =
        coordinateSum
          (fun leftDegree =>
            coefficientCoefficients left leftDegree *
              coefficientCoefficients right (degree - leftDegree))
          (degree + 1) := by
  induction left with
  | nil =>
      intro degree
      rw [mulCoefficients]
      change 0 = coordinateSum
        (fun leftDegree =>
          coefficientCoefficients ([] : List Coordinate) leftDegree *
            coefficientCoefficients right (degree - leftDegree))
        (degree + 1)
      have allZero : ∀ count,
          coordinateSum
              (fun leftDegree =>
                coefficientCoefficients ([] : List Coordinate) leftDegree *
                  coefficientCoefficients right (degree - leftDegree)) count =
            0 := by
        intro count
        induction count with
        | zero => rfl
        | succ count inductionHypothesis =>
            rw [coordinateSum_succ, inductionHypothesis,
              coefficientCoefficients_nil,
              RFAP.ConstructiveFraction.zero_mul_direct,
              RFAP.ConstructiveFraction.zero_add]
      exact (allZero (degree + 1)).symm
  | cons head tail inductionHypothesis =>
      intro degree
      cases degree with
      | zero =>
          rw [coefficientCoefficients_mul_zero,
            coordinateSum_succ, coordinateSum_zero]
          simp only [Nat.zero_sub, coefficientCoefficients_cons_zero]
          ring1
      | succ degree =>
          rw [coefficientCoefficients_mul_cons_succ,
            coordinateSum_succ_front]
          simp only [coefficientCoefficients_cons_zero, Nat.sub_zero]
          rw [coefficientCoefficients_map_scale]
          rw [inductionHypothesis degree]
          apply congrArg
            (head * coefficientCoefficients right (degree + 1) + ·)
          apply coordinateSum_congr
          intro index
          rw [coefficientCoefficients_cons_succ,
            Nat.succ_sub_succ_eq_sub]

@[simp] theorem coefficient_mul (left right : Polynomial) (degree : Nat) :
    coefficient (mul left right) degree =
      coordinateSum
        (fun leftDegree =>
          coefficient left leftDegree * coefficient right (degree - leftDegree))
        (degree + 1) :=
  coefficientCoefficients_mul left.coefficients right.coefficients degree

/-- Equality of every displayed finite coefficient.  This is a proposition
about two finite lists and does not identify polynomials by evaluating them on
an infinite collection of points. -/
def CoefficientwiseEqual (left right : Polynomial) : Prop :=
  ∀ degree, coefficient left degree = coefficient right degree

theorem coefficientwise_refl (polynomial : Polynomial) :
    CoefficientwiseEqual polynomial polynomial := fun _ => rfl

theorem coefficientwise_symm {left right : Polynomial}
    (equal : CoefficientwiseEqual left right) :
    CoefficientwiseEqual right left := fun degree => (equal degree).symm

theorem coefficientwise_trans {first second third : Polynomial}
    (firstSecond : CoefficientwiseEqual first second)
    (secondThird : CoefficientwiseEqual second third) :
    CoefficientwiseEqual first third :=
  fun degree => (firstSecond degree).trans (secondThird degree)

theorem coefficient_derivative_mul (left right : Polynomial) (degree : Nat) :
    coefficient (derivative (mul left right)) degree =
      coefficient
        (add (mul (derivative left) right)
          (mul left (derivative right))) degree := by
  rw [coefficient_derivative, coefficient_mul, coefficient_add,
    coefficient_mul, coefficient_mul]
  rw [convolution_derivative_identity
    (fun index => coefficient left index)
    (fun index => coefficient right index) degree]
  apply congrArg₂ (· + ·)
  · apply coordinateSum_congr
    intro index
    rw [coefficient_derivative]
  · apply coordinateSum_congr
    intro index
    rw [coefficient_derivative]
    ring1

theorem derivative_mul (left right : Polynomial) :
    CoefficientwiseEqual (derivative (mul left right))
      (add (mul (derivative left) right)
        (mul left (derivative right))) :=
  coefficient_derivative_mul left right

@[simp] theorem coefficient_zero (degree : Nat) :
    coefficient zero degree = 0 := by
  cases degree <;> rfl

@[simp] theorem coefficient_constant (value : Coordinate) : ∀ degree,
    coefficient (constant value) degree = if degree = 0 then value else 0
  | 0 => rfl
  | _ + 1 => rfl

theorem coefficientwise_add {left left' right right' : Polynomial}
    (leftEqual : CoefficientwiseEqual left left')
    (rightEqual : CoefficientwiseEqual right right') :
    CoefficientwiseEqual (add left right) (add left' right') := by
  intro degree
  rw [coefficient_add, coefficient_add, leftEqual degree, rightEqual degree]

theorem coefficientwise_scale (factor : Coordinate)
    {left right : Polynomial} (equal : CoefficientwiseEqual left right) :
    CoefficientwiseEqual (scale factor left) (scale factor right) := by
  intro degree
  rw [coefficient_scale, coefficient_scale, equal degree]

theorem coefficientwise_mul {left left' right right' : Polynomial}
    (leftEqual : CoefficientwiseEqual left left')
    (rightEqual : CoefficientwiseEqual right right') :
    CoefficientwiseEqual (mul left right) (mul left' right') := by
  intro degree
  rw [coefficient_mul, coefficient_mul]
  apply coordinateSum_congr
  intro index
  rw [leftEqual index, rightEqual (degree - index)]

theorem coefficientwise_mul_comm (left right : Polynomial) :
    CoefficientwiseEqual (mul left right) (mul right left) := by
  intro degree
  rw [coefficient_mul, coefficient_mul,
    coordinateSum_reverse
      (fun index => coefficient left index *
        coefficient right (degree - index)) (degree + 1)]
  apply coordinateSum_congr_lt
  intro index order
  have indexLe : index ≤ degree := Nat.le_of_lt_succ order
  rw [Nat.add_sub_cancel, Nat.sub_sub_self indexLe]
  ring1

theorem coefficientwise_derivative {left right : Polynomial}
    (equal : CoefficientwiseEqual left right) :
    CoefficientwiseEqual (derivative left) (derivative right) := by
  intro degree
  rw [coefficient_derivative, coefficient_derivative,
    equal (degree + 1)]

theorem derivative_zero : CoefficientwiseEqual (derivative zero) zero := by
  intro degree
  rw [coefficient_derivative, coefficient_zero, coefficient_zero,
    RFAP.ConstructiveFraction.mul_zero_direct]

theorem derivative_constant (value : Coordinate) :
    CoefficientwiseEqual (derivative (constant value)) zero := by
  intro degree
  rw [coefficient_derivative, coefficient_zero, coefficient_constant]
  rw [if_neg (Nat.succ_ne_zero degree),
    RFAP.ConstructiveFraction.mul_zero_direct]

theorem derivative_add (left right : Polynomial) :
    CoefficientwiseEqual (derivative (add left right))
      (add (derivative left) (derivative right)) := by
  intro degree
  rw [coefficient_derivative, coefficient_add, coefficient_add,
    coefficient_derivative, coefficient_derivative]
  ring1

theorem derivative_scale (factor : Coordinate) (polynomial : Polynomial) :
    CoefficientwiseEqual (derivative (scale factor polynomial))
      (scale factor (derivative polynomial)) := by
  intro degree
  rw [coefficient_derivative, coefficient_scale, coefficient_scale,
    coefficient_derivative]
  ring1

theorem coordinateSum_all_zero (term : Nat → Coordinate)
    (allZero : ∀ index, term index = 0) : ∀ count,
    coordinateSum term count = 0
  | 0 => rfl
  | count + 1 => by
      rw [coordinateSum_succ, coordinateSum_all_zero term allZero count,
        allZero count, RFAP.ConstructiveFraction.zero_add]

theorem coordinateSum_single (value : Coordinate) : ∀ position count,
    position < count →
      coordinateSum (fun index => if index = position then value else 0)
          count = value
  | position, 0, order => (Nat.not_lt_zero position order).elim
  | position, count + 1, order => by
      rw [coordinateSum_succ]
      by_cases final : position = count
      · subst position
        have prefixZero :
            coordinateSum
                (fun index => if index = count then value else 0) count = 0 := by
          rw [coordinateSum_congr_lt count (by
            intro index order
            rw [if_neg (Nat.ne_of_lt order)])]
          exact coordinateSum_all_zero (fun _ => (0 : Coordinate))
            (fun _ => rfl) count
        rw [if_pos rfl, prefixZero,
          RFAP.ConstructiveFraction.zero_add]
      · have earlier : position < count :=
          Nat.lt_of_le_of_ne (Nat.le_of_lt_succ order) final
        rw [if_neg (Ne.symm final),
          coordinateSum_single value position count earlier]
        ring1

@[simp] theorem coefficient_shift_one_zero (polynomial : Polynomial) :
    coefficient (shift 1 polynomial) 0 = 0 := rfl

@[simp] theorem coefficient_shift_one_succ (polynomial : Polynomial)
    (degree : Nat) :
    coefficient (shift 1 polynomial) (degree + 1) =
      coefficient polynomial degree := rfl

theorem coefficientwise_cons_decompose (head : Coordinate)
    (tail : List Coordinate) :
    CoefficientwiseEqual ⟨head :: tail⟩
      (add (constant head) (shift 1 ⟨tail⟩)) := by
  intro degree
  cases degree with
  | zero =>
      change head = _
      rw [coefficient_add, coefficient_constant,
        coefficient_shift_one_zero]
      simp only [if_pos]
      ring1
  | succ degree =>
      change coefficient ⟨tail⟩ degree = _
      rw [coefficient_add, coefficient_constant,
        if_neg (Nat.succ_ne_zero degree), coefficient_shift_one_succ,
        RFAP.ConstructiveFraction.zero_add]

theorem coefficientwise_constant_mul (factor : Coordinate)
    (polynomial : Polynomial) :
    CoefficientwiseEqual (mul (constant factor) polynomial)
      (scale factor polynomial) := by
  intro degree
  rw [coefficient_mul, coefficient_scale, coordinateSum_succ_front]
  change
    factor * coefficient polynomial degree +
        coordinateSum
          (fun index =>
            coefficient (constant factor) (index + 1) *
              coefficient polynomial (degree - (index + 1))) degree =
      factor * coefficient polynomial degree
  rw [coordinateSum_all_zero _ (by
    intro index
    rw [coefficient_constant, if_neg (Nat.succ_ne_zero index),
      RFAP.ConstructiveFraction.zero_mul_direct])]
  ring1

theorem coefficientwise_mul_zero (polynomial : Polynomial) :
    CoefficientwiseEqual (mul polynomial zero) zero := by
  intro degree
  rw [coefficient_mul, coefficient_zero]
  exact coordinateSum_all_zero _ (by
    intro index
    rw [coefficient_zero,
      RFAP.ConstructiveFraction.mul_zero_direct]) (degree + 1)

theorem coefficientwise_scale_mul (factor : Coordinate)
    (left right : Polynomial) :
    CoefficientwiseEqual (mul (scale factor left) right)
      (scale factor (mul left right)) := by
  intro degree
  rw [coefficient_mul, coefficient_scale, coefficient_mul,
    coordinateSum_scale_left]
  apply coordinateSum_congr
  intro index
  rw [coefficient_scale]
  ring1

theorem coefficientwise_scale_one (polynomial : Polynomial) :
    CoefficientwiseEqual (scale 1 polynomial) polynomial := by
  intro degree
  rw [coefficient_scale]
  ring1

theorem coefficientwise_one_mul (polynomial : Polynomial) :
    CoefficientwiseEqual (mul one polynomial) polynomial :=
  coefficientwise_trans
    (coefficientwise_constant_mul 1 polynomial)
    (coefficientwise_scale_one polynomial)

theorem coefficientwise_shift_one_mul (left right : Polynomial) :
    CoefficientwiseEqual (mul (shift 1 left) right)
      (shift 1 (mul left right)) := by
  intro degree
  cases degree with
  | zero =>
      rw [coefficient_mul, coordinateSum_succ, coordinateSum_zero,
        coefficient_shift_one_zero, coefficient_shift_one_zero,
        RFAP.ConstructiveFraction.zero_mul_direct,
        RFAP.ConstructiveFraction.zero_add]
  | succ degree =>
      rw [coefficient_mul, coordinateSum_succ_front,
        coefficient_shift_one_zero,
        RFAP.ConstructiveFraction.zero_mul_direct,
        RFAP.ConstructiveFraction.zero_add,
        coefficient_shift_one_succ, coefficient_mul]
      apply coordinateSum_congr
      intro index
      rw [coefficient_shift_one_succ]
      rw [Nat.succ_sub_succ]

theorem coefficientwise_shift_one {left right : Polynomial}
    (equal : CoefficientwiseEqual left right) :
    CoefficientwiseEqual (shift 1 left) (shift 1 right) := by
  intro degree
  cases degree with
  | zero => rfl
  | succ degree => exact equal degree

theorem coefficientwise_mul_add (left middle right : Polynomial) :
    CoefficientwiseEqual (mul left (add middle right))
      (add (mul left middle) (mul left right)) := by
  intro degree
  rw [coefficient_mul, coefficient_add,
    coefficient_mul, coefficient_mul, ← coordinateSum_add]
  apply coordinateSum_congr
  intro index
  rw [coefficient_add]
  ring1

theorem coefficientwise_add_mul (left middle right : Polynomial) :
    CoefficientwiseEqual (mul (add left middle) right)
      (add (mul left right) (mul middle right)) :=
  coefficientwise_trans
    (coefficientwise_mul_comm (add left middle) right)
    (coefficientwise_trans
      (coefficientwise_mul_add right left middle)
      (coefficientwise_add
        (coefficientwise_mul_comm right left)
        (coefficientwise_mul_comm right middle)))

theorem coefficientwise_zero_add (polynomial : Polynomial) :
    CoefficientwiseEqual (add zero polynomial) polynomial := by
  intro degree
  rw [coefficient_add, coefficient_zero,
    RFAP.ConstructiveFraction.zero_add]

theorem coefficientwise_add_zero (polynomial : Polynomial) :
    CoefficientwiseEqual (add polynomial zero) polynomial := by
  intro degree
  rw [coefficient_add, coefficient_zero]
  ring1

theorem coefficientwise_add_comm (left right : Polynomial) :
    CoefficientwiseEqual (add left right) (add right left) := by
  intro degree
  rw [coefficient_add, coefficient_add]
  ring1

theorem coefficientwise_add_assoc (left middle right : Polynomial) :
    CoefficientwiseEqual (add (add left middle) right)
      (add left (add middle right)) := by
  intro degree
  rw [coefficient_add, coefficient_add, coefficient_add, coefficient_add]
  ring1

theorem coefficientwise_add_rearrange
    (first second third fourth : Polynomial) :
    CoefficientwiseEqual (add (add first second) (add third fourth))
      (add (add first third) (add second fourth)) := by
  intro degree
  repeat' rw [coefficient_add]
  ring1

theorem coefficientwise_constant_add (left right : Coordinate) :
    CoefficientwiseEqual (constant (left + right))
      (add (constant left) (constant right)) := by
  intro degree
  cases degree with
  | zero =>
      rw [coefficient_constant, if_pos rfl, coefficient_add,
        coefficient_constant, if_pos rfl,
        coefficient_constant, if_pos rfl]
  | succ degree =>
      rw [coefficient_constant, if_neg (Nat.succ_ne_zero degree),
        coefficient_add, coefficient_constant,
        if_neg (Nat.succ_ne_zero degree), coefficient_constant,
        if_neg (Nat.succ_ne_zero degree)]
      ring1

theorem coefficientwise_mul_assoc : ∀ (left right third : Polynomial),
    CoefficientwiseEqual (mul (mul left right) third)
      (mul left (mul right third))
  | ⟨[]⟩, right, third => coefficientwise_refl zero
  | ⟨head :: tail⟩, right, third => by
      let tailPolynomial : Polynomial := ⟨tail⟩
      let decomposed := add (constant head) (shift 1 tailPolynomial)
      have decomposition :
          CoefficientwiseEqual ⟨head :: tail⟩ decomposed :=
        coefficientwise_cons_decompose head tail
      have headPart :
          CoefficientwiseEqual
            (mul (mul (constant head) right) third)
            (mul (constant head) (mul right third)) :=
        coefficientwise_trans
          (coefficientwise_mul
            (coefficientwise_constant_mul head right)
            (coefficientwise_refl third))
          (coefficientwise_trans
            (coefficientwise_scale_mul head right third)
            (coefficientwise_symm
              (coefficientwise_constant_mul head (mul right third))))
      have tailPart :
          CoefficientwiseEqual
            (mul (mul (shift 1 tailPolynomial) right) third)
            (mul (shift 1 tailPolynomial) (mul right third)) :=
        coefficientwise_trans
          (coefficientwise_mul
            (coefficientwise_shift_one_mul tailPolynomial right)
            (coefficientwise_refl third))
          (coefficientwise_trans
            (coefficientwise_shift_one_mul (mul tailPolynomial right) third)
            (coefficientwise_trans
              (coefficientwise_shift_one
                (coefficientwise_mul_assoc tailPolynomial right third))
              (coefficientwise_symm
                (coefficientwise_shift_one_mul tailPolynomial
                  (mul right third)))))
      exact coefficientwise_trans
        (coefficientwise_mul
          (coefficientwise_mul decomposition
            (coefficientwise_refl right))
          (coefficientwise_refl third))
        (coefficientwise_trans
          (coefficientwise_mul
            (coefficientwise_add_mul (constant head)
              (shift 1 tailPolynomial) right)
            (coefficientwise_refl third))
          (coefficientwise_trans
            (coefficientwise_add_mul
              (mul (constant head) right)
              (mul (shift 1 tailPolynomial) right) third)
            (coefficientwise_trans
              (coefficientwise_add headPart tailPart)
              (coefficientwise_trans
                (coefficientwise_symm
                  (coefficientwise_add_mul (constant head)
                    (shift 1 tailPolynomial) (mul right third)))
                (coefficientwise_mul
                  (coefficientwise_symm decomposition)
                  (coefficientwise_refl (mul right third)))))))

def evalCoefficients (z : Gaussian) : List Coordinate → Gaussian
  | [] => 0
  | coefficient :: remaining =>
      CCL.FiniteExp.scale coefficient 1 +
        z * evalCoefficients z remaining

def eval (polynomial : Polynomial) (z : Gaussian) : Gaussian :=
  evalCoefficients z polynomial.coefficients

@[simp] theorem evalCoefficients_nil (z : Gaussian) :
    evalCoefficients z [] = 0 := rfl

@[simp] theorem evalCoefficients_cons (z : Gaussian) (head : Coordinate)
    (tail : List Coordinate) :
    evalCoefficients z (head :: tail) =
      CCL.FiniteExp.scale head 1 +
        z * evalCoefficients z tail := rfl

private theorem scale_one_add (left right : Coordinate) :
    CCL.FiniteExp.scale (left + right) (1 : Gaussian) =
      CCL.FiniteExp.scale left 1 +
        CCL.FiniteExp.scale right 1 := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [CCL.FiniteExp.scale_re,
      CCL.FiniteExp.scale_im, add_re, add_im, one_re, one_im] <;>
    ring1

theorem eval_addCoefficients (z : Gaussian) : ∀ left right,
    evalCoefficients z (addCoefficients left right) =
      evalCoefficients z left + evalCoefficients z right
  | [], right => by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [addCoefficients, evalCoefficients, add_re, add_im,
          zero_re, zero_im] <;> ring1
  | left, [] => by
      rw [addCoefficients_nil_right]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [evalCoefficients, add_re, add_im,
          zero_re, zero_im] <;> ring1
  | left :: leftTail, right :: rightTail => by
      rw [addCoefficients, evalCoefficients, evalCoefficients,
        evalCoefficients, scale_one_add,
        eval_addCoefficients z leftTail rightTail]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [add_re, add_im, mul_re, mul_im] <;> ring1

@[simp] theorem eval_add (left right : Polynomial) (z : Gaussian) :
    eval (add left right) z = eval left z + eval right z :=
  eval_addCoefficients z left.coefficients right.coefficients

private theorem evalCoefficients_eq_nil_of_coefficients_eq (z : Gaussian) :
    ∀ (right : List Coordinate),
      (∀ degree,
        coefficientCoefficients [] degree =
          coefficientCoefficients right degree) →
      evalCoefficients z [] = evalCoefficients z right
  | [], _ => rfl
  | right :: rightTail, equal => by
      have headZero : right = 0 := (equal 0).symm
      have tailEqual : ∀ degree,
          coefficientCoefficients [] degree =
            coefficientCoefficients rightTail degree := by
        intro degree
        exact equal (degree + 1)
      subst right
      have tailEval :=
        evalCoefficients_eq_nil_of_coefficients_eq z rightTail tailEqual
      rw [evalCoefficients, evalCoefficients, ← tailEval, evalCoefficients]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [CCL.FiniteExp.scale_re,
          CCL.FiniteExp.scale_im, add_re, add_im, mul_re, mul_im,
          zero_re, zero_im, one_re, one_im] <;> ring1

/-- Equal displayed coefficients give equal finite Horner evaluations.  The
proof follows the two finite coefficient lists directly; in particular, it
does not infer polynomial equality from values across Gaussian rationals. -/
theorem evalCoefficients_eq_of_coefficients_eq (z : Gaussian) :
    ∀ (left right : List Coordinate),
      (∀ degree,
        coefficientCoefficients left degree =
          coefficientCoefficients right degree) →
      evalCoefficients z left = evalCoefficients z right
  | [], right, equal =>
      evalCoefficients_eq_nil_of_coefficients_eq z right equal
  | left :: leftTail, [], equal => by
      have headZero : left = 0 := equal 0
      have tailEqual : ∀ degree,
          coefficientCoefficients leftTail degree =
            coefficientCoefficients [] degree := by
        intro degree
        exact equal (degree + 1)
      subst left
      have tailEval :=
        evalCoefficients_eq_of_coefficients_eq z leftTail [] tailEqual
      rw [evalCoefficients, evalCoefficients, tailEval, evalCoefficients]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [CCL.FiniteExp.scale_re,
          CCL.FiniteExp.scale_im, add_re, add_im, mul_re, mul_im,
          zero_re, zero_im, one_re, one_im] <;> ring1
  | left :: leftTail, right :: rightTail, equal => by
      have headEqual : left = right := equal 0
      have tailEqual : ∀ degree,
          coefficientCoefficients leftTail degree =
            coefficientCoefficients rightTail degree := by
        intro degree
        exact equal (degree + 1)
      rw [evalCoefficients, evalCoefficients, headEqual,
        evalCoefficients_eq_of_coefficients_eq z leftTail rightTail tailEqual]

theorem eval_eq_of_coefficientwise {left right : Polynomial}
    (equal : CoefficientwiseEqual left right) (z : Gaussian) :
    eval left z = eval right z :=
  evalCoefficients_eq_of_coefficients_eq z left.coefficients
    right.coefficients equal

private theorem scale_one_mul (factor coefficient : Coordinate) :
    CCL.FiniteExp.scale (factor * coefficient) (1 : Gaussian) =
      CCL.FiniteExp.scale factor
        (CCL.FiniteExp.scale coefficient 1) := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [CCL.FiniteExp.scale_re,
      CCL.FiniteExp.scale_im, one_re, one_im] <;> ring1

private theorem scale_add (factor : Coordinate) (left right : Gaussian) :
    CCL.FiniteExp.scale factor (left + right) =
      CCL.FiniteExp.scale factor left +
        CCL.FiniteExp.scale factor right := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [CCL.FiniteExp.scale_re,
      CCL.FiniteExp.scale_im, add_re, add_im] <;> ring1

private theorem scale_mul_left (factor : Coordinate)
    (left right : Gaussian) :
    CCL.FiniteExp.scale factor (left * right) =
      CCL.FiniteExp.scale factor left * right := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [CCL.FiniteExp.scale_re,
      CCL.FiniteExp.scale_im, mul_re, mul_im] <;> ring1

theorem evalCoefficients_map_scale (factor : Coordinate) (z : Gaussian) :
    ∀ coefficients,
      evalCoefficients z (coefficients.map (factor * ·)) =
        CCL.FiniteExp.scale factor
          (evalCoefficients z coefficients)
  | [] => by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [List.map, evalCoefficients,
          CCL.FiniteExp.scale_re,
          CCL.FiniteExp.scale_im, zero_re, zero_im] <;> ring1
  | coefficient :: remaining => by
      rw [List.map, evalCoefficients, evalCoefficients,
        scale_one_mul, evalCoefficients_map_scale factor z remaining]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [CCL.FiniteExp.scale_re,
          CCL.FiniteExp.scale_im, add_re, add_im, mul_re, mul_im] <;>
        ring1

@[simp] theorem eval_scale (factor : Coordinate) (polynomial : Polynomial)
    (z : Gaussian) :
    eval (scale factor polynomial) z =
      CCL.FiniteExp.scale factor (eval polynomial z) :=
  evalCoefficients_map_scale factor z polynomial.coefficients

theorem evalCoefficients_replicate_zero_append (z : Gaussian) :
    ∀ count coefficients,
      evalCoefficients z (List.replicate count 0 ++ coefficients) =
        z ^ count * evalCoefficients z coefficients
  | 0, coefficients => by
      simp only [List.replicate_zero, List.nil_append, pow_zero]
      exact (RFAP.ConstructiveGaussian.Gaussian.one_mul _).symm
  | count + 1, coefficients => by
      rw [List.replicate_succ, List.cons_append, evalCoefficients,
        evalCoefficients_replicate_zero_append z count coefficients,
        pow_succ]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [CCL.FiniteExp.scale_re,
          CCL.FiniteExp.scale_im, add_re, add_im, mul_re, mul_im] <;>
        ring1

@[simp] theorem eval_shift (count : Nat) (polynomial : Polynomial)
    (z : Gaussian) :
    eval (shift count polynomial) z = z ^ count * eval polynomial z :=
  evalCoefficients_replicate_zero_append z count polynomial.coefficients

theorem eval_mulCoefficients (z : Gaussian) : ∀ left right,
    evalCoefficients z (mulCoefficients left right) =
      evalCoefficients z left * evalCoefficients z right
  | [], right => by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [mulCoefficients, evalCoefficients, mul_re, mul_im,
          zero_re, zero_im] <;> ring1
  | left :: leftTail, right => by
      rw [mulCoefficients, eval_addCoefficients,
        evalCoefficients_map_scale, evalCoefficients,
        evalCoefficients, eval_mulCoefficients z leftTail right]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [CCL.FiniteExp.scale_re,
          CCL.FiniteExp.scale_im, add_re, add_im, mul_re, mul_im,
          one_re, one_im] <;> ring1

@[simp] theorem eval_mul (left right : Polynomial) (z : Gaussian) :
    eval (mul left right) z = eval left z * eval right z :=
  eval_mulCoefficients z left.coefficients right.coefficients

@[simp] theorem eval_pow (polynomial : Polynomial) (z : Gaussian) :
    ∀ exponent, eval (pow polynomial exponent) z = eval polynomial z ^ exponent
  | 0 => by
      change CCL.FiniteExp.scale 1 1 + z * 0 = _
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [CCL.FiniteExp.scale_re,
          CCL.FiniteExp.scale_im, add_re, add_im, mul_re, mul_im,
          zero_re, zero_im, one_re, one_im, pow_zero] <;> ring1
  | exponent + 1 => by
      rw [pow, eval_mul, eval_pow polynomial z exponent, pow_succ]

def monomial (degree : Nat) (coefficient : Coordinate) : Polynomial :=
  shift degree (constant coefficient)

theorem coefficient_shift (count : Nat) (polynomial : Polynomial)
    (degree : Nat) :
    coefficient (shift count polynomial) degree =
      if degree < count then 0 else coefficient polynomial (degree - count) := by
  by_cases below : degree < count
  · rw [if_pos below]
    exact coefficientCoefficients_replicate_zero_append_below
      count polynomial.coefficients degree below
  · rw [if_neg below]
    have order : count ≤ degree := Nat.le_of_not_gt below
    rw [show degree = count + (degree - count) by
      exact (Nat.add_sub_cancel' order).symm]
    change coefficientCoefficients
        (List.replicate count 0 ++ polynomial.coefficients)
          (count + (degree - count)) =
      coefficientCoefficients polynomial.coefficients
        (count + (degree - count) - count)
    rw [Nat.add_sub_cancel_left]
    exact coefficientCoefficients_replicate_zero_append
      count polynomial.coefficients (degree - count)

@[simp] theorem coefficient_monomial (monomialDegree : Nat)
    (value : Coordinate) (degree : Nat) :
    coefficient (monomial monomialDegree value) degree =
      if degree = monomialDegree then value else 0 := by
  rw [monomial, coefficient_shift]
  by_cases equal : degree = monomialDegree
  · subst degree
    rw [if_neg (Nat.not_lt_of_ge (Nat.le_refl _)), Nat.sub_self,
      coefficient_constant, if_pos rfl, if_pos rfl]
  · by_cases below : degree < monomialDegree
    · rw [if_pos below, if_neg equal]
    · have above : monomialDegree < degree := Nat.lt_of_le_of_ne
          (Nat.le_of_not_gt below) (Ne.symm equal)
      rw [if_neg below, if_neg equal, coefficient_constant,
        if_neg (Nat.ne_of_gt (Nat.sub_pos_of_lt above))]

theorem coefficientwise_monomial_mul (leftDegree rightDegree : Nat)
    (left right : Coordinate) :
    CoefficientwiseEqual
      (mul (monomial leftDegree left) (monomial rightDegree right))
      (monomial (leftDegree + rightDegree) (left * right)) := by
  intro degree
  rw [coefficient_mul, coefficient_monomial]
  by_cases total : degree = leftDegree + rightDegree
  · subst degree
    rw [if_pos rfl]
    have pointwise : ∀ index, index < leftDegree + rightDegree + 1 →
        coefficient (monomial leftDegree left) index *
            coefficient (monomial rightDegree right)
              (leftDegree + rightDegree - index) =
          if index = leftDegree then left * right else 0 := by
      intro index order
      rw [coefficient_monomial, coefficient_monomial]
      by_cases atLeft : index = leftDegree
      · subst index
        rw [if_pos rfl, if_pos (Nat.add_sub_cancel_left leftDegree rightDegree),
          if_pos rfl]
      · rw [if_neg atLeft, if_neg atLeft,
          RFAP.ConstructiveFraction.zero_mul_direct]
    rw [coordinateSum_congr_lt _ pointwise,
      coordinateSum_single (left * right) leftDegree
        (leftDegree + rightDegree + 1)
          (Nat.lt_succ_of_le (Nat.le_add_right leftDegree rightDegree))]
  · rw [if_neg total]
    have pointwise : ∀ index, index < degree + 1 →
        coefficient (monomial leftDegree left) index *
            coefficient (monomial rightDegree right) (degree - index) = 0 := by
      intro index order
      rw [coefficient_monomial, coefficient_monomial]
      by_cases atLeft : index = leftDegree
      · subst index
        have leftLe : leftDegree ≤ degree := Nat.le_of_lt_succ order
        have differentRemainder : degree - leftDegree ≠ rightDegree := by
          intro remainderEqual
          apply total
          calc
            degree = leftDegree + (degree - leftDegree) :=
              (Nat.add_sub_cancel' leftLe).symm
            _ = leftDegree + rightDegree :=
              congrArg (leftDegree + ·) remainderEqual
        rw [if_pos rfl, if_neg differentRemainder,
          RFAP.ConstructiveFraction.mul_zero_direct]
      · rw [if_neg atLeft, RFAP.ConstructiveFraction.zero_mul_direct]
    rw [coordinateSum_congr_lt _ pointwise]
    exact coordinateSum_all_zero (fun _ => (0 : Coordinate))
      (fun _ => rfl) (degree + 1)

theorem coefficient_monomial_mul (monomialDegree : Nat)
    (value : Coordinate) (polynomial : Polynomial) (degree : Nat) :
    coefficient (mul (monomial monomialDegree value) polynomial) degree =
      if degree < monomialDegree then 0
      else value * coefficient polynomial (degree - monomialDegree) := by
  rw [coefficient_mul]
  by_cases below : degree < monomialDegree
  · rw [if_pos below]
    rw [coordinateSum_congr_lt (degree + 1) (by
      intro index inSum
      have different : index ≠ monomialDegree := by
        intro equal
        subst index
        exact (Nat.not_lt_of_ge (Nat.succ_le_of_lt below)) inSum
      rw [coefficient_monomial, if_neg different,
        RFAP.ConstructiveFraction.zero_mul_direct])]
    exact coordinateSum_all_zero (fun _ => (0 : Coordinate))
      (fun _ => rfl) (degree + 1)
  · rw [if_neg below]
    have inSum : monomialDegree < degree + 1 :=
      Nat.lt_succ_of_le (Nat.le_of_not_gt below)
    have pointwise : ∀ index, index < degree + 1 →
        coefficient (monomial monomialDegree value) index *
            coefficient polynomial (degree - index) =
          if index = monomialDegree then
            value * coefficient polynomial (degree - monomialDegree)
          else 0 := by
      intro index indexBound
      rw [coefficient_monomial]
      by_cases equal : index = monomialDegree
      · subst index
        simp only [if_pos]
      · rw [if_neg equal,
          RFAP.ConstructiveFraction.zero_mul_direct, if_neg equal]
    rw [coordinateSum_congr_lt (degree + 1) pointwise]
    exact coordinateSum_single
      (value * coefficient polynomial (degree - monomialDegree))
      monomialDegree (degree + 1) inSum

theorem eval_monomial (degree : Nat) (coefficient : Coordinate)
    (z : Gaussian) :
    eval (monomial degree coefficient) z =
      CCL.FiniteExp.scale coefficient (z ^ degree) := by
  rw [monomial, eval_shift]
  change z ^ degree *
      (CCL.FiniteExp.scale coefficient 1 + z * 0) = _
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [CCL.FiniteExp.scale_re,
      CCL.FiniteExp.scale_im, add_re, add_im, mul_re, mul_im,
      zero_re, zero_im, one_re, one_im] <;> ring1

/-- Finite substitution by low-to-high Horner recursion. -/
def composeCoefficients (outer : List Coordinate) (inner : Polynomial) :
    Polynomial :=
  match outer with
  | [] => zero
  | coefficient :: remaining =>
      add (constant coefficient)
        (mul inner (composeCoefficients remaining inner))

def compose (outer inner : Polynomial) : Polynomial :=
  composeCoefficients outer.coefficients inner

theorem eval_composeCoefficients (inner : Polynomial) (z : Gaussian) :
    ∀ outer,
      eval (composeCoefficients outer inner) z =
        evalCoefficients (eval inner z) outer
  | [] => rfl
  | coefficient :: remaining => by
      rw [composeCoefficients, eval_add, eval_mul,
        eval_composeCoefficients inner z remaining]
      change
        (CCL.FiniteExp.scale coefficient 1 + z * 0) +
            eval inner z * evalCoefficients (eval inner z) remaining =
          CCL.FiniteExp.scale coefficient 1 +
            eval inner z * evalCoefficients (eval inner z) remaining
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [add_re, add_im, mul_re, mul_im, zero_re, zero_im] <;> ring1

@[simp] theorem eval_compose (outer inner : Polynomial) (z : Gaussian) :
    eval (compose outer inner) z = eval outer (eval inner z) :=
  eval_composeCoefficients inner z outer.coefficients

theorem composeCoefficients_add (inner : Polynomial) : ∀ left right,
    CoefficientwiseEqual
      (composeCoefficients (addCoefficients left right) inner)
      (add (composeCoefficients left inner)
        (composeCoefficients right inner))
  | [], right =>
      coefficientwise_symm
        (coefficientwise_zero_add (composeCoefficients right inner))
  | left :: leftTail, [] => by
      rw [addCoefficients_nil_right]
      exact coefficientwise_symm
        (coefficientwise_add_zero
          (composeCoefficients (left :: leftTail) inner))
  | left :: leftTail, right :: rightTail => by
      change CoefficientwiseEqual
        (add (constant (left + right))
          (mul inner
            (composeCoefficients
              (addCoefficients leftTail rightTail) inner)))
        (add
          (add (constant left)
            (mul inner (composeCoefficients leftTail inner)))
          (add (constant right)
            (mul inner (composeCoefficients rightTail inner))))
      exact coefficientwise_trans
        (coefficientwise_add
          (coefficientwise_constant_add left right)
          (coefficientwise_refl _))
        (coefficientwise_trans
          (coefficientwise_add
            (coefficientwise_refl _)
            (coefficientwise_mul (coefficientwise_refl inner)
              (composeCoefficients_add inner leftTail rightTail)))
          (coefficientwise_trans
            (coefficientwise_add
              (coefficientwise_refl _)
              (coefficientwise_mul_add inner
                (composeCoefficients leftTail inner)
                (composeCoefficients rightTail inner)))
            (coefficientwise_add_rearrange
              (constant left) (constant right)
              (mul inner (composeCoefficients leftTail inner))
              (mul inner (composeCoefficients rightTail inner)))))

theorem compose_add (left right inner : Polynomial) :
    CoefficientwiseEqual (compose (add left right) inner)
      (add (compose left inner) (compose right inner)) :=
  composeCoefficients_add inner left.coefficients right.coefficients

theorem composeCoefficients_derivativeFrom_succ (factor : Nat)
    (coefficients : List Coordinate) (inner : Polynomial) :
    CoefficientwiseEqual
      (composeCoefficients (derivativeFrom (factor + 1) coefficients) inner)
      (add
        (composeCoefficients (derivativeFrom factor coefficients) inner)
        (composeCoefficients coefficients inner)) := by
  rw [derivativeFrom_succ_eq_add]
  exact composeCoefficients_add inner _ _

theorem coefficientwise_constant_one_mul (value : Coordinate) :
    CoefficientwiseEqual
      (constant (((1 : Nat) : Coordinate) * value)) (constant value) := by
  intro degree
  cases degree with
  | zero =>
      rw [coefficient_constant, if_pos rfl,
        coefficient_constant, if_pos rfl]
      ring1
  | succ degree =>
      rw [coefficient_constant, if_neg (Nat.succ_ne_zero degree),
        coefficient_constant, if_neg (Nat.succ_ne_zero degree)]

theorem composeDerivativeTail (inner : Polynomial) : ∀ tail,
    CoefficientwiseEqual
      (composeCoefficients (derivativeFrom 1 tail) inner)
      (add (composeCoefficients tail inner)
        (mul inner (compose (derivative ⟨tail⟩) inner)))
  | [] =>
      coefficientwise_trans
        (coefficientwise_symm (coefficientwise_add_zero zero))
        (coefficientwise_add (coefficientwise_refl zero)
          (coefficientwise_symm (coefficientwise_mul_zero inner)))
  | coefficient :: remaining => by
      change CoefficientwiseEqual
        (add (constant (((1 : Nat) : Coordinate) * coefficient))
          (mul inner
            (composeCoefficients (derivativeFrom 2 remaining) inner)))
        (add
          (add (constant coefficient)
            (mul inner (composeCoefficients remaining inner)))
          (mul inner
            (composeCoefficients (derivativeFrom 1 remaining) inner)))
      exact coefficientwise_trans
        (coefficientwise_add
          (coefficientwise_constant_one_mul coefficient)
          (coefficientwise_refl _))
        (coefficientwise_trans
          (coefficientwise_add
            (coefficientwise_refl _)
            (coefficientwise_mul (coefficientwise_refl inner)
              (composeCoefficients_derivativeFrom_succ 1 remaining inner)))
          (coefficientwise_trans
            (coefficientwise_add (coefficientwise_refl _)
              (coefficientwise_mul_add inner
                (composeCoefficients (derivativeFrom 1 remaining) inner)
                (composeCoefficients remaining inner)))
            (coefficientwise_trans
              (coefficientwise_add (coefficientwise_refl _)
                (coefficientwise_add_comm
                  (mul inner
                    (composeCoefficients (derivativeFrom 1 remaining) inner))
                  (mul inner (composeCoefficients remaining inner))))
              (coefficientwise_symm
                (coefficientwise_add_assoc
                  (constant coefficient)
                  (mul inner (composeCoefficients remaining inner))
                  (mul inner
                    (composeCoefficients
                      (derivativeFrom 1 remaining) inner)))))))

theorem derivative_composeCoefficients (inner : Polynomial) : ∀ outer,
    CoefficientwiseEqual
      (derivative (composeCoefficients outer inner))
      (mul (derivative inner)
        (compose (derivative ⟨outer⟩) inner))
  | [] =>
      coefficientwise_trans derivative_zero
        (coefficientwise_symm
          (coefficientwise_mul_zero (derivative inner)))
  | head :: tail => by
      let tailComposition := composeCoefficients tail inner
      let outerDerivativeComposition :=
        composeCoefficients (derivativeFrom 1 tail) inner
      have reordered :
          CoefficientwiseEqual
            (mul inner
              (mul (derivative inner)
                (compose (derivative ⟨tail⟩) inner)))
            (mul (derivative inner)
              (mul inner (compose (derivative ⟨tail⟩) inner))) :=
        coefficientwise_trans
          (coefficientwise_symm
            (coefficientwise_mul_assoc inner (derivative inner)
              (compose (derivative ⟨tail⟩) inner)))
          (coefficientwise_trans
            (coefficientwise_mul
              (coefficientwise_mul_comm inner (derivative inner))
              (coefficientwise_refl _))
            (coefficientwise_mul_assoc (derivative inner) inner
              (compose (derivative ⟨tail⟩) inner)))
      change CoefficientwiseEqual
        (derivative (add (constant head) (mul inner tailComposition)))
        (mul (derivative inner) outerDerivativeComposition)
      exact coefficientwise_trans
        (derivative_add (constant head) (mul inner tailComposition))
        (coefficientwise_trans
          (coefficientwise_add
            (derivative_constant head)
            (derivative_mul inner tailComposition))
          (coefficientwise_trans
            (coefficientwise_zero_add
              (add (mul (derivative inner) tailComposition)
                (mul inner (derivative tailComposition))))
            (coefficientwise_trans
              (coefficientwise_add (coefficientwise_refl _)
                (coefficientwise_trans
                  (coefficientwise_mul (coefficientwise_refl inner)
                    (derivative_composeCoefficients inner tail))
                  reordered))
              (coefficientwise_trans
                (coefficientwise_symm
                  (coefficientwise_mul_add (derivative inner)
                    tailComposition
                    (mul inner (compose (derivative ⟨tail⟩) inner))))
                (coefficientwise_mul (coefficientwise_refl (derivative inner))
                  (coefficientwise_symm
                    (composeDerivativeTail inner tail)))))))

theorem derivative_compose (outer inner : Polynomial) :
    CoefficientwiseEqual (derivative (compose outer inner))
      (mul (derivative inner) (compose (derivative outer) inner)) :=
  derivative_composeCoefficients inner outer.coefficients

theorem coefficientwise_constant_zero :
    CoefficientwiseEqual (constant 0) zero := by
  intro degree
  rw [coefficient_constant, coefficient_zero]
  split <;> rfl

theorem composeCoefficients_zero_cons (coefficients : List Coordinate)
    (inner : Polynomial) :
    CoefficientwiseEqual (composeCoefficients (0 :: coefficients) inner)
      (mul inner (composeCoefficients coefficients inner)) := by
  change CoefficientwiseEqual
    (add (constant 0)
      (mul inner (composeCoefficients coefficients inner)))
    (mul inner (composeCoefficients coefficients inner))
  exact coefficientwise_trans
    (coefficientwise_add coefficientwise_constant_zero
      (coefficientwise_refl _))
    (coefficientwise_zero_add _)

theorem compose_shift (outer inner : Polynomial) : ∀ count,
    CoefficientwiseEqual (compose (shift count outer) inner)
      (mul (pow inner count) (compose outer inner))
  | 0 =>
      coefficientwise_symm (coefficientwise_one_mul (compose outer inner))
  | count + 1 => by
      change CoefficientwiseEqual
        (composeCoefficients
          (0 :: (List.replicate count 0 ++ outer.coefficients)) inner)
        (mul (mul (pow inner count) inner) (compose outer inner))
      exact coefficientwise_trans
        (composeCoefficients_zero_cons _ inner)
        (coefficientwise_trans
          (coefficientwise_mul (coefficientwise_refl inner)
            (compose_shift outer inner count))
          (coefficientwise_trans
            (coefficientwise_symm
              (coefficientwise_mul_assoc inner (pow inner count)
                (compose outer inner)))
            (coefficientwise_mul
              (coefficientwise_mul_comm inner (pow inner count))
              (coefficientwise_refl _))))

theorem compose_monomial (degree : Nat) (value : Coordinate)
    (inner : Polynomial) :
    CoefficientwiseEqual (compose (monomial degree value) inner)
      (scale value (pow inner degree)) := by
  exact coefficientwise_trans
    (compose_shift (constant value) inner degree)
    (coefficientwise_trans
      (coefficientwise_mul (coefficientwise_refl _)
        (coefficientwise_trans
          (coefficientwise_add (coefficientwise_refl _)
            (coefficientwise_mul_zero inner))
          (coefficientwise_add_zero (constant value))))
      (coefficientwise_trans
        (coefficientwise_mul_comm (pow inner degree) (constant value))
        (coefficientwise_constant_mul value (pow inner degree))))

theorem composeCoefficients_zero_of_coefficients_zero (inner : Polynomial) :
    ∀ coefficients,
      (∀ degree, coefficientCoefficients coefficients degree = 0) →
        CoefficientwiseEqual (composeCoefficients coefficients inner) zero
  | [], allZero => coefficientwise_refl zero
  | coefficient :: remaining, allZero => by
      have headZero : coefficient = 0 := allZero 0
      have tailZero :
          ∀ degree, coefficientCoefficients remaining degree = 0 := by
        intro degree
        exact allZero (degree + 1)
      subst coefficient
      exact coefficientwise_trans
        (coefficientwise_add coefficientwise_constant_zero
          (coefficientwise_mul (coefficientwise_refl inner)
            (composeCoefficients_zero_of_coefficients_zero inner remaining
              tailZero)))
        (coefficientwise_trans
          (coefficientwise_add (coefficientwise_refl zero)
            (coefficientwise_mul_zero inner))
          (coefficientwise_zero_add zero))

theorem composeCoefficients_congr (inner : Polynomial) :
    ∀ {left right : List Coordinate},
      CoefficientwiseEqual ⟨left⟩ ⟨right⟩ →
        CoefficientwiseEqual (composeCoefficients left inner)
          (composeCoefficients right inner)
  | [], [], equal => coefficientwise_refl zero
  | [], right :: rightTail, equal => by
      have rightZero :
          ∀ degree,
            coefficientCoefficients (right :: rightTail) degree = 0 := by
        intro degree
        exact (equal degree).symm
      exact coefficientwise_symm
        (composeCoefficients_zero_of_coefficients_zero inner
          (right :: rightTail) rightZero)
  | left :: leftTail, [], equal => by
      have leftZero :
          ∀ degree,
            coefficientCoefficients (left :: leftTail) degree = 0 := by
        intro degree
        exact equal degree
      exact composeCoefficients_zero_of_coefficients_zero inner
        (left :: leftTail) leftZero
  | left :: leftTail, right :: rightTail, equal => by
      have headEqual : left = right := equal 0
      have tailEqual : CoefficientwiseEqual ⟨leftTail⟩ ⟨rightTail⟩ := by
        intro degree
        exact equal (degree + 1)
      have constantEqual :
          CoefficientwiseEqual (constant left) (constant right) := by
        rw [headEqual]
        exact coefficientwise_refl _
      exact coefficientwise_add
        constantEqual
        (coefficientwise_mul (coefficientwise_refl inner)
          (composeCoefficients_congr inner tailEqual))

theorem compose_congr {left right : Polynomial}
    (equal : CoefficientwiseEqual left right) (inner : Polynomial) :
    CoefficientwiseEqual (compose left inner) (compose right inner) :=
  composeCoefficients_congr inner equal

def exponential : Nat → Polynomial
  | 0 => constant 1
  | degree + 1 =>
      add (exponential degree)
        (monomial (degree + 1)
          (1 / (CCL.TranscendentalLaws.factorial
            (degree + 1) : Coordinate)))

theorem coefficientwise_monomial_value (degree : Nat)
    {left right : Coordinate} (equal : left = right) :
    CoefficientwiseEqual (monomial degree left) (monomial degree right) := by
  rw [equal]
  exact coefficientwise_refl _

theorem coefficientwise_monomial_zero (value : Coordinate) :
    CoefficientwiseEqual (monomial 0 value) (constant value) := by
  intro degree
  rw [coefficient_monomial, coefficient_constant]

theorem derivative_monomial_succ (degree : Nat) (value : Coordinate) :
    CoefficientwiseEqual (derivative (monomial (degree + 1) value))
      (monomial degree (((degree + 1 : Nat) : Coordinate) * value)) := by
  intro outputDegree
  rw [coefficient_derivative, coefficient_monomial, coefficient_monomial]
  by_cases equal : outputDegree = degree
  · subst outputDegree
    rw [if_pos rfl, if_pos rfl]
  · rw [if_neg equal, if_neg (Nat.succ_ne_succ_iff.mpr equal),
      RFAP.ConstructiveFraction.mul_zero_direct]

theorem factorialCoefficient_step (degree : Nat) :
    ((degree + 1 : Nat) : Coordinate) *
        (1 / (CCL.TranscendentalLaws.factorial
          (degree + 1) : Coordinate)) =
      1 / (CCL.TranscendentalLaws.factorial degree : Coordinate) := by
  let current : Coordinate :=
    (CCL.TranscendentalLaws.factorial degree : Coordinate)
  let next : Coordinate :=
    (CCL.TranscendentalLaws.factorial (degree + 1) : Coordinate)
  have currentNonzero : current ≠ 0 :=
    (RFAP.ConstructiveFraction.natCast_pos_direct
      (CCL.TranscendentalLaws.factorial_pos degree)).ne'
  have nextNonzero : next ≠ 0 :=
    (RFAP.ConstructiveFraction.natCast_pos_direct
      (CCL.TranscendentalLaws.factorial_pos
        (degree + 1))).ne'
  have cross :
      ((degree + 1 : Nat) : Coordinate) * current = 1 * next := by
    dsimp only [current, next]
    rw [CCL.TranscendentalLaws.factorial_succ, Nat.cast_mul]
    ring1
  calc
    ((degree + 1 : Nat) : Coordinate) * (1 / next) =
        ((degree + 1 : Nat) : Coordinate) / next := by
      change _ * (1 * next⁻¹) = _ * next⁻¹
      rw [RFAP.ConstructiveFraction.one_mul]
    _ = 1 / current :=
      CCL.TranscendentalLaws.coordinate_div_eq_div_of_cross
        _ _ _ _ nextNonzero currentNonzero cross

theorem derivative_exponential_succ : ∀ degree,
    CoefficientwiseEqual (derivative (exponential (degree + 1)))
      (exponential degree)
  | 0 => by
      change CoefficientwiseEqual
        (derivative
          (add (constant 1)
            (monomial 1
              (1 / (CCL.TranscendentalLaws.factorial
                1 : Coordinate)))))
        (constant 1)
      exact coefficientwise_trans
        (derivative_add _ _)
        (coefficientwise_trans
          (coefficientwise_add (derivative_constant 1)
            (derivative_monomial_succ 0 _))
          (coefficientwise_trans
            (coefficientwise_add (coefficientwise_refl zero)
              (coefficientwise_monomial_value 0
                (factorialCoefficient_step 0)))
            (coefficientwise_trans
              (coefficientwise_zero_add
                (monomial 0
                  (1 / (CCL.TranscendentalLaws.factorial
                    0 : Coordinate))))
              (coefficientwise_monomial_zero 1))))
  | degree + 1 => by
      change CoefficientwiseEqual
        (derivative
          (add (exponential (degree + 1))
            (monomial (degree + 2)
              (1 / (CCL.TranscendentalLaws.factorial
                (degree + 2) : Coordinate)))))
        (add (exponential degree)
          (monomial (degree + 1)
            (1 / (CCL.TranscendentalLaws.factorial
              (degree + 1) : Coordinate))))
      exact coefficientwise_trans
        (derivative_add _ _)
        (coefficientwise_trans
          (coefficientwise_add
            (derivative_exponential_succ degree)
            (derivative_monomial_succ (degree + 1) _))
          (coefficientwise_add (coefficientwise_refl _)
            (coefficientwise_monomial_value (degree + 1)
              (factorialCoefficient_step (degree + 1)))))

theorem eval_exponential (z : Gaussian) : ∀ degree,
    eval (exponential degree) z =
      CCL.TranscendentalLaws.truncatedExp z degree
  | 0 => by
      change CCL.FiniteExp.scale 1 1 + z * 0 = 1
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [CCL.FiniteExp.scale_re,
          CCL.FiniteExp.scale_im, add_re, add_im, mul_re, mul_im,
          zero_re, zero_im, one_re, one_im] <;> ring1
  | degree + 1 => by
      rw [exponential, eval_add, eval_exponential z degree, eval_monomial,
        CCL.TranscendentalLaws.truncatedExp_succ,
        CCL.TranscendentalLaws.taylorTerm]

def localLog : Nat → Polynomial
  | 0 => monomial 1 2
  | depth + 1 =>
      add (localLog depth)
        (monomial (2 * (depth + 1) + 1)
          (2 / (2 * ((depth + 1 : Nat) : Coordinate) + 1)))

def evenGeometric : Nat → Polynomial
  | 0 => constant 2
  | depth + 1 =>
      add (evenGeometric depth) (monomial (2 * (depth + 1)) 2)

def oneMinusSquare : Polynomial :=
  add one (monomial 2 (-1))

theorem odd_mul_localLogCoefficient (index : Nat) :
    ((2 * index + 1 : Nat) : Coordinate) *
        (2 / (2 * (index : Coordinate) + 1)) = 2 := by
  have castOdd :
      ((2 * index + 1 : Nat) : Coordinate) =
        2 * (index : Coordinate) + 1 := by
    rw [Nat.cast_add, Nat.cast_mul]
    rw [show ((2 : Nat) : Coordinate) = 2 by decide,
      show ((1 : Nat) : Coordinate) = 1 by decide]
  have denominatorPositive :
      0 < (2 * (index : Coordinate) + 1) := by
    rw [← castOdd]
    exact RFAP.ConstructiveFraction.natCast_pos_direct
      (Nat.zero_lt_succ (2 * index))
  rw [castOdd, RFAP.ConstructiveFraction.mul_comm]
  exact RFAP.ConstructiveFraction.div_mul_cancel_of_ne 2 _
    denominatorPositive.ne'

theorem derivative_localLog : ∀ depth,
    CoefficientwiseEqual (derivative (localLog depth))
      (evenGeometric depth)
  | 0 => by
      change CoefficientwiseEqual (derivative (monomial 1 2)) (constant 2)
      exact coefficientwise_trans
        (derivative_monomial_succ 0 2)
        (coefficientwise_trans
          (coefficientwise_monomial_value 0
            (odd_mul_localLogCoefficient 0))
          (coefficientwise_monomial_zero 2))
  | depth + 1 => by
      change CoefficientwiseEqual
        (derivative
          (add (localLog depth)
            (monomial (2 * (depth + 1) + 1)
              (2 / (2 * ((depth + 1 : Nat) : Coordinate) + 1)))))
        (add (evenGeometric depth) (monomial (2 * (depth + 1)) 2))
      exact coefficientwise_trans
        (derivative_add _ _)
        (coefficientwise_trans
          (coefficientwise_add (derivative_localLog depth)
            (derivative_monomial_succ (2 * (depth + 1)) _))
          (coefficientwise_add (coefficientwise_refl _)
            (coefficientwise_monomial_value (2 * (depth + 1))
              (odd_mul_localLogCoefficient (depth + 1)))))

theorem coefficientwise_monomial_cancel (degree : Nat)
    (value : Coordinate) :
    CoefficientwiseEqual
      (add (monomial degree (-value)) (monomial degree value)) zero := by
  intro outputDegree
  rw [coefficient_add, coefficient_monomial, coefficient_monomial,
    coefficient_zero]
  by_cases equal : outputDegree = degree
  · rw [if_pos equal, if_pos equal]
    ring1
  · rw [if_neg equal, if_neg equal]
    ring1

theorem coefficientwise_telescope_rearrange
    (first cancelledLeft cancelledRight last : Polynomial) :
    CoefficientwiseEqual
      (add (add first cancelledLeft) (add cancelledRight last))
      (add (add first last) (add cancelledLeft cancelledRight)) := by
  intro degree
  repeat' rw [coefficient_add]
  ring1

theorem oneMinusSquare_mul_evenGeometric : ∀ depth,
    CoefficientwiseEqual (mul oneMinusSquare (evenGeometric depth))
      (add (constant 2) (monomial (2 * depth + 2) (-2)))
  | 0 => by
      change CoefficientwiseEqual
        (mul (add one (monomial 2 (-1))) (constant 2))
        (add (constant 2) (monomial 2 (-2)))
      exact coefficientwise_trans
        (coefficientwise_add_mul one (monomial 2 (-1)) (constant 2))
        (coefficientwise_add
          (coefficientwise_one_mul (constant 2))
          (coefficientwise_trans
            (coefficientwise_mul (coefficientwise_refl _)
              (coefficientwise_symm (coefficientwise_monomial_zero 2)))
            (coefficientwise_trans
              (coefficientwise_monomial_mul 2 0 (-1) 2)
              (coefficientwise_monomial_value 2 (by decide)))))
  | depth + 1 => by
      let currentDegree := 2 * (depth + 1)
      let highDegree := currentDegree + 2
      change CoefficientwiseEqual
        (mul oneMinusSquare
          (add (evenGeometric depth) (monomial currentDegree 2)))
        (add (constant 2) (monomial highDegree (-2)))
      have currentProduct :
          CoefficientwiseEqual
            (mul oneMinusSquare (monomial currentDegree 2))
            (add (monomial currentDegree 2)
              (monomial highDegree (-2))) := by
        exact coefficientwise_trans
          (coefficientwise_add_mul one (monomial 2 (-1))
            (monomial currentDegree 2))
          (coefficientwise_add
            (coefficientwise_one_mul (monomial currentDegree 2))
            (coefficientwise_trans
              (coefficientwise_monomial_mul 2 currentDegree (-1) 2)
              (by
                have degreeEqual : 2 + currentDegree = highDegree := by
                  dsimp only [highDegree, currentDegree]
                  exact Nat.add_comm 2 (2 * (depth + 1))
                rw [degreeEqual]
                exact coefficientwise_monomial_value highDegree (by decide))))
      exact coefficientwise_trans
        (coefficientwise_mul_add oneMinusSquare (evenGeometric depth)
          (monomial currentDegree 2))
        (coefficientwise_trans
          (coefficientwise_add
            (oneMinusSquare_mul_evenGeometric depth) currentProduct)
          (coefficientwise_trans
            (coefficientwise_telescope_rearrange
              (constant 2) (monomial currentDegree (-2))
              (monomial currentDegree 2) (monomial highDegree (-2)))
            (coefficientwise_trans
              (coefficientwise_add (coefficientwise_refl _)
                (coefficientwise_monomial_cancel currentDegree 2))
              (coefficientwise_add_zero
                (add (constant 2) (monomial highDegree (-2)))))))

theorem eval_localLog (z : Gaussian) : ∀ depth,
    eval (localLog depth) z =
      CCL.FiniteComplexLog.sample z depth
  | 0 => by
      rw [localLog, eval_monomial,
        CCL.TranscendentalLaws.complexLog_sample_eq_finiteSum,
        CCL.TranscendentalLaws.finiteSum_succ,
        CCL.TranscendentalLaws.finiteSum_zero,
        RFAP.ConstructiveGaussian.Gaussian.zero_add,
        CCL.TranscendentalLaws.localLogTerm]
      change CCL.FiniteExp.scale 2 (z ^ 1) =
        CCL.FiniteExp.scale (2 / (2 * (0 : Coordinate) + 1))
          (z ^ (2 * 0 + 1))
      rw [show (2 / (2 * (0 : Coordinate) + 1) : Coordinate) = 2 by decide]
  | depth + 1 => by
      rw [localLog, eval_add, eval_localLog z depth, eval_monomial,
        CCL.TranscendentalLaws.complexLog_sample_eq_finiteSum,
        CCL.TranscendentalLaws.complexLog_sample_eq_finiteSum,
        CCL.TranscendentalLaws.finiteSum_succ]
      change
        CCL.TranscendentalLaws.finiteSum
              (CCL.TranscendentalLaws.localLogTerm z)
              (depth + 1) +
            CCL.FiniteExp.scale
              (2 / (2 * ((depth + 1 : Nat) : Coordinate) + 1))
              (z ^ (2 * (depth + 1) + 1)) =
          CCL.TranscendentalLaws.finiteSum
              (CCL.TranscendentalLaws.localLogTerm z)
              (depth + 1) +
            CCL.TranscendentalLaws.localLogTerm z (depth + 1)
      rfl

/-- The actual finite program obtained by substituting the displayed local
logarithm polynomial into the displayed exponential polynomial. -/
def exponentialLocalLog (expDegree logDepth : Nat) : Polynomial :=
  compose (exponential expDegree) (localLog logDepth)

theorem eval_exponentialLocalLog (z : Gaussian)
    (expDegree logDepth : Nat) :
    eval (exponentialLocalLog expDegree logDepth) z =
      CCL.TranscendentalLaws.truncatedExp
        (CCL.FiniteComplexLog.sample z logDepth) expDegree := by
  rw [exponentialLocalLog, eval_compose, eval_exponential, eval_localLog]

/-! ## Bounded coefficient identities used by the local inverse law -/

def EqualBelow (count : Nat) (left right : Polynomial) : Prop :=
  ∀ degree, degree < count →
    coefficient left degree = coefficient right degree

def VanishesBelow (count : Nat) (polynomial : Polynomial) : Prop :=
  ∀ degree, degree < count → coefficient polynomial degree = 0

theorem CoefficientwiseEqual.equalBelow {left right : Polynomial}
    (equal : CoefficientwiseEqual left right) (count : Nat) :
    EqualBelow count left right := fun degree _ => equal degree

theorem equalBelow_refl (count : Nat) (polynomial : Polynomial) :
    EqualBelow count polynomial polynomial := fun _ _ => rfl

theorem equalBelow_symm {count : Nat} {left right : Polynomial}
    (equal : EqualBelow count left right) : EqualBelow count right left :=
  fun degree below => (equal degree below).symm

theorem equalBelow_trans {count : Nat} {first second third : Polynomial}
    (firstSecond : EqualBelow count first second)
    (secondThird : EqualBelow count second third) :
    EqualBelow count first third :=
  fun degree below => (firstSecond degree below).trans
    (secondThird degree below)

theorem equalBelow_add {count : Nat}
    {left left' right right' : Polynomial}
    (leftEqual : EqualBelow count left left')
    (rightEqual : EqualBelow count right right') :
    EqualBelow count (add left right) (add left' right') := by
  intro degree below
  rw [coefficient_add, coefficient_add,
    leftEqual degree below, rightEqual degree below]

theorem equalBelow_scale (factor : Coordinate) {count : Nat}
    {left right : Polynomial} (equal : EqualBelow count left right) :
    EqualBelow count (scale factor left) (scale factor right) := by
  intro degree below
  rw [coefficient_scale, coefficient_scale, equal degree below]

theorem equalBelow_mul {count : Nat}
    {left left' right right' : Polynomial}
    (leftEqual : EqualBelow count left left')
    (rightEqual : EqualBelow count right right') :
    EqualBelow count (mul left right) (mul left' right') := by
  intro degree below
  rw [coefficient_mul, coefficient_mul]
  apply coordinateSum_congr_lt
  intro index inSum
  rw [leftEqual index ((Nat.le_of_lt_succ inSum).trans_lt below),
    rightEqual (degree - index) ((Nat.sub_le degree index).trans_lt below)]

theorem vanishesBelow_scale (factor : Coordinate) {count : Nat}
    {polynomial : Polynomial} (vanishes : VanishesBelow count polynomial) :
    VanishesBelow count (scale factor polynomial) := by
  intro degree below
  rw [coefficient_scale, vanishes degree below,
    RFAP.ConstructiveFraction.mul_zero_direct]

theorem vanishesBelow_monomial (count degree : Nat) (order : count ≤ degree)
    (value : Coordinate) : VanishesBelow count (monomial degree value) := by
  intro outputDegree below
  rw [coefficient_monomial,
    if_neg (Nat.ne_of_lt (below.trans_le order))]

theorem vanishesBelow_mul_left {count : Nat} {left : Polynomial}
    (vanishes : VanishesBelow count left) (right : Polynomial) :
    VanishesBelow count (mul left right) := by
  intro degree below
  rw [coefficient_mul]
  rw [coordinateSum_congr_lt (degree + 1) (by
    intro index inSum
    rw [vanishes index
        ((Nat.le_of_lt_succ inSum).trans_lt below),
      RFAP.ConstructiveFraction.zero_mul_direct])]
  exact coordinateSum_all_zero (fun _ => (0 : Coordinate))
    (fun _ => rfl) (degree + 1)

theorem vanishesBelow_add_right {count : Nat} {left right : Polynomial}
    (vanishes : VanishesBelow count right) :
    EqualBelow count (add left right) left := by
  intro degree below
  rw [coefficient_add, vanishes degree below]
  ring1

theorem vanishesBelow_pow_of_zero_constant {polynomial : Polynomial}
    (zeroConstant : coefficient polynomial 0 = 0) : ∀ exponent,
    VanishesBelow exponent (pow polynomial exponent)
  | 0 => fun degree below => (Nat.not_lt_zero degree below).elim
  | exponent + 1 => by
      intro degree below
      rw [pow, coefficient_mul]
      rw [coordinateSum_congr_lt (degree + 1) (by
        intro index inSum
        by_cases before : index < exponent
        · rw [vanishesBelow_pow_of_zero_constant zeroConstant exponent
              index before,
            RFAP.ConstructiveFraction.zero_mul_direct]
        · have degreeLe : degree ≤ exponent := Nat.le_of_lt_succ below
          have indexLe : index ≤ degree := Nat.le_of_lt_succ inSum
          have exponentLe : exponent ≤ index := Nat.le_of_not_gt before
          have indexEqual : index = exponent :=
            Nat.le_antisymm (indexLe.trans degreeLe) exponentLe
          subst index
          have degreeEqual : degree = exponent :=
            Nat.le_antisymm degreeLe indexLe
          subst degree
          rw [Nat.sub_self, zeroConstant,
            RFAP.ConstructiveFraction.mul_zero_direct])]
      exact coordinateSum_all_zero (fun _ => (0 : Coordinate))
        (fun _ => rfl) (degree + 1)

theorem localLog_zero_constant : ∀ depth,
    coefficient (localLog depth) 0 = 0
  | 0 => by
      rw [localLog, coefficient_monomial, if_neg Nat.zero_ne_one]
  | depth + 1 => by
      rw [localLog, coefficient_add, localLog_zero_constant depth,
        coefficient_monomial,
        if_neg (Nat.zero_ne_add_one (2 * (depth + 1))),
        RFAP.ConstructiveFraction.zero_add]

theorem compose_exponential_succ_below (depth : Nat) (inner : Polynomial)
    (zeroConstant : coefficient inner 0 = 0) :
    EqualBelow (depth + 1)
      (compose (exponential (depth + 1)) inner)
      (compose (exponential depth) inner) := by
  change EqualBelow (depth + 1)
    (compose
      (add (exponential depth)
        (monomial (depth + 1)
          (1 / (CCL.TranscendentalLaws.factorial
            (depth + 1) : Coordinate)))) inner)
    (compose (exponential depth) inner)
  exact equalBelow_trans
    ((compose_add _ _ inner).equalBelow (depth + 1))
    (equalBelow_trans
      (equalBelow_add (equalBelow_refl _ _)
        ((compose_monomial (depth + 1) _ inner).equalBelow (depth + 1)))
      (vanishesBelow_add_right
        (vanishesBelow_scale _
          (vanishesBelow_pow_of_zero_constant zeroConstant (depth + 1)))))

theorem exponentialLocalLog_ode_below (depth : Nat) :
    EqualBelow (2 * depth + 2)
      (mul oneMinusSquare
        (derivative (exponentialLocalLog (2 * depth + 2) depth)))
      (scale 2 (exponentialLocalLog (2 * depth + 2) depth)) := by
  let logarithm := localLog depth
  let previousExponential := exponential (2 * depth + 1)
  let composition := exponentialLocalLog (2 * depth + 2) depth
  let previousComposition := compose previousExponential logarithm
  let highTerm := monomial (2 * depth + 2) (-2)
  have derivativeIdentity :
      CoefficientwiseEqual (derivative composition)
        (mul (derivative logarithm) previousComposition) := by
    exact coefficientwise_trans
      (derivative_compose (exponential (2 * depth + 2)) logarithm)
      (coefficientwise_mul (coefficientwise_refl _)
        (compose_congr
          (derivative_exponential_succ (2 * depth + 1)) logarithm))
  have kernelIdentity :
      CoefficientwiseEqual (mul oneMinusSquare (derivative logarithm))
        (add (constant 2) highTerm) := by
    exact coefficientwise_trans
      (coefficientwise_mul (coefficientwise_refl oneMinusSquare)
        (derivative_localLog depth))
      (oneMinusSquare_mul_evenGeometric depth)
  have fullIdentity :
      CoefficientwiseEqual
        (mul oneMinusSquare (derivative composition))
        (mul (add (constant 2) highTerm) previousComposition) := by
    exact coefficientwise_trans
      (coefficientwise_mul (coefficientwise_refl oneMinusSquare)
        derivativeIdentity)
      (coefficientwise_trans
        (coefficientwise_symm
          (coefficientwise_mul_assoc oneMinusSquare
            (derivative logarithm) previousComposition))
        (coefficientwise_mul kernelIdentity (coefficientwise_refl _)))
  have highVanishes :
      VanishesBelow (2 * depth + 2)
        (mul highTerm previousComposition) :=
    vanishesBelow_mul_left
      (vanishesBelow_monomial (2 * depth + 2) (2 * depth + 2)
        (Nat.le_refl _) (-2)) previousComposition
  have removeHigh :
      EqualBelow (2 * depth + 2)
        (mul (add (constant 2) highTerm) previousComposition)
        (scale 2 previousComposition) :=
    equalBelow_trans
      ((coefficientwise_add_mul (constant 2) highTerm
        previousComposition).equalBelow _)
      (equalBelow_trans
        (equalBelow_add
          ((coefficientwise_constant_mul 2 previousComposition).equalBelow _)
          (equalBelow_refl _ _))
        (vanishesBelow_add_right highVanishes))
  have previousToCurrent :
      EqualBelow (2 * depth + 2) previousComposition composition := by
    exact equalBelow_symm
      (compose_exponential_succ_below (2 * depth + 1) logarithm
        (localLog_zero_constant depth))
  exact equalBelow_trans (fullIdentity.equalBelow _)
    (equalBelow_trans removeHigh
      (equalBelow_scale 2 previousToCurrent))

theorem coefficient_oneMinusSquare_mul_derivative
    (polynomial : Polynomial) (degree : Nat) :
    coefficient (mul oneMinusSquare (derivative polynomial)) degree =
      if degree < 2 then
        ((degree + 1 : Nat) : Coordinate) *
          coefficient polynomial (degree + 1)
      else
        ((degree + 1 : Nat) : Coordinate) *
            coefficient polynomial (degree + 1) -
          ((degree - 1 : Nat) : Coordinate) *
            coefficient polynomial (degree - 1) := by
  rw [oneMinusSquare,
    (coefficientwise_add_mul one (monomial 2 (-1))
      (derivative polynomial)) degree,
    coefficient_add,
    (coefficientwise_one_mul (derivative polynomial)) degree,
    coefficient_monomial_mul, coefficient_derivative]
  by_cases below : degree < 2
  · rw [if_pos below, if_pos below]
    ring1
  · rw [if_neg below, if_neg below, coefficient_derivative]
    rw [show degree - 2 + 1 = degree - 1 by omega]
    ring1

theorem exponential_zero_coefficient : ∀ depth,
    coefficient (exponential depth) 0 = 1
  | 0 => by rw [exponential, coefficient_constant, if_pos rfl]
  | depth + 1 => by
      rw [exponential, coefficient_add, exponential_zero_coefficient depth,
        coefficient_monomial, if_neg (Nat.zero_ne_add_one depth)]
      ring1

theorem coefficient_compose_zero_of_inner_zero (inner : Polynomial)
    (zeroConstant : coefficient inner 0 = 0) : ∀ outer,
    coefficient (composeCoefficients outer inner) 0 =
      coefficientCoefficients outer 0
  | [] => rfl
  | outer :: remaining => by
      rw [composeCoefficients, coefficient_add, coefficient_constant,
        if_pos rfl, coefficient_mul, coordinateSum_succ,
        coordinateSum_zero, Nat.zero_sub, zeroConstant,
        RFAP.ConstructiveFraction.zero_mul_direct,
        RFAP.ConstructiveFraction.zero_add]
      change outer + 0 = outer
      ring1

theorem exponentialLocalLog_zero_coefficient (depth : Nat) :
    coefficient (exponentialLocalLog (2 * depth + 2) depth) 0 = 1 := by
  rw [exponentialLocalLog]
  exact (coefficient_compose_zero_of_inner_zero (localLog depth)
    (localLog_zero_constant depth)
    (exponential (2 * depth + 2)).coefficients).trans
      (exponential_zero_coefficient (2 * depth + 2))

theorem exponentialLocalLog_low_coefficient (depth : Nat) :
    ∀ degree, degree ≤ 2 * depth + 2 →
      coefficient (exponentialLocalLog (2 * depth + 2) depth) degree =
        if degree = 0 then 1 else 2 := by
  let polynomial := exponentialLocalLog (2 * depth + 2) depth
  have all : ∀ limit, limit ≤ 2 * depth + 2 →
      ∀ degree, degree ≤ limit →
        coefficient polynomial degree = if degree = 0 then 1 else 2 := by
    intro limit
    induction limit with
    | zero =>
        intro limitBound degree degreeBound
        have degreeZero : degree = 0 := Nat.eq_zero_of_le_zero degreeBound
        subst degree
        rw [if_pos rfl]
        exact exponentialLocalLog_zero_coefficient depth
    | succ limit inductionHypothesis =>
        intro limitBound degree degreeBound
        have limitLeMaximum : limit ≤ 2 * depth + 2 :=
          (Nat.le_succ limit).trans limitBound
        by_cases earlier : degree ≤ limit
        · exact inductionHypothesis limitLeMaximum degree earlier
        · have degreeEqual : degree = limit + 1 :=
            Nat.le_antisymm degreeBound
              (Nat.succ_le_of_lt (Nat.lt_of_not_ge earlier))
          subst degree
          rw [if_neg (Nat.succ_ne_zero limit)]
          have ode := exponentialLocalLog_ode_below depth limit
            (Nat.lt_of_succ_le limitBound)
          rw [coefficient_oneMinusSquare_mul_derivative,
            coefficient_scale] at ode
          have current := inductionHypothesis limitLeMaximum limit
            (Nat.le_refl _)
          by_cases limitZero : limit = 0
          · subst limit
            rw [if_pos (by decide)] at current
            rw [if_pos (by decide)] at ode
            rw [current] at ode
            change coefficient
              (exponentialLocalLog (2 * depth + 2) depth) 1 = 2
            calc
              coefficient (exponentialLocalLog (2 * depth + 2) depth) 1 =
                  (1 : Coordinate) *
                    coefficient
                      (exponentialLocalLog (2 * depth + 2) depth) 1 := by ring1
              _ = 2 * 1 := ode
              _ = 2 := by ring1
          · rw [if_neg limitZero] at current
            by_cases limitOne : limit = 1
            · subst limit
              rw [if_pos (by decide)] at ode
              rw [current] at ode
              apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
                (show (2 : Coordinate) ≠ 0 by decide)
              calc
                coefficient polynomial 2 * 2 =
                    2 * coefficient polynomial 2 := by ring1
              _ = 2 * 2 := ode
            · have atLeastTwo : 2 ≤ limit :=
                by
                  cases limit with
                  | zero => exact (limitZero rfl).elim
                  | succ predecessor =>
                      cases predecessor with
                      | zero => exact (limitOne rfl).elim
                      | succ predecessor =>
                          exact Nat.succ_le_succ
                            (Nat.succ_le_succ (Nat.zero_le predecessor))
              rw [if_neg (Nat.not_lt_of_ge atLeastTwo)] at ode
              have previous := inductionHypothesis limitLeMaximum (limit - 1)
                (Nat.sub_le limit 1)
              have previousPositive : 0 < limit - 1 :=
                Nat.sub_pos_of_lt atLeastTwo
              rw [if_neg previousPositive.ne'] at previous
              have scaled :
                  ((limit + 1 : Nat) : Coordinate) *
                      coefficient polynomial (limit + 1) =
                    ((limit + 1 : Nat) : Coordinate) * 2 := by
                calc
                  ((limit + 1 : Nat) : Coordinate) *
                        coefficient polynomial (limit + 1) =
                      (((limit + 1 : Nat) : Coordinate) *
                          coefficient polynomial (limit + 1) -
                        ((limit - 1 : Nat) : Coordinate) *
                          coefficient polynomial (limit - 1)) +
                        ((limit - 1 : Nat) : Coordinate) *
                          coefficient polynomial (limit - 1) := by ring1
                  _ = 2 * coefficient polynomial limit +
                        ((limit - 1 : Nat) : Coordinate) *
                          coefficient polynomial (limit - 1) := by rw [ode]
                  _ = ((limit + 1 : Nat) : Coordinate) * 2 := by
                    rw [current, previous]
                    conv_rhs =>
                      rw [show limit + 1 = (limit - 1) + 2 by
                        have oneLe : 1 ≤ limit :=
                          (show 1 ≤ 2 by decide).trans atLeastTwo
                        calc
                          limit + 1 = (limit - 1 + 1) + 1 :=
                            congrArg (· + 1) (Nat.sub_add_cancel oneLe).symm
                          _ = (limit - 1) + (1 + 1) :=
                            Nat.add_assoc (limit - 1) 1 1
                          _ = (limit - 1) + 2 := rfl,
                        Nat.cast_add]
                    rw [show ((2 : Nat) : Coordinate) = 2 by decide]
                    ring1
              apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
                ((RFAP.ConstructiveFraction.natCast_pos_direct
                  (Nat.zero_lt_succ limit)).ne')
              calc
                coefficient polynomial (limit + 1) *
                      ((limit + 1 : Nat) : Coordinate) =
                    ((limit + 1 : Nat) : Coordinate) *
                      coefficient polynomial (limit + 1) := by ring1
                _ = ((limit + 1 : Nat) : Coordinate) * 2 := scaled
                _ = 2 * ((limit + 1 : Nat) : Coordinate) := by ring1
  intro degree bound
  exact all degree bound degree (Nat.le_refl _)

/-! ## Finite coefficient majorants -/

def CoefficientsNonnegative (polynomial : Polynomial) : Prop :=
  ∀ degree, 0 ≤ coefficient polynomial degree

def scalarEvalCoefficients (radius : Coordinate) :
    List Coordinate → Coordinate
  | [] => 0
  | coefficient :: remaining =>
      coefficient + radius * scalarEvalCoefficients radius remaining

def scalarEval (radius : Coordinate) (polynomial : Polynomial) : Coordinate :=
  scalarEvalCoefficients radius polynomial.coefficients

theorem coordinateSum_nonnegative (term : Nat → Coordinate)
    (termNonnegative : ∀ index, 0 ≤ term index) : ∀ count,
    0 ≤ coordinateSum term count
  | 0 => le_rfl
  | count + 1 =>
      add_nonneg (coordinateSum_nonnegative term termNonnegative count)
        (termNonnegative count)

theorem coefficientsNonnegative_constant {value : Coordinate}
    (nonnegative : 0 ≤ value) : CoefficientsNonnegative (constant value) := by
  intro degree
  rw [coefficient_constant]
  split
  · exact nonnegative
  · exact le_rfl

theorem coefficientsNonnegative_add {left right : Polynomial}
    (leftNonnegative : CoefficientsNonnegative left)
    (rightNonnegative : CoefficientsNonnegative right) :
    CoefficientsNonnegative (add left right) := by
  intro degree
  rw [coefficient_add]
  exact add_nonneg (leftNonnegative degree) (rightNonnegative degree)

theorem coefficientsNonnegative_scale {factor : Coordinate}
    (factorNonnegative : 0 ≤ factor) {polynomial : Polynomial}
    (nonnegative : CoefficientsNonnegative polynomial) :
    CoefficientsNonnegative (scale factor polynomial) := by
  intro degree
  rw [coefficient_scale]
  exact RFAP.ConstructiveFraction.mul_nonneg_direct factorNonnegative
    (nonnegative degree)

theorem coefficientsNonnegative_mul {left right : Polynomial}
    (leftNonnegative : CoefficientsNonnegative left)
    (rightNonnegative : CoefficientsNonnegative right) :
    CoefficientsNonnegative (mul left right) := by
  intro degree
  rw [coefficient_mul]
  exact coordinateSum_nonnegative _ (by
    intro index
    exact RFAP.ConstructiveFraction.mul_nonneg_direct
      (leftNonnegative index) (rightNonnegative (degree - index))) _

theorem coefficientsNonnegative_pow {polynomial : Polynomial}
    (nonnegative : CoefficientsNonnegative polynomial) : ∀ exponent,
    CoefficientsNonnegative (pow polynomial exponent)
  | 0 => coefficientsNonnegative_constant (by decide)
  | exponent + 1 =>
      coefficientsNonnegative_mul
        (coefficientsNonnegative_pow nonnegative exponent) nonnegative

theorem coefficientsNonnegative_monomial (degree : Nat)
    {value : Coordinate} (nonnegative : 0 ≤ value) :
    CoefficientsNonnegative (monomial degree value) := by
  intro outputDegree
  rw [coefficient_monomial]
  split
  · exact nonnegative
  · exact le_rfl

theorem coefficientsNonnegative_composeCoefficients
    {inner : Polynomial} (innerNonnegative : CoefficientsNonnegative inner) :
    ∀ coefficients,
      (∀ degree, 0 ≤ coefficientCoefficients coefficients degree) →
        CoefficientsNonnegative (composeCoefficients coefficients inner)
  | [], outerNonnegative => fun degree => by
      change 0 ≤ 0
      exact le_rfl
  | coefficient :: remaining, outerNonnegative => by
      apply coefficientsNonnegative_add
      · exact coefficientsNonnegative_constant (outerNonnegative 0)
      · apply coefficientsNonnegative_mul innerNonnegative
        apply coefficientsNonnegative_composeCoefficients innerNonnegative
        intro degree
        exact outerNonnegative (degree + 1)

theorem coefficientsNonnegative_compose {outer inner : Polynomial}
    (outerNonnegative : CoefficientsNonnegative outer)
    (innerNonnegative : CoefficientsNonnegative inner) :
    CoefficientsNonnegative (compose outer inner) :=
  coefficientsNonnegative_composeCoefficients innerNonnegative
    outer.coefficients outerNonnegative

theorem coefficientsNonnegative_exponential : ∀ depth,
    CoefficientsNonnegative (exponential depth)
  | 0 => coefficientsNonnegative_constant (by decide)
  | depth + 1 => by
      apply coefficientsNonnegative_add
        (coefficientsNonnegative_exponential depth)
      apply coefficientsNonnegative_monomial
      exact RFAP.ConstructiveFraction.div_nonneg_direct (by decide)
        (RFAP.ConstructiveFraction.natCast_pos_direct
          (CCL.TranscendentalLaws.factorial_pos
            (depth + 1))).le

theorem coefficientsNonnegative_localLog : ∀ depth,
    CoefficientsNonnegative (localLog depth)
  | 0 => coefficientsNonnegative_monomial 1 (by decide)
  | depth + 1 => by
      apply coefficientsNonnegative_add
        (coefficientsNonnegative_localLog depth)
      apply coefficientsNonnegative_monomial
      exact RFAP.ConstructiveFraction.div_nonneg_direct (by decide)
        (add_nonneg
          (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
            (RFAP.ConstructiveFraction.natCast_pos_direct
              (show 0 < depth + 1 by omega)).le)
          (by decide))

theorem coefficientsNonnegative_exponentialLocalLog
    (expDegree logDepth : Nat) :
    CoefficientsNonnegative (exponentialLocalLog expDegree logDepth) :=
  coefficientsNonnegative_compose
    (coefficientsNonnegative_exponential expDegree)
    (coefficientsNonnegative_localLog logDepth)

theorem scalarEvalCoefficients_nonnegative {radius : Coordinate}
    (radiusNonnegative : 0 ≤ radius) : ∀ coefficients,
    (∀ degree, 0 ≤ coefficientCoefficients coefficients degree) →
      0 ≤ scalarEvalCoefficients radius coefficients
  | [], _ => le_rfl
  | _ :: remaining, coefficientsNonnegative =>
      add_nonneg (coefficientsNonnegative 0)
        (RFAP.ConstructiveFraction.mul_nonneg_direct radiusNonnegative
          (scalarEvalCoefficients_nonnegative radiusNonnegative remaining
            (fun degree => coefficientsNonnegative (degree + 1))))

theorem evalCoefficients_scalar (radius : Coordinate) : ∀ coefficients,
    evalCoefficients (CCL.FiniteComplexLog.scalar radius)
        coefficients =
      CCL.FiniteComplexLog.scalar
        (scalarEvalCoefficients radius coefficients)
  | [] => rfl
  | coefficient :: remaining => by
      rw [evalCoefficients, scalarEvalCoefficients,
        evalCoefficients_scalar radius remaining]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [CCL.FiniteComplexLog.scalar,
          CCL.FiniteExp.scale_re,
          CCL.FiniteExp.scale_im, add_re, add_im,
          mul_re, mul_im, one_re, one_im] <;> ring1

theorem eval_scalar (radius : Coordinate) (polynomial : Polynomial) :
    eval polynomial (CCL.FiniteComplexLog.scalar radius) =
      CCL.FiniteComplexLog.scalar (scalarEval radius polynomial) :=
  evalCoefficients_scalar radius polynomial.coefficients

theorem evalCoefficients_normSq_le_scalarHalf : ∀ coefficients
    (z : Gaussian), normSq z ≤ 1 / 9 →
    (∀ degree, 0 ≤ coefficientCoefficients coefficients degree) →
    normSq (evalCoefficients z coefficients) ≤
      2 * scalarEvalCoefficients (1 / 2) coefficients ^ 2
  | [], z, zBound, coefficientsNonnegative => by
      rw [evalCoefficients, normSq_zero, scalarEvalCoefficients]
      decide
  | coefficient :: remaining, z, zBound, coefficientsNonnegative => by
      let tailMagnitude := scalarEvalCoefficients (1 / 2) remaining
      have coefficientNonnegative : 0 ≤ coefficient :=
        coefficientsNonnegative 0
      have tailNonnegative : 0 ≤ tailMagnitude :=
        scalarEvalCoefficients_nonnegative (by decide) remaining
          (fun degree => coefficientsNonnegative (degree + 1))
      have tailBound := evalCoefficients_normSq_le_scalarHalf remaining z
        zBound (fun degree => coefficientsNonnegative (degree + 1))
      have productBound :
          normSq (z * evalCoefficients z remaining) ≤
            (2 / 9 : Coordinate) * tailMagnitude ^ 2 := by
        rw [normSq_mul]
        calc
          normSq z * normSq (evalCoefficients z remaining) ≤
              (1 / 9 : Coordinate) *
                (2 * tailMagnitude ^ 2) :=
            RFAP.ConstructiveFraction.mul_le_mul_direct zBound tailBound
              (normSq_nonneg _) (by decide)
          _ = ((1 / 9 : Coordinate) * 2) * tailMagnitude ^ 2 := by ring1
          _ = (2 / 9 : Coordinate) * tailMagnitude ^ 2 := by
            rw [show (1 / 9 : Coordinate) * 2 = 2 / 9 by
              rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
                RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
              ring1]
      have insideBound :
          coefficient ^ 2 + (2 / 9 : Coordinate) * tailMagnitude ^ 2 ≤
            (coefficient + (1 / 2 : Coordinate) * tailMagnitude) ^ 2 := by
        have remainderNonnegative :
            0 ≤ coefficient * tailMagnitude +
              (1 / 36 : Coordinate) * tailMagnitude ^ 2 :=
          add_nonneg
            (RFAP.ConstructiveFraction.mul_nonneg_direct
              coefficientNonnegative tailNonnegative)
            (RFAP.ConstructiveFraction.mul_nonneg_direct
              (RFAP.ConstructiveFraction.div_nonneg_direct
                (RFAP.ConstructiveFraction.natCast_pos_direct
                  (n := 1) (by decide)).le
                (RFAP.ConstructiveFraction.natCast_pos_direct
                  (n := 36) (by decide)).le)
              (RFAP.ConstructiveFraction.sq_nonneg_direct tailMagnitude))
        calc
          coefficient ^ 2 + (2 / 9 : Coordinate) * tailMagnitude ^ 2 ≤
              (coefficient ^ 2 + (2 / 9 : Coordinate) * tailMagnitude ^ 2) +
                (coefficient * tailMagnitude +
                  (1 / 36 : Coordinate) * tailMagnitude ^ 2) :=
            le_add_of_nonneg_right remainderNonnegative
          _ = coefficient ^ 2 + coefficient * tailMagnitude +
                ((2 / 9 : Coordinate) + 1 / 36) * tailMagnitude ^ 2 := by
            ring1
          _ = coefficient ^ 2 + coefficient * tailMagnitude +
                (1 / 4 : Coordinate) * tailMagnitude ^ 2 := by
            rw [show (2 / 9 : Coordinate) + 1 / 36 = 1 / 4 by
              have nineNonzero : (9 : Coordinate) ≠ 0 :=
                (RFAP.ConstructiveFraction.natCast_pos_direct
                  (n := 9) (by decide)).ne'
              have thirtySixNonzero : (36 : Coordinate) ≠ 0 :=
                (RFAP.ConstructiveFraction.natCast_pos_direct
                  (n := 36) (by decide)).ne'
              have fourNonzero : (4 : Coordinate) ≠ 0 :=
                (RFAP.ConstructiveFraction.natCast_pos_direct
                  (n := 4) (by decide)).ne'
              have first : (2 / 9 : Coordinate) = 8 / 36 := by
                apply RFAP.ConstructiveFraction.div_eq_div_of_cross_mul
                  nineNonzero thirtySixNonzero
                ring1
              have last : (9 / 36 : Coordinate) = 1 / 4 := by
                apply RFAP.ConstructiveFraction.div_eq_div_of_cross_mul
                  thirtySixNonzero fourNonzero
                ring1
              rw [first]
              calc
                (8 / 36 : Coordinate) + 1 / 36 = 9 / 36 := by
                  rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
                    RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
                    RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
                  ring1
                _ = 1 / 4 := last]
          _ = coefficient ^ 2 +
                (2 * (1 / 2 : Coordinate)) * coefficient * tailMagnitude +
                (1 / 2 : Coordinate) ^ 2 * tailMagnitude ^ 2 := by
            rw [show (2 : Coordinate) * (1 / 2) = 1 by
                calc
                  (2 : Coordinate) * (1 / 2) = (1 / 2) * 2 := by ring1
                  _ = 1 := RFAP.ConstructiveFraction.div_mul_cancel_of_ne
                    1 2 (RFAP.ConstructiveFraction.natCast_pos_direct
                      (n := 2) (by decide)).ne',
              show (1 / 2 : Coordinate) ^ 2 = 1 / 4 by
                rw [pow_two, RFAP.ConstructiveFraction.div_mul_div_direct]
                apply RFAP.ConstructiveFraction.div_eq_div_of_cross_mul
                · exact RFAP.ConstructiveFraction.mul_ne_zero_direct
                    (RFAP.ConstructiveFraction.natCast_pos_direct
                      (n := 2) (by decide)).ne'
                    (RFAP.ConstructiveFraction.natCast_pos_direct
                      (n := 2) (by decide)).ne'
                · exact (RFAP.ConstructiveFraction.natCast_pos_direct
                    (n := 4) (by decide)).ne'
                · ring1]
            ring1
          _ = (coefficient + (1 / 2 : Coordinate) * tailMagnitude) ^ 2 := by
            ring1
      rw [evalCoefficients, scalarEvalCoefficients]
      calc
        normSq
            (CCL.FiniteExp.scale coefficient 1 +
              z * evalCoefficients z remaining) ≤
            2 * (normSq (CCL.FiniteExp.scale coefficient 1) +
              normSq (z * evalCoefficients z remaining)) :=
          normSq_add_le_two _ _
        _ ≤ 2 * (coefficient ^ 2 +
              (2 / 9 : Coordinate) * tailMagnitude ^ 2) := by
          have headNorm :
              normSq (CCL.FiniteExp.scale coefficient 1) =
                coefficient ^ 2 := by
            rw [CCL.FiniteExp.normSq_scale, normSq_one]
            ring1
          rw [headNorm]
          apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            (add_le_add le_rfl productBound) (by decide)
        _ ≤ 2 *
            (coefficient + (1 / 2 : Coordinate) * tailMagnitude) ^ 2 :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            insideBound (by decide)

theorem eval_normSq_le_scalarHalf {polynomial : Polynomial}
    (nonnegative : CoefficientsNonnegative polynomial) {z : Gaussian}
    (zBound : normSq z ≤ 1 / 9) :
    normSq (eval polynomial z) ≤ 2 * scalarEval (1 / 2) polynomial ^ 2 :=
  evalCoefficients_normSq_le_scalarHalf polynomial.coefficients z zBound
    nonnegative

theorem scalarEvalCoefficients_add (radius : Coordinate) : ∀ left right,
    scalarEvalCoefficients radius (addCoefficients left right) =
      scalarEvalCoefficients radius left +
        scalarEvalCoefficients radius right
  | [], right => by
      rw [addCoefficients, scalarEvalCoefficients,
        RFAP.ConstructiveFraction.zero_add]
  | left, [] => by
      rw [addCoefficients_nil_right, scalarEvalCoefficients]
      ring1
  | left :: leftTail, right :: rightTail => by
      rw [addCoefficients, scalarEvalCoefficients,
        scalarEvalCoefficients, scalarEvalCoefficients,
        scalarEvalCoefficients_add radius leftTail rightTail]
      ring1

@[simp] theorem scalarEval_add (radius : Coordinate)
    (left right : Polynomial) :
    scalarEval radius (add left right) =
      scalarEval radius left + scalarEval radius right :=
  scalarEvalCoefficients_add radius left.coefficients right.coefficients

theorem scalarEvalCoefficients_shift (radius : Coordinate) :
    ∀ count coefficients,
      scalarEvalCoefficients radius
          (List.replicate count 0 ++ coefficients) =
        radius ^ count * scalarEvalCoefficients radius coefficients
  | 0, coefficients => by
      rw [List.replicate_zero, List.nil_append, pow_zero]
      ring1
  | count + 1, coefficients => by
      rw [List.replicate_succ, List.cons_append, scalarEvalCoefficients,
        scalarEvalCoefficients_shift radius count coefficients, pow_succ]
      ring1

@[simp] theorem scalarEval_shift (radius : Coordinate) (count : Nat)
    (polynomial : Polynomial) :
    scalarEval radius (shift count polynomial) =
      radius ^ count * scalarEval radius polynomial :=
  scalarEvalCoefficients_shift radius count polynomial.coefficients

@[simp] theorem scalarEval_constant (radius value : Coordinate) :
    scalarEval radius (constant value) = value := by
  change value + radius * 0 = value
  ring1

@[simp] theorem scalarEval_monomial (radius : Coordinate) (degree : Nat)
    (value : Coordinate) :
    scalarEval radius (monomial degree value) = value * radius ^ degree := by
  rw [monomial, scalarEval_shift, scalarEval_constant]
  ring1

def quarterSum : Nat → Coordinate
  | 0 => 0
  | count + 1 => quarterSum count + (1 / 4 : Coordinate) ^ count

theorem quarterSum_remainder : ∀ count,
    quarterSum count + (4 / 3 : Coordinate) * (1 / 4) ^ count = 4 / 3
  | 0 => by rw [quarterSum, pow_zero]; decide
  | count + 1 => by
      rw [quarterSum, pow_succ]
      calc
        quarterSum count + (1 / 4 : Coordinate) ^ count +
            (4 / 3 : Coordinate) *
              ((1 / 4 : Coordinate) ^ count * (1 / 4)) =
            quarterSum count +
              (1 + (4 / 3 : Coordinate) * (1 / 4)) *
                (1 / 4 : Coordinate) ^ count := by ring1
        _ = quarterSum count +
              (4 / 3 : Coordinate) * (1 / 4) ^ count := by
            rw [show (1 : Coordinate) + (4 / 3) * (1 / 4) = 4 / 3 by decide]
        _ = 4 / 3 := quarterSum_remainder count

theorem quarterSum_le (count : Nat) : quarterSum count ≤ 4 / 3 := by
  have remainderNonnegative :
      0 ≤ (4 / 3 : Coordinate) * (1 / 4) ^ count :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) count)
  calc
    quarterSum count ≤
        quarterSum count + (4 / 3 : Coordinate) * (1 / 4) ^ count :=
      le_add_of_nonneg_right remainderNonnegative
    _ = 4 / 3 := quarterSum_remainder count

theorem twice_half_odd_power : ∀ index,
    (2 : Coordinate) * (1 / 2 : Coordinate) ^ (2 * index + 1) =
      (1 / 4 : Coordinate) ^ index
  | 0 => by decide
  | index + 1 => by
      rw [show 2 * (index + 1) + 1 = (2 * index + 1) + 2 by ring1,
        pow_add]
      calc
        (2 : Coordinate) *
            ((1 / 2 : Coordinate) ^ (2 * index + 1) * (1 / 2) ^ 2) =
            (2 * (1 / 2 : Coordinate) ^ (2 * index + 1)) *
              (1 / 2) ^ 2 := by ring1
        _ = (1 / 4 : Coordinate) ^ index * (1 / 2) ^ 2 := by
          rw [twice_half_odd_power index]
        _ = (1 / 4 : Coordinate) ^ index * (1 / 4) := by
          rw [show (1 / 2 : Coordinate) ^ 2 = 1 / 4 by decide]
        _ = (1 / 4 : Coordinate) ^ (index + 1) := (pow_succ _ _).symm

theorem localLogCoefficient_le_two (index : Nat) :
    2 / (2 * (index : Coordinate) + 1) ≤ 2 := by
  have indexNonnegative : (0 : Coordinate) ≤ (index : Coordinate) := by
    have castBound := RFAP.ConstructiveFraction.natCast_le_direct
      (Nat.zero_le index)
    simpa only [Nat.cast_zero] using castBound
  have denominatorPositive : 0 < 2 * (index : Coordinate) + 1 :=
    add_pos_of_nonneg_of_pos
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        indexNonnegative)
      (by decide)
  apply (RFAP.ConstructiveFraction.div_le_iff_pos denominatorPositive).mpr
  have denominatorAtLeastOne :
      (1 : Coordinate) ≤ 2 * (index : Coordinate) + 1 := by
    calc
      (1 : Coordinate) = 0 + 1 := by ring1
      _ ≤ 2 * (index : Coordinate) + 1 :=
        add_le_add (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
          indexNonnegative) le_rfl
  calc
    (2 : Coordinate) ≤ 2 * 1 := by
      rw [RFAP.ConstructiveFraction.mul_one_direct]
    _ ≤ 2 * (2 * (index : Coordinate) + 1) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        denominatorAtLeastOne (by decide)

theorem scalarEval_localLog_half_le_quarterSum : ∀ depth,
    scalarEval (1 / 2) (localLog depth) ≤ quarterSum (depth + 1)
  | 0 => by
      rw [localLog, scalarEval_monomial, quarterSum, quarterSum]
      decide
  | depth + 1 => by
      rw [localLog, scalarEval_add, scalarEval_monomial,
        quarterSum]
      apply add_le_add (scalarEval_localLog_half_le_quarterSum depth)
      calc
        (2 / (2 * ((depth + 1 : Nat) : Coordinate) + 1)) *
            (1 / 2 : Coordinate) ^ (2 * (depth + 1) + 1) ≤
            2 * (1 / 2 : Coordinate) ^ (2 * (depth + 1) + 1) :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
            (localLogCoefficient_le_two (depth + 1))
            (RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) _)
        _ = (1 / 4 : Coordinate) ^ (depth + 1) :=
          twice_half_odd_power (depth + 1)

theorem scalarEval_localLog_half_le (depth : Nat) :
    scalarEval (1 / 2) (localLog depth) ≤ 4 / 3 :=
  (scalarEval_localLog_half_le_quarterSum depth).trans
    (quarterSum_le (depth + 1))

theorem scalarEval_compose (radius : Coordinate) (outer inner : Polynomial) :
    scalarEval radius (compose outer inner) =
      scalarEval (scalarEval radius inner) outer := by
  have evaluated := eval_compose outer inner
    (CCL.FiniteComplexLog.scalar radius)
  rw [eval_scalar, eval_scalar, eval_scalar] at evaluated
  exact congrArg RFAP.ConstructiveGaussian.Gaussian.re evaluated

theorem two_pow_le_factorial_succ : ∀ index,
    2 ^ index ≤
      CCL.TranscendentalLaws.factorial (index + 1)
  | 0 => by decide
  | index + 1 => by
      rw [pow_succ,
        CCL.TranscendentalLaws.factorial_succ]
      exact Nat.mul_le_mul
        (two_pow_le_factorial_succ index) (by omega)

theorem fourThird_div_twoPow (index : Nat) :
    (4 / 3 : Coordinate) ^ (index + 1) /
        (2 : Coordinate) ^ index =
      2 * (2 / 3 : Coordinate) ^ (index + 1) := by
  have denominatorPositive : 0 < (2 : Coordinate) ^ index :=
    RFAP.ConstructiveFraction.pow_pos_direct (by decide) index
  apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
    denominatorPositive.ne'
  calc
    ((4 / 3 : Coordinate) ^ (index + 1) /
          (2 : Coordinate) ^ index) * (2 : Coordinate) ^ index =
        (4 / 3 : Coordinate) ^ (index + 1) :=
      RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _
        denominatorPositive.ne'
    _ = (2 * (2 / 3 : Coordinate) ^ (index + 1)) *
          (2 : Coordinate) ^ index := by
      rw [show (4 / 3 : Coordinate) = 2 * (2 / 3) by decide,
        mul_pow, pow_succ]
      ring1

theorem scalarExponentialTerm_bound {value : Coordinate}
    (nonnegative : 0 ≤ value) (upper : value ≤ 4 / 3) (index : Nat) :
    (1 / (CCL.TranscendentalLaws.factorial
        (index + 1) : Coordinate)) * value ^ (index + 1) ≤
      2 * (2 / 3 : Coordinate) ^ (index + 1) := by
  have valuePowerNonnegative : 0 ≤ value ^ (index + 1) :=
    RFAP.ConstructiveFraction.pow_nonneg_direct nonnegative _
  have upperPower := RFAP.ConstructiveFraction.pow_le_pow_direct
    nonnegative upper (index + 1)
  have factorialPositive :
      0 < (CCL.TranscendentalLaws.factorial
        (index + 1) : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_pos_direct
      (CCL.TranscendentalLaws.factorial_pos (index + 1))
  have twoPowerPositive : 0 < (2 : Coordinate) ^ index :=
    RFAP.ConstructiveFraction.pow_pos_direct (by decide) index
  have denominatorOrder :
      (2 : Coordinate) ^ index ≤
        (CCL.TranscendentalLaws.factorial
          (index + 1) : Coordinate) := by
    have castOrder := RFAP.ConstructiveFraction.natCast_le_direct
      (two_pow_le_factorial_succ index)
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using castOrder
  calc
    (1 / (CCL.TranscendentalLaws.factorial
          (index + 1) : Coordinate)) * value ^ (index + 1) =
        value ^ (index + 1) /
          (CCL.TranscendentalLaws.factorial
            (index + 1) : Coordinate) := by
      rw [RFAP.ExplicitField.div_eq_mul_inv,
        RFAP.ExplicitField.div_eq_mul_inv,
        RFAP.ConstructiveFraction.one_mul,
        RFAP.ConstructiveFraction.mul_comm]
    _ ≤ (4 / 3 : Coordinate) ^ (index + 1) /
          (CCL.TranscendentalLaws.factorial
            (index + 1) : Coordinate) := by
      apply (RFAP.ConstructiveFraction.div_le_iff_pos
        factorialPositive).mpr
      calc
        value ^ (index + 1) ≤ (4 / 3 : Coordinate) ^ (index + 1) := upperPower
        _ = ((4 / 3 : Coordinate) ^ (index + 1) /
              (CCL.TranscendentalLaws.factorial
                (index + 1) : Coordinate)) *
            (CCL.TranscendentalLaws.factorial
              (index + 1) : Coordinate) := by
          exact (RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _
            factorialPositive.ne').symm
    _ ≤ (4 / 3 : Coordinate) ^ (index + 1) /
          (2 : Coordinate) ^ index :=
      RFAP.ConstructiveFraction.div_le_div_of_nonneg_left_direct
        (RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) _)
        twoPowerPositive denominatorOrder
    _ = 2 * (2 / 3 : Coordinate) ^ (index + 1) :=
      fourThird_div_twoPow index

def twoThirdSum : Nat → Coordinate
  | 0 => 0
  | count + 1 =>
      twoThirdSum count + 2 * (2 / 3 : Coordinate) ^ (count + 1)

theorem twoThirdSum_remainder : ∀ count,
    twoThirdSum count + 4 * (2 / 3 : Coordinate) ^ count = 4
  | 0 => by rw [twoThirdSum, pow_zero]; decide
  | count + 1 => by
      rw [twoThirdSum, pow_succ]
      calc
        twoThirdSum count + 2 * (2 / 3 : Coordinate) ^ (count + 1) +
            4 * ((2 / 3 : Coordinate) ^ count * (2 / 3)) =
          twoThirdSum count +
            (2 * (2 / 3 : Coordinate) + 4 * (2 / 3)) *
              (2 / 3 : Coordinate) ^ count := by
            rw [pow_succ]
            ring1
        _ = twoThirdSum count + 4 * (2 / 3 : Coordinate) ^ count := by
          rw [show (2 : Coordinate) * (2 / 3) + 4 * (2 / 3) = 4 by decide]
        _ = 4 := twoThirdSum_remainder count

theorem twoThirdSum_le_four (count : Nat) : twoThirdSum count ≤ 4 := by
  have remainderNonnegative :
      0 ≤ (4 : Coordinate) * (2 / 3 : Coordinate) ^ count :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) count)
  calc
    twoThirdSum count ≤
        twoThirdSum count + 4 * (2 / 3 : Coordinate) ^ count :=
      le_add_of_nonneg_right remainderNonnegative
    _ = 4 := twoThirdSum_remainder count

theorem scalarEval_exponential_le {value : Coordinate}
    (nonnegative : 0 ≤ value) (upper : value ≤ 4 / 3) : ∀ depth,
    scalarEval value (exponential depth) ≤ 1 + twoThirdSum depth
  | 0 => by rw [exponential, scalarEval_constant, twoThirdSum]; exact le_rfl
  | depth + 1 => by
      rw [exponential, scalarEval_add, scalarEval_monomial, twoThirdSum]
      calc
        scalarEval value (exponential depth) +
            (1 / (CCL.TranscendentalLaws.factorial
              (depth + 1) : Coordinate)) * value ^ (depth + 1) ≤
          (1 + twoThirdSum depth) +
            2 * (2 / 3 : Coordinate) ^ (depth + 1) :=
          add_le_add
            (scalarEval_exponential_le nonnegative upper depth)
            (scalarExponentialTerm_bound nonnegative upper depth)
        _ = 1 +
            (twoThirdSum depth +
              2 * (2 / 3 : Coordinate) ^ (depth + 1)) := by ring1

theorem scalarEval_exponential_le_five {value : Coordinate}
    (nonnegative : 0 ≤ value) (upper : value ≤ 4 / 3) (depth : Nat) :
    scalarEval value (exponential depth) ≤ 5 :=
  (scalarEval_exponential_le nonnegative upper depth).trans (by
    have sumBound := twoThirdSum_le_four depth
    calc
      (1 : Coordinate) + twoThirdSum depth ≤ 1 + 4 :=
        add_le_add le_rfl sumBound
      _ = 5 := by decide)

theorem scalarEval_exponentialLocalLog_half_le_five
    (expDegree logDepth : Nat) :
    scalarEval (1 / 2) (exponentialLocalLog expDegree logDepth) ≤ 5 := by
  rw [exponentialLocalLog, scalarEval_compose]
  apply scalarEval_exponential_le_five
  · exact scalarEvalCoefficients_nonnegative (by decide)
      (localLog logDepth).coefficients
      (coefficientsNonnegative_localLog logDepth)
  · exact scalarEval_localLog_half_le logDepth

/-! ## Low prefix and high tail decomposition -/

def prefixEvalCoefficients (z : Gaussian) :
    List Coordinate → Nat → Gaussian
  | _, 0 => 0
  | [], _ + 1 => 0
  | coefficient :: remaining, count + 1 =>
      CCL.FiniteExp.scale coefficient 1 +
        z * prefixEvalCoefficients z remaining count

def prefixEval (z : Gaussian) (polynomial : Polynomial) (count : Nat) :
    Gaussian := prefixEvalCoefficients z polynomial.coefficients count

@[simp] theorem prefixEvalCoefficients_nil (z : Gaussian) : ∀ count,
    prefixEvalCoefficients z [] count = 0
  | 0 => rfl
  | _ + 1 => rfl

theorem evalCoefficients_split (z : Gaussian) : ∀ coefficients count,
    evalCoefficients z coefficients =
      prefixEvalCoefficients z coefficients count +
        z ^ count * evalCoefficients z (coefficients.drop count)
  | coefficients, 0 => by
      rw [prefixEvalCoefficients, pow_zero, List.drop_zero]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [add_re, add_im, mul_re, mul_im,
          zero_re, zero_im, one_re, one_im] <;> ring1
  | [], count + 1 => by
      rw [evalCoefficients, prefixEvalCoefficients, List.drop_nil,
        evalCoefficients]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [add_re, add_im, mul_re, mul_im,
          zero_re, zero_im] <;> ring1
  | coefficient :: remaining, count + 1 => by
      rw [evalCoefficients, prefixEvalCoefficients, List.drop_succ_cons,
        evalCoefficients_split z remaining count, pow_succ]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [add_re, add_im, mul_re, mul_im] <;> ring1

theorem eval_split (z : Gaussian) (polynomial : Polynomial) (count : Nat) :
    eval polynomial z =
      prefixEval z polynomial count +
        z ^ count * eval ⟨polynomial.coefficients.drop count⟩ z :=
  evalCoefficients_split z polynomial.coefficients count

theorem prefixEvalCoefficients_congr (z : Gaussian) :
    ∀ {left right : List Coordinate} count,
      (∀ degree, degree < count →
        coefficientCoefficients left degree =
          coefficientCoefficients right degree) →
      prefixEvalCoefficients z left count =
        prefixEvalCoefficients z right count
  | left, right, 0, equal => by
      cases left <;> cases right <;> rfl
  | [], [], count + 1, equal => rfl
  | [], right :: rightTail, count + 1, equal => by
      have headZero : right = 0 := by
        have atZero := equal 0 (by omega)
        change 0 = right at atZero
        exact atZero.symm
      have tailEqual : ∀ degree, degree < count →
          coefficientCoefficients [] degree =
            coefficientCoefficients rightTail degree := by
        intro degree below
        exact equal (degree + 1) (by omega)
      subst right
      change 0 = CCL.FiniteExp.scale 0 1 +
        z * prefixEvalCoefficients z rightTail count
      rw [← prefixEvalCoefficients_congr z count tailEqual]
      rw [prefixEvalCoefficients_nil]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [CCL.FiniteExp.scale_re,
          CCL.FiniteExp.scale_im, add_re, add_im, mul_re, mul_im,
          zero_re, zero_im, one_re, one_im] <;> ring1
  | left :: leftTail, [], count + 1, equal => by
      have headZero : left = 0 := equal 0 (by omega)
      have tailEqual : ∀ degree, degree < count →
          coefficientCoefficients leftTail degree =
            coefficientCoefficients [] degree := by
        intro degree below
        exact equal (degree + 1) (by omega)
      subst left
      change CCL.FiniteExp.scale 0 1 +
        z * prefixEvalCoefficients z leftTail count = 0
      rw [prefixEvalCoefficients_congr z count tailEqual]
      rw [prefixEvalCoefficients_nil]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [CCL.FiniteExp.scale_re,
          CCL.FiniteExp.scale_im, add_re, add_im, mul_re, mul_im,
          zero_re, zero_im, one_re, one_im] <;> ring1
  | left :: leftTail, right :: rightTail, count + 1, equal => by
      have headEqual : left = right := equal 0 (by omega)
      have tailEqual : ∀ degree, degree < count →
          coefficientCoefficients leftTail degree =
            coefficientCoefficients rightTail degree := by
        intro degree below
        exact equal (degree + 1) (by omega)
      rw [prefixEvalCoefficients, prefixEvalCoefficients, headEqual,
        prefixEvalCoefficients_congr z count tailEqual]

theorem prefixEval_congr {count : Nat} {left right : Polynomial}
    (equal : EqualBelow count left right) (z : Gaussian) :
    prefixEval z left count = prefixEval z right count :=
  prefixEvalCoefficients_congr z count equal

def geometricPrefix : Nat → Polynomial
  | 0 => constant 1
  | degree + 1 => add (geometricPrefix degree) (monomial (degree + 1) 2)

theorem geometricPrefix_coefficient : ∀ prefixDegree degree,
    coefficient (geometricPrefix prefixDegree) degree =
      if degree = 0 then 1 else if degree ≤ prefixDegree then 2 else 0
  | 0, degree => by
      rw [geometricPrefix, coefficient_constant]
      by_cases zero : degree = 0
      · subst degree
        simp only [if_pos]
      · simp only [if_neg zero]
        rw [if_neg (fun degreeLeZero =>
          zero (Nat.eq_zero_of_le_zero degreeLeZero))]
  | prefixDegree + 1, degree => by
      rw [geometricPrefix, coefficient_add,
        geometricPrefix_coefficient prefixDegree degree,
        coefficient_monomial]
      by_cases zero : degree = 0
      · subst degree
        simp only [if_pos]
        rw [if_neg (Nat.zero_ne_add_one prefixDegree)]
        ring1
      · simp only [if_neg zero]
        by_cases inside : degree ≤ prefixDegree
        · have notFinal : degree ≠ prefixDegree + 1 := by
            intro final
            subst degree
            exact (Nat.not_succ_le_self prefixDegree) inside
          rw [if_pos inside, if_neg notFinal,
            if_pos (inside.trans (Nat.le_succ prefixDegree))]
          ring1
        · by_cases final : degree = prefixDegree + 1
          · subst degree
            rw [if_neg inside, if_pos rfl,
              if_pos (Nat.le_refl _)]
            ring1
          · have beyond : ¬degree ≤ prefixDegree + 1 := by
              intro degreeLe
              exact inside (Nat.le_of_lt_succ
                (Nat.lt_of_le_of_ne degreeLe final))
            rw [if_neg inside, if_neg final, if_neg beyond]
            ring1

theorem exponentialLocalLog_equalBelow_geometricPrefix (depth : Nat) :
    EqualBelow (2 * depth + 3)
      (exponentialLocalLog (2 * depth + 2) depth)
      (geometricPrefix (2 * depth + 2)) := by
  intro degree below
  rw [exponentialLocalLog_low_coefficient depth degree (by omega),
    geometricPrefix_coefficient]
  by_cases zero : degree = 0
  · simp only [if_pos zero]
  · simp only [if_neg zero]
    rw [if_pos (by omega)]

theorem one_sub_mul_geometricPrefix (z : Gaussian) : ∀ degree,
    (1 - z) * eval (geometricPrefix degree) z =
      1 + z + CCL.FiniteExp.scale (-2) (z ^ (degree + 1))
  | 0 => by
      rw [geometricPrefix]
      rw [show z ^ (0 + 1) = z by
        rw [Nat.zero_add, pow_one]]
      change (1 - z) *
          (CCL.FiniteExp.scale 1 1 + z * 0) = _
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [CCL.FiniteExp.scale_re,
          CCL.FiniteExp.scale_im, add_re, add_im, sub_re, sub_im,
          mul_re, mul_im, zero_re, zero_im, one_re, one_im] <;> ring1
  | degree + 1 => by
      rw [geometricPrefix, eval_add, eval_monomial, pow_succ]
      calc
        (1 - z) *
            (eval (geometricPrefix degree) z +
              CCL.FiniteExp.scale 2 (z ^ degree * z)) =
            (1 - z) * eval (geometricPrefix degree) z +
              (1 - z) *
                CCL.FiniteExp.scale 2 (z ^ degree * z) := by
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [CCL.FiniteExp.scale_re,
              CCL.FiniteExp.scale_im, add_re, add_im, sub_re,
              sub_im, mul_re, mul_im] <;> ring1
        _ = (1 + z +
              CCL.FiniteExp.scale (-2) (z ^ (degree + 1))) +
            (1 - z) *
              CCL.FiniteExp.scale 2 (z ^ degree * z) := by
          rw [one_sub_mul_geometricPrefix z degree]
        _ = 1 + z +
            CCL.FiniteExp.scale (-2)
              (z ^ (degree + 1 + 1)) := by
          have nextPower :
              z ^ (degree + 1 + 1) = (z ^ degree * z) * z := by
            rw [pow_succ, pow_succ]
          have currentPower : z ^ (degree + 1) = z ^ degree * z := by
            rw [pow_succ]
          rw [nextPower, currentPower]
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [CCL.FiniteExp.scale_re,
              CCL.FiniteExp.scale_im, add_re, add_im, sub_re,
              sub_im, mul_re, mul_im, one_re, one_im] <;> ring1

theorem gaussian_div_mul_cancel (numerator denominator : Gaussian)
    (nonzero : denominator ≠ 0) :
    (numerator / denominator) * denominator = numerator := by
  rw [RFAP.ExplicitField.div_eq_mul_inv,
    RFAP.ConstructiveGaussian.Gaussian.mul_assoc]
  rw [show denominator⁻¹ * denominator = 1 from
    RFAP.CanonicalGaussian.Gaussian.inv_mul_cancel denominator nonzero,
    RFAP.ConstructiveGaussian.Gaussian.mul_one]

theorem geometricPrefix_sub_chart (z : Gaussian) (degree : Nat)
    (denominatorNonzero : 1 - z ≠ 0) :
    eval (geometricPrefix degree) z - (1 + z) / (1 - z) =
      CCL.FiniteExp.scale (-2) (z ^ (degree + 1)) /
        (1 - z) := by
  apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne
    denominatorNonzero
  calc
    (eval (geometricPrefix degree) z - (1 + z) / (1 - z)) * (1 - z) =
        eval (geometricPrefix degree) z * (1 - z) -
          ((1 + z) / (1 - z)) * (1 - z) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [sub_re, sub_im, mul_re, mul_im] <;> ring1
    _ = eval (geometricPrefix degree) z * (1 - z) - (1 + z) := by
      rw [gaussian_div_mul_cancel _ _ denominatorNonzero]
    _ = CCL.FiniteExp.scale (-2) (z ^ (degree + 1)) := by
      rw [RFAP.ConstructiveGaussian.Gaussian.mul_comm,
        one_sub_mul_geometricPrefix]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [add_re, add_im, sub_re, sub_im] <;> ring1
    _ = (CCL.FiniteExp.scale (-2) (z ^ (degree + 1)) /
          (1 - z)) * (1 - z) :=
      (gaussian_div_mul_cancel _ _ denominatorNonzero).symm

theorem one_sub_normSq_lower {z : Gaussian} (bound : normSq z ≤ 1 / 9) :
    4 / 9 ≤ normSq (1 - z) := by
  have realSquare : z.re ^ 2 ≤ (1 / 3 : Coordinate) ^ 2 := by
    calc
      z.re ^ 2 ≤ z.re ^ 2 + z.im ^ 2 :=
        le_add_of_nonneg_right
          (RFAP.ConstructiveFraction.sq_nonneg_direct z.im)
      _ ≤ 1 / 9 := bound
      _ = (1 / 3 : Coordinate) ^ 2 := by decide
  have realUpper : z.re ≤ 1 / 3 :=
    RFAP.ConstructiveFraction.le_of_sq_le_sq_direct (by decide) realSquare
  have differenceLower : (2 / 3 : Coordinate) ≤ 1 - z.re := by
    calc
      (2 / 3 : Coordinate) = 1 - 1 / 3 := by decide
      _ ≤ 1 - z.re := RFAP.ConstructiveFraction.sub_le_sub_left_direct realUpper 1
  have differenceNonnegative : 0 ≤ 1 - z.re :=
    (show (0 : Coordinate) ≤ 2 / 3 by decide).trans differenceLower
  have squareLower := RFAP.ConstructiveFraction.pow_le_pow_direct
    (by decide : (0 : Coordinate) ≤ 2 / 3) differenceLower 2
  change (4 / 9 : Coordinate) ≤
    (1 - z.re) ^ 2 + (0 - z.im) ^ 2
  calc
    (4 / 9 : Coordinate) = (2 / 3 : Coordinate) ^ 2 := by decide
    _ ≤ (1 - z.re) ^ 2 := squareLower
    _ ≤ (1 - z.re) ^ 2 + (0 - z.im) ^ 2 :=
      le_add_of_nonneg_right
        (RFAP.ConstructiveFraction.sq_nonneg_direct (0 - z.im))

theorem one_sub_ne_zero {z : Gaussian} (bound : normSq z ≤ 1 / 9) :
    1 - z ≠ 0 := by
  intro equal
  have lower := one_sub_normSq_lower bound
  rw [equal, normSq_zero] at lower
  have : ¬(4 / 9 : Coordinate) ≤ 0 := by decide
  exact this lower

theorem localChart_sub_localChart {x y : Gaussian}
    (xBound : normSq x ≤ 1 / 9) (yBound : normSq y ≤ 1 / 9) :
    (1 + x) / (1 - x) - (1 + y) / (1 - y) =
      CCL.FiniteExp.scale 2 (x - y) /
        ((1 - x) * (1 - y)) := by
  have xNonzero := one_sub_ne_zero xBound
  have yNonzero := one_sub_ne_zero yBound
  have productNonzero :=
    RFAP.ConstructiveGaussian.Gaussian.mul_ne_zero_direct xNonzero yNonzero
  apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne
    productNonzero
  calc
    ((1 + x) / (1 - x) - (1 + y) / (1 - y)) *
          ((1 - x) * (1 - y)) =
        (((1 + x) / (1 - x)) * (1 - x)) * (1 - y) -
          (((1 + y) / (1 - y)) * (1 - y)) * (1 - x) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [sub_re, sub_im, mul_re, mul_im] <;> ring1
    _ = (1 + x) * (1 - y) - (1 + y) * (1 - x) := by
      rw [gaussian_div_mul_cancel _ _ xNonzero,
        gaussian_div_mul_cancel _ _ yNonzero]
    _ = CCL.FiniteExp.scale 2 (x - y) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [CCL.FiniteExp.scale_re,
          CCL.FiniteExp.scale_im, add_re, add_im, sub_re,
          sub_im, mul_re, mul_im, one_re, one_im] <;> ring1
    _ = (CCL.FiniteExp.scale 2 (x - y) /
          ((1 - x) * (1 - y))) * ((1 - x) * (1 - y)) :=
      (gaussian_div_mul_cancel _ _ productNonzero).symm

private theorem four_ninths_pos : (0 : Coordinate) < 4 / 9 := by
  decide

private theorem nine_mul_four_ninths :
    (9 : Coordinate) * (4 / 9) = 4 := by
  calc
    (9 : Coordinate) * (4 / 9) = (4 / 9) * 9 :=
      RFAP.ConstructiveFraction.mul_comm _ _
    _ = 4 := RFAP.ConstructiveFraction.div_mul_cancel_of_ne 4 9 (by decide)

private theorem localChartSensitivity_scalar :
    ((((9 : Coordinate) * 9) / 4) * ((4 / 9) * (4 / 9))) = 4 := by
  decide

private theorem localChartSensitivity_identity (distance : Coordinate) :
    4 * distance =
      ((((9 : Coordinate) * 9) / 4) * distance) *
        ((4 / 9) * (4 / 9)) := by
  calc
    4 * distance =
        (((((9 : Coordinate) * 9) / 4) * ((4 / 9) * (4 / 9))) *
          distance) := by rw [localChartSensitivity_scalar]
    _ = ((((9 : Coordinate) * 9) / 4) * distance) *
          ((4 / 9) * (4 / 9)) := by ring1

/-- Square-root-free Lipschitz bound for the local Möbius reconstruction on
the certified reduced disk. -/
theorem localChart_input_close {x y : Gaussian}
    (xBound : normSq x ≤ 1 / 9) (yBound : normSq y ≤ 1 / 9) :
    normSq ((1 + x) / (1 - x) - (1 + y) / (1 - y)) ≤
      (((9 : Coordinate) * 9) / 4) * normSq (x - y) := by
  have xLower := one_sub_normSq_lower xBound
  have yLower := one_sub_normSq_lower yBound
  have denominatorLower :
      (4 / 9 : Coordinate) * (4 / 9) ≤
        normSq ((1 - x) * (1 - y)) := by
    rw [normSq_mul]
    have product := RFAP.ConstructiveFraction.mul_le_mul_direct
      xLower yLower (show (0 : Coordinate) ≤ 4 / 9 by decide)
        (normSq_nonneg (1 - x))
    exact product
  have denominatorPositive :
      0 < normSq ((1 - x) * (1 - y)) := by
    exact (RFAP.ConstructiveFraction.mul_pos_direct
      four_ninths_pos four_ninths_pos).trans_le denominatorLower
  rw [localChart_sub_localChart xBound yBound,
    RFAP.ConstructiveGaussian.Gaussian.normSq_div _ _
      (RFAP.ConstructiveGaussian.Gaussian.mul_ne_zero_direct
        (one_sub_ne_zero xBound) (one_sub_ne_zero yBound)),
    CCL.FiniteExp.normSq_scale]
  rw [show (2 : Coordinate) ^ 2 = 4 by decide]
  rw [← RFAP.ExplicitField.div_eq_mul_inv]
  apply (RFAP.ConstructiveFraction.div_le_iff_pos denominatorPositive).2
  let distance := normSq (x - y)
  let coefficient := (((9 : Coordinate) * 9) / 4) * distance
  have coefficientNonnegative : 0 ≤ coefficient :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (normSq_nonneg (x - y))
  calc
    4 * normSq (x - y) = coefficient * ((4 / 9) * (4 / 9)) := by
      exact localChartSensitivity_identity distance
    _ ≤ coefficient *
          normSq ((1 - x) * (1 - y)) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        denominatorLower coefficientNonnegative

theorem scaledReduced_sub_scaledReduced (factor x y : Gaussian)
    (xDenominatorNonzero : factor * x + 1 ≠ 0)
    (yDenominatorNonzero : factor * y + 1 ≠ 0) :
    (factor * x - 1) / (factor * x + 1) -
        (factor * y - 1) / (factor * y + 1) =
      CCL.FiniteExp.scale 2 (factor * (x - y)) /
        ((factor * x + 1) * (factor * y + 1)) := by
  have productNonzero :=
    RFAP.ConstructiveGaussian.Gaussian.mul_ne_zero_direct
      xDenominatorNonzero yDenominatorNonzero
  apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne
    productNonzero
  calc
    ((factor * x - 1) / (factor * x + 1) -
          (factor * y - 1) / (factor * y + 1)) *
          ((factor * x + 1) * (factor * y + 1)) =
        (((factor * x - 1) / (factor * x + 1)) *
            (factor * x + 1)) * (factor * y + 1) -
          (((factor * y - 1) / (factor * y + 1)) *
            (factor * y + 1)) * (factor * x + 1) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [sub_re, sub_im, mul_re, mul_im] <;> ring1
    _ = (factor * x - 1) * (factor * y + 1) -
          (factor * y - 1) * (factor * x + 1) := by
      rw [gaussian_div_mul_cancel _ _ xDenominatorNonzero,
        gaussian_div_mul_cancel _ _ yDenominatorNonzero]
    _ = CCL.FiniteExp.scale 2 (factor * (x - y)) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [CCL.FiniteExp.scale_re,
          CCL.FiniteExp.scale_im, add_re, add_im, sub_re,
          sub_im, mul_re, mul_im, one_re, one_im] <;> ring1
    _ = (CCL.FiniteExp.scale 2 (factor * (x - y)) /
          ((factor * x + 1) * (factor * y + 1))) *
            ((factor * x + 1) * (factor * y + 1)) :=
      (gaussian_div_mul_cancel _ _ productNonzero).symm

/-- Exact difference between an asynchronously sampled scaled quotient and a
diagonal reduced-coordinate sample. -/
theorem asynchronousScaledReduced_sub_scaledReduced
    (factor x y z : Gaussian)
    (yDenominatorNonzero : factor * y + 1 ≠ 0)
    (zDenominatorNonzero : factor * z + 1 ≠ 0) :
    (factor * x - 1) / (factor * y + 1) -
        (factor * z - 1) / (factor * z + 1) =
      (factor * factor * z * (x - y) +
          factor * ((x - z) + (y - z))) /
        ((factor * y + 1) * (factor * z + 1)) := by
  have productNonzero :=
    RFAP.ConstructiveGaussian.Gaussian.mul_ne_zero_direct
      yDenominatorNonzero zDenominatorNonzero
  apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne
    productNonzero
  calc
    ((factor * x - 1) / (factor * y + 1) -
          (factor * z - 1) / (factor * z + 1)) *
          ((factor * y + 1) * (factor * z + 1)) =
        (((factor * x - 1) / (factor * y + 1)) *
            (factor * y + 1)) * (factor * z + 1) -
          (((factor * z - 1) / (factor * z + 1)) *
            (factor * z + 1)) * (factor * y + 1) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [sub_re, sub_im, mul_re, mul_im] <;> ring1
    _ = (factor * x - 1) * (factor * z + 1) -
          (factor * z - 1) * (factor * y + 1) := by
      rw [gaussian_div_mul_cancel _ _ yDenominatorNonzero,
        gaussian_div_mul_cancel _ _ zDenominatorNonzero]
    _ = factor * factor * z * (x - y) +
          factor * ((x - z) + (y - z)) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [add_re, add_im, sub_re, sub_im, mul_re, mul_im,
          one_re, one_im] <;> ring1
    _ = ((factor * factor * z * (x - y) +
          factor * ((x - z) + (y - z))) /
            ((factor * y + 1) * (factor * z + 1))) *
              ((factor * y + 1) * (factor * z + 1)) :=
      (gaussian_div_mul_cancel _ _ productNonzero).symm

/-- Square-root-free sensitivity bound comparing an independently sampled
numerator/denominator quotient with a diagonal reduced-coordinate sample. -/
theorem asynchronousScaledReduced_input_close
    (factor x y z : Gaussian) (lowerSq sourceBound : Coordinate)
    (lowerPositive : 0 < lowerSq)
    (yLower : lowerSq ≤ normSq (factor * y + 1))
    (zLower : lowerSq ≤ normSq (factor * z + 1))
    (zBound : normSq z ≤ sourceBound) :
    normSq
        ((factor * x - 1) / (factor * y + 1) -
          (factor * z - 1) / (factor * z + 1)) ≤
      (4 * (normSq factor * normSq factor * sourceBound + normSq factor) /
          (lowerSq * lowerSq)) *
        (normSq (x - z) + normSq (y - z)) := by
  have yPositive : 0 < normSq (factor * y + 1) :=
    lowerPositive.trans_le yLower
  have zPositive : 0 < normSq (factor * z + 1) :=
    lowerPositive.trans_le zLower
  have yNonzero : factor * y + 1 ≠ 0 := by
    intro equal
    rw [equal, normSq_zero] at yPositive
    exact (lt_irrefl _ yPositive).elim
  have zNonzero : factor * z + 1 ≠ 0 := by
    intro equal
    rw [equal, normSq_zero] at zPositive
    exact (lt_irrefl _ zPositive).elim
  let distance := normSq (x - z) + normSq (y - z)
  have distanceNonnegative : 0 ≤ distance :=
    add_nonneg (normSq_nonneg (x - z)) (normSq_nonneg (y - z))
  have reverseDistance : normSq (z - y) = normSq (y - z) := by
    have reverse : z - y = -(y - z) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [sub_re, sub_im, neg_re, neg_im] <;> ring1
    rw [reverse, normSq_neg]
  have xyBound : normSq (x - y) ≤ 2 * distance := by
    calc
      normSq (x - y) ≤
          2 * (normSq (x - z) + normSq (z - y)) :=
        normSq_sub_le_via x z y
      _ = 2 * distance := by rw [reverseDistance]
  have sumBound :
      normSq ((x - z) + (y - z)) ≤ 2 * distance :=
    normSq_add_le_two (x - z) (y - z)
  have sourceBoundNonnegative : 0 ≤ sourceBound :=
    (normSq_nonneg z).trans zBound
  let firstTerm := factor * factor * z * (x - y)
  let secondTerm := factor * ((x - z) + (y - z))
  have firstCoefficientNonnegative :
      0 ≤ normSq factor * normSq factor * normSq z :=
    RFAP.ConstructiveFraction.mul_nonneg_direct
      (RFAP.ConstructiveFraction.mul_nonneg_direct
        (normSq_nonneg factor) (normSq_nonneg factor))
      (normSq_nonneg z)
  have twiceDistanceNonnegative : 0 ≤ 2 * distance :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      distanceNonnegative
  have firstTermBound :
      normSq firstTerm ≤
        (normSq factor * normSq factor * sourceBound) *
          (2 * distance) := by
    change normSq (factor * factor * z * (x - y)) ≤ _
    rw [normSq_mul, normSq_mul, normSq_mul]
    calc
      normSq factor * normSq factor * normSq z * normSq (x - y) ≤
          (normSq factor * normSq factor * normSq z) *
            (2 * distance) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct xyBound
          firstCoefficientNonnegative
      _ ≤ (normSq factor * normSq factor * sourceBound) *
            (2 * distance) := by
        apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct _
          twiceDistanceNonnegative
        exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          zBound
          (RFAP.ConstructiveFraction.mul_nonneg_direct
            (normSq_nonneg factor) (normSq_nonneg factor))
  have secondTermBound :
      normSq secondTerm ≤ normSq factor * (2 * distance) := by
    change normSq (factor * ((x - z) + (y - z))) ≤ _
    rw [normSq_mul]
    exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      sumBound (normSq_nonneg factor)
  let numerator := firstTerm + secondTerm
  let numeratorScale :=
    4 * (normSq factor * normSq factor * sourceBound + normSq factor)
  have numeratorBound : normSq numerator ≤ numeratorScale * distance := by
    calc
      normSq numerator ≤
          2 * (normSq firstTerm + normSq secondTerm) :=
        normSq_add_le_two firstTerm secondTerm
      _ ≤ 2 *
          ((normSq factor * normSq factor * sourceBound) *
              (2 * distance) +
            normSq factor * (2 * distance)) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (add_le_add firstTermBound secondTermBound) (by decide)
      _ = numeratorScale * distance := by
        dsimp only [numeratorScale]
        ring1
  have numeratorNonnegative : 0 ≤ normSq numerator :=
    normSq_nonneg numerator
  have lowerProductPositive : 0 < lowerSq * lowerSq :=
    RFAP.ConstructiveFraction.mul_pos_direct lowerPositive lowerPositive
  have denominatorLower :
      lowerSq * lowerSq ≤
        normSq (factor * y + 1) * normSq (factor * z + 1) :=
    RFAP.ConstructiveFraction.mul_le_mul_direct
      yLower zLower lowerPositive.le (normSq_nonneg (factor * y + 1))
  have inverseNonnegative : 0 ≤ (lowerSq * lowerSq)⁻¹ :=
    (RFAP.ConstructiveFraction.inv_pos_direct lowerProductPositive).le
  rw [asynchronousScaledReduced_sub_scaledReduced factor x y z
      yNonzero zNonzero,
    RFAP.ConstructiveGaussian.Gaussian.normSq_div _ _
      (RFAP.ConstructiveGaussian.Gaussian.mul_ne_zero_direct
        yNonzero zNonzero), normSq_mul]
  change normSq numerator /
      (normSq (factor * y + 1) * normSq (factor * z + 1)) ≤ _
  calc
    normSq numerator /
          (normSq (factor * y + 1) * normSq (factor * z + 1)) ≤
        normSq numerator / (lowerSq * lowerSq) :=
      RFAP.ConstructiveFraction.div_le_div_of_nonneg_left_direct
        numeratorNonnegative lowerProductPositive denominatorLower
    _ ≤ (numeratorScale * distance) / (lowerSq * lowerSq) := by
      change normSq numerator * (lowerSq * lowerSq)⁻¹ ≤
        (numeratorScale * distance) * (lowerSq * lowerSq)⁻¹
      exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        numeratorBound inverseNonnegative
    _ = (numeratorScale / (lowerSq * lowerSq)) * distance := by
      change (numeratorScale * distance) * (lowerSq * lowerSq)⁻¹ =
        (numeratorScale * (lowerSq * lowerSq)⁻¹) * distance
      calc
        (numeratorScale * distance) * (lowerSq * lowerSq)⁻¹ =
            numeratorScale *
              (distance * (lowerSq * lowerSq)⁻¹) :=
          RFAP.ConstructiveFraction.mul_assoc _ _ _
        _ = numeratorScale *
              ((lowerSq * lowerSq)⁻¹ * distance) := by
          rw [RFAP.ConstructiveFraction.mul_comm distance
            ((lowerSq * lowerSq)⁻¹)]
        _ = (numeratorScale * (lowerSq * lowerSq)⁻¹) * distance :=
          (RFAP.ConstructiveFraction.mul_assoc _ _ _).symm

/-- Exact inverse of the scaled reduced-coordinate map on the certified local
disk. -/
theorem scaledReduced_chart (factor value : Gaussian)
    (denominatorNonzero : factor * value + 1 ≠ 0)
    (reducedBound :
      normSq ((factor * value - 1) / (factor * value + 1)) ≤ 1 / 9) :
    (1 + (factor * value - 1) / (factor * value + 1)) /
        (1 - (factor * value - 1) / (factor * value + 1)) =
      factor * value := by
  let scaled := factor * value
  let reduced := (scaled - 1) / (scaled + 1)
  have reducedIdentity : reduced * (scaled + 1) = scaled - 1 :=
    gaussian_div_mul_cancel (scaled - 1) (scaled + 1) denominatorNonzero
  have oneSubNonzero : 1 - reduced ≠ 0 :=
    one_sub_ne_zero reducedBound
  have reducedCancellation :
      (1 - reduced) * (scaled + 1) = 1 + 1 := by
    calc
      (1 - reduced) * (scaled + 1) =
          (scaled + 1) - reduced * (scaled + 1) := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [add_re, add_im, sub_re, sub_im, mul_re, mul_im,
            one_re, one_im] <;> ring1
      _ = (scaled + 1) - (scaled - 1) := by rw [reducedIdentity]
      _ = 1 + 1 := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [add_re, add_im, sub_re, sub_im, one_re, one_im] <;> ring1
  apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne
    oneSubNonzero
  rw [gaussian_div_mul_cancel (1 + reduced) (1 - reduced) oneSubNonzero]
  apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne
    denominatorNonzero
  calc
    (1 + reduced) * (scaled + 1) =
        (scaled + 1) + reduced * (scaled + 1) := by ring1
    _ = (scaled + 1) + (scaled - 1) := by rw [reducedIdentity]
    _ = scaled * (1 - reduced) * (scaled + 1) := by
      rw [RFAP.ConstructiveGaussian.Gaussian.mul_assoc, reducedCancellation]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [add_re, add_im, sub_re, sub_im, mul_re, mul_im,
          one_re, one_im] <;> ring1

/-- Finite sensitivity of the scaled reduced-coordinate map under one
displayed positive denominator-quadrance lower bound. -/
theorem scaledReduced_input_close (factor x y : Gaussian)
    (lowerSq : Coordinate) (lowerPositive : 0 < lowerSq)
    (xLower : lowerSq ≤ normSq (factor * x + 1))
    (yLower : lowerSq ≤ normSq (factor * y + 1)) :
    normSq
        ((factor * x - 1) / (factor * x + 1) -
          (factor * y - 1) / (factor * y + 1)) ≤
      ((4 * normSq factor) / (lowerSq * lowerSq)) *
        normSq (x - y) := by
  have xPositive : 0 < normSq (factor * x + 1) :=
    lowerPositive.trans_le xLower
  have yPositive : 0 < normSq (factor * y + 1) :=
    lowerPositive.trans_le yLower
  have xNonzero : factor * x + 1 ≠ 0 := by
    intro equal
    rw [equal, normSq_zero] at xPositive
    exact (lt_irrefl _ xPositive).elim
  have yNonzero : factor * y + 1 ≠ 0 := by
    intro equal
    rw [equal, normSq_zero] at yPositive
    exact (lt_irrefl _ yPositive).elim
  have lowerProductPositive : 0 < lowerSq * lowerSq :=
    RFAP.ConstructiveFraction.mul_pos_direct lowerPositive lowerPositive
  have denominatorLower :
      lowerSq * lowerSq ≤
        normSq (factor * x + 1) * normSq (factor * y + 1) := by
    exact RFAP.ConstructiveFraction.mul_le_mul_direct
      xLower yLower lowerPositive.le (normSq_nonneg (factor * x + 1))
  let numerator := 4 * normSq factor * normSq (x - y)
  have numeratorNonnegative : 0 ≤ numerator :=
    RFAP.ConstructiveFraction.mul_nonneg_direct
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (normSq_nonneg factor))
      (normSq_nonneg (x - y))
  rw [scaledReduced_sub_scaledReduced factor x y xNonzero yNonzero,
    RFAP.ConstructiveGaussian.Gaussian.normSq_div _ _
      (RFAP.ConstructiveGaussian.Gaussian.mul_ne_zero_direct
        xNonzero yNonzero),
    CCL.FiniteExp.normSq_scale, normSq_mul, normSq_mul]
  rw [show (2 : Coordinate) ^ 2 = 4 by decide]
  rw [← RFAP.ExplicitField.div_eq_mul_inv]
  calc
    4 * (normSq factor * normSq (x - y)) /
          (normSq (factor * x + 1) * normSq (factor * y + 1)) =
        numerator /
          (normSq (factor * x + 1) * normSq (factor * y + 1)) := by
      dsimp only [numerator]
      congr 1
      ring1
    _ ≤ numerator / (lowerSq * lowerSq) :=
      RFAP.ConstructiveFraction.div_le_div_of_nonneg_left_direct
        numeratorNonnegative lowerProductPositive denominatorLower
    _ = ((4 * normSq factor) / (lowerSq * lowerSq)) *
          normSq (x - y) := by
      rw [RFAP.ExplicitField.div_eq_mul_inv,
        RFAP.ExplicitField.div_eq_mul_inv]
      dsimp only [numerator]
      calc
        (4 * normSq factor * normSq (x - y)) *
              (lowerSq * lowerSq)⁻¹ =
            (4 * normSq factor) *
              (normSq (x - y) * (lowerSq * lowerSq)⁻¹) :=
          RFAP.ConstructiveFraction.mul_assoc _ _ _
        _ = (4 * normSq factor) *
              ((lowerSq * lowerSq)⁻¹ * normSq (x - y)) := by
          rw [RFAP.ConstructiveFraction.mul_comm
            (normSq (x - y)) ((lowerSq * lowerSq)⁻¹)]
        _ = ((4 * normSq factor) * (lowerSq * lowerSq)⁻¹) *
              normSq (x - y) :=
          (RFAP.ConstructiveFraction.mul_assoc _ _ _).symm

theorem geometricPrefix_chart_error {z : Gaussian}
    (bound : normSq z ≤ 1 / 9) (degree : Nat) :
    normSq (eval (geometricPrefix degree) z - (1 + z) / (1 - z)) ≤
      9 * (1 / 9 : Coordinate) ^ (degree + 1) := by
  let denominator := 1 - z
  have denominatorLower : (4 / 9 : Coordinate) ≤ normSq denominator :=
    one_sub_normSq_lower bound
  have denominatorPositive : 0 < normSq denominator :=
    (by decide : (0 : Coordinate) < 4 / 9).trans_le denominatorLower
  rw [geometricPrefix_sub_chart z degree (one_sub_ne_zero bound),
    RFAP.ConstructiveGaussian.Gaussian.normSq_div _ _
      (one_sub_ne_zero bound),
    CCL.FiniteExp.normSq_scale,
    RFAP.ConstructiveGaussian.Gaussian.normSq_pow]
  rw [show ((-2 : Coordinate) ^ 2) = 4 by decide]
  apply (RFAP.ConstructiveFraction.div_le_iff_pos denominatorPositive).mpr
  have powerBound := RFAP.ConstructiveFraction.pow_le_pow_direct
    (normSq_nonneg z) bound (degree + 1)
  calc
    4 * normSq z ^ (degree + 1) ≤
        4 * (1 / 9 : Coordinate) ^ (degree + 1) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct powerBound
        (by decide)
    _ = (9 * (1 / 9 : Coordinate) ^ (degree + 1)) * (4 / 9) := by
      calc
        4 * (1 / 9 : Coordinate) ^ (degree + 1) =
            (1 / 9 : Coordinate) ^ (degree + 1) * 4 := by ring1
        _ = (1 / 9 : Coordinate) ^ (degree + 1) *
              (9 * (4 / 9)) := by
          rw [show (9 : Coordinate) * (4 / 9) = 4 by decide]
        _ = (9 * (1 / 9 : Coordinate) ^ (degree + 1)) * (4 / 9) := by
          ring1
    _ ≤ (9 * (1 / 9 : Coordinate) ^ (degree + 1)) *
          normSq denominator :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        denominatorLower
        (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
          (RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) _))

theorem scalarEvalCoefficients_drop_scaled_le {radius : Coordinate}
    (radiusNonnegative : 0 ≤ radius) : ∀ coefficients count,
    (∀ degree, 0 ≤ coefficientCoefficients coefficients degree) →
      radius ^ count *
          scalarEvalCoefficients radius (coefficients.drop count) ≤
        scalarEvalCoefficients radius coefficients
  | coefficients, 0, coefficientsNonnegative => by
      rw [List.drop_zero, pow_zero,
        RFAP.ConstructiveFraction.one_mul]
  | [], count + 1, coefficientsNonnegative => by
      change radius ^ (count + 1) * 0 ≤ 0
      rw [RFAP.ConstructiveFraction.mul_zero_direct]
  | coefficient :: remaining, count + 1, coefficientsNonnegative => by
      rw [List.drop_succ_cons, pow_succ, scalarEvalCoefficients]
      have tailBound := scalarEvalCoefficients_drop_scaled_le
        radiusNonnegative remaining count
        (fun degree => coefficientsNonnegative (degree + 1))
      calc
        radius ^ count * radius *
            scalarEvalCoefficients radius (remaining.drop count) =
          radius *
            (radius ^ count *
              scalarEvalCoefficients radius (remaining.drop count)) := by
            ring1
        _ ≤ radius * scalarEvalCoefficients radius remaining :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            tailBound radiusNonnegative
        _ ≤ coefficient + radius * scalarEvalCoefficients radius remaining :=
          le_add_of_nonneg_left (coefficientsNonnegative 0)

theorem coefficientCoefficients_drop : ∀ count coefficients degree,
    coefficientCoefficients (coefficients.drop count) degree =
      coefficientCoefficients coefficients (count + degree)
  | 0, coefficients, degree => by rw [List.drop_zero, Nat.zero_add]
  | count + 1, [], degree => by
      rw [List.drop_nil, coefficientCoefficients_nil,
        coefficientCoefficients_nil]
  | count + 1, coefficient :: remaining, degree => by
      rw [List.drop_succ_cons,
        coefficientCoefficients_drop count remaining degree]
      rw [show count + 1 + degree = (count + degree) + 1 by ring1,
        coefficientCoefficients_cons_succ]

theorem evalCoefficients_zero_of_coefficients_zero (z : Gaussian) :
    ∀ coefficients,
      (∀ degree, coefficientCoefficients coefficients degree = 0) →
        evalCoefficients z coefficients = 0
  | [], allZero => rfl
  | coefficient :: remaining, allZero => by
      have headZero : coefficient = 0 := allZero 0
      have tailZero :
          ∀ degree, coefficientCoefficients remaining degree = 0 := by
        intro degree
        exact allZero (degree + 1)
      subst coefficient
      rw [evalCoefficients,
        evalCoefficients_zero_of_coefficients_zero z remaining tailZero]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [CCL.FiniteExp.scale_re,
          CCL.FiniteExp.scale_im, add_re, add_im, mul_re, mul_im,
          zero_re, zero_im, one_re, one_im] <;> ring1

theorem geometricPrefix_eval_eq_prefix (z : Gaussian) (degree : Nat) :
    eval (geometricPrefix degree) z =
      prefixEval z (geometricPrefix degree) (degree + 1) := by
  rw [eval_split]
  have tailZero :
      eval
        ⟨(geometricPrefix degree).coefficients.drop (degree + 1)⟩ z = 0 := by
    apply evalCoefficients_zero_of_coefficients_zero
    intro tailDegree
    rw [coefficientCoefficients_drop]
    change coefficient (geometricPrefix degree) (degree + 1 + tailDegree) = 0
    rw [geometricPrefix_coefficient, if_neg (by omega), if_neg (by omega)]
  rw [tailZero]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [add_re, add_im, mul_re, mul_im, zero_re, zero_im] <;> ring1

theorem exponentialLocalLog_sub_prefix (z : Gaussian) (depth : Nat) :
    eval (exponentialLocalLog (2 * depth + 2) depth) z -
        eval (geometricPrefix (2 * depth + 2)) z =
      z ^ (2 * depth + 3) *
        eval
          ⟨(exponentialLocalLog (2 * depth + 2) depth).coefficients.drop
            (2 * depth + 3)⟩ z := by
  rw [eval_split z (exponentialLocalLog (2 * depth + 2) depth)
      (2 * depth + 3),
    prefixEval_congr
      (exponentialLocalLog_equalBelow_geometricPrefix depth) z,
    ← geometricPrefix_eval_eq_prefix z (2 * depth + 2)]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [add_re, add_im, sub_re, sub_im] <;> ring1

theorem highTail_power_identity (count : Nat) (tail : Coordinate) :
    (1 / 9 : Coordinate) ^ count * (2 * tail ^ 2) =
      2 * (4 / 9 : Coordinate) ^ count *
        (((1 / 2 : Coordinate) ^ count * tail) ^ 2) := by
  have halfSquare :
      ((1 / 2 : Coordinate) ^ count) ^ 2 =
        (1 / 4 : Coordinate) ^ count := by
    rw [pow_two, ← mul_pow]
    congr 1
  calc
    (1 / 9 : Coordinate) ^ count * (2 * tail ^ 2) =
        2 * (1 / 9 : Coordinate) ^ count * tail ^ 2 := by ring1
    _ = 2 * (((4 / 9 : Coordinate) * (1 / 4)) ^ count) *
          tail ^ 2 := by
      rw [show (4 / 9 : Coordinate) * (1 / 4) = 1 / 9 by decide]
    _ = 2 * ((4 / 9 : Coordinate) ^ count *
          (1 / 4 : Coordinate) ^ count) * tail ^ 2 := by
      rw [mul_pow]
    _ = 2 * (4 / 9 : Coordinate) ^ count *
          (((1 / 2 : Coordinate) ^ count) ^ 2 * tail ^ 2) := by
      rw [halfSquare]
      ring1
    _ = 2 * (4 / 9 : Coordinate) ^ count *
          (((1 / 2 : Coordinate) ^ count * tail) ^ 2) := by ring1

theorem exponentialLocalLog_highTail_bound {z : Gaussian}
    (zBound : normSq z ≤ 1 / 9) (depth : Nat) :
    normSq
      (eval (exponentialLocalLog (2 * depth + 2) depth) z -
        eval (geometricPrefix (2 * depth + 2)) z) ≤
      (5 * 10) * (4 / 9 : Coordinate) ^ (2 * depth + 3) := by
  let polynomial := exponentialLocalLog (2 * depth + 2) depth
  let count := 2 * depth + 3
  let tail : Polynomial := ⟨polynomial.coefficients.drop count⟩
  let tailMagnitude := scalarEval (1 / 2) tail
  let fullMagnitude := scalarEval (1 / 2) polynomial
  have polynomialNonnegative : CoefficientsNonnegative polynomial :=
    coefficientsNonnegative_exponentialLocalLog _ _
  have tailNonnegative : CoefficientsNonnegative tail := by
    intro degree
    change 0 ≤ coefficientCoefficients (polynomial.coefficients.drop count) degree
    rw [coefficientCoefficients_drop]
    exact polynomialNonnegative (count + degree)
  have tailMagnitudeNonnegative : 0 ≤ tailMagnitude :=
    scalarEvalCoefficients_nonnegative (by decide) tail.coefficients
      tailNonnegative
  have fullMagnitudeNonnegative : 0 ≤ fullMagnitude :=
    scalarEvalCoefficients_nonnegative (by decide) polynomial.coefficients
      polynomialNonnegative
  have fullMagnitudeBound : fullMagnitude ≤ 5 :=
    scalarEval_exponentialLocalLog_half_le_five _ _
  have scaledTailBound :
      (1 / 2 : Coordinate) ^ count * tailMagnitude ≤ fullMagnitude := by
    exact scalarEvalCoefficients_drop_scaled_le (by decide)
      polynomial.coefficients count polynomialNonnegative
  have scaledTailNonnegative :
      0 ≤ (1 / 2 : Coordinate) ^ count * tailMagnitude :=
    RFAP.ConstructiveFraction.mul_nonneg_direct
      (RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) count)
      tailMagnitudeNonnegative
  have scaledTailSquare :
      (((1 / 2 : Coordinate) ^ count * tailMagnitude) ^ 2) ≤
        fullMagnitude ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct scaledTailNonnegative
      scaledTailBound 2
  have fullMagnitudeSquare : fullMagnitude ^ 2 ≤ 25 := by
    have square := RFAP.ConstructiveFraction.pow_le_pow_direct
      fullMagnitudeNonnegative fullMagnitudeBound 2
    simpa only [show (5 : Coordinate) ^ 2 = 25 by decide] using square
  rw [exponentialLocalLog_sub_prefix z depth,
    normSq_mul, RFAP.ConstructiveGaussian.Gaussian.normSq_pow]
  have tailNorm := eval_normSq_le_scalarHalf tailNonnegative zBound
  calc
    normSq z ^ count * normSq (eval tail z) ≤
        (1 / 9 : Coordinate) ^ count * (2 * tailMagnitude ^ 2) :=
      RFAP.ConstructiveFraction.mul_le_mul_direct
        (RFAP.ConstructiveFraction.pow_le_pow_direct
          (normSq_nonneg z) zBound count)
        tailNorm (normSq_nonneg _)
        (RFAP.ConstructiveFraction.pow_nonneg_direct
          (by decide : (0 : Coordinate) ≤ 1 / 9) count)
    _ = 2 * (4 / 9 : Coordinate) ^ count *
          (((1 / 2 : Coordinate) ^ count * tailMagnitude) ^ 2) :=
      highTail_power_identity count tailMagnitude
    _ ≤ 2 * (4 / 9 : Coordinate) ^ count * fullMagnitude ^ 2 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        scaledTailSquare
        (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
          (RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) count))
    _ ≤ 2 * (4 / 9 : Coordinate) ^ count * 25 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        fullMagnitudeSquare
        (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
          (RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) count))
    _ = (5 * 10) * (4 / 9 : Coordinate) ^ (2 * depth + 3) := by
      dsimp only [count]
      ring1

theorem fourNinth_depth_bound : ∀ depth,
    (4 / 9 : Coordinate) ^ (2 * depth + 3) ≤
      (1 / 4 : Coordinate) ^ depth
  | 0 => by decide
  | depth + 1 => by
      rw [show 2 * (depth + 1) + 3 = (2 * depth + 3) + 2 by ring1,
        pow_add, pow_succ]
      calc
        (4 / 9 : Coordinate) ^ (2 * depth + 3) *
            ((4 / 9 : Coordinate) ^ 1 * (4 / 9)) ≤
          (1 / 4 : Coordinate) ^ depth * (1 / 4) :=
        RFAP.ConstructiveFraction.mul_le_mul_direct
          (fourNinth_depth_bound depth) (by decide)
          (RFAP.ConstructiveFraction.mul_nonneg_direct
            (RFAP.ConstructiveFraction.pow_nonneg_direct
              (by decide : (0 : Coordinate) ≤ 4 / 9) 1)
            (by decide : (0 : Coordinate) ≤ 4 / 9))
          (RFAP.ConstructiveFraction.pow_nonneg_direct
            (by decide : (0 : Coordinate) ≤ 1 / 4) depth)
        _ = (1 / 4 : Coordinate) ^ (depth + 1) := (pow_succ _ _).symm

def expLogErrorScale : Coordinate := 2 * (5 * 10 + 3 * 3)

theorem expLogErrorScale_nonnegative : 0 ≤ expLogErrorScale :=
  RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
    (add_nonneg
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide) (by decide))
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide) (by decide)))

theorem exponentialLocalLog_chart_error {z : Gaussian}
    (zBound : normSq z ≤ 1 / 9) (depth : Nat) :
    normSq
      (eval (exponentialLocalLog (2 * depth + 2) depth) z -
        (1 + z) / (1 - z)) ≤
      expLogErrorScale * (1 / 4 : Coordinate) ^ depth := by
  let polynomialValue :=
    eval (exponentialLocalLog (2 * depth + 2) depth) z
  let prefixValue := eval (geometricPrefix (2 * depth + 2)) z
  let chartValue := (1 + z) / (1 - z)
  have split : polynomialValue - chartValue =
      (polynomialValue - prefixValue) + (prefixValue - chartValue) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [add_re, add_im, sub_re, sub_im] <;> ring1
  rw [split]
  have highBound := exponentialLocalLog_highTail_bound zBound depth
  have chartBound := geometricPrefix_chart_error zBound (2 * depth + 2)
  have ninthToFour :
      (1 / 9 : Coordinate) ^ (2 * depth + 3) ≤
        (4 / 9 : Coordinate) ^ (2 * depth + 3) :=
    RFAP.ConstructiveFraction.pow_le_pow_direct (by decide) (by decide) _
  calc
    normSq ((polynomialValue - prefixValue) +
        (prefixValue - chartValue)) ≤
      2 * (normSq (polynomialValue - prefixValue) +
        normSq (prefixValue - chartValue)) := normSq_add_le_two _ _
    _ ≤ 2 *
        ((5 * 10) * (4 / 9 : Coordinate) ^ (2 * depth + 3) +
          9 * (1 / 9 : Coordinate) ^ (2 * depth + 3)) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add highBound chartBound) (by decide)
    _ ≤ 2 *
        ((5 * 10) * (4 / 9 : Coordinate) ^ (2 * depth + 3) +
          9 * (4 / 9 : Coordinate) ^ (2 * depth + 3)) := by
      apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct _
        (by decide)
      exact add_le_add le_rfl
        (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          ninthToFour (by decide))
    _ = expLogErrorScale *
          (4 / 9 : Coordinate) ^ (2 * depth + 3) := by
      rw [show (9 : Coordinate) = 3 * 3 by decide]
      dsimp only [expLogErrorScale]
      ring1
    _ ≤ expLogErrorScale * (1 / 4 : Coordinate) ^ depth :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (fourNinth_depth_bound depth)
        expLogErrorScale_nonnegative

/-! ## Operational local inverse -/

def localExpLogSample (z : Gaussian) (depth : Nat) : Gaussian :=
  CCL.FiniteExp.sample
    (CCL.FiniteComplexLog.sample z depth) (2 * depth + 1)

theorem localExpLogSample_eq_eval (z : Gaussian) (depth : Nat) :
    localExpLogSample z depth =
      eval (exponentialLocalLog (2 * depth + 2) depth) z := by
  rw [localExpLogSample,
    CCL.TranscendentalLaws.sample_eq_truncatedExp,
    eval_exponentialLocalLog]

theorem localExpLogSample_chart_error {z : Gaussian}
    (zBound : normSq z ≤ 1 / 9) (depth : Nat) :
    normSq (localExpLogSample z depth - (1 + z) / (1 - z)) ≤
      expLogErrorScale * (1 / 4 : Coordinate) ^ depth := by
  rw [localExpLogSample_eq_eval]
  exact exponentialLocalLog_chart_error zBound depth

theorem quarterPower_antitone {earlier later : Nat} (order : earlier ≤ later) :
    (1 / 4 : Coordinate) ^ later ≤ (1 / 4 : Coordinate) ^ earlier := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le order
  rw [pow_add]
  have extraLe : (1 / 4 : Coordinate) ^ extra ≤ 1 := by
    have powerOrder := RFAP.ConstructiveFraction.pow_le_pow_direct
      (by decide : (0 : Coordinate) ≤ 1 / 4)
      (by decide : (1 / 4 : Coordinate) ≤ 1) extra
    simpa only [one_pow] using powerOrder
  calc
    (1 / 4 : Coordinate) ^ earlier * (1 / 4 : Coordinate) ^ extra ≤
        (1 / 4 : Coordinate) ^ earlier * 1 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct extraLe
        (RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) earlier)
    _ = (1 / 4 : Coordinate) ^ earlier := by ring1

def localExpLogApproximationScale : Coordinate := 4 * expLogErrorScale

theorem localExpLogApproximationScale_nonnegative :
    0 ≤ localExpLogApproximationScale :=
  RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
    expLogErrorScale_nonnegative

theorem localExpLogSample_bounded {z : Gaussian}
    (zBound : normSq z ≤ 1 / 9) (depth : Nat) :
    normSq (localExpLogSample z depth) ≤ 5 * 10 := by
  rw [localExpLogSample_eq_eval]
  let polynomial := exponentialLocalLog (2 * depth + 2) depth
  have polynomialNonnegative : CoefficientsNonnegative polynomial :=
    coefficientsNonnegative_exponentialLocalLog _ _
  have magnitudeNonnegative : 0 ≤ scalarEval (1 / 2) polynomial :=
    scalarEvalCoefficients_nonnegative (by decide) polynomial.coefficients
      polynomialNonnegative
  have magnitudeBound : scalarEval (1 / 2) polynomial ≤ 5 :=
    scalarEval_exponentialLocalLog_half_le_five _ _
  have magnitudeSquare := RFAP.ConstructiveFraction.pow_le_pow_direct
    magnitudeNonnegative magnitudeBound 2
  calc
    normSq (eval polynomial z) ≤
        2 * scalarEval (1 / 2) polynomial ^ 2 :=
      eval_normSq_le_scalarHalf polynomialNonnegative zBound
    _ ≤ 2 * (5 : Coordinate) ^ 2 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        magnitudeSquare (by decide)
    _ = 5 * 10 := by decide

def localExpLogApproximation (z : Gaussian)
    (zBound : normSq z ≤ 1 / 9) : Approximation where
  sample := localExpLogSample z
  radiusSq := fun depth =>
    CCL.FiniteGeometric.quarterRadius
      localExpLogApproximationScale depth
  radiusSq_nonneg := fun depth =>
    CCL.FiniteGeometric.quarterRadius_nonneg
      localExpLogApproximationScale_nonnegative depth
  later_close := by
    intro earlier later order
    let chart := (1 + z) / (1 - z)
    have laterError := localExpLogSample_chart_error zBound later
    have earlierError := localExpLogSample_chart_error zBound earlier
    have earlierError' :
        normSq (chart - localExpLogSample z earlier) ≤
          expLogErrorScale * (1 / 4 : Coordinate) ^ earlier := by
      have identity : chart - localExpLogSample z earlier =
          -(localExpLogSample z earlier - chart) := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [sub_re, sub_im, neg_re, neg_im] <;> ring1
      rw [identity, normSq_neg]
      exact earlierError
    have laterScaled :
        expLogErrorScale * (1 / 4 : Coordinate) ^ later ≤
          expLogErrorScale * (1 / 4 : Coordinate) ^ earlier :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (quarterPower_antitone order) expLogErrorScale_nonnegative
    calc
      normSq (localExpLogSample z later - localExpLogSample z earlier) ≤
          2 * (normSq (localExpLogSample z later - chart) +
            normSq (chart - localExpLogSample z earlier)) :=
        normSq_sub_le_via _ chart _
      _ ≤ 2 *
          (expLogErrorScale * (1 / 4 : Coordinate) ^ earlier +
            expLogErrorScale * (1 / 4 : Coordinate) ^ earlier) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (add_le_add (laterError.trans laterScaled) earlierError') (by decide)
      _ = CCL.FiniteGeometric.quarterRadius
          localExpLogApproximationScale earlier := by
        rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
        dsimp only [localExpLogApproximationScale]
        ring1
  refineIndex := fun current target positive =>
    CCL.FiniteGeometric.firstQuarterBelow
      localExpLogApproximationScale current target
  refineIndex_ge := by
    intro current target positive
    exact CCL.FiniteGeometric.firstQuarterBelow_ge
      localExpLogApproximationScale current target
  refineIndex_accurate := by
    intro current target positive
    exact CCL.FiniteGeometric.firstQuarterBelow_accurate
      localExpLogApproximationScale localExpLogApproximationScale_nonnegative
        current target positive
  centerBound := 5 * 10
  centerBound_nonneg :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide) (by decide)
  sample_bounded := localExpLogSample_bounded zBound

def localChartApproximation (z : Gaussian) : Approximation :=
  CCL.TranscendentalLaws.constantApproximation
    ((1 + z) / (1 - z))

/-- Finite operational form of
`exp(2(z + z^3/3 + ...)) = (1+z)/(1-z)` on the displayed local disk. -/
def local_exp_log_equivalent (z : Gaussian) (zBound : normSq z ≤ 1 / 9) :
    Equivalent (localExpLogApproximation z zBound)
      (localChartApproximation z) where
  compare := by
    intro leftStart rightStart target positive
    let leftIndex := CCL.FiniteGeometric.firstQuarterBelow
      expLogErrorScale leftStart target
    have leftSmall :
        expLogErrorScale * (1 / 4 : Coordinate) ^ leftIndex < target := by
      simpa only [CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
        using CCL.FiniteGeometric.firstQuarterBelow_accurate
          expLogErrorScale expLogErrorScale_nonnegative leftStart target positive
    exact
      { leftIndex := leftIndex
        rightIndex := rightStart
        left_ge := CCL.FiniteGeometric.firstQuarterBelow_ge
          expLogErrorScale leftStart target
        right_ge := Nat.le_refl _
        close := by
          intro leftLater rightLater leftOrder rightOrder
          change normSq
            (localExpLogSample z leftLater - (1 + z) / (1 - z)) < target
          exact (localExpLogSample_chart_error zBound leftLater).trans_lt
            ((RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              (quarterPower_antitone leftOrder)
              expLogErrorScale_nonnegative).trans_lt leftSmall) }

end CCL.FinitePolynomial
