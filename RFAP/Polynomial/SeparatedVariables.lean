import mathlib.Data.ConstructiveList
import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import mathlib.RFAP.ConstructiveFiniteRoots
import mathlib.RFAP.ConstructivePolynomialMatrixLeading

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

namespace RFAP.SeparatedVariables

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial :=
  RFAP.ComputablePolynomial.DensePolynomial Gaussian
abbrev ParameterPolynomial :=
  RFAP.ComputablePolynomial.DensePolynomial Gaussian
abbrev Bivariate := RFAP.ConstructiveBivariate.Bivariate Gaussian

open RFAP.ConstructiveGaussian.Gaussian
open RFAP.ComputablePolynomial.DensePolynomial
open RFAP.ConstructivePolynomialLeading

/-- A normalized dense constant, including the zero constant. -/
def parameterConstant (a : Gaussian) : ParameterPolynomial :=
  if a = 0 then 0 else constant a

@[simp] theorem eval_parameterConstant (a t : Gaussian) :
    (parameterConstant a).eval t = a := by
  rw [parameterConstant]
  split
  · rename_i zero
    rw [zero, eval_zero]
  · exact eval_constant a t

@[simp] theorem parameterConstant_zero :
    parameterConstant (0 : Gaussian) = 0 := by
  simp [parameterConstant]

theorem parameterConstant_atMost (a : Gaussian) :
    DegreeAtMost (parameterConstant a) 0 := by
  by_cases zero : a = 0
  · rw [parameterConstant, if_pos zero]
    exact DegreeAtMost.zero 0
  · rw [parameterConstant, if_neg zero]
    exact (LeadingTerm.constant zero).atMost

theorem parameterConstant_leading {a : Gaussian} (nonzero : a ≠ 0) :
    LeadingTerm (parameterConstant a) 0 a := by
  rw [parameterConstant, if_neg nonzero]
  exact LeadingTerm.constant nonzero

/-- The parameter polynomial `2T`. -/
def twiceParameter : ParameterPolynomial := ⟨[2, 0]⟩

theorem twiceParameter_leading :
    LeadingTerm twiceParameter 1 (2 : Gaussian) := by
  have twoNonzero : (2 : Gaussian) ≠ 0 := by decide
  refine
    { normalized := ?_
      nonzero := ?_
      degree_eq := ?_
      coefficient_eq := ?_ }
  · apply RFAP.ComputablePolynomial.DensePolynomial.ext
    change ([2, 0] : List Gaussian).dropWhile (· = 0) = [2, 0]
    rw [List.dropWhile_cons_of_neg (by simp [twoNonzero])]
  · change (([2, 0] : List Gaussian).dropWhile (· = 0)).isEmpty = false
    rw [List.dropWhile_cons_of_neg (by simp [twoNonzero])]
    rfl
  · change (([2, 0] : List Gaussian).dropWhile (· = 0)).length - 1 = 1
    rw [List.dropWhile_cons_of_neg (by simp [twoNonzero])]
    rfl
  · change (([2, 0] : List Gaussian).dropWhile (· = 0)).headD 0 = 2
    rw [List.dropWhile_cons_of_neg (by simp [twoNonzero])]
    rfl

def twiceShift (p : ParameterPolynomial) : ParameterPolynomial :=
  twiceParameter * p

@[simp] theorem eval_twiceShift (p : ParameterPolynomial) (t : Gaussian) :
    (twiceShift p).eval t = 2 * t * p.eval t := by
  rw [twiceShift, eval_mul]
  change ((⟨[2, 0]⟩ : ParameterPolynomial).eval t) * p.eval t = _
  simp [eval, evalCoeffs]

/-- Remaining low coefficients after the new constant coefficient. -/
def reflectedTailStep (previous : ParameterPolynomial) :
    List ParameterPolynomial → List ParameterPolynomial
  | [] => [-previous]
  | current :: remaining =>
      (twiceShift current - previous) ::
        reflectedTailStep current remaining

/-- One Horner step for substitution by `2T-U`, in low-to-high `U`
coefficients. -/
def reflectedStep (coefficients : List ParameterPolynomial)
    (coefficient : Gaussian) : List ParameterPolynomial :=
  match coefficients with
  | [] => [parameterConstant (conj coefficient)]
  | head :: tail =>
      (twiceShift head - parameterConstant (-conj coefficient)) ::
        reflectedTailStep head tail

/-- Evaluate a low-to-high outer coefficient list. -/
def evalLow (coefficients : List ParameterPolynomial)
    (outer parameter : Gaussian) : Gaussian :=
  coefficients.reverse.foldl
    (fun value coefficient => value * outer + coefficient.eval parameter) 0

theorem evalLow_cons (coefficient : ParameterPolynomial)
    (remaining : List ParameterPolynomial) (outer parameter : Gaussian) :
    evalLow (coefficient :: remaining) outer parameter =
      coefficient.eval parameter + outer * evalLow remaining outer parameter := by
  unfold evalLow
  rw [List.reverse_cons, QuotientFreeList.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

private theorem reflectedTailRingIdentity {R : Type} [CommRing R]
    (two parameter coefficient previous outer remaining : R) :
    two * parameter * coefficient - previous +
        outer * ((two * parameter - outer) * remaining - coefficient) =
      (two * parameter - outer) * (coefficient + outer * remaining) -
        previous := by
  ring1

private theorem reflectedStepRingIdentity {R : Type} [CommRing R]
    (two parameter head coefficient outer remaining : R) :
    two * parameter * head - -coefficient +
        outer * ((two * parameter - outer) * remaining - head) =
      (head + outer * remaining) * (two * parameter - outer) +
        coefficient := by
  ring1

private theorem evalLow_reflectedTailStep (previous : ParameterPolynomial)
    (coefficients : List ParameterPolynomial) (outer parameter : Gaussian) :
    evalLow (reflectedTailStep previous coefficients) outer parameter =
      (2 * parameter - outer) * evalLow coefficients outer parameter -
        previous.eval parameter := by
  induction coefficients generalizing previous with
  | nil =>
      rw [reflectedTailStep, evalLow_cons]
      simp [evalLow]
  | cons coefficient remaining inductionHypothesis =>
      rw [reflectedTailStep, evalLow_cons, eval_sub, eval_twiceShift,
        inductionHypothesis, evalLow_cons]
      exact reflectedTailRingIdentity 2 parameter
        (coefficient.eval parameter) (previous.eval parameter) outer
        (evalLow remaining outer parameter)

theorem evalLow_reflectedStep (coefficients : List ParameterPolynomial)
    (coefficient outer parameter : Gaussian) :
    evalLow (reflectedStep coefficients coefficient) outer parameter =
      evalLow coefficients outer parameter * (2 * parameter - outer) +
        conj coefficient := by
  cases coefficients with
  | nil =>
      rw [reflectedStep, evalLow_cons, eval_parameterConstant]
      simp [evalLow]
  | cons head tail =>
      rw [reflectedStep, evalLow_cons, eval_sub, eval_twiceShift,
        eval_parameterConstant, evalLow_reflectedTailStep, evalLow_cons]
      exact reflectedStepRingIdentity 2 parameter (head.eval parameter)
        (conj coefficient) outer (evalLow tail outer parameter)

private theorem evalLow_foldl_reflectedStep (outer parameter : Gaussian) :
    ∀ (coefficients : List Gaussian)
      (state : List ParameterPolynomial) (value : Gaussian),
      evalLow state outer parameter = value →
      evalLow (coefficients.foldl reflectedStep state) outer parameter =
        coefficients.foldl
          (fun accumulator coefficient =>
            accumulator * (2 * parameter - outer) + conj coefficient)
          value
  | [], _, _, stateEvaluation => stateEvaluation
  | coefficient :: remaining, state, value, stateEvaluation => by
      simp only [List.foldl_cons]
      apply evalLow_foldl_reflectedStep outer parameter remaining
      rw [evalLow_reflectedStep, stateEvaluation]

private theorem conj_evalFold (argument : Gaussian) :
    ∀ (coefficients : List Gaussian) (accumulator : Gaussian),
      conj (coefficients.foldl
        (fun value coefficient => value * conj argument + coefficient)
        accumulator) =
      coefficients.foldl
        (fun value coefficient => value * argument + conj coefficient)
        (conj accumulator)
  | [], _ => rfl
  | coefficient :: remaining, accumulator => by
      simp only [List.foldl_cons]
      rw [conj_evalFold argument remaining]
      apply congrArg (fun initial => remaining.foldl
        (fun value next => value * argument + conj next) initial)
      rw [conj_add, conj_mul, conj_conj]

/-! ## Finite leading-term invariant -/

structure ReflectedShape (coefficients : List ParameterPolynomial)
    (degree : Nat) (leading : Gaussian) : Prop where
  length_eq : coefficients.length = degree + 1
  headLeading : LeadingTerm (coefficients.headD 0) degree leading
  tailBelow : ∀ coefficient ∈ coefficients.tail,
    DegreeBelow coefficient degree

namespace ReflectedShape

/-- Transport a finite reflected-shape certificate across its three
displayed parameters without generated congruence for the predicate. -/
theorem of_equal {coefficients otherCoefficients : List ParameterPolynomial}
    {degree otherDegree : Nat} {leading otherLeading : Gaussian}
    (coefficientsEqual : coefficients = otherCoefficients)
    (degreeEqual : degree = otherDegree)
    (leadingEqual : leading = otherLeading)
    (shape : ReflectedShape otherCoefficients otherDegree otherLeading) :
    ReflectedShape coefficients degree leading := by
  cases coefficientsEqual
  cases degreeEqual
  cases leadingEqual
  exact shape

end ReflectedShape

private theorem reflectedTailStep_length (previous : ParameterPolynomial) :
    ∀ coefficients : List ParameterPolynomial,
      (reflectedTailStep previous coefficients).length =
        coefficients.length + 1
  | [] => rfl
  | _ :: remaining => by
      simp only [reflectedTailStep, List.length_cons]
      rw [reflectedTailStep_length]

private theorem reflectedTailStep_below
    {degree : Nat} {previous : ParameterPolynomial}
    (previousBound : DegreeAtMost previous degree) :
    ∀ coefficients : List ParameterPolynomial,
      (∀ coefficient ∈ coefficients, DegreeBelow coefficient degree) →
      ∀ output ∈ reflectedTailStep previous coefficients,
        DegreeBelow output (degree + 1)
  | [], _, output, membership => by
      simp only [reflectedTailStep, List.mem_singleton] at membership
      subst output
      exact DegreeBelow.neg previousBound.toBelowSucc
  | current :: remaining, bounded, output, membership => by
      simp only [reflectedTailStep, List.mem_cons] at membership
      rcases membership with first | later
      · subst output
        apply DegreeBelow.sub
        · exact DegreeBelow.mono
            (DegreeBelow.atMostMul twiceParameter_leading.atMost
              (bounded current List.mem_cons_self))
            (Nat.add_comm 1 degree).le
        · exact previousBound.toBelowSucc
      · exact reflectedTailStep_below
          (bounded current (List.mem_cons_self)).toAtMost remaining
          (fun coefficient member => bounded coefficient
            (List.mem_cons_of_mem _ member)) output later

theorem reflectedStep_shape
    {coefficients : List ParameterPolynomial} {degree : Nat}
    {leading : Gaussian} (shape : ReflectedShape coefficients degree leading)
    (coefficient : Gaussian) :
    ReflectedShape (reflectedStep coefficients coefficient) (degree + 1)
      (2 * leading) := by
  cases coefficients with
  | nil =>
      have impossible : 0 = degree + 1 := shape.length_eq
      change 0 = Nat.succ degree at impossible
      exact Nat.noConfusion impossible
  | cons head tail =>
      have headLeading : LeadingTerm head degree leading :=
        shape.headLeading
      have headBound := headLeading.atMost
      have tailBound : ∀ polynomial ∈ tail,
          DegreeBelow polynomial degree := shape.tailBelow
      refine
        { length_eq := ?_
          headLeading := ?_
          tailBelow := ?_ }
      · simp only [reflectedStep, List.length_cons,
          reflectedTailStep_length]
        simpa only [List.length_cons] using congrArg Nat.succ shape.length_eq
      · change LeadingTerm
          (twiceShift head - parameterConstant (-conj coefficient))
          (degree + 1) (2 * leading)
        apply LeadingTerm.subBelow
        · exact LeadingTerm.of_equal rfl (Nat.add_comm degree 1) rfl
            (LeadingTerm.mul twiceParameter_leading headLeading)
        · exact DegreeBelow.mono
            (parameterConstant_atMost (-conj coefficient)).toBelowSucc
            (Nat.succ_le_succ (Nat.zero_le degree))
      · exact reflectedTailStep_below headBound tail tailBound

def reflectedLeadingStep (leading : Gaussian) (_ : Gaussian) : Gaussian :=
  2 * leading

def reflectedCoefficients (p : GaussianPolynomial) :
    List ParameterPolynomial :=
  match p.normalize.coeffs with
  | [] => []
  | leading :: remaining =>
      remaining.foldl reflectedStep [parameterConstant (conj leading)]

def reflectedLeading (p : GaussianPolynomial) : Gaussian :=
  match p.normalize.coeffs with
  | [] => 0
  | leading :: remaining =>
      remaining.foldl reflectedLeadingStep (conj leading)

private theorem conj_ne_zero {z : Gaussian} (nonzero : z ≠ 0) :
    conj z ≠ 0 := by
  intro conjugateZero
  apply nonzero
  apply RFAP.ConstructiveGaussian.Gaussian.ext
  · have real :=
      congrArg RFAP.ConstructiveGaussian.Gaussian.re conjugateZero
    change z.re = 0 at real
    exact real
  · have imaginary :=
      congrArg RFAP.ConstructiveGaussian.Gaussian.im conjugateZero
    change -z.im = 0 at imaginary
    exact neg_eq_zero.mp imaginary

private theorem foldl_reflectedShape :
    ∀ (coefficients : List Gaussian) (state : List ParameterPolynomial)
      (degree : Nat) (leading : Gaussian),
      ReflectedShape state degree leading →
      ReflectedShape (coefficients.foldl reflectedStep state)
        (degree + coefficients.length)
        (coefficients.foldl reflectedLeadingStep leading)
  | [], _, degree, _, shape =>
      ReflectedShape.of_equal rfl (Nat.add_zero degree) rfl shape
  | coefficient :: remaining, state, degree, leading, shape => by
      have next := reflectedStep_shape shape coefficient
      have final := foldl_reflectedShape remaining
        (reflectedStep state coefficient) (degree + 1)
        (reflectedLeadingStep leading coefficient) next
      have degreeEqual : degree + (remaining.length + 1) =
          degree + 1 + remaining.length := by
        rw [Nat.add_assoc, Nat.add_comm 1 remaining.length]
      exact ReflectedShape.of_equal rfl degreeEqual rfl final

theorem reflectedCoefficients_shape (p : GaussianPolynomial)
    (nonzero : p.isZero = false) :
    ReflectedShape (reflectedCoefficients p) p.natDegree
      (reflectedLeading p) := by
  cases coefficients : p.normalize.coeffs with
  | nil =>
      have contradiction : p.normalize.coeffs.isEmpty = false := nonzero
      rw [coefficients] at contradiction
      exact Bool.noConfusion contradiction
  | cons leading remaining =>
      have leadingNonzero : leading ≠ 0 := by
        have := leadingCoeff_ne_zero nonzero
        change p.normalize.coeffs.headD 0 ≠ 0 at this
        simpa only [coefficients, List.headD_cons] using this
      have initial : ReflectedShape
          [parameterConstant (conj leading)] 0 (conj leading) := by
        refine
          { length_eq := rfl
            headLeading := ?_
            tailBelow := ?_ }
        · exact parameterConstant_leading (conj_ne_zero leadingNonzero)
        · intro coefficient membership
          simp at membership
      have folded := foldl_reflectedShape remaining
        [parameterConstant (conj leading)] 0 (conj leading) initial
      have degreeEq : p.natDegree = remaining.length := by
        change p.normalize.coeffs.length - 1 = remaining.length
        rw [coefficients]
        simp
      have coefficientsEqual : reflectedCoefficients p =
          remaining.foldl reflectedStep
            [parameterConstant (conj leading)] := by
        unfold reflectedCoefficients
        rw [coefficients]
      have fullDegreeEqual : p.natDegree = 0 + remaining.length :=
        degreeEq.trans (Nat.zero_add remaining.length).symm
      have leadingEqual : reflectedLeading p =
          remaining.foldl reflectedLeadingStep (conj leading) := by
        unfold reflectedLeading
        rw [coefficients]
      exact ReflectedShape.of_equal coefficientsEqual fullDegreeEqual
        leadingEqual folded

/-! ## Separated bivariate pair -/

/-- The low-to-high outer coefficients of `p(U)`, viewed as constants in the
parameter. -/
def liftedCoefficients (p : GaussianPolynomial) :
    List ParameterPolynomial :=
  p.normalize.coeffs.reverse.map parameterConstant

/-- The polynomial `p(U)`. -/
def lifted (p : GaussianPolynomial) : Bivariate :=
  ⟨(liftedCoefficients p).reverse⟩

/-- The polynomial `conj(p)(2T-U)`. -/
def reflected (p : GaussianPolynomial) : Bivariate :=
  ⟨(reflectedCoefficients p).reverse⟩

@[simp] theorem eval_lifted (p : GaussianPolynomial)
    (outer parameter : Gaussian) :
    RFAP.ConstructiveBivariate.eval (lifted p) outer parameter =
      p.eval outer := by
  rw [← eval_normalize p outer]
  simp only [RFAP.ConstructiveBivariate.eval, lifted, liftedCoefficients,
    List.map_reverse, List.reverse_reverse]
  rw [List.foldl_map]
  unfold RFAP.ComputablePolynomial.DensePolynomial.eval
  unfold RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs
  change p.normalize.coeffs.foldl
      (fun value coefficient =>
        value * outer + (parameterConstant coefficient).eval parameter) 0 =
    p.normalize.coeffs.foldl
      (fun value coefficient => value * outer + coefficient) 0
  exact QuotientFreeList.foldl_congr _ _ (fun value coefficient => by
    rw [eval_parameterConstant]) _ _

@[simp] theorem eval_reflected (p : GaussianPolynomial)
    (outer parameter : Gaussian) :
    RFAP.ConstructiveBivariate.eval (reflected p) outer parameter =
      conj (p.eval (conj (2 * parameter - outer))) := by
  rw [← eval_normalize p (conj (2 * parameter - outer))]
  change evalLow (reflectedCoefficients p) outer parameter =
    conj (p.normalize.coeffs.foldl
      (fun value coefficient =>
        value * conj (2 * parameter - outer) + coefficient) 0)
  cases coefficients : p.normalize.coeffs with
  | nil =>
      have reflectedEmpty : reflectedCoefficients p = [] := by
        rw [reflectedCoefficients, coefficients]
      rw [reflectedEmpty]
      rfl
  | cons leading remaining =>
      have initialEvaluation :
          evalLow [parameterConstant (conj leading)] outer parameter =
            conj leading := by
        rw [evalLow_cons, eval_parameterConstant]
        simp [evalLow]
      have reflectedFold := evalLow_foldl_reflectedStep outer parameter
        remaining [parameterConstant (conj leading)] (conj leading)
        initialEvaluation
      have conjugatedFold := conj_evalFold (2 * parameter - outer)
        remaining leading
      rw [reflectedCoefficients, coefficients]
      simp only [List.foldl_cons]
      rw [show (0 : Gaussian) * conj (2 * parameter - outer) + leading =
          leading by ring1]
      exact reflectedFold.trans conjugatedFold.symm

@[simp] theorem outerCoeff_lifted (p : GaussianPolynomial) (index : Nat) :
    RFAP.ConstructiveBivariate.outerCoeff (lifted p) index =
      (liftedCoefficients p).getD index 0 := by
  simp [RFAP.ConstructiveBivariate.outerCoeff, lifted]

@[simp] theorem outerCoeff_reflected (p : GaussianPolynomial) (index : Nat) :
    RFAP.ConstructiveBivariate.outerCoeff (reflected p) index =
      (reflectedCoefficients p).getD index 0 := by
  simp [RFAP.ConstructiveBivariate.outerCoeff, reflected]

private theorem getD_atMost_of_all (degree : Nat) :
    ∀ (coefficients : List ParameterPolynomial) (index : Nat),
      (∀ coefficient ∈ coefficients, DegreeAtMost coefficient degree) →
      DegreeAtMost (coefficients.getD index 0) degree
  | [], _, _ => DegreeAtMost.zero degree
  | coefficient :: _, 0, bounded =>
      bounded coefficient List.mem_cons_self
  | coefficient :: remaining, index + 1, bounded =>
      getD_atMost_of_all degree remaining index
        (fun output membership => bounded output
          (List.mem_cons_of_mem coefficient membership))

private theorem getD_below_of_all (degree : Nat) :
    ∀ (coefficients : List ParameterPolynomial) (index : Nat),
      (∀ coefficient ∈ coefficients, DegreeBelow coefficient degree) →
      DegreeBelow (coefficients.getD index 0) degree
  | [], _, _ => DegreeBelow.zero degree
  | coefficient :: _, 0, bounded =>
      bounded coefficient List.mem_cons_self
  | coefficient :: remaining, index + 1, bounded =>
      getD_below_of_all degree remaining index
        (fun output membership => bounded output
          (List.mem_cons_of_mem coefficient membership))

theorem reflectedCoeff_atMost (p : GaussianPolynomial)
    (nonzero : p.isZero = false) (index : Nat) :
    DegreeAtMost
      (RFAP.ConstructiveBivariate.outerCoeff (reflected p) index)
      p.natDegree := by
  apply DegreeAtMost.of_equal (outerCoeff_reflected p index) rfl
  have shape := reflectedCoefficients_shape p nonzero
  cases coefficients : reflectedCoefficients p with
  | nil =>
      have impossible := shape.length_eq
      rw [coefficients] at impossible
      change 0 = Nat.succ p.natDegree at impossible
      exact Nat.noConfusion impossible
  | cons head tail =>
      cases index with
      | zero =>
          have headEqual :
              (reflectedCoefficients p).headD 0 = head := by
            rw [coefficients]
            rfl
          exact (LeadingTerm.of_equal headEqual.symm rfl rfl
            shape.headLeading).atMost
      | succ index =>
          apply getD_atMost_of_all p.natDegree tail index
          intro coefficient membership
          apply DegreeBelow.toAtMost
          apply shape.tailBelow coefficient
          rw [coefficients]
          exact membership

theorem reflectedCoeff_below_of_pos (p : GaussianPolynomial)
    (nonzero : p.isZero = false) (index : Nat) :
    DegreeBelow
      (RFAP.ConstructiveBivariate.outerCoeff (reflected p) (index + 1))
      p.natDegree := by
  apply DegreeBelow.of_equal (outerCoeff_reflected p (index + 1)) rfl
  have shape := reflectedCoefficients_shape p nonzero
  cases coefficients : reflectedCoefficients p with
  | nil =>
      have impossible := shape.length_eq
      rw [coefficients] at impossible
      change 0 = Nat.succ p.natDegree at impossible
      exact Nat.noConfusion impossible
  | cons head tail =>
      apply getD_below_of_all p.natDegree tail index
      intro coefficient membership
      apply shape.tailBelow coefficient
      rw [coefficients]
      exact membership

theorem reflectedCoeff_zero_leading (p : GaussianPolynomial)
    (nonzero : p.isZero = false) :
    LeadingTerm
      (RFAP.ConstructiveBivariate.outerCoeff (reflected p) 0)
      p.natDegree (reflectedLeading p) := by
  apply LeadingTerm.of_equal (outerCoeff_reflected p 0) rfl rfl
  have shape := reflectedCoefficients_shape p nonzero
  cases coefficients : reflectedCoefficients p with
  | nil =>
      have impossible := shape.length_eq
      rw [coefficients] at impossible
      change 0 = Nat.succ p.natDegree at impossible
      exact Nat.noConfusion impossible
  | cons head tail =>
      have headEqual : (reflectedCoefficients p).headD 0 = head := by
        rw [coefficients]
        rfl
      exact LeadingTerm.of_equal headEqual.symm rfl rfl shape.headLeading

private theorem getD_map_parameterConstant_atMost :
    ∀ (coefficients : List Gaussian) (index : Nat),
      DegreeAtMost
        ((coefficients.map parameterConstant).getD index 0) 0
  | [], _ => DegreeAtMost.zero 0
  | coefficient :: _, 0 => parameterConstant_atMost coefficient
  | _ :: remaining, index + 1 =>
      getD_map_parameterConstant_atMost remaining index

private theorem getD_map_parameterConstant :
    ∀ (coefficients : List Gaussian) (index : Nat),
      (coefficients.map parameterConstant).getD index 0 =
        parameterConstant (coefficients.getD index 0)
  | [], _ => by
      simp only [List.map_nil, List.getD_nil, parameterConstant_zero]
  | _ :: _, 0 => rfl
  | _ :: remaining, index + 1 => by
      simp only [List.map_cons, List.getD_cons_succ]
      exact getD_map_parameterConstant remaining index

private theorem getD_append_at_length {A : Type} (left right : List A)
    (defaultValue : A) :
    (left ++ right).getD left.length defaultValue =
      right.getD 0 defaultValue := by
  induction left with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [List.cons_append, List.length_cons, List.getD_cons_succ]
      exact inductionHypothesis

private theorem reverse_getD_last {A : Type} (head : A) (tail : List A)
    (defaultValue : A) :
    (head :: tail).reverse.getD tail.length defaultValue = head := by
  simp only [List.reverse_cons]
  rw [show tail.length = tail.reverse.length by simp]
  rw [getD_append_at_length]
  rfl

private theorem getD_eq_default_of_length_le {A : Type} :
    ∀ (coefficients : List A) (index : Nat) (defaultValue : A),
      coefficients.length ≤ index →
      coefficients.getD index defaultValue = defaultValue
  | [], _, _, _ => rfl
  | _ :: _, 0, _, bound => by simp at bound
  | _ :: remaining, index + 1, defaultValue, bound => by
      simp only [List.length_cons, List.getD_cons_succ] at bound ⊢
      exact getD_eq_default_of_length_le remaining index defaultValue
        (Nat.succ_le_succ_iff.mp bound)

theorem liftedCoeff_atMost (p : GaussianPolynomial) (index : Nat) :
    DegreeAtMost
      (RFAP.ConstructiveBivariate.outerCoeff (lifted p) index) 0 := by
  apply DegreeAtMost.of_equal (outerCoeff_lifted p index) rfl
  exact getD_map_parameterConstant_atMost p.normalize.coeffs.reverse index

private theorem normalizedCoefficients_length (p : GaussianPolynomial)
    (nonzero : p.isZero = false) :
    p.normalize.coeffs.length = p.natDegree + 1 := by
  have degreeCount := natDegree_add_one_eq_degreeCount nonzero
  change p.natDegree + 1 = p.normalize.coeffs.length at degreeCount
  exact degreeCount.symm

theorem liftedCoefficients_length (p : GaussianPolynomial)
    (nonzero : p.isZero = false) :
    (liftedCoefficients p).length = p.natDegree + 1 := by
  simp only [liftedCoefficients, List.length_map, List.length_reverse]
  exact normalizedCoefficients_length p nonzero

theorem liftedCoeff_degree_leading (p : GaussianPolynomial)
    (nonzero : p.isZero = false) :
    LeadingTerm
      (RFAP.ConstructiveBivariate.outerCoeff (lifted p) p.natDegree) 0
      p.leadingCoeff := by
  apply LeadingTerm.of_equal (outerCoeff_lifted p p.natDegree) rfl rfl
  have coefficientIdentity :
      (liftedCoefficients p).getD p.natDegree 0 =
        parameterConstant p.leadingCoeff := by
    unfold liftedCoefficients
    have lengthEq := normalizedCoefficients_length p nonzero
    cases coefficients : p.normalize.coeffs with
    | nil =>
        rw [coefficients] at lengthEq
        change 0 = Nat.succ p.natDegree at lengthEq
        exact Nat.noConfusion lengthEq
    | cons leading remaining =>
        have degreeEq : p.natDegree = remaining.length := by
          rw [coefficients] at lengthEq
          simp only [List.length_cons] at lengthEq
          exact (Nat.succ.inj lengthEq).symm
        rw [getD_map_parameterConstant, degreeEq,
          reverse_getD_last]
        simp only [leadingCoeff, coefficients, List.headD_cons]
  exact LeadingTerm.of_equal coefficientIdentity rfl rfl
    (parameterConstant_leading (leadingCoeff_ne_zero nonzero))

theorem liftedCoeff_eq_zero_of_degree_lt (p : GaussianPolynomial)
    (nonzero : p.isZero = false) {index : Nat}
    (beyond : p.natDegree < index) :
    RFAP.ConstructiveBivariate.outerCoeff (lifted p) index = 0 := by
  rw [outerCoeff_lifted]
  apply getD_eq_default_of_length_le
  rw [liftedCoefficients_length p nonzero]
  exact Nat.succ_le_of_lt beyond

abbrev PolynomialMatrix (n : Nat) :=
  RFAP.ConstructivePolynomialMatrix.Matrix Gaussian n

/-- Equality of polynomial matrices means that every normalized coefficient
difference is the zero polynomial. -/
def PolynomialMatrixIdentity {n : Nat}
    (left right : PolynomialMatrix n) : Prop :=
  ∀ row column, (left row column - right row column).isZero = true

/-- The fraction-free symbolic recursion returns a two-sided scaled inverse
as an identity of finite coefficient polynomials. -/
theorem scaledInverseData_coefficientIdentity (matrix : PolynomialMatrix n) :
    let data :=
      RFAP.ConstructivePolynomialMatrix.scaledInverseData n matrix
    PolynomialMatrixIdentity
        (RFAP.ConstructivePolynomialMatrix.mul data.inverse matrix)
        (RFAP.ConstructivePolynomialMatrix.scaleIdentity data.scalar) ∧
      PolynomialMatrixIdentity
        (RFAP.ConstructivePolynomialMatrix.mul matrix data.inverse)
        (RFAP.ConstructivePolynomialMatrix.scaleIdentity data.scalar) := by
  dsimp only
  constructor
  · intro row column
    apply RFAP.ConstructiveFiniteRoots.difference_isZero_of_candidate_evals
    intro point _
    have identity :=
      (RFAP.ConstructivePolynomialMatrix.scaledInverseData_spec
        point n matrix).1
    calc
      (RFAP.ConstructivePolynomialMatrix.mul
          (RFAP.ConstructivePolynomialMatrix.scaledInverseData n matrix).inverse
          matrix row column).eval point =
          (RFAP.ConstructiveFiniteMatrix.mul
            (RFAP.ConstructivePolynomialMatrix.evalMatrix point
              (RFAP.ConstructivePolynomialMatrix.scaledInverseData
                n matrix).inverse)
            (RFAP.ConstructivePolynomialMatrix.evalMatrix point matrix))
              row column := by
                simpa only [
                  RFAP.ConstructivePolynomialMatrix.evalMatrix_apply] using
                  RFAP.ConstructiveFiniteMatrix.matrix_eq_at
                    (RFAP.ConstructivePolynomialMatrix.eval_matrixMul point
                      (RFAP.ConstructivePolynomialMatrix.scaledInverseData
                        n matrix).inverse matrix) row column
      _ = (RFAP.ConstructiveFiniteMatrix.scaleIdentity
          ((RFAP.ConstructivePolynomialMatrix.scaledInverseData
            n matrix).scalar.eval point)) row column :=
        RFAP.ConstructiveFiniteMatrix.matrix_eq_at identity row column
      _ = (RFAP.ConstructivePolynomialMatrix.scaleIdentity
          (RFAP.ConstructivePolynomialMatrix.scaledInverseData
            n matrix).scalar row column).eval point :=
        by
          simpa only [
            RFAP.ConstructivePolynomialMatrix.evalMatrix_apply] using
            (RFAP.ConstructiveFiniteMatrix.matrix_eq_at
              (RFAP.ConstructivePolynomialMatrix.eval_scaleIdentity point
                (RFAP.ConstructivePolynomialMatrix.scaledInverseData
                  n matrix).scalar) row column).symm
  · intro row column
    apply RFAP.ConstructiveFiniteRoots.difference_isZero_of_candidate_evals
    intro point _
    have identity :=
      (RFAP.ConstructivePolynomialMatrix.scaledInverseData_spec
        point n matrix).2
    calc
      (RFAP.ConstructivePolynomialMatrix.mul matrix
          (RFAP.ConstructivePolynomialMatrix.scaledInverseData n matrix).inverse
          row column).eval point =
          (RFAP.ConstructiveFiniteMatrix.mul
            (RFAP.ConstructivePolynomialMatrix.evalMatrix point matrix)
            (RFAP.ConstructivePolynomialMatrix.evalMatrix point
              (RFAP.ConstructivePolynomialMatrix.scaledInverseData
                n matrix).inverse)) row column := by
              simpa only [
                RFAP.ConstructivePolynomialMatrix.evalMatrix_apply] using
                RFAP.ConstructiveFiniteMatrix.matrix_eq_at
                  (RFAP.ConstructivePolynomialMatrix.eval_matrixMul point matrix
                    (RFAP.ConstructivePolynomialMatrix.scaledInverseData
                      n matrix).inverse) row column
      _ = (RFAP.ConstructiveFiniteMatrix.scaleIdentity
          ((RFAP.ConstructivePolynomialMatrix.scaledInverseData
            n matrix).scalar.eval point)) row column :=
        RFAP.ConstructiveFiniteMatrix.matrix_eq_at identity row column
      _ = (RFAP.ConstructivePolynomialMatrix.scaleIdentity
          (RFAP.ConstructivePolynomialMatrix.scaledInverseData
            n matrix).scalar row column).eval point :=
        by
          simpa only [
            RFAP.ConstructivePolynomialMatrix.evalMatrix_apply] using
            (RFAP.ConstructiveFiniteMatrix.matrix_eq_at
              (RFAP.ConstructivePolynomialMatrix.eval_scaleIdentity point
                (RFAP.ConstructivePolynomialMatrix.scaledInverseData
                  n matrix).scalar) row column).symm

/-- The finite Sylvester matrix for `p(U)` and `conj(p)(2T-U)`. -/
def separatedSylvester (p : GaussianPolynomial) :
    PolynomialMatrix (p.natDegree + p.natDegree) :=
  RFAP.ConstructiveBivariate.sylvester
    (lifted p) (reflected p) p.natDegree p.natDegree

def separatedDegrees (p : GaussianPolynomial) :
    Fin (p.natDegree + p.natDegree) → Nat :=
  fun column => QuotientFreeFin.addCases
    (fun _ => p.natDegree) (fun _ => 0) column

def separatedDiagonal (p : GaussianPolynomial) :
    Fin (p.natDegree + p.natDegree) → Gaussian :=
  fun column => QuotientFreeFin.addCases
    (fun _ => reflectedLeading p) (fun _ => p.leadingCoeff) column

/-- The top parameter coefficient matrix of the separated Sylvester matrix is
upper triangular.  This is a finite coefficient-list fact: the reflected
block contributes its top term on the first diagonal, and `p(U)` contributes
its leading coefficient on the second diagonal. -/
theorem separatedSylvester_leading (p : GaussianPolynomial)
    (nonzero : p.isZero = false) :
    RFAP.ConstructivePolynomialMatrixLeading.UpperTriangularLeading
      (separatedSylvester p) (separatedDegrees p) (separatedDiagonal p) where
  atMost := by
    intro row column
    rcases QuotientFreeFin.addCases_split column with
      ⟨left, rfl⟩ | ⟨right, rfl⟩
    · have entryEqual :
          separatedSylvester p row (Fin.castAdd p.natDegree left) =
            if (left : Nat) ≤ (row : Nat) ∧
                (row : Nat) ≤ (left : Nat) + p.natDegree then
              RFAP.ConstructiveBivariate.outerCoeff
                (reflected p) ((row : Nat) - left)
            else 0 :=
        RFAP.ConstructiveBivariate.sylvester_left_apply
          (lifted p) (reflected p) p.natDegree p.natDegree row left
      have degreeEqual :
          separatedDegrees p (Fin.castAdd p.natDegree left) =
            p.natDegree := by
        unfold separatedDegrees
        exact QuotientFreeFin.addCases_left _ _ _
      apply DegreeAtMost.of_equal entryEqual degreeEqual
      by_cases included : (left : Nat) ≤ (row : Nat) ∧
          (row : Nat) ≤ (left : Nat) + p.natDegree
      · exact DegreeAtMost.of_equal (if_pos included) rfl
          (reflectedCoeff_atMost p nonzero _)
      · exact DegreeAtMost.of_equal (if_neg included) rfl
          (DegreeAtMost.zero p.natDegree)
    · have entryEqual :
          separatedSylvester p row (Fin.natAdd p.natDegree right) =
            if (right : Nat) ≤ (row : Nat) ∧
                (row : Nat) ≤ (right : Nat) + p.natDegree then
              RFAP.ConstructiveBivariate.outerCoeff
                (lifted p) ((row : Nat) - right)
            else 0 :=
        RFAP.ConstructiveBivariate.sylvester_right_apply
          (lifted p) (reflected p) p.natDegree p.natDegree row right
      have degreeEqual :
          separatedDegrees p (Fin.natAdd p.natDegree right) = 0 := by
        unfold separatedDegrees
        exact QuotientFreeFin.addCases_right _ _ _
      apply DegreeAtMost.of_equal entryEqual degreeEqual
      by_cases included : (right : Nat) ≤ (row : Nat) ∧
          (row : Nat) ≤ (right : Nat) + p.natDegree
      · exact DegreeAtMost.of_equal (if_pos included) rfl
          (liftedCoeff_atMost p _)
      · exact DegreeAtMost.of_equal (if_neg included) rfl
          (DegreeAtMost.zero 0)
  below := by
    intro row column belowDiagonal
    rcases QuotientFreeFin.addCases_split column with
      ⟨left, rfl⟩ | ⟨right, rfl⟩
    · have entryEqual :
          separatedSylvester p row (Fin.castAdd p.natDegree left) =
            if (left : Nat) ≤ (row : Nat) ∧
                (row : Nat) ≤ (left : Nat) + p.natDegree then
              RFAP.ConstructiveBivariate.outerCoeff
                (reflected p) ((row : Nat) - left)
            else 0 :=
        RFAP.ConstructiveBivariate.sylvester_left_apply
          (lifted p) (reflected p) p.natDegree p.natDegree row left
      have degreeEqual :
          separatedDegrees p (Fin.castAdd p.natDegree left) =
            p.natDegree := by
        unfold separatedDegrees
        exact QuotientFreeFin.addCases_left _ _ _
      apply DegreeBelow.of_equal entryEqual degreeEqual
      by_cases included : (left : Nat) ≤ (row : Nat) ∧
          (row : Nat) ≤ (left : Nat) + p.natDegree
      · apply DegreeBelow.of_equal (if_pos included) rfl
        have positive : 0 < (row : Nat) - (left : Nat) := by
          have leftLt : (left : Nat) < (row : Nat) := belowDiagonal
          exact Nat.sub_pos_iff_lt.mpr leftLt
        have successorIdentity :
            (row : Nat) - (left : Nat) =
              ((row : Nat) - (left : Nat) - 1) + 1 :=
          (Nat.sub_add_cancel (Nat.succ_le_iff.mpr positive)).symm
        exact DegreeBelow.of_equal
          (congrArg
            (RFAP.ConstructiveBivariate.outerCoeff (reflected p))
            successorIdentity)
          rfl (reflectedCoeff_below_of_pos p nonzero _)
      · exact DegreeBelow.of_equal (if_neg included) rfl
          (DegreeBelow.zero p.natDegree)
    · have entryEqual :
          separatedSylvester p row (Fin.natAdd p.natDegree right) =
            if (right : Nat) ≤ (row : Nat) ∧
                (row : Nat) ≤ (right : Nat) + p.natDegree then
              RFAP.ConstructiveBivariate.outerCoeff
                (lifted p) ((row : Nat) - right)
            else 0 :=
        RFAP.ConstructiveBivariate.sylvester_right_apply
          (lifted p) (reflected p) p.natDegree p.natDegree row right
      have degreeEqual :
          separatedDegrees p (Fin.natAdd p.natDegree right) = 0 := by
        unfold separatedDegrees
        exact QuotientFreeFin.addCases_right _ _ _
      apply DegreeBelow.of_equal entryEqual degreeEqual
      by_cases included : (right : Nat) ≤ (row : Nat) ∧
          (row : Nat) ≤ (right : Nat) + p.natDegree
      · apply DegreeBelow.of_equal (if_pos included) rfl
        have beyond :
            p.natDegree < (row : Nat) - (right : Nat) := by
          have rightBelow :
              p.natDegree + (right : Nat) < (row : Nat) := belowDiagonal
          exact Nat.lt_sub_of_add_lt rightBelow
        exact DegreeBelow.of_equal
          (liftedCoeff_eq_zero_of_degree_lt p nonzero beyond)
          rfl (DegreeBelow.zero 0)
      · exact DegreeBelow.of_equal (if_neg included) rfl
          (DegreeBelow.zero 0)
  diagonalLeading := by
    intro index
    rcases QuotientFreeFin.addCases_split index with
      ⟨left, rfl⟩ | ⟨right, rfl⟩
    · have entryEqual :
          separatedSylvester p
              (Fin.castAdd p.natDegree left)
              (Fin.castAdd p.natDegree left) =
            RFAP.ConstructiveBivariate.outerCoeff (reflected p) 0 := by
        rw [separatedSylvester,
          RFAP.ConstructiveBivariate.sylvester_left_apply,
          Fin.val_castAdd,
          if_pos ⟨le_rfl, Nat.le_add_right _ _⟩,
          Nat.sub_self]
      have degreeEqual :
          separatedDegrees p (Fin.castAdd p.natDegree left) =
            p.natDegree := by
        unfold separatedDegrees
        exact QuotientFreeFin.addCases_left _ _ _
      have diagonalEqual :
          separatedDiagonal p (Fin.castAdd p.natDegree left) =
            reflectedLeading p := by
        unfold separatedDiagonal
        exact QuotientFreeFin.addCases_left _ _ _
      exact LeadingTerm.of_equal entryEqual degreeEqual diagonalEqual
        (reflectedCoeff_zero_leading p nonzero)
    · have difference :
          p.natDegree + (right : Nat) - (right : Nat) =
            p.natDegree := Nat.add_sub_cancel_right _ _
      have entryEqual :
          separatedSylvester p
              (Fin.natAdd p.natDegree right)
              (Fin.natAdd p.natDegree right) =
            RFAP.ConstructiveBivariate.outerCoeff (lifted p) p.natDegree := by
        rw [separatedSylvester,
          RFAP.ConstructiveBivariate.sylvester_right_apply,
          Fin.val_natAdd,
          if_pos ⟨Nat.le_add_left _ _, (Nat.add_comm _ _).le⟩,
          difference]
      have degreeEqual :
          separatedDegrees p (Fin.natAdd p.natDegree right) = 0 := by
        unfold separatedDegrees
        exact QuotientFreeFin.addCases_right _ _ _
      have diagonalEqual :
          separatedDiagonal p (Fin.natAdd p.natDegree right) =
            p.leadingCoeff := by
        unfold separatedDiagonal
        exact QuotientFreeFin.addCases_right _ _ _
      exact LeadingTerm.of_equal entryEqual degreeEqual diagonalEqual
        (liftedCoeff_degree_leading p nonzero)

/-- The fraction-free scaled inverse of the separated Sylvester matrix has a
nonzero scalar polynomial. -/
theorem separatedScalar_nonzero (p : GaussianPolynomial)
    (nonzero : p.isZero = false) :
    (RFAP.ConstructivePolynomialMatrix.scaledInverseData
      (p.natDegree + p.natDegree) (separatedSylvester p)).scalar.isZero =
        false :=
  RFAP.ConstructivePolynomialMatrixLeading.scaledInverseData_scalar_nonzero
    (separatedSylvester_leading p nonzero)

end RFAP.SeparatedVariables
