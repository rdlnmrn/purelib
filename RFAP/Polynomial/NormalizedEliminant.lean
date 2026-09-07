import mathlib.Data.ConstructiveList
import mathlib.Tactic.QuotientFreeOmega
import mathlib.RFAP.ConstructiveSylvesterBezout
import mathlib.RFAP.ComputablePolynomialMatrixMap
import mathlib.RFAP.NormalizedPolynomialResource

/-!
# Normalized separated-Sylvester eliminants

This is the reduced-record execution of the separated-variable preparation
and fraction-free Schur recursion.  Its compatibility map to the established
separated-Sylvester interface is structural on the same canonical Gaussian
scalar.  Thus every persistent Gaussian-rational coefficient in this
execution is canonical while the paper-facing algebraic API remains stable.
-/

namespace RFAP.NormalizedEliminant

abbrev SemanticGaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev WorkingGaussian := RFAP.NormalizedGaussian.Gaussian
abbrev SemanticPolynomial :=
  RFAP.ComputablePolynomial.DensePolynomial SemanticGaussian
abbrev WorkingPolynomial :=
  RFAP.ComputablePolynomial.DensePolynomial WorkingGaussian
abbrev WorkingBivariate :=
  RFAP.ConstructiveBivariate.Bivariate WorkingGaussian
abbrev WorkingMatrix (n : Nat) :=
  RFAP.ConstructivePolynomialMatrix.Matrix WorkingGaussian n
abbrev gaussianModel :=
  RFAP.NormalizedPolynomialResource.gaussianModel

open RFAP.ComputablePolynomial.DensePolynomial

def eraseEmbedding :
    RFAP.ComputablePolynomialMap.Embedding WorkingGaussian SemanticGaussian where
  toFun := RFAP.NormalizedGaussian.value
  injective := RFAP.NormalizedGaussian.value_injective
  map_zero := RFAP.NormalizedGaussian.value_zero
  map_one := RFAP.NormalizedGaussian.value_one
  map_add := RFAP.NormalizedGaussian.value_add_instance
  map_neg := RFAP.NormalizedGaussian.value_neg_instance
  map_mul := RFAP.NormalizedGaussian.value_mul_instance
  map_inv := RFAP.NormalizedGaussian.value_inv_instance

def canonicalEmbedding :
    RFAP.ComputablePolynomialMap.Embedding SemanticGaussian WorkingGaussian where
  toFun := RFAP.NormalizedGaussian.ofGaussian
  injective := by
    intro left right equal
    have values := congrArg RFAP.NormalizedGaussian.value equal
    simpa only [RFAP.NormalizedGaussian.value_ofGaussian] using values
  map_zero := by
    apply RFAP.NormalizedGaussian.value_injective
    simp only [RFAP.NormalizedGaussian.value_ofGaussian,
      RFAP.NormalizedGaussian.value_zero]
  map_one := by
    apply RFAP.NormalizedGaussian.value_injective
    simp only [RFAP.NormalizedGaussian.value_ofGaussian,
      RFAP.NormalizedGaussian.value_one]
  map_add := by
    intro left right
    apply RFAP.NormalizedGaussian.value_injective
    simp only [RFAP.NormalizedGaussian.value_ofGaussian,
      RFAP.NormalizedGaussian.value_add_instance]
  map_neg := by
    intro source
    apply RFAP.NormalizedGaussian.value_injective
    simp only [RFAP.NormalizedGaussian.value_ofGaussian,
      RFAP.NormalizedGaussian.value_neg_instance]
  map_mul := by
    intro left right
    apply RFAP.NormalizedGaussian.value_injective
    simp only [RFAP.NormalizedGaussian.value_ofGaussian,
      RFAP.NormalizedGaussian.value_mul_instance]
  map_inv := by
    intro source
    apply RFAP.NormalizedGaussian.value_injective
    simp only [RFAP.NormalizedGaussian.value_ofGaussian,
      RFAP.NormalizedGaussian.value_inv_instance]

def erasePolynomial (polynomial : WorkingPolynomial) : SemanticPolynomial :=
  RFAP.ComputablePolynomialMap.map eraseEmbedding polynomial

def canonicalPolynomial (polynomial : SemanticPolynomial) : WorkingPolynomial :=
  RFAP.ComputablePolynomialMap.map canonicalEmbedding polynomial

private theorem erase_normalize (polynomial : WorkingPolynomial) :
    erasePolynomial polynomial.normalize =
      (erasePolynomial polynomial).normalize :=
  RFAP.ComputablePolynomialMap.map_normalize eraseEmbedding polynomial

private theorem erase_normalize_coeffs (polynomial : WorkingPolynomial) :
    (erasePolynomial polynomial).normalize.coeffs =
      polynomial.normalize.coeffs.map RFAP.NormalizedGaussian.value := by
  rw [← erase_normalize]
  rfl

private theorem erase_neg (polynomial : WorkingPolynomial) :
    erasePolynomial (-polynomial) = -erasePolynomial polynomial :=
  RFAP.ComputablePolynomialMap.map_neg eraseEmbedding polynomial

private theorem erase_sub (left right : WorkingPolynomial) :
    erasePolynomial (left - right) =
      erasePolynomial left - erasePolynomial right :=
  RFAP.ComputablePolynomialMap.map_sub eraseEmbedding left right

private theorem erase_mul (left right : WorkingPolynomial) :
    erasePolynomial (left * right) =
      erasePolynomial left * erasePolynomial right :=
  RFAP.ComputablePolynomialMap.map_mul eraseEmbedding left right

def workingConjugate (source : WorkingGaussian) : WorkingGaussian :=
  ⟨source.re, RFAP.NormalizedFraction.neg source.im⟩

theorem value_workingConjugate (source : WorkingGaussian) :
    RFAP.NormalizedGaussian.value (workingConjugate source) =
      RFAP.ConstructiveGaussian.Gaussian.conj
        (RFAP.NormalizedGaussian.value source) := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext
  · rfl
  · exact RFAP.NormalizedFraction.value_neg source.im

def parameterConstant (value : WorkingGaussian) : WorkingPolynomial :=
  if value = 0 then 0 else constant value

def twiceParameter : WorkingPolynomial :=
  ⟨[RFAP.NormalizedGaussian.ofGaussian 2,
    RFAP.NormalizedGaussian.ofGaussian 0]⟩

def twiceShift (polynomial : WorkingPolynomial) : WorkingPolynomial :=
  twiceParameter * polynomial

def reflectedTailStep (previous : WorkingPolynomial) :
    List WorkingPolynomial → List WorkingPolynomial
  | [] => [-previous]
  | current :: remaining =>
      (twiceShift current - previous) ::
        reflectedTailStep current remaining

def reflectedStep (coefficients : List WorkingPolynomial)
    (coefficient : WorkingGaussian) : List WorkingPolynomial :=
  match coefficients with
  | [] => [parameterConstant (workingConjugate coefficient)]
  | head :: tail =>
      (twiceShift head -
          parameterConstant (-workingConjugate coefficient)) ::
        reflectedTailStep head tail

def reflectedCoefficients (polynomial : WorkingPolynomial) :
    List WorkingPolynomial :=
  match polynomial.normalize.coeffs with
  | [] => []
  | leading :: remaining =>
      remaining.foldl reflectedStep
        [parameterConstant (workingConjugate leading)]

def liftedCoefficients (polynomial : WorkingPolynomial) :
    List WorkingPolynomial :=
  polynomial.normalize.coeffs.reverse.map parameterConstant

def lifted (polynomial : WorkingPolynomial) : WorkingBivariate :=
  ⟨(liftedCoefficients polynomial).reverse⟩

def reflected (polynomial : WorkingPolynomial) : WorkingBivariate :=
  ⟨(reflectedCoefficients polynomial).reverse⟩

def separatedSylvester (polynomial : WorkingPolynomial) :
    WorkingMatrix ((erasePolynomial polynomial).natDegree +
      (erasePolynomial polynomial).natDegree) :=
  RFAP.ConstructiveBivariate.sylvester
    (lifted polynomial) (reflected polynomial)
    (erasePolynomial polynomial).natDegree
    (erasePolynomial polynomial).natDegree

def separatedData (polynomial : WorkingPolynomial) :=
  RFAP.ConstructivePolynomialMatrix.scaledInverseData
    ((erasePolynomial polynomial).natDegree +
      (erasePolynomial polynomial).natDegree)
    (separatedSylvester polynomial)

def normalizedScalar (polynomial : SemanticPolynomial) : WorkingPolynomial :=
  (separatedData (canonicalPolynomial polynomial)).scalar

/-! ## Erasure of separated-variable preparation -/

private theorem erase_parameterConstant (value : WorkingGaussian) :
    erasePolynomial (parameterConstant value) =
      RFAP.SeparatedVariables.parameterConstant
        (RFAP.NormalizedGaussian.value value) := by
  unfold parameterConstant RFAP.SeparatedVariables.parameterConstant
  have zeroIff : RFAP.NormalizedGaussian.value value = 0 ↔ value = 0 := by
    rw [← RFAP.NormalizedGaussian.value_zero]
    exact RFAP.NormalizedGaussian.value_injective.eq_iff
  by_cases zero : value = 0
  · rw [if_pos zero, if_pos (zeroIff.mpr zero)]
    exact RFAP.ComputablePolynomialMap.map_zero_polynomial eraseEmbedding
  · rw [if_neg zero, if_neg (by simpa only [zeroIff] using zero)]
    exact RFAP.ComputablePolynomialMap.map_constant eraseEmbedding value

private theorem erase_twiceParameter :
    erasePolynomial twiceParameter =
      RFAP.SeparatedVariables.twiceParameter := by
  apply RFAP.ComputablePolynomial.DensePolynomial.ext
  simp only [erasePolynomial, twiceParameter,
    RFAP.ComputablePolynomialMap.map_coeffs, List.map_cons, List.map_nil]
  rfl

private theorem erase_twiceShift (polynomial : WorkingPolynomial) :
    erasePolynomial (twiceShift polynomial) =
      RFAP.SeparatedVariables.twiceShift (erasePolynomial polynomial) := by
  unfold twiceShift RFAP.SeparatedVariables.twiceShift
  rw [erase_mul, erase_twiceParameter]

private theorem erase_reflectedTailStep (previous : WorkingPolynomial) :
    ∀ coefficients : List WorkingPolynomial,
      (reflectedTailStep previous coefficients).map erasePolynomial =
        RFAP.SeparatedVariables.reflectedTailStep
          (erasePolynomial previous) (coefficients.map erasePolynomial)
  | [] => by
      simp only [reflectedTailStep,
        RFAP.SeparatedVariables.reflectedTailStep, List.map_cons, List.map_nil]
      rw [erase_neg]
  | current :: remaining => by
      simp only [reflectedTailStep,
        RFAP.SeparatedVariables.reflectedTailStep, List.map_cons]
      rw [erase_sub, erase_twiceShift,
        erase_reflectedTailStep current remaining]

private theorem erase_reflectedStep (coefficients : List WorkingPolynomial)
    (coefficient : WorkingGaussian) :
    (reflectedStep coefficients coefficient).map erasePolynomial =
      RFAP.SeparatedVariables.reflectedStep
        (coefficients.map erasePolynomial)
        (RFAP.NormalizedGaussian.value coefficient) := by
  cases coefficients with
  | nil =>
      simp only [reflectedStep, RFAP.SeparatedVariables.reflectedStep,
        List.map_cons, List.map_nil, erase_parameterConstant,
        value_workingConjugate]
  | cons head tail =>
      simp only [reflectedStep, RFAP.SeparatedVariables.reflectedStep,
        List.map_cons]
      rw [erase_sub, erase_twiceShift,
        erase_parameterConstant,
        RFAP.NormalizedGaussian.value_neg_instance,
        value_workingConjugate, erase_reflectedTailStep]

private theorem erase_fold_reflectedStep :
    ∀ (coefficients : List WorkingGaussian)
      (state : List WorkingPolynomial),
      (coefficients.foldl reflectedStep state).map erasePolynomial =
        (coefficients.map RFAP.NormalizedGaussian.value).foldl
          RFAP.SeparatedVariables.reflectedStep
          (state.map erasePolynomial)
  | [], _ => rfl
  | coefficient :: remaining, state => by
      simp only [List.foldl_cons, List.map_cons]
      rw [erase_fold_reflectedStep remaining,
        erase_reflectedStep state coefficient]

theorem erase_reflectedCoefficients (polynomial : WorkingPolynomial) :
    (reflectedCoefficients polynomial).map erasePolynomial =
      RFAP.SeparatedVariables.reflectedCoefficients
        (erasePolynomial polynomial) := by
  cases coefficients : polynomial.normalize.coeffs with
  | nil =>
      unfold reflectedCoefficients
      unfold RFAP.SeparatedVariables.reflectedCoefficients
      rw [coefficients, erase_normalize_coeffs, coefficients]
      rfl
  | cons leading remaining =>
      unfold reflectedCoefficients
      unfold RFAP.SeparatedVariables.reflectedCoefficients
      rw [coefficients, erase_normalize_coeffs, coefficients]
      simp only [List.map_cons]
      rw [erase_fold_reflectedStep]
      apply congrArg (fun initial =>
        (remaining.map RFAP.NormalizedGaussian.value).foldl
          RFAP.SeparatedVariables.reflectedStep initial)
      simp only [List.map_cons, List.map_nil]
      rw [erase_parameterConstant, value_workingConjugate]

theorem erase_liftedCoefficients (polynomial : WorkingPolynomial) :
    (liftedCoefficients polynomial).map erasePolynomial =
      RFAP.SeparatedVariables.liftedCoefficients
        (erasePolynomial polynomial) := by
  unfold liftedCoefficients RFAP.SeparatedVariables.liftedCoefficients
  rw [erase_normalize_coeffs]
  simp only [List.map_reverse, List.map_map]
  apply congrArg List.reverse
  apply QuotientFreeList.map_congr_left
  intro coefficient _
  change erasePolynomial (parameterConstant coefficient) =
    RFAP.SeparatedVariables.parameterConstant
      (RFAP.NormalizedGaussian.value coefficient)
  exact erase_parameterConstant coefficient

private theorem erase_canonicalPolynomial (polynomial : SemanticPolynomial) :
    erasePolynomial (canonicalPolynomial polynomial) = polynomial := by
  apply RFAP.ComputablePolynomial.DensePolynomial.ext
  unfold erasePolynomial canonicalPolynomial RFAP.ComputablePolynomialMap.map
  induction polynomial.coeffs with
  | nil => rfl
  | cons coefficient remaining inductionHypothesis =>
      simp only [List.map_cons, List.map_map]
      change RFAP.NormalizedGaussian.value
          (RFAP.NormalizedGaussian.ofGaussian coefficient) ::
        List.map (eraseEmbedding.toFun ∘ canonicalEmbedding.toFun) remaining =
          coefficient :: remaining
      rw [RFAP.NormalizedGaussian.value_ofGaussian]
      have tailEqual :
          List.map (eraseEmbedding.toFun ∘ canonicalEmbedding.toFun)
            remaining = remaining := by
        simpa only [RFAP.ComputablePolynomialMap.map_coeffs,
          List.map_map] using inductionHypothesis
      exact congrArg (List.cons coefficient) tailEqual

private theorem erase_lifted (polynomial : WorkingPolynomial) :
    (lifted polynomial).coeffs.map erasePolynomial =
      (RFAP.SeparatedVariables.lifted
        (erasePolynomial polynomial)).coeffs := by
  unfold lifted RFAP.SeparatedVariables.lifted
  rw [List.map_reverse, erase_liftedCoefficients]

private theorem erase_reflected (polynomial : WorkingPolynomial) :
    (reflected polynomial).coeffs.map erasePolynomial =
      (RFAP.SeparatedVariables.reflected
        (erasePolynomial polynomial)).coeffs := by
  unfold reflected RFAP.SeparatedVariables.reflected
  rw [List.map_reverse, erase_reflectedCoefficients]

private theorem map_getD : ∀ (coefficients : List WorkingPolynomial)
    (index : Nat),
    erasePolynomial (coefficients.getD index 0) =
      (coefficients.map erasePolynomial).getD index 0
  | [], _ => RFAP.ComputablePolynomialMap.map_zero_polynomial eraseEmbedding
  | _ :: _, 0 => rfl
  | _ :: remaining, index + 1 => map_getD remaining index

private theorem erase_outerCoeff
    (bivariate : WorkingBivariate) (index : Nat) :
    erasePolynomial (RFAP.ConstructiveBivariate.outerCoeff bivariate index) =
      RFAP.ConstructiveBivariate.outerCoeff
        ⟨bivariate.coeffs.map erasePolynomial⟩ index := by
  unfold RFAP.ConstructiveBivariate.outerCoeff
  change erasePolynomial (bivariate.coeffs.reverse.getD index 0) =
    (bivariate.coeffs.map erasePolynomial).reverse.getD index 0
  rw [← List.map_reverse]
  exact map_getD bivariate.coeffs.reverse index

theorem erase_separatedSylvester (polynomial : WorkingPolynomial) :
    RFAP.ComputablePolynomialMatrixMap.mapMatrix eraseEmbedding
        (separatedSylvester polynomial) =
      RFAP.SeparatedVariables.separatedSylvester
        (erasePolynomial polynomial) := by
  apply RFAP.ConstructiveFiniteMatrix.matrix_ext
  intro row column
  simp only [RFAP.ComputablePolynomialMatrixMap.mapMatrix_apply]
  unfold separatedSylvester RFAP.SeparatedVariables.separatedSylvester
  unfold RFAP.ConstructiveBivariate.sylvester
  simp only [RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply]
  rcases QuotientFreeFin.addCases_split column with
    ⟨left, rfl⟩ | ⟨right, rfl⟩
  · simp only [QuotientFreeFin.addCases_left]
    split
    · change erasePolynomial
          (RFAP.ConstructiveBivariate.outerCoeff (reflected polynomial)
            ((row : Nat) - (left : Nat))) = _
      rw [erase_outerCoeff]
      apply congrArg (fun bivariate =>
        RFAP.ConstructiveBivariate.outerCoeff bivariate
          ((row : Nat) - (left : Nat)))
      exact congrArg RFAP.ConstructiveBivariate.Bivariate.mk
        (erase_reflected polynomial)
    · exact RFAP.ComputablePolynomialMap.map_zero_polynomial eraseEmbedding
  · simp only [QuotientFreeFin.addCases_right]
    split
    · change erasePolynomial
          (RFAP.ConstructiveBivariate.outerCoeff (lifted polynomial)
            ((row : Nat) - (right : Nat))) = _
      rw [erase_outerCoeff]
      apply congrArg (fun bivariate =>
        RFAP.ConstructiveBivariate.outerCoeff bivariate
          ((row : Nat) - (right : Nat)))
      exact congrArg RFAP.ConstructiveBivariate.Bivariate.mk
        (erase_lifted polynomial)
    · exact RFAP.ComputablePolynomialMap.map_zero_polynomial eraseEmbedding

theorem erase_separatedScalar (polynomial : WorkingPolynomial) :
    erasePolynomial (separatedData polynomial).scalar =
      (RFAP.ConstructiveSylvesterBezout.separatedData
        (erasePolynomial polynomial)).scalar := by
  have mapped :=
    (RFAP.ComputablePolynomialMatrixMap.map_scaledInverseData eraseEmbedding
      ((erasePolynomial polynomial).natDegree +
        (erasePolynomial polynomial).natDegree)
      (separatedSylvester polynomial)).1
  rw [erase_separatedSylvester] at mapped
  exact mapped

/-- The complete reduced-record Schur recursion erases to the scalar used by
the existing separated-Sylvester Bézout development. -/
theorem erase_normalizedScalar (polynomial : SemanticPolynomial) :
    erasePolynomial (normalizedScalar polynomial) =
      (RFAP.ConstructiveSylvesterBezout.separatedData polynomial).scalar := by
  unfold normalizedScalar
  rw [erase_separatedScalar, erase_canonicalPolynomial]

/-! ## Separated-variable coefficient envelope -/

open RFAP.NormalizedPolynomialResource

def coefficientMagnitude (polynomial : WorkingPolynomial) : Nat :=
  polynomial.coeffs.foldl
    (fun bound coefficient => max bound (gaussianModel.magnitude coefficient))
    (max (gaussianModel.magnitude 0)
      (max (gaussianModel.magnitude
          (RFAP.NormalizedGaussian.ofGaussian 2))
        (gaussianModel.magnitude
          (RFAP.NormalizedGaussian.ofGaussian 1))))

private theorem foldl_max_initial_le : ∀ (coefficients : List WorkingGaussian)
    (initial : Nat), initial ≤ coefficients.foldl
      (fun bound coefficient => max bound (gaussianModel.magnitude coefficient))
      initial
  | [], _ => le_refl _
  | _ :: remaining, _ =>
      (le_max_left _ _).trans (foldl_max_initial_le remaining _)

private theorem member_le_foldl_max : ∀ (coefficients : List WorkingGaussian)
    (initial : Nat) {candidate : WorkingGaussian}, candidate ∈ coefficients →
    gaussianModel.magnitude candidate ≤ coefficients.foldl
      (fun bound coefficient => max bound (gaussianModel.magnitude coefficient))
      initial
  | [], _, _, member => by simp at member
  | coefficient :: remaining, initial, candidate, member => by
      simp only [List.mem_cons] at member
      rcases member with head | tail
      · rw [head]
        exact (le_max_right _ _).trans (foldl_max_initial_le remaining _)
      · exact member_le_foldl_max remaining
          (max initial (gaussianModel.magnitude coefficient)) tail

theorem source_zero_within (polynomial : WorkingPolynomial) :
    gaussianModel.magnitude 0 ≤ coefficientMagnitude polynomial :=
  (le_max_left _ _).trans (foldl_max_initial_le polynomial.coeffs _)

theorem source_two_within (polynomial : WorkingPolynomial) :
    gaussianModel.magnitude (RFAP.NormalizedGaussian.ofGaussian 2) ≤
      coefficientMagnitude polynomial :=
  ((le_max_left _ _).trans (le_max_right _ _)).trans
    (foldl_max_initial_le polynomial.coeffs _)

theorem source_one_within (polynomial : WorkingPolynomial) :
    gaussianModel.magnitude (1 : WorkingGaussian) ≤
      coefficientMagnitude polynomial :=
  ((le_max_right _ _).trans (le_max_right _ _)).trans
    (foldl_max_initial_le polynomial.coeffs _)

theorem polynomial_within_coefficientMagnitude (polynomial : WorkingPolynomial) :
    PolynomialWithin gaussianModel polynomial
      (coefficientMagnitude polynomial) := by
  intro candidate member
  exact member_le_foldl_max polynomial.coeffs _ member

theorem workingConjugate_within {source : WorkingGaussian} {bound : Nat}
    (bounded : gaussianModel.magnitude source ≤ bound) :
    gaussianModel.magnitude (workingConjugate source) ≤ bound := by
  unfold gaussianModel RFAP.NormalizedPolynomialResource.gaussianModel
    MagnitudeModel.magnitude
  unfold RFAP.NormalizedGaussian.componentMagnitude workingConjugate
  apply max_le
  · exact (RFAP.NormalizedGaussian.realMagnitude_le source).trans bounded
  · exact (RFAP.NormalizedFraction.componentMagnitude_neg_le source.im).trans
      ((RFAP.NormalizedGaussian.imaginaryMagnitude_le source).trans bounded)

private theorem parameterConstant_within {value : WorkingGaussian} {bound : Nat}
    (valueBound : gaussianModel.magnitude value ≤ bound) :
    PolynomialWithin gaussianModel (parameterConstant value) bound := by
  unfold parameterConstant
  split
  · exact zero_within gaussianModel bound
  · exact constant_within gaussianModel valueBound

private theorem twiceParameter_within (polynomial : WorkingPolynomial) :
    PolynomialWithin gaussianModel twiceParameter
      (coefficientMagnitude polynomial) := by
  intro candidate member
  simp only [twiceParameter, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with two | zero
  · rw [two]
    exact source_two_within polynomial
  · rw [zero]
    exact source_zero_within polynomial

private theorem twiceShift_within {polynomial : WorkingPolynomial}
    {bound : Nat}
    (zeroBound : gaussianModel.magnitude 0 ≤ bound)
    (twoWithin : PolynomialWithin gaussianModel twiceParameter bound)
    (bounded : PolynomialWithin gaussianModel polynomial bound) :
    PolynomialWithin gaussianModel (twiceShift polynomial)
      (grow gaussianModel bound 4) := by
  unfold twiceShift
  have multiplied := mul_within gaussianModel zeroBound twoWithin bounded
  simpa only [twiceParameter, List.length_cons, List.length_nil,
    Nat.reduceMul] using multiplied

def reflectedRoundSteps : Nat := 6

private theorem reflectedTailStep_within
    {previous : WorkingPolynomial} {bound : Nat}
    (zeroBound : gaussianModel.magnitude 0 ≤ bound)
    (twoWithin : PolynomialWithin gaussianModel twiceParameter bound)
    (previousWithin : PolynomialWithin gaussianModel previous bound) :
    ∀ {coefficients : List WorkingPolynomial},
      (∀ polynomial ∈ coefficients,
        PolynomialWithin gaussianModel polynomial bound) →
      ∀ {output : WorkingPolynomial},
        output ∈ reflectedTailStep previous coefficients →
        PolynomialWithin gaussianModel output
          (grow gaussianModel bound reflectedRoundSteps)
  | [], _, output, member => by
      simp only [reflectedTailStep, List.mem_singleton] at member
      rw [member]
      exact polynomialWithin_mono gaussianModel
        (neg_within gaussianModel previousWithin)
        (grow_mono_steps gaussianModel bound (by decide : 1 ≤ 6))
  | current :: remaining, allWithin, output, member => by
      simp only [reflectedTailStep, List.mem_cons] at member
      rcases member with head | tail
      · rw [head]
        have currentWithin := allWithin current List.mem_cons_self
        have shifted := twiceShift_within zeroBound twoWithin currentWithin
        have previousFour := polynomialWithin_mono gaussianModel previousWithin
          (bound_le_grow gaussianModel bound 4)
        have difference := sub_within gaussianModel
          (zeroBound.trans (bound_le_grow gaussianModel bound 4))
          shifted previousFour
        rw [grow_add] at difference
        exact difference
      · exact reflectedTailStep_within zeroBound twoWithin
          (allWithin current List.mem_cons_self)
          (fun polynomial polynomialMember => allWithin polynomial
            (List.mem_cons_of_mem current polynomialMember)) tail

private theorem reflectedStep_within
    {state : List WorkingPolynomial} {coefficient : WorkingGaussian}
    {bound : Nat}
    (zeroBound : gaussianModel.magnitude 0 ≤ bound)
    (twoWithin : PolynomialWithin gaussianModel twiceParameter bound)
    (stateWithin : ∀ polynomial ∈ state,
      PolynomialWithin gaussianModel polynomial bound)
    (coefficientWithin : gaussianModel.magnitude coefficient ≤ bound) :
    ∀ {output : WorkingPolynomial}, output ∈ reflectedStep state coefficient →
      PolynomialWithin gaussianModel output
        (grow gaussianModel bound reflectedRoundSteps) := by
  cases state with
  | nil =>
      intro output member
      simp only [reflectedStep, List.mem_singleton] at member
      rw [member]
      exact polynomialWithin_mono gaussianModel
        (parameterConstant_within
          (workingConjugate_within coefficientWithin))
        (bound_le_grow gaussianModel bound reflectedRoundSteps)
  | cons head tail =>
      intro output member
      simp only [reflectedStep, List.mem_cons] at member
      rcases member with first | later
      · rw [first]
        have headWithin := stateWithin head List.mem_cons_self
        have shifted := twiceShift_within zeroBound twoWithin headWithin
        have conjugateWithin := workingConjugate_within coefficientWithin
        have negated := gaussianModel.neg_le conjugateWithin
        have constant := parameterConstant_within negated
        have shiftedOne := polynomialWithin_mono gaussianModel shifted
          (grow_mono_steps gaussianModel bound (by decide : 4 ≤ 4))
        have constantFour := polynomialWithin_mono gaussianModel constant
          (grow_mono_steps gaussianModel bound (by decide : 1 ≤ 4))
        have difference := sub_within gaussianModel
          (zeroBound.trans (bound_le_grow gaussianModel bound 4))
          shiftedOne constantFour
        rw [grow_add] at difference
        exact difference
      · exact reflectedTailStep_within zeroBound twoWithin
          (stateWithin head List.mem_cons_self)
          (fun polynomial polynomialMember => stateWithin polynomial
            (List.mem_cons_of_mem head polynomialMember)) later

private theorem fold_reflectedStep_within :
    ∀ (coefficients : List WorkingGaussian)
      (state : List WorkingPolynomial) (bound : Nat),
      gaussianModel.magnitude 0 ≤ bound →
      PolynomialWithin gaussianModel twiceParameter bound →
      (∀ polynomial ∈ state,
        PolynomialWithin gaussianModel polynomial bound) →
      (∀ coefficient ∈ coefficients,
        gaussianModel.magnitude coefficient ≤ bound) →
      ∀ {output : WorkingPolynomial},
        output ∈ coefficients.foldl reflectedStep state →
        PolynomialWithin gaussianModel output
          (grow gaussianModel bound
            (reflectedRoundSteps * coefficients.length))
  | [], _, _, _, _, stateWithin, _, output, member => by
      simpa using stateWithin output member
  | coefficient :: remaining, state, bound, zeroBound, twoWithin,
      stateWithin, coefficientsWithin, output, member => by
      simp only [List.length_cons]
      let nextBound := grow gaussianModel bound reflectedRoundSteps
      have nextState : ∀ polynomial ∈ reflectedStep state coefficient,
          PolynomialWithin gaussianModel polynomial nextBound := by
        intro polynomial polynomialMember
        exact reflectedStep_within zeroBound twoWithin stateWithin
          (coefficientsWithin coefficient List.mem_cons_self) polynomialMember
      have recursive := fold_reflectedStep_within remaining
        (reflectedStep state coefficient) nextBound
        (zeroBound.trans (bound_le_grow gaussianModel bound _))
        (polynomialWithin_mono gaussianModel twoWithin
          (bound_le_grow gaussianModel bound _)) nextState
        (fun candidate candidateMember =>
          (coefficientsWithin candidate
            (List.mem_cons_of_mem coefficient candidateMember)).trans
              (bound_le_grow gaussianModel bound _)) member
      rw [grow_add] at recursive
      simpa only [Nat.mul_succ, Nat.add_comm] using recursive

def reflectedMagnitudeEnvelope (polynomial : WorkingPolynomial) : Nat :=
  grow gaussianModel (coefficientMagnitude polynomial)
    (reflectedRoundSteps * polynomial.normalize.coeffs.length)

theorem reflectedCoefficients_within (polynomial output : WorkingPolynomial)
    (member : output ∈ reflectedCoefficients polynomial) :
    PolynomialWithin gaussianModel output
      (reflectedMagnitudeEnvelope polynomial) := by
  cases coefficients : polynomial.normalize.coeffs with
  | nil =>
      unfold reflectedCoefficients at member
      rw [coefficients] at member
      simp at member
  | cons leading remaining =>
      have sourceWithin := polynomial_within_coefficientMagnitude polynomial
      have normalizedWithin := normalize_within gaussianModel sourceWithin
      have leadingWithin := normalizedWithin leading (by
        rw [coefficients]
        exact List.mem_cons_self)
      have remainingWithin : ∀ coefficient ∈ remaining,
          gaussianModel.magnitude coefficient ≤ coefficientMagnitude polynomial := by
        intro coefficient coefficientMember
        exact normalizedWithin coefficient (by
          rw [coefficients]
          exact List.mem_cons_of_mem leading coefficientMember)
      unfold reflectedCoefficients at member
      rw [coefficients] at member
      have folded := fold_reflectedStep_within remaining
        [parameterConstant (workingConjugate leading)]
        (coefficientMagnitude polynomial)
        (source_zero_within polynomial)
        (twiceParameter_within polynomial)
        (by
          intro state stateMember
          simp only [List.mem_singleton] at stateMember
          rw [stateMember]
          exact parameterConstant_within
            (workingConjugate_within leadingWithin))
        remainingWithin member
      apply polynomialWithin_mono gaussianModel folded
      apply grow_mono_steps gaussianModel (coefficientMagnitude polynomial)
      rw [coefficients]
      simp only [List.length_cons]
      exact Nat.mul_le_mul_left reflectedRoundSteps
        (Nat.le_succ remaining.length)

/-! ## Fraction-free Schur scalar envelope -/

def maxFin : (count : Nat) → (Fin count → Nat) → Nat
  | 0, _ => 0
  | count + 1, values => max (values 0) (maxFin count (fun index => values index.succ))

theorem le_maxFin {count : Nat} (values : Fin count → Nat)
    (index : Fin count) : values index ≤ maxFin count values := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count inductionHypothesis =>
      refine Fin.cases ?_ (fun tail => ?_) index
      · exact le_max_left _ _
      · exact (inductionHypothesis (fun next => values next.succ) tail).trans
          (le_max_right _ _)

def matrixSlotBound {count : Nat} (matrix : WorkingMatrix count) : Nat :=
  maxFin count (fun row => maxFin count (fun column =>
    (matrix row column).coeffs.length))

theorem matrixSlot_le {count : Nat} (matrix : WorkingMatrix count)
    (row column : Fin count) :
    (matrix row column).coeffs.length ≤ matrixSlotBound matrix :=
  (le_maxFin (fun column => (matrix row column).coeffs.length) column).trans
    (le_maxFin (fun row => maxFin count (fun column =>
      (matrix row column).coeffs.length)) row)

def MatrixWithin {count : Nat} (matrix : WorkingMatrix count)
    (bound : Nat) : Prop :=
  ∀ row column, PolynomialWithin gaussianModel (matrix row column) bound

private theorem degreeCount_le_coeffs_length (polynomial : WorkingPolynomial) :
    polynomial.degreeCount ≤ polynomial.coeffs.length := by
  unfold degreeCount
  exact List.Sublist.length_le
    (List.dropWhile_sublist (fun coefficient : WorkingGaussian =>
      decide (coefficient = 0)))

theorem schur_slots {count : Nat} (matrix : WorkingMatrix (count + 1))
    (row column : Fin count) :
    (RFAP.ConstructivePolynomialMatrix.schur matrix row column).coeffs.length ≤
      2 * matrixSlotBound matrix := by
  let first := RFAP.ConstructivePolynomialMatrix.head matrix *
    RFAP.ConstructivePolynomialMatrix.tail matrix row column
  let second := RFAP.ConstructivePolynomialMatrix.leftColumn matrix row *
    RFAP.ConstructivePolynomialMatrix.topRow matrix column
  have headDegree :
      (RFAP.ConstructivePolynomialMatrix.head matrix).degreeCount ≤
        matrixSlotBound matrix :=
    (degreeCount_le_coeffs_length _).trans (matrixSlot_le matrix 0 0)
  have tailDegree :
      (RFAP.ConstructivePolynomialMatrix.tail matrix row column).degreeCount ≤
        matrixSlotBound matrix :=
    (degreeCount_le_coeffs_length _).trans (by
      simpa only [RFAP.ConstructivePolynomialMatrix.tail,
        RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply] using
        matrixSlot_le matrix row.succ column.succ)
  have leftDegree :
      (RFAP.ConstructivePolynomialMatrix.leftColumn matrix row).degreeCount ≤
        matrixSlotBound matrix :=
    (degreeCount_le_coeffs_length _).trans (by
      simpa only [RFAP.ConstructivePolynomialMatrix.leftColumn,
        RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply] using
        matrixSlot_le matrix row.succ 0)
  have topDegree :
      (RFAP.ConstructivePolynomialMatrix.topRow matrix column).degreeCount ≤
        matrixSlotBound matrix :=
    (degreeCount_le_coeffs_length _).trans (by
      simpa only [RFAP.ConstructivePolynomialMatrix.topRow,
        RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply] using
        matrixSlot_le matrix 0 column.succ)
  have firstDegree : first.degreeCount ≤ 2 * matrixSlotBound matrix := by
    refine (degreeCount_mul_le _ _).trans ((Nat.sub_le _ _).trans ?_)
    calc
      (RFAP.ConstructivePolynomialMatrix.head matrix).degreeCount +
            (RFAP.ConstructivePolynomialMatrix.tail matrix row column).degreeCount ≤
          matrixSlotBound matrix + matrixSlotBound matrix :=
        Nat.add_le_add headDegree tailDegree
      _ = 2 * matrixSlotBound matrix := by ring1
  have secondDegree : second.degreeCount ≤ 2 * matrixSlotBound matrix := by
    refine (degreeCount_mul_le _ _).trans ((Nat.sub_le _ _).trans ?_)
    calc
      (RFAP.ConstructivePolynomialMatrix.leftColumn matrix row).degreeCount +
            (RFAP.ConstructivePolynomialMatrix.topRow matrix column).degreeCount ≤
          matrixSlotBound matrix + matrixSlotBound matrix :=
        Nat.add_le_add leftDegree topDegree
      _ = 2 * matrixSlotBound matrix := by ring1
  have differenceDegree : (first - second).degreeCount ≤
      max first.degreeCount second.degreeCount :=
    degreeCount_sub_le_of_normalized (normalize_mul _ _)
  have normalized : (first - second).normalize = first - second :=
    normalize_sub _ _
  simp only [RFAP.ConstructivePolynomialMatrix.schur,
    RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply]
  change (first - second).coeffs.length ≤ _
  change (first - second).normalize.coeffs.length ≤ _ at differenceDegree
  rw [normalized] at differenceDegree
  exact differenceDegree.trans (max_le firstDegree secondDegree)

theorem schur_within {count : Nat}
    {matrix : WorkingMatrix (count + 1)} {bound : Nat}
    (zeroBound : gaussianModel.magnitude 0 ≤ bound)
    (bounded : MatrixWithin matrix bound) :
    MatrixWithin (RFAP.ConstructivePolynomialMatrix.schur matrix)
      (grow gaussianModel bound (2 * matrixSlotBound matrix + 2)) := by
  intro row column
  let slots := matrixSlotBound matrix
  have headWithin : PolynomialWithin gaussianModel
      (RFAP.ConstructivePolynomialMatrix.head matrix) bound := by
    simpa only [RFAP.ConstructivePolynomialMatrix.head] using bounded 0 0
  have tailWithin : PolynomialWithin gaussianModel
      (RFAP.ConstructivePolynomialMatrix.tail matrix row column) bound := by
    simpa only [RFAP.ConstructivePolynomialMatrix.tail,
      RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply] using
      bounded row.succ column.succ
  have leftWithin : PolynomialWithin gaussianModel
      (RFAP.ConstructivePolynomialMatrix.leftColumn matrix row) bound := by
    simpa only [RFAP.ConstructivePolynomialMatrix.leftColumn,
      RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply] using bounded row.succ 0
  have topWithin : PolynomialWithin gaussianModel
      (RFAP.ConstructivePolynomialMatrix.topRow matrix column) bound := by
    simpa only [RFAP.ConstructivePolynomialMatrix.topRow,
      RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply] using bounded 0 column.succ
  have first := mul_within gaussianModel zeroBound headWithin tailWithin
  have second := mul_within gaussianModel zeroBound leftWithin topWithin
  have headLength := matrixSlot_le matrix 0 0
  have leftLength :
      (RFAP.ConstructivePolynomialMatrix.leftColumn matrix row).coeffs.length ≤
        slots := by
    simpa only [RFAP.ConstructivePolynomialMatrix.leftColumn,
      RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply, slots] using
      matrixSlot_le matrix row.succ 0
  have firstBound : PolynomialWithin gaussianModel
      (RFAP.ConstructivePolynomialMatrix.head matrix *
        RFAP.ConstructivePolynomialMatrix.tail matrix row column)
      (grow gaussianModel bound (2 * slots)) :=
    polynomialWithin_mono gaussianModel first
      (grow_mono_steps gaussianModel bound (Nat.mul_le_mul_left 2 headLength))
  have secondBound : PolynomialWithin gaussianModel
      (RFAP.ConstructivePolynomialMatrix.leftColumn matrix row *
        RFAP.ConstructivePolynomialMatrix.topRow matrix column)
      (grow gaussianModel bound (2 * slots)) :=
    polynomialWithin_mono gaussianModel second
      (grow_mono_steps gaussianModel bound (Nat.mul_le_mul_left 2 leftLength))
  have difference := sub_within gaussianModel
    (zeroBound.trans (bound_le_grow gaussianModel bound (2 * slots)))
    firstBound secondBound
  rw [grow_add] at difference
  simpa only [RFAP.ConstructivePolynomialMatrix.schur,
    RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply, slots] using difference

def scaledScalarMagnitudeEnvelope :
    (count : Nat) → WorkingMatrix count → Nat → Nat
  | 0, _, bound => bound
  | count + 1, matrix, bound =>
      let slots := matrixSlotBound matrix
      let schurBound := grow gaussianModel bound (2 * slots + 2)
      let smallerBound := scaledScalarMagnitudeEnvelope count
        (RFAP.ConstructivePolynomialMatrix.schur matrix) schurBound
      grow gaussianModel smallerBound (2 * slots)

theorem scaledScalar_bound_le_envelope :
    ∀ (count : Nat) (matrix : WorkingMatrix count) (bound : Nat),
      bound ≤ scaledScalarMagnitudeEnvelope count matrix bound
  | 0, _, _ => le_refl _
  | count + 1, matrix, bound => by
      dsimp only [scaledScalarMagnitudeEnvelope]
      exact (bound_le_grow gaussianModel bound _).trans
        ((scaledScalar_bound_le_envelope count
          (RFAP.ConstructivePolynomialMatrix.schur matrix)
          (grow gaussianModel bound (2 * matrixSlotBound matrix + 2))).trans
            (bound_le_grow gaussianModel _ _))

theorem scaledInverseScalar_within :
    ∀ (count : Nat) (matrix : WorkingMatrix count) (bound : Nat),
      gaussianModel.magnitude 0 ≤ bound →
      gaussianModel.magnitude (1 : WorkingGaussian) ≤ bound →
      MatrixWithin matrix bound →
      PolynomialWithin gaussianModel
        (RFAP.ConstructivePolynomialMatrix.scaledInverseData count matrix).scalar
        (scaledScalarMagnitudeEnvelope count matrix bound)
  | 0, _, bound, _, oneBound, _ => by
      simpa only [RFAP.ConstructivePolynomialMatrix.scaledInverseData,
        scaledScalarMagnitudeEnvelope]
        using constant_within gaussianModel oneBound
  | count + 1, matrix, bound, zeroBound, oneBound, matrixWithin => by
      let slots := matrixSlotBound matrix
      let schurBound := grow gaussianModel bound (2 * slots + 2)
      let smallerBound := scaledScalarMagnitudeEnvelope count
        (RFAP.ConstructivePolynomialMatrix.schur matrix) schurBound
      have schurWithin := schur_within zeroBound matrixWithin
      have smallerWithin := scaledInverseScalar_within count
        (RFAP.ConstructivePolynomialMatrix.schur matrix) schurBound
        (zeroBound.trans (bound_le_grow gaussianModel bound _))
        (oneBound.trans (bound_le_grow gaussianModel bound _)) schurWithin
      have headWithin := polynomialWithin_mono gaussianModel (matrixWithin 0 0)
        ((bound_le_grow gaussianModel bound _).trans
          (scaledScalar_bound_le_envelope count
            (RFAP.ConstructivePolynomialMatrix.schur matrix) schurBound))
      have product := mul_within gaussianModel
        (zeroBound.trans
          ((bound_le_grow gaussianModel bound _).trans
            (scaledScalar_bound_le_envelope count
              (RFAP.ConstructivePolynomialMatrix.schur matrix) schurBound)))
        headWithin smallerWithin
      have headLength := matrixSlot_le matrix 0 0
      dsimp only [RFAP.ConstructivePolynomialMatrix.scaledInverseData]
      apply polynomialWithin_mono gaussianModel product
      apply grow_mono_steps gaussianModel smallerBound
      exact Nat.mul_le_mul_left 2 headLength

private theorem getD_within {coefficients : List WorkingPolynomial}
    {bound : Nat}
    (allWithin : ∀ polynomial ∈ coefficients,
      PolynomialWithin gaussianModel polynomial bound) (index : Nat) :
    PolynomialWithin gaussianModel (coefficients.getD index 0) bound := by
  induction coefficients generalizing index with
  | nil =>
      simp only [List.getD_nil]
      exact zero_within gaussianModel bound
  | cons head tail inductionHypothesis =>
      cases index with
      | zero =>
          simp only [List.getD_cons_zero]
          exact allWithin head (List.mem_cons_self)
      | succ index =>
          simp only [List.getD_cons_succ]
          apply inductionHypothesis
          intro polynomial member
          exact allWithin polynomial (List.mem_cons_of_mem head member)

private theorem liftedCoefficient_within (polynomial output : WorkingPolynomial)
    (member : output ∈ liftedCoefficients polynomial) :
    PolynomialWithin gaussianModel output
      (reflectedMagnitudeEnvelope polynomial) := by
  unfold liftedCoefficients at member
  rw [QuotientFreeList.mem_map] at member
  rcases member with ⟨coefficient, coefficientMember, rfl⟩
  rw [List.mem_reverse] at coefficientMember
  have source := normalize_within gaussianModel
    (polynomial_within_coefficientMagnitude polynomial)
  have coefficientWithin := source coefficient
    coefficientMember
  exact polynomialWithin_mono gaussianModel
    (parameterConstant_within coefficientWithin)
    (bound_le_grow gaussianModel _ _)

def separatedMatrixMagnitudeEnvelope (polynomial : WorkingPolynomial) : Nat :=
  reflectedMagnitudeEnvelope polynomial

theorem separatedSylvester_within (polynomial : WorkingPolynomial) :
    MatrixWithin (separatedSylvester polynomial)
      (separatedMatrixMagnitudeEnvelope polynomial) := by
  intro row column
  unfold separatedSylvester RFAP.ConstructiveBivariate.sylvester
  simp only [RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply]
  rcases QuotientFreeFin.addCases_split column with
    ⟨left, rfl⟩ | ⟨right, rfl⟩
  · simp only [QuotientFreeFin.addCases_left]
    split
    · unfold RFAP.ConstructiveBivariate.outerCoeff reflected
      apply getD_within
      · intro output member
        have actualMember : output ∈ reflectedCoefficients polynomial := by
          simpa only [List.reverse_reverse] using member
        exact reflectedCoefficients_within polynomial output
          actualMember
    · exact zero_within gaussianModel _
  · simp only [QuotientFreeFin.addCases_right]
    split
    · unfold RFAP.ConstructiveBivariate.outerCoeff lifted
      apply getD_within
      · intro output member
        have actualMember : output ∈ liftedCoefficients polynomial := by
          simpa only [List.reverse_reverse] using member
        exact liftedCoefficient_within polynomial output
          actualMember
    · exact zero_within gaussianModel _

def eliminantMagnitudeEnvelope (polynomial : SemanticPolynomial) : Nat :=
  let working := canonicalPolynomial polynomial
  scaledScalarMagnitudeEnvelope
    ((erasePolynomial working).natDegree + (erasePolynomial working).natDegree)
    (separatedSylvester working) (separatedMatrixMagnitudeEnvelope working)

theorem normalizedScalar_within (polynomial : SemanticPolynomial) :
    PolynomialWithin gaussianModel (normalizedScalar polynomial)
      (eliminantMagnitudeEnvelope polynomial) := by
  let working := canonicalPolynomial polynomial
  unfold normalizedScalar eliminantMagnitudeEnvelope
  apply scaledInverseScalar_within
  · exact (source_zero_within working).trans
      (bound_le_grow gaussianModel _ _)
  · have oneWithin : gaussianModel.magnitude (1 : WorkingGaussian) ≤
        coefficientMagnitude working :=
      ((le_max_right _ _).trans (le_max_right _ _)).trans
        (foldl_max_initial_le working.coeffs _)
    exact oneWithin.trans (bound_le_grow gaussianModel _ _)
  · exact separatedSylvester_within working

/-! ## The two coordinate eliminants used by safe subdivision -/

abbrev WorkingCoordinatePolynomial :=
  RFAP.ComputablePolynomial.DensePolynomial
    RFAP.NormalizedFraction.ReducedFraction
abbrev SemanticCoordinatePolynomial :=
  RFAP.ComputablePolynomial.DensePolynomial
    RFAP.ConstructiveFraction.Rational

def workingRealPart (polynomial : WorkingPolynomial) :
    WorkingCoordinatePolynomial :=
  ⟨polynomial.coeffs.map RFAP.NormalizedGaussian.Gaussian.re⟩

def workingImagPart (polynomial : WorkingPolynomial) :
    WorkingCoordinatePolynomial :=
  ⟨polynomial.coeffs.map RFAP.NormalizedGaussian.Gaussian.im⟩

def eraseCoordinatePolynomial (polynomial : WorkingCoordinatePolynomial) :
    SemanticCoordinatePolynomial :=
  ⟨polynomial.coeffs.map RFAP.NormalizedFraction.value⟩

theorem erase_workingRealPart (polynomial : WorkingPolynomial) :
    eraseCoordinatePolynomial (workingRealPart polynomial) =
      RFAP.PathPolynomial.realPart (erasePolynomial polynomial) := by
  apply RFAP.ComputablePolynomial.DensePolynomial.ext
  simp only [eraseCoordinatePolynomial, workingRealPart, erasePolynomial,
    RFAP.ComputablePolynomialMap.map_coeffs,
    RFAP.PathPolynomial.realPart, List.map_map]
  rfl

theorem erase_workingImagPart (polynomial : WorkingPolynomial) :
    eraseCoordinatePolynomial (workingImagPart polynomial) =
      RFAP.PathPolynomial.imagPart (erasePolynomial polynomial) := by
  apply RFAP.ComputablePolynomial.DensePolynomial.ext
  simp only [eraseCoordinatePolynomial, workingImagPart, erasePolynomial,
    RFAP.ComputablePolynomialMap.map_coeffs,
    RFAP.PathPolynomial.imagPart, List.map_map]
  rfl

def normalizedEliminant (polynomial : SemanticPolynomial) :
    WorkingCoordinatePolynomial :=
  if (leadingCoeff
      (RFAP.ConstructiveSylvesterBezout.separatedData polynomial).scalar).re =
      0 then
    workingImagPart (normalizedScalar polynomial)
  else workingRealPart (normalizedScalar polynomial)

private theorem scaledInverseScalar_normalized :
    ∀ (count : Nat) (matrix :
      RFAP.ConstructivePolynomialMatrix.Matrix SemanticGaussian count),
      ((RFAP.ConstructivePolynomialMatrix.scaledInverseData count matrix).scalar
          ).normalize =
        (RFAP.ConstructivePolynomialMatrix.scaledInverseData count matrix).scalar
  | 0, _ => by
      simp only [RFAP.ConstructivePolynomialMatrix.scaledInverseData]
      exact normalize_constant_of_ne one_ne_zero
  | count + 1, matrix => by
      dsimp only [RFAP.ConstructivePolynomialMatrix.scaledInverseData]
      exact normalize_mul _ _

theorem erase_normalizedEliminant (polynomial : SemanticPolynomial) :
    eraseCoordinatePolynomial (normalizedEliminant polynomial) =
      RFAP.ConstructiveSylvesterBezout.scalarEliminant polynomial := by
  unfold normalizedEliminant
    RFAP.ConstructiveSylvesterBezout.scalarEliminant
    RFAP.ConstructiveSylvesterBezout.selectedCoordinate
  split
  · rw [erase_workingImagPart, erase_normalizedScalar]
    unfold RFAP.ConstructiveSylvesterBezout.separatedData
    rw [scaledInverseScalar_normalized]
  · rw [erase_workingRealPart, erase_normalizedScalar]
    unfold RFAP.ConstructiveSylvesterBezout.separatedData
    rw [scaledInverseScalar_normalized]

theorem normalizedEliminant_within (polynomial : SemanticPolynomial) :
    PolynomialWithin rationalModel (normalizedEliminant polynomial)
      (eliminantMagnitudeEnvelope polynomial) := by
  have scalarWithin := normalizedScalar_within polynomial
  unfold normalizedEliminant
  split
  · intro candidate member
    unfold workingImagPart at member
    rw [QuotientFreeList.mem_map] at member
    rcases member with ⟨source, sourceMember, rfl⟩
    exact (RFAP.NormalizedGaussian.imaginaryMagnitude_le source).trans
      (scalarWithin source sourceMember)
  · intro candidate member
    unfold workingRealPart at member
    rw [QuotientFreeList.mem_map] at member
    rcases member with ⟨source, sourceMember, rfl⟩
    exact (RFAP.NormalizedGaussian.realMagnitude_le source).trans
      (scalarWithin source sourceMember)

def normalizedHorizontalEliminant (polynomial : SemanticPolynomial) :
    WorkingCoordinatePolynomial :=
  normalizedEliminant
    (RFAP.ConstructiveSylvesterBezout.quarterTurn polynomial)

theorem erase_normalizedHorizontalEliminant (polynomial : SemanticPolynomial) :
    eraseCoordinatePolynomial (normalizedHorizontalEliminant polynomial) =
      RFAP.ConstructiveSylvesterBezout.horizontalEliminant polynomial := by
  exact erase_normalizedEliminant
    (RFAP.ConstructiveSylvesterBezout.quarterTurn polynomial)

theorem normalizedHorizontalEliminant_within
    (polynomial : SemanticPolynomial) :
    PolynomialWithin rationalModel (normalizedHorizontalEliminant polynomial)
      (eliminantMagnitudeEnvelope
        (RFAP.ConstructiveSylvesterBezout.quarterTurn polynomial)) :=
  normalizedEliminant_within
    (RFAP.ConstructiveSylvesterBezout.quarterTurn polynomial)

end RFAP.NormalizedEliminant
