import mathlib.Data.ConstructiveList
import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import RFAP.Geometry.PathClearance
import mathlib.RFAP.NormalizedFraction

/-!
# Bounded constructive safe-candidate search

The finite search in this module does not appeal to a root set or to RFAP.  Its
degree bound is proved directly by synthetic division of coefficient lists:
after removing one displayed root, every remaining distinct displayed root
is a root of the strictly shorter quotient list.
-/

namespace RFAP.SafeCandidates

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Polynomial := RFAP.ComputablePolynomial.DensePolynomial Coordinate

open RFAP.ComputablePolynomial.DensePolynomial

/-! ## Direct finite root bound -/

/-- Synthetic division state for a normalized high-to-low coefficient list.
For the polynomial with coefficients `leading :: remaining`, the first output
is the quotient by `X - root` and the second is the remainder. -/
def syntheticAux (root leading : Coordinate) :
    List Coordinate → List Coordinate × Coordinate
  | [] => ([], leading)
  | coefficient :: remaining =>
      let result := syntheticAux root (leading * root + coefficient) remaining
      (leading :: result.1, result.2)

private theorem evalCoeffs_cons_power (x leading : Coordinate)
    (remaining : List Coordinate) :
    evalCoeffs x (leading :: remaining) =
      leading * x ^ remaining.length + evalCoeffs x remaining := by
  induction remaining generalizing leading with
  | nil =>
      simp only [evalCoeffs_cons, List.foldl_nil, List.length_nil, pow_zero,
        evalCoeffs_nil]
      ring1
  | cons coefficient remaining inductionHypothesis =>
      rw [evalCoeffs_cons]
      simp only [List.foldl_cons]
      rw [← evalCoeffs_cons x (leading * x + coefficient) remaining,
        inductionHypothesis (leading * x + coefficient),
        inductionHypothesis coefficient]
      simp only [List.length_cons, pow_succ]
      ring1

private theorem syntheticAux_spec (root leading : Coordinate)
    (remaining : List Coordinate) :
    let result := syntheticAux root leading remaining
    result.1.length = remaining.length ∧
      result.2 = evalCoeffs root (leading :: remaining) ∧
      ∀ x : Coordinate,
        evalCoeffs x (leading :: remaining) =
          (x - root) * evalCoeffs x result.1 + result.2 := by
  induction remaining generalizing leading with
  | nil =>
      constructor
      · rfl
      constructor
      · change leading = evalCoeffs root [leading]
        simp only [evalCoeffs_cons, List.foldl_nil]
      · intro x
        change evalCoeffs x [leading] =
          (x - root) * evalCoeffs x [] + leading
        simp only [evalCoeffs_cons, List.foldl_nil, evalCoeffs_nil, mul_zero,
          zero_add]
  | cons coefficient remaining inductionHypothesis =>
      let nextLeading := leading * root + coefficient
      let recursive := syntheticAux root nextLeading remaining
      have recursiveSpec := inductionHypothesis nextLeading
      change recursive.1.length = remaining.length ∧
        recursive.2 = evalCoeffs root (nextLeading :: remaining) ∧
        ∀ x : Coordinate,
          evalCoeffs x (nextLeading :: remaining) =
            (x - root) * evalCoeffs x recursive.1 + recursive.2 at recursiveSpec
      change
        (leading :: recursive.1).length =
            (coefficient :: remaining).length ∧
          recursive.2 =
            evalCoeffs root (leading :: coefficient :: remaining) ∧
          ∀ x : Coordinate,
            evalCoeffs x (leading :: coefficient :: remaining) =
              (x - root) * evalCoeffs x (leading :: recursive.1) +
                recursive.2
      constructor
      · simp only [List.length_cons]
        exact congrArg Nat.succ recursiveSpec.1
      constructor
      · rw [evalCoeffs_cons]
        simp only [List.foldl_cons]
        rw [← evalCoeffs_cons root nextLeading remaining]
        exact recursiveSpec.2.1
      · intro x
        have recursiveFactor := recursiveSpec.2.2 x
        calc
          evalCoeffs x (leading :: coefficient :: remaining) =
              leading * x ^ (remaining.length + 1) +
                coefficient * x ^ remaining.length +
                evalCoeffs x remaining := by
            rw [evalCoeffs_cons_power x leading (coefficient :: remaining),
              evalCoeffs_cons_power x coefficient remaining]
            simp only [List.length_cons]
            ring1
          _ = (x - root) * (leading * x ^ remaining.length) +
                evalCoeffs x (nextLeading :: remaining) := by
            rw [evalCoeffs_cons_power x nextLeading remaining, pow_succ]
            dsimp only [nextLeading]
            ring1
          _ = (x - root) * (leading * x ^ remaining.length) +
                ((x - root) * evalCoeffs x recursive.1 + recursive.2) := by
            rw [recursiveFactor]
          _ = (x - root) *
                (leading * x ^ remaining.length +
                  evalCoeffs x recursive.1) + recursive.2 := by
            ring1
          _ = (x - root) * evalCoeffs x (leading :: recursive.1) +
                recursive.2 := by
            rw [evalCoeffs_cons_power, recursiveSpec.1]

/-- A nonzero dense polynomial cannot vanish at as many distinct displayed
coordinates as its number of normalized coefficient slots.  This is the
elementary finite root bound, proved without RFAP. -/
theorem nodup_zeros_length_lt_degreeCount (p : Polynomial)
    (nonzero : p.isZero = false) (points : List Coordinate)
    (nodup : points.Nodup)
    (zeros : ∀ x ∈ points, p.eval x = 0) :
    points.length < p.degreeCount := by
  generalize degreeEquation : p.degreeCount = degree
  induction degree using Nat.strong_induction_on generalizing p points with
  | h degree inductionHypothesis =>
      have degreePositive := degreeCount_pos_of_isZero_false nonzero
      rw [degreeEquation] at degreePositive
      cases points with
      | nil =>
          simp only [List.length_nil]
          exact degreePositive
      | cons root otherPoints =>
          have normalizedNonempty : p.normalize.coeffs ≠ [] := by
            intro empty
            have normalizedNonzero := nonzero
            change p.normalize.coeffs.isEmpty = false at normalizedNonzero
            rw [empty] at normalizedNonzero
            exact Bool.noConfusion normalizedNonzero
          cases coefficientsEquation : p.normalize.coeffs with
          | nil => exact (normalizedNonempty coefficientsEquation).elim
          | cons leading remaining =>
              have leadingNonzero : leading ≠ 0 := by
                have headNonzero := leadingCoeff_ne_zero nonzero
                change p.normalize.coeffs.headD 0 ≠ 0 at headNonzero
                simpa only [coefficientsEquation, List.headD_cons]
                  using headNonzero
              cases remaining with
              | nil =>
                  have rootZero := zeros root (by simp)
                  have normalizedRootZero : p.normalize.eval root = 0 := by
                    simpa only [eval_normalize] using rootZero
                  change evalCoeffs root p.normalize.coeffs = 0 at normalizedRootZero
                  rw [coefficientsEquation] at normalizedRootZero
                  simp only [evalCoeffs_cons, List.foldl_nil] at normalizedRootZero
                  exact (leadingNonzero normalizedRootZero).elim
              | cons coefficient remaining =>
                  let division := syntheticAux root leading
                    (coefficient :: remaining)
                  let quotient : Polynomial := ⟨division.1⟩
                  have divisionSpec := syntheticAux_spec root leading
                    (coefficient :: remaining)
                  have quotientCoefficients : quotient.coeffs =
                      leading ::
                        (syntheticAux root
                          (leading * root + coefficient) remaining).1 := rfl
                  have quotientNonzero : quotient.isZero = false := by
                    simp [isZero, normalize, quotientCoefficients,
                      leadingNonzero]
                  have quotientDegree : quotient.degreeCount =
                      (coefficient :: remaining).length := by
                    calc
                      quotient.degreeCount = quotient.normalize.coeffs.length :=
                        rfl
                      _ = quotient.coeffs.length := by
                        rw [normalize_coeffs, quotientCoefficients,
                          List.dropWhile_cons_of_neg
                            (by simp [leadingNonzero])]
                      _ = division.1.length := rfl
                      _ = (coefficient :: remaining).length := divisionSpec.1
                  have originalDegree : p.degreeCount =
                      (leading :: coefficient :: remaining).length := by
                    simp only [degreeCount, coefficientsEquation]
                  have quotientSmaller : quotient.degreeCount < degree := by
                    rw [quotientDegree, ← degreeEquation, originalDegree]
                    exact Nat.lt_succ_self _
                  have remainderZero : division.2 = 0 := by
                    rw [divisionSpec.2.1]
                    rw [← coefficientsEquation]
                    change p.normalize.eval root = 0
                    rw [eval_normalize]
                    exact zeros root (by simp)
                  have otherZeros : ∀ x ∈ otherPoints,
                      quotient.eval x = 0 := by
                    intro x member
                    have originalZero := zeros x (by simp [member])
                    have factor := divisionSpec.2.2 x
                    rw [← coefficientsEquation] at factor
                    change p.normalize.eval x =
                      (x - root) * quotient.eval x + division.2 at factor
                    rw [eval_normalize, originalZero, remainderZero] at factor
                    have productZero : (x - root) * quotient.eval x = 0 := by
                      calc
                        (x - root) * quotient.eval x =
                            (x - root) * quotient.eval x + 0 := by ring1
                        _ = 0 := factor.symm
                    have distinct : x ≠ root := by
                      intro equal
                      subst x
                      exact (List.nodup_cons.mp nodup).1 member
                    have differenceNonzero : x - root ≠ 0 :=
                      sub_ne_zero.mpr distinct
                    by_cases quotientZero : quotient.eval x = 0
                    · exact quotientZero
                    · have productNonzero :
                          (x - root) * quotient.eval x ≠ 0 :=
                        RFAP.ConstructiveFraction.mul_ne_zero_direct
                          differenceNonzero quotientZero
                      exact (productNonzero productZero).elim
                  have recursive := inductionHypothesis quotient.degreeCount
                    quotientSmaller quotient quotientNonzero otherPoints
                    (List.nodup_cons.mp nodup).2 otherZeros rfl
                  simp only [List.length_cons]
                  exact (Nat.succ_le_of_lt recursive).trans_lt quotientSmaller

/-! ## Executable finite search -/

/-- Return the first displayed point where `p` is nonzero. -/
def firstNonzero (p : Polynomial) : List Coordinate → Option Coordinate
  | [] => none
  | x :: remaining =>
      if p.eval x = 0 then firstNonzero p remaining else some x

theorem firstNonzero_some_spec {p : Polynomial} {points : List Coordinate}
    {x : Coordinate} (found : firstNonzero p points = some x) :
    x ∈ points ∧ p.eval x ≠ 0 := by
  induction points with
  | nil => simp [firstNonzero] at found
  | cons candidate remaining inductionHypothesis =>
      by_cases candidateZero : p.eval candidate = 0
      · rw [firstNonzero, if_pos candidateZero] at found
        rcases inductionHypothesis found with ⟨member, nonzero⟩
        exact ⟨List.mem_cons_of_mem candidate member, nonzero⟩
      · rw [firstNonzero, if_neg candidateZero] at found
        injection found with equal
        subst x
        exact ⟨by simp, candidateZero⟩

theorem firstNonzero_eq_none_iff (p : Polynomial)
    (points : List Coordinate) :
    firstNonzero p points = none ↔
      ∀ x ∈ points, p.eval x = 0 := by
  induction points with
  | nil =>
      constructor
      · intro _ x impossible
        nomatch impossible
      · intro _
        rfl
  | cons candidate remaining inductionHypothesis =>
      constructor
      · intro search x member
        by_cases candidateZero : p.eval candidate = 0
        · rw [firstNonzero, if_pos candidateZero] at search
          rcases List.mem_cons.mp member with equal | tailMember
          · exact equal ▸ candidateZero
          · exact inductionHypothesis.mp search x tailMember
        · rw [firstNonzero, if_neg candidateZero] at search
          nomatch search
      · intro allZero
        have candidateZero : p.eval candidate = 0 :=
          allZero candidate List.mem_cons_self
        rw [firstNonzero, if_pos candidateZero]
        apply inductionHypothesis.mpr
        intro x member
        exact allZero x (List.mem_cons_of_mem candidate member)

theorem firstNonzero_exists (p : Polynomial) (points : List Coordinate)
    (nonzero : p.isZero = false) (nodup : points.Nodup)
    (degreeBound : p.degreeCount ≤ points.length) :
    ∃ x, firstNonzero p points = some x := by
  cases search : firstNonzero p points with
  | none =>
      have allZero := (firstNonzero_eq_none_iff p points).mp search
      have impossible := nodup_zeros_length_lt_degreeCount p nonzero points
        nodup allZero
      exact (Nat.not_lt_of_ge degreeBound impossible).elim
  | some x => exact ⟨x, rfl⟩

/-! ## Equally spaced interior candidates -/

def interiorStep (a b : Coordinate) (degreeBound : Nat) : Coordinate :=
  RFAP.NormalizedFraction.normalizedDiv
    (RFAP.NormalizedFraction.normalizedSub b a)
    (degreeBound + 2 : Nat)

def interiorCandidate (a b : Coordinate) (degreeBound : Nat)
    (index : Fin (degreeBound + 1)) : Coordinate :=
  RFAP.NormalizedFraction.normalizedAdd a
    (RFAP.NormalizedFraction.normalizedMul (index.val + 1 : Nat)
      (interiorStep a b degreeBound))

def interiorCandidates (a b : Coordinate) (degreeBound : Nat) :
    List Coordinate :=
  List.ofFn (interiorCandidate a b degreeBound)

private theorem natCast_pos {n : Nat} (positive : 0 < n) :
    (0 : Coordinate) < (n : Nat) := by
  exact RFAP.ConstructiveFraction.natCast_pos_direct positive

theorem interiorStep_pos {a b : Coordinate} (less : a < b)
    (degreeBound : Nat) : 0 < interiorStep a b degreeBound := by
  simp only [interiorStep, RFAP.NormalizedFraction.normalizedDiv_eq,
    RFAP.NormalizedFraction.normalizedSub_eq]
  apply RFAP.ConstructiveFraction.div_pos_direct
  · exact RFAP.ConstructiveFraction.sub_pos_direct less
  · exact natCast_pos (Nat.zero_lt_succ _)

theorem interiorCandidate_injective {a b : Coordinate} (less : a < b)
    (degreeBound : Nat) :
    Function.Injective (interiorCandidate a b degreeBound) := by
  intro first second equal
  apply Fin.ext
  have productsEqual :
      ((first.val + 1 : Nat) : Coordinate) * interiorStep a b degreeBound =
        ((second.val + 1 : Nat) : Coordinate) *
          interiorStep a b degreeBound := by
    apply add_left_cancel
    simpa only [interiorCandidate,
      RFAP.NormalizedFraction.normalizedAdd_eq,
      RFAP.NormalizedFraction.normalizedMul_eq] using equal
  have castsEqual := RFAP.ConstructiveFraction.mul_right_cancel_of_ne
    (interiorStep_pos less degreeBound).ne' productsEqual
  have sumsEqual : first.val + 1 = second.val + 1 := by
    exact RFAP.ConstructiveFraction.natCast_injective_direct castsEqual
  exact Nat.add_right_cancel sumsEqual

private theorem nodup_ofFn_direct {n : Nat} (f : Fin n → Coordinate)
    (injective : Function.Injective f) : (List.ofFn f).Nodup := by
  induction n with
  | zero => simp only [List.ofFn_zero, List.nodup_nil]
  | succ n inductionHypothesis =>
      rw [QuotientFreeList.ofFn_succ, List.nodup_cons]
      constructor
      · intro member
        rw [List.mem_ofFn] at member
        rcases member with ⟨index, equal⟩
        have impossible : index.succ = (0 : Fin (n + 1)) :=
          injective equal
        exact Fin.succ_ne_zero index impossible
      · apply inductionHypothesis
        intro first second equal
        apply Fin.ext
        have values := congrArg Fin.val (injective equal)
        simp only [Fin.val_succ] at values
        exact Nat.add_right_cancel values

theorem interiorCandidates_nodup {a b : Coordinate} (less : a < b)
    (degreeBound : Nat) : (interiorCandidates a b degreeBound).Nodup :=
  nodup_ofFn_direct _ (interiorCandidate_injective less degreeBound)

@[simp] theorem interiorCandidates_length (a b : Coordinate)
    (degreeBound : Nat) :
    (interiorCandidates a b degreeBound).length = degreeBound + 1 := by
  exact QuotientFreeList.length_ofFn

theorem interiorStep_scaled (a b : Coordinate) (degreeBound : Nat) :
    ((degreeBound + 2 : Nat) : Coordinate) *
        interiorStep a b degreeBound = b - a := by
  simp only [interiorStep, RFAP.NormalizedFraction.normalizedDiv_eq,
    RFAP.NormalizedFraction.normalizedSub_eq]
  rw [RFAP.ConstructiveFraction.mul_comm]
  exact RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _
    (natCast_pos (Nat.zero_lt_succ _)).ne'

theorem interiorCandidate_bounds {a b : Coordinate} (less : a < b)
    (degreeBound : Nat) (index : Fin (degreeBound + 1)) :
    a < interiorCandidate a b degreeBound index ∧
      interiorCandidate a b degreeBound index < b := by
  have stepPositive := interiorStep_pos less degreeBound
  have indexPositive :
      (0 : Coordinate) < ((index.val + 1 : Nat) : Coordinate) :=
    natCast_pos (Nat.zero_lt_succ _)
  have offsetPositive : 0 <
      ((index.val + 1 : Nat) : Coordinate) *
        interiorStep a b degreeBound := by
    have multiplied := mul_lt_mul_of_pos_right indexPositive stepPositive
    have zeroProduct : (0 : Coordinate) *
        interiorStep a b degreeBound = 0 := by
      rw [RFAP.ConstructiveFraction.mul_comm,
        RFAP.ConstructiveFraction.mul_zero_direct]
    rwa [zeroProduct] at multiplied
  have indexLessNat : index.val + 1 < degreeBound + 2 :=
    Nat.add_lt_add_right index.isLt 1
  have indexLess :
      ((index.val + 1 : Nat) : Coordinate) <
        ((degreeBound + 2 : Nat) : Coordinate) := by
    exact RFAP.ConstructiveFraction.natCast_lt_direct indexLessNat
  have offsetLess :
      ((index.val + 1 : Nat) : Coordinate) *
          interiorStep a b degreeBound < b - a := by
    have multiplied := mul_lt_mul_of_pos_right indexLess stepPositive
    rw [interiorStep_scaled] at multiplied
    exact multiplied
  constructor
  · calc
      a = a + 0 := by ring1
      _ < a + ((index.val + 1 : Nat) : Coordinate) *
          interiorStep a b degreeBound :=
        RFAP.ConstructiveFraction.add_lt_add_left_direct offsetPositive a
      _ = interiorCandidate a b degreeBound index := by
        symm
        simp only [interiorCandidate,
          RFAP.NormalizedFraction.normalizedAdd_eq,
          RFAP.NormalizedFraction.normalizedMul_eq]
  · calc
      interiorCandidate a b degreeBound index =
          a + ((index.val + 1 : Nat) : Coordinate) *
            interiorStep a b degreeBound := by
        simp only [interiorCandidate,
          RFAP.NormalizedFraction.normalizedAdd_eq,
          RFAP.NormalizedFraction.normalizedMul_eq]
      _ < a + (b - a) :=
        RFAP.ConstructiveFraction.add_lt_add_left_direct offsetLess a
      _ = b := by ring1

/-- Each selected point leaves both subintervals no longer than `D+1`
candidate spacings. -/
theorem interiorCandidate_contraction {a b : Coordinate} (less : a < b)
    (degreeBound : Nat) (index : Fin (degreeBound + 1)) :
    interiorCandidate a b degreeBound index - a ≤
        ((degreeBound + 1 : Nat) : Coordinate) *
          interiorStep a b degreeBound ∧
      b - interiorCandidate a b degreeBound index ≤
        ((degreeBound + 1 : Nat) : Coordinate) *
          interiorStep a b degreeBound := by
  have stepPositive := interiorStep_pos less degreeBound
  have indexUpperNat : index.val + 1 ≤ degreeBound + 1 :=
    Nat.succ_le_iff.mpr index.isLt
  have indexUpper :
      ((index.val + 1 : Nat) : Coordinate) ≤
        ((degreeBound + 1 : Nat) : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_le_direct indexUpperNat
  have leftBound :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      indexUpper stepPositive.le
  have indexLowerNat : 1 ≤ index.val + 1 :=
    Nat.succ_le_succ (Nat.zero_le _)
  have indexLower : (1 : Coordinate) ≤
      ((index.val + 1 : Nat) : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_le_direct indexLowerNat
  have offsetLower :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      indexLower stepPositive.le
  have offsetLower' : interiorStep a b degreeBound ≤
      ((index.val + 1 : Nat) : Coordinate) *
        interiorStep a b degreeBound := by
    simpa only [one_mul] using offsetLower
  constructor
  · calc
      interiorCandidate a b degreeBound index - a =
          ((index.val + 1 : Nat) : Coordinate) *
            interiorStep a b degreeBound := by
        simp only [interiorCandidate,
          RFAP.NormalizedFraction.normalizedAdd_eq,
          RFAP.NormalizedFraction.normalizedMul_eq]
        ring1
      _ ≤ ((degreeBound + 1 : Nat) : Coordinate) *
          interiorStep a b degreeBound := leftBound
  · calc
      b - interiorCandidate a b degreeBound index =
          (b - a) - ((index.val + 1 : Nat) : Coordinate) *
            interiorStep a b degreeBound := by
        simp only [interiorCandidate,
          RFAP.NormalizedFraction.normalizedAdd_eq,
          RFAP.NormalizedFraction.normalizedMul_eq]
        ring1
      _ ≤ (b - a) - interiorStep a b degreeBound :=
        RFAP.ConstructiveFraction.sub_le_sub_left_direct offsetLower' (b - a)
      _ = ((degreeBound + 2 : Nat) : Coordinate) *
            interiorStep a b degreeBound -
          interiorStep a b degreeBound := by
        rw [interiorStep_scaled]
      _ = ((degreeBound + 1 : Nat) : Coordinate) *
            interiorStep a b degreeBound := by
        simp only [Nat.cast_add, Nat.cast_ofNat]
        ring1

/-- Finite search through the `D+1` displayed interior candidates. -/
def interiorSearch (p : Polynomial) (a b : Coordinate)
    (degreeBound : Nat) : Option Coordinate :=
  firstNonzero p (interiorCandidates a b degreeBound)

theorem interiorSearch_succeeds (p : Polynomial) {a b : Coordinate}
    (degreeBound : Nat) (less : a < b) (nonzero : p.isZero = false)
    (degree : p.natDegree ≤ degreeBound) :
    ∃ x, interiorSearch p a b degreeBound = some x := by
  apply firstNonzero_exists p (interiorCandidates a b degreeBound) nonzero
    (interiorCandidates_nodup less degreeBound)
  rw [interiorCandidates_length]
  have count := natDegree_add_one_eq_degreeCount nonzero
  rw [← count]
  exact Nat.add_le_add_right degree 1

theorem interiorSearch_isSome (p : Polynomial) {a b : Coordinate}
    (degreeBound : Nat) (less : a < b) (nonzero : p.isZero = false)
    (degree : p.natDegree ≤ degreeBound) :
    (interiorSearch p a b degreeBound).isSome := by
  rcases interiorSearch_succeeds p degreeBound less nonzero degree with
    ⟨x, found⟩
  rw [found]
  rfl

/-- Total executable projection of the successful finite scan. -/
def interiorSearchValue (p : Polynomial) {a b : Coordinate}
    (degreeBound : Nat) (less : a < b) (nonzero : p.isZero = false)
    (degree : p.natDegree ≤ degreeBound) : Coordinate :=
  (interiorSearch p a b degreeBound).get
    (interiorSearch_isSome p degreeBound less nonzero degree)

theorem interiorSearchValue_spec (p : Polynomial) {a b : Coordinate}
    (degreeBound : Nat) (less : a < b) (nonzero : p.isZero = false)
    (degree : p.natDegree ≤ degreeBound) :
    p.eval (interiorSearchValue p degreeBound less nonzero degree) ≠ 0 ∧
      a < interiorSearchValue p degreeBound less nonzero degree ∧
      interiorSearchValue p degreeBound less nonzero degree < b := by
  let search := interiorSearch p a b degreeBound
  have isSome : search.isSome :=
    interiorSearch_isSome p degreeBound less nonzero degree
  have found : search = some (search.get isSome) :=
    Option.eq_some_of_isSome isSome
  rcases firstNonzero_some_spec found with ⟨member, valueNonzero⟩
  rw [interiorCandidates, List.mem_ofFn] at member
  rcases member with ⟨index, equal⟩
  have candidateNonzero :
      p.eval (interiorCandidate a b degreeBound index) ≠ 0 := by
    rw [equal]
    exact valueNonzero
  have selectedEqual :
      interiorSearchValue p degreeBound less nonzero degree =
        interiorCandidate a b degreeBound index := by
    change (interiorSearch p a b degreeBound).get _ = _
    change search.get _ = _
    exact equal.symm
  rw [selectedEqual]
  exact And.intro candidateNonzero
    (interiorCandidate_bounds less degreeBound index)

theorem interiorSearchValue_mem (p : Polynomial) {a b : Coordinate}
    (degreeBound : Nat) (less : a < b) (nonzero : p.isZero = false)
    (degree : p.natDegree ≤ degreeBound) :
    interiorSearchValue p degreeBound less nonzero degree ∈
      interiorCandidates a b degreeBound := by
  let search := interiorSearch p a b degreeBound
  have isSome : search.isSome :=
    interiorSearch_isSome p degreeBound less nonzero degree
  have found : search = some (search.get isSome) :=
    Option.eq_some_of_isSome isSome
  exact (firstNonzero_some_spec found).1

theorem interiorSearchValue_contraction (p : Polynomial)
    {a b : Coordinate} (degreeBound : Nat) (less : a < b)
    (nonzero : p.isZero = false) (degree : p.natDegree ≤ degreeBound) :
    interiorSearchValue p degreeBound less nonzero degree - a ≤
        ((degreeBound + 1 : Nat) : Coordinate) *
          interiorStep a b degreeBound ∧
      b - interiorSearchValue p degreeBound less nonzero degree ≤
        ((degreeBound + 1 : Nat) : Coordinate) *
          interiorStep a b degreeBound := by
  let search := interiorSearch p a b degreeBound
  have isSome : search.isSome :=
    interiorSearch_isSome p degreeBound less nonzero degree
  have found : search = some (search.get isSome) :=
    Option.eq_some_of_isSome isSome
  have member := (firstNonzero_some_spec found).1
  rw [interiorCandidates, List.mem_ofFn] at member
  rcases member with ⟨index, equal⟩
  have selectedEqual :
      interiorSearchValue p degreeBound less nonzero degree =
        interiorCandidate a b degreeBound index := by
    change (interiorSearch p a b degreeBound).get _ = _
    change search.get _ = _
    exact equal.symm
  rw [selectedEqual]
  exact interiorCandidate_contraction less degreeBound index

/-! ## Central-third safe cuts -/

def centralLower (a b : Coordinate) : Coordinate :=
  RFAP.NormalizedFraction.normalizedAdd a
    (RFAP.NormalizedFraction.normalizedDiv
      (RFAP.NormalizedFraction.normalizedSub b a) 3)

def centralUpper (a b : Coordinate) : Coordinate :=
  RFAP.NormalizedFraction.normalizedAdd a
    (RFAP.NormalizedFraction.normalizedMul 2
      (RFAP.NormalizedFraction.normalizedDiv
        (RFAP.NormalizedFraction.normalizedSub b a) 3))

theorem centralBounds {a b : Coordinate} (less : a < b) :
    a < centralLower a b ∧
      centralLower a b < centralUpper a b ∧
      centralUpper a b < b := by
  have thirdPositive : 0 < (b - a) / 3 :=
    RFAP.ConstructiveFraction.div_pos_direct
      (RFAP.ConstructiveFraction.sub_pos_direct less) (by decide)
  have thirdScaled : (3 : Coordinate) * ((b - a) / 3) = b - a := by
    rw [RFAP.ConstructiveFraction.mul_comm]
    exact RFAP.ConstructiveFraction.div_mul_cancel_of_ne
      (b - a) 3 (by decide)
  constructor
  · simp only [centralLower, RFAP.NormalizedFraction.normalizedAdd_eq,
      RFAP.NormalizedFraction.normalizedDiv_eq,
      RFAP.NormalizedFraction.normalizedSub_eq]
    calc
      a = a + 0 := by ring1
      _ < a + (b - a) / 3 :=
        RFAP.ConstructiveFraction.add_lt_add_left_direct thirdPositive a
  constructor
  · have shifted :=
      RFAP.ConstructiveFraction.add_lt_add_left_direct thirdPositive
        (centralLower a b)
    calc
      centralLower a b = centralLower a b + 0 := by ring1
      _ < centralLower a b + (b - a) / 3 := shifted
      _ = centralUpper a b := by
        simp only [centralLower, centralUpper,
          RFAP.NormalizedFraction.normalizedAdd_eq,
          RFAP.NormalizedFraction.normalizedMul_eq,
          RFAP.NormalizedFraction.normalizedDiv_eq,
          RFAP.NormalizedFraction.normalizedSub_eq]
        ring1
  · have shifted :=
      RFAP.ConstructiveFraction.add_lt_add_left_direct thirdPositive
        (centralUpper a b)
    calc
      centralUpper a b = centralUpper a b + 0 := by ring1
      _ < centralUpper a b + (b - a) / 3 := shifted
      _ = b := by
        simp only [centralUpper,
          RFAP.NormalizedFraction.normalizedAdd_eq,
          RFAP.NormalizedFraction.normalizedMul_eq,
          RFAP.NormalizedFraction.normalizedDiv_eq,
          RFAP.NormalizedFraction.normalizedSub_eq]
        calc
          a + 2 * ((b - a) / 3) + (b - a) / 3 =
              a + 3 * ((b - a) / 3) := by ring1
          _ = a + (b - a) := by rw [thirdScaled]
          _ = b := by ring1

/-- Total bounded search for a nonzero polynomial value in the middle third
of a proper interval. -/
def centralSearchValue (p : Polynomial) {a b : Coordinate}
    (degreeBound : Nat) (less : a < b) (nonzero : p.isZero = false)
    (degree : p.natDegree ≤ degreeBound) : Coordinate :=
  interiorSearchValue p degreeBound (centralBounds less).2.1 nonzero degree

theorem centralSearchValue_spec (p : Polynomial) {a b : Coordinate}
    (degreeBound : Nat) (less : a < b) (nonzero : p.isZero = false)
    (degree : p.natDegree ≤ degreeBound) :
    p.eval (centralSearchValue p degreeBound less nonzero degree) ≠ 0 ∧
      a < centralSearchValue p degreeBound less nonzero degree ∧
      centralSearchValue p degreeBound less nonzero degree < b := by
  have selected := interiorSearchValue_spec p degreeBound
    (centralBounds less).2.1 nonzero degree
  have selected' :
      p.eval (centralSearchValue p degreeBound less nonzero degree) ≠ 0 ∧
        centralLower a b <
          centralSearchValue p degreeBound less nonzero degree ∧
        centralSearchValue p degreeBound less nonzero degree <
          centralUpper a b := by
    simpa only [centralSearchValue] using selected
  exact ⟨selected'.1,
    (centralBounds less).1.trans selected'.2.1,
    selected'.2.2.trans (centralBounds less).2.2⟩

theorem add_twice_sub_left (a t : Coordinate) :
    a + 2 * t - a = 2 * t := by ring1

theorem sub_add_eq_twice_of_three_mul
    (a b t : Coordinate) (scaled : 3 * t = b - a) :
    b - (a + t) = 2 * t := by
  calc
    b - (a + t) = (b - a) - t := by ring1
    _ = 3 * t - t := by rw [← scaled]
    _ = 2 * t := by ring1

/-- A central-third safe cut contracts both child widths by the uniform
factor `2/3`, independently of the polynomial degree. -/
theorem centralSearchValue_contraction
    (p : Polynomial) {a b : Coordinate}
    (degreeBound : Nat) (less : a < b) (nonzero : p.isZero = false)
    (degree : p.natDegree ≤ degreeBound) :
    centralSearchValue p degreeBound less nonzero degree - a <
        (2 / 3 : Coordinate) * (b - a) ∧
      b - centralSearchValue p degreeBound less nonzero degree <
        (2 / 3 : Coordinate) * (b - a) := by
  have selected := interiorSearchValue_spec p degreeBound
    (centralBounds less).2.1 nonzero degree
  have selected' :
      p.eval (centralSearchValue p degreeBound less nonzero degree) ≠ 0 ∧
        centralLower a b <
          centralSearchValue p degreeBound less nonzero degree ∧
        centralSearchValue p degreeBound less nonzero degree <
          centralUpper a b := by
    simpa only [centralSearchValue] using selected
  constructor
  · have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
      selected'.2.2 (-a)
    calc
      centralSearchValue p degreeBound less nonzero degree - a <
          centralUpper a b - a := by simpa only [sub_eq_add_neg] using shifted
      _ = (2 / 3 : Coordinate) * (b - a) := by
        simp only [centralUpper,
          RFAP.NormalizedFraction.normalizedAdd_eq,
          RFAP.NormalizedFraction.normalizedMul_eq,
          RFAP.NormalizedFraction.normalizedDiv_eq,
          RFAP.NormalizedFraction.normalizedSub_eq]
        rw [add_twice_sub_left]
        rw [RFAP.ExplicitField.div_eq_mul_inv,
          RFAP.ExplicitField.div_eq_mul_inv]
        ring1
  · have reversed := RFAP.ConstructiveFraction.neg_lt_neg_direct
      selected'.2.1
    have shifted := RFAP.ConstructiveFraction.add_lt_add_left_direct
      reversed b
    calc
      b - centralSearchValue p degreeBound less nonzero degree <
          b - centralLower a b := by simpa only [sub_eq_add_neg] using shifted
      _ = (2 / 3 : Coordinate) * (b - a) := by
        simp only [centralLower,
          RFAP.NormalizedFraction.normalizedAdd_eq,
          RFAP.NormalizedFraction.normalizedDiv_eq,
          RFAP.NormalizedFraction.normalizedSub_eq]
        have scaled : (3 : Coordinate) * ((b - a) / 3) = b - a := by
          rw [RFAP.ConstructiveFraction.mul_comm]
          exact RFAP.ConstructiveFraction.div_mul_cancel_of_ne
            (b - a) 3 (by decide)
        rw [sub_add_eq_twice_of_three_mul a b ((b - a) / 3) scaled]
        rw [RFAP.ExplicitField.div_eq_mul_inv,
          RFAP.ExplicitField.div_eq_mul_inv]
        ring1

/-! ## Explicit finite contraction depth -/

theorem inverseContraction_linear_lower (depth : Nat) :
    (1 : Coordinate) + (depth : Coordinate) * (1 / 2) ≤
      (3 / 2 : Coordinate) ^ depth := by
  induction depth with
  | zero =>
      simp only [Nat.cast_zero, zero_mul, add_zero, pow_zero]
      exact le_rfl
  | succ depth inductionHypothesis =>
      have halfNonnegative : (0 : Coordinate) ≤ 1 / 2 := by decide
      have depthNonnegative : (0 : Coordinate) ≤ (depth : Coordinate) :=
        RFAP.ConstructiveFraction.natCast_le_direct (Nat.zero_le depth)
      have remainderNonnegative : 0 ≤
          (depth : Coordinate) * (1 / 2) * (1 / 2) :=
        RFAP.ConstructiveFraction.mul_nonneg_direct
          (RFAP.ConstructiveFraction.mul_nonneg_direct
            depthNonnegative halfNonnegative)
          halfNonnegative
      have ratioNonnegative : (0 : Coordinate) ≤ 3 / 2 := by decide
      have scaled :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          inductionHypothesis ratioNonnegative
      calc
        (1 : Coordinate) + (Nat.succ depth : Coordinate) * (1 / 2) ≤
            (1 + (depth : Coordinate) * (1 / 2)) * (3 / 2) := by
          apply sub_nonneg.mp
          calc
            0 ≤ (depth : Coordinate) * (1 / 2) * (1 / 2) :=
              remainderNonnegative
            _ = (1 + (depth : Coordinate) * (1 / 2)) * (3 / 2) -
                (1 + (Nat.succ depth : Coordinate) * (1 / 2)) := by
              have threeHalves : (3 / 2 : Coordinate) = 1 + 1 / 2 := by
                decide
              rw [threeHalves, Nat.cast_succ]
              ring1
        _ ≤ (3 / 2 : Coordinate) ^ depth * (3 / 2) := scaled
        _ = (3 / 2 : Coordinate) ^ Nat.succ depth := by
          rw [pow_succ]

/-- Conservative finite search bound computed from the constructive rational
ceiling.  This is a finite integer calculation, not an Archimedean or
infinite-carrier argument. -/
def geometricDepthBound (width epsilon : Coordinate) : Nat :=
  RFAP.ConstructiveFraction.ceilNat (2 * width / epsilon)

theorem geometricDepthBound_sufficient {width epsilon : Coordinate}
    (widthNonnegative : 0 ≤ width) (epsilonPositive : 0 < epsilon) :
    (2 / 3 : Coordinate) ^ geometricDepthBound width epsilon * width ≤
      epsilon := by
  let depth := geometricDepthBound width epsilon
  have ratioNonnegative : 0 ≤ 2 * width / epsilon := by
    rw [RFAP.ExplicitField.div_eq_mul_inv]
    exact RFAP.ConstructiveFraction.mul_nonneg_direct
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        widthNonnegative)
      (RFAP.ConstructiveFraction.inv_pos_direct epsilonPositive).le
  have ceiling : 2 * width / epsilon ≤ (depth : Coordinate) := by
    exact RFAP.ConstructiveFraction.le_natCast_ceilNat_of_nonneg
      ratioNonnegative
  have halfNonnegative : (0 : Coordinate) ≤ 1 / 2 := by decide
  have halfScaled :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      ceiling halfNonnegative
  have widthRatio : width / epsilon ≤
      (depth : Coordinate) * (1 / 2) := by
    calc
      width / epsilon = (2 * width / epsilon) * (1 / 2) := by
        rw [RFAP.ExplicitField.div_eq_mul_inv,
          RFAP.ExplicitField.div_eq_mul_inv]
        have twoHalf : (2 : Coordinate) * (1 / 2) = 1 := by decide
        calc
          width * epsilon⁻¹ = width * epsilon⁻¹ * 1 :=
            (RFAP.ConstructiveFraction.mul_one_direct _).symm
          _ = width * epsilon⁻¹ * (2 * (1 / 2)) := by rw [twoHalf]
          _ = 2 * width * epsilon⁻¹ * (1 / 2) := by ring1
      _ ≤ (depth : Coordinate) * (1 / 2) := halfScaled
  have linear := inverseContraction_linear_lower depth
  have depthHalfLeLinear : (depth : Coordinate) * (1 / 2) ≤
      1 + (depth : Coordinate) * (1 / 2) := by
    calc
      (depth : Coordinate) * (1 / 2) =
          0 + (depth : Coordinate) * (1 / 2) := by ring1
      _ ≤ 1 + (depth : Coordinate) * (1 / 2) :=
        add_le_add (by decide) (le_refl _)
  have ratioPower : width / epsilon ≤
      (3 / 2 : Coordinate) ^ depth :=
    widthRatio.trans (depthHalfLeLinear.trans linear)
  have widthBound : width ≤
      epsilon * (3 / 2 : Coordinate) ^ depth := by
    have divided :=
      (RFAP.ConstructiveFraction.div_le_iff_pos epsilonPositive).mp ratioPower
    simpa only [RFAP.ConstructiveFraction.mul_comm] using divided
  have contractionNonnegative :
      0 ≤ (2 / 3 : Coordinate) ^ depth :=
    RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) depth
  have inverseProduct :
      (2 / 3 : Coordinate) ^ depth * (3 / 2 : Coordinate) ^ depth = 1 := by
    rw [← mul_pow]
    have inverseBase : (2 / 3 : Coordinate) * (3 / 2) = 1 := by decide
    rw [inverseBase, one_pow]
  change (2 / 3 : Coordinate) ^ depth * width ≤ epsilon
  calc
    (2 / 3 : Coordinate) ^ depth * width ≤
        (2 / 3 : Coordinate) ^ depth *
          (epsilon * (3 / 2 : Coordinate) ^ depth) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        widthBound contractionNonnegative
    _ = epsilon := by
      rw [show (2 / 3 : Coordinate) ^ depth *
          (epsilon * (3 / 2 : Coordinate) ^ depth) =
        epsilon * ((2 / 3 : Coordinate) ^ depth *
          (3 / 2 : Coordinate) ^ depth) by ring1,
        inverseProduct]
      ring1

/-- Scan at most the displayed fuel for the first sufficient geometric
contraction.  The recursive width is an exact rational, so every stop test is
decidable and the construction remains a bounded finite calculation. -/
private def geometricDepthSearch (width epsilon : Coordinate) : Nat → Nat
  | 0 => 0
  | fuel + 1 =>
      if width ≤ epsilon then 0
      else 1 + geometricDepthSearch ((2 / 3 : Coordinate) * width) epsilon fuel

private theorem geometricDepthSearch_sufficient
    {width epsilon : Coordinate} (fuel : Nat)
    (terminal : (2 / 3 : Coordinate) ^ fuel * width ≤ epsilon) :
    (2 / 3 : Coordinate) ^ geometricDepthSearch width epsilon fuel * width ≤
      epsilon := by
  induction fuel generalizing width with
  | zero =>
      simpa only [geometricDepthSearch, pow_zero, one_mul] using terminal
  | succ fuel inductionHypothesis =>
      by_cases small : width ≤ epsilon
      · simp only [geometricDepthSearch, small, ↓reduceIte, pow_zero,
          one_mul]
      · let next := (2 / 3 : Coordinate) * width
        have nextTerminal :
            (2 / 3 : Coordinate) ^ fuel * next ≤ epsilon := by
          calc
            (2 / 3 : Coordinate) ^ fuel * next =
                (2 / 3 : Coordinate) ^ (fuel + 1) * width := by
              dsimp only [next]
              rw [pow_succ]
              ring1
            _ ≤ epsilon := terminal
        have recursive := inductionHypothesis nextTerminal
        simp only [geometricDepthSearch, small, ↓reduceIte]
        calc
          (2 / 3 : Coordinate) ^
                (1 + geometricDepthSearch next epsilon fuel) * width =
              (2 / 3 : Coordinate) ^
                  geometricDepthSearch next epsilon fuel * next := by
            dsimp only [next]
            rw [Nat.add_comm 1, pow_succ]
            ring1
          _ ≤ epsilon := recursive

/-- The first sufficient contraction depth found inside the proven finite
ceiling bound.  Unlike the ceiling itself, this value grows logarithmically
with the requested reciprocal tolerance. -/
def geometricDepth (width epsilon : Coordinate) : Nat :=
  geometricDepthSearch width epsilon (geometricDepthBound width epsilon)

theorem geometricDepth_sufficient {width epsilon : Coordinate}
    (widthNonnegative : 0 ≤ width) (epsilonPositive : 0 < epsilon) :
    (2 / 3 : Coordinate) ^ geometricDepth width epsilon * width ≤
      epsilon := by
  exact geometricDepthSearch_sufficient _
    (geometricDepthBound_sufficient widthNonnegative epsilonPositive)

end RFAP.SafeCandidates
