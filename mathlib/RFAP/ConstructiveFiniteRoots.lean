import mathlib.Data.ConstructiveList
import mathlib.RFAP.ConstructiveDerivativeDegree
import mathlib.Tactic.QuotientFreeRing

/-!
# Finite root bounds over constructive Gaussian rationals

A nonzero dense polynomial cannot vanish at as many distinct displayed
Gaussian rationals as it has normalized coefficient slots.  Synthetic
division proves this directly.  The resulting bounded scan supplies one
explicit nonzero evaluation without forming or quantifying over a root set.
-/

namespace RFAP.ConstructiveFiniteRoots

abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial

open RFAP.ComputablePolynomial.DensePolynomial

def syntheticAux (root leading : Gaussian) :
    List Gaussian → List Gaussian × Gaussian
  | [] => ([], leading)
  | coefficient :: remaining =>
      let result := syntheticAux root (leading * root + coefficient) remaining
      (leading :: result.1, result.2)

private theorem evalCoeffs_cons_power (x leading : Gaussian)
    (remaining : List Gaussian) :
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

private theorem syntheticAux_spec (root leading : Gaussian)
    (remaining : List Gaussian) :
    let result := syntheticAux root leading remaining
    result.1.length = remaining.length ∧
      result.2 = evalCoeffs root (leading :: remaining) ∧
      ∀ x : Gaussian,
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
        ∀ x : Gaussian,
          evalCoeffs x (nextLeading :: remaining) =
            (x - root) * evalCoeffs x recursive.1 + recursive.2 at recursiveSpec
      change
        (leading :: recursive.1).length =
            (coefficient :: remaining).length ∧
          recursive.2 =
            evalCoeffs root (leading :: coefficient :: remaining) ∧
          ∀ x : Gaussian,
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
            let power := x ^ remaining.length
            change leading * (power * x) + coefficient * power +
                evalCoeffs x remaining =
              (x - root) * (leading * power) +
                ((leading * root + coefficient) * power +
                  evalCoeffs x remaining)
            apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
              simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
                RFAP.ConstructiveGaussian.Gaussian.add_im,
                RFAP.ConstructiveGaussian.Gaussian.sub_re,
                RFAP.ConstructiveGaussian.Gaussian.sub_im,
                RFAP.ConstructiveGaussian.Gaussian.mul_re,
                RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
              ring1
          _ = (x - root) * (leading * x ^ remaining.length) +
                ((x - root) * evalCoeffs x recursive.1 + recursive.2) := by
            rw [recursiveFactor]
          _ = (x - root) *
                (leading * x ^ remaining.length +
                  evalCoeffs x recursive.1) + recursive.2 := by ring1
          _ = (x - root) * evalCoeffs x (leading :: recursive.1) +
                recursive.2 := by
            rw [evalCoeffs_cons_power, recursiveSpec.1]

/-- Direct finite distinct-root bound for a displayed Gaussian polynomial. -/
theorem nodup_zeros_length_lt_degreeCount
    (p : GaussianPolynomial) (nonzero : p.isZero = false)
    (points : List Gaussian) (nodup : points.Nodup)
    (zeros : ∀ x ∈ points, p.eval x = 0) :
    points.length < p.degreeCount := by
  generalize degreeEquation : p.degreeCount = degree
  induction degree using Nat.strong_induction_on generalizing p points with
  | h degree inductionHypothesis =>
      have degreePositive := degreeCount_pos_of_isZero_false nonzero
      rw [degreeEquation] at degreePositive
      cases points with
      | nil => exact degreePositive
      | cons root otherPoints =>
          cases coefficientsEquation : p.normalize.coeffs with
          | nil =>
              change p.normalize.coeffs.isEmpty = false at nonzero
              rw [coefficientsEquation] at nonzero
              exact Bool.noConfusion nonzero
          | cons leading remaining =>
              have leadingNonzero : leading ≠ 0 := by
                have canonical := leadingCoeff_ne_zero nonzero
                change p.normalize.coeffs.headD 0 ≠ 0 at canonical
                rw [coefficientsEquation] at canonical
                simpa only [List.headD_cons] using canonical
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
                  let quotient : GaussianPolynomial := ⟨division.1⟩
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
                    · exact
                        (RFAP.ConstructiveGaussian.Gaussian.mul_ne_zero_direct
                          differenceNonzero quotientZero productZero).elim
                  have recursive := inductionHypothesis quotient.degreeCount
                    quotientSmaller quotient quotientNonzero otherPoints
                    (List.nodup_cons.mp nodup).2 otherZeros rfl
                  simp only [List.length_cons]
                  exact (Nat.succ_le_of_lt recursive).trans_lt quotientSmaller

def naturalPoint (n : Nat) : Gaussian := (n : Gaussian)

theorem naturalPoint_injective : Function.Injective naturalPoint := by
  intro left right equal
  have real := congrArg RFAP.ConstructiveGaussian.Gaussian.re equal
  change ((left : Gaussian).re) = ((right : Gaussian).re) at real
  rw [RFAP.ConstructiveGaussian.Gaussian.natCast_re,
    RFAP.ConstructiveGaussian.Gaussian.natCast_re] at real
  exact RFAP.ConstructiveFraction.natCast_injective_direct real

private theorem nodup_map_of_injective
    {A B : Type*} (f : A → B) (injective : Function.Injective f) :
    ∀ {values : List A}, values.Nodup → (values.map f).Nodup
  | [], _ => List.Pairwise.nil
  | head :: tail, nodup => by
      rw [List.nodup_cons] at nodup
      change (f head :: tail.map f).Nodup
      rw [List.nodup_cons]
      constructor
      · intro member
        rcases QuotientFreeList.mem_map.mp member with ⟨value, valueMember, equal⟩
        exact nodup.1 (injective equal.symm ▸ valueMember)
      · exact nodup_map_of_injective f injective nodup.2

private def descendingNaturals : Nat → List Nat
  | 0 => []
  | count + 1 => count :: descendingNaturals count

private theorem descendingNaturals_length : ∀ count : Nat,
    (descendingNaturals count).length = count
  | 0 => rfl
  | count + 1 => by
      simp only [descendingNaturals, List.length_cons,
        descendingNaturals_length count]

private theorem mem_descendingNaturals_lt
    {count value : Nat} (member : value ∈ descendingNaturals count) :
    value < count := by
  induction count with
  | zero =>
      change value ∈ [] at member
      exact (List.not_mem_nil member).elim
  | succ count inductionHypothesis =>
      simp only [descendingNaturals, List.mem_cons] at member
      rcases member with equal | member
      · subst value
        exact Nat.lt_succ_self count
      · exact (inductionHypothesis member).trans (Nat.lt_succ_self count)

private theorem descendingNaturals_nodup : ∀ count : Nat,
    (descendingNaturals count).Nodup
  | 0 => List.Pairwise.nil
  | count + 1 => by
      apply List.Pairwise.cons
      · intro value member equal
        subst value
        exact (Nat.lt_irrefl count (mem_descendingNaturals_lt member)).elim
      · exact descendingNaturals_nodup count

def candidates (p : GaussianPolynomial) : List Gaussian :=
  (descendingNaturals p.degreeCount).map naturalPoint

theorem candidates_nodup (p : GaussianPolynomial) :
    (candidates p).Nodup :=
  nodup_map_of_injective naturalPoint naturalPoint_injective
    (descendingNaturals_nodup p.degreeCount)

theorem candidates_length (p : GaussianPolynomial) :
    (candidates p).length = p.degreeCount := by
  simp only [candidates, List.length_map, descendingNaturals_length]

/-- Equality of two finite dense polynomials, expressed as an exactly zero
coefficient difference, can be certified by testing only the displayed
candidate list of that difference.  This is finite coefficient extensionality,
not extensionality over the Gaussian-rational carrier. -/
theorem difference_isZero_of_candidate_evals
    (p q : GaussianPolynomial)
    (equal : ∀ point ∈ candidates (p - q), p.eval point = q.eval point) :
    (p - q).isZero = true := by
  by_cases zero : (p - q).isZero = true
  · exact zero
  · have nonzero : (p - q).isZero = false := by simpa using zero
    have candidateZeros : ∀ point ∈ candidates (p - q),
        (p - q).eval point = 0 := by
      intro point member
      rw [eval_sub, equal point member]
      exact sub_self _
    have tooMany := nodup_zeros_length_lt_degreeCount (p - q) nonzero
      (candidates (p - q)) (candidates_nodup (p - q)) candidateZeros
    rw [candidates_length] at tooMany
    exact (Nat.lt_irrefl _ tooMany).elim

def firstNonzero (p : GaussianPolynomial) : List Gaussian → Option Gaussian
  | [] => none
  | point :: remaining =>
      if p.eval point = 0 then firstNonzero p remaining else some point

theorem firstNonzero_none_zeros
    (p : GaussianPolynomial) : ∀ {points : List Gaussian},
    firstNonzero p points = none → ∀ point ∈ points, p.eval point = 0
  | [], _, _, member => by simp at member
  | head :: tail, outcome, point, member => by
      rw [firstNonzero] at outcome
      split at outcome
      · rename_i headZero
        rcases List.mem_cons.mp member with rfl | tailMember
        · exact headZero
        · exact firstNonzero_none_zeros p outcome point tailMember
      · contradiction

theorem firstNonzero_some_spec
    (p : GaussianPolynomial) : ∀ {points : List Gaussian} {point : Gaussian},
    firstNonzero p points = some point →
      point ∈ points ∧ p.eval point ≠ 0
  | [], _, outcome => by simp [firstNonzero] at outcome
  | head :: tail, point, outcome => by
      rw [firstNonzero] at outcome
      split at outcome
      · rename_i headZero
        have recursive := firstNonzero_some_spec p outcome
        exact ⟨by simp [recursive.1], recursive.2⟩
      · rename_i headNonzero
        have pointEq : point = head := Option.some.inj outcome.symm
        subst point
        exact ⟨by simp, headNonzero⟩

structure NonzeroEvaluation (p : GaussianPolynomial) where
  point : Gaussian
  valueNonzero : p.eval point ≠ 0

/-- Bounded coefficient-count search for one displayed nonzero evaluation. -/
def findNonzeroEvaluation
    (p : GaussianPolynomial) (nonzero : p.isZero = false) :
    NonzeroEvaluation p := by
  let points := candidates p
  match outcome : firstNonzero p points with
  | some point =>
      exact ⟨point, (firstNonzero_some_spec p outcome).2⟩
  | none =>
      have zeros := firstNonzero_none_zeros p outcome
      have tooMany := nodup_zeros_length_lt_degreeCount p nonzero points
        (candidates_nodup p) zeros
      have exactLength := candidates_length p
      rw [exactLength] at tooMany
      exact (Nat.lt_irrefl _ tooMany).elim

end RFAP.ConstructiveFiniteRoots
