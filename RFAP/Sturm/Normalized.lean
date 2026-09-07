import mathlib.Tactic.QuotientFreeOmega
import RFAP.Sturm
import mathlib.RFAP.ComputablePolynomialMap
import mathlib.RFAP.NormalizedPolynomialResource

/-!
# Normalized finite Sturm calculations

This module runs the finite Sturm recursion on canonical reduced coefficient
records.  The compatibility maps called `erase` and `canonical` are now
mutually inverse structural maps on the same canonical scalar carrier; they
remain named so the reduction-aware resource theorems keep their established
API.  The accompanying recurrence bounds every coefficient in every chain
member from the two displayed source polynomials.
-/

namespace RFAP.NormalizedSturm

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev WorkingCoordinate := RFAP.NormalizedFraction.ReducedFraction
abbrev Polynomial := RFAP.ComputablePolynomial.DensePolynomial Coordinate
abbrev WorkingPolynomial :=
  RFAP.ComputablePolynomial.DensePolynomial WorkingCoordinate

open RFAP.ComputablePolynomial.DensePolynomial
open RFAP.NormalizedPolynomialResource

def eraseEmbedding :
    RFAP.ComputablePolynomialMap.Embedding WorkingCoordinate Coordinate where
  toFun := RFAP.NormalizedFraction.value
  injective := RFAP.NormalizedFraction.value_injective
  map_zero := RFAP.NormalizedFraction.value_zero
  map_one := RFAP.NormalizedFraction.value_one
  map_add := RFAP.NormalizedFraction.value_add_instance
  map_neg := RFAP.NormalizedFraction.value_neg_instance
  map_mul := RFAP.NormalizedFraction.value_mul_instance
  map_inv := RFAP.NormalizedFraction.value_inv_instance

def canonicalEmbedding :
    RFAP.ComputablePolynomialMap.Embedding Coordinate WorkingCoordinate where
  toFun := RFAP.NormalizedFraction.ofRational
  injective := by
    intro left right equal
    have values := congrArg RFAP.NormalizedFraction.value equal
    simpa only [RFAP.NormalizedFraction.value_ofRational] using values
  map_zero := by
    apply RFAP.NormalizedFraction.value_injective
    simp only [RFAP.NormalizedFraction.value_ofRational,
      RFAP.NormalizedFraction.value_zero]
  map_one := by
    apply RFAP.NormalizedFraction.value_injective
    simp only [RFAP.NormalizedFraction.value_ofRational,
      RFAP.NormalizedFraction.value_one]
  map_add := by
    intro left right
    apply RFAP.NormalizedFraction.value_injective
    simp only [RFAP.NormalizedFraction.value_ofRational,
      RFAP.NormalizedFraction.value_add_instance]
  map_neg := by
    intro source
    apply RFAP.NormalizedFraction.value_injective
    simp only [RFAP.NormalizedFraction.value_ofRational,
      RFAP.NormalizedFraction.value_neg_instance]
  map_mul := by
    intro left right
    apply RFAP.NormalizedFraction.value_injective
    simp only [RFAP.NormalizedFraction.value_ofRational,
      RFAP.NormalizedFraction.value_mul_instance]
  map_inv := by
    intro source
    apply RFAP.NormalizedFraction.value_injective
    simp only [RFAP.NormalizedFraction.value_ofRational,
      RFAP.NormalizedFraction.value_inv_instance]

def erasePolynomial (polynomial : WorkingPolynomial) : Polynomial :=
  RFAP.ComputablePolynomialMap.map eraseEmbedding polynomial

def canonicalPolynomial (polynomial : Polynomial) : WorkingPolynomial :=
  RFAP.ComputablePolynomialMap.map canonicalEmbedding polynomial

theorem erase_canonicalPolynomial (polynomial : Polynomial) :
    erasePolynomial (canonicalPolynomial polynomial) = polynomial := by
  apply RFAP.ComputablePolynomial.DensePolynomial.ext
  unfold erasePolynomial canonicalPolynomial RFAP.ComputablePolynomialMap.map
  induction polynomial.coeffs with
  | nil => rfl
  | cons value remaining inductionHypothesis =>
      simp only [List.map_cons, List.map_map]
      change RFAP.NormalizedFraction.value
          (RFAP.NormalizedFraction.ofRational value) ::
        List.map (eraseEmbedding.toFun ∘ canonicalEmbedding.toFun) remaining =
          value :: remaining
      rw [RFAP.NormalizedFraction.value_ofRational]
      have tailEqual :
          List.map (eraseEmbedding.toFun ∘ canonicalEmbedding.toFun)
            remaining = remaining := by
        simpa only [RFAP.ComputablePolynomialMap.map_coeffs,
          List.map_map] using inductionHypothesis
      exact congrArg (List.cons value) tailEqual

/-- Fuel-bounded signed Euclidean recursion over reduced coefficient records. -/
def signedRemainderChainFuel :
    Nat → WorkingPolynomial → WorkingPolynomial → List WorkingPolynomial :=
  Nat.rec
    (fun p _ => [p])
    (fun _ recursive p q =>
      if q.isZero then [p]
      else
        let division := divMod p q
        if division.remainder.isZero then [p, q]
        else p :: recursive q (-division.remainder))

@[simp] theorem signedRemainderChainFuel_zero
    (p q : WorkingPolynomial) :
    signedRemainderChainFuel 0 p q = [p] := rfl

theorem signedRemainderChainFuel_succ
    (fuel : Nat) (p q : WorkingPolynomial) :
    signedRemainderChainFuel (fuel + 1) p q =
      if q.isZero then [p]
      else
        let division := divMod p q
        if division.remainder.isZero then [p, q]
        else p :: signedRemainderChainFuel fuel q
          (-division.remainder) := rfl

/-- Once the fuel covers the represented degree, one further step cannot
change the normalized signed chain. -/
theorem signedRemainderChainFuel_succ_of_degreeCount_le :
    ∀ (fuel : Nat) (p q : WorkingPolynomial), q.degreeCount ≤ fuel →
      signedRemainderChainFuel (fuel + 1) p q =
        signedRemainderChainFuel fuel p q := by
  intro fuel
  induction fuel with
  | zero =>
      intro p q enough
      have degreeZero : q.degreeCount = 0 := Nat.eq_zero_of_le_zero enough
      have qZero := isZero_true_of_degreeCount_eq_zero degreeZero
      change (if q.isZero then [p]
          else
            let division := divMod p q
            if division.remainder.isZero then [p, q]
            else p :: signedRemainderChainFuel 0 q
              (-division.remainder)) = [p]
      rw [qZero]
      simp only [↓reduceIte]
  | succ fuel inductionHypothesis =>
      intro p q enough
      change (if q.isZero then [p]
          else
            let division := divMod p q
            if division.remainder.isZero then [p, q]
            else p :: signedRemainderChainFuel (fuel + 1) q
              (-division.remainder)) =
        if q.isZero then [p]
          else
            let division := divMod p q
            if division.remainder.isZero then [p, q]
            else p :: signedRemainderChainFuel fuel q
              (-division.remainder)
      cases qZero : q.isZero
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases remainderZero : (divMod p q).remainder.isZero
        · simp only [Bool.false_eq_true, ↓reduceIte]
          apply congrArg (List.cons p)
          apply inductionHypothesis q (-((divMod p q).remainder))
          have remainderDegree := divMod_remainder_degreeCount_lt p q qZero
          rw [degreeCount_neg]
          exact Nat.lt_succ_iff.mp
            (lt_of_lt_of_le remainderDegree enough)
        · rfl
      · simp only [↓reduceIte]

theorem signedRemainderChainFuel_add_of_degreeCount_le
    (extra fuel : Nat) (p q : WorkingPolynomial)
    (enough : q.degreeCount ≤ fuel) :
    signedRemainderChainFuel (fuel + extra) p q =
      signedRemainderChainFuel fuel p q := by
  induction extra with
  | zero => rw [Nat.add_zero]
  | succ extra inductionHypothesis =>
      rw [Nat.add_succ]
      calc
        signedRemainderChainFuel (fuel + extra + 1) p q =
            signedRemainderChainFuel (fuel + extra) p q :=
          signedRemainderChainFuel_succ_of_degreeCount_le
            (fuel + extra) p q (enough.trans (Nat.le_add_right fuel extra))
        _ = signedRemainderChainFuel fuel p q := inductionHypothesis

theorem signedRemainderChainFuel_stable
    (fuel : Nat) (p q : WorkingPolynomial)
    (enough : q.degreeCount ≤ fuel) :
    signedRemainderChainFuel fuel p q =
      signedRemainderChainFuel q.degreeCount p q := by
  have fuelEquation : q.degreeCount + (fuel - q.degreeCount) = fuel :=
    Nat.add_sub_of_le enough
  rw [← fuelEquation]
  exact signedRemainderChainFuel_add_of_degreeCount_le
    (fuel - q.degreeCount) q.degreeCount p q le_rfl

/-- The normalized chain with its fuel computed from the second polynomial. -/
def signedRemainderChainWF (p q : WorkingPolynomial) :
    List WorkingPolynomial :=
  signedRemainderChainFuel q.degreeCount p q

theorem signedRemainderChainWF_eq (p q : WorkingPolynomial) :
    signedRemainderChainWF p q =
      if q.isZero then [p]
      else
        let division := divMod p q
        if division.remainder.isZero then [p, q]
        else p :: signedRemainderChainWF q (-division.remainder) := by
  change signedRemainderChainFuel q.degreeCount p q =
    if q.isZero then [p]
    else
      let division := divMod p q
      if division.remainder.isZero then [p, q]
      else p :: signedRemainderChainFuel (-division.remainder).degreeCount q
        (-division.remainder)
  cases qZero : q.isZero
  · have degreePositive := degreeCount_pos_of_isZero_false qZero
    obtain ⟨qDegree, degreeEq⟩ :=
      Nat.exists_eq_succ_of_ne_zero degreePositive.ne'
    rw [degreeEq, signedRemainderChainFuel_succ, qZero]
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases remainderZero : (divMod p q).remainder.isZero
    · have remainderDegree := divMod_remainder_degreeCount_lt p q qZero
      simp only [Bool.false_eq_true, ↓reduceIte]
      apply congrArg (List.cons p)
      exact signedRemainderChainFuel_stable qDegree q
          (-((divMod p q).remainder)) (by
            rw [degreeCount_neg]
            omega)
    · rfl
  · have degreeZero := degreeCount_eq_zero_of_isZero qZero
    rw [degreeZero, signedRemainderChainFuel_zero]
    simp only [↓reduceIte]

def signedRemainderChain (p q : WorkingPolynomial) :
    List WorkingPolynomial :=
  signedRemainderChainWF p q

theorem signedRemainderChainWF_length_le (p q : WorkingPolynomial) :
    (signedRemainderChainWF p q).length ≤ q.degreeCount + 1 := by
  change (signedRemainderChainFuel q.degreeCount p q).length ≤
    q.degreeCount + 1
  generalize q.degreeCount = fuel
  induction fuel generalizing p q with
  | zero => exact le_rfl
  | succ fuel inductionHypothesis =>
      rw [signedRemainderChainFuel_succ]
      split
      · simp only [List.length_cons, List.length_nil]
        omega
      · dsimp only
        split
        · simp only [List.length_cons, List.length_nil]
          omega
        · simp only [List.length_cons]
          have recursive := inductionHypothesis q
            (-((divMod p q).remainder))
          omega

/-! ## Erasure to the paper-facing chain -/

theorem erase_signedRemainderChainWF (p q : WorkingPolynomial) :
    (signedRemainderChainWF p q).map erasePolynomial =
      RFAP.Sturm.signedRemainderChainWF
        (erasePolynomial p) (erasePolynomial q) := by
  generalize degreeEquation : q.degreeCount = degree
  induction degree using Nat.strong_induction_on generalizing p q with
  | h degree inductionHypothesis =>
      rw [signedRemainderChainWF_eq,
        RFAP.Sturm.signedRemainderChainWF_eq]
      have zeroEqual : (erasePolynomial q).isZero = q.isZero :=
        RFAP.ComputablePolynomialMap.map_isZero eraseEmbedding q
      rw [zeroEqual]
      split
      · rfl
      · rename_i qNonzeroProof
        dsimp only
        have remainderEqual : erasePolynomial (divMod p q).remainder =
            (divMod (erasePolynomial p) (erasePolynomial q)).remainder :=
          RFAP.ComputablePolynomialMap.map_divMod_remainder eraseEmbedding p q
        have remainderZeroEqual :
            (divMod (erasePolynomial p)
                (erasePolynomial q)).remainder.isZero =
              (divMod p q).remainder.isZero := by
          rw [← remainderEqual]
          exact RFAP.ComputablePolynomialMap.map_isZero eraseEmbedding _
        rw [remainderZeroEqual]
        split
        · rfl
        · simp only [List.map_cons]
          apply congrArg (List.cons (erasePolynomial p))
          have qNonzero : q.isZero = false := by simpa using qNonzeroProof
          have smaller : (-((divMod p q).remainder)).degreeCount < degree := by
            rw [degreeCount_neg, ← degreeEquation]
            exact divMod_remainder_degreeCount_lt p q qNonzero
          rw [inductionHypothesis _ smaller q
            (-((divMod p q).remainder)) rfl]
          apply congrArg (RFAP.Sturm.signedRemainderChainWF
            (erasePolynomial q))
          change RFAP.ComputablePolynomialMap.map eraseEmbedding
              (-((divMod p q).remainder)) = _
          rw [RFAP.ComputablePolynomialMap.map_neg,
            RFAP.ComputablePolynomialMap.map_divMod_remainder]
          rfl

theorem erase_signedRemainderChain (p q : WorkingPolynomial) :
    (signedRemainderChain p q).map erasePolynomial =
      RFAP.Sturm.signedRemainderChain
        (erasePolynomial p) (erasePolynomial q) :=
  erase_signedRemainderChainWF p q

theorem erase_canonical_signedRemainderChain (p q : Polynomial) :
    (signedRemainderChain (canonicalPolynomial p)
        (canonicalPolynomial q)).map erasePolynomial =
      RFAP.Sturm.signedRemainderChain p q := by
  rw [erase_signedRemainderChain, erase_canonicalPolynomial,
    erase_canonicalPolynomial]

/-! ## Source-only coefficient envelope -/

def coefficientMagnitude (polynomial : WorkingPolynomial) : Nat :=
  polynomial.coeffs.foldl
    (fun bound value => max bound (rationalModel.magnitude value))
    (rationalModel.magnitude 0)

private theorem foldl_max_le_final : ∀ (values : List WorkingCoordinate)
    (current : Nat), current ≤ values.foldl
      (fun bound value => max bound (rationalModel.magnitude value)) current
  | [], _ => le_refl _
  | _ :: remaining, _ =>
      (le_max_left _ _).trans (foldl_max_le_final remaining _)

private theorem member_le_foldl_max : ∀ (values : List WorkingCoordinate)
    (current : Nat) {candidate : WorkingCoordinate}, candidate ∈ values →
    rationalModel.magnitude candidate ≤
      values.foldl
        (fun bound value => max bound (rationalModel.magnitude value)) current
  | [], _, _, member => by simp at member
  | value :: remaining, current, candidate, member => by
      simp only [List.mem_cons] at member
      rcases member with head | tail
      · rw [head]
        exact (le_max_right _ _).trans (foldl_max_le_final remaining _)
      · exact member_le_foldl_max remaining
          (max current (rationalModel.magnitude value)) tail

theorem polynomial_within_coefficientMagnitude (polynomial : WorkingPolynomial) :
    PolynomialWithin rationalModel polynomial
      (coefficientMagnitude polynomial) := by
  intro candidate member
  exact member_le_foldl_max polynomial.coeffs _ member

theorem zero_le_coefficientMagnitude (polynomial : WorkingPolynomial) :
    rationalModel.magnitude 0 ≤ coefficientMagnitude polynomial :=
  foldl_max_le_final polynomial.coeffs _

def sourceMagnitude (p q : WorkingPolynomial) : Nat :=
  max (coefficientMagnitude p) (coefficientMagnitude q)

def chainRoundSteps (degreeLimit : Nat) : Nat :=
  4 * (degreeLimit + 1) + 1

def chainMagnitudeEnvelope (p q : WorkingPolynomial) : Nat :=
  grow rationalModel (sourceMagnitude p q)
    (chainRoundSteps (max p.degreeCount q.degreeCount) *
      (q.degreeCount + 1))

private theorem signedRemainderChainWF_within
    {p q : WorkingPolynomial} {bound degreeLimit : Nat}
    (zeroBound : rationalModel.magnitude 0 ≤ bound)
    (pWithin : PolynomialWithin rationalModel p bound)
    (qWithin : PolynomialWithin rationalModel q bound)
    (pDegree : p.degreeCount ≤ degreeLimit)
    (qDegree : q.degreeCount ≤ degreeLimit) :
    ∀ {candidate : WorkingPolynomial},
      candidate ∈ signedRemainderChainWF p q →
      PolynomialWithin rationalModel candidate
        (grow rationalModel bound
          (chainRoundSteps degreeLimit * (q.degreeCount + 1))) := by
  generalize degreeEquation : q.degreeCount = degree
  induction degree using Nat.strong_induction_on generalizing p q bound with
  | h degree inductionHypothesis =>
      intro candidate member
      rw [signedRemainderChainWF_eq] at member
      split at member
      · simp only [List.mem_singleton] at member
        rw [member]
        exact polynomialWithin_mono rationalModel pWithin
          (bound_le_grow rationalModel bound _)
      · rename_i qNonzeroProof
        dsimp only at member
        split at member
        · simp only [List.mem_cons] at member
          rcases member with head | tail
          · rw [head]
            exact polynomialWithin_mono rationalModel pWithin
              (bound_le_grow rationalModel bound _)
          · rcases tail with second | impossible
            · rw [second]
              exact polynomialWithin_mono rationalModel qWithin
                (bound_le_grow rationalModel bound _)
            · simp at impossible
        · simp only [List.mem_cons] at member
          rcases member with head | tail
          · rw [head]
            exact polynomialWithin_mono rationalModel pWithin
              (bound_le_grow rationalModel bound _)
          · have qNonzero : q.isZero = false := by simpa using qNonzeroProof
            have division := divMod_within rationalModel zeroBound pWithin qWithin
            let divisionBound := grow rationalModel bound (4 * (degreeLimit + 1))
            let roundBound := grow rationalModel bound (chainRoundSteps degreeLimit)
            have divisionSteps : 4 * (p.degreeCount + 1) ≤
                4 * (degreeLimit + 1) :=
              Nat.mul_le_mul_left 4 (Nat.add_le_add_right pDegree 1)
            have remainderWithin : PolynomialWithin rationalModel
                (divMod p q).remainder
                divisionBound :=
              polynomialWithin_mono rationalModel division.2
                (grow_mono_steps rationalModel bound divisionSteps)
            have negated := neg_within rationalModel remainderWithin
            rw [grow_add] at negated
            have nextWithin : PolynomialWithin rationalModel
                (-((divMod p q).remainder)) roundBound := by
              simpa only [divisionBound, roundBound, chainRoundSteps] using negated
            have qNext := polynomialWithin_mono rationalModel qWithin
              (bound_le_grow rationalModel bound (chainRoundSteps degreeLimit))
            have smallerActual :
                (-((divMod p q).remainder)).degreeCount < q.degreeCount := by
              rw [degreeCount_neg]
              exact divMod_remainder_degreeCount_lt p q qNonzero
            have smaller :
                (-((divMod p q).remainder)).degreeCount < degree := by
              rwa [degreeEquation] at smallerActual
            have nextDegree :
                (-((divMod p q).remainder)).degreeCount ≤ degreeLimit :=
              (Nat.le_of_lt smallerActual).trans qDegree
            have recursive := inductionHypothesis _ smaller
              (p := q) (q := -((divMod p q).remainder))
              (bound := roundBound)
              (zeroBound.trans (bound_le_grow rationalModel bound _))
              qNext nextWithin qDegree nextDegree rfl tail
            rw [grow_add] at recursive
            apply polynomialWithin_mono rationalModel recursive
            apply grow_mono_steps rationalModel bound
            have degreeDrop :
                (-((divMod p q).remainder)).degreeCount + 1 ≤
                  q.degreeCount := smallerActual
            calc
              chainRoundSteps degreeLimit +
                    chainRoundSteps degreeLimit *
                      ((-((divMod p q).remainder)).degreeCount + 1) =
                  chainRoundSteps degreeLimit *
                    ((-((divMod p q).remainder)).degreeCount + 2) := by
                symm
                calc
                  chainRoundSteps degreeLimit *
                        ((-((divMod p q).remainder)).degreeCount + 2) =
                      chainRoundSteps degreeLimit *
                        (1 + ((-((divMod p q).remainder)).degreeCount + 1)) := by
                    congr 1
                    let count := (-((divMod p q).remainder)).degreeCount
                    change count + 2 = 1 + (count + 1)
                    calc
                      count + 2 = (count + 1) + 1 :=
                        (Nat.add_assoc count 1 1).symm
                      _ = (1 + count) + 1 := by
                        rw [Nat.add_comm count 1]
                      _ = 1 + (count + 1) := Nat.add_assoc 1 count 1
                  _ = chainRoundSteps degreeLimit * 1 +
                        chainRoundSteps degreeLimit *
                          ((-((divMod p q).remainder)).degreeCount + 1) :=
                    Nat.mul_add _ _ _
                  _ = chainRoundSteps degreeLimit +
                        chainRoundSteps degreeLimit *
                          ((-((divMod p q).remainder)).degreeCount + 1) := by
                    rw [Nat.mul_one]
              _ ≤ chainRoundSteps degreeLimit * (q.degreeCount + 1) :=
                Nat.mul_le_mul_left _ (Nat.add_le_add_right degreeDrop 1)
              _ = chainRoundSteps degreeLimit * (degree + 1) := by
                rw [degreeEquation]

/-- Every reduced numerator and denominator in the normalized Sturm chain is
bounded by an explicit recurrence in the two displayed source polynomials and
their finite degree counts. -/
theorem signedRemainderChain_coefficient_le
    (p q candidate : WorkingPolynomial)
    (member : candidate ∈ signedRemainderChain p q) :
    PolynomialWithin rationalModel candidate (chainMagnitudeEnvelope p q) := by
  let bound := sourceMagnitude p q
  have zeroBound : rationalModel.magnitude 0 ≤ bound :=
    (zero_le_coefficientMagnitude p).trans
      ((le_max_left _ _))
  have pWithin : PolynomialWithin rationalModel p bound :=
    polynomialWithin_mono rationalModel
      (polynomial_within_coefficientMagnitude p) (le_max_left _ _)
  have qWithin : PolynomialWithin rationalModel q bound :=
    polynomialWithin_mono rationalModel
      (polynomial_within_coefficientMagnitude q) (le_max_right _ _)
  exact signedRemainderChainWF_within zeroBound pWithin qWithin
    (le_max_left _ _) (le_max_right _ _) member

/-! ## Normalized endpoint execution and winding cost -/

private theorem signedRemainderChainWF_slots_le :
    ∀ (p q candidate : WorkingPolynomial),
      candidate ∈ signedRemainderChainWF p q →
      candidate.coeffs.length ≤ max p.coeffs.length q.coeffs.length := by
  intro p q
  generalize degreeEquation : q.degreeCount = degree
  induction degree using Nat.strong_induction_on generalizing p q with
  | h degree inductionHypothesis =>
      intro candidate member
      rw [signedRemainderChainWF_eq] at member
      split at member
      · simpa only [List.mem_singleton] using
          (show candidate = p from by simpa using member) ▸ le_max_left _ _
      · rename_i qNonzeroProof
        dsimp only at member
        split at member
        · simp only [List.mem_cons] at member
          rcases member with head | tail
          · rw [head]
            exact le_max_left _ _
          · rcases tail with second | impossible
            · rw [second]
              exact le_max_right _ _
            · simp at impossible
        · simp only [List.mem_cons] at member
          rcases member with head | tail
          · rw [head]
            exact le_max_left _ _
          · let next := -((divMod p q).remainder)
            have qNonzero : q.isZero = false := by
              simpa using qNonzeroProof
            have nextDegree : next.degreeCount < degree := by
              dsimp only [next]
              rw [degreeCount_neg, ← degreeEquation]
              exact divMod_remainder_degreeCount_lt p q qNonzero
            have recursive := inductionHypothesis next.degreeCount nextDegree
              (p := q) (q := next) rfl candidate
              (by simpa only [next] using tail)
            have nextNormalized : next.normalize = next := by
              dsimp only [next]
              exact normalize_neg _
            have nextSlots : next.coeffs.length ≤ q.coeffs.length := by
              have degreeDrop : next.degreeCount < q.degreeCount := by
                simpa only [next, degreeCount_neg] using
                  divMod_remainder_degreeCount_lt p q qNonzero
              have degreeToSlots : q.degreeCount ≤ q.coeffs.length := by
                unfold degreeCount
                exact List.Sublist.length_le
                  (List.dropWhile_sublist (fun coefficient : WorkingCoordinate =>
                    decide (coefficient = 0)))
              have nextLength : next.coeffs.length = next.degreeCount := by
                unfold degreeCount
                rw [nextNormalized]
              rw [nextLength]
              exact (Nat.le_of_lt degreeDrop).trans degreeToSlots
            exact recursive.trans
              (max_le (le_max_right _ _) (nextSlots.trans (le_max_right _ _)))

theorem signedRemainderChain_slots_le (p q candidate : WorkingPolynomial)
    (member : candidate ∈ signedRemainderChain p q) :
    candidate.coeffs.length ≤ max p.coeffs.length q.coeffs.length :=
  signedRemainderChainWF_slots_le p q candidate member

def workingEval (polynomial : Polynomial) (point : Coordinate) :
    WorkingCoordinate :=
  (canonicalPolynomial polynomial).eval
    (RFAP.NormalizedFraction.ofRational point)

theorem value_workingEval (polynomial : Polynomial) (point : Coordinate) :
    RFAP.NormalizedFraction.value (workingEval polynomial point) =
      polynomial.eval point := by
  unfold workingEval
  calc
    RFAP.NormalizedFraction.value
          ((canonicalPolynomial polynomial).eval
            (RFAP.NormalizedFraction.ofRational point)) =
        (erasePolynomial (canonicalPolynomial polynomial)).eval
          (RFAP.NormalizedFraction.value
            (RFAP.NormalizedFraction.ofRational point)) :=
      RFAP.ComputablePolynomialMap.map_eval eraseEmbedding _ _
    _ = polynomial.eval point := by
      rw [erase_canonicalPolynomial,
        RFAP.NormalizedFraction.value_ofRational]

def endpointVariation2 (chain : List WorkingPolynomial)
    (point : Coordinate) : Nat :=
  RFAP.Sturm.variation2 (chain.map fun polynomial =>
    RFAP.NormalizedFraction.value
      (polynomial.eval (RFAP.NormalizedFraction.ofRational point)))

private theorem workingEvaluations_eq (chain : List WorkingPolynomial)
    (point : Coordinate) :
    chain.map (fun polynomial => RFAP.NormalizedFraction.value
        (polynomial.eval (RFAP.NormalizedFraction.ofRational point))) =
      (chain.map erasePolynomial).map (fun polynomial =>
        polynomial.eval point) := by
  induction chain with
  | nil => rfl
  | cons polynomial remaining inductionHypothesis =>
      simp only [List.map_cons, List.cons.injEq, inductionHypothesis, and_true]
      calc
        RFAP.NormalizedFraction.value
              (polynomial.eval
                (RFAP.NormalizedFraction.ofRational point)) =
            (erasePolynomial polynomial).eval
              (RFAP.NormalizedFraction.value
                (RFAP.NormalizedFraction.ofRational point)) :=
          RFAP.ComputablePolynomialMap.map_eval eraseEmbedding _ _
        _ = (erasePolynomial polynomial).eval point := by
          rw [RFAP.NormalizedFraction.value_ofRational]

def cauchyIndex2 (p q : Polynomial) (a b : Coordinate) : Int :=
  let chain := signedRemainderChain
    (canonicalPolynomial q) (canonicalPolynomial p)
  (endpointVariation2 chain a : Int) - endpointVariation2 chain b

theorem cauchyIndex2_eq (p q : Polynomial) (a b : Coordinate) :
    cauchyIndex2 p q a b = RFAP.Sturm.cauchyIndex2 p q a b := by
  let chain := signedRemainderChain
    (canonicalPolynomial q) (canonicalPolynomial p)
  change (endpointVariation2 chain a : Int) - endpointVariation2 chain b = _
  rw [endpointVariation2, endpointVariation2,
    workingEvaluations_eq chain a, workingEvaluations_eq chain b,
    erase_canonical_signedRemainderChain]
  rfl

def workingEndpointMagnitudeEnvelope (p q : WorkingPolynomial)
    (point : WorkingCoordinate) : Nat :=
  grow rationalModel
    (max (chainMagnitudeEnvelope p q) (rationalModel.magnitude point))
    (2 * max p.coeffs.length q.coeffs.length)

structure ChainMemberResource (p q candidate : WorkingPolynomial) : Prop where
  coefficients : PolynomialWithin rationalModel candidate
    (chainMagnitudeEnvelope p q)
  slots : candidate.coeffs.length ≤ max p.coeffs.length q.coeffs.length

theorem chainMember_resource (p q candidate : WorkingPolynomial)
    (member : candidate ∈ signedRemainderChain p q) :
    ChainMemberResource p q candidate :=
  ⟨signedRemainderChain_coefficient_le p q candidate member,
    signedRemainderChain_slots_le p q candidate member⟩

def endpointMagnitudeEnvelope (p q : Polynomial)
    (point : Coordinate) : Nat :=
  workingEndpointMagnitudeEnvelope (canonicalPolynomial q)
    (canonicalPolynomial p) (RFAP.NormalizedFraction.ofRational point)

/-- Source-computed field-operation budget for constructing one signed chain
and evaluating every emitted member at both endpoints. -/
def cauchyIndexFieldOperationBudget (p q : Polynomial) : Nat :=
  let workingP := canonicalPolynomial p
  let workingQ := canonicalPolynomial q
  chainRoundSteps (max workingQ.degreeCount workingP.degreeCount) *
      (workingP.degreeCount + 1) +
    4 * (workingP.degreeCount + 1) *
      max workingQ.coeffs.length workingP.coeffs.length

theorem normalizedChain_length_le (p q : Polynomial) :
    (signedRemainderChain (canonicalPolynomial q)
        (canonicalPolynomial p)).length ≤ p.degreeCount + 1 := by
  have lengthBound := signedRemainderChainWF_length_le
    (canonicalPolynomial q) (canonicalPolynomial p)
  have degreeEqual : (canonicalPolynomial p).degreeCount = p.degreeCount :=
    RFAP.ComputablePolynomialMap.map_degreeCount canonicalEmbedding p
  rw [degreeEqual] at lengthBound
  exact lengthBound

end RFAP.NormalizedSturm
