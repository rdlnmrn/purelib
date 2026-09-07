import mathlib.Data.ConstructiveList
import mathlib.RFAP.ComputablePolynomial

/-!
# Coefficient maps for finite dense polynomials

The project intentionally avoids the broad sparse-polynomial map API.  This
file proves directly, on finite high-to-low coefficient lists, that an
injective explicit-field embedding commutes with the dense operations,
including fuel-bounded long division.  It is used to erase normalized working
records without changing the calculation they certify.
-/

namespace RFAP.ComputablePolynomialMap

abbrev Polynomial (K : Type*) := RFAP.ComputablePolynomial.DensePolynomial K

open RFAP.ComputablePolynomial.DensePolynomial

structure Embedding (K L : Type*)
    [RFAP.ExplicitField K] [DecidableEq K]
    [RFAP.ExplicitField L] [DecidableEq L] where
  toFun : K → L
  injective : Function.Injective toFun
  map_zero : toFun 0 = 0
  map_one : toFun 1 = 1
  map_add : ∀ left right, toFun (left + right) = toFun left + toFun right
  map_neg : ∀ source, toFun (-source) = -toFun source
  map_mul : ∀ left right, toFun (left * right) = toFun left * toFun right
  map_inv : ∀ source, toFun source⁻¹ = (toFun source)⁻¹

variable {K L : Type*}
  [RFAP.ExplicitField K] [DecidableEq K]
  [RFAP.ExplicitField L] [DecidableEq L]

def map (embedding : Embedding K L) (polynomial : Polynomial K) :
    Polynomial L :=
  ⟨polynomial.coeffs.map embedding.toFun⟩

@[simp] theorem map_coeffs (embedding : Embedding K L)
    (polynomial : Polynomial K) :
    (map embedding polynomial).coeffs = polynomial.coeffs.map embedding.toFun :=
  rfl

theorem map_zero_iff (embedding : Embedding K L) (source : K) :
    embedding.toFun source = 0 ↔ source = 0 := by
  rw [← embedding.map_zero]
  exact embedding.injective.eq_iff

private theorem map_dropWhile_zero (embedding : Embedding K L) :
    ∀ values : List K,
      (values.dropWhile (· = 0)).map embedding.toFun =
        (values.map embedding.toFun).dropWhile (· = 0)
  | [] => rfl
  | value :: remaining => by
      by_cases zero : value = 0
      · subst value
        rw [List.dropWhile_cons_of_pos (by simp),
          List.map_cons, embedding.map_zero,
          List.dropWhile_cons_of_pos (by simp),
          map_dropWhile_zero embedding remaining]
      · rw [List.dropWhile_cons_of_neg (by simp [zero]), List.map_cons,
          List.dropWhile_cons_of_neg (by
            simp [map_zero_iff embedding, zero])]

theorem map_normalize (embedding : Embedding K L) (polynomial : Polynomial K) :
    map embedding polynomial.normalize = (map embedding polynomial).normalize := by
  apply RFAP.ComputablePolynomial.DensePolynomial.ext
  exact map_dropWhile_zero embedding polynomial.coeffs

@[simp] theorem map_isZero (embedding : Embedding K L)
    (polynomial : Polynomial K) :
    (map embedding polynomial).isZero = polynomial.isZero := by
  unfold isZero
  rw [← map_normalize]
  simp only [map_coeffs, List.isEmpty_map]

@[simp] theorem map_degreeCount (embedding : Embedding K L)
    (polynomial : Polynomial K) :
    (map embedding polynomial).degreeCount = polynomial.degreeCount := by
  unfold degreeCount
  rw [← map_normalize]
  simp only [map_coeffs, List.length_map]

@[simp] theorem map_natDegree (embedding : Embedding K L)
    (polynomial : Polynomial K) :
    (map embedding polynomial).natDegree = polynomial.natDegree := by
  unfold natDegree
  rw [map_degreeCount]

private theorem headD_map (embedding : Embedding K L) :
    ∀ values : List K,
      (values.map embedding.toFun).headD 0 =
        embedding.toFun (values.headD 0)
  | [] => embedding.map_zero.symm
  | _ :: _ => rfl

@[simp] theorem map_leadingCoeff (embedding : Embedding K L)
    (polynomial : Polynomial K) :
    (map embedding polynomial).leadingCoeff =
      embedding.toFun polynomial.leadingCoeff := by
  unfold leadingCoeff
  rw [← map_normalize]
  exact headD_map embedding polynomial.normalize.coeffs

@[simp] theorem map_zero_polynomial (embedding : Embedding K L) :
    map embedding (0 : Polynomial K) = 0 := rfl

@[simp] theorem map_constant (embedding : Embedding K L) (value : K) :
    map embedding (constant value) = constant (embedding.toFun value) := rfl

private theorem map_replicate_zero (embedding : Embedding K L) (amount : Nat) :
    (List.replicate amount (0 : K)).map embedding.toFun =
      List.replicate amount (0 : L) := by
  simp [embedding.map_zero]

private theorem map_padLeft (embedding : Embedding K L)
    (amount : Nat) (values : List K) :
    (padLeft amount values).map embedding.toFun =
      padLeft amount (values.map embedding.toFun) := by
  simp [padLeft, map_replicate_zero embedding]

private theorem map_zipWith_add (embedding : Embedding K L) :
    ∀ left right : List K,
      (List.zipWith (· + ·) left right).map embedding.toFun =
        List.zipWith (· + ·) (left.map embedding.toFun)
          (right.map embedding.toFun)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | left :: leftTail, right :: rightTail => by
      simp only [List.zipWith_cons_cons, List.map_cons,
        embedding.map_add, map_zipWith_add embedding leftTail rightTail]

theorem map_add (embedding : Embedding K L) (left right : Polynomial K) :
    map embedding (left + right) = map embedding left + map embedding right := by
  change map embedding (add left right) =
    add (map embedding left) (map embedding right)
  unfold add
  simp only [map_coeffs, List.length_map]
  rw [map_normalize]
  apply congrArg normalize
  apply RFAP.ComputablePolynomial.DensePolynomial.ext
  simp only [map_coeffs, map_zipWith_add, map_padLeft]

theorem map_neg (embedding : Embedding K L) (polynomial : Polynomial K) :
    map embedding (-polynomial) = -map embedding polynomial := by
  change map embedding (neg polynomial) = neg (map embedding polynomial)
  change map embedding (normalize ⟨polynomial.coeffs.map (-·)⟩) =
    normalize ⟨(polynomial.coeffs.map embedding.toFun).map (-·)⟩
  rw [map_normalize]
  apply congrArg normalize
  apply RFAP.ComputablePolynomial.DensePolynomial.ext
  simp only [map_coeffs, List.map_map]
  apply QuotientFreeList.map_congr_left
  intro value _
  exact embedding.map_neg value

theorem map_sub (embedding : Embedding K L) (left right : Polynomial K) :
    map embedding (left - right) = map embedding left - map embedding right := by
  change map embedding (left + -right) = map embedding left + -map embedding right
  rw [map_add, map_neg]

private theorem map_scale (embedding : Embedding K L)
    (scalar : K) (polynomial : Polynomial K) :
    map embedding (scale scalar polynomial) =
      scale (embedding.toFun scalar) (map embedding polynomial) := by
  calc
    map embedding (scale scalar polynomial) =
        map embedding (normalize
          ⟨polynomial.coeffs.map (scalar * ·)⟩) := rfl
    _ = (map embedding
          ⟨polynomial.coeffs.map (scalar * ·)⟩).normalize :=
      map_normalize embedding _
    _ = scale (embedding.toFun scalar) (map embedding polynomial) := by
      apply RFAP.ComputablePolynomial.DensePolynomial.ext
      unfold scale map
      simp only [List.map_map]
      apply congrArg (List.dropWhile (· = (0 : L)))
      apply QuotientFreeList.map_congr_left
      intro value _
      exact embedding.map_mul scalar value

theorem map_shift (embedding : Embedding K L)
    (amount : Nat) (polynomial : Polynomial K) :
    map embedding (shift amount polynomial) =
      shift amount (map embedding polynomial) := by
  unfold shift
  rw [map_isZero]
  split
  · exact map_zero_polynomial embedding
  · apply RFAP.ComputablePolynomial.DensePolynomial.ext
    change ((polynomial.normalize.coeffs ++ List.replicate amount 0).map
        embedding.toFun) =
      (map embedding polynomial).normalize.coeffs ++ List.replicate amount 0
    rw [List.map_append, map_replicate_zero, ← map_normalize]
    rfl

theorem map_mul (embedding : Embedding K L) (left right : Polynomial K) :
    map embedding (left * right) = map embedding left * map embedding right := by
  change map embedding (mulPolynomial left right) =
    mulPolynomial (map embedding left) (map embedding right)
  unfold mulPolynomial
  have foldMap : ∀ (coefficients : List K) (accumulator : Polynomial K),
      map embedding
          (coefficients.foldl
            (fun value coefficient => shift 1 value + scale coefficient right)
            accumulator) =
        (coefficients.map embedding.toFun).foldl
          (fun value coefficient =>
            shift 1 value + scale coefficient (map embedding right))
          (map embedding accumulator) := by
    intro coefficients
    induction coefficients with
    | nil => intro accumulator; rfl
    | cons coefficient remaining inductionHypothesis =>
        intro accumulator
        simp only [List.foldl_cons, List.map_cons]
        rw [inductionHypothesis]
        apply congrArg (fun initial => remaining.map embedding.toFun |>.foldl
          (fun value coefficient =>
            shift 1 value + scale coefficient (map embedding right)) initial)
        rw [map_add, map_shift, map_scale]
  rw [foldMap]
  rfl

theorem map_inv (embedding : Embedding K L) (source : K) :
    embedding.toFun source⁻¹ = (embedding.toFun source)⁻¹ :=
  embedding.map_inv source

theorem map_div (embedding : Embedding K L) (left right : K) :
    embedding.toFun (left / right) =
      embedding.toFun left / embedding.toFun right := by
  rw [RFAP.ExplicitField.div_eq_mul_inv,
    RFAP.ExplicitField.div_eq_mul_inv, embedding.map_mul, embedding.map_inv]

private theorem map_evalCoeffs_from (embedding : Embedding K L)
    (point : K) : ∀ (coefficients : List K) (accumulator : K),
      embedding.toFun
          (coefficients.foldl (fun current coefficient =>
            current * point + coefficient) accumulator) =
        (coefficients.map embedding.toFun).foldl
          (fun current coefficient =>
            current * embedding.toFun point + coefficient)
          (embedding.toFun accumulator)
  | [], _ => rfl
  | coefficient :: remaining, accumulator => by
      simp only [List.foldl_cons, List.map_cons]
      simpa only [embedding.map_add, embedding.map_mul] using
        map_evalCoeffs_from embedding point remaining
          (accumulator * point + coefficient)

/-- Horner evaluation commutes with an explicit finite field embedding. -/
theorem map_eval (embedding : Embedding K L) (polynomial : Polynomial K)
    (point : K) :
    embedding.toFun (polynomial.eval point) =
      (map embedding polynomial).eval (embedding.toFun point) := by
  unfold RFAP.ComputablePolynomial.DensePolynomial.eval
    RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs map
  rw [← embedding.map_zero]
  exact map_evalCoeffs_from embedding point polynomial.coeffs 0

theorem map_leadQuotient (embedding : Embedding K L)
    (left right : Polynomial K) :
    map embedding (leadQuotient left right) =
      leadQuotient (map embedding left) (map embedding right) := by
  unfold leadQuotient
  rw [map_shift, map_natDegree, map_natDegree]
  apply congrArg (shift (left.natDegree - right.natDegree))
  apply RFAP.ComputablePolynomial.DensePolynomial.ext
  simp only [map_coeffs, List.map_cons, List.map_nil]
  rw [map_div, map_leadingCoeff, map_leadingCoeff]

theorem map_cancelLead (embedding : Embedding K L)
    (left right : Polynomial K) :
    map embedding (cancelLead left right) =
      cancelLead (map embedding left) (map embedding right) := by
  unfold cancelLead
  rw [map_sub, map_shift, map_scale, map_natDegree, map_natDegree,
    map_div, map_leadingCoeff, map_leadingCoeff]

theorem map_divLoop_quotient (embedding : Embedding K L) :
    ∀ (fuel : Nat) (left right quotient : Polynomial K),
      map embedding (divLoop fuel left right quotient).quotient =
        (divLoop fuel (map embedding left) (map embedding right)
          (map embedding quotient)).quotient
  | 0, _, _, _ => rfl
  | fuel + 1, left, right, quotient => by
      rw [divLoop_succ, divLoop_succ, map_isZero, map_isZero,
        map_natDegree, map_natDegree]
      split
      · rfl
      · dsimp only
        rw [← map_cancelLead, ← map_leadQuotient, ← map_add]
        exact map_divLoop_quotient embedding fuel
          (cancelLead left right) right (quotient + leadQuotient left right)

theorem map_divLoop_remainder (embedding : Embedding K L) :
    ∀ (fuel : Nat) (left right quotient : Polynomial K),
      map embedding (divLoop fuel left right quotient).remainder =
        (divLoop fuel (map embedding left) (map embedding right)
          (map embedding quotient)).remainder
  | 0, _, _, _ => rfl
  | fuel + 1, left, right, quotient => by
      rw [divLoop_succ, divLoop_succ, map_isZero, map_isZero,
        map_natDegree, map_natDegree]
      split
      · rfl
      · dsimp only
        rw [← map_cancelLead, ← map_leadQuotient, ← map_add]
        exact map_divLoop_remainder embedding fuel
          (cancelLead left right) right (quotient + leadQuotient left right)

theorem map_divLoop_steps (embedding : Embedding K L) :
    ∀ (fuel : Nat) (left right quotient : Polynomial K),
      (divLoop fuel left right quotient).steps =
        (divLoop fuel (map embedding left) (map embedding right)
          (map embedding quotient)).steps
  | 0, _, _, _ => rfl
  | fuel + 1, left, right, quotient => by
      rw [divLoop_succ, divLoop_succ, map_isZero, map_isZero,
        map_natDegree, map_natDegree]
      split
      · rfl
      · dsimp only
        rw [← map_cancelLead, ← map_leadQuotient, ← map_add]
        exact congrArg (· + 1) (map_divLoop_steps embedding fuel
          (cancelLead left right) right (quotient + leadQuotient left right))

theorem map_divMod_quotient (embedding : Embedding K L)
    (left right : Polynomial K) :
    map embedding (divMod left right).quotient =
      (divMod (map embedding left) (map embedding right)).quotient := by
  unfold divMod
  rw [map_degreeCount, ← map_normalize, ← map_normalize,
    ← map_zero_polynomial (K := K) (L := L)]
  exact map_divLoop_quotient embedding _ left.normalize right.normalize 0

theorem map_divMod_remainder (embedding : Embedding K L)
    (left right : Polynomial K) :
    map embedding (divMod left right).remainder =
      (divMod (map embedding left) (map embedding right)).remainder := by
  unfold divMod
  rw [map_degreeCount, ← map_normalize, ← map_normalize,
    ← map_zero_polynomial (K := K) (L := L)]
  exact map_divLoop_remainder embedding _ left.normalize right.normalize 0

theorem map_divMod_steps (embedding : Embedding K L)
    (left right : Polynomial K) :
    (divMod left right).steps =
      (divMod (map embedding left) (map embedding right)).steps := by
  unfold divMod
  rw [map_degreeCount, ← map_normalize, ← map_normalize,
    ← map_zero_polynomial (K := K) (L := L)]
  exact map_divLoop_steps embedding _ left.normalize right.normalize 0

end RFAP.ComputablePolynomialMap
