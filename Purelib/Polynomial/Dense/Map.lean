module
public import Purelib.Algebra.Field.Embedding
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.List.Map
import Purelib.Data.List.DropWhile.Basic
import Purelib.Data.List.Replicate
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Division.Basic
import Purelib.Polynomial.Dense.Division.CancelLead
import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Dense.Multiplication

/-!
# Coefficient maps through retained field embeddings

The original scalar embedding visits every descending coefficient in order.
Its retained field-operation and injectivity certificates transport normalization,
padding, paired addition, Horner multiplication/evaluation and the same finite
long-division states, accumulators and completed outputs.
-/

namespace Purelib.Polynomial.Dense.Map

open Purelib.Algebra.Field
open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense
open Purelib.Data

/-- The descending dense polynomial representation on either side of a coefficient embedding. -/
public abbrev CoefficientPolynomial (K : Type*) := DensePolynomial K

variable {K L : Type*}
  [ExplicitField K] [DecidableEq K]
  [ExplicitField L] [DecidableEq L]

/-- Apply the explicit field embedding to each retained coefficient.

The descending coefficient order and list length are preserved; normalization is handled by separate compatibility
lemmas. -/
@[expose] public def map (embedding : Algebra.Field.Embedding K L) (polynomial : CoefficientPolynomial K) :
    CoefficientPolynomial L :=
  ⟨polynomial.coeffs.map embedding.toFun⟩

/-- Coefficient readback after mapping is the list map of the original coefficient table. -/
@[simp] public theorem map_coeffs (embedding : Algebra.Field.Embedding K L)
    (polynomial : CoefficientPolynomial K) :
    (map embedding polynomial).coeffs = polynomial.coeffs.map embedding.toFun :=
  rfl

/-- An injective field embedding commutes with removing leading zero coefficients.

Injectivity identifies the exact mapped zero decision with the source decision. The first nonzero original coefficient
therefore retains its whole same mapped tail, while zero heads are discarded in the same order. -/
private theorem map_dropWhile_zero (embedding : Algebra.Field.Embedding K L) :
    ∀ values : List K,
      (values.dropWhile (· = 0)).map embedding.toFun =
        (values.map embedding.toFun).dropWhile (· = 0)
  | [] => rfl
  | value :: remaining => by
      by_cases zero : value = 0
      · have imageZero : embedding.toFun value = 0 :=
          (Embedding.map_zero_iff embedding value).mpr zero
        rewrite [List.DropWhile.cons_of_true (fun entry : K => decide (entry = 0))
            value remaining (decide_eq_true zero),
          List.map_cons,
          List.DropWhile.cons_of_true (fun entry : L => decide (entry = 0))
            (embedding.toFun value) (remaining.map embedding.toFun)
            (decide_eq_true imageZero)]
        exact map_dropWhile_zero embedding remaining
      · have imageNonzero : embedding.toFun value ≠ 0 :=
          fun imageZero => zero ((Embedding.map_zero_iff embedding value).mp imageZero)
        rewrite [List.DropWhile.cons_of_false (fun entry : K => decide (entry = 0))
            value remaining (decide_eq_false zero),
          List.map_cons,
          List.DropWhile.cons_of_false (fun entry : L => decide (entry = 0))
            (embedding.toFun value) (remaining.map embedding.toFun)
            (decide_eq_false imageNonzero)]
        exact Eq.refl _

/-- Mapping coefficients commutes with dense normalization.

The same original leading-zero scan and retained scalar map commute at each coefficient. The resulting normalized list
retains its original coefficient order. -/
public theorem map_normalize (embedding : Algebra.Field.Embedding K L) (polynomial : CoefficientPolynomial K) :
    map embedding polynomial.normalize = (map embedding polynomial).normalize := by
  apply DensePolynomial.ext
  exact map_dropWhile_zero embedding polynomial.coeffs

/-- An injective coefficient embedding preserves the executable polynomial zero test.

Normalization commutes with the retained embedding, whose list map preserves the original empty or nonempty constructor.
The same normalized coefficient table therefore determines the zero test. -/
@[simp] public theorem map_isZero (embedding : Algebra.Field.Embedding K L)
    (polynomial : CoefficientPolynomial K) :
    (map embedding polynomial).isZero = polynomial.isZero := by
  unfold DensePolynomial.isZero
  rw [← map_normalize]
  change (polynomial.normalize.coeffs.map embedding.toFun).isEmpty =
    polynomial.normalize.coeffs.isEmpty
  cases polynomial.normalize.coeffs <;> rfl

/-- An injective coefficient embedding preserves the normalized coefficient count.

The retained normalized source table maps to the normalized target table. Each original entry contributes one mapped
entry, preserving that same finite count. -/
@[simp] public theorem map_degreeCount (embedding : Algebra.Field.Embedding K L)
    (polynomial : CoefficientPolynomial K) :
    (map embedding polynomial).degreeCount = polynomial.degreeCount := by
  unfold DensePolynomial.degreeCount
  rw [← map_normalize]
  change (polynomial.normalize.coeffs.map embedding.toFun).length =
    polynomial.normalize.coeffs.length
  exact List.Map.length_map embedding.toFun polynomial.normalize.coeffs

/-- An injective coefficient embedding preserves the executable natural degree. -/
@[simp] public theorem map_natDegree (embedding : Algebra.Field.Embedding K L)
    (polynomial : CoefficientPolynomial K) :
    (map embedding polynomial).natDegree = polynomial.natDegree := by
  unfold DensePolynomial.natDegree
  rw [map_degreeCount]

/-- Mapping a list and reading its head with zero default equals mapping the original head readback. -/
private theorem headD_map (embedding : Algebra.Field.Embedding K L) :
    ∀ values : List K,
      (values.map embedding.toFun).headD 0 =
        embedding.toFun (values.headD 0)
  | [] => embedding.map_zero.symm
  | _ :: _ => rfl

/-- The mapped polynomial leading coefficient is the embedding of the original leading coefficient.

The original normalized head is retained on both sides. The embedding of the zero default agrees with the target zero
when the same original list is empty. -/
@[simp] public theorem map_leadingCoeff (embedding : Algebra.Field.Embedding K L)
    (polynomial : CoefficientPolynomial K) :
    (map embedding polynomial).leadingCoeff =
      embedding.toFun polynomial.leadingCoeff := by
  unfold DensePolynomial.leadingCoeff
  rw [← map_normalize]
  exact headD_map embedding polynomial.normalize.coeffs

/-- Coefficient mapping preserves the empty zero polynomial. -/
@[simp] public theorem map_zero_polynomial (embedding : Algebra.Field.Embedding K L) :
    map embedding (0 : CoefficientPolynomial K) = 0 := rfl

/-- Mapping a constant polynomial maps its retained constant coefficient. -/
@[simp] public theorem map_constant (embedding : Algebra.Field.Embedding K L) (value : K) :
    map embedding (DensePolynomial.constant value) = DensePolynomial.constant (embedding.toFun value) := rfl

/-- A field embedding maps a finite zero block to the same-length zero block.

Preservation of the original scalar zero maps every retained repeated entry to target zero. The same finite count and
original block order remain. -/
private theorem map_replicate_zero (embedding : Algebra.Field.Embedding K L) (amount : Nat) :
    (List.replicate amount (0 : K)).map embedding.toFun =
      List.replicate amount (0 : L) := by
  rewrite [List.Replicate.map_replicate, embedding.map_zero]
  exact Eq.refl _

/-- A field embedding commutes with zero-padding the high-degree end of a coefficient list.

The retained zero block is mapped before the same original coefficient list. Neither its displayed count nor the
coefficient order changes. -/
private theorem map_padLeft (embedding : Algebra.Field.Embedding K L)
    (amount : Nat) (values : List K) :
    (DensePolynomial.padLeft amount values).map embedding.toFun =
      DensePolynomial.padLeft amount (values.map embedding.toFun) := by
  unfold DensePolynomial.padLeft
  rewrite [List.Map.map_append, map_replicate_zero embedding]
  exact Eq.refl _

/-- A field embedding commutes with pairwise addition of coefficient lists.

Both retained lists advance together until one ends. The original scalar addition certificate maps each paired head and
structural recursion preserves the unchanged paired tails. -/
private theorem map_zipWith_add (embedding : Algebra.Field.Embedding K L) :
    ∀ left right : List K,
      (List.zipWith (· + ·) left right).map embedding.toFun =
        List.zipWith (· + ·) (left.map embedding.toFun)
          (right.map embedding.toFun)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | left :: leftTail, right :: rightTail => by
      rewrite [List.zipWith_cons_cons, List.map_cons, List.map_cons,
        List.map_cons, List.zipWith_cons_cons]
      exact congrArg₂ List.cons (embedding.map_add left right)
        (map_zipWith_add embedding leftTail rightTail)

/-- Coefficient mapping preserves dense polynomial addition.

The two original coefficient counts determine the same maximum padding width after mapping. Mapping their retained
padded sum list and normalizing therefore gives the same output. -/
public theorem map_add (embedding : Algebra.Field.Embedding K L) (left right : CoefficientPolynomial K) :
    map embedding (left + right) = map embedding left + map embedding right := by
  change map embedding (DensePolynomial.add left right) =
    DensePolynomial.add (map embedding left) (map embedding right)
  unfold DensePolynomial.add
  rewrite [map_normalize]
  apply congrArg DensePolynomial.normalize
  apply DensePolynomial.ext
  change (List.zipWith (· + ·)
      (DensePolynomial.padLeft (max left.coeffs.length right.coeffs.length - left.coeffs.length)
        left.coeffs)
      (DensePolynomial.padLeft (max left.coeffs.length right.coeffs.length - right.coeffs.length)
        right.coeffs)).map embedding.toFun =
    List.zipWith (· + ·)
      (DensePolynomial.padLeft
        (max (left.coeffs.map embedding.toFun).length (right.coeffs.map embedding.toFun).length -
          (left.coeffs.map embedding.toFun).length) (left.coeffs.map embedding.toFun))
      (DensePolynomial.padLeft
        (max (left.coeffs.map embedding.toFun).length (right.coeffs.map embedding.toFun).length -
          (right.coeffs.map embedding.toFun).length) (right.coeffs.map embedding.toFun))
  rewrite [List.Map.length_map, List.Map.length_map, map_zipWith_add,
    map_padLeft, map_padLeft]
  exact Eq.refl _

/-- Coefficient mapping preserves normalized dense negation.

Each original coefficient negation is transported by the retained scalar negation certificate. The same mapped
coefficient list then undergoes its original normalization. -/
public theorem map_neg (embedding : Algebra.Field.Embedding K L) (polynomial : CoefficientPolynomial K) :
    map embedding (-polynomial) = -map embedding polynomial := by
  change map embedding (DensePolynomial.neg polynomial) = DensePolynomial.neg (map embedding polynomial)
  change map embedding (DensePolynomial.normalize ⟨polynomial.coeffs.map (-·)⟩) =
    DensePolynomial.normalize ⟨(polynomial.coeffs.map embedding.toFun).map (-·)⟩
  rw [map_normalize]
  apply congrArg DensePolynomial.normalize
  apply DensePolynomial.ext
  change (polynomial.coeffs.map (-·)).map embedding.toFun =
    (polynomial.coeffs.map embedding.toFun).map (-·)
  rewrite [List.Map.map_map, List.Map.map_map]
  apply List.Map.map_congr_left
  intro value _
  exact embedding.map_neg value

/-- Coefficient mapping preserves dense polynomial subtraction.

The original coefficient subtraction is normalized addition with the negated right input. Mapping transports those same
two original operations. -/
public theorem map_sub (embedding : Algebra.Field.Embedding K L) (left right : CoefficientPolynomial K) :
    map embedding (left - right) = map embedding left - map embedding right := by
  change map embedding (left + -right) = map embedding left + -map embedding right
  rw [map_add, map_neg]

/-- Mapping a scaled polynomial maps both the scalar and the coefficient table.

The original supplied scalar maps once and multiplies every same original coefficient. Their retained product readbacks
and leading-zero decisions determine the same normalized output. -/
private theorem map_scale (embedding : Algebra.Field.Embedding K L)
    (scalar : K) (polynomial : CoefficientPolynomial K) :
    map embedding (DensePolynomial.scale scalar polynomial) =
      DensePolynomial.scale (embedding.toFun scalar) (map embedding polynomial) := by
  calc
    map embedding (DensePolynomial.scale scalar polynomial) =
        map embedding (DensePolynomial.normalize
          ⟨polynomial.coeffs.map (scalar * ·)⟩) := rfl
    _ = (map embedding
          ⟨polynomial.coeffs.map (scalar * ·)⟩).normalize :=
      map_normalize embedding _
    _ = DensePolynomial.scale (embedding.toFun scalar) (map embedding polynomial) := by
      apply DensePolynomial.ext
      unfold DensePolynomial.scale map
      change ((polynomial.coeffs.map (scalar * ·)).map embedding.toFun).dropWhile
          (fun value : L => decide (value = 0)) =
        ((polynomial.coeffs.map embedding.toFun).map (embedding.toFun scalar * ·)).dropWhile
          (fun value : L => decide (value = 0))
      rewrite [List.Map.map_map, List.Map.map_map]
      apply congrArg (List.dropWhile (fun value : L => decide (value = 0)))
      apply List.Map.map_congr_left
      intro value _
      exact embedding.map_mul scalar value

/-- Coefficient mapping commutes with multiplication by a displayed power of the variable.

The original zero decision chooses the same branch after mapping. A nonzero polynomial retains its normalized original
table followed by the same-length zero block. -/
public theorem map_shift (embedding : Algebra.Field.Embedding K L)
    (amount : Nat) (polynomial : CoefficientPolynomial K) :
    map embedding (DensePolynomial.shift amount polynomial) =
      DensePolynomial.shift amount (map embedding polynomial) := by
  unfold DensePolynomial.shift
  rw [map_isZero]
  split
  · exact map_zero_polynomial embedding
  · apply DensePolynomial.ext
    change ((polynomial.normalize.coeffs ++ List.replicate amount 0).map
        embedding.toFun) =
      (map embedding polynomial).normalize.coeffs ++ List.replicate amount 0
    rewrite [List.Map.map_append, map_replicate_zero, ← map_normalize]
    exact Eq.refl _

/-- Coefficient mapping preserves finite Horner polynomial multiplication.

The fold invariant maps the accumulator together with the fixed right factor and each next coefficient. -/
public theorem map_mul (embedding : Algebra.Field.Embedding K L) (left right : CoefficientPolynomial K) :
    map embedding (left * right) = map embedding left * map embedding right := by
  change map embedding (DensePolynomial.mulPolynomial left right) =
    DensePolynomial.mulPolynomial (map embedding left) (map embedding right)
  unfold DensePolynomial.mulPolynomial
  have foldMap : ∀ (coefficients : List K) (accumulator : CoefficientPolynomial K),
      map embedding
          (coefficients.foldl
            (fun value coefficient => DensePolynomial.shift 1 value + DensePolynomial.scale coefficient right)
            accumulator) =
        (coefficients.map embedding.toFun).foldl
          (fun value coefficient =>
            DensePolynomial.shift 1 value + DensePolynomial.scale coefficient (map embedding right))
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
            DensePolynomial.shift 1 value + DensePolynomial.scale coefficient (map embedding right)) initial)
        rw [map_add, map_shift, map_scale]
  rw [foldMap]
  rfl

/-- A field embedding commutes with scalar Horner evaluation from a supplied accumulator.

Each original multiply-and-add Horner update maps to the corresponding update at the mapped point. The retained original
accumulator and remaining coefficients advance through the same scan. -/
private theorem map_evalCoeffs_from (embedding : Algebra.Field.Embedding K L)
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

/-- Horner evaluation commutes with an explicit finite field embedding.

The original zero-start Horner accumulator maps to target zero. Each retained coefficient and the supplied point are
mapped through the same finite scalar scan. -/
public theorem map_eval (embedding : Algebra.Field.Embedding K L) (polynomial : CoefficientPolynomial K)
    (point : K) :
    embedding.toFun (polynomial.eval point) =
      (map embedding polynomial).eval (embedding.toFun point) := by
  unfold DensePolynomial.eval
    DensePolynomial.evalCoeffs map
  rw [← embedding.map_zero]
  exact map_evalCoeffs_from embedding point polynomial.coeffs 0

/-- Coefficient mapping preserves the one-term quotient used in leading cancellation.

The original leading ratio maps by the retained division certificate. The exact same degree difference shifts that
retained single coefficient. -/
public theorem map_leadQuotient (embedding : Algebra.Field.Embedding K L)
    (left right : CoefficientPolynomial K) :
    map embedding (DensePolynomial.leadQuotient left right) =
      DensePolynomial.leadQuotient (map embedding left) (map embedding right) := by
  unfold DensePolynomial.leadQuotient
  rw [map_shift, map_natDegree, map_natDegree]
  apply congrArg (DensePolynomial.shift (left.natDegree - right.natDegree))
  apply DensePolynomial.ext
  simp only [map_coeffs, List.map_cons, List.map_nil]
  rw [Embedding.map_div, map_leadingCoeff, map_leadingCoeff]

/-- Coefficient mapping commutes with one exact leading-term cancellation.

Both original leading coefficients and their ratio map together. The same degree shift, scaled divisor and subtraction
state give the mapped cancellation output. -/
public theorem map_cancelLead (embedding : Algebra.Field.Embedding K L)
    (left right : CoefficientPolynomial K) :
    map embedding (DensePolynomial.cancelLead left right) =
      DensePolynomial.cancelLead (map embedding left) (map embedding right) := by
  unfold DensePolynomial.cancelLead
  rw [map_sub, map_shift, map_scale, map_natDegree, map_natDegree,
    Embedding.map_div, map_leadingCoeff, map_leadingCoeff]

/-- A coefficient embedding maps the quotient of a fixed-fuel division run to the quotient of the mapped run.

The initial quotient accumulator is mapped together with both inputs, preserving every stopping test. -/
public theorem map_divLoop_quotient (embedding : Algebra.Field.Embedding K L) :
    ∀ (fuel : Nat) (left right quotient : CoefficientPolynomial K),
      map embedding (DensePolynomial.divLoop fuel left right quotient).quotient =
        (DensePolynomial.divLoop fuel (map embedding left) (map embedding right)
          (map embedding quotient)).quotient
  | 0, _, _, _ => rfl
  | fuel + 1, left, right, quotient => by
      rw [DensePolynomial.divLoop_succ, DensePolynomial.divLoop_succ, map_isZero, map_isZero,
        map_natDegree, map_natDegree]
      split
      · rfl
      · dsimp only
        rw [← map_cancelLead, ← map_leadQuotient, ← map_add]
        exact map_divLoop_quotient embedding fuel
          (DensePolynomial.cancelLead left right) right (quotient + DensePolynomial.leadQuotient left right)

/-- A coefficient embedding maps the remainder of a fixed-fuel division run to the mapped run remainder.

The original fuel, inputs and quotient accumulator determine the same stopping guard. Continuing branches map the same
cancelled dividend and completed recursive remainder. -/
public theorem map_divLoop_remainder (embedding : Algebra.Field.Embedding K L) :
    ∀ (fuel : Nat) (left right quotient : CoefficientPolynomial K),
      map embedding (DensePolynomial.divLoop fuel left right quotient).remainder =
        (DensePolynomial.divLoop fuel (map embedding left) (map embedding right)
          (map embedding quotient)).remainder
  | 0, _, _, _ => rfl
  | fuel + 1, left, right, quotient => by
      rw [DensePolynomial.divLoop_succ, DensePolynomial.divLoop_succ, map_isZero, map_isZero,
        map_natDegree, map_natDegree]
      split
      · rfl
      · dsimp only
        rw [← map_cancelLead, ← map_leadQuotient, ← map_add]
        exact map_divLoop_remainder embedding fuel
          (DensePolynomial.cancelLead left right) right (quotient + DensePolynomial.leadQuotient left right)

/-- A coefficient embedding preserves the number of cancellations in a fixed-fuel division run.

The original stopping branch contributes zero steps. Every continuing branch adds one to the same completed
predecessor-fuel run after mapping its retained state. -/
public theorem map_divLoop_steps (embedding : Algebra.Field.Embedding K L) :
    ∀ (fuel : Nat) (left right quotient : CoefficientPolynomial K),
      (DensePolynomial.divLoop fuel left right quotient).steps =
        (DensePolynomial.divLoop fuel (map embedding left) (map embedding right)
          (map embedding quotient)).steps
  | 0, _, _, _ => rfl
  | fuel + 1, left, right, quotient => by
      rw [DensePolynomial.divLoop_succ, DensePolynomial.divLoop_succ, map_isZero, map_isZero,
        map_natDegree, map_natDegree]
      split
      · rfl
      · dsimp only
        rw [← map_cancelLead, ← map_leadQuotient, ← map_add]
        exact congrArg (· + 1) (map_divLoop_steps embedding fuel
          (DensePolynomial.cancelLead left right) right (quotient + DensePolynomial.leadQuotient left right))

/-- Executable normalized division commutes with coefficient mapping on its quotient.

Normalized original inputs and the same coefficient-count fuel are retained. The completed mapped run returns the
embedding of the original quotient. -/
public theorem map_divMod_quotient (embedding : Algebra.Field.Embedding K L)
    (left right : CoefficientPolynomial K) :
    map embedding (DensePolynomial.divMod left right).quotient =
      (DensePolynomial.divMod (map embedding left) (map embedding right)).quotient := by
  unfold DensePolynomial.divMod
  rw [map_degreeCount, ← map_normalize, ← map_normalize,
    ← map_zero_polynomial (K := K) (L := L)]
  exact map_divLoop_quotient embedding _ left.normalize right.normalize 0

/-- Executable normalized division commutes with coefficient mapping on its remainder.

Normalized original inputs and the same coefficient-count fuel are retained. The completed mapped run returns the
embedding of the original remainder. -/
public theorem map_divMod_remainder (embedding : Algebra.Field.Embedding K L)
    (left right : CoefficientPolynomial K) :
    map embedding (DensePolynomial.divMod left right).remainder =
      (DensePolynomial.divMod (map embedding left) (map embedding right)).remainder := by
  unfold DensePolynomial.divMod
  rw [map_degreeCount, ← map_normalize, ← map_normalize,
    ← map_zero_polynomial (K := K) (L := L)]
  exact map_divLoop_remainder embedding _ left.normalize right.normalize 0

/-- Executable normalized division performs the same number of steps after a coefficient embedding.

Mapping preserves both original normalized states and their coefficient-count fuel. Each same cancellation decision
contributes to the retained step count. -/
public theorem map_divMod_steps (embedding : Algebra.Field.Embedding K L)
    (left right : CoefficientPolynomial K) :
    (DensePolynomial.divMod left right).steps =
      (DensePolynomial.divMod (map embedding left) (map embedding right)).steps := by
  unfold DensePolynomial.divMod
  rw [map_degreeCount, ← map_normalize, ← map_normalize,
    ← map_zero_polynomial (K := K) (L := L)]
  exact map_divLoop_steps embedding _ left.normalize right.normalize 0

end Purelib.Polynomial.Dense.Map
