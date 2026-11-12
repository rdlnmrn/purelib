module

public import Purelib.Polynomial.Dense.Map.Basic
public import Purelib.Polynomial.Dense.Multiplication.Basic
import Purelib.Data.List.Map
import Purelib.Data.List.DropWhile.Basic
import Purelib.Data.List.Replicate

/-!
# Injective ring coefficient maps and normalized arithmetic

The original coefficient map and every normalization decision commute through
an injective zero-preserving scalar function. Retained addition, negation and
multiplication laws transport the same finite polynomial operations.
-/

namespace Purelib.Polynomial.Dense.Map

open Purelib.Polynomial.Dense.Basic
open Purelib.Data

variable {K L : Type*} [CommRing K] [DecidableEq K] [CommRing L] [DecidableEq L]

omit [DecidableEq K] [DecidableEq L] in
/-- An injective zero-preserving scalar map detects the original scalar zero. -/
public theorem map_zero_iff (function : K → L) (mapZero : function 0 = 0)
    (injective : Function.Injective function) (value : K) : function value = 0 ↔ value = 0 := by
  constructor
  · intro equal
    exact injective (equal.trans mapZero.symm)
  · intro equal
    exact (congrArg function equal).trans mapZero

/-- An injective scalar map commutes with removing leading zero coefficients.

Injectivity identifies the exact mapped zero decision with the source decision. The first nonzero original coefficient
therefore retains its whole same mapped tail, while zero heads are discarded in the same order. -/
private theorem map_dropWhile_zero (function : K → L) (mapZero : function 0 = 0)
    (injective : Function.Injective function) :
    ∀ values : List K,
      (values.dropWhile (· = 0)).map function =
        (values.map function).dropWhile (· = 0)
  | [] => rfl
  | value :: remaining => by
      by_cases zero : value = 0
      · have imageZero : function value = 0 :=
          (map_zero_iff function mapZero injective value).mpr zero
        rewrite [List.DropWhile.cons_of_true (fun entry : K => decide (entry = 0))
            value remaining (decide_eq_true zero),
          List.map_cons,
          List.DropWhile.cons_of_true (fun entry : L => decide (entry = 0))
            (function value) (remaining.map function)
            (decide_eq_true imageZero)]
        exact (map_dropWhile_zero function mapZero injective) remaining
      · have imageNonzero : function value ≠ 0 :=
          fun imageZero => zero ((map_zero_iff function mapZero injective value).mp imageZero)
        rewrite [List.DropWhile.cons_of_false (fun entry : K => decide (entry = 0))
            value remaining (decide_eq_false zero),
          List.map_cons,
          List.DropWhile.cons_of_false (fun entry : L => decide (entry = 0))
            (function value) (remaining.map function)
            (decide_eq_false imageNonzero)]
        exact Eq.refl _

/-- Mapping coefficients commutes with dense normalization.

The same original leading-zero scan and retained scalar map commute at each coefficient. The resulting normalized list
retains its original coefficient order. -/
public theorem map_normalize (function : K → L) (mapZero : function 0 = 0)
    (injective : Function.Injective function) (polynomial : CoefficientPolynomial K) :
    map function polynomial.normalize = (map function polynomial).normalize := by
  apply DensePolynomial.ext
  exact (map_dropWhile_zero function mapZero injective) polynomial.coeffs

/-- An injective coefficient function preserves the executable polynomial zero test.

Normalization commutes with the retained function, whose list map preserves the original empty or nonempty constructor.
The same normalized coefficient table therefore determines the zero test. -/
@[simp] public theorem map_isZero (function : K → L) (mapZero : function 0 = 0)
    (injective : Function.Injective function)
    (polynomial : CoefficientPolynomial K) :
    (map function polynomial).isZero = polynomial.isZero := by
  unfold DensePolynomial.isZero
  rw [← (map_normalize function mapZero injective)]
  change (polynomial.normalize.coeffs.map function).isEmpty =
    polynomial.normalize.coeffs.isEmpty
  cases polynomial.normalize.coeffs <;> rfl

/-- An injective coefficient function preserves the normalized coefficient count.

The retained normalized source table maps to the normalized target table. Each original entry contributes one mapped
entry, preserving that same finite count. -/
@[simp] public theorem map_degreeCount (function : K → L) (mapZero : function 0 = 0)
    (injective : Function.Injective function)
    (polynomial : CoefficientPolynomial K) :
    (map function polynomial).degreeCount = polynomial.degreeCount := by
  unfold DensePolynomial.degreeCount
  rw [← (map_normalize function mapZero injective)]
  change (polynomial.normalize.coeffs.map function).length =
    polynomial.normalize.coeffs.length
  exact List.Map.length_map function polynomial.normalize.coeffs

/-- An injective coefficient function preserves the executable natural degree. -/
@[simp] public theorem map_natDegree (function : K → L) (mapZero : function 0 = 0)
    (injective : Function.Injective function)
    (polynomial : CoefficientPolynomial K) :
    (map function polynomial).natDegree = polynomial.natDegree := by
  unfold DensePolynomial.natDegree
  rw [(map_degreeCount function mapZero injective)]

omit [DecidableEq K] [DecidableEq L] in
/-- Mapping a list and reading its head with zero default equals mapping the original head readback. -/
private theorem headD_map (function : K → L) (mapZero : function 0 = 0) :
    ∀ values : List K,
      (values.map function).headD 0 =
        function (values.headD 0)
  | [] => mapZero.symm
  | _ :: _ => rfl

/-- The mapped polynomial leading coefficient is the function of the original leading coefficient.

The original normalized head is retained on both sides. The function of the zero default agrees with the target zero
when the same original list is empty. -/
@[simp] public theorem map_leadingCoeff (function : K → L) (mapZero : function 0 = 0)
    (injective : Function.Injective function)
    (polynomial : CoefficientPolynomial K) :
    (map function polynomial).leadingCoeff =
      function polynomial.leadingCoeff := by
  unfold DensePolynomial.leadingCoeff
  rw [← (map_normalize function mapZero injective)]
  exact (headD_map function mapZero) polynomial.normalize.coeffs

omit [CommRing K] [DecidableEq K] [CommRing L] [DecidableEq L] in
/-- Coefficient mapping preserves the empty zero polynomial. -/
@[simp] public theorem map_zero_polynomial (function : K → L) :
    map function (0 : CoefficientPolynomial K) = 0 := rfl

omit [CommRing K] [DecidableEq K] [CommRing L] [DecidableEq L] in
/-- Mapping a constant polynomial maps its retained constant coefficient. -/
@[simp] public theorem map_constant (function : K → L) (value : K) :
    map function (DensePolynomial.constant value) = DensePolynomial.constant (function value) := rfl

omit [DecidableEq K] [DecidableEq L] in
/-- A scalar map maps a finite zero block to the same-length zero block.

Preservation of the original scalar zero maps every retained repeated entry to target zero. The same finite count and
original block order remain. -/
private theorem map_replicate_zero (function : K → L) (mapZero : function 0 = 0) (amount : Nat) :
    (List.replicate amount (0 : K)).map function =
      List.replicate amount (0 : L) := by
  rewrite [List.Replicate.map_replicate, mapZero]
  exact Eq.refl _

omit [DecidableEq K] [DecidableEq L] in
/-- A scalar map commutes with zero-padding the high-degree end of a coefficient list.

The retained zero block is mapped before the same original coefficient list. Neither its displayed count nor the
coefficient order changes. -/
private theorem map_padLeft (function : K → L) (mapZero : function 0 = 0)
    (amount : Nat) (values : List K) :
    (DensePolynomial.padLeft amount values).map function =
      DensePolynomial.padLeft amount (values.map function) := by
  unfold DensePolynomial.padLeft
  rewrite [List.Map.map_append, (map_replicate_zero function mapZero)]
  exact Eq.refl _

omit [DecidableEq K] [DecidableEq L] in
/-- A scalar map commutes with pairwise addition of coefficient lists.

Both retained lists advance together until one ends. The original scalar addition certificate maps each paired head and
structural recursion preserves the unchanged paired tails. -/
private theorem map_zipWith_add (function : K → L)
    (mapAdd : ∀ left right, function (left + right) = function left + function right) :
    ∀ left right : List K,
      (List.zipWith (· + ·) left right).map function =
        List.zipWith (· + ·) (left.map function)
          (right.map function)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | left :: leftTail, right :: rightTail => by
      rewrite [List.zipWith_cons_cons, List.map_cons, List.map_cons,
        List.map_cons, List.zipWith_cons_cons]
      exact congrArg₂ List.cons (mapAdd left right)
        ((map_zipWith_add function mapAdd) leftTail rightTail)

/-- Coefficient mapping preserves dense polynomial addition.

The two original coefficient counts determine the same maximum padding width after mapping. Mapping their retained
padded sum list and normalizing therefore gives the same output. -/
public theorem map_add (function : K → L) (mapZero : function 0 = 0)
    (injective : Function.Injective function)
    (mapAdd : ∀ left right, function (left + right) = function left + function right)
    (left right : CoefficientPolynomial K) :
    map function (left + right) = map function left + map function right := by
  change map function (DensePolynomial.add left right) =
    DensePolynomial.add (map function left) (map function right)
  unfold DensePolynomial.add
  rewrite [(map_normalize function mapZero injective)]
  apply congrArg DensePolynomial.normalize
  apply DensePolynomial.ext
  change (List.zipWith (· + ·)
      (DensePolynomial.padLeft (max left.coeffs.length right.coeffs.length - left.coeffs.length)
        left.coeffs)
      (DensePolynomial.padLeft (max left.coeffs.length right.coeffs.length - right.coeffs.length)
        right.coeffs)).map function =
    List.zipWith (· + ·)
      (DensePolynomial.padLeft
        (max (left.coeffs.map function).length (right.coeffs.map function).length -
          (left.coeffs.map function).length) (left.coeffs.map function))
      (DensePolynomial.padLeft
        (max (left.coeffs.map function).length (right.coeffs.map function).length -
          (right.coeffs.map function).length) (right.coeffs.map function))
  rewrite [List.Map.length_map, List.Map.length_map, (map_zipWith_add function mapAdd),
    (map_padLeft function mapZero), (map_padLeft function mapZero)]
  exact Eq.refl _

/-- Coefficient mapping preserves normalized dense negation.

Each original coefficient negation is transported by the retained scalar negation certificate. The same mapped
coefficient list then undergoes its original normalization. -/
public theorem map_neg (function : K → L) (mapZero : function 0 = 0)
    (injective : Function.Injective function)
    (mapNeg : ∀ value, function (-value) = -function value) (polynomial : CoefficientPolynomial K) :
    map function (-polynomial) = -map function polynomial := by
  change map function (DensePolynomial.neg polynomial) = DensePolynomial.neg (map function polynomial)
  change map function (DensePolynomial.normalize ⟨polynomial.coeffs.map (-·)⟩) =
    DensePolynomial.normalize ⟨(polynomial.coeffs.map function).map (-·)⟩
  rw [(map_normalize function mapZero injective)]
  apply congrArg DensePolynomial.normalize
  apply DensePolynomial.ext
  change (polynomial.coeffs.map (-·)).map function =
    (polynomial.coeffs.map function).map (-·)
  rewrite [List.Map.map_map, List.Map.map_map]
  apply List.Map.map_congr_left
  intro value _
  exact mapNeg value

/-- Coefficient mapping preserves dense polynomial subtraction.

The original coefficient subtraction is normalized addition with the negated right input. Mapping transports those same
two original operations. -/
public theorem map_sub (function : K → L) (mapZero : function 0 = 0)
    (injective : Function.Injective function)
    (mapAdd : ∀ left right, function (left + right) = function left + function right)
    (mapNeg : ∀ value, function (-value) = -function value) (left right : CoefficientPolynomial K) :
    map function (left - right) = map function left - map function right := by
  change map function (left + -right) = map function left + -map function right
  rw [(map_add function mapZero injective mapAdd), (map_neg function mapZero injective mapNeg)]

/-- Mapping a scaled polynomial maps both the scalar and the coefficient table.

The original supplied scalar maps once and multiplies every same original coefficient. Their retained product readbacks
and leading-zero decisions determine the same normalized output. -/
public theorem map_scale (function : K → L) (mapZero : function 0 = 0)
    (injective : Function.Injective function)
    (mapMul : ∀ left right, function (left * right) = function left * function right)
    (scalar : K) (polynomial : CoefficientPolynomial K) :
    map function (DensePolynomial.scale scalar polynomial) =
      DensePolynomial.scale (function scalar) (map function polynomial) := by
  calc
    map function (DensePolynomial.scale scalar polynomial) =
        map function (DensePolynomial.normalize
          ⟨polynomial.coeffs.map (scalar * ·)⟩) := rfl
    _ = (map function
          ⟨polynomial.coeffs.map (scalar * ·)⟩).normalize :=
      (map_normalize function mapZero injective) _
    _ = DensePolynomial.scale (function scalar) (map function polynomial) := by
      apply DensePolynomial.ext
      unfold DensePolynomial.scale map
      change ((polynomial.coeffs.map (scalar * ·)).map function).dropWhile
          (fun value : L => decide (value = 0)) =
        ((polynomial.coeffs.map function).map (function scalar * ·)).dropWhile
          (fun value : L => decide (value = 0))
      rewrite [List.Map.map_map, List.Map.map_map]
      apply congrArg (List.dropWhile (fun value : L => decide (value = 0)))
      apply List.Map.map_congr_left
      intro value _
      exact mapMul scalar value

/-- Coefficient mapping commutes with multiplication by a displayed power of the variable.

The original zero decision chooses the same branch after mapping. A nonzero polynomial retains its normalized original
table followed by the same-length zero block. -/
public theorem map_shift (function : K → L) (mapZero : function 0 = 0)
    (injective : Function.Injective function)
    (amount : Nat) (polynomial : CoefficientPolynomial K) :
    map function (DensePolynomial.shift amount polynomial) =
      DensePolynomial.shift amount (map function polynomial) := by
  unfold DensePolynomial.shift
  rw [(map_isZero function mapZero injective)]
  split
  · exact (map_zero_polynomial function)
  · apply DensePolynomial.ext
    change ((polynomial.normalize.coeffs ++ List.replicate amount 0).map
        function) =
      (map function polynomial).normalize.coeffs ++ List.replicate amount 0
    rewrite [List.Map.map_append, (map_replicate_zero function mapZero), ← (map_normalize function mapZero injective)]
    exact Eq.refl _

/-- Coefficient mapping preserves finite Horner polynomial multiplication.

The fold invariant maps the accumulator together with the fixed right factor and each next coefficient. -/
public theorem map_mul (function : K → L) (mapZero : function 0 = 0)
    (injective : Function.Injective function)
    (mapAdd : ∀ left right, function (left + right) = function left + function right)
    (mapMul : ∀ left right, function (left * right) = function left * function right)
    (left right : CoefficientPolynomial K) :
    map function (left * right) = map function left * map function right := by
  change map function (DensePolynomial.mulPolynomial left right) =
    DensePolynomial.mulPolynomial (map function left) (map function right)
  unfold DensePolynomial.mulPolynomial
  have foldMap : ∀ (coefficients : List K) (accumulator : CoefficientPolynomial K),
      map function
          (coefficients.foldl
            (fun value coefficient => DensePolynomial.shift 1 value + DensePolynomial.scale coefficient right)
            accumulator) =
        (coefficients.map function).foldl
          (fun value coefficient =>
            DensePolynomial.shift 1 value + DensePolynomial.scale coefficient (map function right))
          (map function accumulator) := by
    intro coefficients
    induction coefficients with
    | nil => intro accumulator; rfl
    | cons coefficient remaining inductionHypothesis =>
        intro accumulator
        simp only [List.foldl_cons, List.map_cons]
        rw [inductionHypothesis]
        apply congrArg (fun initial => remaining.map function |>.foldl
          (fun value coefficient =>
            DensePolynomial.shift 1 value + DensePolynomial.scale coefficient (map function right)) initial)
        rw [map_add function mapZero injective mapAdd, map_shift function mapZero injective,
          map_scale function mapZero injective mapMul]
  rw [foldMap]
  rfl

end Purelib.Polynomial.Dense.Map
