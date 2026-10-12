module

public import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Ring.IntCast
-- Public evaluation laws retain this exact negation parent in their signatures.
public import Purelib.Algebra.Group.Negation
import Purelib.Data.Int.Arithmetic
import Purelib.Data.Nat.Order
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

/-!
# Finite integer-polynomial certificates

Integer coefficient lists are stored in ascending degree order.  The
primitive-recursive operations below let a literal finite Bezout identity be
checked by kernel reduction over `Int`, then evaluated in any constructive
explicit field.  This is useful for prime-field exclusions without listing
or searching an ambient carrier.
-/

namespace Purelib.Polynomial.Ascending.Integer.Basic

open Purelib.Algebra.Field
open Purelib.Algebra.Ring
open Purelib.Data.Int
open Purelib.Data.Nat
open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

/-- Evaluate an ascending finite integer coefficient list by Horner's rule.

Each displayed integer coefficient uses its original cast into the supplied
explicit field. The original ascending Horner recursion retains the tail and
evaluation argument at every scalar step. -/
@[expose] public def eval {K : Type*} [ExplicitField K] : List Int → K → K
  | [], _ => 0
  | coefficient :: remaining, value =>
      (coefficient : K) + value * Purelib.Polynomial.Ascending.Integer.Basic.eval remaining value

/-- The empty integer coefficient table evaluates to zero in the explicit field. -/
@[simp] public theorem eval_nil {K : Type*} [ExplicitField K] (value : K) :
    eval [] value = 0 := rfl

/-- A nonempty integer table evaluates as its cast head plus the argument times its tail value. -/
@[simp] public theorem eval_cons {K : Type*} [ExplicitField K]
    (coefficient : Int) (remaining : List Int) (value : K) :
    eval (coefficient :: remaining) value =
      (coefficient : K) + value * eval remaining value := rfl

namespace Certificate

/-- Coefficientwise addition, padding the shorter high-degree tail by zero.

Paired heads are added using the retained integer operation. Once either
original spine is exhausted, the unmatched higher-degree tail is retained unchanged. -/
@[expose] public def add : List Int → List Int → List Int
  | [], right => right
  | left, [] => left
  | left :: lefts, right :: rights => (left + right) :: Purelib.Polynomial.Ascending.Integer.Basic.Certificate.add lefts
    rights

end Certificate

namespace Certificate

/-- Multiply every coefficient by one displayed integer.

Each original coefficient is multiplied by the same displayed integer.
The retained recursive tail preserves the original coefficient positions. -/
@[expose] public def scale (factor : Int) : List Int → List Int
  | [] => []
  | coefficient :: remaining =>
      factor * coefficient :: Purelib.Polynomial.Ascending.Integer.Basic.Certificate.scale factor remaining

end Certificate

namespace Certificate

/-- Finite convolution in ascending-degree representation.

Each head coefficient scales the original right table. The recursively
completed tail product is shifted by one degree before the same padded addition. -/
@[expose] public def mul : List Int → List Int → List Int
  | [], _ => []
  | coefficient :: remaining, right =>
      Certificate.add (Certificate.scale coefficient right) (0 ::
        Purelib.Polynomial.Ascending.Integer.Basic.Certificate.mul remaining right)

end Certificate

/-- Evaluation preserves padded addition of integer coefficient tables.

The shorter original coefficient tail is retained by padded addition. Each
paired head uses the integer addition cast equation before the unchanged tails
are compared by scalar field arithmetic. -/
public theorem eval_add {K : Type*} [ExplicitField K]
    (left right : List Int) (value : K) :
    eval (Certificate.add left right) value = eval left value + eval right value := by
  induction left generalizing right with
  | nil =>
      change eval right value = 0 + eval right value
      exact (zero_add _).symm
  | cons coefficient remaining inductionHypothesis =>
      cases right with
      | nil =>
          change eval (coefficient :: remaining) value =
            eval (coefficient :: remaining) value + 0
          exact (add_zero _).symm
      | cons other others =>
          rewrite [Certificate.add, eval_cons,
            eval_cons, eval_cons,
            IntCast.add, inductionHypothesis others]
          ring1

/-- Evaluation of integer-scaled coefficients equals the cast factor times the original value.

Each original coefficient is multiplied by the same retained integer factor.
The multiplication cast equation transports each scalar step into the supplied
field without changing its operations. -/
public theorem eval_scale {K : Type*} [ExplicitField K]
    (factor : Int) (coefficients : List Int) (value : K) :
    eval (Certificate.scale factor coefficients) value =
      (factor : K) * eval coefficients value := by
  induction coefficients with
  | nil =>
      change (0 : K) = (factor : K) * 0
      rewrite [mul_zero]
      exact Eq.refl _
  | cons coefficient remaining inductionHypothesis =>
      rewrite [Certificate.scale, eval_cons,
        IntCast.intCast_mul, inductionHypothesis, eval_cons]
      ring1

/-- Evaluation turns finite integer coefficient convolution into multiplication in the explicit field.

The original convolution retains its scaled right list and shifted tail product.
Their evaluation certificates combine the same coefficients and scalar field
operations along the original finite recursion. -/
public theorem eval_mul {K : Type*} [ExplicitField K]
    (left right : List Int) (value : K) :
    eval (Certificate.mul left right) value = eval left value * eval right value := by
  induction left with
  | nil =>
      change (0 : K) = 0 * eval right value
      rewrite [zero_mul]
      exact Eq.refl _
  | cons coefficient remaining inductionHypothesis =>
      rewrite [Certificate.mul, eval_add,
        eval_scale, eval_cons,
        IntCast.cast_zero, zero_add, inductionHypothesis, eval_cons]
      ring1

/-- Coefficientwise negation. -/
@[expose] public def neg (coefficients : List Int) : List Int :=
  Certificate.scale (-1) coefficients

/-- Coefficientwise subtraction, padding the shorter high-degree tail.

The original left coefficient table is added to the retained negated right
table. The same padded addition preserves every unmatched high-degree entry. -/
@[expose] public def sub (left right : List Int) : List Int :=
  Certificate.add left (neg right)

/-- Negating every integer coefficient negates the polynomial value.

The original coefficient operation scales by the integer negative unit. Its
retained cast and scalar field law identify the negated original evaluation. -/
public theorem eval_neg {K : Type*} [ExplicitField K]
    (coefficients : List Int) (value : K) :
    eval (neg coefficients) value = -eval coefficients value := by
  rw [neg, eval_scale]
  change ((Int.neg 1 : Int) : K) * eval coefficients value =
    -eval coefficients value
  rewrite [IntCast.neg, Int.cast_one]
  ring1

/-- Evaluation preserves padded coefficient subtraction.

The original subtraction adds the left table to the original negated right
table. Their retained evaluations use the same field subtraction operation. -/
public theorem eval_sub {K : Type*} [ExplicitField K]
    (left right : List Int) (value : K) :
    eval (sub left right) value = eval left value - eval right value := by
  rw [sub, eval_add, eval_neg]
  ring1

/-- Multiply by the indeterminate by shifting every coefficient up one
degree. -/
@[expose] public def shift (coefficients : List Int) : List Int := 0 :: coefficients

/-- Prepending zero multiplies the value by the evaluation argument.

The retained zero coefficient has field cast zero. Its original Horner step
therefore multiplies the unchanged tail evaluation by the supplied point. -/
public theorem eval_shift {K : Type*} [ExplicitField K]
    (coefficients : List Int) (value : K) :
    eval (shift coefficients) value = value * eval coefficients value := by
  unfold shift
  rewrite [eval_cons, IntCast.cast_zero, zero_add]
  exact Eq.refl _

/-- Prepending zero preserves the final coefficient of a nonempty table. -/
public theorem getLast?_shift_of_ne_nil (coefficients : List Int)
    (nonempty : coefficients ≠ []) :
    (shift coefficients).getLast? = coefficients.getLast? := by
  cases coefficients with
  | nil => exact (nonempty rfl).elim
  | cons coefficient remaining =>
      unfold shift
      rfl

/-- Integer coefficient scaling preserves the retained table length.

Every original entry contributes one scaled entry. Successor congruence
counts those same retained coefficient positions. -/
public theorem length_scale (factor : Int) (coefficients : List Int) :
    (Certificate.scale factor coefficients).length = coefficients.length := by
  induction coefficients with
  | nil => rfl
  | cons coefficient remaining inductionHypothesis =>
      change Nat.succ (Certificate.scale factor remaining).length =
        Nat.succ remaining.length
      exact congrArg Nat.succ inductionHypothesis

/-- Padded coefficient addition has the maximum of the two input lengths.

The shorter high-degree tail is padded by the original addition recurrence.
Paired heads consume one position on each side until one unchanged tail remains. -/
public theorem length_add (left right : List Int) :
    (Certificate.add left right).length = max left.length right.length := by
  induction left generalizing right with
  | nil =>
      change right.length = Nat.max 0 right.length
      exact (Order.zero_max _).symm
  | cons coefficient remaining inductionHypothesis =>
      cases right with
      | nil =>
          change (coefficient :: remaining).length = Nat.max (coefficient :: remaining).length 0
          exact (Order.max_zero _).symm
      | cons other others =>
          change Nat.succ (Certificate.add remaining others).length =
            Nat.max (Nat.succ remaining.length) (Nat.succ others.length)
          exact (congrArg Nat.succ (inductionHypothesis others)).trans
            (Order.succ_max_succ _ _).symm

/-- Coefficient negation preserves the retained table length. -/
public theorem length_neg (coefficients : List Int) :
    (neg coefficients).length = coefficients.length := by
  exact length_scale (-1) coefficients

/-- Padded coefficient subtraction has the maximum of the two input lengths. -/
public theorem length_sub (left right : List Int) :
    (sub left right).length = max left.length right.length := by
  rw [sub, length_add, length_neg]

/-- Adding a strictly shorter coefficient list cannot change the leading
coefficient of the longer list.

The strict length bound retains a final entry from the longer left table.
Structural recursion removes matching heads while keeping that final occurrence. -/
public theorem getLast?_add_of_length_lt : ∀ left right : List Int,
    right.length < left.length →
      (Certificate.add left right).getLast? = left.getLast?
  | [], right, shorter => by
      exact False.elim (Nat.not_lt_zero right.length shorter)
  | coefficient :: remaining, [], shorter => rfl
  | coefficient :: remaining, other :: others, shorter => by
      have tailsShorter : others.length < remaining.length := by
        exact Nat.lt_of_succ_lt_succ shorter
      cases remaining with
      | nil =>
          exact False.elim (Nat.not_lt_zero others.length tailsShorter)
      | cons next rest =>
          cases others with
          | nil => rfl
          | cons otherNext otherRest =>
              change (Certificate.add (next :: rest)
                (otherNext :: otherRest)).getLast? = (next :: rest).getLast?
              exact getLast?_add_of_length_lt (next :: rest)
                (otherNext :: otherRest) tailsShorter

/-- Negation maps the optional final coefficient to its integer negative.

The original coefficient scaling retains every position. Its scalar negative
unit multiplication identifies the integer negative at the original final slot. -/
public theorem getLast?_neg (coefficients : List Int) :
    (neg coefficients).getLast? = coefficients.getLast?.map (fun value => -value) := by
  induction coefficients with
  | nil => rfl
  | cons coefficient remaining inductionHypothesis =>
      cases remaining with
      | nil =>
          change some ((-1 : Int) * coefficient) = some (-coefficient)
          apply congrArg some
          rewrite [Arithmetic.neg_mul, one_mul]
          exact Eq.refl _
      | cons next rest =>
          change (neg (next :: rest)).getLast? =
            (next :: rest).getLast?.map (fun value => -value)
          exact inductionHypothesis

/-- Subtracting a strictly shorter table preserves the final coefficient of the longer left table. -/
public theorem getLast?_sub_of_length_lt (left right : List Int)
    (shorter : right.length < left.length) :
    (sub left right).getLast? = left.getLast? := by
  unfold sub
  apply getLast?_add_of_length_lt
  rw [length_neg]
  exact shorter

/-! ## Retained coefficient-table operations

The original table realization also retains direct degree readback and its
separate mapped-scaling convolution. These public operation owners and their
original finite recurrences remain unchanged.
-/

/-- An ascending finite integer coefficient list, retaining any trailing zeros. -/
public abbrev CoefficientList := List Int

/-- Read an integer coefficient by degree, returning zero beyond the retained list.

The retained natural degree selects its original list position. Exhausting
the finite table returns integer zero without adding coefficient entries. -/
@[expose] public def coefficient : CoefficientList → Nat → Int
  | [], _ => 0
  | value :: _, 0 => value
  | _ :: remaining, degree + 1 => coefficient remaining degree

namespace TorusInvariants

/-- Add ascending integer coefficient tables, retaining the unmatched longer tail.

The original table realization retains the unmatched longer tail after
adding each pair of displayed coefficient heads. -/
@[expose] public def add : CoefficientList → CoefficientList → CoefficientList
  | [], right => right
  | left, [] => left
  | left :: leftTail, right :: rightTail =>
      (left + right) :: Purelib.Polynomial.Ascending.Integer.Basic.TorusInvariants.add leftTail rightTail

end TorusInvariants

namespace TorusInvariants

/-- Scale the retained integer coefficient list by a displayed integer.

The original mapped-scaling realization visits each retained coefficient
once, preserving the complete list order and length. -/
@[expose] public def scale (factor : Int) (polynomial : CoefficientList) : CoefficientList :=
  polynomial.map fun coefficient => factor * coefficient

end TorusInvariants

namespace TorusInvariants

/-- Multiply retained integer coefficient lists by finite convolution.

Each head coefficient scales the right list; the recursively computed tail product is shifted by one degree before
addition. -/
@[expose] public def mul : CoefficientList → CoefficientList → CoefficientList
  | [], _ => []
  | left :: leftTail, right =>
      TorusInvariants.add (TorusInvariants.scale left right) (0 ::
        Purelib.Polynomial.Ascending.Integer.Basic.TorusInvariants.mul leftTail right)

end TorusInvariants

end Purelib.Polynomial.Ascending.Integer.Basic
