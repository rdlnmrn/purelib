module

public import Purelib.Algebra.Ring.Basic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Checked finite inverse candidates

Every candidate product is retained once with its exact reading. A successful
scan retains its rejected prefix and untried suffix; exhaustion retains every
failed test in order and asserts no impossibility outside that supplied list.
-/

public section

namespace Purelib.Algebra.Ring.Unit

variable {K : Type*} [Mul K] [One K] {value : K} {candidates : List K}

set_option genInjectivity false in
/-- A rejected inverse candidate retains its original product and failed equality test. -/
structure Rejected (value : K) where
  /-- The actual scalar candidate tested against the original value. -/
  candidate : K
  /-- The retained product from that one test. -/
  product : K
  /-- The cached product is the original value times this same candidate. -/
  product_eq : product = value * candidate
  /-- The retained product failed the comparison with one. -/
  failure : product ≠ 1

constructive_injectivity Rejected

namespace Rejected

/-- The original coefficient and this rejected candidate do not multiply to one. -/
theorem not_unit (test : Rejected value) : value * test.candidate ≠ 1 :=
  fun unit => test.failure (test.product_eq.trans unit)

end Rejected

set_option genInjectivity false in
/-- A successful finite inverse scan retains its original scalar and ordered tests.

The rejected prefix followed by the accepted candidate and untried suffix is
exactly the original candidate list. The accepted product is cached separately
from its unit equality, so selecting the inverse does not multiply it again.
-/
structure Found (value : K) (candidates : List K) where
  /-- The retained original scalar on which these tests ran. -/
  input : K
  /-- The retained scalar is the original input of the scan. -/
  input_eq : input = value
  /-- The actual rejected candidate tests in their original order. -/
  tested : List (Rejected value)
  /-- The accepted original inverse candidate. -/
  inverse : K
  /-- The retained product of the accepted test. -/
  product : K
  /-- The cached accepted product reads the same original value and candidate. -/
  product_eq : product = value * inverse
  /-- The retained accepted product equals one. -/
  product_one : product = 1
  /-- The original suffix not tested after the accepted candidate. -/
  remaining : List K
  /-- The retained prefix, accepted candidate and suffix reconstruct the original list. -/
  order : candidates = tested.map Rejected.candidate ++ inverse :: remaining

constructive_injectivity Found

namespace Found

/-- The accepted retained candidate multiplies the original input to one. -/
theorem unit (found : Found value candidates) : value * found.inverse = 1 :=
  found.product_eq.symm.trans found.product_one

/-- Prepend one actual rejected test without replaying the successful suffix scan. -/
@[expose] def prepend (test : Rejected value) (found : Found value candidates) :
    Found value (test.candidate :: candidates) where
  input := found.input
  input_eq := found.input_eq
  tested := test :: found.tested
  inverse := found.inverse
  product := found.product
  product_eq := found.product_eq
  product_one := found.product_one
  remaining := found.remaining
  order := congrArg (fun suffix => test.candidate :: suffix) found.order

/-- Count the actual rejected products and final accepted product. -/
@[expose] def count (found : Found value candidates) : Nat := found.tested.length + 1

end Found

set_option genInjectivity false in
/-- An exhausted finite inverse scan retains every rejected product in order.

Every supplied candidate has been tested. Candidates outside this same finite
list remain unresolved, so exhaustion is not a nonunit certificate.
-/
structure Exhausted (value : K) (candidates : List K) where
  /-- The retained original scalar on which these tests ran. -/
  input : K
  /-- The retained scalar is the original scan input. -/
  input_eq : input = value
  /-- All actual failed candidate products, in their original order. -/
  tested : List (Rejected value)
  /-- The rejected candidate list is exactly the original finite input list. -/
  order : candidates = tested.map Rejected.candidate

constructive_injectivity Exhausted

namespace Exhausted

/-- Prepend one actual rejected test without replaying any retained tail test. -/
@[expose] def prepend (test : Rejected value) (exhausted : Exhausted value candidates) :
    Exhausted value (test.candidate :: candidates) where
  input := exhausted.input
  input_eq := exhausted.input_eq
  tested := test :: exhausted.tested
  order := congrArg (fun suffix => test.candidate :: suffix) exhausted.order

/-- Every candidate in a retained rejected list fails its same original unit equation. -/
private theorem failed_list (tested : List (Rejected value)) :
    ∀ candidate, candidate ∈ tested.map Rejected.candidate → value * candidate ≠ 1 := by
  induction tested with
  | nil => intro candidate member; cases member
  | cons first remaining previous =>
      intro candidate member
      cases member with
      | head => exact first.not_unit
      | tail _ member => exact previous candidate member

/-- Every supplied original candidate failed, with no assertion about other possible inverses. -/
theorem all_failed (exhausted : Exhausted value candidates) (candidate : K)
    (member : candidate ∈ candidates) : value * candidate ≠ 1 :=
  failed_list exhausted.tested candidate
    (Eq.mp (congrArg (fun values : List K => candidate ∈ values) exhausted.order) member)

/-- Count all actual retained rejected products. -/
@[expose] def count (exhausted : Exhausted value candidates) : Nat := exhausted.tested.length

end Exhausted

set_option genInjectivity false in
/-- A checked finite candidate scan returns a retained success or exact finite exhaustion. -/
inductive Result (value : K) (candidates : List K) where
  /-- Retain the accepted inverse, failed prefix and original untried suffix. -/
  | found (receipt : Found value candidates)
  /-- Retain all failed original tests without declaring the value a nonunit. -/
  | exhausted (receipt : Exhausted value candidates)

constructive_injectivity Result

variable [DecidableEq K]

/-- Test the original inverse candidates in order, caching each product exactly once.

Selection stops at the first product equal to one. Rejected products are
prepended to the retained tail receipt, preserving its actual work and suffix.
-/
@[expose] def scan (value : K) : (candidates : List K) → Result value candidates
  | [] => .exhausted ⟨value, rfl, [], rfl⟩
  | candidate :: remaining =>
      let product := value * candidate
      if unit : product = 1 then
        .found ⟨value, rfl, [], candidate, product, rfl, unit, remaining, rfl⟩
      else
        let rejected : Rejected value := ⟨candidate, product, rfl, unit⟩
        match scan value remaining with
        | .found receipt => .found (receipt.prepend rejected)
        | .exhausted receipt => .exhausted (receipt.prepend rejected)

end Purelib.Algebra.Ring.Unit

end
