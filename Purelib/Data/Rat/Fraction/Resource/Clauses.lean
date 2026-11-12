module
import Purelib.Data.Nat.Divisibility

public import Purelib.Data.Nat.GCD.Resource.Clauses
import Purelib.Data.Nat.GCD.Scalar
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Basic
public import Purelib.Data.Rat.Fraction.Resource.Components
public import Purelib.Data.Rat.SignedFraction.Arithmetic

import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

section
section
@[expose] public section

/-!
# Normalized rational arithmetic

This module retains the reduction-aware size and step accounting API.  The
underlying semantic type is now itself the canonical reduced record, so
`value` and `ofRational` no longer erase to or select from a quotient.

Addition first removes the gcd shared by the two denominators.  Multiplication
cross-cancels numerator/denominator pairs before forming either product.
Inversion swaps the already coprime components.  Multiplication is reduced
by cross-cancellation alone; addition's remaining gcd uses only the shared
denominator factor.  Reducedness certificates are retained as erased proofs,
not reconstructed by a redundant final gcd.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Clauses

open Purelib.Data.Nat in
open Purelib.Data.Rat in
/-- Count both GCD clause traversals used by reduced-fraction addition.

The first traversal compares the original denominators. The second compares the absolute raw sum numerator with their
retained common divisor, matching the original two-stage reduction arithmetic. -/
def addGcdClauses (left right : Basic.ReducedFraction) : Nat
  :=
  GCD.Resource.Clauses.gcdClauses left.den right.den +
    GCD.Resource.Clauses.gcdClauses (SignedFraction.Arithmetic.addRaw left right).num.natAbs
      (Arithmetic.additionCommon left right)
end Purelib.Data.Rat.Fraction.Resource.Clauses

end

end

section
section
@[expose] public section

/-!
# Normalized rational arithmetic

This module retains the reduction-aware size and step accounting API.  The
underlying semantic type is now itself the canonical reduced record, so
`value` and `ofRational` no longer erase to or select from a quotient.

Addition first removes the gcd shared by the two denominators.  Multiplication
cross-cancels numerator/denominator pairs before forming either product.
Inversion swaps the already coprime components.  Multiplication is reduced
by cross-cancellation alone; addition's remaining gcd uses only the shared
denominator factor.  Reducedness certificates are retained as erased proofs,
not reconstructed by a redundant final gcd.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Clauses

open Purelib.Data

/-- The two retained addition GCD scans use at most the displayed denominator sum plus two clauses.

The first scan bounds the common denominator factor by the original positive
left denominator. The second scan retains that common factor as its bound. -/
theorem addGcdClauses_le (left right : Basic.ReducedFraction)
  :
    addGcdClauses left right ≤ left.den + right.den + 2 := by
  have commonLe : Arithmetic.additionCommon left right ≤ left.den :=
    Nat.Divisibility.le_of_dvd left.den_pos (Nat.GCD.Scalar.gcd_dvd left.den right.den).1
  have final := (Nat.GCD.Resource.Clauses.gcdClauses_le (SignedFraction.Arithmetic.addRaw left right).num.natAbs
    (Arithmetic.additionCommon left right)).trans (Nat.add_le_add_right commonLe 1)
  have total := Nat.add_le_add (Nat.GCD.Resource.Clauses.gcdClauses_le left.den right.den) final
  simpa only [addGcdClauses, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using total
end Purelib.Data.Rat.Fraction.Resource.Clauses

end

end

section
section
@[expose] public section

/-!
# Normalized rational arithmetic

This module retains the reduction-aware size and step accounting API.  The
underlying semantic type is now itself the canonical reduced record, so
`value` and `ofRational` no longer erase to or select from a quotient.

Addition first removes the gcd shared by the two denominators.  Multiplication
cross-cancels numerator/denominator pairs before forming either product.
Inversion swaps the already coprime components.  Multiplication is reduced
by cross-cancellation alone; addition's remaining gcd uses only the shared
denominator factor.  Reducedness certificates are retained as erased proofs,
not reconstructed by a redundant final gcd.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Clauses

/-- Compute the addition step envelope as the sum of the input magnitude bounds plus ten. -/
def addStepEnvelope (left right : Nat) : Nat :=
  left + right + 10
end Purelib.Data.Rat.Fraction.Resource.Clauses

end

end

section
section
@[expose] public section

/-!
# Normalized rational arithmetic

This module retains the reduction-aware size and step accounting API.  The
underlying semantic type is now itself the canonical reduced record, so
`value` and `ofRational` no longer erase to or select from a quotient.

Addition first removes the gcd shared by the two denominators.  Multiplication
cross-cancels numerator/denominator pairs before forming either product.
Inversion swaps the already coprime components.  Multiplication is reduced
by cross-cancellation alone; addition's remaining gcd uses only the shared
denominator factor.  Reducedness certificates are retained as erased proofs,
not reconstructed by a redundant final gcd.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Clauses

open Purelib.Data.Rat in
/-- The addition step envelope is monotone in its supplied component magnitude bounds. -/
theorem addStepEnvelope_mono
    {left right leftBound rightBound : Nat}
    (leftLe : left ≤ leftBound) (rightLe : right ≤ rightBound) :
    addStepEnvelope left right ≤ addStepEnvelope leftBound
      rightBound :=
  Nat.add_le_add_right (Nat.add_le_add leftLe rightLe) 10
end Purelib.Data.Rat.Fraction.Resource.Clauses

end

end

section
section
@[expose] public section

/-!
# Normalized rational arithmetic

This module retains the reduction-aware size and step accounting API.  The
underlying semantic type is now itself the canonical reduced record, so
`value` and `ofRational` no longer erase to or select from a quotient.

Addition first removes the gcd shared by the two denominators.  Multiplication
cross-cancels numerator/denominator pairs before forming either product.
Inversion swaps the already coprime components.  Multiplication is reduced
by cross-cancellation alone; addition's remaining gcd uses only the shared
denominator factor.  Reducedness certificates are retained as erased proofs,
not reconstructed by a redundant final gcd.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Clauses

/-! ## Arithmetic-step envelopes -/

open Purelib.Data.Rat in
/-- Count the addition GCD clauses together with eight scalar operation steps. -/
def addSteps (left right : Basic.ReducedFraction) : Nat :=
  addGcdClauses left right + 8
end Purelib.Data.Rat.Fraction.Resource.Clauses

end

end

section
section
@[expose] public section

/-!
# Normalized rational arithmetic

This module retains the reduction-aware size and step accounting API.  The
underlying semantic type is now itself the canonical reduced record, so
`value` and `ofRational` no longer erase to or select from a quotient.

Addition first removes the gcd shared by the two denominators.  Multiplication
cross-cancels numerator/denominator pairs before forming either product.
Inversion swaps the already coprime components.  Multiplication is reduced
by cross-cancellation alone; addition's remaining gcd uses only the shared
denominator factor.  Reducedness certificates are retained as erased proofs,
not reconstructed by a redundant final gcd.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Clauses

open Purelib.Data.Rat in
/-- The counted addition steps are bounded by the envelope of the retained reduced-fraction component magnitudes. -/
theorem addSteps_le_envelope (left right :
  Basic.ReducedFraction) :
    addSteps left right ≤
      addStepEnvelope (Components.NormalizedFraction.componentMagnitude
        left)
        (Components.NormalizedFraction.componentMagnitude right) := by
  have components := Nat.add_le_add (Components.NormalizedFraction.denominator_le_componentMagnitude
    left)
    (Components.NormalizedFraction.denominator_le_componentMagnitude right)
  have total := Nat.add_le_add_right
    ((addGcdClauses_le left right).trans (Nat.add_le_add_right components 2)) 8
  simpa only [addSteps, addStepEnvelope, Nat.add_assoc] using total
end Purelib.Data.Rat.Fraction.Resource.Clauses

end

end

section
section
@[expose] public section

/-!
# Normalized rational arithmetic

This module retains the reduction-aware size and step accounting API.  The
underlying semantic type is now itself the canonical reduced record, so
`value` and `ofRational` no longer erase to or select from a quotient.

Addition first removes the gcd shared by the two denominators.  Multiplication
cross-cancels numerator/denominator pairs before forming either product.
Inversion swaps the already coprime components.  Multiplication is reduced
by cross-cancellation alone; addition's remaining gcd uses only the shared
denominator factor.  Reducedness certificates are retained as erased proofs,
not reconstructed by a redundant final gcd.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Clauses

/-- Return the constant two-step envelope for reduced-fraction inversion. -/
def invStepEnvelope (_source : Nat) : Nat := 2
end Purelib.Data.Rat.Fraction.Resource.Clauses

end

end

section
section
@[expose] public section

/-!
# Normalized rational arithmetic

This module retains the reduction-aware size and step accounting API.  The
underlying semantic type is now itself the canonical reduced record, so
`value` and `ofRational` no longer erase to or select from a quotient.

Addition first removes the gcd shared by the two denominators.  Multiplication
cross-cancels numerator/denominator pairs before forming either product.
Inversion swaps the already coprime components.  Multiplication is reduced
by cross-cancellation alone; addition's remaining gcd uses only the shared
denominator factor.  Reducedness certificates are retained as erased proofs,
not reconstructed by a redundant final gcd.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Clauses

open Purelib.Data.Rat in
/-- The inversion step envelope is monotone in its supplied component magnitude bounds. -/
theorem invStepEnvelope_mono {source bound : Nat} (_sourceLe : source
  ≤ bound) :
    invStepEnvelope source ≤ invStepEnvelope bound :=
  Nat.le_refl 2
end Purelib.Data.Rat.Fraction.Resource.Clauses

end

end

section
section
@[expose] public section

/-!
# Normalized rational arithmetic

This module retains the reduction-aware size and step accounting API.  The
underlying semantic type is now itself the canonical reduced record, so
`value` and `ofRational` no longer erase to or select from a quotient.

Addition first removes the gcd shared by the two denominators.  Multiplication
cross-cancels numerator/denominator pairs before forming either product.
Inversion swaps the already coprime components.  Multiplication is reduced
by cross-cancellation alone; addition's remaining gcd uses only the shared
denominator factor.  Reducedness certificates are retained as erased proofs,
not reconstructed by a redundant final gcd.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Clauses

open Purelib.Data.Rat in
/-- Count two scalar steps for inversion of a reduced fraction. -/
def invSteps (_source : Basic.ReducedFraction) : Nat := 2
end Purelib.Data.Rat.Fraction.Resource.Clauses

end

end

section
section
@[expose] public section

/-!
# Normalized rational arithmetic

This module retains the reduction-aware size and step accounting API.  The
underlying semantic type is now itself the canonical reduced record, so
`value` and `ofRational` no longer erase to or select from a quotient.

Addition first removes the gcd shared by the two denominators.  Multiplication
cross-cancels numerator/denominator pairs before forming either product.
Inversion swaps the already coprime components.  Multiplication is reduced
by cross-cancellation alone; addition's remaining gcd uses only the shared
denominator factor.  Reducedness certificates are retained as erased proofs,
not reconstructed by a redundant final gcd.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Clauses

open Purelib.Data.Rat in
/-- The counted inversion steps are bounded by the envelope of the retained reduced-fraction component magnitudes. -/
theorem invSteps_le_envelope (source : Basic.ReducedFraction)
  :
    invSteps source ≤ invStepEnvelope
      (Components.NormalizedFraction.componentMagnitude source) :=
  Nat.le_refl 2
end Purelib.Data.Rat.Fraction.Resource.Clauses

end

end

section
section
@[expose] public section

/-!
# Normalized rational arithmetic

This module retains the reduction-aware size and step accounting API.  The
underlying semantic type is now itself the canonical reduced record, so
`value` and `ofRational` no longer erase to or select from a quotient.

Addition first removes the gcd shared by the two denominators.  Multiplication
cross-cancels numerator/denominator pairs before forming either product.
Inversion swaps the already coprime components.  Multiplication is reduced
by cross-cancellation alone; addition's remaining gcd uses only the shared
denominator factor.  Reducedness certificates are retained as erased proofs,
not reconstructed by a redundant final gcd.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Clauses

open Purelib.Data.Nat in
open Purelib.Data.Rat in
/-- Count the two cross-cancellation GCD clause traversals used by reduced-fraction multiplication.

Count cancellation of the left numerator against the right denominator and of the right numerator against the left
denominator. Both counts use the original retained fraction components. -/
def mulGcdClauses (left right : Basic.ReducedFraction) : Nat
  :=
  GCD.Resource.Clauses.gcdClauses left.num.natAbs right.den +
    GCD.Resource.Clauses.gcdClauses right.num.natAbs left.den
end Purelib.Data.Rat.Fraction.Resource.Clauses

end

end

section
section
@[expose] public section

/-!
# Normalized rational arithmetic

This module retains the reduction-aware size and step accounting API.  The
underlying semantic type is now itself the canonical reduced record, so
`value` and `ofRational` no longer erase to or select from a quotient.

Addition first removes the gcd shared by the two denominators.  Multiplication
cross-cancels numerator/denominator pairs before forming either product.
Inversion swaps the already coprime components.  Multiplication is reduced
by cross-cancellation alone; addition's remaining gcd uses only the shared
denominator factor.  Reducedness certificates are retained as erased proofs,
not reconstructed by a redundant final gcd.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Clauses

open Purelib.Data.Nat in
open Purelib.Data.Rat in
/-- The multiplication GCD clause count is at most the sum of the two denominators plus two. -/
theorem mulGcdClauses_le (left right : Basic.ReducedFraction)
  :
    mulGcdClauses left right ≤ left.den + right.den + 2 := by
  have total := Nat.add_le_add (GCD.Resource.Clauses.gcdClauses_le left.num.natAbs right.den)
    (GCD.Resource.Clauses.gcdClauses_le right.num.natAbs left.den)
  simpa only [mulGcdClauses, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using total
end Purelib.Data.Rat.Fraction.Resource.Clauses

end

end

section
section
@[expose] public section

/-!
# Normalized rational arithmetic

This module retains the reduction-aware size and step accounting API.  The
underlying semantic type is now itself the canonical reduced record, so
`value` and `ofRational` no longer erase to or select from a quotient.

Addition first removes the gcd shared by the two denominators.  Multiplication
cross-cancels numerator/denominator pairs before forming either product.
Inversion swaps the already coprime components.  Multiplication is reduced
by cross-cancellation alone; addition's remaining gcd uses only the shared
denominator factor.  Reducedness certificates are retained as erased proofs,
not reconstructed by a redundant final gcd.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Clauses

/-- Compute the multiplication step envelope as the sum of the input magnitude bounds plus ten. -/
def mulStepEnvelope (left right : Nat) : Nat :=
  left + right + 10
end Purelib.Data.Rat.Fraction.Resource.Clauses

end

end

section
section
@[expose] public section

/-!
# Normalized rational arithmetic

This module retains the reduction-aware size and step accounting API.  The
underlying semantic type is now itself the canonical reduced record, so
`value` and `ofRational` no longer erase to or select from a quotient.

Addition first removes the gcd shared by the two denominators.  Multiplication
cross-cancels numerator/denominator pairs before forming either product.
Inversion swaps the already coprime components.  Multiplication is reduced
by cross-cancellation alone; addition's remaining gcd uses only the shared
denominator factor.  Reducedness certificates are retained as erased proofs,
not reconstructed by a redundant final gcd.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Clauses

open Purelib.Data.Rat in
/-- Add the inverse and multiplication envelopes for rational division. -/
def divStepEnvelope (left right : Nat) : Nat :=
  invStepEnvelope right + mulStepEnvelope left right
end Purelib.Data.Rat.Fraction.Resource.Clauses

end

end

section
section
@[expose] public section

/-!
# Normalized rational arithmetic

This module retains the reduction-aware size and step accounting API.  The
underlying semantic type is now itself the canonical reduced record, so
`value` and `ofRational` no longer erase to or select from a quotient.

Addition first removes the gcd shared by the two denominators.  Multiplication
cross-cancels numerator/denominator pairs before forming either product.
Inversion swaps the already coprime components.  Multiplication is reduced
by cross-cancellation alone; addition's remaining gcd uses only the shared
denominator factor.  Reducedness certificates are retained as erased proofs,
not reconstructed by a redundant final gcd.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Clauses

open Purelib.Data.Rat in
/-- The multiplication step envelope is monotone in its supplied component magnitude bounds. -/
theorem mulStepEnvelope_mono
    {left right leftBound rightBound : Nat}
    (leftLe : left ≤ leftBound) (rightLe : right ≤ rightBound) :
    mulStepEnvelope left right ≤ mulStepEnvelope leftBound
      rightBound :=
  Nat.add_le_add_right (Nat.add_le_add leftLe rightLe) 10
end Purelib.Data.Rat.Fraction.Resource.Clauses

end

end

section
section
@[expose] public section

/-!
# Normalized rational arithmetic

This module retains the reduction-aware size and step accounting API.  The
underlying semantic type is now itself the canonical reduced record, so
`value` and `ofRational` no longer erase to or select from a quotient.

Addition first removes the gcd shared by the two denominators.  Multiplication
cross-cancels numerator/denominator pairs before forming either product.
Inversion swaps the already coprime components.  Multiplication is reduced
by cross-cancellation alone; addition's remaining gcd uses only the shared
denominator factor.  Reducedness certificates are retained as erased proofs,
not reconstructed by a redundant final gcd.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Clauses

open Purelib.Data.Rat in
/-- The division step envelope is monotone in its supplied component magnitude bounds. -/
theorem divStepEnvelope_mono
    {left right leftBound rightBound : Nat}
    (leftLe : left ≤ leftBound) (rightLe : right ≤ rightBound) :
    divStepEnvelope left right ≤ divStepEnvelope leftBound
      rightBound := by
  unfold divStepEnvelope
  exact Nat.add_le_add (invStepEnvelope_mono rightLe)
    (mulStepEnvelope_mono leftLe rightLe)
end Purelib.Data.Rat.Fraction.Resource.Clauses

end

end

section
section
@[expose] public section

/-!
# Normalized rational arithmetic

This module retains the reduction-aware size and step accounting API.  The
underlying semantic type is now itself the canonical reduced record, so
`value` and `ofRational` no longer erase to or select from a quotient.

Addition first removes the gcd shared by the two denominators.  Multiplication
cross-cancels numerator/denominator pairs before forming either product.
Inversion swaps the already coprime components.  Multiplication is reduced
by cross-cancellation alone; addition's remaining gcd uses only the shared
denominator factor.  Reducedness certificates are retained as erased proofs,
not reconstructed by a redundant final gcd.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Clauses

open Purelib.Data.Rat in
/-- Count the multiplication cross-cancellation GCD clauses together with eight scalar steps. -/
def mulSteps (left right : Basic.ReducedFraction) : Nat :=
  mulGcdClauses left right + 8
end Purelib.Data.Rat.Fraction.Resource.Clauses

end

end

section
section
@[expose] public section

/-!
# Normalized rational arithmetic

This module retains the reduction-aware size and step accounting API.  The
underlying semantic type is now itself the canonical reduced record, so
`value` and `ofRational` no longer erase to or select from a quotient.

Addition first removes the gcd shared by the two denominators.  Multiplication
cross-cancels numerator/denominator pairs before forming either product.
Inversion swaps the already coprime components.  Multiplication is reduced
by cross-cancellation alone; addition's remaining gcd uses only the shared
denominator factor.  Reducedness certificates are retained as erased proofs,
not reconstructed by a redundant final gcd.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Clauses

open Purelib.Data.Rat in
/-- Count inversion of the right input followed by multiplication by that exact inverse.

The multiplication count receives the exact computed inverse of the right reduced fraction. Its envelope proof
transports the inverse component bound without replacing the counted inputs. -/
def divSteps (left right : Basic.ReducedFraction) : Nat :=
  invSteps right + mulSteps left (Arithmetic.inv right)
end Purelib.Data.Rat.Fraction.Resource.Clauses

end

end

section
section
@[expose] public section

/-!
# Normalized rational arithmetic

This module retains the reduction-aware size and step accounting API.  The
underlying semantic type is now itself the canonical reduced record, so
`value` and `ofRational` no longer erase to or select from a quotient.

Addition first removes the gcd shared by the two denominators.  Multiplication
cross-cancels numerator/denominator pairs before forming either product.
Inversion swaps the already coprime components.  Multiplication is reduced
by cross-cancellation alone; addition's remaining gcd uses only the shared
denominator factor.  Reducedness certificates are retained as erased proofs,
not reconstructed by a redundant final gcd.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Clauses

open Purelib.Data.Rat in
/-- The counted multiplication steps are bounded by the envelope of the retained reduced-fraction component magnitudes.
-/
theorem mulSteps_le_envelope (left right :
  Basic.ReducedFraction) :
    mulSteps left right ≤
      mulStepEnvelope (Components.NormalizedFraction.componentMagnitude
        left)
        (Components.NormalizedFraction.componentMagnitude right) := by
  have components := Nat.add_le_add (Components.NormalizedFraction.denominator_le_componentMagnitude
    left)
    (Components.NormalizedFraction.denominator_le_componentMagnitude right)
  have total := Nat.add_le_add_right
    ((mulGcdClauses_le left right).trans (Nat.add_le_add_right components 2)) 8
  simpa only [mulSteps, mulStepEnvelope, Nat.add_assoc] using total
end Purelib.Data.Rat.Fraction.Resource.Clauses

end

end

section
section
@[expose] public section

/-!
# Normalized rational arithmetic

This module retains the reduction-aware size and step accounting API.  The
underlying semantic type is now itself the canonical reduced record, so
`value` and `ofRational` no longer erase to or select from a quotient.

Addition first removes the gcd shared by the two denominators.  Multiplication
cross-cancels numerator/denominator pairs before forming either product.
Inversion swaps the already coprime components.  Multiplication is reduced
by cross-cancellation alone; addition's remaining gcd uses only the shared
denominator factor.  Reducedness certificates are retained as erased proofs,
not reconstructed by a redundant final gcd.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Clauses

open Purelib.Data.Rat in
/-- The counted division steps are bounded by the envelope of the retained reduced-fraction component magnitudes. -/
theorem divSteps_le_envelope (left right :
  Basic.ReducedFraction) :
    divSteps left right ≤
      divStepEnvelope (Components.NormalizedFraction.componentMagnitude
        left)
        (Components.NormalizedFraction.componentMagnitude right) := by
  have invBound := invSteps_le_envelope right
  have mulBound := mulSteps_le_envelope left (Arithmetic.inv right)
  have mulEnvelopeBound := mulStepEnvelope_mono
    (left := Components.NormalizedFraction.componentMagnitude left)
    (right := Components.NormalizedFraction.componentMagnitude (Arithmetic.inv right))
    (leftBound := Components.NormalizedFraction.componentMagnitude left)
    (rightBound := Components.NormalizedFraction.componentMagnitude right)
    (le_refl _) (Components.NormalizedFraction.componentMagnitude_inv_le right)
  unfold divSteps divStepEnvelope
  exact Nat.add_le_add invBound (mulBound.trans mulEnvelopeBound)
end Purelib.Data.Rat.Fraction.Resource.Clauses

end

end

section
section
@[expose] public section

/-!
# Normalized rational arithmetic

This module retains the reduction-aware size and step accounting API.  The
underlying semantic type is now itself the canonical reduced record, so
`value` and `ofRational` no longer erase to or select from a quotient.

Addition first removes the gcd shared by the two denominators.  Multiplication
cross-cancels numerator/denominator pairs before forming either product.
Inversion swaps the already coprime components.  Multiplication is reduced
by cross-cancellation alone; addition's remaining gcd uses only the shared
denominator factor.  Reducedness certificates are retained as erased proofs,
not reconstructed by a redundant final gcd.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Clauses

/-- Return the constant one-step envelope for reduced-fraction negation. -/
def negStepEnvelope (_source : Nat) : Nat := 1
end Purelib.Data.Rat.Fraction.Resource.Clauses

end

end

section
section
@[expose] public section

/-!
# Normalized rational arithmetic

This module retains the reduction-aware size and step accounting API.  The
underlying semantic type is now itself the canonical reduced record, so
`value` and `ofRational` no longer erase to or select from a quotient.

Addition first removes the gcd shared by the two denominators.  Multiplication
cross-cancels numerator/denominator pairs before forming either product.
Inversion swaps the already coprime components.  Multiplication is reduced
by cross-cancellation alone; addition's remaining gcd uses only the shared
denominator factor.  Reducedness certificates are retained as erased proofs,
not reconstructed by a redundant final gcd.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Clauses

open Purelib.Data.Rat in
/-- The negation step envelope is monotone in its supplied component magnitude bounds. -/
theorem negStepEnvelope_mono {source bound : Nat} (_sourceLe : source
  ≤ bound) :
    negStepEnvelope source ≤ negStepEnvelope bound :=
  Nat.le_refl 1
end Purelib.Data.Rat.Fraction.Resource.Clauses

end

end

section
section
@[expose] public section

/-!
# Normalized rational arithmetic

This module retains the reduction-aware size and step accounting API.  The
underlying semantic type is now itself the canonical reduced record, so
`value` and `ofRational` no longer erase to or select from a quotient.

Addition first removes the gcd shared by the two denominators.  Multiplication
cross-cancels numerator/denominator pairs before forming either product.
Inversion swaps the already coprime components.  Multiplication is reduced
by cross-cancellation alone; addition's remaining gcd uses only the shared
denominator factor.  Reducedness certificates are retained as erased proofs,
not reconstructed by a redundant final gcd.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Clauses

open Purelib.Data.Rat in
/-- Count one scalar step for negation of a reduced fraction. -/
def negSteps (_source : Basic.ReducedFraction) : Nat := 1
end Purelib.Data.Rat.Fraction.Resource.Clauses

end

end

section
section
@[expose] public section

/-!
# Normalized rational arithmetic

This module retains the reduction-aware size and step accounting API.  The
underlying semantic type is now itself the canonical reduced record, so
`value` and `ofRational` no longer erase to or select from a quotient.

Addition first removes the gcd shared by the two denominators.  Multiplication
cross-cancels numerator/denominator pairs before forming either product.
Inversion swaps the already coprime components.  Multiplication is reduced
by cross-cancellation alone; addition's remaining gcd uses only the shared
denominator factor.  Reducedness certificates are retained as erased proofs,
not reconstructed by a redundant final gcd.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Clauses

open Purelib.Data.Rat in
/-- The counted negation steps are bounded by the envelope of the retained reduced-fraction component magnitudes. -/
theorem negSteps_le_envelope (source : Basic.ReducedFraction)
  :
    negSteps source ≤ negStepEnvelope
      (Components.NormalizedFraction.componentMagnitude source) :=
  Nat.le_refl 1
end Purelib.Data.Rat.Fraction.Resource.Clauses

end

end

section
section
@[expose] public section

/-!
# Normalized rational arithmetic

This module retains the reduction-aware size and step accounting API.  The
underlying semantic type is now itself the canonical reduced record, so
`value` and `ofRational` no longer erase to or select from a quotient.

Addition first removes the gcd shared by the two denominators.  Multiplication
cross-cancels numerator/denominator pairs before forming either product.
Inversion swaps the already coprime components.  Multiplication is reduced
by cross-cancellation alone; addition's remaining gcd uses only the shared
denominator factor.  Reducedness certificates are retained as erased proofs,
not reconstructed by a redundant final gcd.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Clauses

open Purelib.Data.Rat in
/-- Add the negation and addition envelopes for rational subtraction. -/
def subStepEnvelope (left right : Nat) : Nat :=
  negStepEnvelope right + addStepEnvelope left right
end Purelib.Data.Rat.Fraction.Resource.Clauses

end

end

section
section
@[expose] public section

/-!
# Normalized rational arithmetic

This module retains the reduction-aware size and step accounting API.  The
underlying semantic type is now itself the canonical reduced record, so
`value` and `ofRational` no longer erase to or select from a quotient.

Addition first removes the gcd shared by the two denominators.  Multiplication
cross-cancels numerator/denominator pairs before forming either product.
Inversion swaps the already coprime components.  Multiplication is reduced
by cross-cancellation alone; addition's remaining gcd uses only the shared
denominator factor.  Reducedness certificates are retained as erased proofs,
not reconstructed by a redundant final gcd.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Clauses

open Purelib.Data.Rat in
/-- The subtraction step envelope is monotone in its supplied component magnitude bounds. -/
theorem subStepEnvelope_mono
    {left right leftBound rightBound : Nat}
    (leftLe : left ≤ leftBound) (rightLe : right ≤ rightBound) :
    subStepEnvelope left right ≤ subStepEnvelope leftBound
      rightBound := by
  unfold subStepEnvelope
  exact Nat.add_le_add (negStepEnvelope_mono rightLe)
    (addStepEnvelope_mono leftLe rightLe)
end Purelib.Data.Rat.Fraction.Resource.Clauses

end

end

section
section
@[expose] public section

/-!
# Normalized rational arithmetic

This module retains the reduction-aware size and step accounting API.  The
underlying semantic type is now itself the canonical reduced record, so
`value` and `ofRational` no longer erase to or select from a quotient.

Addition first removes the gcd shared by the two denominators.  Multiplication
cross-cancels numerator/denominator pairs before forming either product.
Inversion swaps the already coprime components.  Multiplication is reduced
by cross-cancellation alone; addition's remaining gcd uses only the shared
denominator factor.  Reducedness certificates are retained as erased proofs,
not reconstructed by a redundant final gcd.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Clauses

open Purelib.Data.Rat in
/-- Count negation of the right input followed by addition of that exact negation.

The addition count receives the exact computed negation of the right reduced fraction. Its envelope proof retains the
corresponding component-magnitude bound. -/
def subSteps (left right : Basic.ReducedFraction) : Nat :=
  negSteps right + addSteps left (Arithmetic.neg right)
end Purelib.Data.Rat.Fraction.Resource.Clauses

end

end

section
section
@[expose] public section

/-!
# Normalized rational arithmetic

This module retains the reduction-aware size and step accounting API.  The
underlying semantic type is now itself the canonical reduced record, so
`value` and `ofRational` no longer erase to or select from a quotient.

Addition first removes the gcd shared by the two denominators.  Multiplication
cross-cancels numerator/denominator pairs before forming either product.
Inversion swaps the already coprime components.  Multiplication is reduced
by cross-cancellation alone; addition's remaining gcd uses only the shared
denominator factor.  Reducedness certificates are retained as erased proofs,
not reconstructed by a redundant final gcd.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Clauses

open Purelib.Data.Rat in
/-- The counted subtraction steps are bounded by the envelope of the retained reduced-fraction component magnitudes. -/
theorem subSteps_le_envelope (left right :
  Basic.ReducedFraction) :
    subSteps left right ≤
      subStepEnvelope (Components.NormalizedFraction.componentMagnitude
        left)
        (Components.NormalizedFraction.componentMagnitude right) := by
  have negBound := negSteps_le_envelope right
  have addBound := addSteps_le_envelope left (Arithmetic.neg right)
  have addEnvelopeBound := addStepEnvelope_mono
    (left := Components.NormalizedFraction.componentMagnitude left)
    (right := Components.NormalizedFraction.componentMagnitude (Arithmetic.neg right))
    (leftBound := Components.NormalizedFraction.componentMagnitude left)
    (rightBound := Components.NormalizedFraction.componentMagnitude right)
    (le_refl _) (Components.componentMagnitude_neg_le right)
  unfold subSteps subStepEnvelope
  exact Nat.add_le_add negBound (addBound.trans addEnvelopeBound)
end Purelib.Data.Rat.Fraction.Resource.Clauses

end

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Clauses

open Purelib.Data.Rat in
/-- Count the addition GCD clauses on the actual reduced representatives of the canonical rational inputs. -/
def normalizedAddGcdClauses (left right : Rational) : Nat :=
  addGcdClauses
    (Basic.ofRational left)
    (Basic.ofRational right)
end Purelib.Data.Rat.Fraction.Resource.Clauses

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Clauses

open Purelib.Data.Rat in
/-- Compute the addition step budget from the actual reduced representatives of the canonical rational inputs. -/
def normalizedAddStepBudget (left right : Rational) : Nat :=
  addStepEnvelope
    (Components.NormalizedFraction.componentMagnitude
      (Basic.ofRational left))
    (Components.NormalizedFraction.componentMagnitude
      (Basic.ofRational right))
end Purelib.Data.Rat.Fraction.Resource.Clauses

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Clauses

open Purelib.Data.Rat in
/-- The addition step count on the original rational representatives is at most the computed budget. -/
theorem normalizedAdd_steps_le_budget (left right : Rational)
  :
    addSteps
        (Basic.ofRational left)
        (Basic.ofRational right) ≤
      normalizedAddStepBudget left right :=
  addSteps_le_envelope _ _
end Purelib.Data.Rat.Fraction.Resource.Clauses

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Clauses

open Purelib.Data.Rat in
/-- Compute the division step budget from the actual reduced representatives of the canonical rational inputs. -/
def normalizedDivStepBudget (left right : Rational) : Nat :=
  divStepEnvelope
    (Components.NormalizedFraction.componentMagnitude
      (Basic.ofRational left))
    (Components.NormalizedFraction.componentMagnitude
      (Basic.ofRational right))
end Purelib.Data.Rat.Fraction.Resource.Clauses

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Clauses

open Purelib.Data.Rat in
/-- The division step count on the original rational representatives is at most the computed budget. -/
theorem normalizedDiv_steps_le_budget (left right : Rational)
  :
    divSteps
        (Basic.ofRational left)
        (Basic.ofRational right) ≤
      normalizedDivStepBudget left right :=
  divSteps_le_envelope _ _
end Purelib.Data.Rat.Fraction.Resource.Clauses

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Clauses

open Purelib.Data.Rat in
/-- Compute the inversion step budget from the actual reduced representatives of the canonical rational inputs. -/
def normalizedInvStepBudget (source : Rational) : Nat :=
  invStepEnvelope
    (Components.NormalizedFraction.componentMagnitude
      (Basic.ofRational source))
end Purelib.Data.Rat.Fraction.Resource.Clauses

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Clauses

open Purelib.Data.Rat in
/-- The inversion step count on the original rational representatives is at most the computed budget. -/
theorem normalizedInv_steps_le_budget (source : Rational) :
    invSteps
        (Basic.ofRational source) ≤
      normalizedInvStepBudget source :=
  invSteps_le_envelope _
end Purelib.Data.Rat.Fraction.Resource.Clauses

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Clauses

open Purelib.Data.Rat in
/-- Count the multiplication GCD clauses on the actual reduced representatives of the canonical rational inputs. -/
def normalizedMulGcdClauses (left right : Rational) : Nat :=
  mulGcdClauses
    (Basic.ofRational left)
    (Basic.ofRational right)
end Purelib.Data.Rat.Fraction.Resource.Clauses

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Clauses

open Purelib.Data.Rat in
/-- Compute the multiplication step budget from the actual reduced representatives of the canonical rational inputs. -/
def normalizedMulStepBudget (left right : Rational) : Nat :=
  mulStepEnvelope
    (Components.NormalizedFraction.componentMagnitude
      (Basic.ofRational left))
    (Components.NormalizedFraction.componentMagnitude
      (Basic.ofRational right))
end Purelib.Data.Rat.Fraction.Resource.Clauses

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Clauses

open Purelib.Data.Rat in
/-- The multiplication step count on the original rational representatives is at most the computed budget. -/
theorem normalizedMul_steps_le_budget (left right : Rational)
  :
    mulSteps
        (Basic.ofRational left)
        (Basic.ofRational right) ≤
      normalizedMulStepBudget left right :=
  mulSteps_le_envelope _ _
end Purelib.Data.Rat.Fraction.Resource.Clauses

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Clauses

open Purelib.Data.Rat in
/-- Compute the negation step budget from the actual reduced representatives of the canonical rational inputs. -/
def normalizedNegStepBudget (source : Rational) : Nat :=
  negStepEnvelope
    (Components.NormalizedFraction.componentMagnitude
      (Basic.ofRational source))
end Purelib.Data.Rat.Fraction.Resource.Clauses

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Clauses

open Purelib.Data.Rat in
/-- The negation step count on the original rational representatives is at most the computed budget. -/
theorem normalizedNeg_steps_le_budget (source : Rational) :
    negSteps
        (Basic.ofRational source) ≤
      normalizedNegStepBudget source :=
  negSteps_le_envelope _
end Purelib.Data.Rat.Fraction.Resource.Clauses

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Clauses

open Purelib.Data.Rat in
/-- Compute the subtraction step budget from the actual reduced representatives of the canonical rational inputs. -/
def normalizedSubStepBudget (left right : Rational) : Nat :=
  subStepEnvelope
    (Components.NormalizedFraction.componentMagnitude
      (Basic.ofRational left))
    (Components.NormalizedFraction.componentMagnitude
      (Basic.ofRational right))
end Purelib.Data.Rat.Fraction.Resource.Clauses

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Clauses

open Purelib.Data.Rat in
/-- The subtraction step count on the original rational representatives is at most the computed budget. -/
theorem normalizedSub_steps_le_budget (left right : Rational)
  :
    subSteps
        (Basic.ofRational left)
        (Basic.ofRational right) ≤
      normalizedSubStepBudget left right :=
  subSteps_le_envelope _ _
end Purelib.Data.Rat.Fraction.Resource.Clauses

end
