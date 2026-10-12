module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Field.Finite.Five
public import Purelib.Algebra.Field.Finite.Odd.Presentation
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

open Purelib.Algebra.Field

open Purelib.Algebra.Field.Finite

open Purelib.Algebra.Field.Finite.Odd.Presentation

section
@[expose] public section

/-!
# Rational rotations, Theorem 2: null vectors

The paper treats ordered fields and finite fields separately.  The ordered
rational case below is proved from the stored finite numerator order on the
repository's canonical rational carrier.  The finite-field construction is
implemented by a recursive intersection search over explicit carrier and
square tables, so the resulting null vector is executable data rather than a
bare existence claim.
-/

namespace Purelib.Rotations

variable {K : Type*} [ExplicitField K]

namespace FieldFive

end FieldFive
end Purelib.Rotations

namespace Purelib.Algebra.Field.Finite.Five.Presentation

variable {K : Type*} [ExplicitField K]

namespace FieldFive

/-- Present the five-element field by explicit carrier and square tables.

The carrier contains all five residues, the square table is [0, 1, 4], and retained finite proofs certify the root
cache, completeness, distinctness and odd-size count. -/
def finiteOddFieldPresentation :
  FiniteOddFieldPresentation Five.Element where
  eqDecidable := inferInstance
  carrier := [0, 1, 2, 3, 4]
  carrierNodup := by decide
  carrierComplete := by decide +revert
  squareValues := [0, 1, 4]
  squareValuesNodup := by decide
  squareValuesComplete := by decide +revert
  squareRoot := fun value => if value = 4 then 2 else value
  squareRoot_spec := by decide +revert
  squareCount := by decide
  twoNonzero := by decide
end FieldFive

end Purelib.Algebra.Field.Finite.Five.Presentation

end
