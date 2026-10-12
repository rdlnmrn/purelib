module
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Rational.Constants.RawLinear
public import Purelib.Polynomial.Dense.Rational.Linear.Translated
public import Purelib.Polynomial.Dense.Rational.SignedRemainder.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic

/-!
# Translated monic signed-remainder chains

The original monic coordinate and two-slot rational constant supply exact finite signed-remainder chains. Nonzero
constant coefficients determine the same normalized negated final table.
-/

namespace Purelib.Polynomial.Dense.Rational.SignedRemainder.Linear.Translated

open Purelib.Data.Rat

open Purelib.Polynomial

/-- A nonzero constant followed by a translated monic variable emits that constant and recurses with its negated
normalization.

The nonzero constant and monic translated coordinate select the original degree-drop branch, retaining the emitted
constant and the normalized negated divisor for recursion. -/
private theorem signedChain_rawConstant_affineVariable_cons
    {center value : Fraction.Rational} (nonzero : value ≠ 0) :
    Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain (Dense.Rational.Constants.RawLinear.rawConstant
      value) (Dense.Rational.Linear.Translated.affineVariable center) =
      Dense.Rational.Constants.RawLinear.rawConstant value ::
        Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain (Dense.Rational.Linear.Translated.affineVariable
        center)
        (-((Dense.Rational.Constants.RawLinear.rawConstant value).normalize)) :=
  Dense.Rational.SignedRemainder.Basic.signedRemainderChain_eq_cons_of_degree_lt
    (Dense.Rational.Constants.RawLinear.rawConstant_isZero_false nonzero)
    (Dense.Rational.Linear.Translated.affineVariable_isZero_false center)
    (Dense.Rational.Linear.Translated.rawConstant_natDegree_lt_affineVariable nonzero)

/-- The signed remainder chain of a translated monic variable and nonzero constant is exactly their two-entry list.

The original monic coordinate and nonzero constant form the complete two-entry chain. The retained constant has one
normalized degree slot, so the algorithm stops after these two entries. -/
public theorem signedChain_affineVariable_rawConstant
    {center value : Fraction.Rational} (nonzero : value ≠ 0) :
    Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain (Dense.Rational.Linear.Translated.affineVariable
      center) (Dense.Rational.Constants.RawLinear.rawConstant value) =
      [Dense.Rational.Linear.Translated.affineVariable center, Dense.Rational.Constants.RawLinear.rawConstant value] :=
  Dense.Rational.SignedRemainder.Basic.signedRemainderChain_eq_pair_of_second_degreeCount_one
    (Dense.Rational.Constants.RawLinear.rawConstant_isZero_false nonzero)
    (Dense.Rational.Constants.RawLinear.rawConstant_degreeCount nonzero)

/-- The signed remainder chain of a nonzero constant and translated variable has three entries, ending in the negated
normalized constant.

The original nonzero constant is emitted before the monic coordinate. The final retained entry is the negated
normalization of that same constant table. -/
public theorem signedChain_rawConstant_affineVariable
    {center value : Fraction.Rational} (nonzero : value ≠ 0) :
    Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain (Dense.Rational.Constants.RawLinear.rawConstant
      value) (Dense.Rational.Linear.Translated.affineVariable center) =
      [Dense.Rational.Constants.RawLinear.rawConstant value, Dense.Rational.Linear.Translated.affineVariable center,
        -((Dense.Rational.Constants.RawLinear.rawConstant value).normalize)] := by
  rw [Dense.Rational.SignedRemainder.Linear.Translated.signedChain_rawConstant_affineVariable_cons nonzero]
  rw [Dense.Rational.SignedRemainder.Basic.signedRemainderChain_eq_pair_of_second_degreeCount_one
    (Dense.Rational.Constants.RawLinear.negNormalizedRawConstant_isZero_false nonzero)
    (Dense.Rational.Constants.RawLinear.negNormalizedRawConstant_degreeCount nonzero)]

end Purelib.Polynomial.Dense.Rational.SignedRemainder.Linear.Translated
