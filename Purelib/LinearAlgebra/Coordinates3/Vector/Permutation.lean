module
import Purelib.Algebra.Field.ExplicitField

public import Purelib.LinearAlgebra.Coordinates3.Vector

open Purelib.Algebra.Field

open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

section
@[expose] public section

namespace Purelib.LinearAlgebra.Coordinates3.Vector.Permutation

variable {K : Type*}

/-- The six finite ways in which two triples can have identical entries.
Repeated entries may of course admit more than one constructor. -/
inductive SameEntries (left right : Vector3 K) : Prop
  /-- Certify the coordinate ordering `abc` of the original three entries. -/ | abc (first : left.t = right.t)
      (second : left.r = right.r)
      (third : left.s = right.s)
  /-- Certify the coordinate ordering `acb` of the original three entries. -/ | acb (first : left.t = right.t)
      (second : left.r = right.s)
      (third : left.s = right.r)
  /-- Certify the coordinate ordering `bac` of the original three entries. -/ | bac (first : left.t = right.r)
      (second : left.r = right.t)
      (third : left.s = right.s)
  /-- Certify the coordinate ordering `bca` of the original three entries. -/ | bca (first : left.t = right.r)
      (second : left.r = right.s)
      (third : left.s = right.t)
  /-- Certify the coordinate ordering `cab` of the original three entries. -/ | cab (first : left.t = right.s)
      (second : left.r = right.t)
      (third : left.s = right.r)
  /-- Certify the coordinate ordering `cba` of the original three entries. -/ | cba (first : left.t = right.s)
      (second : left.r = right.r)
      (third : left.s = right.t)

end Purelib.LinearAlgebra.Coordinates3.Vector.Permutation

end

end

section
@[expose] public section

/-!
# Divine Proportions, Exercises 10.10 and 10.11

The two small-field classifications are reduced to finite scalar certificates.
No list of field points, lines, or triangles is constructed.  The `F₅` null
case also makes explicit the boundary in the book's spread-based definition of
similarity: a triangle with two null sides has no vertex at which a spread is
defined.
-/

namespace Purelib.LinearAlgebra.Coordinates3.Vector.Permutation

variable {K : Type*} [ExplicitField K]

/-- An unordered triple with two copies of `repeated` and one copy of
`single`, written as the three possible displayed positions. -/
def RepeatedEntryPattern (repeated single : K)
    (entries : Vector3 K) : Prop :=
  (entries.t = repeated ∧ entries.r = repeated ∧
      entries.s = single) ∨
    (entries.t = repeated ∧ entries.r = single ∧
      entries.s = repeated) ∨
    (entries.t = single ∧ entries.r = repeated ∧
      entries.s = repeated)

omit [ExplicitField K] in
/-- Equal repeated-entry patterns give a retained permutation of the three entries. -/
theorem sameEntries_of_repeatedEntryPattern
    {repeated single : K} {left right : Vector3 K}
    (leftPattern : Vector3.Permutation.RepeatedEntryPattern repeated single left)
    (rightPattern : Vector3.Permutation.RepeatedEntryPattern repeated single right) :
    Vector3.Permutation.SameEntries left right := by
  rcases leftPattern with leftFirst | leftSecond | leftThird
  · rcases leftFirst with ⟨leftOne, leftTwo, leftThree⟩
    rcases rightPattern with rightFirst | rightSecond | rightThird
    · rcases rightFirst with ⟨rightOne, rightTwo, rightThree⟩
      apply Vector3.Permutation.SameEntries.abc
      · exact leftOne.trans rightOne.symm
      · exact leftTwo.trans rightTwo.symm
      · exact leftThree.trans rightThree.symm
    · rcases rightSecond with ⟨rightOne, rightTwo, rightThree⟩
      apply Vector3.Permutation.SameEntries.acb
      · exact leftOne.trans rightOne.symm
      · exact leftTwo.trans rightThree.symm
      · exact leftThree.trans rightTwo.symm
    · rcases rightThird with ⟨rightOne, rightTwo, rightThree⟩
      apply Vector3.Permutation.SameEntries.bca
      · exact leftOne.trans rightTwo.symm
      · exact leftTwo.trans rightThree.symm
      · exact leftThree.trans rightOne.symm
  · rcases leftSecond with ⟨leftOne, leftTwo, leftThree⟩
    rcases rightPattern with rightFirst | rightSecond | rightThird
    · rcases rightFirst with ⟨rightOne, rightTwo, rightThree⟩
      apply Vector3.Permutation.SameEntries.acb
      · exact leftOne.trans rightOne.symm
      · exact leftTwo.trans rightThree.symm
      · exact leftThree.trans rightTwo.symm
    · rcases rightSecond with ⟨rightOne, rightTwo, rightThree⟩
      apply Vector3.Permutation.SameEntries.abc
      · exact leftOne.trans rightOne.symm
      · exact leftTwo.trans rightTwo.symm
      · exact leftThree.trans rightThree.symm
    · rcases rightThird with ⟨rightOne, rightTwo, rightThree⟩
      apply Vector3.Permutation.SameEntries.bac
      · exact leftOne.trans rightTwo.symm
      · exact leftTwo.trans rightOne.symm
      · exact leftThree.trans rightThree.symm
  · rcases leftThird with ⟨leftOne, leftTwo, leftThree⟩
    rcases rightPattern with rightFirst | rightSecond | rightThird
    · rcases rightFirst with ⟨rightOne, rightTwo, rightThree⟩
      apply Vector3.Permutation.SameEntries.cab
      · exact leftOne.trans rightThree.symm
      · exact leftTwo.trans rightOne.symm
      · exact leftThree.trans rightTwo.symm
    · rcases rightSecond with ⟨rightOne, rightTwo, rightThree⟩
      apply Vector3.Permutation.SameEntries.bca
      · exact leftOne.trans rightTwo.symm
      · exact leftTwo.trans rightThree.symm
      · exact leftThree.trans rightOne.symm
    · rcases rightThird with ⟨rightOne, rightTwo, rightThree⟩
      apply Vector3.Permutation.SameEntries.abc
      · exact leftOne.trans rightOne.symm
      · exact leftTwo.trans rightTwo.symm
      · exact leftThree.trans rightThree.symm

end Purelib.LinearAlgebra.Coordinates3.Vector.Permutation

end
