module
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Rat.SignTest.Equality
public import Purelib.Geometry.Projective.Hermitian.Atom
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.SignTest
import Purelib.Geometry.Projective.Hermitian.Basic

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry.Projective

section
@[expose] public section

/-!
# Finite equality ownership for CCL formula atoms

The parser's weak/strict convention decides every atom exactly at a zero of
its Hermitian form.  This module records that decision as finite data and
lets formula inspection reuse boundaries already proved identically zero.
Consequently a universal boundary is discharged once, and structural
reinspection either proves the complete formula stable or returns a
different unresolved atom.
-/

namespace Purelib.Geometry.Projective.Hermitian

/-- An atom whose form vanishes either owns that equality or excludes it, exactly as reported by its finite sign tag. -/
def atomEqualityDecision (atom : Hermitian.Atom) :
  SignTest.EqualityDecision atom.sign :=
  SignTest.decideEquality atom.sign

/-- An equality-owning sign atom holds wherever its Hermitian form vanishes. -/
theorem atom_holds_of_boundary
    {atom : Hermitian.Atom} {value : Data.Gaussian.Basic.Canonical}
    (boundary : atom.form.eval value = 0)
    (ownedProof : atom.sign.Holds 0)
    (_owned : atomEqualityDecision atom = .owned ownedProof) :
    atom.Holds value := by
  unfold Hermitian.Atom.Holds
  rw [boundary]
  exact ownedProof

/-- An equality-excluding sign atom fails wherever its Hermitian form vanishes. -/
theorem atom_not_holds_of_boundary
    {atom : Hermitian.Atom} {value : Data.Gaussian.Basic.Canonical}
    (boundary : atom.form.eval value = 0)
    (excludedProof : ¬atom.sign.Holds 0)
    (_excluded : atomEqualityDecision atom = .excluded excludedProof) :
    ¬atom.Holds value := by
  unfold Hermitian.Atom.Holds
  rw [boundary]
  exact excludedProof
end Purelib.Geometry.Projective.Hermitian

end
