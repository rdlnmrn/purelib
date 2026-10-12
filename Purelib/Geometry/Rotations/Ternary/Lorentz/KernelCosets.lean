module

public import Purelib.Geometry.Rotations.Ternary.Lorentz.SquareClass
public import Purelib.NumberTheory.SquareClass.Rational.Separation
public import Purelib.Data.List.Map
public import Purelib.Data.List.Pairwise

/-!
# Finite packs of rational Lorentz kernel cosets

An explicit Euclid-prime request supplies pairwise inequivalent norms.
Each entry retains its original prime, exact Clifford norm witness and
original rotation. Separation concerns their actual inverse-left product.
-/

public section

namespace Purelib.Geometry.Rotations.Ternary.Lorentz

open Purelib.Algebra.Quadratic.Ternary.Basic renaming TernaryForm -> Form
open Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.NumberTheory.Prime.FinitePacks
open Purelib.NumberTheory.SquareClass.Rational
open Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm
open Purelib.Data.List

/-- A retained prime, original Clifford norm witness and original Lorentz rotation.

The exact norm is the positive rational square-class target of that prime.
The cached rotation is the action of the same retained representative;
the dependent tuple preserves all three original owners.
-/
abbrev KernelCosetEntry (oneNonzero : (1 : Rational) ≠ 0) :=
  Σ' prime : SquareClassPacks.EuclidPrime,
    Σ' representative : (Form.lorentz oneNonzero).NonNullEvenClifford,
      Σ' rotation : (Form.lorentz oneNonzero).SpecialOrthogonal,
        EvenClifford.norm representative.toEvenClifford =
          (Separation.SquareClassPacks.positivePrimeClass prime).representative.value ∧
        NonNullEvenClifford.actionRotation representative = rotation

namespace KernelCosetEntry

variable {oneNonzero : (1 : Rational) ≠ 0}

/-- Read the original prime of a retained kernel-coset entry. -/
abbrev prime (entry : KernelCosetEntry oneNonzero) := entry.1

/-- Read the original cached non-null Clifford representative. -/
abbrev representative (entry : KernelCosetEntry oneNonzero) := entry.2.1

/-- Read the original cached Lorentz rotation. -/
abbrev rotation (entry : KernelCosetEntry oneNonzero) := entry.2.2.1

/-- The retained Clifford norm is exactly the original prime target value. -/
theorem norm_eq (entry : KernelCosetEntry oneNonzero) :
    EvenClifford.norm entry.representative.toEvenClifford =
      (Separation.SquareClassPacks.positivePrimeClass entry.prime).representative.value := entry.2.2.2.1

/-- The cached rotation is the action of the same retained Clifford representative. -/
theorem represents (entry : KernelCosetEntry oneNonzero) :
    NonNullEvenClifford.actionRotation entry.representative = entry.rotation := entry.2.2.2.2

end KernelCosetEntry

/-- Construct a rational Lorentz coset entry from the original prime through its exact norm witness. -/
@[expose] def kernelCosetEntry (oneNonzero : (1 : Rational) ≠ 0)
    (twoNonzero : (2 : Rational) ≠ 0) (prime : SquareClassPacks.EuclidPrime) : KernelCosetEntry oneNonzero :=
  let target := Separation.SquareClassPacks.positivePrimeClass prime
  let representative := nonNullNormWitness oneNonzero target.representative.value
    target.representative.nonzero twoNonzero
  ⟨prime, representative, NonNullEvenClifford.actionRotation representative,
    norm_normWitness oneNonzero target.representative.value twoNonzero, rfl⟩

/-- Distinct original prime targets give Lorentz rotations with no unit-norm relative preimage.

Both cached rotations and both original Clifford inputs are retained.
The norm-class equivalence forced by a unit relative preimage contradicts
the separation of the original prime targets.
-/
theorem kernelCosetEntries_separated (oneNonzero : (1 : Rational) ≠ 0)
    (twoNonzero : (2 : Rational) ≠ 0) (left right : KernelCosetEntry oneNonzero)
    (different : left.prime ≠ right.prime) :
    ¬ ∃ value : (Form.lorentz oneNonzero).NonNullEvenClifford,
      NonNullEvenClifford.actionRotation value =
        SpecialOrthogonal.mul (SpecialOrthogonal.inverse left.rotation) right.rotation ∧
      EvenClifford.norm value.toEvenClifford = 1 := by
  intro unitPreimage
  rw [← left.represents, ← right.represents] at unitPreimage
  have classes := (NonNullEvenClifford.unitNormRelativePreimage_iff
    left.representative right.representative twoNonzero).mp unitPreimage
  apply Separation.SquareClassPacks.distinct_primes_not_equivalent left.prime right.prime different
  rcases classes with ⟨factor, factorNonzero, equal⟩
  refine ⟨factor, factorNonzero, ?_⟩
  change EvenClifford.norm right.representative.toEvenClifford =
    factor ^ 2 * EvenClifford.norm left.representative.toEvenClifford at equal
  rw [left.norm_eq, right.norm_eq] at equal
  exact equal

/-- A requested finite list of Lorentz rotations in pairwise separated unit-norm kernel cosets.

The response retains its exact length and excludes unit-norm Clifford
preimages of every actual inverse-left product in the ordered pairwise list.
-/
abbrev SeparatedKernelCosetPack (oneNonzero : (1 : Rational) ≠ 0) (count : Nat) :=
  Σ' entries : List (KernelCosetEntry oneNonzero), entries.length = count ∧
    entries.Pairwise fun left right =>
      ¬ ∃ value : (Form.lorentz oneNonzero).NonNullEvenClifford,
        NonNullEvenClifford.actionRotation value =
          SpecialOrthogonal.mul (SpecialOrthogonal.inverse left.rotation) right.rotation ∧
        EvenClifford.norm value.toEvenClifford = 1

namespace SeparatedKernelCosetPack

variable {oneNonzero : (1 : Rational) ≠ 0} {count : Nat}

/-- Read the retained finite list of original kernel-coset entries. -/
abbrev entries (pack : SeparatedKernelCosetPack oneNonzero count) := pack.1

/-- The retained list has exactly the requested number of entries. -/
theorem length_eq (pack : SeparatedKernelCosetPack oneNonzero count) :
    pack.entries.length = count := pack.2.1

/-- Every actual ordered relative rotation in the retained list lacks a unit-norm Clifford preimage. -/
theorem pairwiseSeparated (pack : SeparatedKernelCosetPack oneNonzero count) :
    pack.entries.Pairwise fun left right =>
      ¬ ∃ value : (Form.lorentz oneNonzero).NonNullEvenClifford,
        NonNullEvenClifford.actionRotation value =
          SpecialOrthogonal.mul (SpecialOrthogonal.inverse left.rotation) right.rotation ∧
        EvenClifford.norm value.toEvenClifford = 1 := pack.2.2

end SeparatedKernelCosetPack

/-- Produce exactly the requested number of pairwise separated rational Lorentz kernel cosets.

The original finite Euclid iteration runs once. Each retained prime maps
to one exact norm witness and one cached original rotation; the actual
relative-preimage criterion transports the prime separation certificate.
-/
@[expose] def separatedKernelCosetPack (oneNonzero : (1 : Rational) ≠ 0)
    (twoNonzero : (2 : Rational) ≠ 0) (count : Nat) : SeparatedKernelCosetPack oneNonzero count :=
  let primes := SquareClassPacks.euclidPrimes count
  ⟨primes.map (kernelCosetEntry oneNonzero twoNonzero),
    (Map.length_map (kernelCosetEntry oneNonzero twoNonzero) primes).trans
      (SquareClassPacks.euclidPrimes_length count),
    Pairwise.pairwise_map.mpr ((SquareClassPacks.euclidPrimes_nodup count).imp (by
      intro left right different
      exact kernelCosetEntries_separated oneNonzero twoNonzero
        (kernelCosetEntry oneNonzero twoNonzero left) (kernelCosetEntry oneNonzero twoNonzero right) different))⟩

end Purelib.Geometry.Rotations.Ternary.Lorentz
