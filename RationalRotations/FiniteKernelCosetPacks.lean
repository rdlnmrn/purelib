import RationalRotations.FiniteSquareClassPacks
import RationalRotations.QuaternionObstruction

/-!
# Arbitrarily large finite packs of separated unit-kernel cosets

Corollary 63's infinite-index sentence is represented by a finite request.
For every supplied natural count, the constructor below returns that many
rotations whose pairwise relative proportions do not admit norm-one
representatives.  No quotient group or abstract subgroup index is formed.
-/

namespace RationalRotations

namespace FiniteKernelCosetPacks

abbrev Scalar := RFAP.ConstructiveFraction.Rational

/-- Two displayed projective rotation proportions represent the same coset
of the unit-quaternion kernel when their relative product has a norm-one
representative. -/
abbrev SameUnitKernelCoset {K : Type*} [RFAP.ExplicitField K] :=
  @NonNullProportion.InSameUnitKernelCoset K _

theorem sameUnitKernelCoset_iff_quadranceClass_equivalent
    {K : Type*} [RFAP.ExplicitField K]
    (left right : NonNullProportion K) :
    SameUnitKernelCoset left right ↔
      left.quadranceClass.Equivalent right.quadranceClass :=
  NonNullProportion.inSameUnitKernelCoset_iff_quadranceClass_equivalent
    left right

theorem sameUnitKernelCoset_respects_equivalent
    {K : Type*} [RFAP.ExplicitField K]
    {left left' right right' : NonNullProportion K}
    (leftEquivalent : left.Equivalent left')
    (rightEquivalent : right.Equivalent right') :
    SameUnitKernelCoset left right ↔ SameUnitKernelCoset left' right' := by
  rw [sameUnitKernelCoset_iff_quadranceClass_equivalent,
    sameUnitKernelCoset_iff_quadranceClass_equivalent]
  have leftClass :=
    NonNullProportion.quadranceClass_respects_equivalent leftEquivalent
  have rightClass :=
    NonNullProportion.quadranceClass_respects_equivalent rightEquivalent
  constructor
  · intro sameClass
    exact SquareClassRepresentative.equivalent_trans
      (SquareClassRepresentative.equivalent_symm leftClass)
      (SquareClassRepresentative.equivalent_trans sameClass rightClass)
  · intro sameClass
    exact SquareClassRepresentative.equivalent_trans leftClass
      (SquareClassRepresentative.equivalent_trans sameClass
        (SquareClassRepresentative.equivalent_symm rightClass))

/-- One retained rotation representative of a separated kernel coset. -/
structure KernelCosetEntry where
  squareClassEntry : FiniteSquareClassPacks.PositiveSquareClassEntry
  proportion : NonNullProportion Scalar
  proportion_eq : proportion = squareClassEntry.preimage
  rotation : Rotation Scalar
  rotation_eq : rotation = proportion.rotation
  quadranceClass_value : proportion.quadranceClass.value =
    squareClassEntry.target.representative.value

/-- Preserve the cached four-square preimage while exposing its rotation. -/
def kernelCosetEntry
    (entry : FiniteSquareClassPacks.PositiveSquareClassEntry) :
    KernelCosetEntry where
  squareClassEntry := entry
  proportion := entry.preimage
  proportion_eq := rfl
  rotation := entry.preimage.rotation
  rotation_eq := rfl
  quadranceClass_value := entry.quadranceClass_value

theorem kernelCosetEntries_separated
    (left right : FiniteSquareClassPacks.PositiveSquareClassEntry)
    (inequivalent :
      ¬ left.target.representative.Equivalent
        right.target.representative) :
    ¬ SameUnitKernelCoset (kernelCosetEntry left).proportion
      (kernelCosetEntry right).proportion := by
  intro sameCoset
  apply inequivalent
  have preimageEquivalent :=
    (sameUnitKernelCoset_iff_quadranceClass_equivalent
      left.preimage right.preimage).mp sameCoset
  rcases preimageEquivalent with ⟨factor, factorNonzero, equation⟩
  refine ⟨factor, factorNonzero, ?_⟩
  rw [← left.quadranceClass_value, ← right.quadranceClass_value]
  exact equation

/-- The complete finite response to one kernel-index request. -/
structure SeparatedKernelCosetPack (count : Nat) where
  entries : List KernelCosetEntry
  length_eq : entries.length = count
  pairwiseSeparated : entries.Pairwise fun left right =>
    ¬ SameUnitKernelCoset left.proportion right.proportion

/-- Produce exactly `count` rotations in pairwise separated unit-kernel
cosets, consuming the square-class pack and all of its cached preimages. -/
def separatedKernelCosetPack (count : Nat) :
    SeparatedKernelCosetPack count := by
  let source :=
    FiniteSquareClassPacks.distinctPositiveSquareClassPack count
  refine
    { entries := source.entries.map kernelCosetEntry
      length_eq := ?_
      pairwiseSeparated := ?_ }
  · rw [List.length_map, source.length_eq]
  · rw [QuotientFreeList.pairwise_map]
    exact source.pairwiseInequivalent.imp (by
      intro left right inequivalent
      exact kernelCosetEntries_separated left right inequivalent)

theorem separatedKernelCosetPack_entry_realizes
    (count : Nat) (entry : KernelCosetEntry)
    (_member : entry ∈ (separatedKernelCosetPack count).entries) :
    entry.proportion.quadranceClass.value =
      entry.squareClassEntry.target.representative.value :=
  entry.quadranceClass_value

end FiniteKernelCosetPacks

end RationalRotations
