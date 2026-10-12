module
import Purelib.Data.List.Map
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Geometry.Rotations.Projective.Action
import Purelib.Algebra.Field.SquareClass.Basic
public import Purelib.Algebra.Quaternion.Projective.Rational.Packs
import Purelib.Algebra.Quaternion.Projective.SquareClass
public import Purelib.Algebra.Quaternion.Projective.UnitObstruction
public import Purelib.Data.List.Pairwise
import Purelib.Data.Rat.Fraction

import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Quaternion.Projective.Basic
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Rotations.Basic
import Init.Data.List.Lemmas
import Init.Prelude
import Purelib.Data.Rat.Fraction.Field
import Purelib.NumberTheory.SquareClass.Rational.Basic

open Purelib

open Purelib.Algebra.Field.SquareClass.Basic

open Purelib.Algebra.Quaternion

open Purelib.Algebra.Quaternion.Projective.Rational.Packs

open Purelib.Algebra.Quaternion.Projective.SquareClass

open Purelib.Algebra.Quaternion.Projective.UnitObstruction

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Geometry.Rotations.Projective.Action

@[expose] public section

/-!
# Arbitrarily large finite packs of separated unit-kernel cosets

Corollary 63's infinite-index sentence is represented by a finite request.
For every supplied natural count, the constructor below returns that many
rotations whose pairwise relative proportions do not admit norm-one
representatives.  No quotient group or abstract subgroup index is formed.
-/

namespace Purelib.Geometry.Rotations.Rational.Kernel.CosetPacks

open Purelib.Geometry.Rotations.Basic

namespace KernelCosetPacks

/-- The constructive rational scalar field for separated kernel-coset packs. -/
abbrev Scalar := Fraction.Rational

/-- Two displayed projective rotation proportions represent the same coset of the unit-quaternion kernel when their
relative product has a norm-one representative. -/
abbrev SameUnitKernelCoset {K : Type*} [Algebra.Field.ExplicitField K] :=
  @NonNullProportion.InSameUnitKernelCoset K _

/-- Two retained proportions lie in the same unit-kernel coset exactly when their quadrance classes agree. -/
theorem sameUnitKernelCoset_iff_quadranceClass_equivalent
    {K : Type*} [Algebra.Field.ExplicitField K]
    (left right : Projective.Basic.NonNullProportion K) :
    Geometry.Rotations.Rational.Kernel.CosetPacks.KernelCosetPacks.SameUnitKernelCoset left right ↔
      (NonNullProportion.quadranceClass left).Equivalent (NonNullProportion.quadranceClass right) :=
  NonNullProportion.inSameUnitKernelCoset_iff_quadranceClass_equivalent
    left right

/-- The same-unit-kernel-coset relation respects equivalent homogeneous representatives. -/
theorem sameUnitKernelCoset_respects_equivalent
    {K : Type*} [Algebra.Field.ExplicitField K]
    {left left' right right' : Projective.Basic.NonNullProportion K}
    (leftEquivalent : left.Equivalent left')
    (rightEquivalent : right.Equivalent right') :
    Geometry.Rotations.Rational.Kernel.CosetPacks.KernelCosetPacks.SameUnitKernelCoset left right ↔
      Geometry.Rotations.Rational.Kernel.CosetPacks.KernelCosetPacks.SameUnitKernelCoset left' right' := by
  have leftClass :=
    NonNullProportion.quadranceClass_respects_equivalent leftEquivalent
  have rightClass :=
    NonNullProportion.quadranceClass_respects_equivalent rightEquivalent
  constructor
  · intro sameCoset
    apply (sameUnitKernelCoset_iff_quadranceClass_equivalent left' right').mpr
    have sameClass :=
      (sameUnitKernelCoset_iff_quadranceClass_equivalent left right).mp sameCoset
    exact SquareClassRepresentative.equivalent_trans
      (SquareClassRepresentative.equivalent_symm leftClass)
      (SquareClassRepresentative.equivalent_trans sameClass rightClass)
  · intro sameCoset
    apply (sameUnitKernelCoset_iff_quadranceClass_equivalent left right).mpr
    have sameClass :=
      (sameUnitKernelCoset_iff_quadranceClass_equivalent left' right').mp sameCoset
    exact SquareClassRepresentative.equivalent_trans leftClass
      (SquareClassRepresentative.equivalent_trans sameClass
        (SquareClassRepresentative.equivalent_symm rightClass))

set_option genInjectivity false in
/-- One retained rotation representative of a separated kernel coset. -/
structure KernelCosetEntry where
  /-- The original positive square-class entry and its cached preimage. -/ squareClassEntry :
    SquareClassPacks.PositiveSquareClassEntry
  /-- The retained non-null projective proportion. -/ proportion : Projective.Basic.NonNullProportion
    Geometry.Rotations.Rational.Kernel.CosetPacks.KernelCosetPacks.Scalar
  /-- The proportion is exactly the original square-class entry's cached preimage. -/ proportion_eq : proportion =
    squareClassEntry.preimage
  /-- The cached rotation of the retained proportion. -/ rotation : Rotations.Basic.Rotation
    Geometry.Rotations.Rational.Kernel.CosetPacks.KernelCosetPacks.Scalar
  /-- The cached rotation is the projective rotation of the retained proportion. -/ rotation_eq : rotation =
    (NonNullProportion.rotation proportion)
  /-- The proportion's quadrance-class value equals the original target value. -/ quadranceClass_value :
    (NonNullProportion.quadranceClass proportion).value =
    squareClassEntry.target.representative.value

constructive_injectivity KernelCosetEntry

/-- Preserve the cached four-square preimage while exposing its rotation. -/
def kernelCosetEntry
    (entry : SquareClassPacks.PositiveSquareClassEntry) :
    Geometry.Rotations.Rational.Kernel.CosetPacks.KernelCosetPacks.KernelCosetEntry where
  squareClassEntry := entry
  proportion := entry.preimage
  proportion_eq := rfl
  rotation := (NonNullProportion.rotation entry.preimage)
  rotation_eq := rfl
  quadranceClass_value := entry.quadranceClass_value

/-- Inequivalent retained positive square classes give distinct unit-kernel cosets. -/
theorem kernelCosetEntries_separated
    (left right : SquareClassPacks.PositiveSquareClassEntry)
    (inequivalent :
      ¬ left.target.representative.Equivalent
        right.target.representative) :
    ¬ Geometry.Rotations.Rational.Kernel.CosetPacks.KernelCosetPacks.SameUnitKernelCoset
      (Geometry.Rotations.Rational.Kernel.CosetPacks.KernelCosetPacks.kernelCosetEntry left).proportion
      (Geometry.Rotations.Rational.Kernel.CosetPacks.KernelCosetPacks.kernelCosetEntry right).proportion := by
  intro sameCoset
  apply inequivalent
  have preimageEquivalent :=
    (Geometry.Rotations.Rational.Kernel.CosetPacks.KernelCosetPacks.sameUnitKernelCoset_iff_quadranceClass_equivalent
      left.preimage right.preimage).mp sameCoset
  rcases preimageEquivalent with ⟨factor, factorNonzero, equation⟩
  refine ⟨factor, factorNonzero, ?_⟩
  rw [← left.quadranceClass_value, ← right.quadranceClass_value]
  exact equation

set_option genInjectivity false in
/-- The complete finite response to one kernel-index request. -/
structure SeparatedKernelCosetPack (count : Nat) where
  /-- The list of retained rotation representatives. -/ entries : List
    Geometry.Rotations.Rational.Kernel.CosetPacks.KernelCosetPacks.KernelCosetEntry
  /-- The list has exactly the requested number of entries. -/ length_eq : entries.length = count
  /-- Every pair of entries occupies distinct unit-kernel cosets. -/ pairwiseSeparated : entries.Pairwise fun left right
    =>
    ¬ Geometry.Rotations.Rational.Kernel.CosetPacks.KernelCosetPacks.SameUnitKernelCoset left.proportion
      right.proportion

constructive_injectivity SeparatedKernelCosetPack

/-- Produce exactly `count` rotations in pairwise separated unit-kernel cosets, consuming the square-class pack and all
of its cached preimages. -/
def separatedKernelCosetPack (count : Nat) :
    Geometry.Rotations.Rational.Kernel.CosetPacks.KernelCosetPacks.SeparatedKernelCosetPack count := by
  let source :=
    SquareClassPacks.distinctPositiveSquareClassPack count
  refine
    { entries := source.entries.map Geometry.Rotations.Rational.Kernel.CosetPacks.KernelCosetPacks.kernelCosetEntry
      length_eq := ?_
      pairwiseSeparated := ?_ }
  · exact (Map.length_map
      Geometry.Rotations.Rational.Kernel.CosetPacks.KernelCosetPacks.kernelCosetEntry
      source.entries).trans source.length_eq
  · apply Pairwise.pairwise_map.mpr
    exact source.pairwiseInequivalent.imp (by
      intro left right inequivalent
      exact Geometry.Rotations.Rational.Kernel.CosetPacks.KernelCosetPacks.kernelCosetEntries_separated left right
        inequivalent)

/-- Each retained pack entry realizes its original square-class representative. -/
theorem separatedKernelCosetPack_entry_realizes
    (count : Nat) (entry : Geometry.Rotations.Rational.Kernel.CosetPacks.KernelCosetPacks.KernelCosetEntry)
    (_member : entry ∈ (Geometry.Rotations.Rational.Kernel.CosetPacks.KernelCosetPacks.separatedKernelCosetPack
      count).entries) :
    (NonNullProportion.quadranceClass entry.proportion).value =
      entry.squareClassEntry.target.representative.value :=
  entry.quadranceClass_value

end KernelCosetPacks

end Purelib.Geometry.Rotations.Rational.Kernel.CosetPacks

end
