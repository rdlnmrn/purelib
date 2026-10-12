module
public import Purelib.Algebra.FiniteSum.Fin
public import Purelib.Data.Vector.Basic

import Purelib.Tactic.QuotientFreeOmega
public import Purelib.Data.Fin
-- FiniteSum.Fin deliberately re-exports this original integer ring record.
import Purelib.Algebra.Ring.Int
import Purelib.Algebra.Group.Negation
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

public section

/-!
# Finite cellular homology and the standard symplectic basis

This module gives the explicit finite cellular chain complex of the standard
one-vertex, one-face genus-`g` surface model.  Its first cellular boundary and
the abelianized attaching boundary of its face are both zero.  Consequently
the displayed `2g` edge chains are unique representatives of first homology.

The intersection pairing is a finite fold over the `g` displayed handle
coordinates.  The standard `a` and `b` chains are proved to have the exact
Kronecker intersection table.
-/

namespace Purelib.Topology.Surface.CellularHomology

attribute [local instance high] Group.Negation.subNegZeroMonoid

/-- Integral one-chains in the standard genus-`g` finite cell model. The first block contains the `a` edges and the
second block the `b` edges. -/
abbrev OneChain (genus : Nat) :=
  Data.Vector Int (genus + genus)

/-- Integral coefficients on the unique vertex of the standard surface cell model. -/
abbrev ZeroChain := Data.Vector Int 1
/-- Integral coefficients on the unique face of the standard surface cell model. -/
abbrev TwoChain := Data.Vector Int 1

/-- The integral edge chain whose two handle-coordinate blocks vanish. -/
@[expose] def zeroOneChain (genus : Nat) : OneChain genus :=
  Data.Vector.Basic.vectorOfFn fun _ => 0

/-- The zero coefficient at the unique surface vertex. -/
@[expose] def zeroZeroChain : ZeroChain := Data.Vector.Basic.vectorOfFn fun _ => 0

/-- Cellular boundary from edges to the unique vertex. -/
@[expose] def boundaryOne {genus : Nat} (_chain : OneChain genus) : ZeroChain :=
  zeroZeroChain

/-- The oriented face word is a product of commutators, so its finite abelianized cellular boundary is zero. -/
@[expose] def boundaryTwo {genus : Nat} (_chain : TwoChain) : OneChain genus :=
  zeroOneChain genus

/-- The cellular boundary of the face boundary vanishes. -/
theorem boundary_boundary {genus : Nat} (faceChain : TwoChain) :
    boundaryOne (boundaryTwo (genus := genus) faceChain) = zeroZeroChain :=
  rfl

/-- An integral edge chain has zero cellular vertex boundary. -/
@[expose] def IsCycle {genus : Nat} (chain : OneChain genus) : Prop :=
  boundaryOne chain = zeroZeroChain

/-- An integral edge chain is the cellular boundary of a displayed face chain. -/
@[expose] def IsBoundary {genus : Nat} (chain : OneChain genus) : Prop :=
  exists faceChain : TwoChain, boundaryTwo faceChain = chain

/-- Every edge chain is a cycle in the one-vertex surface model. -/
theorem every_oneChain_isCycle {genus : Nat} (chain : OneChain genus) :
    IsCycle chain := rfl

/-- The only edge boundary in the commutator surface model is the zero chain. -/
theorem isBoundary_iff_eq_zero {genus : Nat} (chain : OneChain genus) :
    IsBoundary chain <-> chain = zeroOneChain genus := by
  constructor
  · intro boundary
    rcases boundary with ⟨faceChain, boundaryEqual⟩
    exact boundaryEqual.symm
  · intro chainZero
    exact ⟨Data.Vector.Basic.vectorOfFn (fun _ : Fin 1 => 0), by
      rw [chainZero]
      rfl⟩

/-- Since the boundary subgroup is zero, a first-homology class has a unique displayed integral one-chain
representative. -/
abbrev FirstHomology (genus : Nat) := OneChain genus

/-- Read the coefficient of the indexed a-edge in the first coordinate block. -/
@[expose] def aCoefficient {genus : Nat} (chain : OneChain genus)
    (index : Fin genus) : Int :=
  chain (Fin.castAdd genus index)

/-- Read the coefficient of the indexed b-edge in the second coordinate block. -/
@[expose] def bCoefficient {genus : Nat} (chain : OneChain genus)
    (index : Fin genus) : Int :=
  chain (Fin.natAdd genus index)

/-- Assemble a one-chain from its two displayed coefficient blocks. -/
@[expose] def fromCoefficients {genus : Nat}
    (a b : Fin genus -> Int) : OneChain genus :=
  Data.Vector.Basic.vectorOfFn (Data.Fin.addCases a b)

/-- Assembling the two blocks preserves each supplied a-coefficient. -/
@[simp] theorem fromCoefficients_aCoefficient {genus : Nat}
    (a b : Fin genus -> Int) (index : Fin genus) :
    aCoefficient (fromCoefficients a b) index = a index := by
  unfold aCoefficient fromCoefficients
  rw [Data.Vector.Basic.vectorOfFn_apply, Data.Fin.addCases_left]

/-- Assembling the two blocks preserves each supplied b-coefficient. -/
@[simp] theorem fromCoefficients_bCoefficient {genus : Nat}
    (a b : Fin genus -> Int) (index : Fin genus) :
    bCoefficient (fromCoefficients a b) index = b index := by
  unfold bCoefficient fromCoefficients
  rw [Data.Vector.Basic.vectorOfFn_apply, Data.Fin.addCases_right]

/-- Every homology representative is reconstructed from its explicit `a` and `b` integral coordinates. -/
theorem basis_reconstruct {genus : Nat} (chain : FirstHomology genus) :
    fromCoefficients (aCoefficient chain) (bCoefficient chain) = chain := by
  apply Data.Vector.Basic.vector_ext
  intro position
  rcases Data.Fin.addCases_split position with
    ⟨index, positionEqual⟩ | ⟨index, positionEqual⟩
  · subst position
    change aCoefficient
      (fromCoefficients (aCoefficient chain) (bCoefficient chain)) index =
        aCoefficient chain index
    rw [fromCoefficients_aCoefficient]
  · subst position
    change bCoefficient
      (fromCoefficients (aCoefficient chain) (bCoefficient chain)) index =
        bCoefficient chain index
    rw [fromCoefficients_bCoefficient]

/-- The `a_i` homology chain. -/
@[expose] def aCycle {genus : Nat} (index : Fin genus) : FirstHomology genus :=
  fromCoefficients
    (fun position => if position = index then 1 else 0)
    (fun _ => 0)

/-- The `b_i` homology chain. -/
@[expose] def bCycle {genus : Nat} (index : Fin genus) : FirstHomology genus :=
  fromCoefficients
    (fun _ => 0)
    (fun position => if position = index then 1 else 0)

/-- The a-cycle has unit coefficient at its own a-index and zero elsewhere. -/
@[simp] theorem aCoefficient_aCycle {genus : Nat}
    (left right : Fin genus) :
    aCoefficient (aCycle left) right = if right = left then 1 else 0 := by
  unfold aCycle
  rw [fromCoefficients_aCoefficient]

/-- Every b-coefficient of an a-cycle vanishes. -/
@[simp] theorem bCoefficient_aCycle {genus : Nat}
    (left right : Fin genus) :
    bCoefficient (aCycle left) right = 0 := by
  unfold aCycle
  rw [fromCoefficients_bCoefficient]

/-- Every a-coefficient of a b-cycle vanishes. -/
@[simp] theorem aCoefficient_bCycle {genus : Nat}
    (left right : Fin genus) :
    aCoefficient (bCycle left) right = 0 := by
  unfold bCycle
  rw [fromCoefficients_aCoefficient]

/-- The b-cycle has unit coefficient at its own b-index and zero elsewhere. -/
@[simp] theorem bCoefficient_bCycle {genus : Nat}
    (left right : Fin genus) :
    bCoefficient (bCycle left) right = if right = left then 1 else 0 := by
  unfold bCycle
  rw [fromCoefficients_bCoefficient]

/-- Finite integral intersection pairing in handle coordinates.

The original handle index order and the two retained coefficient blocks supply each displayed alternating product. The
sum uses the unchanged integer addition and multiplication operations. -/
@[expose] def intersection {genus : Nat}
    (left right : FirstHomology genus) : Int :=
  FiniteSum.Fin.sumFin fun index =>
    aCoefficient left index * bCoefficient right index -
      bCoefficient left index * aCoefficient right index

/-- Any two standard a-cycles have zero intersection.

The two original a-cycles have zero b-coefficients at every retained handle index. Each displayed alternating product is
therefore the integer zero. -/
theorem intersection_a_a {genus : Nat} (left right : Fin genus) :
    intersection (aCycle left) (aCycle right) = 0 := by
  unfold intersection
  rw [FiniteSum.Fin.sumFin_congr (right := fun _ : Fin genus => (0 : Int)) (fun index => by
    rw [aCoefficient_aCycle, bCoefficient_aCycle, bCoefficient_aCycle]
    omega0)]
  exact FiniteSum.Fin.sumFin_zero

/-- Any two standard b-cycles have zero intersection.

The two original b-cycles have zero a-coefficients at every retained handle index. Each displayed alternating product is
therefore the integer zero. -/
theorem intersection_b_b {genus : Nat} (left right : Fin genus) :
    intersection (bCycle left) (bCycle right) = 0 := by
  unfold intersection
  rw [FiniteSum.Fin.sumFin_congr (right := fun _ : Fin genus => (0 : Int)) (fun index => by
    rw [aCoefficient_bCycle, aCoefficient_bCycle, bCoefficient_bCycle]
    omega0)]
  exact FiniteSum.Fin.sumFin_zero

/-- An a-cycle meets its matching b-cycle with intersection one and all others with zero.

The original coefficient readbacks give unit weights exactly at the selected handle indices. Equal indices contribute
one, and distinct indices give zero at every displayed summand. -/
theorem intersection_a_b {genus : Nat} (left right : Fin genus) :
    intersection (aCycle left) (bCycle right) =
      if left = right then 1 else 0 := by
  unfold intersection
  by_cases equal : left = right
  · subst right
    rw [if_pos rfl]
    rw [FiniteSum.Fin.sumFin_congr
      (right := fun index : Fin genus => if index = left then 1 else 0)
      (fun index => by
        rw [aCoefficient_aCycle, bCoefficient_bCycle,
          bCoefficient_aCycle, aCoefficient_bCycle]
        by_cases indexEqual : index = left
        · rw [if_pos indexEqual]
          omega0
        · rw [if_neg indexEqual]
          omega0)]
    exact FiniteSum.Fin.sumFin_ite_eq left (fun _ => (1 : Int))
  · rw [if_neg equal]
    rw [FiniteSum.Fin.sumFin_congr (right := fun _ : Fin genus => (0 : Int))
      (fun index => by
        rw [aCoefficient_aCycle, bCoefficient_bCycle,
          bCoefficient_aCycle, aCoefficient_bCycle]
        by_cases indexLeft : index = left
        · rw [if_pos indexLeft]
          have indexNotRight : index ≠ right := by
            intro indexRight
            exact equal (indexLeft.symm.trans indexRight)
          rw [if_neg indexNotRight]
          omega0
        · rw [if_neg indexLeft]
          ring1)]
    exact FiniteSum.Fin.sumFin_zero

/-- Exchanging homology arguments negates their integral intersection pairing. -/
theorem intersection_skew {genus : Nat}
    (left right : FirstHomology genus) :
    intersection left right = -intersection right left := by
  unfold intersection
  rw [← FiniteSum.Fin.sumFin_neg]
  apply FiniteSum.Fin.sumFin_congr
  intro index
  ring1

/-- A b-cycle meets its matching a-cycle with intersection minus one and all others with zero. -/
theorem intersection_b_a {genus : Nat} (left right : Fin genus) :
    intersection (bCycle left) (aCycle right) =
      -(if left = right then 1 else 0) := by
  rw [intersection_skew, intersection_a_b]
  by_cases equal : left = right
  · rw [if_pos equal, if_pos equal.symm]
  · rw [if_neg equal, if_neg (fun reverse => equal reverse.symm)]

/-- The explicit basis and its finite intersection table. -/
structure SymplecticBasisCertificate (genus : Nat) : Type where
  /-- The two coordinate blocks reconstruct every retained homology representative. -/ reconstruct : forall chain :
    FirstHomology genus,
    fromCoefficients (aCoefficient chain) (bCoefficient chain) = chain
  /-- Pairwise intersections among the standard a-cycles vanish. -/ a_a : forall left right : Fin genus,
    intersection (aCycle left) (aCycle right) = 0
  /-- Pairwise intersections among the standard b-cycles vanish. -/ b_b : forall left right : Fin genus,
    intersection (bCycle left) (bCycle right) = 0
  /-- The ordered a-b intersection matrix is the identity. -/ a_b : forall left right : Fin genus,
    intersection (aCycle left) (bCycle right) =
    if left = right then 1 else 0

/-- Construct the symplectic homology basis for every finite genus. -/
@[expose] def standardSymplecticBasis (genus : Nat) :
    SymplecticBasisCertificate genus where
  reconstruct := basis_reconstruct
  a_a := intersection_a_a
  b_b := intersection_b_b
  a_b := intersection_a_b

end Purelib.Topology.Surface.CellularHomology
