import CCL.Riemann.HyperellipticTopology
import mathlib.Data.ConstructiveFin
import mathlib.RFAP.ConstructiveFiniteMatrix

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

namespace CCL.Riemann.CellularHomology

open RFAP.ConstructiveFiniteMatrix

/-- Integral one-chains in the standard genus-`g` finite cell model.  The
first block contains the `a` edges and the second block the `b` edges. -/
abbrev OneChain (genus : Nat) :=
  RFAP.ConstructiveFiniteMatrix.Vector Int (genus + genus)

abbrev ZeroChain := RFAP.ConstructiveFiniteMatrix.Vector Int 1
abbrev TwoChain := RFAP.ConstructiveFiniteMatrix.Vector Int 1

def zeroOneChain (genus : Nat) : OneChain genus :=
  vectorOfFn fun _ => 0

def zeroZeroChain : ZeroChain := vectorOfFn fun _ => 0

/-- Cellular boundary from edges to the unique vertex. -/
def boundaryOne {genus : Nat} (_chain : OneChain genus) : ZeroChain :=
  zeroZeroChain

/-- The oriented face word is a product of commutators, so its finite
abelianized cellular boundary is zero. -/
def boundaryTwo {genus : Nat} (_chain : TwoChain) : OneChain genus :=
  zeroOneChain genus

theorem boundary_boundary {genus : Nat} (faceChain : TwoChain) :
    boundaryOne (boundaryTwo (genus := genus) faceChain) = zeroZeroChain :=
  rfl

def IsCycle {genus : Nat} (chain : OneChain genus) : Prop :=
  boundaryOne chain = zeroZeroChain

def IsBoundary {genus : Nat} (chain : OneChain genus) : Prop :=
  exists faceChain : TwoChain, boundaryTwo faceChain = chain

theorem every_oneChain_isCycle {genus : Nat} (chain : OneChain genus) :
    IsCycle chain := rfl

theorem isBoundary_iff_eq_zero {genus : Nat} (chain : OneChain genus) :
    IsBoundary chain <-> chain = zeroOneChain genus := by
  constructor
  · intro boundary
    rcases boundary with ⟨faceChain, boundaryEqual⟩
    exact boundaryEqual.symm
  · intro chainZero
    exact ⟨vectorOfFn (fun _ : Fin 1 => 0), by
      rw [chainZero]
      rfl⟩

/-- Since the boundary subgroup is zero, a first-homology class has a unique
displayed integral one-chain representative. -/
abbrev FirstHomology (genus : Nat) := OneChain genus

def aCoefficient {genus : Nat} (chain : OneChain genus)
    (index : Fin genus) : Int :=
  chain (Fin.castAdd genus index)

def bCoefficient {genus : Nat} (chain : OneChain genus)
    (index : Fin genus) : Int :=
  chain (Fin.natAdd genus index)

/-- Assemble a one-chain from its two displayed coefficient blocks. -/
def fromCoefficients {genus : Nat}
    (a b : Fin genus -> Int) : OneChain genus :=
  vectorOfFn (QuotientFreeFin.addCases a b)

@[simp] theorem fromCoefficients_aCoefficient {genus : Nat}
    (a b : Fin genus -> Int) (index : Fin genus) :
    aCoefficient (fromCoefficients a b) index = a index := by
  unfold aCoefficient fromCoefficients
  rw [vectorOfFn_apply, QuotientFreeFin.addCases_left]

@[simp] theorem fromCoefficients_bCoefficient {genus : Nat}
    (a b : Fin genus -> Int) (index : Fin genus) :
    bCoefficient (fromCoefficients a b) index = b index := by
  unfold bCoefficient fromCoefficients
  rw [vectorOfFn_apply, QuotientFreeFin.addCases_right]

/-- Every homology representative is reconstructed from its explicit `a` and
`b` integral coordinates. -/
theorem basis_reconstruct {genus : Nat} (chain : FirstHomology genus) :
    fromCoefficients (aCoefficient chain) (bCoefficient chain) = chain := by
  apply vector_ext
  intro position
  rcases QuotientFreeFin.addCases_split position with
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
def aCycle {genus : Nat} (index : Fin genus) : FirstHomology genus :=
  fromCoefficients
    (fun position => if position = index then 1 else 0)
    (fun _ => 0)

/-- The `b_i` homology chain. -/
def bCycle {genus : Nat} (index : Fin genus) : FirstHomology genus :=
  fromCoefficients
    (fun _ => 0)
    (fun position => if position = index then 1 else 0)

@[simp] theorem aCoefficient_aCycle {genus : Nat}
    (left right : Fin genus) :
    aCoefficient (aCycle left) right = if right = left then 1 else 0 := by
  unfold aCycle
  rw [fromCoefficients_aCoefficient]

@[simp] theorem bCoefficient_aCycle {genus : Nat}
    (left right : Fin genus) :
    bCoefficient (aCycle left) right = 0 := by
  unfold aCycle
  rw [fromCoefficients_bCoefficient]

@[simp] theorem aCoefficient_bCycle {genus : Nat}
    (left right : Fin genus) :
    aCoefficient (bCycle left) right = 0 := by
  unfold bCycle
  rw [fromCoefficients_aCoefficient]

@[simp] theorem bCoefficient_bCycle {genus : Nat}
    (left right : Fin genus) :
    bCoefficient (bCycle left) right = if right = left then 1 else 0 := by
  unfold bCycle
  rw [fromCoefficients_bCoefficient]

/-- Finite integral intersection pairing in handle coordinates. -/
def intersection {genus : Nat}
    (left right : FirstHomology genus) : Int :=
  sumFin fun index =>
    aCoefficient left index * bCoefficient right index -
      bCoefficient left index * aCoefficient right index

theorem intersection_a_a {genus : Nat} (left right : Fin genus) :
    intersection (aCycle left) (aCycle right) = 0 := by
  unfold intersection
  rw [sumFin_congr (right := fun _ : Fin genus => (0 : Int)) (fun index => by
    rw [aCoefficient_aCycle, bCoefficient_aCycle, bCoefficient_aCycle]
    omega0)]
  exact sumFin_zero

theorem intersection_b_b {genus : Nat} (left right : Fin genus) :
    intersection (bCycle left) (bCycle right) = 0 := by
  unfold intersection
  rw [sumFin_congr (right := fun _ : Fin genus => (0 : Int)) (fun index => by
    rw [aCoefficient_bCycle, aCoefficient_bCycle, bCoefficient_bCycle]
    omega0)]
  exact sumFin_zero

theorem intersection_a_b {genus : Nat} (left right : Fin genus) :
    intersection (aCycle left) (bCycle right) =
      if left = right then 1 else 0 := by
  unfold intersection
  by_cases equal : left = right
  · subst right
    rw [if_pos rfl]
    rw [sumFin_congr
      (right := fun index : Fin genus => if index = left then 1 else 0)
      (fun index => by
        rw [aCoefficient_aCycle, bCoefficient_bCycle,
          bCoefficient_aCycle, aCoefficient_bCycle]
        by_cases indexEqual : index = left
        · rw [if_pos indexEqual]
          omega0
        · rw [if_neg indexEqual]
          omega0)]
    exact sumFin_ite_eq left (fun _ => (1 : Int))
  · rw [if_neg equal]
    rw [sumFin_congr (right := fun _ : Fin genus => (0 : Int))
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
    exact sumFin_zero

theorem intersection_skew {genus : Nat}
    (left right : FirstHomology genus) :
    intersection left right = -intersection right left := by
  unfold intersection
  rw [← sumFin_neg]
  apply sumFin_congr
  intro index
  ring1

theorem intersection_b_a {genus : Nat} (left right : Fin genus) :
    intersection (bCycle left) (aCycle right) =
      -(if left = right then 1 else 0) := by
  rw [intersection_skew, intersection_a_b]
  by_cases equal : left = right
  · rw [if_pos equal, if_pos equal.symm]
  · rw [if_neg equal, if_neg (fun reverse => equal reverse.symm)]

/-- The explicit basis and its finite intersection table. -/
structure SymplecticBasisCertificate (genus : Nat) : Type where
  reconstruct : forall chain : FirstHomology genus,
    fromCoefficients (aCoefficient chain) (bCoefficient chain) = chain
  a_a : forall left right : Fin genus,
    intersection (aCycle left) (aCycle right) = 0
  b_b : forall left right : Fin genus,
    intersection (bCycle left) (bCycle right) = 0
  a_b : forall left right : Fin genus,
    intersection (aCycle left) (bCycle right) =
    if left = right then 1 else 0

/-- Construct the symplectic homology basis for every finite genus. -/
def standardSymplecticBasis (genus : Nat) :
    SymplecticBasisCertificate genus where
  reconstruct := basis_reconstruct
  a_a := intersection_a_a
  b_b := intersection_b_b
  a_b := intersection_a_b

end CCL.Riemann.CellularHomology
