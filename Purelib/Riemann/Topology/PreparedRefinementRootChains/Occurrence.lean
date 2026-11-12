module

public import Purelib.Riemann.Topology.PreparedRefinementRootChains

/-! # Adjacent original query comparisons at arbitrary retained root-chain occurrences

Only original RootChain.remaining projections are consumed. An arbitrary
bounded child occurrence follows the unchanged actual prefix, and its
successor comparison is the SAME retained nextEquivalent witness. No name,
root query, continuation or approximation observation is constructed.
-/

public section

namespace Purelib.Riemann.Topology.PreparedRefinementRootChains.RootChain

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}

/-- Read the exact original adjacent finish-to-start comparison after any literal retained prefix.

The bounded occurrence and its actual successor bound determine the two
original centered parents. Structural recursion reads only the stored root
tail; no replacement chain or desired signed relation is supplied or built.
-/
def adjacentEquivalent : (parents : List (CenteredEdge curve differential)) →
    {first last : Named} → RootChain parents first last →
    (index : Fin parents.length) → (later : index.val + 1 < parents.length) →
    let current := parents[index.val]'index.isLt
    let next := parents[index.val + 1]'later
    NamedEquivalent (current.edge.rootName 1 (of_decide_eq_true rfl))
      (next.edge.rootName 0 next.edge.baseInside)
  | [], _, _, _, index, _ => Fin.elim0 index
  | _ :: remaining, _, _, roots, ⟨0, _⟩, later =>
      match remaining with
      | [] => False.elim (Nat.lt_irrefl 1 later)
      | _next :: _tail => roots.nextEquivalent
  | _ :: remaining, _, _, roots, ⟨index + 1, bounded⟩, later =>
      adjacentEquivalent remaining roots.remaining ⟨index, Nat.lt_of_succ_lt_succ bounded⟩
        (Nat.lt_of_succ_lt_succ later)
termination_by structural parents => parents

/-- At the first two retained parents the readback is the identical original nextEquivalent witness. -/
theorem adjacentEquivalent_zero {parent next : CenteredEdge curve differential}
    {remaining : List (CenteredEdge curve differential)} {first last : Named}
    (roots : RootChain (parent :: next :: remaining) first last) :
    adjacentEquivalent (parent :: next :: remaining) roots 0
      (Nat.succ_lt_succ (Nat.zero_lt_succ remaining.length)) = roots.nextEquivalent := by
  unfold adjacentEquivalent
  rfl

/-- Read the unchanged original incoming query comparison at its certified first list occurrence. -/
def startEquivalent : (parents : List (CenteredEdge curve differential)) →
    {first last : Named} → RootChain parents first last →
    (index : Fin parents.length) → index.val = 0 →
    NamedEquivalent first ((parents[index.val]'index.isLt).edge.rootName 0
      (parents[index.val]'index.isLt).edge.baseInside)
  | [], _, _, _, index, _ => Fin.elim0 index
  | _ :: _, _, _, roots, ⟨index, _⟩, atFirst => by
      cases atFirst
      exact roots.firstEquivalent

/-- Read the exact retained terminal query comparison after any literal original prefix.

The actual bounded index and last-index equality identify the original last
parent. Recursion follows only RootChain.remaining and returns the original
finishEquivalent witness, with the literal terminal name unchanged.
-/
def terminalEquivalent : (parents : List (CenteredEdge curve differential)) →
    {first last : Named} → RootChain parents first last →
    (index : Fin parents.length) → index.val + 1 = parents.length →
    NamedEquivalent ((parents[index.val]'index.isLt).edge.rootName 1 (of_decide_eq_true rfl)) last
  | [], _, _, _, index, _ => Fin.elim0 index
  | _ :: remaining, _, _, roots, ⟨0, _⟩, atLast =>
      match remaining with
      | [] => roots.finishEquivalent
      | _ :: _ => False.elim (Nat.noConfusion (Nat.succ.inj atLast))
  | _ :: remaining, _, _, roots, ⟨index + 1, bounded⟩, atLast =>
      terminalEquivalent remaining roots.remaining ⟨index, Nat.lt_of_succ_lt_succ bounded⟩ (Nat.succ.inj atLast)
termination_by structural parents => parents

/-- A singleton terminal readback is the SAME complete original finishing comparison witness. -/
theorem terminalEquivalent_singleton {parent : CenteredEdge curve differential} {first last : Named}
    (roots : RootChain [parent] first last) :
    terminalEquivalent [parent] roots 0 rfl = roots.finishEquivalent := by
  unfold terminalEquivalent
  rfl

end Purelib.Riemann.Topology.PreparedRefinementRootChains.RootChain

end
