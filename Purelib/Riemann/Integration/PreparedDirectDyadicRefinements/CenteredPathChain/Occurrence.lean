module

public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain

/-! # Literal lifted endpoint incidence at arbitrary centered-chain occurrences

The original whole centered chain supplies every physical endpoint and sheet.
Reading an arbitrary adjacent occurrence follows only its stored prefix and
tail, without replacing the parent list, prepared edge or Owner indices.
-/

public section

namespace Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}

/-- The actual next parent's lifted start equals the actual current parent's lifted finish at any retained occurrence.

The full original physical chain, its two endpoint indices and ordered
parent list remain inputs. Structural recursion projects only the actual
stored tail and specializes its original start_eq law.
-/
theorem adjacent_eq : (parents : List (CenteredEdge curve differential)) →
    {start finish : LiftedPoint 2} → CenteredPathChain parents (start := start) (finish := finish) →
    (index : Fin parents.length) → (later : index.val + 1 < parents.length) →
    let current := parents[index.val]'index.isLt
    let next := parents[index.val + 1]'later
    (⟨next.edge.segment.pointAt next.edge.left.parameter, next.edge.sheet⟩ : LiftedPoint 2) =
      ⟨current.edge.segment.pointAt current.edge.request.endpoint.parameter, current.edge.sheet⟩
  | [], _, _, _, index, _ => Fin.elim0 index
  | _ :: remaining, _, _, chain, ⟨0, _⟩, later =>
      match remaining with
      | [] => False.elim (Nat.lt_irrefl 1 later)
      | _next :: _tail => chain.remaining.start_eq
  | _ :: remaining, _, _, chain, ⟨index + 1, bounded⟩, later =>
      adjacent_eq remaining chain.remaining ⟨index, Nat.lt_of_succ_lt_succ bounded⟩
        (Nat.lt_of_succ_lt_succ later)
termination_by structural parents => parents

/-- Read the actual lifted source point and original sheet at the certified first parent occurrence. -/
theorem startAt_eq : (parents : List (CenteredEdge curve differential)) →
    {start finish : LiftedPoint 2} → CenteredPathChain parents (start := start) (finish := finish) →
    (index : Fin parents.length) → index.val = 0 →
    let parent := parents[index.val]'index.isLt
    (⟨parent.edge.segment.pointAt parent.edge.left.parameter, parent.edge.sheet⟩ : LiftedPoint 2) = start
  | [], _, _, _, index, _ => Fin.elim0 index
  | _ :: _, _, _, chain, ⟨index, _⟩, atFirst => by
      cases atFirst
      exact chain.start_eq

/-- Read the actual lifted finish point at the last parent after any retained original prefix.

Only the same original centered-chain tails are read. The last-index
identity determines the terminal occurrence, and empty_eq supplies the
original physical endpoint and sheet without changing any parent or Owner.
-/
theorem finishAt_eq : (parents : List (CenteredEdge curve differential)) →
    {start finish : LiftedPoint 2} → CenteredPathChain parents (start := start) (finish := finish) →
    (index : Fin parents.length) → index.val + 1 = parents.length →
    let parent := parents[index.val]'index.isLt
    (⟨parent.edge.segment.pointAt parent.edge.request.endpoint.parameter, parent.edge.sheet⟩ : LiftedPoint 2) = finish
  | [], _, _, _, index, _ => Fin.elim0 index
  | _ :: remaining, _, _, chain, ⟨0, _⟩, atLast =>
      match remaining with
      | [] => chain.remaining.empty_eq
      | _ :: _ => False.elim (Nat.noConfusion (Nat.succ.inj atLast))
  | _ :: remaining, _, _, chain, ⟨index + 1, bounded⟩, atLast =>
      finishAt_eq remaining chain.remaining ⟨index, Nat.lt_of_succ_lt_succ bounded⟩ (Nat.succ.inj atLast)
termination_by structural parents => parents

end Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain

end
