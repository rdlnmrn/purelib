module

public import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Riemann.Topology.SquareRootContinuationChain

/-! # Ordered concatenation of retained open Owner paths

A nonempty finite family retains its separate starting and finishing
Owners. The structural fold inserts only the supplied interior links,
leaving the final/first closing join to the original closing operation.
-/

public section

namespace Purelib.Riemann.Paths.OwnerTracePath.OwnerPath

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {polynomial : CoefficientPolynomial}

/-- The ordered given path vertices with one supplied handoff point between consecutive paths.

The final path contributes its own vertices only. In particular this list
contains no separately constructed final/first closing arc.
-/
def interleaveVertices : (size : Nat) → (Fin (size + 1) → List Canonical) →
    (Fin size → Canonical) → List Canonical
  | 0, vertices, _handoffs => vertices 0
  | size + 1, vertices, handoffs =>
      vertices 0 ++ handoffs 0 ::
        interleaveVertices size (fun index => vertices index.succ) (fun index => handoffs index.succ)

/-- Concatenate the SAME nonempty path family using its supplied interior Owner links.

Every supplied path is consumed in literal occurrence order. Each of the
exactly `size` interior links is inserted once; no endpoint comparison,
root tail, join or closing link is produced by this structural fold.
-/
def concatenate : (size : Nat) → (starts finishes : Fin (size + 1) → Canonical) →
    (firsts : (index : Fin (size + 1)) → Owner (polynomial.eval (starts index))) →
    (lasts : (index : Fin (size + 1)) → Owner (polynomial.eval (finishes index))) →
    ((index : Fin (size + 1)) → OwnerPath polynomial (starts index) (firsts index)
      (finishes index) (lasts index)) →
    ((index : Fin size) → OwnerLink polynomial (finishes index.castSucc) (starts index.succ)
      (lasts index.castSucc) (firsts index.succ)) →
    OwnerPath polynomial (starts 0) (firsts 0) (finishes (Fin.last size)) (lasts (Fin.last size))
  | 0, _starts, _finishes, _firsts, _lasts, paths, _links => paths 0
  | size + 1, starts, finishes, firsts, lasts, paths, links =>
      (paths 0).append (.cons (links 0)
        (concatenate size (fun index => starts index.succ) (fun index => finishes index.succ)
          (fun index => firsts index.succ) (fun index => lasts index.succ)
          (fun index => paths index.succ) (fun index => links index.succ)))

/-- A singleton concatenation retains the SAME supplied open path without adding a link. -/
theorem concatenate_zero (starts finishes : Fin 1 → Canonical)
    (firsts : (index : Fin 1) → Owner (polynomial.eval (starts index)))
    (lasts : (index : Fin 1) → Owner (polynomial.eval (finishes index)))
    (paths : (index : Fin 1) → OwnerPath polynomial (starts index) (firsts index)
      (finishes index) (lasts index))
    (links : (index : Fin 0) → OwnerLink polynomial (finishes index.castSucc) (starts index.succ)
      (lasts index.castSucc) (firsts index.succ)) :
    concatenate 0 starts finishes firsts lasts paths links = paths 0 := by rfl

/-- The original successor concatenation appends its SAME first path, supplied link and exact original tail. -/
theorem concatenate_succ (size : Nat) (starts finishes : Fin (size + 1 + 1) → Canonical)
    (firsts : (index : Fin (size + 1 + 1)) → Owner (polynomial.eval (starts index)))
    (lasts : (index : Fin (size + 1 + 1)) → Owner (polynomial.eval (finishes index)))
    (paths : (index : Fin (size + 1 + 1)) → OwnerPath polynomial (starts index) (firsts index)
      (finishes index) (lasts index))
    (links : (index : Fin (size + 1)) → OwnerLink polynomial (finishes index.castSucc) (starts index.succ)
      (lasts index.castSucc) (firsts index.succ)) :
    concatenate (size + 1) starts finishes firsts lasts paths links =
      (paths 0).append (.cons (links 0)
        (concatenate size (fun index => starts index.succ) (fun index => finishes index.succ)
          (fun index => firsts index.succ) (fun index => lasts index.succ)
          (fun index => paths index.succ) (fun index => links index.succ))) := by rfl

/-- Pointwise block-vertex readbacks preserve the exact ordered concatenation vertex word. -/
theorem interleaveVertices_congr : (size : Nat) → (first last : Fin (size + 1) → List Canonical) →
    (handoffs : Fin size → Canonical) → (∀ index, first index = last index) →
    interleaveVertices size first handoffs = interleaveVertices size last handoffs
  | 0, _first, _last, _handoffs, same => same 0
  | size + 1, first, last, handoffs, same =>
      congrArg₂ List.append (same 0) (congrArg (List.cons (handoffs 0))
        (interleaveVertices_congr size (fun index => first index.succ) (fun index => last index.succ)
          (fun index => handoffs index.succ) (fun index => same index.succ)))

/-- Concatenation preserves every path vertex and every supplied interior-link contribution in order. -/
theorem concatenate_vertices : (size : Nat) → (starts finishes : Fin (size + 1) → Canonical) →
    (firsts : (index : Fin (size + 1)) → Owner (polynomial.eval (starts index))) →
    (lasts : (index : Fin (size + 1)) → Owner (polynomial.eval (finishes index))) →
    (paths : (index : Fin (size + 1)) → OwnerPath polynomial (starts index) (firsts index)
      (finishes index) (lasts index)) →
    (links : (index : Fin size) → OwnerLink polynomial (finishes index.castSucc) (starts index.succ)
      (lasts index.castSucc) (firsts index.succ)) →
    (concatenate size starts finishes firsts lasts paths links).vertices =
      interleaveVertices size (fun index => (paths index).vertices) (fun index => starts index.succ)
  | 0, _, _, _, _, _, _ => rfl
  | size + 1, starts, finishes, firsts, lasts, paths, links => by
      change ((paths 0).append (.cons (links 0)
        (concatenate size (fun index => starts index.succ) (fun index => finishes index.succ)
          (fun index => firsts index.succ) (fun index => lasts index.succ)
          (fun index => paths index.succ) (fun index => links index.succ)))).vertices = _
      rewrite [append_vertices]
      change (paths 0).vertices ++ starts (Fin.succ 0) :: _ = _
      rewrite [concatenate_vertices size (fun index => starts index.succ) (fun index => finishes index.succ)
        (fun index => firsts index.succ) (fun index => lasts index.succ)
        (fun index => paths index.succ) (fun index => links index.succ)]
      rfl

end Purelib.Riemann.Paths.OwnerTracePath.OwnerPath

end
