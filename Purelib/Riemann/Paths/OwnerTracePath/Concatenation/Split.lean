module

public import Purelib.Riemann.Paths.OwnerTracePath.Concatenation
public import Purelib.Riemann.Paths.OwnerTracePath.Split.Append
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.OwnerTracePath.Split
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Riemann.Topology.SquareRootContinuationChain

/-! # Actual retained splits through an ordered path concatenation

The scalar prefix length reads the supplied old path lengths and counts
each actual interior link. Splitting reads the GIVEN whole concatenated
path once; whole construction equations are used only in the ownership
proof, never to rebuild a tail path for the operation.
-/

public section

namespace Purelib.Riemann.Paths.OwnerTracePath.OwnerPath

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {polynomial : CoefficientPolynomial}

/-- Count exactly the original vertices and single handoffs preceding one bounded path occurrence. -/
def precedingVertices : (size : Nat) → (Fin (size + 1) → Nat) → Fin (size + 1) → Nat
  | 0, _lengths, _index => 0
  | size + 1, lengths, index =>
      Fin.cases 0 (fun index => lengths 0 + 1 + precedingVertices size
        (fun index => lengths index.succ) index) index

/-- Split the GIVEN whole path at the selected original block split boundary.

Only the existing splitAt reader executes. The supplied whole-path factory
retains the exact concat owner and actual paths/links; no concatenation,
source, root, query, tail acquisition or endpoint comparison is replayed.
-/
def concatenateSplit (size : Nat) (starts finishes : Fin (size + 1) → Canonical)
    (firsts : (index : Fin (size + 1)) → Owner (polynomial.eval (starts index)))
    (lasts : (index : Fin (size + 1)) → Owner (polynomial.eval (finishes index)))
    (paths : (index : Fin (size + 1)) → OwnerPath polynomial (starts index) (firsts index)
      (finishes index) (lasts index))
    (links : (index : Fin size) → OwnerLink polynomial (finishes index.castSucc) (starts index.succ)
      (lasts index.castSucc) (firsts index.succ))
    (whole : {path : OwnerPath polynomial (starts 0) (firsts 0)
        (finishes (Fin.last size)) (lasts (Fin.last size)) //
      path = concatenate size starts finishes firsts lasts paths links})
    (index : Fin (size + 1)) (divided : Split (paths index)) : Split whole.val :=
  whole.val.splitAt (precedingVertices size (fun position => (paths position).vertices.length) index +
    divided.initial.vertices.length)

/-- The actual whole-path split preserves the SAME selected point and complete Owner of the supplied block split. -/
theorem concatenateSplit_vertex : (size : Nat) → (starts finishes : Fin (size + 1) → Canonical) →
    (firsts : (index : Fin (size + 1)) → Owner (polynomial.eval (starts index))) →
    (lasts : (index : Fin (size + 1)) → Owner (polynomial.eval (finishes index))) →
    (paths : (index : Fin (size + 1)) → OwnerPath polynomial (starts index) (firsts index)
      (finishes index) (lasts index)) →
    (links : (index : Fin size) → OwnerLink polynomial (finishes index.castSucc) (starts index.succ)
      (lasts index.castSucc) (firsts index.succ)) →
    (whole : {path : OwnerPath polynomial (starts 0) (firsts 0)
        (finishes (Fin.last size)) (lasts (Fin.last size)) //
      path = concatenate size starts finishes firsts lasts paths links}) →
    (index : Fin (size + 1)) → (divided : Split (paths index)) →
    (concatenateSplit size starts finishes firsts lasts paths links whole index divided).vertex = divided.vertex
  | 0, starts, finishes, firsts, lasts, paths, links, whole, index, divided =>
      Fin.cases
        (motive := fun index => (divided : Split (paths index)) →
          (concatenateSplit 0 starts finishes firsts lasts paths links whole index divided).vertex = divided.vertex)
        (fun divided => by
          change (splitAt (0 + divided.initial.vertices.length) whole.val).vertex = divided.vertex
          rewrite [Nat.zero_add divided.initial.vertices.length]
          have factory := whole.property.trans
            ((concatenate_zero starts finishes firsts lasts paths links).trans divided.append_eq.symm)
          have selected := splitAt_suffix divided.initial.vertices.length whole.val divided.initial divided.suffix.path
            rfl factory
          exact congrArg (fun suffix : Suffix (lasts (Fin.last 0)) => (⟨suffix.point, suffix.owner⟩ :
            Σ point : Canonical, Owner (polynomial.eval point))) selected)
        (fun index => Fin.elim0 index) index divided
  | size + 1, starts, finishes, firsts, lasts, paths, links, whole, index, divided =>
      Fin.cases
        (motive := fun index => (divided : Split (paths index)) →
          (concatenateSplit (size + 1) starts finishes firsts lasts paths links whole index divided).vertex =
            divided.vertex)
        (fun divided => by
          change (splitAt (0 + divided.initial.vertices.length) whole.val).vertex = divided.vertex
          rewrite [Nat.zero_add divided.initial.vertices.length]
          let rest := OwnerPath.cons (links 0)
            (concatenate size (fun index => starts index.succ) (fun index => finishes index.succ)
              (fun index => firsts index.succ) (fun index => lasts index.succ)
              (fun index => paths index.succ) (fun index => links index.succ))
          have factory : whole.val = divided.initial.append (divided.suffix.path.append rest) :=
            whole.property.trans ((concatenate_succ size starts finishes firsts lasts paths links).trans
              ((congrArg (fun first => first.append rest) divided.append_eq.symm).trans
                (append_assoc divided.initial divided.suffix.path rest)))
          have selected := splitAt_suffix divided.initial.vertices.length whole.val divided.initial
            (divided.suffix.path.append rest) rfl factory
          exact congrArg (fun suffix : Suffix (lasts (Fin.last (size + 1))) => (⟨suffix.point, suffix.owner⟩ :
            Σ point : Canonical, Owner (polynomial.eval point))) selected)
        (fun index divided => by
          let rest := concatenate size (fun index => starts index.succ) (fun index => finishes index.succ)
            (fun index => firsts index.succ) (fun index => lasts index.succ)
            (fun index => paths index.succ) (fun index => links index.succ)
          let count := precedingVertices size (fun position => (paths position.succ).vertices.length) index +
            divided.initial.vertices.length
          have countEq : (paths 0).vertices.length + 1 +
              precedingVertices size (fun position => (paths position.succ).vertices.length) index +
              divided.initial.vertices.length = (paths 0).vertices.length + (count + 1) := by
            unfold count
            exact (Nat.add_assoc ((paths 0).vertices.length + 1)
              (precedingVertices size (fun position => (paths position.succ).vertices.length) index)
              divided.initial.vertices.length).trans
              ((Nat.add_assoc (paths 0).vertices.length 1
                (precedingVertices size (fun position => (paths position.succ).vertices.length) index +
                  divided.initial.vertices.length)).trans
                (congrArg (Nat.add (paths 0).vertices.length) (Nat.add_comm 1 _)))
          have factory := whole.property.trans (concatenate_succ size starts finishes firsts lasts paths links)
          have actual := congrArg (fun path => (splitAt
            ((paths 0).vertices.length + (count + 1)) path).vertex) factory
          have first := congrArg Split.vertex (splitAt_afterPrefix (paths 0) (.cons (links 0) rest) (count + 1))
          have second := Split.prependPath_vertex (paths 0) (.cons (links 0) rest)
            (splitAt (count + 1) (.cons (links 0) rest))
          have last : (splitAt (count + 1) (.cons (links 0) rest)).vertex = (splitAt count rest).vertex :=
            split_prepend_vertex (links 0) rest (splitAt count rest)
          have tail := concatenateSplit_vertex size (fun index => starts index.succ)
            (fun index => finishes index.succ) (fun index => firsts index.succ) (fun index => lasts index.succ)
            (fun index => paths index.succ) (fun index => links index.succ) ⟨rest, rfl⟩ index divided
          change (splitAt ((paths 0).vertices.length + 1 +
            precedingVertices size (fun position => (paths position.succ).vertices.length) index +
              divided.initial.vertices.length) whole.val).vertex = _
          rewrite [countEq]
          exact actual.trans (first.trans (second.trans (last.trans tail)))) index divided

end Purelib.Riemann.Paths.OwnerTracePath.OwnerPath

end
