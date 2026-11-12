module

public import Purelib.Approximation.Gaussian.Acquisition.Expression.Normalization
public import Purelib.Polynomial.Multivariate.Gaussian.Renaming
public import Purelib.Data.Vector.Basic
import Purelib.Approximation.Gaussian.Equivalence
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Cached alignment of original expression bindings

An alignment stores the actual target position of each original retained leaf.
Its full source-key equations authenticate channel identity. Rebasing reads
that finite position cache and the original computed polynomial coefficients.
-/

public section

namespace Purelib.Approximation.Gaussian.Acquisition.Expression.Basic

open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib
open Purelib.Polynomial

namespace Binding

/-- Reading a bounded retained table position gives an actual original occurrence of its source leaf. -/
theorem present_read {arity : Nat} {environment : Fin arity → Annotated}
    (bindings : List (Binding environment)) (index : Fin bindings.length) :
    Present (read bindings index).leaf bindings := by
  induction bindings with
  | nil => exact Fin.elim0 index
  | cons first remaining ih =>
      refine Fin.cases (Or.inl rfl) (fun tailIndex => Or.inr (ih tailIndex)) index

set_option genInjectivity false in
/-- Cached bounded target positions with the exact original leaf identity of every source occurrence. -/
structure Alignment {arity : Nat} {environment : Fin arity → Annotated}
    (source destination : List (Binding environment)) where
  /-- Each source occurrence's actual stored bounded destination position. -/
  positions : Data.Vector (Fin destination.length) source.length
  /-- Position lookup preserves the entire original source key, including atom indices and root labels. -/
  leaf_eq : ∀ index, (read source index).leaf = (read destination (positions.get index)).leaf

constructive_injectivity Alignment

namespace Alignment

variable {arity : Nat} {environment : Fin arity → Annotated}

/-- Materialize each source occurrence's checked destination position once from finite key inclusion. -/
@[expose] def ofInclusion (source destination : List (Binding environment))
    (included : ∀ leaf, Present leaf source → Present leaf destination) : Alignment source destination :=
  let selection := fun index : Fin source.length =>
    locate (read source index).leaf destination (included _ (present_read source index))
  let positions := Data.Vector.Basic.vectorOfFn (fun index => (selection index).val)
  { positions := positions
    leaf_eq := by
      intro index
      have position_eq : positions.get index = (selection index).val :=
        Data.Vector.Basic.vectorOfFn_apply (fun next => (selection next).val) index
      rewrite [position_eq]
      exact (selection index).property.symm }

/-- Exact source-key alignment identifies the full actual retained annotations at its cached positions. -/
theorem annotation_eq {source destination : List (Binding environment)} (alignment : Alignment source destination)
    (index : Fin source.length) :
    (read source index).annotation = (read destination (alignment.positions.get index)).annotation :=
  (read source index).annotation_eq.trans
    ((congrArg (Leaf.annotation environment) (alignment.leaf_eq index)).trans
      (read destination (alignment.positions.get index)).annotation_eq.symm)

/-- Aligned positions read the exact original channels from their actual cached annotations. -/
theorem channel_eq {source destination : List (Binding environment)} (alignment : Alignment source destination)
    (index : Fin source.length) : channels source index = channels destination (alignment.positions.get index) :=
  congrArg Annotated.channel (alignment.annotation_eq index)

/-- Read a comparison of the actual aligned original channels without running either leaf producer again. -/
def equivalent {source destination : List (Binding environment)} (alignment : Alignment source destination)
    (index : Fin source.length) :
    NamedEquivalent (channels source index).name (channels destination (alignment.positions.get index)).name := by
  rewrite [alignment.channel_eq index]
  exact NamedEquivalent.refl _

end Alignment

end Binding

namespace Normalized

/-- Rebase an original cached coefficient form using actual stored alignment positions and channel comparisons. -/
@[expose] def rebind {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    (normalized : Normalized environment expression) (destination : List (Binding environment))
    (alignment : Binding.Alignment normalized.bindings destination) :
    Multivariate.Gaussian.Normalized (Binding.channels destination) normalized.compiled.annotation.channel :=
  normalized.polynomial.rename (Binding.channels destination) alignment.positions.get alignment.equivalent

end Normalized

end Purelib.Approximation.Gaussian.Acquisition.Expression.Basic

end
