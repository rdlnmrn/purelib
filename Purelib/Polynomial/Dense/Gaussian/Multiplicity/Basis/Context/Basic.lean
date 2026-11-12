module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Map
public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive

import Purelib.Tactic.QuotientFreeOmega

open Purelib.Polynomial

section
public section

/-!
# Winding of finite weighted multiplicity products

This module connects the executable multiplicity polynomial from
`ConstructiveMultiplicity` to the finite box product formula.  Powers are
structural recursion over a displayed natural number; no root collection or
factor evaluation over a completed carrier is introduced.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic

/-! ## One focused entry of a weighted multiplicity list -/

set_option genInjectivity false in
/-- A displayed split of a finite positive multiplicity list around one
focused factor. -/
structure PositiveContext (entries : List Positive.PositiveEntry) where
  /-- The entries preceding the focused occurrence. -/ before : List
    Positive.PositiveEntry
  /-- The retained positive-degree entry at the focused position. -/ focus :
    Positive.PositiveEntry
  /-- The entries following the focused occurrence. -/ after : List
    Positive.PositiveEntry
  /-- The original list is exactly the prefix, focused occurrence and suffix in this order. -/ split : entries = before
    ++ focus :: after

constructive_injectivity PositiveContext

/-- Preserve a focused position while prepending one entry.

The new entry extends the retained prefix; the focus and suffix remain those of the original context. -/
@[expose] def PositiveContext.lift
    (head : Positive.PositiveEntry) {entries : List
      Positive.PositiveEntry}
    (context : PositiveContext entries) :
    PositiveContext (head :: entries) where
  before := head :: context.before
  focus := context.focus
  after := context.after
  split := by
    calc
      head :: entries =
          head :: (context.before ++ context.focus :: context.after) :=
        congrArg (head :: ·) context.split
      _ = (head :: context.before) ++ context.focus :: context.after := rfl

/-- Enumerate every focused position by structural recursion on the finite
entry list. -/
@[expose] def positiveContexts : (entries : List Positive.PositiveEntry) →
    List (PositiveContext entries)
  | [] => []
  | head :: entries =>
      { before := []
        focus := head
        after := entries
        split := rfl } ::
      (Basic.positiveContexts entries).map
        (PositiveContext.lift head)

/-- The explicit list of focused contexts has one element for each original entry. -/
theorem positiveContexts_length : ∀ entries : List Positive.PositiveEntry,
    (positiveContexts entries).length = entries.length
  | [] => rfl
  | head :: entries => by
      simp only [positiveContexts, List.length_cons,
        Data.List.Map.length_map,
        Basic.positiveContexts_length entries, -eq_self,
          -iff_self]
      rfl

/-- Lifting an original context preserves its focused entry throughout the same finite list. -/
private theorem lifted_focuses (head : Positive.PositiveEntry) {entries : List Positive.PositiveEntry} :
    (contexts : List (PositiveContext entries)) →
    ((contexts.map (PositiveContext.lift head)).map (fun context => context.focus)) =
      contexts.map (fun context => context.focus)
  | [] => rfl
  | context :: contexts => congrArg (List.cons context.focus) (lifted_focuses head contexts)

/-- The ordered focused entries of the complete original context enumeration are exactly the original entries. -/
theorem positiveContexts_focuses : (entries : List Positive.PositiveEntry) →
    (positiveContexts entries).map (fun context => context.focus) = entries
  | [] => rfl
  | head :: entries => by
      change head :: (((positiveContexts entries).map (PositiveContext.lift head)).map
        (fun context => context.focus)) = head :: entries
      rw [lifted_focuses head (positiveContexts entries), positiveContexts_focuses entries]

/-- Reading one original context focus gives its same original bounded entry occurrence. -/
theorem positiveContexts_get_focus (entries : List Positive.PositiveEntry)
    (index : Fin (positiveContexts entries).length) :
    ((positiveContexts entries).get index).focus =
      entries.get (Fin.cast (positiveContexts_length entries) index) := by
  have mappedBound : index.val < ((positiveContexts entries).map (fun context => context.focus)).length := by
    rw [positiveContexts_focuses]
    exact (Fin.cast (positiveContexts_length entries) index).isLt
  have mapped := Data.List.Map.getElem_map (fun context : PositiveContext entries => context.focus)
    (positiveContexts entries) index.val index.isLt mappedBound
  exact mapped.symm.trans
    (getElem_congr (positiveContexts_focuses entries) (Eq.refl index.val) mappedBound)

/-- The focused entry belongs to the original list certified by the context. -/
theorem PositiveContext.focus_mem
    {entries : List Positive.PositiveEntry} (context :
      PositiveContext entries) :
    context.focus ∈ entries := by
  have member : context.focus ∈
      context.before ++ context.focus :: context.after :=
    List.mem_append_right _ List.mem_cons_self
  exact (congrArg (fun values : List Positive.PositiveEntry =>
    context.focus ∈ values) context.split).symm.mp member

end Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic

end

section
public section

/-!
# Constructive signed multiplicity sites

A squarefree factor track represents one geometric zero location.  This
module attaches the factor's complete finite multiplicity while protecting
the same box from both the remaining same-side factors and the opposite
rational-function cofactor.  One minimum of two positive rational requests
provides both protections simultaneously.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic
end Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic

end

section
public section

/-!
# Total finite rational-function zero and pole sites

This module packages the signed multiplicity theorem over every finite
degree branch.  Linear factors return only exact displayed Gaussian-rational
zeros or poles.  Higher factors retain shrinking box tracks.  Constants have
no finite sites, and the identically-zero numerator has its own constructor.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic
end Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic

end
