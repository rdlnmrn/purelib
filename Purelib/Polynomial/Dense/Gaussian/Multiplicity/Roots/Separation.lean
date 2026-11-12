module

public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Images.Separation
import Purelib.Data.List.OfFn.Nodup
import Purelib.Data.List.Nodup
import Purelib.Data.List.Pairwise
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Automatic separation of original multiplicity-factor root images

The same complete original context enumeration supplies every squarefree
first-jet cache and every distinct-context coprimality cache. All root-pair
cofactors belong to those retained final images and original bounded indices.
-/

public section

namespace Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side (PositiveSideInput)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic (PositiveContext)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity
open Purelib.Data.List

variable {source opposite : DensePolynomial Canonical} {input : PositiveSideInput source opposite}

namespace Stages.Prepared

/-- The cached original complete context-index enumeration has no repeated occurrence. -/
theorem indices_nodup (prepared : Prepared input) : prepared.indices.Nodup := by
  rewrite [prepared.indices_eq]
  exact OfFn.Nodup.nodup_ofFn_of_injective (fun _ _ equal => equal)

/-- Equal retained context-index readings identify the same original stage occurrence. -/
theorem index_injective (prepared : Prepared input) :
    Function.Injective (fun position : Fin prepared.indices.length => prepared.indices.get position) := by
  intro first second equal
  exact Fin.ext (Nodup.getElem_index_injective prepared.indices_nodup first.isLt second.isLt equal)

/-- Distinct cached context occurrences retain their same original positive-factor coprimality relation. -/
theorem context_relation (prepared : Prepared input) (first second : Fin prepared.indices.length)
    (different : first ≠ second) :
    CoprimeRelation (prepared.contexts.get (prepared.indices.get first)).focus.part
      (prepared.contexts.get (prepared.indices.get second)).focus.part := by
  let left := prepared.indices.get first
  let right := prepared.indices.get second
  have distinct : left ≠ right := fun equal => different (prepared.index_injective equal)
  have pairwise : prepared.contexts.Pairwise (fun left right => CoprimeRelation left.focus.part right.focus.part) :=
    prepared.contexts_eq.symm ▸ input.contexts_pairwise
  by_cases ordered : left.val < right.val
  · exact Pairwise.pairwise_get_of_val_lt pairwise left right ordered
  · have valuesDifferent : left.val ≠ right.val := fun equal => distinct (Fin.ext equal)
    have reversed : right.val < left.val :=
      Nat.lt_of_le_of_ne (Nat.le_of_not_gt ordered) valuesDifferent.symm
    exact CoprimeRelation.coprimeRelation_symm (Pairwise.pairwise_get_of_val_lt pairwise right left reversed)

/-- Compute the original certificate directly from the same cached focused parts.

The original side input supplies its pairwise relation proof. The original
certificate constructor consumes the already retained contexts, so their
complete multiplicity preprocessing is not replayed by a root-pair request.
-/
@[expose] def contextCoprime (prepared : Prepared input) (first second : Fin prepared.indices.length)
    (different : first ≠ second) :
    Gaussian.Coprime.Basic.CoprimeCertificate (factor prepared.contexts (prepared.indices.get first))
      (factor prepared.contexts (prepared.indices.get second)) :=
  input.focusCoprimeOfRelation (prepared.contexts.get (prepared.indices.get first))
    (prepared.contexts.get (prepared.indices.get second)) (context_relation prepared first second different)

end Stages.Prepared

set_option genInjectivity false in
/-- The same original context occurrence or its actual original cross-factor separation cache. -/
inductive FactorPair (prepared : Stages.Prepared input) (images : Stages.Images prepared.stages)
    (first second : Fin prepared.indices.length) where
  /-- The same original factor occurrence uses its retained squarefree first-jet cache. -/
  | diagonal (equal : first = second)
  /-- Distinct original factor occurrences retain their actual original coprimality and root-pair caches. -/
  | separated (different : first ≠ second) (cross : Stages.Images.Cross prepared.stages images first second)

constructive_injectivity FactorPair

set_option genInjectivity false in
/-- Complete actual original factor towers, images and separation caches for one original positive side input. -/
structure Separation (input : PositiveSideInput source opposite) where
  /-- The same complete original contexts and once-per-factor adjunction towers. -/
  prepared : Stages.Prepared input
  /-- The original towers' once-mapped final roots and original source multiplicities. -/
  images : Stages.Images prepared.stages
  /-- One retained original squarefree first-jet and within-factor pair cache per original context. -/
  jets : DependentProduct prepared.indices (fun position => Stages.Images.FirstJets prepared.stages images position)
  /-- One retained original coprimality and cross-factor pair cache per distinct original context pair. -/
  pairs : DependentProduct prepared.indices (fun first =>
    DependentProduct prepared.indices (fun second => FactorPair prepared images first second))

constructive_injectivity Separation

namespace Separation

/-- Split each original squarefree factor once and retain all actual root-difference construction work.

The same original context caches supply their original squarefree and
cross-factor certificates. Every right cofactor is mapped once per certificate,
its inverse readings once per original root, and its difference cofactors once
per original bounded root pair. Multiplicity does not repeat any splitting.
-/
@[expose] def prepare (input : PositiveSideInput source opposite) : Separation input :=
  let prepared := Stages.prepareInput input
  let images := Stages.Images.prepare prepared.stages
  let jets := DependentProduct.ofFn prepared.indices fun position =>
    Stages.Images.FirstJets.prepare prepared.stages images rfl (fun _ _ equal => equal) rfl
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) position
  let pairs := DependentProduct.ofFn prepared.indices fun first =>
    DependentProduct.ofFn prepared.indices fun second =>
      if equal : first = second then FactorPair.diagonal equal
      else
        let different := equal
        let certificate := prepared.contextCoprime first second different
        FactorPair.separated different (Stages.Images.Cross.prepare prepared.stages images rfl
          (fun _ _ equal => equal) rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) first second certificate)
  { prepared := prepared, images := images, jets := jets, pairs := pairs }

end Separation

end Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots

end
