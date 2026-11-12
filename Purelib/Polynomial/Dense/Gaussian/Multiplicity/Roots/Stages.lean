module

public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side
public import Purelib.Polynomial.Dense.Roots.Tower.Factorization
public import Purelib.Polynomial.Dense.Map.Ring
public import Init.Data.List.OfFn
import Purelib.Data.Gaussian.Field
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Sequential adjunctions of original multiplicity factors

Every displayed original context supplies its same squarefree factor once.
The next stage maps the next original factor through the preceding retained
scalar embeddings, so all factor roots belong to one common final algebra.
The source multiplicities remain on their original contexts throughout.
-/

public section

namespace Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive (PositiveEntry)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic (PositiveContext)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side (PositiveSideInput)

universe u

variable {entries : List PositiveEntry}

/-- Read the same original squarefree factor at a retained bounded context index. -/
abbrev factor (contexts : List (PositiveContext entries)) (index : Fin contexts.length) :
    DensePolynomial Canonical :=
  (contexts.get index).focus.part.polynomial

set_option genInjectivity false in
/-- A source-indexed chain of original factor towers in successive coefficient algebras.

The cached mapped factor retains its exact original context and coefficient
map. Each tail uses the same preceding tower's final scalar embedding. The
original factor degrees are retained independently of their multiplicities.
-/
inductive Stages (contexts : List (PositiveContext entries)) :
    List (Fin contexts.length) → (K : Type u) → CommRing K → DecidableEq K → (Canonical → K) → Type (u + 1)
  /-- No original factor remains to be adjoined. -/
  | done {K : Type u} [ring : CommRing K] [equality : DecidableEq K] {function : Canonical → K} :
      Stages contexts [] K ring equality function
  /-- Split one same original squarefree factor, then continue in its actual final algebra. -/
  | adjoin {K : Type u} [ring : CommRing K] [equality : DecidableEq K]
      {function : Canonical → K} {index : Fin contexts.length} {indices : List (Fin contexts.length)}
      (mapped : DensePolynomial K)
      (mapped_eq : mapped = Map.map function (factor contexts index))
      (normalized : mapped.normalize = mapped)
      (degree_eq : mapped.natDegree = (factor contexts index).natDegree)
      (tower : Dense.Roots.Tower K ring equality mapped)
      (roots : List (Dense.Roots.Block tower.Scalar))
      (roots_eq : roots = tower.blocks)
      (remaining : Stages contexts indices tower.Scalar inferInstance inferInstance
        (fun value => tower.embed (function value))) :
      Stages contexts (index :: indices) K ring equality function

constructive_injectivity Stages

namespace Stages

/-- The final original coefficient carrier of all retained factor towers. -/
@[expose] def Scalar {contexts : List (PositiveContext entries)}
    {indices : List (Fin contexts.length)} {K : Type u} {ring : CommRing K} {equality : DecidableEq K}
    {function : Canonical → K} (stages : Stages contexts indices K ring equality function) : Type u :=
  match indices, stages with
  | [], .done => K
  | _ :: _, .adjoin _ _ _ _ _ _ _ remaining => Scalar remaining

/-- Retain the same actual ring dictionary of the last original factor stage. -/
@[expose, implicit_reducible] def scalarRing {contexts : List (PositiveContext entries)}
    {indices : List (Fin contexts.length)} {K : Type u} {ring : CommRing K} {equality : DecidableEq K}
    {function : Canonical → K} (stages : Stages contexts indices K ring equality function) : CommRing stages.Scalar :=
  match indices, stages with
  | [], .done => ring
  | _ :: _, .adjoin _ _ _ _ _ _ _ remaining => scalarRing remaining

/-- The final operations come from the same retained original coefficient stage. -/
instance instCommRingScalar {contexts : List (PositiveContext entries)}
    {indices : List (Fin contexts.length)} {K : Type u} {ring : CommRing K} {equality : DecidableEq K}
    {function : Canonical → K} (stages : Stages contexts indices K ring equality function) : CommRing stages.Scalar :=
  stages.scalarRing

/-- Retain the final original equality procedure without a field assumption. -/
@[expose] def scalarDecidableEq {contexts : List (PositiveContext entries)}
    {indices : List (Fin contexts.length)} {K : Type u} {ring : CommRing K} {equality : DecidableEq K}
    {function : Canonical → K} (stages : Stages contexts indices K ring equality function) :
    DecidableEq stages.Scalar :=
  match indices, stages with
  | [], .done => equality
  | _ :: _, .adjoin _ _ _ _ _ _ _ remaining => scalarDecidableEq remaining

/-- The final equality instance reads the same original scalar payloads. -/
instance instDecidableEqScalar {contexts : List (PositiveContext entries)}
    {indices : List (Fin contexts.length)} {K : Type u} {ring : CommRing K} {equality : DecidableEq K}
    {function : Canonical → K} (stages : Stages contexts indices K ring equality function) :
    DecidableEq stages.Scalar := stages.scalarDecidableEq

/-- Compose the same actual factor-tower embeddings into their common final algebra.

Both retained maps are captured before a coefficient is supplied. No new
root adjunction or original factor mapping is executed by a coefficient read.
-/
@[expose] def embed {contexts : List (PositiveContext entries)}
    {indices : List (Fin contexts.length)} {K : Type u} {ring : CommRing K} {equality : DecidableEq K}
    {function : Canonical → K} (stages : Stages contexts indices K ring equality function) : K → stages.Scalar :=
  match indices, stages with
  | [], .done => id
  | _ :: _, .adjoin _ _ _ _ tower _ _ remaining =>
      let first := tower.embed
      let later := remaining.embed
      fun value => later (first value)

variable {contexts : List (PositiveContext entries)} {indices : List (Fin contexts.length)}
variable {K : Type u} [ring : CommRing K] [equality : DecidableEq K] {function : Canonical → K}

/-- The actual composite coefficient map preserves original zero. -/
theorem embed_zero (stages : Stages contexts indices K ring equality function) : stages.embed 0 = 0 := by
  induction stages with
  | done => rfl
  | adjoin _ _ _ _ tower _ _ remaining previous =>
      change remaining.embed (tower.embed 0) = 0
      rewrite [tower.embed_zero]
      exact previous

/-- The actual composite coefficient map preserves original one. -/
theorem embed_one (stages : Stages contexts indices K ring equality function) : stages.embed 1 = 1 := by
  induction stages with
  | done => rfl
  | adjoin _ _ _ _ tower _ _ remaining previous =>
      change remaining.embed (tower.embed 1) = 1
      rewrite [tower.embed_one]
      exact previous

/-- The actual composite coefficient map preserves original addition. -/
theorem embed_add (stages : Stages contexts indices K ring equality function) (left right : K) :
    stages.embed (left + right) = stages.embed left + stages.embed right := by
  induction stages with
  | done => rfl
  | adjoin _ _ _ _ tower _ _ remaining previous =>
      change remaining.embed (tower.embed (left + right)) = _
      rewrite [tower.embed_add]
      exact previous _ _

/-- The actual composite coefficient map preserves original negation. -/
theorem embed_neg (stages : Stages contexts indices K ring equality function) (value : K) :
    stages.embed (-value) = -stages.embed value := by
  induction stages with
  | done => rfl
  | adjoin _ _ _ _ tower _ _ remaining previous =>
      change remaining.embed (tower.embed (-value)) = _
      rewrite [tower.embed_neg]
      exact previous _

/-- The actual composite coefficient map preserves original multiplication. -/
theorem embed_mul (stages : Stages contexts indices K ring equality function) (left right : K) :
    stages.embed (left * right) = stages.embed left * stages.embed right := by
  induction stages with
  | done => rfl
  | adjoin _ _ _ _ tower _ _ remaining previous =>
      change remaining.embed (tower.embed (left * right)) = _
      rewrite [tower.embed_mul]
      exact previous _ _

/-- Equal final coefficients identify their same original coefficients. -/
theorem embed_injective (stages : Stages contexts indices K ring equality function) :
    Function.Injective stages.embed := by
  induction stages with
  | done => intro _ _ equal; exact equal
  | adjoin _ _ _ _ tower _ _ remaining previous =>
      intro left right equal
      change remaining.embed (tower.embed left) = remaining.embed (tower.embed right) at equal
      exact tower.embed_injective (previous equal)

/-- Split each displayed original factor once, in its supplied original bounded-index order.

Each cached factor is mapped through the preceding actual coefficient map.
Its original Gaussian leading inverse gives a unit after the same map; the
target coefficient algebra is only a commutative ring. The recursive tail
uses the exact retained original tower embedding, without repeating a factor
according to its source multiplicity.
-/
@[expose] def prepare (contexts : List (PositiveContext entries))
    (indices : List (Fin contexts.length)) {K : Type u} [ring : CommRing K] [equality : DecidableEq K]
    (function : Canonical → K) (mapZero : function 0 = 0) (mapOne : function 1 = 1)
    (mapAdd : ∀ left right, function (left + right) = function left + function right)
    (mapNeg : ∀ value, function (-value) = -function value)
    (mapMul : ∀ left right, function (left * right) = function left * function right)
    (injective : Function.Injective function) : Stages contexts indices K ring equality function :=
  match indices with
  | [] => .done
  | index :: indices =>
      let source := factor contexts index
      let mapped := Map.map function source
      have normalized : mapped.normalize = mapped :=
        (Map.map_normalize function mapZero injective source).symm.trans
          (congrArg (Map.map function) (contexts.get index).focus.part.normalized)
      let leadingInverse := function source.leadingCoeff⁻¹
      have unit : mapped.leadingCoeff * leadingInverse = 1 := by
        rewrite [Map.map_leadingCoeff function mapZero injective source]
        change function source.leadingCoeff * function source.leadingCoeff⁻¹ = 1
        rewrite [← mapMul, Canonical.mul_inv_cancel source.leadingCoeff
          (Basic.DensePolynomial.leadingCoeff_ne_zero (contexts.get index).focus.part.nonzero)]
        exact mapOne
      let tower := Dense.Roots.Tower.prepare mapped normalized leadingInverse unit
      let roots := tower.blocks
      let coefficientMap := let next := tower.embed; fun value => next (function value)
      let remaining := prepare contexts indices coefficientMap
        (by change tower.embed (function 0) = 0; rewrite [mapZero]; exact tower.embed_zero)
        (by change tower.embed (function 1) = 1; rewrite [mapOne]; exact tower.embed_one)
        (by intro left right; change tower.embed (function (left + right)) = _
            rewrite [mapAdd]; exact tower.embed_add _ _)
        (by intro value; change tower.embed (function (-value)) = _
            rewrite [mapNeg]; exact tower.embed_neg _)
        (by intro left right; change tower.embed (function (left * right)) = _
            rewrite [mapMul]; exact tower.embed_mul _ _)
        (fun _ _ equal => injective (tower.embed_injective equal))
      .adjoin mapped rfl normalized (Map.map_natDegree function mapZero injective source) tower roots rfl remaining

set_option genInjectivity false in
/-- The complete original side contexts and their actual once-per-factor adjunction stages.

The original context list and its complete bounded index enumeration are
materialized once. Every cached mapped factor and tower belongs to that
same original context list, starting at the original Gaussian coefficient
algebra and its identity map.
-/
structure Prepared {source opposite : DensePolynomial Canonical} (input : PositiveSideInput source opposite) where
  /-- The actual cached original positive multiplicity contexts. -/
  contexts : List (PositiveContext input.entries)
  /-- The context cache retains the exact original positive-context enumeration. -/
  contexts_eq : contexts = input.contexts
  /-- The complete original bounded context indices in their source order. -/
  indices : List (Fin contexts.length)
  /-- Every original context occurs exactly once in the displayed order. -/
  indices_eq : indices = List.ofFn (fun index : Fin contexts.length => index)
  /-- The actual original factor towers in their shared final coefficient algebra. -/
  stages : Stages contexts indices Canonical inferInstance inferInstance id

constructive_injectivity Prepared

/-- Construct all original factor towers once from the same retained positive-side preprocessing.

The source and opposite cofactor remain indexed by their original input.
The complete context list supplies each squarefree factor once, while its
source multiplicity remains attached to that same original context.
-/
@[expose] def prepareInput {source opposite : DensePolynomial Canonical}
    (input : PositiveSideInput source opposite) : Prepared input :=
  let contexts := input.contexts
  let indices := List.ofFn (fun index : Fin contexts.length => index)
  let stages := prepare contexts indices id rfl rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ equal => equal)
  { contexts := contexts
    contexts_eq := rfl
    indices := indices
    indices_eq := rfl
    stages := stages }

end Stages

end Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots

end
