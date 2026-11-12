module

public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages
import Purelib.Data.List.Map
import Purelib.Data.List.OfFn.Basic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Cached final images of the original factor roots

Each original factor tower supplies one simple root list. The remaining
retained towers map that same list into the common final algebra once. A
second retained list attaches the original context's positive multiplicity
to those same cached final points, without repeating an adjunction.
-/

public section

namespace Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages

open Purelib.Polynomial.Dense.Roots (Block)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive (PositiveEntry)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic (PositiveContext)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side (PositiveSideInput)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List

universe u v

variable {entries : List PositiveEntry}

/-- Attach an original positive context's multiplicity to the same displayed root point. -/
@[expose] def weighted (context : PositiveContext entries) {K : Type*} (root : Block K) : Block K :=
  ⟨root.point, context.focus.multiplicity, context.focus.multiplicityPositive⟩

set_option genInjectivity false in
/-- The once-mapped final root list and its same original multiplicity-weighted image.

The type retains the original factor context, its original simple root
cache, and the exact remaining-stage scalar embedding. Both list equations
bind the retained values to those original owners.
-/
structure Image (context : PositiveContext entries) {K : Type u} {L : Type v}
    (original : List (Block K)) (function : K → L) where
  /-- The original simple roots mapped once into the common final coefficient algebra. -/
  roots : List (Block L)
  /-- Every final simple point uses the same original root and remaining embedding. -/
  roots_eq : roots = original.map (Block.map function)
  /-- The same cached final points with the original source-factor multiplicity. -/
  blocks : List (Block L)
  /-- Source multiplicities are attached to the same retained final root cache. -/
  blocks_eq : blocks = roots.map (weighted context)

constructive_injectivity Image

namespace Image

/-- Map each original root once, then attach its original context multiplicity once. -/
@[expose] def prepare (context : PositiveContext entries) {K : Type u} {L : Type v}
    (original : List (Block K)) (function : K → L) : Image context original function :=
  let roots := original.map (Block.map function)
  let blocks := roots.map (weighted context)
  ⟨roots, rfl, blocks, rfl⟩

/-- The final simple-root list preserves the original factor-root occurrence count. -/
theorem roots_length {context : PositiveContext entries} {K : Type u} {L : Type v}
    {original : List (Block K)} {function : K → L} (image : Image context original function) :
    image.roots.length = original.length := by
  rewrite [image.roots_eq]
  exact Purelib.Data.List.Map.length_map _ _

/-- Attaching multiplicities preserves the same original factor-root occurrence count. -/
theorem blocks_length {context : PositiveContext entries} {K : Type u} {L : Type v}
    {original : List (Block K)} {function : K → L} (image : Image context original function) :
    image.blocks.length = original.length := by
  rewrite [image.blocks_eq, Purelib.Data.List.Map.length_map]
  exact image.roots_length

/-- Weighting the original simple roots gives the source multiplicity times the original factor degree count. -/
theorem totalMultiplicity {context : PositiveContext entries} {K : Type u} {L : Type v}
    {original : List (Block K)} {function : K → L} (image : Image context original function) :
    Dense.Roots.totalMultiplicity image.blocks = context.focus.multiplicity * original.length := by
  have weighted_count : ∀ roots : List (Block L),
      Dense.Roots.totalMultiplicity (roots.map (weighted context)) = context.focus.multiplicity * roots.length := by
    intro roots
    induction roots with
    | nil => exact (Nat.mul_zero _).symm
    | cons root remaining previous =>
        change context.focus.multiplicity + Dense.Roots.totalMultiplicity (remaining.map (weighted context)) =
          context.focus.multiplicity * (remaining.length + 1)
        rewrite [previous, Nat.mul_succ, Nat.add_comm]
        rfl
  rewrite [image.blocks_eq, weighted_count, image.roots_length]
  rfl

end Image

/-- The actual final-image caches following the same original adjunction-stage spine.

Each ordinary pair retains the head factor's two image lists and the
remaining original stages' image caches. The final scalar carrier is the
same retained carrier throughout; no alternative root collection is built.
-/
@[expose] def Images {contexts : List (PositiveContext entries)}
    {indices : List (Fin contexts.length)} {K : Type u} {ring : CommRing K} {equality : DecidableEq K}
    {function : Canonical → K}
    (stages : Stages contexts indices K ring equality function) : Type (u + 1) :=
  match indices, stages with
  | [], .done => PUnit
  | index :: _, .adjoin _ _ _ _ _ roots _ remaining =>
      Image (contexts.get index) roots remaining.embed × Images remaining

namespace Images

/-- Materialize every stage's final root images and original multiplicities once. -/
@[expose] def prepare {contexts : List (PositiveContext entries)}
    {indices : List (Fin contexts.length)} {K : Type u} {ring : CommRing K} {equality : DecidableEq K}
    {function : Canonical → K}
    (stages : Stages contexts indices K ring equality function) : Images stages :=
  match indices, stages with
  | [], .done => PUnit.unit
  | index :: _, .adjoin _ _ _ _ _ roots _ remaining =>
      (Image.prepare (contexts.get index) roots remaining.embed, prepare remaining)

/-- Read the original weighted blocks in their retained context and root-occurrence order. -/
@[expose] def blocks {contexts : List (PositiveContext entries)}
    {indices : List (Fin contexts.length)} {K : Type u} {ring : CommRing K} {equality : DecidableEq K}
    {function : Canonical → K}
    (stages : Stages contexts indices K ring equality function) (images : Images stages) :
    List (Block stages.Scalar) :=
  match indices, stages with
  | [], .done => []
  | _ :: _, .adjoin _ _ _ _ _ _ _ remaining => images.1.blocks ++ blocks remaining images.2

/-- The retained final images count the actual original factor degrees with their source multiplicities. -/
theorem totalMultiplicity {contexts : List (PositiveContext entries)}
    {indices : List (Fin contexts.length)} {K : Type u} {ring : CommRing K} {equality : DecidableEq K}
    {function : Canonical → K} (stages : Stages contexts indices K ring equality function)
    (images : Images stages) :
    Dense.Roots.totalMultiplicity (blocks stages images) =
      indices.foldr (fun index total =>
        (contexts.get index).focus.multiplicity * (factor contexts index).natDegree + total) 0 := by
  induction stages with
  | done => rfl
  | @adjoin K ring equality function index indices mapped mappedEq normalized degreeEq tower roots rootsEq
      remaining previous =>
      change Dense.Roots.totalMultiplicity (images.1.blocks ++ blocks remaining images.2) = _
      rewrite [Dense.Roots.totalMultiplicity_append, images.1.totalMultiplicity, previous images.2,
        rootsEq, tower.blocks_length, degreeEq]
      rfl

end Images

namespace Image

/-- The same cached final simple roots transport the original tower's literal coefficient factorization.

The original normalized factor and its same retained tower supply the
factorization. Only the remaining actual scalar embedding maps its cached
roots and coefficients into the common final algebra.
-/
theorem factorization {context : PositiveContext entries} {K : Type u} [ring : CommRing K]
    [equality : DecidableEq K] {polynomial : DensePolynomial K}
    (tower : Dense.Roots.Tower K ring equality polynomial) (normalized : polynomial.normalize = polynomial)
    {original : List (Block tower.Scalar)} (original_eq : original = tower.blocks)
    {L : Type v} [CommRing L] [DecidableEq L] (function : tower.Scalar → L)
    (mapZero : function 0 = 0) (injective : Function.Injective function) (mapOne : function 1 = 1)
    (mapAdd : ∀ left right, function (left + right) = function left + function right)
    (mapMul : ∀ left right, function (left * right) = function left * function right)
    (mapNeg : ∀ value, function (-value) = -function value)
    (image : Image context original function) :
    (Dense.Map.map (function ∘ tower.embed) polynomial).normalize =
      DensePolynomial.scale (function (tower.embed polynomial.leadingCoeff)) (Dense.Roots.product image.roots) := by
  have retained := congrArg (Dense.Map.map function) (tower.factorization normalized)
  rewrite [Dense.Map.map_normalize function mapZero injective,
    Dense.Map.map_map,
    Dense.Map.map_scale function mapZero injective mapMul,
    Dense.Roots.map_product function mapZero injective mapOne mapAdd mapMul mapNeg] at retained
  rewrite [image.roots_eq, original_eq]
  exact retained

end Image

namespace Prepared

/-- The same retained bounded context order reads exactly the original positive source entries. -/
theorem focuses_eq {source opposite : DensePolynomial Canonical}
    {input : PositiveSideInput source opposite} (prepared : Prepared input) :
    prepared.indices.map (fun index => (prepared.contexts.get index).focus) = input.entries := by
  rewrite [prepared.indices_eq, OfFn.Basic.map_ofFn]
  change List.ofFn (fun index : Fin prepared.contexts.length => (prepared.contexts.get index).focus) = input.entries
  have retained : List.ofFn (fun index : Fin prepared.contexts.length =>
      (prepared.contexts.get index).focus) = prepared.contexts.map (fun context => context.focus) :=
    OfFn.Basic.map_ofFn.symm.trans
      (congrArg (List.map (fun context : PositiveContext input.entries => context.focus))
        (OfFn.Basic.ofFn_getElem prepared.contexts))
  rewrite [retained, prepared.contexts_eq]
  exact Context.Basic.positiveContexts_focuses input.entries

/-- The complete original final-image cache exhausts exactly the original source degree.

The actual source context enumeration supplies the original factor degrees
and positive multiplicities. The complete bounded index table neither omits
nor repeats any original factor context.
-/
theorem totalMultiplicity {source opposite : DensePolynomial Canonical}
    {input : PositiveSideInput source opposite} (prepared : Prepared input) (images : Images prepared.stages) :
    Dense.Roots.totalMultiplicity (Images.blocks prepared.stages images) = source.natDegree := by
  have fold : ∀ indices : List (Fin prepared.contexts.length),
      indices.foldr (fun index total =>
        (prepared.contexts.get index).focus.multiplicity * (factor prepared.contexts index).natDegree + total) 0 =
      Product.positiveDegree (indices.map (fun index => (prepared.contexts.get index).focus)) := by
    intro indices
    induction indices with
    | nil => rfl
    | cons index remaining previous =>
        change _ + _ = _ + _
        exact congrArg (fun total => _ + total) previous
  rewrite [Images.totalMultiplicity, fold, prepared.focuses_eq]
  exact input.multiplicityDegree

end Prepared

end Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages

end
