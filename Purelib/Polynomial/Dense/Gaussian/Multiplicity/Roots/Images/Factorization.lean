module

public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Images
public import Purelib.Polynomial.Dense.Roots.Product.Derivative
import Purelib.Data.List.Map

/-!
# Original factor occurrences in the common final algebra

Bounded stage lookup reads the retained final simple-root list for the same
original positive context. Its literal coefficient factorization and simple
multiplicity certificates come from that context's actual original tower.
-/

public section

namespace Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages.Images

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Roots (Block)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive (PositiveEntry)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic (PositiveContext)
open Purelib.Data

universe u

variable {entries : List PositiveEntry} {contexts : List (PositiveContext entries)}
variable {indices : List (Fin contexts.length)} {K : Type u} {ring : CommRing K} {equality : DecidableEq K}
variable {function : Canonical → K}

/-- Read the same cached final simple-root list at its original bounded factor-stage occurrence. -/
@[expose] def rootsAt {entries : List PositiveEntry} {contexts : List (PositiveContext entries)}
    {indices : List (Fin contexts.length)} {K : Type u} {ring : CommRing K} {equality : DecidableEq K}
    {function : Canonical → K} (stages : Stages contexts indices K ring equality function) (images : Images stages)
    (position : Fin indices.length) : List (Block stages.Scalar) :=
  match indices, stages with
  | [], .done => Fin.elim0 position
  | _ :: _, .adjoin _ _ _ _ _ _ _ remaining =>
      Fin.cases images.1.roots (fun tail => rootsAt remaining images.2 tail) position

/-- Read the same cached source-multiplicity blocks at their original bounded factor-stage occurrence. -/
@[expose] def blocksAt {entries : List PositiveEntry} {contexts : List (PositiveContext entries)}
    {indices : List (Fin contexts.length)} {K : Type u} {ring : CommRing K} {equality : DecidableEq K}
    {function : Canonical → K} (stages : Stages contexts indices K ring equality function) (images : Images stages)
    (position : Fin indices.length) : List (Block stages.Scalar) :=
  match indices, stages with
  | [], .done => Fin.elim0 position
  | _ :: _, .adjoin _ _ _ _ _ _ _ remaining =>
      Fin.cases images.1.blocks (fun tail => blocksAt remaining images.2 tail) position

/-- The actual original Gaussian coefficient map into the same final stage algebra. -/
@[expose] def coefficientMap (stages : Stages contexts indices K ring equality function) : Canonical → stages.Scalar :=
  let finalEmbedding := stages.embed
  fun coefficient => finalEmbedding (function coefficient)

/-- The same final coefficient map preserves the original scalar zero. -/
theorem coefficientMap_zero (stages : Stages contexts indices K ring equality function)
    (mapZero : function 0 = 0) : coefficientMap stages 0 = 0 := by
  change stages.embed (function 0) = 0
  rewrite [mapZero]
  exact stages.embed_zero

/-- The same final coefficient map preserves the original scalar one. -/
theorem coefficientMap_one (stages : Stages contexts indices K ring equality function)
    (mapOne : function 1 = 1) : coefficientMap stages 1 = 1 := by
  change stages.embed (function 1) = 1
  rewrite [mapOne]
  exact stages.embed_one

/-- The same final coefficient map preserves original scalar sums. -/
theorem coefficientMap_add (stages : Stages contexts indices K ring equality function)
    (mapAdd : ∀ left right, function (left + right) = function left + function right) (left right : Canonical) :
    coefficientMap stages (left + right) = coefficientMap stages left + coefficientMap stages right := by
  change stages.embed (function (left + right)) = _
  rewrite [mapAdd]
  exact stages.embed_add _ _

/-- The same final coefficient map preserves original scalar products. -/
theorem coefficientMap_mul (stages : Stages contexts indices K ring equality function)
    (mapMul : ∀ left right, function (left * right) = function left * function right) (left right : Canonical) :
    coefficientMap stages (left * right) = coefficientMap stages left * coefficientMap stages right := by
  change stages.embed (function (left * right)) = _
  rewrite [mapMul]
  exact stages.embed_mul _ _

/-- The same final coefficient map preserves original scalar negatives. -/
theorem coefficientMap_neg (stages : Stages contexts indices K ring equality function)
    (mapNeg : ∀ value, function (-value) = -function value) (value : Canonical) :
    coefficientMap stages (-value) = -coefficientMap stages value := by
  change stages.embed (function (-value)) = _
  rewrite [mapNeg]
  exact stages.embed_neg _

/-- Equal final coefficient images identify their same original Gaussian scalars. -/
theorem coefficientMap_injective (stages : Stages contexts indices K ring equality function)
    (injective : Function.Injective function) : Function.Injective (coefficientMap stages) :=
  fun _ _ equal => injective (stages.embed_injective equal)

/-- A mapped final root cache retains each original simple multiplicity. -/
private theorem image_simple {context : PositiveContext entries} {A L : Type*}
    {original : List (Block A)} {embedding : A → L} (image : Image context original embedding)
    (simple : ∀ index : Fin original.length, (original.get index).multiplicity = 1)
    (index : Fin image.roots.length) : (image.roots.get index).multiplicity = 1 := by
  have bound : index.val < original.length := image.roots_length ▸ index.isLt
  have mappedBound : index.val < (original.map (Block.map embedding)).length := image.roots_eq ▸ index.isLt
  have retained := getElem_congr image.roots_eq (Eq.refl index.val) index.isLt
  have mapped := List.Map.getElem_map (Block.map embedding) original index.val bound mappedBound
  have reading := congrArg Block.multiplicity (retained.trans mapped)
  exact reading.trans (simple ⟨index.val, bound⟩)

/-- Every retained final factor-root occurrence has the same original simple multiplicity. -/
theorem rootsAt_simple (stages : Stages contexts indices K ring equality function) (images : Images stages)
    (position : Fin indices.length) (index : Fin (rootsAt stages images position).length) :
    ((rootsAt stages images position).get index).multiplicity = 1 := by
  induction stages with
  | done => exact Fin.elim0 position
  | adjoin _ _ _ _ tower roots rootsEq remaining previous =>
      rcases position with ⟨value, bound⟩
      cases value with
      | zero =>
          apply image_simple images.1
          intro original
          let sourceIndex : Fin tower.blocks.length := ⟨original.val, (congrArg List.length rootsEq) ▸ original.isLt⟩
          have reading := getElem_congr rootsEq (Eq.refl original.val) original.isLt
          exact (congrArg Block.multiplicity reading).trans (tower.blocks_simple sourceIndex)
      | succ value => exact previous images.2 ⟨value, Nat.lt_of_succ_lt_succ bound⟩ index

/-- The same stage's final simple-root count equals its original squarefree factor degree. -/
theorem rootsAt_length (stages : Stages contexts indices K ring equality function) (images : Images stages)
    (position : Fin indices.length) :
    (rootsAt stages images position).length = (factor contexts (indices.get position)).natDegree := by
  induction stages with
  | done => exact Fin.elim0 position
  | adjoin _ _ _ degreeEq tower _ rootsEq remaining previous =>
      rcases position with ⟨value, bound⟩
      cases value with
      | zero => exact images.1.roots_length.trans ((congrArg List.length rootsEq).trans
          (tower.blocks_length.trans degreeEq))
      | succ value => exact previous images.2 ⟨value, Nat.lt_of_succ_lt_succ bound⟩

/-- The same final simple-root list gives the literal original context-factor coefficient identity. -/
theorem factorizationAt (stages : Stages contexts indices K ring equality function) (images : Images stages)
    (mapZero : function 0 = 0) (injective : Function.Injective function) (mapOne : function 1 = 1)
    (mapAdd : ∀ left right, function (left + right) = function left + function right)
    (mapMul : ∀ left right, function (left * right) = function left * function right)
    (mapNeg : ∀ value, function (-value) = -function value) (position : Fin indices.length) :
    (Dense.Map.map (coefficientMap stages) (factor contexts (indices.get position))).normalize =
      DensePolynomial.scale (coefficientMap stages (factor contexts (indices.get position)).leadingCoeff)
        (Dense.Roots.product (rootsAt stages images position)) := by
  induction stages with
  | done => exact Fin.elim0 position
  | @adjoin K ring equality function context indices mapped mappedEq normalized _ tower roots rootsEq
      remaining previous =>
      rcases position with ⟨value, bound⟩
      cases value with
      | zero =>
          have retained := images.1.factorization tower normalized rootsEq remaining.embed
            remaining.embed_zero remaining.embed_injective remaining.embed_one remaining.embed_add
            remaining.embed_mul remaining.embed_neg
          let composite := remaining.embed ∘ tower.embed
          have source := (congrArg (Dense.Map.map composite) mappedEq).trans
            (Dense.Map.map_map composite function (factor contexts context))
          have leading := (congrArg (fun polynomial : DensePolynomial K => polynomial.leadingCoeff) mappedEq).trans
            (Dense.Map.map_leadingCoeff function mapZero injective (factor contexts context))
          exact (congrArg DensePolynomial.normalize source).symm.trans
            (retained.trans (congrArg
              (fun value => DensePolynomial.scale (composite value) (Dense.Roots.product images.1.roots)) leading))
      | succ value =>
          exact previous images.2
            (by change tower.embed (function 0) = 0; rewrite [mapZero]; exact tower.embed_zero)
            (fun _ _ equal => injective (tower.embed_injective equal))
            (by change tower.embed (function 1) = 1; rewrite [mapOne]; exact tower.embed_one)
            (by intro left right; change tower.embed (function (left + right)) = _
                rewrite [mapAdd]; exact tower.embed_add _ _)
            (by intro left right; change tower.embed (function (left * right)) = _
                rewrite [mapMul]; exact tower.embed_mul _ _)
            (by intro coefficient; change tower.embed (function (-coefficient)) = _
                rewrite [mapNeg]; exact tower.embed_neg _)
            ⟨value, Nat.lt_of_succ_lt_succ bound⟩

/-- Every original final simple root vanishes on its same original mapped context factor. -/
theorem rootsAt_vanishes (stages : Stages contexts indices K ring equality function) (images : Images stages)
    (mapZero : function 0 = 0) (injective : Function.Injective function) (mapOne : function 1 = 1)
    (mapAdd : ∀ left right, function (left + right) = function left + function right)
    (mapMul : ∀ left right, function (left * right) = function left * function right)
    (mapNeg : ∀ value, function (-value) = -function value) (position : Fin indices.length)
    (index : Fin (rootsAt stages images position).length) :
    (Dense.Map.map (coefficientMap stages) (factor contexts (indices.get position))).eval
      ((rootsAt stages images position).get index).point = 0 := by
  have retained := congrArg
    (fun polynomial : DensePolynomial stages.Scalar =>
      polynomial.eval ((rootsAt stages images position).get index).point)
    (factorizationAt stages images mapZero injective mapOne mapAdd mapMul mapNeg position)
  have vanishes : (Dense.Roots.product (rootsAt stages images position)).eval
      ((rootsAt stages images position).get index).point = 0 :=
    Dense.Roots.Product.eval_at (rootsAt stages images position) (rootsAt_simple stages images position) index
  rewrite [DensePolynomial.eval_normalize, DensePolynomial.eval_scale,
    vanishes, mul_zero] at retained
  exact retained

end Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages.Images

end
