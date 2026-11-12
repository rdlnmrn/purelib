module

public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Images.Factorization
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Decomposition
import Purelib.Polynomial.Dense.Reflection
import Purelib.Algebra.Semiring.Normalization
import Purelib.Data.List.Map
import Purelib.Data.List.OfFn.Basic
import Purelib.Tactic.Ring

/-!
# The original weighted factor product in the final coefficient algebra

The retained source preprocessing supplies its original scalar and powered
positive factors. Each same factor's final simple-root image supplies its
literal coefficient identity. Finite shift reflection compares the resulting
weighted original root-block product without assuming an infinite field.
-/

public section

namespace Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages.Images

open Purelib.Data
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Roots (Block)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive (PositiveEntry)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic (PositiveContext)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side (PositiveSideInput)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis
open Purelib.Algebra.Monogenic
open Purelib.Algebra.Semiring

universe u v

/-- A unital multiplicative coefficient function preserves its same finite scalar power. -/
private theorem map_power {A L : Type*} [CommRing A] [CommRing L]
    (function : A → L) (one : function 1 = 1)
    (multiply : ∀ left right, function (left * right) = function left * function right)
    (value : A) : (exponent : Nat) → function (value ^ exponent) = function value ^ exponent
  | 0 => by rewrite [pow_zero, pow_zero]; exact one
  | exponent + 1 => by
      rewrite [pow_succ, multiply, map_power function one multiply value exponent, pow_succ]
      rfl

/-- Interpreting the original Gaussian power table evaluates to the same finite target scalar power. -/
private theorem mappedPower_eval {L : Type*} [CommRing L] [DecidableEq L]
    (function : Canonical → L) (zero : function 0 = 0) (injective : Function.Injective function)
    (one : function 1 = 1) (add : ∀ left right, function (left + right) = function left + function right)
    (multiply : ∀ left right, function (left * right) = function left * function right)
    (polynomial : DensePolynomial Canonical) (point : L) : (exponent : Nat) →
    (Dense.Map.map function (Power.polynomialPower polynomial exponent)).eval point =
      (Dense.Map.map function polynomial).eval point ^ exponent
  | 0 => by rewrite [Power.polynomialPower, Dense.Map.map_constant, DensePolynomial.eval_constant, one, pow_zero]; rfl
  | exponent + 1 => by
      change (Dense.Map.map function (polynomial * Power.polynomialPower polynomial exponent)).eval point = _
      rewrite [Dense.Map.map_mul function zero injective add multiply, DensePolynomial.eval_mul,
        mappedPower_eval function zero injective one add multiply polynomial point exponent, pow_succ]
      exact mul_comm _ _

/-- Reweighting the same simple roots evaluates as their original product raised to the source multiplicity. -/
private theorem weighted_eval {entries : List PositiveEntry} (context : PositiveContext entries)
    {A L : Type*} [CommRing A] [DecidableEq A] [CommRing L] [DecidableEq L]
    (roots : List (Block A))
    (simple : ∀ index : Fin roots.length, (roots.get index).multiplicity = 1)
    (function : A → L) (zero : function 0 = 0) (injective : Function.Injective function)
    (one : function 1 = 1) (add : ∀ left right, function (left + right) = function left + function right)
    (multiply : ∀ left right, function (left * right) = function left * function right)
    (negate : ∀ value, function (-value) = -function value) (point : L) :
    (Dense.Map.map function (Dense.Roots.product (roots.map (weighted context)))).eval point =
      (Dense.Map.map function (Dense.Roots.product roots)).eval point ^ context.focus.multiplicity := by
  induction roots with
  | nil =>
      change (Dense.Map.map function (DensePolynomial.constant 1)).eval point =
        (Dense.Map.map function (DensePolynomial.constant 1)).eval point ^ _
      rewrite [Dense.Map.map_constant, DensePolynomial.eval_constant, one, one_pow]
      rfl
  | cons root remaining previous =>
      have head : root.multiplicity = 1 := simple ⟨0, Nat.zero_lt_succ _⟩
      have tail := fun index : Fin remaining.length => simple index.succ
      change (Dense.Map.map function ((weighted context root).polynomial *
        Dense.Roots.product (remaining.map (weighted context)))).eval point =
        (Dense.Map.map function (root.polynomial * Dense.Roots.product remaining)).eval point ^ _
      rewrite [Dense.Map.map_mul function zero injective add multiply,
        Dense.Map.map_mul function zero injective add multiply, DensePolynomial.eval_mul,
        DensePolynomial.eval_mul, Dense.Roots.Block.eval_map _ function zero injective one add multiply negate,
        Dense.Roots.Block.eval_map _ function zero injective one add multiply negate, head, pow_one,
        previous tail, Normalization.product_pow]
      rfl

/-- Mapping and evaluating an original concatenated block product preserves the same two retained block lists. -/
private theorem append_eval {A L : Type*} [CommRing A] [DecidableEq A] [CommRing L] [DecidableEq L]
    (first second : List (Block A)) (function : A → L) (zero : function 0 = 0)
    (injective : Function.Injective function) (one : function 1 = 1)
    (add : ∀ left right, function (left + right) = function left + function right)
    (multiply : ∀ left right, function (left * right) = function left * function right) (point : L) :
    (Dense.Map.map function (Dense.Roots.product (first ++ second))).eval point =
      (Dense.Map.map function (Dense.Roots.product first)).eval point *
        (Dense.Map.map function (Dense.Roots.product second)).eval point := by
  induction first with
  | nil =>
      rewrite [List.nil_append]
      change _ = (Dense.Map.map function (DensePolynomial.constant 1)).eval point * _
      rewrite [Dense.Map.map_constant, DensePolynomial.eval_constant, one, one_mul]
      rfl
  | cons root remaining previous =>
      change (Dense.Map.map function (root.polynomial * Dense.Roots.product (remaining ++ second))).eval point =
        (Dense.Map.map function (root.polynomial * Dense.Roots.product remaining)).eval point * _
      rewrite [Dense.Map.map_mul function zero injective add multiply,
        Dense.Map.map_mul function zero injective add multiply, DensePolynomial.eval_mul,
        DensePolynomial.eval_mul, previous]
      ring0

/-- An original literal factor identity reads the same target values after another coefficient interpretation. -/
private theorem factor_eval {A L : Type*} [CommRing A] [DecidableEq A] [CommRing L] [DecidableEq L]
    (function : Canonical → A) (polynomial : DensePolynomial Canonical) (roots : List (Block A))
    (literal : (Dense.Map.map function polynomial).normalize =
      DensePolynomial.scale (function polynomial.leadingCoeff) (Dense.Roots.product roots))
    (embedding : A → L) (zero : embedding 0 = 0) (injective : Function.Injective embedding)
    (multiply : ∀ left right, embedding (left * right) = embedding left * embedding right) (point : L) :
    (Dense.Map.map (embedding ∘ function) polynomial).eval point =
      embedding (function polynomial.leadingCoeff) *
        (Dense.Map.map embedding (Dense.Roots.product roots)).eval point := by
  have same := congrArg (fun value : DensePolynomial A => (Dense.Map.map embedding value).eval point) literal
  rewrite [Dense.Map.map_normalize embedding zero injective, Dense.Map.map_map, DensePolynomial.eval_normalize,
    Dense.Map.map_scale embedding zero injective multiply, DensePolynomial.eval_scale] at same
  exact same

variable {entries : List PositiveEntry} {contexts : List (PositiveContext entries)}
variable {indices : List (Fin contexts.length)} {K : Type u} {ring : CommRing K} {equality : DecidableEq K}
variable {function : Canonical → K}

/-- The original weighted factors retain the same final block values and exact original leading scalars. -/
private theorem product_eval (stages : Stages contexts indices K ring equality function) (images : Images stages)
    (mapZero : function 0 = 0) (injective : Function.Injective function) (mapOne : function 1 = 1)
    (mapAdd : ∀ left right, function (left + right) = function left + function right)
    (mapMul : ∀ left right, function (left * right) = function left * function right)
    (mapNeg : ∀ value, function (-value) = -function value)
    {L : Type v} [CommRing L] [DecidableEq L] (embedding : stages.Scalar → L)
    (embedZero : embedding 0 = 0) (embedInjective : Function.Injective embedding) (embedOne : embedding 1 = 1)
    (embedAdd : ∀ left right, embedding (left + right) = embedding left + embedding right)
    (embedMul : ∀ left right, embedding (left * right) = embedding left * embedding right)
    (embedNeg : ∀ value, embedding (-value) = -embedding value) (point : L) :
    (Dense.Map.map (embedding ∘ coefficientMap stages)
      (Product.positivePolynomial (indices.map (fun index => (contexts.get index).focus)))).eval point =
      embedding (coefficientMap stages ((indices.map (fun index => (contexts.get index).focus)).foldr
        (fun entry total => entry.part.polynomial.leadingCoeff ^ entry.multiplicity * total) 1)) *
        (Dense.Map.map embedding (Dense.Roots.product (blocks stages images))).eval point := by
  induction stages with
  | @done K ring equality function =>
      change (Dense.Map.map (embedding ∘ function) (DensePolynomial.constant 1)).eval point =
        embedding (function 1) * (Dense.Map.map embedding (DensePolynomial.constant 1)).eval point
      rewrite [Dense.Map.map_constant, Dense.Map.map_constant, DensePolynomial.eval_constant,
        DensePolynomial.eval_constant, mapOne, embedOne, mul_one]
      change embedding (function 1) = embedding 1
      exact congrArg embedding mapOne
  | @adjoin K ring equality function index indices mapped mappedEq normalized degree tower roots rootsEq
      remaining previous =>
      let model : remaining.Scalar → L := embedding
      have modelZero : model 0 = 0 := embedZero
      have modelInjective : Function.Injective model := embedInjective
      have modelOne : model 1 = 1 := embedOne
      have modelAdd : ∀ left right, model (left + right) = model left + model right := embedAdd
      have modelMul : ∀ left right, model (left * right) = model left * model right := embedMul
      have modelNeg : ∀ value, model (-value) = -model value := embedNeg
      let image : Image (contexts.get index) roots remaining.embed := images.1
      let later : Images remaining := images.2
      let complete : Stages contexts (index :: indices) K ring equality function :=
        .adjoin mapped mappedEq normalized degree tower roots rootsEq remaining
      let g : Canonical → L := model ∘ coefficientMap remaining
      have gZero : g 0 = 0 := (congrArg model (coefficientMap_zero complete mapZero)).trans modelZero
      have gOne : g 1 = 1 := (congrArg model (coefficientMap_one complete mapOne)).trans modelOne
      have gInjective : Function.Injective g :=
        fun _ _ equal => (coefficientMap_injective complete injective) (modelInjective equal)
      have gAdd : ∀ left right, g (left + right) = g left + g right := by
        intro left right
        exact (congrArg model (coefficientMap_add complete mapAdd left right)).trans (modelAdd _ _)
      have gMul : ∀ left right, g (left * right) = g left * g right := by
        intro left right
        exact (congrArg model (coefficientMap_mul complete mapMul left right)).trans (modelMul _ _)
      have tail := previous later
        (by change tower.embed (function 0) = 0; rewrite [mapZero]; exact tower.embed_zero)
        (fun _ _ equal => injective (tower.embed_injective equal))
        (by change tower.embed (function 1) = 1; rewrite [mapOne]; exact tower.embed_one)
        (by intro left right; change tower.embed (function (left + right)) = _
            rewrite [mapAdd]; exact tower.embed_add _ _)
        (by intro left right; change tower.embed (function (left * right)) = _
            rewrite [mapMul]; exact tower.embed_mul _ _)
        (by intro value; change tower.embed (function (-value)) = _
            rewrite [mapNeg]; exact tower.embed_neg _)
        model modelZero modelInjective modelOne modelAdd modelMul modelNeg
      have literal : (Dense.Map.map (coefficientMap remaining) (factor contexts index)).normalize =
          DensePolynomial.scale (coefficientMap remaining (factor contexts index).leadingCoeff)
            (Dense.Roots.product image.roots) :=
        factorizationAt complete images mapZero injective mapOne mapAdd mapMul mapNeg ⟨0, Nat.zero_lt_succ _⟩
      have head := factor_eval (coefficientMap remaining) (factor contexts index) image.roots literal
        model modelZero modelInjective modelMul point
      have simple : ∀ position : Fin image.roots.length, (image.roots.get position).multiplicity = 1 :=
        rootsAt_simple complete images ⟨0, Nat.zero_lt_succ _⟩
      have weighted : (Dense.Map.map model (Dense.Roots.product image.blocks)).eval point =
          (Dense.Map.map model (Dense.Roots.product image.roots)).eval point ^
            (contexts.get index).focus.multiplicity := by
        rewrite [image.blocks_eq]
        exact weighted_eval (contexts.get index) image.roots simple model modelZero modelInjective
          modelOne modelAdd modelMul modelNeg point
      change (Dense.Map.map g (Power.polynomialPower (factor contexts index)
        (contexts.get index).focus.multiplicity *
        Product.positivePolynomial (indices.map (fun original => (contexts.get original).focus)))).eval point =
          g ((factor contexts index).leadingCoeff ^ (contexts.get index).focus.multiplicity *
            (indices.map (fun original => (contexts.get original).focus)).foldr
              (fun entry total => entry.part.polynomial.leadingCoeff ^ entry.multiplicity * total) 1) *
          (Dense.Map.map model (Dense.Roots.product (image.blocks ++ blocks remaining later))).eval point
      rewrite [Dense.Map.map_mul g gZero gInjective gAdd gMul, DensePolynomial.eval_mul,
        mappedPower_eval g gZero gInjective gOne gAdd gMul, head, Normalization.product_pow, tail, gMul,
        map_power g gOne gMul, append_eval image.blocks (blocks remaining later) model
          modelZero modelInjective modelOne modelAdd modelMul point, weighted]
      dsimp only [g, Function.comp_apply]
      ring0

/-- The retained original source is literally its same final multiplicity-weighted block product.

The original preprocessing's discarded scalar and powered factor heads
reconstruct the source head internally. The proof uses one finite shift
algebra computed from these two actual coefficient lists; no target field,
additional roots, or supplied final leading identity is required.
-/
theorem factorization {source opposite : DensePolynomial Canonical} {input : PositiveSideInput source opposite}
    (prepared : Prepared input) (images : Images prepared.stages) :
    (Dense.Map.map (coefficientMap prepared.stages) source).normalize =
      DensePolynomial.scale (coefficientMap prepared.stages source.leadingCoeff)
        (Dense.Roots.product (blocks prepared.stages images)) := by
  let decomposition := input.preprocessing.decomposition
  let unit := Positive.unitValue decomposition.multiplicityBasis.entries
  have sourceLiteral : source = DensePolynomial.scale unit (Product.positivePolynomial input.entries) :=
    ((DensePolynomial.normalize_normalize source).trans input.sourceNormalized).symm.trans
      decomposition.positiveMultiplicity_factorization
  have headNormalized : source.normalize.leadingCoeff = source.leadingCoeff := by
    change source.normalize.normalize.coeffs.headD 0 = source.normalize.coeffs.headD 0
    rewrite [DensePolynomial.normalize_normalize]
    rfl
  have sourceHead : source.leadingCoeff = unit * input.entries.foldr
      (fun entry total => entry.part.polynomial.leadingCoeff ^ entry.multiplicity * total) 1 :=
    headNormalized.symm.trans decomposition.positiveMultiplicity_leadingCoeff
  let original := Dense.Map.map (coefficientMap prepared.stages) source
  let displayed := DensePolynomial.scale (coefficientMap prepared.stages source.leadingCoeff)
    (Dense.Roots.product (blocks prepared.stages images))
  have same : original.normalize = displayed.normalize := by
    apply Dense.Reflection.normalize_eq
    let dimension := Nat.max original.coeffs.length displayed.coeffs.length + 1
    let cyclic := Cyclic.shift prepared.stages.Scalar dimension (Nat.zero_lt_succ _)
    let embedding := Cyclic.Element.scalar cyclic
    let point := Cyclic.Element.root cyclic
    let g : Canonical → Cyclic.Element cyclic := embedding ∘ coefficientMap prepared.stages
    have gZero : g 0 = 0 :=
      (congrArg embedding (coefficientMap_zero prepared.stages rfl)).trans (Cyclic.Element.scalar_zero cyclic)
    have gInjective : Function.Injective g := fun _ _ equal =>
      coefficientMap_injective prepared.stages (fun _ _ same => same)
        (Cyclic.Element.scalar_injective cyclic equal)
    have gMul : ∀ left right, g (left * right) = g left * g right := by
      intro left right
      exact (congrArg embedding (coefficientMap_mul prepared.stages (fun _ _ => rfl) left right)).trans
        (Cyclic.Element.scalar_mul cyclic _ _)
    have interpreted := congrArg (Dense.Map.map g) sourceLiteral
    rewrite [Dense.Map.map_scale g gZero gInjective gMul] at interpreted
    have reading := congrArg (fun polynomial : DensePolynomial (Cyclic.Element cyclic) => polynomial.eval point)
      interpreted
    rewrite [DensePolynomial.eval_scale] at reading
    have weighted := product_eval prepared.stages images rfl (fun _ _ same => same) rfl
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) embedding
      (Cyclic.Element.scalar_zero cyclic) (fun _ _ equal => Cyclic.Element.scalar_injective cyclic equal)
      (Cyclic.Element.scalar_one cyclic) (Cyclic.Element.scalar_add cyclic) (Cyclic.Element.scalar_mul cyclic)
      (Cyclic.Element.scalar_neg cyclic) point
    rewrite [prepared.focuses_eq] at weighted
    change (Dense.Map.map embedding original).eval point = (Dense.Map.map embedding displayed).eval point
    dsimp only [original, displayed]
    rewrite [Dense.Map.map_map, Dense.Map.map_scale embedding (Cyclic.Element.scalar_zero cyclic)
      (fun _ _ equal => Cyclic.Element.scalar_injective cyclic equal) (Cyclic.Element.scalar_mul cyclic),
      DensePolynomial.eval_scale]
    change (Dense.Map.map g source).eval point =
      g source.leadingCoeff * (Dense.Map.map embedding (Dense.Roots.product (blocks prepared.stages images))).eval point
    rewrite [reading, weighted, sourceHead, gMul]
    dsimp only [g, Function.comp_apply]
    ring0
  exact same.trans (DensePolynomial.normalize_scale _ _)

end Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages.Images

end
