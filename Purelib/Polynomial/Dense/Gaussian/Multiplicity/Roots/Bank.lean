module

public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Separation.Inverse
public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Images.Product
import Purelib.LinearAlgebra.Matrix.Basic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Automatic original root banks from positive multiplicity preprocessing

Every original squarefree multiplicity factor is split once in successive
coefficient algebras. The same original context/root images, cofactor units
and bounded origin vector supply one original Bank, including its literal
weighted coefficient factorization and actual root-difference inverse matrix.
-/

public section

namespace Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side (PositiveSideInput)
open Purelib.LinearAlgebra renaming Matrix → SquareMatrix
open Stages

variable {source opposite : DensePolynomial Canonical} {input : PositiveSideInput source opposite}

namespace Separation

/-- The same actual final coefficient algebra of the retained original factor towers. -/
abbrev Scalar (retained : Separation input) := retained.prepared.stages.Scalar

end Separation

set_option genInjectivity false in
/-- An original Gaussian side's actual factor towers, root origins, mapped source and original certified Bank.

The final carrier is the same retained original tower algebra and has no
field premise. The actual Bank retains the original weighted root lists and
source coefficient identity; its difference matrix reads the same already
computed original cofactor caches.
-/
structure Prepared (input : PositiveSideInput source opposite) where
  /-- The original contexts, once-split factor towers and complete actual separation caches. -/
  separation : Separation input
  /-- The once-materialized original bounded factor-root views in weighted-block order. -/
  origins : Images.Origin.Table separation.prepared.stages separation.images
  /-- The retained views are the same original flattened occurrence materialization. -/
  origins_eq : origins = Images.Origin.prepare separation.prepared.stages separation.images
  /-- The actual original source coefficient table mapped once into the common final algebra. -/
  mapped : DensePolynomial separation.Scalar
  /-- The mapped cache uses the same original source and retained composite coefficient function. -/
  mapped_eq : mapped = Dense.Map.map (Images.coefficientMap separation.prepared.stages) source
  /-- The same original Bank with literal source factorization and actual difference units. -/
  bank : Dense.Roots.Bank mapped
  /-- Every Bank block is the same original retained context-weighted final root image. -/
  blocks_eq : bank.blocks = Images.blocks separation.prepared.stages separation.images

constructive_injectivity Prepared

namespace Prepared

/-- Read the same retained original factor-root view at an actual Bank block index. -/
@[expose] def origin (prepared : Prepared input) (index : Fin prepared.bank.blocks.length) :
    Images.Origin prepared.separation.prepared.stages prepared.separation.images :=
  prepared.origins ⟨index.val, (congrArg List.length prepared.blocks_eq) ▸ index.isLt⟩

/-- The retained origin has the same original flattened Bank position. -/
theorem origin_position (prepared : Prepared input) (index : Fin prepared.bank.blocks.length) :
    Images.Origin.position prepared.separation.prepared.stages prepared.separation.images
      (prepared.origin index) = index.val := by
  rewrite [origin, prepared.origins_eq]
  exact Images.Origin.prepare_position _ _ _

/-- An actual Bank block reads the point from its same retained original factor-root occurrence. -/
theorem origin_point (prepared : Prepared input) (index : Fin prepared.bank.blocks.length) :
    (prepared.bank.block index).point = (prepared.origin index).point := by
  have same := getElem_congr prepared.blocks_eq (Eq.refl index.val) index.isLt
  have reading := congrArg Dense.Roots.Block.point same
  apply reading.trans
  rewrite [origin, prepared.origins_eq]
  exact Images.Origin.prepare_point _ _ _

/-- Read the same original cached positive context of an actual Bank block. -/
@[expose] def context (prepared : Prepared input) (index : Fin prepared.bank.blocks.length) :=
  (prepared.origin index).context

/-- Read the original bounded input-context index without repeating its enumeration. -/
@[expose] def contextIndex (prepared : Prepared input) (index : Fin prepared.bank.blocks.length) :
    Fin input.contexts.length :=
  let retained := (prepared.origin index).contextIndex
  ⟨retained.val, (congrArg List.length prepared.separation.prepared.contexts_eq) ▸ retained.isLt⟩

/-- The retained context is exactly the original input context at its same bounded occurrence. -/
theorem context_eq_original (prepared : Prepared input) (index : Fin prepared.bank.blocks.length) :
    prepared.context index = input.contexts.get (prepared.contextIndex index) := by
  exact getElem_congr prepared.separation.prepared.contexts_eq
    (Eq.refl (prepared.origin index).contextIndex.val) (prepared.origin index).contextIndex.isLt

/-- An actual Bank block retains the multiplicity of its same original positive context. -/
theorem multiplicity_eq_context (prepared : Prepared input) (index : Fin prepared.bank.blocks.length) :
    (prepared.bank.block index).multiplicity = (prepared.context index).focus.multiplicity := by
  have same := getElem_congr prepared.blocks_eq (Eq.refl index.val) index.isLt
  have reading := congrArg Dense.Roots.Block.multiplicity same
  apply reading.trans
  rewrite [context, origin, prepared.origins_eq]
  exact Images.Origin.prepare_multiplicity _ _ _

end Prepared

/-- Construct the original certified Bank automatically from the same positive-side preprocessing.

The actual source-indexed towers and difference cofactors are computed once.
The same original vector materializes the factor/root origins; the difference
matrix only reads their already retained within-factor or cross-factor units.
The original weighted multiplicity identity supplies both degree and literal
source factorization, without supplied roots, rank, basis or final identity.
-/
@[expose] def prepare (input : PositiveSideInput source opposite) : Prepared input :=
  let separation := Separation.prepare input
  let stages := separation.prepared.stages
  let images := separation.images
  let embedding := Images.coefficientMap stages
  let blocks := Images.blocks stages images
  let origins := Images.Origin.prepare stages images
  let mapped := Dense.Map.map embedding source
  let monic := Dense.Roots.product blocks
  let differences := SquareMatrix.matrixOfFn fun first second => separation.inverse (origins first) (origins second)
  let bank : Dense.Roots.Bank mapped :=
    { blocks := blocks
      count_eq := (separation.prepared.totalMultiplicity images).trans
        (Dense.Map.map_natDegree embedding (Images.coefficientMap_zero stages rfl)
          (Images.coefficientMap_injective stages (fun _ _ equal => equal)) source).symm
      monicProduct := monic
      product_eq := rfl
      factorization := by
        have leading := Dense.Map.map_leadingCoeff embedding (Images.coefficientMap_zero stages rfl)
          (Images.coefficientMap_injective stages (fun _ _ equal => equal)) source
        exact (Images.factorization separation.prepared images).trans
          (congrArg (fun value => DensePolynomial.scale value monic) leading.symm)
      differenceInverses := differences
      difference_unit := by
        intro first second different
        rewrite [SquareMatrix.matrixOfFn_apply]
        have left : (blocks[first.val]'first.isLt).point = (origins first).point :=
          Images.Origin.prepare_point stages images first
        have right : (blocks[second.val]'second.isLt).point = (origins second).point :=
          Images.Origin.prepare_point stages images second
        rewrite [left, right]
        apply separation.inverse_unit
        intro equal
        apply different
        exact Fin.ext ((Images.Origin.prepare_position stages images first).symm.trans
          (equal.trans (Images.Origin.prepare_position stages images second))) }
  { separation := separation, origins := origins, origins_eq := rfl, mapped := mapped, mapped_eq := rfl,
    bank := bank, blocks_eq := rfl }

end Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots

end
