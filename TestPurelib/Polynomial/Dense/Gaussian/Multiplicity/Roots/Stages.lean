module

import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Bank
import Purelib.Polynomial.Dense.Gaussian.Coprime.Operations
import Purelib.System.IO

/-!
# Separate squarefree-factor adjunctions retain source multiplicity

The original degree-five source is `(x²-1)²(x-2)`. Its automatic Gaussian
preprocessing has two distinct squarefree multiplicity contexts. The same
contexts supply only three simple factor roots, then attach multiplicities
two, two and one in the common final coefficient algebra.
-/

namespace TestPurelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots

/-- The original degree-five source has one repeated quadratic and one other linear factor. -/
private def source : DensePolynomial Canonical := ⟨[1, -2, -2, 4, 1, -2]⟩

/-- The exact original coefficient table is already normalized. -/
private theorem source_normalized : source.normalize = source := by decide +kernel

/-- The source's original zero test sees its nonzero leading coefficient. -/
private theorem source_nonzero : source.isZero = false := by decide +kernel

/-- Its represented degree is exactly five. -/
private theorem source_degree : source.natDegree = 5 := by decide +kernel

/-- The original total preprocessing supplies the actual squarefree occurrence decomposition. -/
private def preprocessing : Squarefree.Decomposition.Compute.PositivePreprocessing source :=
  match Squarefree.Decomposition.Compute.preprocess source with
  | .positive retained => retained
  | .zero zero => False.elim (Bool.noConfusion (source_nonzero.symm.trans zero))
  | .constant _ degreeZero => False.elim (by
      have impossible : (5 : Nat) = 0 := source_degree.symm.trans degreeZero
      cases impossible)

/-- The same original preprocessing and constant opposite factor supply the positive-side input. -/
private def input : Multiplicity.Basis.Coprime.Side.PositiveSideInput source (DensePolynomial.constant 1) :=
  { sourceNormalized := source_normalized
    preprocessing := preprocessing
    oppositeNonzero := by decide +kernel
    sourceOppositeCoprime := Coprime.Operations.CoprimeCertificate.constantRight source_nonzero }

/-- Each original multiplicity context is split once through the shared sequential tower producer. -/
private def retained := Stages.prepareInput input

/-- The original final root images and weighted blocks are materialized from those same towers. -/
private def images := Stages.Images.prepare retained.stages

/-- The original preprocessing computes two distinct factor contexts rather than five simple occurrences. -/
private theorem context_count : retained.contexts.length = 2 := by decide +kernel

/-- The original squarefree factors generate three roots across the two sequential towers. -/
private theorem final_block_count : (Stages.Images.blocks retained.stages images).length = 3 := by decide +kernel

/-- The source multiplicities attach to those same three final points and exhaust degree five. -/
private theorem weighted_count :
    Purelib.Polynomial.Dense.Roots.totalMultiplicity (Stages.Images.blocks retained.stages images) = 5 :=
  (retained.totalMultiplicity images).trans source_degree

/-- The same original preprocessing automatically constructs every actual separation cache. -/
private def separated := Separation.prepare input

/-- The actual complete separation retains the same two original factor occurrences. -/
private theorem separated_context_count : separated.prepared.indices.length = 2 := by decide +kernel

/-- Every actual within-factor pair reads its original retained indexed cofactor inverse. -/
private theorem within_factor_units (position : Fin separated.prepared.indices.length)
    (first second : Fin (Stages.Images.rootsAt separated.prepared.stages separated.images position).length)
    (different : second ≠ first) :
    let roots := Stages.Images.rootsAt separated.prepared.stages separated.images position
    let jets := DependentProduct.get separated.prepared.indices separated.jets position
    ((roots.get first).point - (roots.get second).point) * (jets.pairs.get first second).inverse = 1 := by
  exact (Stages.Images.Pairs.get
    (DependentProduct.get separated.prepared.indices separated.jets position).pairs first second).unit different

/-- Every actual cross-factor pair reads its same original one-exclusion difference inverse. -/
private theorem cross_factor_units (first second : Fin separated.prepared.indices.length)
    (different : first ≠ second)
    (firstRoot : Fin (Stages.Images.rootsAt separated.prepared.stages separated.images first).length)
    (secondRoot : Fin (Stages.Images.rootsAt separated.prepared.stages separated.images second).length) :
    ∃ inverse : separated.prepared.stages.Scalar,
      (((Stages.Images.rootsAt separated.prepared.stages separated.images first).get firstRoot).point -
        ((Stages.Images.rootsAt separated.prepared.stages separated.images second).get secondRoot).point) * inverse =
          1 := by
  let pair := DependentProduct.get separated.prepared.indices
    (DependentProduct.get separated.prepared.indices separated.pairs first) second
  cases pair with
  | diagonal equal => exact (different equal).elim
  | separated _ cross => exact ⟨(cross.get firstRoot secondRoot).inverse.val,
      (cross.get firstRoot secondRoot).inverse.property⟩

/-- The complete automatic producer retains one original Bank in the same source-indexed final algebra. -/
private def completed := prepare input

/-- The complete original Bank has three actual root blocks, without duplicating repeated-root adjunctions. -/
private theorem bank_block_count : completed.bank.blocks.length = 3 := by decide +kernel

/-- The complete original Bank retains the same original normalized source coefficient factorization. -/
private theorem bank_factorization : completed.mapped.normalize =
    DensePolynomial.scale completed.mapped.leadingCoeff completed.bank.monicProduct :=
  completed.bank.factorization

/-- Every actual Bank point is the same retained point at its original context/root occurrence. -/
private theorem bank_origin_point (index : Fin completed.bank.blocks.length) :
    (completed.bank.block index).point = (completed.origin index).point :=
  completed.origin_point index

/-- Every actual Bank block keeps its original positive-context multiplicity. -/
private theorem bank_origin_multiplicity (index : Fin completed.bank.blocks.length) :
    (completed.bank.block index).multiplicity = (completed.context index).focus.multiplicity :=
  completed.multiplicity_eq_context index

/-- Every Bank context is the same original input context at the retained bounded original occurrence. -/
private theorem bank_context_original (index : Fin completed.bank.blocks.length) :
    completed.context index = input.contexts.get (completed.contextIndex index) :=
  completed.context_eq_original index

/-- The complete original Bank reads the actual retained root-difference inverse table. -/
private theorem bank_difference_units (first second : Fin completed.bank.blocks.length) (different : first ≠ second) :
    ((completed.bank.block first).point - (completed.bank.block second).point) *
      completed.bank.differenceInverses first second = 1 :=
  completed.bank.difference_unit first second different

/-- Check the same complete retained Bank without reducing the concrete tower construction in the checker. -/
private def check (completed : Prepared input) : IO Unit := do
  let retained := completed.separation
  let bank := completed.bank
  let positions := List.ofFn (fun index : Fin retained.prepared.indices.length => index)
  let blocks := bank.blocks
  unless retained.prepared.contexts.length == 2 && blocks.length == 3 &&
      Purelib.Polynomial.Dense.Roots.totalMultiplicity blocks == 5 do
    throw (IO.userError "automatic original factor/root/multiplicity counts differ from 2/3/5")
  unless decide (bank.monicProduct.coeffs = completed.mapped.coeffs) do
    throw (IO.userError "actual automatic Bank product differs from independent original monic source coefficients")
  let blockIndices := List.ofFn (fun index : Fin bank.blocks.length => index)
  for first in blockIndices do
    let origin := completed.origin first
    unless Stages.Images.Origin.position retained.prepared.stages retained.images origin == first.val &&
        (bank.block first).multiplicity == origin.context.focus.multiplicity do
      throw (IO.userError "actual Bank origin lost its original position or context multiplicity")
    for second in blockIndices do
      if first != second then
        unless decide (((bank.block first).point - (bank.block second).point) *
            bank.differenceInverses first second = 1) do
          throw (IO.userError "actual original Bank difference matrix failed")
  for position in positions do
    let roots := Stages.Images.rootsAt retained.prepared.stages retained.images position
    let rootsIndices := List.ofFn (fun index : Fin roots.length => index)
    let jets := DependentProduct.get retained.prepared.indices retained.jets position
    for first in rootsIndices do
      for second in rootsIndices do
        if first != second then
          let inverse := (jets.pairs.get first second).inverse
          unless decide (((roots.get first).point - (roots.get second).point) * inverse = 1) do
            throw (IO.userError "actual original squarefree first-jet difference inverse failed")
  for first in positions do
    for second in positions do
      let pair := DependentProduct.get retained.prepared.indices
        (DependentProduct.get retained.prepared.indices retained.pairs first) second
      match pair with
      | .diagonal _ => pure ()
      | .separated _ cross =>
          let firstRoots := Stages.Images.rootsAt retained.prepared.stages retained.images first
          let secondRoots := Stages.Images.rootsAt retained.prepared.stages retained.images second
          for firstRoot in List.ofFn (fun index : Fin firstRoots.length => index) do
            for secondRoot in List.ofFn (fun index : Fin secondRoots.length => index) do
              let inverse := (cross.get firstRoot secondRoot).inverse.val
              unless decide (((firstRoots.get firstRoot).point - (secondRoots.get secondRoot).point) * inverse = 1) do
                throw (IO.userError "actual original coprime-factor difference inverse failed")
  Purelib.System.IO.println
    "Original Bank: 2 factors, 3 roots, weight 5; coefficients, origins and all units passed."

/-- Execute the same automatic source construction and independently check all retained Bank readbacks and units. -/
public def run : IO Unit := check (prepare input)

end TestPurelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages
