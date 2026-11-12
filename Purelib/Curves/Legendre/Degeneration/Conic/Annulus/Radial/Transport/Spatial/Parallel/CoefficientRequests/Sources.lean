module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.CoefficientRequests.Comparison
import Purelib.Data.Nat.Order
import Purelib.Tactic.Ring
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.OwnerTrace
import Purelib.Curves.Legendre.Periods.Jets.Source
import Purelib.Curves.Legendre.Periods.Jets.Source.Cells
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Programs
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Equivalence.Sampling
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Integration.Program.Gaussian.Approximation
import Purelib.Integration.Program.Gaussian.Name
import Purelib.Integration.Polynomial.Gaussian.Path.Basic.Indexed
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Riemann.Paths.PreparedPrimitivePaths
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Program
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Partition
import Purelib.Data.List.DependentProduct
import Purelib.Data.Nat.List.Maximum
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer
import Purelib.Polynomial.Dense.Power
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Piece
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Cells
import Purelib.Curves.Legendre.Periods.Jets.Specification.Table
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Approximation.Rational.Geometric.Search

import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests

import Purelib.Riemann.Readings.UniformPreparedRequests

import Purelib.Polynomial.Dense.Arithmetic

import Purelib.Riemann.Integration.ContinuedPrimitiveOverlap

import Purelib.Riemann.Readings.PreparedPrimitiveSamples

/-! # Shared original coefficient requests along retained parallel moves

One materialized bank determines common model and scalar stages before a
single original source/model/root acquisition. Every original form consumes
that same retained Point, observation and comparison with its own indexed
coefficient and internally derived payment. These are coefficient requests;
whole supplied-Blocks or six-programme integral agreement remains separate.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

open Purelib.Data
open Purelib.Approximation.Rational
open Purelib.Data.Gaussian
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential.Bounds renaming Data → WaistBounds
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)

open Purelib.Data.Rat.Fraction.Order

namespace OwnerTrace

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Approximation
open Purelib.Data.List (DependentProduct)
open Purelib.Data.Vector (DependentVector)
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Legendre.Periods.Jets
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement (Piece Layer)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath (Blocks)
open Purelib.Integration.Path.Dyadic
open OwnerMove.PrimitiveTarget
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport

variable {site : Fin 2} {parameter : Canonical} {quarter : Geometry.Gaussian.UnitCircle.Quarter.UnitCircuitQuarter}
variable {leg : Leg site parameter quarter} {coarse : Leg.TraceBudget leg}
variable {clearance : OwnerBudget.SourceClearance leg}
variable {originalSource : Spatial.Source leg.source leg.sourcePrepared}
variable (bounds : OwnerBudget.PrimitiveBounds leg coarse clearance)
variable {count : Nat} {frame : Curves.Legendre.Paths.Frame parameter} {basis : Differential 1} {sheet : Fin 2}
variable (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
  (Specification.Table.forms parameter channel)))
variable {initialAccuracy : AccuracyRequest} {initial : Piece (forms.get 0) leg.actual initialAccuracy}

/-- The actual paired primitive, scalar Piece and whole original parent cache at one retained move occurrence.

This is an exact tuple view in the original dependent product. Its two
inputs remain complete stored values; no Point, model, source or parent
factory is evaluated by this type.
-/
@[expose] def NumericalInput
    (trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest))
    (bank : OwnerMoves.Entries trace.moves)
    (scalar : Layer initial trace.budget.fine.selection.stage)
    (edge : Fin (DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1).length) :=
  (OwnerMove.PrimitiveTarget.Anchored bounds (bank.get edge).2.2 count ×
    Piece (forms.get 0) leg.actual scalar.accuracy) ×
      bank.ParentCacheAt frame basis sheet edge

/-- The original local stage selections and common numerical preparation on one actual retained input tuple.

The parent/six pair selections determine the necessary model floor before
one original Source Request. Six original Precisions then retain their
actual Taylor stages without acquiring any scalar Point/root triple.
-/
@[expose] def NumericalPreparation
    {trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest)}
    {bank : OwnerMoves.Entries trace.moves}
    {scalar : Layer initial trace.budget.fine.selection.stage}
    {edge : Fin (DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1).length}
    (input : NumericalInput (count := count) (frame := frame) (basis := basis) (sheet := sheet) bounds forms trace bank
      scalar edge)
    (modelFloor scalarFloor pairCurrent : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest) :=
  Σ cache : Source.Cache input.1.1.target.patch,
  Σ paired : PreparedParents.PairSelections input.1.1.target.patch input.2.covered pairCurrent
      (Budget.Aggregate.perTerm (target / 4) input.2.parents.length),
  let minimum := max modelFloor paired.modelFloor
  let quarterPositive := Fraction.Order.Field.div_pos_direct positive (by decide +kernel : (0 : Fraction.Rational) < 4)
  Σ prepared : CoefficientRequests.Preparation bounds input.1.1.target cache forms scalar.accuracy
      minimum scalarFloor (ScalarModels.coefficientTarget input.1.2 (target / 4))
        (ScalarModels.coefficientTarget_positive input.1.2 quarterPositive) sourceAccuracy,
    {actual : CoefficientRequests.Precisions bounds input.1.1.target forms input.1.2
        minimum scalarFloor (target / 4) quarterPositive //
      actual = CoefficientRequests.precisions bounds input.1.1.target cache forms input.1.2
        minimum scalarFloor (target / 4) quarterPositive sourceAccuracy prepared}

/-- Compute the actual parent and six-form numerical payments before any scalar Point/root acquisition.

The original pair selections, common Source Request, powers and Precisions
are retained as complete values. Each factory runs once on the supplied
whole primitive, scalar Piece and parent cache; later maxima consume these
stored stages without rerunning a request or selection.
-/
def prepareNumerical
    {trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest)}
    {bank : OwnerMoves.Entries trace.moves}
    {scalar : Layer initial trace.budget.fine.selection.stage}
    {edge : Fin (DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1).length}
    (input : NumericalInput (count := count) (frame := frame) (basis := basis) (sheet := sheet) bounds forms
        trace bank scalar edge)
    (modelFloor scalarFloor pairCurrent : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest) :
    NumericalPreparation (count := count) bounds forms input modelFloor scalarFloor pairCurrent target positive
        sourceAccuracy := by
  let cache := Source.Cache.ofPatch input.1.1.target.patch
  have quarterPositive : 0 < target / 4 := Fraction.Order.Field.div_pos_direct positive (by decide +kernel)
  let paired := PreparedParents.pairSelections input.1.1.target.patch input.2.covered pairCurrent
    (Budget.Aggregate.perTerm (target / 4) input.2.parents.length)
    (Budget.Aggregate.perTerm_positive quarterPositive input.2.parents.length)
  let minimum := max modelFloor paired.modelFloor
  let prepared := CoefficientRequests.prepare bounds input.1.1.target cache forms scalar.accuracy minimum scalarFloor
    (ScalarModels.coefficientTarget input.1.2 (target / 4))
    (ScalarModels.coefficientTarget_positive input.1.2 quarterPositive) sourceAccuracy
  let selected := CoefficientRequests.precisions bounds input.1.1.target cache forms input.1.2
    minimum scalarFloor (target / 4) quarterPositive sourceAccuracy prepared
  exact ⟨cache, paired, prepared, ⟨selected, rfl⟩⟩

namespace NumericalPreparation

variable {trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest)}
variable {bank : OwnerMoves.Entries trace.moves}
variable {scalar : Layer initial trace.budget.fine.selection.stage}
variable {edge : Fin (DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1).length}
variable {input : NumericalInput (count := count) (frame := frame) (basis := basis) (sheet := sheet) bounds
    forms trace bank scalar edge}
variable {modelFloor scalarFloor pairCurrent : Nat} {target : Fraction.Rational} {positive : 0 < target}
variable {sourceAccuracy : AccuracyRequest}

/-- The actual final common Source Selection stage retained by the original numerical preparation. -/
@[expose] def sourceStage
    (values : NumericalPreparation (count := count) bounds forms input modelFloor scalarFloor pairCurrent
        target positive sourceAccuracy) :
    Nat := values.2.2.1.2.1.val.selection.stage

/-- The maximum of the six actual retained Taylor Selection stages on the same numerical preparation. -/
@[expose] def taylorDepth
    (values : NumericalPreparation (count := count) bounds forms input modelFloor scalarFloor pairCurrent
        target positive sourceAccuracy) :
    Nat := values.2.2.2.val.maximum (fun _ entry => entry.2.taylor.stage)

/-- The actual common Source Selection pays the original requested model floor. -/
theorem modelFloor_le
    (values : NumericalPreparation (count := count) bounds forms input modelFloor scalarFloor pairCurrent
        target positive sourceAccuracy) :
    modelFloor ≤ sourceStage bounds forms values := by
  have minimum := CoefficientRequests.Preparation.modelFloor_le bounds input.1.1.target values.1 forms scalar.accuracy
    (max modelFloor values.2.1.modelFloor) scalarFloor
    (ScalarModels.coefficientTarget input.1.2 (target / 4))
    (ScalarModels.coefficientTarget_positive input.1.2
      (Fraction.Order.Field.div_pos_direct positive (by decide +kernel))) sourceAccuracy values.2.2.1
  exact ((Nat.Order.le_max_left modelFloor values.2.1.modelFloor).trans minimum).trans
    values.2.2.1.2.1.val.selection.lower

/-- Every actual parent/six pair Selection is paid by the same retained common Source stage. -/
theorem pairs_le
    (values : NumericalPreparation (count := count) bounds forms input modelFloor scalarFloor pairCurrent
        target positive sourceAccuracy)
    (channel : Fin 6) (parent : Fin input.2.parents.length) :
    (values.2.1.entry channel parent).2.stage ≤ sourceStage bounds forms values := by
  have minimum := CoefficientRequests.Preparation.modelFloor_le bounds input.1.1.target values.1 forms scalar.accuracy
    (max modelFloor values.2.1.modelFloor) scalarFloor
    (ScalarModels.coefficientTarget input.1.2 (target / 4))
    (ScalarModels.coefficientTarget_positive input.1.2
      (Fraction.Order.Field.div_pos_direct positive (by decide +kernel))) sourceAccuracy values.2.2.1
  exact (((values.2.1.stage_le channel parent).trans
    (Nat.Order.le_max_right modelFloor values.2.1.modelFloor)).trans minimum).trans
      values.2.2.1.2.1.val.selection.lower

end NumericalPreparation

/-- Pair the same retained primitives, scalar Pieces and parent-cache heads in their original occurrence order.

The two original finite views allocate only their tuple spines. zipWith
then consumes the same complete supplied heads and literal tails; no Point,
source request, model, selection or scalar Piece factory is run here.
-/
def numericalInputs
    (trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest))
    (bank : OwnerMoves.Entries trace.moves)
    (retained : OwnerMoves.Entries.Primitives bounds bank count)
    (scalar : Layer initial trace.budget.fine.selection.stage) (factory : bank = OwnerMoves.entries trace.moves)
    (caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet trace.moves.spatialBlocks) :
    DependentProduct (DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1)
      (fun edge => NumericalInput (count := count) (frame := frame) (basis := basis) (sheet := sheet)
        bounds forms trace bank scalar edge) :=
  let times := DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1
  let paired := primitivePieces bounds trace bank retained scalar
  let cacheEntries := OwnerMoves.parentCacheEntries ⟨bank, factory⟩ frame basis sheet caches
  DependentProduct.zipWith times paired.val cacheEntries
    (fun edge => NumericalInput (count := count) (frame := frame) (basis := basis) (sheet := sheet)
      bounds forms trace bank scalar edge)
    (fun _ primitivePiece cache _ _ => (primitivePiece, cache))

/-- The complete numerical input forwards the identical original parent-cache view at its bounded occurrence. -/
theorem numericalInputs_cache
    (trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest))
    (bank : OwnerMoves.Entries trace.moves)
    (retained : OwnerMoves.Entries.Primitives bounds bank count)
    (scalar : Layer initial trace.budget.fine.selection.stage) (factory : bank = OwnerMoves.entries trace.moves)
    (caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet trace.moves.spatialBlocks)
    (edge : Fin (DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1).length) :
    let times := DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1
    (DependentProduct.get times (numericalInputs bounds forms trace bank retained scalar factory caches) edge).2 =
      DependentProduct.get times (OwnerMoves.parentCacheEntries ⟨bank, factory⟩ frame basis sheet caches) edge := by
  dsimp only [numericalInputs]
  rewrite [DependentProduct.get_zipWith]
  rfl

/-- The bounded numerical input retains its original scalar Piece at the same physical occurrence. -/
theorem numericalInputs_piece
    (trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest))
    (bank : OwnerMoves.Entries trace.moves)
    (retained : OwnerMoves.Entries.Primitives bounds bank count)
    (scalar : Layer initial trace.budget.fine.selection.stage) (factory : bank = OwnerMoves.entries trace.moves)
    (caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet trace.moves.spatialBlocks)
    (edge : Fin (DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1).length) :
    let times := DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1
    (DependentProduct.get times (numericalInputs bounds forms trace bank retained scalar factory caches) edge).1.2 =
      scalar.pieces[edge.val]'((scalar.count.trans
        (DyadicSteps.tail_length trace.budget.fine.selection.stage 0 1).symm).symm ▸ edge.isLt) := by
  dsimp only [numericalInputs]
  rewrite [DependentProduct.get_zipWith]
  exact congrArg Prod.snd ((primitivePieces bounds trace bank retained scalar).property edge)

/-- The original ordered product of actual row preparations on their same stored input tuples.

Only the complete dependent type is named. Every entry is the unchanged
Sigma of original Cache, PairSelections, Preparation and Precisions owners.
-/
@[expose] def NumericalRows
    {trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest)}
    {bank : OwnerMoves.Entries trace.moves} {scalar : Layer initial trace.budget.fine.selection.stage}
    (inputs : DependentProduct (DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1)
      (fun edge => NumericalInput (count := count) (frame := frame) (basis := basis) (sheet := sheet)
        bounds forms trace bank scalar edge))
    (modelFloor scalarFloor pairCurrent : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest) : Type 1 :=
  let times := DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1
  DependentProduct times (fun edge => NumericalPreparation (count := count) bounds forms
    (DependentProduct.get times inputs edge) modelFloor scalarFloor pairCurrent target positive sourceAccuracy)

/-- Materialize every actual parent/six numerical preparation before acquiring any scalar Layer observations.

The structural map consumes the supplied actual input tuples directly.
Each row retains its own computed pair selections, one common Source
Request and all six Precisions; bounded getters never run these factories.
-/
def numericalRows
    {trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest)}
    {bank : OwnerMoves.Entries trace.moves} {scalar : Layer initial trace.budget.fine.selection.stage}
    (inputs : DependentProduct (DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1)
      (fun edge => NumericalInput (count := count) (frame := frame) (basis := basis) (sheet := sheet)
        bounds forms trace bank scalar edge))
    (modelFloor scalarFloor pairCurrent : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest) :
    NumericalRows (count := count) bounds forms inputs modelFloor scalarFloor pairCurrent target positive
      sourceAccuracy :=
  let times := DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1
  DependentProduct.map times inputs
    (fun _ input => NumericalPreparation (count := count) bounds forms input modelFloor scalarFloor pairCurrent
      target positive sourceAccuracy)
    (fun _ input => prepareNumerical bounds forms input modelFloor scalarFloor pairCurrent target positive
        sourceAccuracy)

/-- Read both global maxima from the same retained actual row Selection stages before any scalar acquisition.

The two finite scalar lists read existing fields only. Their original
listMaximum folds neither select nor request nor refine a numerical model.
-/
def numericalFloors
    {trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest)}
    {bank : OwnerMoves.Entries trace.moves} {scalar : Layer initial trace.budget.fine.selection.stage}
    {inputs : DependentProduct (DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1)
      (fun edge => NumericalInput (count := count) (frame := frame) (basis := basis) (sheet := sheet)
        bounds forms trace bank scalar edge)}
    {modelFloor scalarFloor pairCurrent : Nat} {target : Fraction.Rational} {positive : 0 < target}
    {sourceAccuracy : AccuracyRequest}
    (rows : NumericalRows (count := count) bounds forms inputs modelFloor scalarFloor pairCurrent target positive
      sourceAccuracy) : Nat × Nat :=
  let times := DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1
  let sourceStages := DependentProduct.mapToList times rows (fun _ values =>
    NumericalPreparation.sourceStage bounds forms values)
  let taylorStages := DependentProduct.mapToList times rows (fun _ values =>
    NumericalPreparation.taylorDepth bounds forms values)
  (max modelFloor (Data.Nat.List.Maximum.listMaximum sourceStages),
    max scalarFloor (Data.Nat.List.Maximum.listMaximum taylorStages))

/-- Both computed floors retain the caller's original model and scalar lower bounds. -/
theorem numericalFloors_minimum
    {trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest)}
    {bank : OwnerMoves.Entries trace.moves} {scalar : Layer initial trace.budget.fine.selection.stage}
    {inputs : DependentProduct (DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1)
      (fun edge => NumericalInput (count := count) (frame := frame) (basis := basis) (sheet := sheet)
        bounds forms trace bank scalar edge)}
    {modelFloor scalarFloor pairCurrent : Nat} {target : Fraction.Rational} {positive : 0 < target}
    {sourceAccuracy : AccuracyRequest}
    (rows : NumericalRows (count := count) bounds forms inputs modelFloor scalarFloor pairCurrent target positive
      sourceAccuracy) :
    modelFloor ≤ (numericalFloors bounds forms rows).1 ∧
      scalarFloor ≤ (numericalFloors bounds forms rows).2 := by
  change modelFloor ≤ max modelFloor _ ∧ scalarFloor ≤ max scalarFloor _
  exact ⟨Nat.Order.le_max_left _ _, Nat.Order.le_max_left _ _⟩

/-- Both computed global floors cover each identical retained row's actual Source and Taylor stages. -/
theorem numericalFloors_paid
    {trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest)}
    {bank : OwnerMoves.Entries trace.moves} {scalar : Layer initial trace.budget.fine.selection.stage}
    {inputs : DependentProduct (DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1)
      (fun edge => NumericalInput (count := count) (frame := frame) (basis := basis) (sheet := sheet)
        bounds forms trace bank scalar edge)}
    {modelFloor scalarFloor pairCurrent : Nat} {target : Fraction.Rational} {positive : 0 < target}
    {sourceAccuracy : AccuracyRequest}
    (rows : NumericalRows (count := count) bounds forms inputs modelFloor scalarFloor pairCurrent target positive
      sourceAccuracy)
    (edge : Fin (DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1).length) :
    NumericalPreparation.sourceStage bounds forms (DependentProduct.get _ rows edge) ≤
        (numericalFloors bounds forms rows).1 ∧
      NumericalPreparation.taylorDepth bounds forms (DependentProduct.get _ rows edge) ≤
        (numericalFloors bounds forms rows).2 := by
  let times := DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1
  have bounded (read : (index : Fin times.length) →
      NumericalPreparation (count := count) bounds forms (DependentProduct.get times inputs index)
        modelFloor scalarFloor pairCurrent target positive sourceAccuracy → Nat) :
      read edge (DependentProduct.get times rows edge) ≤
        Data.Nat.List.Maximum.listMaximum (DependentProduct.mapToList times rows read) := by
    let values := DependentProduct.mapToList times rows read
    have same := DependentProduct.get_mapToList times rows read edge
    have member : read edge (DependentProduct.get times rows edge) ∈ values :=
      Eq.mp (congrArg (fun value => value ∈ values) same)
        (List.getElem_mem ((DependentProduct.length_mapToList times rows read).symm ▸ edge.isLt))
    exact Data.Nat.List.Maximum.member_le_listMaximum values _ member
  exact ⟨(bounded (fun _ values => NumericalPreparation.sourceStage bounds forms values)).trans
      (Nat.Order.le_max_right _ _),
    (bounded (fun _ values => NumericalPreparation.taylorDepth bounds forms values)).trans (Nat.Order.le_max_right _ _)⟩

/-- The same retained numerical rows, computed global floors and original whole source acquisition.

This exact Sigma retains the actual input tuples, original preparations
and both once-computed maxima. Its Source result belongs to the same
whole ParentCaches, original global Targets and literal covered Blocks.
-/
@[expose] def NumericalSources
    (trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest))
    (bank : OwnerMoves.Entries trace.moves)
    (retained : OwnerMoves.Entries.Primitives bounds bank count)
    (scalar : Layer initial trace.budget.fine.selection.stage) (factory : bank = OwnerMoves.entries trace.moves)
    (caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet trace.moves.spatialBlocks)
    (modelFloor scalarFloor pairCurrent : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest) (requestStage : Nat) :=
  let times := DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1
  let rowTarget := Budget.Aggregate.perTerm target times.length
  let rowPositive := Budget.Aggregate.perTerm_positive positive times.length
  Σ inputs : {actual : DependentProduct times
        (fun edge => NumericalInput (count := count) (frame := frame) (basis := basis) (sheet := sheet)
          bounds forms trace bank scalar edge) //
      actual = numericalInputs bounds forms trace bank retained scalar factory caches},
  Σ rows : {actual : NumericalRows (count := count) bounds forms inputs.val modelFloor scalarFloor pairCurrent
        rowTarget rowPositive sourceAccuracy //
      actual = numericalRows bounds forms inputs.val modelFloor scalarFloor pairCurrent
        rowTarget rowPositive sourceAccuracy},
  Σ floors : {actual : Nat × Nat // actual = numericalFloors bounds forms rows.val},
    {actual : PreparedParents.BlockSources caches floors.val.1 requestStage //
      actual = PreparedParents.blockSources caches floors.val.1 requestStage}

/-- Compute every row payment and both global floors before one original global source acquisition.

The same input, preparation and Selection banks are retained once. The
original source producer consumes the actual global floor and preserves
its whole parent chain, count allocation, cached source cells and six row
lists. No scalar Point or Layer acquisition runs in this preparation.
-/
def prepareSources
    (trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest))
    (bank : OwnerMoves.Entries trace.moves)
    (retained : OwnerMoves.Entries.Primitives bounds bank count)
    (scalar : Layer initial trace.budget.fine.selection.stage) (factory : bank = OwnerMoves.entries trace.moves)
    (caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet trace.moves.spatialBlocks)
    (modelFloor scalarFloor pairCurrent : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest) (requestStage : Nat) :
    NumericalSources bounds forms trace bank retained scalar factory caches modelFloor scalarFloor pairCurrent
      target positive sourceAccuracy requestStage :=
  let times := DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1
  let rowTarget := Budget.Aggregate.perTerm target times.length
  have rowPositive : 0 < rowTarget := Budget.Aggregate.perTerm_positive positive times.length
  let inputs := numericalInputs bounds forms trace bank retained scalar factory caches
  let rows := numericalRows bounds forms inputs modelFloor scalarFloor pairCurrent rowTarget rowPositive
    sourceAccuracy
  let floors := numericalFloors bounds forms rows
  let sources := PreparedParents.blockSources caches floors.1 requestStage
  ⟨⟨inputs, rfl⟩, ⟨rows, rfl⟩, ⟨floors, rfl⟩, ⟨sources, rfl⟩⟩

/-- The actual scalar-factory input tuple has the two same original dyadic endpoints at every retained occurrence.

The complete proposition names the original primitive/Piece view and its
whole scalar factory equation. Its conclusion is geometric incidence,
including strict endpoint order, rather than a numerical comparison.
-/
@[expose] def NumericalInputsEndpoints : Prop :=
  ∀ (trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest))
    (bank : OwnerMoves.Entries trace.moves)
    (retained : OwnerMoves.Entries.Primitives bounds bank count)
    (scalar : Layer initial trace.budget.fine.selection.stage) (factory : bank = OwnerMoves.entries trace.moves)
    (caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet trace.moves.spatialBlocks)
    (_scalarFactory : scalar = initial.layerAt trace.budget.fine.selection.stage)
    (_unitSpan : initial.span.lower = 0 ∧ initial.span.upper = 1)
    (edge : Fin (DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1).length),
    let times := DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1
    let input := DependentProduct.get times
      (numericalInputs bounds forms trace bank retained scalar factory caches) edge
    input.1.2.span.lower = DyadicTrace.indexed 0 times edge.castSucc ∧
      input.1.2.span.upper = DyadicTrace.indexed 0 times edge.succ ∧
        DyadicTrace.indexed 0 times edge.castSucc < DyadicTrace.indexed 0 times edge.succ

/-- Read actual occurrence endpoints from the original Piece factory and complete stored primitive/Piece view. -/
theorem numericalInputs_endpoints :
    NumericalInputsEndpoints (originalSource := originalSource) (initial := initial)
      (count := count) (frame := frame) (basis := basis) (sheet := sheet) bounds forms := by
  intro trace bank retained scalar factory caches scalarFactory unitSpan edge
  cases scalarFactory
  let depth := trace.budget.fine.selection.stage
  let scalar := initial.layerAt depth
  let times := DyadicTrace.tail depth (0 : Fraction.Rational) 1
  have same : scalar.pieces.length = times.length :=
    scalar.count.trans (DyadicSteps.tail_length depth 0 1).symm
  let paired := primitivePieces bounds trace bank retained scalar
  have pieceEq : (DependentProduct.get times
      (numericalInputs bounds forms trace bank retained scalar factory caches) edge).1.2 =
        scalar.pieces[edge.val]'(same.symm ▸ edge.isLt) := by
    dsimp only [numericalInputs]
    rewrite [DependentProduct.get_zipWith]
    exact congrArg (fun entry => entry.2) (paired.property edge)
  have endpoints := initial.layerAt_endpoints depth
  rewrite [unitSpan.1, unitSpan.2] at endpoints
  have starts := congrArg (fun piece : Piece (forms.get 0) leg.actual scalar.accuracy => piece.span.lower) pieceEq
  have finishes := congrArg (fun piece : Piece (forms.get 0) leg.actual scalar.accuracy => piece.span.upper) pieceEq
  have member : (scalar.pieces[edge.val]'(same.symm ▸ edge.isLt)).span ∈
      Data.Rat.Interval.Bisection.parts depth initial.span := by
    rewrite [← initial.layerAt_spans depth]
    exact Data.List.Map.mem_map.mpr ⟨_, List.getElem_mem (same.symm ▸ edge.isLt), rfl⟩
  have originalProper : initial.span.lower < initial.span.upper := by
    rewrite [unitSpan.1, unitSpan.2]
    exact (by decide +kernel : (0 : Fraction.Rational) < 1)
  have proper := Data.Rat.Interval.Bisection.parts_proper depth initial.span originalProper member
  refine ⟨starts.trans (endpoints edge).1.symm, finishes.trans (endpoints edge).2.symm, ?_⟩
  rewrite [(endpoints edge).1, (endpoints edge).2]
  exact proper

/-- The same actual scalar tuple's exact original two endpoint incidences and strict edge order. -/
@[expose] def NumericalInput.Endpoints
    {trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest)}
    {bank : OwnerMoves.Entries trace.moves} {scalar : Layer initial trace.budget.fine.selection.stage}
    {edge : Fin (DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1).length}
    (input : NumericalInput (count := count) (frame := frame) (basis := basis) (sheet := sheet)
      bounds forms trace bank scalar edge) : Prop :=
  let times := DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1
  input.1.2.span.lower = DyadicTrace.indexed 0 times edge.castSucc ∧
    input.1.2.span.upper = DyadicTrace.indexed 0 times edge.succ ∧
      DyadicTrace.indexed 0 times edge.castSucc < DyadicTrace.indexed 0 times edge.succ

/-- All supplied actual numerical inputs have their original occurrence endpoints. -/
@[expose] def NumericalSpans
    (trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest))
    (bank : OwnerMoves.Entries trace.moves) (scalar : Layer initial trace.budget.fine.selection.stage)
    (inputs : DependentProduct (DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1)
      (fun edge => NumericalInput (count := count) (frame := frame) (basis := basis) (sheet := sheet)
        bounds forms trace bank scalar edge)) : Prop :=
  ∀ edge, NumericalInput.Endpoints bounds forms (DependentProduct.get _ inputs edge)

namespace NumericalPreparation

variable {trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest)}
variable {bank : OwnerMoves.Entries trace.moves}
variable {scalar : Layer initial trace.budget.fine.selection.stage}
variable {edge : Fin (DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1).length}
variable {input : NumericalInput (count := count) (frame := frame) (basis := basis) (sheet := sheet)
  bounds forms trace bank scalar edge}
variable {modelFloor scalarFloor pairCurrent : Nat} {target : Fraction.Rational} {positive : 0 < target}
variable {sourceAccuracy : AccuracyRequest}

/-- The original acquired Layer bank and six typed request projections on the same supplied numerical row.

The subtype retains the whole original factory result. Its preparation,
Source Request, powers and six Precisions are the supplied cached values;
only the original chronological scalar acquisition runs at the later depth.
-/
@[expose] def Layers
    (values : NumericalPreparation (count := count) bounds forms input modelFloor scalarFloor pairCurrent
      target positive sourceAccuracy) (depth : Nat) (span : NumericalInput.Endpoints bounds forms input) : Type 2 :=
  let source := curveSource bounds input.1.1.target
  let minimum := max modelFloor values.2.1.modelFloor
  let quarterPositive := Fraction.Order.Field.div_pos_direct positive (by decide +kernel : (0 : Fraction.Rational) < 4)
  Σ layer : {actual : CoefficientRequests.LayerBank bounds input.1.1 source values.1 forms input.1.2 minimum
        scalarFloor (target / 4) quarterPositive sourceAccuracy depth //
      actual = CoefficientRequests.layerBank bounds input.1.1 source values.1 forms input.1.2
        ⟨span.1, span.2.1⟩ span.2.2 minimum scalarFloor (target / 4) quarterPositive sourceAccuracy
        values.2.2.1 values.2.2.2 depth},
    CoefficientRequests.LayerBank.Requests bounds layer.val

/-- Acquire one original scalar row at the chosen depth from its complete retained preparation and six Precisions. -/
def acquireLayers
    (values : NumericalPreparation (count := count) bounds forms input modelFloor scalarFloor pairCurrent
      target positive sourceAccuracy) (depth : Nat) (span : NumericalInput.Endpoints bounds forms input) :
    Layers bounds forms values depth span :=
  let source := curveSource bounds input.1.1.target
  let minimum := max modelFloor values.2.1.modelFloor
  have quarterPositive : 0 < target / 4 := Fraction.Order.Field.div_pos_direct positive (by decide +kernel)
  let layer := CoefficientRequests.layerBank bounds input.1.1 source values.1 forms input.1.2
    ⟨span.1, span.2.1⟩ span.2.2 minimum scalarFloor (target / 4) quarterPositive sourceAccuracy
    values.2.2.1 values.2.2.2 depth
  let requests := CoefficientRequests.LayerBank.requests bounds layer
  ⟨⟨layer, rfl⟩, requests⟩

end NumericalPreparation

/-- The original ordered product of actual same-depth Layer banks and all six cached typed request banks. -/
@[expose] def NumericalLayerRows
    {trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest)}
    {bank : OwnerMoves.Entries trace.moves} {scalar : Layer initial trace.budget.fine.selection.stage}
    {inputs : DependentProduct (DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1)
      (fun edge => NumericalInput (count := count) (frame := frame) (basis := basis) (sheet := sheet)
        bounds forms trace bank scalar edge)}
    {modelFloor scalarFloor pairCurrent : Nat} {target : Fraction.Rational} {positive : 0 < target}
    {sourceAccuracy : AccuracyRequest}
    (rows : NumericalRows (count := count) bounds forms inputs modelFloor scalarFloor pairCurrent target positive
      sourceAccuracy) (depth : Nat) (spans : NumericalSpans bounds forms trace bank scalar inputs) : Type 2 :=
  let times := DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1
  DependentProduct times (fun edge =>
    NumericalPreparation.Layers bounds forms (DependentProduct.get times rows edge) depth (spans edge))

/-- Consume both original stored row banks structurally and acquire the six typed Layers once per occurrence.

The actual input and preparation heads are supplied directly. Erased
equality transport retains both whole payloads. The original Layer factory
still reads its two nominal owner indices from the retained trace banks;
no selection, Source Request or preparation is repeated.
-/
def acquireLayerRows
    {trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest)}
    {bank : OwnerMoves.Entries trace.moves} {scalar : Layer initial trace.budget.fine.selection.stage}
    (inputs : DependentProduct (DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1)
      (fun edge => NumericalInput (count := count) (frame := frame) (basis := basis) (sheet := sheet)
        bounds forms trace bank scalar edge))
    {modelFloor scalarFloor pairCurrent : Nat} {target : Fraction.Rational} {positive : 0 < target}
    {sourceAccuracy : AccuracyRequest}
    (rows : NumericalRows (count := count) bounds forms inputs modelFloor scalarFloor pairCurrent target positive
      sourceAccuracy) (depth : Nat) (spans : NumericalSpans bounds forms trace bank scalar inputs) :
    NumericalLayerRows bounds forms rows depth spans :=
  let times := DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1
  DependentProduct.zipWith times inputs rows
    (fun edge => NumericalPreparation.Layers bounds forms (DependentProduct.get times rows edge) depth (spans edge))
    (fun edge input values inputEq valuesEq => by
      let actualValues : NumericalPreparation (count := count) bounds forms input
          modelFloor scalarFloor pairCurrent target positive sourceAccuracy :=
        Eq.mp (congrArg (fun actual => NumericalPreparation (count := count) bounds forms actual
          modelFloor scalarFloor pairCurrent target positive sourceAccuracy) inputEq.symm) values
      have actualSpan : NumericalInput.Endpoints bounds forms input :=
        Eq.mp (congrArg (fun actual => NumericalInput.Endpoints bounds forms actual) inputEq.symm) (spans edge)
      let made := NumericalPreparation.acquireLayers bounds forms actualValues depth actualSpan
      have same : NumericalPreparation.Layers bounds forms actualValues depth actualSpan =
          NumericalPreparation.Layers bounds forms (DependentProduct.get times rows edge) depth (spans edge) := by
        cases inputEq
        cases valuesEq
        rfl
      exact Eq.mp same made)

/-- The retained global source acquisition has the same original scalar occurrence endpoints. -/
theorem NumericalSources.inputSpans
    {trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest)}
    {bank : OwnerMoves.Entries trace.moves} {retained : OwnerMoves.Entries.Primitives bounds bank count}
    {scalar : Layer initial trace.budget.fine.selection.stage} {factory : bank = OwnerMoves.entries trace.moves}
    {caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet trace.moves.spatialBlocks}
    {modelFloor scalarFloor pairCurrent : Nat} {target : Fraction.Rational} {positive : 0 < target}
    {sourceAccuracy : AccuracyRequest} {requestStage : Nat}
    (prepared : NumericalSources bounds forms trace bank retained scalar factory caches modelFloor scalarFloor
      pairCurrent target positive sourceAccuracy requestStage)
    (scalarFactory : scalar = initial.layerAt trace.budget.fine.selection.stage)
    (unitSpan : initial.span.lower = 0 ∧ initial.span.upper = 1) :
    NumericalSpans bounds forms trace bank scalar prepared.1.val := by
  have actual := numericalInputs_endpoints (count := count) bounds forms
    trace bank retained scalar factory caches scalarFactory unitSpan
  exact Eq.mp (congrArg (fun inputs => NumericalSpans bounds forms trace bank scalar inputs)
    prepared.1.property.symm) actual

/-- Acquire every scalar row at the once-computed global Taylor floor after the single whole source acquisition.

This consumes the same stored preparation, Selection and primitive banks.
The only endpoint conditions are read from the original scalar factory;
no successful sample comparison or domain certificate is an input.
-/
def NumericalSources.acquireLayers
    {trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest)}
    {bank : OwnerMoves.Entries trace.moves} {retained : OwnerMoves.Entries.Primitives bounds bank count}
    {scalar : Layer initial trace.budget.fine.selection.stage} {factory : bank = OwnerMoves.entries trace.moves}
    {caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet trace.moves.spatialBlocks}
    {modelFloor scalarFloor pairCurrent : Nat} {target : Fraction.Rational} {positive : 0 < target}
    {sourceAccuracy : AccuracyRequest} {requestStage : Nat}
    (prepared : NumericalSources bounds forms trace bank retained scalar factory caches modelFloor scalarFloor
      pairCurrent target positive sourceAccuracy requestStage)
    (scalarFactory : scalar = initial.layerAt trace.budget.fine.selection.stage)
    (unitSpan : initial.span.lower = 0 ∧ initial.span.upper = 1) :
    NumericalLayerRows bounds forms prepared.2.1.val prepared.2.2.1.val.2
      (prepared.inputSpans bounds forms scalarFactory unitSpan) :=
  acquireLayerRows bounds forms prepared.1.val prepared.2.1.val prepared.2.2.1.val.2
    (prepared.inputSpans bounds forms scalarFactory unitSpan)

namespace NumericalPreparation.Layers

/-- The actual acquired Layer uses an already-paid later depth exactly, retaining its supplied whole Precision bank. -/
theorem depth_eq
    {trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest)}
    {bank : OwnerMoves.Entries trace.moves} {scalar : Layer initial trace.budget.fine.selection.stage}
    {edge : Fin (DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1).length}
    {input : NumericalInput (count := count) (frame := frame) (basis := basis) (sheet := sheet)
      bounds forms trace bank scalar edge}
    {modelFloor scalarFloor pairCurrent : Nat} {target : Fraction.Rational} {positive : 0 < target}
    {sourceAccuracy : AccuracyRequest}
    (values : NumericalPreparation (count := count) bounds forms input modelFloor scalarFloor pairCurrent
      target positive sourceAccuracy) (depth : Nat) (span : NumericalInput.Endpoints bounds forms input)
    (acquired : NumericalPreparation.Layers bounds forms values depth span)
    (paid : NumericalPreparation.taylorDepth bounds forms values ≤ depth) :
    CoefficientRequests.Precisions.depth bounds acquired.1.val.2.1.val depth = depth := by
  let source := curveSource bounds input.1.1.target
  let minimum := max modelFloor values.2.1.modelFloor
  have quarterPositive : 0 < target / 4 := Fraction.Order.Field.div_pos_direct positive (by decide +kernel)
  have whole := congrArg
    (fun actual : CoefficientRequests.LayerBank bounds input.1.1 source values.1 forms input.1.2 minimum
      scalarFloor (target / 4) quarterPositive sourceAccuracy depth => actual.2.1.val) acquired.1.property
  have scalar := CoefficientRequests.layerBank_precisions_values bounds input.1.1 source values.1 forms input.1.2
    ⟨span.1, span.2.1⟩ span.2.2 minimum scalarFloor (target / 4) quarterPositive sourceAccuracy
    values.2.2.1 values.2.2.2 depth
  have same := whole.trans scalar
  have chosen := CoefficientRequests.Precisions.depth_eq_of_le
    (cached := input.1.1.target) (forms := forms) (initial := input.1.2)
    (modelFloor := minimum) (scalarFloor := scalarFloor) (target := target / 4) (positive := quarterPositive)
    bounds values.2.2.2.val depth paid
  exact (congrArg (fun selected => CoefficientRequests.Precisions.depth bounds selected depth) same).trans chosen

/-- The same retained numerical preparation pays its independently floored actual source row and returned Layer. -/
private theorem source_accurate
    {trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest)}
    {bank : OwnerMoves.Entries trace.moves} {scalar : Layer initial trace.budget.fine.selection.stage}
    {edge : Fin (DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1).length}
    {input : NumericalInput (count := count) (frame := frame) (basis := basis) (sheet := sheet)
      bounds forms trace bank scalar edge}
    {modelFloor scalarFloor pairCurrent : Nat} {target : Fraction.Rational} {positive : 0 < target}
    {sourceAccuracy : AccuracyRequest}
    (values : NumericalPreparation (count := count) bounds forms input modelFloor scalarFloor pairCurrent
      target positive sourceAccuracy) (depth : Nat) (span : NumericalInput.Endpoints bounds forms input)
    (acquired : NumericalPreparation.Layers bounds forms values depth span)
    {baseStart baseFinish : Geometry.Path.Gaussian.Lifted.Basic.LiftedPoint 2}
    {path : Geometry.Path.Gaussian.Lifted.Basic.LiftedPath 2 baseStart baseFinish} {stage sourceFloor : Nat}
    (targets : Integration.Path.Primitive.PrimitiveEdge.CellEndpoints.Targets path stage)
    (row : DependentVector (fun _ : Fin 6 => List Integration.Polynomial.Gaussian.Cell.Basic.CellModel))
    (origin : PreparedParents.CellRow (frame := frame) (basis := basis) (count := 1)
      input.2.covered sourceFloor targets row)
    (floorPaid : NumericalPreparation.sourceStage bounds forms values ≤ sourceFloor) (channel : Fin 6) :
    Norm.Basic.normSq
      ((PathModel.mk
          (row.get channel)).integralSample -
        (CoefficientRequests.LayerBank.layer bounds acquired.1.val channel).model.integralSample) < target := by
  rcases origin with ⟨spatial, stored⟩
  let source := curveSource bounds input.1.1.target
  let minimum := max modelFloor values.2.1.modelFloor
  have quarterPositive : 0 < target / 4 := Fraction.Order.Field.div_pos_direct positive (by decide +kernel)
  let saved := acquired.1.val
  have whole := congrArg
    (fun actual : CoefficientRequests.LayerBank bounds input.1.1 source values.1 forms input.1.2 minimum
      scalarFloor (target / 4) quarterPositive sourceAccuracy depth => actual.1) acquired.1.property
  have prepared := CoefficientRequests.layerBank_preparation bounds input.1.1 source values.1 forms input.1.2
    ⟨span.1, span.2.1⟩ span.2.2 minimum scalarFloor (target / 4) quarterPositive sourceAccuracy
    values.2.2.1 values.2.2.2 depth
  have preparationSame : saved.1 = values.2.2.1 := whole.trans prepared
  have commonStage : saved.1.2.1.val.selection.stage = NumericalPreparation.sourceStage bounds forms values :=
    congrArg (fun actual => actual.2.1.val.selection.stage) preparationSame
  let covered := Covered.build (trace.geometries.get edge) (bank.get edge).1
  let points := OwnerMove.PrimitiveTarget.parentPoints bounds input.1.1.target input.1.1.sourcePoint
    frame covered input.2 ⟨input.1.1.reference, input.1.1.reference_eq⟩
  have payments : ∀ (selected : Fin 6) (parent : Fin input.2.parents.length),
      (values.2.1.entry selected parent).2.stage ≤ saved.1.2.1.val.selection.stage ∧
      (values.2.1.entry selected parent).2.stage ≤
        (spatial.entry parent).preparation.attached.source.selection.stage := by
    intro selected parent
    have pairPaid := NumericalPreparation.pairs_le bounds forms values selected parent
    exact ⟨pairPaid.trans_eq commonStage.symm,
      (pairPaid.trans floorPaid).trans (PreparedParent.floor_le_model_stage (spatial.entry parent))⟩
  have bounded := CoefficientRequests.LayerBank.ParentSources.scalar_accurate bounds input.1.1 source values.1 forms
    input.1.2 minimum scalarFloor target positive sourceAccuracy covered input.2 points targets values.2.1
    saved spatial payments acquired.2 ⟨span.1, span.2.1⟩ channel
  have rowCells := (congrArg (fun actual => actual.get channel) stored).trans
    (DependentVector.ofFn_get (fun selected : Fin 6 => PreparedParents.cells spatial selected) channel)
  have sourceCells := PreparedParents.sources_cells input.2.covered spatial input.2.centeredChain channel
  have sampleSame := congrArg
    (fun cells => (PathModel.mk cells).integralSample)
    (rowCells.trans sourceCells.symm)
  exact (congrArg (fun sample => Norm.Basic.normSq
    (sample - (CoefficientRequests.LayerBank.layer bounds acquired.1.val channel).model.integralSample))
    sampleSame).trans_lt bounded

end NumericalPreparation.Layers

/-- Every actual acquired scalar row has the same once-computed global Taylor depth.

The original whole Layer factory equation retains the supplied Precision
vector. The global finite maximum pays each identical stored Taylor stage,
so the original later-floor operation returns that global depth literally.
-/
@[expose] def NumericalSources.CommonDepth : Prop :=
  ∀ (trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest))
    (bank : OwnerMoves.Entries trace.moves) (retained : OwnerMoves.Entries.Primitives bounds bank count)
    (scalar : Layer initial trace.budget.fine.selection.stage) (factory : bank = OwnerMoves.entries trace.moves)
    (caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet trace.moves.spatialBlocks)
    (modelFloor scalarFloor pairCurrent : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest) (requestStage : Nat)
    (prepared : NumericalSources bounds forms trace bank retained scalar factory caches modelFloor scalarFloor
      pairCurrent target positive sourceAccuracy requestStage)
    (scalarFactory : scalar = initial.layerAt trace.budget.fine.selection.stage)
    (unitSpan : initial.span.lower = 0 ∧ initial.span.upper = 1)
    (layers : NumericalLayerRows bounds forms prepared.2.1.val prepared.2.2.1.val.2
      (prepared.inputSpans bounds forms scalarFactory unitSpan))
    (edge : Fin (DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1).length),
    let times := DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1
    CoefficientRequests.Precisions.depth bounds (DependentProduct.get times layers edge).1.val.2.1.val
      prepared.2.2.1.val.2 = prepared.2.2.1.val.2

/-- The computed global maximum pays the common depth of every actual returned scalar Layer bank. -/
theorem NumericalSources.layers_depth :
    NumericalSources.CommonDepth (originalSource := originalSource) (initial := initial)
      (count := count) (frame := frame) (basis := basis) (sheet := sheet) bounds forms := by
  intro trace bank retained scalar factory caches modelFloor scalarFloor pairCurrent target positive
    sourceAccuracy requestStage prepared scalarFactory unitSpan layers edge
  have paid := numericalFloors_paid bounds forms prepared.2.1.val edge
  have floorEq := congrArg (fun floors : Nat × Nat => floors.2) prepared.2.2.1.property
  exact NumericalPreparation.Layers.depth_eq bounds forms
    (DependentProduct.get _ prepared.2.1.val edge) prepared.2.2.1.val.2
    (prepared.inputSpans bounds forms scalarFactory unitSpan edge)
    (DependentProduct.get _ layers edge) (paid.2.trans_eq floorEq.symm)

/-- The actual stored global source rows belong to each numerical input's identical retained parent cache.

The complete proposition retains the original input and global-source
factory equations. Each existential certifies the actual split source
product on its unchanged cover, source floor and global Targets; it
contains no numerical bound or alternative owner.
-/
@[expose] def NumericalSources.RowOrigins : Prop :=
  ∀ (trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest))
    (bank : OwnerMoves.Entries trace.moves) (retained : OwnerMoves.Entries.Primitives bounds bank count)
    (scalar : Layer initial trace.budget.fine.selection.stage) (factory : bank = OwnerMoves.entries trace.moves)
    (caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet trace.moves.spatialBlocks)
    (modelFloor scalarFloor pairCurrent : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest) (requestStage : Nat)
    (values : NumericalSources bounds forms trace bank retained scalar factory caches modelFloor scalarFloor
      pairCurrent target positive sourceAccuracy requestStage)
    (edge : Fin (DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1).length),
    let times := DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1
    let sources := values.2.2.2.val
    let input := DependentProduct.get times values.1.val edge
    ∃ inside : edge.val < sources.2.2.2.2.val.length,
      PreparedParents.CellRow (frame := frame) (basis := basis) (count := 1)
        (parents := input.2.parents) input.2.covered values.2.2.1.val.1 sources.2.1.val
        (sources.2.2.2.2.val[edge.val]'inside)

/-- Read the same split source product at every actual materialized numerical-input occurrence. -/
theorem NumericalSources.row_origins :
    NumericalSources.RowOrigins (originalSource := originalSource) (initial := initial)
      (count := count) (frame := frame) (basis := basis) (sheet := sheet) bounds forms := by
  intro trace bank retained scalar factory caches modelFloor scalarFloor pairCurrent target positive
    sourceAccuracy requestStage values edge
  let times := DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1
  let sources := values.2.2.2.val
  let original := sources.2.2.1.val
  have sameRows := OwnerMoves.sourceRows (moves := trace.moves) (original := sources.1.val.path)
    (stage := requestStage) (floor := values.2.2.1.val.1) (targets := sources.2.1.val)
    ⟨bank, factory⟩ frame basis sheet caches original
  let atRow : List (DependentVector (fun _ : Fin 6 =>
      List Integration.Polynomial.Gaussian.Cell.Basic.CellModel)) → Prop := fun rows =>
    ∃ inside : edge.val < rows.length,
      PreparedParents.CellRow (frame := frame) (basis := basis) (count := 1)
        (DependentProduct.get times (OwnerMoves.parentCacheEntries ⟨bank, factory⟩ frame basis sheet caches)
          edge).covered values.2.2.1.val.1 sources.2.1.val (rows[edge.val]'inside)
  have row : atRow (PreparedParents.blockRows caches original) :=
    Eq.mpr (congrArg atRow (PreparedParents.blockRows_eq_mapBanks caches original))
      (sameRows.2 edge)
  rcases row with ⟨inside, actual⟩
  have cacheSame : (DependentProduct.get times values.1.val edge).2 =
      DependentProduct.get times (OwnerMoves.parentCacheEntries ⟨bank, factory⟩ frame basis sheet caches) edge :=
    (congrArg (fun inputs : DependentProduct times (fun edge =>
      NumericalInput (count := count) (frame := frame) (basis := basis) (sheet := sheet)
        bounds forms trace bank scalar edge) => (DependentProduct.get times inputs edge).2)
      values.1.property).trans (numericalInputs_cache bounds forms trace bank retained scalar factory caches edge)
  let value := (PreparedParents.blockRows caches original)[edge.val]'inside
  have propagated := Eq.mpr (congrArg
    (fun cache : bank.ParentCacheAt frame basis sheet edge =>
      PreparedParents.CellRow (frame := frame) (basis := basis) (count := 1)
        cache.covered values.2.2.1.val.1 sources.2.1.val value) cacheSame) actual
  have stored := sources.2.2.2.2.property.1
  have bound : edge.val < sources.2.2.2.2.val.length :=
    Eq.mpr (congrArg (fun rows => edge.val < rows.length) stored) inside
  refine ⟨bound, ?_⟩
  exact Eq.mpr (congrArg (fun row =>
    PreparedParents.CellRow (frame := frame) (basis := basis) (count := 1)
      (DependentProduct.get times values.1.val edge).2.covered
      values.2.2.1.val.1 sources.2.1.val row) (getElem_congr stored rfl bound)) propagated

/-- The actual global source rows and returned six-channel scalar Layers meet their computed count-paid row targets.

The original ordinal source readback provides the same covered parent
cache. Its global model floor pays both actual paired stages, while the
same retained Preparation and Precision values supply every scalar Layer
and request. No numerical comparison or successful payment is an input.
-/
@[expose] def NumericalSources.RowsAccuracy : Prop :=
  ∀ (trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest))
    (bank : OwnerMoves.Entries trace.moves) (retained : OwnerMoves.Entries.Primitives bounds bank count)
    (scalar : Layer initial trace.budget.fine.selection.stage) (factory : bank = OwnerMoves.entries trace.moves)
    (caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet trace.moves.spatialBlocks)
    (modelFloor scalarFloor pairCurrent : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest) (requestStage : Nat)
    (values : NumericalSources bounds forms trace bank retained scalar factory caches modelFloor scalarFloor
      pairCurrent target positive sourceAccuracy requestStage)
    (scalarFactory : scalar = initial.layerAt trace.budget.fine.selection.stage)
    (unitSpan : initial.span.lower = 0 ∧ initial.span.upper = 1)
    (layers : NumericalLayerRows bounds forms values.2.1.val values.2.2.1.val.2
      (values.inputSpans bounds forms scalarFactory unitSpan))
    (edge : Fin (DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1).length)
    (channel : Fin 6),
    let times := DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1
    let sources := values.2.2.2.val
    let acquired := DependentProduct.get times layers edge
    ∃ inside : edge.val < sources.2.2.2.2.val.length,
      Norm.Basic.normSq
        ((PathModel.mk
          ((sources.2.2.2.2.val[edge.val]'inside).get channel)).integralSample -
          (CoefficientRequests.LayerBank.layer bounds acquired.1.val channel).model.integralSample) <
        Budget.Aggregate.perTerm target times.length

/-- The saved global maximum pays every actual source-row/scalar-Layer comparison on all six original forms. -/
theorem NumericalSources.rows_accurate :
    NumericalSources.RowsAccuracy (originalSource := originalSource) (initial := initial)
      (count := count) (frame := frame) (basis := basis) (sheet := sheet) bounds forms := by
  intro trace bank retained scalar factory caches modelFloor scalarFloor pairCurrent target positive
    sourceAccuracy requestStage values scalarFactory unitSpan layers edge channel
  let times := DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1
  let source := values.2.2.2.val
  let selected := DependentProduct.get times values.2.1.val edge
  let acquired := DependentProduct.get times layers edge
  have origins := NumericalSources.row_origins bounds forms trace bank retained scalar factory caches
    modelFloor scalarFloor pairCurrent target positive sourceAccuracy requestStage values edge
  rcases origins with ⟨inside, origin⟩
  have globalPaid := (numericalFloors_paid bounds forms values.2.1.val edge).1
  have floorSame := congrArg (fun floors : Nat × Nat => floors.1) values.2.2.1.property
  have floorPaid : NumericalPreparation.sourceStage bounds forms selected ≤ values.2.2.1.val.1 :=
    globalPaid.trans_eq floorSame.symm
  refine ⟨inside, ?_⟩
  exact NumericalPreparation.Layers.source_accurate bounds forms selected values.2.2.1.val.2
    (values.inputSpans bounds forms scalarFactory unitSpan edge) acquired source.2.1.val
    (source.2.2.2.2.val[edge.val]'inside) origin floorPaid channel

end OwnerTrace

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
