module

public import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Primitive
public import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Integration.Program.Comparison
import Purelib.Integration.Program.Gaussian.Approximation
import Purelib.Integration.Program.Gaussian.Name
import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Riemann.Periods.PreparedPeriodPrimitiveRequests
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Tactic.Ring

/-! # Requested source-to-period comparisons from the original retained primitive bank

One controlled primitive request, one original source-floor search and one
original canonical PeriodTail are retained per comparison. Their own
coefficient and geometric payments derive the all-later sample bound.
The original source and canonical programme outputs are then compared
through their exact same-index geometric views.
-/

public section

namespace Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Rational
open Purelib.Curves.Legendre
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell (PreparedParents)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Geometry.Rational (Box)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Polynomial.Geometry.Grid (ClearGrid)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Integration.PreparedRefinementMovement (movementMass movementMass_nonnegative)
open Purelib.Riemann.Integration.PreparedCoveredParentLists
open Purelib.Riemann.Integration.PreparedRefinementProgramCore (standardDifferentials)
open Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests (ControlledSumRequest)
open Purelib.Riemann.Periods.PreparedPeriodPrimitiveRequests (PeriodTail)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {ambient : Box}
    {grid : ClearGrid (Fibre.frameCurve frame).polynomial ambient} {base : Canonical}
    {owner : Owner ((Fibre.frameCurve frame).polynomial.eval base)} {source : Differential 1}

/-- The actual primitive request, paid source floor and canonical tail retained for one positive comparison target.

The first request is indexed by the original initial parent list and exact
one-sixty-fourth target. The other caches depend on that same stored request
and source geometry; no final programme-comparison field is part of the type.
-/
@[expose] def PrimitiveSelection (walk : PeriodWalk grid base owner source) (sourceStart periodStart : Nat)
    (tolerance : Rational) (positive : 0 < tolerance) : Type _ :=
  (request : { retained : ControlledSumRequest
    (walk.initial.state.parents.map (recastCenteredEdge (PeriodMatrix.standardDifferential (0 : Fin 1)))) 1
      (tolerance / 64) // retained = walk.primitiveRequest 0 (tolerance / 64)
        (Field.div_pos_direct positive (by decide +kernel)) }) ×
  (first : { retained : Geometric.Search.Selection (32 * movementMass walk.initial.state.parents)
      sourceStart (tolerance / 4) //
    retained = Geometric.Search.Selection.build (32 * movementMass walk.initial.state.parents)
      (Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Rational) ≤ 32)
        (movementMass_nonnegative walk.initial.state.parents)) sourceStart (tolerance / 4)
      (Field.div_pos_direct positive (by decide +kernel)) }) ×
  { tail : PeriodTail walk.initial (standardDifferentials 1) (PeriodMatrix.standardDifferential (0 : Fin 1))
      request.val periodStart //
    tail = PeriodTail.acquire walk.initial (standardDifferentials 1)
      (PeriodMatrix.standardDifferential (0 : Fin 1)) request.val periodStart }

/-- Acquire the three original comparison caches once and retain their whole factory equations. -/
def primitiveSelection (walk : PeriodWalk grid base owner source) (sourceStart periodStart : Nat)
    (tolerance : Rational) (positive : 0 < tolerance) :
    PrimitiveSelection walk sourceStart periodStart tolerance positive :=
  let request := walk.primitiveRequest 0 (tolerance / 64)
    (Field.div_pos_direct positive (by decide +kernel))
  let scale := 32 * movementMass walk.initial.state.parents
  let first := Geometric.Search.Selection.build scale
    (Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Rational) ≤ 32)
      (movementMass_nonnegative walk.initial.state.parents)) sourceStart (tolerance / 4)
    (Field.div_pos_direct positive (by decide +kernel))
  let tail := PeriodTail.acquire walk.initial (standardDifferentials 1)
    (PeriodMatrix.standardDifferential (0 : Fin 1)) request periodStart
  ⟨⟨request, rfl⟩, ⟨first, rfl⟩, ⟨tail, rfl⟩⟩

/-- The complete comparison retains its original request, source search and canonical-tail factories. -/
private theorem packaged_primitiveSelection_factory (walk : PeriodWalk grid base owner source)
    (sourceStart periodStart : Nat)
    (tolerance : Rational) (positive : 0 < tolerance) :
    primitiveSelection walk sourceStart periodStart tolerance positive =
  let request := walk.primitiveRequest 0 (tolerance / 64)
    (Field.div_pos_direct positive (by decide +kernel))
  let scale := 32 * movementMass walk.initial.state.parents
  let first := Geometric.Search.Selection.build scale
    (Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Rational) ≤ 32)
      (movementMass_nonnegative walk.initial.state.parents)) sourceStart (tolerance / 4)
    (Field.div_pos_direct positive (by decide +kernel))
  let tail := PeriodTail.acquire walk.initial (standardDifferentials 1)
    (PeriodMatrix.standardDifferential (0 : Fin 1)) request periodStart
  ⟨⟨request, rfl⟩, ⟨first, rfl⟩, ⟨tail, rfl⟩⟩ := by rfl

/-- The complete comparison retains its original request, source search and canonical-tail factories. -/
theorem primitiveSelection_factory (walk : PeriodWalk grid base owner source)
    (sourceStart periodStart : Nat)
    (tolerance : Rational) (positive : 0 < tolerance) :
    primitiveSelection walk sourceStart periodStart tolerance positive =
  let request := walk.primitiveRequest 0 (tolerance / 64)
    (Field.div_pos_direct positive (by decide +kernel))
  let scale := 32 * movementMass walk.initial.state.parents
  let first := Geometric.Search.Selection.build scale
    (Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Rational) ≤ 32)
      (movementMass_nonnegative walk.initial.state.parents)) sourceStart (tolerance / 4)
    (Field.div_pos_direct positive (by decide +kernel))
  let tail := PeriodTail.acquire walk.initial (standardDifferentials 1)
    (PeriodMatrix.standardDifferential (0 : Fin 1)) request periodStart
  ⟨⟨request, rfl⟩, ⟨first, rfl⟩, ⟨tail, rfl⟩⟩ :=
  packaged_primitiveSelection_factory walk sourceStart periodStart tolerance positive

/-- The actual GIVEN source observation and later original programme sample are paid by the retained selection.

The original request, source search and period tail are consumed unchanged.
Only this one fixed source observation enters the bound; no preparation
family or second observation is constructed to recover its owner.
-/
theorem primitiveSelection_sample (walk : PeriodWalk grid base owner source)
    {sourceStart periodStart : Nat} {tolerance : Rational} {positive : 0 < tolerance}
    (retained : PrimitiveSelection walk sourceStart periodStart tolerance positive) {floor : Nat}
    {point : LiftedPoint 2}
    (chain : CenteredPathChain
      (walk.initial.state.parents.map (recastCenteredEdge (PeriodMatrix.standardDifferential (0 : Fin 1))))
      (start := point) (finish := point))
    (sourceStage periodStage : Nat)
    (prepared : PreparedParents
      (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered) floor
      (CellEndpoints.Targets.build chain.path sourceStage))
    (sourceLater : retained.2.1.val.stage ≤ sourceStage)
    (periodLater : retained.2.2.val.stage ≤ periodStage) :
    Norm.Basic.normSq
      ((PathModel.mk ((PreparedParents.sources
          (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered)
          prepared chain).cells 0)).integralSample -
        ((walk.program 0).integral.model periodStage).integralSample) < tolerance := by
  have original := walk.source_period_error_le (parameter := parameter) (frame := frame)
    (Field.div_pos_direct positive (by decide +kernel))
    retained.1.val retained.1.property chain sourceStage prepared retained.2.2.val periodStage periodLater
  rewrite [walk.sourceErrorScale_eq (parameter := parameter) (frame := frame)] at original
  have sourcePaid := retained.2.1.val.later_accurate sourceLater
  have first := Arithmetic.add_lt_add_right_direct sourcePaid (18 * (tolerance / 64))
  have finalPayment : tolerance / 4 + 18 * (tolerance / 64) < tolerance := by
    have scaled := Arithmetic.mul_lt_mul_of_pos_right_direct
      (by decide +kernel : (17 / 32 : Rational) < 1) positive
    have budget_eq : tolerance / 4 + 18 * (tolerance / 64) = (17 / 32) * tolerance := by
      apply Data.Rat.Fraction.Field.mul_right_cancel_of_ne (by decide +kernel : (64 : Rational) ≠ 0)
      calc
        _ = ((tolerance / 4) * 4) * 16 + 18 * ((tolerance / 64) * 64) := by ring1
        _ = tolerance * 16 + 18 * tolerance := by
          rewrite [Data.Rat.Fraction.Field.div_mul_cancel_of_ne tolerance 4 (by decide +kernel),
            Data.Rat.Fraction.Field.div_mul_cancel_of_ne tolerance 64 (by decide +kernel)]
          rfl
        _ = ((17 / 32) * 32) * (2 * tolerance) := by
          rewrite [Data.Rat.Fraction.Field.div_mul_cancel_of_ne 17 32 (by decide +kernel)]
          ring1
        _ = _ := by ring1
    exact budget_eq.trans_lt (scaled.trans_eq (by ring1))
  exact original.trans_lt (first.trans finalPayment)

/-- Every later source/canonical sample pair is paid by this same retained selection's original three caches. -/
theorem primitiveSelection_close (walk : PeriodWalk grid base owner source)
    {sourceStart periodStart : Nat} {tolerance : Rational} {positive : 0 < tolerance}
    (retained : PrimitiveSelection walk sourceStart periodStart tolerance positive) {floor : Nat}
    {point : LiftedPoint 2}
    (chain : CenteredPathChain
      (walk.initial.state.parents.map (recastCenteredEdge (PeriodMatrix.standardDifferential (0 : Fin 1))))
      (start := point) (finish := point))
    (prepared : (index : Nat) → PreparedParents
      (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered) floor
      (CellEndpoints.Targets.build chain.path index))
    (sourceStage periodStage : Nat) (sourceLater : retained.2.1.val.stage ≤ sourceStage)
    (periodLater : retained.2.2.val.stage ≤ periodStage) :
    Norm.Basic.normSq
      ((PathModel.mk ((PreparedParents.sources
          (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered)
          (prepared sourceStage) chain).cells 0)).integralSample -
        ((walk.program 0).integral.model periodStage).integralSample) < tolerance := by
  exact primitiveSelection_sample walk retained chain sourceStage periodStage (prepared sourceStage)
    sourceLater periodLater

/-- The original source and canonical integral sample streams have an internally constructed finite comparison.

Each call retains one primitive selection before reading its two indices.
The supplied source family is the actual already retained preparation bank
at each stage; no source or canonical acquisition is repeated by a projection.
-/
def sourcePeriodEquivalent (walk : PeriodWalk grid base owner source) {floor : Nat}
    {point : LiftedPoint 2}
    (chain : CenteredPathChain
      (walk.initial.state.parents.map (recastCenteredEdge (PeriodMatrix.standardDifferential (0 : Fin 1))))
      (start := point) (finish := point))
    (prepared : (index : Nat) → PreparedParents
      (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered) floor
      (CellEndpoints.Targets.build chain.path index)) :
    Equivalence.Equivalent
      (PreparedParents.certified
        (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered)
        chain prepared 0).integral.geometric.toApproximation
      (walk.program 0).integral.geometric.toApproximation where
  compare := fun sourceStart periodStart tolerance positive =>
    let retained := walk.primitiveSelection (parameter := parameter) (frame := frame)
      sourceStart periodStart tolerance positive
    { leftIndex := retained.2.1.val.stage
      rightIndex := retained.2.2.val.stage
      left_ge := retained.2.1.val.lower
      right_ge := retained.2.2.val.stage_ge
      close := by
        intro sourceStage periodStage sourceLater periodLater
        have original := walk.primitiveSelection_close (parameter := parameter) (frame := frame)
          retained chain prepared sourceStage periodStage
          sourceLater periodLater
        have cells := PreparedParents.certified_cells
          (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered)
          chain prepared 0 sourceStage
        change Norm.Basic.normSq
          (((PreparedParents.certified
              (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered)
              chain prepared 0).integral.model sourceStage).integralSample -
            ((walk.program 0).integral.model periodStage).integralSample) < tolerance
        rewrite [show ((PreparedParents.certified
          (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered)
          chain prepared 0).integral.model sourceStage) = PathModel.mk ((PreparedParents.sources
          (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered)
          (prepared sourceStage) chain).cells 0) from congrArg PathModel.mk cells]
        exact original }

/-- The actual source value-zero programme and original grid-walk dx/y programme name the same value.

Both productive programmes keep their original finite models and caches.
The comparison is derived from the retained primitive selection, actual
source polynomial bounds and original canonical period-tail payments.
This identifies these two same-parent ordinary programmes; no geometric
monodromy or parameter-derivative realization follows from the result.
-/
def valueZero_outputEquivalent (walk : PeriodWalk grid base owner source) {floor : Nat}
    {point : LiftedPoint 2}
    (chain : CenteredPathChain
      (walk.initial.state.parents.map (recastCenteredEdge (PeriodMatrix.standardDifferential (0 : Fin 1))))
      (start := point) (finish := point))
    (prepared : (index : Nat) → PreparedParents
      (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered) floor
      (CellEndpoints.Targets.build chain.path index)) :
    NamedEquivalent
      (PreparedParents.certified
        (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered)
        chain prepared 0).integral.output.name
      (walk.program 0).integral.output.name := by
  let left := (PreparedParents.certified
    (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered) chain prepared 0).integral
  let right := (walk.program 0).integral
  have middle : NamedEquivalent (PeriodMatrix.geometricNamed left.geometric).name
      (PeriodMatrix.geometricNamed right.geometric).name := by
    exact Sequence.Name.Equivalence.approximationEquivalent_toNamed
      (walk.sourcePeriodEquivalent (parameter := parameter) (frame := frame) chain prepared)
  exact (Integration.Program.Comparison.output_equivalent_geometric left).trans
    (middle.trans (Integration.Program.Comparison.output_equivalent_geometric right).symm)

end Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk

end
