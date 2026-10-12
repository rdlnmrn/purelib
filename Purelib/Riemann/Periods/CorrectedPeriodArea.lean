module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Basic
public import Purelib.Integration.Energy.Polygon
import Purelib.LinearAlgebra.Alternating.Handle.Basic
import Purelib.LinearAlgebra.Alternating.NormalForm.Basic
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Surface.Cut.PrimitiveJumps

public import Purelib.Topology.Surface.Boundary.HandleAreaBounds
import Purelib.Topology.Surface.Boundary.NormalFormArea
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Sewing.ChordCycleBank
public import Purelib.Topology.Surface.Sewing.NormalFormCycles
import Purelib.Topology.Surface.Boundary.NormalFormErrorBounds
import Purelib.Topology.Surface.Word.NormalFormMagnitude
public import Purelib.Topology.Surface.Boundary.HandleAreaBudgets
import Purelib.Tactic.Ring

public section

/-!
# Cached period areas with their physical-boundary corrections

The input rows may be the already materialized common-stage period samples.
Subtract each physical coordinate once; every handle then consumes minus
row q followed by row p. The cache retains exact equations to those rows.
-/

namespace Purelib.Riemann.Periods

open Purelib.Topology.Polygon.Stokes (OrientedEdge PrimitivePoint)
open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.LinearAlgebra.Alternating.Handle.Basic (PivotIndices)
open _root_.Purelib.LinearAlgebra.Alternating (NormalForm)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open _root_.Purelib.Data.Gaussian.Basic (conj)
open Purelib.Integration.Energy.Polygon (energyPrimitivePoint)
open Purelib.Topology.Surface.Cut.BoundaryWord (CutBoundaryWord)
open _root_.Purelib.Topology.Surface.Cut.IntegralPairing renaming CutBoundaryWord -> IntegralPairing
open _root_.Purelib.Topology.Surface.Sewing (ChordCycleBank)
open _root_.Purelib.Topology.Surface.Sewing (NormalFormCycles)
open Purelib.Topology.Surface.Boundary.HandleAreaBounds (sampledHandleArea)
open Purelib.Topology.Surface.Boundary.HandleAreaBudgets (HandleAreaBudget)
open _root_.Purelib.Topology.Surface.Boundary (NormalFormArea)
open Purelib.Riemann.Readings.PrimitiveAreaBounds (AreaCoordinate)

namespace CorrectedPeriodArea.PrimitivePoint

open Purelib.Riemann in
open Purelib.Integration in
/-- A conjugate primitive point equals the energy point of its right coordinate. -/
theorem eq_energy {point : PrimitivePoint} (related :
  (Readings.PrimitiveAreaBounds.PrimitivePoint.Conjugate point)) :
    point = Energy.Polygon.energyPrimitivePoint point.right := by
  cases point with
  | mk left right => exact congrArg (fun value => PrimitivePoint.mk value right) related

end CorrectedPeriodArea.PrimitivePoint

variable {source target : Nat} {labels : Fin source → Fin target} {edges : List (OrientedEdge source)}
  {word : CutBoundaryWord labels edges} {pairing :
    Topology.Surface.Cut.IntegralPairing.CutBoundaryWord word}
  {primitive : Fin source → PrimitivePoint}
  {values : Data.Vector PrimitivePoint word.alphabet.count}
  {routes : Topology.Surface.Sewing.ChordCycleBank word} {raw : List
    (PivotIndices word.alphabet.count)}
  {normal : LinearAlgebra.Alternating.NormalForm pairing.paired raw} {bank :
    Topology.Surface.Sewing.ChordCycleBank.Sample routes pairing primitive values}

open Purelib.Integration in
open Purelib.Topology in
open Purelib.Data in
set_option genInjectivity false in
/-- Cached period points after physical-boundary correction, with their ordered handle area.

Subtract the same retained physical coordinate from each input row once. Each handle consumes minus its q row followed
by its p row, preserving the original pivot order. -/
structure CorrectedPeriodArea (cycles : Topology.Surface.Sewing.NormalFormCycles normal bank)
    (rows : Data.Vector Gaussian.Basic.Canonical word.alphabet.count) where
  /-- The materialized conjugate primitive points from corrected period rows. -/ points : Data.Vector
    PrimitivePoint word.alphabet.count
  /-- Each cached point uses its exact input row minus the retained physical right coordinate. -/ points_eq : ∀ index,
    points index = Energy.Polygon.energyPrimitivePoint (rows index - (cycles.physical index).right)
  /-- The cached signed handle area of the corrected points. -/ area : Gaussian.Basic.Canonical
  /-- The area cache uses the retained pivot list with minus-q then p endpoint order. -/ area_eq : area =
    Surface.Boundary.HandleAreaBounds.sampledHandleArea raw (fun pair => (Polygon.Stokes.PrimitivePoint.sub
    PrimitivePoint.zero) (points pair.2)) (fun pair => points pair.1)

constructive_injectivity CorrectedPeriodArea

namespace CorrectedPeriodArea

variable {cycles : Topology.Surface.Sewing.NormalFormCycles normal bank} {rows :
  Data.Vector Canonical word.alphabet.count}

open Purelib.Integration in
open Purelib.Topology in
open Purelib.Data in
/-- Cache physically corrected period points and their ordered handle area. -/
@[expose] def build (cycles : Topology.Surface.Sewing.NormalFormCycles normal bank) (rows : Data.Vector
  Gaussian.Basic.Canonical word.alphabet.count) :
    CorrectedPeriodArea cycles rows :=
  let points := Vector.Basic.vectorOfFn fun index => Energy.Polygon.energyPrimitivePoint (rows index - (cycles.physical
    index).right)
  ⟨points, Vector.Basic.vectorOfFn_apply _, Surface.Boundary.HandleAreaBounds.sampledHandleArea raw (fun pair =>
    (Polygon.Stokes.PrimitivePoint.sub PrimitivePoint.zero) (points pair.2)) (fun pair => points pair.1), rfl⟩

open Purelib.Topology in
open Purelib.LinearAlgebra in
/-- Read the negated corrected q point for this retained handle pair. -/
@[expose] def first (sample : CorrectedPeriodArea cycles rows) (pair : Alternating.Handle.Basic.PivotIndices
  word.alphabet.count) : PrimitivePoint :=
  (Polygon.Stokes.PrimitivePoint.sub PrimitivePoint.zero) (sample.points pair.2)

section
open Purelib.LinearAlgebra
/-- Read the corrected p point for this retained handle pair. -/
@[expose] def last (sample : CorrectedPeriodArea cycles rows) (pair : Alternating.Handle.Basic.PivotIndices
  word.alphabet.count) : PrimitivePoint := sample.points pair.1

/-- The first handle coordinate is minus the q period row plus its physical correction. -/
theorem first_right (sample : CorrectedPeriodArea cycles rows) (pair : Alternating.Handle.Basic.PivotIndices
  word.alphabet.count) :
    (sample.first pair).right = -rows pair.2 + (cycles.physical pair.2).right := by
  rw [first, sample.points_eq]
  change 0 - (rows pair.2 - (cycles.physical pair.2).right) = _
  ring1

/-- The last handle coordinate is the p period row minus its physical correction. -/
theorem last_right (sample : CorrectedPeriodArea cycles rows) (pair : Alternating.Handle.Basic.PivotIndices
  word.alphabet.count) :
    (sample.last pair).right = rows pair.1 - (cycles.physical pair.1).right := by
  rw [last, sample.points_eq]
  rfl

end

section
open Purelib.Riemann
open Purelib.LinearAlgebra
/-- The first corrected handle point is a conjugate primitive pair. -/
theorem first_conjugate (sample : CorrectedPeriodArea cycles rows) (pair : Alternating.Handle.Basic.PivotIndices
  word.alphabet.count) :
    (Readings.PrimitiveAreaBounds.PrimitivePoint.Conjugate (sample.first pair)) := by
  apply Readings.PrimitiveAreaBounds.PrimitivePoint.sub_conjugate (by rfl)
  rw [sample.points_eq]
  rfl

/-- The last corrected handle point is a conjugate primitive pair. -/
theorem last_conjugate (sample : CorrectedPeriodArea cycles rows) (pair : Alternating.Handle.Basic.PivotIndices
  word.alphabet.count) :
    (Readings.PrimitiveAreaBounds.PrimitivePoint.Conjugate (sample.last pair)) := by
  rw [last, sample.points_eq]
  rfl

end

section
open Purelib.Integration
open Purelib.LinearAlgebra
/-- The first handle point is the energy point of its signed corrected q coordinate. -/
theorem first_eq_energy (sample : CorrectedPeriodArea cycles rows) (pair : Alternating.Handle.Basic.PivotIndices
  word.alphabet.count) :
    sample.first pair = Energy.Polygon.energyPrimitivePoint (-rows pair.2 + (cycles.physical pair.2).right) :=
  (PrimitivePoint.eq_energy (sample.first_conjugate pair)).trans (congrArg Energy.Polygon.energyPrimitivePoint
    (sample.first_right pair))

/-- The last handle point is the energy point of its corrected p coordinate. -/
theorem last_eq_energy (sample : CorrectedPeriodArea cycles rows) (pair : Alternating.Handle.Basic.PivotIndices
  word.alphabet.count) :
    sample.last pair = Energy.Polygon.energyPrimitivePoint (rows pair.1 - (cycles.physical pair.1).right) :=
  (PrimitivePoint.eq_energy (sample.last_conjugate pair)).trans (congrArg Energy.Polygon.energyPrimitivePoint
    (sample.last_right pair))

end

section
open Purelib.Riemann
open Purelib.Topology
open Purelib.Data
open Purelib.LinearAlgebra
/-- A signed q-row error bound controls both coordinates of the first handle-point difference. -/
theorem first_error_bounded (sample : CorrectedPeriodArea cycles rows) (evaluated :
  Topology.Surface.Boundary.NormalFormArea normal values)
    (pair : Alternating.Handle.Basic.PivotIndices word.alphabet.count) (conjugate :
      (Readings.PrimitiveAreaBounds.PrimitivePoint.Conjugate (evaluated.points pair.1))) {error : AreaCoordinate}
    (accurate : Data.Gaussian.Norm.Basic.normSq (-rows pair.2 - ((evaluated.points pair.1).right - (cycles.physical
      pair.2).right)) ≤ error) :
    (Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded ((Polygon.Stokes.PrimitivePoint.sub (sample.first pair))
      (evaluated.points pair.1))) error := by
  apply Readings.PrimitiveAreaBounds.PrimitivePoint.bounded_of_conjugate
    (Readings.PrimitiveAreaBounds.PrimitivePoint.sub_conjugate (sample.first_conjugate pair) conjugate)
  rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
  change Data.Gaussian.Norm.Basic.normSq ((sample.first pair).right - (evaluated.points pair.1).right) ≤ _
  rw [sample.first_right]
  have equal : (-rows pair.2 + (cycles.physical pair.2).right) - (evaluated.points pair.1).right =
      -rows pair.2 - ((evaluated.points pair.1).right - (cycles.physical pair.2).right) := by ring1
  exact (congrArg Data.Gaussian.Norm.Basic.normSq equal).le.trans accurate

/-- A p-row error bound controls both coordinates of the last handle-point difference. -/
theorem last_error_bounded (sample : CorrectedPeriodArea cycles rows) (evaluated :
  Topology.Surface.Boundary.NormalFormArea normal values)
    (pair : Alternating.Handle.Basic.PivotIndices word.alphabet.count) (conjugate :
      (Readings.PrimitiveAreaBounds.PrimitivePoint.Conjugate (evaluated.points pair.2))) {error : AreaCoordinate}
    (accurate : Data.Gaussian.Norm.Basic.normSq (rows pair.1 - ((evaluated.points pair.2).right + (cycles.physical
      pair.1).right)) ≤ error) :
    (Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded ((Polygon.Stokes.PrimitivePoint.sub (sample.last pair))
      (evaluated.points pair.2))) error := by
  apply Readings.PrimitiveAreaBounds.PrimitivePoint.bounded_of_conjugate
    (Readings.PrimitiveAreaBounds.PrimitivePoint.sub_conjugate (sample.last_conjugate pair) conjugate)
  rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
  change Data.Gaussian.Norm.Basic.normSq ((sample.last pair).right - (evaluated.points pair.2).right) ≤ _
  rw [sample.last_right]
  have equal : (rows pair.1 - (cycles.physical pair.1).right) - (evaluated.points pair.2).right =
      rows pair.1 - ((evaluated.points pair.2).right + (cycles.physical pair.1).right) := by ring1
  exact (congrArg Data.Gaussian.Norm.Basic.normSq equal).le.trans accurate

end

open Purelib.Riemann in
open Purelib.Topology in
open Purelib.Data in
/-- The handle budget controls corrected sampled area against the evaluated normal-form area.

Evaluated primitive points satisfy the common magnitude and conjugacy conditions, and both signed row errors obey the
same row target at every retained pivot occurrence. -/
theorem accurate (sample : CorrectedPeriodArea cycles rows) (evaluated : Topology.Surface.Boundary.NormalFormArea
  normal values)
    {magnitude target : AreaCoordinate} (budget : Surface.Boundary.HandleAreaBudgets.HandleAreaBudget magnitude
      raw.length target)
    (bounded : ∀ index, (Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (evaluated.points index)) magnitude)
    (conjugate : ∀ index, (Readings.PrimitiveAreaBounds.PrimitivePoint.Conjugate (evaluated.points index)))
    (firstBound : ∀ pair ∈ raw, Data.Gaussian.Norm.Basic.normSq (-rows pair.2 - ((evaluated.points pair.1).right -
      (cycles.physical pair.2).right)) ≤ budget.rowTarget)
    (lastBound : ∀ pair ∈ raw, Data.Gaussian.Norm.Basic.normSq (rows pair.1 - ((evaluated.points pair.2).right +
      (cycles.physical pair.1).right)) ≤ budget.rowTarget) :
    Data.Gaussian.Norm.Basic.normSq (sample.area - evaluated.area) < budget.handleTarget := by
  rw [sample.area_eq, evaluated.area_eq_handles]
  exact Surface.Boundary.HandleAreaBounds.sampledHandleArea_accurate raw sample.first sample.last evaluated.points
    budget.handle_positive budget.magnitude_nonnegative
    budget.row_positive.le budget.row_le_one budget.row_paid (fun pair _ => ⟨bounded pair.1, bounded pair.2⟩)
    (fun pair member => ⟨sample.first_error_bounded evaluated pair (conjugate pair.1) (firstBound pair member),
      sample.last_error_bounded evaluated pair (conjugate pair.2) (lastBound pair member)⟩)

end CorrectedPeriodArea
end Purelib.Riemann.Periods
