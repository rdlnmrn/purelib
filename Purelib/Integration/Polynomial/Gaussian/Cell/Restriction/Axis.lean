module

public import Purelib.Integration.Polynomial.Gaussian.Cell.Restriction.Chain
public import Purelib.Polynomial.Geometry.Grid.AxisWalks.Parameters
public import Purelib.Data.List.DependentProduct
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.List.Map
import Purelib.Data.Gaussian.Basic
import Purelib.Tactic.Ring

/-! # Cached source-polynomial restrictions on original axis-word occurrences

The original source list supplies every dependent index. Ordered scalar
incidence comes from its same retained axis walk. Only polynomial
restrictions are newly materialized; the source model, word and geometry
are retained. Exact reassembly uses the original interval-chain theorem.
-/

public section

namespace Purelib.Integration.Polynomial.Gaussian.Cell.Restriction.Axis

open Purelib
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.List
open Purelib.Integration.Partition (Interval)
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Polynomial.Ascending.Gaussian.Restriction (Cached)
open Purelib.Polynomial.Geometry.Grid

universe u v

variable {Alpha : Type u} {key : Alpha → Rational} {intervals : List (ClearGrid.Interval key)}
    {first last : Rational} (walk : AxisWalks.Walk intervals first last)
    {Edge : Type} (sources : List Edge) (read : Edge → Rational × Rational)

/-- Read one normalized interval on the same original source occurrence and orientation. -/
@[expose] def interval (edge : Edge) : Interval :=
  ⟨walk.parameter (read edge).1, walk.parameter (read edge).2⟩

/-- Exact scalar source incidence gives the original normalized interval chain. -/
theorem chain (different : first ≠ last) (coordinates : sources.map read = walk.steps) :
    Interval.Chain 0 1 (sources.map (interval walk read)) := by
  have equal : sources.map (interval walk read) = walk.parameters :=
    (Map.map_map (fun step : Rational × Rational =>
      (⟨walk.parameter step.1, walk.parameter step.2⟩ : Interval)) read sources).symm.trans
      (congrArg (fun steps => steps.map (fun step : Rational × Rational =>
        (⟨walk.parameter step.1, walk.parameter step.2⟩ : Interval))) coordinates)
  exact Eq.mpr (congrArg (Interval.Chain 0 1) equal) (walk.parameters_chain different)

/-- Equal original walk endpoints force the same supplied source occurrence list to be empty. -/
theorem sources_nil (same : first = last) (coordinates : sources.map read = walk.steps) : sources = [] := by
  have empty := coordinates.trans (walk.steps_nil_of_eq same)
  cases sources with
  | nil => rfl
  | cons => cases empty

/-- The same source-occurrence endpoints have normalized unit bounds derived from their actual retained walk. -/
theorem inside (different : first ≠ last) (coordinates : sources.map read = walk.steps)
    (index : Fin sources.length) :
    (0 ≤ (interval walk read (sources[index.val]'index.isLt)).start ∧
        (interval walk read (sources[index.val]'index.isLt)).start ≤ 1) ∧
      (0 ≤ (interval walk read (sources[index.val]'index.isLt)).finish ∧
        (interval walk read (sources[index.val]'index.isLt)).finish ≤ 1) := by
  have member : read (sources[index.val]'index.isLt) ∈ sources.map read :=
    Map.mem_map.mpr ⟨_, List.getElem_mem index.isLt, rfl⟩
  have kept : read (sources[index.val]'index.isLt) ∈ walk.steps :=
    Eq.mp (congrArg (fun steps => read (sources[index.val]'index.isLt) ∈ steps) coordinates) member
  exact walk.step_parameters_inside different kept

variable (cell : CellModel)

/-- Actual restriction caches retain each complete canonical factory on its same original source occurrence. -/
@[expose] def Caches :=
  DependentProduct sources (fun index =>
    {cached : Cached cell.polynomial
        (Cast.Path.ofCoordinate (interval walk read (sources[index.val]'index.isLt)).start)
        (Cast.Path.ofCoordinate (interval walk read (sources[index.val]'index.isLt)).finish) //
      cached = Cached.canonical cell.polynomial
        (Cast.Path.ofCoordinate (interval walk read (sources[index.val]'index.isLt)).start)
        (Cast.Path.ofCoordinate (interval walk read (sources[index.val]'index.isLt)).finish)})

/-- Materialize only the finite polynomial restrictions, once per same ordered source occurrence. -/
def cache : Caches walk sources read cell :=
  DependentProduct.ofFn sources (fun index =>
    ⟨Cached.canonical cell.polynomial
      (Cast.Path.ofCoordinate (interval walk read (sources[index.val]'index.isLt)).start)
      (Cast.Path.ofCoordinate (interval walk read (sources[index.val]'index.isLt)).finish), rfl⟩)

variable (cached : Caches walk sources read cell)

/-- Read the stored restriction at its literal original source index, without evaluating its factory. -/
@[expose] def restriction (index : Fin sources.length) : Cached cell.polynomial
    (Cast.Path.ofCoordinate (interval walk read (sources[index.val]'index.isLt)).start)
    (Cast.Path.ofCoordinate (interval walk read (sources[index.val]'index.isLt)).finish) :=
  (DependentProduct.get sources cached index).val

/-- Every stored restriction retains its complete original factory equation. -/
theorem restriction_eq (index : Fin sources.length) :
    restriction walk sources read cell cached index = Cached.canonical cell.polynomial
      (Cast.Path.ofCoordinate (interval walk read (sources[index.val]'index.isLt)).start)
      (Cast.Path.ofCoordinate (interval walk read (sources[index.val]'index.isLt)).finish) :=
  (DependentProduct.get sources cached index).property

/-- Read the physical restriction model using the same stored coefficient and integral cache. -/
@[expose] def model (index : Fin sources.length) : CellModel :=
  Cell.Restriction.model cell (restriction walk sources read cell cached index)

/-- Read the retained unit-integral cache with its same physical restriction displacement. -/
@[expose] def sample (index : Fin sources.length) : Canonical :=
  (model walk sources read cell cached index).displacement *
    (restriction walk sources read cell cached index).sample

/-- The cached scalar sample equals its same restriction model's integral without replaying the cache factory. -/
theorem sample_eq (index : Fin sources.length) :
    sample walk sources read cell cached index = (model walk sources read cell cached index).integralSample :=
  congrArg (fun value : Canonical => (model walk sources read cell cached index).displacement * value)
    (restriction walk sources read cell cached index).sample_eq

/-- The same cached restricted cells recover the original source integral exactly.

The displayed sum keeps the original source indices and traversal signs.
No root query, model preparation, row or numerical primitive bank is run.
-/
theorem integralSample_sum (different : first ≠ last) (coordinates : sources.map read = walk.steps) :
    sumFin (fun index => (model walk sources read cell cached index).integralSample) = cell.integralSample := by
  have materialized := OfFn.Basic.ofFn_map_cast sources rfl (interval walk read)
  have indexed : Interval.Chain 0 1
      (List.ofFn (fun index : Fin sources.length => interval walk read (sources[index.val]'index.isLt))) :=
    Eq.mpr (congrArg (Interval.Chain 0 1) materialized) (chain walk sources read different coordinates)
  exact Cell.Restriction.integralSample_sum_unit cell
    (fun index => interval walk read (sources[index.val]'index.isLt))
    (restriction walk sources read cell cached) indexed

/-- An empty same source word keeps an empty restriction cache and zero ordered integral sum. -/
theorem integralSample_sum_nil (empty : sources = []) :
    sumFin (fun index => (model walk sources read cell cached index).integralSample) = 0 := by
  cases empty
  rfl

/-- The original horizontal source model recovers each retained scalar coordinate at its exact normalized parameter. -/
theorem point_horizontal (different : first ≠ last) (height : Rational)
    (start : cell.start = (⟨first, height⟩ : Canonical))
    (finish : cell.finish = (⟨last, height⟩ : Canonical)) (value : Rational) :
    cell.point (walk.parameter value) = (⟨value, height⟩ : Canonical) := by
  unfold CellModel.point CellModel.displacement
  rewrite [start, finish]
  apply Basic.ext
  · change first + (walk.parameter value * (last - first) - 0 * (height - height)) = value
    calc
      _ = first + walk.parameter value * (last - first) := by ring1
      _ = value := walk.parameter_coordinate different value
  · change height + (walk.parameter value * (height - height) + 0 * (last - first)) = height
    ring1

/-- The original vertical source model recovers each retained scalar coordinate at its exact normalized parameter. -/
theorem point_vertical (different : first ≠ last) (width : Rational)
    (start : cell.start = (⟨width, first⟩ : Canonical))
    (finish : cell.finish = (⟨width, last⟩ : Canonical)) (value : Rational) :
    cell.point (walk.parameter value) = (⟨width, value⟩ : Canonical) := by
  unfold CellModel.point CellModel.displacement
  rewrite [start, finish]
  apply Basic.ext
  · change width + (walk.parameter value * (width - width) - 0 * (last - first)) = width
    ring1
  · change first + (walk.parameter value * (last - first) + 0 * (width - width)) = value
    calc
      _ = first + walk.parameter value * (last - first) := by ring1
      _ = value := walk.parameter_coordinate different value

/-- Each same horizontal source occurrence is the exact geometric edge of its retained restriction model. -/
theorem horizontal_endpoints (different : first ≠ last) (height : Rational)
    (start : cell.start = (⟨first, height⟩ : Canonical))
    (finish : cell.finish = (⟨last, height⟩ : Canonical))
    (coordinates : Edge → Canonical × Canonical)
    (embedded : sources.map coordinates = walk.steps.map (fun step =>
      ((⟨step.1, height⟩ : Canonical), (⟨step.2, height⟩ : Canonical))))
    (retained : Caches walk sources (fun edge => ((coordinates edge).1.re, (coordinates edge).2.re)) cell)
    (index : Fin sources.length) :
    (model walk sources (fun edge => ((coordinates edge).1.re, (coordinates edge).2.re))
      cell retained index).start = (coordinates (sources[index.val]'index.isLt)).1 ∧
      (model walk sources (fun edge => ((coordinates edge).1.re, (coordinates edge).2.re))
        cell retained index).finish = (coordinates (sources[index.val]'index.isLt)).2 := by
  have member : coordinates (sources[index.val]'index.isLt) ∈ sources.map coordinates :=
    Map.mem_map.mpr ⟨_, List.getElem_mem index.isLt, rfl⟩
  have kept := Eq.mp (congrArg (fun pairs => coordinates (sources[index.val]'index.isLt) ∈ pairs) embedded) member
  rcases Map.mem_map.mp kept with ⟨step, _present, equal⟩
  have firstEq := congrArg Prod.fst equal
  have lastEq := congrArg Prod.snd equal
  constructor
  · change cell.point (walk.parameter (coordinates (sources[index.val]'index.isLt)).1.re) = _
    exact (congrArg (fun value => cell.point (walk.parameter value))
      (congrArg (fun point : Canonical => point.re) firstEq).symm).trans
        ((point_horizontal walk cell different height start finish step.1).trans firstEq)
  · change cell.point (walk.parameter (coordinates (sources[index.val]'index.isLt)).2.re) = _
    exact (congrArg (fun value => cell.point (walk.parameter value))
      (congrArg (fun point : Canonical => point.re) lastEq).symm).trans
        ((point_horizontal walk cell different height start finish step.2).trans lastEq)

/-- Each same vertical source occurrence is the exact geometric edge of its retained restriction model. -/
theorem vertical_endpoints (different : first ≠ last) (width : Rational)
    (start : cell.start = (⟨width, first⟩ : Canonical))
    (finish : cell.finish = (⟨width, last⟩ : Canonical))
    (coordinates : Edge → Canonical × Canonical)
    (embedded : sources.map coordinates = walk.steps.map (fun step =>
      ((⟨width, step.1⟩ : Canonical), (⟨width, step.2⟩ : Canonical))))
    (retained : Caches walk sources (fun edge => ((coordinates edge).1.im, (coordinates edge).2.im)) cell)
    (index : Fin sources.length) :
    (model walk sources (fun edge => ((coordinates edge).1.im, (coordinates edge).2.im))
      cell retained index).start = (coordinates (sources[index.val]'index.isLt)).1 ∧
      (model walk sources (fun edge => ((coordinates edge).1.im, (coordinates edge).2.im))
        cell retained index).finish = (coordinates (sources[index.val]'index.isLt)).2 := by
  have member : coordinates (sources[index.val]'index.isLt) ∈ sources.map coordinates :=
    Map.mem_map.mpr ⟨_, List.getElem_mem index.isLt, rfl⟩
  have kept := Eq.mp (congrArg (fun pairs => coordinates (sources[index.val]'index.isLt) ∈ pairs) embedded) member
  rcases Map.mem_map.mp kept with ⟨step, _present, equal⟩
  have firstEq := congrArg Prod.fst equal
  have lastEq := congrArg Prod.snd equal
  constructor
  · change cell.point (walk.parameter (coordinates (sources[index.val]'index.isLt)).1.im) = _
    exact (congrArg (fun value => cell.point (walk.parameter value))
      (congrArg (fun point : Canonical => point.im) firstEq).symm).trans
        ((point_vertical walk cell different width start finish step.1).trans firstEq)
  · change cell.point (walk.parameter (coordinates (sources[index.val]'index.isLt)).2.im) = _
    exact (congrArg (fun value => cell.point (walk.parameter value))
      (congrArg (fun point : Canonical => point.im) lastEq).symm).trans
        ((point_vertical walk cell different width start finish step.2).trans lastEq)

/-- Projecting an exact embedded coordinate list reads the same original scalar step list. -/
private theorem project_coordinates (scalar : Canonical → Rational) (embed : Rational → Canonical)
    (readback : ∀ value, scalar (embed value) = value) (coordinates : Edge → Canonical × Canonical)
    (embedded : sources.map coordinates = walk.steps.map (fun step => (embed step.1, embed step.2))) :
    sources.map (fun edge => (scalar (coordinates edge).1, scalar (coordinates edge).2)) = walk.steps := by
  have mapped : ∀ steps : List (Rational × Rational),
      (steps.map (fun step => (embed step.1, embed step.2))).map
        (fun pair => (scalar pair.1, scalar pair.2)) = steps := by
    intro steps
    induction steps with
    | nil => rfl
    | cons head tail previous =>
        exact congrArg₂ List.cons (congrArg₂ Prod.mk (readback head.1) (readback head.2)) previous
  exact (Map.map_map (fun pair : Canonical × Canonical => (scalar pair.1, scalar pair.2))
    coordinates sources).symm.trans
      ((congrArg (fun pairs => pairs.map (fun pair : Canonical × Canonical =>
        (scalar pair.1, scalar pair.2))) embedded).trans (mapped walk.steps))

variable {AlphaH AlphaV : Type u} {keyH : AlphaH → Rational} {keyV : AlphaV → Rational}
    {intervalsH : List (ClearGrid.Interval keyH)} {intervalsV : List (ClearGrid.Interval keyV)}
    (firstPoint lastPoint : Canonical)
    (horizontal : AxisWalks.Walk intervalsH firstPoint.re lastPoint.re)
    (vertical : AxisWalks.Walk intervalsV firstPoint.im lastPoint.im)
    (horizontalSources verticalSources : List Edge) (readH readV : Edge → Rational × Rational)

/-- The two original outer roles reassemble the same source integral, including either empty inner word.

The supplied actual endpoint decision is retained. The zero-displacement
branch proves both inner words empty and uses the original source cell's
zero-integral law. The other branch reassembles only its nonstationary
axis and keeps the transverse role with zero inner contributions.
-/
theorem axes_integral
    (sourceStart : cell.start = firstPoint) (sourceFinish : cell.finish = lastPoint)
    (horizontalCache : Caches horizontal horizontalSources readH cell)
    (verticalCache : Caches vertical verticalSources readV cell)
    (decision : Decidable (firstPoint = lastPoint))
    (axis : firstPoint.im = lastPoint.im ∨ firstPoint.re = lastPoint.re)
    (horizontalCoordinates : horizontalSources.map readH = horizontal.steps)
    (verticalCoordinates : verticalSources.map readV = vertical.steps) :
    sumFin (fun index => (model horizontal horizontalSources readH cell horizontalCache index).integralSample) +
      sumFin (fun index => (model vertical verticalSources readV cell verticalCache index).integralSample) =
        cell.integralSample := by
  cases decision with
  | isTrue same =>
      have hEmpty := sources_nil horizontal horizontalSources readH
        (congrArg (fun point : Canonical => point.re) same) horizontalCoordinates
      have vEmpty := sources_nil vertical verticalSources readV
        (congrArg (fun point : Canonical => point.im) same) verticalCoordinates
      exact (congrArg₂ (fun first last : Canonical => first + last)
        (integralSample_sum_nil horizontal horizontalSources readH cell horizontalCache hEmpty)
        (integralSample_sum_nil vertical verticalSources readV cell verticalCache vEmpty)).trans
          ((Basic.zero_add 0).trans (cell.integralSample_eq_zero_of_start_eq_finish
            (sourceStart.trans (same.trans sourceFinish.symm))).symm)
  | isFalse different =>
      rcases axis with horizontalLine | verticalLine
      · have nonstationary : firstPoint.re ≠ lastPoint.re :=
          fun real => different (Basic.ext real horizontalLine)
        have empty := sources_nil vertical verticalSources readV horizontalLine verticalCoordinates
        exact (congrArg₂ (fun first last : Canonical => first + last)
          (integralSample_sum horizontal horizontalSources readH cell horizontalCache
            nonstationary horizontalCoordinates)
          (integralSample_sum_nil vertical verticalSources readV cell verticalCache empty)).trans
            (Basic.add_zero _)
      · have nonstationary : firstPoint.im ≠ lastPoint.im :=
          fun imag => different (Basic.ext verticalLine imag)
        have empty := sources_nil horizontal horizontalSources readH verticalLine horizontalCoordinates
        exact (congrArg₂ (fun first last : Canonical => first + last)
          (integralSample_sum_nil horizontal horizontalSources readH cell horizontalCache empty)
          (integralSample_sum vertical verticalSources readV cell verticalCache
            nonstationary verticalCoordinates)).trans (Basic.zero_add _)

/-- The exact two-cache continuation retains both original outer roles and their derived reassembly. -/
@[expose] def AxesConsumer (coordinates : Edge → Canonical × Canonical) (Result : Type v) :=
  let readH := fun edge => ((coordinates edge).1.re, (coordinates edge).2.re)
  let readV := fun edge => ((coordinates edge).1.im, (coordinates edge).2.im)
  (horizontalCache : Caches horizontal horizontalSources readH cell) →
  horizontalCache = cache horizontal horizontalSources readH cell →
  (verticalCache : Caches vertical verticalSources readV cell) →
  verticalCache = cache vertical verticalSources readV cell →
  horizontalSources.map readH = horizontal.steps →
  verticalSources.map readV = vertical.steps →
  (firstPoint.re ≠ lastPoint.re →
    Interval.Chain 0 1 (horizontalSources.map (interval horizontal readH))) →
  (firstPoint.im ≠ lastPoint.im →
    Interval.Chain 0 1 (verticalSources.map (interval vertical readV))) →
  (decision : Decidable (firstPoint = lastPoint)) →
  sumFin (fun index => (model horizontal horizontalSources readH cell horizontalCache index).integralSample) +
    sumFin (fun index => (model vertical verticalSources readV cell verticalCache index).integralSample) =
      cell.integralSample →
  sumFin (sample horizontal horizontalSources readH cell horizontalCache) +
    sumFin (sample vertical verticalSources readV cell verticalCache) = cell.integralSample →
  (firstPoint = lastPoint → horizontalSources = [] ∧ verticalSources = [] ∧ cell.integralSample = 0) →
  Result

/-- Construct the two occurrence-indexed restriction caches on the same original embedded axis words.

The complete coordinate-list laws supply scalar incidence internally.
Both caches and their whole factory equations reach the continuation,
even in the zero-displacement branch. No source/row/root query runs here.
-/
def withAxes (sourceStart : cell.start = firstPoint) (sourceFinish : cell.finish = lastPoint)
    (coordinates : Edge → Canonical × Canonical)
    (horizontalCoordinates : horizontalSources.map coordinates = horizontal.steps.map (fun step =>
      ((⟨step.1, firstPoint.im⟩ : Canonical), (⟨step.2, firstPoint.im⟩ : Canonical))))
    (verticalCoordinates : verticalSources.map coordinates = vertical.steps.map (fun step =>
      ((⟨lastPoint.re, step.1⟩ : Canonical), (⟨lastPoint.re, step.2⟩ : Canonical))))
    (axis : firstPoint.im = lastPoint.im ∨ firstPoint.re = lastPoint.re)
    {Result : Type v}
    (consume : AxesConsumer cell firstPoint lastPoint horizontal vertical horizontalSources verticalSources
      coordinates Result) : Result :=
  let readH := fun edge => ((coordinates edge).1.re, (coordinates edge).2.re)
  let readV := fun edge => ((coordinates edge).1.im, (coordinates edge).2.im)
  have horizontalRead : horizontalSources.map readH = horizontal.steps :=
    project_coordinates horizontal horizontalSources (fun point => point.re)
      (fun value => (⟨value, firstPoint.im⟩ : Canonical)) (fun _ => rfl) coordinates horizontalCoordinates
  have verticalRead : verticalSources.map readV = vertical.steps :=
    project_coordinates vertical verticalSources (fun point => point.im)
      (fun value => (⟨lastPoint.re, value⟩ : Canonical)) (fun _ => rfl) coordinates verticalCoordinates
  let horizontalCache := cache horizontal horizontalSources readH cell
  let verticalCache := cache vertical verticalSources readV cell
  let decision : Decidable (firstPoint = lastPoint) := inferInstance
  have reassembled := axes_integral cell firstPoint lastPoint horizontal vertical
    horizontalSources verticalSources readH readV sourceStart sourceFinish
    horizontalCache verticalCache decision axis horizontalRead verticalRead
  have cachedReassembled := (congrArg₂ (fun first last : Canonical => first + last)
    (sumFin_congr (sample_eq horizontal horizontalSources readH cell horizontalCache))
    (sumFin_congr (sample_eq vertical verticalSources readV cell verticalCache))).trans
      reassembled
  consume horizontalCache rfl verticalCache rfl horizontalRead verticalRead
    (fun different => chain horizontal horizontalSources readH different horizontalRead)
    (fun different => chain vertical verticalSources readV different verticalRead) decision
    reassembled cachedReassembled
    (fun same =>
      ⟨sources_nil horizontal horizontalSources readH (congrArg (fun point : Canonical => point.re) same)
          horizontalRead,
        sources_nil vertical verticalSources readV (congrArg (fun point : Canonical => point.im) same)
          verticalRead,
        cell.integralSample_eq_zero_of_start_eq_finish (sourceStart.trans (same.trans sourceFinish.symm))⟩)

end Purelib.Integration.Polynomial.Gaussian.Cell.Restriction.Axis

end
