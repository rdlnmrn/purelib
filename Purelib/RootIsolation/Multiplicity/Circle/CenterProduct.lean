module
import Purelib.RootIsolation.Winding.Bounds.Residual

public import Purelib.RootIsolation.Multiplicity.Circle.Location
public import Purelib.Geometry.Rational.Box.Separation.Family
public import Purelib.Polynomial.Dense.Gaussian.Interpolation
public import Purelib.Polynomial.Dense.Gaussian.Split
import Purelib.Polynomial.Dense.Leading
public import Purelib.Polynomial.Winding.Circle
import Purelib.Polynomial.Winding.Circle.Comparison
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Target
import Purelib.Data.List.Map
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.List.Pairwise
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Sufficient center products of original radial owner families

Original initial boxes give one cached positive separation floor. Their same
ambient box and finite owner count determine the interpolation amplification
and sufficient residual request. Sufficient stored radial states are reused; additional refinements start from
those same states, preserving their owner and strict radial classification.
-/

namespace Purelib.RootIsolation.Multiplicity.Circle.CenterProduct

open Purelib
open Purelib.Data
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Geometry.Projective
open Purelib.Polynomial
open Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Dense.Basic (DensePolynomial)
open Dense.Gaussian
open Dense.Gaussian.Bounds.RootRadius.Box (largeSquareBox)
open Purelib.Polynomial.Clearance.Circle (Certificate)
open Purelib.RootIsolation.State.WindingOne.Basic (WindingOneState)
open Purelib.RootIsolation.Track.Basic (WindingOneTrack)
open Rat.Fraction (Rational)
open Rat.Fraction.Order

/-- The original initial owner boxes in their original isolation order. -/
@[expose] public def initialBoxes {polynomial : CoefficientPolynomial} (source : FTA.Squarefree.BoxResult polynomial) :
    List Box := source.isolation.tracks.map fun track => track.initial.box

/-- The same original initial box list has the original track family's pairwise separation. -/
public theorem initialBoxes_pairwise {polynomial : CoefficientPolynomial}
    (source : FTA.Squarefree.BoxResult polynomial) :
    (initialBoxes source).Pairwise Box.Separated := by
  exact Data.List.Pairwise.pairwise_map.mpr source.isolation.tracks_pairwise

set_option genInjectivity false in
/-- Coefficient- and original-box-computed sufficient interpolation requests.

The original squarefree isolation remains an index. The stored original boxes
and their same coordinate-gap certificates determine a positive residual
threshold before any additional track state or rational center is computed.
-/
public structure Request {polynomial : CoefficientPolynomial} (clearance : Certificate polynomial)
    (source : FTA.Squarefree.BoxResult polynomial) where
  /-- The same original initial boxes, materialized in isolation order. -/
  regions : List Box
  /-- The box list reads the same original ordered tracks. -/
  regions_eq : regions = initialBoxes source
  /-- The original initial boxes remain pairwise separated. -/
  pairwise : regions.Pairwise Box.Separated
  /-- The stored original coordinate-gap bank and its positive common floor. -/
  gaps : Box.Separation.Family regions pairwise
  /-- The gap bank is the actual original coordinate-certificate constructor. -/
  gaps_eq : gaps = Box.Separation.Family.prepare regions pairwise
  /-- The common original ambient quadrance ceiling. -/
  radius : Rational
  /-- The ceiling is the same original root-radius box's endpoint bound. -/
  radius_eq : radius = (largeSquareBox polynomial).normSqBound
  /-- The finite Newton interpolation amplification. -/
  amplification : Rational
  /-- The amplification uses the original count, ambient ceiling and stored pair floor. -/
  amplification_eq : amplification = Interpolation.amplification radius gaps.bound regions.length
  /-- The once-computed sufficiently small original-factor residual threshold. -/
  threshold : Rational
  /-- The threshold pays the original circle margin and same interpolation amplification. -/
  threshold_eq : threshold = clearance.bound / (16 * (1 + amplification))
  /-- The retained residual threshold is strictly positive. -/
  threshold_positive : 0 < threshold
  /-- The original coefficient-computed accuracy request, shared by every owner. -/
  residualRadius : Rational
  /-- The retained accuracy is the original uniform-residual construction's radius. -/
  residualRadius_eq : residualRadius =
    Bounds.Box.Target.uniformResidualRadius polynomial (largeSquareBox polynomial) threshold
  /-- The retained original accuracy is strictly positive. -/
  residualRadius_positive : 0 < residualRadius

constructive_injectivity Request

namespace Request

/-- Compute all common original-box and coefficient requests once before refining any owner. -/
@[expose] public def prepare {polynomial : CoefficientPolynomial} (clearance : Certificate polynomial)
    (source : FTA.Squarefree.BoxResult polynomial) : Request clearance source :=
  let regions := initialBoxes source
  let pairwise := initialBoxes_pairwise source
  let gaps := Box.Separation.Family.prepare regions pairwise
  let ambient := largeSquareBox polynomial
  let radius := ambient.normSqBound
  let amplification := Interpolation.amplification radius gaps.bound regions.length
  have amplificationNonnegative : 0 ≤ amplification :=
    Interpolation.amplification_nonnegative (largeSquareBox polynomial).normSqBound_nonneg
      gaps.positive regions.length
  let threshold := clearance.bound / (16 * (1 + amplification))
  have thresholdPositive : 0 < threshold := Field.div_pos_direct clearance.positive
    (Arithmetic.mul_pos_direct (by decide)
      (Arithmetic.add_pos_of_pos_of_nonneg_direct (by decide) amplificationNonnegative))
  let residualRadius := Bounds.Box.Target.uniformResidualRadius polynomial
    ambient threshold
  { regions, regions_eq := rfl, pairwise, gaps, gaps_eq := rfl
    radius, radius_eq := rfl, amplification, amplification_eq := rfl
    threshold, threshold_eq := rfl, threshold_positive := thresholdPositive
    residualRadius, residualRadius_eq := rfl
    residualRadius_positive := Bounds.Box.Target.uniformResidualRadius_pos _ _ thresholdPositive }

/-- The retained original box count is the original ordered track count. -/
public theorem regions_length {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {source : FTA.Squarefree.BoxResult polynomial} (request : Request clearance source) :
    request.regions.length = source.isolation.tracks.length := by
  rw [request.regions_eq]
  exact Data.List.Map.length_map _ _

/-- The retained original box count is exactly the original squarefree polynomial degree. -/
public theorem count {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {source : FTA.Squarefree.BoxResult polynomial} (request : Request clearance source) :
    request.regions.length = polynomial.natDegree := request.regions_length.trans source.isolation.tracks_length

/-- Preserve the original natural occurrence while transporting the retained box-count bound. -/
@[expose] public def trackIndex {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {source : FTA.Squarefree.BoxResult polynomial} (request : Request clearance source)
    (index : Fin request.regions.length) : Fin source.isolation.tracks.length :=
  ⟨index.val, request.regions_length ▸ index.isLt⟩

/-- Reading a retained initial box gives the same original track's initial box. -/
public theorem regionAt_eq {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {source : FTA.Squarefree.BoxResult polynomial} (request : Request clearance source)
    (index : Fin request.regions.length) :
    request.regions.get index = (source.isolation.tracks.get (request.trackIndex index)).initial.box := by
  have mappedBound : index.val < (initialBoxes source).length := by
    rw [← request.regions_eq]
    exact index.isLt
  have equation := Data.List.Map.getElem_map
    (fun track : Track.Basic.WindingOneTrack polynomial (largeSquareBox polynomial) => track.initial.box)
    source.isolation.tracks index.val
    (request.trackIndex index).isLt mappedBound
  exact (getElem_congr request.regions_eq (Eq.refl index.val) index.isLt).trans equation

/-- The stored amplification is nonnegative. -/
public theorem amplification_nonnegative {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {source : FTA.Squarefree.BoxResult polynomial} (request : Request clearance source) :
    0 ≤ request.amplification := by
  rw [request.amplification_eq, request.radius_eq]
  exact Interpolation.amplification_nonnegative (largeSquareBox polynomial).normSqBound_nonneg
    request.gaps.positive _

/-- The computed threshold pays the same complete interpolation amplification. -/
public theorem payment {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {source : FTA.Squarefree.BoxResult polynomial} (request : Request clearance source) :
    request.threshold * request.amplification ≤ clearance.bound / 16 := by
  apply (Field.le_div_iff_pos (by decide : (0 : Rational) < 16)).mpr
  have coefficientBound : request.amplification ≤ 1 + request.amplification := by
    have bound := Arithmetic.add_le_add_right_direct (by decide : (0 : Rational) ≤ 1) request.amplification
    simpa only [Rat.Fraction.Field.zero_add] using bound
  calc
    (request.threshold * request.amplification) * 16 ≤ (request.threshold * (1 + request.amplification)) * 16 :=
      Arithmetic.mul_le_mul_of_nonneg_right_direct
        (Arithmetic.mul_le_mul_of_nonneg_left_direct coefficientBound request.threshold_positive.le) (by decide)
    _ = request.threshold * (16 * (1 + request.amplification)) := by ring1
    _ = clearance.bound := by
      rw [request.threshold_eq]
      exact Rat.Fraction.Field.div_mul_cancel_of_ne _ _
        (Arithmetic.mul_pos_direct (by decide)
          (Arithmetic.add_pos_of_pos_of_nonneg_direct (by decide) request.amplification_nonnegative)).ne'

end Request

namespace Sample

set_option genInjectivity false in
/-- A sufficient original state is reused, or the same original track is strictly refined.

Both alternatives retain the exact preceding state and requested accuracy.
The refinement alternative additionally proves that reuse was insufficient;
neither alternative changes the original track's strict refinement contract.
-/
public inductive Selection {polynomial : CoefficientPolynomial} {ambient : Box}
    (track : WindingOneTrack polynomial ambient) (current : WindingOneState polynomial ambient)
    (radius : Rational) (positive : 0 < radius) : WindingOneState polynomial ambient → Type
  /-- The retained original state already meets the requested squared-diagonal bound. -/
  | reused (accurate : current.box.diagonalSq ≤ radius ^ 2) : Selection track current radius positive current
  /-- An insufficient retained state is refined by the same original strict track procedure. -/
  | refined (needed : ¬ current.box.diagonalSq ≤ radius ^ 2) :
      Selection track current radius positive (track.refine current radius positive)

constructive_injectivity Selection

namespace Selection

/-- Select an already sufficient original state, otherwise run its same strict refiner once.

The returned dependent pair retains the actual state and the exact original
reuse or refinement branch. No sample or replacement track is constructed.
-/
@[expose] public def prepare {polynomial : CoefficientPolynomial} {ambient : Box}
    (track : WindingOneTrack polynomial ambient) (current : WindingOneState polynomial ambient)
    (radius : Rational) (positive : 0 < radius) :
    (state : WindingOneState polynomial ambient) × Selection track current radius positive state :=
  if accurate : current.box.diagonalSq ≤ radius ^ 2 then
    ⟨current, .reused accurate⟩
  else
    ⟨track.refine current radius positive, .refined accurate⟩

/-- Retained typed branch evidence recovers the complete original selected-state result. -/
public theorem result_eq_prepare {polynomial : CoefficientPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} {current state : WindingOneState polynomial ambient}
    {radius : Rational} {positive : 0 < radius} (selection : Selection track current radius positive state) :
    (⟨state, selection⟩ : (next : WindingOneState polynomial ambient) ×
      Selection track current radius positive next) = prepare track current radius positive := by
  cases selection with
  | reused accurate => unfold prepare; rw [dif_pos accurate]
  | refined needed => unfold prepare; rw [dif_neg needed]

/-- Read whether the exact selected state was reused without invoking its strict refiner. -/
@[expose] public def isReused {polynomial : CoefficientPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} {current state : WindingOneState polynomial ambient}
    {radius : Rational} {positive : 0 < radius} : Selection track current radius positive state → Bool
  | .reused _ => true
  | .refined _ => false

/-- Either certified selection remains inside its same preceding original state. -/
public theorem nested {polynomial : CoefficientPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} {current state : WindingOneState polynomial ambient}
    {radius : Rational} {positive : 0 < radius} (selection : Selection track current radius positive state) :
    state.box.Refines current.box := by
  cases selection with
  | reused _ => exact Box.refines_refl _
  | refined _ => exact track.nested current radius positive

/-- Either certified selection meets the same requested squared-diagonal bound. -/
public theorem accurate {polynomial : CoefficientPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} {current state : WindingOneState polynomial ambient}
    {radius : Rational} {positive : 0 < radius} (selection : Selection track current radius positive state) :
    state.box.diagonalSq ≤ radius ^ 2 := by
  cases selection with
  | reused accurate => exact accurate
  | refined _ => exact track.accurate current radius positive

end Selection
end Sample

set_option genInjectivity false in
/-- An original radial state selected at the sufficient interpolation accuracy.

The preceding radial owner and bounded occurrence remain indices. A typed
selection records whether that same state was already accurate or its same
original strict track procedure computed the additional state.
-/
public structure Sample {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {source : FTA.Squarefree.BoxResult polynomial} (locations : HigherLocations clearance source)
    (request : Request clearance source) (index : Fin request.regions.length) where
  /-- The exact selected original state. -/
  state : WindingOneState polynomial (largeSquareBox polynomial)
  /-- The retained original state was reused or its same original track was strictly refined. -/
  selection : Sample.Selection (source.isolation.tracks.get (request.trackIndex index))
    (locations.refinementAt (request.trackIndex index)).next request.residualRadius
      request.residualRadius_positive state
  /-- The retained exact rational sample. -/
  point : Canonical
  /-- The sample is the selected original box's actual anchor. -/
  point_eq : point = state.box.anchor

constructive_injectivity Sample

namespace Sample

/-- Retain a certified selected original state and its same exact rational box anchor. -/
@[expose] public def ofState {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {source : FTA.Squarefree.BoxResult polynomial} (locations : HigherLocations clearance source)
    (request : Request clearance source) (index : Fin request.regions.length)
    (state : WindingOneState polynomial (largeSquareBox polynomial))
    (selection : Selection (source.isolation.tracks.get (request.trackIndex index))
      (locations.refinementAt (request.trackIndex index)).next request.residualRadius
      request.residualRadius_positive state) :
    Sample locations request index :=
  { state, selection, point := state.box.anchor, point_eq := rfl }

/-- Reuse a sufficient original radial state, otherwise refine its same original track once.

The requested norm guarantee is unchanged. The original strict refiner runs
only when the retained state's exact diagonal comparison fails.
-/
@[expose] public def prepare {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {source : FTA.Squarefree.BoxResult polynomial} (locations : HigherLocations clearance source)
    (request : Request clearance source) (index : Fin request.regions.length) : Sample locations request index :=
  let current := (locations.refinementAt (request.trackIndex index)).next
  let selected := Selection.prepare (source.isolation.tracks.get (request.trackIndex index))
    current request.residualRadius request.residualRadius_positive
  ofState locations request index selected.1 selected.2

/-- The original sample constructor preserves its complete preceding-state branch equation. -/
public theorem prepare_eq {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {source : FTA.Squarefree.BoxResult polynomial} (locations : HigherLocations clearance source)
    (request : Request clearance source) (index : Fin request.regions.length) :
    prepare locations request index =
      if accurate : (locations.refinementAt (request.trackIndex index)).next.box.diagonalSq ≤
          request.residualRadius ^ 2 then
        ofState locations request index (locations.refinementAt (request.trackIndex index)).next (.reused accurate)
      else
        ofState locations request index ((source.isolation.tracks.get (request.trackIndex index)).refine
          (locations.refinementAt (request.trackIndex index)).next
            request.residualRadius request.residualRadius_positive) (.refined accurate) := by
  unfold prepare Selection.prepare
  dsimp only
  by_cases accurate : (locations.refinementAt (request.trackIndex index)).next.box.diagonalSq ≤
      request.residualRadius ^ 2
  · rewrite [dif_pos accurate, dif_pos accurate]
    rfl
  · rewrite [dif_neg accurate, dif_neg accurate]
    rfl

/-- Restore the complete current sample procedure from its same typed selected-state evidence. -/
public theorem ofState_eq_prepare {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {source : FTA.Squarefree.BoxResult polynomial} (locations : HigherLocations clearance source)
    (request : Request clearance source) (index : Fin request.regions.length)
    (state : WindingOneState polynomial (largeSquareBox polynomial))
    (selection : Selection (source.isolation.tracks.get (request.trackIndex index))
      (locations.refinementAt (request.trackIndex index)).next request.residualRadius
      request.residualRadius_positive state) :
    ofState locations request index state selection = prepare locations request index := by
  cases selection with
  | reused accurate => rw [prepare_eq, dif_pos accurate]
  | refined needed => rw [prepare_eq, dif_neg needed]

/-- The stored sample belongs to its actual returned original box. -/
public theorem inside {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {source : FTA.Squarefree.BoxResult polynomial} {locations : HigherLocations clearance source}
    {request : Request clearance source} {index : Fin request.regions.length}
    (sample : Sample locations request index) :
    sample.state.box.Contains sample.point := sample.point_eq.symm ▸ sample.state.box.contains_anchor

/-- The same sample remains inside its preceding retained radial box. -/
public theorem inside_previous {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {source : FTA.Squarefree.BoxResult polynomial} {locations : HigherLocations clearance source}
    {request : Request clearance source} {index : Fin request.regions.length}
    (sample : Sample locations request index) :
    (locations.refinementAt (request.trackIndex index)).next.box.Contains sample.point := by
  exact sample.selection.nested.contains sample.inside

/-- The same sample remains inside its same original initial owner box. -/
public theorem inside_region {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {source : FTA.Squarefree.BoxResult polynomial} {locations : HigherLocations clearance source}
    {request : Request clearance source} {index : Fin request.regions.length}
    (sample : Sample locations request index) :
    (request.regions.get index).Contains sample.point := by
  rw [request.regionAt_eq]
  exact (locations.refinementAt (request.trackIndex index)).refines.contains sample.inside_previous

/-- The additional center has the same strict radial side as its same retained original radial owner. -/
public theorem radial {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {source : FTA.Squarefree.BoxResult polynomial} {locations : HigherLocations clearance source}
    {request : Request clearance source} {index : Fin request.regions.length}
    (sample : Sample locations request index) :
    match (locations.refinementAt (request.trackIndex index)).side with
    | .negative _ => sample.point.normSq < 1
    | .positive _ => 1 < sample.point.normSq := by
  cases side : (locations.refinementAt (request.trackIndex index)).side with
  | negative holds =>
      have negative := holds sample.point sample.inside_previous
      rw [Hermitian.eval_affineNormComparisonForm, Gaussian.Norm.Basic.normSq_eq_canonical] at negative
      exact Arithmetic.lt_of_sub_neg_direct negative
  | positive holds =>
      have positive := holds sample.point sample.inside_previous
      rw [Hermitian.eval_affineNormComparisonForm, Gaussian.Norm.Basic.normSq_eq_canonical] at positive
      exact Arithmetic.lt_of_sub_pos_direct positive

/-- The additional sample satisfies the computed sufficient original-factor residual bound. -/
public theorem residual_lt {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {source : FTA.Squarefree.BoxResult polynomial} {locations : HigherLocations clearance source}
    {request : Request clearance source} {index : Fin request.regions.length}
    (sample : Sample locations request index) :
    Gaussian.Norm.Basic.normSq (polynomial.eval sample.point) < request.threshold := by
  have accurate : sample.state.box.diagonalSq ≤
      (Bounds.Box.Target.uniformResidualRadius polynomial (largeSquareBox polynomial) request.threshold) ^ 2 := by
    rewrite [← request.residualRadius_eq]
    exact sample.selection.accurate
  exact Winding.Bounds.Residual.normSq_eval_lt_of_diagonal locations.degreePositive sample.state
    request.threshold_positive accurate sample.inside

end Sample

set_option genInjectivity false in
/-- The materialized sufficient samples of every same original radial owner occurrence.

Each entry retains its certified original state selection and anchor. The cached point
list reads those exact stored entries in original box order, without another
track refinement or replacement observation.
-/
public structure Samples {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {source : FTA.Squarefree.BoxResult polynomial} (locations : HigherLocations clearance source)
    (request : Request clearance source) where
  /-- One actual sufficient original sample at every original bounded occurrence. -/
  entries : List.DependentProduct request.regions (Sample locations request)
  /-- The stored bank is the materialized original sample constructor. -/
  entries_eq : entries = List.DependentProduct.ofFn request.regions (Sample.prepare locations request)
  /-- The once-materialized ordered point list from those same entries. -/
  points : List Canonical
  /-- Every point reads its same original stored entry and occurrence. -/
  points_eq : points = List.ofFn (fun index : Fin request.regions.length =>
    (List.DependentProduct.get request.regions entries index).point)

constructive_injectivity Samples

namespace Samples

/-- Retain checked original sample entries and materialize their same ordered rational point list once. -/
@[expose] public def ofEntries {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {source : FTA.Squarefree.BoxResult polynomial} (locations : HigherLocations clearance source)
    (request : Request clearance source) (entries : List.DependentProduct request.regions (Sample locations request))
    (entriesEq : entries = List.DependentProduct.ofFn request.regions (Sample.prepare locations request)) :
    Samples locations request :=
  { entries, entries_eq := entriesEq
    points := List.ofFn (fun index : Fin request.regions.length =>
      (List.DependentProduct.get request.regions entries index).point)
    points_eq := rfl }

/-- Materialize every original additional refinement once and retain the exact ordered center list. -/
@[expose] public def prepare {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {source : FTA.Squarefree.BoxResult polynomial} (locations : HigherLocations clearance source)
    (request : Request clearance source) : Samples locations request :=
  let entries := List.DependentProduct.ofFn request.regions (Sample.prepare locations request)
  ofEntries locations request entries rfl

/-- Checked retained sample entries preserve the complete original sample-bank result. -/
public theorem ofEntries_eq_prepare {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {source : FTA.Squarefree.BoxResult polynomial} (locations : HigherLocations clearance source)
    (request : Request clearance source) (entries : List.DependentProduct request.regions (Sample locations request))
    (entriesEq : entries = List.DependentProduct.ofFn request.regions (Sample.prepare locations request)) :
    ofEntries locations request entries entriesEq = prepare locations request := by cases entriesEq; rfl

/-- Read the same stored complete original sample at its bounded occurrence. -/
@[expose] public def sampleAt {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {source : FTA.Squarefree.BoxResult polynomial} {locations : HigherLocations clearance source}
    {request : Request clearance source} (samples : Samples locations request) (index : Fin request.regions.length) :
    Sample locations request index := List.DependentProduct.get request.regions samples.entries index

/-- Stored sample lookup returns the complete original sample constructor result. -/
public theorem sampleAt_eq {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {source : FTA.Squarefree.BoxResult polynomial} {locations : HigherLocations clearance source}
    {request : Request clearance source} (samples : Samples locations request) (index : Fin request.regions.length) :
    samples.sampleAt index = Sample.prepare locations request index :=
  (congrArg (fun entries => List.DependentProduct.get request.regions entries index) samples.entries_eq).trans
    (List.DependentProduct.get_ofFn _ _ index)

/-- The retained point list has exactly the original stored box count. -/
public theorem points_length {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {source : FTA.Squarefree.BoxResult polynomial} {locations : HigherLocations clearance source}
    {request : Request clearance source} (samples : Samples locations request) :
    samples.points.length = request.regions.length := by
  rw [samples.points_eq]
  exact Data.List.OfFn.Basic.length_ofFn

/-- The retained center list has exactly the original squarefree factor degree. -/
public theorem count {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {source : FTA.Squarefree.BoxResult polynomial} {locations : HigherLocations clearance source}
    {request : Request clearance source} (samples : Samples locations request) :
    samples.points.length = polynomial.natDegree := samples.points_length.trans request.count

/-- Every retained rational center satisfies the same original ambient quadrance ceiling. -/
public theorem node_bounds {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {source : FTA.Squarefree.BoxResult polynomial} {locations : HigherLocations clearance source}
    {request : Request clearance source} (samples : Samples locations request) :
    ∀ point ∈ samples.points, Gaussian.Norm.Basic.normSq point ≤ request.radius := by
  intro point member
  rw [samples.points_eq] at member
  rcases Data.List.OfFn.Basic.mem_ofFn.mp member with ⟨index, equal⟩
  rw [← equal, request.radius_eq]
  exact Box.normSq_le_normSqBound
    ((samples.sampleAt index).state.refinesAmbient.contains (samples.sampleAt index).inside)

/-- The same original gap bank bounds every ordered distinct retained center pair. -/
public theorem separated {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {source : FTA.Squarefree.BoxResult polynomial} {locations : HigherLocations clearance source}
    {request : Request clearance source} (samples : Samples locations request) :
    samples.points.Pairwise (fun left right => request.gaps.bound ≤ Gaussian.Norm.Basic.normSq (left - right)) := by
  rw [samples.points_eq]
  exact request.gaps.points_separated (fun index => (samples.sampleAt index).point)
    (fun index => (samples.sampleAt index).inside_region)

/-- Every retained center satisfies the computed sufficient original-factor residual threshold. -/
public theorem residual_le {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {source : FTA.Squarefree.BoxResult polynomial} {locations : HigherLocations clearance source}
    {request : Request clearance source} (samples : Samples locations request) :
    ∀ point ∈ samples.points, Gaussian.Norm.Basic.normSq (polynomial.eval point) ≤ request.threshold := by
  intro point member
  rw [samples.points_eq] at member
  rcases Data.List.OfFn.Basic.mem_ofFn.mp member with ⟨index, equal⟩
  rw [← equal]
  exact (samples.sampleAt index).residual_lt.le

/-- Matching the original leading term cancels its highest slot in the center-product difference. -/
private theorem error_below {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {source : FTA.Squarefree.BoxResult polynomial} {locations : HigherLocations clearance source}
    {request : Request clearance source} (samples : Samples locations request) :
    Dense.Leading.DegreeBelow
      (polynomial.normalize - DensePolynomial.scale polynomial.leadingCoeff
        (Split.splitPolynomial samples.points)) polynomial.natDegree := by
  have original := Dense.Leading.LeadingTerm.normalizeSelf clearance.nonzero
  have product := (Split.splitPolynomial_leading samples.points).scale
    (DensePolynomial.leadingCoeff_ne_zero clearance.nonzero)
  rw [samples.count, Gaussian.Basic.mul_one] at product
  exact original.sub_same product

/-- The original synthetic interpolation chain proves the center product uniformly close on the whole circle.

The exact source degree cancels the center product's same leading term.
Every remaining sample residual is the original polynomial residual because
the literal split product vanishes at its same retained centers. The original
separation floor and computed request pay the complete interpolation bound.
-/
public theorem close {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {source : FTA.Squarefree.BoxResult polynomial} {locations : HigherLocations clearance source}
    {request : Request clearance source} (samples : Samples locations request)
    (expansion : Interpolation.Expansion
      (polynomial.normalize - DensePolynomial.scale polynomial.leadingCoeff
        (Split.splitPolynomial samples.points)) samples.points) :
    clearance.Close
      (DensePolynomial.scale polynomial.leadingCoeff (Split.splitPolynomial samples.points)) := by
  let difference := polynomial.normalize - DensePolynomial.scale polynomial.leadingCoeff
    (Split.splitPolynomial samples.points)
  have lengthBound : difference.coeffs.length ≤ samples.points.length := by
    have bound := samples.error_below.count_le
    change difference.normalize.coeffs.length ≤ polynomial.natDegree at bound
    rw [DensePolynomial.normalize_sub] at bound
    exact bound.trans_eq samples.count.symm
  have values : ∀ point ∈ samples.points, Gaussian.Norm.Basic.normSq (difference.eval point) ≤ request.threshold := by
    intro point member
    change Gaussian.Norm.Basic.normSq
      ((polynomial.normalize - DensePolynomial.scale polynomial.leadingCoeff
        (Split.splitPolynomial samples.points)).eval point) ≤ request.threshold
    rw [DensePolynomial.eval_sub, DensePolynomial.eval_normalize,
      DensePolynomial.eval_scale, Split.splitPolynomial_eval_eq_zero_of_mem member,
      Gaussian.Basic.mul_zero, Gaussian.Basic.sub_zero]
    exact samples.residual_le point member
  intro point unit
  have radiusNonnegative : 0 ≤ request.radius := request.radius_eq.symm ▸ (largeSquareBox polynomial).normSqBound_nonneg
  have unitDisk : Gaussian.Norm.Basic.normSq point ≤ 1 :=
    ((Gaussian.Norm.Basic.normSq_eq_canonical point).trans unit).le
  have bound := expansion.normSq_eval_le radiusNonnegative request.gaps.positive request.threshold_positive.le
    lengthBound samples.node_bounds samples.separated values unitDisk
  rw [samples.points_length, ← request.amplification_eq] at bound
  rw [DensePolynomial.eval_sub, DensePolynomial.eval_normalize] at bound
  exact (Gaussian.Norm.Bounds.normSq_sub_symm _ _).le.trans (bound.trans request.payment)

end Samples

set_option genInjectivity false in
/-- An automatically sufficient center-product approximation of the same original squarefree factor.

The original radial family remains an index. The result retains the common
request, every actual additional state and center, the literal original split
product, its original leading-coefficient scale, their exact difference and
the original synthetic expansion that proves whole-circle closeness.
-/
public structure Approximation {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {source : FTA.Squarefree.BoxResult polynomial} (locations : HigherLocations clearance source) where
  /-- The once-computed sufficient original-factor request. -/
  request : Request clearance source
  /-- The request is the actual coefficient- and original-box constructor. -/
  request_eq : request = Request.prepare clearance source
  /-- The actual additional samples of the same retained original radial states. -/
  samples : Samples locations request
  /-- The bank is the actual once-materialized sample construction. -/
  samples_eq : samples = Samples.prepare locations request
  /-- The retained literal monic polynomial at the same ordered rational centers. -/
  monic : CoefficientPolynomial
  /-- The monic polynomial is the original finite split-product procedure. -/
  monic_eq : monic = Split.splitPolynomial samples.points
  /-- The once-scaled center product with the original source leading coefficient. -/
  target : CoefficientPolynomial
  /-- The scale consumes this same retained monic product. -/
  target_eq : target = DensePolynomial.scale polynomial.leadingCoeff monic
  /-- The retained coefficient difference from the same normalized original polynomial. -/
  difference : CoefficientPolynomial
  /-- The difference consumes this same retained target. -/
  difference_eq : difference = polynomial.normalize - target
  /-- The actual original synthetic divisions at the same ordered centers. -/
  expansion : Interpolation.Expansion difference samples.points
  /-- The expansion is the same original finite synthetic constructor. -/
  expansion_eq : expansion = Interpolation.Expansion.prepare difference samples.points
  /-- The retained target satisfies the computed whole-circle perturbation margin. -/
  close : clearance.Close target

constructive_injectivity Approximation

namespace Approximation

/-- Assemble a sufficient original center approximation from its checked retained sample and polynomial caches.

Every complete constructor equation retains the same original request,
samples, center product, leading scale, difference and synthetic expansion.
The whole-circle estimate consumes that same retained expansion directly.
-/
@[expose] public def ofExpansion {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {source : FTA.Squarefree.BoxResult polynomial} (locations : HigherLocations clearance source)
    (request : Request clearance source) (requestEq : request = Request.prepare clearance source)
    (samples : Samples locations request) (samplesEq : samples = Samples.prepare locations request)
    (monic : CoefficientPolynomial) (monicEq : monic = Split.splitPolynomial samples.points)
    (target : CoefficientPolynomial) (targetEq : target = DensePolynomial.scale polynomial.leadingCoeff monic)
    (difference : CoefficientPolynomial) (differenceEq : difference = polynomial.normalize - target)
    (expansion : Interpolation.Expansion difference samples.points)
    (expansionEq : expansion = Interpolation.Expansion.prepare difference samples.points) : Approximation locations :=
  { request, request_eq := requestEq, samples, samples_eq := samplesEq
    monic, monic_eq := monicEq, target, target_eq := targetEq
    difference, difference_eq := differenceEq, expansion, expansion_eq := expansionEq
    close := by
      have targetOriginal : target =
          DensePolynomial.scale polynomial.leadingCoeff (Split.splitPolynomial samples.points) :=
        targetEq.trans (congrArg (DensePolynomial.scale polynomial.leadingCoeff) monicEq)
      have differenceOriginal := differenceEq.trans
        (congrArg (fun target => polynomial.normalize - target) targetOriginal)
      have originalExpansion := differenceOriginal ▸ expansion
      exact targetOriginal.symm ▸ samples.close originalExpansion }

/-- Compute the original center-polynomial caches from checked retained samples, with no additional refinement. -/
@[expose] public def ofSamples {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {source : FTA.Squarefree.BoxResult polynomial} (locations : HigherLocations clearance source)
    (request : Request clearance source) (requestEq : request = Request.prepare clearance source)
    (samples : Samples locations request) (samplesEq : samples = Samples.prepare locations request) :
    Approximation locations :=
  let monic := Split.splitPolynomial samples.points
  let target := DensePolynomial.scale polynomial.leadingCoeff monic
  let difference := polynomial.normalize - target
  let expansion := Interpolation.Expansion.prepare difference samples.points
  ofExpansion locations request requestEq samples samplesEq monic rfl target rfl difference rfl expansion rfl

/-- Refine the same original radial owners and retain a sufficient center product without caller nodes or fuel. -/
@[expose] public def prepare {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {source : FTA.Squarefree.BoxResult polynomial} (locations : HigherLocations clearance source) :
    Approximation locations :=
  let request := Request.prepare clearance source
  let samples := Samples.prepare locations request
  ofSamples locations request rfl samples rfl

/-- Checked original sample restoration preserves the complete original sufficient approximation. -/
public theorem ofSamples_eq_prepare {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {source : FTA.Squarefree.BoxResult polynomial} (locations : HigherLocations clearance source)
    (request : Request clearance source) (requestEq : request = Request.prepare clearance source)
    (samples : Samples locations request) (samplesEq : samples = Samples.prepare locations request) :
    ofSamples locations request requestEq samples samplesEq = prepare locations := by
  cases requestEq
  cases samplesEq
  rfl

/-- Checked original polynomial and expansion caches preserve the complete original sufficient approximation. -/
public theorem ofExpansion_eq_prepare {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {source : FTA.Squarefree.BoxResult polynomial} (locations : HigherLocations clearance source)
    (request : Request clearance source) (requestEq : request = Request.prepare clearance source)
    (samples : Samples locations request) (samplesEq : samples = Samples.prepare locations request)
    (monic : CoefficientPolynomial) (monicEq : monic = Split.splitPolynomial samples.points)
    (target : CoefficientPolynomial) (targetEq : target = DensePolynomial.scale polynomial.leadingCoeff monic)
    (difference : CoefficientPolynomial) (differenceEq : difference = polynomial.normalize - target)
    (expansion : Interpolation.Expansion difference samples.points)
    (expansionEq : expansion = Interpolation.Expansion.prepare difference samples.points) :
    ofExpansion locations request requestEq samples samplesEq monic monicEq target targetEq difference differenceEq
      expansion expansionEq = prepare locations := by
  cases requestEq
  cases samplesEq
  cases monicEq
  cases targetEq
  cases differenceEq
  cases expansionEq
  rfl

/-- The same original independent chart-event winding agrees with the retained sufficient center product. -/
public theorem raw_eq {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {source : FTA.Squarefree.BoxResult polynomial} {locations : HigherLocations clearance source}
    (approximation : Approximation locations)
    (sourcePaths : RationalFunctions.Curve.Canonical.Circle.Boundary.Substitutions polynomial)
    (targetPaths : RationalFunctions.Curve.Canonical.Circle.Boundary.Substitutions approximation.target) :
    Polynomial.Winding.Circle.raw targetPaths = Polynomial.Winding.Circle.raw sourcePaths :=
  Polynomial.Winding.Circle.Comparison.raw_eq_of_close clearance sourcePaths targetPaths approximation.close

end Approximation
end Purelib.RootIsolation.Multiplicity.Circle.CenterProduct
