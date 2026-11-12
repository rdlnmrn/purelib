module
import Purelib.RootIsolation.Winding.Bounds.Residual

public import Purelib.RootIsolation.Multiplicity.Circle.CenterProduct
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Target
import Purelib.Geometry.Rational.Box.Bounds
public import Purelib.RootIsolation.Newton.Search.Execution.Uniqueness
public import Purelib.RootIsolation.State.WindingOne.Raw
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Requested continuations of retained original circle samples

A positive source residual target reads the same original cached Horner
fold. Its sufficient accuracy selects from the actual preceding sample
state, retaining that sample's point when no strict refinement is needed.
The original track, initial box, radial label and norm ceiling are preserved.
-/

public section

namespace Purelib.RootIsolation.Multiplicity.Circle.CenterProduct.Sample

open Purelib.Data
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Geometry.Projective
open Purelib.Polynomial
open Dense.Gaussian
open Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Dense.Gaussian.Bounds.RootRadius.Box (largeSquareBox)
open Purelib.Polynomial.Clearance.Circle (Certificate)
open Purelib.RootIsolation.State.WindingOne.Basic (WindingOneState)
open Rat.Fraction (Rational)
open Rat.Fraction.Order

set_option genInjectivity false in
/-- A sufficient positive accuracy computed from the same original retained coefficient fold.

The original locations and positive source target remain indices. Only the
new radius is computed; the original polynomial's Horner fold is read from
those locations rather than executed again.
-/
structure Request {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {source : FTA.Squarefree.BoxResult polynomial} (locations : HigherLocations clearance source)
    (target : Rational) where
  /-- The original requested source residual is strictly positive. -/
  target_positive : 0 < target
  /-- The retained sufficient radius shared by all original sample continuations. -/
  radius : Rational
  /-- The radius is exactly the original coefficient-computed residual accuracy. -/
  radius_eq : radius = Bounds.Box.Target.uniformResidualRadius polynomial (largeSquareBox polynomial) target
  /-- The retained radius is strictly positive. -/
  positive : 0 < radius

constructive_injectivity Request

namespace Request

/-- Compute one sufficient accuracy using the same original cached Horner slope. -/
@[expose] def prepare {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {source : FTA.Squarefree.BoxResult polynomial} (locations : HigherLocations clearance source)
    (target : Rational) (targetPositive : 0 < target) : Request locations target :=
  let radius := min 1 (target / (8 * max 1 locations.request.bounds.slope))
  have radiusEq : radius =
      Bounds.Box.Target.uniformResidualRadius polynomial (largeSquareBox polynomial) target := by
    change min 1 (target / (8 * max 1 locations.request.bounds.slope)) = _
    rewrite [locations.request.bounds_eq]
    rfl
  { target_positive := targetPositive, radius, radius_eq := radiusEq
    positive := radiusEq.symm ▸ Bounds.Box.Target.uniformResidualRadius_pos _ _ targetPositive }

end Request

namespace Refinement

open Purelib.RootIsolation.Track.Basic (WindingOneTrack)
open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)

/-- The same original six-proposal search, including every actual attempted numerical value. -/
@[expose] def Attempt {polynomial : CoefficientPolynomial} {ambient : Box} {degree : Nat}
    (elimination : AxisEliminationCertificate polynomial degree)
    (current : WindingOneState polynomial ambient) (radius : Rational) : Type :=
  Newton.Search.Trace.Retained elimination current.raw radius (.canonical elimination)
    ⟨(current.box.xLower + current.box.xUpper) / 2, (current.box.yLower + current.box.yUpper) / 2⟩
    6 0 ⟨(current.box.xLower + current.box.xUpper) / 2, (current.box.yLower + current.box.yUpper) / 2⟩

set_option genInjectivity false in
/-- Certified reuse, an accepted original Newton attempt, or the unchanged total strict fallback.

An insufficient preceding state retains the complete bounded attempt even
when that attempt fails. Failure is only finite inconclusivity; the same
original track supplies the total sufficient refinement in that branch.
-/
inductive Selection {polynomial : CoefficientPolynomial} {ambient : Box} {degree : Nat}
    (elimination : AxisEliminationCertificate polynomial degree)
    (track : WindingOneTrack polynomial ambient) (current : WindingOneState polynomial ambient)
    (radius : Rational) (positive : 0 < radius) : WindingOneState polynomial ambient → Type
  /-- The same cached original state already pays the requested accuracy. -/
  | reused (accurate : current.box.diagonalSq ≤ radius ^ 2) :
      Selection elimination track current radius positive current
  /-- The first accepted certified original bounded proposal pays the complete request. -/
  | accepted (needed : ¬ current.box.diagonalSq ≤ radius ^ 2)
      (attempt : Attempt elimination current radius) (result : RootIsolation.Refinement current.raw radius)
      (found : attempt.finished.value = some result) : Selection elimination track current radius positive result.state
  /-- A retained failed original bounded attempt delegates to the same total strict track. -/
  | refined (needed : ¬ current.box.diagonalSq ≤ radius ^ 2)
      (attempt : Attempt elimination current radius) (failed : attempt.finished.value = none) :
      Selection elimination track current radius positive (track.refine current radius positive)

constructive_injectivity Selection

namespace Selection

variable {polynomial : CoefficientPolynomial} {ambient : Box} {degree : Nat}
variable {elimination : AxisEliminationCertificate polynomial degree}
variable {track : WindingOneTrack polynomial ambient} {current state : WindingOneState polynomial ambient}
variable {radius : Rational} {positive : 0 < radius}

/-- Reuse the same sufficient state, otherwise run one certified bounded attempt before the original total fallback. -/
@[expose] def prepare (elimination : AxisEliminationCertificate polynomial degree)
    (track : WindingOneTrack polynomial ambient) (current : WindingOneState polynomial ambient)
    (radius : Rational) (positive : 0 < radius) :
    (state : WindingOneState polynomial ambient) × Selection elimination track current radius positive state :=
  if accurate : current.box.diagonalSq ≤ radius ^ 2 then
    ⟨current, .reused accurate⟩
  else
    let attempt := Newton.Search.Trace.run elimination current.raw radius (.canonical elimination)
      ⟨(current.box.xLower + current.box.xUpper) / 2, (current.box.yLower + current.box.yUpper) / 2⟩
    match found : attempt.finished.value with
    | some result => ⟨result.state, .accepted accurate attempt result found⟩
    | none => ⟨track.refine current radius positive, .refined accurate attempt found⟩

/-- Retained branch evidence restores the complete same selected state, attempted data and stopping result. -/
theorem result_eq_prepare (selection : Selection elimination track current radius positive state) :
    (⟨state, selection⟩ : (next : WindingOneState polynomial ambient) ×
      Selection elimination track current radius positive next) =
      prepare elimination track current radius positive := by
  cases selection with
  | reused accurate => unfold prepare; rw [dif_pos accurate]
  | accepted needed attempt result found =>
      unfold Attempt at attempt
      unfold prepare
      rw [dif_neg needed, ← attempt.eq_run]
      dsimp only
      split
      next other otherFound =>
        have same := Option.some.inj (found.symm.trans otherFound)
        cases same
        rfl
      next absent => cases found.symm.trans absent
  | refined needed attempt failed =>
      unfold Attempt at attempt
      unfold prepare
      rw [dif_neg needed, ← attempt.eq_run]
      dsimp only
      split
      next other otherFound => cases failed.symm.trans otherFound
      next absent => rfl

/-- Read the certified original reuse branch without rerunning the attempt or total refiner. -/
@[expose] def isReused : Selection elimination track current radius positive state → Bool
  | .reused _ => true
  | .accepted _ _ _ _ => false
  | .refined _ _ _ => false

/-- All certified selection branches remain inside the exact original preceding state. -/
theorem nested (selection : Selection elimination track current radius positive state) :
    state.box.Refines current.box := by
  cases selection with
  | reused _ => exact Box.refines_refl _
  | accepted _ _ result _ => exact Box.Refinement.StrictInterior.refines result.strict
  | refined _ _ _ => exact track.nested current radius positive

/-- Every certified selected state pays the exact requested squared-diagonal bound. -/
theorem accurate (selection : Selection elimination track current radius positive state) :
    state.box.diagonalSq ≤ radius ^ 2 := by
  cases selection with
  | reused accurate => exact accurate
  | accepted _ _ result _ => exact result.accurate
  | refined _ _ _ => exact track.accurate current radius positive

end Selection
end Refinement

set_option genInjectivity false in
/-- A requested original sample state with its retained reuse or strict-refinement certificate.

The preceding sample remains an index. Selection starts from that exact
sample's retained state, and the point is the selected original box anchor.
The canonical constructor reads the preceding cached point in its reused branch.
-/
structure Refinement {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {source : FTA.Squarefree.BoxResult polynomial} {locations : HigherLocations clearance source}
    {original : CenterProduct.Request clearance source} {index : Fin original.regions.length}
    (sample : Sample locations original index) {target : Rational} (request : Request locations target) where
  /-- The actual selected original state. -/
  state : WindingOneState polynomial (largeSquareBox polynomial)
  /-- The same original state is reused, accepted by the checked bounded attempt, or strictly refined after its miss. -/
  selection : Refinement.Selection (source.elimination locations.degreePositive)
    (source.isolation.tracks.get (original.trackIndex index))
    sample.state request.radius request.positive state
  /-- The actual cached rational point of the selected original state. -/
  point : Canonical
  /-- The point is the selected original box's anchor. -/
  point_eq : point = state.box.anchor

constructive_injectivity Refinement

namespace Refinement

variable {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
variable {source : FTA.Squarefree.BoxResult polynomial} {locations : HigherLocations clearance source}
variable {original : CenterProduct.Request clearance source} {index : Fin original.regions.length}
variable {target : Rational}

/-- Retain a selected original state, reusing the preceding actual point precisely in the reused branch. -/
@[expose] def ofSelection (sample : Sample locations original index) (request : Request locations target)
    (state : WindingOneState polynomial (largeSquareBox polynomial))
    (selection : Selection (source.elimination locations.degreePositive)
      (source.isolation.tracks.get (original.trackIndex index))
      sample.state request.radius request.positive state) : Refinement sample request :=
  let point := if selection.isReused then sample.point else state.box.anchor
  { state, selection, point
    point_eq := by
      cases selection with
      | reused _ => exact sample.point_eq
      | accepted _ _ _ _ => rfl
      | refined _ _ _ => rfl }

/-- Request the new sufficient accuracy from the same cached original sample state.

The original selected-state procedure runs once. Its reused branch consumes
the preceding sample's actual point; its strict branch computes one new anchor.
-/
@[expose] def prepare (sample : Sample locations original index) (request : Request locations target) :
    Refinement sample request :=
  let selected := Selection.prepare (source.elimination locations.degreePositive)
    (source.isolation.tracks.get (original.trackIndex index))
    sample.state request.radius request.positive
  ofSelection sample request selected.1 selected.2

/-- Typed selected-state evidence restores the complete same requested sample procedure. -/
theorem ofSelection_eq_prepare (sample : Sample locations original index) (request : Request locations target)
    (state : WindingOneState polynomial (largeSquareBox polynomial))
    (selection : Selection (source.elimination locations.degreePositive)
      (source.isolation.tracks.get (original.trackIndex index))
      sample.state request.radius request.positive state) :
    ofSelection sample request state selection = prepare sample request := by
  exact congrArg (fun selected => ofSelection sample request selected.1 selected.2)
    selection.result_eq_prepare

/-- A sufficient retained sample preserves its complete original state, point and reuse branch. -/
theorem prepare_reuses (sample : Sample locations original index) (request : Request locations target)
    (accurate : sample.state.box.diagonalSq ≤ request.radius ^ 2) :
    (prepare sample request).state = sample.state ∧
      (prepare sample request).point = sample.point ∧
        (prepare sample request).selection.isReused = true := by
  unfold prepare Selection.prepare
  rewrite [dif_pos accurate]
  exact ⟨rfl, rfl, rfl⟩

/-- The selected point belongs to its same actual returned original state. -/
theorem inside {sample : Sample locations original index} {request : Request locations target}
    (refinement : Refinement sample request) : refinement.state.box.Contains refinement.point :=
  refinement.point_eq.symm ▸ refinement.state.box.contains_anchor

/-- The selected point remains inside its preceding retained original sample state. -/
theorem inside_previous {sample : Sample locations original index} {request : Request locations target}
    (refinement : Refinement sample request) : sample.state.box.Contains refinement.point :=
  refinement.selection.nested.contains refinement.inside

/-- The same requested point remains inside its original retained radial owner's box. -/
theorem inside_radial {sample : Sample locations original index} {request : Request locations target}
    (refinement : Refinement sample request) :
    (locations.refinementAt (original.trackIndex index)).next.box.Contains refinement.point :=
  sample.selection.nested.contains refinement.inside_previous

/-- The requested point remains inside its same original isolated initial box occurrence. -/
theorem inside_region {sample : Sample locations original index} {request : Request locations target}
    (refinement : Refinement sample request) : (original.regions.get index).Contains refinement.point := by
  rewrite [original.regionAt_eq]
  exact (locations.refinementAt (original.trackIndex index)).refines.contains refinement.inside_radial

/-- The requested point satisfies the same original fixed squared norm ceiling. -/
theorem node_bound {sample : Sample locations original index} {request : Request locations target}
    (refinement : Refinement sample request) : Gaussian.Norm.Basic.normSq refinement.point ≤ original.radius := by
  rewrite [original.radius_eq]
  exact Box.normSq_le_normSqBound (refinement.state.refinesAmbient.contains refinement.inside)

/-- The requested point retains the strict side of its same original cached radial owner. -/
theorem radial {sample : Sample locations original index} {request : Request locations target}
    (refinement : Refinement sample request) :
    match (locations.refinementAt (original.trackIndex index)).side with
    | .negative _ => refinement.point.normSq < 1
    | .positive _ => 1 < refinement.point.normSq := by
  cases side : (locations.refinementAt (original.trackIndex index)).side with
  | negative holds =>
      have negative := holds refinement.point refinement.inside_radial
      rewrite [Hermitian.eval_affineNormComparisonForm, Gaussian.Norm.Basic.normSq_eq_canonical] at negative
      exact Arithmetic.lt_of_sub_neg_direct negative
  | positive holds =>
      have positive := holds refinement.point refinement.inside_radial
      rewrite [Hermitian.eval_affineNormComparisonForm, Gaussian.Norm.Basic.normSq_eq_canonical] at positive
      exact Arithmetic.lt_of_sub_pos_direct positive

/-- The same requested point pays the positive original-factor source residual target. -/
theorem residual_lt {sample : Sample locations original index} {request : Request locations target}
    (refinement : Refinement sample request) :
    Gaussian.Norm.Basic.normSq (polynomial.eval refinement.point) < target := by
  have accurate : refinement.state.box.diagonalSq ≤
      (Bounds.Box.Target.uniformResidualRadius polynomial (largeSquareBox polynomial) target) ^ 2 := by
    rewrite [← request.radius_eq]
    exact refinement.selection.accurate
  exact Winding.Bounds.Residual.normSq_eval_lt_of_diagonal locations.degreePositive refinement.state
    request.target_positive accurate refinement.inside

/-- The requested point preserves the original quantitative collar gap, beyond its strict radial label. -/
theorem radial_gap {sample : Sample locations original index} {request : Request locations target}
    (refinement : Refinement sample request) :
    locations.request.collar.width ^ 2 < (refinement.point.normSq - 1) ^ 2 :=
  (locations.refinementAt (original.trackIndex index)).radial_gap refinement.inside_radial

end Refinement
end Purelib.RootIsolation.Multiplicity.Circle.CenterProduct.Sample

end
