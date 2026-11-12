module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.RootIsolation.Newton.Search.Attempt
import Purelib.RootIsolation.State.Raw
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Subdivision.Raw.Request

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticAxisElimination
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticLineClearance
import Purelib.RootIsolation.SquareRoot.Replay.QuadraticSampleReplay
public import Purelib.RootIsolation.SquareRoot.Replay.QuadraticTrackReplay
import Purelib.RootIsolation.SquareRoot.Replay.QuadraticTrackSampleReplay
import Purelib.Geometry.Rational.Box.Refinement
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.Refinement.Basic
import Purelib.RootIsolation.State.WindingOne.Raw
import Purelib.RootIsolation.Track.Basic

open Purelib.RootIsolation.SquareRoot.Clearance

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

public section

/-!
Replay the strict-inset branch of the original deferred quadratic refiner.
Saved winding chains supply the expensive finite decisions. A nonzero raw
subdivision depth remains an explicit unresolved attempt, never a different
root track or an increased Newton-search budget.
-/

namespace Purelib.RootIsolation.SquareRoot.Replay.QuadraticFallbackReplay

open QuadraticSampleReplay (Coordinate Gaussian Box)
open Purelib.Riemann.Integration
open Purelib.Riemann.Topology

/-- The original winding-one quadratic state in its retained ambient box. -/
abbrev State (parameter : Gaussian) (ambient : Geometry.Rational.Box) :=
  State.WindingOne.Basic.WindingOneState (ExactQuadraticOwnerClearance.rootPolynomial parameter)
    ambient
open Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance (directBoundaryClearance)
open SquareRootContinuationChain (Owner)

/-- The original proper box strictly inside the current quadratic state box. -/
abbrev Inset {parameter : Gaussian} {ambient : Geometry.Rational.Box} (current :
  State parameter
  ambient) :=
  ExactQuadraticOwnerClearance.StrictInsetData current
/-- The original raw winding state certified strictly inside the current state box. -/
abbrev RawInset {parameter : Gaussian} {ambient : Geometry.Rational.Box} (current :
  State
  parameter ambient) :=
  ExactQuadraticOwnerClearance.StrictRawInset current

/-- Construct the original fixed strict inset of the retained current box. -/
@[expose] def fixedInset {parameter : Gaussian} {ambient : Geometry.Rational.Box} (current :
  State parameter ambient) : Inset
  current :=
  Clearance.ExactQuadraticOwnerClearance.StrictInsetData.mk
    (ExactQuadraticOwnerClearance.strictInsetBox current.box current.proper)
    (ExactQuadraticOwnerClearance.strictInsetBox_strict current.box current.proper)
    (ExactQuadraticOwnerClearance.strictInsetBox_proper current.box current.proper)

/-- Read the original clearance-protected strict inset of the retained current state. -/
@[expose] def protectedInset {parameter : Gaussian} {ambient : Geometry.Rational.Box} (current :
  State parameter ambient) : Inset
  current :=
  ExactQuadraticOwnerClearance.protectedStrictInset current

/-- A retained option equal to the original checked raw-inset decision for this exact inset. -/
abbrev InsetDecision {parameter : Gaussian} {ambient : Geometry.Rational.Box} (current :
  State
  parameter ambient)
    (inset : Inset current) :=
  { value : Option (RawInset current) // value =
    ExactQuadraticOwnerClearance.checkedRawInset? current inset }

/-- The exact canonical inset decision, assembled from a checked winding value. -/
@[expose, irreducible] def checkInset {parameter : Gaussian} {ambient : Geometry.Rational.Box} (current :
  State parameter ambient)
    (inset : Inset current)
    (winding : { value : Int // value = Winding.Box.Basic.quadrupledBoxWinding
      (ExactQuadraticOwnerClearance.rootPolynomial parameter)
        (ExactQuadraticOwnerClearance.StrictInsetData.box inset) }) :
    { value : Option (RawInset current) // value =
      ExactQuadraticOwnerClearance.checkedRawInset? current inset } := by
  if left : QuadraticAxisElimination.verticalDeterminant parameter
    (ExactQuadraticOwnerClearance.StrictInsetData.box inset).xLower ≠ 0 then
    if right : QuadraticAxisElimination.verticalDeterminant parameter
      (ExactQuadraticOwnerClearance.StrictInsetData.box inset).xUpper ≠ 0 then
      if bottom : QuadraticAxisElimination.horizontalDeterminant parameter
        (ExactQuadraticOwnerClearance.StrictInsetData.box inset).yLower ≠ 0 then
        if top : QuadraticAxisElimination.horizontalDeterminant parameter
          (ExactQuadraticOwnerClearance.StrictInsetData.box inset).yUpper ≠ 0 then
          if four : winding.val = 4 then
            have windingFour := winding.property.symm.trans four
            let value : RawInset current :=
              Clearance.ExactQuadraticOwnerClearance.StrictRawInset.mk
                ⟨(ExactQuadraticOwnerClearance.StrictInsetData.box inset),
                (Box.Refinement.StrictInterior.refines
                (ExactQuadraticOwnerClearance.StrictInsetData.strict inset)).trans
                current.refinesAmbient, (ExactQuadraticOwnerClearance.StrictInsetData.proper
                inset),
                directBoundaryClearance parameter (ExactQuadraticOwnerClearance.StrictInsetData.box
                  inset) left right bottom top,
                by rw [windingFour]; decide⟩ (ExactQuadraticOwnerClearance.StrictInsetData.strict
                  inset)
            exact ⟨some value, by
              unfold ExactQuadraticOwnerClearance.checkedRawInset?
              dsimp only
              rw [dif_pos left, dif_pos right, dif_pos bottom, dif_pos top, dif_pos windingFour]⟩
          else
            have miss : Winding.Box.Basic.quadrupledBoxWinding
                (ExactQuadraticOwnerClearance.rootPolynomial parameter)
                  (ExactQuadraticOwnerClearance.StrictInsetData.box inset) ≠ 4 := by
              rw [← winding.property]; exact four
            exact ⟨none, by
              unfold ExactQuadraticOwnerClearance.checkedRawInset?
              dsimp only
              rw [dif_pos left, dif_pos right, dif_pos bottom, dif_pos top, dif_neg miss]⟩
        else exact ⟨none, by unfold ExactQuadraticOwnerClearance.checkedRawInset?; dsimp only; rw
          [dif_pos left, dif_pos right, dif_pos bottom, dif_neg top]⟩
      else exact ⟨none, by unfold ExactQuadraticOwnerClearance.checkedRawInset?; dsimp only; rw
        [dif_pos left, dif_pos right, dif_neg bottom]⟩
    else exact ⟨none, by unfold ExactQuadraticOwnerClearance.checkedRawInset?; dsimp only; rw
      [dif_pos left, dif_neg right]⟩
  else exact ⟨none, by unfold ExactQuadraticOwnerClearance.checkedRawInset?; dsimp only; rw
    [dif_neg left]⟩

/-- Read the exact box retained by the original strict-inset data. -/
@[expose] def insetBox {parameter : Gaussian} {ambient : Geometry.Rational.Box} {current :
  State
  parameter ambient}
    (inset : Inset current) : Geometry.Rational.Box :=
      ExactQuadraticOwnerClearance.StrictInsetData.box inset

/-- Read the exact raw winding state retained by the original checked inset. -/
@[expose] def rawState {parameter : Gaussian} {ambient : Geometry.Rational.Box} {current :
  State
  parameter ambient}
    (inset : RawInset current) :=
      ExactQuadraticOwnerClearance.StrictRawInset.state inset

/-- A successful checked inset retains the supplied cached winding as the winding of its exact returned box. -/
theorem checkInset_winding {parameter : Gaussian} {ambient : Geometry.Rational.Box} (current :
  State parameter ambient)
    (data : Inset current)
    (winding : { value : Int // value = Winding.Box.Basic.quadrupledBoxWinding
      (ExactQuadraticOwnerClearance.rootPolynomial parameter)
        (insetBox data) })
    (inset : RawInset current) (found :
      (checkInset current data winding).val = some inset) :
    winding.val = Winding.Box.Basic.quadrupledBoxWinding
      (ExactQuadraticOwnerClearance.rootPolynomial parameter)
        (rawState inset).box := by
  unfold checkInset at found
  dsimp only at found
  by_cases left : QuadraticAxisElimination.verticalDeterminant parameter
    (ExactQuadraticOwnerClearance.StrictInsetData.box data).xLower ≠ 0
  · rw [dif_pos left] at found
    by_cases right : QuadraticAxisElimination.verticalDeterminant parameter
      (ExactQuadraticOwnerClearance.StrictInsetData.box data).xUpper ≠ 0
    · rw [dif_pos right] at found
      by_cases bottom : QuadraticAxisElimination.horizontalDeterminant parameter
        (ExactQuadraticOwnerClearance.StrictInsetData.box data).yLower ≠ 0
      · rw [dif_pos bottom] at found
        by_cases top : QuadraticAxisElimination.horizontalDeterminant parameter
          (ExactQuadraticOwnerClearance.StrictInsetData.box data).yUpper ≠ 0
        · rw [dif_pos top] at found
          by_cases four : winding.val = 4
          · rw [dif_pos four] at found
            cases Option.some.inj found
            exact winding.property
          · rw [dif_neg four] at found
            cases found
        · rw [dif_neg top] at found
          cases found
      · rw [dif_neg bottom] at found
        cases found
    · rw [dif_neg right] at found
      cases found
  · rw [dif_neg left] at found
    cases found

set_option genInjectivity false in
/-- A selected original raw inset together with its checked selection and cached winding.

The equality fields bind both the option returned by the original search and the winding of the exact retained box. -/
structure SelectedInset {parameter : Gaussian} {ambient : Geometry.Rational.Box} (current :
  State parameter ambient) where
  /-- The exact raw inset returned by the original checked search. -/ value :
    RawInset current
  /-- The original inset search returns this retained inset. -/ equation :
    ExactQuadraticOwnerClearance.strictRawInset? current = some value
  /-- The cached quadrupled winding of the retained inset box. -/ winding : Int
  /-- The cached winding equals the original polynomial's winding on this exact retained box. -/ winding_eq : winding =
    Winding.Box.Basic.quadrupledBoxWinding
    (ExactQuadraticOwnerClearance.rootPolynomial parameter)
      (rawState value).box

constructive_injectivity SelectedInset

/-- A retained option equal to the original fixed-then-protected inset search result. -/
abbrev InsetAttempt {parameter : Gaussian} {ambient : Geometry.Rational.Box} (current :
  State
  parameter ambient) :=
  { value : Option (RawInset current) //
    ExactQuadraticOwnerClearance.strictRawInset? current = value }

/-- Reconstruct the original failed inset search from failures of both retained inset checks. -/
@[expose] def missingInsets {parameter : Gaussian} {ambient : Geometry.Rational.Box} (current :
  State parameter ambient)
    (fixed : InsetDecision current
      (fixedInset current)) (fixedMiss : fixed.val = none)
    (narrow : InsetDecision current
      (protectedInset current)) (narrowMiss : narrow.val = none) :
    InsetAttempt current :=
  ⟨none, by
    unfold ExactQuadraticOwnerClearance.strictRawInset?
    change (match ExactQuadraticOwnerClearance.checkedRawInset? current
      (fixedInset current) with
      | some value => some value
      | none => ExactQuadraticOwnerClearance.checkedRawInset? current
        (protectedInset current)) = none
    rw [← fixed.property, fixedMiss]
    exact narrow.property.symm.trans narrowMiss⟩

/-- A successful fixed-inset check is the exact result of the original inset search. -/
theorem firstInset {parameter : Gaussian} {ambient : Geometry.Rational.Box} (current :
  State
  parameter ambient)
    (fixed : { value : Option (RawInset current) // value =
      ExactQuadraticOwnerClearance.checkedRawInset? current
      (fixedInset current) })
    (inset : RawInset current) (found : fixed.val = some inset) :
    ExactQuadraticOwnerClearance.strictRawInset? current = some inset := by
  unfold ExactQuadraticOwnerClearance.strictRawInset?
  change (match ExactQuadraticOwnerClearance.checkedRawInset? current
    (fixedInset current) with
    | some value => some value
    | none => ExactQuadraticOwnerClearance.checkedRawInset? current
      (protectedInset current)) = _
  rw [← fixed.property, found]

/-- After the fixed-inset check fails, the original search returns the retained protected-inset decision exactly. -/
theorem secondInset {parameter : Gaussian} {ambient : Geometry.Rational.Box} (current :
  State
  parameter ambient)
    (fixed : { value : Option (RawInset current) // value =
      ExactQuadraticOwnerClearance.checkedRawInset? current
      (fixedInset current) })
    (missed : fixed.val = none)
    (narrow : { value : Option (RawInset current) // value =
      ExactQuadraticOwnerClearance.checkedRawInset? current
      (protectedInset current) }) :
    ExactQuadraticOwnerClearance.strictRawInset? current = narrow.val := by
  unfold ExactQuadraticOwnerClearance.strictRawInset?
  change (match ExactQuadraticOwnerClearance.checkedRawInset? current
    (fixedInset current) with
    | some value => some value
    | none => ExactQuadraticOwnerClearance.checkedRawInset? current
      (protectedInset current)) = _
  rw [← fixed.property, missed]
  exact narrow.property.symm

/-- The original certified fast refinement of the current quadratic state at the supplied accuracy. -/
abbrev Fast {parameter : Gaussian} {ambient : Geometry.Rational.Box} (current :
  State parameter
  ambient) (epsilon : Coordinate) :=
  ExactQuadraticOwnerClearance.FastRefinement current epsilon

/-- Read the exact next winding-one state retained by a successful fast refinement. -/
@[expose] def fastState {parameter : Gaussian} {ambient : Geometry.Rational.Box} {current :
  State parameter ambient} {epsilon : Coordinate}
    (fast : Fast current epsilon) :
      State parameter ambient :=
      ExactQuadraticOwnerClearance.FastRefinement.state fast

/-- The inset's checked winding is reused when promoting it to a full state. -/
@[expose, irreducible] def promote {parameter : Gaussian} {ambient : Geometry.Rational.Box} (current :
  State parameter ambient)
    (epsilon : Coordinate) (inset : RawInset current)
    (accurate : (rawState inset).box.diagonalSq ≤ epsilon ^ 2)
    (winding : { value : Int // value = Winding.Box.Basic.quadrupledBoxWinding
      (ExactQuadraticOwnerClearance.rootPolynomial parameter)
        (rawState inset).box }) :
    { value : Option (Fast current epsilon) // value =
      ExactQuadraticOwnerClearance.checkedFastRefinement? current epsilon
      (rawState inset)
        (ExactQuadraticOwnerClearance.StrictRawInset.strict inset) accurate } := by
  let candidate := rawState inset
  if left : QuadraticAxisElimination.verticalDeterminant parameter candidate.box.xLower ≠ 0 then
    if right : QuadraticAxisElimination.verticalDeterminant parameter candidate.box.xUpper ≠ 0 then
      if bottom : QuadraticAxisElimination.horizontalDeterminant parameter candidate.box.yLower ≠ 0
        then
        if top : QuadraticAxisElimination.horizontalDeterminant parameter candidate.box.yUpper ≠ 0
          then
          if four : winding.val = 4 then
            have windingFour := winding.property.symm.trans four
            let state : State parameter ambient :=
              ⟨candidate.box, candidate.refinesAmbient, candidate.proper,
                directBoundaryClearance parameter candidate.box left right bottom top, windingFour,
                QuadraticLineClearance.ExactQuadraticOwnerClearance.directVerticalClearance
                  parameter ambient candidate.box.xLower left,
                QuadraticLineClearance.ExactQuadraticOwnerClearance.directVerticalClearance
                  parameter ambient candidate.box.xUpper right,
                QuadraticLineClearance.ExactQuadraticOwnerClearance.directHorizontalClearance
                  parameter ambient candidate.box.yLower bottom,
                QuadraticLineClearance.ExactQuadraticOwnerClearance.directHorizontalClearance
                  parameter ambient candidate.box.yUpper top⟩
            let value : Fast current epsilon :=
              Clearance.ExactQuadraticOwnerClearance.FastRefinement.mk state
              (Box.Refinement.StrictInterior.refines
                (ExactQuadraticOwnerClearance.StrictRawInset.strict inset))
                (ExactQuadraticOwnerClearance.StrictRawInset.strict inset) accurate
            exact ⟨some value, by
              unfold ExactQuadraticOwnerClearance.checkedFastRefinement?
              rw [dif_pos left, dif_pos right, dif_pos bottom, dif_pos top, dif_pos windingFour]⟩
          else
            have miss : Winding.Box.Basic.quadrupledBoxWinding
                (ExactQuadraticOwnerClearance.rootPolynomial parameter) candidate.box ≠ 4 := by
              rw [← winding.property]; exact four
            exact ⟨none, by
              unfold ExactQuadraticOwnerClearance.checkedFastRefinement?
              rw [dif_pos left, dif_pos right, dif_pos bottom, dif_pos top, dif_neg miss]⟩
        else exact ⟨none, by unfold ExactQuadraticOwnerClearance.checkedFastRefinement?; rw
          [dif_pos left, dif_pos right, dif_pos bottom, dif_neg top]⟩
      else exact ⟨none, by unfold ExactQuadraticOwnerClearance.checkedFastRefinement?; rw [dif_pos
        left, dif_pos right, dif_neg bottom]⟩
    else exact ⟨none, by unfold ExactQuadraticOwnerClearance.checkedFastRefinement?; rw [dif_pos
      left, dif_neg right]⟩
  else exact ⟨none, by unfold ExactQuadraticOwnerClearance.checkedFastRefinement?; rw [dif_neg
    left]⟩

/-- Run the original quadratic subdivision fallback at the supplied positive accuracy. -/
@[expose] def subdivision {parameter : Gaussian} {ambient : Geometry.Rational.Box} (current :
  State parameter ambient)
    (epsilon : Coordinate) (positive : 0 < epsilon) :=
      ExactQuadraticOwnerClearance.subdivisionRefinement? current epsilon positive

/-- Continue the original fallback from an accurate raw candidate.

Check it directly when strictly inside the current box; otherwise use the retained original inset search and
subdivision. -/
private def afterRaw {parameter : Gaussian} {ambient : Geometry.Rational.Box} (current :
  State
  parameter ambient)
    (epsilon : Coordinate) (positive : 0 < epsilon)
    (candidate : State.Raw.RawWindingState (ExactQuadraticOwnerClearance.rootPolynomial parameter)
      ambient)
    (accurate : candidate.box.diagonalSq ≤ epsilon ^ 2) : Option (Fast current
      epsilon) :=
  open Purelib.Data.Rat in if strict : candidate.box.StrictInterior current.box then
    Clearance.ExactQuadraticOwnerClearance.checkedFastRefinement? current epsilon candidate strict accurate
  else
    match ExactQuadraticOwnerClearance.strictRawInset? current with
    | none => none
    | some inset =>
      let next := Subdivision.Raw.Request.refineTo (p :=
        ExactQuadraticOwnerClearance.rootPolynomial parameter)
        (QuadraticAxisElimination.quadraticAxisElimination parameter)
          (rawState inset) (epsilon ^ 2)
      ExactQuadraticOwnerClearance.checkedFastRefinement? current epsilon next
        (Box.Refinement.StrictInterior.of_refines
          (ExactQuadraticOwnerClearance.StrictRawInset.strict inset)
          (Subdivision.Raw.Request.refineTo_refines _ _ _))
        (Subdivision.Raw.Request.refineTo_diagonalSq_le _ _
          (Fraction.Order.Arithmetic.pow_pos_direct positive 2))

/-- Equal raw candidates yield the same continuation of the original fallback. -/
private theorem afterRaw_congr {parameter : Gaussian} {ambient : Geometry.Rational.Box} (current :
  State parameter ambient)
    (epsilon : Coordinate) (positive : 0 < epsilon)
    (first second : State.Raw.RawWindingState (ExactQuadraticOwnerClearance.rootPolynomial
      parameter) ambient)
    (firstAccurate : first.box.diagonalSq ≤ epsilon ^ 2) (secondAccurate : second.box.diagonalSq ≤ epsilon ^ 2)
    (same : first = second) : afterRaw current epsilon positive first
      firstAccurate =
      afterRaw current epsilon positive second secondAccurate := by
  cases same
  rfl

/-- Equal raw candidates yield the same original checked fast-refinement option. -/
private theorem checkedFast_congr {parameter : Gaussian} {ambient : Geometry.Rational.Box} (current :
  State parameter ambient)
    (epsilon : Coordinate)
    (first second : State.Raw.RawWindingState (ExactQuadraticOwnerClearance.rootPolynomial
      parameter) ambient)
    (firstStrict : first.box.StrictInterior current.box) (secondStrict : second.box.StrictInterior current.box)
    (firstAccurate : first.box.diagonalSq ≤ epsilon ^ 2) (secondAccurate : second.box.diagonalSq ≤ epsilon ^ 2)
    (same : first = second) : ExactQuadraticOwnerClearance.checkedFastRefinement? current epsilon
      first firstStrict firstAccurate =
      ExactQuadraticOwnerClearance.checkedFastRefinement? current epsilon second secondStrict
        secondAccurate := by
  cases same
  rfl

/-- A raw subdivision request of depth zero returns the supplied raw state unchanged. -/
private theorem refineTo_zero {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {ambient : Geometry.Rational.Box} {degree :
  Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degree)
    (state : State.Raw.RawWindingState p ambient) (threshold : Coordinate)
    (zero : Subdivision.Raw.Request.refinementDepth state threshold = 0) :
    Subdivision.Raw.Request.refineTo elimination state threshold = state := by
  unfold Subdivision.Raw.Request.refineTo
  rw [zero]
  rfl

/-- A zero-depth subdivision request already satisfies the supplied squared accuracy. -/
theorem zero_accurate {parameter : Gaussian} {ambient : Geometry.Rational.Box}
    (state : State.Raw.RawWindingState (ExactQuadraticOwnerClearance.rootPolynomial parameter)
      ambient)
    (epsilon : Coordinate) (positive : 0 < epsilon)
    (zero : Subdivision.Raw.Request.refinementDepth state (epsilon ^ 2) = 0) : state.box.diagonalSq ≤ epsilon ^ 2 :=
      open Purelib.Data.Rat in by
  let elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate
      (ExactQuadraticOwnerClearance.rootPolynomial parameter) 4 :=
        QuadraticAxisElimination.quadraticAxisElimination parameter
  have accurate := Subdivision.Raw.Request.refineTo_diagonalSq_le elimination state
    (Fraction.Order.Arithmetic.pow_pos_direct positive 2)
  rw [refineTo_zero elimination state (epsilon ^ 2) zero] at accurate
  exact accurate

/-- When both subdivision depths are zero, the original fallback is exactly the checked refinement of the retained
inset. -/
theorem subdivision_zero {parameter : Gaussian} {ambient : Geometry.Rational.Box} (current :
  State parameter ambient)
    (epsilon : Coordinate) (positive : 0 < epsilon)
    (initialDepth : Subdivision.Raw.Request.refinementDepth current.raw (epsilon ^ 2) = 0)
    (inset : RawInset current) (found :
      ExactQuadraticOwnerClearance.strictRawInset? current = some inset)
    (insetDepth : Subdivision.Raw.Request.refinementDepth (rawState inset)
      (epsilon ^ 2) = 0)
    (accurate : (rawState inset).box.diagonalSq ≤ epsilon ^ 2) :
    subdivision current epsilon positive =
      ExactQuadraticOwnerClearance.checkedFastRefinement? current epsilon
      (rawState inset)
        (ExactQuadraticOwnerClearance.StrictRawInset.strict inset) accurate := open
        Purelib.Data.Rat in by
  let elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate
      (ExactQuadraticOwnerClearance.rootPolynomial parameter) 4 :=
        QuadraticAxisElimination.quadraticAxisElimination parameter
  have first := refineTo_zero elimination current.raw (epsilon ^ 2)
    initialDepth
  have firstAccurate := Subdivision.Raw.Request.refineTo_diagonalSq_le elimination current.raw
    (Fraction.Order.Arithmetic.pow_pos_direct positive 2)
  have currentAccurate : current.raw.box.diagonalSq ≤ epsilon ^ 2 := by
    rw [first] at firstAccurate
    exact firstAccurate
  have step : subdivision current epsilon positive =
    afterRaw current epsilon positive current.raw currentAccurate :=
    afterRaw_congr current epsilon positive _ _ firstAccurate currentAccurate
      first
  rw [step]
  have notStrict : ¬ current.raw.box.StrictInterior current.box := by
    intro strict
    exact (lt_irrefl current.box.xLower) strict.1
  unfold afterRaw
  rw [dif_neg notStrict, found]
  exact checkedFast_congr current epsilon _ _ _ _ _ _
    (refineTo_zero elimination
      (rawState inset) (epsilon ^ 2) insetDepth)

/-- After the first attempt fails, a successful original subdivision determines the deferred track's next state exactly.
-/
theorem deferred_refine {parameter : Gaussian} {ambient : Geometry.Rational.Box} (nonzero : parameter ≠ 0)
    (initial current : State parameter ambient) (epsilon : Coordinate)
      (positive : 0 < epsilon)
    (missed : QuadraticSampleReplay.attempt current epsilon = none)
    (accepted : Fast current epsilon) (found :
      subdivision current epsilon positive = some accepted) :
    (QuadraticSampleReplay.Recipe.deferred.track nonzero initial).refine current epsilon positive =
      fastState accepted := by
  change ExactQuadraticOwnerClearance.deferredRefine nonzero current epsilon positive = _
  unfold ExactQuadraticOwnerClearance.deferredRefine
  unfold ExactQuadraticOwnerClearance.fastRefinement?
  with_unfolding_all erw [show Newton.Search.Attempt.attempt
    (QuadraticAxisElimination.quadraticAxisElimination parameter)
    current.raw epsilon (QuadraticLineClearance.Owner.quadraticAxisClearances parameter) = none
      from missed]
  with_unfolding_all erw [show ExactQuadraticOwnerClearance.subdivisionRefinement? current epsilon
    positive = some accepted from found]
  rfl

/-- Available original-source evidence. A checked-first law alone does not
identify the later fallback of an arbitrary inherited track. -/
inductive Plan {parameter : Gaussian} {ambient : Geometry.Rational.Box} (track :
  QuadraticTrackReplay.Track parameter
  ambient) where
  /-- Only the successful first-attempt law is retained; no later fallback identity is supplied. -/ | checkedFirstOnly
  /-- The retained track's total refinement function equals the original deferred recipe at every state and positive
    request. -/ | deferred (nonzero : parameter ≠ 0)
      (equation : ∀ (current : State parameter ambient) (epsilon : Coordinate)
        (positive : 0 < epsilon),
        track.refine current epsilon positive =
          (QuadraticSampleReplay.Recipe.deferred.track nonzero track.initial).refine current epsilon positive)

/-- Retain the original deferred fallback equation from a matching deferred owner recipe. -/
@[expose] def Plan.ofDeferred {parameter : Gaussian} (owner : Owner parameter)
    (same : QuadraticSampleReplay.Recipe.deferred.Matches owner) : Plan
      owner.track :=
  .deferred owner.parameterNonzero (by
    intro current epsilon positive
    have refine := congrArg (fun track => track.refine current epsilon positive) same
    exact refine.symm)

end Purelib.RootIsolation.SquareRoot.Replay.QuadraticFallbackReplay

end
