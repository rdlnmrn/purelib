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
abbrev State (parameter : Gaussian) (ambient : Purelib.Geometry.Rational.Box) :=
  State.WindingOne.Basic.WindingOneState (SquareRoot.Clearance.ExactQuadraticOwnerClearance.rootPolynomial parameter)
    ambient
open Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance (directBoundaryClearance)
open SquareRootContinuationChain (Owner)

/-- The original proper box strictly inside the current quadratic state box. -/
abbrev Inset {parameter : Gaussian} {ambient : Purelib.Geometry.Rational.Box} (current :
  SquareRoot.Replay.QuadraticFallbackReplay.State parameter
  ambient) :=
  SquareRoot.Clearance.ExactQuadraticOwnerClearance.StrictInsetData current
/-- The original raw winding state certified strictly inside the current state box. -/
abbrev RawInset {parameter : Gaussian} {ambient : Purelib.Geometry.Rational.Box} (current :
  SquareRoot.Replay.QuadraticFallbackReplay.State
  parameter ambient) :=
  SquareRoot.Clearance.ExactQuadraticOwnerClearance.StrictRawInset current

/-- Construct the original fixed strict inset of the retained current box. -/
@[expose] def fixedInset {parameter : Gaussian} {ambient : Purelib.Geometry.Rational.Box} (current :
  SquareRoot.Replay.QuadraticFallbackReplay.State parameter ambient) : SquareRoot.Replay.QuadraticFallbackReplay.Inset
  current :=
  SquareRoot.Clearance.ExactQuadraticOwnerClearance.StrictInsetData.mk
    (SquareRoot.Clearance.ExactQuadraticOwnerClearance.strictInsetBox current.box current.proper)
    (SquareRoot.Clearance.ExactQuadraticOwnerClearance.strictInsetBox_strict current.box current.proper)
    (SquareRoot.Clearance.ExactQuadraticOwnerClearance.strictInsetBox_proper current.box current.proper)

/-- Read the original clearance-protected strict inset of the retained current state. -/
@[expose] def protectedInset {parameter : Gaussian} {ambient : Purelib.Geometry.Rational.Box} (current :
  SquareRoot.Replay.QuadraticFallbackReplay.State parameter ambient) : SquareRoot.Replay.QuadraticFallbackReplay.Inset
  current :=
  SquareRoot.Clearance.ExactQuadraticOwnerClearance.protectedStrictInset current

/-- A retained option equal to the original checked raw-inset decision for this exact inset. -/
abbrev InsetDecision {parameter : Gaussian} {ambient : Purelib.Geometry.Rational.Box} (current :
  SquareRoot.Replay.QuadraticFallbackReplay.State
  parameter ambient)
    (inset : SquareRoot.Replay.QuadraticFallbackReplay.Inset current) :=
  { value : Option (SquareRoot.Replay.QuadraticFallbackReplay.RawInset current) // value =
    SquareRoot.Clearance.ExactQuadraticOwnerClearance.checkedRawInset? current inset }

/-- The exact canonical inset decision, assembled from a checked winding value. -/
@[expose, irreducible] def checkInset {parameter : Gaussian} {ambient : Purelib.Geometry.Rational.Box} (current :
  SquareRoot.Replay.QuadraticFallbackReplay.State parameter ambient)
    (inset : SquareRoot.Replay.QuadraticFallbackReplay.Inset current)
    (winding : { value : Int // value = Winding.Box.Basic.quadrupledBoxWinding
      (SquareRoot.Clearance.ExactQuadraticOwnerClearance.rootPolynomial parameter)
        (SquareRoot.Clearance.ExactQuadraticOwnerClearance.StrictInsetData.box inset) }) :
    { value : Option (SquareRoot.Replay.QuadraticFallbackReplay.RawInset current) // value =
      SquareRoot.Clearance.ExactQuadraticOwnerClearance.checkedRawInset? current inset } := by
  if left : SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant parameter
    (SquareRoot.Clearance.ExactQuadraticOwnerClearance.StrictInsetData.box inset).xLower ≠ 0 then
    if right : SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant parameter
      (SquareRoot.Clearance.ExactQuadraticOwnerClearance.StrictInsetData.box inset).xUpper ≠ 0 then
      if bottom : SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant parameter
        (SquareRoot.Clearance.ExactQuadraticOwnerClearance.StrictInsetData.box inset).yLower ≠ 0 then
        if top : SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant parameter
          (SquareRoot.Clearance.ExactQuadraticOwnerClearance.StrictInsetData.box inset).yUpper ≠ 0 then
          if four : winding.val = 4 then
            have windingFour := winding.property.symm.trans four
            let value : SquareRoot.Replay.QuadraticFallbackReplay.RawInset current :=
              SquareRoot.Clearance.ExactQuadraticOwnerClearance.StrictRawInset.mk
                ⟨(SquareRoot.Clearance.ExactQuadraticOwnerClearance.StrictInsetData.box inset),
                (Geometry.Rational.Box.Refinement.StrictInterior.refines
                (SquareRoot.Clearance.ExactQuadraticOwnerClearance.StrictInsetData.strict inset)).trans
                current.refinesAmbient, (SquareRoot.Clearance.ExactQuadraticOwnerClearance.StrictInsetData.proper
                inset),
                directBoundaryClearance parameter (SquareRoot.Clearance.ExactQuadraticOwnerClearance.StrictInsetData.box
                  inset) left right bottom top,
                by rw [windingFour]; decide⟩ (SquareRoot.Clearance.ExactQuadraticOwnerClearance.StrictInsetData.strict
                  inset)
            exact ⟨some value, by
              unfold SquareRoot.Clearance.ExactQuadraticOwnerClearance.checkedRawInset?
              dsimp only
              rw [dif_pos left, dif_pos right, dif_pos bottom, dif_pos top, dif_pos windingFour]⟩
          else
            have miss : Winding.Box.Basic.quadrupledBoxWinding
                (SquareRoot.Clearance.ExactQuadraticOwnerClearance.rootPolynomial parameter)
                  (SquareRoot.Clearance.ExactQuadraticOwnerClearance.StrictInsetData.box inset) ≠ 4 := by
              rw [← winding.property]; exact four
            exact ⟨none, by
              unfold SquareRoot.Clearance.ExactQuadraticOwnerClearance.checkedRawInset?
              dsimp only
              rw [dif_pos left, dif_pos right, dif_pos bottom, dif_pos top, dif_neg miss]⟩
        else exact ⟨none, by unfold SquareRoot.Clearance.ExactQuadraticOwnerClearance.checkedRawInset?; dsimp only; rw
          [dif_pos left, dif_pos right, dif_pos bottom, dif_neg top]⟩
      else exact ⟨none, by unfold SquareRoot.Clearance.ExactQuadraticOwnerClearance.checkedRawInset?; dsimp only; rw
        [dif_pos left, dif_pos right, dif_neg bottom]⟩
    else exact ⟨none, by unfold SquareRoot.Clearance.ExactQuadraticOwnerClearance.checkedRawInset?; dsimp only; rw
      [dif_pos left, dif_neg right]⟩
  else exact ⟨none, by unfold SquareRoot.Clearance.ExactQuadraticOwnerClearance.checkedRawInset?; dsimp only; rw
    [dif_neg left]⟩

/-- Read the exact box retained by the original strict-inset data. -/
@[expose] def insetBox {parameter : Gaussian} {ambient : Purelib.Geometry.Rational.Box} {current :
  SquareRoot.Replay.QuadraticFallbackReplay.State
  parameter ambient}
    (inset : SquareRoot.Replay.QuadraticFallbackReplay.Inset current) : Purelib.Geometry.Rational.Box :=
      SquareRoot.Clearance.ExactQuadraticOwnerClearance.StrictInsetData.box inset

/-- Read the exact raw winding state retained by the original checked inset. -/
@[expose] def rawState {parameter : Gaussian} {ambient : Purelib.Geometry.Rational.Box} {current :
  SquareRoot.Replay.QuadraticFallbackReplay.State
  parameter ambient}
    (inset : SquareRoot.Replay.QuadraticFallbackReplay.RawInset current) :=
      SquareRoot.Clearance.ExactQuadraticOwnerClearance.StrictRawInset.state inset

/-- A successful checked inset retains the supplied cached winding as the winding of its exact returned box. -/
theorem checkInset_winding {parameter : Gaussian} {ambient : Purelib.Geometry.Rational.Box} (current :
  SquareRoot.Replay.QuadraticFallbackReplay.State parameter ambient)
    (data : SquareRoot.Replay.QuadraticFallbackReplay.Inset current)
    (winding : { value : Int // value = Winding.Box.Basic.quadrupledBoxWinding
      (SquareRoot.Clearance.ExactQuadraticOwnerClearance.rootPolynomial parameter)
        (SquareRoot.Replay.QuadraticFallbackReplay.insetBox data) })
    (inset : SquareRoot.Replay.QuadraticFallbackReplay.RawInset current) (found :
      (SquareRoot.Replay.QuadraticFallbackReplay.checkInset current data winding).val = some inset) :
    winding.val = Winding.Box.Basic.quadrupledBoxWinding
      (SquareRoot.Clearance.ExactQuadraticOwnerClearance.rootPolynomial parameter)
        (SquareRoot.Replay.QuadraticFallbackReplay.rawState inset).box := by
  unfold SquareRoot.Replay.QuadraticFallbackReplay.checkInset at found
  dsimp only at found
  by_cases left : SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant parameter
    (SquareRoot.Clearance.ExactQuadraticOwnerClearance.StrictInsetData.box data).xLower ≠ 0
  · rw [dif_pos left] at found
    by_cases right : SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant parameter
      (SquareRoot.Clearance.ExactQuadraticOwnerClearance.StrictInsetData.box data).xUpper ≠ 0
    · rw [dif_pos right] at found
      by_cases bottom : SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant parameter
        (SquareRoot.Clearance.ExactQuadraticOwnerClearance.StrictInsetData.box data).yLower ≠ 0
      · rw [dif_pos bottom] at found
        by_cases top : SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant parameter
          (SquareRoot.Clearance.ExactQuadraticOwnerClearance.StrictInsetData.box data).yUpper ≠ 0
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
structure SelectedInset {parameter : Gaussian} {ambient : Purelib.Geometry.Rational.Box} (current :
  SquareRoot.Replay.QuadraticFallbackReplay.State parameter ambient) where
  /-- The exact raw inset returned by the original checked search. -/ value :
    SquareRoot.Replay.QuadraticFallbackReplay.RawInset current
  /-- The original inset search returns this retained inset. -/ equation :
    SquareRoot.Clearance.ExactQuadraticOwnerClearance.strictRawInset? current = some value
  /-- The cached quadrupled winding of the retained inset box. -/ winding : Int
  /-- The cached winding equals the original polynomial's winding on this exact retained box. -/ winding_eq : winding =
    Winding.Box.Basic.quadrupledBoxWinding
    (SquareRoot.Clearance.ExactQuadraticOwnerClearance.rootPolynomial parameter)
      (SquareRoot.Replay.QuadraticFallbackReplay.rawState value).box

constructive_injectivity SelectedInset

/-- A retained option equal to the original fixed-then-protected inset search result. -/
abbrev InsetAttempt {parameter : Gaussian} {ambient : Purelib.Geometry.Rational.Box} (current :
  SquareRoot.Replay.QuadraticFallbackReplay.State
  parameter ambient) :=
  { value : Option (SquareRoot.Replay.QuadraticFallbackReplay.RawInset current) //
    SquareRoot.Clearance.ExactQuadraticOwnerClearance.strictRawInset? current = value }

/-- Reconstruct the original failed inset search from failures of both retained inset checks. -/
@[expose] def missingInsets {parameter : Gaussian} {ambient : Purelib.Geometry.Rational.Box} (current :
  SquareRoot.Replay.QuadraticFallbackReplay.State parameter ambient)
    (fixed : SquareRoot.Replay.QuadraticFallbackReplay.InsetDecision current
      (SquareRoot.Replay.QuadraticFallbackReplay.fixedInset current)) (fixedMiss : fixed.val = none)
    (narrow : SquareRoot.Replay.QuadraticFallbackReplay.InsetDecision current
      (SquareRoot.Replay.QuadraticFallbackReplay.protectedInset current)) (narrowMiss : narrow.val = none) :
    SquareRoot.Replay.QuadraticFallbackReplay.InsetAttempt current :=
  ⟨none, by
    unfold SquareRoot.Clearance.ExactQuadraticOwnerClearance.strictRawInset?
    change (match SquareRoot.Clearance.ExactQuadraticOwnerClearance.checkedRawInset? current
      (SquareRoot.Replay.QuadraticFallbackReplay.fixedInset current) with
      | some value => some value
      | none => SquareRoot.Clearance.ExactQuadraticOwnerClearance.checkedRawInset? current
        (SquareRoot.Replay.QuadraticFallbackReplay.protectedInset current)) = none
    rw [← fixed.property, fixedMiss]
    exact narrow.property.symm.trans narrowMiss⟩

/-- A successful fixed-inset check is the exact result of the original inset search. -/
theorem firstInset {parameter : Gaussian} {ambient : Purelib.Geometry.Rational.Box} (current :
  SquareRoot.Replay.QuadraticFallbackReplay.State
  parameter ambient)
    (fixed : { value : Option (SquareRoot.Replay.QuadraticFallbackReplay.RawInset current) // value =
      SquareRoot.Clearance.ExactQuadraticOwnerClearance.checkedRawInset? current
      (SquareRoot.Replay.QuadraticFallbackReplay.fixedInset current) })
    (inset : SquareRoot.Replay.QuadraticFallbackReplay.RawInset current) (found : fixed.val = some inset) :
    SquareRoot.Clearance.ExactQuadraticOwnerClearance.strictRawInset? current = some inset := by
  unfold SquareRoot.Clearance.ExactQuadraticOwnerClearance.strictRawInset?
  change (match SquareRoot.Clearance.ExactQuadraticOwnerClearance.checkedRawInset? current
    (SquareRoot.Replay.QuadraticFallbackReplay.fixedInset current) with
    | some value => some value
    | none => SquareRoot.Clearance.ExactQuadraticOwnerClearance.checkedRawInset? current
      (SquareRoot.Replay.QuadraticFallbackReplay.protectedInset current)) = _
  rw [← fixed.property, found]

/-- After the fixed-inset check fails, the original search returns the retained protected-inset decision exactly. -/
theorem secondInset {parameter : Gaussian} {ambient : Purelib.Geometry.Rational.Box} (current :
  SquareRoot.Replay.QuadraticFallbackReplay.State
  parameter ambient)
    (fixed : { value : Option (SquareRoot.Replay.QuadraticFallbackReplay.RawInset current) // value =
      SquareRoot.Clearance.ExactQuadraticOwnerClearance.checkedRawInset? current
      (SquareRoot.Replay.QuadraticFallbackReplay.fixedInset current) })
    (missed : fixed.val = none)
    (narrow : { value : Option (SquareRoot.Replay.QuadraticFallbackReplay.RawInset current) // value =
      SquareRoot.Clearance.ExactQuadraticOwnerClearance.checkedRawInset? current
      (SquareRoot.Replay.QuadraticFallbackReplay.protectedInset current) }) :
    SquareRoot.Clearance.ExactQuadraticOwnerClearance.strictRawInset? current = narrow.val := by
  unfold SquareRoot.Clearance.ExactQuadraticOwnerClearance.strictRawInset?
  change (match SquareRoot.Clearance.ExactQuadraticOwnerClearance.checkedRawInset? current
    (SquareRoot.Replay.QuadraticFallbackReplay.fixedInset current) with
    | some value => some value
    | none => SquareRoot.Clearance.ExactQuadraticOwnerClearance.checkedRawInset? current
      (SquareRoot.Replay.QuadraticFallbackReplay.protectedInset current)) = _
  rw [← fixed.property, missed]
  exact narrow.property.symm

/-- The original certified fast refinement of the current quadratic state at the supplied accuracy. -/
abbrev Fast {parameter : Gaussian} {ambient : Purelib.Geometry.Rational.Box} (current :
  SquareRoot.Replay.QuadraticFallbackReplay.State parameter
  ambient) (epsilon : Coordinate) :=
  SquareRoot.Clearance.ExactQuadraticOwnerClearance.FastRefinement current epsilon

/-- Read the exact next winding-one state retained by a successful fast refinement. -/
@[expose] def fastState {parameter : Gaussian} {ambient : Purelib.Geometry.Rational.Box} {current :
  SquareRoot.Replay.QuadraticFallbackReplay.State parameter ambient} {epsilon : Coordinate}
    (fast : SquareRoot.Replay.QuadraticFallbackReplay.Fast current epsilon) :
      SquareRoot.Replay.QuadraticFallbackReplay.State parameter ambient :=
      SquareRoot.Clearance.ExactQuadraticOwnerClearance.FastRefinement.state fast

/-- The inset's checked winding is reused when promoting it to a full state. -/
@[expose, irreducible] def promote {parameter : Gaussian} {ambient : Purelib.Geometry.Rational.Box} (current :
  SquareRoot.Replay.QuadraticFallbackReplay.State parameter ambient)
    (epsilon : Coordinate) (inset : SquareRoot.Replay.QuadraticFallbackReplay.RawInset current)
    (accurate : (SquareRoot.Replay.QuadraticFallbackReplay.rawState inset).box.diagonalSq ≤ epsilon ^ 2)
    (winding : { value : Int // value = Winding.Box.Basic.quadrupledBoxWinding
      (SquareRoot.Clearance.ExactQuadraticOwnerClearance.rootPolynomial parameter)
        (SquareRoot.Replay.QuadraticFallbackReplay.rawState inset).box }) :
    { value : Option (SquareRoot.Replay.QuadraticFallbackReplay.Fast current epsilon) // value =
      SquareRoot.Clearance.ExactQuadraticOwnerClearance.checkedFastRefinement? current epsilon
      (SquareRoot.Replay.QuadraticFallbackReplay.rawState inset)
        (SquareRoot.Clearance.ExactQuadraticOwnerClearance.StrictRawInset.strict inset) accurate } := by
  let candidate := SquareRoot.Replay.QuadraticFallbackReplay.rawState inset
  if left : SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant parameter candidate.box.xLower ≠ 0 then
    if right : SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant parameter candidate.box.xUpper ≠ 0 then
      if bottom : SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant parameter candidate.box.yLower ≠ 0
        then
        if top : SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant parameter candidate.box.yUpper ≠ 0
          then
          if four : winding.val = 4 then
            have windingFour := winding.property.symm.trans four
            let state : SquareRoot.Replay.QuadraticFallbackReplay.State parameter ambient :=
              ⟨candidate.box, candidate.refinesAmbient, candidate.proper,
                directBoundaryClearance parameter candidate.box left right bottom top, windingFour,
                SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directVerticalClearance
                  parameter ambient candidate.box.xLower left,
                SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directVerticalClearance
                  parameter ambient candidate.box.xUpper right,
                SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directHorizontalClearance
                  parameter ambient candidate.box.yLower bottom,
                SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directHorizontalClearance
                  parameter ambient candidate.box.yUpper top⟩
            let value : SquareRoot.Replay.QuadraticFallbackReplay.Fast current epsilon :=
              SquareRoot.Clearance.ExactQuadraticOwnerClearance.FastRefinement.mk state
              (Geometry.Rational.Box.Refinement.StrictInterior.refines
                (SquareRoot.Clearance.ExactQuadraticOwnerClearance.StrictRawInset.strict inset))
                (SquareRoot.Clearance.ExactQuadraticOwnerClearance.StrictRawInset.strict inset) accurate
            exact ⟨some value, by
              unfold SquareRoot.Clearance.ExactQuadraticOwnerClearance.checkedFastRefinement?
              rw [dif_pos left, dif_pos right, dif_pos bottom, dif_pos top, dif_pos windingFour]⟩
          else
            have miss : Winding.Box.Basic.quadrupledBoxWinding
                (SquareRoot.Clearance.ExactQuadraticOwnerClearance.rootPolynomial parameter) candidate.box ≠ 4 := by
              rw [← winding.property]; exact four
            exact ⟨none, by
              unfold SquareRoot.Clearance.ExactQuadraticOwnerClearance.checkedFastRefinement?
              rw [dif_pos left, dif_pos right, dif_pos bottom, dif_pos top, dif_neg miss]⟩
        else exact ⟨none, by unfold SquareRoot.Clearance.ExactQuadraticOwnerClearance.checkedFastRefinement?; rw
          [dif_pos left, dif_pos right, dif_pos bottom, dif_neg top]⟩
      else exact ⟨none, by unfold SquareRoot.Clearance.ExactQuadraticOwnerClearance.checkedFastRefinement?; rw [dif_pos
        left, dif_pos right, dif_neg bottom]⟩
    else exact ⟨none, by unfold SquareRoot.Clearance.ExactQuadraticOwnerClearance.checkedFastRefinement?; rw [dif_pos
      left, dif_neg right]⟩
  else exact ⟨none, by unfold SquareRoot.Clearance.ExactQuadraticOwnerClearance.checkedFastRefinement?; rw [dif_neg
    left]⟩

/-- Run the original quadratic subdivision fallback at the supplied positive accuracy. -/
@[expose] def subdivision {parameter : Gaussian} {ambient : Purelib.Geometry.Rational.Box} (current :
  SquareRoot.Replay.QuadraticFallbackReplay.State parameter ambient)
    (epsilon : Coordinate) (positive : 0 < epsilon) :=
      SquareRoot.Clearance.ExactQuadraticOwnerClearance.subdivisionRefinement? current epsilon positive

/-- Continue the original fallback from an accurate raw candidate.

Check it directly when strictly inside the current box; otherwise use the retained original inset search and
subdivision. -/
private def afterRaw {parameter : Gaussian} {ambient : Purelib.Geometry.Rational.Box} (current :
  SquareRoot.Replay.QuadraticFallbackReplay.State
  parameter ambient)
    (epsilon : Coordinate) (positive : 0 < epsilon)
    (candidate : State.Raw.RawWindingState (SquareRoot.Clearance.ExactQuadraticOwnerClearance.rootPolynomial parameter)
      ambient)
    (accurate : candidate.box.diagonalSq ≤ epsilon ^ 2) : Option (SquareRoot.Replay.QuadraticFallbackReplay.Fast current
      epsilon) :=
  open Purelib.Data.Rat in if strict : candidate.box.StrictInterior current.box then
    SquareRoot.Clearance.ExactQuadraticOwnerClearance.checkedFastRefinement? current epsilon candidate strict accurate
  else
    match SquareRoot.Clearance.ExactQuadraticOwnerClearance.strictRawInset? current with
    | none => none
    | some inset =>
      let next := Subdivision.Raw.Request.refineTo (p :=
        SquareRoot.Clearance.ExactQuadraticOwnerClearance.rootPolynomial parameter)
        (SquareRoot.Clearance.QuadraticAxisElimination.quadraticAxisElimination parameter)
          (SquareRoot.Replay.QuadraticFallbackReplay.rawState inset) (epsilon ^ 2)
      SquareRoot.Clearance.ExactQuadraticOwnerClearance.checkedFastRefinement? current epsilon next
        (Geometry.Rational.Box.Refinement.StrictInterior.of_refines
          (SquareRoot.Clearance.ExactQuadraticOwnerClearance.StrictRawInset.strict inset)
          (Subdivision.Raw.Request.refineTo_refines _ _ _))
        (Subdivision.Raw.Request.refineTo_diagonalSq_le _ _
          (Fraction.Order.Arithmetic.pow_pos_direct positive 2))

/-- Equal raw candidates yield the same continuation of the original fallback. -/
private theorem afterRaw_congr {parameter : Gaussian} {ambient : Purelib.Geometry.Rational.Box} (current :
  SquareRoot.Replay.QuadraticFallbackReplay.State parameter ambient)
    (epsilon : Coordinate) (positive : 0 < epsilon)
    (first second : State.Raw.RawWindingState (SquareRoot.Clearance.ExactQuadraticOwnerClearance.rootPolynomial
      parameter) ambient)
    (firstAccurate : first.box.diagonalSq ≤ epsilon ^ 2) (secondAccurate : second.box.diagonalSq ≤ epsilon ^ 2)
    (same : first = second) : SquareRoot.Replay.QuadraticFallbackReplay.afterRaw current epsilon positive first
      firstAccurate =
      SquareRoot.Replay.QuadraticFallbackReplay.afterRaw current epsilon positive second secondAccurate := by
  cases same
  rfl

/-- Equal raw candidates yield the same original checked fast-refinement option. -/
private theorem checkedFast_congr {parameter : Gaussian} {ambient : Purelib.Geometry.Rational.Box} (current :
  SquareRoot.Replay.QuadraticFallbackReplay.State parameter ambient)
    (epsilon : Coordinate)
    (first second : State.Raw.RawWindingState (SquareRoot.Clearance.ExactQuadraticOwnerClearance.rootPolynomial
      parameter) ambient)
    (firstStrict : first.box.StrictInterior current.box) (secondStrict : second.box.StrictInterior current.box)
    (firstAccurate : first.box.diagonalSq ≤ epsilon ^ 2) (secondAccurate : second.box.diagonalSq ≤ epsilon ^ 2)
    (same : first = second) : SquareRoot.Clearance.ExactQuadraticOwnerClearance.checkedFastRefinement? current epsilon
      first firstStrict firstAccurate =
      SquareRoot.Clearance.ExactQuadraticOwnerClearance.checkedFastRefinement? current epsilon second secondStrict
        secondAccurate := by
  cases same
  rfl

/-- A raw subdivision request of depth zero returns the supplied raw state unchanged. -/
private theorem refineTo_zero {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {ambient : Purelib.Geometry.Rational.Box} {degree :
  Nat}
    (elimination : Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degree)
    (state : State.Raw.RawWindingState p ambient) (threshold : Coordinate)
    (zero : Subdivision.Raw.Request.refinementDepth state threshold = 0) :
    Subdivision.Raw.Request.refineTo elimination state threshold = state := by
  unfold Subdivision.Raw.Request.refineTo
  rw [zero]
  rfl

/-- A zero-depth subdivision request already satisfies the supplied squared accuracy. -/
theorem zero_accurate {parameter : Gaussian} {ambient : Purelib.Geometry.Rational.Box}
    (state : State.Raw.RawWindingState (SquareRoot.Clearance.ExactQuadraticOwnerClearance.rootPolynomial parameter)
      ambient)
    (epsilon : Coordinate) (positive : 0 < epsilon)
    (zero : Subdivision.Raw.Request.refinementDepth state (epsilon ^ 2) = 0) : state.box.diagonalSq ≤ epsilon ^ 2 :=
      open Purelib.Data.Rat in by
  let elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate
      (SquareRoot.Clearance.ExactQuadraticOwnerClearance.rootPolynomial parameter) 4 :=
        SquareRoot.Clearance.QuadraticAxisElimination.quadraticAxisElimination parameter
  have accurate := Subdivision.Raw.Request.refineTo_diagonalSq_le elimination state
    (Fraction.Order.Arithmetic.pow_pos_direct positive 2)
  rw [SquareRoot.Replay.QuadraticFallbackReplay.refineTo_zero elimination state (epsilon ^ 2) zero] at accurate
  exact accurate

/-- When both subdivision depths are zero, the original fallback is exactly the checked refinement of the retained
inset. -/
theorem subdivision_zero {parameter : Gaussian} {ambient : Purelib.Geometry.Rational.Box} (current :
  SquareRoot.Replay.QuadraticFallbackReplay.State parameter ambient)
    (epsilon : Coordinate) (positive : 0 < epsilon)
    (initialDepth : Subdivision.Raw.Request.refinementDepth current.raw (epsilon ^ 2) = 0)
    (inset : SquareRoot.Replay.QuadraticFallbackReplay.RawInset current) (found :
      SquareRoot.Clearance.ExactQuadraticOwnerClearance.strictRawInset? current = some inset)
    (insetDepth : Subdivision.Raw.Request.refinementDepth (SquareRoot.Replay.QuadraticFallbackReplay.rawState inset)
      (epsilon ^ 2) = 0)
    (accurate : (SquareRoot.Replay.QuadraticFallbackReplay.rawState inset).box.diagonalSq ≤ epsilon ^ 2) :
    SquareRoot.Replay.QuadraticFallbackReplay.subdivision current epsilon positive =
      SquareRoot.Clearance.ExactQuadraticOwnerClearance.checkedFastRefinement? current epsilon
      (SquareRoot.Replay.QuadraticFallbackReplay.rawState inset)
        (SquareRoot.Clearance.ExactQuadraticOwnerClearance.StrictRawInset.strict inset) accurate := open
        Purelib.Data.Rat in by
  let elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate
      (SquareRoot.Clearance.ExactQuadraticOwnerClearance.rootPolynomial parameter) 4 :=
        SquareRoot.Clearance.QuadraticAxisElimination.quadraticAxisElimination parameter
  have first := SquareRoot.Replay.QuadraticFallbackReplay.refineTo_zero elimination current.raw (epsilon ^ 2)
    initialDepth
  have firstAccurate := Subdivision.Raw.Request.refineTo_diagonalSq_le elimination current.raw
    (Fraction.Order.Arithmetic.pow_pos_direct positive 2)
  have currentAccurate : current.raw.box.diagonalSq ≤ epsilon ^ 2 := by
    rw [first] at firstAccurate
    exact firstAccurate
  have step : SquareRoot.Replay.QuadraticFallbackReplay.subdivision current epsilon positive =
    SquareRoot.Replay.QuadraticFallbackReplay.afterRaw current epsilon positive current.raw currentAccurate :=
    SquareRoot.Replay.QuadraticFallbackReplay.afterRaw_congr current epsilon positive _ _ firstAccurate currentAccurate
      first
  rw [step]
  have notStrict : ¬ current.raw.box.StrictInterior current.box := by
    intro strict
    exact (lt_irrefl current.box.xLower) strict.1
  unfold SquareRoot.Replay.QuadraticFallbackReplay.afterRaw
  rw [dif_neg notStrict, found]
  exact SquareRoot.Replay.QuadraticFallbackReplay.checkedFast_congr current epsilon _ _ _ _ _ _
    (SquareRoot.Replay.QuadraticFallbackReplay.refineTo_zero elimination
      (SquareRoot.Replay.QuadraticFallbackReplay.rawState inset) (epsilon ^ 2) insetDepth)

/-- After the first attempt fails, a successful original subdivision determines the deferred track's next state exactly.
-/
theorem deferred_refine {parameter : Gaussian} {ambient : Purelib.Geometry.Rational.Box} (nonzero : parameter ≠ 0)
    (initial current : SquareRoot.Replay.QuadraticFallbackReplay.State parameter ambient) (epsilon : Coordinate)
      (positive : 0 < epsilon)
    (missed : SquareRoot.Replay.QuadraticSampleReplay.attempt current epsilon = none)
    (accepted : SquareRoot.Replay.QuadraticFallbackReplay.Fast current epsilon) (found :
      SquareRoot.Replay.QuadraticFallbackReplay.subdivision current epsilon positive = some accepted) :
    (QuadraticSampleReplay.Recipe.deferred.track nonzero initial).refine current epsilon positive =
      SquareRoot.Replay.QuadraticFallbackReplay.fastState accepted := by
  change SquareRoot.Clearance.ExactQuadraticOwnerClearance.deferredRefine nonzero current epsilon positive = _
  unfold SquareRoot.Clearance.ExactQuadraticOwnerClearance.deferredRefine
  unfold SquareRoot.Clearance.ExactQuadraticOwnerClearance.fastRefinement?
  with_unfolding_all erw [show Newton.Search.Attempt.attempt
    (SquareRoot.Clearance.QuadraticAxisElimination.quadraticAxisElimination parameter)
    current.raw epsilon (SquareRoot.Clearance.QuadraticLineClearance.Owner.quadraticAxisClearances parameter) = none
      from missed]
  with_unfolding_all erw [show SquareRoot.Clearance.ExactQuadraticOwnerClearance.subdivisionRefinement? current epsilon
    positive = some accepted from found]
  rfl

/-- Available original-source evidence. A checked-first law alone does not
identify the later fallback of an arbitrary inherited track. -/
inductive Plan {parameter : Gaussian} {ambient : Purelib.Geometry.Rational.Box} (track :
  SquareRoot.Replay.QuadraticTrackReplay.Track parameter
  ambient) where
  /-- Only the successful first-attempt law is retained; no later fallback identity is supplied. -/ | checkedFirstOnly
  /-- The retained track's total refinement function equals the original deferred recipe at every state and positive
    request. -/ | deferred (nonzero : parameter ≠ 0)
      (equation : ∀ (current : SquareRoot.Replay.QuadraticFallbackReplay.State parameter ambient) (epsilon : Coordinate)
        (positive : 0 < epsilon),
        track.refine current epsilon positive =
          (QuadraticSampleReplay.Recipe.deferred.track nonzero track.initial).refine current epsilon positive)

/-- Retain the original deferred fallback equation from a matching deferred owner recipe. -/
@[expose] def Plan.ofDeferred {parameter : Gaussian} (owner : Owner parameter)
    (same : QuadraticSampleReplay.Recipe.deferred.Matches owner) : SquareRoot.Replay.QuadraticFallbackReplay.Plan
      owner.track :=
  .deferred owner.parameterNonzero (by
    intro current epsilon positive
    have refine := congrArg (fun track => track.refine current epsilon positive) same
    exact refine.symm)

end Purelib.RootIsolation.SquareRoot.Replay.QuadraticFallbackReplay

end
