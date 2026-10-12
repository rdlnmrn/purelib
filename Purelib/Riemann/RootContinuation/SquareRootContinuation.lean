module
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Power.Gaussian
public import Purelib.Polynomial.Power.Gaussian.Squarefree
import Purelib.RootIsolation.Owner.Local.Basic
public import Purelib.RootIsolation.Progressive.Power.Owner.Transport
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
public import Purelib.RootIsolation.Newton.Search.Extraction
import Purelib.RootIsolation.State.Raw
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic
public import Purelib.RootIsolation.Track.Newton.Build

import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticAxisElimination
public import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticLineClearance

/-!
# Finite continuation of a square-root owner across one rational move

The specialized power-monodromy API rebases through equal-norm global
squares.  A general algebraic path does not preserve the norm of its
radicand.  For one sufficiently small rational move we instead enlarge the
ambient box by a finite coordinatewise hull, carry the old owner by Rouché,
and try exactly checked Newton bands in that hull.  Rejected proposals retain
the total eliminant-driven extractor as fallback.  Both the initial extraction
and later track steps use the shared short quadratic resultants.  This yields
a fresh globally supported target track without an equal-norm hypothesis.
-/

namespace Purelib.Riemann.RootContinuation.SquareRootContinuation

open Purelib.Data.Rat

section

open Purelib.Data

/-- The rational coordinate type for finite continuation bounds. -/
public abbrev Coordinate := Rat.Fraction.Rational
/-- The executable Gaussian rational parameter type. -/
public abbrev Gaussian := Gaussian.Basic.Canonical

end

open Purelib.Geometry in
/-- The rational axis-aligned box type for retained root owners. -/
public abbrev Box := Rational.Box
section

open Purelib.RootIsolation

/-- A certified winding-one state indexed by its polynomial and ambient box. -/
public abbrev WindingOneState := State.WindingOne.Basic.WindingOneState
/-- The deterministic refinement track for a retained winding-one state. -/
public abbrev WindingOneTrack := Track.Basic.WindingOneTrack

end

/-- The smallest coordinatewise rational box containing both supplied boxes.

The four coordinate extrema retain both original input boxes. Their
original validity inequalities certify the computed minima and maxima. -/
@[expose] public def hull (left right : Box) : Box where
  xLower := min left.xLower right.xLower
  xUpper := max left.xUpper right.xUpper
  yLower := min left.yLower right.yLower
  yUpper := max left.yUpper right.yUpper
  x_valid := (Fraction.Order.Basic.min_le_left _ _).trans
    (left.x_valid.trans (Fraction.Order.Basic.le_max_left _ _))
  y_valid := (Fraction.Order.Basic.min_le_left _ _).trans
    (left.y_valid.trans (Fraction.Order.Basic.le_max_left _ _))

/-- The left input box refines the retained coordinatewise hull.

The original left coordinates lie between the retained minima and maxima
that define the same common hull. No input box or coordinate is replaced. -/
public theorem left_refines_hull (left right : Box) : left.Refines (hull left right) :=
  ⟨Fraction.Order.Basic.min_le_left _ _, Fraction.Order.Basic.le_max_left _ _, Fraction.Order.Basic.min_le_left _ _,
    Fraction.Order.Basic.le_max_left _ _⟩

/-- The right input box refines the retained coordinatewise hull.

The original right coordinates lie between the retained minima and maxima
that define the same common hull, with both original validity bounds retained. -/
public theorem right_refines_hull (left right : Box) :
    right.Refines (hull left right) :=
  ⟨Fraction.Order.Basic.min_le_right _ _, Fraction.Order.Basic.le_max_right _ _, Fraction.Order.Basic.min_le_right _ _,
    Fraction.Order.Basic.le_max_right _ _⟩

open Purelib.Riemann in
open Purelib.Polynomial in
/-- The finite hull of the source ambient box and the target polynomial's computed global square.

Both original source and computed target boxes determine the four retained extrema. The hull preserves their coordinate
bounds for the same source state and target polynomial. -/
@[expose] public def commonAmbient {source : Gaussian} {ambient : Box}
    (_sourceState : WindingOneState
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial source
        RootContinuation.SquareRootDegree.degreeTwo) ambient)
    (target : Gaussian) : Box :=
  hull ambient
    (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial target
        RootContinuation.SquareRootDegree.degreeTwo))

section

open Purelib.Riemann
open Purelib.Data
open Purelib.Polynomial
open Purelib.RootIsolation

/-- Transport the local square-root owner across one certified small radicand move.

The parameter displacement quadrance is below the source state's retained clearance bound, so finite Rouché transport
preserves the local root occurrence. -/
@[expose] public def transportedOwner {source target : Gaussian} {ambient : Box}
    (sourceState : WindingOneState
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial source
        RootContinuation.SquareRootDegree.degreeTwo) ambient)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) <
      sourceState.clearance.bound) :
    Owner.Local.Basic.LocalOwner
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial target
        RootContinuation.SquareRootDegree.degreeTwo) :=
  Progressive.Power.Owner.Transport.transportedOwner
    RootContinuation.SquareRootDegree.degreeTwo
    { box := sourceState.box
      proper := sourceState.proper
      clearance := sourceState.clearance
      rawWindingFour := sourceState.rawWindingFour }
    small

/-- Retain the transported target owner as a raw state in the common finite hull.

Its actual box is the source box, while the hull containment and retained winding certify the target-polynomial state.
-/
@[expose] public def transportedRawState {source target : Gaussian} {ambient : Box}
    (sourceState : WindingOneState
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial source
        RootContinuation.SquareRootDegree.degreeTwo) ambient)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) <
      sourceState.clearance.bound) :
    State.Raw.RawWindingState
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial target
        RootContinuation.SquareRootDegree.degreeTwo)
      (commonAmbient sourceState target) := by
  let owner := transportedOwner sourceState small
  exact
    { box := owner.box
      refinesAmbient := by
        change sourceState.box.Refines (hull ambient
          (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox
            (Purelib.Polynomial.Power.Gaussian.rootPolynomial target
              RootContinuation.SquareRootDegree.degreeTwo)))
        exact sourceState.refinesAmbient.trans
          (left_refines_hull ambient _)
      proper := owner.proper
      clearance := owner.clearance
      rawWinding_ne := by
        intro zero
        have fourZero : (4 : Int) = 0 := by
          rw [← owner.rawWindingFour]
          exact zero
        exact (by decide : (4 : Int) ≠ 0) fourZero }

end

section
open Purelib.Riemann
open Purelib.Data
open Purelib.Polynomial
/-- The transported raw target state retains the source state's exact box. -/
@[simp] public theorem transportedRawState_box {source target : Gaussian}
    {ambient : Box}
    (sourceState : WindingOneState
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial source
        RootContinuation.SquareRootDegree.degreeTwo) ambient)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) <
      sourceState.clearance.bound) :
    (transportedRawState sourceState small).box = sourceState.box := rfl

open Purelib.RootIsolation in
/-- Extract a fresh target-polynomial Newton band inside the transported local owner.

The nonzero target supplies squarefreeness; checked quadratic axis elimination and clearances provide the retained
finite extraction data and fallback. -/
@[expose] public def extraction {source target : Gaussian} {ambient : Box}
    (targetNonzero : target ≠ 0)
    (sourceState : WindingOneState
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial source
        RootContinuation.SquareRootDegree.degreeTwo) ambient)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) <
      sourceState.clearance.bound) :=
  Newton.Search.Extraction.extract
    (by
      rw [Purelib.Polynomial.Power.Gaussian.rootPolynomial_degree]
      exact RootContinuation.SquareRootDegree.degreeTwo_atLeastTwo)
    (Power.Gaussian.Squarefree.squarefree targetNonzero
      RootContinuation.SquareRootDegree.degreeTwo)
    (SquareRoot.Clearance.QuadraticAxisElimination.quadraticAxisElimination target)
    (transportedRawState sourceState small) (epsilon := (1 : Coordinate))
    (by decide)
    (SquareRoot.Clearance.QuadraticLineClearance.Owner.quadraticAxisClearances target)

/-- Read the freshly extracted globally line-cleared target state in the common finite hull.

The exact checked extractor result retains the target polynomial, shared common hull and transported original local
owner. Reading its state preserves those same witnesses and clearances. -/
@[expose] public def continuedState {source target : Gaussian} {ambient : Box}
    (targetNonzero : target ≠ 0)
    (sourceState : WindingOneState
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial source
        RootContinuation.SquareRootDegree.degreeTwo) ambient)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) <
      sourceState.clearance.bound) :
    WindingOneState
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial target
        RootContinuation.SquareRootDegree.degreeTwo)
      (commonAmbient sourceState target) :=
  (extraction targetNonzero sourceState small).state

open Purelib.Geometry in
/-- The freshly continued target state's box refines the original source box.

The exact extraction certificate gives strict containment in the transported owner box. That box is the original source
box, so the retained target state refines it. -/
public theorem continuedState_refines_source {source target : Gaussian}
    {ambient : Box} (targetNonzero : target ≠ 0)
    (sourceState : WindingOneState
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial source
        RootContinuation.SquareRootDegree.degreeTwo) ambient)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) <
      sourceState.clearance.bound) :
    (continuedState targetNonzero sourceState small).box.Refines
      sourceState.box := by
  change (extraction targetNonzero sourceState small).state.box.Refines sourceState.box
  rw [← transportedRawState_box sourceState small]
  exact (Geometry.Rational.Box.Refinement.StrictInterior.refines (extraction targetNonzero sourceState small).strict)

open Purelib.RootIsolation in
/-- Build the deterministic shrinking target track after a certified small parameter move.

The extracted initial state retains the common hull, and the same checked quadratic accelerator governs later
refinements. -/
@[expose] public def continuedTrack {source target : Gaussian} {ambient : Box}
    (targetNonzero : target ≠ 0)
    (sourceState : WindingOneState
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial source
        RootContinuation.SquareRootDegree.degreeTwo) ambient)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) <
      sourceState.clearance.bound) :
    WindingOneTrack
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial target
        RootContinuation.SquareRootDegree.degreeTwo)
      (commonAmbient sourceState target) :=
  SquareRoot.Clearance.QuadraticLineClearance.Owner.accelerateTrack target
  (Track.Newton.Build.ofInitial
    (by
      rw [Purelib.Polynomial.Power.Gaussian.rootPolynomial_degree]
      exact RootContinuation.SquareRootDegree.degreeTwo_atLeastTwo)
    (Power.Gaussian.Squarefree.squarefree targetNonzero
      RootContinuation.SquareRootDegree.degreeTwo)
    (SquareRoot.Clearance.QuadraticAxisElimination.quadraticAxisElimination target)
    (continuedState targetNonzero sourceState small))

end

section

open Purelib.Riemann
open Purelib.Data
open Purelib.Polynomial

/-- The continued track's initial box refines the original source box.

The continued track retains the exact freshly extracted initial state. Its original extraction certificate gives
containment in the same source box. -/
public theorem continuedTrack_initial_refines_source {source target : Gaussian}
    {ambient : Box} (targetNonzero : target ≠ 0)
    (sourceState : WindingOneState
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial source
        RootContinuation.SquareRootDegree.degreeTwo) ambient)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) <
      sourceState.clearance.bound) :
    (continuedTrack targetNonzero sourceState small).initial.box.Refines
      sourceState.box :=
  continuedState_refines_source targetNonzero sourceState small

/-- The continued track's initial box lies strictly inside the original source box.

The retained continued initial state is the exact checked extraction result. Its original strict-containment certificate
refers to the same transported source box. -/
public theorem continuedTrack_initial_strict_source {source target : Gaussian}
    {ambient : Box} (targetNonzero : target ≠ 0)
    (sourceState : WindingOneState
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial source
        RootContinuation.SquareRootDegree.degreeTwo) ambient)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) <
      sourceState.clearance.bound) :
    (continuedTrack targetNonzero sourceState small).initial.box.StrictInterior
      sourceState.box := by
  change (extraction targetNonzero sourceState small).state.box.StrictInterior
    sourceState.box
  rw [← transportedRawState_box sourceState small]
  exact (extraction targetNonzero sourceState small).strict

end

end Purelib.Riemann.RootContinuation.SquareRootContinuation
