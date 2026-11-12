module

public import Purelib.RootIsolation.Power.Unit.Source
import Purelib.RootIsolation.Power.Isolation
import Purelib.RootIsolation.Power.Isolation.Track
import Purelib.RootIsolation.Exact.Canonical
import Purelib.RootIsolation.Track.Newton.Canonical
public import Purelib.RootIsolation.FTA.Squarefree.Prepare
public import Purelib.RootIsolation.Track.Newton.Refinement

/-! # Exact original source-state preparation for robust unit-power owners -/

public section

namespace Purelib.RootIsolation.Power.Unit.Source.Preparation

open Purelib
open Purelib.Data
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Nat.Positive (RootDegree)
open Purelib.Polynomial
open Purelib.RootIsolation

/-- The original ambient-indexed winding-one state of the unit-power family. -/
abbrev State (parameter : Canonical) (degree : RootDegree) :=
  RootIsolation.State.WindingOne.Basic.WindingOneState (Power.Gaussian.rootPolynomial parameter degree)
    (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (Power.Gaussian.rootPolynomial parameter degree))

/-- A cached state equal to the original robust-source refinement at one original owner index. -/
abbrev Prepared {parameter : Canonical} (nonzero : parameter ≠ 0) (unit : normSq parameter = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value) (index : Fin degree.value) :=
  { value : State parameter degree // value = unitRobustSourceState nonzero unit degree degreeTwo index }

/-- An original isolated power track uses its original canonical Newton refinement.

The retained degree index selects a member of the original large-square track
list. Its canonical refinement law uses that same input's squarefree and axis
elimination certificates for every supplied state and positive request. -/
theorem refine_eq {parameter : Canonical} (nonzero : parameter ≠ 0)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value) (index : Fin degree.value)
    (current : State parameter degree) (epsilon : Rat.Fraction.Rational) (positive : 0 < epsilon) :
    (Isolation.Track.isolatedTrack nonzero degree degreeTwo index).refine current epsilon positive =
      Track.Newton.Refinement.refineState
        (Isolation.isolationInput nonzero degree degreeTwo).degreeAtLeastTwo
        (Isolation.isolationInput nonzero degree degreeTwo).squarefree
        (Isolation.isolationInput nonzero degree degreeTwo).elimination current epsilon positive := by
  let input := Isolation.isolationInput nonzero degree degreeTwo
  have original := Exact.Canonical.trackAt input.degreeAtLeastTwo input.squarefree input.elimination
    (Exact.LargeSquare.isolateLargeSquare input.degreeAtLeastTwo input.squarefree input.elimination)
    (Exact.Canonical.largeSquare input.degreeAtLeastTwo input.squarefree input.elimination)
    (Fin.cast (Power.Gaussian.rootPolynomial_degree parameter degree).symm index)
  exact original current epsilon positive

/-- Attach an exact saved canonical refinement to its original robust-source request.

The accuracy remains the original unit source radius and the current state is
the original isolated track's initial state. The retained full-state equality
permits reuse without evaluating the canonical refinement again. -/
@[expose] def ofRefinement {parameter : Canonical} (nonzero : parameter ≠ 0) (unit : normSq parameter = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value) (index : Fin degree.value)
    (saved : { value : State parameter degree // value =
      Track.Newton.Refinement.refineState
        (Isolation.isolationInput nonzero degree degreeTwo).degreeAtLeastTwo
        (Isolation.isolationInput nonzero degree degreeTwo).squarefree
        (Isolation.isolationInput nonzero degree degreeTwo).elimination
        (Isolation.Track.isolatedTrack nonzero degree degreeTwo index).initial
        (Radius.unitRobustSourceRadius unit degree degreeTwo)
        (Radius.unitRobustSourceRadius_pos unit degree degreeTwo) }) :
    Prepared nonzero unit degree degreeTwo index :=
  ⟨saved.val, saved.property.trans
    (refine_eq nonzero degree degreeTwo index _ _ _).symm⟩

end Purelib.RootIsolation.Power.Unit.Source.Preparation
