module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Approximation.Rational.Budget.Square
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Bound.Operational
import Purelib.Approximation.Bound.Process
public import Purelib.Approximation.Box.Content
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Content
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
public import Purelib.RootIsolation.Track.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Tactic.Ring

open Purelib.Approximation.Rational.Budget

open Purelib.Polynomial.Dense.Gaussian.Basic

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
public section

/-!
# Finite area observations of RFAP shrinking tracks

This is the Paper-I-side area interpretation of a winding-one track.  It uses
only RFAP rational boxes and no downstream encoding layer.  A request returns another
finite winding certificate whose enclosing rational area meets the supplied
budget.
-/

namespace Purelib.RootIsolation.Track.Area

/-- One area-requested state of an RFAP winding-one track. -/
@[expose] def trackAreaState
    {p : CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (track : Basic.WindingOneTrack p ambient) (current : State.WindingOne.Basic.WindingOneState p ambient)
    (target : Fraction.Rational) (positive : 0 < target) :
    State.WindingOne.Basic.WindingOneState p ambient :=
  track.refine current (Square.radius target)
    (Square.radius_pos positive)

/-- An area-requested winding state refines its original input box. -/
theorem trackAreaState_refines
    {p : CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (track : Basic.WindingOneTrack p ambient) (current : State.WindingOne.Basic.WindingOneState p ambient)
    (target : Fraction.Rational) (positive : 0 < target) :
    (trackAreaState track current target positive).box.Refines current.box :=
  track.nested current (Square.radius target)
    (Square.radius_pos positive)

/-- Every RFAP site admits a further finite winding-one box whose exact
rational area is below any supplied positive rational budget. -/
theorem trackAreaState_content_lt
    {p : CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (track : Basic.WindingOneTrack p ambient) (current : State.WindingOne.Basic.WindingOneState p ambient)
    (target : Fraction.Rational) (positive : 0 < target) :
    Box.Content.boxContent (trackAreaState track current target positive).box < target := by
  apply Box.Content.boxContent_lt_of_diagonalSq_lt
  exact (track.accurate current (Square.radius target)
    (Square.radius_pos positive)).trans_lt
      (Square.radius_sq_lt positive)

set_option genInjectivity false in
/-- One displayed RFAP track state together with its finite refinement
certificate back to the track's distinguished initial box. -/
structure TrackAreaProcessState
    {p : CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (track : Basic.WindingOneTrack p ambient) where
  /-- The actual retained winding-one state of the original track. -/ current : State.WindingOne.Basic.WindingOneState p
    ambient
  /-- The current box refines the original track's distinguished initial box. -/ refines_initial : current.box.Refines
    track.initial.box

constructive_injectivity TrackAreaProcessState

/-- Distinguished initial state of the finite area process. -/
@[expose] def trackAreaProcessInitial
    {p : CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (track : Basic.WindingOneTrack p ambient) : TrackAreaProcessState track :=
  ⟨track.initial, Box.refines_refl _⟩

/-- Execute one finite rational area request while retaining reachability
from the initial RFAP track box. -/
@[expose] def trackAreaProcessRequest
    {p : CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (track : Basic.WindingOneTrack p ambient)
    (state : TrackAreaProcessState track)
    (target : Fraction.Rational) (positive : 0 < target) :
    TrackAreaProcessState track :=
  let refined := trackAreaState track state.current target positive
  ⟨refined,
    (trackAreaState_refines track state.current target positive).trans
      state.refines_initial⟩

/-- Executable finite process for the shrinking rational area budget of one
RFAP winding track. -/
@[expose] def trackAreaProcess
    {p : CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (track : Basic.WindingOneTrack p ambient) :
    Approximation.BoundProcess where
  State := TrackAreaProcessState track
  bound state := Approximation.Box.Content.boxContentBound state.current.box
  initial := trackAreaProcessInitial track
  request := trackAreaProcessRequest track
  request_refines state target positive := by
    apply Approximation.Box.Content.boxContentBound_refines
    exact trackAreaState_refines track state.current target positive
  accurate state target positive := by
    rw [Approximation.Box.Content.boxContentBound_width]
    exact trackAreaState_content_lt track state.current target positive
  refinesInitial state :=
    Approximation.Box.Content.boxContentBound_refines state.refines_initial

/-- Every retained area-process bound contains exact rational zero. -/
theorem trackAreaProcess_anchored
    {p : CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (track : Basic.WindingOneTrack p ambient) :
    (trackAreaProcess track).AnchoredAt 0 := by
  intro state
  exact ⟨le_rfl, Box.Content.boxContent_nonneg state.current.box⟩

/-- The RFAP shrinking-area controller is operationally equivalent to exact
rational zero, witnessed entirely by finite requests. -/
theorem trackAreaProcess_operationallyEquivalent_zero
    {p : CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (track : Basic.WindingOneTrack p ambient) :
    Approximation.OperationallyEquivalent (trackAreaProcess track)
      (Approximation.BoundProcess.exact 0) :=
  Approximation.operationallyEquivalent_exact_of_anchoredAt
    (trackAreaProcess track) 0 (trackAreaProcess_anchored track)

/-- Simultaneous finite area observations of a homogeneous finite RFAP track
family. -/
@[expose] def trackFamilyStates
    {p : CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} :
    (tracks : List (Basic.WindingOneTrack p ambient)) →
    (target : Fraction.Rational) → 0 < target → List (State.WindingOne.Basic.WindingOneState p ambient)
  | [], _, _ => []
  | track :: remaining, target, positive =>
      let half := target / 2
      let halfPositive := Fraction.Order.Field.div_pos_direct positive
        (by decide : (0 : Fraction.Rational) < 2)
      trackAreaState track track.initial half halfPositive ::
        Area.trackFamilyStates remaining half halfPositive

/-- Total exact rational area of displayed winding states. -/
@[expose] def trackFamilyContent
    {p : CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (states : List (State.WindingOne.Basic.WindingOneState p ambient)) : Fraction.Rational :=
  (states.map fun state => Box.Content.boxContent state.box).sum

/-- A finite RFAP root-site family has simultaneous winding-certified box
observations inside every positive rational total area budget. -/
theorem trackFamilyStates_content_lt
    {p : CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} :
    ∀ (tracks : List (Basic.WindingOneTrack p ambient))
      (target : Fraction.Rational) (positive : 0 < target),
      trackFamilyContent (trackFamilyStates tracks target positive) < target
  | [], target, positive => by
      simpa only [trackFamilyStates, trackFamilyContent, List.map_nil,
        List.sum_nil] using positive
  | track :: remaining, target, positive => by
      let half := target / 2
      have halfPositive : (0 : Fraction.Rational) < half :=
        Fraction.Order.Field.div_pos_direct positive (by decide)
      have headSmall :=
        trackAreaState_content_lt track track.initial half halfPositive
      have tailSmall :=
        Area.trackFamilyStates_content_lt remaining half halfPositive
      dsimp only [trackFamilyStates, trackFamilyContent]
      rw [List.map_cons, List.sum_cons]
      calc
        Box.Content.boxContent (trackAreaState track track.initial half halfPositive).box +
            trackFamilyContent
              (trackFamilyStates remaining half halfPositive) <
            half + half :=
          Fraction.Order.Arithmetic.add_lt_add_direct headSmall tailSmall
        _ = target := by
          dsimp only [half]
          calc
            target / 2 + target / 2 = (target / 2) * 2 := by ring1
            _ = target :=
              Fraction.Field.div_mul_cancel_of_ne target 2
                (by decide)

end Purelib.RootIsolation.Track.Area

end
