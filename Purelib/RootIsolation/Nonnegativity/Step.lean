module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Winding.Box.Grid.Central.Basic
public import Purelib.Polynomial.Winding.Box.Grid.Central.Build
import Purelib.RootIsolation.Newton.Band.Build
import Purelib.RootIsolation.State.Negative
public import Purelib.RootIsolation.State.Negative
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic
public import Purelib.RootIsolation.Track.Newton.Build
public import Purelib.Polynomial.Winding.Box.Grid.Central.Selection
import Purelib.Polynomial.Clearance.Box.Grid.Central.Separation
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Band.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Grid.Central.Cell
import Purelib.Polynomial.Clearance.Box.Line.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
import Purelib.RootIsolation.Newton.Band.Basic
import Purelib.RootIsolation.State.Raw
import Purelib.RootIsolation.Track.Newton.Refinement
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

/-!
# Removing a central winding-one band

One extraction retains the checked Newton track and a deterministically
selected negative complementary region. The original grid certificates
link the retained boxes by refinement, strict containment and separation.
-/

namespace Purelib.RootIsolation.Nonnegativity.Step

set_option genInjectivity false in
/-- A retained winding-one track and negative complementary region.

Both retain the original polynomial, ambient box and negative input state.
Strict containment and separation certificates relate the same extracted
track to every strict inner box of the selected complementary region. -/
public structure StepOutput
    (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (ambient : Box)
    (current : State.Negative.NegativeState p ambient) where
  /-- The winding-one track extracted from the original negative-winding state. -/ track :
    Track.Basic.WindingOneTrack p ambient
  /-- The selected negative complementary region on the same polynomial and ambient box. -/ next :
    State.Negative.NegativeState p ambient
  /-- The extracted initial track box lies strictly inside the original state box. -/ center_strict_current :
    track.initial.box.StrictInterior current.box
  /-- The selected negative complement refines the original state box. -/ next_refines_current : next.box.Refines
    current.box
  /-- Every strict inner box of the selected negative complement is separated from the extracted track's initial box. -/
    center_avoids_next : ∀ {small : Box},
    small.StrictInterior next.box → track.initial.box.Separated small

constructive_injectivity StepOutput

/-- Extract the checked central winding-one track and retain a negative complementary region.

The original Newton band supplies the inner state and eight-cell grid. Selecting its negative complement retains strict
containment, refinement and separation from the same extracted track. -/
@[expose] public def extractStep
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (current : State.Negative.NegativeState p ambient) : StepOutput p ambient current := by
  have onePositive : (0 : Fraction.Rational) < 1 :=
    Fraction.Cast.Order.natCast_pos_direct (n := 1) (by decide)
  let extracted := Newton.Band.Build.extract degreeAtLeastTwo
    squarefree elimination current.raw onePositive
  let center := extracted.band.box
  let centerState : State.WindingOne.Basic.WindingOneState p ambient :=
    { box := center
      refinesAmbient := extracted.refinesAmbient
      proper := extracted.proper
      clearance := extracted.clearance
      rawWindingFour := extracted.rawWindingFour
      ambientLeftClearance := extracted.ambientLeftClearance
      ambientRightClearance := extracted.ambientRightClearance
      ambientBottomClearance := extracted.ambientBottomClearance
      ambientTopClearance := extracted.ambientTopClearance }
  let track := Track.Newton.Build.ofInitial degreeAtLeastTwo
    squarefree elimination centerState
  let grid : Polynomial.Winding.Box.Grid.Central.Basic.Arrangement p current.box center :=
    Winding.Box.Grid.Central.Build.build current.clearance extracted.proper extracted.strictCurrent
      extracted.leftLineClearance extracted.rightLineClearance
      extracted.bottomLineClearance extracted.topLineClearance
  let nextCell := grid.firstNegative
  have nextNegative : Winding.Box.Basic.quadrupledBoxWinding p nextCell.box < 0 :=
    grid.firstNegative_rawWinding_neg current.rawWinding_neg
      extracted.rawWindingFour
  let next : State.Negative.NegativeState p ambient :=
    { box := nextCell.box
      refinesAmbient := nextCell.refines.trans current.refinesAmbient
      proper := nextCell.proper
      clearance := nextCell.clearance
      rawWinding_neg := nextNegative }
  exact
    { track := track
      next := next
      center_strict_current := by
        simpa only [track, Track.Newton.Build.ofInitial,
          centerState, center, State.Negative.NegativeState.raw] using extracted.strictCurrent
      next_refines_current := nextCell.refines
      center_avoids_next := by
        intro small strict
        change center.Separated small
        exact nextCell.center_separated_from_strictInterior strict }
end Purelib.RootIsolation.Nonnegativity.Step
