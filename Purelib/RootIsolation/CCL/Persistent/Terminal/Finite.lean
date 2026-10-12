module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RootIsolation.CCL.Persistent.State.Basic
public import Purelib.RootIsolation.CCL.Persistent.Terminal.Point
import Purelib.RootIsolation.Track.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.List.BinaryPrefix.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.RootIsolation.State.WindingOne.Basic

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

public section

open Purelib.Data

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

/-!
# Resolving rational terminal samples on a persistent CCL track

Every displayed Gaussian-rational sample has a finite CCL terminal.  Reaching
that terminal while constructing a persistent prefix therefore does not by
itself mean that the polynomial root is rational.  This module makes the
necessary distinction executable: evaluate the polynomial at the displayed
terminal point; return an exact root when it vanishes, otherwise perform one
coefficient-computed winding-one refinement that excludes that point.
-/

namespace Purelib.RootIsolation.CCL.Persistent.Terminal.Finite

set_option genInjectivity false in
/-- Bounded outcome after resolving both possible terminals of a two-bit
sector phase. -/
inductive PairResolution
    {p : CoefficientPolynomial} {ambient : Box}
    (current : State p ambient) (left right : Canonical) where
  /-- An exact displayed polynomial root retained inside the original current box. -/ | exact (root :
    CCL.Persistent.State.Basic.ExactRootIn p current.numerical.box)
  /-- A same-prefix refinement excludes both original displayed terminal candidates. -/ | excluded (state :
    State p ambient)
      (boxRefines : state.numerical.box.Refines current.numerical.box)
      (word_eq : state.word = current.word)
      (leftOutside : ¬state.numerical.box.Contains left)
      (rightOutside : ¬state.numerical.box.Contains right)

constructive_injectivity PairResolution

/-- Resolve the two phase-computable terminal candidates in at most two
winding-track refinements. -/
@[expose] def resolvePair
    {p : CoefficientPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (track : Track.Basic.WindingOneTrack p ambient) (current : State p ambient)
    (left right : Canonical) : PairResolution current left right := by
  match CCL.Persistent.Terminal.Point.resolvePoint degreePositive track current left with
  | .exact root => exact .exact root
  | .excluded leftState leftRefines leftWord leftOutside =>
      match CCL.Persistent.Terminal.Point.resolvePoint degreePositive track leftState right with
      | .exact root =>
          exact .exact
            { point := root.point
              root := root.root
              inside := leftRefines.contains root.inside }
      | .excluded rightState rightRefines rightWord rightOutside =>
          exact .excluded rightState (rightRefines.trans leftRefines)
            (rightWord.trans leftWord) (by
              intro inside
              exact leftOutside (rightRefines.contains inside)) rightOutside

set_option genInjectivity false in
/-- Bounded outcome after resolving an arbitrary displayed finite boundary
list. -/
inductive PointsResolution
    {p : CoefficientPolynomial} {ambient : Box}
    (current : State p ambient) (points : List Canonical) where
  /-- An exact displayed polynomial root retained inside the original current box. -/ | exact (root :
    CCL.Persistent.State.Basic.ExactRootIn p current.numerical.box)
  /-- A same-prefix refinement excludes every point in the original finite list. -/ | excluded (state :
    State p ambient)
      (boxRefines : state.numerical.box.Refines current.numerical.box)
      (word_eq : state.word = current.word)
      (outside : ∀ point, point ∈ points →
        ¬state.numerical.box.Contains point)

constructive_injectivity PointsResolution

/-- Resolve every member of one explicit finite zero set.  The first
displayed polynomial root is returned; otherwise the final same-prefix
winding state excludes the whole list. -/
@[expose] def resolvePoints
    {p : CoefficientPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (track : Track.Basic.WindingOneTrack p ambient) (current : State p ambient) :
    (points : List Canonical) →
      PointsResolution current points
  | [] => .excluded current
      (Box.refines_refl current.numerical.box) rfl
      (by intro point member; exact (List.not_mem_nil member).elim)
  | point :: points =>
      match CCL.Persistent.Terminal.Point.resolvePoint degreePositive track current point with
      | .exact root => .exact root
      | .excluded next nextRefines nextWord pointOutside =>
          match resolvePoints degreePositive track next points with
          | .exact root => .exact
              { point := root.point
                root := root.root
                inside := nextRefines.contains root.inside }
          | .excluded final finalRefines finalWord remainingOutside =>
              .excluded final (finalRefines.trans nextRefines)
                (finalWord.trans nextWord) (by
                  intro target member inside
                  rcases Purelib.Data.List.Membership.mem_cons.mp member with equal | tailMember
                  · subst target
                    exact pointOutside (finalRefines.contains inside)
                  · exact remainingOutside target tailMember inside)
end Purelib.RootIsolation.CCL.Persistent.Terminal.Finite

end
