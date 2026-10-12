module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.RootIsolation.CCL.Persistent.Controller.Basic
import Purelib.RootIsolation.CCL.Persistent.State.Basic
import Purelib.RootIsolation.Track.Basic

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.List.BinaryPrefix.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Evaluation
import Purelib.RootIsolation.State.WindingOne.Basic

open Purelib.RootIsolation.CCL.Persistent (State)

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Persistent constructive CCL prefixes on shrinking root boxes

A fresh rational sample from each refined box need not retain any prefix of
the preceding sample's CCL word.  The persistent invariant below records the
stronger fact actually needed by the paper: every later winding-one subbox
has an explicit nonzero rational sample represented by the same raw prefix.

The second half of the file is deliberately structural.  It proves that a
finite one-bit controller with this invariant can be iterated for any
requested natural number of bits while the numerical box is independently
contracted to a requested rational accuracy.  Constructing that one-bit
controller from the finite curve-count and equality-owner geometry is a
separate obligation; it is not postulated as a theorem here.
-/

namespace Purelib.RootIsolation.CCL.Persistent.Controller.Request

set_option genInjectivity false in
/-- Joint finite request: first contract the numerical box to the requested
accuracy and then request exactly `count` additional bits unless an exact
rational root is encountered. -/
inductive RequestResult
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (current : State p ambient) (epsilon : Fraction.Rational) (count : Nat) where
  /-- An exact displayed root certified inside the original current box. -/ | exact (root :
    CCL.Persistent.State.Basic.ExactRootIn p current.numerical.box)
  /-- The retained refined state meeting the original accuracy and exact additional-bit request. -/ | nonterminal (state
    : State p ambient)
      (refines : CCL.Persistent.State.Basic.StateRefines state current)
      (accurate : state.numerical.box.diagonalSq ≤ epsilon ^ 2)
      (length_eq : state.word.length = current.word.length + count)

constructive_injectivity RequestResult

/-- Contract the original numerical box and request the specified number of additional persistent bits.

Return an exact displayed root when encountered; otherwise retain refinement, squared-diagonal accuracy and the exact
increased prefix length. -/
def request
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (track : Track.Basic.WindingOneTrack p ambient) (controller : RootIsolation.CCL.Persistent.Controller p ambient)
    (current : State p ambient) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) (count : Nat) :
    RequestResult current epsilon count := by
  let contracted := State.Basic.refineAlong track current epsilon positive
  let run := CCL.Persistent.Controller.Basic.advanceBits controller contracted count
  match run with
  | .exact root =>
      exact .exact
        { point := root.point
          root := root.root
          inside :=
            (State.Basic.refineAlong_refines track current epsilon positive).box.contains
              root.inside }
  | .advanced final finalRefines _extension _extensionLength _wordEq
      finalLength =>
      have refinesCurrent : CCL.Persistent.State.Basic.StateRefines final current :=
        finalRefines.trans (State.Basic.refineAlong_refines track current epsilon positive)
      have diagonalMonotone : final.numerical.box.diagonalSq ≤
          contracted.numerical.box.diagonalSq :=
        Box.diagonalSq_le_of_refines finalRefines.box
      exact .nonterminal final refinesCurrent
        (diagonalMonotone.trans
          (State.Basic.refineAlong_accurate track current epsilon positive)) (by
            simpa only [contracted, State.Basic.refineAlong,
              State.refine_word] using
              finalLength)

end Purelib.RootIsolation.CCL.Persistent.Controller.Request

end
