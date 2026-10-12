module
import Purelib.Topology.Knot.Braid.ThreeStrand.Word
public import Purelib.Approximation.Gaussian.Acquisition.Positive.Search
import Purelib.Approximation.Gaussian.Acquisition.State
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Control.FiniteRunner.Basic
import Purelib.Curves.Legendre.Acquisition.Automatic.Basic
import Purelib.Curves.Legendre.Acquisition.Automatic.Positive
import Purelib.Curves.Legendre.FractionalWords.Periods
public import Purelib.Curves.Legendre.GuaranteedFold
import Init.Prelude
import Purelib.Approximation.Gaussian.Process.Imaginary.Positive.Basic

open Purelib.Approximation.Gaussian.Acquisition

open Purelib.Approximation.Gaussian.Acquisition.Positive

open Purelib.Approximation.Gaussian.Name

open Purelib.Control.FiniteRunner

open Purelib.Curves.Legendre

open Purelib.Curves.Legendre.Acquisition

open Purelib.Curves.Legendre.Acquisition.Automatic

open Purelib.Curves.Legendre.FractionalWords

open Purelib.Topology.Knot.Braid

section
@[expose] public section

/-!
# Automatic discovery of the initial positive enclosure

A cached rational ball passes when its centre is above the real axis and its
squared radius is below the squared half-height. The soundness proof gives a
positive imaginary lower bound for every point in that ball. Failed tests
perform one canonical finite refinement; bounded runs retain their exact
state on exhaustion and never infer a negative positivity verdict.
-/

namespace Purelib.Curves.Legendre.Acquisition.Positive

/-- Discover positivity, then prepare the final matrix and productive output. The caller supplies only the input, word,
retained state, and finite budget. -/
def attemptTransport (tau : Coherent.CoherentNamed) (word :
  ThreeStrand.Word) (state : Approximation.Gaussian.Acquisition.State tau) (fuel : Nat) :
    LegendreTransport.ResultPayload
      (Automatic.Basic.Ready tau word) (Approximation.Gaussian.Acquisition.State tau) :=
  match Search.attempt tau state fuel with
  | .ready positive => .ready (Positive.guaranteed positive word)
  | .exhausted retained => .exhausted retained

/-- The same discovered enclosure also prepares the entire dependent fold and its final preparation provider, without
further positivity searches. -/
def attemptFold (tau : Coherent.CoherentNamed) (word :
  ThreeStrand.Word) (state : Approximation.Gaussian.Acquisition.State tau) (fuel : Nat) :
    LegendreTransport.ResultPayload
      (GuaranteedFold.Prepared tau
        (Periods.periodBraidMatrices word)) (Approximation.Gaussian.Acquisition.State tau) :=
  match Search.attempt tau state fuel with
  | .ready positive => .ready (GuaranteedFold.prepareWord positive word)
  | .exhausted retained => .exhausted retained

end Purelib.Curves.Legendre.Acquisition.Positive

end
