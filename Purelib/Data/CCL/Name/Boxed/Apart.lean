module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Enclosure.Ball.Box
public import Purelib.Approximation.Gaussian.Name.Apart
import Purelib.Approximation.Gaussian.Process.Apart
public import Purelib.Data.CCL.Name.Boxed.Approximation
import Purelib.Data.CCL.Name.Boxed.Process
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.CCL.Name.Boxed.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

section
public section

/-!
# Boxed CCL names as arithmetic enclosure processes

This is the deliberate one-way bridge from an ordinary raw CCL word plus a
finite rational box sidecar to the generic arithmetic process.  The raw
encoder, parser, and boxed-name definitions do not import this module.
-/

namespace Purelib.Data.CCL.Name.Boxed
section ProgressiveName

open Purelib.Approximation.Gaussian in
open Purelib.Data.CCL.Name in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
set_option genInjectivity false in
/-- Retain a positive uniform squared-norm lower bound for every ball of the same progressive boxed name.

The bound applies to every value contained in the ball enclosing any retained certificate's box. It keeps the original
name and states, providing the stronger enclosure condition needed for its approximation process. -/
structure Apart (name : Boxed.Process.ProgressiveName) where
  /-- The retained rational lower bound for squared norms throughout every enclosing ball. -/ lowerSq :
    Fraction.Rational
  /-- The retained squared-norm lower bound is strictly positive. -/ positive : 0 < lowerSq
  /-- Every point in the enclosing ball at any original name state satisfies that same lower bound. -/ lower : ∀ (state
    : name.State) {value : Basic.Canonical},
    (Approximation.Gaussian.Enclosure.Ball.ofBox
      (name.certificate state).box).Contains value → lowerSq ≤
      Gaussian.Norm.Basic.normSq value

constructive_injectivity Apart

namespace Apart

end Apart
namespace Apart

open Purelib.Approximation.Gaussian
open Purelib.Data.CCL.Name
/-- Transport the same positive lower bound to the exact approximation process of the retained boxed name. -/
@[expose] def toProcessApart {name :
  Boxed.Process.ProgressiveName} (apart : Apart name) :
    Approximation.Gaussian.Process.Apart (Boxed.Approximation.ProgressiveName.toProcess name) :=
  { lowerSq := apart.lowerSq
    positive := apart.positive
    lower := by
      intro state value inside
      exact apart.lower state (by
          simpa only [Boxed.Approximation.ProgressiveName.toProcess_ball]
            using inside) }

/-- Attach the same apartness certificate to the boxed name's exact initial named approximation. -/
@[expose] def toNamedApart {name :
  Boxed.Process.ProgressiveName} (apart : Apart name) :
    Name.Basic.Named.Apart (Boxed.Approximation.ProgressiveName.toNamed name) :=
  { certificate := (toProcessApart apart) }

end Apart
end ProgressiveName

end Purelib.Data.CCL.Name.Boxed

end
