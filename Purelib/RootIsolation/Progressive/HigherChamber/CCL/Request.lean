module

import Purelib.Data.CCL.Progressive.Cursor.Image
import Purelib.Data.CCL.Transducer.Mode.Semantics
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
import Purelib.RootIsolation.CCL.Persistent.Track.Basic
import Purelib.RootIsolation.Progressive.HigherChamber.Basic
import Purelib.RootIsolation.Track.CCL.Sample.Basic
public import Purelib.RootIsolation.Track.CCL.Sample.Build
import Purelib.Tactic.Ring
public import Purelib.RootIsolation.Progressive.HigherChamber.Refinement
public import Purelib.RootIsolation.CCL.Persistent.Track.Request
import Purelib.RootIsolation.Track.CCL.Sample.Residual
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.CCL.Progressive.Cursor.Request
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Refinement
import Purelib.RootIsolation.FTA.Squarefree.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Approximation.Process
import Purelib.RootIsolation.Track.Basic

open Purelib

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.RootIsolation.Progressive.HigherChamber
open Purelib.Data.Gaussian
section HigherChamber

/-! ### CCL observations of every transported owner -/

/-- Empty-word persistent CCL state for one transported owner. -/
def persistentInitialAt
    {table : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {target : Fraction.Rational}
    {positive : 0 < target}
    (chamber : HigherChamber table target positive)
    (index : chamber.Index) :
    CCL.Persistent.Track.Basic.State (chamber.nextTrackAt index) :=
  CCL.Persistent.Track.Basic.State.initial (chamber.nextTrackAt index)
end HigherChamber

end Purelib.RootIsolation.Progressive.HigherChamber

end

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.RootIsolation.Progressive.HigherChamber
open Purelib.Data.Gaussian
section HigherChamber

/-- One persistent bit-and-accuracy request on a transported owner. -/
def persistentRequestAt
    {table : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {target : Fraction.Rational}
    {positive : 0 < target}
    (chamber : HigherChamber table target positive)
    (index : chamber.Index) (epsilon : Fraction.Rational)
    (epsilonPositive : 0 < epsilon) (count : Nat) :
    CCL.Persistent.Track.Basic.State (chamber.nextTrackAt index) :=
  (chamber.persistentInitialAt index).request epsilon epsilonPositive count
end HigherChamber

end Purelib.RootIsolation.Progressive.HigherChamber

end

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.RootIsolation.Progressive.HigherChamber
open Purelib.Data.Gaussian
section HigherChamber

/-- The persistent request's retained numerical box meets the supplied positive accuracy target. -/
theorem persistentRequestAt_accurate
    {table : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {target : Fraction.Rational}
    {positive : 0 < target}
    (chamber : HigherChamber table target positive)
    (index : chamber.Index) (epsilon : Fraction.Rational)
    (epsilonPositive : 0 < epsilon) (count : Nat) :
    (chamber.persistentRequestAt index epsilon epsilonPositive count).numerical.box.diagonalSq ≤
      epsilon ^ 2 :=
  (chamber.persistentInitialAt index).request_box_accurate epsilon
    epsilonPositive count
end HigherChamber

end Purelib.RootIsolation.Progressive.HigherChamber

end

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.RootIsolation.Progressive.HigherChamber
open Purelib.Data.Gaussian
section HigherChamber

/-- Parallel exact rational sample request on the same deterministic
transported track.  This supplies the polynomial residual certificate while
the persistent state supplies the already-running raw CCL word. -/
def sampleRequestAt
    {table : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {target : Fraction.Rational}
    {positive : 0 < target}
    (chamber : HigherChamber table target positive)
    (index : chamber.Index) (epsilon : Fraction.Rational)
    (epsilonPositive : 0 < epsilon) :
    Track.CCL.Sample.Basic.Request
      (chamber.nextTrackAt index) (chamber.nextTrackAt index).initial
      epsilon epsilonPositive :=
  Track.CCL.Sample.Build.request (chamber.nextTrackAt index)
    (chamber.nextTrackAt index).initial epsilon epsilonPositive
end HigherChamber

end Purelib.RootIsolation.Progressive.HigherChamber

end

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.RootIsolation.Progressive.HigherChamber
open Purelib.Data.Gaussian
section HigherChamber

/-- The persistent and exact-sample requests retain exactly the same numerical box. -/
theorem
  persistentRequestAt_box_eq_sampleRequestAt
    {table : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {target : Fraction.Rational}
    {positive : 0 < target}
    (chamber : HigherChamber table target positive)
    (index : chamber.Index) (epsilon : Fraction.Rational)
    (epsilonPositive : 0 < epsilon) (count : Nat) :
    (chamber.persistentRequestAt index epsilon epsilonPositive count).numerical.box =
      (chamber.sampleRequestAt index epsilon epsilonPositive).next.box := rfl
end HigherChamber

end Purelib.RootIsolation.Progressive.HigherChamber

end

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.RootIsolation.Progressive.HigherChamber
open Purelib.Data.Gaussian
section HigherChamber

/-- The persistent request's numerical box refines the same preceding owner box. -/
theorem persistentRequestAt_box_refines_owner
    {table : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {target : Fraction.Rational}
    {positive : 0 < target}
    (chamber : HigherChamber table target positive)
    (index : chamber.Index) (epsilon : Fraction.Rational)
    (epsilonPositive : 0 < epsilon) (count : Nat) :
    (chamber.persistentRequestAt index epsilon epsilonPositive count).numerical.box.Refines
      (chamber.owners.trackAt index).initial.box := by
  exact (chamber.persistentRequestAt index epsilon epsilonPositive count).numericalRefinesInitial
end HigherChamber

end Purelib.RootIsolation.Progressive.HigherChamber

end

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.RootIsolation.Progressive.HigherChamber
open Purelib.Data.Gaussian
section HigherChamber

/-- Every live parser candidate after the request remains owned by the same
preceding rational root box. -/
theorem
  persistentRequestAt_candidate_in_owner
    {table : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {target : Fraction.Rational}
    {positive : 0 < target}
    (chamber : HigherChamber table target positive)
    (index : chamber.Index) (epsilon : Fraction.Rational)
    (epsilonPositive : 0 < epsilon) (count : Nat)
    {tail : Gaussian.Basic.Canonical}
    (possible : Data.CCL.Transducer.Mode.Semantics.SemanticMode.possible
      (chamber.persistentRequestAt index epsilon epsilonPositive count).cursor.machine.mode
      tail) :
    ∃ value : Gaussian.Basic.Canonical,
      (chamber.owners.trackAt index).initial.box.Contains value ∧
        (Data.CCL.Progressive.Cursor.Image.Machine.image
          (chamber.persistentRequestAt index epsilon epsilonPositive count).cursor.machine
          tail).Equivalent (Geometry.Projective.Line.Proj.affine value) := by
  exact (chamber.persistentRequestAt index epsilon epsilonPositive count).candidate_in_initial_box
    possible

end HigherChamber

end Purelib.RootIsolation.Progressive.HigherChamber

end

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.RootIsolation.Progressive.HigherChamber
open Purelib.Data.Gaussian
section HigherChamber

/-- Persistent requests at distinct original indices retain pairwise separated boxes. -/
theorem persistentRequestAt_pairwiseSeparated
    {table : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {target : Fraction.Rational}
    {positive : 0 < target}
    (chamber : HigherChamber table target positive)
    (left right : chamber.Index) (different : left ≠ right)
    (epsilon : Fraction.Rational) (epsilonPositive : 0 < epsilon)
    (count : Nat) :
    (chamber.persistentRequestAt left epsilon epsilonPositive count).numerical.box.Separated
      (chamber.persistentRequestAt right epsilon epsilonPositive count).numerical.box :=
  Box.Separated.of_refines
    (chamber.owners.trackAt_pairwiseSeparated left right different)
    (chamber.persistentRequestAt_box_refines_owner left epsilon
      epsilonPositive count)
    (chamber.persistentRequestAt_box_refines_owner right epsilon
      epsilonPositive count)
end HigherChamber

end Purelib.RootIsolation.Progressive.HigherChamber

end

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.RootIsolation.Progressive.HigherChamber
open Purelib.Data.Gaussian
section HigherChamber

/-- The persistent request emits exactly the requested number of bits from its initial empty word. -/
theorem persistentRequestAt_word_length
    {table : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {target : Fraction.Rational}
    {positive : 0 < target}
    (chamber : HigherChamber table target positive)
    (index : chamber.Index) (epsilon : Fraction.Rational)
    (epsilonPositive : 0 < epsilon) (count : Nat) :
    (chamber.persistentRequestAt index epsilon epsilonPositive count).cursor.machine.emitted.length =
      count := by
  have initialLength :
      (chamber.persistentInitialAt index).cursor.machine.emitted.length = 0 := rfl
  have length := (chamber.persistentInitialAt index).request_word_length
    epsilon epsilonPositive count
  rw [initialLength, Nat.zero_add] at length
  exact length
end HigherChamber

end Purelib.RootIsolation.Progressive.HigherChamber

end

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.RootIsolation.Progressive.HigherChamber
open Purelib.Data.Gaussian
section HigherChamber

/-- The requested exact sample's polynomial residual is bounded by the original owner-box residual constant times the
squared accuracy. -/
theorem sampleRequestAt_residual_le
    {table : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {target : Fraction.Rational}
    {positive : 0 < target}
    (chamber : HigherChamber table target positive)
    (index : chamber.Index) (epsilon : Fraction.Rational)
    (epsilonPositive : 0 < epsilon) :
    Data.Gaussian.Norm.Basic.normSq
        ((table.refine target positive).polynomial.eval
          (chamber.sampleRequestAt index epsilon epsilonPositive).sample.point) ≤
      Dense.Gaussian.Bounds.Box.residualConstant
          (table.refine target positive).polynomial
          (chamber.owners.trackAt index).initial.box * epsilon ^ 2 :=
  (chamber.sampleRequestAt index epsilon epsilonPositive).sampleResidual_le_requested
    chamber.nextInput.degreePositive
end HigherChamber

end Purelib.RootIsolation.Progressive.HigherChamber

end
