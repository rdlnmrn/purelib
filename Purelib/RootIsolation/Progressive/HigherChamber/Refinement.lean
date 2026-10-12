module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Clearance.Box.Boundary.Lines
public import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Refinement.Transport
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.RootIsolation.FTA.Squarefree.Input
public import Purelib.RootIsolation.Progressive.HigherChamber.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic
import Purelib.RootIsolation.Track.Newton.Build
import Purelib.Tactic.Ring
public import Purelib.RootIsolation.FTA.Squarefree.Prepare
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Refinement
import Purelib.RootIsolation.FTA.Squarefree.Basic

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

/-- The finite index type bounded by the original higher chamber's retained polynomial degree. -/
abbrev Index
    {table : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {target : Fraction.Rational}
    {positive : 0 < target}
    (_chamber : HigherChamber table target positive) :=
  Fin table.polynomial.natDegree
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

/-- Read the original stable refinement step at the supplied chamber index. -/
def stepAt
    {table : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {target : Fraction.Rational}
    {positive : 0 < target}
    (chamber : HigherChamber table target positive)
    (index : chamber.Index) :
    Dense.Gaussian.Coefficient.Progressive.Refinement.Transport.StableRefinement table target positive
      (chamber.owners.trackAt index).initial.box where
  currentSmall := chamber.currentSmall
  proper := (chamber.owners.trackAt index).initial.proper
  clearance := (chamber.owners.trackAt index).initial.clearance
  budget_lt := chamber.stable index
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

/-- The transported polynomial has winding one on the preceding owner's
whole box.  Taking that box itself as ambient supplies all four required
ambient-line certificates directly from the transported boundary clearance. -/
def nextInitialAt
    {table : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {target : Fraction.Rational}
    {positive : 0 < target}
    (chamber : HigherChamber table target positive)
    (index : chamber.Index) :
    State.WindingOne.Basic.WindingOneState
      (table.refine target positive).polynomial
      (chamber.owners.trackAt index).initial.box := by
  let old := (chamber.owners.trackAt index).initial
  let step := chamber.stepAt index
  let clearance := step.nextClearance
  exact
    { box := old.box
      refinesAmbient := Box.refines_refl old.box
      proper := old.proper
      clearance := clearance
      rawWindingFour := by
        change Winding.Box.Basic.quadrupledBoxWinding step.nextTable.polynomial
            old.box = 4
        rw [step.next_winding_eq]
        exact old.rawWindingFour
      ambientLeftClearance := Clearance.Box.Boundary.Lines.leftOfBoundary clearance
      ambientRightClearance := Clearance.Box.Boundary.Lines.rightOfBoundary clearance
      ambientBottomClearance := Clearance.Box.Boundary.Lines.bottomOfBoundary clearance
      ambientTopClearance := Clearance.Box.Boundary.Lines.topOfBoundary clearance }
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

/-- Build the next chamber input from the retained refined boxes and original degree bounds. -/
def nextInput
    {table : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {target : Fraction.Rational}
    {positive : 0 < target}
    (chamber : HigherChamber table target positive) :
    FTA.Squarefree.Input (table.refine target positive).polynomial where
  squarefree := chamber.nextSquarefree
  degreeAtLeastTwo := by
    rw [(table.refine target positive).polynomial_natDegree,
      table.refine_degree target positive, ← table.polynomial_natDegree]
    exact chamber.degreeAtLeastTwo
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

/-- A total shrinking track for the transported owner.  Its ambient box is
literally the preceding owner box, so every later request retains finite owner
identity without relabelling roots. -/
def nextTrackAt
    {table : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {target : Fraction.Rational}
    {positive : 0 < target}
    (chamber : HigherChamber table target positive)
    (index : chamber.Index) :
    Track.Basic.WindingOneTrack
      (table.refine target positive).polynomial
      (chamber.owners.trackAt index).initial.box :=
  Track.Newton.Build.ofInitial
    chamber.nextInput.degreeAtLeastTwo chamber.nextSquarefree
    chamber.nextInput.elimination (chamber.nextInitialAt index)
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

/-- The next track's initial box is exactly the refined box at the supplied original index. -/
theorem nextTrackAt_initial_box
    {table : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {target : Fraction.Rational}
    {positive : 0 < target}
    (chamber : HigherChamber table target positive)
    (index : chamber.Index) :
    (chamber.nextTrackAt index).initial.box =
      (chamber.owners.trackAt index).initial.box := rfl
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

/-- The next tracks' initial boxes retain the original pairwise separation certificate. -/
theorem nextTrackAt_pairwiseSeparated
    {table : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {target : Fraction.Rational}
    {positive : 0 < target}
    (chamber : HigherChamber table target positive)
    (left right : chamber.Index) (different : left ≠ right) :
    (chamber.nextTrackAt left).initial.box.Separated
      (chamber.nextTrackAt right).initial.box :=
  chamber.owners.trackAt_pairwiseSeparated left right different
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

/-- One arbitrary-accuracy refinement of a transported owner, strictly
inside the preceding owner's box. -/
def requestAt
    {table : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {target : Fraction.Rational}
    {positive : 0 < target}
    (chamber : HigherChamber table target positive)
    (index : chamber.Index) (epsilon : Fraction.Rational)
    (epsilonPositive : 0 < epsilon) :
    State.WindingOne.Basic.WindingOneState
      (table.refine target positive).polynomial
      (chamber.owners.trackAt index).initial.box :=
  (chamber.nextTrackAt index).refine
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

/-- Each indexed chamber request meets the supplied positive accuracy target. -/
theorem requestAt_accurate
    {table : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {target : Fraction.Rational}
    {positive : 0 < target}
    (chamber : HigherChamber table target positive)
    (index : chamber.Index) (epsilon : Fraction.Rational)
    (epsilonPositive : 0 < epsilon) :
    (chamber.requestAt index epsilon epsilonPositive).box.diagonalSq ≤
      epsilon ^ 2 :=
  (chamber.nextTrackAt index).accurate
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

/-- The indexed requested owner boxes are pairwise separated. -/
theorem requestAt_pairwiseSeparated
    {table : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {target : Fraction.Rational}
    {positive : 0 < target}
    (chamber : HigherChamber table target positive)
    (left right : chamber.Index) (different : left ≠ right)
    (epsilon : Fraction.Rational) (epsilonPositive : 0 < epsilon) :
    (chamber.requestAt left epsilon epsilonPositive).box.Separated
      (chamber.requestAt right epsilon epsilonPositive).box :=
  Box.Separated.of_refines
    (chamber.nextTrackAt_pairwiseSeparated left right different)
    ((chamber.nextTrackAt left).nested
      (chamber.nextTrackAt left).initial epsilon epsilonPositive)
    ((chamber.nextTrackAt right).nested
      (chamber.nextTrackAt right).initial epsilon epsilonPositive)
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

/-- Every requested box remains strictly inside its own retained original owner box. -/
theorem requestAt_strict_owner
    {table : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {target : Fraction.Rational}
    {positive : 0 < target}
    (chamber : HigherChamber table target positive)
    (index : chamber.Index) (epsilon : Fraction.Rational)
    (epsilonPositive : 0 < epsilon) :
    (chamber.requestAt index epsilon epsilonPositive).box.StrictInterior
      (chamber.owners.trackAt index).initial.box :=
  (chamber.nextTrackAt index).strict
    (chamber.nextTrackAt index).initial epsilon epsilonPositive
end HigherChamber

end Purelib.RootIsolation.Progressive.HigherChamber

end

