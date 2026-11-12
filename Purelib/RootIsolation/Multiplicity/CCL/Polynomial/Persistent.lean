module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.CCL.Progressive.Cursor.Image
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.CCL.Transducer.Machine.Semantics.Basic
import Purelib.Data.CCL.Transducer.Mode.Semantics
import Purelib.Data.CCL.Transducer.Machine.History
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RootIsolation.Multiplicity.CCL.Polynomial.Basic
import Purelib.RootIsolation.Multiplicity.Side.CCL.Name
import Purelib.RootIsolation.Multiplicity.Side.CCL.Persistent
public import Purelib.RationalFunctions.ArgumentPrinciple.CCL.Persistent
import Purelib.RootIsolation.Multiplicity.CCL.Polynomial.Index
public import Purelib.RootIsolation.Multiplicity.CCL.Polynomial.Name
import Purelib.Data.List.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Gaussian.Unit
import Purelib.RationalFunctions.ArgumentPrinciple.CCL.Basic
import Purelib.RationalFunctions.ArgumentPrinciple.General
import Purelib.RationalFunctions.Reduction.Basic
import Purelib.RationalFunctions.Reduction.Nonzero

open Purelib.RationalFunctions.ArgumentPrinciple.CCL.Basic

open Purelib.Polynomial.Dense.Gaussian.Basic

open Purelib

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RationalFunctions

open Purelib.RootIsolation

section
public section

/-!
# Productive CCL streams for every polynomial root site

This polynomial-facing facade specializes the finite rational-function
argument principle to `p / 1`.  A nonzero polynomial receives one displayed
site index for every exact root or higher-degree root-approximation track of
its squarefree multiplicity basis.  The attached natural multiplicity records
repeated factors without duplicating a geometric site.

Every site exposes a persistent finite-request CCL cursor.  A request appends
exactly the requested number of raw bits, preserves the preceding prefix, and
contracts its projective sidecar below the requested squared error.  Exact
rational sites, including zero, use an exact progressive name; higher sites
simultaneously refine their nested Paper-I winding box.  No completed root or
actual infinite stream is introduced.
-/

namespace Purelib.RootIsolation.Multiplicity.CCL.Polynomial.Persistent
namespace NonzeroResult

open Purelib.Data.CCL.Transducer (Machine)

/-- Persistent finite state of one polynomial root stream. -/
abbrev RootState
    {p : CanonicalCoefficients.CoefficientPolynomial} (result :
      Basic.NonzeroResult p)
    (index : (Index.NonzeroResult.RootIndex result)) :=
  (NonzeroResult.ZeroPersistentState result) index

/-- Empty-prefix persistent state of one root stream. -/
@[expose] def rootInitial
    {p : CanonicalCoefficients.CoefficientPolynomial} (result :
      Basic.NonzeroResult p)
    (index : (Index.NonzeroResult.RootIndex result)) :
      (RootState result) index :=
  (NonzeroResult.zeroPersistentInitial result) index

/-- Append `count` bits to one persistent root stream and contract its
sidecar below `epsilon ^ 2`. -/
@[expose] def rootRequest
    {p : CanonicalCoefficients.CoefficientPolynomial} (result :
      Basic.NonzeroResult p)
    (index : (Index.NonzeroResult.RootIndex result)) (current :
      (RootState result) index)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) (count : Nat) :
    (RootState result) index :=
  (NonzeroResult.zeroPersistentRequest result) index current epsilon positive count

/-- Current raw CCL machine of one persistent root state. -/
@[expose] def rootMachine
    {p : CanonicalCoefficients.CoefficientPolynomial} (result :
      Basic.NonzeroResult p)
    (index : (Index.NonzeroResult.RootIndex result)) (state :
      (RootState result) index) :
    CCL.Transducer.Machine :=
  Side.CCL.Persistent.sidePersistentMachine
    result.rfap.numeratorSites result.numeratorCCL index state

/-- Current exposed finite raw word of one persistent root state. -/
@[expose] def rootWord
    {p : CanonicalCoefficients.CoefficientPolynomial} (result :
      Basic.NonzeroResult p)
    (index : (Index.NonzeroResult.RootIndex result)) (state :
      (RootState result) index) : List.Basic.BinaryWord
      :=
  ((rootMachine result) index state).emitted

/-- Current optional numerical box.  Exact rational roots return `none`;
higher RAT sites return their current nested winding box. -/
@[expose] def rootBox?
    {p : CanonicalCoefficients.CoefficientPolynomial} (result :
      Basic.NonzeroResult p)
    (index : (Index.NonzeroResult.RootIndex result)) (state :
      (RootState result) index) :
    Option Box :=
  Side.CCL.Persistent.sidePersistentBox?
    result.rfap.numeratorSites result.numeratorCCL index state

/-- Every persistent state retains exact raw-parser semantics for its original
exact site or initial RAT box. -/
theorem rootState_exact
    {p : CanonicalCoefficients.CoefficientPolynomial} (result :
      Basic.NonzeroResult p)
    (index : (Index.NonzeroResult.RootIndex result)) (state :
      (RootState result) index) :
    CCL.Transducer.Machine.Semantics.Basic.ExactCursor
      ((Name.NonzeroResult.rootName result) index).process
      ((Name.NonzeroResult.rootName result) index).state
      ((rootMachine result) index state) :=
  Side.CCL.Name.sidePersistentExact
    result.rfap.numeratorSites result.numeratorCCL index state

/-- A root request never retracts an exposed bit. -/
theorem rootRequest_word_extends
    {p : CanonicalCoefficients.CoefficientPolynomial} (result :
      Basic.NonzeroResult p)
    (index : (Index.NonzeroResult.RootIndex result)) (current :
      (RootState result) index)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) (count : Nat) :
    ((rootWord result) index current).IsPrefix
      ((rootWord result) index
        ((rootRequest result) index current epsilon positive
          count)) :=
  (NonzeroResult.zeroPersistentRequest_word_extends result) index current epsilon positive
    count

/-- A root request appends exactly the requested number of exposed bits. -/
theorem rootRequest_word_length
    {p : CanonicalCoefficients.CoefficientPolynomial} (result :
      Basic.NonzeroResult p)
    (index : (Index.NonzeroResult.RootIndex result)) (current :
      (RootState result) index)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) (count : Nat) :
    ((rootWord result) index
      ((rootRequest result) index current epsilon positive
        count)).length =
        ((rootWord result) index current).length + count :=
  Side.CCL.Persistent.sidePersistentRequest_word_length
    result.rfap.numeratorSites result.numeratorCCL index current
      epsilon positive count

/-- Exact roots remain exact; a higher root request returns a box nested in
its preceding RAT box. -/
theorem rootRequest_box_refines
    {p : CanonicalCoefficients.CoefficientPolynomial} (result :
      Basic.NonzeroResult p)
    (index : (Index.NonzeroResult.RootIndex result)) (current :
      (RootState result) index)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) (count : Nat) :
    match (rootBox? result) index
        ((rootRequest result) index current epsilon positive
          count),
      (rootBox? result) index current with
    | none, none => True
    | some inner, some outer => inner.Refines outer
    | none, some _ => False
    | some _, none => False :=
  Side.CCL.Persistent.sidePersistentRequest_box_refines
    result.rfap.numeratorSites result.numeratorCCL index current
      epsilon positive count

/-- A higher root request meets the requested numerical box accuracy; exact
roots require no box. -/
theorem rootRequest_box_accurate
    {p : CanonicalCoefficients.CoefficientPolynomial} (result :
      Basic.NonzeroResult p)
    (index : (Index.NonzeroResult.RootIndex result)) (current :
      (RootState result) index)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) (count : Nat) :
    match (rootBox? result) index
      ((rootRequest result) index current epsilon positive count)
        with
    | none => True
    | some box => box.diagonalSq ≤ epsilon ^ 2 :=
  (NonzeroResult.zeroPersistentRequest_box_accurate result) index current epsilon positive
    count

/-- The projective CCL sidecar after a root request has pairwise squared
diameter at most `epsilon ^ 2`. -/
theorem rootRequest_cylinder_accurate
    {p : CanonicalCoefficients.CoefficientPolynomial} (result :
      Basic.NonzeroResult p)
    (index : (Index.NonzeroResult.RootIndex result)) (current :
      (RootState result) index)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) (count : Nat)
    {left right : Gaussian.Basic.Canonical}
    (leftPossible :
      CCL.Transducer.Mode.Semantics.SemanticMode.possible
        ((rootMachine result) index
          ((rootRequest result) index current epsilon positive
            count)).mode left)
    (rightPossible :
      CCL.Transducer.Mode.Semantics.SemanticMode.possible
        ((rootMachine result) index
          ((rootRequest result) index current epsilon positive
            count)).mode right) :
    Geometry.Projective.Chordal.Basic.chordalSq
        (CCL.Progressive.Cursor.Image.Machine.image
          ((rootMachine result) index
            ((rootRequest result) index current epsilon positive
              count)) left)
        (CCL.Progressive.Cursor.Image.Machine.image
          ((rootMachine result) index
            ((rootRequest result) index current epsilon positive
              count)) right) ≤
      epsilon ^ 2 :=
  (NonzeroResult.zeroPersistentRequest_cylinder_accurate result) index current epsilon
    positive count leftPossible rightPossible
/-- Handle the original polynomial-root request with its same result, site index and retained cursor history.

The exact numerical action belongs to this original root's actual reduced-side
observation. The returned complete state is the original `rootRequest` result;
the same history and original process identity remain available for the next
request, including across its retained pending queue and inverse charts.
-/
def withRootRequest {m : Type → Type} [Monad m] {α : Type} {initial : Machine.Snapshot}
    {p : CanonicalCoefficients.CoefficientPolynomial} (result : Basic.NonzeroResult p)
    (index : Index.NonzeroResult.RootIndex result)
    (execute : Side.CCL.Persistent.NumericalHandler m result.rfap.numeratorSites result.numeratorCCL index)
    (current : RootState result index) (history : Machine.History initial)
    (cursorEq : history.current.machine = rootMachine result index current)
    (sourceEq : history.current.source =
      Side.CCL.Persistent.sourceProcess result.rfap.numeratorSites result.numeratorCCL index)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) (count : Nat)
    (use : (next : RootState result index) → next = rootRequest result index current epsilon positive count →
      (retained : Machine.History initial) → retained.current.machine = rootMachine result index next →
        retained.current.source =
          Side.CCL.Persistent.sourceProcess result.rfap.numeratorSites result.numeratorCCL index → m α) : m α :=
  Side.CCL.Persistent.withRequest result.rfap.numeratorSites result.numeratorCCL index execute current history
    cursorEq sourceEq epsilon positive count use

end NonzeroResult

end Purelib.RootIsolation.Multiplicity.CCL.Polynomial.Persistent

end
