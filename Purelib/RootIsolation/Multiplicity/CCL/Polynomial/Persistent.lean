module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.CCL.Progressive.Cursor.Image
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.CCL.Transducer.Machine.Semantics.Basic
import Purelib.Data.CCL.Transducer.Mode.Semantics
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

/-- Persistent finite state of one polynomial root stream. -/
abbrev RootState
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (result :
      Multiplicity.CCL.Polynomial.Basic.NonzeroResult p)
    (index : (Multiplicity.CCL.Polynomial.Index.NonzeroResult.RootIndex result)) :=
  (ArgumentPrinciple.CCL.Basic.NonzeroResult.ZeroPersistentState result) index

/-- Empty-prefix persistent state of one root stream. -/
@[expose] def rootInitial
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (result :
      Multiplicity.CCL.Polynomial.Basic.NonzeroResult p)
    (index : (Multiplicity.CCL.Polynomial.Index.NonzeroResult.RootIndex result)) :
      (Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.RootState result) index :=
  (ArgumentPrinciple.CCL.Basic.NonzeroResult.zeroPersistentInitial result) index

/-- Append `count` bits to one persistent root stream and contract its
sidecar below `epsilon ^ 2`. -/
@[expose] def rootRequest
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (result :
      Multiplicity.CCL.Polynomial.Basic.NonzeroResult p)
    (index : (Multiplicity.CCL.Polynomial.Index.NonzeroResult.RootIndex result)) (current :
      (Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.RootState result) index)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) (count : Nat) :
    (Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.RootState result) index :=
  (ArgumentPrinciple.CCL.Basic.NonzeroResult.zeroPersistentRequest result) index current epsilon positive count

/-- Current raw CCL machine of one persistent root state. -/
@[expose] def rootMachine
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (result :
      Multiplicity.CCL.Polynomial.Basic.NonzeroResult p)
    (index : (Multiplicity.CCL.Polynomial.Index.NonzeroResult.RootIndex result)) (state :
      (Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.RootState result) index) :
    Data.CCL.Transducer.Machine :=
  Multiplicity.Side.CCL.Persistent.sidePersistentMachine
    result.rfap.numeratorSites result.numeratorCCL index state

/-- Current exposed finite raw word of one persistent root state. -/
@[expose] def rootWord
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (result :
      Multiplicity.CCL.Polynomial.Basic.NonzeroResult p)
    (index : (Multiplicity.CCL.Polynomial.Index.NonzeroResult.RootIndex result)) (state :
      (Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.RootState result) index) : List.Basic.BinaryWord
      :=
  ((Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.rootMachine result) index state).emitted

/-- Current optional numerical box.  Exact rational roots return `none`;
higher RAT sites return their current nested winding box. -/
@[expose] def rootBox?
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (result :
      Multiplicity.CCL.Polynomial.Basic.NonzeroResult p)
    (index : (Multiplicity.CCL.Polynomial.Index.NonzeroResult.RootIndex result)) (state :
      (Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.RootState result) index) :
    Option Box :=
  Multiplicity.Side.CCL.Persistent.sidePersistentBox?
    result.rfap.numeratorSites result.numeratorCCL index state

/-- Every persistent state retains exact raw-parser semantics for its original
exact site or initial RAT box. -/
theorem rootState_exact
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (result :
      Multiplicity.CCL.Polynomial.Basic.NonzeroResult p)
    (index : (Multiplicity.CCL.Polynomial.Index.NonzeroResult.RootIndex result)) (state :
      (Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.RootState result) index) :
    Data.CCL.Transducer.Machine.Semantics.Basic.ExactCursor
      ((Multiplicity.CCL.Polynomial.Name.NonzeroResult.rootName result) index).process
      ((Multiplicity.CCL.Polynomial.Name.NonzeroResult.rootName result) index).state
      ((Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.rootMachine result) index state) :=
  Multiplicity.Side.CCL.Name.sidePersistentExact
    result.rfap.numeratorSites result.numeratorCCL index state

/-- A root request never retracts an exposed bit. -/
theorem rootRequest_word_extends
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (result :
      Multiplicity.CCL.Polynomial.Basic.NonzeroResult p)
    (index : (Multiplicity.CCL.Polynomial.Index.NonzeroResult.RootIndex result)) (current :
      (Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.RootState result) index)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) (count : Nat) :
    ((Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.rootWord result) index current).IsPrefix
      ((Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.rootWord result) index
        ((Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.rootRequest result) index current epsilon positive
          count)) :=
  (ArgumentPrinciple.CCL.Basic.NonzeroResult.zeroPersistentRequest_word_extends result) index current epsilon positive
    count

/-- A root request appends exactly the requested number of exposed bits. -/
theorem rootRequest_word_length
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (result :
      Multiplicity.CCL.Polynomial.Basic.NonzeroResult p)
    (index : (Multiplicity.CCL.Polynomial.Index.NonzeroResult.RootIndex result)) (current :
      (Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.RootState result) index)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) (count : Nat) :
    ((Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.rootWord result) index
      ((Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.rootRequest result) index current epsilon positive
        count)).length =
        ((Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.rootWord result) index current).length + count :=
  Multiplicity.Side.CCL.Persistent.sidePersistentRequest_word_length
    result.rfap.numeratorSites result.numeratorCCL index current
      epsilon positive count

/-- Exact roots remain exact; a higher root request returns a box nested in
its preceding RAT box. -/
theorem rootRequest_box_refines
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (result :
      Multiplicity.CCL.Polynomial.Basic.NonzeroResult p)
    (index : (Multiplicity.CCL.Polynomial.Index.NonzeroResult.RootIndex result)) (current :
      (Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.RootState result) index)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) (count : Nat) :
    match (Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.rootBox? result) index
        ((Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.rootRequest result) index current epsilon positive
          count),
      (Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.rootBox? result) index current with
    | none, none => True
    | some inner, some outer => inner.Refines outer
    | none, some _ => False
    | some _, none => False :=
  Multiplicity.Side.CCL.Persistent.sidePersistentRequest_box_refines
    result.rfap.numeratorSites result.numeratorCCL index current
      epsilon positive count

/-- A higher root request meets the requested numerical box accuracy; exact
roots require no box. -/
theorem rootRequest_box_accurate
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (result :
      Multiplicity.CCL.Polynomial.Basic.NonzeroResult p)
    (index : (Multiplicity.CCL.Polynomial.Index.NonzeroResult.RootIndex result)) (current :
      (Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.RootState result) index)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) (count : Nat) :
    match (Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.rootBox? result) index
      ((Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.rootRequest result) index current epsilon positive count)
        with
    | none => True
    | some box => box.diagonalSq ≤ epsilon ^ 2 :=
  (ArgumentPrinciple.CCL.Basic.NonzeroResult.zeroPersistentRequest_box_accurate result) index current epsilon positive
    count

/-- The projective CCL sidecar after a root request has pairwise squared
diameter at most `epsilon ^ 2`. -/
theorem rootRequest_cylinder_accurate
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (result :
      Multiplicity.CCL.Polynomial.Basic.NonzeroResult p)
    (index : (Multiplicity.CCL.Polynomial.Index.NonzeroResult.RootIndex result)) (current :
      (Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.RootState result) index)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) (count : Nat)
    {left right : Gaussian.Basic.Canonical}
    (leftPossible :
      Data.CCL.Transducer.Mode.Semantics.SemanticMode.possible
        ((Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.rootMachine result) index
          ((Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.rootRequest result) index current epsilon positive
            count)).mode left)
    (rightPossible :
      Data.CCL.Transducer.Mode.Semantics.SemanticMode.possible
        ((Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.rootMachine result) index
          ((Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.rootRequest result) index current epsilon positive
            count)).mode right) :
    Geometry.Projective.Chordal.Basic.chordalSq
        (Data.CCL.Progressive.Cursor.Image.Machine.image
          ((Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.rootMachine result) index
            ((Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.rootRequest result) index current epsilon positive
              count)) left)
        (Data.CCL.Progressive.Cursor.Image.Machine.image
          ((Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.rootMachine result) index
            ((Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.rootRequest result) index current epsilon positive
              count)) right) ≤
      epsilon ^ 2 :=
  (ArgumentPrinciple.CCL.Basic.NonzeroResult.zeroPersistentRequest_cylinder_accurate result) index current epsilon
    positive count leftPossible rightPossible
end NonzeroResult

end Purelib.RootIsolation.Multiplicity.CCL.Polynomial.Persistent

end
