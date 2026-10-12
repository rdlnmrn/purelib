module
import Purelib.Data.Rat.Fraction
import Purelib.Data.CCL.Progressive.Cursor.Image
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.CCL.Transducer.Mode.Semantics
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RootIsolation.Multiplicity.Observation.CCL.Numerical
import Purelib.RootIsolation.Multiplicity.Observation.CCL.Persistent.Basic
import Purelib.RootIsolation.Multiplicity.Observation.CCL.Persistent.Contract
public import Purelib.RootIsolation.Multiplicity.Observation.CCL.Persistent.Request
import Purelib.RootIsolation.Multiplicity.Side.Basic
public import Purelib.RootIsolation.Multiplicity.Side.CCL.Basic
public import Purelib.RootIsolation.Multiplicity.Side.Index
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Data.CCL.Progressive.Cursor.Request
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side
import Purelib.RootIsolation.Multiplicity.Family.Basic
import Purelib.RootIsolation.Multiplicity.Observation.CCL.Name
import Purelib.RootIsolation.Multiplicity.Observation.Index

open Purelib

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
public section

/-!
# CCL-2 data for the rational-function argument principle

Paper I returns exact rational sites or independently shrinking zero/pole
tracks after finite cancellation.  This module adds CCL observations to those
existing results without duplicating any RFAP isolation or winding proof.
-/

namespace Purelib.RootIsolation.Multiplicity.Side.CCL.Persistent

/-- Persistent state at any exact or higher site on one reduced cofactor
side. -/
@[expose] def SidePersistentState
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (side : Multiplicity.Side.Basic.SideResult source opposite)
    (data : Multiplicity.Side.CCL.Basic.SideCCL side) (index : Multiplicity.Side.Index.SideIndex side) : Type 1 := by
  cases side with
  | constant sourceNonzero degreeZero oppositeNonzero => exact nomatch index
  | positive input family =>
      exact Multiplicity.Observation.CCL.Persistent.Basic.ObservationPersistentState (family.observationAt index.1)
        (data index.1) index.2

/-- Initialize the persistent numerical state and CCL cursor at the supplied original side-site index. -/
@[expose] def sidePersistentInitial
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (side : Multiplicity.Side.Basic.SideResult source opposite)
    (data : Multiplicity.Side.CCL.Basic.SideCCL side) (index : Multiplicity.Side.Index.SideIndex side) :
    Multiplicity.Side.CCL.Persistent.SidePersistentState side data index := by
  cases side with
  | constant sourceNonzero degreeZero oppositeNonzero => exact nomatch index
  | positive input family =>
      exact Multiplicity.Observation.CCL.Persistent.Basic.observationPersistentInitial (family.observationAt index.1)
        (data index.1) index.2

/-- Refine the same retained side site and advance its CCL cursor by the requested number of bits.

Exact and higher sites keep their original dependent index and observation attachment; higher numerical boxes meet the
positive tolerance. -/
@[expose] def sidePersistentRequest
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (side : Multiplicity.Side.Basic.SideResult source opposite)
    (data : Multiplicity.Side.CCL.Basic.SideCCL side) (index : Multiplicity.Side.Index.SideIndex side)
    (current : Multiplicity.Side.CCL.Persistent.SidePersistentState side data index)
    (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) (count : Nat) :
    Multiplicity.Side.CCL.Persistent.SidePersistentState side data index := by
  cases side with
  | constant sourceNonzero degreeZero oppositeNonzero => exact nomatch index
  | positive input family =>
      exact Multiplicity.Observation.CCL.Persistent.Request.observationPersistentRequest (family.observationAt index.1)
        (data index.1) index.2 current epsilon positive count

/-- Read the exact CCL machine retained by the indexed persistent side state. -/
@[expose] def sidePersistentMachine
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (side : Multiplicity.Side.Basic.SideResult source opposite)
    (data : Multiplicity.Side.CCL.Basic.SideCCL side) (index : Multiplicity.Side.Index.SideIndex side)
    (state : Multiplicity.Side.CCL.Persistent.SidePersistentState side data index) :
    Data.CCL.Transducer.Machine := by
  cases side with
  | constant sourceNonzero degreeZero oppositeNonzero => exact nomatch index
  | positive input family => exact state.cursor.machine

/-- Read the retained numerical box of a higher site, or no box for an exact site. -/
@[expose] def sidePersistentBox?
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (side : Multiplicity.Side.Basic.SideResult source opposite)
    (data : Multiplicity.Side.CCL.Basic.SideCCL side) (index : Multiplicity.Side.Index.SideIndex side)
    (state : Multiplicity.Side.CCL.Persistent.SidePersistentState side data index) : Option Box := by
  cases side with
  | constant sourceNonzero degreeZero oppositeNonzero => exact nomatch index
  | positive input family =>
      exact Multiplicity.Observation.CCL.Numerical.observationNumericalBox? (family.observationAt index.1)
        (data index.1) index.2 state.numerical

/-- A persistent side-site request extends the previously emitted CCL word. -/
theorem sidePersistentRequest_word_extends
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (side : Multiplicity.Side.Basic.SideResult source opposite)
    (data : Multiplicity.Side.CCL.Basic.SideCCL side) (index : Multiplicity.Side.Index.SideIndex side)
    (current : Multiplicity.Side.CCL.Persistent.SidePersistentState side data index)
    (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) (count : Nat) :
    (Multiplicity.Side.CCL.Persistent.sidePersistentMachine side data index current).emitted.IsPrefix
      (Multiplicity.Side.CCL.Persistent.sidePersistentMachine side data index
        (Multiplicity.Side.CCL.Persistent.sidePersistentRequest side data index current epsilon positive count)).emitted
          := by
  cases side with
  | constant sourceNonzero degreeZero oppositeNonzero => exact nomatch index
  | positive input family =>
      exact Multiplicity.Observation.CCL.Persistent.Contract.observationPersistentRequest_word_extends
        (family.observationAt index.1) (data index.1) index.2 current
          epsilon positive count

/-- A persistent side-site request emits exactly the requested number of additional bits. -/
theorem sidePersistentRequest_word_length
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (side : Multiplicity.Side.Basic.SideResult source opposite)
    (data : Multiplicity.Side.CCL.Basic.SideCCL side) (index : Multiplicity.Side.Index.SideIndex side)
    (current : Multiplicity.Side.CCL.Persistent.SidePersistentState side data index)
    (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) (count : Nat) :
    (Multiplicity.Side.CCL.Persistent.sidePersistentMachine side data index
      (Multiplicity.Side.CCL.Persistent.sidePersistentRequest side data index current epsilon positive
        count)).emitted.length =
        (Multiplicity.Side.CCL.Persistent.sidePersistentMachine side data index current).emitted.length + count := by
  cases side with
  | constant sourceNonzero degreeZero oppositeNonzero => exact nomatch index
  | positive input family =>
      exact Multiplicity.Observation.CCL.Persistent.Contract.observationPersistentRequest_word_length
        (family.observationAt index.1) (data index.1) index.2 current
          epsilon positive count

/-- Exact side sites remain exact, and each requested higher-site box refines its retained predecessor. -/
theorem sidePersistentRequest_box_refines
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (side : Multiplicity.Side.Basic.SideResult source opposite)
    (data : Multiplicity.Side.CCL.Basic.SideCCL side) (index : Multiplicity.Side.Index.SideIndex side)
    (current : Multiplicity.Side.CCL.Persistent.SidePersistentState side data index)
    (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) (count : Nat) :
    match Multiplicity.Side.CCL.Persistent.sidePersistentBox? side data index
        (Multiplicity.Side.CCL.Persistent.sidePersistentRequest side data index current epsilon positive count),
      Multiplicity.Side.CCL.Persistent.sidePersistentBox? side data index current with
    | none, none => True
    | some inner, some outer => inner.Refines outer
    | none, some _ => False
    | some _, none => False := by
  cases side with
  | constant sourceNonzero degreeZero oppositeNonzero => exact nomatch index
  | positive input family =>
      exact Multiplicity.Observation.CCL.Persistent.Contract.observationPersistentRequest_box_refines
        (family.observationAt index.1) (data index.1) index.2 current
          epsilon positive count

/-- The retained higher-site box has squared diagonal at most the requested tolerance squared. -/
theorem sidePersistentRequest_box_accurate
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (side : Multiplicity.Side.Basic.SideResult source opposite)
    (data : Multiplicity.Side.CCL.Basic.SideCCL side) (index : Multiplicity.Side.Index.SideIndex side)
    (current : Multiplicity.Side.CCL.Persistent.SidePersistentState side data index)
    (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) (count : Nat) :
    match Multiplicity.Side.CCL.Persistent.sidePersistentBox? side data index
      (Multiplicity.Side.CCL.Persistent.sidePersistentRequest side data index current epsilon positive count) with
    | none => True
    | some box => box.diagonalSq ≤ epsilon ^ 2 := by
  cases side with
  | constant sourceNonzero degreeZero oppositeNonzero => exact nomatch index
  | positive input family =>
      exact Multiplicity.Observation.CCL.Persistent.Contract.observationPersistentRequest_box_accurate
        (family.observationAt index.1) (data index.1) index.2 current
          epsilon positive count

/-- The requested side-site CCL cylinder has squared chordal diameter at most the requested tolerance squared. -/
theorem sidePersistentRequest_cylinder_accurate
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (side : Multiplicity.Side.Basic.SideResult source opposite)
    (data : Multiplicity.Side.CCL.Basic.SideCCL side) (index : Multiplicity.Side.Index.SideIndex side)
    (current : Multiplicity.Side.CCL.Persistent.SidePersistentState side data index)
    (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) (count : Nat)
    {left right : Gaussian.Basic.Canonical}
    (leftPossible :
      Data.CCL.Transducer.Mode.Semantics.SemanticMode.possible
        (Multiplicity.Side.CCL.Persistent.sidePersistentMachine side data index
          (Multiplicity.Side.CCL.Persistent.sidePersistentRequest side data index current epsilon positive count)).mode
        left)
    (rightPossible :
      Data.CCL.Transducer.Mode.Semantics.SemanticMode.possible
        (Multiplicity.Side.CCL.Persistent.sidePersistentMachine side data index
          (Multiplicity.Side.CCL.Persistent.sidePersistentRequest side data index current epsilon positive count)).mode
        right) :
    Geometry.Projective.Chordal.Basic.chordalSq
        (Data.CCL.Progressive.Cursor.Image.Machine.image
          (Multiplicity.Side.CCL.Persistent.sidePersistentMachine side data index
            (Multiplicity.Side.CCL.Persistent.sidePersistentRequest side data index current epsilon positive count))
          left)
        (Data.CCL.Progressive.Cursor.Image.Machine.image
          (Multiplicity.Side.CCL.Persistent.sidePersistentMachine side data index
            (Multiplicity.Side.CCL.Persistent.sidePersistentRequest side data index current epsilon positive count))
          right) ≤ epsilon ^ 2 := by
  cases side with
  | constant sourceNonzero degreeZero oppositeNonzero => exact nomatch index
  | positive input family =>
      exact Multiplicity.Observation.CCL.Persistent.Contract.observationPersistentRequest_cylinder_accurate
        (family.observationAt index.1) (data index.1) index.2 current
          epsilon positive count leftPossible rightPossible
end Purelib.RootIsolation.Multiplicity.Side.CCL.Persistent

end
