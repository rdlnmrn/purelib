module
import Purelib.Data.Rat.Fraction
import Purelib.Data.CCL.Progressive.Cursor.Image
import Purelib.Data.CCL.Transducer.Mode.Semantics
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side
import Purelib.RootIsolation.Multiplicity.Observation.Basic
import Purelib.RootIsolation.Multiplicity.Observation.CCL.Basic
import Purelib.RootIsolation.Multiplicity.Observation.CCL.Numerical
import Purelib.RootIsolation.Multiplicity.Observation.CCL.Persistent.Basic
public import Purelib.RootIsolation.Multiplicity.Observation.CCL.Persistent.Request
import Purelib.RootIsolation.Multiplicity.Observation.Index
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Data.CCL.Progressive.Cursor.Request
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.RootIsolation.Multiplicity.Observation.CCL.Name

open Purelib

open Purelib.Data

open Purelib.Data.Rat

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

namespace Purelib.RootIsolation.Multiplicity.Observation.CCL.Persistent.Contract

/-- A persistent site request extends the exact previously emitted CCL word. -/
theorem observationPersistentRequest_word_extends
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {input : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput source opposite}
    {context : Dense.Gaussian.Multiplicity.Basis.Context.Basic.PositiveContext input.entries}
    (observation :
      Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput.FactorObservation input context)
    (data : Multiplicity.Observation.CCL.Basic.ObservationCCL observation)
    (index : Multiplicity.Observation.Index.ObservationIndex observation)
    (current : Multiplicity.Observation.CCL.Persistent.Basic.ObservationPersistentState observation data index)
    (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) (count : Nat) :
    current.cursor.machine.emitted.IsPrefix
      (Multiplicity.Observation.CCL.Persistent.Request.observationPersistentRequest observation data index current
        epsilon
        positive count).cursor.machine.emitted := by
  exact current.cursor.request_extends (epsilon ^ 2)
    (Fraction.Order.Arithmetic.pow_pos_direct positive 2) count

/-- A persistent site request emits exactly the requested number of additional bits. -/
theorem observationPersistentRequest_word_length
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {input : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput source opposite}
    {context : Dense.Gaussian.Multiplicity.Basis.Context.Basic.PositiveContext input.entries}
    (observation :
      Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput.FactorObservation input context)
    (data : Multiplicity.Observation.CCL.Basic.ObservationCCL observation)
    (index : Multiplicity.Observation.Index.ObservationIndex observation)
    (current : Multiplicity.Observation.CCL.Persistent.Basic.ObservationPersistentState observation data index)
    (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) (count : Nat) :
    (Multiplicity.Observation.CCL.Persistent.Request.observationPersistentRequest observation data index current epsilon
      positive count).cursor.machine.emitted.length =
        current.cursor.machine.emitted.length + count := by
  exact current.cursor.request_length (epsilon ^ 2)
    (Fraction.Order.Arithmetic.pow_pos_direct positive 2) count

/-- Uniform optional-box contract: exact rational sites remain exact, while
higher sites return a box nested in the preceding displayed box. -/
theorem observationPersistentRequest_box_refines
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {input : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput source opposite}
    {context : Dense.Gaussian.Multiplicity.Basis.Context.Basic.PositiveContext input.entries}
    (observation :
      Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput.FactorObservation input context)
    (data : Multiplicity.Observation.CCL.Basic.ObservationCCL observation)
    (index : Multiplicity.Observation.Index.ObservationIndex observation)
    (current : Multiplicity.Observation.CCL.Persistent.Basic.ObservationPersistentState observation data index)
    (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) (count : Nat) :
    match Multiplicity.Observation.CCL.Numerical.observationNumericalBox? observation data index
        (Multiplicity.Observation.CCL.Persistent.Request.observationPersistentRequest observation data index current
          epsilon
          positive count).numerical,
      Multiplicity.Observation.CCL.Numerical.observationNumericalBox? observation data index current.numerical with
    | none, none => True
    | some inner, some outer => inner.Refines outer
    | none, some _ => False
    | some _, none => False := by
  cases observation with
  | exact root degree oppositeAtRoot => exact True.intro
  | higher boxes degree =>
      exact (data.trackAt index).nested current.numerical epsilon positive

/-- Uniform optional-box accuracy contract. -/
theorem observationPersistentRequest_box_accurate
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {input : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput source opposite}
    {context : Dense.Gaussian.Multiplicity.Basis.Context.Basic.PositiveContext input.entries}
    (observation :
      Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput.FactorObservation input context)
    (data : Multiplicity.Observation.CCL.Basic.ObservationCCL observation)
    (index : Multiplicity.Observation.Index.ObservationIndex observation)
    (current : Multiplicity.Observation.CCL.Persistent.Basic.ObservationPersistentState observation data index)
    (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) (count : Nat) :
    match Multiplicity.Observation.CCL.Numerical.observationNumericalBox? observation data index
      (Multiplicity.Observation.CCL.Persistent.Request.observationPersistentRequest observation data index current
        epsilon
        positive count).numerical with
    | none => True
    | some box => box.diagonalSq ≤ epsilon ^ 2 := by
  cases observation with
  | exact root degree oppositeAtRoot => exact True.intro
  | higher boxes degree =>
      exact (data.trackAt index).accurate current.numerical epsilon positive

/-- Any two possible points in the requested CCL cylinder have squared chordal distance at most the squared requested
tolerance. -/
theorem observationPersistentRequest_cylinder_accurate
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {input : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput source opposite}
    {context : Dense.Gaussian.Multiplicity.Basis.Context.Basic.PositiveContext input.entries}
    (observation :
      Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput.FactorObservation input context)
    (data : Multiplicity.Observation.CCL.Basic.ObservationCCL observation)
    (index : Multiplicity.Observation.Index.ObservationIndex observation)
    (current : Multiplicity.Observation.CCL.Persistent.Basic.ObservationPersistentState observation data index)
    (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) (count : Nat)
    {left right : Gaussian.Basic.Canonical}
    (leftPossible :
      Data.CCL.Transducer.Mode.Semantics.SemanticMode.possible
        (Multiplicity.Observation.CCL.Persistent.Request.observationPersistentRequest observation data index current
          epsilon
          positive count).cursor.machine.mode left)
    (rightPossible :
      Data.CCL.Transducer.Mode.Semantics.SemanticMode.possible
        (Multiplicity.Observation.CCL.Persistent.Request.observationPersistentRequest observation data index current
          epsilon
          positive count).cursor.machine.mode right) :
    Geometry.Projective.Chordal.Basic.chordalSq
        (Data.CCL.Progressive.Cursor.Image.Machine.image
          (Multiplicity.Observation.CCL.Persistent.Request.observationPersistentRequest observation data index current
            epsilon
            positive count).cursor.machine left)
        (Data.CCL.Progressive.Cursor.Image.Machine.image
          (Multiplicity.Observation.CCL.Persistent.Request.observationPersistentRequest observation data index current
            epsilon
            positive count).cursor.machine right) ≤ epsilon ^ 2 := by
  exact current.cursor.request_pair_chordalSq_le (epsilon ^ 2)
    (Fraction.Order.Arithmetic.pow_pos_direct positive 2) count
      leftPossible rightPossible
end Purelib.RootIsolation.Multiplicity.Observation.CCL.Persistent.Contract

end
