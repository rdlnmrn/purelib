module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Table.Reading
public import Purelib.Calculus.Jet.Progressive.Multivariable.First
public import Purelib.LinearAlgebra.Gaussian.List.InnerProduct.Error

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Norm.Basic

section
@[expose] public section

/-!
# Finite error transport for progressive Taylor tables

The progressive higher-jet layer emits every displayed coefficient.  This
module transports those finitely many coefficient allowances through Horner
evaluation and through an explicit finite truncation.  The bounds are coarse
recursive rational expressions; no omitted infinite tail or formal power
series is introduced.
-/

namespace Purelib.Calculus.Jet.Progressive.Multivariable.Error.MultivariableFirstJet

open Purelib.Approximation.Gaussian in
open Purelib.Data in
open Purelib.LinearAlgebra.Gaussian.List.InnerProduct in
open Purelib.Calculus.Jet.Progressive.Multivariable.First in
/-- Bound directional evaluation error for one finite table of shared channel readings.

A positive target and SharedReadingsPossible evidence control every displayed reading relative to its shared center. The
two length equalities align the readings, direction and retained partial channels; the finite directional error budget
bounds their evaluation difference. -/
theorem directional_evaluation_error
    (jet : MultivariableFirstJet)
    (readings direction : List Gaussian.Basic.Canonical) (target : Rat.Fraction.Rational)
    (positive : 0 < target)
    (readingLength : readings.length = direction.length)
    (directionLength : direction.length = jet.partials.length)
    (possible : Table.Reading.SharedReadingsPossible jet.partials jet.partials readings
      target positive) :
    Gaussian.Norm.Basic.normSq (Error.directionalEval readings direction -
        Error.directionalEval
          (Table.Reading.sharedCenters jet.partials jet.partials target positive) direction) ≤
      Error.directionalErrorBudget direction target := by
  apply Error.directional_error_le readings
    (Table.Reading.sharedCenters jet.partials jet.partials target positive) direction target
    readingLength
  · unfold Table.Reading.sharedCenters
    exact (List.Map.length_map _ jet.partials).trans directionLength.symm
  · exact Table.Reading.sharedReadings_close jet.partials jet.partials readings target
      positive possible

end Purelib.Calculus.Jet.Progressive.Multivariable.Error.MultivariableFirstJet

end
