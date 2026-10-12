module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Exponential.Horner.Sample
import Purelib.Approximation.Gaussian.Exponential.Taylor.Integral
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.RationalEmbedding.Bounds
public import Purelib.Integration.Exponential.Polynomial.Source
public import Purelib.Integration.Partition.Affine
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
public import Purelib.Integration.Polynomial.Gaussian.Partition.Child
import Purelib.Polynomial.Ascending.Gaussian.Evaluation
import Purelib.Data.Gaussian.RationalEmbedding
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Ascending.Gaussian.Restriction.Cached
import Purelib.Integration.Partition.Interval
import Purelib.Integration.Polynomial.Gaussian.Segment.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Integration.Partition.Unit.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Integration.Polynomial.Gaussian.Partition (Child)

section
@[expose] public section

/-!
# Observed, cached exponential polynomial cells

Every cell retains its generated affine coefficient restriction and exact
integral sample.  The observations are actual later finite exponential
readings at displayed rational parameters; they are not evidence about an
unspecified integrand.  Endpoint observations make each generated list
nonempty, and the general constructor supports every displayed unit parameter.
-/

namespace Purelib.Integration.Exponential.Cell.Observation

open Purelib.Approximation.Gaussian in
open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Exponential in
open Purelib.Integration.Partition in
open Purelib.Integration.Polynomial in
open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Polynomial.Ascending in
/-- Retain a later Horner exponential reading and its certified error against the exact restricted Taylor polynomial.

The original child interval is valid, the local parameter lies in the unit interval, and the reading depth is the
polynomial depth plus the extra depth plus one. -/
def observation {depth : Nat} (child :
  Child (Polynomial.Source.source depth)) (valid : child.interval.Valid)
    (localParameter : Fraction.Rational) (nonnegative : 0 ≤ localParameter)
    (bounded : localParameter ≤ 1) (extraDepth : Nat) :
    Basic.LocalObservation child.restriction.polynomial
      (Geometric.Basic.quarterRadius 10 depth) :=
  let reading := Exponential.Horner.Sample.sample (RationalEmbedding.parameter (Affine.sourceParameter child.interval
    localParameter))
    (depth + extraDepth + 1)
  let error := reading - Gaussian.Evaluation.eval child.restriction.polynomial (RationalEmbedding.parameter
    localParameter)
  { parameter := localParameter
    integrandReading := reading
    error := error
    decomposition := rfl
    error_le := by
      dsimp only [error, reading]
      rw [child.restriction.eval_eq, ← Affine.parameter_sourceParameter]
      change Basic.Canonical.normSq (Exponential.Horner.Sample.sample (RationalEmbedding.parameter
        (Affine.sourceParameter child.interval localParameter))
        (depth + extraDepth + 1) - Gaussian.Evaluation.eval
          (Exponential.Taylor.Integral.polynomial depth)
            (RationalEmbedding.parameter (Affine.sourceParameter child.interval localParameter))) ≤ _
      rw [Exponential.Taylor.Integral.eval_polynomial]
      have bounds := Affine.sourceParameter_bounds valid nonnegative bounded
      have unit : Data.Gaussian.Norm.Basic.normSq (RationalEmbedding.parameter (Affine.sourceParameter child.interval
        localParameter)) ≤ 1 := by
        rw [Norm.Basic.normSq_eq_canonical]
        exact RationalEmbedding.Bounds.unit_parameter bounds.1 bounds.2
      have scalar := Exponential.Horner.Sample.sample_later_close
        (RationalEmbedding.parameter (Affine.sourceParameter child.interval localParameter)) unit
        (earlier := depth) (later := depth + extraDepth + 1) (by omega)
      rw [Norm.Basic.normSq_eq_canonical] at scalar
      exact scalar }

open Purelib.Approximation.Rational in
open Purelib.Integration.Exponential in
open Purelib.Integration.Polynomial in
open Purelib.Integration.Polynomial.Gaussian.Cell in
/-- Build the original restricted exponential cell with its exact polynomial and two retained endpoint observations.

The cell keeps its original segment endpoints and quarter-radius allowance; the extra reading depth affects observations
while preserving the exact polynomial sample. -/
def cell {depth : Nat} (child :
  Child
  (Polynomial.Source.source depth)) (valid : child.interval.Valid)
    (extraDepth : Nat) : Basic.CellModel :=
  { start := (Polynomial.Source.source depth).point child.interval.start
    finish := (Polynomial.Source.source depth).point child.interval.finish
    polynomial := child.restriction.polynomial
    localAllowance := Geometric.Basic.quarterRadius 10 depth
    localAllowance_nonneg := Geometric.Basic.quarterRadius_nonneg (by decide) depth
    observations := [observation child valid 0 (by decide) (by decide) extraDepth,
      observation child valid 1 (by decide) (by decide) extraDepth] }

open Purelib.Integration.Exponential
open Purelib.Integration.Polynomial
/-- The observed exponential cell retains exactly two endpoint observations. -/
theorem cell_observation_count {depth : Nat} (child :
  Child (Polynomial.Source.source depth))
    (valid : child.interval.Valid) (extraDepth : Nat) :
    (cell child valid extraDepth).observations.length = 2 := rfl

/-- The observed exponential cell has the exact original restricted child's cached sample. -/
theorem cell_sample {depth : Nat} (child :
  Child (Polynomial.Source.source depth))
    (valid : child.interval.Valid) (extraDepth : Nat) :
    (cell child valid extraDepth).integralSample = child.sample := by
  rw [child.sample_eq, child.restriction.sample_eq]
  rfl
end Purelib.Integration.Exponential.Cell.Observation

end
