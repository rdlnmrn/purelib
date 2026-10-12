module
import Purelib.Approximation.Rational.Geometric.Basic
public import Purelib.Integration.Exponential.Cell.Observation
import Purelib.Integration.Exponential.Polynomial.Source
public import Purelib.Integration.Partition.QuadraticWeight
import Purelib.Integration.Polynomial.Gaussian.Partition.Child
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Integration.Polynomial.Gaussian.Cell.Allowance
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Integration.Partition.Unit.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Tactic.Ring

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

namespace Purelib.Integration.Exponential.Cell.Allowance

open Purelib.Data.Gaussian in
open Purelib.Integration.Exponential in
open Purelib.Integration.Partition in
open Purelib.Integration.Polynomial in
/-- The observed exponential cell's displacement squared norm equals its original interval's quadratic weight. -/
theorem cell_displacement_norm {depth : Nat} (child :
  Integration.Polynomial.Gaussian.Partition.Child (Polynomial.Source.source depth))
    (valid : child.interval.Valid) (extraDepth : Nat) :
    Basic.Canonical.normSq (Cell.Observation.cell child valid extraDepth).displacement = QuadraticWeight.intervalWeight
      child.interval := by
  change Basic.Canonical.normSq ((Polynomial.Source.source depth).point child.interval.finish -
    (Polynomial.Source.source depth).point child.interval.start) = _
  rw [Polynomial.Source.source_point, Polynomial.Source.source_point]
  change (child.interval.finish - child.interval.start) * (child.interval.finish - child.interval.start) + (0 - 0) * (0
    - 0) = _
  unfold QuadraticWeight.intervalWeight
  ring1

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Integration.Exponential in
open Purelib.Integration.Partition in
open Purelib.Integration.Polynomial in
/-- The observed cell's weighted allowance is its retained interval weight times the original polynomial-depth quarter
radius. -/
theorem cell_weightedAllowance {depth : Nat} (child :
  Integration.Polynomial.Gaussian.Partition.Child (Polynomial.Source.source depth))
    (valid : child.interval.Valid) (extraDepth : Nat) :
    (Cell.Observation.cell child valid extraDepth).weightedAllowance =
      QuadraticWeight.intervalWeight child.interval * Geometric.Basic.quarterRadius 10 depth := by
  change Basic.Canonical.normSq (Cell.Observation.cell child valid extraDepth).displacement *
    Geometric.Basic.quarterRadius 10 depth = _
  rw [cell_displacement_norm]
end Purelib.Integration.Exponential.Cell.Allowance

end
