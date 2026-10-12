module
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.State.Raw

public import Purelib.Riemann.RootContinuation.PreparedNewtonPairedSide
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Riemann.Integration.UniformPrimitiveNeighborhoods
import Purelib.RootIsolation.Newton.Band.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Topology.Polygon.Stokes
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Gaussian.Field
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedBank
import Mathlib.Order.Basic

@[expose] public section

/-! One selected Newton band pays both differential densities together. -/
namespace Purelib.Riemann.RootContinuation.PreparedNewtonPairedBudget
open Purelib.RootIsolation.Newton.Band
open Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples (PreparedBandRequest PreparedBandSelection)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples.Sample (preparedDensity preparedDensity_movement_le
  preparedDensity_nonnegative)
open Purelib.Riemann.RootContinuation.PreparedNewtonPairedSide (PairedBoundarySide)
open Purelib.Riemann.RootContinuation.NewtonBandBounds (Profile)
open Purelib.Riemann.RootContinuation.NewtonBandDifferentials (DifferentialProfile)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_nonneg)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)

variable {genus : Nat} {curve : HyperellipticCurve genus} {first other :
  Differential genus}
  {ambient : Purelib.Geometry.Rational.Box} {current : Purelib.RootIsolation.State.Raw.RawWindingState
    curve.polynomial ambient}
  {profile : Profile curve.squarefree current.box}

open Purelib.Data.Rat in
/-- One band selection paid for two differential profiles.

The selection retains the sum of the two original rate weights, together with the requested target and radius. -/
abbrev PairedBandSelection (left : DifferentialProfile profile first.exponent)
    (right : DifferentialProfile profile other.exponent) (target radius : Fraction.Rational) :=
  PreparedBandSelection profile ((2 * left.rate + 256) + (2 * right.rate + 256)) target radius

namespace PairedBandSelection
variable {left : DifferentialProfile profile first.exponent} {right : DifferentialProfile profile other.exponent}
  {target radius : Purelib.Data.Rat.Fraction.Rational}

open Purelib.Data.Rat in
open Purelib.Polynomial in
open Purelib.Riemann.RootContinuation in
/-- Acquire the paired band selection from a certified elimination and positive budgets.

Uses the original polynomial degree bound and both differential rate nonnegativity certificates to retain one shared
prepared sample. -/
def build (left : DifferentialProfile profile first.exponent) (right : DifferentialProfile profile other.exponent)
    {degreeBound : Nat} (higher : 2 ≤ curve.polynomial.natDegree)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate curve.polynomial degreeBound)
    (positive : 0 < target) (radiusPositive : 0 < radius) : PairedBandSelection left right target radius :=
  PreparedNewtonBandSamples.Profile.requestPreparation profile higher elimination _
    (add_nonneg
      (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) left.rate_nonnegative) (by decide +kernel))
      (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) right.rate_nonnegative) (by decide +kernel)))
        positive radiusPositive

open Purelib.Data.Rat in
/-- View the paired selection as a request for its first differential.

Uses nonnegativity of the second rate weight without changing the selected sample or target. -/
def sourceRequest (selection : PairedBandSelection left right target radius) : PreparedBandRequest left target :=
  selection.forDifferential left (le_add_of_nonneg_right
    (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) right.rate_nonnegative) (by decide +kernel)))

/-- The two retained differential densities jointly fit the requested target.

Adds the original density-movement bounds and uses the selection's payment at thirty-two times the squared output
radius. -/
theorem densities_paid (selection : PairedBandSelection left right target radius) :
    (preparedDensity selection.sample left selection.error +
      preparedDensity selection.sample right selection.error) * (32 * selection.sample.output.radius^2) ≤ target := by
  have bounds := add_le_add
    (preparedDensity_movement_le selection.sample left selection.error_le_one selection.radius_le_one)
    (preparedDensity_movement_le selection.sample right selection.error_le_one selection.radius_le_one)
  rw [← add_mul, ← add_mul] at bounds
  exact bounds.trans selection.paid

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Polynomial in
open Purelib.Riemann.Topology in
/-- Bound a retained paired side area by sixteen times the squared target.

Uses the actual segment endpoints inside the selected band, its diagonal bound and the joint density payment without
changing the cached side summary. -/
theorem side_area_bound (selection : PairedBandSelection left right target radius)
    {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial selection.sample.output.box start finish}
    {within : segment.WithinAmbient}
    {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {sheet : Fin 2}
    (side : PairedBoundarySide selection.sourceRequest other segment within owner sheet) :
    Data.Gaussian.Norm.Basic.normSq side.summary.areaValue ≤ 16 * target^2 := by
  have firstInside : selection.sample.output.box.Contains start := by
    simpa only [Geometry.ClearPath.ClearSegment.pointAt_zero] using segment.pointAt_contains within 0 (by decide)
  have lastInside : selection.sample.output.box.Contains finish := by
    simpa only [Geometry.ClearPath.ClearSegment.pointAt_one] using segment.pointAt_contains within 1 (by decide)
  have movement := (selection.sample.output.box.normSq_sub_le_diagonalSq lastInside firstInside).trans
    (selection.sample.output.band.diagonalSq_le selection.sample.output.radiusPositive)
  rw [Norm.Basic.normSq_eq_canonical] at movement
  have nonnegative := add_nonneg
    (preparedDensity_nonnegative selection.sample left selection.errorPositive.le)
    (preparedDensity_nonnegative selection.sample right selection.errorPositive.le)
  have paid := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct movement nonnegative).trans
    selection.densities_paid
  have scalar := (side.area_density_bound right).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.pow_le_pow_direct (Fraction.Order.Arithmetic.mul_nonneg_direct nonnegative
        (Basic.Canonical.normSq_nonneg (finish - start))) paid 2) (by decide))
  rw [← Norm.Basic.normSq_eq_canonical] at scalar
  exact scalar

end PairedBandSelection
end Purelib.Riemann.RootContinuation.PreparedNewtonPairedBudget
