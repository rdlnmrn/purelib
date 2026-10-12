module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Riemann.RootContinuation.PreparedNewtonBandBoundary
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedDoubleBoundary
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedBudget
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.RootIsolation.State.Raw
import Purelib.Topology.Polygon.Stokes

import Purelib.Integration.Path.PairedIncrementArea
public import Purelib.Riemann.RootContinuation.PreparedNewtonPairedClosure
import Purelib.RootIsolation.Newton.Band.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedBoundary
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Field
import Mathlib.Order.Basic

open Purelib.Data

public section

/-! A positive area request constructs and certifies the actual two-lap sample.
The actual final root returns operationally to the initial owner. Comparison
with a separate grid primitive bank remains a distinct obligation. -/
namespace Purelib.Riemann.RootContinuation.RequestedNewtonPairedArea
open Purelib.RootIsolation.Newton.Band
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.RootContinuation.NewtonBandBounds (Profile)
open Purelib.Riemann.RootContinuation.NewtonBandDifferentials (DifferentialProfile)
open Purelib.Riemann.RootContinuation.PreparedNewtonPairedBudget (PairedBandSelection)
open Purelib.Riemann.RootContinuation.PreparedNewtonPairedDoubleBoundary (PairedDoubleBoundary)
open Purelib.Riemann.Topology.PreparedBankRootChains (ownerName)
open Purelib.Integration.Path.PairedIncrementArea (traceArea traceArea_eq area_eq_trace)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandBoundary.PreparedBandRequest (boundaryOwner)

variable {genus : Nat} {curve : HyperellipticCurve genus} {first other :
  Differential genus}
  {ambient : Purelib.Geometry.Rational.Box} {current : Purelib.RootIsolation.State.Raw.RawWindingState
    curve.polynomial ambient}
  {profile : Profile curve.squarefree current.box}

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
set_option genInjectivity false in
/-- Paid double-boundary area request for two differential profiles.

Retains a positive internal allowance, one shared band selection and the actual two-traversal boundary, with its cached
squared area bounded by the requested target. -/
structure RequestedPairedArea (left : DifferentialProfile profile first.exponent)
    (right : DifferentialProfile profile other.exponent) (target radius : Fraction.Rational) (sheet : Fin 2) where
  /-- Positive internal target allocated to the paired band selection. -/ allowance : Fraction.Rational
  /-- Strict positivity of the retained internal allowance. -/ positive : 0 < allowance
  /-- Actual shared selection for the two differential profiles. -/ selection : PairedBandSelection left right allowance
    radius
  /-- Actual double traversal from the selected sheet's original boundary owner. -/ boundary : PairedDoubleBoundary
    selection.sourceRequest other
    (boundaryOwner selection.sourceRequest sheet) sheet
  /-- The squared norm of the cached boundary area lies below the requested target. -/ paid :
    Data.Gaussian.Norm.Basic.normSq
    boundary.summary.areaValue ≤ target

constructive_injectivity RequestedPairedArea

namespace RequestedPairedArea
variable {left : DifferentialProfile profile first.exponent} {right : DifferentialProfile profile other.exponent}
  {target radius : Purelib.Data.Rat.Fraction.Rational} {sheet : Fin 2}

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Polynomial in
open Purelib.Riemann.RootContinuation in
/-- Allocate and construct a paid paired double-boundary area request.

Caps the weighted allowance at one, pays the exact factor 34816, and retains the original elimination certificate,
selected sheet and actual boundary owner. -/
@[expose] def build (left : DifferentialProfile profile first.exponent) (right : DifferentialProfile profile
  other.exponent)
    {degreeBound : Nat} (higher : 2 ≤ curve.polynomial.natDegree)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate curve.polynomial degreeBound)
    (positive : 0 < target) (radiusPositive : 0 < radius) (sheet : Fin 2) :
    RequestedPairedArea left right target radius sheet := by
  let allowance := min (1 : Fraction.Rational) (Budget.Weighted.allowance target 34816)
  have weightNonnegative : (0 : Fraction.Rational) ≤ 34816 :=
    Fraction.Cast.Order.natCast_le_direct (m := 0) (n := 34816) (Nat.zero_le _)
  have allowancePositive : 0 < allowance := Rat.Fraction.Order.Basic.lt_min (by decide)
    (Budget.Weighted.allowance_positive positive weightNonnegative)
  have small : allowance ≤ 1 := Rat.Fraction.Order.Basic.min_le_left _ _
  have squared : allowance^2 ≤ allowance := by
    have bound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct small allowancePositive.le
    simpa only [pow_two, mul_one] using bound
  have paid : 34816 * allowance^2 ≤ target :=
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct squared weightNonnegative).trans
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Rat.Fraction.Order.Basic.min_le_right _ _)
        weightNonnegative).trans
        (Budget.Weighted.mul_allowance_le positive.le weightNonnegative))
  let selection := PreparedNewtonPairedBudget.PairedBandSelection.build
    left right higher elimination allowancePositive radiusPositive
  let boundary := PairedDoubleBoundary.build selection.sourceRequest other
    (boundaryOwner selection.sourceRequest sheet) sheet
  have areaBound := selection.double_area_bound boundary
  have areaPaid : Data.Gaussian.Norm.Basic.normSq boundary.summary.areaValue ≤ target := by
    simpa only [Norm.Basic.normSq_eq_canonical] using areaBound.trans paid
  exact ⟨allowance, allowancePositive, selection, boundary, areaPaid⟩

open Purelib.Approximation.Gaussian in
/-- Read the retained double-boundary root closure certificate. -/
@[expose] def roots (requested : RequestedPairedArea left right target radius sheet) :
    Equivalence.NamedEquivalent
      (ownerName requested.boundary.finishOwner)
      (ownerName (boundaryOwner requested.selection.sourceRequest sheet)) :=
  requested.boundary.rootEquivalent

section
open Purelib.Integration.Path
open Purelib.Topology.Polygon
/-- The cached paired area is the zero-origin trace area of its actual increments. -/
theorem area_readback (requested : RequestedPairedArea left right target radius sheet) :
    requested.boundary.summary.areaValue =
      PairedIncrementArea.traceArea Stokes.PrimitivePoint.zero
        (requested.boundary.first.increments ++ requested.boundary.second.increments) :=
  requested.boundary.summary.area_eq.trans (PairedIncrementArea.area_eq_trace _)

/-- Translation adds the original edge-area correction against the cached total.

Keeps the actual two-traversal increment list and separates its cached area from the origin-dependent endpoint term. -/
theorem translated_area_readback (requested : RequestedPairedArea left right target radius sheet)
    (origin : Stokes.PrimitivePoint) :
    PairedIncrementArea.traceArea origin
        (requested.boundary.first.increments ++ requested.boundary.second.increments) =
      requested.boundary.summary.areaValue +
        Stokes.edgeArea origin requested.boundary.summary.totalValue := by
  rw [PairedIncrementArea.traceArea_eq, requested.boundary.summary.area_eq,
    requested.boundary.summary.total_eq]

end

open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
open Purelib.Topology.Polygon in
/-- The translated trace area is paid after removing its endpoint correction.

Uses the exact cached-total translation identity and the request's original area bound. -/
theorem translated_area_paid (requested : RequestedPairedArea left right target radius sheet)
    (origin : Stokes.PrimitivePoint) :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.traceArea origin
        (requested.boundary.first.increments ++ requested.boundary.second.increments) -
      Stokes.edgeArea origin requested.boundary.summary.totalValue) ≤ target := by
  rw [requested.translated_area_readback, add_sub_cancel_right]
  exact requested.paid

end RequestedPairedArea
end Purelib.Riemann.RootContinuation.RequestedNewtonPairedArea
