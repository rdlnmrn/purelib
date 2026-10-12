module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.LinearAlgebra.Gaussian.Energy

public import Purelib.Riemann.RootContinuation.NewtonAutomaticOddRaw
public import Purelib.Riemann.RootContinuation.NewtonAutomaticRegularRaw
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Riemann.RootContinuation.NewtonOddRawRequest
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.OriginalRawRequest
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.LiftedPuncturedGrid

public section

/-! Curve-only raw coercivity for both degree cases on the actual corrected period bank.
The empty genus retains a direct finite certificate and acquires no geometry. -/
namespace Purelib.Riemann.Readings.CurveRawRequest.PairedPeriodBank

open Purelib

open Purelib.Data.Rat

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank (PairedPeriodBank)
open Purelib.Riemann.RootContinuation.NewtonAutomaticOddRaw (AutomaticOddRaw)
open Purelib.Riemann.RootContinuation.NewtonAutomaticRegularRaw (AutomaticRegularRaw)
open Purelib.LinearAlgebra.Gaussian.Energy (unnormalizedEnergyForm)
open Purelib.Riemann.Periods.PeriodMatrix (sampledMatrix)

open Purelib.Curves.Hyperelliptic in
/-- Degree-sensitive retained data for a curve's raw-energy request.

Genus zero uses the unit payload; a positive-genus retained period bank stores either the actual odd or regular
construction, while an empty positive-genus bank is impossible. -/
@[expose] def RawPayload : {genus : Nat} → {curve : Basic.HyperellipticCurve genus} →
  Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank curve → Nat → Type _
  | 0, _, _, _ => PUnit
  | _ + 1, _, .empty _, _ => PEmpty
  | genus + 1, _, .retained prepared, floor =>
      Sum (AutomaticOddRaw prepared ⟨0, Nat.zero_lt_succ genus⟩ floor) (AutomaticRegularRaw prepared floor)

variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
open Purelib.LinearAlgebra.Gaussian in
open Purelib.Riemann.Readings in
/-- Uniform original period-energy lower bound after a retained index.

The positive lower constant multiplies the coefficient squared-norm sum and bounds the original sampled A/B energy at
every later stage. -/
@[expose] def RawAccuracy (bank : Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank curve) (lower :
  Fraction.Rational) (index : Nat) : Prop :=
  ∀ stage, index ≤ stage → ∀ coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus,
    lower * PreparedObservationCoercivity.coefficientNormSq coefficients ≤
      Energy.unnormalizedEnergyForm coefficients
        (sampledMatrix bank.periodData.aMatrix stage) (sampledMatrix bank.periodData.bMatrix stage)

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
set_option genInjectivity false in
/-- Retained curve raw-energy payload with a positive lower bound.

Keeps the actual degree-dependent construction, lower constant and numerical index, with the requested floor and uniform
later-stage accuracy certificate. -/
structure RawRequest (bank : Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank curve) (floor : Nat) where
  /-- Actual genus- and degree-dependent retained construction. -/ payload : RawPayload bank floor
  /-- Positive rational energy lower constant. -/ lower : Fraction.Rational
  /-- Strict positivity of the retained lower constant. -/ lower_positive : 0 < lower
  /-- Numerical index after which the energy certificate holds. -/ index : Nat
  /-- The retained index respects the requested floor. -/ floor_le : floor ≤ index
  /-- Uniform original sampled-period energy bound at every later stage. -/ accurate : RawAccuracy bank lower index

constructive_injectivity RawRequest

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
/-- Construct a raw-energy request for an actual paired period bank.

Handles genus zero directly, eliminates the impossible empty positive-genus case, and retains the original odd or even
degree construction with its exact bound and index. -/
@[expose] def rawRequest : {genus : Nat} → {curve : Basic.HyperellipticCurve genus} → (bank :
  Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank curve) →
    (floor : Nat) → RawRequest bank floor
  | 0, _, _, floor =>
      ⟨PUnit.unit, 1, by decide, floor, Nat.le_refl _, fun _ _ _ => by
        change (1 : Fraction.Rational) * 0 ≤ 0 / 2
        decide⟩
  | genus + 1, _, .empty zero, _ => Fin.elim0 (Fin.cast zero (⟨0, Nat.zero_lt_succ genus⟩ : Fin (genus + 1)))
  | genus + 1, curve, .retained prepared, floor =>
      match curve.degreeShape with
      | .odd degree =>
          let data := AutomaticOddRaw.build prepared degree ⟨0, Nat.zero_lt_succ genus⟩ floor
          ⟨.inl data, data.lower, data.lower_positive, data.request.index, data.request.floor_le,
            fun stage later coefficients => data.accurate stage later coefficients⟩
      | .even degree =>
          let data := AutomaticRegularRaw.build prepared degree floor
          ⟨.inr data, data.lower, data.lower_positive, data.request.index, data.request.floor_le,
            fun stage later coefficients => data.accurate ⟨0, Nat.zero_lt_succ genus⟩ stage later coefficients⟩

end Purelib.Riemann.Readings.CurveRawRequest.PairedPeriodBank

namespace Purelib.Riemann.Readings.CurveRawRequest.ClearGrid

open Purelib.Data.Rat

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank (PairedPeriodBank)
open Purelib.Riemann.Readings.CurveRawRequest.PairedPeriodBank (RawRequest rawRequest)

open Purelib.Curves.Hyperelliptic in
/-- Construct the raw-energy certificate from a curve and stage floor.

Uses the curve's actual constructed paired period bank and retains its degree-sensitive request payload and uniform
energy bound. -/
@[expose] def curveRawRequest {genus : Nat} (curve : Basic.HyperellipticCurve genus) (floor : Nat) :
    RawRequest (Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank.ofCurve curve) floor :=
  rawRequest (Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank.ofCurve curve) floor

end Purelib.Riemann.Readings.CurveRawRequest.ClearGrid
