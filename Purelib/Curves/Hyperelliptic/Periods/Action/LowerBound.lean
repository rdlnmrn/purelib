module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.LinearAlgebra.Gaussian.Energy

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Riemann.Readings.CurveRawRequest
public import Purelib.Riemann.Readings.NamedMatrixActionBound
import Purelib.Riemann.Integration.RawActionLower
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Data.Rat

open Purelib.LinearAlgebra.Gaussian

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Integration

open Purelib.Riemann.Periods

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.NamedMatrixActionBound

public section

/-! Quantitative A-action separation on the actual corrected raw tail. -/
namespace Purelib.Curves.Hyperelliptic.Periods.Action.LowerBound

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Readings.NamedMatrixActionBound (UniformActionBound)
open Purelib.Riemann.Periods.PeriodMatrix (sampledMatrix)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank (PairedPeriodBank)
open Purelib.Riemann.Readings.CurveRawRequest.PairedPeriodBank (RawRequest)
open Purelib.LinearAlgebra.Gaussian.Energy (periodCombination)
open Purelib.Riemann.Integration.RawActionLower (a_action_lower)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {bank :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank curve} {floor : Nat}
  (request : Purelib.Riemann.Readings.CurveRawRequest.PairedPeriodBank.RawRequest bank floor)

set_option genInjectivity false in
/-- Retain the B-sample bound and the resulting positive A-action constant on the same raw request. -/
structure ActionLower where
  /-- The retained uniform action bound on the same original raw B-period matrix. -/ bBound :
    NamedMatrixActionBound.UniformActionBound bank.periodData.bMatrix
  /-- The cached positive lower coefficient for the original raw A action. -/ lower : Fraction.Rational
  /-- The cached lower coefficient is the original coercivity bound squared divided by the retained B-action scale. -/
    lower_eq : lower = request.lower ^ 2 / bBound.scale
  /-- The cached A-action lower coefficient is strictly positive. -/ positive : 0 < lower

constructive_injectivity ActionLower

namespace ActionLower

/-- Retain the original B-action bound and derive the positive A-action coefficient on this exact raw request. -/
@[expose] def build : Curves.Hyperelliptic.Periods.Action.LowerBound.ActionLower request :=
  let bBound := UniformActionBound.build bank.periodData.bMatrix
  ⟨bBound, request.lower ^ 2 / bBound.scale, rfl,
    Fraction.Order.Field.div_pos_direct
      (by
          simpa only [pow_two]
            using Fraction.Order.Arithmetic.mul_pos_direct request.lower_positive request.lower_positive)
      bBound.scale_positive⟩

variable {request} (bound : Purelib.Curves.Hyperelliptic.Periods.Action.LowerBound.ActionLower request)

/-- Every original raw A sample above the retained stage floor bounds coefficient norm from below by the cached positive
action coefficient. -/
theorem accurate (stage : Nat) (later : request.index ≤ stage) (coefficients :
  LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    bound.lower * PreparedObservationCoercivity.coefficientNormSq coefficients ≤
      PreparedObservationCoercivity.coefficientNormSq (Energy.periodCombination coefficients (PeriodMatrix.sampledMatrix
        bank.periodData.aMatrix stage)) := by
  rw [bound.lower_eq]
  exact RawActionLower.a_action_lower coefficients _ _ request.lower bound.bBound.scale
    request.lower_positive bound.bBound.scale_positive (request.accurate stage later coefficients)
    (bound.bBound.action_bound stage coefficients)

end ActionLower
end Purelib.Curves.Hyperelliptic.Periods.Action.LowerBound
