module
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.RootIsolation.State.Raw

public import Purelib.Integration.Path.NoisyPathArea
public import Purelib.Riemann.RootContinuation.PreparedNewtonBandFamilies
import Purelib.Riemann.RootContinuation.NewtonAreaRate
import Purelib.Tactic.Ring

@[expose] public section

/-! One radius-independent area coefficient for the shared Newton band and
all pairs of basis differentials. Density itself is allowed to grow. -/
namespace Purelib.Riemann.RootContinuation.PreparedNewtonAreaRate

open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction renaming Rational -> Coordinate
open Purelib.RootIsolation.Newton.Band
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Integration.Path.NoisyPathArea (LengthErrorBudget)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandFamilies (DifferentialFamily)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples (PreparedBandBudget)
open Purelib.Riemann.RootContinuation.NewtonBandBounds (Profile Sample)
open Purelib.Riemann.RootContinuation.NewtonBandDifferentials (DifferentialProfile)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandFamilies (PreparedBandFamily)

namespace Sample
variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {ambient :
  Purelib.Geometry.Rational.Box}
  {current : Purelib.RootIsolation.State.Raw.RawWindingState curve.polynomial ambient} {profile : Profile
    curve.squarefree current.box}
  {requestSize : Purelib.Data.Rat.Fraction.Rational} (sample : Sample profile requestSize)

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Data in
/-- Bound prepared differential density times the actual Newton radius.

For nonnegative error at most one and radius at most one, the product is at most twice the fixed differential rate plus
256. -/
theorem preparedDensity_radius_le {differential : Hyperelliptic.Differentials.Basic.Differential genus} (fixed :
  DifferentialProfile profile differential.exponent)
    {error : Rat.Fraction.Rational} (errorNonnegative : 0 ≤ error) (errorLe : error ≤ 1)
    (radiusLe : sample.output.radius ≤ 1) :
    RootContinuation.PreparedNewtonBandSamples.Sample.preparedDensity sample fixed error * sample.output.radius ≤ 2 *
      fixed.rate + 256 := by
  apply Rat.Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := sample.output.radius) _
    sample.output.radiusPositive
  have movement := RootContinuation.PreparedNewtonBandSamples.Sample.preparedDensity_movement_le sample fixed errorLe
    radiusLe
  have small : sample.output.radius^2 ≤ 32 * sample.output.radius^2 := by
    have h := Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (show (1 : Rat.Fraction.Rational) ≤ 32 by
      decide +kernel)
      (Rat.Fraction.Order.Arithmetic.sq_nonneg_direct sample.output.radius)
    simpa only [Rat.Fraction.Field.one_mul] using h
  have bound := (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct small
    (RootContinuation.PreparedNewtonBandSamples.Sample.preparedDensity_nonnegative sample fixed errorNonnegative)).trans
    movement
  exact (show RootContinuation.PreparedNewtonBandSamples.Sample.preparedDensity sample fixed error *
    sample.output.radius * sample.output.radius =
    RootContinuation.PreparedNewtonBandSamples.Sample.preparedDensity sample fixed error * sample.output.radius^2 by
      ring1) ▸ bound

end Sample

namespace PreparedBandFamily
variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {ambient :
  Purelib.Geometry.Rational.Box}
  {current : Purelib.RootIsolation.State.Raw.RawWindingState curve.polynomial ambient} {profile : Profile
    curve.squarefree current.box}
  {family : DifferentialFamily profile genus} {target radius : Purelib.Data.Rat.Fraction.Rational}

section
open Purelib.Data
/-- The retained Newton band width is at most four times its actual radius. -/
theorem widthX_le (prepared : PreparedBandFamily family target radius) :
    prepared.selection.sample.output.box.widthX ≤ 4 * prepared.selection.sample.output.radius := by
  have h := Rat.Fraction.Order.Arithmetic.sub_le_sub_direct prepared.selection.sample.output.band.right_upper
    prepared.selection.sample.output.band.left_lower
  exact h.trans_eq (by ring1)

/-- The retained Newton band height is at most four times its actual radius. -/
theorem widthY_le (prepared : PreparedBandFamily family target radius) :
    prepared.selection.sample.output.box.widthY ≤ 4 * prepared.selection.sample.output.radius := by
  have h := Rat.Fraction.Order.Arithmetic.sub_le_sub_direct prepared.selection.sample.output.band.top_upper
    prepared.selection.sample.output.band.bottom_lower
  exact h.trans_eq (by ring1)

end

open Purelib.Integration in
/-- Allocate the finite side-junction tolerance after fixing the retained band radius. -/
def sideBudget (prepared : PreparedBandFamily family target radius) (edges : Nat) :
    Path.NoisyPathArea.LengthErrorBudget edges prepared.selection.sample.output.radius :=
  Path.NoisyPathArea.LengthErrorBudget.build edges _ prepared.selection.sample.output.radiusPositive

section
open Purelib.Riemann
/-- The selected side padding is at most the retained band radius. -/
theorem sideBudget_padding_le (prepared : PreparedBandFamily family target radius) (edges : Nat) :
    (sideBudget prepared edges).padding ≤ prepared.selection.sample.output.radius :=
  RootContinuation.NewtonAreaRate.LengthErrorBudget.build_padding_le edges
    prepared.selection.sample.output.radiusPositive

/-- Sum two differential density bounds using the same retained sample and error cache. -/
def pairedDensity (prepared : PreparedBandFamily family target radius) (first second : Fin genus) : Coordinate :=
  RootContinuation.PreparedNewtonBandSamples.Sample.preparedDensity prepared.selection.sample (differential := ⟨first⟩)
    (family.profiles.get first) prepared.selection.error +
    RootContinuation.PreparedNewtonBandSamples.Sample.preparedDensity prepared.selection.sample (differential :=
      ⟨second⟩) (family.profiles.get second) prepared.selection.error

end

/-- The uniform paired-density rate from the retained maximum differential rate. -/
def areaRate (family : DifferentialFamily profile genus) : Coordinate := 4 * family.maximum + 512

/-- The radius-independent quadratic area coefficient for the retained differential family. -/
def areaCoefficient (family : DifferentialFamily profile genus) : Coordinate :=
  100 * (3 + 128 * areaRate family) * (4 * areaRate family + 3)

section
open Purelib.Data
/-- The retained family's area coefficient is nonnegative. -/
theorem areaCoefficient_nonnegative (family : DifferentialFamily profile genus) : 0 ≤ areaCoefficient family := by
  have rateNonnegative : 0 ≤ areaRate family :=
    add_nonneg (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) family.maximum_nonnegative) (by
      decide +kernel)
  exact Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
    (add_nonneg (by decide +kernel) (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
      rateNonnegative)))
    (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) rateNonnegative) (by decide +kernel))

/-- Choose a radius cap paying the requested area error before constructing the band.

The positive error and geometric radius request determine a budget for the retained family's area coefficient. -/
def areaBudget (family : DifferentialFamily profile genus) {error radius : Rat.Fraction.Rational}
    (positive : 0 < error) (radiusPositive : 0 < radius) :
    PreparedBandBudget (areaCoefficient family) error radius :=
  PreparedBandBudget.build _ (areaCoefficient_nonnegative family) positive radiusPositive

/-- The actual selected Newton radius respects the caller's geometric radius request. -/
theorem radius_le (prepared : PreparedBandFamily family target radius) :
    prepared.selection.sample.output.radius ≤ radius := by
  have sizeBound : (1 / 8 : Rat.Fraction.Rational) * prepared.selection.requestSize ≤ prepared.selection.requestSize :=
    by
    have h := Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (show (1 / 8 : Rat.Fraction.Rational) ≤ 1
      by decide +kernel)
      prepared.selection.requestPositive.le
    simpa only [Rat.Fraction.Field.one_mul] using h
  exact prepared.selection.sample.radius_le.trans (sizeBound.trans prepared.selection.request_le_radius)

/-- Every band selected under the retained area cap pays the quadratic-radius estimate.

The same budget also retains the caller's geometric radius cap. -/
theorem quadratic_paid {error cap : Rat.Fraction.Rational}
    (budget : PreparedBandBudget (areaCoefficient family) error cap)
    (prepared : PreparedBandFamily family target budget.size) :
    areaCoefficient family * prepared.selection.sample.output.radius^2 ≤ error := by
  have squared : prepared.selection.sample.output.radius^2 ≤ prepared.selection.sample.output.radius := by
    have h := Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct prepared.selection.radius_le_one
      prepared.selection.sample.output.radiusPositive.le
    simpa only [pow_two, Rat.Fraction.Field.one_mul] using h
  exact (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (squared.trans (radius_le prepared))
    (areaCoefficient_nonnegative family)).trans budget.paid

end

section
open Purelib.Riemann
/-- The combined density bound for any retained basis pair is nonnegative. -/
theorem pairedDensity_nonnegative (prepared : PreparedBandFamily family target radius) (first second : Fin genus) :
    0 ≤ pairedDensity prepared first second :=
  add_nonneg (RootContinuation.PreparedNewtonBandSamples.Sample.preparedDensity_nonnegative prepared.selection.sample
    (differential := ⟨first⟩) (family.profiles.get first) prepared.selection.errorPositive.le)
    (RootContinuation.PreparedNewtonBandSamples.Sample.preparedDensity_nonnegative prepared.selection.sample
      (differential := ⟨second⟩) (family.profiles.get second) prepared.selection.errorPositive.le)

/-- The first retained differential density is bounded by the paired density. -/
theorem first_density_le (prepared : PreparedBandFamily family target radius) (first second : Fin genus) :
    RootContinuation.PreparedNewtonBandSamples.Sample.preparedDensity (prepared.forDifferential first).sample
      (differential := ⟨first⟩) (family.profiles.get first)
      (prepared.forDifferential first).error ≤ pairedDensity prepared first second :=
  le_add_of_nonneg_right (RootContinuation.PreparedNewtonBandSamples.Sample.preparedDensity_nonnegative
    prepared.selection.sample (differential := ⟨second⟩) (family.profiles.get second)
    prepared.selection.errorPositive.le)

/-- The second retained differential density is bounded by the paired density. -/
theorem second_density_le (prepared : PreparedBandFamily family target radius) (first second : Fin genus) :
    RootContinuation.PreparedNewtonBandSamples.Sample.preparedDensity (prepared.forDifferential second).sample
      (differential := ⟨second⟩) (family.profiles.get second)
      (prepared.forDifferential second).error ≤ pairedDensity prepared first second :=
  le_add_of_nonneg_left (RootContinuation.PreparedNewtonBandSamples.Sample.preparedDensity_nonnegative
    prepared.selection.sample (differential := ⟨first⟩) (family.profiles.get first) prepared.selection.errorPositive.le)

end

open Purelib.Data in
/-- Paired density times the actual band radius is bounded by the uniform family rate. -/
theorem pairedDensity_radius_le (prepared : PreparedBandFamily family target radius) (first second : Fin genus) :
    pairedDensity prepared first second * prepared.selection.sample.output.radius ≤ areaRate family := by
  have bound := Rat.Fraction.Order.Arithmetic.add_le_add_direct
    (Sample.preparedDensity_radius_le prepared.selection.sample (differential := ⟨first⟩) (family.profiles.get first)
      prepared.selection.errorPositive.le prepared.selection.error_le_one prepared.selection.radius_le_one)
    (Sample.preparedDensity_radius_le prepared.selection.sample (differential := ⟨second⟩) (family.profiles.get second)
      prepared.selection.errorPositive.le prepared.selection.error_le_one prepared.selection.radius_le_one)
  have rates := Rat.Fraction.Order.Arithmetic.add_le_add_direct
    (Rat.Fraction.Order.Arithmetic.add_le_add_direct (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (family.rate_le first) (by decide +kernel : (0 : Rat.Fraction.Rational) ≤ 2)) (le_refl 256))
    (Rat.Fraction.Order.Arithmetic.add_le_add_direct (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (family.rate_le second) (by decide +kernel : (0 : Rat.Fraction.Rational) ≤ 2)) (le_refl 256))
  calc
    _ = _ + _ := by unfold pairedDensity; exact add_mul ..
    _ ≤ (2 * (family.profiles.get first).rate + 256) + (2 * (family.profiles.get second).rate + 256) := bound
    _ ≤ (2 * family.maximum + 256) + (2 * family.maximum + 256) := rates
    _ = _ := by unfold areaRate; ring1

open Purelib.Riemann in
open Purelib.Integration in
open Purelib.Data in
/-- Convert the complete noisy-side area estimate to quadratic decay in the Newton radius.

The retained padding fits the radius, and the nonnegative geometric length is at most four times that radius. -/
theorem area_rate (prepared : PreparedBandFamily family target radius) (first second : Fin genus)
    {edges : Nat} (budget : Path.NoisyPathArea.LengthErrorBudget edges prepared.selection.sample.output.radius)
    (paddingLe : budget.padding ≤ prepared.selection.sample.output.radius)
    {length : Rat.Fraction.Rational} (lengthNonnegative : 0 ≤ length)
    (lengthLe : length ≤ 4 * prepared.selection.sample.output.radius) :
    4 * (3 * budget.tolerance + 4 * pairedDensity prepared first second *
      prepared.selection.sample.output.box.diagonalSq) *
      (4 * pairedDensity prepared first second + 3) * (length + prepared.selection.sample.output.radius)^2 ≤
      100 * (3 + 128 * areaRate family) * (4 * areaRate family + 3) * prepared.selection.sample.output.radius^2 :=
  RootContinuation.NewtonAreaRate.newton_area_rate
    prepared.selection.sample.output.radiusPositive.le prepared.selection.radius_le_one
    budget.tolerance_positive.le (RootContinuation.NewtonAreaRate.LengthErrorBudget.tolerance_le_radius_sq budget
      paddingLe)
    (pairedDensity_nonnegative prepared first second) (pairedDensity_radius_le prepared first second)
    prepared.selection.sample.output.box.diagonalSq_nonneg
    (prepared.selection.sample.output.band.diagonalSq_le prepared.selection.sample.output.radiusPositive)
    lengthNonnegative lengthLe

end PreparedBandFamily
end Purelib.Riemann.RootContinuation.PreparedNewtonAreaRate
