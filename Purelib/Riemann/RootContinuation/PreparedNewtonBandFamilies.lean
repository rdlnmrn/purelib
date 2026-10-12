module

import Purelib.Data.Fin

meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.RootIsolation.State.Raw

public import Purelib.Riemann.RootContinuation.PreparedNewtonBandBoundary
public import Purelib.Data.Vector.Dependent
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Gaussian.Field
import Purelib.RootIsolation.Newton.Band.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Mathlib.Order.Basic

public section

/-!
# One Newton band for all basis differentials

Cache the finite coefficient-rate bank before requesting geometry. Its
maximum selects one band and one residual allowance, shared by every standard
differential. Independent integral and geometric-radius requests are both
paid. Empty families use maximum zero without a nonemptiness assumption.
-/

namespace Purelib.Riemann.RootContinuation.PreparedNewtonBandFamilies

open Purelib.RootIsolation.Newton.Band
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Riemann.RootContinuation.NewtonBandBounds (Profile)
open Purelib.Riemann.RootContinuation.NewtonBandDifferentials (DifferentialProfile)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
  (PreparedBandSelection PreparedBandRequest)
open Purelib.Data.Rat in
/-- The exact rational coordinate carrier. -/
private abbrev Coordinate := Fraction.Rational
/-- The original rational Gaussian box carrier. -/
private abbrev Box := Purelib.Geometry.Rational.Box

open Purelib.Data in
open Purelib.Data.Rat in
/-- A retained rational rate vector with the original finite length. -/
abbrev RateVector (count : Nat) := Data.Vector Fraction.Rational count

section
open Purelib.Data.Rat
/-- Fold a retained finite rate vector with maximum and zero.

The original structural spine determines the head/tail order. The empty tail
contributes zero, which keeps the retained maximum nonnegative. -/
@[expose] def maximumRate {count : Nat} (rates : RateVector count) : Fraction.Rational :=
  match rates with
  | .nil => 0
  | .cons head tail => max head (maximumRate tail)

/-- The retained rate maximum is nonnegative because its fold includes zero.

Structural vector induction retains the supplied spine and bounds each tail
maximum by the maximum of that same tail and its original head. -/
theorem maximumRate_nonnegative : ∀ {count : Nat} (rates : RateVector count), 0 ≤ maximumRate rates := by
  intro count rates
  induction rates with
  | nil => exact Fraction.Order.Basic.le_refl 0
  | cons head tail tailBound =>
    exact Data.Rat.Fraction.Order.Basic.le_trans _ _ _ tailBound
      (Fraction.Order.Basic.le_max_right _ _)

end

open Purelib.Data.Rat in
open Purelib.Data in
/-- Every bounded rate entry is at most its retained finite maximum.

The zero index selects the original head. A successor uses the retained tail
and predecessor bound, whose maximum is bounded by the same original fold. -/
theorem rate_le_maximum : ∀ {count : Nat} (rates : RateVector count) (index : Fin count),
    rates index ≤ maximumRate rates := by
  intro count rates
  induction rates with
  | nil => intro index; exact Fin.elim0 index
  | cons head tail tailBound =>
    intro index
    exact Fin.cases_induction
      (Fraction.Order.Basic.le_max_left _ _)
      (fun remaining => Data.Rat.Fraction.Order.Basic.le_trans _ _ _
        (tailBound remaining) (Fraction.Order.Basic.le_max_right _ _)) index

set_option genInjectivity false in
open Purelib.Data in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Polynomial.Dense.Gaussian in
/-- An indexed family of original differential profiles with exact rate-vector and maximum caches.

Each profile's exponent remains its original bounded index, and the stored rate equation connects the cache to that same
profile. -/
structure DifferentialFamily {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {squarefree : Squarefree.Basic.SquarefreeCertificate
  p}
    {current : Box} (profile : Profile squarefree current) (count : Nat) where
  /-- The retained original differential profiles indexed by their exact exponents. -/ profiles : Vector.DependentVector
    (fun index : Fin count => DifferentialProfile profile index.val)
  /-- The cached original finite vector of differential rates. -/ rates : RateVector count
  /-- Every cached rate equals the exact retained profile rate at that index. -/ rates_eq : ∀ index, rates index =
    (profiles.get index).rate
  /-- The retained nonnegative maximum of the original rate vector. -/ maximum : Fraction.Rational
  /-- The maximum cache equals the original finite rate fold. -/ maximum_eq : maximum = maximumRate rates

constructive_injectivity DifferentialFamily

namespace DifferentialFamily

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {squarefree :
  Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p}
  {current : Purelib.Geometry.Rational.Box} {profile : Profile squarefree current} {count : Nat}

open Purelib.Data in
/-- Cache the exact rates and their finite maximum from the original retained differential profiles. -/
@[expose] def ofProfiles (profiles : Vector.DependentVector (fun index : Fin count => DifferentialProfile profile
  index.val)) :
    DifferentialFamily profile count :=
  let rates := Vector.Basic.vectorOfFn fun index => (profiles.get index).rate
  ⟨profiles, rates, Vector.Basic.vectorOfFn_apply _, maximumRate rates, rfl⟩

open Purelib.Data in
open Purelib.Riemann.RootContinuation in
/-- Construct the original differential profiles at every retained exponent index and cache their rates. -/
@[expose] def build (profile : Profile squarefree current) (count : Nat) : DifferentialFamily profile count :=
  ofProfiles (Vector.DependentVector.ofFn fun index =>
    NewtonBandDifferentials.Profile.differential profile index.val)

/-- The original differential family's retained maximum is nonnegative. -/
theorem maximum_nonnegative (family : DifferentialFamily profile count) : 0 ≤ family.maximum := by
  rw [family.maximum_eq]
  exact maximumRate_nonnegative _

/-- Every original indexed differential rate is bounded by the family's retained maximum. -/
theorem rate_le (family : DifferentialFamily profile count) (index : Fin count) :
    (family.profiles.get index).rate ≤ family.maximum := by
  rw [← family.rates_eq, family.maximum_eq]
  exact rate_le_maximum _ _

end DifferentialFamily

set_option genInjectivity false in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.RootIsolation in
/-- One retained band selection paying all original differential profiles through their common maximum rate.

The exact sample, error allowance and radius bound are shared; the selection pays one sixteenth of the boundary target.
-/
structure PreparedBandFamily {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient
  : Box}
    {squarefree : Squarefree.Basic.SquarefreeCertificate p} {current : State.Raw.RawWindingState p ambient}
    {profile : Profile squarefree current.box} {count : Nat}
    (family : DifferentialFamily profile count) (target radius : Fraction.Rational) where
  /-- The original shared band sample and error selection paying the maximum rate. -/ selection : PreparedBandSelection
    profile (2 * family.maximum + 256) (target / 16) radius

constructive_injectivity PreparedBandFamily

namespace PreparedBandFamily

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient :
  Purelib.Geometry.Rational.Box} {squarefree :
  Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p}
  {current : Purelib.RootIsolation.State.Raw.RawWindingState p ambient} {profile : Profile squarefree current.box}
    {count : Nat}
  {family : DifferentialFamily profile count} {target radius : Purelib.Data.Rat.Fraction.Rational}

open Purelib.Data.Rat in
open Purelib.Polynomial in
open Purelib.Riemann.RootContinuation in
/-- Acquire a shared original Newton band paying every retained differential rate and the requested radius limit.

The original maximum rate plus its fixed error coefficient determines the selection; positivity and the one-sixteenth
target allowance are retained. -/
@[expose] def build (family : DifferentialFamily profile count) {degreeBound : Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree) (elimination :
      Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    {target radius : Fraction.Rational} (positive : 0 < target) (radiusPositive : 0 < radius) : PreparedBandFamily
      family target radius :=
  ⟨PreparedNewtonBandSamples.Profile.requestPreparation
    profile degreeAtLeastTwo elimination (2 * family.maximum + 256)
    (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct
      (by decide) family.maximum_nonnegative) (by decide +kernel))
    (Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Fraction.Rational) < 16)) radiusPositive⟩

open Purelib.Data.Rat in
/-- Specialize the shared original band selection to one retained differential profile without rebuilding its sample. -/
@[expose] def forDifferential (prepared : PreparedBandFamily family target radius) (index : Fin count) :
    PreparedBandRequest (family.profiles.get index) (target / 16) :=
  prepared.selection.forDifferential (family.profiles.get index)
    (add_le_add (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (family.rate_le index) (by decide)) le_rfl)

/-- Each differential specialization retains exactly the original shared sample box. -/
theorem differential_box (prepared : PreparedBandFamily family target radius) (index : Fin count) :
    (prepared.forDifferential index).sample.output.box = prepared.selection.sample.output.box := rfl

/-- Each differential specialization retains exactly the original shared error allowance. -/
theorem differential_error (prepared : PreparedBandFamily family target radius) (index : Fin count) :
    (prepared.forDifferential index).error = prepared.selection.error := rfl

open Purelib.Data.Rat in
/-- The original shared band box has squared diameter at most the requested radius squared. -/
theorem diagonal (prepared : PreparedBandFamily family target radius) :
    prepared.selection.sample.output.box.diagonalSq ≤ radius ^ 2 :=
  prepared.selection.sample.output.diagonalSq_le.trans
    (Fraction.Order.Arithmetic.pow_le_pow_direct prepared.selection.requestPositive.le
      prepared.selection.request_le_radius 2)

end PreparedBandFamily

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Riemann.RootContinuation in
open Purelib.RootIsolation in
/-- Prepare an original boundary for one retained differential and sheet using the shared sample selection.

The exact shared request supplies its anchor owner and four-side traversal, whose retained integral payment meets the
original family target. -/
@[expose] def PreparedBandFamily.boundary {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    {ambient : Box} {current : State.Raw.RawWindingState curve.polynomial ambient}
    {profile : Profile curve.squarefree current.box} {family : DifferentialFamily profile genus}
    {target radius : Fraction.Rational} (prepared : PreparedBandFamily family target radius) (index : Fin genus) (sheet
      : Fin 2) :
    PreparedNewtonBandBoundary.RequestedPreparedBoundary
      (family.profiles.get index) target sheet := by
  let request := prepared.forDifferential index
  let owner := PreparedNewtonBandBoundary.PreparedBandRequest.boundaryOwner
    request sheet
  let traversal := PreparedNewtonBandBoundary.PreparedBoundaryTraversal.build
    request owner sheet
  exact ⟨request, owner, traversal, traversal.bound.trans_eq (by
    rw [Fraction.Field.mul_comm]
    exact Fraction.Field.div_mul_cancel_of_ne target 16 (by decide))⟩

end Purelib.Riemann.RootContinuation.PreparedNewtonBandFamilies
