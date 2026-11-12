module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartEnergy
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartOrientation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.Dyadic.RadialTriangles
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.RootContinuation.RootRadialGeometry
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergySamples
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Approximation

open Purelib.Curves

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

public section

/-! One automatically paid parent allowance and one retained polynomial-bound
cache prepare every common-interval fan before the shared radial acquisition. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergyPreparation

open Purelib.Riemann.RootContinuation

variable {genus count : Nat} {curve : Basic.HyperellipticCurve genus} {differential :
  Differentials.Basic.Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    UniformReciprocalModels.Data patch count}
  {cover : UniformReciprocalCover.Cover data} {covers :
    SourceLocations.BasisSourceCovers parent}
  {regular : RegularBounds.Data cap} {bounds :
    ReciprocalPaddedInverse.UniformBounds regular.padded}
  {depth floor sourceFloor : Nat} {target sourceTarget : Normalization.InverseRootPolynomial.Coordinate}
  {index minimum stage : Nat} {box : Rational.Box}
  {capSample : Cap.Primitives.Sample cap differential index box}
  {polynomials : Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}
  {anchorBank : UniformReciprocalPrimitives.PrimitiveCells data index cover.mesh.edges}
  {bank : SourceLocations.BasisSourceLocations.SampleBank covers index}
  {basis : ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {joinTarget : Normalization.InverseRootPolynomial.Coordinate} {joinFloor : Nat}

open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Data.Gaussian.Basic.Canonical

variable {energyTarget : Normalization.InverseRootPolynomial.Coordinate} {energyFloor energyDepth : Nat}

variable {intervals : List (CommonCover.BasisCommonInterval cover covers)}
  {requests : CommonChartSchedule.BasisCommonChartRequests regular depth
    target sourceTarget floor sourceFloor intervals}
  {plans : CommonChartSchedule.BasisCommonChartRequests.Plans capSample
    polynomials minimum requests} {readings :
    CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
    bank stage requests plans}

set_option genInjectivity false in
/-- A paid common-interval energy request with one retained polynomial-bound cache and radial depth.

Its local allowance is weighted by the actual interval count before any fan acquisition. -/
structure EnergyPreparation
    (requests : CommonChartSchedule.BasisCommonChartRequests regular depth
      target sourceTarget floor sourceFloor intervals)
    (plans : CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests) (readings :
      CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans)
    (energyTarget : Normalization.InverseRootPolynomial.Coordinate) (energyFloor : Nat) where
  /-- The cached original polynomial bounds on the retained radial domain. -/ bounds :
    Meshes.PuncturedGrid.Exterior.CapBasisBounds.RegularBasisBounds polynomials
    RootRadialGeometry.domain
  /-- The cached energy allowance for each actual interval. -/ allowance :
    Normalization.InverseRootPolynomial.Coordinate
  /-- The local allowance uses the original parent target and actual interval count. -/ allowance_eq : allowance =
    Rational.Budget.Weighted.allowance energyTarget (intervals.length : Normalization.InverseRootPolynomial.Coordinate)
  /-- The cached local energy allowance is positive. -/ positive : 0 < allowance
  /-- The actual interval count times its allowance is paid by the parent energy target. -/ paid : (intervals.length :
    Normalization.InverseRootPolynomial.Coordinate) * allowance ≤ energyTarget
  /-- The original interval energy requests sharing that bound cache and allowance. -/ energies :
    CommonChartEnergy.EnergyRequests bounds allowance energyFloor requests
    plans readings
  /-- The common radial depth sufficient for every interval request. -/ radialDepth : Nat
  /-- The selected radial depth is the maximum of the retained interval thresholds. -/ depth_eq : radialDepth =
    energies.maximum

constructive_injectivity EnergyPreparation

namespace EnergyPreparation

/-- Cache the original polynomial bounds and prepare every interval energy request with its paid common allowance. -/
@[expose] def build (requests : CommonChartSchedule.BasisCommonChartRequests
  regular depth target sourceTarget floor sourceFloor intervals)
    (plans : CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests) (readings :
      CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans)
    (energyTarget : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < energyTarget) (energyFloor : Nat) :
    EnergyPreparation requests plans readings
      energyTarget energyFloor := open Purelib.Data.Rat in by
  let bounds := Meshes.PuncturedGrid.Exterior.CapBasisBounds.RegularBasisBounds.build polynomials
    RootRadialGeometry.domain
  let allowance := Rational.Budget.Weighted.allowance energyTarget (intervals.length :
    Normalization.InverseRootPolynomial.Coordinate)
  have nonnegative : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ intervals.length :=
    Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)
  have allowancePositive : 0 < allowance := Rational.Budget.Weighted.allowance_positive positive nonnegative
  let energies := CommonChartEnergy.EnergyRequests.build bounds allowance
    allowancePositive energyFloor requests plans readings
  exact ⟨bounds, allowance, rfl, allowancePositive, Rational.Budget.Weighted.mul_allowance_le positive.le nonnegative,
    energies, energies.maximum, rfl⟩

/-- Raise every request to the selected family-wide radial depth before any
fan is built. Reuse its parameter bank throughout the acquisition. -/
@[expose] def acquire (preparation :
  EnergyPreparation requests plans readings
  energyTarget energyFloor)
    (parameters : Path.Dyadic.RadialTriangles.Parameters energyDepth)
    (oriented : CommonChartOrientation.Orientation requests plans readings)
      (later : preparation.radialDepth ≤ energyDepth) :
    CommonChartEnergy.Energies preparation.allowance energyFloor energyDepth
      requests plans readings :=
  preparation.energies.acquire parameters requests plans readings oriented (preparation.depth_eq ▸ later)

/-- The retained parent energy target pays the coefficient-weighted lower bound for the acquired cached fan area. -/
theorem lower (preparation : EnergyPreparation
  requests plans readings energyTarget energyFloor)
    {energies : CommonChartEnergy.Energies preparation.allowance energyFloor
      energyDepth requests plans readings}
    {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus} (sampled :
      CommonEnergySamples.SampledEnergy energies coefficients) :
    -(Readings.PreparedObservationCoercivity.coefficientNormSq coefficients * energyTarget) ≤ sampled.area.im / 4 :=
      open Purelib.Algebra in open Purelib.Data in open Purelib.Data.Rat in by
  have nonnegative : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
      Normalization.InverseRootPolynomial.Coordinate)) _ (fun row => normSq_nonneg
      (coefficients row)))
  exact (Fraction.Order.Arithmetic.neg_le_neg_direct (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    preparation.paid nonnegative)).trans sampled.lower

end EnergyPreparation
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergyPreparation
