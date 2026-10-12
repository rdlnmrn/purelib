module
import Purelib.Algebra.NatCast
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartPath
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartEnergy
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartAcquisition
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartBudget
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.RootRadialGeometry
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib

open Purelib.Riemann

@[expose] public section

/-! Retain each acquired fan area, both endpoint potentials and its exact
arc readback. The parent sum consumes these cached samples once. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergySamples

open Purelib.Riemann.RootContinuation

variable {genus count : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {cover : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data} {covers :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers parent}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {bounds :
    Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}
  {depth floor sourceFloor : Nat} {target sourceTarget : Normalization.InverseRootPolynomial.Coordinate}
  {index minimum stage : Nat} {box : Rational.Box}
  {capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}
  {anchorBank : Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.PrimitiveCells data index cover.mesh.edges}
  {bank : Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceLocations.SampleBank covers index}
  {basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {joinTarget : Normalization.InverseRootPolynomial.Coordinate} {joinFloor : Nat}

open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Data.Gaussian.Basic.Canonical

variable {energyTarget : Normalization.InverseRootPolynomial.Coordinate} {energyFloor energyDepth : Nat}

/-- The dependent bank of acquired interval fan samples for one retained coefficient vector.

Each entry preserves its actual endpoint coordinates, chart path and previously acquired fan energy. -/
def EnergySamples (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    {intervals : List (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval cover covers)} →
    (requests : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests regular depth
      target sourceTarget floor sourceFloor intervals) →
    (plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests) → (readings :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans) →
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartEnergy.Energies energyTarget energyFloor energyDepth requests
      plans readings → Type
  | _, .nil, _, _, _ => PUnit
  | _, .cons _ tail, plans, readings, energies =>
      energies.1.val.Sample coefficients readings.1.evaluated.first.root.coordinate
        readings.1.evaluated.last.root.coordinate ×
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergySamples.EnergySamples coefficients tail
          plans.2 readings.2 energies.2

namespace EnergySamples

/-- Sample each acquired interval fan using its original evaluated chart path and retained coefficient vector. -/
def build (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    {intervals : List (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval cover covers)} →
    (requests : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests regular depth
      target sourceTarget floor sourceFloor intervals) →
    (plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests) → (readings :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans) →
    (energies : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartEnergy.Energies energyTarget energyFloor
      energyDepth requests plans readings) →
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergySamples.EnergySamples coefficients requests plans readings
      energies
  | _, .nil, _, _, _ => ⟨⟩
  | _, .cons _ tail, plans, readings, energies =>
      ⟨energies.1.val.sample coefficients _ _
        (Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartPath.BasisIntervalChartRequest.Plan.Evaluation.path
          readings.1.evaluated).chain,
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergySamples.EnergySamples.build coefficients
          tail plans.2 readings.2 energies.2⟩

variable {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

/-- Read the cached fan areas in original interval order. -/
def areas : {intervals : List (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval cover covers)}
  →
    {requests : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests regular depth
      target sourceTarget floor sourceFloor intervals} →
    {plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} → {readings :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans} →
    {energies : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartEnergy.Energies energyTarget energyFloor
      energyDepth requests plans readings} →
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergySamples.EnergySamples coefficients requests plans readings
      energies → List Normalization.InverseRootPolynomial.Gaussian
  | _, .nil, _, _, _, _ => []
  | _, .cons _ _, _, _, _, samples => samples.1.area ::
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergySamples.EnergySamples.areas samples.2

/-- The retained coefficient vector has nonnegative squared norm. -/
private theorem norm_nonnegative : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := open
  Purelib.Algebra in FiniteSum.Fin.sumFin_zero.symm.trans_le
  (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
    Normalization.InverseRootPolynomial.Coordinate)) _ (fun row => Gaussian.Basic.Canonical.normSq_nonneg (coefficients
    row)))

/-- The cached fan area sum has the lower bound paid by the coefficient norm, actual interval count and common energy
target. -/
theorem lower : {intervals : List (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval cover
  covers)} →
    {requests : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests regular depth
      target sourceTarget floor sourceFloor intervals} →
    {plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} → {readings :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans} →
    {energies : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartEnergy.Energies energyTarget energyFloor
      energyDepth requests plans readings} →
    (samples : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergySamples.EnergySamples coefficients requests plans
      readings energies) →
    -(Readings.PreparedObservationCoercivity.coefficientNormSq coefficients * ((intervals.length :
      Normalization.InverseRootPolynomial.Coordinate) * energyTarget)) ≤
      (Data.Gaussian.Norm.Sum.Basic.gaussianSum samples.areas).im / 4
  | _, .nil, _, _, _, _ => by
      change -(Readings.PreparedObservationCoercivity.coefficientNormSq coefficients * (0 * energyTarget)) ≤ 0 / 4
      rw [Fraction.Field.zero_mul_direct, Fraction.Field.mul_zero_direct]
      decide
  | _, .cons _ _, _, _, energies, samples => by
      have head := (Fraction.Order.Arithmetic.neg_le_neg_direct
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct energies.1.val.error_lt.le
        (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergySamples.EnergySamples.norm_nonnegative (coefficients :=
          coefficients)))).trans samples.1.lower
      have combined := Fraction.Order.Arithmetic.add_le_add_direct head
        (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergySamples.EnergySamples.lower samples.2)
      change -(Readings.PreparedObservationCoercivity.coefficientNormSq coefficients * (((_ + 1 : Nat) :
        Normalization.InverseRootPolynomial.Coordinate) * energyTarget)) ≤
        (samples.1.area + Data.Gaussian.Norm.Sum.Basic.gaussianSum samples.2.areas).im / 4
      rw [Algebra.NatCast.add, Nat.cast_one, Gaussian.Basic.add_im]
      exact (show -(Readings.PreparedObservationCoercivity.coefficientNormSq coefficients * ((_ + 1) * energyTarget)) =
        -(Readings.PreparedObservationCoercivity.coefficientNormSq coefficients * energyTarget) +
          -(Readings.PreparedObservationCoercivity.coefficientNormSq coefficients * (_ * energyTarget)) by
          ring1).trans_le
        (combined.trans_eq (by simp only [Fraction.Field.div_eq_mul_inv_direct]; ring1))

end EnergySamples

variable {intervals : List (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval cover covers)}
  {requests : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests regular depth
    target sourceTarget floor sourceFloor intervals}
  {plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests.Plans capSample
    polynomials minimum requests} {readings :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
    bank stage requests plans}

set_option genInjectivity false in
/-- A cached parent fan area with its actual interval samples and coefficient-weighted lower bound. -/
structure SampledEnergy (energies : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartEnergy.Energies energyTarget
  energyFloor energyDepth requests plans readings)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) where
  /-- The acquired fan samples on the original interval list. -/ samples :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergySamples.EnergySamples coefficients requests plans readings
    energies
  /-- The cached sum of those fan areas. -/ area : Normalization.InverseRootPolynomial.Gaussian
  /-- The cached parent area is exactly the sum of its retained interval samples. -/ area_eq : area =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum samples.areas
  /-- The coefficient norm and actual interval count pay the parent lower bound. -/ lower :
    -(Readings.PreparedObservationCoercivity.coefficientNormSq coefficients * ((intervals.length :
    Normalization.InverseRootPolynomial.Coordinate) * energyTarget)) ≤ area.im / 4

constructive_injectivity SampledEnergy

/-- Cache the acquired interval fan samples, their total area and the complete parent lower bound. -/
def Energies.sample (energies : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartEnergy.Energies energyTarget
  energyFloor energyDepth requests plans readings)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergySamples.SampledEnergy energies coefficients :=
  let samples := Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergySamples.EnergySamples.build coefficients
    requests plans readings energies
  ⟨samples, Data.Gaussian.Norm.Sum.Basic.gaussianSum samples.areas, rfl, samples.lower⟩

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergySamples
