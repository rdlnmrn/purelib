module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceSamples
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonPreparedComparison
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Tactic.Ring

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib

open Purelib.Riemann

@[expose] public section

/-! Retain prepared child-integral comparisons alongside every acquired
surface component, using the same shared numerical stage and original caches. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePrepared

open Purelib.Riemann.Normalization

open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {bounds : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}

variable {basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {target coefficientTarget : Normalization.InverseRootPolynomial.Coordinate} {coverFloor floor index minimum
    readingIndex : Nat}
  {box : Rational.Box} {capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap
    differential index box}
  {polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}

variable {energyFloor radialDepth : Nat}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

namespace Plans.Samples

/-- The dependent spine of prepared child-integral comparisons on all original surface samples.

Each comparison keeps the exact component plans, readings, fan preparation and cached sample. -/
def PreparedComparisons :
    (entries : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest.Entry (domains := domains)
      (differential := differential) basis target coefficientTarget coverFloor floor)) →
    (plans : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans capSample polynomials minimum entries)
      → (readings : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans.Readings entries plans
      readingIndex) →
    (fans : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceSamples.Plans.FanPreparations energyFloor entries
      plans readings) →
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceSamples.Plans.Samples coefficients radialDepth entries
      plans readings fans → Type 3
  | [], _, _, _, _ => PUnit
  | _ :: tail, plans, readings, fans, samples =>

        CommonPreparedComparison.CommonBasisRequest.Sampled.PreparedComparisons
        samples.1 ×
        PreparedComparisons
        tail plans.2 readings.2 fans.2 samples.2

/-- Compare every original surface sample at a numerical stage paying all retained entry floors. -/
def comparePrepared :
    (entries : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest.Entry (domains := domains)
      (differential := differential) basis target coefficientTarget coverFloor floor)) →
    (plans : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans capSample polynomials minimum entries)
      → (readings : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans.Readings entries plans
      readingIndex) →
    (fans : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceSamples.Plans.FanPreparations energyFloor entries
      plans readings) →
    (samples : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceSamples.Plans.Samples coefficients radialDepth
      entries plans readings fans) →
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest.Entry.maximum entries ≤ index →
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePrepared.Plans.Samples.PreparedComparisons entries plans
      readings fans samples
  | [], _, _, _, _, _ => PUnit.unit
  | _ :: tail, plans, readings, fans, samples, later =>
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonPreparedComparison.CommonBasisRequest.Sampled.comparePrepared
        samples.1 (((show _ ≤ max _ _ from Data.Nat.Order.le_max_left ..)).trans later),
        Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePrepared.Plans.Samples.comparePrepared
          tail plans.2 readings.2 fans.2 samples.2 (((show _ ≤ max _ _ from Data.Nat.Order.le_max_right ..)).trans
          later))

/-- Each disconnected surface component retains its own prepared
trace and certified endpoint return; no cross-component connectors are inserted. -/
def PreparedTraces : (entries : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest.Entry (domains :=
  domains) (differential := differential) basis target coefficientTarget coverFloor floor)) →
    (plans : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans capSample polynomials minimum entries)
      → (readings : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans.Readings entries plans
      readingIndex) →
    (fans : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceSamples.Plans.FanPreparations energyFloor entries
      plans readings) →
    (samples : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceSamples.Plans.Samples coefficients radialDepth
      entries plans readings fans) →
    (comparisons : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePrepared.Plans.Samples.PreparedComparisons
      entries plans readings fans samples) → Type
  | [], _, _, _, _, _ => PUnit
  | _ :: tail, plans, readings, fans, samples, comparisons =>
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonPreparedComparison.CommonBasisRequest.Sampled.PreparedTrace
        samples.1 comparisons.1 ×
        Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePrepared.Plans.Samples.PreparedTraces
        tail plans.2 readings.2 fans.2 samples.2 comparisons.2

/-- Prepare each original component's trace and endpoint return at the shared paid reading stage.

The branch condition is shared, while each disconnected component keeps its own original trace. -/
def prepareTraces (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) : (entries :
  List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest.Entry (domains := domains) (differential :=
  differential) basis target coefficientTarget coverFloor floor)) →
    (plans : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans capSample polynomials minimum entries)
      → (readings : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans.Readings entries plans
      readingIndex) →
    (fans : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceSamples.Plans.FanPreparations energyFloor entries
      plans readings) →
    (samples : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceSamples.Plans.Samples coefficients radialDepth
      entries plans readings fans) →
    (comparisons : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePrepared.Plans.Samples.PreparedComparisons
      entries plans readings fans samples) →
    plans.stage entries ≤ readingIndex →
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePrepared.Plans.Samples.PreparedTraces entries plans
      readings fans samples comparisons
  | [], _, _, _, _, _, _ => PUnit.unit
  | _ :: tail, plans, readings, fans, samples, comparisons, later =>
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonPreparedComparison.CommonBasisRequest.Sampled.prepareTrace
        samples.1 comparisons.1 branch (plans.1.stage_eq.symm.trans_le (((show _ ≤ max _ _ from
        Data.Nat.Order.le_max_left ..)).trans later)),
        Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePrepared.Plans.Samples.prepareTraces
          branch tail plans.2 readings.2 fans.2 samples.2 comparisons.2 (((show _ ≤ max _ _ from
          Data.Nat.Order.le_max_right ..)).trans later))

/-- Read the ordered list of negated original component traces from the retained comparison spine. -/
def preparedValues : (entries : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest.Entry (domains :=
  domains) (differential := differential) basis target coefficientTarget coverFloor floor)) →
    (plans : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans capSample polynomials minimum entries)
      → (readings : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans.Readings entries plans
      readingIndex) →
    (fans : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceSamples.Plans.FanPreparations energyFloor entries
      plans readings) →
    (samples : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceSamples.Plans.Samples coefficients radialDepth
      entries plans readings fans) →
    (comparisons : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePrepared.Plans.Samples.PreparedComparisons
      entries plans readings fans samples) →
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePrepared.Plans.Samples.PreparedTraces entries plans
      readings fans samples comparisons → List Normalization.InverseRootPolynomial.Gaussian
  | [], _, _, _, _, _, _ => []
  | _ :: tail, plans, readings, fans, samples, comparisons, traces =>
      (-traces.1.trace) ::
        Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePrepared.Plans.Samples.preparedValues
        tail plans.2 readings.2 fans.2 samples.2 comparisons.2 traces.2

open Purelib.Data.Gaussian.Basic.Canonical

/-- Bound the imaginary reading of the complete retained component-trace sum.

The actual component count pays three local allowances per component, scaled by the common coefficient norm. -/
theorem preparedLower : (entries : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest.Entry (domains
  := domains) (differential := differential) basis target coefficientTarget coverFloor floor)) →
    (plans : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans capSample polynomials minimum entries)
      → (readings : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans.Readings entries plans
      readingIndex) →
    (fans : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceSamples.Plans.FanPreparations energyFloor entries
      plans readings) →
    (samples : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceSamples.Plans.Samples coefficients radialDepth
      entries plans readings fans) →
    (comparisons : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePrepared.Plans.Samples.PreparedComparisons
      entries plans readings fans samples) →
    (traces : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePrepared.Plans.Samples.PreparedTraces entries
      plans readings fans samples comparisons) →
    -((entries.length : Normalization.InverseRootPolynomial.Coordinate) * (target + target + target) *
      Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) ≤
      (Data.Gaussian.Norm.Sum.Basic.gaussianSum
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePrepared.Plans.Samples.preparedValues entries plans
        readings fans samples comparisons traces)).im / 4
  | [], _, _, _, _, _, _ => by
      change -(0 * (target + target + target) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) ≤
        0 / 4
      exact (show -(0 * (target + target + target) * Readings.PreparedObservationCoercivity.coefficientNormSq
        coefficients) = (0 : Normalization.InverseRootPolynomial.Coordinate) / 4 by
        simp only [Fraction.Field.div_eq_mul_inv_direct]; ring1).le
  | head :: tail, plans, readings, fans, samples, comparisons, traces => by
      have bounded := Fraction.Order.Arithmetic.add_le_add_direct traces.1.trace_lower
        (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePrepared.Plans.Samples.preparedLower
          tail plans.2 readings.2 fans.2 samples.2 comparisons.2 traces.2)
      have left : -(((head :: tail).length : Normalization.InverseRootPolynomial.Coordinate) * (target + target +
        target) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) =
          -((target + target + target) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) -
            ((tail.length : Normalization.InverseRootPolynomial.Coordinate) * (target + target + target) *
              Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) := by
        simp only [List.length_cons, Fraction.Cast.natCast_add_direct, Nat.cast_one]
        ring1
      rw [left]
      apply bounded.trans_eq
      change (-traces.1.trace).im / 4 +
        (Data.Gaussian.Norm.Sum.Basic.gaussianSum
          (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePrepared.Plans.Samples.preparedValues tail plans.2
          readings.2 fans.2 samples.2 comparisons.2 traces.2)).im / 4 =
        ((-traces.1.trace) + Data.Gaussian.Norm.Sum.Basic.gaussianSum
          (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePrepared.Plans.Samples.preparedValues tail plans.2
          readings.2 fans.2 samples.2 comparisons.2 traces.2)).im / 4
      rw [Gaussian.Basic.add_im]
      simp only [Fraction.Field.div_eq_mul_inv_direct]
      ring1

end Plans.Samples
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePrepared
