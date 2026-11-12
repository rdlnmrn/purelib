module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.Dyadic.RadialTriangles
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePrepared
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Tactic.Ring

open Purelib.LinearAlgebra.Gaussian.Energy (GaussianVector)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePrepared.Plans

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

@[expose] public section

/-! Cache the shared component acquisition and aggregate its prepared trace
bounds after paying endpoint return against the requested complete-surface budget. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceEnergy.Request

open Purelib.Riemann.Normalization

open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Differentials.Basic.Differential genus}
  {collar : Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {bounds : Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}

variable {basis : Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {target coefficientTarget : InverseRootPolynomial.Coordinate} {coverFloor floor index minimum
    readingIndex : Nat}
  {box : Rational.Box} {capSample : Charts.Reciprocal.Cap.Primitives.Sample cap
    differential index box}
  {polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box}

variable {energyFloor radialDepth : Nat}
  {coefficients : GaussianVector genus}

open Purelib.Data.Gaussian.Basic.Canonical

section Request

variable {prepared :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential}
  {request : SurfaceRequest.Request prepared basis target
    coefficientTarget coverFloor floor}

set_option genInjectivity false in
/-- The cached common numerical acquisition for every original surface component.

Original plans, root readings and radial fans retain their exact shared stages and one common radial parameter bank. -/
structure Acquisition (request : SurfaceRequest.Request prepared basis
  target coefficientTarget coverFloor floor)
    (capSample : Charts.Reciprocal.Cap.Primitives.Sample cap differential index box)
    (polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box)
      (minimum energyFloor : Nat) where
  /-- The supplied numerical stage pays the original complete-surface request. -/ index_later : request.index ≤ index
  /-- The complete original component plan spine. -/ plans :
    SurfacePlans.Plans capSample polynomials minimum request.entries
  /-- The retained common root-reading stage. -/ readingIndex : Nat
  /-- The shared reading stage is exactly the maximum computed from the retained plans. -/ reading_eq : readingIndex =
    plans.stage request.entries
  /-- The root readings acquired on those exact original plans. -/ readings :
    SurfacePlans.Plans.Readings request.entries plans readingIndex
  /-- The radial fan preparations on those exact acquired readings. -/ fans :
    SurfaceSamples.Plans.FanPreparations energyFloor request.entries
    plans readings
  /-- The cached common radial depth. -/ radialDepth : Nat
  /-- The cached depth is exactly the maximum required by the retained fans. -/ radial_eq : radialDepth =
    SurfaceSamples.Plans.FanPreparations.depth request.entries plans
    readings fans
  /-- The shared radial parameter bank at the retained depth. -/ parameters : Path.Dyadic.RadialTriangles.Parameters
    radialDepth

constructive_injectivity Acquisition

/-- Prepare all component plans, acquire their original readings and cache the common radial parameter bank.

The supplied numerical stage pays the request floor, and the branch condition certifies the retained root acquisition.
-/
def acquire (request : SurfaceRequest.Request prepared basis target
  coefficientTarget coverFloor floor)
    (capSample : Charts.Reciprocal.Cap.Primitives.Sample cap differential index box)
    (polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box)
      (minimum energyFloor : Nat)
    (branch : Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) (later : request.index ≤
      index) :
    Acquisition request capSample polynomials
      minimum energyFloor :=
  let plans := SurfacePlans.Plans.build capSample polynomials minimum
    request.entries
  let readingIndex := plans.stage request.entries
  let readings := SurfacePlans.Plans.acquire branch readingIndex
    request.entries plans (request.index_eq.symm.trans_le later) le_rfl
  let fans := SurfaceSamples.Plans.prepareFans energyFloor
    request.entries plans readings
  let radialDepth := SurfaceSamples.Plans.FanPreparations.depth
    request.entries plans readings fans
  ⟨later, plans, readingIndex, rfl, readings, fans, radialDepth, rfl, Path.Dyadic.RadialTriangles.Parameters.build
    radialDepth⟩

namespace Acquisition

variable (acquired : Acquisition
  request capSample polynomials minimum energyFloor)

/-- The exact coefficient-weighted sample spine on this cached component acquisition. -/
def Samples (coefficients : GaussianVector genus) :=
  SurfaceSamples.Plans.Samples coefficients acquired.radialDepth
    request.entries acquired.plans acquired.readings acquired.fans

/-- The exact prepared-comparison spine on the supplied retained component samples. -/
def Comparisons {coefficients : GaussianVector genus} (samples : acquired.Samples
  coefficients) :=
  Samples.PreparedComparisons request.entries
    acquired.plans acquired.readings acquired.fans samples

/-- The exact certified trace spine on the supplied original samples and comparisons. -/
def Traces {coefficients : GaussianVector genus} (samples : acquired.Samples
  coefficients)
    (comparisons : acquired.Comparisons samples) :=
  Samples.PreparedTraces request.entries
    acquired.plans acquired.readings acquired.fans samples comparisons

set_option genInjectivity false in
/-- The cached component samples, prepared comparisons, traces and complete Gaussian total.

Exact readback equalities retain all intermediate values, and the original surface budget bounds the total's imaginary
reading. -/
structure Evaluation (coefficients : GaussianVector genus) where
  /-- The samples on the exact retained component acquisition. -/ samples : acquired.Samples coefficients
  /-- The prepared child-integral comparisons on those original samples. -/ comparisons : acquired.Comparisons samples
  /-- The certified original component traces on those comparisons. -/ traces : acquired.Traces samples comparisons
  /-- The cached ordered component trace readings. -/ values : List InverseRootPolynomial.Gaussian
  /-- The cached values are exactly the readings of the retained component traces. -/ values_eq : values =
    Samples.preparedValues request.entries
    acquired.plans acquired.readings acquired.fans samples comparisons traces
  /-- The cached complete Gaussian sum of component readings. -/ total : InverseRootPolynomial.Gaussian
  /-- The cached total is exactly the finite sum of the cached component values. -/ total_eq : total =
    Gaussian.Norm.Sum.Basic.gaussianSum values
  /-- The original complete-surface target pays the homogeneous lower bound on the total's imaginary reading. -/ lower :
    -(target * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) ≤ total.im / 4

constructive_injectivity Evaluation

/-- Sample and compare the cached component acquisition using the supplied coefficient vector.

The original component trace budgets pay the complete total bound without recomputing the retained plans, readings or
radial bank. -/
def evaluate (coefficients : GaussianVector genus) (branch :
  Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) :
    acquired.Evaluation coefficients := open Algebra in open Rat in by
  let samples := SurfaceSamples.Plans.sample coefficients
    acquired.parameters branch request.entries acquired.plans acquired.readings acquired.fans
    acquired.reading_eq.symm.le acquired.radial_eq.symm.le
  let comparisons := Samples.comparePrepared
    request.entries acquired.plans acquired.readings acquired.fans samples
    (request.index_eq.symm.trans_le acquired.index_later)
  let traces := Samples.prepareTraces branch
    request.entries acquired.plans acquired.readings acquired.fans samples comparisons
    acquired.reading_eq.symm.le
  let values := Samples.preparedValues
    request.entries acquired.plans acquired.readings acquired.fans samples comparisons traces
  let total := Gaussian.Norm.Sum.Basic.gaussianSum values
  have lower := Samples.preparedLower
    request.entries acquired.plans acquired.readings acquired.fans samples comparisons traces
  have normNonnegative : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
      InverseRootPolynomial.Coordinate)) _ (fun row => Gaussian.Basic.Canonical.normSq_nonneg
      (coefficients row)))
  have paid : (request.entries.length : InverseRootPolynomial.Coordinate) * (request.localTarget +
    request.localTarget + request.localTarget) ≤ target := by
    rw [request.entries_length]
    exact (show (prepared.components.length : InverseRootPolynomial.Coordinate) * (request.localTarget +
      request.localTarget + request.localTarget) =
      (3 * (prepared.components.length : InverseRootPolynomial.Coordinate)) * request.localTarget by
        ring1).trans_le
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide : (3 :
          InverseRootPolynomial.Coordinate) ≤ 4) (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)))
        request.positive.le).trans request.paid)
  exact ⟨samples, comparisons, traces, values, rfl, total, rfl,
    (Fraction.Order.Arithmetic.neg_le_neg_direct (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct paid
      normNonnegative)).trans lower⟩

end Acquisition
end Request
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceEnergy.Request

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceEnergy.Request.Acquisition.Evaluation

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceEnergy.Request.Acquisition.Evaluation
