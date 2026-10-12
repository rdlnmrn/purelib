module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Riemann.RootContinuation.NewtonRawEnergyGrid

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Riemann.RootContinuation.NewtonOddRawAcquisition
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Gaussian.Basic
public import Purelib.Riemann.RootContinuation.NewtonOddRawRequest
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Topology.NewtonObservationSurfaceLower
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.LiftedPuncturedGrid

public section

/-! Construct every auxiliary owner for odd raw coercivity from the
retained corrected period preparation and the intrinsic odd-degree case. -/
namespace Purelib.Riemann.RootContinuation.NewtonAutomaticOddRaw

open Purelib

open Purelib.Data.Rat

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Riemann.RootContinuation.NewtonOddRawRequest (OddRawRequest)
open Purelib.Riemann.Topology.NewtonObservationSurfaceLower (surfaceLowerConstant surfaceLowerConstant_positive)
open Purelib.LinearAlgebra.Gaussian.Energy (unnormalizedEnergyForm)
open Purelib.Riemann.Periods.PeriodMatrix (sampledMatrix)
open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin
    2}
  {ordered : Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank
    sheet} {paired : Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered}

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
set_option genInjectivity false in
/-- Automatically constructed odd-degree raw-energy certificate.

Retains the original degree, protected observations, Newton preparation, reciprocal collar and cap bounds, actual
unit-radius request and a positive lower constant with its exact identity. -/
structure AutomaticOddRaw (prepared : Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired) (first : Fin genus)
  (floor : Nat) where
  /-- Odd-degree equation for the original curve polynomial. -/ degree : curve.polynomial.natDegree = 2 * genus + 1
  /-- Actual protected observations on the original branch bank. -/ observations : ProtectedObservations
    base.bank.toBranchCellBank
  /-- Newton preparation retaining that branch bank. -/ preparation : NewtonPreparation base.bank.toBranchCellBank
  /-- Reciprocal exterior collar of the original curve. -/ collar : Charts.Reciprocal.ReciprocalExteriorCollar.Data
    curve
  /-- Inner inverse cap over the retained collar. -/ cap : Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar
  /-- Regular-region bounds for that exact cap. -/ regular : Charts.Reciprocal.Disk.RegularBounds.Data cap
  /-- Actual odd raw-energy request at unit radius. -/ request : OddRawRequest prepared observations preparation 1
    regular first floor
  /-- Cached positive energy lower constant. -/ lower : Fraction.Rational
  /-- The cached lower constant is half the protected surface lower constant. -/ lower_eq : lower = surfaceLowerConstant
    observations / 2
  /-- Strict positivity of the retained lower constant. -/ lower_positive : 0 < lower

constructive_injectivity AutomaticOddRaw

namespace AutomaticOddRaw

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
open Purelib.Riemann.RootContinuation in
/-- Construct all data for the odd-degree original-energy bound.

Builds protected observations and Newton data from the original branch bank, constructs the reciprocal regular region
and unit-radius grid, and retains the resulting odd raw request. -/
@[expose] def build (prepared : Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired) (degree :
  curve.polynomial.natDegree = 2 * genus + 1) (first : Fin genus) (floor : Nat) :
    AutomaticOddRaw prepared first floor :=
  let observations := ProtectedObservations.build base.bank.toBranchCellBank
  let preparation := NewtonPreparation.build base.bank.toBranchCellBank
  let collar := Charts.Reciprocal.ReciprocalExteriorCollar.Data.build curve
  let cap := Charts.Reciprocal.ReciprocalInnerInverse.Data.build curve collar 0
  let regular := Charts.Reciprocal.Disk.RegularBounds.Data.build cap
  let grid := NewtonRawEnergyGrid.RawEnergyGrid.build observations preparation 1 (by decide)
  let request := OddRawRequest.build prepared observations preparation 1 regular grid first floor degree
  ⟨degree, observations, preparation, collar, cap, regular, request, surfaceLowerConstant observations / 2, rfl,
    Fraction.Order.Field.div_pos_direct (surfaceLowerConstant_positive observations) (by decide)⟩

variable {prepared : Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired} {first : Fin
  genus} {floor : Nat}

open Purelib.LinearAlgebra.Gaussian in
open Purelib.Riemann.Readings in
open Purelib.Riemann.RootContinuation in
/-- The retained automatic lower constant bounds original sampled period energy.

At every stage after the actual request index, applies the odd raw certificate to the supplied coefficient vector and
original A/B sampled matrices. -/
theorem accurate (data : AutomaticOddRaw prepared first floor) (stage : Nat)
    (later : data.request.index ≤ stage) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    data.lower * PreparedObservationCoercivity.coefficientNormSq coefficients ≤
      Energy.unnormalizedEnergyForm coefficients
        (sampledMatrix prepared.periodData.aMatrix stage) (sampledMatrix prepared.periodData.bMatrix stage) := by
  rw [data.lower_eq]
  exact NewtonOddRawAcquisition.OddRawRequest.lower data.request stage later coefficients

end AutomaticOddRaw
end Purelib.Riemann.RootContinuation.NewtonAutomaticOddRaw
