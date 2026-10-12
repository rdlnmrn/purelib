module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.LinearAlgebra.Gaussian.Energy

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.OriginalRawRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.OriginalRawLower

public section

/-! Construct every auxiliary owner for regular raw coercivity from the
retained corrected period preparation and the intrinsic even-degree case. -/
namespace Purelib.Riemann.RootContinuation.NewtonAutomaticRegularRaw

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
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.OriginalRawRequest (RegularOriginalRawRequest)
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

open Purelib.Curves in
open Purelib.Data in
set_option genInjectivity false in
/-- Retained auxiliary data certifying regular raw-period coercivity in the even-degree case.

The record keeps the original corrected period preparation, observation and Newton owners, reciprocal geometry, request
and exact positive lower constant. -/
structure AutomaticRegularRaw (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
  (floor : Nat) where
  /-- The curve has the intrinsic even degree for the given genus. -/ degree : curve.polynomial.natDegree = 2 * genus +
    2
  /-- The protected observations on the original branch-cell bank. -/ observations : ProtectedObservations
    base.bank.toBranchCellBank
  /-- The retained Newton preparation of that same bank. -/ preparation : NewtonPreparation base.bank.toBranchCellBank
  /-- The reciprocal exterior collar for the original curve. -/ collar :
    Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve
  /-- The retained reciprocal inner inverse on that collar. -/ cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar
  /-- The regularity bounds for the retained reciprocal cap. -/ regular :
    Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap
  /-- The regular raw request using these exact retained owners and floor. -/ request :
    Hyperelliptic.Meshes.Newton.Regular.OriginalRawRequest.RegularOriginalRawRequest prepared observations preparation 1
    regular floor
  /-- The retained raw-energy lower constant. -/ lower : Rat.Fraction.Rational
  /-- The lower constant is half the original observation surface constant. -/ lower_eq : lower = surfaceLowerConstant
    observations / 2
  /-- The retained raw-energy lower constant is strictly positive. -/ lower_positive : 0 < lower

constructive_injectivity AutomaticRegularRaw

namespace AutomaticRegularRaw

open Purelib.Curves in
open Purelib.Data in
/-- Construct all auxiliary owners for a regular raw-period request.

Use the original corrected period preparation and even-degree equation, retaining the generated observation, Newton and
reciprocal data and their positive lower constant. -/
@[expose] def build (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired) (degree :
  curve.polynomial.natDegree = 2 * genus + 2) (floor : Nat) :
    AutomaticRegularRaw prepared floor :=
  let observations := ProtectedObservations.build base.bank.toBranchCellBank
  let preparation := NewtonPreparation.build base.bank.toBranchCellBank
  let collar := Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data.build curve
  let cap := Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data.build curve collar 0
  let regular := Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data.build cap
  let request := Hyperelliptic.Meshes.Newton.Regular.OriginalRawRequest.RegularOriginalRawRequest.build prepared
    observations preparation 1 regular (by decide) floor
  ⟨degree, observations, preparation, collar, cap, regular, request, surfaceLowerConstant observations / 2, rfl,
    Rat.Fraction.Order.Field.div_pos_direct (surfaceLowerConstant_positive observations) (by decide)⟩

variable {prepared : Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired} {floor : Nat}

open Purelib.Riemann in
open Purelib.LinearAlgebra in
/-- Beyond the retained request stage, sampled raw energy bounds the coefficient norm.

The bound uses the exact retained positive lower constant and the original prepared A and B period matrices. -/
theorem accurate (data : AutomaticRegularRaw prepared floor) (first : Fin genus) (stage : Nat)
    (later : data.request.index ≤ stage) (coefficients : Purelib.LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    data.lower * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ≤
      Gaussian.Energy.unnormalizedEnergyForm coefficients
        (sampledMatrix prepared.periodData.aMatrix stage) (sampledMatrix prepared.periodData.bMatrix stage) := by
  rw [data.lower_eq]
  exact data.request.lower stage first data.degree later coefficients

end AutomaticRegularRaw
end Purelib.Riemann.RootContinuation.NewtonAutomaticRegularRaw
