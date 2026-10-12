module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Riemann.RootContinuation.NewtonOddSourcePreparation
import Purelib.Riemann.RootContinuation.NewtonRawEnergyBudget
import Purelib.Riemann.RootContinuation.NewtonRawOddEnergyBudget

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
public import Purelib.Riemann.RootContinuation.NewtonOddRawRequest
public import Purelib.Riemann.Periods.NewtonRawPeriodSamples
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.OriginalLower
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Topology.NewtonObservationSurfaceLower
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineAreaRequests
import Purelib.Riemann.RootContinuation.NewtonRawEnergyGrid
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

public section

/-! Acquire one later face cache and prove odd raw coercivity on the original A/B samples. -/
namespace Purelib.Riemann.RootContinuation.NewtonOddRawAcquisition

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis

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
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential sampledMatrix)
open Purelib.Riemann.Topology.NewtonObservationSurfaceLower (surfaceLowerConstant)
open Purelib.LinearAlgebra.Gaussian.Energy (unnormalizedEnergyForm)
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests.NewtonPreparation (outerCount)

variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin
    2}
  {ordered : Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank
    sheet} {paired : Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered} {prepared :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired}
  {observations : ProtectedObservations base.bank.toBranchCellBank}
  {preparation : NewtonPreparation base.bank.toBranchCellBank} {radius : Data.Rat.Fraction.Rational}
  {collar : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {first : Fin genus} {floor : Nat}
  (request : OddRawRequest prepared observations preparation radius regular first floor)

open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Periods in
set_option genInjectivity false in
/-- Numerical cache and raw period samples for an odd raw request.

Both are tied to the original retained grid domains and the supplied stage; the period samples reuse that exact cache.
-/
structure OddRawAcquisition (stage : Nat) where
  /-- Actual basis-indexed numerical cache on the retained grid domains. -/ cache :
    Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics request.grid.domains stage
  /-- Raw period samples built from that exact cache and request owners. -/ periods :
    NewtonRawPeriodSamples.Request.RawPeriodSamples prepared request.sewing request.period cache

constructive_injectivity OddRawAcquisition

namespace OddRawAcquisition

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
open Purelib.Riemann.Periods in
/-- Acquire the basis cache once and derive its raw period samples.

Builds each standard differential's face primitive bank at the selected stage, then passes that dependent cache to the
retained period and sewing requests. -/
@[expose] def build (stage : Nat) : OddRawAcquisition request stage :=
  let cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics request.grid.domains stage :=
    Vector.DependentVector.ofFn fun row =>
    Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank.build (standardDifferential row) stage
      request.grid.domains
  ⟨cache, NewtonRawPeriodSamples.Request.RawPeriodSamples.build prepared request.sewing request.period cache⟩

variable {request} {stage : Nat} (acquired : OddRawAcquisition request stage)

include acquired

open Purelib.Curves.Hyperelliptic in
open Purelib.LinearAlgebra.Gaussian in
open Purelib.Riemann.Readings in
open Purelib.Riemann.RootContinuation in
/-- The retained acquisition supplies a positive lower bound for original period energy.

After the raw request index, combines its exact source occurrence, coercivity, annular, sewing, exterior and
matrix-comparison certificates using the actual cached readings. -/
theorem lower (later : request.index ≤ stage) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    surfaceLowerConstant observations / 2 * PreparedObservationCoercivity.coefficientNormSq coefficients ≤
      Energy.unnormalizedEnergyForm coefficients
        (sampledMatrix prepared.periodData.aMatrix stage)
        (sampledMatrix prepared.periodData.bMatrix stage) :=

    OriginalLower.CommonBasisPreparation.RequestedSurfaceRuns.SourceSurfaceAcquisition.CoercivitySchedule.original_lower
    request.coercivity acquired.cache coefficients
    (NewtonOddSourcePreparation.OddSourcePreparation.occurrence_member request.source request.branch)
    (request.coercivity_le.trans later) request.grid.neighbors
    (NewtonRawEnergyBudget.rawEnergyAllowance_positive observations)
    acquired.periods.triangles acquired.periods.surfaces acquired.periods.pairs acquired.periods.selected
    acquired.periods.periods request.period.cut (request.period_le.trans later)
    request.sewing.sewing (request.sewing_le.trans later)
    request.joining.joining ((request.joining.joining_le request.grid request.sewing).trans (request.joining_le.trans
      later))
    request.sewing.annular acquired.periods.annular (request.annular_le.trans later) acquired.periods.holes
    request.source.component_eq
    (NewtonRawOddEnergyBudget.rawOddPhysicalTarget_positive observations)
    (le_refl _) request.branch request.degree
    (NewtonRawEnergyBudget.rawEnergyGridTarget_remaining observations
      (Meshes.Newton.Annulus.AreaRequests.NewtonPreparation.outerCount preparation))
    (NewtonRawEnergyBudget.rawEnergyGridTarget_annular observations
      (Meshes.Newton.Annulus.AreaRequests.NewtonPreparation.outerCount preparation))
    rfl rfl rfl request.comparison (request.comparison_le.trans later) request.sheet_eq

end OddRawAcquisition

namespace OddRawRequest

open Purelib.LinearAlgebra.Gaussian in
open Purelib.Riemann.Readings in
/-- Acquire and prove the original period-energy lower bound at a later stage.

Builds the stage cache and raw samples for this request, then applies their retained coercivity certificate with half
the surface lower constant. -/
theorem lower (stage : Nat) (later : request.index ≤ stage) (coefficients :
  LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    surfaceLowerConstant observations / 2 * PreparedObservationCoercivity.coefficientNormSq coefficients ≤
      Energy.unnormalizedEnergyForm coefficients
        (sampledMatrix prepared.periodData.aMatrix stage)
        (sampledMatrix prepared.periodData.bMatrix stage) :=
  (OddRawAcquisition.build request stage).lower later coefficients

end OddRawRequest
end Purelib.Riemann.RootContinuation.NewtonOddRawAcquisition
