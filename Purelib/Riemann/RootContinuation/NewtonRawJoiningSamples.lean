module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRawEnergyGrid
import Purelib.Riemann.Topology.NewtonRawSewingSchedule
import Purelib.Riemann.Topology.NewtonRawSurfaceSchedule
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Dependent
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.JoiningFamily
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
public import Purelib.Riemann.RootContinuation.NewtonRawJoiningSchedule
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRawEnergyBudget
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Topology.NewtonPhysicalSurfaceSchedule
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineAreaRequests
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Riemann.Branches.NewtonSharedExteriorCuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnEnergyRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisSourceCuts

public section

/-! Cache the regular cap attachment bank and joining evaluations from the
same retained numerical and polynomial banks, at the scheduled reading index. -/
namespace Purelib.Riemann.RootContinuation.NewtonRawJoiningSamples

open Purelib
open Purelib.Data.Rat

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Riemann.RootContinuation.NewtonRawEnergyGrid (RawEnergyGrid)
open Purelib.Riemann.Topology.NewtonRawSurfaceSchedule (SurfaceSchedule)
open Purelib.Riemann.Topology.NewtonRawSewingSchedule (SewingSchedule)
open Purelib.Riemann.RootContinuation.NewtonRawJoiningSchedule (RawJoiningSchedule)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation (CapAttachment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin
    2}
  {ordered : Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank
    sheet} {paired : Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered}
  {preparation : NewtonPreparation base.bank.toBranchCellBank} {radius : Data.Rat.Fraction.Rational}
  {observations : ProtectedObservations base.bank.toBranchCellBank}
  {gridData : RawEnergyGrid observations preparation radius}
  {collar : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {physicalMinimum physicalFloor
    sewingFloor : Nat}
  (surfaceData : SurfaceSchedule gridData regular physicalMinimum physicalFloor)
  (sewingData : SewingSchedule gridData sewingFloor)

variable {floor stage : Nat} {box : Purelib.Geometry.Rational.Box}
  (joiningData : RawJoiningSchedule (paired := paired) surfaceData sewingData floor)
  (polynomials : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap stage
    box)
  (cache : Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics gridData.domains stage)

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
set_option genInjectivity false in
/-- Cached cap attachments and evaluations of a regular joining family.

Retains the actual surface basis preparations, polynomial family and numerical cache at the requested depth and the
joining family's own reading index. -/
structure RawJoiningSamples (depth : Nat) where
  /-- Dependent cap attachments for the retained surface basis preparations. -/ attachments : Vector.DependentVector
    (fun first => Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment
    (surfaceData.schedule.basis.preparations.get first))
  /-- Actual joining-family evaluations at the selected depth and retained reading index. -/ evaluated :
    Meshes.Newton.Regular.JoiningFamily.RegularJoiningFamily.Evaluations joiningData.joining polynomials cache depth
    joiningData.joining.readingIndex

constructive_injectivity RawJoiningSamples

namespace RawJoiningSamples

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
/-- Build joining samples after the retained family index.

Creates the dependent attachment bank and evaluates the original joining request at its exact reading index without
changing the retained spatial depth. -/
@[expose] def build (depth : Nat) (later : joiningData.joining.index ≤ stage) :
    RawJoiningSamples surfaceData sewingData joiningData polynomials cache depth :=
  let attachments := Vector.DependentVector.ofFn fun first =>
    Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.build
    (surfaceData.schedule.basis.preparations.get first)
  let evaluated := Meshes.Newton.Regular.JoiningFamily.RegularJoiningFamily.evaluate joiningData.joining polynomials
    cache depth joiningData.joining.readingIndex later (Nat.le_refl _)
  ⟨attachments, evaluated⟩

end RawJoiningSamples
end Purelib.Riemann.RootContinuation.NewtonRawJoiningSamples
