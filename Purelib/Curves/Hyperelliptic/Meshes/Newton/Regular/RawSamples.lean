module
import Purelib.Data.Nat.Addition
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.RawRequest
public import Purelib.Riemann.Periods.NewtonRawPeriodSamples
public import Purelib.Riemann.RootContinuation.NewtonRawJoiningSamples
public import Purelib.Riemann.RootContinuation.NewtonRawCapSampling
public import Purelib.Riemann.Topology.NewtonRawSurfaceSamples
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.JoiningFamily
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisSourceCuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnEnergyRequest
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Branches.NewtonSharedExteriorCuts
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Riemann.RootContinuation.NewtonRawEnergyBudget
import Purelib.Riemann.RootContinuation.NewtonRawEnergyGrid
import Purelib.Riemann.RootContinuation.NewtonRawJoiningSchedule
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Riemann.Topology.NewtonPhysicalSurfaceSchedule
import Purelib.Riemann.Topology.NewtonRawSewingSchedule
import Purelib.Riemann.Topology.NewtonRawSurfaceSchedule

public section

/-! Complete coefficient-independent sampling for a regular raw-energy request.
The cap uses an attachment already retained by the joining sample bank. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.RawSamples

open Purelib.Curves
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Riemann
open Purelib

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin 2}
  {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered}
  (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
  (observations : RootContinuation.NewtonProtectedObservations.ProtectedObservations base.bank.toBranchCellBank)
  (preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation base.bank.toBranchCellBank)
    (radius : Fraction.Rational)
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  (regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap)

variable {newSheet : Fin 2} {floor stage : Nat} {box : Rational.Box}
  (raw : Hyperelliptic.Meshes.Newton.Regular.RawRequest.RegularRawRequest prepared observations preparation radius
    regular newSheet floor)
  (polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap stage box)
  (cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics raw.grid.domains stage) (first
    : Fin genus)

set_option genInjectivity false in
/-- The actual regular period, joining, cap and surface samples at the original retained request stages.

The cap samples belong to the exact joining attachments and the surface readings retain the same original surface. -/
structure RegularRawSamples where
  /-- The actual period cache of the original regular request. -/ period :
    Periods.NewtonRawPeriodSamples.Request.RawPeriodSamples prepared raw.sewing raw.period cache
  /-- The actual joining samples on the original retained surface. -/ joining :
    RootContinuation.NewtonRawJoiningSamples.RawJoiningSamples raw.surface raw.sewing raw.joining polynomials cache
    raw.surface.schedule.basis.depth
  /-- The cap samples on the exact original joining attachments. -/ caps :
    RootContinuation.NewtonRawCapSampling.CapSampling raw.grid regular raw.surface (joining.attachments.get first)
    polynomials
  /-- The actual raw readings of the same retained surface. -/ surface :
    Topology.NewtonRawSurfaceSamples.RawSurfaceReadings raw.surface cache

constructive_injectivity RegularRawSamples

namespace RegularRawSamples

/-- Evaluate the original period, joining, cap and surface requests at their retained sufficient stages.

The even degree certificate gives order zero at the reciprocal origin, and every cache retains its original owner. -/
@[expose] def build (degree : curve.polynomial.natDegree = 2 * genus + 2) (later : raw.index ≤ stage) :
    Hyperelliptic.Meshes.Newton.Regular.RawSamples.RegularRawSamples prepared observations preparation radius regular
      raw polynomials cache first := by
  have joinedLater := raw.boundary.joining_le.trans (raw.boundary_le.trans later)
  have surfaceLater := raw.joining.surface_le.trans joinedLater
  have basisLater := raw.surface.schedule.physical.basis_le.trans
    (raw.surface.schedule.physical_le.trans (raw.surface.schedule_le.trans surfaceLater))
  have balance := Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.degree_balance curve
  rw [degree] at balance
  have chart : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 0 :=
    Data.Nat.Addition.add_left_cancel (balance :
    (2 * genus + 2) + Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = (2 * genus + 2) + 0)
  let period := Periods.NewtonRawPeriodSamples.Request.RawPeriodSamples.build prepared raw.sewing raw.period cache
  let joining := RootContinuation.NewtonRawJoiningSamples.RawJoiningSamples.build raw.surface raw.sewing raw.joining
    polynomials cache
    raw.surface.schedule.basis.depth (raw.joining.joining_le.trans joinedLater)
  let caps := RootContinuation.NewtonRawCapSampling.CapSampling.build raw.grid regular raw.surface
    (joining.attachments.get first) polynomials chart basisLater
  let surface := Topology.NewtonRawSurfaceSamples.RawSurfaceReadings.build raw.surface cache
  exact ⟨period, joining, caps, surface⟩

end RegularRawSamples
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.RawSamples
