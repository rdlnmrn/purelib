module
import Purelib.Data.List.Membership
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.SourceSurfaceAcquisition
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
public import Purelib.Riemann.Topology.NewtonOddSurfaceGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RamifiedComponent
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonRawEnergyBudget
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisSourceCuts
public import Purelib.Riemann.RootContinuation.NewtonRawOddEnergyBudget
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Branches.NewtonSharedExteriorCuts
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Gaussian.Field
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.CanonicalJoiningComponents

public section

/-! Acquire the canonical odd component and its source stages from the shared mesh geometry. -/
namespace Purelib.Riemann.RootContinuation.NewtonOddSourcePreparation

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib

open Purelib.Data.Rat

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Riemann.RootContinuation.NewtonRawOddEnergyBudget
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Normalization
open Purelib.Riemann.Topology.NewtonOddSurfaceGeometry (OddSurfaceGeometry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceComponent)
open
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  (built_components_ramified)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms (ExteriorProgram)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation (CommonBasisPreparation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse (UniformBounds)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds (BasisBounds)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules.RequestedSurfaceRuns
  (Schedules prepare)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis
  (SourceSurfaceAcquisition)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices (occurrenceAt)

variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {preparation : NewtonPreparation original} {gridTarget radius : Data.Rat.Fraction.Rational}
  {grid : NewtonGrid preparation gridTarget radius}
  (observations : ProtectedObservations original) (partitions : SurfacePartitions observations grid)
  {lifted : LiftedPuncturedGrid grid.punctured}
  {collar : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  (regular : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap)
  (domains : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames
    grid.faces.regulars)

variable (geometry : OddSurfaceGeometry observations partitions regular domains) (first : Fin genus) (floor : Nat)

open Purelib.Curves.Hyperelliptic in
set_option genInjectivity false in
/-- Retained exterior source preparation for an odd branch.

Keeps the canonical component, common basis preparation, padded inverse and basis bounds, original inputs and schedules,
and the actual source-surface acquisition. -/
structure OddSourcePreparation where
  /-- Actual exterior surface component for the selected standard differential. -/ component :
    Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceComponent regular
    domains (standardDifferential first)
  /-- The retained component equals its canonical exterior-program construction. -/ component_eq : component =
    Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceComponent.build regular
    domains (Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram.build lifted (standardDifferential first) 0)
  /-- Common basis preparation of the retained component. -/ retained :
    Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation component.prepared
  /-- Uniform inverse bounds on the original padded region. -/ bounds :
    Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded
  /-- Basis bounds derived from those exact inverse bounds. -/ basis :
    Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds
  /-- Retained common-preparation inputs at the requested floor. -/ inputs : retained.Inputs floor
  /-- Actual surface-run schedules at the odd physical target. -/ schedules :
    Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules.RequestedSurfaceRuns.Schedules
    (geometry.shared.source.select first) geometry.whole retained inputs (rawOddPhysicalTarget observations) floor
  /-- Source-surface acquisition retaining those schedules, pieces and basis bounds. -/ acquired :
    Curves.Hyperelliptic.Meshes.Newton.Basis.SourceSurfaceAcquisition schedules geometry.pieces
    basis (rawOddSourceTarget observations) 1 0 floor

constructive_injectivity OddSourcePreparation

namespace OddSourcePreparation

open Purelib.Curves.Hyperelliptic in
/-- Construct the retained odd source schedules and acquisition.

Reuses the canonical component and common basis preparation, builds the padded bounds once, and allocates the distinct
physical and source targets with the requested floor. -/
@[expose] def build : OddSourcePreparation observations partitions regular domains geometry first floor :=
  let component :=
    Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceComponent.build regular
    domains (Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram.build lifted (standardDifferential first) 0)
  let retained := Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation.build component.prepared
  let bounds := Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds.build regular.padded
  let basis := Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds.build bounds
  let inputs := retained.inputs floor
  let schedules := Meshes.PuncturedGrid.Exterior.Basis.SurfaceRunSchedules.RequestedSurfaceRuns.prepare
    (geometry.shared.source.select first) geometry.whole retained inputs
    (rawOddPhysicalTarget observations) (rawOddPhysicalTarget_positive observations) floor
  let acquired := Curves.Hyperelliptic.Meshes.Newton.Basis.SourceSurfaceAcquisition.build
    schedules geometry.pieces basis (rawOddSourceTarget observations) 1 0 floor
    (rawOddSourceTarget_positive observations) (by decide)
  ⟨component, rfl, retained, bounds, basis, inputs, schedules, acquired⟩

variable {observations partitions regular domains geometry first floor}
  (source : OddSourcePreparation observations partitions regular domains geometry first floor)

section
open Purelib.Curves.Hyperelliptic
/-- The retained component belongs to the selected exterior preparation.

Under origin order one, the canonical component list is a singleton and the stored component equality identifies its
actual member. -/
theorem component_member (branch : Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) :
    source.component ∈ (geometry.preparations.get first).components := by
  rw [geometry.preparation_readback,
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation.built_components_ramified
    branch]
  exact Data.List.Membership.mem_singleton.mpr source.component_eq

/-- An occurrence of the retained component belongs to the full preparation.

Uses origin order one and the component membership witness without changing the original occurrence index or list owner.
-/
theorem occurrence_member (branch : Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (outer : Fin source.component.prepared.occurrences.length) :
    Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt source.component.prepared.occurrences outer ∈
      (geometry.preparations.get first).occurrences :=
  (geometry.preparations.get first).component_occurrence_member source.component (source.component_member branch) outer

end

/-- The actual source acquisition index respects the requested floor. -/
theorem floor_le : floor ≤ source.acquired.index := source.acquired.initial_index_le

end OddSourcePreparation
end Purelib.Riemann.RootContinuation.NewtonOddSourcePreparation
