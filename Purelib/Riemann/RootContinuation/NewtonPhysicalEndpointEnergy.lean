module
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalComponents
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Dependent
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisSourceCuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisAggregate
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisRequest
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshEndpoints
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPhysicalComponents
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Integration.Path.Dyadic.RadialTriangles
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalEndpointReadback
public import Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalEndpointReadback
import Purelib.Riemann.Periods.BilinearCombination
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshEnergy
import Purelib.Data.Vector.Basic
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisAccuracy
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshReindex

public section

/-! Identify the cap comparison's physical endpoint energy with the original
cached endpoint correction of the complete Newton observation surface. -/
namespace Purelib.Riemann.RootContinuation.NewtonPhysicalEndpointEnergy

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (CommonCuts Preflights)
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPhysicalComponents (componentEvaluation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues.SideNeighbor (componentValue)
open Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalComponents.SynchronizedSurfaceRequests.PerimeterSamples
  (componentSum)
open Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalEndpointReadback.SynchronizedSurfaceRequests.PerimeterSamples
  (cachedSideEndpoint cachedEndpointSideSum)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshRequest
  (cachedConjugateEndpoint)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity.SelectedSides (value)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (AllSurfacePreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation (CapAttachment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds (RegularBasisBounds)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest (RegularBasisRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisAggregate (RegularBasisCap)
open Purelib.Riemann.Normalization
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_sub sumFin_zero)
open _root_.Purelib.Data.Gaussian.Basic (conj)
open Purelib.Riemann.Periods.BilinearCombination (edgeArea_combination sumFin_combination)

variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {preparation : NewtonPreparation original} {target radius : Data.Rat.Fraction.Rational} {grid : NewtonGrid preparation
    target radius}
  {lifted : LiftedPuncturedGrid grid.punctured} {domains :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames grid.faces.regulars}
  {stage : Nat} {cache : Numerics domains stage}

namespace SynchronizedSurfaceRequests.PerimeterSamples

attribute [local congr] Algebra.FiniteSum.Fin.sumFin_congr

section
open Purelib.Algebra
open Purelib.Curves.Hyperelliptic
open Purelib.Data.Gaussian
open Purelib.LinearAlgebra.Gaussian
/-- Exterior component selection commutes with the coefficient combination.

Checks the actual neighbor classification; non-exterior neighbors contribute zero to each retained basis-pair term. -/
private theorem neighbor_combination {face : RegularFace grid.shrunk.prepared.toBranchCellBank} {side : GridSide}
    (neighbor : PuncturedFaces.SideNeighbor grid.faces face side)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (values : Fin genus → Fin genus →
      Basic.Canonical) :
    Meshes.PuncturedGrid.PhysicalComponentValues.SideNeighbor.componentValue neighbor .exterior (FiniteSum.Fin.sumFin
      (fun first => FiniteSum.Fin.sumFin (fun second =>
      Data.Gaussian.Basic.conj (coefficients first) * coefficients second * values first second))) =
      FiniteSum.Fin.sumFin (fun first => FiniteSum.Fin.sumFin (fun second => Data.Gaussian.Basic.conj (coefficients
        first) *
        coefficients second *
        Meshes.PuncturedGrid.PhysicalComponentValues.SideNeighbor.componentValue neighbor .exterior (values first
          second))) := by
  cases neighbor with
  | exterior equal => rfl
  | neighbor cell member matching location =>
      cases location <;> simp only [Meshes.PuncturedGrid.PhysicalComponentValues.SideNeighbor.componentValue, mul_zero,
        FiniteSum.Fin.sumFin_zero, -eq_self, -iff_self] <;> rfl

/-- Commute the exterior component sum with the conjugate coefficient combination.

Reorders only finite sums and preserves the original four-side signs, neighbor selection and distinct first/second basis
factors. -/
theorem component_combination (neighbors : PuncturedFaces.NeighborBank grid.faces)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (values : GridSide → Fin grid.faces.regulars.length → Fin genus → Fin genus → Basic.Canonical) :
    componentSum neighbors .exterior (fun side position => FiniteSum.Fin.sumFin (fun first => FiniteSum.Fin.sumFin (fun
      second =>
      Data.Gaussian.Basic.conj (coefficients first) * coefficients second * values side position first second))) =
      FiniteSum.Fin.sumFin (fun first => FiniteSum.Fin.sumFin (fun second => Data.Gaussian.Basic.conj (coefficients
        first) *
        coefficients second *
        Meshes.PuncturedGrid.SelectedPhysicalComponents.componentEvaluation neighbors (fun _ => true)
          (fun side position => values side position first second) .exterior)) := by
  have sideSum (side : GridSide) :
      FiniteSum.Fin.sumFin (fun position => Meshes.PuncturedGrid.PhysicalComponentValues.SideNeighbor.componentValue
        (Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.FaceNeighbors.at
        (neighbors.entries.get position) side) .exterior
        (FiniteSum.Fin.sumFin (fun first => FiniteSum.Fin.sumFin (fun second =>
          Data.Gaussian.Basic.conj (coefficients first) * coefficients second * values side position first second)))) =
      FiniteSum.Fin.sumFin (fun first => FiniteSum.Fin.sumFin (fun second => Data.Gaussian.Basic.conj (coefficients
        first) *
        coefficients second *
        FiniteSum.Fin.sumFin (fun position => Meshes.PuncturedGrid.PhysicalComponentValues.SideNeighbor.componentValue
          (Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.FaceNeighbors.at
          (neighbors.entries.get position) side) .exterior
          (values side position first second)))) := by
    rw [FiniteSum.Fin.sumFin_congr (fun position => neighbor_combination
      (Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.FaceNeighbors.at (neighbors.entries.get
      position) side)
      coefficients (values side position))]
    exact sumFin_combination (fun first => Data.Gaussian.Basic.conj (coefficients first)) coefficients _
  have right := sideSum .right
  have left := sideSum .left
  have top := sideSum .top
  have bottom := sideSum .bottom
  dsimp only
    [Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces.FaceNeighbors.at] at right left top bottom
  unfold componentSum
  rw [right, left, top, bottom]
  dsimp only [Meshes.PuncturedGrid.SelectedPhysicalComponents.componentEvaluation,
    Meshes.PuncturedGrid.SelectedPerimeterIdentity.SelectedSides.value]
  simp only [mul_sub, FiniteSum.Fin.sumFin_sub, -eq_self, -iff_self]
  rfl

/-- Expand one cached side endpoint into conjugate basis-pair areas.

Uses the exact edge-area bilinearity for each original side and sheet. -/
private theorem cachedSideEndpoint_combination (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (position : Fin grid.faces.regulars.length) (sheet : Fin 2) (side : GridSide) :
    cachedSideEndpoint cache coefficients position sheet side =
      FiniteSum.Fin.sumFin (fun first => FiniteSum.Fin.sumFin (fun second => Data.Gaussian.Basic.conj (coefficients
        first) *
        coefficients second *
        Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshRequest.cachedConjugateEndpoint cache first
            second
          position sheet side)) := by
  cases side <;> exact edgeArea_combination _ _ _ _ _ _

/-- Expand the cached two-sheet endpoint sum into basis-pair contributions.

Moves the coefficient factors outside the finite sheet sum while preserving the actual cached conjugate endpoints. -/
private theorem cachedEndpointSideSum_combination (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (side : GridSide) (position : Fin grid.faces.regulars.length) :
    cachedEndpointSideSum cache coefficients side position =
      FiniteSum.Fin.sumFin (fun first => FiniteSum.Fin.sumFin (fun second => Data.Gaussian.Basic.conj (coefficients
        first) *
        coefficients second *
        FiniteSum.Fin.sumFin (fun sheet =>
          Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshRequest.cachedConjugateEndpoint cache first
          second position sheet side))) := by
  unfold cachedEndpointSideSum
  rw [FiniteSum.Fin.sumFin_congr (fun sheet => cachedSideEndpoint_combination coefficients position sheet side)]
  exact sumFin_combination (fun first => Data.Gaussian.Basic.conj (coefficients first)) coefficients _

end

variable {collar : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
  Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {fixed : (sheet : Fin 2) → Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights
    domains sheet} {surfaceTarget physicalTarget : Data.Rat.Fraction.Rational}
  {minimum floor coarseDepth : Nat}
  {basis : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisRequest regular domains
    physicalTarget minimum floor}
  {previous : Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains} {selected
    : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisSourceCuts basis.preparations previous}
  {initial : Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest (fun sheet =>
    Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains selected.cuts sheet
    coarseDepth) fixed surfaceTarget}
  {request : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshRequest basis initial}

open Purelib.Algebra in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.LinearAlgebra.Gaussian in
/-- Identify physical endpoint energy with the retained exterior endpoint sum.

Combines the exact cache readback and coefficient expansion using the original neighbor bank and exterior component. -/
theorem physicalEndpointEnergy_eq_newton (entries : request.Readings cache)
    (neighbors : PuncturedFaces.NeighborBank grid.faces) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector
      genus) :
    entries.physicalEndpointEnergy coefficients =
      componentSum neighbors .exterior (cachedEndpointSideSum cache coefficients) := by
  rw [entries.physicalEndpointEnergy_eq_cached neighbors coefficients]
  have expanded : componentSum neighbors .exterior (cachedEndpointSideSum cache coefficients) =
      componentSum neighbors .exterior (fun side position =>
        FiniteSum.Fin.sumFin (fun first => FiniteSum.Fin.sumFin (fun second => Data.Gaussian.Basic.conj (coefficients
          first)
          * coefficients second *
          FiniteSum.Fin.sumFin (fun sheet =>
            Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshRequest.cachedConjugateEndpoint cache first
            second position sheet side)))) := by
    simp only [componentSum, cachedEndpointSideSum_combination, -eq_self, -iff_self]
    rfl
  exact ((component_combination neighbors coefficients _).symm.trans expanded.symm)

variable (selected)
  {differential : Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
    regular domains differential}
  (attached : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment prepared)
  {box : Purelib.Geometry.Rational.Box} {polynomials :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap stage box}
  {bounds : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds.RegularBasisBounds polynomials} {capTarget
    : Data.Rat.Fraction.Rational} {capMinimum : Nat}
  (capRequest : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest.RegularBasisRequest bounds
    attached.caps.length capTarget capMinimum)
  {geometry :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry
    attached}
  {parameters : Purelib.Integration.Path.Dyadic.RadialTriangles.Parameters capRequest.depth}

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
open Purelib.Data.Rat in
open Purelib.LinearAlgebra.Gaussian in
open Purelib.Riemann.Readings in
/-- Bound physical exterior energy after its endpoint correction and cap joining.

Uses the retained physical and cap samples, numerical and spatial bounds, and explicit genus-scaled target payment; the
endpoint correction is read from the original cache. -/
theorem exterior_cap_energy_upper (entries : request.Readings cache) (faces : request.FacePerimeterBank cache)
    (attachments : Vector.DependentVector (fun first =>
      Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment (basis.preparations.get first)))
    (neighbors : PuncturedFaces.NeighborBank grid.faces)
    (evaluated : basis.Evaluations polynomials capRequest.depth)
    (later : request.index ≤ stage) (spatial : basis.depth ≤ capRequest.depth)
    (caps : Meshes.PuncturedGrid.Exterior.CapBasisAggregate.RegularBasisCap geometry parameters polynomials)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (capSample : (capRequest.certify caps).Evaluation coefficients)
    (allowance : Fraction.Rational) (nonnegative : 0 ≤ allowance)
    (paid : (genus : Fraction.Rational) ^ 2 * physicalTarget ≤ 16 * allowance ^ 2) :
    (faces.componentEnergy neighbors coefficients -
      componentSum neighbors .exterior (cachedEndpointSideSum cache coefficients) +
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshRequest.Readings.capJoiningEnergy attachments
        polynomials coefficients).im / 4 ≤
        (capTarget + allowance) * PreparedObservationCoercivity.coefficientNormSq coefficients := by
  have bound := entries.joining_energy_upper selected attached capRequest faces attachments neighbors
    evaluated later spatial caps coefficients capSample allowance nonnegative paid
  rw [physicalEndpointEnergy_eq_newton entries neighbors coefficients] at bound
  exact bound

end SynchronizedSurfaceRequests.PerimeterSamples
end Purelib.Riemann.RootContinuation.NewtonPhysicalEndpointEnergy
