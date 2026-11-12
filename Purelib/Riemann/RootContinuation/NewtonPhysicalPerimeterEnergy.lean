module
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalComponents
public import Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalEndpointReadback
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Dependent
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Riemann.Periods.BilinearCombination
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
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.SeamAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ConjugateFacePerimeters
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Integration.Path.Dyadic.RadialTriangles
import Purelib.Riemann.RootContinuation.NewtonPhysicalEndpointEnergy
import Purelib.Integration.Polynomial.Rectangle.ClippedPerimeterCombination
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshEnergy
import Purelib.Data.Vector.Basic
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Riemann.Integration.RectangularStitchedPerimeter
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisAccuracy
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshReindex
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Riemann.Meshes.RectangularObservationMesh

public section

/-! Read the basis-pair exterior energy as the actual perimeter of the
coefficient-combined primitive, with every owner junction retained. -/
namespace Purelib.Riemann.RootContinuation.NewtonPhysicalPerimeterEnergy

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (CommonCuts Preflights)
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation (CapAttachment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (AllSurfacePreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds (RegularBasisBounds)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest (RegularBasisRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisAggregate (RegularBasisCap)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests (PerimeterSamples)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.SeamAreas (seamValues)
open Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalComponents.SynchronizedSurfaceRequests.PerimeterSamples
  (componentSum)
open Purelib.Riemann.RootContinuation.NewtonPhysicalEndpointEnergy.SynchronizedSurfaceRequests.PerimeterSamples
  (component_combination exterior_cap_energy_upper)
open Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalEndpointReadback.SynchronizedSurfaceRequests.PerimeterSamples
  (cachedEndpointSideSum)
open Purelib.Riemann.Normalization
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)
open _root_.Purelib.Data.Gaussian.Basic (conj)
open Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh (ClippedAssembly)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve branches
    higher}
  {preparation : NewtonPreparation original} {target radius : Rational} {grid : NewtonGrid preparation
    target radius}
  {lifted : LiftedPuncturedGrid grid.punctured} {domains :
    FaceDomainBank lifted.frames grid.faces.regulars}
  {stage : Nat} {cache : Numerics domains stage}
  {collar : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {fixed : (sheet : Fin 2) → Preflights
    domains sheet} {surfaceTarget physicalTarget : Rational}
  {minimum floor coarseDepth : Nat}
  {basis : PhysicalBasisRequest regular domains
    physicalTarget minimum floor}
  {previous : CommonCuts domains} {selected
    : BasisSourceCuts basis.preparations previous}
  {initial : TwoSheetRequest (fun sheet =>
    RegularMeshes.build domains selected.cuts sheet
    coarseDepth) fixed surfaceTarget}
  {request : PhysicalMeshRequest basis initial}

namespace SynchronizedSurfaceRequests.PerimeterSamples

open Purelib.Curves.Hyperelliptic in
open Purelib.LinearAlgebra.Gaussian in
/-- Whole clipped face assembly for coefficient-combined energy values.

The mesh comes from the retained physical request and the seam values from the exact numerical cache, face and sheet. -/
@[expose] def WholeFaceEnergyAssembly
    {coarse : (sheet : Fin 2) → RegularMeshes domains sheet}
    {initial : TwoSheetRequest coarse fixed surfaceTarget} (request :
      PhysicalMeshRequest basis initial) (cache : Numerics domains
      stage)
    (coefficients : Energy.GaussianVector genus) (position : Fin grid.faces.regulars.length)
      (sheet : Fin 2) :=
  ClippedAssembly ((request.surface.entries.get sheet).meshes.entries.get position)
    (seamValues (sheet := sheet) cache coefficients position)

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.LinearAlgebra.Gaussian in
/-- Read the selected side area of a retained whole-face perimeter. -/
@[expose] def wholePerimeterSide
    {coarse : (sheet : Fin 2) → RegularMeshes domains sheet}
    {initial : TwoSheetRequest coarse fixed surfaceTarget} {request :
      PhysicalMeshRequest basis initial}
    {coefficients : Energy.GaussianVector genus}
    {position : Fin grid.faces.regulars.length} {sheet : Fin 2}
    {assembly : WholeFaceEnergyAssembly request cache coefficients position sheet}
    (perimeter : assembly.Perimeter) : GridSide → Basic.Canonical
  | .bottom => perimeter.bottom
  | .right => perimeter.right
  | .top => perimeter.top
  | .left => perimeter.left

open Purelib.Algebra in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Rectangle in
open Purelib.LinearAlgebra.Gaussian in
/-- Expand a whole perimeter side into conjugate basis-pair areas.

Uses the exact clipped-perimeter combination on the retained cache anchors and offsets, keeping the same face and sheet.
-/
theorem wholePerimeterSide_combination (faces : request.FacePerimeterBank cache)
    (coefficients : Energy.GaussianVector genus)
    (position : Fin grid.faces.regulars.length) (sheet : Fin 2)
    {assembly : WholeFaceEnergyAssembly request cache coefficients position sheet}
    (perimeter : assembly.Perimeter) (side : GridSide) :
    wholePerimeterSide perimeter side =
      sumFin (fun first => sumFin (fun second => conj (coefficients
        first) *
        coefficients second *
        ((faces.get first).get second).area position sheet side)) := by
  let first := fun i column row point => conj ((cache.atDomain position sheet
    i).anchors.alignedValue
    (cache.atDomain position sheet i).offsets column row point)
  let second := fun i column row point => (cache.atDomain position sheet i).anchors.alignedValue
    (cache.atDomain position sheet i).offsets column row point
  let pairs := fun i j => (((faces.get i).get j).perimeters.get position).get sheet
  cases side with
  | bottom =>
      simpa only [wholePerimeterSide, Meshes.PuncturedGrid.ConjugateFacePerimeters.area,
        -eq_self, -iff_self]
        using ClippedPerimeterCombination.bottom_combination
          (fun i => conj (coefficients i)) coefficients first second perimeter pairs
  | right =>
      simpa only [wholePerimeterSide, Meshes.PuncturedGrid.ConjugateFacePerimeters.area,
        -eq_self, -iff_self]
        using ClippedPerimeterCombination.right_combination
          (fun i => conj (coefficients i)) coefficients first second perimeter pairs
  | top =>
      simpa only [wholePerimeterSide, Meshes.PuncturedGrid.ConjugateFacePerimeters.area,
        -eq_self, -iff_self]
        using ClippedPerimeterCombination.top_combination
          (fun i => conj (coefficients i)) coefficients first second perimeter pairs
  | left =>
      simpa only [wholePerimeterSide, Meshes.PuncturedGrid.ConjugateFacePerimeters.area,
        -eq_self, -iff_self]
        using ClippedPerimeterCombination.left_combination
          (fun i => conj (coefficients i)) coefficients first second perimeter pairs

attribute [local congr] sumFin_congr

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.LinearAlgebra.Gaussian in
open Purelib.Riemann.Periods in
/-- Physical perimeter energy equals the combined whole-face exterior sum.

Commutes the finite sheet and basis-pair sums and retains the original neighbor classification and side orientations. -/
theorem physicalPerimeterEnergy_eq_combined (faces : request.FacePerimeterBank cache)
    (coefficients : Energy.GaussianVector genus)
    (assemblies : (position : Fin grid.faces.regulars.length) → (sheet : Fin 2) →
      WholeFaceEnergyAssembly request cache coefficients position sheet)
    (perimeters : (position : Fin grid.faces.regulars.length) → (sheet : Fin 2) → (assemblies position sheet).Perimeter)
    (neighbors : PuncturedFaces.NeighborBank grid.faces) :
    faces.componentEnergy neighbors coefficients =
      componentSum neighbors .exterior (fun side position =>
        sumFin (fun sheet => wholePerimeterSide (perimeters position sheet) side)) := by
  have sideSum (side : GridSide) (position : Fin grid.faces.regulars.length) :
      sumFin (fun sheet => wholePerimeterSide (perimeters position sheet) side) =
      sumFin (fun first => sumFin (fun second => conj (coefficients
        first) *
        coefficients second *
        sumFin (fun sheet => ((faces.get first).get second).area position sheet side))) := by
    rw [sumFin_congr (fun sheet => wholePerimeterSide_combination faces coefficients position sheet
      (perimeters position sheet) side)]
    exact BilinearCombination.sumFin_combination (fun first => conj (coefficients first))
      coefficients _
  have expanded : componentSum neighbors .exterior (fun side position =>
      sumFin (fun sheet => wholePerimeterSide (perimeters position sheet) side)) =
      componentSum neighbors .exterior (fun side position =>
        sumFin (fun first => sumFin (fun second => conj (coefficients
          first)
          * coefficients second *
          sumFin (fun sheet => ((faces.get first).get second).area position sheet side)))) := by
    simp only [componentSum, sideSum, -eq_self, -iff_self]
    rfl
  exact (component_combination neighbors coefficients _).symm.trans expanded.symm

variable (selected)
  {differential : Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {prepared :
    AllSurfacePreparation
    regular domains differential}
  (attached : CapAttachment prepared)
  {box : Geometry.Rational.Box} {polynomials :
    RegularBasisPolynomials cap stage box}
  {bounds : RegularBasisBounds polynomials} {capTarget
    : Rational} {capMinimum : Nat}
  (capRequest : RegularBasisRequest bounds
    attached.caps.length capTarget capMinimum)
  {geometry :
    CapAttachment.ReciprocalGeometry
    attached}
  {parameters : Integration.Path.Dyadic.RadialTriangles.Parameters capRequest.depth}

open Purelib.Algebra in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
open Purelib.Data.Rat in
open Purelib.LinearAlgebra.Gaussian in
open Purelib.Riemann.Readings in
/-- Bound combined whole perimeters with cached endpoint and cap corrections.

Transports the physical exterior-cap estimate through the exact perimeter readback, preserving the explicit target
payment and retained samples. -/
theorem combined_exterior_cap_energy_upper (entries : request.Readings cache) (faces : request.FacePerimeterBank cache)
    (attachments : Vector.DependentVector (fun first =>
      CapAttachment (basis.preparations.get first)))
    (neighbors : PuncturedFaces.NeighborBank grid.faces)
    (evaluated : basis.Evaluations polynomials capRequest.depth)
    (later : request.index ≤ stage) (spatial : basis.depth ≤ capRequest.depth)
    (caps : RegularBasisCap geometry parameters polynomials)
    (coefficients : Energy.GaussianVector genus)
    (assemblies : (position : Fin grid.faces.regulars.length) → (sheet : Fin 2) →
      WholeFaceEnergyAssembly request cache coefficients position sheet)
    (perimeters : (position : Fin grid.faces.regulars.length) → (sheet : Fin 2) → (assemblies position sheet).Perimeter)
    (capSample : (capRequest.certify caps).Evaluation coefficients)
    (allowance : Rational) (nonnegative : 0 ≤ allowance)
    (paid : (genus : Rational) ^ 2 * physicalTarget ≤ 16 * allowance ^ 2) :
    (componentSum neighbors .exterior (fun side position =>
        sumFin (fun sheet => wholePerimeterSide (perimeters position sheet) side)) -
      componentSum neighbors .exterior (cachedEndpointSideSum cache coefficients) +
      PhysicalMeshRequest.Readings.capJoiningEnergy attachments
        polynomials coefficients).im / 4 ≤
        (capTarget + allowance) * PreparedObservationCoercivity.coefficientNormSq coefficients := by
  have bound := exterior_cap_energy_upper selected attached capRequest entries faces attachments neighbors
    evaluated later spatial caps coefficients capSample allowance nonnegative paid
  rw [physicalPerimeterEnergy_eq_combined faces coefficients assemblies perimeters neighbors] at bound
  exact bound

end SynchronizedSurfaceRequests.PerimeterSamples
end Purelib.Riemann.RootContinuation.NewtonPhysicalPerimeterEnergy
