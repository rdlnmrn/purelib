module
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Geometry.Rational.Box.Basic

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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateArcFamily
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshPerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.Dyadic.RadialTriangles
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshEnergy
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateChordPolygons
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisAccuracy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshReindex
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Integration.Path.ConjugateIncrementComparison
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring

public section

/-! Express the endpoint correction using the actual cap joining polygons,
while retaining the distinct physical endpoint chords on the shared bank. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshRequest

open Purelib.Algebra
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib
open Purelib.Geometry
open Purelib.Integration
open Purelib.Riemann

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {fixed : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains
    sheet} {surfaceTarget target : Fraction.Rational}
  {minimum floor stage coarseDepth : Nat} {box : Rational.Box}
  {basis : PhysicalBasisRequest regular domains target
    minimum floor}
  {previous : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains} {selected :
    BasisSourceCuts basis.preparations previous}
  {initial : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest (fun sheet =>
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains selected.cuts sheet coarseDepth)
    fixed surfaceTarget}
  {request : PhysicalMeshRequest basis initial} {cache :
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage}

namespace Readings

/-- Sum the original physical endpoint chords with the directions of their retained source occurrences. -/
@[expose] def physicalEndpoints (entries : request.Readings cache) (first second : Fin genus) : Gaussian :=
  FiniteSum.Fin.sumFin fun i =>
    let occurrence := (basis.preparations.get first).occurrences[i.val]'i.isLt
    let endpoint := (((entries.get first).get second).get i).original.endpoint
    if occurrence.sourceForward then endpoint else -endpoint

/-- The endpoint correction is exactly the retained cap joining area minus the oriented physical endpoint sum. -/
theorem endpointCorrection_eq_joining (entries : request.Readings cache)
    (polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap stage box)
      (first second : Fin genus)
    (attached : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment
      (basis.preparations.get first)) :
    entries.endpointCorrection polynomials first second =
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateChordPolygons.CapAttachment.conjugateJoiningArea
        attached (polynomials.get first) (polynomials.get second) -
        entries.physicalEndpoints first second := by
  unfold endpointCorrection
    OccurrenceReadings.endpointCorrection
    physicalEndpoints
  rw [FiniteSum.Fin.sumFin_sub]
  have readback :
      FiniteSum.Fin.sumFin (fun index : Fin (basis.preparations.get first).occurrences.length =>
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateArcFamily.PairedArcRequest.conjugateChordValue
          ((basis.preparations.get first).occurrences[index.val]'index.isLt)
          (polynomials.get first) (polynomials.get second)) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum
        ((basis.preparations.get first).occurrences.map (fun occurrence =>
          Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateArcFamily.PairedArcRequest.conjugateChordValue occurrence
            (polynomials.get first) (polynomials.get second))) := by
    rw [Data.Gaussian.Norm.Sum.Indexed.sumFin_eq_gaussianSum]
    apply congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum
    exact (Data.List.OfFn.Basic.map_ofFn (function := fun index : Fin (basis.preparations.get first).occurrences.length
      =>
      (basis.preparations.get first).occurrences[index.val]'index.isLt)
      (transform := fun occurrence =>
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateArcFamily.PairedArcRequest.conjugateChordValue occurrence
        (polynomials.get first) (polynomials.get second))).symm.trans
        (congrArg (List.map (fun occurrence =>
          Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateArcFamily.PairedArcRequest.conjugateChordValue occurrence
          (polynomials.get first) (polynomials.get second)))
          (Data.List.OfFn.Basic.ofFn_getElem (basis.preparations.get first).occurrences))
  exact congrArg (fun value => value - entries.physicalEndpoints first second)
    (readback.trans
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateChordPolygons.CapAttachment.conjugate_chords_eq_joining
        attached (polynomials.get first) (polynomials.get second)))

/-- Form the conjugate coefficient-weighted sum of the original physical endpoint chords. -/
@[expose] def physicalEndpointEnergy (entries : request.Readings cache)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) : Gaussian :=
  FiniteSum.Fin.sumFin fun first => FiniteSum.Fin.sumFin fun second => Data.Gaussian.Basic.conj (coefficients first)
    * coefficients second *
    entries.physicalEndpoints first second

/-- Form the conjugate coefficient-weighted sum of the cap joining polygons for the retained attachments. -/
@[expose] def capJoiningEnergy (attachments : Data.Vector.DependentVector (fun first =>
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment (basis.preparations.get first)))
    (polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap stage box)
      (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) : Gaussian :=
  FiniteSum.Fin.sumFin fun first => FiniteSum.Fin.sumFin fun second => Data.Gaussian.Basic.conj (coefficients first)
    * coefficients second *
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateChordPolygons.CapAttachment.conjugateJoiningArea
      (attachments.get first) (polynomials.get first) (polynomials.get second)

/-- The complete endpoint correction equals cap joining energy minus the original physical endpoint energy. -/
theorem endpointEnergy_eq_joining (entries : request.Readings cache)
    (attachments : Data.Vector.DependentVector (fun first =>
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment (basis.preparations.get
      first)))
    (polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap stage box)
      (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    entries.endpointEnergy polynomials coefficients =
      capJoiningEnergy
        attachments polynomials coefficients - entries.physicalEndpointEnergy coefficients := by
  unfold endpointEnergy
    capJoiningEnergy
    physicalEndpointEnergy
  rw [← FiniteSum.Fin.sumFin_sub]
  apply FiniteSum.Fin.sumFin_congr
  intro first
  rw [← FiniteSum.Fin.sumFin_sub]
  apply FiniteSum.Fin.sumFin_congr
  intro second
  rw [entries.endpointCorrection_eq_joining polynomials first second (attachments.get first)]
  ring1

variable (selected)
  {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
    regular domains differential} (attached :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment prepared)
  {polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap stage box}
    {bounds : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds.RegularBasisBounds polynomials}
  {capTarget : Fraction.Rational} {capMinimum : Nat}
  (capRequest : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest.RegularBasisRequest bounds
    attached.caps.length capTarget capMinimum)
  {geometry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry
    attached} {parameters : Path.Dyadic.RadialTriangles.Parameters capRequest.depth}

/-- The regular cap pays the centered physical component plus the full cap
joining polygons. The physical chords remain explicit for the Newton bridge. -/
theorem joining_energy_upper (entries : request.Readings cache) (faces : request.FacePerimeterBank cache)
    (attachments : Data.Vector.DependentVector (fun first =>
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment (basis.preparations.get
      first)))
    (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank base.faces)
    (evaluated : basis.Evaluations polynomials capRequest.depth)
    (later : request.index ≤ stage) (spatial : basis.depth ≤ capRequest.depth)
    (caps : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisAggregate.RegularBasisCap geometry parameters
      polynomials)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (capSample : (capRequest.certify caps).Evaluation coefficients)
    (allowance : Fraction.Rational) (nonnegative : 0 ≤ allowance)
    (paid : (genus : Fraction.Rational) ^ 2 * target ≤ 16 * allowance ^ 2) :
    (faces.componentEnergy neighbors coefficients - entries.physicalEndpointEnergy coefficients +
      capJoiningEnergy
        attachments polynomials coefficients).im / 4 ≤
        (capTarget + allowance) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := by
  have bound := entries.component_energy_upper selected attached capRequest faces neighbors
    evaluated later spatial caps coefficients capSample allowance nonnegative paid
  rw [entries.endpointEnergy_eq_joining attachments polynomials coefficients] at bound
  have rearrange (a b c : Gaussian.Basic.Canonical) : a + (b - c) = a - c + b := by ring1
  rwa [rearrange] at bound

end Readings
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshRequest
