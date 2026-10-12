module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Dependent
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Riemann.RootContinuation.NewtonSelectedPerimeters
import Purelib.Riemann.RootContinuation.PreparedNewtonAreaRate

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PerimeterEndpointRequest
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchCellWinding
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BandSideReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideBoundaryGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideCenteredRemainder
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WeightedPerimeterAreas
public import Purelib.Riemann.RootContinuation.NewtonSelectedSideGeometry
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.RootIsolation.State.WindingOne.Raw
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.RootIsolation.Newton.Band.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.RootContinuation.PreparedNewtonBandFamilies
import Purelib.RootIsolation.State.Raw
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Data.Rat.Fraction.Field
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Riemann.Integration.RectangularCenteredPerimeter
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Polynomial.Dense.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring

public section

/-! Actual selected boundary interfaces acquire Newton side-area requests.
The original face, band, sheet and perimeter traces remain shared. -/
namespace Purelib.Riemann.RootContinuation.NewtonSelectedInterfaceRequests
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (CommonCuts Preflights
  Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision AnnularEntry)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideBoundaryGeometry (SideBoundary)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests (PerimeterTraceBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering (CenteredPerimeters)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WeightedPerimeterAreas.CenteredPerimeters (Lengths)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched (FacePerimeters)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid (PerimeterEndpointRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideCenteredRemainder (sideCenteredArea)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder (sideAreaRemainder)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BandSideReferences (BandSideReference)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target radius : Rational}
  {grid : NewtonGrid preparation target radius} {lifted : LiftedPuncturedGrid grid.punctured}
  {domains : FaceDomainBank lifted.frames
    grid.faces.regulars}
  {cuts : CommonCuts domains}
    {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    Preflights domains sheet}
  {meshTarget : Rational} {i j : Fin genus}
  {request : TwoSheetRequest (fun sheet =>
    RegularMeshes.build domains cuts sheet
    coarseDepth) fixed meshTarget}

section
open Purelib.Curves.Hyperelliptic
/-- An original band-side reference indexed by the retained face, side, sheet and differential pair. -/
@[expose] def InterfaceReference (traces : Meshes.PuncturedGrid.BandOccurrenceRequests.PerimeterTraceBank request)
  (entry : Meshes.Newton.AllHoles.Excision.AnnularEntry grid lifted)
    (i j : Fin genus) (position : Fin grid.faces.regulars.length) (side : GridSide) (sheet : Fin 2) :=
  Meshes.PuncturedGrid.BandSideReferences.BandSideReference ((domains.get position).domain sheet) ((traces.get
    position).get sheet)
    (grid.bands.entries.get entry.hole.index) i j side

/-- The stage required by the exact retained interface reference. -/
@[expose] def InterfaceReference.index {traces : Meshes.PuncturedGrid.BandOccurrenceRequests.PerimeterTraceBank request}
  {entry : Meshes.Newton.AllHoles.Excision.AnnularEntry grid lifted}
    {i j : Fin genus} {position : Fin grid.faces.regulars.length} {side : GridSide} {sheet : Fin 2}
    (reference : InterfaceReference traces entry i j position side sheet) : Nat :=
  Meshes.PuncturedGrid.BandSideReferences.BandSideReference.index (domain := (domains.get position).domain sheet)
    (traces := (traces.get position).get sheet) (band := grid.bands.entries.get entry.hole.index) side reference

end

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
set_option genInjectivity false in
/-- An original selected boundary side with its retained annular entry and two-sheet band references.

The entry belongs to the exact excision, its boundary certificate preserves the original face and side, and the common
stage covers both retained sheet references. -/
structure InterfaceRequest (excision : Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted) (traces :
  Meshes.PuncturedGrid.BandOccurrenceRequests.PerimeterTraceBank request)
    (i j : Fin genus) (position : Fin grid.faces.regulars.length) (side : GridSide) where
  /-- The retained original annular entry owning the side's band. -/ entry :
    Meshes.Newton.AllHoles.Excision.AnnularEntry grid lifted
  /-- The retained entry belongs to the exact original excision. -/ member : entry ∈ excision.entries
  /-- The original regular face side lies on the retained entry's exact band boundary. -/ boundary :
    Meshes.PuncturedGrid.SideBoundaryGeometry.SideBoundary (grid.faces.regulars[position.val]'position.isLt).cell.box
    (grid.bands.box entry.hole.index) side
  /-- The retained interface-reference vector indexed by the two original sheets. -/ references : Vector.DependentVector
    (InterfaceReference traces entry i j position side)
  /-- The common retained stage for both original sheet references. -/ index : Nat
  /-- Every original sheet-reference stage is at most the retained common stage. -/ index_ge : ∀ sheet,
    InterfaceReference.index (references.get sheet) ≤ index

constructive_injectivity InterfaceRequest

namespace InterfaceRequest
variable {excision : AllHoleExcision grid lifted} {traces :
  PerimeterTraceBank request}
  {position : Fin grid.faces.regulars.length} {side : GridSide}

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
/-- Acquire both original sheet references from the exact retained band-side boundary certificate.

The stored reference vector keeps the original domain, perimeter traces and annular entry; its maximum stage covers both
exact reference indices. -/
@[expose] def ofBoundary (excision : Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted) (traces :
  Meshes.PuncturedGrid.BandOccurrenceRequests.PerimeterTraceBank request)
    (i j : Fin genus) (position : Fin grid.faces.regulars.length) (side : GridSide)
    (entry : Meshes.Newton.AllHoles.Excision.AnnularEntry grid lifted) (member : entry ∈ excision.entries)
    (boundary : Meshes.PuncturedGrid.SideBoundaryGeometry.SideBoundary
      (grid.faces.regulars[position.val]'position.isLt).cell.box (grid.bands.box entry.hole.index) side) :
    InterfaceRequest excision traces i j position side :=
  let references : Vector.DependentVector (InterfaceReference traces entry i j position side) :=
    Vector.DependentVector.ofFn (fun sheet : Fin 2 =>
      Meshes.PuncturedGrid.BandSideReferences.BandSideReference.build ((traces.get position).get sheet)
        (grid.bands.entries.get entry.hole.index) i j side)
  ⟨entry, member, boundary, references,
    references.maximum (fun _ reference => InterfaceReference.index reference),
    references.get_le_maximum (fun _ reference => InterfaceReference.index reference)⟩

open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.RootContinuation in
/-- Construct the retained interface request from an original selected-to-discarded neighboring-face transition. -/
@[expose] def build (excision : Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted) (traces :
  Meshes.PuncturedGrid.BandOccurrenceRequests.PerimeterTraceBank request)
    (i j : Fin genus) (position next : Fin grid.faces.regulars.length) (side : GridSide)
    (matching : side.Matches (grid.faces.regulars[position.val]'position.isLt).cell.box
      (grid.faces.regulars[next.val]'next.isLt).cell.box)
    (selected : NewtonSelectedPerimeters.AllHoleExcision.fineMask excision position = true)
    (discarded : NewtonSelectedPerimeters.AllHoleExcision.fineMask excision next = false) :
    InterfaceRequest excision traces i j position side :=
  let found := excision.interfaceBand position next side matching selected discarded
  ofBoundary excision traces i j position side found.val found.property.1 found.property.2

open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.Data.Rat in
open Purelib.Riemann.RootContinuation in
/-- The exact retained band area coefficient times its selected radius squared. -/
@[expose] def allowance (allocated : InterfaceRequest excision traces i j position side) : Fraction.Rational :=
  PreparedNewtonAreaRate.PreparedBandFamily.areaCoefficient
    (curve := curve) (current := (BranchCellWinding.state original allocated.entry.hole.index).raw)
    (preparation.profiles.get allocated.entry.hole.index).differentials *
    (grid.bands.entries.get allocated.entry.hole.index).selection.sample.output.radius^2

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
/-- Later original centered perimeter readings satisfy the retained interface's band-area allowance. -/
theorem centered_bound {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains
  stage}
    (samples : Meshes.PuncturedGrid.RequestedHoleCentering.CenteredPerimeters request cache i j)
    (lengths : Meshes.PuncturedGrid.WeightedPerimeterAreas.CenteredPerimeters.Lengths samples)
    (allocated : InterfaceRequest excision samples.traces i j position side)
    (later : allocated.index ≤ stage) (sheet : Fin 2) :
    Data.Gaussian.Norm.Basic.normSq (Meshes.PuncturedGrid.SideCenteredRemainder.sideCenteredArea ((samples.samples.get
      position).get sheet) side) ≤ allocated.allowance := by
  change Data.Gaussian.Norm.Basic.normSq (Meshes.PuncturedGrid.BandSideReferences.BandSideReference.sideArea
    ((samples.samples.get position).get sheet) side) ≤ _
  exact Meshes.PuncturedGrid.BandSideReferences.BandSideReference.area_bound (allocated.references.get sheet)
    ((lengths.get position).get sheet)
    allocated.boundary ((allocated.index_ge sheet).trans later)
    (cache.normalize.atDomain position sheet i) (cache.normalize.atDomain position sheet j)
    ((samples.samples.get position).get sheet)

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The original side remainder is bounded by twice the endpoint allowance plus retained band allowance.

The same side's endpoint request controls its difference from the centered reading, whose original band reference pays
the remaining term. -/
theorem remainder_bound {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains
  stage}
    (samples : Meshes.PuncturedGrid.RequestedHoleCentering.CenteredPerimeters request cache i j)
    (lengths : Meshes.PuncturedGrid.WeightedPerimeterAreas.CenteredPerimeters.Lengths samples)
    (allocated : InterfaceRequest excision samples.traces i j position side)
    (later : allocated.index ≤ stage) {error : Fraction.Rational}
    (endpoints : Curves.Hyperelliptic.Meshes.PuncturedGrid.PerimeterEndpointRequest fixed i j error) (endpointLater
      : endpoints.index ≤ stage)
    (perimeters : Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters (request := request) cache.normalize
        i j)
      (sheet : Fin 2) :
    Data.Gaussian.Norm.Basic.normSq (Meshes.PuncturedGrid.HoleAreaRemainder.sideAreaRemainder perimeters position sheet
      side)
      ≤ 2 * (error + allocated.allowance) := by
  have centered := allocated.centered_bound samples lengths later sheet
  have difference := endpoints.bound endpointLater ((samples.samples.get position).get sheet) perimeters side
  have equal : Meshes.PuncturedGrid.HoleAreaRemainder.sideAreaRemainder perimeters position sheet side =
      (Meshes.PuncturedGrid.HoleAreaRemainder.sideAreaRemainder perimeters position sheet side -
        Meshes.PuncturedGrid.SideCenteredRemainder.sideCenteredArea ((samples.samples.get position).get sheet) side) +
      Meshes.PuncturedGrid.SideCenteredRemainder.sideCenteredArea ((samples.samples.get position).get sheet) side := by
        ring1
  rw [equal]
  exact (Norm.Bounds.normSq_add_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct difference
      centered) (by decide))

end InterfaceRequest
end Purelib.Riemann.RootContinuation.NewtonSelectedInterfaceRequests
