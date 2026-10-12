module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.ConjugateIncrementComparison
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedBlocks
public import Purelib.Approximation.Budget.RequestedLengthBudget
import Mathlib.Data.Nat.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.QuerySchedule
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches

open Purelib.Approximation

open Purelib.Curves

open Purelib

open Purelib.Geometry

open Purelib.Integration

open Purelib.Riemann

public section

/-! Select owner budgets and one face stage for the complete fragment bank. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedBlocks

open Purelib.Data

open Purelib.Riemann.Normalization

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest (OwnedReadings
  ownedValue)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential other : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {count : Nat} {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
  {sourceData : Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count} {cover :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover sourceData}
  {covers : Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers parent} {minimum floor index
    depth : Nat}
  {common : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonCover cover covers minimum}
  {areaAllowance sourceTarget coefficientTarget : Normalization.InverseRootPolynomial.Coordinate}
  {request : Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedCommonRequest regular common
    areaAllowance sourceTarget coefficientTarget floor}
  {box : Rational.Box}
  {polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}
  {originals : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank
    covers index}
  {cells : Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceLocations.SampleBank covers index}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

open Purelib.Data.Rat.Fraction.Compatibility

variable {acquired :
  Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedCommonRequest.Acquisition request
  polynomials originals cells coefficients depth}

variable {faceIndex : Nat} {data : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.RowData occurrence
  faceIndex}

namespace BlockRequest
variable {fragmentCount : Nat} {target : Normalization.InverseRootPolynomial.Coordinate}

/-- The dependent finite length budgets for the original fragment vertex counts.

Every retained budget has unit allowance and meets the selected block owner tolerance. -/
@[expose] def LengthBudgets (selected : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedBlocks.BlockRequest
  occurrence covers fragmentCount target)
    (vertices : Fin fragmentCount → Nat) :=
  Data.Vector.DependentVector (fun position => Budget.RequestedLengthBudget.Requested (vertices position) 1
    selected.budget.tolerance)

/-- The dependent original point-owner requests at the exact retained fragment tolerances. -/
@[expose] def OwnerBudgets (selected : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedBlocks.BlockRequest
  occurrence covers fragmentCount target)
    {vertices : Fin fragmentCount → Nat} (budgets : selected.LengthBudgets vertices) :=
  Data.Vector.DependentVector (fun position =>
    OwnerRequest occurrence (budgets.get
    position).budget.tolerance)

set_option genInjectivity false in
/-- The retained length budgets, original owner requests and shared face stage for a complete fragment bank.

The cached maximum pays both the existing cell-query schedule and every original point-owner request. -/
structure OwnerPreparation (selected : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedBlocks.BlockRequest
  occurrence covers fragmentCount target)
    (vertices : Fin fragmentCount → Nat) where
  /-- The retained length budgets indexed by the original fragment positions. -/ budgets : selected.LengthBudgets
    vertices
  /-- The original point-owner requests at those exact retained length-budget tolerances. -/ owners :
    selected.OwnerBudgets budgets
  /-- The cached common face stage. -/ faceIndex : Nat
  /-- The cached stage is exactly the maximum of the cell-query and retained owner requirements. -/ face_eq : faceIndex
    = max selected.queries.faceIndex (owners.maximum (fun _ owner =>
    OwnerRequest.index owner))

constructive_injectivity OwnerPreparation

/-- Prepare all original fragment length and owner budgets and cache their common paid face stage. -/
@[expose] def prepareOwners (selected : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedBlocks.BlockRequest
  occurrence covers fragmentCount target)
    (vertices : Fin fragmentCount → Nat) : selected.OwnerPreparation vertices :=
  let budgets : selected.LengthBudgets vertices := Data.Vector.DependentVector.ofFn
    (fun position => Budget.RequestedLengthBudget.requested (vertices position) 1 selected.budget.tolerance
      (by decide) selected.budget.tolerance_positive)
  let owners : selected.OwnerBudgets budgets := Data.Vector.DependentVector.ofFn
    (fun position => OwnerRequest.build occurrence _
      (budgets.get position).budget.tolerance_positive)
  ⟨budgets, owners, max selected.queries.faceIndex (owners.maximum (fun _ owner =>
    OwnerRequest.index owner)), rfl⟩

set_option genInjectivity false in
/-- A fragment carries the two local budget facts consumed by block assembly. -/
structure BudgetedFragment (selected : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedBlocks.BlockRequest
  occurrence covers fragmentCount target)
    {faceIndex : Nat} (data : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.RowData occurrence
      faceIndex) where
  /-- The original owned fragment with its actual geometry, readings and cached area samples. -/ fragment :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment (originals := originals)
    (coefficients := coefficients) data
  /-- The retained fragment padding allowance is at most one. -/ allowance_le : fragment.allowance ≤ 1
  /-- The original fragment owner tolerance meets the selected block tolerance. -/ tolerance_le :
    fragment.budget.tolerance ≤ selected.budget.tolerance

constructive_injectivity BudgetedFragment

namespace OwnerPreparation
variable {selected : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedBlocks.BlockRequest occurrence covers
  fragmentCount target} {vertices : Fin fragmentCount → Nat}

/-- The retained common face stage pays the original block cell-query schedule. -/
theorem query_le (prepared : selected.OwnerPreparation vertices) : selected.queries.faceIndex ≤ prepared.faceIndex :=
  (Nat.Order.le_max_left ..).trans_eq prepared.face_eq.symm

/-- Every original retained point-owner request is paid by the common face stage. -/
theorem owner_le (prepared : selected.OwnerPreparation vertices) (position : Fin fragmentCount) :
    OwnerRequest.index (prepared.owners.get position) ≤
      prepared.faceIndex :=
  (prepared.owners.get_le_maximum (fun _ owner =>
    OwnerRequest.index owner) position).trans
    ((Nat.Order.le_max_right ..).trans_eq prepared.face_eq.symm)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest in
/-- Retain the physical geometry, readings and area samples, attaching only
the already selected length and owner budgets. -/
@[expose] def fragment (prepared : selected.OwnerPreparation vertices) (position : Fin fragmentCount)
    (later : prepared.faceIndex ≤ faceIndex)
    (member : parent ∈ occurrence.compared.entered.cache.parents)
    (piece : Paths.RectangularSegmentSplitting.SegmentPiece occurrence.compared.entered.domain.geometry
      (parent.edge.point 0) (parent.edge.point 1))
    (parameters : Fin (vertices position + 1) → Normalization.InverseRootPolynomial.Coordinate)
    (inside : ∀ vertex, piece.interval.lower ≤ parameters vertex ∧ parameters vertex ≤ piece.interval.upper)
    (forward : Bool)
    (ordered : ∀ edge : Fin (vertices position), if forward then parameters edge.castSucc ≤ parameters edge.succ
      else parameters edge.succ ≤ parameters edge.castSucc)
    (readings : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest.OwnedReadings data (fun vertex =>
      parent.edge.point (parameters vertex)))
    (owned : Periods.CenteredBilinearPath.Sample (fun vertex => Path.ConjugateIncrementComparison.conjugateFirst
      (⟨ownedValue readings coefficients vertex, ownedValue readings coefficients vertex⟩ :
        Topology.Polygon.Stokes.PrimitivePoint)))
    (source : Periods.CenteredBilinearPath.Sample (fun vertex => Path.ConjugateIncrementComparison.conjugateFirst
      (⟨Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback.BasisSourceLocations.PrimitiveBank.value
        originals coefficients (parameters vertex),
        Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback.BasisSourceLocations.PrimitiveBank.value
        originals coefficients (parameters vertex)⟩ : Topology.Polygon.Stokes.PrimitivePoint))) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedBlocks.BlockRequest.BudgetedFragment (originals :=
      originals) (coefficients := coefficients) selected data :=
  ⟨
  { member := member, piece := piece, vertices := vertices position, parameters := parameters
    inside := inside, forward := forward, ordered := ordered, allowance := 1
    budget := (prepared.budgets.get position).budget
    owners := prepared.owners.get position, later := (prepared.owner_le position).trans later
    readings := readings, owned := owned, source := source }, le_rfl, (prepared.budgets.get position).tolerance_le⟩

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedBlocks.BlockRequest.OwnerPreparation in
/-- The common stage pays query and owner requirements together. The
budgeted fragments supply their local certificates directly. -/
theorem block_error (prepared : selected.OwnerPreparation vertices)
    (fragments : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedBlocks.BlockRequest.BudgetedFragment
      (originals := originals) (coefficients := coefficients) selected data))
    (countLe : fragments.length ≤ fragmentCount)
    (sourcePaid : selected.queries.sourceMinimum ≤ index) (later : prepared.faceIndex ≤ faceIndex) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentBlocks.fragmentBlockError (acquired := acquired)
      (fragments.map
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedBlocks.BlockRequest.BudgetedFragment.fragment) < target
      := by
  apply selected.accurate _ ((List.Map.length_map ..).trans_le countLe) sourcePaid (prepared.query_le.trans later)
  · intro fragment member
    obtain ⟨certified, _, rfl⟩ := Data.List.Map.mem_map.mp member
    exact certified.allowance_le
  · intro fragment member
    obtain ⟨certified, _, rfl⟩ := Data.List.Map.mem_map.mp member
    exact certified.tolerance_le

end OwnerPreparation
end BlockRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedBlocks
