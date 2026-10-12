module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedAnnuli
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineSideAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WeightedPerimeterAreas
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.OuterChordTransport
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests
public import Purelib.Riemann.Branches.NewtonRequestedCutBudget
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.CutBalance
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PairedAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PairedCutRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Branches.NewtonCutPrimitiveArea
import Purelib.Riemann.Branches.NewtonPairedCutRequests
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Riemann.Topology.NewtonPairedSewnAreaRequests
import Purelib.Riemann.Topology.NewtonSewnExcision
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.ProjectedAreaCancellation
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Tactic.Ring

public section

/-! Transport selected annular areas to their actual full fine outer sides.
The original inner areas, cut jumps, cut defects and owner origins remain
explicit. Both occurrence counts are paid by the shared cut allocator. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineTransport

open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Riemann
open Purelib

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction.Compatibility

/-- A bounded nonnegative occurrence count controls its squared repeated rational contribution by the original count
cap. -/
private theorem repeat_bound {count cap : Nat} {value : Fraction.Rational} (bounded : count ≤ cap) (nonnegative : 0 ≤
  value) :
    (count : Fraction.Rational) * ((count : Fraction.Rational) * value) ≤ (cap : Fraction.Rational)^2 * value := by
  have countLe := Fraction.Order.Arithmetic.pow_le_pow_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le
    count)) (Fraction.Cast.Order.natCast_le_direct bounded) 2
  exact (show (count : Fraction.Rational) * ((count : Fraction.Rational) * value) = (count : Fraction.Rational)^2 *
    value by ring1).trans_le
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct countLe nonnegative)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target radius :
    Fraction.Rational}

namespace FamilyAreaRequest.PairedComparison.SewnSample
variable {request : Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest
  preparation target radius}
  {lifted : Meshes.LiftedPuncturedGrid request.single.grid.punctured}
  {excision : Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision request.single.grid lifted}
  {prepared : Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonGrid.AllHoleExcision.OuterPreparations
    excision} {first second : Fin genus}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames
    request.single.grid.faces.regulars}
  {comparison :
    PairedComparison prepared
    first second domains}
  {cutTarget : Fraction.Rational} {floor stage : Nat}
  {cut : Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest lifted domains first second cutTarget
    floor}
  {cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage} {readings :
    Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings cut cache}
  {source :
    PairedComparison.Sample
    comparison readings.left readings.right}

/-- This residual displays every term surviving outer source-chord cancellation. -/
@[expose] def fineResidual (sewn :
  Hyperelliptic.Meshes.Newton.AllHoles.PairedAnnuli.NewtonPreparation.FamilyAreaRequest.PairedComparison.SewnSample
  source readings.leftSurface readings.rightSurface) : Gaussian :=
  Data.Gaussian.Norm.Sum.Basic.gaussianSum (sewn.terms.map (fun term => term.data.selectedArea -
    (term.data.innerArea + term.data.paired.jumpSum + term.data.paired.defectSum +
      (Hyperelliptic.Meshes.Newton.Annulus.OuterChordTransport.AnnularSample.outerOrigins term.data)) -
    (Hyperelliptic.Meshes.Newton.Annulus.FineSideAreas.fineSideArea term.source.source.source.outer
      readings.normalized)))

end FamilyAreaRequest.PairedComparison.SewnSample

namespace FamilyFineAreaRequest.SideRequests
variable {allocated : Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests.FamilyFineAreaRequest preparation target
  radius}
  {lifted : Meshes.LiftedPuncturedGrid allocated.family.single.grid.punctured}
  {excision : Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision allocated.family.single.grid lifted}
  {prepared : Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonGrid.AllHoleExcision.OuterPreparations
    excision} {first second : Fin genus}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames
    allocated.family.single.grid.faces.regulars}
  {comparison :
    PairedComparison prepared
    first second domains}
  {cutTarget : Fraction.Rational} {floor stage : Nat}
  {cut : Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest lifted domains first second cutTarget
    floor}
  {cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage} {readings :
    Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings cut cache}
  {source :
    PairedComparison.Sample
    comparison readings.left readings.right}

/-- The actual cut samples supply the sewing hypothesis and normalized
perimeters. The geometric allocator supplies every fine-side estimate. -/
theorem sewn_fine_accurate
    (samples : Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering.CenteredPerimeters cut.exterior.prepared.energy
      cache first second) (lengths :
      Hyperelliptic.Meshes.PuncturedGrid.WeightedPerimeterAreas.CenteredPerimeters.Lengths samples)
    (requested : allocated.SideRequests comparison samples.traces)
    (sewn :
      Hyperelliptic.Meshes.Newton.AllHoles.PairedAnnuli.NewtonPreparation.FamilyAreaRequest.PairedComparison.SewnSample
      source readings.leftSurface readings.rightSurface)
    (later : requested.index ≤ stage) (cutLater : cut.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq
      (Hyperelliptic.Meshes.Newton.AllHoles.FineTransport.FamilyAreaRequest.PairedComparison.SewnSample.fineResidual
      sewn) < 2 * (Branches.NewtonRequestedCutBudget.CutAnnularReadings.outerAllowance cut + target) := open
      Purelib.Approximation in open Purelib in open Purelib.Integration in by
  let error := cut.sewing.budget.weight * cut.sewing.budget.error
  let count : Coordinate := allocated.family.single.count
  let bound := 2 * (count^2 * error + allocated.family.perHole)
  have errorNonnegative : 0 ≤ error := Fraction.Order.Arithmetic.mul_nonneg_direct cut.sewing.budget.weight_nonnegative
    cut.sewing.budget.error_positive.le
  have boundNonnegative : 0 ≤ bound := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.sq_nonneg_direct count)
      errorNonnegative) allocated.family.perHole_positive.le)
  let values := sewn.terms.map (fun term => term.data.selectedArea -
    (term.data.innerArea + term.data.paired.jumpSum + term.data.paired.defectSum +
      (Hyperelliptic.Meshes.Newton.Annulus.OuterChordTransport.AnnularSample.outerOrigins term.data)) -
    (Hyperelliptic.Meshes.Newton.Annulus.FineSideAreas.fineSideArea term.source.source.source.outer
      readings.normalized))
  have bounded : ∀ value ∈ values, Data.Gaussian.Norm.Basic.normSq value ≤ bound := by
    intro value member
    obtain ⟨term, belongs, equal⟩ := Data.List.Map.mem_map.mp member
    have sourceMember : term.source.source ∈ comparison.entries :=
      source.terms_eq ▸ Data.List.Map.mem_map_of_mem
        (sewn.terms_eq ▸ Data.List.Map.mem_map_of_mem belongs)
    have fine := requested.entry_accurate samples lengths readings.normalized readings.left readings.right later
      term.source.source sourceMember
    have estimate := Hyperelliptic.Meshes.Newton.Annulus.OuterChordTransport.AnnularSample.selected_fine_bound term.data
      cut.sewing (cut.sewing_le.trans cutLater) readings.surface readings.normalized fine.le
    have cap := Hyperelliptic.Meshes.Newton.AllHoles.FineTransport.repeat_bound (allocated.family.single.outer_count
      term.source.source.source.entry.region) errorNonnegative
    have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct cap (le_refl allocated.family.perHole)) (by
          decide : (0 : Fraction.Rational) ≤ 2)
    exact equal ▸ estimate.trans scaled
  have size : values.length ≤ allocated.family.count := (Data.List.Map.length_map ..).le.trans sewn.terms_count
  have estimate := Path.IncrementArea.sum_bound_of_length boundNonnegative bounded size
  have paid := Rational.Budget.Aggregate.count_mul_perTerm_lt allocated.positive allocated.family.count
  have sameAllowance : allocated.family.perHole = Rational.Budget.Aggregate.perTerm target allocated.family.count :=
    allocated.family.perHole_eq
  rw [← sameAllowance] at paid
  have finish := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2)
    (Fraction.Order.Arithmetic.add_lt_add_left_direct paid
      (Branches.NewtonRequestedCutBudget.CutAnnularReadings.outerAllowance cut))
  have equal : (allocated.family.count : Fraction.Rational)^2 * bound =
      2 * (Branches.NewtonRequestedCutBudget.CutAnnularReadings.outerAllowance cut +
        (allocated.family.count : Fraction.Rational) * ((allocated.family.count : Fraction.Rational) *
          allocated.family.perHole)) := by
    dsimp only [bound, count, error, Branches.NewtonRequestedCutBudget.CutAnnularReadings.outerAllowance,
      Branches.NewtonRequestedCutBudget.CutAnnularReadings.outerWeight, -eq_self, -iff_self]
    rw [Rational.Budget.Aggregate.countCoordinate_eq, Rational.Budget.Aggregate.countCoordinate_eq]
    ring1
  exact estimate.trans_lt (equal.trans_lt finish)

end FamilyFineAreaRequest.SideRequests
end Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineTransport
