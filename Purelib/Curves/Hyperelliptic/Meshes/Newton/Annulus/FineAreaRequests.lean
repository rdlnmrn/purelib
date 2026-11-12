module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Vector.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchCellWinding
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineSideAreas
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.SideOccurrences
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WeightedPerimeterAreas
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PerimeterEndpointRequest
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.PreparedNewtonAreaRate
import Purelib.Riemann.RootContinuation.PreparedNewtonBandFamilies
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.RequestedSideAreas
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PairedAreaRequests
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.RootIsolation.Newton.Band.Basic
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.State.Raw
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.State.WindingOne.Raw
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Tactic.Ring

open Purelib.Curves.Hyperelliptic.Branches.BranchIsolation

open Purelib.Data.Rat.Fraction.Order

public section

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Riemann

/-! Choose the shared radius before the grid, paying the original two-lap
occurrence count uniformly over all bands and pairs of basis differentials.
The fine-side correction is relative to the actual retained source chords;
annular interior and primitive-origin corrections remain separate. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineAreaRequests

open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Branches.BranchCellBank curve branches higher}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original}

/-- The retained differential-family area coefficient at the original branch-band index. -/
@[expose] def bandAreaCoefficient (preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation
  original) (index : Data.Index branches) : Fraction.Rational :=
  RootContinuation.PreparedNewtonAreaRate.PreparedBandFamily.areaCoefficient (curve := curve) (current :=
    (Branches.BranchCellWinding.state original index).raw)
    (preparation.profiles.get index).differentials

/-- Every original branch-band area coefficient is nonnegative. -/
theorem bandAreaCoefficient_nonnegative (preparation :
  RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original) (index :
  Data.Index branches) :
    0 ≤ FineAreaRequests.bandAreaCoefficient preparation index :=
  RootContinuation.PreparedNewtonAreaRate.PreparedBandFamily.areaCoefficient_nonnegative _

set_option genInjectivity false in
/-- Cached coefficient bounds are fixed before extracting any requested band. -/
structure FineAreaRequest (preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original)
  (target radius : Fraction.Rational) where
  /-- The cached original area coefficient for every retained branch index. -/ coefficients :
    RootContinuation.PreparedNewtonBandFamilies.RateVector branches.siteCount
  /-- Each cached coefficient equals the corresponding original differential-family area coefficient. -/ coefficients_eq
    : ∀ index, coefficients index = FineAreaRequests.bandAreaCoefficient preparation
    index
  /-- The cached maximum over the retained coefficient vector. -/ maximum : Fraction.Rational
  /-- The maximum is computed from the exact retained coefficient vector. -/ maximum_eq : maximum =
    RootContinuation.PreparedNewtonBandFamilies.maximumRate coefficients
  /-- The common local allowance allocated to every original outer-side contribution. -/ component : Fraction.Rational
  /-- The component allowance uses a quarter target and the retained outer occurrence count. -/ component_eq : component
    = Rational.Budget.Aggregate.perTerm (target / 4)
    (AreaRequests.NewtonPreparation.outerCount preparation)
  /-- The common local allowance is strictly positive. -/ component_positive : 0 < component
  /-- The retained radius allocation paying the maximum coefficient at the common local allowance. -/ radiusBudget :
    RootContinuation.PreparedNewtonBandSamples.PreparedBandBudget maximum component radius
  /-- The original annular area request using the radius selected by the retained budget. -/ area :
    AreaRequests.NewtonPreparation.AreaRequest preparation target radiusBudget.size

constructive_injectivity FineAreaRequest

namespace FineAreaRequest
variable {target radius : Fraction.Rational}

/-- Cache all original band coefficients and allocate a common radius paying their fine-side area errors.

Positive target and radius bounds determine the local allowance before the actual Newton grid and requested bands are
constructed. -/
@[expose] def build (preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original)
  (target radius : Fraction.Rational)
    (positive : 0 < target) (radiusPositive : 0 < radius) :
      FineAreaRequest preparation target radius :=
  let coefficients := Vector.Basic.vectorOfFn
    (FineAreaRequests.bandAreaCoefficient preparation)
  let maximum := RootContinuation.PreparedNewtonBandFamilies.maximumRate coefficients
  let component := Rational.Budget.Aggregate.perTerm (target / 4)
    (AreaRequests.NewtonPreparation.outerCount preparation)
  have componentPositive : 0 < component := Rational.Budget.Aggregate.perTerm_positive
    (Field.div_pos_direct positive (by decide)) _
  let budget := RootContinuation.PreparedNewtonBandSamples.PreparedBandBudget.build maximum
    (RootContinuation.PreparedNewtonBandFamilies.maximumRate_nonnegative coefficients) componentPositive radiusPositive
  ⟨coefficients, Vector.Basic.vectorOfFn_apply _, maximum, rfl, component, rfl, componentPositive,
    budget, AreaRequests.NewtonPreparation.AreaRequest.build preparation target
      budget.size positive budget.positive⟩

/-- Each original band coefficient is bounded by the retained common maximum. -/
theorem coefficient_le (allocated : FineAreaRequest preparation
  target radius) (index : Data.Index branches) :
    FineAreaRequests.bandAreaCoefficient preparation index ≤ allocated.maximum := by
  rw [← allocated.coefficients_eq, allocated.maximum_eq]
  exact RootContinuation.PreparedNewtonBandFamilies.rate_le_maximum _ _

/-- Every actual band pays the same local allowance, for all basis pairs. -/
theorem band_paid (allocated : FineAreaRequest preparation target
  radius) (index : Data.Index branches) :
    FineAreaRequests.bandAreaCoefficient preparation index *
      (allocated.area.grid.bands.entries.get index).selection.sample.output.radius^2 ≤ allocated.component := by
  let band := allocated.area.grid.bands.entries.get index
  have squared : band.selection.sample.output.radius^2 ≤ band.selection.sample.output.radius := by
    have h := Arithmetic.mul_le_mul_of_nonneg_right_direct band.selection.radius_le_one
      band.selection.sample.output.radiusPositive.le
    simpa only [pow_two, Fraction.Field.one_mul, -eq_self, -iff_self] using h
  have rate := Arithmetic.mul_le_mul_of_nonneg_right_direct (allocated.coefficient_le index)
    (Arithmetic.sq_nonneg_direct band.selection.sample.output.radius)
  exact rate.trans ((Arithmetic.mul_le_mul_of_nonneg_left_direct (squared.trans
    (RootContinuation.PreparedNewtonAreaRate.PreparedBandFamily.radius_le band))
    (allocated.maximum_eq ▸ RootContinuation.PreparedNewtonBandFamilies.maximumRate_nonnegative
      allocated.coefficients)).trans allocated.radiusBudget.paid)

/-- Every extracted band radius is bounded by the original requested radius. -/
theorem radius_le (allocated : FineAreaRequest preparation target
  radius) (index : Data.Index branches) :
    (allocated.area.grid.bands.entries.get index).selection.sample.output.radius ≤ radius :=
  (RootContinuation.PreparedNewtonAreaRate.PreparedBandFamily.radius_le (allocated.area.grid.bands.entries.get
    index)).trans allocated.radiusBudget.le_radius

/-- Every outer occurrence count below the retained cap pays its doubled pair of component errors within the target. -/
private theorem count_paid (allocated : FineAreaRequest preparation
  target radius) (positive : 0 < target)
    {count : Nat} (bounded : count ≤ (AreaRequests.NewtonPreparation.outerCount
      preparation)) :
    2 * ((count : Fraction.Rational) * ((count : Fraction.Rational) * allocated.component) +
      (count : Fraction.Rational) * ((count : Fraction.Rational) * allocated.component)) < target := by
  have countNonnegative := Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count)
  have capNonnegative := Fraction.Cast.Order.natCast_le_direct (Nat.zero_le
    (AreaRequests.NewtonPreparation.outerCount preparation))
  have cap := Fraction.Cast.Order.natCast_le_direct bounded
  have product := Arithmetic.mul_le_mul_direct cap
    (Arithmetic.mul_le_mul_of_nonneg_right_direct cap allocated.component_positive.le)
    (Arithmetic.mul_nonneg_direct countNonnegative allocated.component_positive.le) capNonnegative
  have paid := Rational.Budget.Aggregate.count_mul_perTerm_lt (Field.div_pos_direct positive (by decide :
    (0 : Fraction.Rational) < 4)) (AreaRequests.NewtonPreparation.outerCount
    preparation)
  rw [← allocated.component_eq] at paid
  have scaled := Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 4)
    (product.trans_lt paid)
  calc
    _ = 4 * ((count : Fraction.Rational) * ((count : Fraction.Rational) * allocated.component)) := by ring1
    _ < 4 * (target / 4) := scaled
    _ = target := by rw [Fraction.Field.mul_comm]; exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)

variable (allocated : FineAreaRequest preparation
  target radius)
  {index : Data.Index branches} {annulus :
    Faces.AnnularFaces allocated.area.grid index}
  {lifted : Meshes.LiftedPuncturedGrid allocated.area.grid.punctured} {region :
    LiftedBoundary.Lifted annulus lifted}
  {domains : PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames
    allocated.area.grid.faces.regulars}
  {cuts : PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains} {coarseDepth : Nat}
    {fixed : (sheet : Fin 2) → PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains
    sheet}
  {meshTarget : Fraction.Rational} {i j : Fin genus} {stage : Nat} {cache :
    PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage}
  {request : PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest (fun sheet =>
    PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet coarseDepth) fixed
    meshTarget}

/-- The endpoint allocator consumes the same pre-grid local allowance. -/
@[expose] def endpoints
    (fixed : (sheet : Fin 2) → PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains
      sheet) (i j : Fin genus) :=
  PuncturedGrid.PerimeterEndpointRequest.build fixed i j
    allocated.component allocated.component_positive

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineAreaRequests.FineAreaRequest in
/-- A requested fine-side comparison on the original annular sources.
The grid count is bounded by construction, independently of radius and
fine subdivisions; no geometric or analytic success hypothesis is supplied. -/
theorem fineSideArea_accurate (positive : 0 < target)
    (prepared : PrimitiveComparison.Lifted.OuterPreparation region)
    (samples : PuncturedGrid.RequestedHoleCentering.CenteredPerimeters request cache i j) (lengths
      : PuncturedGrid.WeightedPerimeterAreas.CenteredPerimeters.Lengths samples)
    (perimeters : PuncturedGrid.Matched.FacePerimeters (request := request)
      cache.normalize i j)
    (left : PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get i) lifted.mesh)
      (right : PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get j) lifted.mesh)
    (references : PuncturedGrid.BandOccurrenceRequests.BandOccurrenceBank samples.traces
      (allocated.area.grid.bands.entries.get index) i j
      (SideOccurrences.sideOccurrences prepared))
    (endpoints : PuncturedGrid.PerimeterEndpointRequest fixed i j
      allocated.component)
    (later : references.index ≤ stage) (endpointsLater : endpoints.index ≤ stage) :
    Gaussian.Norm.Basic.normSq (FineSideAreas.fineSideArea prepared
      perimeters - Gaussian.Norm.Sum.Basic.gaussianSum (prepared.sources.map
      (PuncturedGrid.HoleSourceChords.BranchCellBank.TriangleReadings.sourceChord left right))) <
      target := by
  have estimate := RequestedSideAreas.fineSideArea_bound prepared samples lengths
    perimeters left right references endpoints later endpointsLater
  have countNonnegative := Fraction.Cast.Order.natCast_le_direct (Nat.zero_le region.outer.length)
  have band := Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.mul_le_mul_of_nonneg_left_direct (allocated.band_paid index) countNonnegative)
      countNonnegative
  have total := Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct (le_refl ((region.outer.length : Fraction.Rational) *
      ((region.outer.length : Fraction.Rational) * allocated.component))) band)
    (by decide : (0 : Fraction.Rational) ≤ 2)
  have count := allocated.area.outer_count region
  exact (estimate.trans total).trans_lt
    (allocated.count_paid positive (count.trans_eq allocated.area.count_eq))

end FineAreaRequest
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineAreaRequests
