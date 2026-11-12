module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Polynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AnalyticComparison.Polynomial.Models
public import Purelib.Riemann.Readings.UniformPreparedRequests.Covered
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.Polynomial
import Purelib.Data.Rat.Fraction.Cast.Order

/-! # The retained coordinate-numerator source model on an actual regular fragment

The original polynomial work and complete stage model bank remain data.
The head model supplies its own inverse, numerator primitive and pullback;
independent face primitives supply the actual numerical comparison values.
No source or numerical bank is constructed by this attachment.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent

open Purelib
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredParents (PolynomialWork)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AnalyticComparison
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces (RegularPrimitiveFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment (SheetEntry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rectangle (AxisPartition)
open Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions (Interval)
open Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh.RectangularInverseModels (CommonMesh)
open Purelib.LinearAlgebra.Grid (Offsets)
open Purelib.Riemann.Branches.RectangularSheetGauge
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveOverlapBounds)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Integration.RectangularSharedPrimitives (SharedPrimitiveValues)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.UniformRequest (PolynomialModel)
open Purelib.Riemann.Readings.RectangularExteriorBoundary.Geometry (allCells)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
variable {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
variable {base : FramedPuncturedGrid (Fibre.frameCurve frame) branches higher}
variable {frames : RootFrames base.bank.grid} {axes : PrimitiveAxes base.bank.grid}
variable {domains : FaceDomainBank frames base.faces.regulars}
variable {count polynomialFloor polynomialStage : Nat} {target : Rational}
variable {parent : CenteredEdge (Fibre.frameCurve frame) basis} {request : LocalRequest parent count target}
variable {cuts : List Rational} {partition : AxisPartition 0 1 cuts} {interval : Interval}
variable {fragment : RegularPrimitiveFragment axes parent partition interval}
variable (assigned : SheetEntry fragment domains request)
variable {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)}
variable {tail : CoveredParents count remaining}
variable (work : PolynomialWork (.cons request.patch request.patch_finishInside tail)
  polynomialFloor (Specification.valueSpecification parameter 1))
variable (models : work.Models polynomialStage)
variable {globalBounds : PrimitiveOverlapBounds fragment.face.located.face.clearance
  ((Specification.valueSpecification parameter 1).numerator.scale
    (Specification.valueSpecification parameter 1).scale)}
variable {tolerance : Rational}
variable (accuracy : GridPrimitiveAccuracy globalBounds assigned.domain.steps tolerance)
variable (primitives : Primitives
  (Transitions.oriented (assigned.domain.patch.sheets.refine accuracy.index).transitions
    (assigned.domain.patch.sheets.refine accuracy.index).gauge)
  ((Specification.valueSpecification parameter 1).numerator.scale
    (Specification.valueSpecification parameter 1).scale))
variable {anchors : PrimitiveAnchors primitives} {offsets : Offsets anchors.edges} {points : List Canonical}
variable (mesh : CommonMesh assigned.domain.geometry (allCells assigned.domain.geometry) points)
variable (included : ∀ point ∈ assigned.split.points, point ∈ points)
variable (readings : SharedPrimitiveValues anchors offsets mesh.surface)

/-- The original coordinate-numerator work/model bank and one actual fragment comparison on its retained head.

The full actual work and stage model product remain unchanged. Its head
model retains its original request, inverse, powers, primitive and pullback
factories. The face accuracy, primitive constants and mesh remain independent.
-/
abbrev CoordinateFragmentComparison :=
  {value : PolynomialWork (.cons request.patch request.patch_finishInside tail)
      polynomialFloor (Specification.valueSpecification parameter 1) × work.Models polynomialStage //
    value = (work, models)} ×
  {value : PolynomialModelComparison.Cache assigned models.1.2.val accuracy primitives mesh included readings //
    value = PolynomialModelComparison.build assigned models.1.2.val accuracy primitives mesh included readings
      (Specification.valueSpecification_denominatorPairs parameter 1)}

/-- Attach the SAME actual coordinate-numerator programme model to the original retained physical fragment.

The generic operation consumes the supplied model's own inverse and
primitive, transporting both jointly by the original neighborhood factory.
Only the new signed numerical comparisons are prepared; the source work,
model bank, selectors, Points, primitive bank and mesh are all supplied caches.
-/
def compareCoordinateFragment :
    CoordinateFragmentComparison assigned work models accuracy primitives mesh included readings :=
  let originals : {value : PolynomialWork (.cons request.patch request.patch_finishInside tail)
      polynomialFloor (Specification.valueSpecification parameter 1) × work.Models polynomialStage //
      value = (work, models)} := ⟨(work, models), rfl⟩
  let compared : {value : PolynomialModelComparison.Cache assigned models.1.2.val
      accuracy primitives mesh included readings //
      value = PolynomialModelComparison.build assigned models.1.2.val accuracy primitives mesh included readings
        (Specification.valueSpecification_denominatorPairs parameter 1)} :=
    ⟨PolynomialModelComparison.build assigned models.1.2.val accuracy primitives mesh included readings
      (Specification.valueSpecification_denominatorPairs parameter 1), rfl⟩
  ⟨originals, compared⟩

namespace CoordinateFragmentComparison

variable {assigned work models accuracy primitives mesh included readings}
variable (kept : CoordinateFragmentComparison assigned work models accuracy primitives mesh included readings)

/-- Read the actual sole full-model comparison; its nested value and bound are the retained numerical caches. -/
@[expose] def comparison :
    PolynomialModelComparison.Cache assigned models.1.2.val accuracy primitives mesh included readings := kept.2.val

/-- Both complete given source products retain their literal original identities. -/
theorem originals_eq : kept.1.val = (work, models) := kept.1.property

/-- The retained result is the original generic constructor at the genuine coordinate-numerator specification. -/
theorem comparison_eq : kept.comparison = PolynomialModelComparison.build assigned models.1.2.val
    accuracy primitives mesh included readings (Specification.valueSpecification_denominatorPairs parameter 1) :=
  kept.2.property

/-- The whole original head model keeps its own actual selected-request and polynomial-model factory. -/
theorem model_factory : kept.comparison.originalModel = PolynomialModel.build
    (curve := Fibre.frameCurve frame) (differential := Specification.valueSpecification parameter 1)
    models.1.1.val (work.entry 0).1.val
    (Approximation.Rational.Geometric.Basic.quarterRadius_pos
      (Data.Rat.Fraction.Cast.Order.natCast_pos_direct (n := 1) (Nat.zero_lt_succ 0)) polynomialStage) :=
  kept.comparison.originalModel_eq.trans models.1.2.property

/-- The actual coordinate-channel source primitive and numerical fragment increment obey their finite piece charge.

The left value reads the same supplied face mesh. The right increment uses
the complete original source model's polynomial, with every additive constant
preserved. This concerns the fragment endpoints; no old value-zero gap is used.
-/
theorem accurate : normSq (kept.comparison.comparison.value -
    (models.1.2.val.primitive.primitive.value.eval fragment.located.last -
      models.1.2.val.primitive.primitive.value.eval fragment.located.first)) ≤ kept.comparison.comparison.bound :=
  kept.comparison.accurate

end CoordinateFragmentComparison

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent
