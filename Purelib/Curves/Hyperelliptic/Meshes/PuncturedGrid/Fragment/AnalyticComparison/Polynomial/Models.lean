module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AnalyticComparison.Polynomial
public import Purelib.Riemann.Normalization.ContinuedInverseRoot.Primitive.Polynomial
import Purelib.Riemann.Readings.UniformPreparedRequests.Covered
import Purelib.Integration.Polynomial.Gaussian.Cell.Spatial

/-! # Whole ordinary polynomial models on actual retained fragment caches

The complete original inverse/powers/primitive/pullback model remains data.
Its coupled neighborhood-index view changes no model or primitive constant.
The numerical fragment comparison consumes those same inverse and primitive
objects rather than constructing another source model or inverse table.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AnalyticComparison.PolynomialModelComparison

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces (RegularPrimitiveFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment (SheetEntry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rectangle (AxisPartition)
open Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions (Interval)
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood (UniformBounds UniformRequest)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.UniformRequest (PolynomialModel)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Model)
open Purelib.Riemann.Normalization.InverseRootPrimitive (PrimitiveModel)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Integration.RectangularSharedPrimitives (SharedPrimitiveValues)
open Purelib.Riemann.Branches.RectangularSheetGauge
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveOverlapBounds)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)
open Purelib.Riemann.Readings.RectangularExteriorBoundary.Geometry (allCells)
open Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh.RectangularInverseModels (CommonMesh)
open Purelib.LinearAlgebra.Grid (Offsets)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)

universe u

/-- Transport both GIVEN source-model caches jointly, retaining their whole refinement and primitive identities. -/
private def withSourceViews {polynomial numerator : CoefficientPolynomial} {count index : Nat}
    {first last : ContinuedNeighborhood polynomial count} (same : first = last)
    (inverse : Model polynomial first.base.box) (inverseFactory : inverse = first.base.refine index)
    (primitive : PrimitiveModel first index numerator) {Result : Type u}
    (consume : (viewedInverse : Model polynomial last.base.box) →
      viewedInverse = last.base.refine index → HEq viewedInverse inverse →
      (viewedPrimitive : PrimitiveModel last index numerator) → HEq viewedPrimitive primitive →
      viewedPrimitive.primitive.value = primitive.primitive.value → Result) : Result := by
  cases same
  exact consume inverse inverseFactory HEq.rfl primitive HEq.rfl rfl

variable {genus count modelFloor : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
variable {frames : RootFrames base.bank.grid} {source : Differential genus} {axes : PrimitiveAxes base.bank.grid}
variable {parent : CenteredEdge curve source} {domains : FaceDomainBank frames base.faces.regulars}
variable {target : Rational} {request : LocalRequest parent count target}
variable {cuts : List Rational} {partition : AxisPartition 0 1 cuts} {interval : Interval}
variable {fragment : RegularPrimitiveFragment axes parent partition interval}
variable (assigned : SheetEntry fragment domains request)
variable {differential : OddPowerDifferential curve.polynomial}
variable {sourceBounds : UniformBounds (request.patch.neighborhood count)}
variable {allowance : Rational} {positive : 0 < allowance}
variable {uniform : UniformRequest sourceBounds 0 (differential.numerator.scale differential.scale)
  modelFloor (allowance / 4)}
variable {first last : Canonical} {coordinate : Spatial.Coordinate first last}
variable (model : PolynomialModel (curve := curve) (differential := differential) uniform coordinate positive)
variable {globalBounds : PrimitiveOverlapBounds fragment.face.located.face.clearance
  (differential.numerator.scale differential.scale)} {tolerance : Rational}
variable (accuracy : GridPrimitiveAccuracy globalBounds assigned.domain.steps tolerance)
variable (targetPrimitives : Primitives
  (Transitions.oriented (assigned.domain.patch.sheets.refine accuracy.index).transitions
    (assigned.domain.patch.sheets.refine accuracy.index).gauge) (differential.numerator.scale differential.scale))
variable {anchors : PrimitiveAnchors targetPrimitives} {offsets : Offsets anchors.edges} {points : List Canonical}
variable (mesh : CommonMesh assigned.domain.geometry (allCells assigned.domain.geometry) points)
variable (included : ∀ point ∈ assigned.split.points, point ∈ points)
variable (readings : SharedPrimitiveValues anchors offsets mesh.surface)

/-- The complete original model, its jointly transported source caches and actual general-numerator fragment result.

The ordinary specification is certified explicitly. The original full
model's own stage/floor and the independent face mesh index remain distinct.
Both whole source HEq witnesses and the literal primitive polynomial survive.
-/
abbrev Cache :=
  {_value : Unit // differential.denominatorPairs = 0} ×
  {value : PolynomialModel (curve := curve) (differential := differential)
      uniform coordinate positive // value = model} ×
  (Σ inverse : {value : Model curve.polynomial request.neighborhood.base.box //
      value = request.neighborhood.base.refine uniform.selection.stage ∧ HEq value model.inverse},
  Σ primitive : {value : PrimitiveModel request.neighborhood uniform.selection.stage
      (differential.numerator.scale differential.scale) //
      HEq value model.primitive ∧ value.primitive.value = model.primitive.primitive.value},
  {value : NumeratorFragmentComparison.Cache (sourceIndex := uniform.selection.stage)
      assigned inverse.val inverse.property.1 primitive.val accuracy targetPrimitives mesh included readings //
    value = NumeratorFragmentComparison.build (sourceIndex := uniform.selection.stage)
      assigned inverse.val inverse.property.1 primitive.val accuracy targetPrimitives mesh included readings})

/-- Consume the GIVEN whole ordinary polynomial model and its original neighborhood factory, with no inverse replay. -/
def build (ordinary : differential.denominatorPairs = 0) :
    Cache assigned model accuracy targetPrimitives mesh included readings :=
  withSourceViews request.neighborhood_eq.symm model.inverse model.inverse_eq model.primitive
    (fun inverse inverseFactory inverseHeq primitive primitiveHeq primitiveValue =>
      let original : {value : PolynomialModel (curve := curve) (differential := differential)
          uniform coordinate positive // value = model} := ⟨model, rfl⟩
      let inverseView : {value : Model curve.polynomial request.neighborhood.base.box //
          value = request.neighborhood.base.refine uniform.selection.stage ∧ HEq value model.inverse} :=
        ⟨inverse, inverseFactory, inverseHeq⟩
      let primitiveView : {value : PrimitiveModel request.neighborhood uniform.selection.stage
          (differential.numerator.scale differential.scale) //
          HEq value model.primitive ∧ value.primitive.value = model.primitive.primitive.value} :=
        ⟨primitive, primitiveHeq, primitiveValue⟩
      let compared : {value : NumeratorFragmentComparison.Cache (sourceIndex := uniform.selection.stage)
          assigned inverseView.val inverseView.property.1 primitiveView.val
          accuracy targetPrimitives mesh included readings //
        value = NumeratorFragmentComparison.build (sourceIndex := uniform.selection.stage)
          assigned inverseView.val inverseView.property.1 primitiveView.val
          accuracy targetPrimitives mesh included readings} :=
        ⟨NumeratorFragmentComparison.build (sourceIndex := uniform.selection.stage)
          assigned inverseView.val inverseView.property.1 primitiveView.val
          accuracy targetPrimitives mesh included readings, rfl⟩
      ⟨⟨(), ordinary⟩, original, inverseView, primitiveView, compared⟩)

namespace Cache

variable {assigned model accuracy targetPrimitives mesh included readings}
variable (kept : Cache assigned model accuracy targetPrimitives mesh included readings)

/-- Read the SAME complete original polynomial model and all of its inverse/powers/primitive/pullback factories. -/
@[expose] def originalModel :
    PolynomialModel (curve := curve) (differential := differential) uniform coordinate positive := kept.2.1.val

/-- Read the same source inverse under the original request-neighborhood index view. -/
@[expose] def inverse : Model curve.polynomial request.neighborhood.base.box := kept.2.2.1.val

/-- Read the same original primitive under that exact coupled neighborhood transport. -/
@[expose] def primitive : PrimitiveModel request.neighborhood uniform.selection.stage
    (differential.numerator.scale differential.scale) := kept.2.2.2.1.val

/-- Read the actual one general-numerator fragment comparison on those same transported source caches. -/
@[expose] def comparison : NumeratorFragmentComparison.Cache (sourceIndex := uniform.selection.stage)
    assigned kept.inverse kept.2.2.1.property.1 kept.primitive accuracy targetPrimitives mesh included readings :=
  kept.2.2.2.2.val

include kept in
/-- The accepted original specification is ordinary, without a holomorphic differential relabeling. -/
theorem ordinary : differential.denominatorPairs = 0 := kept.1.property

/-- The whole given polynomial model is retained unchanged. -/
theorem originalModel_eq : kept.originalModel = model := kept.2.1.property

/-- The given source inverse retains its entire original cache heterogeneously. -/
theorem inverse_heq : HEq kept.inverse model.inverse := kept.2.2.1.property.2

/-- The given source primitive retains its entire original cache heterogeneously. -/
theorem primitive_heq : HEq kept.primitive model.primitive := kept.2.2.2.1.property.1

/-- The source primitive polynomial and every additive constant remain exactly the original model's value. -/
theorem primitive_value_eq : kept.primitive.primitive.value = model.primitive.primitive.value :=
  kept.2.2.2.1.property.2

/-- The actual whole comparison is its sole original general-numerator constructor on these retained cache views. -/
theorem comparison_eq : kept.comparison = NumeratorFragmentComparison.build (sourceIndex := uniform.selection.stage)
    assigned kept.inverse kept.2.2.1.property.1 kept.primitive accuracy targetPrimitives mesh included readings :=
  kept.2.2.2.2.property

/-- The actual shared endpoint increment compares to the SAME whole model's partial primitive increment. -/
theorem accurate : normSq (kept.comparison.value -
    (model.primitive.primitive.value.eval fragment.located.last -
      model.primitive.primitive.value.eval fragment.located.first)) ≤ kept.comparison.bound :=
  Eq.mp (congrArg (fun increment : Canonical =>
    normSq (kept.comparison.value - increment) ≤ kept.comparison.bound)
      (congrArg (fun value : CoefficientPolynomial =>
        value.eval fragment.located.last - value.eval fragment.located.first) kept.primitive_value_eq))
    kept.comparison.accurate

end Cache

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AnalyticComparison.PolynomialModelComparison
