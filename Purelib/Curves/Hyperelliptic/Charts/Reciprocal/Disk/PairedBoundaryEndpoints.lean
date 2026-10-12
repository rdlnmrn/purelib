module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartConnections
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedPairedRadialRibbon
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Riemann.RootContinuation.RootRadialGeometry
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentBoundaries
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSourceRootJoins
import Init.Data.Fin.Basic
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAdjacency
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPreparation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRequestedBoundary
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Owners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.Dyadic.DyadicTrace
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.Normalization.ReciprocalDiskCommonSourceCharts
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedArcArea

public section

/-! The retained common-chart endpoints are the actual parent endpoints.
Their source-root equivalence transports to the cap coordinate programs;
equality of physical positions alone is never used as root closure. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.ChartRequest

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Name
open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartConnections
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSourceRootJoins
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Riemann.Normalization
open Purelib.Riemann.Readings.PrimitiveAreaBounds
open Purelib.Riemann.RootContinuation.RootRadialGeometry
open Purelib.Topology.Polygon
open Purelib.Topology.Polygon.Stokes
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels (Data)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover (CommonCover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank (ChartRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest (Parameter)
variable {genus count otherCount depth floor : Nat} {curve : HyperellipticCurve
  genus}
  {differential other : Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : PreparedPatch parent}
  {otherPatch : PreparedPatch
    (Purelib.Riemann.Integration.PreparedEdgeRecasting.recastCenteredEdge other parent)}
  {data : Data patch count} {otherData :
    Data otherPatch otherCount}
  {cover : Cover data} {otherCover :
    Cover otherData}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {common :
    CommonCover cover otherCover}
  {target : Coordinate} (request :
    ChartRequest regular common depth target floor)

/-- The exact first parameter of the original retained common-chart request. -/
@[expose] def firstParameter : Coordinate :=
  SourceChartRequest.Parameter (geometry := (request.plans.get common.firstIndex).geometry) 0
/-- The exact final parameter of the original retained common-chart request. -/
@[expose] def lastParameter : Coordinate :=
  SourceChartRequest.Parameter (geometry := (request.plans.get common.lastIndex).geometry)
    (Fin.last (request.plans.get common.lastIndex).geometry.tail.length)

/-- The actual retained original root owner at the common chart's first vertex. -/
@[expose] def firstPoint := ((request.plans.get common.firstIndex).geometry.vertices.get 0).first
/-- The actual retained original root owner at the common chart's final vertex. -/
@[expose] def lastPoint := ((request.plans.get common.lastIndex).geometry.vertices.get
  (Fin.last (request.plans.get common.lastIndex).geometry.tail.length)).first

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.ChartRequest
/-- The original complete common chart starts at parent parameter zero. -/
theorem firstParameter_eq : firstParameter request = 0 := common.first_parameter
/-- The original complete common chart ends at parent parameter one. -/
theorem lastParameter_eq : lastParameter request = 1 :=
  (request.plans.get common.lastIndex).geometry.last_parameter.trans common.last_parameter

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.ChartRequest

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.ReciprocalDiskArcOwners

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Name
open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartConnections
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSourceRootJoins
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Riemann.Normalization
open Purelib.Riemann.Readings.PrimitiveAreaBounds
open Purelib.Riemann.RootContinuation.RootRadialGeometry
open Purelib.Topology.Polygon
open Purelib.Topology.Polygon.Stokes
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels (Data)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cell)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels (RootModel)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners (Point Join)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
variable {genus count otherCount : Nat} {curve : HyperellipticCurve genus}
  {differential other : Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {otherParent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve other}
  {patch : PreparedPatch parent}
  {otherPatch : PreparedPatch otherParent}
  {data : Data patch count} {otherData :
    Data otherPatch otherCount}
  {edge otherEdge : ParameterEdge}
  {cell : Cell data edge} {otherCell :
    Cell otherData otherEdge}
  {model : RootModel cell} {otherModel :
    RootModel otherCell} {parameter
    otherParameter : Coordinate}

/-- Transport the original physical endpoint equality and source-root equivalence to the two actual retained reciprocal
chart owners. -/
@[expose] def sourceEndpointJoin (first : ArcOwners.Point cap model parameter) (last : ArcOwners.Point cap otherModel
  otherParameter)
    (firstParameter : parameter = 1) (lastParameter : otherParameter = 0)
    (same : parent.edge.point 1 = otherParent.edge.point 0)
    (roots : Gaussian.Equivalence.NamedEquivalent (parent.edge.rootName 1 (by decide))
      (otherParent.edge.rootName 0 otherParent.edge.baseInside)) : ArcOwners.Join first last := by
  subst parameter
  subst otherParameter
  let source := SourceJoin.build first.root last.root
    (parent.edge.point 1) rfl same.symm roots
  exact Join.ofRoots first last same (SourceJoin.rootEquivalent
    (first := first.root) (last := last.root) source)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.ReciprocalDiskArcOwners

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.BoundaryBankRequest

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Name
open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartConnections
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSourceRootJoins
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Riemann.Normalization
open Purelib.Riemann.Readings.PrimitiveAreaBounds
open Purelib.Riemann.RootContinuation.RootRadialGeometry
open Purelib.Topology.Polygon
open Purelib.Topology.Polygon.Stokes
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest (Request)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts (ChartParent)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentBoundaries (BoundaryBankRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners (Join)
open Purelib.Riemann.RootContinuation
variable {genus : Nat} {curve : HyperellipticCurve genus} {differential other :
  Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {parents : List (Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)}
  {target requested : Coordinate} {minimum : Nat}
  {original : Request regular other parents
    target minimum}
  (request : BoundaryBankRequest original
    requested)

/-- The sheet-aware join between the actual last owner of one retained parent and the first owner of another. -/
@[expose] def EndpointJoin (i j : Fin original.plans.length) :=
  ArcOwners.Join (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.ChartRequest.lastPoint
    (request.plans.get i).request)
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.ChartRequest.firstPoint (request.plans.get
    j).request)

/-- The actual retained endpoint owners consume the original physical and sheet-aware source link. This works across
independently prepared parents. -/
@[expose] def endpointJoin (i j : Fin original.plans.length)
    (same : (PairedParentCharts.ChartParent original i).parent.edge.point 1 = (PairedParentCharts.ChartParent original
      j).parent.edge.point 0)
    (roots : Gaussian.Equivalence.NamedEquivalent ((PairedParentCharts.ChartParent original i).parent.edge.rootName 1
      (by decide))
      ((PairedParentCharts.ChartParent original j).parent.edge.rootName 0 (PairedParentCharts.ChartParent original
        j).parent.edge.baseInside)) :
        EndpointJoin request i j
        :=
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.ReciprocalDiskArcOwners.sourceEndpointJoin
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.ChartRequest.lastPoint (request.plans.get
    i).request) (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.ChartRequest.firstPoint
    (request.plans.get j).request)
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.ChartRequest.lastParameter_eq
      (request.plans.get i).request)
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.ChartRequest.firstParameter_eq
      (request.plans.get j).request) same roots

/-- The named primitive equivalence at two exact retained parent endpoints for the supplied original cap sample. -/
@[expose] def EndpointPrimitiveLink (i j : Fin original.plans.length) {numerator : Differentials.Basic.Differential
  genus}
    {index : Nat} {box : Rational.Box} (sample : Primitives.Sample cap numerator index box) :=
  Gaussian.Equivalence.NamedEquivalent
    ((Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.ChartRequest.lastPoint (request.plans.get
      i).request).coordinates.chartPrimitive sample).name
    ((Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.ChartRequest.firstPoint (request.plans.get
      j).request).coordinates.chartPrimitive sample).name

/-- Both shared cap primitives consume the same retained root-owner join. -/
@[expose] def Evaluation.endpointPrimitives (evaluated : request.Evaluation) (i j : Fin original.plans.length)
    (joined : EndpointJoin
      request i j) :
    EndpointPrimitiveLink
      request i j evaluated.firstCap ×
      EndpointPrimitiveLink
      request i j evaluated.otherCap :=
  ⟨joined.primitiveEquivalent evaluated.firstCap, joined.primitiveEquivalent evaluated.otherCap⟩

open Purelib.Data.Rat.Fraction.Compatibility
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_nonneg normSq_neg)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian)

/-- The original coordinate approximation name retained at the parent's actual final chart owner. -/
@[expose] def LastApproximation (i : Fin original.plans.length) :=
  Sampling.approximation
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.ChartRequest.lastPoint (request.plans.get
      i).request).coordinates.coordinate.prepared.denominator.name

/-- The original coordinate approximation name retained at the parent's actual initial chart owner. -/
@[expose] def FirstApproximation (i : Fin original.plans.length) :=
  Sampling.approximation
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.ChartRequest.firstPoint (request.plans.get
      i).request).coordinates.coordinate.prepared.denominator.name

set_option genInjectivity false in
/-- A cross-parent comparison is selected before either retained endpoint is read. Its coefficient cache is the one
already prepared for the left parent. -/
structure JunctionRequest (i j : Fin original.plans.length) (joined :
  EndpointJoin request i j)
    (tolerance : InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The cached paired primitive sensitivity scale from the left parent's original coefficient bounds. -/ scale :
    InverseRootPolynomial.Coordinate
  /-- The sensitivity scale is exactly 512 times the squared maximum of the two retained differential coefficient
    bounds. -/ scale_eq : scale = 512 * (max ((request.plans.get i).preparation.bounds.coefficientUpper differential)
    ((request.plans.get i).preparation.bounds.coefficientUpper other)) ^ 2
  /-- The cached original paired sensitivity scale is nonnegative. -/ nonnegative : 0 ≤ scale
  /-- The cached coordinate comparison budget for the actual endpoint pair. -/ budget : InverseRootPolynomial.Coordinate
  /-- The coordinate budget is the requested junction tolerance divided by the original scale plus one. -/ budget_eq :
    budget = tolerance / (scale + 1)
  /-- The actual coordinate-name comparison retaining both endpoint approximations and the original stage floors. -/
    comparison : Gaussian.Equivalence.Comparison
    (LastApproximation request
    i)
    (FirstApproximation request
      j) floor floor budget
  /-- The common cached reading stage paying both sides of the original coordinate comparison. -/ index : Nat
  /-- The common junction reading stage is exactly the maximum of both original comparison stages. -/ index_eq : index =
    max comparison.leftIndex comparison.rightIndex

constructive_injectivity JunctionRequest

/-- Prepare the actual retained endpoint-name comparison using the left parent's existing coefficient cache and the
requested positive tolerance. -/
@[expose] def JunctionRequest.build (i j : Fin original.plans.length) (joined :
  EndpointJoin request i j)
    (tolerance : InverseRootPolynomial.Coordinate) (positive : 0 < tolerance) (floor : Nat) :
    JunctionRequest request i j
      joined tolerance floor :=
  let bounds := (request.plans.get i).preparation.bounds
  let scale : Coordinate := 512 * (max (bounds.coefficientUpper differential) (bounds.coefficientUpper other)) ^ 2
  have nonnegative : 0 ≤ scale := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
    (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  let budget := tolerance / (scale + 1)
  let comparison := joined.coordinate.compare floor floor budget
    (Fraction.Order.Field.div_pos_direct positive (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct nonnegative
      (by decide)))
  ⟨scale, rfl, nonnegative, budget, rfl, comparison, max comparison.leftIndex comparison.rightIndex, rfl⟩

variable {request}

/-- The actual retained reading stage at the parent's final common-chart vertex. -/
@[expose] def Evaluation.lastStage (evaluated : request.Evaluation) (i : Fin original.plans.length) : Nat :=
  ((evaluated.entries.get i).entries.get (PairedParentCharts.ChartParent original
    i).common.lastIndex).evaluated.chart.retained.area.refined.stage

/-- The actual retained reading stage at the parent's first common-chart vertex. -/
@[expose] def Evaluation.firstStage (evaluated : request.Evaluation) (i : Fin original.plans.length) : Nat :=
  ((evaluated.entries.get i).entries.get (PairedParentCharts.ChartParent original
    i).common.firstIndex).evaluated.chart.retained.area.refined.stage

/-- The actual acquired coordinate at the parent's final retained common-chart vertex. -/
@[expose] def Evaluation.lastCoordinate (evaluated : request.Evaluation) (i : Fin original.plans.length) : Gaussian :=
  (Evaluation.chartCoordinate (evaluated.entries.get i)) (PairedParentCharts.ChartParent original i).common.lastIndex
    (Fin.last ((request.plans.get i).request.plans.get (PairedParentCharts.ChartParent original
      i).common.lastIndex).geometry.tail.length)

/-- The actual acquired coordinate at the parent's first retained common-chart vertex. -/
@[expose] def Evaluation.firstCoordinate (evaluated : request.Evaluation) (i : Fin original.plans.length) : Gaussian :=
  (Evaluation.chartCoordinate (evaluated.entries.get i)) (PairedParentCharts.ChartParent original i).common.firstIndex 0

/-- The acquired final coordinate is the original retained endpoint approximation sampled at its actual reading stage.
-/
theorem Evaluation.lastCoordinate_eq (evaluated : request.Evaluation) (i : Fin original.plans.length) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.BoundaryBankRequest.Evaluation.lastCoordinate
      evaluated i =
      (LastApproximation request
      i).sample
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.BoundaryBankRequest.Evaluation.lastStage
      evaluated i) :=
  (((evaluated.entries.get i).entries.get (PairedParentCharts.ChartParent original
    i).common.lastIndex).evaluated.chart.retained.area.evaluated.readings.get
    (Fin.last ((request.plans.get i).request.plans.get (PairedParentCharts.ChartParent original
      i).common.lastIndex).geometry.tail.length)).first.coordinate_eq

/-- The acquired first coordinate is the original retained endpoint approximation sampled at its actual reading stage.
-/
theorem Evaluation.firstCoordinate_eq (evaluated : request.Evaluation) (i : Fin original.plans.length) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.BoundaryBankRequest.Evaluation.firstCoordinate
      evaluated i =
      (FirstApproximation
      request i).sample
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.BoundaryBankRequest.Evaluation.firstStage
      evaluated i) :=
  (((evaluated.entries.get i).entries.get (PairedParentCharts.ChartParent original
    i).common.firstIndex).evaluated.chart.retained.area.evaluated.readings.get 0).first.coordinate_eq

/-- The paired primitive values read from the two exact cap samples shared by the whole retained parent bank. -/
@[expose] def Evaluation.radialValues (evaluated : request.Evaluation) (point : InverseRootPolynomial.Gaussian) :
  Stokes.PrimitivePoint :=
  ⟨evaluated.firstCap.primitive.value.eval point, evaluated.otherCap.primitive.value.eval point⟩

/-- The actual cross-parent radial area difference minus the retained endpoint joining-edge area. -/
@[expose] def Evaluation.junctionError (evaluated : request.Evaluation) (i j : Fin original.plans.length) : Gaussian :=
  Bilinear.radialArea
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.BoundaryBankRequest.Evaluation.radialValues
    evaluated) evaluated.radialDepth
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.BoundaryBankRequest.Evaluation.firstCoordinate
    evaluated j) -
    Bilinear.radialArea
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.BoundaryBankRequest.Evaluation.radialValues
      evaluated) evaluated.radialDepth
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.BoundaryBankRequest.Evaluation.lastCoordinate
      evaluated i) -
    Stokes.edgeArea
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.BoundaryBankRequest.Evaluation.radialValues
      evaluated
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.BoundaryBankRequest.Evaluation.lastCoordinate
      evaluated i))
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.BoundaryBankRequest.Evaluation.radialValues
        evaluated
        (Evaluation.firstCoordinate
        evaluated j))

/-- The paid original junction comparison bounds the acquired first-to-last coordinate gap at their retained reading
stages. -/
private theorem JunctionRequest.coordinate_accurate {i j : Fin original.plans.length} {joined :
  EndpointJoin request i j}
    {tolerance : InverseRootPolynomial.Coordinate} {floor : Nat} (junction :
      JunctionRequest request i
      j joined tolerance floor)
    (evaluated : request.Evaluation) (later : junction.index ≤ evaluated.externalFloor) :
    Data.Gaussian.Norm.Basic.normSq
      (Evaluation.firstCoordinate
      evaluated j -
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.BoundaryBankRequest.Evaluation.lastCoordinate
      evaluated i) < junction.budget := by
  have firstLater : junction.index ≤
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.BoundaryBankRequest.Evaluation.lastStage
    evaluated i := later.trans
    ((evaluated.readingFloors i).symm.trans_le ((evaluated.entries.get i).readingsLater (PairedParentCharts.ChartParent
      original i).common.lastIndex))
  have lastLater : junction.index ≤
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.BoundaryBankRequest.Evaluation.firstStage
    evaluated j := later.trans
    ((evaluated.readingFloors j).symm.trans_le ((evaluated.entries.get j).readingsLater (PairedParentCharts.ChartParent
      original j).common.firstIndex))
  rw [show
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.BoundaryBankRequest.Evaluation.firstCoordinate
    evaluated j -
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.BoundaryBankRequest.Evaluation.lastCoordinate
    evaluated i =
    -(Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.BoundaryBankRequest.Evaluation.lastCoordinate
      evaluated i -
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.BoundaryBankRequest.Evaluation.firstCoordinate
      evaluated j) by ring1, Data.Gaussian.Norm.Basic.normSq_neg,
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.BoundaryBankRequest.Evaluation.lastCoordinate_eq
      evaluated,
      Evaluation.firstCoordinate_eq
      evaluated]
  exact junction.comparison.close
    ((Data.Nat.Order.le_max_left _ _).trans (junction.index_eq.ge.trans firstLater))
    ((Data.Nat.Order.le_max_right _ _).trans (junction.index_eq.ge.trans lastLater))

/-- Pay the cross-parent radial cancellation on the retained endpoint coordinates and the shared radial mesh, without
assuming equality of samples. -/
theorem JunctionRequest.accurate {i j : Fin original.plans.length} {joined :
  EndpointJoin request i j}
    {tolerance : InverseRootPolynomial.Coordinate} {floor : Nat} (junction :
      JunctionRequest request i
      j joined tolerance floor)
    (evaluated : request.Evaluation) (later : junction.index ≤ evaluated.externalFloor)
    (branch : HyperellipticReciprocal.originOrder curve = 1) :
    Data.Gaussian.Norm.Basic.normSq
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.BoundaryBankRequest.Evaluation.junctionError
      evaluated i j) < tolerance := by
  have close := junction.coordinate_accurate evaluated later
  have firstInside := (Evaluation.chart_square_inside (evaluated.entries.get i)) branch (PairedParentCharts.ChartParent
    original i).common.lastIndex
    (Fin.last ((request.plans.get i).request.plans.get (PairedParentCharts.ChartParent original
      i).common.lastIndex).geometry.tail.length)
  have lastInside := (Evaluation.chart_square_inside (evaluated.entries.get j)) branch (PairedParentCharts.ChartParent
    original j).common.firstIndex 0
  have bound := (request.plans.get i).preparation.bounds.paired_radial_connector_bound
    evaluated.firstCap evaluated.otherCap branch firstInside lastInside evaluated.radialDepth
  change Data.Gaussian.Norm.Basic.normSq
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.BoundaryBankRequest.Evaluation.junctionError
    evaluated i j) ≤ _ at bound
  rw [← junction.scale_eq] at bound
  have positive : 0 < junction.scale + 1 := Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
    junction.nonnegative (by decide)
  apply bound.trans_lt
  calc
    _ ≤ (junction.scale + 1) * Data.Gaussian.Norm.Basic.normSq
      (Evaluation.firstCoordinate
      evaluated j -
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.BoundaryBankRequest.Evaluation.lastCoordinate
      evaluated i) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (le_add_of_nonneg_right (by decide))
        (Data.Gaussian.Norm.Basic.normSq_nonneg _)
    _ < (junction.scale + 1) * junction.budget := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct positive close
    _ = tolerance := by
      rw [junction.budget_eq, Fraction.Field.mul_comm]
      exact Fraction.Field.div_mul_cancel_of_ne _ _ positive.ne'

/-- The same preselected coordinate comparison also pays the actual paired increment inserted between the two retained
parent traces. -/
private theorem JunctionRequest.radial_increment_accurate {i j : Fin original.plans.length} {joined :
  EndpointJoin request i j}
    {tolerance : InverseRootPolynomial.Coordinate} {floor : Nat} (junction :
      JunctionRequest request i
      j joined tolerance floor)
    (evaluated : request.Evaluation) (later : junction.index ≤ evaluated.externalFloor)
    (branch : HyperellipticReciprocal.originOrder curve = 1) :
    PrimitivePoint.Bounded
      ((Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.BoundaryBankRequest.Evaluation.radialValues
      evaluated
      (Evaluation.firstCoordinate
      evaluated j)).sub
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.BoundaryBankRequest.Evaluation.radialValues
        evaluated
        (Evaluation.lastCoordinate
        evaluated i))) tolerance := by
  let bounds := (request.plans.get i).preparation.bounds
  let coefficient := max (bounds.coefficientUpper differential) (bounds.coefficientUpper other)
  have scale : 2 * coefficient ≤ junction.scale + 1 := by
    have square := Fraction.Order.Arithmetic.sq_nonneg_direct (coefficient - 1)
    have first : 2 * coefficient ≤ coefficient^2 + 1 := by
      have translated := Fraction.Order.Arithmetic.add_le_add_direct square (le_refl (2 * coefficient))
      exact (by ring1 : 2 * coefficient = 0 + 2 * coefficient).trans_le
        (translated.trans_eq (by ring1))
    have larger := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by
        decide +kernel : (1 : InverseRootPolynomial.Coordinate) ≤ 512)
      (Fraction.Order.Arithmetic.sq_nonneg_direct coefficient)
    rw [Fraction.Field.one_mul] at larger
    have result := first.trans (Fraction.Order.Arithmetic.add_le_add_direct larger (le_refl (1 :
      InverseRootPolynomial.Coordinate)))
    exact result.trans_eq (congrArg (fun value : InverseRootPolynomial.Coordinate => value + 1) junction.scale_eq.symm)
  have firstInside := (Evaluation.chart_square_inside (evaluated.entries.get i)) branch (PairedParentCharts.ChartParent
    original i).common.lastIndex
    (Fin.last ((request.plans.get i).request.plans.get (PairedParentCharts.ChartParent original
      i).common.lastIndex).geometry.tail.length)
  have lastInside := (Evaluation.chart_square_inside (evaluated.entries.get j)) branch (PairedParentCharts.ChartParent
    original j).common.firstIndex 0
  have close := junction.coordinate_accurate evaluated later
  have positive : 0 < junction.scale + 1 := Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
    junction.nonnegative (by decide)
  have paid : (junction.scale + 1) * Data.Gaussian.Norm.Basic.normSq
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.BoundaryBankRequest.Evaluation.firstCoordinate
    evaluated j -
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.BoundaryBankRequest.Evaluation.lastCoordinate
    evaluated i) < tolerance := by
    have estimate := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct positive close
    apply estimate.trans_eq
    rw [junction.budget_eq, Fraction.Field.mul_comm]
    exact Fraction.Field.div_mul_cancel_of_ne _ _ positive.ne'
  have scalar {d : Differentials.Basic.Differential genus} (sample : Primitives.Sample cap d request.index collar.box)
      (coefficientLe : bounds.coefficientUpper d ≤ coefficient) :
      Data.Gaussian.Norm.Basic.normSq (sample.primitive.value.eval
        (Evaluation.firstCoordinate
        evaluated j) -
        sample.primitive.value.eval
          (Evaluation.lastCoordinate
          evaluated i)) ≤ tolerance := by
    have bound := bounds.chord_increment sample branch firstInside lastInside
      (left := 0) (right := 1) (by decide) (by decide)
    change Data.Gaussian.Norm.Basic.normSq (sample.primitive.value.eval
      (Riemann.RootContinuation.RootRadialGeometry.chord
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.BoundaryBankRequest.Evaluation.lastCoordinate
        evaluated i)
        (Evaluation.firstCoordinate
        evaluated j) 1) -
      sample.primitive.value.eval (Riemann.RootContinuation.RootRadialGeometry.chord

          (Evaluation.lastCoordinate
          evaluated i)
          (Evaluation.firstCoordinate
          evaluated j) 0)) ≤
      2 * bounds.coefficientUpper d * Data.Gaussian.Norm.Basic.normSq
        (Evaluation.firstCoordinate
        evaluated j -
        Evaluation.lastCoordinate
        evaluated i) * (1 - 0)^2 at bound
    have first : Riemann.RootContinuation.RootRadialGeometry.chord
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.BoundaryBankRequest.Evaluation.lastCoordinate
      evaluated i)
      (Evaluation.firstCoordinate
      evaluated j) 0 =
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.BoundaryBankRequest.Evaluation.lastCoordinate
      evaluated i := by
      unfold Riemann.RootContinuation.RootRadialGeometry.chord Data.Gaussian.Scale.scale
      apply Data.Gaussian.Basic.ext <;>
        simp only [Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im, -eq_self, -iff_self] <;> ring1
    have last : Riemann.RootContinuation.RootRadialGeometry.chord
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.BoundaryBankRequest.Evaluation.lastCoordinate
      evaluated i)
      (Evaluation.firstCoordinate
      evaluated j) 1 =
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.BoundaryBankRequest.Evaluation.firstCoordinate
      evaluated j := by
      unfold Riemann.RootContinuation.RootRadialGeometry.chord Data.Gaussian.Scale.scale
      apply Data.Gaussian.Basic.ext <;>
        simp only [Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im, -eq_self, -iff_self] <;> ring1
    rw [first, last, show ((1 : InverseRootPolynomial.Coordinate) - 0)^2 = 1 by decide, mul_one] at bound
    exact bound.trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct coefficientLe (by decide)).trans scale)
      (Data.Gaussian.Norm.Basic.normSq_nonneg _)).trans paid.le)
  constructor
  · rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical]
    exact scalar evaluated.firstCap (Fraction.Order.Basic.le_max_left _ _)
  · rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical]
    exact scalar evaluated.otherCap (Fraction.Order.Basic.le_max_right _ _)

/-- The actual paired primitive increment between the retained last chart point and the next first chart point. -/
@[expose] def Evaluation.junctionIncrement (evaluated : request.Evaluation) (i j : Fin original.plans.length) :
    Stokes.PrimitivePoint :=
  ((Evaluation.firstChartPoint (evaluated.entries.get j)) (PairedParentCharts.ChartParent original
    j).common.firstIndex).sub
    ((Evaluation.lastChartPoint (evaluated.entries.get i)) (PairedParentCharts.ChartParent original i).common.lastIndex)

/-- The actual junction increment reads the same two exact shared cap samples at its retained endpoint coordinates. -/
theorem Evaluation.junctionIncrement_eq (evaluated : request.Evaluation) (i j : Fin original.plans.length)
    (branch : HyperellipticReciprocal.originOrder curve = 1) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.BoundaryBankRequest.Evaluation.junctionIncrement
      evaluated i j =
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.BoundaryBankRequest.Evaluation.radialValues
      evaluated
      (Evaluation.firstCoordinate
      evaluated j)).sub
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.BoundaryBankRequest.Evaluation.radialValues
        evaluated
        (Evaluation.lastCoordinate
        evaluated i)) := by
  have first : (Evaluation.firstChartPoint (evaluated.entries.get j)) (PairedParentCharts.ChartParent original
    j).common.firstIndex =
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.BoundaryBankRequest.Evaluation.radialValues
        evaluated
        (Evaluation.firstCoordinate
        evaluated j) := by
    unfold Evaluation.firstChartPoint
    rw [Evaluation.chartPoint_readback (evaluated.entries.get j) branch]
    rw [(evaluated.shared j).1, (evaluated.shared j).2]
    rfl
  have last : (Evaluation.lastChartPoint (evaluated.entries.get i)) (PairedParentCharts.ChartParent original
    i).common.lastIndex =
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.BoundaryBankRequest.Evaluation.radialValues
        evaluated
        (Evaluation.lastCoordinate
        evaluated i) := by
    unfold Evaluation.lastChartPoint
    rw [Evaluation.chartPoint_readback (evaluated.entries.get i) branch]
    rw [(evaluated.shared i).1, (evaluated.shared i).2]
    rfl
  exact congrArg₂ PrimitivePoint.sub first last

/-- The paid original junction request bounds both components of the actual retained paired joining increment. -/
theorem JunctionRequest.increment_accurate {i j : Fin original.plans.length} {joined :
  EndpointJoin request i j}
    {tolerance : InverseRootPolynomial.Coordinate} {floor : Nat} (junction :
      JunctionRequest request i
      j joined tolerance floor)
    (evaluated : request.Evaluation) (later : junction.index ≤ evaluated.externalFloor)
    (branch : HyperellipticReciprocal.originOrder curve = 1) :
    PrimitivePoint.Bounded
      (Evaluation.junctionIncrement
      evaluated i j) tolerance := by
  rw
    [Evaluation.junctionIncrement_eq
    evaluated i j branch]
  exact junction.radial_increment_accurate evaluated later branch

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.BoundaryBankRequest
