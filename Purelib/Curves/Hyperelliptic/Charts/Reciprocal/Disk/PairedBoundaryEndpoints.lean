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

open Purelib.Data.Rat.Fraction.Order

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
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {parent : Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : PreparedPatch parent}
  {otherPatch : PreparedPatch
    (recastCenteredEdge other parent)}
  {data : Data patch count} {otherData :
    Data otherPatch otherCount}
  {cover : Cover data} {otherCover :
    Cover otherData}
  {regular : RegularBounds.Data cap} {common :
    CommonCover cover otherCover}
  {target : Coordinate} (request :
    ChartRequest regular common depth target floor)

/-- The exact first parameter of the original retained common-chart request. -/
@[expose] def firstParameter : Coordinate :=
  Parameter (geometry := (request.plans.get common.firstIndex).geometry) 0
/-- The exact final parameter of the original retained common-chart request. -/
@[expose] def lastParameter : Coordinate :=
  Parameter (geometry := (request.plans.get common.lastIndex).geometry)
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
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {parent : Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {otherParent : Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve other}
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
@[expose] def sourceEndpointJoin (first : Point cap model parameter) (last : Point cap otherModel
  otherParameter)
    (firstParameter : parameter = 1) (lastParameter : otherParameter = 0)
    (same : parent.edge.point 1 = otherParent.edge.point 0)
    (roots : Gaussian.Equivalence.NamedEquivalent (parent.edge.rootName 1 (by decide))
      (otherParent.edge.rootName 0 otherParent.edge.baseInside)) : Join first last := by
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
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {regular : RegularBounds.Data cap}
  {parents : List (Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)}
  {target requested : Coordinate} {minimum : Nat}
  {original : Request regular other parents
    target minimum}
  (request : BoundaryBankRequest original
    requested)

/-- The sheet-aware join between the actual last owner of one retained parent and the first owner of another. -/
@[expose] def EndpointJoin (i j : Fin original.plans.length) :=
  Join (ChartRequest.lastPoint
    (request.plans.get i).request)
    (ChartRequest.firstPoint (request.plans.get
    j).request)

/-- The actual retained endpoint owners consume the original physical and sheet-aware source link. This works across
independently prepared parents. -/
@[expose] def endpointJoin (i j : Fin original.plans.length)
    (same : (ChartParent original i).parent.edge.point 1 = (ChartParent original
      j).parent.edge.point 0)
    (roots : Gaussian.Equivalence.NamedEquivalent ((ChartParent original i).parent.edge.rootName 1
      (by decide))
      ((ChartParent original j).parent.edge.rootName 0 (ChartParent original
        j).parent.edge.baseInside)) :
        EndpointJoin request i j
        :=
  ReciprocalDiskArcOwners.sourceEndpointJoin
    (ChartRequest.lastPoint (request.plans.get
    i).request) (ChartRequest.firstPoint
    (request.plans.get j).request)
    (ChartRequest.lastParameter_eq
      (request.plans.get i).request)
    (ChartRequest.firstParameter_eq
      (request.plans.get j).request) same roots

/-- The named primitive equivalence at two exact retained parent endpoints for the supplied original cap sample. -/
@[expose] def EndpointPrimitiveLink (i j : Fin original.plans.length) {numerator : Differential
  genus}
    {index : Nat} {box : Rational.Box} (sample : Primitives.Sample cap numerator index box) :=
  Gaussian.Equivalence.NamedEquivalent
    ((ChartRequest.lastPoint (request.plans.get
      i).request).coordinates.chartPrimitive sample).name
    ((ChartRequest.firstPoint (request.plans.get
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
    (ChartRequest.lastPoint (request.plans.get
      i).request).coordinates.coordinate.prepared.denominator.name

/-- The original coordinate approximation name retained at the parent's actual initial chart owner. -/
@[expose] def FirstApproximation (i : Fin original.plans.length) :=
  Sampling.approximation
    (ChartRequest.firstPoint (request.plans.get
      i).request).coordinates.coordinate.prepared.denominator.name

set_option genInjectivity false in
/-- A cross-parent comparison is selected before either retained endpoint is read. Its coefficient cache is the one
already prepared for the left parent. -/
structure JunctionRequest (i j : Fin original.plans.length) (joined :
  EndpointJoin request i j)
    (tolerance : Coordinate) (floor : Nat) where
  /-- The cached paired primitive sensitivity scale from the left parent's original coefficient bounds. -/ scale :
    Coordinate
  /-- The sensitivity scale is exactly 512 times the squared maximum of the two retained differential coefficient
    bounds. -/ scale_eq : scale = 512 * (max ((request.plans.get i).preparation.bounds.coefficientUpper differential)
    ((request.plans.get i).preparation.bounds.coefficientUpper other)) ^ 2
  /-- The cached original paired sensitivity scale is nonnegative. -/ nonnegative : 0 ≤ scale
  /-- The cached coordinate comparison budget for the actual endpoint pair. -/ budget : Coordinate
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
    (tolerance : Coordinate) (positive : 0 < tolerance) (floor : Nat) :
    JunctionRequest request i j
      joined tolerance floor :=
  let bounds := (request.plans.get i).preparation.bounds
  let scale : Coordinate := 512 * (max (bounds.coefficientUpper differential) (bounds.coefficientUpper other)) ^ 2
  have nonnegative : 0 ≤ scale := Arithmetic.mul_nonneg_direct (by decide +kernel)
    (Arithmetic.sq_nonneg_direct _)
  let budget := tolerance / (scale + 1)
  let comparison := joined.coordinate.compare floor floor budget
    (Field.div_pos_direct positive (Arithmetic.add_pos_of_nonneg_of_pos_direct nonnegative
      (by decide)))
  ⟨scale, rfl, nonnegative, budget, rfl, comparison, max comparison.leftIndex comparison.rightIndex, rfl⟩

variable {request}

/-- The actual retained reading stage at the parent's final common-chart vertex. -/
@[expose] def Evaluation.lastStage (evaluated : request.Evaluation) (i : Fin original.plans.length) : Nat :=
  ((evaluated.entries.get i).entries.get (ChartParent original
    i).common.lastIndex).evaluated.chart.retained.area.refined.stage

/-- The actual retained reading stage at the parent's first common-chart vertex. -/
@[expose] def Evaluation.firstStage (evaluated : request.Evaluation) (i : Fin original.plans.length) : Nat :=
  ((evaluated.entries.get i).entries.get (ChartParent original
    i).common.firstIndex).evaluated.chart.retained.area.refined.stage

/-- The actual acquired coordinate at the parent's final retained common-chart vertex. -/
@[expose] def Evaluation.lastCoordinate (evaluated : request.Evaluation) (i : Fin original.plans.length) : Gaussian :=
  (Evaluation.chartCoordinate (evaluated.entries.get i)) (ChartParent original i).common.lastIndex
    (Fin.last ((request.plans.get i).request.plans.get (ChartParent original
      i).common.lastIndex).geometry.tail.length)

/-- The actual acquired coordinate at the parent's first retained common-chart vertex. -/
@[expose] def Evaluation.firstCoordinate (evaluated : request.Evaluation) (i : Fin original.plans.length) : Gaussian :=
  (Evaluation.chartCoordinate (evaluated.entries.get i)) (ChartParent original i).common.firstIndex 0

/-- The acquired final coordinate is the original retained endpoint approximation sampled at its actual reading stage.
-/
theorem Evaluation.lastCoordinate_eq (evaluated : request.Evaluation) (i : Fin original.plans.length) :
    Evaluation.lastCoordinate
      evaluated i =
      (LastApproximation request
      i).sample
      (Evaluation.lastStage
      evaluated i) :=
  (((evaluated.entries.get i).entries.get (ChartParent original
    i).common.lastIndex).evaluated.chart.retained.area.evaluated.readings.get
    (Fin.last ((request.plans.get i).request.plans.get (ChartParent original
      i).common.lastIndex).geometry.tail.length)).first.coordinate_eq

/-- The acquired first coordinate is the original retained endpoint approximation sampled at its actual reading stage.
-/
theorem Evaluation.firstCoordinate_eq (evaluated : request.Evaluation) (i : Fin original.plans.length) :
    Evaluation.firstCoordinate
      evaluated i =
      (FirstApproximation
      request i).sample
      (Evaluation.firstStage
      evaluated i) :=
  (((evaluated.entries.get i).entries.get (ChartParent original
    i).common.firstIndex).evaluated.chart.retained.area.evaluated.readings.get 0).first.coordinate_eq

/-- The paired primitive values read from the two exact cap samples shared by the whole retained parent bank. -/
@[expose] def Evaluation.radialValues (evaluated : request.Evaluation) (point : Gaussian) :
  PrimitivePoint :=
  ⟨evaluated.firstCap.primitive.value.eval point, evaluated.otherCap.primitive.value.eval point⟩

/-- The actual cross-parent radial area difference minus the retained endpoint joining-edge area. -/
@[expose] def Evaluation.junctionError (evaluated : request.Evaluation) (i j : Fin original.plans.length) : Gaussian :=
  Bilinear.radialArea
    (Evaluation.radialValues
    evaluated) evaluated.radialDepth
    (Evaluation.firstCoordinate
    evaluated j) -
    Bilinear.radialArea
      (Evaluation.radialValues
      evaluated) evaluated.radialDepth
      (Evaluation.lastCoordinate
      evaluated i) -
    edgeArea
      (Evaluation.radialValues
      evaluated
      (Evaluation.lastCoordinate
      evaluated i))
      (Evaluation.radialValues
        evaluated
        (Evaluation.firstCoordinate
        evaluated j))

/-- The paid original junction comparison bounds the acquired first-to-last coordinate gap at their retained reading
stages. -/
private theorem JunctionRequest.coordinate_accurate {i j : Fin original.plans.length} {joined :
  EndpointJoin request i j}
    {tolerance : Coordinate} {floor : Nat} (junction :
      JunctionRequest request i
      j joined tolerance floor)
    (evaluated : request.Evaluation) (later : junction.index ≤ evaluated.externalFloor) :
    normSq
      (Evaluation.firstCoordinate
      evaluated j -
      Evaluation.lastCoordinate
      evaluated i) < junction.budget := by
  have firstLater : junction.index ≤
    Evaluation.lastStage
    evaluated i := later.trans
    ((evaluated.readingFloors i).symm.trans_le ((evaluated.entries.get i).readingsLater (ChartParent
      original i).common.lastIndex))
  have lastLater : junction.index ≤
    Evaluation.firstStage
    evaluated j := later.trans
    ((evaluated.readingFloors j).symm.trans_le ((evaluated.entries.get j).readingsLater (ChartParent
      original j).common.firstIndex))
  rw [show
    Evaluation.firstCoordinate
    evaluated j -
    Evaluation.lastCoordinate
    evaluated i =
    -(Evaluation.lastCoordinate
      evaluated i -
      Evaluation.firstCoordinate
      evaluated j) by ring1, normSq_neg,
    Evaluation.lastCoordinate_eq
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
    {tolerance : Coordinate} {floor : Nat} (junction :
      JunctionRequest request i
      j joined tolerance floor)
    (evaluated : request.Evaluation) (later : junction.index ≤ evaluated.externalFloor)
    (branch : HyperellipticReciprocal.originOrder curve = 1) :
    normSq
      (Evaluation.junctionError
      evaluated i j) < tolerance := by
  have close := junction.coordinate_accurate evaluated later
  have firstInside := (Evaluation.chart_square_inside (evaluated.entries.get i)) branch (ChartParent
    original i).common.lastIndex
    (Fin.last ((request.plans.get i).request.plans.get (ChartParent original
      i).common.lastIndex).geometry.tail.length)
  have lastInside := (Evaluation.chart_square_inside (evaluated.entries.get j)) branch (ChartParent
    original j).common.firstIndex 0
  have bound := (request.plans.get i).preparation.bounds.paired_radial_connector_bound
    evaluated.firstCap evaluated.otherCap branch firstInside lastInside evaluated.radialDepth
  change normSq
    (Evaluation.junctionError
    evaluated i j) ≤ _ at bound
  rw [← junction.scale_eq] at bound
  have positive : 0 < junction.scale + 1 := Arithmetic.add_pos_of_nonneg_of_pos_direct
    junction.nonnegative (by decide)
  apply bound.trans_lt
  calc
    _ ≤ (junction.scale + 1) * normSq
      (Evaluation.firstCoordinate
      evaluated j -
      Evaluation.lastCoordinate
      evaluated i) :=
      Arithmetic.mul_le_mul_of_nonneg_right_direct (le_add_of_nonneg_right (by decide))
        (normSq_nonneg _)
    _ < (junction.scale + 1) * junction.budget := Arithmetic.mul_lt_mul_of_pos_left_direct positive close
    _ = tolerance := by
      rw [junction.budget_eq, Fraction.Field.mul_comm]
      exact Fraction.Field.div_mul_cancel_of_ne _ _ positive.ne'

/-- The same preselected coordinate comparison also pays the actual paired increment inserted between the two retained
parent traces. -/
private theorem JunctionRequest.radial_increment_accurate {i j : Fin original.plans.length} {joined :
  EndpointJoin request i j}
    {tolerance : Coordinate} {floor : Nat} (junction :
      JunctionRequest request i
      j joined tolerance floor)
    (evaluated : request.Evaluation) (later : junction.index ≤ evaluated.externalFloor)
    (branch : HyperellipticReciprocal.originOrder curve = 1) :
    PrimitivePoint.Bounded
      ((Evaluation.radialValues
      evaluated
      (Evaluation.firstCoordinate
      evaluated j)).sub
      (Evaluation.radialValues
        evaluated
        (Evaluation.lastCoordinate
        evaluated i))) tolerance := by
  let bounds := (request.plans.get i).preparation.bounds
  let coefficient := max (bounds.coefficientUpper differential) (bounds.coefficientUpper other)
  have scale : 2 * coefficient ≤ junction.scale + 1 := by
    have square := Arithmetic.sq_nonneg_direct (coefficient - 1)
    have first : 2 * coefficient ≤ coefficient^2 + 1 := by
      have translated := Arithmetic.add_le_add_direct square (le_refl (2 * coefficient))
      exact (by ring1 : 2 * coefficient = 0 + 2 * coefficient).trans_le
        (translated.trans_eq (by ring1))
    have larger := Arithmetic.mul_le_mul_of_nonneg_right_direct (by
        decide +kernel : (1 : Coordinate) ≤ 512)
      (Arithmetic.sq_nonneg_direct coefficient)
    rw [Fraction.Field.one_mul] at larger
    have result := first.trans (Arithmetic.add_le_add_direct larger (le_refl (1 :
      Coordinate)))
    exact result.trans_eq (congrArg (fun value : Coordinate => value + 1) junction.scale_eq.symm)
  have firstInside := (Evaluation.chart_square_inside (evaluated.entries.get i)) branch (ChartParent
    original i).common.lastIndex
    (Fin.last ((request.plans.get i).request.plans.get (ChartParent original
      i).common.lastIndex).geometry.tail.length)
  have lastInside := (Evaluation.chart_square_inside (evaluated.entries.get j)) branch (ChartParent
    original j).common.firstIndex 0
  have close := junction.coordinate_accurate evaluated later
  have positive : 0 < junction.scale + 1 := Arithmetic.add_pos_of_nonneg_of_pos_direct
    junction.nonnegative (by decide)
  have paid : (junction.scale + 1) * normSq
    (Evaluation.firstCoordinate
    evaluated j -
    Evaluation.lastCoordinate
    evaluated i) < tolerance := by
    have estimate := Arithmetic.mul_lt_mul_of_pos_left_direct positive close
    apply estimate.trans_eq
    rw [junction.budget_eq, Fraction.Field.mul_comm]
    exact Fraction.Field.div_mul_cancel_of_ne _ _ positive.ne'
  have scalar {d : Differential genus} (sample : Primitives.Sample cap d request.index collar.box)
      (coefficientLe : bounds.coefficientUpper d ≤ coefficient) :
      normSq (sample.primitive.value.eval
        (Evaluation.firstCoordinate
        evaluated j) -
        sample.primitive.value.eval
          (Evaluation.lastCoordinate
          evaluated i)) ≤ tolerance := by
    have bound := bounds.chord_increment sample branch firstInside lastInside
      (left := 0) (right := 1) (by decide) (by decide)
    change normSq (sample.primitive.value.eval
      (chord
      (Evaluation.lastCoordinate
        evaluated i)
        (Evaluation.firstCoordinate
        evaluated j) 1) -
      sample.primitive.value.eval (chord

          (Evaluation.lastCoordinate
          evaluated i)
          (Evaluation.firstCoordinate
          evaluated j) 0)) ≤
      2 * bounds.coefficientUpper d * normSq
        (Evaluation.firstCoordinate
        evaluated j -
        Evaluation.lastCoordinate
        evaluated i) * (1 - 0)^2 at bound
    have first : chord
      (Evaluation.lastCoordinate
      evaluated i)
      (Evaluation.firstCoordinate
      evaluated j) 0 =
      Evaluation.lastCoordinate
      evaluated i := by
      unfold chord Data.Gaussian.Scale.scale
      apply Data.Gaussian.Basic.ext <;>
        simp only [Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im, -eq_self, -iff_self] <;> ring1
    have last : chord
      (Evaluation.lastCoordinate
      evaluated i)
      (Evaluation.firstCoordinate
      evaluated j) 1 =
      Evaluation.firstCoordinate
      evaluated j := by
      unfold chord Data.Gaussian.Scale.scale
      apply Data.Gaussian.Basic.ext <;>
        simp only [Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im, -eq_self, -iff_self] <;> ring1
    rw [first, last, show ((1 : Coordinate) - 0)^2 = 1 by decide, mul_one] at bound
    exact bound.trans ((Arithmetic.mul_le_mul_of_nonneg_right_direct
      ((Arithmetic.mul_le_mul_of_nonneg_left_direct coefficientLe (by decide)).trans scale)
      (normSq_nonneg _)).trans paid.le)
  constructor
  · rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical]
    exact scalar evaluated.firstCap (Basic.le_max_left _ _)
  · rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical]
    exact scalar evaluated.otherCap (Basic.le_max_right _ _)

/-- The actual paired primitive increment between the retained last chart point and the next first chart point. -/
@[expose] def Evaluation.junctionIncrement (evaluated : request.Evaluation) (i j : Fin original.plans.length) :
    PrimitivePoint :=
  ((Evaluation.firstChartPoint (evaluated.entries.get j)) (ChartParent original
    j).common.firstIndex).sub
    ((Evaluation.lastChartPoint (evaluated.entries.get i)) (ChartParent original i).common.lastIndex)

/-- The actual junction increment reads the same two exact shared cap samples at its retained endpoint coordinates. -/
theorem Evaluation.junctionIncrement_eq (evaluated : request.Evaluation) (i j : Fin original.plans.length)
    (branch : HyperellipticReciprocal.originOrder curve = 1) :
    Evaluation.junctionIncrement
      evaluated i j =
      (Evaluation.radialValues
      evaluated
      (Evaluation.firstCoordinate
      evaluated j)).sub
      (Evaluation.radialValues
        evaluated
        (Evaluation.lastCoordinate
        evaluated i)) := by
  have first : (Evaluation.firstChartPoint (evaluated.entries.get j)) (ChartParent original
    j).common.firstIndex =
      Evaluation.radialValues
        evaluated
        (Evaluation.firstCoordinate
        evaluated j) := by
    unfold Evaluation.firstChartPoint
    rw [Evaluation.chartPoint_readback (evaluated.entries.get j) branch]
    rw [(evaluated.shared j).1, (evaluated.shared j).2]
    rfl
  have last : (Evaluation.lastChartPoint (evaluated.entries.get i)) (ChartParent original
    i).common.lastIndex =
      Evaluation.radialValues
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
    {tolerance : Coordinate} {floor : Nat} (junction :
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
