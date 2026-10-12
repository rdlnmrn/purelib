module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Energy.AffineTriangle
import Purelib.Polynomial.Dense.Gaussian.Reciprocal.Bounds

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcCoarsening
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CoordinatePolynomial
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CoordinateVariation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.Dyadic.DyadicAreaRefinement
import Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon
import Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.ReciprocalDiskCoordinateOrientation
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.AngularRequest
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedRootGeometry
import Init.Data.Nat.Basic
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.IncrementArea
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring

public section

open Purelib
open Purelib.Approximation.Rational
open Purelib.Approximation.Rational.Geometric
open Purelib.Approximation.Rational.Geometric.Basic
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.AngularRequest
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcCoarsening
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CoordinatePolynomial
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CoordinateVariation
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexArea
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
open Purelib.Data.Rat
open Purelib.Integration.Energy
open Purelib.Integration.Path.Dyadic
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Riemann.Normalization

/-!
# Requested full arc-area comparison with the global cap-chart polygon

Choose the finite mesh and every vertex tolerance before the common
polynomial stage. Later evaluate each vertex once and pay both the original
fine-path area and the complete chart polygon. The returned original path,
coordinates and endpoint data remain available for the gluing proof.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree (Mesh ChartMesh)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths (Segment)

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {edge : Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell data edge}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {owners :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.OwnedEndpoints regular cell}
  {comparison : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular cell} {target :
    Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

set_option genInjectivity false in
/-- A finite request for the full retained arc-area and cap-chart polygon comparison.

The cached spatial depth and vertex tolerance pay primitive area, coordinate clearance, angular orientation and both
scalar and basis energy errors before any shared sample is selected. -/
structure AreaRequest (comparison : ArcSamples.Data regular cell)
    (owners : ParentOwners.OwnedEndpoints regular cell) (target : InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The cached uniform reference-coordinate polynomial bounds. -/ coordinateBounds :
    CoordinatePolynomial.CoordinateBounds comparison
  /-- The retained positive target for every actual root-coordinate step. -/ coordinateTarget :
    InverseRootPolynomial.Coordinate
  /-- The retained coordinate-step target is positive. -/ coordinatePositive : 0 < coordinateTarget
  /-- The retained coordinate-step target is at most one. -/ coordinateSmall : coordinateTarget ≤ 1
  /-- The retained coordinate target fits one sixty-fourth of the original boundary clearance. -/ coordinateClearance :
    coordinateTarget ≤ collar.coordinateBound / 64
  /-- The cached spatial floor paying the reference-coordinate variation. -/ coordinateFloor : Nat
  /-- The coordinate floor is the exact finite quarter-radius search result. -/ coordinateFloor_eq : coordinateFloor =
    Search.firstQuarterBelow (2 * coordinateBounds.slope) floor (coordinateTarget / 4)
  /-- The cached uniform padded inverse bounds for the original regular disk. -/ energyBounds :
    ReciprocalPaddedInverse.UniformBounds regular.padded
  /-- The cached scalar primitive-energy variation scale. -/ energyScale : InverseRootPolynomial.Coordinate
  /-- The scalar energy scale is exactly the retained coefficient and coordinate-slope expression. -/ energyScale_eq :
    energyScale = 64 * (energyBounds.coefficientUpper differential) ^ 2 * (coordinateBounds.slope + 4) ^ 2
  /-- The cached simultaneous differential-basis bounds on the same padded inverse data. -/ basisBounds :
    ReciprocalPaddedBasisBounds.BasisBounds energyBounds
  /-- The cached simultaneous basis-energy variation scale. -/ basisScale : InverseRootPolynomial.Coordinate
  /-- The basis energy scale is exactly the retained basis coefficient and coordinate-slope expression. -/ basisScale_eq
    : basisScale = 64 * basisBounds.coefficient^2 * (coordinateBounds.slope + 4)^2
  /-- The cached spatial floor paying both scalar and basis energy targets. -/ energyFloor : Nat
  /-- The energy floor is exactly the maximum of both retained quarter-radius searches. -/ energyFloor_eq : energyFloor
    = max (Search.firstQuarterBelow energyScale coordinateFloor target)
    (Search.firstQuarterBelow basisScale coordinateFloor target)
  /-- The cached coarse arc request at the retained energy floor and quarter-area target. -/ spatial :
    ArcCoarsening.SpatialRequest comparison (target / 4) energyFloor
  /-- The retained spatial depth pays the scalar primitive-energy target. -/ energy_paid : Geometric.Basic.quarterRadius
    energyScale spatial.depth < target
  /-- The retained spatial depth pays the simultaneous basis-energy target. -/ basis_paid :
    Geometric.Basic.quarterRadius basisScale spatial.depth < target
  /-- The cached number of actual dyadic chart segments. -/ count : Nat
  /-- The retained segment count is exactly two to the spatial depth. -/ count_eq : count = 2 ^ spatial.depth
  /-- The cached angular margin request on the actual original cell interval. -/ angular : AngularRequest
    comparison spatial.depth edge.left.parameter edge.right.parameter
  /-- The cached finite chart-polygon area cost. -/ cost : InverseRootPolynomial.Coordinate
  /-- The area cost uses the actual fourth power of the retained segment count and source slope. -/ cost_eq : cost = 512
    * (count : InverseRootPolynomial.Coordinate) ^ 4 * (spatial.bounds.slope + 16)
  /-- The cached common root-reading tolerance. -/ tolerance : InverseRootPolynomial.Coordinate
  /-- The tolerance is exactly the minimum paying area, coordinate, angular, padded-disk and mesh-width constraints. -/
    tolerance_eq : tolerance = min 1 (min ((target / 4) / (cost + 1)) (min ((coordinateTarget / 4) / 8) (min
    (angular.margin ^ 2 / 16)
    (min regular.padded.squareTolerance (Geometric.Basic.quarterRadius 1 spatial.depth)))))
  /-- The retained common reading tolerance is positive. -/ positive : 0 < tolerance
  /-- The retained reading tolerance is at most one. -/ small : tolerance ≤ 1
  /-- The finite chart area cost times tolerance is strictly below the quarter-area target. -/ paid : cost * tolerance <
    target / 4
  /-- The reading tolerance pays the retained squared angular margin. -/ orientation_paid : 16 * tolerance ≤
    angular.margin ^ 2
  /-- The reading tolerance fits the original padded-disk square tolerance. -/ padded_paid : tolerance ≤
    regular.padded.squareTolerance
  /-- The reading tolerance fits the retained dyadic mesh-width factor. -/ mesh_paid : tolerance ≤
    Geometric.Basic.quarterRadius 1 spatial.depth
  /-- The cached upper bound for every actual chart-coordinate step. -/ coordinateStep :
    InverseRootPolynomial.Coordinate
  /-- The step bound combines the retained reference variation with both endpoint reading errors. -/ coordinateStep_eq :
    coordinateStep = 2 * (Geometric.Basic.quarterRadius coordinateBounds.slope spatial.depth + 4 * tolerance)
  /-- The cached coordinate-step bound is below its retained target. -/ coordinateStep_paid : coordinateStep <
    coordinateTarget
  /-- The cached dyadic chart mesh retaining the actual original endpoint owners. -/ mesh : VertexTree.Mesh regular
    owners.model spatial.depth tolerance floor
  /-- The retained first chart endpoint has exactly the original first owner. -/ first_owner : mesh.first.point =
    owners.first
  /-- The retained last chart endpoint has exactly the original last owner. -/ last_owner : mesh.last.point =
    owners.last

constructive_injectivity AreaRequest

namespace AreaRequest

/-- Both the primitive-area target and the intrinsic coordinate-step target are paid before selecting a source
polynomial or reading any root. -/
@[expose] def buildWithCoordinateTarget (comparison : ArcSamples.Data regular cell)
    (owners : ParentOwners.OwnedEndpoints regular cell)
    (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) (requestedCoordinateTarget :
      InverseRootPolynomial.Coordinate) (requestedCoordinatePositive : 0 < requestedCoordinateTarget)
    (floor : Nat) : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest.AreaRequest comparison owners target
      floor := by
  let coordinateTarget := min requestedCoordinateTarget (min 1 (collar.coordinateBound / 64))
  have coordinatePositive : 0 < coordinateTarget := Fraction.Order.Basic.lt_min requestedCoordinatePositive
    (Fraction.Order.Basic.lt_min (by decide) (Fraction.Order.Field.div_pos_direct collar.coordinateBound_positive (by
      decide +kernel)))
  have coordinateSmall : coordinateTarget ≤ 1 := (Fraction.Order.Basic.min_le_right _ _).trans
    (Fraction.Order.Basic.min_le_left _ _)
  have coordinateClearance : coordinateTarget ≤ collar.coordinateBound / 64 := (Fraction.Order.Basic.min_le_right _
    _).trans (Fraction.Order.Basic.min_le_right _ _)
  have quarterPositive := Fraction.Order.Field.div_pos_direct positive (by
      decide : (0 : InverseRootPolynomial.Coordinate) < 4)
  have coordinateQuarter := Fraction.Order.Field.div_pos_direct coordinatePositive (by
      decide : (0 : InverseRootPolynomial.Coordinate) < 4)
  let coordinateBounds := CoordinateBounds.build comparison
  have slopeNonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct (by
      decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2) coordinateBounds.slope_nonnegative
  let coordinateFloor := Search.firstQuarterBelow (2 * coordinateBounds.slope) floor (coordinateTarget / 4)
  let energyBounds := UniformBounds.build regular.padded
  let energyScale := 64 * (energyBounds.coefficientUpper differential) ^ 2 * (coordinateBounds.slope + 4) ^ 2
  have energyNonnegative : 0 ≤ energyScale := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : InverseRootPolynomial.Coordinate) ≤ 64)
      (Fraction.Order.Arithmetic.sq_nonneg_direct _)) (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  let basisBounds := BasisBounds.build energyBounds
  let basisScale := 64 * basisBounds.coefficient^2 * (coordinateBounds.slope + 4)^2
  have basisNonnegative : 0 ≤ basisScale := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) (Fraction.Order.Arithmetic.sq_nonneg_direct _))
    (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  let energyFloor := max (Search.firstQuarterBelow energyScale coordinateFloor target)
    (Search.firstQuarterBelow basisScale coordinateFloor target)
  let spatial := SpatialRequest.build comparison (target / 4) quarterPositive energyFloor
  have energyPaid : Geometric.Basic.quarterRadius energyScale spatial.depth < target :=
    (quarterRadius_antitone energyNonnegative ((Data.Nat.Order.le_max_left _ _).trans
      spatial.floor_le)).trans_lt
      (Search.firstQuarterBelow_accurate _ energyNonnegative _ _ positive)
  have basisPaid : Geometric.Basic.quarterRadius basisScale spatial.depth < target :=
    (quarterRadius_antitone basisNonnegative ((Data.Nat.Order.le_max_right _ _).trans
      spatial.floor_le)).trans_lt
      (Search.firstQuarterBelow_accurate _ basisNonnegative _ _ positive)
  have coordinateLater : coordinateFloor ≤ spatial.depth :=
    (Search.firstQuarterBelow_ge energyScale coordinateFloor target).trans
      ((Data.Nat.Order.le_max_left _ _).trans spatial.floor_le)
  let count := 2 ^ spatial.depth
  let angular := AngularRequest.build comparison spatial.depth edge.left.parameter edge.right.parameter cell.ordered
  let cost := 512 * (count : InverseRootPolynomial.Coordinate) ^ 4 * (spatial.bounds.slope + 16)
  have costNonnegative : 0 ≤ cost := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (show (0 : Fraction.Rational) ≤ 512 from by decide +kernel)
      (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count)) 4))
    (add_nonneg spatial.bounds.slope_nonnegative (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 16))
  let tolerance := min 1 (min ((target / 4) / (cost + 1)) (min ((coordinateTarget / 4) / 8) (min (angular.margin ^ 2 /
    16)
    (min regular.padded.squareTolerance (Geometric.Basic.quarterRadius 1 spatial.depth)))))
  have tolerancePositive : 0 < tolerance := Fraction.Order.Basic.lt_min (by decide) (Fraction.Order.Basic.lt_min
    (Fraction.Order.Field.div_pos_direct quarterPositive (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
      costNonnegative (by decide)))
    (Fraction.Order.Basic.lt_min (Fraction.Order.Field.div_pos_direct coordinateQuarter (by decide))
      (Fraction.Order.Basic.lt_min (Fraction.Order.Field.div_pos_direct (Fraction.Order.Arithmetic.pow_pos_direct
        angular.positive 2) (by decide))
        (Fraction.Order.Basic.lt_min regular.padded.squareTolerance_positive (Geometric.Basic.quarterRadius_pos (by
          decide) spatial.depth)))))
  have areaLe : tolerance ≤ min 1 ((target / 4) / (cost + 1)) :=
    le_min (Fraction.Order.Basic.min_le_left _ _) ((Fraction.Order.Basic.min_le_right _ _).trans
      (Fraction.Order.Basic.min_le_left _ _))
  have areaPaid : cost * tolerance < target / 4 :=
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct areaLe costNonnegative).trans_lt
      (Purelib.Data.Rat.Fraction.Order.Field.mul_min_one_div_lt costNonnegative quarterPositive)
  have readingLe : tolerance ≤ (coordinateTarget / 4) / 8 :=
    (Fraction.Order.Basic.min_le_right _ _).trans ((Fraction.Order.Basic.min_le_right _ _).trans
      (Fraction.Order.Basic.min_le_left _ _))
  have orientationLe : tolerance ≤ angular.margin ^ 2 / 16 :=
    (Fraction.Order.Basic.min_le_right _ _).trans ((Fraction.Order.Basic.min_le_right _ _).trans
      ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _)))
  have paddedLe : tolerance ≤ regular.padded.squareTolerance :=
    (Fraction.Order.Basic.min_le_right _ _).trans ((Fraction.Order.Basic.min_le_right _ _).trans
      ((Fraction.Order.Basic.min_le_right _ _).trans ((Fraction.Order.Basic.min_le_right _ _).trans
      (Fraction.Order.Basic.min_le_left _ _))))
  have meshLe : tolerance ≤ Geometric.Basic.quarterRadius 1 spatial.depth :=
    (Fraction.Order.Basic.min_le_right _ _).trans ((Fraction.Order.Basic.min_le_right _ _).trans
      ((Fraction.Order.Basic.min_le_right _ _).trans ((Fraction.Order.Basic.min_le_right _ _).trans
      (Fraction.Order.Basic.min_le_right _ _))))
  have orientationPaid : 16 * tolerance ≤ angular.margin ^ 2 :=
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct orientationLe (by decide)).trans_eq (by
      rw [Fraction.Field.mul_comm]
      exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))
  have readingPaid : 8 * tolerance ≤ coordinateTarget / 4 :=
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct readingLe (by decide)).trans_eq (by
      rw [Fraction.Field.mul_comm]
      exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))
  have spatialPaid : 2 * Geometric.Basic.quarterRadius coordinateBounds.slope spatial.depth < coordinateTarget / 4 := by
    have estimate := (quarterRadius_antitone slopeNonnegative coordinateLater).trans_lt
      (Search.firstQuarterBelow_accurate _ slopeNonnegative floor _ coordinateQuarter)
    exact (show 2 * Geometric.Basic.quarterRadius coordinateBounds.slope spatial.depth =
      Geometric.Basic.quarterRadius (2 * coordinateBounds.slope) spatial.depth by
      simp only [Geometric.Basic.quarterRadius_eq_mul_pow, -eq_self, -iff_self]; ring1).trans_lt estimate
  have doubledQuarter : coordinateTarget / 4 + coordinateTarget / 4 < coordinateTarget := by
    have estimate := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct (by
        decide : (2 : InverseRootPolynomial.Coordinate) < 4) coordinateQuarter
    exact (show coordinateTarget / 4 + coordinateTarget / 4 = 2 * (coordinateTarget / 4) by ring1).trans_lt
      (estimate.trans_eq (by rw [Fraction.Field.mul_comm]; exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)))
  have stepPaid : 2 * (Geometric.Basic.quarterRadius coordinateBounds.slope spatial.depth + 4 * tolerance) <
    coordinateTarget := by
    rw [show 2 * (Geometric.Basic.quarterRadius coordinateBounds.slope spatial.depth + 4 * tolerance) =
      2 * Geometric.Basic.quarterRadius coordinateBounds.slope spatial.depth + 8 * tolerance by ring1]
    exact ((Fraction.Order.Arithmetic.add_lt_add_right_direct spatialPaid _).trans_le
      (add_le_add le_rfl readingPaid)).trans doubledQuarter
  let mesh := Mesh.build owners spatial.depth tolerance tolerancePositive floor
  exact ⟨coordinateBounds, coordinateTarget, coordinatePositive, coordinateSmall, coordinateClearance, coordinateFloor,
    rfl, energyBounds, energyScale, rfl, basisBounds, basisScale, rfl, energyFloor, rfl, spatial, energyPaid, basisPaid,
    count, rfl, angular, cost, rfl,
    tolerance, rfl, tolerancePositive, Fraction.Order.Basic.min_le_left _ _, areaPaid, orientationPaid, paddedLe,
      meshLe,
    2 * (Geometric.Basic.quarterRadius coordinateBounds.slope spatial.depth + 4 * tolerance), rfl, stepPaid, mesh, rfl,
      rfl⟩

/-- Default chart acquisition also controls its intrinsic coordinate steps at a scale derived from the actual
outer-boundary clearance. -/
@[expose] def build (comparison : ArcSamples.Data regular cell)
    (owners : ParentOwners.OwnedEndpoints regular cell)
    (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) (floor : Nat) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest.AreaRequest comparison owners target floor :=
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest.AreaRequest.buildWithCoordinateTarget comparison owners
    target positive (min 1 (collar.coordinateBound / 64))
    (Fraction.Order.Basic.lt_min (by decide) (Fraction.Order.Field.div_pos_direct collar.coordinateBound_positive (by
      decide +kernel))) floor

variable {index depth stage : Nat} {box : Purelib.Geometry.Rational.Box}
  {capSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {source : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive data index}
  {request : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest.AreaRequest comparison owners target
    floor} {minimum : Nat}

set_option genInjectivity false in
/-- Cached actual chart vertices and coordinate polynomial with full original-path comparison certificates. -/
structure Evaluation (charts : VertexTree.ChartMesh request.mesh capSample minimum)
    (original : ParentCells.ComparedCell comparison source capSample depth) (stage : Nat) where
  /-- The evaluated retained vertex tree and its complete chart polygon. -/ vertices : ChartMesh.Evaluation charts
    original.sample stage
  /-- The cached reference-coordinate polynomial of the exact original arc sample. -/ coordinate :
    CoordinatePolynomial original.sample
  /-- The retained first chart endpoint has exactly the original first owner. -/ first_owner :
    vertices.first.prepared.point = owners.first
  /-- The retained last chart endpoint has exactly the original last owner. -/ last_owner : vertices.last.prepared.point
    = owners.last
  /-- The original fine path depth is at least the retained requested spatial depth. -/ fine_later :
    request.spatial.depth ≤ depth
  /-- The cached coarse source polygon has exactly the original fine path's total. -/ source_total :
    vertices.path.source.total = original.capSummary.total
  /-- The actual source and chart totals satisfy the paid endpoint-reading error. -/ total_error :
    Data.Gaussian.Norm.Basic.normSq (original.capSummary.total - vertices.path.chart.total) < 16 *
    request.tolerance
  /-- The original fine area and cached coarse source area satisfy the quarter-area target. -/ fine_error :
    Data.Gaussian.Norm.Basic.normSq (original.capSummary.area - vertices.path.source.area) < target / 4
  /-- The cached coarse source and actual chart polygon areas satisfy the quarter-area target. -/ chart_error :
    Data.Gaussian.Norm.Basic.normSq (vertices.path.source.area - vertices.path.chart.area) < target / 4
  /-- The original fine area and complete chart polygon area satisfy the full target. -/ area_error :
    Data.Gaussian.Norm.Basic.normSq (original.capSummary.area - vertices.path.chart.area) < target

constructive_injectivity Evaluation

/-- The fourth power of an ordered retained unit-interval cell width is at most one. -/
theorem width_fourth (ordered : edge.left.parameter ≤ edge.right.parameter) :
    (edge.right.parameter - edge.left.parameter) ^ 4 ≤ (1 : InverseRootPolynomial.Coordinate) := by
  have widthLe : edge.right.parameter - edge.left.parameter ≤ 1 := by
    simpa only [(show (1 : InverseRootPolynomial.Coordinate) - 0 = 1 from by decide), -eq_self, -iff_self] using
      Fraction.Order.Arithmetic.sub_le_sub_direct edge.right.inside.2 edge.left.inside.1
  simpa only [one_pow, -eq_self, -iff_self] using Fraction.Order.Arithmetic.pow_le_pow_direct
    (Fraction.Order.Arithmetic.sub_nonneg_direct ordered) widthLe 4

/-- The original fine path is supplied, not rebuilt. Its coarse summary is already cached by the evaluated vertex tree
and is reused in both bounds. -/
@[expose] def evaluate (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest.AreaRequest comparison
  owners target floor)
    (charts : VertexTree.ChartMesh request.mesh capSample minimum)
    (original : ParentCells.ComparedCell comparison source capSample depth)
    (modelLater : request.mesh.index ≤ index) (fineLater : request.spatial.depth ≤ depth)
    (stage : Nat) (readingLater : charts.stage ≤ stage) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest.AreaRequest.Evaluation charts original stage := by
  let vertices := ChartMesh.evaluate charts original.sample modelLater stage readingLater
  have sourceTotal : vertices.path.source.total = original.capSummary.total := by
    rw [vertices.path.source.total_eq, vertices.path.source_dyadic, DyadicPrimitivePaths.dyadicIncrements_sum,
      ArcArea.Sample.capValue_left original.sample, Data.Gaussian.Basic.sub_zero,
      ArcArea.Sample.capValue_right original.sample, original.cap_total]
  have totalError : Data.Gaussian.Norm.Basic.normSq (original.capSummary.total - vertices.path.chart.total) <
    16 * request.tolerance := by
    rw [original.cap_total, original.sample.increment_eq, original.sample.firstValue_eq, original.sample.lastValue_eq,
      ← vertices.first.source_eq, ← vertices.last.source_eq, vertices.path.chart_total]
    rw [show vertices.last.sourceValue - vertices.first.sourceValue -
      (vertices.last.chartValue - vertices.first.chartValue) =
      (vertices.last.sourceValue - vertices.last.chartValue) - (vertices.first.sourceValue - vertices.first.chartValue)
        by ring1]
    exact (Data.Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans_lt
      ((Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : InverseRootPolynomial.Coordinate) < 2)
        (Fraction.Order.Arithmetic.add_lt_add_direct vertices.last.accurate vertices.first.accurate)).trans_eq (by
          ring1))
  have sourceArea : vertices.path.source.area = DyadicBoundaryRibbon.dyadicArea (ArcArea.Sample.capValue
    original.sample)
      request.spatial.depth edge.left.parameter edge.right.parameter := by
    rw [vertices.path.source.area_eq, vertices.path.source_dyadic]
    exact DyadicPrimitivePaths.pathArea_dyadicIncrements _ _ _ _ (ArcArea.Sample.capValue_left original.sample)
  have estimate := DyadicAreaRefinement.dyadicArea_refinement_bound (ArcArea.Sample.capValue original.sample)
    request.spatial.bounds.slope_nonnegative
    (fun _ _ firstInside lastInside => request.spatial.bounds.increment_bound source original.sample firstInside
      lastInside)
    request.spatial.depth (depth - request.spatial.depth) ⟨le_rfl, cell.ordered.le⟩ ⟨cell.ordered.le, le_rfl⟩
      cell.ordered.le
  rw [Data.Nat.Subtraction.add_sub_of_le fineLater, ← request.spatial.bounds.areaScale_eq, ← request.spatial.error_eq,
    ← original.cap_area, ← sourceArea] at estimate
  have errorNonnegative : 0 ≤ request.spatial.error := by
    rw [request.spatial.error_eq]
    exact Geometric.Basic.quarterRadius_nonneg request.spatial.bounds.areaScale_nonnegative _
  have fineError : Data.Gaussian.Norm.Basic.normSq (original.capSummary.area - vertices.path.source.area) <
    target / 4 :=
    (estimate.trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (width_fourth cell.ordered.le)
      errorNonnegative).trans_eq
      (Fraction.Field.mul_one_direct _))).trans_lt request.spatial.accurate
  have chartError : Data.Gaussian.Norm.Basic.normSq (vertices.path.source.area - vertices.path.chart.area) <
    target / 4 := by
    have bounded := Path.area_error vertices.path request.spatial.bounds source request.positive request.small
    rw [← request.count_eq, ← request.cost_eq] at bounded
    exact bounded.trans_lt request.paid
  have paid : 2 * (target / 4 + target / 4) = target := by
    rw [show 2 * (target / 4 + target / 4) = target / 4 * 4 by ring1]
    exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
  have areaError := (Data.Gaussian.Norm.Bounds.normSq_sub_le_via original.capSummary.area vertices.path.source.area
    vertices.path.chart.area).trans_lt
    ((Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : InverseRootPolynomial.Coordinate) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_direct fineError chartError)).trans_eq paid)
  exact ⟨vertices, CoordinatePolynomial.build original.sample,
    (congrArg Prepared.point vertices.first_prepared).trans request.first_owner,
    (congrArg Prepared.point vertices.last_prepared).trans request.last_owner,
    fineLater, sourceTotal, totalError, fineError, chartError, areaError⟩

namespace Evaluation

/-- Every root-coordinate step of the actual sampled chart polygon obeys the bound computed before selecting its
polynomial and reading stages. -/
theorem coordinate_step_bound {charts : VertexTree.ChartMesh request.mesh capSample minimum}
    {original : ParentCells.ComparedCell comparison source capSample depth}
    (evaluated : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest.AreaRequest.Evaluation charts original
      stage) (branch : HyperellipticReciprocal.originOrder curve = 1)
    (segment : VertexPaths.Segment regular owners.model original.sample request.tolerance floor stage)
    (member : segment ∈ evaluated.vertices.path.segments) :
    Data.Gaussian.Norm.Basic.normSq (segment.last.root.coordinate - segment.first.root.coordinate) <
      request.coordinateStep := by
  have widthLe : edge.right.parameter - edge.left.parameter ≤ 1 := by
    simpa only [(show (1 : InverseRootPolynomial.Coordinate) - 0 = 1 from by decide), -eq_self, -iff_self] using
      Fraction.Order.Arithmetic.sub_le_sub_direct edge.right.inside.2 edge.left.inside.1
  have widthSquare : (edge.right.parameter - edge.left.parameter) ^ 2 ≤ 1 :=
    (Fraction.Order.Arithmetic.pow_le_pow_direct (Fraction.Order.Arithmetic.sub_nonneg_direct cell.ordered.le) widthLe
      2).trans_eq (one_pow _)
  have bounded := Path.coordinate_increment_bound evaluated.vertices.path request.coordinateBounds evaluated.coordinate
    branch segment member
  have radiusNonnegative := Geometric.Basic.quarterRadius_nonneg request.coordinateBounds.slope_nonnegative
    request.spatial.depth
  have upper := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct widthSquare radiusNonnegative
  rw [Fraction.Field.mul_one_direct] at upper
  rw [request.coordinateStep_eq]
  exact bounded.trans_le (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add upper le_rfl) (by
    decide))

/-- The automatically paid step bound preserves the local root sheet at every edge of the actual odd-degree chart
polygon. -/
theorem coordinate_dot_positive {charts : VertexTree.ChartMesh request.mesh capSample minimum}
    {original : ParentCells.ComparedCell comparison source capSample depth}
    (evaluated : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest.AreaRequest.Evaluation charts original
      stage) (branch : HyperellipticReciprocal.originOrder curve = 1)
    (segment : VertexPaths.Segment regular owners.model original.sample request.tolerance floor stage)
    (member : segment ∈ evaluated.vertices.path.segments) :
    0 < segment.first.root.coordinate.re * segment.last.root.coordinate.re +
      segment.first.root.coordinate.im * segment.last.root.coordinate.im := by
  have toleranceLe : request.tolerance ≤ (request.coordinateTarget / 4) / 8 := by
    rw [request.tolerance_eq]
    exact (Fraction.Order.Basic.min_le_right _ _).trans ((Fraction.Order.Basic.min_le_right _ _).trans
      (Fraction.Order.Basic.min_le_left _ _))
  have divideLe {value : InverseRootPolynomial.Coordinate} (nonnegative : 0 ≤ value) {denominator :
    InverseRootPolynomial.Coordinate}
      (oneLe : 1 ≤ denominator) : value / denominator ≤ value := by
    apply (Fraction.Order.Field.div_le_iff_pos ((by decide : (0 : InverseRootPolynomial.Coordinate) < 1).trans_le
      oneLe)).mpr
    exact (show value = value * 1 from (Fraction.Field.mul_one_direct _).symm).trans_le
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct oneLe nonnegative)
  have toleranceTarget := toleranceLe.trans ((divideLe
    (Fraction.Order.Field.div_nonneg_direct request.coordinatePositive.le (by decide)) (by decide)).trans
      (divideLe request.coordinatePositive.le (by decide)))
  have paid := (toleranceTarget.trans request.coordinateClearance).trans
    (Fraction.Order.Field.div_le_div_of_nonneg_left_direct collar.coordinateBound_positive.le
      (by decide : (0 : InverseRootPolynomial.Coordinate) < 4) (by
          decide +kernel : (4 : InverseRootPolynomial.Coordinate) ≤ 64))
  have step := ((evaluated.coordinate_step_bound branch segment member).trans request.coordinateStep_paid).trans_le
    (request.coordinateClearance.trans
      (Fraction.Order.Field.div_le_div_of_nonneg_left_direct collar.coordinateBound_positive.le
        (by decide : (0 : InverseRootPolynomial.Coordinate) < 20) (by
            decide +kernel : (20 : InverseRootPolynomial.Coordinate) ≤ 64)))
  exact Segment.coordinate_dot_positive segment branch request.small paid step

/-- The original source orientation transfers to every genuine arc edge of the sampled root polygon, with its square
errors paid by construction. -/
theorem coordinate_area_positive {charts : VertexTree.ChartMesh request.mesh capSample minimum}
    {original : ParentCells.ComparedCell comparison source capSample depth}
    (evaluated : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest.AreaRequest.Evaluation charts original
      stage) (branch : HyperellipticReciprocal.originOrder curve = 1)
    (oriented : 0 < AffineTriangle.crossEnergy (parent.edge.point 0) (parent.edge.point 1))
    (segment : VertexPaths.Segment regular owners.model original.sample request.tolerance floor stage)
    (member : segment ∈ evaluated.vertices.path.segments) :
    0 < AffineTriangle.crossEnergy segment.last.root.coordinate segment.first.root.coordinate := by
  have unit (parameter : InverseRootPolynomial.Coordinate) (inside : edge.left.parameter ≤ parameter ∧ parameter ≤
    edge.right.parameter) :
      Data.Gaussian.Basic.Canonical.normSq (parent.edge.point parameter)⁻¹ ≤ 1 := by
    rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical]
    exact Reciprocal.Bounds.disk_unit_bound (ReciprocalExteriorCollar.inverse_inDisk curve
      (data.boundary.point ⟨edge.left.inside.1.trans inside.1, inside.2.trans edge.right.inside.2⟩))
  have firstSquare := segment.first.square
  have lastSquare := segment.last.square
  rw [branch, pow_one, Data.Gaussian.Norm.Basic.normSq_eq_canonical] at firstSquare lastSquare
  exact ReciprocalDiskCoordinateOrientation.coordinate_area_positive
    (unit _ segment.first.prepared.inside) (unit _ segment.last.prepared.inside) request.positive request.small
      firstSquare lastSquare
    (evaluated.coordinate_dot_positive branch segment member) request.angular.positive
    (request.angular.lower oriented segment.first.prepared.inside segment.last.prepared.inside
      (evaluated.vertices.path.width_eq segment member)) request.orientation_paid

end Evaluation

end AreaRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest
