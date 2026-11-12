module
import Purelib.Algebra.NatCast
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Data.List.Map
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Rational.Squares
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh
import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Integration.RectangularSharedPrimitives
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularExteriorBoundary
import Purelib.Riemann.Readings.RectangularPrimitiveBoundary
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.Readings.UniformPreparedRequests.Face.Shared
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AnalyticComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.EdgeSides
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.PuncturedEdgeFaces
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib.Data.Gaussian.Norm

public section

/-!
# Shared mesh values for an entire original period fragment

Every analytic subfragment pays both ownership discrepancies and its inverse
residual. Exact telescoping leaves the two shared endpoint values; finite
Cauchy--Schwarz retains the complete analytic-piece count.
-/

open Purelib.Riemann.Integration.RectangularSharedPrimitives renaming SharedPrimitiveValues -> SharedValues

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment

open Purelib

open Purelib.Algebra.FiniteSum.Rational

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries

open Purelib.Data.Rat

open Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh

open Purelib.LinearAlgebra.Grid

open Purelib.Riemann.Branches.RectangularSheetGauge

open Purelib.Riemann.Comparison

open Purelib.Riemann.Integration

open Purelib.Riemann.Integration.PreparedParentSplitting

open Purelib.Riemann.Integration.RectangularSharedPrimitives

open Purelib.Riemann.Normalization

open Purelib.Riemann.Paths

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.RectangularExteriorBoundary

open Purelib.Riemann.Readings.RectangularPrimitiveBoundary

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open _root_.Purelib.Geometry.Rectangle renaming AxisPartition -> Partition
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Paths.RectangularSegmentSplitting (SegmentPiece)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh.RectangularInverseModels (CommonMesh)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)
open Purelib.Riemann.Integration.RectangularSharedPrimitives (SharedPrimitiveValues)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentReadings (FragmentBounds)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces (RegularPrimitiveFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment (SheetEntry)
open Purelib.Riemann.Normalization.RegularFaceInverseModels
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveOverlapBounds)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianNormSqSum)
open Purelib.Algebra.FiniteSum.Rational.Squares (coordinateSum)
open Purelib.Approximation.Rational.Budget.Aggregate (countCoordinate countCoordinate_eq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {source :
    Differential genus}
  {axes : PrimitiveAxes base.bank.grid}
    {parent : CenteredEdge curve source}
  {cuts : List Data.Rat.Fraction.Rational} {partition : Partition 0 1 cuts}
    {interval : Geometry.Rectangle.Partition.PreparedAxisPartitions.Interval}
  {fragment : RegularPrimitiveFragment axes
    parent partition interval}
  {domains : DomainBanks.FaceDomainBank frames
    base.faces.regulars}
  {count : Nat} {target : InverseRootPolynomial.Coordinate} {request :
    LocalRequest parent count target}
  {assigned :
    SheetEntry fragment
    domains request}

namespace SharedComparison

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

/-- Read the retained primitive cache through its original face and domain.

The numerical lookup uses the retained face, sheet and domain identities.
It returns the original primitive, anchor, offset and corner caches. -/
@[expose] def sharedPrimitives (assigned : SheetEntry fragment domains request) {index : Nat}
    {numerator : CoefficientPolynomial}
    (numerics : PrimitiveData.FacePrimitiveBank source index (numerator := numerator) domains) :
    PrimitiveData.DomainPrimitives assigned.domain source index (numerator := numerator) :=
  (((numerics.get fragment.face.located.index).castFace fragment.face.located.indexed).atSheet
    assigned.entry.sheet).castDomain
    assigned.domain_eq.symm

end SharedComparison

variable
  {bounds : FragmentBounds assigned.domain.patch
    source}
  {globalBounds : PrimitiveOverlapBounds
    fragment.face.located.face.clearance (PreparedPrimitiveSamples.differentialNumerator
    source)}
  {tolerance : InverseRootPolynomial.Coordinate} {accuracy :
    GridPrimitiveAccuracy globalBounds assigned.domain.steps
    tolerance}
  {primitives : Primitives
    (Transitions.oriented (assigned.domain.patch.sheets.refine
    accuracy.index).transitions (assigned.domain.patch.sheets.refine accuracy.index).gauge)
    (PreparedPrimitiveSamples.differentialNumerator source)}
  {anchors : PrimitiveAnchors primitives} {offsets :
    Offsets anchors.edges}
  {points : List InverseRootPolynomial.Gaussian}
  {mesh : CommonMesh
    assigned.domain.geometry (Geometry.allCells
    assigned.domain.geometry) points}

namespace SharedComparison

/-- Vertex lookups are proved from inclusion in the common mesh's point bank. They do not re-evaluate any primitive or
prepare another root. -/
theorem shared_piece_le (assigned : SheetEntry fragment domains request)
    (bounds : FragmentBounds assigned.domain.patch source)
    {globalBounds : PrimitiveOverlapBounds fragment.face.located.face.clearance
      (PreparedPrimitiveSamples.differentialNumerator source)}
    {tolerance : InverseRootPolynomial.Coordinate} (accuracy : RectangularPrimitiveAccuracy.GridPrimitiveAccuracy
      globalBounds assigned.domain.steps tolerance)
    {primitives : Primitives (Transitions.oriented (assigned.domain.patch.sheets.refine
      accuracy.index).transitions (assigned.domain.patch.sheets.refine accuracy.index).gauge)
      (PreparedPrimitiveSamples.differentialNumerator source)}
    {anchors : PrimitiveAnchors primitives} {offsets : Offsets
      anchors.edges}
    {points : List InverseRootPolynomial.Gaussian} (mesh : CommonMesh assigned.domain.geometry
      (Geometry.allCells assigned.domain.geometry) points)
    (included : ∀ point ∈ assigned.split.points, point ∈ points)
    (readings : RectangularSharedPrimitives.SharedPrimitiveValues anchors offsets mesh.surface)
    (piece : SegmentPiece assigned.domain.geometry fragment.located.first
      fragment.located.last)
    (member : piece ∈ assigned.split.pieces) :
    Basic.normSq (((SharedValues.atPoint readings) piece.lastPoint -
      (SharedValues.atPoint readings) piece.firstPoint) -
      (request.request.model.primitive.value.eval piece.lastPoint - request.request.model.primitive.value.eval
        piece.firstPoint)) ≤
      32 * accuracy.globalBound + 2 * AnalyticComparison.pieceCharge assigned bounds piece accuracy.index := by
  exact request.faceSharedPiece_increment_le assigned.sample assigned.entry assigned.domain assigned.split
    interval.lower assigned.fractionInside fragment.located.first_eq.symm
    (AnalyticComparison.neighborhood_endpoints assigned).1 (AnalyticComparison.neighborhood_endpoints assigned).2
    bounds accuracy mesh included readings piece member

/-- The complete original fragment is compared to the shared values of the supplied mesh. Every analytic-piece and
endpoint-ownership charge remains visible; no closed-path or zero-total cancellation is used. -/
theorem shared_increment_le (readings : RectangularSharedPrimitives.SharedPrimitiveValues anchors offsets mesh.surface)
    (included : ∀ point ∈ assigned.split.points, point ∈ points) :
    Basic.normSq (((SharedValues.atPoint readings) fragment.located.last -
      (SharedValues.atPoint readings) fragment.located.first) -
      (request.request.model.primitive.value.eval fragment.located.last -
        request.request.model.primitive.value.eval fragment.located.first)) ≤
      Aggregate.countCoordinate assigned.split.count * (32 * Aggregate.countCoordinate assigned.split.count *
        accuracy.globalBound +
        2 * Squares.coordinateSum (assigned.split.pieces.map fun piece => AnalyticComparison.pieceCharge assigned bounds
          piece accuracy.index)) := by
  exact request.faceSharedSplit_increment_le assigned.sample assigned.entry assigned.domain assigned.split
    interval.lower assigned.fractionInside fragment.located.first_eq.symm
    (AnalyticComparison.neighborhood_endpoints assigned).1 (AnalyticComparison.neighborhood_endpoints assigned).2
    bounds accuracy mesh included readings

end SharedComparison

set_option genInjectivity false in
/-- Cached scalar comparison for an original fragment and shared mesh.

The endpoint difference and ordered analytic-charge sum are retained caches.
Their exact equations and error certificate use the original request and mesh. -/
structure SharedComparison (readings : RectangularSharedPrimitives.SharedPrimitiveValues anchors offsets mesh.surface)
  where
  /-- The cached difference of the two actual shared endpoint readings. -/ value : InverseRootPolynomial.Gaussian
  /-- The cached value is exactly the original fragment's shared last-minus-first reading. -/ value_eq : value =
    (SharedValues.atPoint readings) fragment.located.last - (SharedValues.atPoint readings)
    fragment.located.first
  /-- The cached sum of every original retained analytic-piece charge. -/ analyticCharge :
    InverseRootPolynomial.Coordinate
  /-- The charge cache equals the exact ordered analytic-piece sum at the retained accuracy index. -/ analyticCharge_eq
    : analyticCharge = Squares.coordinateSum (assigned.split.pieces.map fun piece => AnalyticComparison.pieceCharge
    assigned bounds piece accuracy.index)
  /-- The cached complete fragment discrepancy bound, including its original piece count and ownership allowance. -/
    bound : InverseRootPolynomial.Coordinate
  /-- The bound is the exact piece-count payment for both retained ownership and analytic charges. -/ bound_eq : bound =
    Aggregate.countCoordinate assigned.split.count *
    (32 * Aggregate.countCoordinate assigned.split.count * accuracy.globalBound + 2 * analyticCharge)
  /-- The cached shared increment differs from the original prepared primitive increment by at most the retained full
    bound. -/ accurate : Basic.normSq (value - (request.request.model.primitive.value.eval
    fragment.located.last -
    request.request.model.primitive.value.eval fragment.located.first)) ≤ bound

constructive_injectivity SharedComparison

namespace SharedComparison

/-- Cache the actual shared endpoint difference and complete analytic-piece charge sum, retaining their exact fragment
bound. -/
@[expose] def build (readings : RectangularSharedPrimitives.SharedPrimitiveValues anchors offsets
  mesh.surface)
    (included : ∀ point ∈ assigned.split.points, point ∈ points) :
    SharedComparison (bounds := bounds) (accuracy :=
      accuracy) readings :=
  let charge := Squares.coordinateSum (assigned.split.pieces.map fun piece => AnalyticComparison.pieceCharge assigned
    bounds piece accuracy.index)
  ⟨(SharedValues.atPoint readings) fragment.located.last - (SharedValues.atPoint readings)
    fragment.located.first, rfl, charge, rfl,
    Aggregate.countCoordinate assigned.split.count * (32 * Aggregate.countCoordinate assigned.split.count *
      accuracy.globalBound + 2 * charge), rfl,
    shared_increment_le readings included⟩

end SharedComparison

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment
