module
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartAcquisition
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartPath
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisArcs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CoordinatePolynomial
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.HomogeneousTraceConnection
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartGeometry
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisTrace
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PathValues
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedRootGeometry
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Rational

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartAcquisition.BasisIntervalChartRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartGeometry.BasisIntervalChartRequest.Plan

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartPath.BasisIntervalChartRequest.Plan

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisArcs

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisRequest.AreaRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisTrace.AreaRequest.Evaluation

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Normalization

public section

/-! The refined-arc estimate on the actual common-interval chart path. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartArcs

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers BasisSourceLocations)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRequests (BasisSourceRequest)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cell Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels (RootModel)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest (BasisIntervalChartRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartAcquisition.BasisIntervalChartRequest (Plan)
open
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartPath.BasisIntervalChartRequest.Plan.Evaluation
  (PathData)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEndpointReadings.Point (ReadingView)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover (BasisCommonInterval)
open _root_.Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CoordinatePolynomial (CoordinateBounds)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisArcs (basisArcScale)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisArcs.Path (BasisArcGeometry)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisRequest.AreaRequest.Evaluation (RequestedBasisEnergy)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse (UniformBounds)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds (BasisBounds)
open Purelib.Integration.Path.HomogeneousTraceConnection (HomogeneousTrace)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {edge : ParameterEdge} {cell :
    Cell data edge}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {model :
    RootModel cell}
  {parameter target sourceTarget : Coordinate} {floor sourceFloor :
    Nat}
  {covers : BasisSourceCovers parent}

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)

variable {cover : Cover data}

namespace BasisIntervalChartRequest

variable {interval : BasisCommonInterval cover
  covers} {depth index minimum : Nat} {box : Purelib.Geometry.Rational.Box}
  {request : BasisIntervalChartRequest
    interval regular depth target sourceTarget floor sourceFloor}
  {capSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {polynomials : RegularBasisPolynomials cap
    index box}

namespace Plan.Evaluation

variable {plan :
  Plan
  request capSample polynomials minimum}
  {comparison : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular interval.anchor.cell}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Sample comparison capSample}
  {bank : BasisSourceLocations.SampleBank
    covers index} {stage : Nat}

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)

/-- The acquired common-interval chart path has the retained arc geometry when the origin is simple and the square and
dyadic mesh bounds are paid. -/
theorem basisArcGeometry (evaluated : Plan.Evaluation plan sample bank stage)
    (bounds : CoordinatePolynomial.CoordinateBounds comparison)
    (coordinate : CoordinatePolynomial sample)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (padded : target ≤ regular.padded.squareTolerance)
    (mesh : target ≤ Geometric.Basic.quarterRadius 1 depth) :
    Path.BasisArcGeometry (Evaluation.path evaluated) bounds.slope := by
  intro segment member
  refine ⟨Evaluation.square_inside branch padded segment.last, Evaluation.square_inside branch padded segment.first, ?_⟩
  have actual := (Evaluation.coordinate_step_bound evaluated bounds coordinate branch segment member).le
  have reading := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct mesh (by
      decide : (0 : InverseRootPolynomial.Coordinate) ≤ 4)
  exact actual.trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct le_rfl reading) (by decide)).trans_eq
    (by simp only [-eq_self, -iff_self, Geometric.Basic.quarterRadius, Fraction.Field.div_eq_mul_inv_direct]; ring1))

/-- The trace uses the cached chart polygon and the already sampled endpoint potentials, transported along the literal
chart-path readback. -/
@[expose] def PathData.trace (evaluated : Plan.Evaluation plan sample bank stage)
    {originals : BasisSourceLocations.PrimitiveBank covers index} {coefficients :
      LinearAlgebra.Gaussian.Energy.GaussianVector genus}
    (pathData : Evaluation.PathData evaluated originals coefficients)
    {energyTarget : InverseRootPolynomial.Coordinate} {energyFloor : Nat}
    (energy : Evaluation.RequestedBasisEnergy (Evaluation.path evaluated).segments polynomials energyTarget energyFloor)
    (sampled : energy.Sample coefficients evaluated.first.root.coordinate evaluated.last.root.coordinate)
    {uniform : ReciprocalPaddedInverse.UniformBounds regular.padded}
    (basis : ReciprocalPaddedBasisBounds.BasisBounds uniform)
    (bounds : CoordinatePolynomial.CoordinateBounds comparison)
    (coordinate : CoordinatePolynomial sample)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (padded : target ≤ regular.padded.squareTolerance) (mesh : target ≤ Geometric.Basic.quarterRadius 1 depth)
    (allowance : InverseRootPolynomial.Coordinate) (nonnegative : 0 ≤ allowance)
    (paid : Geometric.Basic.quarterRadius (ChartBasisArcs.basisArcScale basis bounds.slope) depth ≤ (4 * allowance) ^ 2)
      :
    HomogeneousTraceConnection.HomogeneousTrace coefficients (pathData.paired.pairs.map Prod.snd)
      (polynomials.value coefficients evaluated.first.root.coordinate)
      (polynomials.value coefficients evaluated.last.root.coordinate)
      sampled.firstPotential sampled.lastPotential (energy.error + allowance) := by
  have summary : IncrementArea.Summary ((Evaluation.path evaluated).segments.map (fun segment =>
      polynomials.value coefficients segment.last.root.coordinate - polynomials.value coefficients
        segment.first.root.coordinate)) :=
    pathData.paired.chart_eq ▸ pathData.chart
  have connection := RequestedBasisEnergy.Sample.trace energy basis coefficients sampled summary
    branch
      (basisArcGeometry
      evaluated bounds coordinate branch padded mesh) allowance nonnegative paid
  exact pathData.paired.chart_eq.symm ▸ connection

end Plan.Evaluation
end BasisIntervalChartRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartArcs
