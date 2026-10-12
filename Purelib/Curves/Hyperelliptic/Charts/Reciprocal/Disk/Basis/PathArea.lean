module
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PathValues
import Purelib.Integration.Path.IncrementAreaComparison
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
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

open Purelib.Algebra

open Purelib.Algebra.FiniteSum.Rational

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

@[expose] public section

/-! Homogeneous bounds for complete acquired source polygons. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PathArea

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers BasisSourceLocations)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRequests (BasisSourceRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEndpointReadings.Point (ReadingView)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cell)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels (RootModel)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples (Data)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests (Reading)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths (Segment Path TreeReadings)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree (Tree Mesh ChartMesh)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule (BasisTreeSources)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.Mesh (BasisEndpoints)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources (Plans)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources.Plans (Evaluation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.Mesh.BasisEndpoints (Plan)
open Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions (midpoint_between)

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PathValues (BasisPathValues)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
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

variable {index readingStage minimum : Nat} {box : Purelib.Geometry.Rational.Box}
  {capSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {polynomials : RegularBasisPolynomials cap
    index box}
  {comparison : Data regular cell}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Sample comparison capSample}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Compatibility
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Algebra.FiniteSum.Fin (sumFin)

namespace BasisPathValues

variable {segments : List (Segment regular model sample
  target floor readingStage)}
  {firstSource lastSource : Gaussian}

/-- Bound the complete source polygon using its certified paired increments. The fourth power of the actual segment
count remains explicit. -/
theorem area_bound (values : PathValues.BasisPathValues polynomials coefficients sourceTarget segments firstSource
  lastSource)
    (nonnegative : 0 ≤ sourceTarget) {chartBound : InverseRootPolynomial.Coordinate} (chartNonnegative : 0 ≤ chartBound)
    (chart : ∀ segment ∈ segments,
      Data.Gaussian.Norm.Basic.normSq (polynomials.value coefficients segment.last.root.coordinate -
        polynomials.value coefficients segment.first.root.coordinate) ≤ chartBound *
          PreparedObservationCoercivity.coefficientNormSq coefficients) :
    Data.Gaussian.Norm.Basic.normSq (values.source.area - IncrementArea.pathArea (segments.map (fun segment =>
      polynomials.value coefficients segment.last.root.coordinate - polynomials.value coefficients
        segment.first.root.coordinate))) ≤
      1280 * (segments.length : InverseRootPolynomial.Coordinate)^4 * sourceTarget * (40 * sourceTarget + chartBound) *
        (PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := by
  have normNonnegative : 0 ≤ PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
      (Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : InverseRootPolynomial.Coordinate)) _ (fun row =>
        Data.Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))
  have errorNonnegative : 0 ≤ 40 * sourceTarget := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
    nonnegative
  have boundNonnegative : 0 ≤ 2 * (40 * sourceTarget + chartBound) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg errorNonnegative chartNonnegative)
  have pairedChart (pair : InverseRootPolynomial.Gaussian × InverseRootPolynomial.Gaussian) (member : pair ∈
    values.pairs) :
      Data.Gaussian.Norm.Basic.normSq pair.2 ≤ chartBound * PreparedObservationCoercivity.coefficientNormSq
        coefficients := by
    have present : pair.2 ∈ values.pairs.map Prod.snd := Map.mem_map.mpr ⟨pair, member, rfl⟩
    rw [values.chart_eq] at present
    obtain ⟨segment, inSegments, equal⟩ := Map.mem_map.mp present
    rw [← equal]
    exact chart segment inSegments
  have sourceBound (pair : InverseRootPolynomial.Gaussian × InverseRootPolynomial.Gaussian) (member : pair ∈
    values.pairs) :
      Data.Gaussian.Norm.Basic.normSq pair.1 ≤ (2 * (40 * sourceTarget + chartBound)) *
        PreparedObservationCoercivity.coefficientNormSq coefficients := by
    have bound := (Data.Gaussian.Norm.Bounds.normSq_add_le_two (pair.1 - pair.2) pair.2).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
        (values.errors pair member) (pairedChart pair member)) (by decide))
    rw [show pair.1 - pair.2 + pair.2 = pair.1 by ring1] at bound
    exact bound.trans_eq (by ring1)
  have chartLe : chartBound ≤ 2 * (40 * sourceTarget + chartBound) := by
    have extra : 0 ≤ 2 * (40 * sourceTarget) + chartBound :=
      add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) errorNonnegative) chartNonnegative
    exact (show chartBound = chartBound + 0 by ring1).trans_le
      ((Fraction.Order.Arithmetic.add_le_add_direct (le_refl chartBound) extra).trans_eq (by ring1))
  have bound := IncrementAreaComparison.pathArea_difference_bound values.pairs
    (Fraction.Order.Arithmetic.mul_nonneg_direct errorNonnegative normNonnegative)
    (Fraction.Order.Arithmetic.mul_nonneg_direct boundNonnegative normNonnegative) values.errors sourceBound
    (fun pair member => (pairedChart pair member).trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      chartLe normNonnegative))
  have countEq : values.pairs.length = segments.length := by
    have equal := congrArg List.length values.chart_eq
    simpa only [Map.length_map] using equal
  rw [countEq, ← values.source.area_eq, values.chart_eq] at bound
  exact bound.trans_eq (by ring1)

/-- The same bound on literal traces, with the two trace-origin terms retained explicitly. No closure or zero-area
implication is assumed. -/
theorem trace_origin_bound (values : PathValues.BasisPathValues polynomials coefficients sourceTarget segments
  firstSource lastSource)
    (firstChart : InverseRootPolynomial.Gaussian) (nonnegative : 0 ≤ sourceTarget)
    {chartBound : InverseRootPolynomial.Coordinate} (chartNonnegative : 0 ≤ chartBound)
    (chart : ∀ segment ∈ segments,
      Data.Gaussian.Norm.Basic.normSq (polynomials.value coefficients segment.last.root.coordinate -
        polynomials.value coefficients segment.first.root.coordinate) ≤ chartBound *
          PreparedObservationCoercivity.coefficientNormSq coefficients) :
    Data.Gaussian.Norm.Basic.normSq ((IncrementArea.traceArea firstSource (values.pairs.map Prod.fst) -
      IncrementArea.traceArea firstChart (values.pairs.map Prod.snd)) -
      (BoundaryRibbon.area firstSource (lastSource - firstSource) -
        BoundaryRibbon.area firstChart (Data.Gaussian.Norm.Sum.Basic.gaussianSum (values.pairs.map Prod.snd)))) ≤
      1280 * (segments.length : InverseRootPolynomial.Coordinate)^4 * sourceTarget * (40 * sourceTarget + chartBound) *
        (PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := by
  rw [IncrementArea.traceArea_eq, IncrementArea.traceArea_eq,
    ← values.source.total_eq, values.source_total, ← values.source.area_eq]
  rw [show (values.source.area + BoundaryRibbon.area firstSource (lastSource - firstSource) -
      (IncrementArea.pathArea (values.pairs.map Prod.snd) +
        BoundaryRibbon.area firstChart (Data.Gaussian.Norm.Sum.Basic.gaussianSum (values.pairs.map Prod.snd)))) -
      (BoundaryRibbon.area firstSource (lastSource - firstSource) -
        BoundaryRibbon.area firstChart (Data.Gaussian.Norm.Sum.Basic.gaussianSum (values.pairs.map Prod.snd))) =
      values.source.area - IncrementArea.pathArea (values.pairs.map Prod.snd) by ring1,
    values.chart_eq]
  exact area_bound values nonnegative
    chartNonnegative chart

end BasisPathValues
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PathArea
