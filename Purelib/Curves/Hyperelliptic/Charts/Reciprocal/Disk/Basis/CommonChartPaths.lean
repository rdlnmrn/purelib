module
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartPath
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartAcquisition
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartBudget
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PathValues
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisCommonChartRequests

open Purelib.Curves

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

public section

/-! Complete common-parent source/chart paths from the acquired reading bank.
Cached summaries preserve every block and the polygon of block totals. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartPaths

variable {genus count : Nat} {curve : Basic.HyperellipticCurve genus} {differential :
  Differentials.Basic.Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    UniformReciprocalModels.Data patch count}
  {edge : Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
    UniformReciprocalCover.Cell data edge}
  {regular : RegularBounds.Data cap} {model :
    UniformReciprocalRootChannels.RootModel cell}
  {parameter target sourceTarget : Normalization.InverseRootPolynomial.Coordinate} {floor sourceFloor : Nat}
  {covers : SourceLocations.BasisSourceCovers parent}

variable {cover : UniformReciprocalCover.Cover data}

open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Data.Gaussian.Basic.Canonical

variable {depth : Nat} {allowance : Normalization.InverseRootPolynomial.Coordinate}

variable {index minimum stage : Nat} {box : Rational.Box}
  {capSample : Cap.Primitives.Sample cap differential index box}
  {polynomials : Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}

namespace BasisCommonChartRequests.Plans

variable {anchorBank : UniformReciprocalPrimitives.PrimitiveCells data index
  cover.mesh.edges}
  {bank : SourceLocations.BasisSourceLocations.SampleBank covers index}
  {originals : CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank
    covers index} {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

/-- Keep each interval's acquired paths and both retained endpoint values. -/
@[expose] def Paths (originals :
  CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank covers index)
  (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    {intervals : List (CommonCover.BasisCommonInterval cover covers)} →
    (requests : CommonChartSchedule.BasisCommonChartRequests regular depth
      target allowance floor sourceFloor intervals) →
    (plans : CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests) →
      Plans.Readings anchorBank
      bank stage requests plans → Type 2
  | _, .nil, _, _ => PUnit
  | _, .cons _ tail, plans, readings =>
      IntervalChartPath.BasisIntervalChartRequest.Plan.Evaluation.PathData
        readings.1.evaluated originals coefficients ×
          Paths
          originals coefficients tail plans.2 readings.2

/-- Acquire each original common interval's paired source/chart path from the retained reading and primitive banks in
interval order. -/
@[expose] def acquirePaths (originals :
  CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank covers index)
  (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    {intervals : List (CommonCover.BasisCommonInterval cover covers)} →
    (requests : CommonChartSchedule.BasisCommonChartRequests regular depth
      target allowance floor sourceFloor intervals) →
    (plans : CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests) → (readings :
      Plans.Readings anchorBank
      bank stage requests plans) →
    Paths originals
      coefficients requests plans readings
  | _, .nil, _, _ => ⟨⟩
  | _, .cons _ tail, plans, readings =>

        ⟨IntervalChartPath.BasisIntervalChartRequest.Plan.Evaluation.acquirePath
          readings.1.evaluated originals coefficients,

          acquirePaths
          originals coefficients tail plans.2 readings.2⟩

namespace Paths

/-- The ordered original source and chart increment blocks retained by each interval acquisition. -/
@[expose] def pairs : {intervals : List (CommonCover.BasisCommonInterval
  cover covers)} →
    {requests : CommonChartSchedule.BasisCommonChartRequests regular depth
      target allowance floor sourceFloor intervals} →
    {plans : CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} → {readings :
      Plans.Readings anchorBank
      bank stage requests plans} →
    Paths originals
      coefficients requests plans readings → List (List Normalization.InverseRootPolynomial.Gaussian × List
      Normalization.InverseRootPolynomial.Gaussian)
  | _, .nil, _, _, _ => []
  | _, .cons _ _, _, _, paths => (paths.1.paired.pairs.map Prod.fst, paths.1.paired.pairs.map Prod.snd) ::
    pairs
    paths.2

/-- There is exactly one retained source/chart block pair per original common interval. -/
theorem count_eq : {intervals : List (CommonCover.BasisCommonInterval cover
  covers)} →
    {requests : CommonChartSchedule.BasisCommonChartRequests regular depth
      target allowance floor sourceFloor intervals} →
    {plans : CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} → {readings :
      Plans.Readings anchorBank
      bank stage requests plans} →
    (paths : Paths originals
      coefficients requests plans readings) → paths.pairs.length = intervals.length
  | _, .nil, _, _, _ => rfl
  | _, .cons _ _, _, _, paths => congrArg Nat.succ paths.2.count_eq

/-- Compose the cached source summaries in original interval order, retaining the complete polygon of block totals. -/
@[expose] def sourceSummary : {intervals : List
  (CommonCover.BasisCommonInterval cover covers)} →
    {requests : CommonChartSchedule.BasisCommonChartRequests regular depth
      target allowance floor sourceFloor intervals} →
    {plans : CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} → {readings :
      Plans.Readings anchorBank
      bank stage requests plans} →
    (paths : Paths originals
      coefficients requests plans readings) → Path.IncrementArea.Summary (paths.pairs.map Prod.fst).flatten
  | _, .nil, _, _, _ => Path.IncrementArea.Summary.build []
  | _, .cons _ _, _, _, paths => paths.1.paired.source.append paths.2.sourceSummary

/-- Compose the cached chart summaries in original interval order, retaining the complete polygon of block totals. -/
@[expose] def chartSummary : {intervals : List
  (CommonCover.BasisCommonInterval cover covers)} →
    {requests : CommonChartSchedule.BasisCommonChartRequests regular depth
      target allowance floor sourceFloor intervals} →
    {plans : CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} → {readings :
      Plans.Readings anchorBank
      bank stage requests plans} →
    (paths : Paths originals
      coefficients requests plans readings) → Path.IncrementArea.Summary (paths.pairs.map Prod.snd).flatten
  | _, .nil, _, _, _ => Path.IncrementArea.Summary.build []
  | _, .cons _ _, _, _, paths => paths.1.chart.append paths.2.chartSummary

/-- Exact agreement with the common primitive acquisition, block by block in
original interval order. No independent origins or endpoint totals are identified. -/
theorem source_paths {primitiveTarget : Normalization.InverseRootPolynomial.Coordinate} {primitiveFloor : Nat} :
    {intervals : List (CommonCover.BasisCommonInterval cover covers)} →
    {requests : CommonChartSchedule.BasisCommonChartRequests regular depth
      target allowance floor sourceFloor intervals} →
    {plans : CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} → {readings :
      Plans.Readings anchorBank
      bank stage requests plans} →
    (paths : Paths originals
      coefficients requests plans readings) →
    {primitivePlans : CommonPrimitiveAcquisition.CommonPrimitivePlans regular
      primitiveTarget primitiveFloor intervals} →
    (blocks : CommonPrimitiveAcquisition.CommonPrimitivePlans.Blocks regular
      polynomials originals bank coefficients depth primitivePlans) →
    paths.pairs.map Prod.fst = blocks.paths.map Prod.snd
  | _, .nil, _, _, _, _, .nil => rfl
  | _, .cons _ _, _, _, paths, _, .cons block _ remaining => by
      change (paths.1.paired.pairs.map Prod.fst) :: _ = block.pullback.increments :: _
      rw [paths.1.source_path, block.pullback.increments_eq]
      exact congrArg (List.cons _)
        (source_paths
        paths.2 remaining)

end Paths
end BasisCommonChartRequests.Plans
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartPaths
