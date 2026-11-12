module
import Purelib.Data.List.Map
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings
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
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartPaths
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBank
public import Purelib.Integration.Path.IncrementAreaJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnector
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartAcquisition
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartBudget
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartPath
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PathValues
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover

open Purelib.Curves

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

public section

/-! Insert the actual cached connector before each following interval, and
compose the complete path summary from the retained block summaries. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectedPaths

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

namespace Paths

variable {joinTarget : Normalization.InverseRootPolynomial.Coordinate} {radialDepth : Nat}

/-- Insert each actual cached incoming connector before its original interval chart block, retaining interval order. -/
@[expose] def joinedBlocks (incoming : Normalization.InverseRootPolynomial.Gaussian) :
    {intervals : List (CommonCover.BasisCommonInterval cover covers)} →
    {requests : CommonChartSchedule.BasisCommonChartRequests regular depth
      target allowance floor sourceFloor intervals} →
    {plans : CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} → {readings :
      CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans} →
    CommonChartPaths.BasisCommonChartRequests.Plans.Paths originals
      coefficients requests plans readings →
    CommonConnectorBank.Connectors coefficients radialDepth joinTarget
      requests plans readings → List (Normalization.InverseRootPolynomial.Gaussian × List
      Normalization.InverseRootPolynomial.Gaussian)
  | _, .nil, _, _, _, _ => []
  | _, .cons _ .nil, _, _, paths, _ => [(incoming, paths.1.paired.pairs.map Prod.snd)]
  | _, .cons _ (.cons _ _), _, _, paths, connectors =>
      (incoming, paths.1.paired.pairs.map Prod.snd) ::
        joinedBlocks
        connectors.1.increment paths.2 connectors.2

/-- Compose the complete connected parent summary from the cached interval summaries and actual incoming connectors.

Each connector is prepended to its retained block and the full polygon of block totals is preserved. -/
@[expose] def joinedSummary (incoming : Normalization.InverseRootPolynomial.Gaussian) :
    {intervals : List (CommonCover.BasisCommonInterval cover covers)} →
    {requests : CommonChartSchedule.BasisCommonChartRequests regular depth
      target allowance floor sourceFloor intervals} →
    {plans : CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} → {readings :
      CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans} →
    (paths : CommonChartPaths.BasisCommonChartRequests.Plans.Paths originals
      coefficients requests plans readings) →
    (connectors : CommonConnectorBank.Connectors coefficients radialDepth
      joinTarget requests plans readings) →
    Path.IncrementArea.Summary
      ((joinedBlocks
      incoming paths connectors).map (fun block => block.1 :: block.2)).flatten
  | _, .nil, _, _, _, _ => Path.IncrementArea.Summary.build []
  | _, .cons _ .nil, _, _, paths, _ =>
      (Path.IncrementAreaJoins.Summary.prepend paths.1.chart incoming).append (Path.IncrementArea.Summary.build [])
  | _, .cons _ (.cons _ _), _, _, paths, connectors =>
      (Path.IncrementAreaJoins.Summary.prepend paths.1.chart incoming).append
        (joinedSummary
        connectors.1.increment paths.2 connectors.2)

/-- Removing the incoming connectors recovers exactly the original retained chart blocks. -/
theorem joinedBlocks_original (incoming : Normalization.InverseRootPolynomial.Gaussian) :
    {intervals : List (CommonCover.BasisCommonInterval cover covers)} →
    {requests : CommonChartSchedule.BasisCommonChartRequests regular depth
      target allowance floor sourceFloor intervals} →
    {plans : CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} → {readings :
      CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans} →
    (paths : CommonChartPaths.BasisCommonChartRequests.Plans.Paths originals
      coefficients requests plans readings) →
    (connectors : CommonConnectorBank.Connectors coefficients radialDepth
      joinTarget requests plans readings) →
    (joinedBlocks
      incoming paths connectors).map Prod.snd = paths.pairs.map Prod.snd
  | _, .nil, _, _, _, _ => rfl
  | _, .cons _ .nil, _, _, _, _ => rfl
  | _, .cons _ (.cons _ _), _, _, paths, connectors =>
      congrArg (List.cons _)
        (joinedBlocks_original
        connectors.1.increment paths.2 connectors.2)

/-- There is one connected block for each original common interval. -/
theorem joinedBlocks_count (incoming : Normalization.InverseRootPolynomial.Gaussian)
    {intervals : List (CommonCover.BasisCommonInterval cover covers)}
    {requests : CommonChartSchedule.BasisCommonChartRequests regular depth
      target allowance floor sourceFloor intervals}
    {plans : CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} {readings :
      CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans}
    (paths : CommonChartPaths.BasisCommonChartRequests.Plans.Paths originals
      coefficients requests plans readings)
    (connectors : CommonConnectorBank.Connectors coefficients radialDepth
      joinTarget requests plans readings) :
    (joinedBlocks
      incoming paths connectors).length = intervals.length := by
  have same := congrArg List.length
    (joinedBlocks_original
    incoming paths connectors)
  rw [Data.List.Map.length_map, Data.List.Map.length_map, paths.count_eq] at same
  exact same

end Paths
end BasisCommonChartRequests.Plans
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectedPaths
