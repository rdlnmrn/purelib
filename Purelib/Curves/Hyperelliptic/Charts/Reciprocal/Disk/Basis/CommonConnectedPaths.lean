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

variable {genus count : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {edge : Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell data edge}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {model :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels.RootModel cell}
  {parameter target sourceTarget : Normalization.InverseRootPolynomial.Coordinate} {floor sourceFloor : Nat}
  {covers : Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers parent}

variable {cover : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data}

open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Data.Gaussian.Basic.Canonical

variable {depth : Nat} {allowance : Normalization.InverseRootPolynomial.Coordinate}

variable {index minimum stage : Nat} {box : Rational.Box}
  {capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}

namespace BasisCommonChartRequests.Plans

variable {anchorBank : Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.PrimitiveCells data index
  cover.mesh.edges}
  {bank : Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceLocations.SampleBank covers index}
  {originals : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank
    covers index} {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

namespace Paths

variable {joinTarget : Normalization.InverseRootPolynomial.Coordinate} {radialDepth : Nat}

/-- Insert each actual cached incoming connector before its original interval chart block, retaining interval order. -/
@[expose] def joinedBlocks (incoming : Normalization.InverseRootPolynomial.Gaussian) :
    {intervals : List (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval cover covers)} →
    {requests : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests regular depth
      target allowance floor sourceFloor intervals} →
    {plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} → {readings :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans} →
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartPaths.BasisCommonChartRequests.Plans.Paths originals
      coefficients requests plans readings →
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBank.Connectors coefficients radialDepth joinTarget
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
    {intervals : List (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval cover covers)} →
    {requests : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests regular depth
      target allowance floor sourceFloor intervals} →
    {plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} → {readings :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans} →
    (paths : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartPaths.BasisCommonChartRequests.Plans.Paths originals
      coefficients requests plans readings) →
    (connectors : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBank.Connectors coefficients radialDepth
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
    {intervals : List (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval cover covers)} →
    {requests : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests regular depth
      target allowance floor sourceFloor intervals} →
    {plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} → {readings :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans} →
    (paths : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartPaths.BasisCommonChartRequests.Plans.Paths originals
      coefficients requests plans readings) →
    (connectors : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBank.Connectors coefficients radialDepth
      joinTarget requests plans readings) →
    (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectedPaths.BasisCommonChartRequests.Plans.Paths.joinedBlocks
      incoming paths connectors).map Prod.snd = paths.pairs.map Prod.snd
  | _, .nil, _, _, _, _ => rfl
  | _, .cons _ .nil, _, _, _, _ => rfl
  | _, .cons _ (.cons _ _), _, _, paths, connectors =>
      congrArg (List.cons _)
        (joinedBlocks_original
        connectors.1.increment paths.2 connectors.2)

/-- There is one connected block for each original common interval. -/
theorem joinedBlocks_count (incoming : Normalization.InverseRootPolynomial.Gaussian)
    {intervals : List (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval cover covers)}
    {requests : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests regular depth
      target allowance floor sourceFloor intervals}
    {plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} {readings :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans}
    (paths : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartPaths.BasisCommonChartRequests.Plans.Paths originals
      coefficients requests plans readings)
    (connectors : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBank.Connectors coefficients radialDepth
      joinTarget requests plans readings) :
    (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectedPaths.BasisCommonChartRequests.Plans.Paths.joinedBlocks
      incoming paths connectors).length = intervals.length := by
  have same := congrArg List.length
    (joinedBlocks_original
    incoming paths connectors)
  rw [Purelib.Data.List.Map.length_map, Purelib.Data.List.Map.length_map, paths.count_eq] at same
  exact same

end Paths
end BasisCommonChartRequests.Plans
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectedPaths
