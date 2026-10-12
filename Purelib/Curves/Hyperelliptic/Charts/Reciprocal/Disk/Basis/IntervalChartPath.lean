module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSources
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartTree
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PathValues
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartAcquisition
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBlocks
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Integration.Path.Dyadic.DyadicPrimitivePathSamples
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSources

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartTree.BasisTreeSources

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBlocks.BasisCommonInterval

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartAcquisition.BasisIntervalChartRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PathValues.BasisTreeSources

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths

open Purelib.Integration.Path

open Purelib.Integration.Path.Dyadic

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Normalization

public section

/-! Materialize the acquired common-interval source/chart path once, retaining
its exact pullback readback and both cached endpoint combinations. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartPath

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers BasisSourceLocations)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRequests (BasisSourceRequest)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cell Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels (RootModel)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule (EndpointSources BasisTreeSources)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest (BasisIntervalChartRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartAcquisition.BasisIntervalChartRequest (Plan)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths (TreeReadings)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEndpointReadings.Point (ReadingView)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover (BasisCommonInterval)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PathValues (BasisPathValues)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations
  (PrimitiveBank)

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {edge : Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell data edge}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {model :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels.RootModel cell}
  {parameter target sourceTarget : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor sourceFloor :
    Nat}
  {covers : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers parent}

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)

variable {cover : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data}

namespace BasisIntervalChartRequest

variable {interval : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval cover
  covers} {depth index minimum : Nat} {box : Purelib.Geometry.Rational.Box}
  {request : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest.BasisIntervalChartRequest
    interval regular depth target sourceTarget floor sourceFloor}
  {capSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {polynomials : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap
    index box}

namespace Plan.Evaluation

variable {plan :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartAcquisition.BasisIntervalChartRequest.Plan
  request capSample polynomials minimum}
  {comparison : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular interval.anchor.cell}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Sample comparison capSample}
  {bank : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceLocations.SampleBank
    covers index} {stage : Nat}

/-- Reuse the acquired midpoint and extreme root readings. -/
@[expose] def path (evaluated : Plan.Evaluation plan sample bank stage) :=
  TreeReadings.path evaluated.readings evaluated.first evaluated.last interval.ordered

/-- The actual coefficient-weighted source value at the original acquired first root reading. -/
@[expose] def firstValue (evaluated : Plan.Evaluation plan sample bank stage) (coefficients :
  LinearAlgebra.Gaussian.Energy.GaussianVector
  genus) : Gaussian :=
  FiniteSum.Fin.sumFin (fun row => coefficients row * evaluated.firstSources.evaluated.sources row)

/-- The actual coefficient-weighted source value at the original acquired last root reading. -/
@[expose] def lastValue (evaluated : Plan.Evaluation plan sample bank stage) (coefficients :
  LinearAlgebra.Gaussian.Energy.GaussianVector
  genus) : Gaussian :=
  FiniteSum.Fin.sumFin (fun row => coefficients row * evaluated.lastSources.evaluated.sources row)

/-- The paired source/chart path on the exact retained midpoint and endpoint readings, with their original source
accuracy certificates. -/
@[expose] def values (evaluated : Plan.Evaluation plan sample bank stage) (coefficients :
  LinearAlgebra.Gaussian.Energy.GaussianVector genus)
  :=
  Plans.pathValues bank coefficients request.tree request.treeSources plan.treeSources
    evaluated.readings evaluated.treeSources evaluated.first evaluated.last interval.ordered

      (firstValue
      evaluated coefficients)
      (lastValue
      evaluated coefficients)
    (evaluated.firstSources.evaluated.accurate coefficients) (evaluated.lastSources.evaluated.accurate coefficients)

/-- The actual retained source increments equal the original dyadic pullback increments on the complete common interval.
-/
theorem source_path (evaluated : Plan.Evaluation plan sample bank stage)
    (originals : BasisSourceLocations.PrimitiveBank covers index) (coefficients :
      LinearAlgebra.Gaussian.Energy.GaussianVector genus) :

      (values
      evaluated coefficients).pairs.map Prod.fst = DyadicPrimitivePaths.dyadicIncrements
      ((BasisCommonInterval.primitiveSample interval regular polynomials originals bank).pullbackValue coefficients)
      depth interval.edge.left.parameter interval.edge.right.parameter := by
  cases request with
  | mk positive first last tree firstSources firstEq lastSources lastEq treeSources treeEq numerical numericalEq =>
      subst firstSources
      subst lastSources
      subst treeSources
      exact Plans.onInterval_path interval positive bank originals coefficients tree le_rfl le_rfl interval.ordered
        plan.treeSources evaluated.readings evaluated.treeSources evaluated.first evaluated.last

          (firstValue
          evaluated coefficients)
          (lastValue
          evaluated coefficients)
        (EndpointSources.onInterval_value evaluated.firstSources originals coefficients)
        (EndpointSources.onInterval_value evaluated.lastSources originals coefficients)
        (evaluated.firstSources.evaluated.accurate coefficients) (evaluated.lastSources.evaluated.accurate coefficients)

open
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartPath.BasisIntervalChartRequest.Plan.Evaluation
  in
set_option genInjectivity false in
/-- Both polygon summaries refer to the original acquired root path. -/
structure PathData (evaluated : Plan.Evaluation plan sample bank stage)
    (originals : BasisSourceLocations.PrimitiveBank covers index) (coefficients :
      LinearAlgebra.Gaussian.Energy.GaussianVector genus) where
  /-- The cached coefficient-weighted source value at the original first acquired endpoint. -/ firstSource :
    InverseRootPolynomial.Gaussian
  /-- The first source cache reads the original retained first endpoint transports. -/ first_eq : firstSource =
    firstValue
    evaluated coefficients
  /-- The cached coefficient-weighted source value at the original last acquired endpoint. -/ lastSource :
    InverseRootPolynomial.Gaussian
  /-- The last source cache reads the original retained last endpoint transports. -/ last_eq : lastSource =
    lastValue
    evaluated coefficients
  /-- The actual paired source/chart path on the retained original root segments and endpoint values. -/ paired :
    PathValues.BasisPathValues polynomials coefficients sourceTarget (path evaluated).segments firstSource lastSource
  /-- The retained complete source path is exactly the original interval pullback increment path. -/ source_path :
    paired.pairs.map Prod.fst = DyadicPrimitivePaths.dyadicIncrements
    ((BasisCommonInterval.primitiveSample interval regular polynomials originals bank).pullbackValue coefficients)
    depth interval.edge.left.parameter interval.edge.right.parameter
  /-- The cached chart summary of that exact original paired path. -/ chart : IncrementArea.Summary (paired.pairs.map
    Prod.snd)

constructive_injectivity PathData

/-- Materialize the paired source/chart path from the existing original endpoint and midpoint acquisitions and cache its
complete chart summary. -/
@[expose] def acquirePath (evaluated : Plan.Evaluation plan sample bank stage)
    (originals : BasisSourceLocations.PrimitiveBank covers index) (coefficients :
      LinearAlgebra.Gaussian.Energy.GaussianVector genus) :

      PathData
      evaluated originals coefficients :=
  let firstSource :=
    firstValue
    evaluated coefficients
  let lastSource :=
    lastValue
    evaluated coefficients
  let paired := Plans.pathValues bank coefficients request.tree request.treeSources plan.treeSources
    evaluated.readings evaluated.treeSources evaluated.first evaluated.last interval.ordered firstSource lastSource
    (evaluated.firstSources.evaluated.accurate coefficients) (evaluated.lastSources.evaluated.accurate coefficients)
  ⟨firstSource, rfl, lastSource, rfl, paired,
    source_path
    evaluated originals coefficients,
    IncrementArea.Summary.build (paired.pairs.map Prod.snd)⟩

open
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartPath.BasisIntervalChartRequest.Plan.Evaluation
  in
/-- The source summary is the same complete area used by the common-depth comparison; this is a path identity, not just
an endpoint equality. -/
theorem PathData.source_area (evaluated : Plan.Evaluation plan sample bank stage)
    {originals : BasisSourceLocations.PrimitiveBank covers index} {coefficients :
      LinearAlgebra.Gaussian.Energy.GaussianVector genus}
    (path :
      PathData
      evaluated originals coefficients)
    (block : PrimitiveSample.Block (BasisCommonInterval.primitiveSample interval regular polynomials originals bank)
      coefficients depth) :
    path.paired.source.area = block.pullback.summary.area := by
  rw [path.paired.source.area_eq, path.source_path, block.pullback.summary.area_eq, block.pullback.increments_eq]

open
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartPath.BasisIntervalChartRequest.Plan.Evaluation
  in
/-- The retained source path total equals the exact original common-depth pullback block total. -/
theorem PathData.source_total (evaluated : Plan.Evaluation plan sample bank stage)
    {originals : BasisSourceLocations.PrimitiveBank covers index} {coefficients :
      LinearAlgebra.Gaussian.Energy.GaussianVector genus}
    (path :
      PathData
      evaluated originals coefficients)
    (block : PrimitiveSample.Block (BasisCommonInterval.primitiveSample interval regular polynomials originals bank)
      coefficients depth) :
    path.paired.source.total = block.pullback.summary.total := by
  rw [path.paired.source.total_eq, path.source_path, block.pullback.summary.total_eq, block.pullback.increments_eq]

end Plan.Evaluation
end BasisIntervalChartRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartPath
