module
import Purelib.Data.List.Map
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSources
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PathValues
import Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Data.Gaussian.Basic
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

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSources

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PathValues.BasisTreeSources

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations

open Purelib.Geometry.Rectangle.Partition

open Purelib.Integration.Path.Dyadic

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

public section

/-! Use fixed common-interval owners throughout the acquired chart tree;
its source side is the literal dyadic pullback path. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartTree

open Purelib.Data

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers BasisSourceLocations)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRequests (BasisSourceRequest)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cell Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels (RootModel)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests (Reading)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule (EndpointSources BasisTreeSources)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources (Plans)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources.Plans (Evaluation)
open Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions (midpoint_between)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree (Tree)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths (TreeReadings)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PathValues.BasisTreeSources.Plans (pathValues)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEndpointReadings.Point (ReadingView)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover (BasisCommonInterval)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations
  (PrimitiveBank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples (Data Sample)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {parent : Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : PreparedPatch parent} {data :
    UniformReciprocalModels.Data patch count}
  {edge : ParameterEdge} {cell :
    Cell data edge}
  {regular : RegularBounds.Data cap} {model :
    RootModel cell}
  {parameter target sourceTarget : Coordinate} {floor sourceFloor :
    Nat}
  {covers : BasisSourceCovers parent}

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)

variable {cover : Cover data}

namespace BasisTreeSources

/-- Every midpoint keeps the interval's retained source cells. -/
@[expose] def onInterval (interval : BasisCommonInterval cover covers) (sourceTarget :
  Coordinate)
    (positive : 0 < sourceTarget) (sourceFloor : Nat) :
    {depth : Nat} → {first last : Coordinate} → (tree : Tree regular model target floor
      depth first last) →
    interval.edge.left.parameter ≤ first → last ≤ interval.edge.right.parameter → first ≤ last →
    BasisTreeSources covers sourceTarget sourceFloor tree
  | _, _, _, .leaf _ _, _, _, _ => ⟨⟩
  | _, _, _, .node middle left right, lower, upper, ordered =>
      let between := midpoint_between ordered
      ⟨EndpointSources.onInterval middle interval ⟨lower.trans between.1, between.2.trans upper⟩ sourceTarget positive
        sourceFloor,
        BasisTreeSources.onInterval interval
          sourceTarget positive sourceFloor left lower (between.2.trans upper) between.1,
        BasisTreeSources.onInterval interval
          sourceTarget positive sourceFloor right (lower.trans between.1) upper between.2⟩

namespace Plans

variable {index readingStage minimum : Nat} {box : Geometry.Rational.Box}
  {capSample : Cap.Primitives.Sample cap differential index box}
  {polynomials : RegularBasisPolynomials cap
    index box}
  {comparison : Data regular cell}
  {sample : Sample comparison capSample}

/-- Full path readback, including all interior excursions, for the existing chart-path acquisition with interval-owned
source requests. -/
theorem onInterval_path (interval : BasisCommonInterval cover covers)
    (positive : 0 < sourceTarget) (bank : BasisSourceLocations.SampleBank covers index)
    (originals : PrimitiveBank covers index) (coefficients :
      GaussianVector genus) :
    {depth : Nat} → {first last : Coordinate} → (tree : Tree regular model target floor
      depth first last) →
    (lower : interval.edge.left.parameter ≤ first) → (upper : last ≤ interval.edge.right.parameter) → (ordered : first ≤
      last) →
    (plans : Plans polynomials minimum tree
      (onInterval interval
      sourceTarget positive sourceFloor tree lower upper ordered)) →
    (readings : TreeReadings sample readingStage tree) →
    (evaluated : Evaluation bank tree
      (onInterval interval
      sourceTarget positive sourceFloor tree lower upper ordered) plans readings) →
    (before : Reading regular model sample first target floor readingStage) →
    (after : Reading regular model sample last target floor readingStage) →
    (firstSource lastSource : Gaussian) →
    (firstEq : firstSource = (BasisCommonInterval.primitiveSample interval regular polynomials originals
      bank).pullbackValue coefficients first) →
    (lastEq : lastSource = (BasisCommonInterval.primitiveSample interval regular polynomials originals
      bank).pullbackValue coefficients last) →
    (firstClose : Gaussian.Norm.Basic.normSq (firstSource - polynomials.value coefficients
      before.root.coordinate) ≤
      10 * sourceTarget * PreparedObservationCoercivity.coefficientNormSq coefficients) →
    (lastClose : Gaussian.Norm.Basic.normSq (lastSource - polynomials.value coefficients
      after.root.coordinate) ≤
      10 * sourceTarget * PreparedObservationCoercivity.coefficientNormSq coefficients) →
    (pathValues bank coefficients tree _ plans readings evaluated before after ordered firstSource lastSource
      firstClose lastClose).pairs.map Prod.fst =
      DyadicPrimitivePaths.dyadicIncrements ((BasisCommonInterval.primitiveSample interval regular polynomials originals
        bank).pullbackValue coefficients)
        depth first last
  | _, _, _, .leaf _ _, _, _, _, _, _, _, _, _, _, _, firstEq, lastEq, _, _ => by
      change [_ - _] = [_ - _]
      rw [firstEq, lastEq]
  | _, _, _, .node middle left right, lower, upper, ordered, plans, readings, evaluated, before, after,
      firstSource, lastSource, firstEq, lastEq, firstClose, lastClose => by
      have middleEq := EndpointSources.onInterval_value evaluated.1 originals coefficients
      have middleClose := evaluated.1.evaluated.accurate coefficients
      have between := midpoint_between ordered
      change List.map (Prod.fst : Gaussian × Gaussian →
        Gaussian) (_ ++ _) = _
      rw [List.Map.map_append, DyadicPrimitivePaths.dyadicIncrements]
      exact congrArg₂ List.append

          (onInterval_path
          interval positive bank originals coefficients left lower (between.2.trans upper) between.1
          plans.2.1 readings.2.1 evaluated.2.1 before readings.1.reading firstSource _ firstEq middleEq firstClose
            middleClose)

          (onInterval_path
          interval positive bank originals coefficients right (lower.trans between.1) upper between.2
          plans.2.2 readings.2.2 evaluated.2.2 readings.1.reading after _ lastSource middleEq lastEq middleClose
            lastClose)

end Plans
end BasisTreeSources
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartTree
