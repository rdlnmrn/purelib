module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartConnections
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.Dyadic.RadialTriangles
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.ReciprocalCapBilinearBounds
import Purelib.Riemann.RootContinuation.RootRadialGeometry
import Purelib.Riemann.RootContinuation.RootRadialPairedBoundary
import Purelib.Riemann.RootContinuation.RootRadialRefinement
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartRadialJunctions
public import Purelib.Riemann.RootContinuation.RootRadialPairedArcs
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPreparation
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent

public section

/-! Requested paired fan boundaries for the original retained chart edges. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFans

open Purelib
open Purelib.Approximation.Rational
open Purelib.Approximation.Rational.Geometric
open Purelib.Approximation.Rational.Geometric.Basic
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartConnections
open Purelib.Data.Rat
open Purelib.Integration.Path.Dyadic
open Purelib.Integration.Path.Dyadic.RadialTriangles
open Purelib.Riemann.Normalization
open Purelib.Riemann.Periods
open Purelib.Riemann.RootContinuation.RootRadialPairedArcs
open Purelib.Riemann.RootContinuation.RootRadialPairedBoundary
open Purelib.Riemann.RootContinuation.RootRadialRefinement
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels (Data)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover (CommonCover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank (ChartRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.ChartRequest (Evaluation)
open Purelib.Riemann.RootContinuation
open Purelib.Integration.Path.Dyadic.RadialTriangles (Parameters)
open Purelib.Riemann.RootContinuation.RootRadialRefinement (BoundedRefinement)
open Purelib.Riemann.RootContinuation.RootRadialPairedBoundary (PairedPolynomialSample)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)
variable {genus count otherCount depth floor index : Nat} {curve : HyperellipticCurve
  genus}
  {differential other : Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : PreparedPatch parent}
  {otherPatch : PreparedPatch
    (Purelib.Riemann.Integration.PreparedEdgeRecasting.recastCenteredEdge other parent)}
  {data : Data patch count} {otherData :
    Data otherPatch otherCount}
  {cover : Cover data} {otherCover :
    Cover otherData}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {common :
    CommonCover cover otherCover}
  {target : Coordinate} {request :
    ChartRequest regular common depth target floor}
  (evaluated : Evaluation request
    index)

set_option genInjectivity false in
/-- One retained pair of coefficient bounds and a shared radial mesh paying the original chart-edge fan target.

The computed geometric depth retains the supplied minimum and exact error scale for every actual edge. -/
structure FanRequest (target : InverseRootPolynomial.Coordinate) (minimum : Nat) where
  /-- The cached first cap-polynomial energy bounds on the original radial domain. -/ firstBounds :
    Cap.EnergyBounds evaluated.samples.firstCap RootRadialGeometry.domain
  /-- The cached second cap-polynomial energy bounds on that same original radial domain. -/ otherBounds :
    Cap.EnergyBounds evaluated.samples.otherCap RootRadialGeometry.domain
  /-- The cached common paired fan error scale. -/ scale : InverseRootPolynomial.Coordinate
  /-- The retained scale is the exact radial geometric factor times the original paired coefficient scale. -/ scale_eq :
    scale = 128^2 * 64 * ReciprocalCapBilinearBounds.bilinearScale firstBounds otherBounds
  /-- The cached common radial subdivision depth. -/ depth : Nat
  /-- The retained depth is at least the computed positive-target search threshold. -/ depth_ge :
    Search.firstQuarterBelow scale minimum target ≤ depth
  /-- The retained depth preserves the supplied minimum. -/ minimum_le : minimum ≤ depth
  /-- The actual radial parameter mesh at that exact retained depth. -/ parameters : RadialTriangles.Parameters depth
  /-- The cached geometric fan error at the retained depth. -/ error : InverseRootPolynomial.Coordinate
  /-- The error cache is the quarter-radius expression for the original scale and depth. -/ error_eq : error =
    Geometric.Basic.quarterRadius scale depth
  /-- The cached common geometric fan error is strictly below the original positive target. -/ accurate : error < target

constructive_injectivity FanRequest

namespace FanRequest

/-- One pair of coefficient caches and one radial mesh serve all original chart edges. No orientation or analytic
clearance is supplied by the caller. -/
@[expose] def build (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) (minimum : Nat) :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFans.FanRequest evaluated target minimum := by
  let firstBounds := EnergyBounds.build evaluated.samples.firstCap RootRadialGeometry.domain
  let otherBounds := EnergyBounds.build evaluated.samples.otherCap RootRadialGeometry.domain
  let scale : Coordinate := 128^2 * 64 * ReciprocalCapBilinearBounds.bilinearScale firstBounds otherBounds
  have nonnegative : 0 ≤ scale := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.sq_nonneg_direct _) (by decide +kernel))
      (ReciprocalCapBilinearBounds.bilinearScale_nonnegative firstBounds otherBounds)
  let depth := Search.firstQuarterBelow scale minimum target
  exact ⟨firstBounds, otherBounds, scale, rfl, depth, Nat.le_refl _,
    Search.firstQuarterBelow_ge scale minimum target, Parameters.build depth,
    Geometric.Basic.quarterRadius scale depth, rfl, Search.firstQuarterBelow_accurate scale nonnegative minimum target
      positive⟩

variable {evaluated} {fanTarget : Coordinate} {minimum : Nat}

/-- Synchronize radial meshes before acquiring any fans; coefficient caches and the original requested error budget are
retained. -/
@[expose] def atDepth (planned : Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFans.FanRequest evaluated
  fanTarget minimum) (depth : Nat)
    (later : planned.depth ≤ depth) : Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFans.FanRequest evaluated
      fanTarget minimum := by
  have nonnegative : 0 ≤ planned.scale := by
    rw [planned.scale_eq]
    exact Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.sq_nonneg_direct _) (by decide +kernel))
      (ReciprocalCapBilinearBounds.bilinearScale_nonnegative planned.firstBounds planned.otherBounds)
  exact ⟨planned.firstBounds, planned.otherBounds, planned.scale, planned.scale_eq,
    depth, planned.depth_ge.trans later, planned.minimum_le.trans later,
    Parameters.build depth, Geometric.Basic.quarterRadius planned.scale depth, rfl,
    (quarterRadius_antitone nonnegative later).trans_lt
      (planned.error_eq.symm.trans_lt planned.accurate)⟩

/-- The original retained starting chart coordinate of this actual edge. -/
@[expose] def FirstCoordinate (i : Fin common.intervals.length) (edge : Fin (request.plans.get i).geometry.tail.length)
  :=
  Evaluation.chartCoordinate evaluated i edge.castSucc

/-- The original retained finishing chart coordinate of this actual edge. -/
@[expose] def LastCoordinate (i : Fin common.intervals.length) (edge : Fin (request.plans.get i).geometry.tail.length)
  :=
  Evaluation.chartCoordinate evaluated i edge.succ

set_option genInjectivity false in
/-- The actual bounded radial fan on one original retained chart edge with its paired polynomial area estimate. -/
structure Fan (planned : Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFans.FanRequest evaluated fanTarget
  minimum)
    (i : Fin common.intervals.length) (edge : Fin (request.plans.get i).geometry.tail.length) where
  /-- The bounded refinement of the original edge endpoints using the retained common radial parameters. -/ geometry :
    RootRadialRefinement.BoundedRefinement
    (FirstCoordinate (evaluated := evaluated) i
    edge)
    (LastCoordinate (evaluated := evaluated) i
      edge) planned.parameters
  /-- The paired polynomial fan sample using the two original cached coefficient bounds. -/ sampled :
    RootRadialPairedBoundary.PairedPolynomialSample geometry planned.firstBounds planned.otherBounds
  /-- The actual retained paired fan area satisfies the original requested target. -/ accurate :
    Data.Gaussian.Norm.Basic.normSq sampled.area < fanTarget

constructive_injectivity Fan

/-- Construct the actual chart-edge radial fan from the retained root bounds, parameters and original coefficient
caches. -/
@[expose] def acquire (planned : Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFans.FanRequest evaluated
  fanTarget minimum)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (i : Fin common.intervals.length) (edge : Fin (request.plans.get i).geometry.tail.length) :
      Fan planned i edge := by
  have firstScalar := regular.padded.root_norm_le (Evaluation.chart_square_inside evaluated branch i edge.castSucc)
  have lastScalar := regular.padded.root_norm_le (Evaluation.chart_square_inside evaluated branch i edge.succ)
  rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at firstScalar lastScalar
  let geometry := BoundedRefinement.build firstScalar lastScalar planned.parameters
  let sampled := PairedPolynomialSample.build geometry planned.firstBounds planned.otherBounds
  have error : sampled.error = planned.error := by
    rw [sampled.error_eq, planned.error_eq, planned.scale_eq]
  exact ⟨geometry, sampled, sampled.bounded.trans_lt (error.trans_lt planned.accurate)⟩

/-- The actual fan area is the first radial potential plus its original arc area minus the last radial potential. -/
theorem Fan.boundary_eq {planned : Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFans.FanRequest evaluated
  fanTarget minimum}
    {i : Fin common.intervals.length} {edge : Fin (request.plans.get i).geometry.tail.length} (fan :
      Fan planned i edge) :
    fan.sampled.area = CommonChartRadialJunctions.radialPotential evaluated planned.depth i edge.castSucc +
      Bilinear.arcArea (CommonChartRadialJunctions.radialValues evaluated) planned.depth
        (Evaluation.chartCoordinate evaluated i edge.castSucc) (Evaluation.chartCoordinate evaluated i edge.succ) -
      CommonChartRadialJunctions.radialPotential evaluated planned.depth i edge.succ :=
  PairedPolynomialSample.boundary_eq_arcs fan.sampled

end FanRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFans
