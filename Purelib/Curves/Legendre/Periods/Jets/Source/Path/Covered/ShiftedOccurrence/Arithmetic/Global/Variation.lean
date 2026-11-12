module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Global
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Programs.Variation
import Purelib.Calculus.Jet.Quadratic.Weighted.Widths
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Joint.Rows
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Block
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Parameter.Strip
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Vector.Basic
import Purelib.Data.Gaussian.Norm.Components.Maximum
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Variation bounds for the same retained global Taylor remainder

The old weighted-sum certificate and its loose recorded factor are retained.
One common original-patch row ceiling bounds its same stored parent entries.
Weighted quadrance then gives a stronger theorem on that identical remainder,
using total rational variation rather than a parent-count factor.
-/

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.ValueBlocks.Integral

open Purelib
open Purelib.Algebra.FiniteSum.Fin (sumFin_congr)
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Calculus.Jet
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint finishPoint)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

/-- A common original-patch row ceiling gives a count-independent bound on the same stored global remainder.

The local ceiling is a bound on the actual retained source patches; it is
not inferred for different reconditioned boxes. Every original parent entry,
unit weight and whole weighted-certificate factory remains unchanged. The
conclusion does not bound or replace that certificate's old factor field.
Zero physical displacements are handled by the original weighted estimate.
-/
public theorem remainder_variation_le
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : Riemann.Topology.PreparedRefinementRootChains.RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest} {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    {retained : ValueBlocks (next := next)} (actual : Integral (next := next) retained)
    (order coordinate : Fin 2) (ceiling : Rational)
    (ceiling_le : ∀ index : Fin (parent :: parents).length,
      Variation.Point.Step.Joint.rowCeiling ((covered.entry index).val.neighborhood count) 0 order coordinate ≤
        ceiling) :
    Norm.Basic.normSq (actual.certificate order coordinate).remainder ≤
      (16 * (ceiling + 21 / 2) * variation (parent :: parents) ^ 2) * Norm.Basic.normSq increment ^ 2 := by
  let weights := fun index : Fin (parent :: parents).length => Norm.Components.maximum
    ((finishPoint ((parent :: parents)[index.val]'index.isLt)).coordinate -
      (startPoint ((parent :: parents)[index.val]'index.isLt)).coordinate)
  have nonnegative : 0 ≤ ceiling :=
    (Variation.Point.Step.Joint.rowCeiling_nonnegative
      ((covered.entry 0).val.neighborhood count) 0 order coordinate).trans (ceiling_le 0)
  have coefficient : 0 ≤ 8 * (ceiling + 21 / 2) :=
    Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
      (Order.Arithmetic.add_pos_of_nonneg_of_pos_direct nonnegative (by decide +kernel)).le
  have bounded (index : Fin (parent :: parents).length) :
      (actual.entries order coordinate index).factor ≤ (16 * (ceiling + 21 / 2)) * (weights index) ^ 2 := by
    let displacement := (finishPoint ((parent :: parents)[index.val]'index.isLt)).coordinate -
      (startPoint ((parent :: parents)[index.val]'index.isLt)).coordinate
    have original := (congrArg (fun entry : Quadratic.Basic.Certificate increment => entry.factor)
      (actual.entry_eq index order coordinate)).trans ((retained.block index).certificate_factor order coordinate)
    have row := Order.Arithmetic.add_le_add_direct (ceiling_le index)
      (Order.Basic.le_refl (21 / 2 : Rational))
    have common := Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct row (by decide +kernel : (0 : Rational) ≤ 8))
      (Norm.Basic.normSq_nonneg displacement)
    have norm := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Norm.Components.normSq_le_twice_maximum_sq displacement) coefficient
    have density : ValueBlock.density (covered := covered) index order coordinate =
        8 * (Variation.Point.Step.Joint.rowCeiling
          ((covered.entry index).val.neighborhood count) 0 order coordinate + 21 / 2) *
            Norm.Basic.normSq displacement := by
      unfold ValueBlock.density
      have scalar : (21 / 2 : Rational) = 3 * (7 / 2) := by decide +kernel
      rewrite [scalar]
      ring1
    exact original.trans_le (density.trans_le (common.trans (norm.trans_eq (by ring1))))
  have paid := Quadratic.Basic.Certificate.width_remainder_le
    (fun index => actual.entries order coordinate index) weights (16 * (ceiling + 21 / 2))
    (fun index => Norm.Components.maximum_nonnegative _) bounded
  have retainedRemainder := (congrArg (fun original : Quadratic.Basic.Certificate increment => original.remainder)
    (actual.certificate_factory order coordinate)).trans
      (Quadratic.Basic.Certificate.weightedSum_remainder actual.weights (actual.entries order coordinate))
  have unitSum := sumFin_congr (fun index : Fin (parent :: parents).length =>
    (congrArg (fun weight : Canonical => weight * (actual.entries order coordinate index).remainder)
      (actual.weight_eq index)).trans (by ring1))
  exact (congrArg Norm.Basic.normSq (retainedRemainder.trans unitSum)).trans_le paid

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.ValueBlocks.Integral
