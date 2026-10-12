module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
public import Purelib.Integration.Polynomial.Gaussian.Path.Execution
import Purelib.Polynomial.Geometry.ClearPath
public import Purelib.Polynomial.Geometry.ClearPath.Constant
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuation
public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionAutomaticModels
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedEdgeRecasting

open Purelib

open Purelib.Curves

open Purelib.Curves.Hyperelliptic

open Purelib.Geometry

open Purelib.Integration.Polynomial.Gaussian.Path.Basic

open Purelib.Polynomial.Geometry

open Purelib.Polynomial.Geometry.ClearPath
open _root_.Purelib.Polynomial.Geometry renaming ClearPath -> ClearPath

open Purelib.Riemann.Branches

open Purelib.Riemann.Branches.ClearSheetContinuation

open Purelib.Riemann.Integration

open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements

open Purelib.Riemann.Integration.PreparedSubdivisionModelCore

open Purelib.Riemann.Paths

open Purelib.Riemann.Topology

section
@[expose] public section

/-!
# Aggregate A-backward quartic sample certificates

This module identifies the explicit 64-edge A-backward sample table with the
canonical centres stored by the completed prepared path.
-/

namespace Purelib.Curves.Hyperelliptic.Integration.Stationary

/-- A centered prepared edge on a constant segment has zero integral sample. -/
private theorem
  aBackwardCenteredEdge_integralSample_zero_of_segment_constant
    {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus}
    (centered : PreparedSubdivisionModelCore.CenteredEdge curve
      differential)
    (base : Data.Gaussian.Basic.Canonical)
    (constant : forall parameter,
      centered.edge.segment.pointAt parameter = base) :
    centered.model.integralSample = 0 := by
  unfold Integration.Polynomial.Gaussian.Cell.Basic.CellModel.integralSample
  rw [CenteredEdge.model_displacement,
    constant, constant, Data.Gaussian.Basic.sub_self,
    Data.Gaussian.Basic.zero_mul]

/-- A constant prepared subdivision contributes zero integral sample.

Every centered edge has zero displacement along the constant segment. -/
theorem
  tailMappedABackwardCanonicalSubdivision_zero_of_constant
    {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Differentials.Basic.Differential genus)
    {ambient : Rational.Box} {start finish : Data.Gaussian.Basic.Canonical}
    {segment : ClearPath.ClearSegment curve.polynomial ambient
      start finish}
    {within : segment.WithinAmbient}
    {left : Subdivision.Endpoint}
    {owner : SquareRootContinuationChain.Owner
      (curve.polynomial.eval (segment.pointAt left.parameter))}
    (base : Data.Gaussian.Basic.Canonical) (constant : forall parameter,
      segment.pointAt parameter = base) (sheet : Fin 2) :
    forall (subdivision :
        PreparedSheetContinuation.Subdivision segment within left
          owner)
      (centers : PreparedSubdivisionModelCore.CenterStates curve
        differential sheet subdivision),
      PathModel.tailMappedIntegralSample
          (PreparedSubdivisionModelCore.centeredEdges curve
            differential sheet subdivision centers)
          CenteredEdge.model = 0
  | .stop _ _, _ => rfl
  | .next current currentOwner request cached ordered small remaining,
      centers => by
      let head : PreparedSubdivisionModelCore.CenteredEdge curve
          differential :=
        { edge := PreparedSubdivisionModelCore.edgeOfStep curve
            differential segment within current currentOwner request cached
              ordered small sheet
          center := centers.1 }
      have headZero : head.model.integralSample = 0 :=
        aBackwardCenteredEdge_integralSample_zero_of_segment_constant
          head base constant
      unfold PreparedSubdivisionModelCore.centeredEdges
        PathModel.tailMappedIntegralSample
      rw [List.foldl_cons, headZero,
        Data.Gaussian.Basic.zero_add]
      change
        PathModel.tailMappedIntegralSample
          (PreparedSubdivisionModelCore.centeredEdges curve
            differential sheet remaining centers.2)
          CenteredEdge.model = 0
      exact tailMappedABackwardCanonicalSubdivision_zero_of_constant
        differential base constant sheet remaining centers.2
end Purelib.Curves.Hyperelliptic.Integration.Stationary

end

section
@[expose] public section

/-!
# Aggregate horizontal quartic sample certificates

This module connects the exact rational samples emitted by the standalone
Python generator to the 64 canonical centered edges of the prepared
A-forward horizontal connector, then aggregates the local error bounds by
finite Cauchy--Schwarz.
-/

namespace Purelib.Curves.Hyperelliptic.Integration.Stationary

/-- A centered prepared edge on a constant segment has zero integral sample. -/
private theorem
  centeredEdge_integralSample_zero_of_segment_constant
    {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus}
    (centered : PreparedSubdivisionModelCore.CenteredEdge curve
      differential)
    (base : Data.Gaussian.Basic.Canonical)
    (constant : forall parameter,
      centered.edge.segment.pointAt parameter = base) :
    centered.model.integralSample = 0 := by
  unfold Integration.Polynomial.Gaussian.Cell.Basic.CellModel.integralSample
  rw [CenteredEdge.model_displacement,
    constant, constant, Data.Gaussian.Basic.sub_self,
    Data.Gaussian.Basic.zero_mul]

/-- The finite centered integral sample of a constant prepared subdivision is zero. -/
private theorem
  tailMappedCanonicalSubdivision_zero_of_segment_constant
    {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Differentials.Basic.Differential genus)
    {ambient : Rational.Box} {start finish : Data.Gaussian.Basic.Canonical}
    {segment : ClearPath.ClearSegment curve.polynomial ambient
      start finish}
    {within : segment.WithinAmbient}
    {left : Subdivision.Endpoint}
    {owner : SquareRootContinuationChain.Owner
      (curve.polynomial.eval (segment.pointAt left.parameter))}
    (base : Data.Gaussian.Basic.Canonical) (constant : forall parameter,
      segment.pointAt parameter = base) (sheet : Fin 2) :
    forall (subdivision :
        PreparedSheetContinuation.Subdivision segment within left
          owner)
      (centers : PreparedSubdivisionModelCore.CenterStates curve
        differential sheet subdivision),
      PathModel.tailMappedIntegralSample
          (PreparedSubdivisionModelCore.centeredEdges curve
            differential sheet subdivision centers)
          CenteredEdge.model = 0
  | .stop _ _, _ => rfl
  | .next current currentOwner request cached ordered small remaining,
      centers => by
      let head : PreparedSubdivisionModelCore.CenteredEdge curve
          differential :=
        { edge := PreparedSubdivisionModelCore.edgeOfStep curve
            differential segment within current currentOwner request cached
              ordered small sheet
          center := centers.1 }
      have headZero : head.model.integralSample = 0 :=
        centeredEdge_integralSample_zero_of_segment_constant head base
          constant
      unfold PreparedSubdivisionModelCore.centeredEdges
        PathModel.tailMappedIntegralSample
      rw [List.foldl_cons, headZero,
        Data.Gaussian.Basic.zero_add]
      change
        PathModel.tailMappedIntegralSample
          (PreparedSubdivisionModelCore.centeredEdges curve
            differential sheet remaining centers.2)
          CenteredEdge.model = 0
      exact tailMappedCanonicalSubdivision_zero_of_segment_constant
        differential base constant sheet remaining centers.2

/-- A prepared path with pointwise constant segments has zero total centered integral sample.

The finite path induction preserves the original prepared segment owners and uses zero displacement for every retained
centered edge. -/
theorem preparedPath_integralSample_zero_of_pointConstant
    {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Differentials.Basic.Differential genus)
    (sheet : Fin 2) {ambient : Rational.Box} (base : Data.Gaussian.Basic.Canonical) :
    forall {start finish : Data.Gaussian.Basic.Canonical}
      {path : Polynomial.Geometry.ClearPath curve.polynomial ambient
        start finish}
      {owner : SquareRootContinuationChain.Owner
        (curve.polynomial.eval start)}
      (prepared : PreparedClearPathModels.PreparedPath path owner),
      Constant.PathPointConstant base path ->
        PathModel.tailMappedIntegralSample
          (CenteredPathChain.ofPreparedPath
            curve differential sheet prepared).parents
          CenteredEdge.model = 0
  | _, _, .nil point, _, .nil _ _, _ => rfl
  | _, _, .cons head tail, _,
      .cons _ _ _ _ preparedHead preparedTail, constant => by
      simp only [
        CenteredPathChain.ofPreparedPath,
        CenteredPathChain.dataOfCompleteSegment_parents,
        PathModel.tailMappedIntegralSample_append]
      unfold Purelib.Riemann.Paths.PreparedClearPathModels.CompleteSegment.centeredEdges
      rw [tailMappedCanonicalSubdivision_zero_of_segment_constant
        differential
          base constant.1 sheet preparedHead.subdivision
          (PreparedSubdivisionAutomaticModels.canonicalCenterStates curve
            differential sheet preparedHead.subdivision),
        preparedPath_integralSample_zero_of_pointConstant curve
          differential
          sheet base preparedTail constant.2,
        Data.Gaussian.Basic.zero_add]
end Purelib.Curves.Hyperelliptic.Integration.Stationary

end
