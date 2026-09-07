import CCL.Riemann.ClearDifferentialObservations
import CCL.Riemann.ReconditionedClearSheetContinuation

/-!
# Differential observations along reconditioned continuations

These certificates follow the reconditioned mesh cell for cell.  The reading
at the right endpoint of each edge is taken from the Rouché-transported owner;
the recursive tail starts from the fresh canonical owner.  The corresponding
`stepBridge` and `rootEquivalent_of_common_bridge` give the finite operational
identification between those two endpoint presentations.
-/

namespace CCL.Riemann.ReconditionedDifferentialObservations

open CCL.Riemann.AlgebraicDifferentials
open CCL.Riemann.BranchCuts
open CCL.Riemann.LiftedPaths

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Box := RFAP.Boxes.Box
abbrev CellModel := CCL.ProgressiveGaussianIntegration.CellModel
abbrev Owner := CCL.Riemann.SquareRootContinuationChain.Owner

/-- Algebraically certified integration cells aligned with the geometric path
of one successful reconditioned subdivision. -/
structure CertifiedSubdivision {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Coordinate}
    {leftInside : (0 : Coordinate) ≤ left ∧ left ≤ 1}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left))}
    (sheet : Fin 2)
    (subdivision :
      CCL.Riemann.ReconditionedClearSheetContinuation.Subdivision
        segment within left leftInside owner) where
  cells : List CellModel
  certificates : PathCertificates curve differential cells
    (CCL.Riemann.BranchCutLifts.ClearPath.liftOnSheet sheet
      subdivision.toClearPath)

/-- Build the cell-for-cell algebraic observations.  The owner used for a
head reading is the transported endpoint owner, before the operationally
equivalent canonical reset used by the tail. -/
def certifySubdivision {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Coordinate}
    {leftInside : (0 : Coordinate) ≤ left ∧ left ≤ 1}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left))}
    (sheet : Fin 2) :
    (subdivision :
      CCL.Riemann.ReconditionedClearSheetContinuation.Subdivision
        segment within left leftInside owner) →
      CertifiedSubdivision curve differential sheet subdivision
  | .stop _ _ _ =>
      { cells := []
        certificates := .nil _ }
  | .next left leftInside owner right rightInside small remaining => by
      let restricted :=
        segment.restrict within left right leftInside rightInside
      let endpointOwner :=
        CCL.Riemann.ReconditionedClearSheetContinuation.transported
          segment within left right leftInside rightInside owner small
      let head :=
        CCL.Riemann.ClearDifferentialObservations.inheritedEndpointSample
          curve differential restricted sheet endpointOwner
      let tail := certifySubdivision curve differential sheet remaining
      exact
        { cells := head.model :: tail.cells
          certificates := .cons head.start_eq head.finish_eq
            head.observations tail.certificates }

@[simp] theorem certifySubdivision_cellCount {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Coordinate}
    {leftInside : (0 : Coordinate) ≤ left ∧ left ≤ 1}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left))}
    (sheet : Fin 2)
    (subdivision :
      CCL.Riemann.ReconditionedClearSheetContinuation.Subdivision
        segment within left leftInside owner) :
    (certifySubdivision curve differential sheet subdivision).cells.length =
      subdivision.stepCount := by
  induction subdivision with
  | stop => rfl
  | next left leftInside owner right rightInside small remaining
      inductionHypothesis =>
      exact congrArg Nat.succ inductionHypothesis

end CCL.Riemann.ReconditionedDifferentialObservations
