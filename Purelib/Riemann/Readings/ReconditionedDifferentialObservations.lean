module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Diagnostics
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Topology.SquareRootContinuationChain

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
public import Purelib.Riemann.Readings.ClearDifferentialObservations
public import Purelib.Riemann.Branches.ReconditionedClearSheetContinuation

@[expose] public section

/-!
# Differential observations along reconditioned continuations

These certificates follow the reconditioned mesh cell for cell.  The reading
at the right endpoint of each edge is taken from the Rouché-transported owner;
the recursive tail starts from the fresh canonical owner.  The corresponding
`stepBridge` and `rootEquivalent_of_common_bridge` give the finite operational
identification between those two endpoint presentations.
-/

namespace Purelib.Riemann.Readings.ReconditionedDifferentialObservations

open Purelib.Riemann.Curves.AlgebraicDifferentials

section
open Purelib.Data
/-- The exact rational coordinate type. -/
abbrev Coordinate := Rat.Fraction.Rational
/-- The canonical Gaussian rational scalar type. -/
abbrev Gaussian := Gaussian.Basic.Canonical
end

open Purelib.Geometry in
/-- A rational rectangular box. -/
abbrev Box := Rational.Box
open Purelib.Integration in
/-- The executable Gaussian integration cell model. -/
abbrev CellModel := Polynomial.Gaussian.Cell.Basic.CellModel
open Purelib.Riemann in
/-- An operational square-root owner indexed by its original target. -/
abbrev Owner := Topology.SquareRootContinuationChain.Owner

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Polynomial in
set_option genInjectivity false in
/-- Retain algebraically certified integration cells for one successful reconditioned subdivision.

The certificate follows the exact geometric path cell by cell and keeps the original curve, differential and selected
sheet. -/
structure CertifiedSubdivision {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Hyperelliptic.Differentials.Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Coordinate}
    {leftInside : (0 : Coordinate) ≤ left ∧ left ≤ 1}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left))}
    (sheet : Fin 2)
    (subdivision :
      Branches.ReconditionedClearSheetContinuation.Subdivision
        segment within left leftInside owner) where
  /-- The actual ordered integration-cell list. -/ cells : List CellModel
  /-- The algebraic path certificates on the exact lifted reconditioned clear path. -/ certificates :
    Hyperelliptic.Integration.Algebraic.Diagnostics.Basis.PathCertificates curve differential cells
    (Hyperelliptic.Branches.BranchCutLifts.ClearPath.liftOnSheet sheet
      subdivision.toClearPath)

constructive_injectivity CertifiedSubdivision

open Purelib.Riemann
open Purelib.Curves
open Purelib.Polynomial
/-- Construct cell-for-cell differential observations along the retained subdivision.

Each head reading uses the transported endpoint owner; the recursive tail starts from the fresh canonical owner supplied
by the reconditioned continuation. -/
def certifySubdivision {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Hyperelliptic.Differentials.Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Coordinate}
    {leftInside : (0 : Coordinate) ≤ left ∧ left ≤ 1}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left))}
    (sheet : Fin 2) :
    (subdivision :
      Branches.ReconditionedClearSheetContinuation.Subdivision
        segment within left leftInside owner) →
      CertifiedSubdivision curve differential sheet subdivision
  | .stop _ _ _ =>
      { cells := []
        certificates := .nil _ }
  | .next left leftInside owner right rightInside small remaining => by
      let restricted :=
        segment.restrict within left right leftInside rightInside
      let endpointOwner :=
        Branches.ReconditionedClearSheetContinuation.transported
          segment within left right leftInside rightInside owner small
      let head :=
        Readings.ClearDifferentialObservations.inheritedEndpointSample
          curve differential restricted sheet endpointOwner
      let tail := certifySubdivision curve differential sheet remaining
      exact
        { cells := head.model :: tail.cells
          certificates := .cons head.start_eq head.finish_eq
            head.observations tail.certificates }

/-- The certified integration-cell count is exactly the original subdivision's step count. -/
@[simp] theorem certifySubdivision_cellCount {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Hyperelliptic.Differentials.Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Coordinate}
    {leftInside : (0 : Coordinate) ≤ left ∧ left ≤ 1}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left))}
    (sheet : Fin 2)
    (subdivision :
      Branches.ReconditionedClearSheetContinuation.Subdivision
        segment within left leftInside owner) :
    (certifySubdivision curve differential sheet subdivision).cells.length =
      subdivision.stepCount := by
  induction subdivision with
  | stop => rfl
  | next left leftInside owner right rightInside small remaining
      inductionHypothesis =>
      exact congrArg Nat.succ inductionHypothesis

end Purelib.Riemann.Readings.ReconditionedDifferentialObservations
