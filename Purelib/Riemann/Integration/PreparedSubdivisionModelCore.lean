module

meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Map
import Purelib.Data.List.Membership
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
public import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Path
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.ComparisonAllowance
import Purelib.Integration.Polynomial.Gaussian.Path.CompatibleRefinement
import Purelib.Integration.Polynomial.Gaussian.Path.ConstantComparison
import Purelib.Integration.Polynomial.Gaussian.Path.ConstantRefinement
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
public import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Riemann.Topology.SquareRootContinuationChain

import Purelib.Curves.Hyperelliptic.Differentials.PreparedModels
import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
import Purelib.Riemann.Readings.PreparedBoundaryEquivalence
public import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Allowance
import Purelib.Polynomial.Power.Gaussian
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Data.Gaussian.Field
import Purelib.RootIsolation.Track.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Power
import Purelib.Curves.Hyperelliptic.Sheets.Basic
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.RootIsolation.State.WindingOne.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-!
# Uniform models for a complete prepared subdivision

This module folds the shrinking constant-cell constructor over a successful
dependent continuation mesh.  The result is a finite path model together with
cell-for-cell uniform algebraic certification on the inherited sheet.
-/

namespace Purelib.Riemann.Integration.PreparedSubdivisionModelCore

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials

open Purelib.Data.List

open Purelib.Riemann.Curves.AlgebraicDifferentials
open Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts

open Purelib.Data.Rat in
/-- The exact rational coordinate carrier. -/
abbrev Coordinate := Fraction.Rational
open Purelib.Data.Gaussian in
/-- The canonical Gaussian rational carrier. -/
abbrev Gaussian := Basic.Canonical
/-- The original rational box type. -/
abbrev Box := Purelib.Geometry.Rational.Box
/-- The retained square-root continuation owner at its original radicand. -/
abbrev Owner := Purelib.Riemann.Topology.SquareRootContinuationChain.Owner
/-- A subdivision parameter carrying its unit-interval bounds. -/
abbrev Endpoint := Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.Endpoint
/-- The original prepared continuation request. -/
abbrev StepRequest := Purelib.Riemann.Branches.PreparedSheetContinuation.StepRequest
/-- A polynomial cell model retaining its endpoints, observations and local error allowance. -/
abbrev CellModel := Purelib.Integration.Polynomial.Gaussian.Cell.Basic.CellModel
/-- An ordered finite list of polynomial cell models. -/
abbrev PathModel := Purelib.Integration.Polynomial.Gaussian.Path.Basic.PathModel
/-- Operational equivalence between the original Gaussian names. -/
abbrev NamedEquivalent := Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
/-- A coherent Gaussian name retaining its executable process and starting state. -/
abbrev CoherentNamed := Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
/-- A differential edge retaining its original segment, owner, request, cache and sheet. -/
abbrev PreparedEdge {genus : Nat} (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus) :=
  Purelib.Riemann.Integration.PreparedConstantModels.PreparedEdge curve differential
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Branches in
/-- The dependent continuation subdivision retaining its source segment and starting owner. -/
abbrev PreparedSubdivision {polynomial :
    Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (left : ClearSheetContinuation.Subdivision.Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter))) :=
  PreparedSheetContinuation.Subdivision segment within left owner

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- A nonnegative squared-distance radius gives a lower bound for the second real coordinate.

If the squared norm of the first value minus the second is at most the radius squared, the second real coordinate is at
least the first real coordinate minus that radius. -/
theorem real_sub_radius_le_of_normSq_sub_le
    {left right : Gaussian} {radius : Coordinate}
    (radiusNonnegative : 0 <= radius)
    (bounded : Data.Gaussian.Norm.Basic.normSq (left - right) <=
      radius ^ 2) :
    left.re - radius <= right.re := by
  have realSquare : (left - right).re ^ 2 <= radius ^ 2 := by
    calc
      (left - right).re ^ 2 <=
          (left - right).re ^ 2 + (left - right).im ^ 2 :=
        le_add_of_nonneg_right
          (Fraction.Order.Arithmetic.sq_nonneg_direct (left - right).im)
      _ = Data.Gaussian.Norm.Basic.normSq (left - right) := rfl
      _ <= radius ^ 2 := bounded
  have realUpper : (left - right).re <= radius :=
    Fraction.Order.Arithmetic.le_of_sq_le_sq_direct radiusNonnegative
      realSquare
  calc
    left.re - radius <= left.re - (left - right).re :=
      Fraction.Order.Arithmetic.sub_le_sub_left_direct realUpper left.re
    _ = right.re := by
      simp only [Basic.sub_re]
      ring1

open Purelib.Data.Gaussian in
/-- The reversed squared-distance bound gives the same real-coordinate lower bound for a nonnegative radius. -/
theorem real_sub_radius_le_of_normSq_reverse_sub_le
    {left right : Gaussian} {radius : Coordinate}
    (radiusNonnegative : 0 <= radius)
    (bounded : Data.Gaussian.Norm.Basic.normSq (right - left) <=
      radius ^ 2) :
    left.re - radius <= right.re := by
  apply real_sub_radius_le_of_normSq_sub_le radiusNonnegative
  have reverse : left - right = -(right - left) := by
    apply Basic.ext <;>
      simp only [Basic.sub_re,
        Basic.sub_im,
        Basic.neg_re,
        Basic.neg_im] <;> ring1
  rw [reverse, Norm.Basic.normSq_neg]
  exact bounded

/-- The rational endpoint one lies in the closed unit interval. -/
theorem endpointInside :
    (0 : Coordinate) <= 1 ∧ (1 : Coordinate) <= 1 := by decide

open Purelib.Polynomial in
open Purelib.Riemann.Branches in
/-- Package one original prepared continuation step as a differential edge.

The constructor retains the supplied segment, source owner, request, cache, ordering and clearance proof, together with
the selected sheet. -/
@[expose] def edgeOfStep {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (left : Endpoint)
    (owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : PreparedSheetContinuation.CachedSource segment left
      owner request)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (sheet : Fin 2) : PreparedEdge curve differential where
  ambient := ambient
  start := start
  finish := finish
  segment := segment
  within := within
  left := left
  owner := owner
  request := request
  cached := cached
  ordered := ordered
  small := small
  sheet := sheet

section
open Purelib.Polynomial
open Purelib.Riemann.Branches
open Purelib.Riemann.Integration
/-- The constructed edge starts at the original segment's left subdivision parameter. -/
@[simp] theorem edgeOfStep_point_zero {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (left : Endpoint)
    (owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : PreparedSheetContinuation.CachedSource segment left
      owner request)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (sheet : Fin 2) :
    (edgeOfStep curve differential segment within left owner request cached
      ordered small sheet).point 0 = segment.pointAt left.parameter :=
  PreparedConstantModels.PreparedEdge.point_zero _

/-- The constructed edge finishes at the request's original endpoint parameter. -/
@[simp] theorem edgeOfStep_point_one {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (left : Endpoint)
    (owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : PreparedSheetContinuation.CachedSource segment left
      owner request)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (sheet : Fin 2) :
    (edgeOfStep curve differential segment within left owner request cached
      ordered small sheet).point 1 =
        segment.pointAt request.endpoint.parameter :=
  PreparedConstantModels.PreparedEdge.point_one _

end

open Purelib.Polynomial in
open Purelib.Riemann.Branches in
/-- The constructed edge retains the exact cached prepared-owner box. -/
@[simp] theorem edgeOfStep_cached_prepared_box {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (left : Endpoint)
    (owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : PreparedSheetContinuation.CachedSource segment left
      owner request)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (sheet : Fin 2) :
    (edgeOfStep curve differential segment within left owner request cached
      ordered small sheet).cached.preparedOwner.track.initial.box =
        cached.preparedOwner.track.initial.box := rfl

open Purelib.Polynomial in
/-- Read the prepared edges of a continuation subdivision in their original order.

Each step retains its original request, cache and proofs; the terminal constructor contributes no edge. -/
@[expose] def preparedEdges {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) :
    PreparedSubdivision segment within left owner ->
      List (PreparedEdge curve differential)
  | .stop _ _ => []
  | .next left owner request cached ordered small remaining =>
      edgeOfStep curve differential segment within left owner request cached
          ordered small sheet ::
        preparedEdges curve differential sheet remaining

set_option genInjectivity false in
open Purelib.Approximation.Gaussian in
/-- Two retained Gaussian names with an operational equivalence certificate.

The parent and child names remain separate operands. Their certificate records
operational equivalence between those exact names. -/
structure BoundaryWitness where
  /-- The original parent Gaussian name. -/ parentName : Name.Basic.Named
  /-- The original child Gaussian name. -/ childName : Name.Basic.Named
  /-- Operational equivalence of the two retained Gaussian names. -/ equivalent : NamedEquivalent parentName childName

constructive_injectivity BoundaryWitness

set_option genInjectivity false in
open Purelib.Approximation.Gaussian in
/-- A coherent coefficient family certified equivalent to zero at every bounded parameter.

The chart is indexed by the curve and the two differentials; each query retains its unit-interval proof and its actual
coefficient name. -/
structure WedgeChart {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (leftDifferential rightDifferential : Basic.Differential genus) where
  /-- The actual coherent wedge coefficient at each bounded parameter. -/ coefficient : (fraction : Coordinate) ->
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) -> CoherentNamed
  /-- Each coefficient name is operationally equivalent to the exact zero name. -/ zero : forall (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1),
    NamedEquivalent (coefficient fraction inside).name
      (Name.Coherent.CoherentNamed.Coherence.exact 0).name

constructive_injectivity WedgeChart

open Purelib.Polynomial in
open Purelib.Riemann.Branches in
/-- Construct the zero wedge-coefficient chart of two differentials along one prepared sheet step.

The original segment, owner and request determine every coefficient query and its equivalence to the exact zero name. -/
@[expose] public def wedgeChartOfStep {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (leftDifferential rightDifferential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (left : Endpoint)
    (owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (sheet : Fin 2) :
    WedgeChart curve leftDifferential rightDifferential where
  coefficient := fun fraction inside =>
    PreparedModels.wedgeCoefficientAt curve
      leftDifferential rightDifferential segment within left owner request
        ordered small sheet fraction inside
  zero := fun fraction inside =>
    PreparedModels.wedgeCoefficientAt_zero curve
      leftDifferential rightDifferential segment within left owner request
        ordered small sheet fraction inside

section
open Purelib.Polynomial
/-- Read the wedge charts of the original prepared subdivision in step order. -/
@[expose] def wedgeCharts {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (leftDifferential rightDifferential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) :
    (subdivision : PreparedSubdivision segment within left owner) ->
      List (WedgeChart curve leftDifferential rightDifferential)
  | .stop _ _ => []
  | .next left owner request _cached ordered small remaining =>
      wedgeChartOfStep curve leftDifferential rightDifferential segment within
          left owner request ordered small sheet ::
        wedgeCharts curve leftDifferential rightDifferential sheet remaining

/-- There is exactly one wedge chart for each actual subdivision step. -/
@[simp] theorem wedgeCharts_length {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (leftDifferential rightDifferential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2)
    (subdivision : PreparedSubdivision segment within left owner) :
    (wedgeCharts curve leftDifferential rightDifferential sheet
      subdivision).length = subdivision.stepCount := by
  induction subdivision with
  | stop => rfl
  | next left owner request cached ordered small remaining
      inductionHypothesis =>
      exact congrArg Nat.succ inductionHypothesis

end

set_option genInjectivity false in
open Purelib.Polynomial in
open Purelib.Riemann.Branches in
/-- Cell models with uniform certificates along the original subdivision lifted to its selected sheet.

The certificates retain the exact lifted clear path and the supplied differential, tying every model cell to its
corresponding path segment. -/
structure CertifiedSubdivision {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : ClearSheetContinuation.Subdivision.Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2)
    (subdivision : PreparedSubdivision segment within left owner) where
  /-- The ordered cell models of the certified subdivision. -/ cells : List CellModel
  /-- Uniform algebraic certificates along the original subdivision's sheet lift. -/ certificates :
    Curves.Hyperelliptic.Integration.Algebraic.Path.Basis.UniformPathCertificates curve differential cells
    (ClearPath.liftOnSheet sheet subdivision.toClearPath)

constructive_injectivity CertifiedSubdivision

open Purelib.Polynomial in
open Purelib.Riemann.Branches in
open Purelib.Riemann.Integration in
/-- A dependent family retaining one center state for each original subdivision step.

The terminal subdivision carries `Unit`; each nonterminal step carries its exact edge center and the remaining
subdivision's center family. -/
@[expose] def CenterStates {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : ClearSheetContinuation.Subdivision.Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) :
    (subdivision : PreparedSubdivision segment within left owner) -> Type
  | .stop _ _ => Unit
  | .next left owner request cached ordered small remaining =>
      let head := edgeOfStep curve differential segment within left owner
        request cached ordered small sheet
      PreparedConstantModels.PreparedEdge.CenterState head ×
        CenterStates curve differential sheet remaining

set_option genInjectivity false in
open Purelib.Riemann.Integration in
/-- A prepared edge together with its exact retained center state.

The center state is indexed by the stored edge, so its coefficient cache and
root observations belong to that edge and its original preparation. -/
structure CenteredEdge {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus) where
  /-- The original prepared differential edge. -/ edge : PreparedEdge curve differential
  /-- The exact retained center state of that edge. -/ center : PreparedConstantModels.PreparedEdge.CenterState edge

constructive_injectivity CenteredEdge

namespace CenteredEdge

/-- The constant cell model using the edge's retained center value. -/
@[expose] def model {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (centered : CenteredEdge curve differential) : CellModel :=
  centered.edge.centeredModel centered.center

set_option genInjectivity false in
/-- Replacement cached coefficient and denominator values certified at the original center state.

The denominator remains possible at that exact state, and the coefficient value is the original numerator divided by the
retained denominator. -/
structure RecacheCertificate {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (centered : CenteredEdge curve differential) where
  /-- The supplied replacement cached coefficient value. -/ value : Gaussian
  /-- The supplied replacement cached denominator value. -/ denominator : Gaussian
  /-- The denominator is possible at the original center's exact denominator state. -/ denominatorPossible :
    (centered.edge.sheetValue 0
      centered.edge.baseInside).value.name.process.Possible
        centered.center.state.2 denominator
  /-- The supplied coefficient value is the original numerator divided by the supplied denominator. -/ valueEq :
    value = centered.edge.point 0 ^ differential.exponent / denominator

constructive_injectivity RecacheCertificate

namespace RecacheCertificate

/-- Recache the original center state with the certificate's actual value and denominator. -/
@[expose] def center {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {centered : CenteredEdge curve differential}
    (certificate : RecacheCertificate centered) :=
  centered.center.recache certificate.value certificate.denominator
    certificate.denominatorPossible certificate.valueEq

/-- The constant cell model using the certificate's recached center value. -/
@[expose] def model {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {centered : CenteredEdge curve differential}
    (certificate : RecacheCertificate centered) : CellModel :=
  centered.edge.centeredModel certificate.center

/-- Recaching preserves the cell's original weighted error allowance. -/
@[simp] theorem model_weightedAllowance {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {centered : CenteredEdge curve differential}
    (certificate : RecacheCertificate centered) :
    certificate.model.weightedAllowance = centered.model.weightedAllowance :=
  rfl

open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Certify the recached cell as a one-cell constant refinement of the original centered model.

The comparison retains the actual change in cached values and the exact unchanged displacement. -/
@[expose] def partitionCertificate {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {centered : CenteredEdge curve differential}
    (certificate : RecacheCertificate centered) :
    Basic.PathModel.ConstantPartitionCertificate
      centered.model
      (Basic.PathModel.mk [certificate.model]) :=
  centered.edge.centeredModelRecachePartitionCertificate centered.center
    certificate.value certificate.denominator certificate.denominatorPossible
      certificate.valueEq

end RecacheCertificate

/-- The dyadic geometric lower estimate for the real coordinate of the centered integral sample. -/
@[expose] def integralRealLower {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (centered : CenteredEdge curve differential) : Coordinate :=
  centered.edge.centeredModelIntegralRealDyadicLower centered.center

/-- For exponent zero, the retained geometric estimate is below the real coordinate of the actual centered integral
sample. -/
theorem integralRealLower_le {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (centered : CenteredEdge curve differential)
    (exponentZero : differential.exponent = 0) :
    centered.integralRealLower <= centered.model.integralSample.re :=
  centered.edge.centeredModelIntegralRealDyadicLower_le centered.center
    exponentZero

/-- The dyadic geometric lower estimate for the negated real coordinate of the centered integral sample. -/
@[expose] def negatedIntegralRealLower {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (centered : CenteredEdge curve differential) : Coordinate :=
  centered.edge.geometricNegatedIntegralRealDyadicLower

/-- For exponent zero, the retained geometric estimate is below the negated real coordinate of the actual centered
integral sample. -/
theorem negatedIntegralRealLower_le {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (centered : CenteredEdge curve differential)
    (exponentZero : differential.exponent = 0) :
    centered.negatedIntegralRealLower <= -centered.model.integralSample.re :=
  centered.edge.geometricNegatedIntegralRealDyadicLower_le centered.center
    exponentZero

/-- The dyadic geometric lower estimate for the scalar projection onto the supplied Gaussian direction of the centered
integral sample. -/
@[expose] def directionalIntegralLower {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (centered : CenteredEdge curve differential)
    (direction : Gaussian) : Coordinate :=
  centered.edge.geometricDirectionalIntegralDyadicLower direction

/-- For exponent zero, the retained geometric estimate is below the scalar projection onto the supplied Gaussian
direction of the actual centered integral sample. -/
theorem directionalIntegralLower_le {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (centered : CenteredEdge curve differential)
    (direction : Gaussian)
    (exponentZero : differential.exponent = 0) :
    centered.directionalIntegralLower direction <=
      direction.re * centered.model.integralSample.re +
        direction.im * centered.model.integralSample.im :=
  centered.edge.geometricDirectionalIntegralDyadicLower_le centered.center
    direction exponentZero

/-- The dyadic lower estimate from the retained denominator projection box for the real coordinate of the centered
integral sample. -/
@[expose] def ballIntegralRealLower {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (centered : CenteredEdge curve differential) : Coordinate :=
  centered.edge.centeredBallIntegralRealDyadicLower centered.center

/-- For exponent zero, the retained denominator projection-box estimate is below the real coordinate of the actual
integral sample. -/
theorem ballIntegralRealLower_le {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (centered : CenteredEdge curve differential)
    (exponentZero : differential.exponent = 0) :
    centered.ballIntegralRealLower <= centered.model.integralSample.re :=
  centered.edge.centeredBallIntegralRealDyadicLower_le centered.center
    exponentZero

/-- The dyadic lower estimate from the retained denominator projection box for the negated real coordinate of the
centered integral sample. -/
@[expose] def ballNegatedIntegralRealLower {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (centered : CenteredEdge curve differential) : Coordinate :=
  centered.edge.centeredBallNegatedIntegralRealDyadicLower centered.center

/-- For exponent zero, the retained denominator projection-box estimate is below the negated real coordinate of the
actual integral sample. -/
theorem ballNegatedIntegralRealLower_le {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (centered : CenteredEdge curve differential)
    (exponentZero : differential.exponent = 0) :
    centered.ballNegatedIntegralRealLower <=
      -centered.model.integralSample.re :=
  centered.edge.centeredBallNegatedIntegralRealDyadicLower_le centered.center
    exponentZero

/-- The dyadic lower estimate from the retained denominator projection box for the scalar projection onto the supplied
Gaussian direction of the centered integral sample. -/
@[expose] def ballDirectionalIntegralLower {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (centered : CenteredEdge curve differential)
    (direction : Gaussian) : Coordinate :=
  centered.edge.centeredBallDirectionalIntegralDyadicLower centered.center
    direction

/-- For exponent zero, the retained denominator projection-box estimate is below the scalar projection onto the supplied
Gaussian direction of the actual integral sample. -/
theorem ballDirectionalIntegralLower_le {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (centered : CenteredEdge curve differential)
    (direction : Gaussian)
    (exponentZero : differential.exponent = 0) :
    centered.ballDirectionalIntegralLower direction <=
      direction.re * centered.model.integralSample.re +
        direction.im * centered.model.integralSample.im :=
  centered.edge.centeredBallDirectionalIntegralDyadicLower_le centered.center
    direction exponentZero

open Purelib.Riemann.Branches in
/-- The original left and request endpoint of the centered edge. -/
@[expose] def parameterEdge {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (centered : CenteredEdge curve differential) :
    ClearSheetContinuation.Subdivision.ParameterEdge :=
  { left := centered.edge.left
    right := centered.edge.request.endpoint }

open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Riemann.Branches in
open Purelib.Riemann.Integration in
/-- The centered model displacement is the original segment's endpoint difference. -/
theorem model_displacement {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (centered : CenteredEdge curve differential) :
    centered.model.displacement =
      centered.edge.segment.pointAt centered.edge.request.endpoint.parameter -
        centered.edge.segment.pointAt centered.edge.left.parameter := by
  unfold model PreparedConstantModels.PreparedEdge.centeredModel
    Basic.CellModel.displacement
  change centered.edge.point 1 - centered.edge.point 0 = _
  have pointZero : centered.edge.point 0 =
      centered.edge.segment.pointAt centered.edge.left.parameter := by
    change
      (PreparedModels.edge curve centered.edge.segment
        centered.edge.within centered.edge.left
          centered.edge.request).pointAt 0 = _
    unfold PreparedModels.edge
    simpa only [PreparedSheetContinuation.parameterAt_zero] using
      (PreparedSheetContinuation.pointAt_parameterAt
        centered.edge.segment centered.edge.within centered.edge.left
          centered.edge.request 0).symm
  have pointOne : centered.edge.point 1 =
      centered.edge.segment.pointAt
        centered.edge.request.endpoint.parameter := by
    change
      (PreparedModels.edge curve centered.edge.segment
        centered.edge.within centered.edge.left
          centered.edge.request).pointAt 1 = _
    unfold PreparedModels.edge
    simpa only [PreparedSheetContinuation.parameterAt_one] using
      (PreparedSheetContinuation.pointAt_parameterAt
        centered.edge.segment centered.edge.within centered.edge.left
          centered.edge.request 1).symm
  rw [pointZero, pointOne]

end CenteredEdge

set_option genInjectivity false in
/-- A dependent list of recache certificates for the original ordered centered edges.

Each constructor retains the exact head certificate and the remaining original edge list, so recaching cannot reorder or
replace the edge owners. -/
inductive CenteredPathRecache {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} :
    List (CenteredEdge curve differential) -> Type
  /-- The empty recache certificate for the empty original edge list. -/ | nil : CenteredPathRecache []
  /-- Retain the exact head recache certificate and the recache certificates for the original tail. -/ | cons {head :
    CenteredEdge curve differential}
      {tail : List (CenteredEdge curve differential)}
      (certificate : head.RecacheCertificate)
      (remaining : CenteredPathRecache tail) :
      CenteredPathRecache (head :: tail)

constructive_injectivity CenteredPathRecache

namespace CenteredPathRecache

/-- Append recache certificates along the concatenation of their original edge lists. -/
@[expose] def append {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} :
    {first second : List (CenteredEdge curve differential)} ->
      CenteredPathRecache first -> CenteredPathRecache second ->
        CenteredPathRecache (first ++ second)
  | [], _, .nil, second => second
  | _ :: _, _, .cons certificate remaining, second =>
      .cons certificate (remaining.append second)

/-- Read the ordered recached cell models from their retained certificates. -/
@[expose] def models {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} :
    {edges : List (CenteredEdge curve differential)} ->
      CenteredPathRecache edges -> List CellModel
  | [], .nil => []
  | _ :: _, .cons certificate remaining =>
      certificate.model :: remaining.models

/-- Reading recached models commutes with concatenating their certificates. -/
@[simp] theorem models_append {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} :
    forall {first second : List (CenteredEdge curve differential)}
      (left : CenteredPathRecache first)
      (right : CenteredPathRecache second),
      (left.append right).models = left.models ++ right.models
  | [], _, .nil, _ => rfl
  | _ :: _, _, .cons _ remaining, right => by
      simp only [append, models, List.cons_append]
      rw [remaining.models_append right]

open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Compose the retained one-cell recache certificates into a constant path refinement. -/
@[expose] def toConstantPathRefinement {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} :
    {edges : List (CenteredEdge curve differential)} ->
      (recache : CenteredPathRecache edges) ->
      Basic.PathModel.ConstantPathRefinement
        (edges.map CenteredEdge.model) recache.models
  | [], .nil => .nil
  | _ :: _, .cons certificate remaining =>
      .cons certificate.partitionCertificate
        remaining.toConstantPathRefinement

/-- The path model made from the actual recached cells. -/
@[expose] def literalModel {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {edges : List (CenteredEdge curve differential)}
    (recache : CenteredPathRecache edges) : PathModel :=
  ⟨recache.models⟩

/-- The path model made from the original centered edges, in order. -/
@[expose] def canonicalModel {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (edges : List (CenteredEdge curve differential)) : PathModel :=
  ⟨edges.map CenteredEdge.model⟩

/-- Recaching retains exactly one cell per original centered edge. -/
@[simp] theorem models_length {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} :
    forall {edges : List (CenteredEdge curve differential)}
      (recache : CenteredPathRecache edges),
      recache.models.length = edges.length
  | [], .nil => rfl
  | _ :: _, .cons _ remaining => by
      simp only [models, List.length_cons]
      rw [remaining.models_length]

/-- Recaching preserves the total of the original cells' weighted error allowances. -/
theorem totalWeightedAllowance_eq {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} :
    forall {edges : List (CenteredEdge curve differential)}
      (recache : CenteredPathRecache edges),
      recache.literalModel.totalWeightedAllowance =
        (canonicalModel edges).totalWeightedAllowance
  | [], .nil => rfl
  | head :: tail, .cons certificate remaining => by
      change certificate.model.weightedAllowance +
          remaining.literalModel.totalWeightedAllowance =
        head.model.weightedAllowance +
          (canonicalModel tail).totalWeightedAllowance
      rw [certificate.model_weightedAllowance,
        remaining.totalWeightedAllowance_eq]

open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Recaching preserves the path's aggregate error allowance.

The recache keeps one model per retained edge and preserves total weighted
allowance. Those two scalar equalities identify the aggregate allowance. -/
theorem aggregateAllowance_eq {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {edges : List (CenteredEdge curve differential)}
    (recache : CenteredPathRecache edges) :
    recache.literalModel.aggregateAllowance =
      (canonicalModel edges).aggregateAllowance := by
  unfold Basic.PathModel.aggregateAllowance
  rw [recache.totalWeightedAllowance_eq]
  change (recache.models.length : Coordinate) * _ =
    ((edges.map CenteredEdge.model).length : Coordinate) * _
  rw [recache.models_length, Map.length_map]

open Purelib.Integration.Polynomial.Gaussian.Path.ConstantRefinement.PathModel.ConstantPathRefinement
  (integral_difference_le)
open Purelib.Data.Gaussian.Norm.Basic (normSq_eq_canonical)

open Purelib.Data.Gaussian in
/-- The aggregate allowance bounds the squared difference between recached and original path integrals.

The estimate uses the retained constant path refinement, preserving the exact ordered cells and their individual recache
comparisons. -/
theorem integralDifference_le {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {edges : List (CenteredEdge curve differential)}
    (recache : CenteredPathRecache edges) :
    Data.Gaussian.Norm.Basic.normSq
        (recache.literalModel.integralSample -
          (canonicalModel edges).integralSample) <=
      recache.literalModel.aggregateAllowance := by
  have scalar := integral_difference_le recache.toConstantPathRefinement
  rw [← normSq_eq_canonical] at scalar
  exact scalar

/-- A nonnegative movement bound transfers a real lower bound from the recached integral to the original integral.

The recached aggregate allowance must be at most the square of that movement bound; the movement is subtracted from the
actual recached real reading. -/
theorem literalRealLower_le_canonical {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {edges : List (CenteredEdge curve differential)}
    (recache : CenteredPathRecache edges)
    (movement : Coordinate) (movementNonnegative : 0 <= movement)
    (allowanceLe : recache.literalModel.aggregateAllowance <= movement ^ 2) :
    recache.literalModel.integralSample.re - movement <=
      (canonicalModel edges).integralSample.re :=
  real_sub_radius_le_of_normSq_sub_le movementNonnegative
    (recache.integralDifference_le.trans allowanceLe)

/-- Transfer the recached real reading using a squared movement bound on the original aggregate allowance. -/
theorem literalRealLower_le_canonical_of_canonicalAllowance {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {edges : List (CenteredEdge curve differential)}
    (recache : CenteredPathRecache edges)
    (movement : Coordinate) (movementNonnegative : 0 <= movement)
    (allowanceLe : (canonicalModel edges).aggregateAllowance <= movement ^ 2) :
    recache.literalModel.integralSample.re - movement <=
      (canonicalModel edges).integralSample.re :=
  recache.literalRealLower_le_canonical movement movementNonnegative (by
    rw [recache.aggregateAllowance_eq]
    exact allowanceLe)

set_option genInjectivity false in
/-- A positive real lower bound retained with an actual recache and its paid movement bound.

The original aggregate allowance is bounded by the square of a nonnegative movement; the stated positive lower bound
lies below the recached real integral after that movement is subtracted. -/
structure PositiveLiteralRealLowerCertificate {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (edges : List (CenteredEdge curve differential)) where
  /-- The actual recache certificates for the original ordered edge list. -/ recache : CenteredPathRecache edges
  /-- The retained real movement bound between recached and original integral samples. -/ movement : Coordinate
  /-- The retained movement bound is nonnegative. -/ movementNonnegative : 0 <= movement
  /-- The original aggregate allowance is at most the retained movement squared. -/ allowanceLe : (canonicalModel
    edges).aggregateAllowance <= movement ^ 2
  /-- The retained real lower bound after paying the movement. -/ lower : Coordinate
  /-- The retained lower bound is strictly positive. -/ lowerPositive : 0 < lower
  /-- The bound lies below the actual recached real integral after subtracting movement. -/ literalLower : lower <=
    recache.literalModel.integralSample.re - movement

constructive_injectivity PositiveLiteralRealLowerCertificate

namespace PositiveLiteralRealLowerCertificate

/-- The retained positive lower bound is below the original path integral's real coordinate. -/
theorem lower_le_canonical {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {edges : List (CenteredEdge curve differential)}
    (certificate : PositiveLiteralRealLowerCertificate edges) :
    certificate.lower <= (canonicalModel edges).integralSample.re :=
  certificate.literalLower.trans
    (certificate.recache.literalRealLower_le_canonical_of_canonicalAllowance
      certificate.movement certificate.movementNonnegative
        certificate.allowanceLe)

/-- The original path integral's real coordinate is positive under the retained recache certificate. -/
theorem canonical_positive {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {edges : List (CenteredEdge curve differential)}
    (certificate : PositiveLiteralRealLowerCertificate edges) :
    0 < (canonicalModel edges).integralSample.re :=
  certificate.lowerPositive.trans_le certificate.lower_le_canonical

end PositiveLiteralRealLowerCertificate

end CenteredPathRecache

/-- Sum the geometric lower estimates for the real coordinate over the original ordered centered edges. -/
@[expose] def centeredEdgesIntegralRealLower {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (edges : List (CenteredEdge curve differential)) : Coordinate :=
  edges.foldr (fun edge total => edge.integralRealLower + total) 0

open Purelib.Data.Rat in
/-- The sum of geometric estimates for the real coordinate splits over concatenated edge lists.

Structural recursion follows the left edge list and preserves each geometric
lower estimate. Associativity separates the ordered sums for the two lists. -/
theorem centeredEdgesIntegralRealLower_append {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (first second : List (CenteredEdge curve differential)) :
    centeredEdgesIntegralRealLower (first ++ second) =
      centeredEdgesIntegralRealLower first +
        centeredEdgesIntegralRealLower second := by
  induction first with
  | nil =>
      change centeredEdgesIntegralRealLower second =
        0 + centeredEdgesIntegralRealLower second
      exact (Fraction.Field.zero_add _).symm
  | cons edge remaining inductionHypothesis =>
      change edge.integralRealLower +
          centeredEdgesIntegralRealLower (remaining ++ second) =
        (edge.integralRealLower + centeredEdgesIntegralRealLower remaining) +
          centeredEdgesIntegralRealLower second
      exact (congrArg (fun total => edge.integralRealLower + total)
        inductionHypothesis).trans (Fraction.Field.add_assoc _ _ _).symm

open Purelib.Integration.Polynomial.Gaussian.Path in
/-- For exponent zero, the sum of the retained geometric estimates is below the real coordinate of the path integral
sample. -/
theorem centeredEdgesIntegralRealLower_le {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (exponentZero : differential.exponent = 0) :
    forall edges : List (CenteredEdge curve differential),
      centeredEdgesIntegralRealLower edges <=
        (Basic.PathModel.mk
          (edges.map CenteredEdge.model)).integralSample.re
  | [] => by
      unfold centeredEdgesIntegralRealLower
        Basic.PathModel.integralSample
      rfl
  | edge :: remaining => by
      unfold centeredEdgesIntegralRealLower
      simp only [List.foldr_cons, List.map_cons,
        Basic.PathModel.integralSample]
      exact add_le_add (edge.integralRealLower_le exponentZero)
        (centeredEdgesIntegralRealLower_le exponentZero remaining)

/-- Sum the geometric lower estimates for the negated real coordinate over the original ordered centered edges. -/
@[expose] def centeredEdgesNegatedIntegralRealLower {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (edges : List (CenteredEdge curve differential)) : Coordinate :=
  edges.foldr (fun edge total => edge.negatedIntegralRealLower + total) 0

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- For exponent zero, the sum of the retained geometric estimates is below the negated real coordinate of the path
integral sample. -/
theorem centeredEdgesNegatedIntegralRealLower_le {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (exponentZero : differential.exponent = 0) :
    forall edges : List (CenteredEdge curve differential),
      centeredEdgesNegatedIntegralRealLower edges <=
        -(Basic.PathModel.mk
          (edges.map CenteredEdge.model)).integralSample.re
  | [] => by
      unfold centeredEdgesNegatedIntegralRealLower
        Basic.PathModel.integralSample
      rfl
  | edge :: remaining => by
      unfold centeredEdgesNegatedIntegralRealLower
      simp only [List.foldr_cons, List.map_cons,
        Basic.PathModel.integralSample]
      have combined := add_le_add
        (edge.negatedIntegralRealLower_le exponentZero)
        (centeredEdgesNegatedIntegralRealLower_le exponentZero remaining)
      unfold centeredEdgesNegatedIntegralRealLower at combined
      unfold Basic.PathModel.integralSample at combined
      rw [Basic.add_re]
      exact combined.trans_eq (by ring1)

/-- Sum the geometric lower estimates for the scalar projection onto the supplied Gaussian direction over the original
ordered centered edges. -/
@[expose] def centeredEdgesDirectionalIntegralLower {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (direction : Gaussian)
    (edges : List (CenteredEdge curve differential)) : Coordinate :=
  edges.foldr (fun edge total =>
    edge.directionalIntegralLower direction + total) 0

open Purelib.Data.Rat in
/-- The sum of geometric estimates for the scalar projection onto the supplied Gaussian direction splits over
concatenated edge lists.

The direction is fixed throughout both edge lists. Structural recursion and
scalar associativity split the sum without changing any directional estimate. -/
theorem centeredEdgesDirectionalIntegralLower_append {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (direction : Gaussian)
    (first second : List (CenteredEdge curve differential)) :
    centeredEdgesDirectionalIntegralLower direction (first ++ second) =
      centeredEdgesDirectionalIntegralLower direction first +
        centeredEdgesDirectionalIntegralLower direction second := by
  induction first with
  | nil =>
      change centeredEdgesDirectionalIntegralLower direction second =
        0 + centeredEdgesDirectionalIntegralLower direction second
      exact (Fraction.Field.zero_add _).symm
  | cons edge remaining inductionHypothesis =>
      change edge.directionalIntegralLower direction +
          centeredEdgesDirectionalIntegralLower direction (remaining ++ second) =
        (edge.directionalIntegralLower direction +
          centeredEdgesDirectionalIntegralLower direction remaining) +
          centeredEdgesDirectionalIntegralLower direction second
      exact (congrArg (fun total => edge.directionalIntegralLower direction + total)
        inductionHypothesis).trans (Fraction.Field.add_assoc _ _ _).symm

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- For exponent zero, the sum of the retained geometric estimates is below the scalar projection onto the supplied
Gaussian direction of the path integral sample. -/
theorem centeredEdgesDirectionalIntegralLower_le {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (direction : Gaussian)
    (exponentZero : differential.exponent = 0) :
    forall edges : List (CenteredEdge curve differential),
      centeredEdgesDirectionalIntegralLower direction edges <=
        direction.re *
            (Basic.PathModel.mk
              (edges.map CenteredEdge.model)).integralSample.re +
          direction.im *
            (Basic.PathModel.mk
              (edges.map CenteredEdge.model)).integralSample.im
  | [] => by
      unfold centeredEdgesDirectionalIntegralLower
        Basic.PathModel.integralSample
      simp only [List.map_nil, List.foldr_nil,
        Basic.zero_re,
        Basic.zero_im,
        Fraction.Field.mul_zero_direct, zero_add]
      exact (le_refl (0 : Coordinate))
  | edge :: remaining => by
      unfold centeredEdgesDirectionalIntegralLower
      simp only [List.foldr_cons, List.map_cons,
        Basic.PathModel.integralSample,
        Basic.add_re,
        Basic.add_im]
      have combined := add_le_add
        (edge.directionalIntegralLower_le direction exponentZero)
        (centeredEdgesDirectionalIntegralLower_le direction exponentZero
          remaining)
      unfold centeredEdgesDirectionalIntegralLower at combined
      unfold Basic.PathModel.integralSample at combined
      exact combined.trans_eq (by ring1)

/-- Sum the retained denominator projection-box lower estimates for the real coordinate over the original ordered
centered edges. -/
@[expose] def centeredEdgesBallIntegralRealLower {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (edges : List (CenteredEdge curve differential)) : Coordinate :=
  edges.foldr (fun edge total => edge.ballIntegralRealLower + total) 0

open Purelib.Integration.Polynomial.Gaussian.Path in
/-- For exponent zero, the sum of the retained retained denominator projection-box estimates is below the real
coordinate of the path integral sample. -/
theorem centeredEdgesBallIntegralRealLower_le {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (exponentZero : differential.exponent = 0) :
    forall edges : List (CenteredEdge curve differential),
      centeredEdgesBallIntegralRealLower edges <=
        (Basic.PathModel.mk
          (edges.map CenteredEdge.model)).integralSample.re
  | [] => by
      unfold centeredEdgesBallIntegralRealLower
        Basic.PathModel.integralSample
      rfl
  | edge :: remaining => by
      unfold centeredEdgesBallIntegralRealLower
      simp only [List.foldr_cons, List.map_cons,
        Basic.PathModel.integralSample]
      exact add_le_add (edge.ballIntegralRealLower_le exponentZero)
        (centeredEdgesBallIntegralRealLower_le exponentZero remaining)

/-- Sum the retained denominator projection-box lower estimates for the negated real coordinate over the original
ordered centered edges. -/
@[expose] def centeredEdgesBallNegatedIntegralRealLower {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (edges : List (CenteredEdge curve differential)) : Coordinate :=
  edges.foldr (fun edge total => edge.ballNegatedIntegralRealLower + total) 0

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- For exponent zero, the sum of the retained retained denominator projection-box estimates is below the negated real
coordinate of the path integral sample. -/
theorem centeredEdgesBallNegatedIntegralRealLower_le {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (exponentZero : differential.exponent = 0) :
    forall edges : List (CenteredEdge curve differential),
      centeredEdgesBallNegatedIntegralRealLower edges <=
        -(Basic.PathModel.mk
          (edges.map CenteredEdge.model)).integralSample.re
  | [] => by
      unfold centeredEdgesBallNegatedIntegralRealLower
        Basic.PathModel.integralSample
      rfl
  | edge :: remaining => by
      unfold centeredEdgesBallNegatedIntegralRealLower
      simp only [List.foldr_cons, List.map_cons,
        Basic.PathModel.integralSample]
      have combined := add_le_add
        (edge.ballNegatedIntegralRealLower_le exponentZero)
        (centeredEdgesBallNegatedIntegralRealLower_le exponentZero remaining)
      unfold centeredEdgesBallNegatedIntegralRealLower at combined
      unfold Basic.PathModel.integralSample at combined
      rw [Basic.add_re]
      exact combined.trans_eq (by ring1)

/-- Sum the retained denominator projection-box lower estimates for the scalar projection onto the supplied Gaussian
direction over the original ordered centered edges. -/
@[expose] def centeredEdgesBallDirectionalIntegralLower {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (direction : Gaussian)
    (edges : List (CenteredEdge curve differential)) : Coordinate :=
  edges.foldr (fun edge total =>
    edge.ballDirectionalIntegralLower direction + total) 0

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- For exponent zero, the sum of the retained retained denominator projection-box estimates is below the scalar
projection onto the supplied Gaussian direction of the path integral sample. -/
theorem centeredEdgesBallDirectionalIntegralLower_le {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (direction : Gaussian)
    (exponentZero : differential.exponent = 0) :
    forall edges : List (CenteredEdge curve differential),
      centeredEdgesBallDirectionalIntegralLower direction edges <=
        direction.re *
            (Basic.PathModel.mk
              (edges.map CenteredEdge.model)).integralSample.re +
          direction.im *
            (Basic.PathModel.mk
              (edges.map CenteredEdge.model)).integralSample.im
  | [] => by
      unfold centeredEdgesBallDirectionalIntegralLower
        Basic.PathModel.integralSample
      simp only [List.map_nil, List.foldr_nil,
        Basic.zero_re,
        Basic.zero_im,
        Fraction.Field.mul_zero_direct, zero_add]
      exact (le_refl (0 : Coordinate))
  | edge :: remaining => by
      unfold centeredEdgesBallDirectionalIntegralLower
      simp only [List.foldr_cons, List.map_cons,
        Basic.PathModel.integralSample,
        Basic.add_re,
        Basic.add_im]
      have combined := add_le_add
        (edge.ballDirectionalIntegralLower_le direction exponentZero)
        (centeredEdgesBallDirectionalIntegralLower_le direction exponentZero
          remaining)
      unfold centeredEdgesBallDirectionalIntegralLower at combined
      unfold Basic.PathModel.integralSample at combined
      exact combined.trans_eq (by ring1)

section
open Purelib.Polynomial
/-- Sum the geometric lower estimates for the real coordinate along the original prepared subdivision.

The recursion uses the exact cached step geometry and the original remaining subdivision; no center-state selection is
required. -/
@[expose] def preparedSubdivisionIntegralRealLower {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) :
    PreparedSubdivision segment within left owner -> Coordinate
  | .stop _ _ => 0
  | .next current owner request cached ordered small remaining =>
      let edge := edgeOfStep curve differential segment within current owner
        request cached ordered small sheet
      edge.geometricIntegralRealDyadicLower +
        preparedSubdivisionIntegralRealLower curve differential sheet remaining

/-- Sum the geometric lower estimates for the negated real coordinate along the original prepared subdivision.

The recursion uses the exact cached step geometry and the original remaining subdivision; no center-state selection is
required. -/
@[expose] def preparedSubdivisionNegatedIntegralRealLower {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) :
    PreparedSubdivision segment within left owner -> Coordinate
  | .stop _ _ => 0
  | .next current owner request cached ordered small remaining =>
      let edge := edgeOfStep curve differential segment within current owner
        request cached ordered small sheet
      edge.geometricNegatedIntegralRealDyadicLower +
        preparedSubdivisionNegatedIntegralRealLower curve differential sheet
          remaining

/-- Sum the geometric lower estimates for the scalar projection onto the supplied Gaussian direction along the original
prepared subdivision.

The recursion uses the exact cached step geometry and the original remaining subdivision; no center-state selection is
required. -/
@[expose] def preparedSubdivisionDirectionalIntegralLower {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) (direction : Gaussian) :
    PreparedSubdivision segment within left owner -> Coordinate
  | .stop _ _ => 0
  | .next current owner request cached ordered small remaining =>
      let edge := edgeOfStep curve differential segment within current owner
        request cached ordered small sheet
      edge.geometricDirectionalIntegralDyadicLower direction +
        preparedSubdivisionDirectionalIntegralLower curve differential sheet
          direction remaining

end

set_option genInjectivity false in
open Purelib.Riemann.Branches in
/-- A bounded parent-edge fraction realizing the exact current subdivision parameter.

The affine parameter equation retains the current endpoint rather than replacing it with a newly constructed coordinate.
-/
structure ParentPosition {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : PreparedEdge curve differential) (current : Endpoint) where
  /-- The exact parent-edge query fraction. -/ fraction : Coordinate
  /-- The retained query fraction belongs to the closed unit interval. -/ inside : (0 : Coordinate) <= fraction ∧
    fraction <= 1
  /-- The parent's affine parameter at the retained fraction equals the original current endpoint parameter. -/
    parameter_eq :
    PreparedSheetContinuation.parameterAt parent.left
      parent.request fraction = current.parameter

constructive_injectivity ParentPosition

namespace ParentPosition

open Purelib.Riemann.Branches in
open Purelib.Riemann.Integration in
open Purelib.Riemann.RootContinuation in
open Purelib.RootIsolation.SquareRoot.Clearance in
/-- Compare the parent's direct query owner with the direct subdivision owner at the same retained parameter.

The supplied direct-move clearance and position equation identify the radicand; cached query equations and reserved
transport preserve the original root identity. -/
@[expose] def directRootEquivalent {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {parent : PreparedEdge curve differential} {current : Endpoint}
    (position : ParentPosition parent current)
    (sourceCurrentSmall :
      PreparedSheetContinuation.Subdivision.DirectMoveSmall
        parent.segment parent.left
          (PreparedSheetContinuation.prepared parent.segment
            parent.left parent.owner parent.request) current) :
    NamedEquivalent
      (SquareRootTrackEquivalence.ownerRootName
        (parent.segment.pointAt_eval_ne_zero
          (PreparedSheetContinuation.parameterAt parent.left
            parent.request position.fraction)
          (PreparedSheetContinuation.parameterAt_inside parent.left
            parent.request parent.ordered position.fraction position.inside))
        (parent.directQueryOwner position.fraction position.inside))
      (SquareRootTrackEquivalence.ownerRootName
        (parent.segment.pointAt_eval_ne_zero current.parameter current.inside)
        (PreparedSheetContinuation.Subdivision.directOwnerAt
          parent.left
          (PreparedSheetContinuation.prepared parent.segment
            parent.left parent.owner parent.request)
          current sourceCurrentSmall)) := by
  cases current with
  | mk parameter currentInside =>
      cases position with
      | mk fraction inside parameterEq =>
          dsimp only at parameterEq
          subst parameter
          have cachedName_eq : parent.rootName fraction inside =
              SquareRootTrackEquivalence.ownerRootName
                (parent.segment.pointAt_eval_ne_zero
                  (PreparedSheetContinuation.parameterAt parent.left
                    parent.request fraction)
                  (PreparedSheetContinuation.parameterAt_inside
                    parent.left parent.request parent.ordered fraction inside))
                (ExactQuadraticOwnerClearance.reservedTransport
                  (PreparedSheetContinuation.prepared parent.segment
                    parent.left parent.owner parent.request)
                  (parent.segment.pointAt_eval_ne_zero
                    (PreparedSheetContinuation.parameterAt parent.left
                      parent.request fraction)
                    (PreparedSheetContinuation.parameterAt_inside
                      parent.left parent.request parent.ordered fraction inside))
                  (PreparedSheetContinuation.pointNormSmall
                    parent.segment parent.within parent.left parent.owner
                      parent.request parent.ordered parent.small fraction inside)
                  (PreparedSheetContinuation.transportReserve
                    parent.segment parent.left parent.request)) := by
            unfold PreparedConstantModels.PreparedEdge.rootName
            rw [PreparedSheetContinuation.CachedSource.eq_canonical
              parent.cached]
            unfold PreparedModels.rootAtCached
            apply
              PreparedSheetContinuation.reservedTransportRootName_proof_irrel
          have directName_eq :=
            parent.rootName_eq_directQueryOwnerRootName fraction inside
          have directToCanonical := directName_eq.symm.trans cachedName_eq
          rw [directToCanonical]
          exact
            (PreparedSheetContinuation.reservedTransportRootEquivalentGeneric
              (PreparedSheetContinuation.prepared parent.segment
                parent.left parent.owner parent.request)
              (parent.segment.pointAt_eval_ne_zero
                (PreparedSheetContinuation.parameterAt parent.left
                  parent.request fraction)
                (PreparedSheetContinuation.parameterAt_inside
                  parent.left parent.request parent.ordered fraction inside))
              sourceCurrentSmall.proof
              (PreparedSheetContinuation.transportReserve
                parent.segment parent.left parent.request)).symm

open Purelib.Riemann.Branches in
/-- A retained parent position supplies the original direct-move clearance certificate. -/
theorem directMoveSmall {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {parent : PreparedEdge curve differential} {current : Endpoint}
    (position : ParentPosition parent current) :
    PreparedSheetContinuation.Subdivision.DirectMoveSmall
      parent.segment parent.left
        (PreparedSheetContinuation.prepared parent.segment
          parent.left parent.owner parent.request) current := by
  constructor
  cases current with
  | mk parameter currentInside =>
      cases position with
      | mk fraction inside parameterEq =>
          dsimp only at parameterEq
          subst parameter
          exact PreparedSheetContinuation.pointNormSmall
            parent.segment parent.within parent.left parent.owner
              parent.request parent.ordered parent.small fraction inside

open Purelib.Data.Rat in
open Purelib.Riemann.Branches in
/-- Construct the exact parent fraction of an endpoint between a strictly ordered parent's endpoints.

The fraction is the original offset divided by the positive parent width, with explicit unit-interval bounds and its
affine parameter equation. -/
@[expose] def ofBetween {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {parent : PreparedEdge curve differential} {current : Endpoint}
    (proper : parent.left.parameter < parent.request.endpoint.parameter)
    (between : parent.left.parameter <= current.parameter ∧
      current.parameter <= parent.request.endpoint.parameter) :
    ParentPosition parent current := by
  let width := parent.request.endpoint.parameter - parent.left.parameter
  let offset := current.parameter - parent.left.parameter
  have widthPositive : 0 < width :=
    Fraction.Order.Arithmetic.sub_pos_direct proper
  have offsetNonnegative : 0 <= offset :=
    Fraction.Order.Arithmetic.sub_nonneg_direct between.1
  let fraction := offset / width
  have fractionNonnegative : 0 <= fraction :=
    Fraction.Order.Field.div_nonneg_direct offsetNonnegative
      widthPositive.le
  have offsetLeWidth : offset <= width :=
    Fraction.Order.Arithmetic.sub_le_sub_right_direct between.2
      parent.left.parameter
  have fractionLeOne : fraction <= 1 := by
    apply (Fraction.Order.Field.div_le_iff_pos widthPositive).2
    simpa only [Fraction.Field.one_mul] using offsetLeWidth
  exact
    { fraction := fraction
      inside := ⟨fractionNonnegative, fractionLeOne⟩
      parameter_eq := by
        rw [PreparedSheetContinuation.parameterAt_eq_affine]
        change parent.left.parameter + offset / width * width =
          current.parameter
        rw [Fraction.Field.div_mul_cancel_of_ne offset width
          widthPositive.ne']
        ring1 }

end ParentPosition

set_option genInjectivity false in
/-- A parent query and child base query with the same coordinate and equivalent retained root names.

The relation preserves both centered edges, the actual parent fraction and its bounds, and the child center already
supplied by the caller. -/
structure RootChildAt {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent child : CenteredEdge curve differential) where
  /-- The exact parent-edge query fraction. -/ fraction : Coordinate
  /-- The retained query fraction belongs to the closed unit interval. -/ inside : (0 : Coordinate) <= fraction ∧
    fraction <= 1
  /-- The parent query and child base query have exactly the same coordinate. -/ point_eq : parent.edge.point fraction =
    child.edge.point 0
  /-- Operational equivalence of the original parent query root and child base root names. -/ rootEquivalent :
    NamedEquivalent
    (parent.edge.rootName fraction inside)
    (child.edge.rootName 0 child.edge.baseInside)

constructive_injectivity RootChildAt

namespace RootChildAt

open Purelib.Riemann.Integration in
/-- Transfer retained root equivalence to the exact child coefficient comparison, preserving both centers. -/
@[expose] def toCenteredChildAt {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {parent child : CenteredEdge curve differential}
    (relation : RootChildAt parent child) :
    PreparedConstantModels.PreparedEdge.CenteredChildAt
      parent.edge parent.center :=
  PreparedConstantModels.PreparedEdge.CenteredChildAt.ofRootEquivalent
    parent.edge child.edge parent.center child.center relation.fraction
      relation.inside relation.point_eq relation.rootEquivalent

/-- The transferred child comparison retains the original child's centered model. -/
@[simp] theorem toCenteredChildAt_model {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {parent child : CenteredEdge curve differential}
    (relation : RootChildAt parent child) :
    relation.toCenteredChildAt.model = child.model := rfl

end RootChildAt

open Purelib.Approximation.Gaussian in
open Purelib.Riemann.Branches in
open Purelib.Riemann.Integration in
/-- Relate a supplied child step to its parent using the original direct-owner comparison.

The constructor retains the child center and cache. The position equation identifies the coordinates, while
direct-query, owner and base-query equivalences identify the original root names. -/
@[expose] def rootChildAtOfDirectStep {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : CenteredEdge curve differential)
    (current : Endpoint)
    (owner : Owner
      (curve.polynomial.eval (parent.edge.segment.pointAt current.parameter)))
    (request : StepRequest)
    (cached : PreparedSheetContinuation.CachedSource
      parent.edge.segment current owner request)
    (ordered : current.parameter <= request.endpoint.parameter)
    (childSmall : ClearSheetContinuation.variationBound
      parent.edge.segment current.parameter request.endpoint.parameter <
        (PreparedSheetContinuation.prepared parent.edge.segment
          current owner request).track.initial.clearance.bound)
    (center :
      PreparedConstantModels.PreparedEdge.CenterState
        (edgeOfStep curve differential parent.edge.segment parent.edge.within
          current owner request cached ordered childSmall parent.edge.sheet))
    (sourceCurrentSmall :
      PreparedSheetContinuation.Subdivision.DirectMoveSmall
        parent.edge.segment parent.edge.left
          (PreparedSheetContinuation.prepared parent.edge.segment
            parent.edge.left parent.edge.owner parent.edge.request) current)
    (currentEquivalent :
      PreparedSheetContinuation.Subdivision.RootEquivalentAt
        parent.edge.segment current
          (PreparedSheetContinuation.Subdivision.directOwnerAt
            parent.edge.left
            (PreparedSheetContinuation.prepared parent.edge.segment
              parent.edge.left parent.edge.owner parent.edge.request)
            current sourceCurrentSmall)
          owner)
    (position : ParentPosition parent.edge current) :
    RootChildAt parent
      { edge := edgeOfStep curve differential parent.edge.segment
          parent.edge.within current owner request cached ordered childSmall
            parent.edge.sheet
        center := center } := by
  let childEdge := edgeOfStep curve differential parent.edge.segment
    parent.edge.within current owner request cached ordered childSmall
      parent.edge.sheet
  let child : CenteredEdge curve differential :=
    { edge := childEdge
      center := center }
  have parentPoint : parent.edge.point position.fraction =
      parent.edge.segment.pointAt
        (PreparedSheetContinuation.parameterAt parent.edge.left
          parent.edge.request position.fraction) :=
    (PreparedSheetContinuation.pointAt_parameterAt
      parent.edge.segment parent.edge.within parent.edge.left
        parent.edge.request position.fraction).symm
  have childPoint : parent.edge.segment.pointAt current.parameter =
      childEdge.point 0 := by
    change parent.edge.segment.pointAt current.parameter =
      (PreparedModels.edge curve parent.edge.segment
        parent.edge.within current request).pointAt 0
    unfold PreparedModels.edge
    simpa only [PreparedSheetContinuation.parameterAt_zero] using
      PreparedSheetContinuation.pointAt_parameterAt
        parent.edge.segment parent.edge.within current request 0
  have pointEqual : parent.edge.point position.fraction = childEdge.point 0 :=
    parentPoint.trans ((congrArg parent.edge.segment.pointAt
      position.parameter_eq).trans childPoint)
  have queryToDirect := position.directRootEquivalent sourceCurrentSmall
  have directToOwner := currentEquivalent.toNamedEquivalent
  have ownerToChild := childEdge.ownerRootEquivalent_baseQuery
  exact
    { fraction := position.fraction
      inside := position.inside
      point_eq := pointEqual
      rootEquivalent := by
        rw [parent.edge.rootName_eq_directQueryOwnerRootName position.fraction
          position.inside]
        exact Equivalence.NamedEquivalent.trans queryToDirect
          (Equivalence.NamedEquivalent.trans directToOwner
            ownerToChild) }

set_option genInjectivity false in
/-- An ordered block of child edges, each related to the same retained parent by root equivalence.

Each nonempty block stores the comparison for its displayed head and the
remaining comparisons. Every entry refers to the same original parent. -/
inductive RootChildBlock {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : CenteredEdge curve differential) :
    List (CenteredEdge curve differential) -> Type
  /-- The empty child block at the retained parent. -/ | nil : RootChildBlock parent []
  /-- Prepend the actual child root comparison to the remaining child block at the same parent. -/ | cons {child :
    CenteredEdge curve differential}
      {children : List (CenteredEdge curve differential)}
      (head : RootChildAt parent child)
      (tail : RootChildBlock parent children) :
      RootChildBlock parent (child :: children)

constructive_injectivity RootChildBlock

namespace RootChildBlock

section
open Purelib.Riemann.Integration
/-- Read coefficient-level child comparisons from the retained root comparison block. -/
@[expose] def childAts {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {parent : CenteredEdge curve differential} :
    forall {children : List (CenteredEdge curve differential)},
      RootChildBlock parent children ->
        List
          (PreparedConstantModels.PreparedEdge.CenteredChildAt
            parent.edge parent.center)
  | [], .nil => []
  | _ :: _, .cons head tail => head.toCenteredChildAt :: tail.childAts

/-- The transferred child comparisons retain exactly the original ordered child models.

Each transferred head has the same model as its retained child edge. Scalar
list-constructor congruence preserves the ordered tail of those models. -/
@[simp] theorem childAts_models {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {parent : CenteredEdge curve differential} :
    forall {children : List (CenteredEdge curve differential)}
      (block : RootChildBlock parent children),
      block.childAts.map
          PreparedConstantModels.PreparedEdge.CenteredChildAt.model =
        children.map CenteredEdge.model
  | [], .nil => rfl
  | _ :: _, .cons head tail => by
      change head.toCenteredChildAt.model :: _ = head.toCenteredChildAt.model :: _
      exact congrArg (List.cons head.toCenteredChildAt.model) (childAts_models tail)

end

open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Riemann.Integration in
/-- Certify a child comparison block with the retained parent displacement.

The supplied displacement equality and the original root comparisons produce the constant partition certificate without
replacing any child model. -/
@[expose] def partitionCertificate {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {parent : CenteredEdge curve differential}
    {children : List (CenteredEdge curve differential)}
    (block : RootChildBlock parent children)
    (displacement_eq :
      Basic.PathModel.displacementSum
          (children.map CenteredEdge.model) = parent.model.displacement) :
    Basic.PathModel.ConstantPartitionCertificate
      parent.model
      (Basic.PathModel.comparisonBlock
        parent.model
        (Basic.PathModel.mk
          (children.map CenteredEdge.model))) := by
  have modelsEqual := block.childAts_models
  rw [← modelsEqual]
  exact
    PreparedConstantModels.PreparedEdge.CenteredChildAt.partitionCertificate
      block.childAts (by
        rw [modelsEqual]
        simpa only [CenteredEdge.model] using displacement_eq)

end RootChildBlock

set_option genInjectivity false in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- An ordered block refinement retaining each parent's root comparisons and total displacement equation.

Each constructor keeps the actual child block, its parent and its displacement equality before appending the remaining
refinement. -/
inductive CenteredEdgeRefinement {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} :
    List (CenteredEdge curve differential) ->
      List (CenteredEdge curve differential) -> Type
  /-- The empty refinement between the two empty edge lists. -/ | nil : CenteredEdgeRefinement [] []
  /-- Retain the original parent, its actual child block and displacement equality, then append the remaining
    refinement. -/ | cons
      (parent : CenteredEdge curve differential)
      {parents childEdges children : List (CenteredEdge curve differential)}
      (block : RootChildBlock parent childEdges)
      (displacement_eq :
        Basic.PathModel.displacementSum
            (childEdges.map CenteredEdge.model) = parent.model.displacement)
      (remaining : CenteredEdgeRefinement
        (curve := curve) (differential := differential) parents children) :
      CenteredEdgeRefinement (parent :: parents) (childEdges ++ children)

constructive_injectivity CenteredEdgeRefinement

namespace CenteredEdgeRefinement

set_option backward.match.sparseCases false in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Transfer retained root-block refinements to compatible constant path model refinements.

Each parent retains its original partition certificate and ordered child block.
Their model lists are concatenated in the same order as the edge refinement. -/
@[expose] def toCompatible {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} :
    forall {parents children : List (CenteredEdge curve differential)},
      CenteredEdgeRefinement parents children ->
        Basic.PathModel.CompatibleConstantPathRefinement
          (parents.map CenteredEdge.model) (children.map CenteredEdge.model)
  | [], [], .nil => .nil
  | _, _, .cons parent block displacement_eq remaining => by
      rw [List.map_cons, Map.map_append]
      exact .cons (block.partitionCertificate displacement_eq)
        (toCompatible remaining)

end CenteredEdgeRefinement

open Purelib.Polynomial in
open Purelib.Riemann.Branches in
/-- Pair each original subdivision step with its supplied dependent center state.

The resulting ordered edges retain the original owners, caches, requests and selected sheet. -/
@[expose] def centeredEdges {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : ClearSheetContinuation.Subdivision.Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) :
    (subdivision : PreparedSubdivision segment within left owner) ->
      CenterStates curve differential sheet subdivision ->
        List (CenteredEdge curve differential)
  | .stop _ _, _ => []
  | .next left owner request cached ordered small remaining, centers =>
      { edge := edgeOfStep curve differential segment within left owner request
          cached ordered small sheet
        center := centers.1 } ::
        centeredEdges curve differential sheet remaining centers.2

open Purelib.Polynomial in
open Purelib.Riemann.Integration in
/-- The geometric subdivision estimate for the real coordinate equals the corresponding centered-edge sum for every
retained center family. -/
theorem preparedSubdivisionIntegralRealLower_eq_centeredEdges
    {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) :
    forall (subdivision : PreparedSubdivision segment within left owner)
      (centers : CenterStates curve differential sheet subdivision),
      preparedSubdivisionIntegralRealLower curve differential sheet subdivision =
        centeredEdgesIntegralRealLower
          (centeredEdges curve differential sheet subdivision centers)
  | .stop _ _, _centers => rfl
  | .next current owner request cached ordered small remaining, centers => by
      simp only [preparedSubdivisionIntegralRealLower, centeredEdges,
        centeredEdgesIntegralRealLower, List.foldr_cons,
        CenteredEdge.integralRealLower,
        PreparedConstantModels.PreparedEdge.centeredModelIntegralRealDyadicLower]
      rw [preparedSubdivisionIntegralRealLower_eq_centeredEdges curve
        differential sheet remaining centers.2]
      rfl

open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Polynomial in
/-- For exponent zero, the geometric subdivision estimate is below the real coordinate of the path integral with the
supplied centers. -/
theorem preparedSubdivisionIntegralRealLower_le {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2)
    (subdivision : PreparedSubdivision segment within left owner)
    (centers : CenterStates curve differential sheet subdivision)
    (exponentZero : differential.exponent = 0) :
    preparedSubdivisionIntegralRealLower curve differential sheet subdivision <=
      (Basic.PathModel.mk
        ((centeredEdges curve differential sheet subdivision centers).map
          CenteredEdge.model)).integralSample.re := by
  rw [preparedSubdivisionIntegralRealLower_eq_centeredEdges curve differential
    sheet subdivision centers]
  exact centeredEdgesIntegralRealLower_le exponentZero _

open Purelib.Polynomial in
/-- The geometric subdivision estimate for the scalar projection onto the supplied Gaussian direction equals the
corresponding centered-edge sum for every retained center family. -/
theorem preparedSubdivisionDirectionalIntegralLower_eq_centeredEdges
    {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) (direction : Gaussian) :
    forall (subdivision : PreparedSubdivision segment within left owner)
      (centers : CenterStates curve differential sheet subdivision),
      preparedSubdivisionDirectionalIntegralLower curve differential sheet
          direction subdivision =
        centeredEdgesDirectionalIntegralLower direction
          (centeredEdges curve differential sheet subdivision centers)
  | .stop _ _, _centers => rfl
  | .next current owner request cached ordered small remaining, centers => by
      simp only [preparedSubdivisionDirectionalIntegralLower, centeredEdges,
        centeredEdgesDirectionalIntegralLower, List.foldr_cons,
        CenteredEdge.directionalIntegralLower]
      rw [preparedSubdivisionDirectionalIntegralLower_eq_centeredEdges curve
        differential sheet direction remaining centers.2]
      rfl

open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Polynomial in
/-- For exponent zero, the geometric subdivision estimate is below the scalar projection onto the supplied Gaussian
direction of the path integral with the supplied centers. -/
theorem preparedSubdivisionDirectionalIntegralLower_le {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) (direction : Gaussian)
    (subdivision : PreparedSubdivision segment within left owner)
    (centers : CenterStates curve differential sheet subdivision)
    (exponentZero : differential.exponent = 0) :
    preparedSubdivisionDirectionalIntegralLower curve differential sheet
        direction subdivision <=
      direction.re *
          (Basic.PathModel.mk
            ((centeredEdges curve differential sheet subdivision centers).map
              CenteredEdge.model)).integralSample.re +
        direction.im *
          (Basic.PathModel.mk
            ((centeredEdges curve differential sheet subdivision centers).map
              CenteredEdge.model)).integralSample.im := by
  rw [preparedSubdivisionDirectionalIntegralLower_eq_centeredEdges curve
    differential sheet direction subdivision centers]
  exact centeredEdgesDirectionalIntegralLower_le direction exponentZero _

open Purelib.Polynomial in
/-- The geometric subdivision estimate for the negated real coordinate equals the corresponding centered-edge sum for
every retained center family. -/
theorem preparedSubdivisionNegatedIntegralRealLower_eq_centeredEdges
    {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) :
    forall (subdivision : PreparedSubdivision segment within left owner)
      (centers : CenterStates curve differential sheet subdivision),
      preparedSubdivisionNegatedIntegralRealLower curve differential sheet
          subdivision =
        centeredEdgesNegatedIntegralRealLower
          (centeredEdges curve differential sheet subdivision centers)
  | .stop _ _, _centers => rfl
  | .next current owner request cached ordered small remaining, centers => by
      simp only [preparedSubdivisionNegatedIntegralRealLower, centeredEdges,
        centeredEdgesNegatedIntegralRealLower, List.foldr_cons,
        CenteredEdge.negatedIntegralRealLower]
      rw [preparedSubdivisionNegatedIntegralRealLower_eq_centeredEdges curve
        differential sheet remaining centers.2]
      rfl

open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Polynomial in
/-- For exponent zero, the geometric subdivision estimate is below the negated real coordinate of the path integral with
the supplied centers. -/
theorem preparedSubdivisionNegatedIntegralRealLower_le {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2)
    (subdivision : PreparedSubdivision segment within left owner)
    (centers : CenterStates curve differential sheet subdivision)
    (exponentZero : differential.exponent = 0) :
    preparedSubdivisionNegatedIntegralRealLower curve differential sheet
        subdivision <=
      -(Basic.PathModel.mk
        ((centeredEdges curve differential sheet subdivision centers).map
          CenteredEdge.model)).integralSample.re := by
  rw [preparedSubdivisionNegatedIntegralRealLower_eq_centeredEdges curve
    differential sheet subdivision centers]
  exact centeredEdgesNegatedIntegralRealLower_le exponentZero _

section
open Purelib.Polynomial
open Purelib.Riemann.Branches
/-- The centered edge list has exactly the original subdivision's step count. -/
@[simp] theorem centeredEdges_length {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : ClearSheetContinuation.Subdivision.Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) :
    forall (subdivision : PreparedSubdivision segment within left owner)
      (centers : CenterStates curve differential sheet subdivision),
      (centeredEdges curve differential sheet subdivision centers).length =
        subdivision.stepCount
  | .stop _ _, _ => rfl
  | .next left owner request cached ordered small remaining, centers => by
      simp only [centeredEdges, List.length_cons,
        PreparedSheetContinuation.Subdivision.stepCount_next]
      rw [centeredEdges_length curve differential sheet remaining centers.2]

/-- Every centered edge retains the original segment, including its dependent indices.

The subdivision constructor retains its segment as a dependent index. Each
head has that segment, and the same statement follows for the retained tail. -/
theorem centeredEdges_segment_heq {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : ClearSheetContinuation.Subdivision.Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) (subdivision : PreparedSubdivision segment within left owner)
    (centers : CenterStates curve differential sheet subdivision) :
    ∀ centered ∈ centeredEdges curve differential sheet subdivision centers,
      HEq centered.edge.segment segment := by
  induction subdivision with
  | stop endpoint owner =>
      intro centered membership
      change centered ∈ [] at membership
      cases membership
  | @next left owner request cached ordered small remaining induction =>
      intro centered membership
      change centered ∈ _ :: _ at membership
      rcases Membership.mem_cons.mp membership with equal | membership
      · subst centered
        rfl
      · exact induction centers.2 centered membership

/-- Each centered edge starts at its retained left parameter on the original segment.

Every step stores its left parameter in the centered edge. The head endpoint
equation and the corresponding retained-tail equation identify each start. -/
theorem centeredEdges_point_zero {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : ClearSheetContinuation.Subdivision.Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) (subdivision : PreparedSubdivision segment within left owner)
    (centers : CenterStates curve differential sheet subdivision) :
    ∀ centered ∈ centeredEdges curve differential sheet subdivision centers,
      centered.edge.point 0 =
        segment.pointAt centered.parameterEdge.left.parameter := by
  induction subdivision with
  | stop endpoint owner =>
      intro centered membership
      change centered ∈ [] at membership
      cases membership
  | @next left owner request cached ordered small remaining induction =>
      intro centered membership
      change centered ∈ _ :: _ at membership
      rcases Membership.mem_cons.mp membership with equal | membership
      · subst centered
        exact edgeOfStep_point_zero curve differential segment within left owner
          request cached ordered small sheet
      · exact induction centers.2 centered membership

/-- Each centered edge ends at its retained right parameter on the original segment.

Every step stores its requested endpoint in the centered edge. The head
endpoint equation and the retained-tail equation identify each finish. -/
theorem centeredEdges_point_one {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : ClearSheetContinuation.Subdivision.Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) (subdivision : PreparedSubdivision segment within left owner)
    (centers : CenterStates curve differential sheet subdivision) :
    ∀ centered ∈ centeredEdges curve differential sheet subdivision centers,
      centered.edge.point 1 =
        segment.pointAt centered.parameterEdge.right.parameter := by
  induction subdivision with
  | stop endpoint owner =>
      intro centered membership
      change centered ∈ [] at membership
      cases membership
  | @next left owner request cached ordered small remaining induction =>
      intro centered membership
      change centered ∈ _ :: _ at membership
      rcases Membership.mem_cons.mp membership with equal | membership
      · subst centered
        exact edgeOfStep_point_one curve differential segment within left owner
          request cached ordered small sheet
      · exact induction centers.2 centered membership

/-- Reading cached boxes from centered edges reproduces the original subdivision's prepared-box list. -/
theorem centeredEdges_preparedBoxes {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : ClearSheetContinuation.Subdivision.Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) :
    forall (subdivision : PreparedSubdivision segment within left owner)
      (centers : CenterStates curve differential sheet subdivision),
      (centeredEdges curve differential sheet subdivision centers).map
          (fun centered =>
            centered.edge.cached.preparedOwner.track.initial.box) =
        subdivision.preparedBoxes
  | .stop _ _, _ => rfl
  | .next left owner request cached ordered small remaining, centers => by
      simp only [centeredEdges, List.map_cons,
        PreparedSheetContinuation.Subdivision.preparedBoxes_next,
        edgeOfStep_cached_prepared_box]
      rw [centeredEdges_preparedBoxes curve differential sheet remaining
        centers.2]

/-- Reading centered parameter edges reproduces the original subdivision's ordered parameter-edge list. -/
theorem centeredEdges_parameterEdges {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : ClearSheetContinuation.Subdivision.Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) :
    forall (subdivision : PreparedSubdivision segment within left owner)
      (centers : CenterStates curve differential sheet subdivision),
      (centeredEdges curve differential sheet subdivision centers).map
          CenteredEdge.parameterEdge = subdivision.parameterEdges
  | .stop _ _, _ => rfl
  | .next left owner request cached ordered small remaining, centers => by
      simp only [centeredEdges, List.map_cons,
        PreparedSheetContinuation.Subdivision.parameterEdges_next,
        CenteredEdge.parameterEdge]
      rw [centeredEdges_parameterEdges curve differential sheet remaining
        centers.2]
      rfl

end

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Polynomial in
open Purelib.Riemann.Branches in
/-- The centered model displacements telescope to the original subdivision's endpoint difference. -/
theorem centeredEdges_displacementSum {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : ClearSheetContinuation.Subdivision.Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) :
    forall (subdivision : PreparedSubdivision segment within left owner)
      (centers : CenterStates curve differential sheet subdivision),
      Basic.PathModel.displacementSum
          ((centeredEdges curve differential sheet subdivision centers).map
            CenteredEdge.model) =
        segment.pointAt subdivision.endpoint.parameter -
          segment.pointAt left.parameter
  | .stop current owner, _ => by
      simp only [centeredEdges, List.map_nil,
        Basic.PathModel.displacementSum_nil,
        PreparedSheetContinuation.Subdivision.endpoint_stop]
      apply Basic.ext <;>
        simp only [Basic.zero_re,
          Basic.zero_im,
          Basic.sub_re,
          Basic.sub_im] <;> ring1
  | .next current owner request cached ordered small remaining, centers => by
      simp only [centeredEdges, List.map_cons,
        Basic.PathModel.displacementSum_cons]
      rw [CenteredEdge.model_displacement]
      rw [centeredEdges_displacementSum curve differential sheet remaining
        centers.2]
      change
        (segment.pointAt request.endpoint.parameter -
            segment.pointAt current.parameter) +
          (segment.pointAt remaining.endpoint.parameter -
            segment.pointAt request.endpoint.parameter) =
        segment.pointAt remaining.endpoint.parameter -
          segment.pointAt current.parameter
      apply Basic.ext <;>
        simp only [Basic.add_re,
          Basic.add_im,
          Basic.sub_re,
          Basic.sub_im] <;> ring1

open Purelib.Integration.Polynomial.Gaussian.Path in
/-- A subdivision ending at the parent's request endpoint has the parent's exact model displacement. -/
theorem centeredEdges_displacement_eq_parent {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : CenteredEdge curve differential)
    (subdivision : PreparedSubdivision parent.edge.segment parent.edge.within
      parent.edge.left parent.edge.owner)
    (centers : CenterStates curve differential parent.edge.sheet subdivision)
    (endpoint_eq : subdivision.endpoint.parameter =
      parent.edge.request.endpoint.parameter) :
    Basic.PathModel.displacementSum
        ((centeredEdges curve differential parent.edge.sheet subdivision
          centers).map CenteredEdge.model) = parent.model.displacement := by
  rw [centeredEdges_displacementSum]
  rw [endpoint_eq]
  exact (CenteredEdge.model_displacement parent).symm

end Purelib.Riemann.Integration.PreparedSubdivisionModelCore
