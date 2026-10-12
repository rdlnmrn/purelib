module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Endpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JunctionRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ClosingJoins
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedCells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedParent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalAreaRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests

open Purelib.Data.Rat

open Purelib.Riemann.Integration

open Purelib.Riemann.Normalization

@[expose] public section

/-!
# Requested closing discrepancies between retained disk readings

The final comparison stage is selected before any cap polynomial sample.
Its certificate applies to the exact endpoint records already consumed by
the complete connected-path evaluation, without reevaluating either factor.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ClosingRequests

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels (Data)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover ParentCovers)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison (Preparation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins (SideBank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank (Requests Evaluations)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections.Evaluations (firstValue lastValue
  firstCoordinate lastCoordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ClosingJoins (LastJoin ClosingJoin)
open Purelib.Data.Gaussian.Basic.Canonical

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential} {patch :
    Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
  {data : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count} {cover :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data}

/-- A closing accuracy request from the actual last retained parent endpoint to the supplied target's first endpoint. -/
def LastRequest (target : ParentComparison.Preparation regular cover) (error : InverseRootPolynomial.Coordinate) (floor
  : Nat) :
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
      UniformReciprocalCover.ParentCovers parents} →
    (bank : ParentJoins.SideBank regular covers) → ClosingJoins.LastJoin target bank → Type
  | _, _, .nil, _ => PUnit
  | _, _, .cons head .nil, joined => JunctionRequests.Request head.boundary.last.bounds joined error floor
  | _, _, .cons _ (.cons next tail), joined =>
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ClosingRequests.LastRequest target error floor (.cons next tail)
    joined

/-- The closing request joining the actual last and first endpoints of the retained parent bank. -/
def ClosingRequest (error : InverseRootPolynomial.Coordinate) (floor : Nat) :
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
      UniformReciprocalCover.ParentCovers parents} →
    (bank : ParentJoins.SideBank regular covers) → ClosingJoins.ClosingJoin bank → Type
  | _, _, .nil, _ => PUnit
  | _, _, .cons head tail, joined => Curves.Hyperelliptic.Charts.Reciprocal.Disk.ClosingRequests.LastRequest head error
    floor (.cons head tail) joined

namespace LastRequest

/-- Acquire the original endpoint-closing request using its retained root join and supplied positive target. -/
def build (target : ParentComparison.Preparation regular cover) (error : InverseRootPolynomial.Coordinate) (positive : 0
  < error) (floor : Nat) :
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
      UniformReciprocalCover.ParentCovers parents} →
    (bank : ParentJoins.SideBank regular covers) → (joined : ClosingJoins.LastJoin target bank) →
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ClosingRequests.LastRequest target error floor bank joined
  | _, _, .nil, _ => ⟨⟩
  | _, _, .cons head .nil, joined => JunctionRequests.Request.build head.boundary.last.bounds joined error positive
    floor
  | _, _, .cons _ (.cons next tail), joined =>
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ClosingRequests.LastRequest.build target error positive floor
    (.cons next tail) joined

variable {target : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison.Preparation regular cover}
  {error : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

/-- Read the retained closing request's sufficient common stage, using the supplied floor for an empty bank. -/
def maximum : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
  UniformReciprocalCover.ParentCovers parents} →
    {bank : ParentJoins.SideBank regular covers} → {joined : ClosingJoins.LastJoin target bank} →
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ClosingRequests.LastRequest target error floor bank joined → Nat
  | _, _, .nil, _, _ => floor
  | _, _, .cons _ .nil, _, request => request.index
  | _, _, .cons _ (.cons next tail), _, request =>
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ClosingRequests.LastRequest.maximum (bank := .cons next tail)
    request

variable {sourceTarget reciprocalTarget coefficientTarget totalTarget areaTarget :
  Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {minimum index depth readingIndex : Nat}
  {box : Purelib.Geometry.Rational.Box} {sample :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

/-- At a sufficient common stage, the actual last retained primitive value is within the paid closing target of the
supplied target endpoint reading. -/
theorem accurate {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} {covers :
  UniformReciprocalCover.ParentCovers parents}
    {bank : ParentJoins.SideBank regular covers} {requests : SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum bank}
    (evaluated : SideBank.Evaluations sample depth readingIndex requests) {joined : ClosingJoins.LastJoin target bank}
    (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ClosingRequests.LastRequest target error floor bank joined)
      (later : request.maximum ≤ readingIndex) (nonempty : parents ≠ [])
    (endpoint : Coordinates.Overlap.Endpoint target.boundary.first.point.coordinates sample) (previous :
      InverseRootPolynomial.Gaussian) :
    Data.Gaussian.Norm.Basic.normSq (endpoint.approximation.sample readingIndex - Evaluations.lastValue
      evaluated previous) < error := by
  induction evaluated generalizing previous with
  | nil => exact False.elim (nonempty rfl)
  | cons head tail ih =>
      cases tail with
      | nil =>
          change Data.Gaussian.Norm.Basic.normSq (endpoint.approximation.sample readingIndex -
            head.cap.joined.lastValue) < error
          rw [← head.last_value]
          exact JunctionRequests.Request.accurate request head.last endpoint later later
      | cons next tail => exact ih request later (by intro equal; cases equal) head.cap.joined.lastValue

/-- Closing uses the actual cached last root, independently of its primitive. -/
theorem coordinate_accurate {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} {covers :
  UniformReciprocalCover.ParentCovers parents}
    {bank : ParentJoins.SideBank regular covers} {requests : SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum bank}
    (evaluated : SideBank.Evaluations sample depth readingIndex requests) {joined : ClosingJoins.LastJoin target bank}
    (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ClosingRequests.LastRequest target error floor bank joined)
      (later : request.maximum ≤ readingIndex) (nonempty : parents ≠ [])
    {endpoint : Coordinates.Overlap.Endpoint target.boundary.first.point.coordinates sample}
    (reading : ChartReadings.Endpoint.Reading endpoint readingIndex) (previous : InverseRootPolynomial.Gaussian) :
    Data.Gaussian.Norm.Basic.normSq (reading.coordinate - Evaluations.lastCoordinate evaluated previous) <
      collar.coordinateBound / 64 := by
  induction evaluated generalizing previous with
  | nil => exact False.elim (nonempty rfl)
  | cons head tail ih =>
      cases tail with
      | nil =>
          change Data.Gaussian.Norm.Basic.normSq (reading.coordinate - head.lastReading.coordinate) < _
          rw [reading.coordinate_eq, head.lastReading.coordinate_eq]
          exact JunctionRequests.Request.coordinate_accurate request later later
      | cons next tail => exact ih request later (by intro equal; cases equal) head.lastReading.coordinate

end LastRequest

namespace ClosingRequest

/-- Acquire the original endpoint-closing request using its retained root join and supplied positive target. -/
def build (error : InverseRootPolynomial.Coordinate) (positive : 0 < error) (floor : Nat) :
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
      UniformReciprocalCover.ParentCovers parents} →
    (bank : ParentJoins.SideBank regular covers) → (joined : ClosingJoins.ClosingJoin bank) →
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ClosingRequests.ClosingRequest error floor bank joined
  | _, _, .nil, _ => ⟨⟩
  | _, _, .cons head tail, joined => Curves.Hyperelliptic.Charts.Reciprocal.Disk.ClosingRequests.LastRequest.build head
    error positive floor (.cons head tail) joined

variable {error : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

/-- Read the retained closing request's sufficient common stage, using the supplied floor for an empty bank. -/
def maximum : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
  UniformReciprocalCover.ParentCovers parents} →
    {bank : ParentJoins.SideBank regular covers} → {joined : ClosingJoins.ClosingJoin bank} →
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ClosingRequests.ClosingRequest error floor bank joined → Nat
  | _, _, .nil, _, _ => floor
  | _, _, .cons _ _, _, request => Curves.Hyperelliptic.Charts.Reciprocal.Disk.ClosingRequests.LastRequest.maximum
    request

variable {sourceTarget reciprocalTarget coefficientTarget totalTarget areaTarget :
  Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {minimum index depth readingIndex : Nat}
  {box : Purelib.Geometry.Rational.Box} {sample :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

/-- The empty bank closes at zero; every nonempty bank uses the retained last/first coordinate comparison at this same
shared reading stage. -/
theorem accurate {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} {covers :
  UniformReciprocalCover.ParentCovers parents}
    {bank : ParentJoins.SideBank regular covers} {requests : SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum bank}
    (evaluated : SideBank.Evaluations sample depth readingIndex requests) {joined : ClosingJoins.ClosingJoin bank}
    (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ClosingRequests.ClosingRequest error floor bank joined)
      (positive : 0 < error) (later : request.maximum ≤ readingIndex) :
    Data.Gaussian.Norm.Basic.normSq (Evaluations.firstValue evaluated - Evaluations.lastValue evaluated
      (Evaluations.firstValue evaluated)) < error := by
  cases evaluated with
  | nil =>
    simpa only [Evaluations.firstValue, Evaluations.lastValue, Data.Gaussian.Basic.sub_self,
      Data.Gaussian.Norm.Basic.normSq_zero] using positive
  | cons head tail =>
      have close := Curves.Hyperelliptic.Charts.Reciprocal.Disk.ClosingRequests.LastRequest.accurate (.cons head tail)
        request later (by intro equal; cases equal) head.first head.cap.firstValue
      rw [head.first_value] at close
      exact close

/-- The closed source root thread supplies a geometric closing bound for these same readings, in both degree shapes. -/
theorem coordinate_accurate {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} {covers :
  UniformReciprocalCover.ParentCovers parents}
    {bank : ParentJoins.SideBank regular covers} {requests : SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum bank}
    (evaluated : SideBank.Evaluations sample depth readingIndex requests) {joined : ClosingJoins.ClosingJoin bank}
    (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ClosingRequests.ClosingRequest error floor bank joined)
      (later : request.maximum ≤ readingIndex) :
    Data.Gaussian.Norm.Basic.normSq (Evaluations.firstCoordinate evaluated - Evaluations.lastCoordinate
      evaluated (Evaluations.firstCoordinate evaluated)) < collar.coordinateBound / 64 := by
  cases evaluated with
  | nil =>
      change Data.Gaussian.Norm.Basic.normSq ((0 : InverseRootPolynomial.Gaussian) - 0) < _
      rw [Data.Gaussian.Basic.sub_self, Data.Gaussian.Norm.Basic.normSq_zero]
      exact Fraction.Order.Field.div_pos_direct collar.coordinateBound_positive (by decide +kernel)
  | cons head tail =>
      exact Curves.Hyperelliptic.Charts.Reciprocal.Disk.ClosingRequests.LastRequest.coordinate_accurate (.cons head
        tail) request later (by intro equal; cases equal)
        head.firstReading head.firstReading.coordinate

end ClosingRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ClosingRequests
