module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Endpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalAreaRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedParent
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedCells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain

public section

open Purelib
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedParent
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalAreaRequests
open Purelib.Integration.Path
open Purelib.Riemann.Branches
open Purelib.Riemann.Integration
open Purelib.Riemann.Normalization

/-!
# Synchronized retained parent requests on an exterior side

Every numerical plan is selected before the common polynomial sample.
Evaluation materializes each source/reciprocal bank once at that stage and
uses the same cap polynomial and coordinate-reading stage on every parent.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Integration.Path.IncrementArea (Summary)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison (Preparation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedParent (JoinedRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins (SideBank)

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential} {patch :
    Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
  {data : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count} {cover :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data}

set_option genInjectivity false in
/-- A cached shared-stage plan for one original source parent and its complete joined reciprocal cap path. -/
structure StageRequest (prepared : ParentComparison.Preparation regular cover)
    (sourceTarget reciprocalTarget coefficientTarget totalTarget areaTarget : InverseRootPolynomial.Coordinate) (minimum
      : Nat) where
  /-- The retained coupled source/reciprocal numerical plan. -/ source :
    PreparedReciprocalAreaRequests.CoupledLocalAreaPlan data sourceTarget reciprocalTarget coefficientTarget areaTarget
    totalTarget minimum
  /-- The retained complete joined-cap request or its exact evaluated cache. -/ cap : JoinedParent.JoinedRequest
    prepared totalTarget areaTarget minimum
  /-- The cached common polynomial stage of both original plans. -/ index : Nat
  /-- The common stage is exactly the maximum of source and cap requirements. -/ index_eq : index = max source.index
    cap.index

constructive_injectivity StageRequest

namespace StageRequest

/-- Cache both original parent plans and their common stage before selecting the shared sample. -/
@[expose] def build (prepared : ParentComparison.Preparation regular cover) (sourceTarget reciprocalTarget
  coefficientTarget totalTarget areaTarget : InverseRootPolynomial.Coordinate)
    (sourcePositive : 0 < sourceTarget) (reciprocalPositive : 0 < reciprocalTarget) (coefficientPositive : 0 <
      coefficientTarget)
    (totalPositive : 0 < totalTarget) (areaPositive : 0 < areaTarget) (minimum : Nat) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.StageRequest prepared sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum :=
  let source := CoupledLocalAreaPlan.build data sourceTarget reciprocalTarget coefficientTarget areaTarget totalTarget
    sourcePositive reciprocalPositive coefficientPositive areaPositive totalPositive minimum
  let cap := JoinedRequest.build prepared totalTarget areaTarget totalPositive areaPositive minimum
  ⟨source, cap, max source.index cap.index, rfl⟩

variable {prepared : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison.Preparation regular cover}
  {sourceTarget reciprocalTarget coefficientTarget totalTarget areaTarget :
  Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate}
  {minimum index depth readingIndex : Nat} {box : Purelib.Geometry.Rational.Box}

set_option genInjectivity false in
/-- The actual source request, shared cap sample and complete joined-cap evaluation with exact endpoint readbacks. -/
structure Evaluation (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.StageRequest prepared
  sourceTarget reciprocalTarget coefficientTarget totalTarget areaTarget minimum)
    (sample : Primitives.Sample cap differential index box) (depth readingIndex : Nat) where
  /-- The retained original coupled local area request at the supplied spatial depth. -/ original :
    PreparedReciprocalAreaRequests.CoupledLocalAreaRequest cover sourceTarget reciprocalTarget coefficientTarget
    areaTarget totalTarget minimum depth
  /-- The original area request uses exactly the supplied shared polynomial stage. -/ original_index :
    original.area.index = index
  /-- The retained cap sample at the original area request's actual dependent index. -/ capSample : Primitives.Sample
    cap differential original.area.index box
  /-- The retained cap sample is the exact supplied sample after index transport. -/ capSample_eq : HEq capSample sample
  /-- The retained complete joined-cap request or its exact evaluated cache. -/ cap : JoinedRequest.Evaluation
    request.cap original.area capSample readingIndex
  /-- The retained first endpoint channel on the original boundary owner. -/ first : Coordinates.Overlap.Endpoint
    prepared.boundary.first.point.coordinates sample
  /-- Its common-stage primitive reading equals the cached complete path's first value. -/ first_value :
    first.approximation.sample readingIndex = cap.firstValue
  /-- The retained last endpoint channel on the original boundary owner. -/ last : Coordinates.Overlap.Endpoint
    prepared.boundary.last.point.coordinates sample
  /-- Its common-stage primitive reading equals the cached complete path's last value. -/ last_value :
    last.approximation.sample readingIndex = cap.joined.lastValue
  /-- The cached actual first endpoint coordinate reading. -/ firstReading : ChartReadings.Endpoint.Reading first
    readingIndex
  /-- The first coordinate reading is exactly the one retained by the original cap comparison. -/ first_coordinate :
    firstReading.coordinate = cap.boundary.firstReading.coordinate
  /-- The cached actual last endpoint coordinate reading. -/ lastReading : ChartReadings.Endpoint.Reading last
    readingIndex
  /-- The last coordinate reading is exactly the one retained by the original cap comparison. -/ last_coordinate :
    lastReading.coordinate = cap.boundary.lastReading.coordinate

constructive_injectivity Evaluation

/-- Evaluate the retained parent requests once using the supplied shared polynomial and coordinate-reading stages. -/
@[expose] def evaluate (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.StageRequest prepared
  sourceTarget reciprocalTarget coefficientTarget totalTarget areaTarget minimum)
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter)
    (sample : Primitives.Sample cap differential index box) (depth readingIndex : Nat)
    (later : request.index ≤ index) (readingLater : request.cap.readingIndex ≤ readingIndex) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.StageRequest.Evaluation request sample depth readingIndex
      := by
  have indices := later
  rw [request.index_eq] at indices
  let original := request.source.evaluate cover proper index depth ((Data.Nat.Order.le_max_left _ _).trans indices)
  let compared := request.cap.evaluate original.area sample ((Data.Nat.Order.le_max_right _ _).trans indices)
    readingIndex readingLater
  exact ⟨original, rfl, sample, HEq.rfl, compared, compared.boundary.first,
    compared.boundary.first_value.trans compared.firstValue_eq.symm, compared.boundary.last,
    (compared.boundary.last_value compared.firstValue).trans compared.joined.lastValue_eq.symm,
    compared.boundary.firstReading, rfl, compared.boundary.lastReading, rfl⟩

end StageRequest

namespace SideBank

set_option genInjectivity false in
/-- A complete dependent bank of numerical requests on the exact retained exterior-parent spine. -/
inductive Requests (sourceTarget reciprocalTarget coefficientTarget totalTarget areaTarget :
  InverseRootPolynomial.Coordinate) (minimum : Nat) :
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
      UniformReciprocalCover.ParentCovers parents} →
    ParentJoins.SideBank regular covers → Type 2
  /-- The empty request or evaluation bank for an empty retained parent spine. -/ | nil :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank.Requests sourceTarget reciprocalTarget
    coefficientTarget totalTarget areaTarget minimum .nil
  /-- Retain the first original parent request or evaluation together with the exact dependent tail. -/ | cons {parent :
    PreparedSubdivisionModelCore.CenteredEdge curve differential} {parents : List
    (PreparedSubdivisionModelCore.CenteredEdge curve differential)}
      {patch : UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data : UniformReciprocalModels.Data patch
        genus}
      {cover : UniformReciprocalCover.Cover data} {covers : UniformReciprocalCover.ParentCovers parents}
      {head : ParentComparison.Preparation regular cover} {tail : ParentJoins.SideBank regular covers}
      (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.StageRequest head sourceTarget
        reciprocalTarget coefficientTarget totalTarget areaTarget minimum)
      (remaining : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank.Requests sourceTarget
        reciprocalTarget coefficientTarget totalTarget areaTarget minimum tail) :
      Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank.Requests sourceTarget reciprocalTarget
        coefficientTarget totalTarget areaTarget minimum (.cons head tail)

constructive_injectivity Requests

namespace Requests

/-- Construct a request on every original retained parent preparation with the same numerical targets. -/
@[expose] def build (sourceTarget reciprocalTarget coefficientTarget totalTarget areaTarget :
  InverseRootPolynomial.Coordinate)
    (sourcePositive : 0 < sourceTarget) (reciprocalPositive : 0 < reciprocalTarget) (coefficientPositive : 0 <
      coefficientTarget)
    (totalPositive : 0 < totalTarget) (areaPositive : 0 < areaTarget) (minimum : Nat) :
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
      UniformReciprocalCover.ParentCovers parents} →
    (prepared : ParentJoins.SideBank regular covers) →
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.StageRequest.build head sourceTarget reciprocalTarget
        coefficientTarget totalTarget areaTarget
        sourcePositive reciprocalPositive coefficientPositive totalPositive areaPositive minimum)
      (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank.Requests.build sourceTarget
        reciprocalTarget coefficientTarget totalTarget areaTarget sourcePositive reciprocalPositive coefficientPositive
        totalPositive areaPositive minimum tail)

variable {sourceTarget reciprocalTarget coefficientTarget totalTarget areaTarget :
  Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {minimum : Nat}

/-- Read the maximum polynomial-stage requirement over all retained parents and the original minimum. -/
@[expose] def maximum : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
  UniformReciprocalCover.ParentCovers parents} →
    {prepared : ParentJoins.SideBank regular covers} →
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared → Nat
  | _, _, _, .nil => minimum
  | _, _, _, .cons head tail => max head.index tail.maximum

/-- Read the maximum coordinate-reading requirement over all retained parents and the original minimum. -/
@[expose] def readingMaximum : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers
  : UniformReciprocalCover.ParentCovers parents} →
    {prepared : ParentJoins.SideBank regular covers} →
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared → Nat
  | _, _, _, .nil => minimum
  | _, _, _, .cons head tail => max head.cap.readingIndex tail.readingMaximum

end Requests

variable {sourceTarget reciprocalTarget coefficientTarget totalTarget areaTarget :
  Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {minimum index depth readingIndex : Nat}
  {box : Purelib.Geometry.Rational.Box} {sample :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

set_option genInjectivity false in
/-- Cached evaluations of all original parent requests using one supplied cap sample and shared reading stage. -/
inductive Evaluations (sample : Primitives.Sample cap differential index box) (depth readingIndex : Nat) :
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
      UniformReciprocalCover.ParentCovers parents} →
    {prepared : ParentJoins.SideBank regular covers} →
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared → Type 2
  /-- The empty request or evaluation bank for an empty retained parent spine. -/ | nil :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank.Evaluations sample depth readingIndex .nil
  /-- Retain the first original parent request or evaluation together with the exact dependent tail. -/ | cons {parent :
    PreparedSubdivisionModelCore.CenteredEdge curve differential} {parents : List
    (PreparedSubdivisionModelCore.CenteredEdge curve differential)}
      {patch : UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data : UniformReciprocalModels.Data patch
        genus}
      {cover : UniformReciprocalCover.Cover data} {covers : UniformReciprocalCover.ParentCovers parents}
      {head : ParentComparison.Preparation regular cover} {tail : ParentJoins.SideBank regular covers}
      {request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.StageRequest head sourceTarget
        reciprocalTarget coefficientTarget totalTarget areaTarget minimum}
      {remaining : Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank.Requests sourceTarget
        reciprocalTarget coefficientTarget totalTarget areaTarget minimum tail}
      (evaluated : Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.StageRequest.Evaluation request sample depth
        readingIndex)
      (rest : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank.Evaluations sample depth
        readingIndex remaining) : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank.Evaluations
        sample depth readingIndex (.cons request remaining)

constructive_injectivity Evaluations

/-- Evaluate every retained parent request once at the shared polynomial, spatial and reading stages. -/
@[expose] def Requests.evaluate : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
  {covers : UniformReciprocalCover.ParentCovers parents} →
    {prepared : ParentJoins.SideBank regular covers} →
    (requests : Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared) →
    PreparedDyadicRefinements.AllParentsProper parents → (sample : Primitives.Sample cap differential index box) →
    (depth readingIndex : Nat) → requests.maximum ≤ index → requests.readingMaximum ≤ readingIndex →
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank.Evaluations sample depth readingIndex requests
  | _, _, _, .nil, _, _, _, _, _, _ => .nil
  | _, _, _, .cons head tail, proper, sample, depth, readingIndex, later, readingLater =>
      .cons (head.evaluate proper.1 sample depth readingIndex ((Data.Nat.Order.le_max_left _ _).trans later)
        ((Data.Nat.Order.le_max_left _ _).trans readingLater))
        (tail.evaluate proper.2 sample depth readingIndex ((Data.Nat.Order.le_max_right _ _).trans later)
          ((Data.Nat.Order.le_max_right _ _).trans readingLater))

namespace Evaluations

/-- Read the exact retained coupled source area requests without rebuilding any parent. -/
@[expose] def originals : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
  UniformReciprocalCover.ParentCovers parents} →
    {prepared : ParentJoins.SideBank regular covers} → {requests :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared} →
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank.Evaluations sample depth readingIndex requests →
      ReciprocalSideArea.CoupledAreaParents sourceTarget reciprocalTarget coefficientTarget areaTarget totalTarget
        minimum depth covers
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .cons head tail => .cons head.original tail.originals

/-- Read the complete original source and corrected cap paths in retained parent order. -/
@[expose] def pairs : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
  UniformReciprocalCover.ParentCovers parents} →
    {prepared : ParentJoins.SideBank regular covers} → {requests :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared} →
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank.Evaluations sample depth readingIndex requests →
      List (List InverseRootPolynomial.Gaussian × List InverseRootPolynomial.Gaussian)
  | _, _, _, _, .nil => []
  | _, _, _, _, .cons head tail =>
      ((head.original.area.cells.pairs.map Prod.fst).flatten, (head.cap.joined.pairs.map Prod.fst).flatten) ::
        tail.pairs

/-- The retained path-pair count equals the original parent count. -/
theorem pairs_length {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} {covers :
  UniformReciprocalCover.ParentCovers parents}
    {prepared : ParentJoins.SideBank regular covers} {requests :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared}
    (evaluated : Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank.Evaluations sample depth readingIndex
      requests) : evaluated.pairs.length = parents.length := by
  induction evaluated with
  | nil => rfl
  | cons head tail ih => exact congrArg Nat.succ ih

/-- Compose the cached original source summaries including all parent-total cross terms. -/
@[expose] def leftSummary : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
  UniformReciprocalCover.ParentCovers parents} →
    {prepared : ParentJoins.SideBank regular covers} → {requests :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared} →
    (evaluated : Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank.Evaluations sample depth readingIndex
      requests) → IncrementArea.Summary (evaluated.pairs.map Prod.fst).flatten
  | _, _, _, _, .nil => IncrementArea.Summary.build []
  | _, _, _, _, .cons head tail => head.original.area.left.append tail.leftSummary

/-- Compose the cached complete corrected cap summaries including all parent-total cross terms. -/
@[expose] def capSummary : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
  UniformReciprocalCover.ParentCovers parents} →
    {prepared : ParentJoins.SideBank regular covers} → {requests :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared} →
    (evaluated : Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank.Evaluations sample depth readingIndex
      requests) → IncrementArea.Summary (evaluated.pairs.map Prod.snd).flatten
  | _, _, _, _, .nil => IncrementArea.Summary.build []
  | _, _, _, _, .cons head tail => head.cap.joined.summary.append tail.capSummary

end Evaluations
end SideBank
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests
