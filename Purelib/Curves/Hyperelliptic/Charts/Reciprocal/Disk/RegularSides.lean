module
import Purelib.Data.Nat.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideEstimates
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedParent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularCells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalAreaRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility

public section

open Purelib
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularRequests
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularRequests.Request
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests
open Purelib.Integration.Path
open Purelib.Riemann.Integration
open Purelib.Riemann.Normalization

/-!
# Shared regular-cap requests over the retained exterior parent bank

The existing side requests select and cache every source parent. A regular
plan selects the additional sufficient polynomial stage before sampling;
evaluation consumes those same parent records and their retained root joins.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSides

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Integration.Path.IncrementArea (Summary)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins (SideBank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank (Requests Evaluations)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularRequests (RegularRequest)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {sourceTarget reciprocalTarget coefficientTarget totalTarget areaTarget :
    Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {minimum : Nat}

/-- Regular-cap accuracy plans indexed by the original retained exterior-side request bank. -/
@[expose] def Plans : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
    {covers : UniformReciprocalCover.ParentCovers parents} → {prepared : ParentJoins.SideBank regular covers} →
    SideBank.Requests sourceTarget reciprocalTarget coefficientTarget totalTarget areaTarget minimum prepared → Type 2
  | _, _, _, .nil => PUnit
  | _, _, .cons head _, .cons _ remaining =>
      RegularRequests.RegularRequest head totalTarget areaTarget minimum ×
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSides.Plans remaining

namespace Plans

/-- Select one regular-cap plan for every original parent before choosing the common polynomial sample. -/
@[expose] def build (regularChart : HyperellipticReciprocal.originOrder curve = 0)
    (totalPositive : 0 < totalTarget) (areaPositive : 0 < areaTarget) :
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
      UniformReciprocalCover.ParentCovers parents} →
    {prepared : ParentJoins.SideBank regular covers} →
    (requests : SideBank.Requests sourceTarget reciprocalTarget coefficientTarget totalTarget areaTarget minimum
      prepared) → Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSides.Plans requests
  | _, _, _, .nil => ⟨⟩
  | _, _, _, .cons _ tail =>
      ⟨RegularRequest.build _ regularChart totalTarget areaTarget totalPositive areaPositive minimum,
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSides.Plans.build regularChart totalPositive
          areaPositive tail⟩

/-- Read the common sufficient polynomial stage of every retained regular-cap plan. -/
@[expose] def maximum : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
  UniformReciprocalCover.ParentCovers parents} →
    {prepared : ParentJoins.SideBank regular covers} →
    {requests : SideBank.Requests sourceTarget reciprocalTarget coefficientTarget totalTarget areaTarget minimum
      prepared} → Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSides.Plans requests → Nat
  | _, _, _, .nil, _ => minimum
  | _, _, _, .cons _ _, plans => max plans.1.index
    (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSides.Plans.maximum plans.2)

end Plans

variable {index depth readingIndex : Nat} {box : Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

/-- Cached regular-cap evaluations indexed by the exact original side evaluations and their retained plans. -/
@[expose] def Results : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
  UniformReciprocalCover.ParentCovers parents} →
    {prepared : ParentJoins.SideBank regular covers} →
    {requests : SideBank.Requests sourceTarget reciprocalTarget coefficientTarget totalTarget areaTarget minimum
      prepared} →
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSides.Plans requests → SideBank.Evaluations sample depth
      readingIndex requests → Type 2
  | _, _, _, _, _, .nil => PUnit
  | _, _, _, _, plans, .cons head tail =>
      RegularRequest.Evaluation plans.1 head.cap.polynomial.cells ×
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSides.Results plans.2 tail

/-- Evaluate every retained regular-cap plan on the actual original parent cell caches at a sufficient common stage. -/
@[expose] def Plans.evaluate : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers
  : UniformReciprocalCover.ParentCovers parents} →
    {prepared : ParentJoins.SideBank regular covers} →
    {requests : SideBank.Requests sourceTarget reciprocalTarget coefficientTarget totalTarget areaTarget minimum
      prepared} →
    (plans : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSides.Plans requests) → (evaluated :
      SideBank.Evaluations sample depth readingIndex requests) →
    plans.maximum ≤ index → Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSides.Results plans evaluated
  | _, _, _, _, _, .nil, _ => ⟨⟩
  | _, _, _, _, plans, .cons head tail, later =>
      ⟨Evaluation.withRegularCap head.cap.polynomial plans.1 (by
          rw [head.original_index];
          exact (Data.Nat.Order.le_max_left _ _).trans later),
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSides.Plans.evaluate plans.2 tail
          ((Data.Nat.Order.le_max_right _ _).trans later)⟩

namespace Results

/-- Read each actual complete source path paired with its retained regular-cap path. -/
@[expose] def pairs : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
  UniformReciprocalCover.ParentCovers parents} →
    {prepared : ParentJoins.SideBank regular covers} →
    {requests : SideBank.Requests sourceTarget reciprocalTarget coefficientTarget totalTarget areaTarget minimum
      prepared} →
    {plans : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSides.Plans requests} → {evaluated :
      SideBank.Evaluations sample depth readingIndex requests} →
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSides.Results plans evaluated → List (List
      InverseRootPolynomial.Gaussian × List InverseRootPolynomial.Gaussian)
  | _, _, _, _, _, .nil, _ => []
  | _, _, _, _, _, .cons head _, results =>
      ((head.cap.polynomial.cells.pairs.map Prod.fst).flatten, (results.1.cells.pairs.map Prod.snd).flatten) ::
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSides.Results.pairs results.2

/-- Compose the cached original source summaries in their retained parent order. -/
@[expose] def leftSummary : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
  UniformReciprocalCover.ParentCovers parents} →
    {prepared : ParentJoins.SideBank regular covers} →
    {requests : SideBank.Requests sourceTarget reciprocalTarget coefficientTarget totalTarget areaTarget minimum
      prepared} →
    {plans : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSides.Plans requests} → {evaluated :
      SideBank.Evaluations sample depth readingIndex requests} →
    (results : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSides.Results plans evaluated) → IncrementArea.Summary
      (results.pairs.map Prod.fst).flatten
  | _, _, _, _, _, .nil, _ => IncrementArea.Summary.build []
  | _, _, _, _, _, .cons _ _, results => results.1.left.append
    (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSides.Results.leftSummary results.2)

/-- Compose the cached regular-cap summaries in their retained parent order. -/
@[expose] def capSummary : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
  UniformReciprocalCover.ParentCovers parents} →
    {prepared : ParentJoins.SideBank regular covers} →
    {requests : SideBank.Requests sourceTarget reciprocalTarget coefficientTarget totalTarget areaTarget minimum
      prepared} →
    {plans : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSides.Plans requests} → {evaluated :
      SideBank.Evaluations sample depth readingIndex requests} →
    (results : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSides.Results plans evaluated) → IncrementArea.Summary
      (results.pairs.map Prod.snd).flatten
  | _, _, _, _, _, .nil, _ => IncrementArea.Summary.build []
  | _, _, _, _, _, .cons _ _, results => results.1.cap.append
    (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSides.Results.capSummary results.2)

variable {parents : List (Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)}
  {covers : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents}
  {prepared : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank regular covers} {requests :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank.Requests sourceTarget reciprocalTarget
    coefficientTarget totalTarget areaTarget minimum prepared}
  {plans : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSides.Plans requests} {evaluated :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank.Evaluations sample depth readingIndex
    requests}

/-- There is one actual retained source/cap path pair per original parent. -/
theorem pairs_length (results : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSides.Results plans evaluated) :
  results.pairs.length = parents.length := by
  induction evaluated with
  | nil => rfl
  | cons head tail ih => exact congrArg Nat.succ (ih results.2)

/-- The retained regular-cap comparison uses exactly the original complete source increment paths. -/
theorem source_paths (results : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSides.Results plans evaluated) :
    (results.pairs.map Prod.fst).flatten = (evaluated.pairs.map Prod.fst).flatten := by
  induction evaluated with
  | nil => rfl
  | cons head tail ih =>
      change (head.cap.polynomial.cells.pairs.map Prod.fst).flatten ++
        (Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSides.Results.pairs results.2 |>.map Prod.fst).flatten =
        (head.original.area.cells.pairs.map Prod.fst).flatten ++ (tail.pairs.map Prod.fst).flatten
      rw [head.cap.polynomial.cells.left_paths, head.cap.polynomial.original_eq, ih results.2]

end Results
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSides
