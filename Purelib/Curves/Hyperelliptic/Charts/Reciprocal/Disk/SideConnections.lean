module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.List.Membership
import Purelib.Data.List.Append
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JunctionRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Path.IncrementAreaJoins
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedCells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedParent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalAreaRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

public section

open Purelib
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests
open Purelib.Data.Rat
open Purelib.Integration.Path
open Purelib.Integration.Path.IncrementAreaJoins
open Purelib.Riemann.Integration
open Purelib.Riemann.Normalization

/-!
# Actual finite connectors between retained exterior parents

Junction requests consume the source-root joins and cached endpoint bounds.
The connected path keeps every parent's complete path and prepends the actual
difference between consecutive retained readings, at one shared stage.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Integration.Path.IncrementArea (Summary)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins (SideBank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank (Links)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank (Requests Evaluations)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}

/-- Endpoint accuracy requests indexed by every actual junction of the retained exterior-parent bank. -/
@[expose] def JunctionRequests (target : InverseRootPolynomial.Coordinate) (floor : Nat) :
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
      UniformReciprocalCover.ParentCovers parents} →
    (prepared : ParentJoins.SideBank regular covers) → SideBank.Links prepared → Type 2
  | _, _, .nil, .nil => PUnit
  | _, _, .cons _ .nil, .one _ => PUnit
  | _, _, .cons head (.cons _ _), .cons joined remaining =>
      JunctionRequests.Request head.boundary.last.bounds joined target floor ×
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections.JunctionRequests target floor _ remaining

namespace JunctionRequests

/-- Request each actual consecutive parent junction from its original endpoint bounds and retained operational join. -/
@[expose] def build (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) (floor : Nat) :
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
      UniformReciprocalCover.ParentCovers parents} →
    (prepared : ParentJoins.SideBank regular covers) → (links : SideBank.Links prepared) →
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections.JunctionRequests target floor prepared links
  | _, _, .nil, .nil => ⟨⟩
  | _, _, .cons _ .nil, .one _ => ⟨⟩
  | _, _, .cons head (.cons next tail), .cons joined remaining =>
      ⟨JunctionRequests.Request.build head.boundary.last.bounds joined target positive floor,
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections.JunctionRequests.build target positive floor
          (.cons next tail) remaining⟩

variable {target : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

/-- Read a common stage above every retained junction request, respecting the supplied floor. -/
@[expose] def maximum : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
  UniformReciprocalCover.ParentCovers parents} →
    {prepared : ParentJoins.SideBank regular covers} → {links : SideBank.Links prepared} →
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections.JunctionRequests target floor prepared links → Nat
  | _, _, .nil, .nil, _ => floor
  | _, _, .cons _ .nil, .one _, _ => floor
  | _, _, .cons _ (.cons _ _), .cons _ _, requests => max requests.1.index
    (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections.JunctionRequests.maximum requests.2)

end JunctionRequests

variable {sourceTarget reciprocalTarget coefficientTarget totalTarget areaTarget :
  Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {minimum index depth readingIndex : Nat}
  {box : Purelib.Geometry.Rational.Box} {sample :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

namespace Evaluations

/-- Read the first cached primitive value of the retained parent bank, or zero for an empty bank. -/
@[expose] def firstValue : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
  UniformReciprocalCover.ParentCovers parents} →
    {prepared : ParentJoins.SideBank regular covers} → {requests : SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared} →
    SideBank.Evaluations sample depth readingIndex requests → InverseRootPolynomial.Gaussian
  | _, _, _, _, .nil => 0
  | _, _, _, _, .cons head _ => head.cap.firstValue

/-- Read the final cached primitive value, preserving the supplied previous value for an empty bank. -/
@[expose] def lastValue : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
  UniformReciprocalCover.ParentCovers parents} →
    {prepared : ParentJoins.SideBank regular covers} → {requests : SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared} →
    SideBank.Evaluations sample depth readingIndex requests → InverseRootPolynomial.Gaussian →
      InverseRootPolynomial.Gaussian
  | _, _, _, _, .nil, previous => previous
  | _, _, _, _, .cons head tail, _ =>
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections.Evaluations.lastValue tail
    head.cap.joined.lastValue

/-- Each retained parent's actual initial primitive reading is within the supplied squared-norm budget of the previous
cached final reading. -/
@[expose] def GapsSmall : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
  UniformReciprocalCover.ParentCovers parents} →
    {prepared : ParentJoins.SideBank regular covers} → {requests : SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared} →
    SideBank.Evaluations sample depth readingIndex requests → InverseRootPolynomial.Gaussian →
      InverseRootPolynomial.Coordinate → Prop
  | _, _, _, _, .nil, _, _ => True
  | _, _, _, _, .cons head tail, previous, bound =>
      Data.Gaussian.Norm.Basic.normSq (head.cap.firstValue - previous) ≤ bound ∧
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections.Evaluations.GapsSmall tail
        head.cap.joined.lastValue bound

/-- The retained junction requests bound all actual primitive connectors at the supplied common reading stage. -/
theorem gaps_small {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} {covers :
  UniformReciprocalCover.ParentCovers parents}
    {prepared : ParentJoins.SideBank regular covers} {requests : SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared}
    (evaluated : SideBank.Evaluations sample depth readingIndex requests) {links : SideBank.Links prepared} {target :
      InverseRootPolynomial.Coordinate} {floor : Nat}
    (junctions : Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections.JunctionRequests target floor prepared
      links) (later : junctions.maximum ≤ readingIndex)
    (previous : InverseRootPolynomial.Gaussian) (small : Data.Gaussian.Norm.Basic.normSq
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections.Evaluations.firstValue evaluated - previous) ≤
      target) : Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections.Evaluations.GapsSmall evaluated previous
      target := by
  induction evaluated generalizing previous with
  | nil => trivial
  | cons head tail ih =>
      refine ⟨small, ?_⟩
      cases tail with
      | nil => trivial
      | cons next tail =>
          cases links with
          | cons joined remaining =>
              apply ih junctions.2 ((Data.Nat.Order.le_max_right _ _).trans later) head.cap.joined.lastValue
              change Data.Gaussian.Norm.Basic.normSq (next.cap.firstValue - head.cap.joined.lastValue) ≤ target
              rw [← next.first_value, ← head.last_value]
              exact (junctions.1.accurate head.last next.first ((Data.Nat.Order.le_max_left _ _).trans later)
                ((Data.Nat.Order.le_max_left _ _).trans later)).le

/-- Read the first cached coordinate of the actual retained parent bank, or zero for an empty bank. -/
@[expose] def firstCoordinate : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
  {covers : UniformReciprocalCover.ParentCovers parents} →
    {prepared : ParentJoins.SideBank regular covers} → {requests : SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared} →
    SideBank.Evaluations sample depth readingIndex requests → InverseRootPolynomial.Gaussian
  | _, _, _, _, .nil => 0
  | _, _, _, _, .cons head _ => head.firstReading.coordinate

/-- Read the final retained endpoint coordinate, preserving the supplied previous coordinate for an empty bank. -/
@[expose] def lastCoordinate : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers
  : UniformReciprocalCover.ParentCovers parents} →
    {prepared : ParentJoins.SideBank regular covers} → {requests : SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared} →
    SideBank.Evaluations sample depth readingIndex requests → InverseRootPolynomial.Gaussian →
      InverseRootPolynomial.Gaussian
  | _, _, _, _, .nil, previous => previous
  | _, _, _, _, .cons head tail, _ =>
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections.Evaluations.lastCoordinate tail
    head.lastReading.coordinate

/-- Include every inter-parent connector and each parent's cached cell joins. -/
@[expose] def coordinateGaps : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers
  : UniformReciprocalCover.ParentCovers parents} →
    {prepared : ParentJoins.SideBank regular covers} → {requests : SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared} →
    SideBank.Evaluations sample depth readingIndex requests → InverseRootPolynomial.Gaussian → List
      InverseRootPolynomial.Gaussian
  | _, _, _, _, .nil, _ => []
  | _, _, _, _, .cons head tail, previous =>
      (head.firstReading.coordinate - previous) :: (head.cap.coordinates.gaps ++
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections.Evaluations.coordinateGaps tail
        head.lastReading.coordinate)

/-- Count all actual inter-parent connectors and retained internal coordinate gaps. -/
@[expose] def coordinateGapCount : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
  {covers : UniformReciprocalCover.ParentCovers parents} →
    {prepared : ParentJoins.SideBank regular covers} → {requests : SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared} →
    SideBank.Evaluations sample depth readingIndex requests → Nat
  | _, _, _, _, .nil => 0
  | _, _, _, _, .cons head tail => 1 + head.cap.coordinates.gaps.length +
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections.Evaluations.coordinateGapCount tail

/-- The retained coordinate-gap list has exactly its cached recursive gap count. -/
theorem coordinateGaps_length {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} {covers :
  UniformReciprocalCover.ParentCovers parents}
    {prepared : ParentJoins.SideBank regular covers} {requests : SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared}
    (evaluated : SideBank.Evaluations sample depth readingIndex requests) (previous : InverseRootPolynomial.Gaussian) :
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections.Evaluations.coordinateGaps evaluated previous).length =
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections.Evaluations.coordinateGapCount evaluated := by
  induction evaluated generalizing previous with
  | nil => rfl
  | cons head tail ih =>
      change ((head.firstReading.coordinate - previous) :: (_ ++ _)).length = _
      rw [List.length_cons, Data.List.Append.length_append, ih]
      change _ = 1 + _ + _
      omega

/-- Every actual inter-parent and internal coordinate gap satisfies the original collar's coordinate budget. -/
theorem coordinate_gaps_small {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} {covers :
  UniformReciprocalCover.ParentCovers parents}
    {prepared : ParentJoins.SideBank regular covers} {requests : SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared}
    (evaluated : SideBank.Evaluations sample depth readingIndex requests) {links : SideBank.Links prepared} {target :
      InverseRootPolynomial.Coordinate} {floor : Nat}
    (junctions : Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections.JunctionRequests target floor prepared
      links) (later : junctions.maximum ≤ readingIndex)
    (previous : InverseRootPolynomial.Gaussian) (small : Data.Gaussian.Norm.Basic.normSq
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections.Evaluations.firstCoordinate evaluated - previous) ≤
      collar.coordinateBound / 64) :
    ∀ gap ∈ Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections.Evaluations.coordinateGaps evaluated previous,
      Data.Gaussian.Norm.Basic.normSq gap ≤ collar.coordinateBound / 64 := by
  induction evaluated generalizing previous with
  | nil => intro _ member; exact False.elim (List.not_mem_nil member)
  | cons head tail ih =>
      intro gap member
      rcases Data.List.Membership.mem_cons.mp member with same | member
      · subst gap; exact small
      · rcases Data.List.Membership.mem_append.mp member with member | member
        · exact head.cap.coordinates.bounded gap member
        · cases tail with
          | nil => exact False.elim (List.not_mem_nil member)
          | cons next tail =>
              cases links with
              | cons joined remaining =>
                  apply ih junctions.2 ((Data.Nat.Order.le_max_right _ _).trans later) head.lastReading.coordinate ?_
                    gap member
                  change Data.Gaussian.Norm.Basic.normSq (next.firstReading.coordinate -
                    head.lastReading.coordinate) ≤ _
                  rw [next.firstReading.coordinate_eq, head.lastReading.coordinate_eq]
                  exact (junctions.1.coordinate_accurate ((Data.Nat.Order.le_max_left _ _).trans later)
                    ((Data.Nat.Order.le_max_left _ _).trans later)).le

set_option genInjectivity false in
/-- The exact endpoint coordinates and complete bounded gap list of the retained exterior-parent path.

Both endpoints and the ordered gaps read back the original cached evaluations, including inter-parent connectors and
each parent's internal joins. -/
structure CoordinateConnections {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} {covers
  : UniformReciprocalCover.ParentCovers parents}
    {prepared : ParentJoins.SideBank regular covers} {requests : SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared}
    (evaluated : SideBank.Evaluations sample depth readingIndex requests) where
  /-- The cached actual first coordinate of the retained parent evaluations. -/ first : InverseRootPolynomial.Gaussian
  /-- The first coordinate cache reads back the original evaluations exactly. -/ first_eq : first =
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections.Evaluations.firstCoordinate evaluated
  /-- The cached actual final coordinate, seeded by the retained first coordinate for an empty bank. -/ last :
    InverseRootPolynomial.Gaussian
  /-- The final coordinate cache is exactly the retained evaluations' last-coordinate readback. -/ last_eq : last =
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections.Evaluations.lastCoordinate evaluated first
  /-- The ordered cached actual inter-parent connectors and internal coordinate gaps. -/ gaps : List
    InverseRootPolynomial.Gaussian
  /-- The gap cache is exactly the complete retained evaluations' coordinate-gap list. -/ gaps_eq : gaps =
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections.Evaluations.coordinateGaps evaluated first
  /-- The retained gap list has the exact recursive connector count. -/ length_eq : gaps.length =
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections.Evaluations.coordinateGapCount evaluated
  /-- Every actual retained gap satisfies one sixty-fourth of the original coordinate bound. -/ bounded : ∀ gap ∈ gaps,
    Data.Gaussian.Norm.Basic.normSq gap ≤ collar.coordinateBound / 64

constructive_injectivity CoordinateConnections

/-- Cache the actual endpoints and complete coordinate-gap list once, using the retained junction requests to certify
every gap. -/
@[expose] def coordinateConnections {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)}
  {covers : UniformReciprocalCover.ParentCovers parents}
    {prepared : ParentJoins.SideBank regular covers} {requests : SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared}
    (evaluated : SideBank.Evaluations sample depth readingIndex requests) {links : SideBank.Links prepared} {target :
      InverseRootPolynomial.Coordinate} {floor : Nat}
    (junctions : Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections.JunctionRequests target floor prepared
      links) (later : junctions.maximum ≤ readingIndex) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections.Evaluations.CoordinateConnections evaluated := by
  let first := Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections.Evaluations.firstCoordinate evaluated
  let last := Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections.Evaluations.lastCoordinate evaluated first
  let gaps := Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections.Evaluations.coordinateGaps evaluated first
  exact ⟨first, rfl, last, rfl, gaps, rfl,
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections.Evaluations.coordinateGaps_length evaluated first,
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections.Evaluations.coordinate_gaps_small evaluated junctions
      later first (by
      change Data.Gaussian.Norm.Basic.normSq (first - first) ≤ _
      rw [Data.Gaussian.Basic.sub_self, Data.Gaussian.Norm.Basic.normSq_zero]
      exact (Fraction.Order.Field.div_pos_direct collar.coordinateBound_positive (by decide +kernel)).le)⟩

/-- Pair every parent's exact complete increment path with the connector from the previous retained primitive reading.
-/
@[expose] def connectedBlocks : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
  {covers : UniformReciprocalCover.ParentCovers parents} →
    {prepared : ParentJoins.SideBank regular covers} → {requests : SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared} →
    SideBank.Evaluations sample depth readingIndex requests → InverseRootPolynomial.Gaussian → List
      (InverseRootPolynomial.Gaussian × List InverseRootPolynomial.Gaussian)
  | _, _, _, _, .nil, _ => []
  | _, _, _, _, .cons head tail, previous =>
      (head.cap.firstValue - previous, (head.cap.joined.pairs.map Prod.fst).flatten) ::
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections.Evaluations.connectedBlocks tail
        head.cap.joined.lastValue

/-- Reuse each retained parent summary and prepend its actual connector when composing the complete path summary. -/
@[expose] def connectedSummary : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
  {covers : UniformReciprocalCover.ParentCovers parents} →
    {prepared : ParentJoins.SideBank regular covers} → {requests : SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared} →
    (evaluated : SideBank.Evaluations sample depth readingIndex requests) → (previous : InverseRootPolynomial.Gaussian)
      →
      IncrementArea.Summary ((Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections.Evaluations.connectedBlocks
        evaluated previous).map (fun block => block.1 :: block.2)).flatten
  | _, _, _, _, .nil, _ => IncrementArea.Summary.build []
  | _, _, _, _, .cons head tail, previous =>
      (Summary.prepend head.cap.joined.summary (head.cap.firstValue - previous)).append
        (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections.Evaluations.connectedSummary tail
        head.cap.joined.lastValue)

/-- The complete connected summary telescopes to the actual last retained primitive value minus the supplied initial
value. -/
theorem connected_total {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} {covers :
  UniformReciprocalCover.ParentCovers parents}
    {prepared : ParentJoins.SideBank regular covers} {requests : SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared}
    (evaluated : SideBank.Evaluations sample depth readingIndex requests) (previous : InverseRootPolynomial.Gaussian) :
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections.Evaluations.connectedSummary evaluated previous).total
      = Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections.Evaluations.lastValue evaluated previous - previous
      := by
  induction evaluated generalizing previous with
  | nil => change (0 : InverseRootPolynomial.Gaussian) = previous - previous; ring1
  | cons head tail ih =>
      change head.cap.firstValue - previous + head.cap.joined.summary.total +
        (Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections.Evaluations.connectedSummary tail
        head.cap.joined.lastValue).total = _
      rw [head.cap.joined.total_eq, ih]
      change head.cap.firstValue - previous + (head.cap.joined.lastValue - head.cap.firstValue) +
        (Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections.Evaluations.lastValue tail
          head.cap.joined.lastValue - head.cap.joined.lastValue) =
          Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections.Evaluations.lastValue tail
          head.cap.joined.lastValue - previous
      ring1

/-- There is exactly one connected block for every original retained parent. -/
theorem connected_length {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} {covers :
  UniformReciprocalCover.ParentCovers parents}
    {prepared : ParentJoins.SideBank regular covers} {requests : SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared}
    (evaluated : SideBank.Evaluations sample depth readingIndex requests) (previous : InverseRootPolynomial.Gaussian) :
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections.Evaluations.connectedBlocks evaluated previous).length
      = parents.length := by
  induction evaluated generalizing previous with
  | nil => rfl
  | cons head tail ih => exact congrArg Nat.succ (ih _)

/-- Removing each actual connector recovers the exact ordered complete parent paths. -/
theorem connected_paths {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} {covers :
  UniformReciprocalCover.ParentCovers parents}
    {prepared : ParentJoins.SideBank regular covers} {requests : SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared}
    (evaluated : SideBank.Evaluations sample depth readingIndex requests) (previous : InverseRootPolynomial.Gaussian) :
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections.Evaluations.connectedBlocks evaluated previous).map
      Prod.snd = evaluated.pairs.map Prod.snd := by
  induction evaluated generalizing previous with
  | nil => rfl
  | cons head tail ih => exact congrArg (List.cons _) (ih _)

/-- Every retained connected block's actual connector satisfies the supplied common gap budget. -/
theorem connected_small {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} {covers :
  UniformReciprocalCover.ParentCovers parents}
    {prepared : ParentJoins.SideBank regular covers} {requests : SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared}
    (evaluated : SideBank.Evaluations sample depth readingIndex requests) (previous : InverseRootPolynomial.Gaussian)
      {target : InverseRootPolynomial.Coordinate}
    (small : Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections.Evaluations.GapsSmall evaluated previous
      target) :
    ∀ block ∈ Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections.Evaluations.connectedBlocks evaluated
      previous, Data.Gaussian.Norm.Basic.normSq block.1 ≤ target := by
  induction evaluated generalizing previous with
  | nil => intro _ member; exact False.elim (List.not_mem_nil member)
  | cons head tail ih =>
      intro block member
      rcases Data.List.Membership.mem_cons.mp member with equal | member
      · exact equal ▸ small.1
      · exact ih _ small.2 block member

end Evaluations
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections
