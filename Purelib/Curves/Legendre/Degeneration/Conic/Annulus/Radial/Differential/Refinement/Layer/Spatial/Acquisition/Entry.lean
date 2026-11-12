module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Spatial.Acquisition
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Reading.Time
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Data.List.Membership

/-! # A supplied original source Owner entering the SAME actual finer numerical layer

One finite decomposition reads the original nonempty Layer's actual first
piece and tail. Original source factory receipts identify that SAME first
Reading with the initial cache by exact time-index transport. The supplied
Owner and original comparison are transported unchanged; the actual paid
fold consumes these original pieces without another Source attachment.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Rational
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Integration.Partition
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (Endpoint)
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
open Transport.Spatial
open Transport.Spatial.Parallel

variable {radicand : CoefficientPolynomial}
variable {site : Fin 2} {parameter : Canonical} {differential : OddPowerDifferential radicand}
variable {data : Waist.Differential.Bounds.Data site parameter differential}
variable {quarter : UnitCircuitQuarter} {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive} {accuracy : AccuracyRequest}
variable {initial : Piece data actual accuracy} {depth : Nat} (layer : Layer initial depth)

attribute [local irreducible] Transport.Spatial.coordinate
attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

/-- A retained original Layer factory receipt transports erased source-query proofs, keeping the actual old cache. -/
theorem queried_of_factory (factory : layer = initial.layerAt depth) (queried : initial.Queried) :
    ∀ piece ∈ layer.pieces, piece.Queried :=
  Eq.mpr (congrArg (fun retained : Layer initial depth => ∀ piece ∈ retained.pieces, piece.Queried) factory)
    (initial.layerAt_queried queried depth)

/-- A retained original factory receipt supplies the actual cached Layer's original endpoint Chain. -/
theorem chain_of_factory (factory : layer = initial.layerAt depth) :
    Interval.Chain initial.span.lower initial.span.upper (Piece.chartIntervals layer.pieces) :=
  Eq.mpr (congrArg (fun retained : Layer initial depth =>
    Interval.Chain initial.span.lower initial.span.upper
      (Piece.chartIntervals retained.pieces)) factory) (initial.layerAt_chain depth)

/-- A finite view of this SAME nonempty original Layer's actual first piece and complete remaining list. -/
@[expose] def Decomposition : Type 1 :=
  Σ first : Piece data actual layer.accuracy,
    { remaining : List (Piece data actual layer.accuracy) // layer.pieces = first :: remaining }

namespace Decomposition

/-- Read one nonempty original list constructor and retain its actual head, tail and whole-list equation once. -/
def build : Decomposition layer := by
  cases same : layer.pieces with
  | nil =>
      have positive := layer.nonempty
      rewrite [same] at positive
      exact (Nat.not_lt_zero 0 positive).elim
  | cons first remaining => exact ⟨first, remaining, same⟩

variable {layer} (parts : Decomposition layer)

/-- Read the identical actual first old piece, including its scalar Model and original complete source Reading. -/
@[expose] def first : Piece data actual layer.accuracy := parts.1

/-- Read the identical complete original remaining piece list without dropping or rebuilding any source cache. -/
@[expose] def remaining : List (Piece data actual layer.accuracy) := parts.2.val

/-- The retained head/tail view is the whole SAME original Layer list, including order and repeated occurrences. -/
theorem pieces_eq : layer.pieces = parts.first :: parts.remaining := parts.2.property

/-- The retained first old piece is an actual occurrence of this SAME original Layer. -/
theorem first_member : parts.first ∈ layer.pieces :=
  Eq.mpr (congrArg (fun pieces => parts.first ∈ pieces) parts.pieces_eq) (List.Mem.head parts.remaining)

/-- Each retained tail occurrence is the corresponding actual occurrence of the SAME original Layer. -/
theorem remaining_member (piece : Piece data actual layer.accuracy) (member : piece ∈ parts.remaining) :
    piece ∈ layer.pieces :=
  Eq.mpr (congrArg (fun pieces => piece ∈ pieces) parts.pieces_eq) (List.Mem.tail parts.first member)

/-- The original cached Layer's first source time is exactly its original initial piece's source time. -/
theorem start_time (factory : layer = initial.layerAt depth) : parts.first.span.lower = initial.span.lower := by
  have chain := layer.chain_of_factory factory
  have reindexed := Eq.mp (congrArg (fun pieces =>
    Interval.Chain initial.span.lower initial.span.upper (Piece.chartIntervals pieces))
      parts.pieces_eq) chain
  exact Interval.Chain.start_eq reindexed (by
    change 0 < Nat.succ (Piece.chartIntervals parts.remaining).length
    exact Nat.zero_lt_succ _)

/-- Exact time transport identifies the complete SAME retained first source cache with the old initial query. -/
theorem firstSource_eq (factory : layer = initial.layerAt depth) (queried : initial.Queried) :
    Transport.Reading.castTime (parts.start_time factory) parts.first.source = initial.source := by
  have firstQueried := layer.queried_of_factory factory queried parts.first parts.first_member
  have reading := congrArg (Transport.Reading.castTime (lastInside :=
    initial.within initial.span.lower ⟨Fraction.Order.Basic.le_refl _, initial.span.valid⟩)
      (parts.start_time factory)) firstQueried.readback
  exact reading.trans ((Transport.Reading.castTime_build (parts.start_time factory)).trans queried.readback.symm)

/-- The exact first-source correspondence preserves the whole original Reading and all original caches. -/
theorem firstSource_heq (factory : layer = initial.layerAt depth) (queried : initial.Queried) :
    HEq parts.first.source initial.source :=
  (Transport.Reading.castTime_heq (parts.start_time factory) parts.first.source).symm.trans
    (heq_of_eq (parts.firstSource_eq factory queried))

/-- The actual original full-cubic name is unchanged by the first-source cache correspondence. -/
theorem firstName_eq (factory : layer = initial.layerAt depth) (queried : initial.Queried) :
    parts.first.source.lift.value.name = initial.source.lift.value.name := by
  have retained := congrArg (fun reading => reading.lift.value.name) (parts.firstSource_eq factory queried)
  have transported := congrArg (fun value => value.name)
    (Transport.Reading.castTime_lift_value (lastInside :=
      initial.within initial.span.lower ⟨Fraction.Order.Basic.le_refl _, initial.span.valid⟩)
      (parts.start_time factory) parts.first.source)
  exact transported.symm.trans retained

variable (sourceOwner : OwnerAt site parameter quarter positive initial.lowerEndpoint)

/-- Reindex the SAME supplied original initial Owner onto the identical actual cached first physical point. -/
@[expose] def startOwner (factory : layer = initial.layerAt depth) :
    OwnerAt site parameter quarter positive parts.first.lowerEndpoint :=
  RootIsolation.SquareRoot.Owner.Transport.castOwnerParameter
    (congrArg (fun time : Fraction.Rational => (Paths.polynomial parameter).eval
      (Transport.Spatial.coordinate site parameter 2 quarter positive time))
        (parts.start_time factory).symm) sourceOwner

/-- Exact first-point reindexing preserves the complete SAME original initial Owner/track and clearance data. -/
theorem startOwner_heq (factory : layer = initial.layerAt depth) :
    HEq (parts.startOwner sourceOwner factory) sourceOwner :=
  RootIsolation.SquareRoot.Owner.Transport.castOwnerParameter_heq _ sourceOwner

/-- Exact first-point reindexing preserves the SAME supplied initial Owner's actual root name. -/
theorem startOwner_name (factory : layer = initial.layerAt depth) :
    ownerRootName (parts.startOwner sourceOwner factory).parameterNonzero (parts.startOwner sourceOwner factory) =
      ownerRootName sourceOwner.parameterNonzero sourceOwner :=
  ownerRootName_castOwnerParameter _ sourceOwner

/-- Transport the original operational source comparison to the SAME old first Reading and unchanged supplied Owner. -/
def startAgreement (factory : layer = initial.layerAt depth) (queried : initial.Queried)
    (agreement : Parallel.Steps.Acquisition.InitialAgreement initial.lowerEndpoint initial.source sourceOwner) :
    Parallel.Steps.Acquisition.InitialAgreement parts.first.lowerEndpoint parts.first.source
      (parts.startOwner sourceOwner factory) :=
  NamedEquivalent.transport (parts.firstName_eq factory queried).symm
    (parts.startOwner_name sourceOwner factory).symm agreement

end Decomposition

namespace Spatial.Acquisition

variable {layer}
variable (parts : Decomposition layer) (factory : layer = initial.layerAt depth) (queried : initial.Queried)
variable {regular : parameter ≠ criticalValue site}
variable (finishQuery : { reading : ReadingAt actual initial.upperEndpoint //
  QueryCache actual initial.upperEndpoint reading })
variable (sourceOwner : OwnerAt site parameter quarter positive initial.lowerEndpoint)
variable (agreement : Parallel.Steps.Acquisition.InitialAgreement initial.lowerEndpoint initial.source sourceOwner)

/-- Realize this SAME cached original fine Layer using its exact queries, original initial Owner and one final cache.

The original factory receipt supplies erased Chain/query proofs only. The
runtime builder consumes parts.first/remaining directly. All paid head
factories run once; no layer, source Reading, Source attachment, scalar
Model or final observation is reconstructed from a readback equation.
-/
def ofLayer (enough : 7 ≤ depth) :
    Acquisition regular finishQuery parts.remaining parts.first
      (fun piece member => layer.queried_of_factory factory queried piece (parts.remaining_member piece member))
      (parts.startOwner sourceOwner factory) (parts.startAgreement sourceOwner factory queried agreement) :=
  have chain : Interval.Chain parts.first.span.lower initial.span.upper
      (Piece.chartIntervals (parts.first :: parts.remaining)) := by
    have original := Eq.mp (congrArg (fun pieces =>
      Interval.Chain initial.span.lower initial.span.upper (Piece.chartIntervals pieces))
        parts.pieces_eq) (layer.chain_of_factory factory)
    exact Eq.mpr (congrArg (fun time => Interval.Chain time initial.span.upper
      (Piece.chartIntervals (parts.first :: parts.remaining))) (parts.start_time factory)) original
  have widths : ∀ piece ∈ parts.first :: parts.remaining,
      piece.span.width ^ 2 ≤ Geometric.Basic.quarterRadius 1 7 := by
    intro piece member
    have actualMember := Eq.mpr (congrArg (fun pieces => piece ∈ pieces) parts.pieces_eq) member
    exact layer.width_le 7 enough piece actualMember
  build finishQuery parts.remaining parts.first
    (fun piece member => layer.queried_of_factory factory queried piece (parts.remaining_member piece member))
    (parts.startOwner sourceOwner factory) (parts.startAgreement sourceOwner factory queried agreement) chain widths

/-- The SAME original layer widths pay actual physical-query distances throughout this literal paid head/tail fold. -/
theorem ofLayer_pointPayments (enough : 7 ≤ depth) (physical : AccuracyRequest)
    (sufficient : Geometry.widthMinimum site parameter physical ≤ depth) :
    Acquisition.PointPayments (regular := regular) physical
      (ofLayer (regular := regular) parts factory queried finishQuery sourceOwner agreement enough) := by
  apply Acquisition.pointPayments (regular := regular) (finishQuery := finishQuery) physical
  intro piece member
  have actualMember := Eq.mpr (congrArg (fun pieces => piece ∈ pieces) parts.pieces_eq) member
  exact layer.width_le _ sufficient piece actualMember

end Spatial.Acquisition

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer

end
