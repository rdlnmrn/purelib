module
import Purelib.Data.List.Membership
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ClosingJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Endpoints
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JunctionRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Path.IncrementRestoration
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.StageEnergyEndpoints
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ClosingRequests
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
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
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndpoints

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Riemann.Branches

open Purelib.Riemann.Integration

open Purelib.Riemann.Normalization

public section

/-!
# Retained energy endpoints independent of local request budgets

The endpoint packets contain the actual root readings, primitive values and
shifted potentials. Their parent-bank index preserves mathematical ownership
when adjoining surface segments used different local requests.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Integration.Path.BoundaryRibbon (area)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndpoints.ReciprocalDiskVertices (EnergyEndpoint)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover ParentCovers)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison (Preparation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank (Links)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections (JunctionRequests)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ClosingJoins (LastJoin ClosingJoin)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ClosingRequests (LastRequest ClosingRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings.Endpoint (Reading)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {parent : CenteredEdge curve differential} {patch :
    PreparedPatch parent}
  {data : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count} {cover :
    Cover data}
  {index readingIndex energyDepth : Nat} {box : Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box} {target
    joining : Coordinate} {joinFloor : Nat}

namespace EnergyEndBank

set_option genInjectivity false in
/-- The actual synchronized endpoint roots, primitive readings and shifted energy potentials of one retained parent.

Both endpoint certificates share the original cap sample, reading stage and radial depth independently of local
preparation budgets. -/
structure EnergyEnds (sample : Primitives.Sample cap differential index box)
    (readingIndex energyDepth : Nat) (target : InverseRootPolynomial.Coordinate) (prepared :
      ParentComparison.Preparation regular cover) where
  /-- The actual original first endpoint approximation on the retained cap sample. -/ first :
    Coordinates.Overlap.Endpoint prepared.boundary.first.point.coordinates sample
  /-- The cached original first endpoint root reading at the shared stage. -/ firstReading :
    ChartReadings.Endpoint.Reading first readingIndex
  /-- The actual original terminal endpoint approximation on that same retained cap sample. -/ last :
    Coordinates.Overlap.Endpoint prepared.boundary.last.point.coordinates sample
  /-- The cached original terminal endpoint root reading at the shared stage. -/ lastReading :
    ChartReadings.Endpoint.Reading last readingIndex
  /-- The cached actual primitive reading at the original first endpoint. -/ firstValue : InverseRootPolynomial.Gaussian
  /-- The first primitive-value cache is exactly the retained endpoint approximation sample. -/ first_value :
    first.approximation.sample readingIndex = firstValue
  /-- The cached actual primitive reading at the original terminal endpoint. -/ lastValue :
    InverseRootPolynomial.Gaussian
  /-- The last primitive-value cache is exactly the retained endpoint approximation sample. -/ last_value :
    last.approximation.sample readingIndex = lastValue
  /-- The cached shifted radial potential of the original first endpoint. -/ firstPotential :
    InverseRootPolynomial.Gaussian
  /-- The cached shifted radial potential of the original terminal endpoint. -/ lastPotential :
    InverseRootPolynomial.Gaussian
  /-- The retained first potential and reading satisfy the original energy endpoint certificate. -/ first_bound :
    ReciprocalDiskVertices.EnergyEndpoint sample regular energyDepth target firstReading.coordinate firstValue
    firstPotential
  /-- The retained terminal potential and reading satisfy that same original energy target. -/ last_bound :
    ReciprocalDiskVertices.EnergyEndpoint sample regular energyDepth target lastReading.coordinate lastValue
    lastPotential

constructive_injectivity EnergyEnds

end EnergyEndBank

namespace EnergyEndBank.EnergyEnds

variable {prepared : Preparation regular cover}

/-- Enlarge the original endpoint-error target while preserving the exact roots, readings and potential caches. -/
@[expose] def weaken (ends : Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndBank.EnergyEnds sample readingIndex
  energyDepth target prepared) {larger : InverseRootPolynomial.Coordinate} (le : target ≤ larger) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndBank.EnergyEnds sample readingIndex energyDepth larger prepared
      :=
  { ends with
    first_bound := ⟨ends.first_bound.potential_eq, ends.first_bound.offset.trans le, ends.first_bound.small,
      ends.first_bound.inside⟩
    last_bound := ⟨ends.last_bound.potential_eq, ends.last_bound.offset.trans le, ends.last_bound.small,
      ends.last_bound.inside⟩ }

variable {otherCount : Nat} {otherParent : CenteredEdge curve
  differential}
  {otherPatch : PreparedPatch otherParent}
  {otherData : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data otherPatch otherCount}
    {otherCover : Cover otherData}
  {next : Preparation regular otherCover}

/-- The actual neighboring energy-potential discrepancy, including its endpoint wedge, satisfies the original endpoint
and junction budgets. -/
theorem join_bound (left : Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndBank.EnergyEnds sample readingIndex
  energyDepth target prepared)
    (right : Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndBank.EnergyEnds sample readingIndex energyDepth target
      next)
    (branch : HyperellipticReciprocal.originOrder curve = 1) (small : joining ≤ 1)
    {joined : ArcOwners.Join prepared.boundary.last.point next.boundary.first.point}
    (request : JunctionRequests.Request prepared.boundary.last.bounds joined joining joinFloor) (later : request.index ≤
      readingIndex) :
    Data.Gaussian.Norm.Basic.normSq (right.firstPotential - left.lastPotential - BoundaryRibbon.area
      left.lastValue right.firstValue) ≤ 80 * target + 2 * joining := by
  have radial := request.radial_accurate left.lastReading right.firstReading branch left.last_bound.inside
    right.first_bound.inside later later energyDepth
  have gap := request.accurate left.last right.first later later
  rw [left.last_value, right.first_value] at gap
  rw [left.last_bound.potential_eq, right.first_bound.potential_eq]
  exact IncrementRestoration.potential_join_bound radial.le left.last_bound.offset right.first_bound.offset
    right.first_bound.small (gap.le.trans small)

end EnergyEndBank.EnergyEnds

section SideBank

set_option genInjectivity false in
/-- The ordered complete energy endpoint bank indexed by the original retained side preparation. -/
inductive EnergyEndBank (sample : Primitives.Sample cap differential index box)
    (readingIndex energyDepth : Nat) (target : InverseRootPolynomial.Coordinate) :
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
      UniformReciprocalCover.ParentCovers parents} → ParentJoins.SideBank regular covers → Type 2
  /-- The empty original side bank retains no energy endpoint packets. -/ | nil :
    EnergyEndBank sample readingIndex
    energyDepth target .nil
  /-- Retain one original parent's energy endpoints before the exact remaining side bank. -/ | cons {parent :
    PreparedSubdivisionModelCore.CenteredEdge curve differential} {parents : List
    (PreparedSubdivisionModelCore.CenteredEdge curve differential)}
      {patch : UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data : UniformReciprocalModels.Data patch
        genus}
      {cover : UniformReciprocalCover.Cover data} {covers : UniformReciprocalCover.ParentCovers parents}
      {head : ParentComparison.Preparation regular cover} {tail : ParentJoins.SideBank regular covers}
      (ends : Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndBank.EnergyEnds sample readingIndex energyDepth
        target head)
      (remaining : EnergyEndBank sample
        readingIndex energyDepth target tail) :
        EnergyEndBank sample readingIndex
        energyDepth target (.cons head tail)

constructive_injectivity EnergyEndBank

namespace EnergyEndBank

variable {parents : List (CenteredEdge curve differential)}
  {covers : ParentCovers parents}
  {prepared : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank regular covers}

/-- Enlarge the common endpoint target throughout the actual original side bank without changing its retained data. -/
@[expose] def weaken {larger : InverseRootPolynomial.Coordinate} (le : target ≤ larger) :
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
      UniformReciprocalCover.ParentCovers parents} → {prepared : ParentJoins.SideBank regular covers} →
    EnergyEndBank sample readingIndex energyDepth
      target prepared → EnergyEndBank sample
      readingIndex energyDepth larger prepared
  | _, _, _, .nil => .nil
  | _, _, _, .cons head tail => .cons (head.weaken le)
    (weaken le tail)

/-- Read the first actual cached primitive value, returning zero for an empty original bank. -/
@[expose] def firstValue : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
  UniformReciprocalCover.ParentCovers parents} → {prepared : ParentJoins.SideBank regular covers} →
    EnergyEndBank sample readingIndex energyDepth
      target prepared → InverseRootPolynomial.Gaussian
  | _, _, _, .nil => 0
  | _, _, _, .cons head _ => head.firstValue

/-- Read the first actual cached shifted potential, returning zero for an empty original bank. -/
@[expose] def firstPotential : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers
  : UniformReciprocalCover.ParentCovers parents} → {prepared : ParentJoins.SideBank regular covers} →
    EnergyEndBank sample readingIndex energyDepth
      target prepared → InverseRootPolynomial.Gaussian
  | _, _, _, .nil => 0
  | _, _, _, .cons head _ => head.firstPotential

/-- Read the last actual cached primitive value, retaining the supplied previous value for an empty tail. -/
@[expose] def lastValue : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
  UniformReciprocalCover.ParentCovers parents} → {prepared : ParentJoins.SideBank regular covers} →
    EnergyEndBank sample readingIndex energyDepth
      target prepared → InverseRootPolynomial.Gaussian → InverseRootPolynomial.Gaussian
  | _, _, _, .nil, previous => previous
  | _, _, _, .cons head tail, _ => tail.lastValue head.lastValue

/-- Read the last actual cached shifted potential, retaining the supplied previous potential for an empty tail. -/
@[expose] def lastPotential : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers
  : UniformReciprocalCover.ParentCovers parents} → {prepared : ParentJoins.SideBank regular covers} →
    EnergyEndBank sample readingIndex energyDepth
      target prepared → InverseRootPolynomial.Gaussian → InverseRootPolynomial.Gaussian
  | _, _, _, .nil, previous => previous
  | _, _, _, .cons head tail, _ => tail.lastPotential head.lastPotential

/-- Read each actual inter-parent potential discrepancy with its original endpoint wedge in retained parent order. -/
@[expose] def errors : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
  UniformReciprocalCover.ParentCovers parents} → {prepared : ParentJoins.SideBank regular covers} →
    EnergyEndBank sample readingIndex energyDepth
      target prepared → InverseRootPolynomial.Gaussian → InverseRootPolynomial.Gaussian → List
      InverseRootPolynomial.Gaussian
  | _, _, _, .nil, _, _ => []
  | _, _, _, .cons head tail, value, potential =>
      (head.firstPotential - potential - BoundaryRibbon.area value head.firstValue) :: tail.errors head.lastValue
        head.lastPotential

/-- The actual initial connector satisfies the supplied bound, or the retained bank is empty. -/
@[expose] def FirstBound : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
  UniformReciprocalCover.ParentCovers parents} → {prepared : ParentJoins.SideBank regular covers} →
    EnergyEndBank sample readingIndex energyDepth
      target prepared → InverseRootPolynomial.Gaussian → InverseRootPolynomial.Gaussian →
      InverseRootPolynomial.Coordinate → Prop
  | _, _, _, .nil, _, _, _ => True
  | _, _, _, .cons head _, value, potential, bound => Data.Gaussian.Norm.Basic.normSq (head.firstPotential -
    potential - BoundaryRibbon.area value head.firstValue) ≤ bound

/-- There is exactly one retained connector error per actual original parent. -/
theorem errors_count (ends : EnergyEndBank sample
  readingIndex energyDepth target prepared) (value potential : InverseRootPolynomial.Gaussian) :
    (ends.errors value potential).length = parents.length := by
  induction ends generalizing value potential with
  | nil => rfl
  | cons head tail ih => exact congrArg Nat.succ (ih head.lastValue head.lastPotential)

/-- Every actual retained connector error satisfies the original endpoint and paid junction budgets. -/
theorem errors_bounded (branch : HyperellipticReciprocal.originOrder curve = 1) (small : joining ≤ 1) :
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
      UniformReciprocalCover.ParentCovers parents} → {prepared : ParentJoins.SideBank regular covers} →
    (ends : EnergyEndBank sample readingIndex
      energyDepth target prepared) → {links : SideBank.Links prepared} →
    (requests : SideConnections.JunctionRequests joining joinFloor prepared links) → requests.maximum ≤ readingIndex →
    (value potential : InverseRootPolynomial.Gaussian) → ends.FirstBound value potential (80 * target + 2 * joining) →
    ∀ error ∈ ends.errors value potential, Data.Gaussian.Norm.Basic.normSq error ≤ 80 * target + 2 * joining
  | _, _, _, .nil, _, _, _, _, _, _, _, member => by cases member
  | _, _, _, .cons head tail, links, requests, later, value, potential, first, error, member => by
      rcases Data.List.Membership.mem_cons.mp member with same | member
      · subst error; exact first
      · cases tail with
        | nil => cases member
        | cons next rest =>
            cases links with
            | cons joined remaining =>
                exact
                  errors_bounded
                  branch small (.cons next rest) requests.2 ((Data.Nat.Order.le_max_right _ _).trans later) _ _
                  (head.join_bound next branch small requests.1 ((Data.Nat.Order.le_max_left _ _).trans later)) error
                    member

/-- The actual final connector to the supplied original first endpoint satisfies the retained root-return budget. -/
theorem last_closing_bound (branch : HyperellipticReciprocal.originOrder curve = 1) (small : joining ≤ 1)
    {destination : ParentComparison.Preparation regular cover} (first :
      EnergyEnds sample readingIndex energyDepth target
      destination) :
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
      UniformReciprocalCover.ParentCovers parents} → {prepared : ParentJoins.SideBank regular covers} →
    (ends : EnergyEndBank sample readingIndex
      energyDepth target prepared) → {joined : ClosingJoins.LastJoin destination prepared} →
    (request : ClosingRequests.LastRequest destination joining joinFloor prepared joined) → request.maximum ≤
      readingIndex → parents ≠ [] →
    (value potential : InverseRootPolynomial.Gaussian) →
    Data.Gaussian.Norm.Basic.normSq (first.firstPotential - ends.lastPotential potential - BoundaryRibbon.area
      (ends.lastValue value) first.firstValue) ≤ 80 * target + 2 * joining
  | _, _, _, .nil, _, _, _, nonempty, _, _ => False.elim (nonempty rfl)
  | _, _, _, .cons head tail, _, request, later, _, value, potential => by
      cases tail with
      | nil => exact head.join_bound first branch small request later
      | cons next rest =>
          exact
            last_closing_bound
            branch small first (.cons next rest) request later
            (by intro same; cases same) head.lastValue head.lastPotential

/-- The actual closing connector of the complete retained side bank satisfies its original endpoint and junction budget.
-/
theorem closing_bound (ends : EnergyEndBank sample
  readingIndex energyDepth target prepared)
    (branch : HyperellipticReciprocal.originOrder curve = 1) (nonnegative : 0 ≤ target) (joinNonnegative : 0 ≤ joining)
      (small : joining ≤ 1)
    {joined : ClosingJoins.ClosingJoin prepared} (request : ClosingRequests.ClosingRequest joining joinFloor prepared
      joined) (later : request.maximum ≤ readingIndex) :
    Data.Gaussian.Norm.Basic.normSq (ends.firstPotential - ends.lastPotential ends.firstPotential -
      BoundaryRibbon.area (ends.lastValue ends.firstValue) ends.firstValue) ≤ 80 * target + 2 * joining := by
  cases ends with
  | nil =>
      change Data.Gaussian.Norm.Basic.normSq ((0 : InverseRootPolynomial.Gaussian) - 0 - BoundaryRibbon.area 0
        0) ≤ _
      rw [Data.Gaussian.Basic.sub_self, IncrementArea.area_self, Data.Gaussian.Basic.sub_zero,
        Data.Gaussian.Norm.Basic.normSq_zero]
      exact add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) nonnegative)
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) joinNonnegative)
  | cons head tail =>
      exact last_closing_bound branch
        small head (.cons head tail) request later
        (by intro same; cases same) head.firstValue head.firstPotential

/-- The residual around this exact original root bank is a finite sum of its join errors and its final root-return
error. -/
@[expose] def residual (ends : EnergyEndBank sample
  readingIndex energyDepth target prepared) : Gaussian :=
  -(Data.Gaussian.Norm.Sum.Basic.gaussianSum (ends.errors ends.firstValue ends.firstPotential) +
    (ends.firstPotential - ends.lastPotential ends.firstPotential - BoundaryRibbon.area (ends.lastValue ends.firstValue)
      ends.firstValue))

/-- The actual complete energy residual satisfies the count-weighted original join and root-return bounds. -/
theorem residual_bound (ends : EnergyEndBank sample
  readingIndex energyDepth target prepared)
    (branch : HyperellipticReciprocal.originOrder curve = 1) (nonnegative : 0 ≤ target) (joinNonnegative : 0 ≤ joining)
      (small : joining ≤ 1)
    {links : SideBank.Links prepared} (requests : SideConnections.JunctionRequests joining joinFloor prepared links)
      (later : requests.maximum ≤ readingIndex)
    {joined : ClosingJoins.ClosingJoin prepared} (closing : ClosingRequests.ClosingRequest joining joinFloor prepared
      joined) (closingLater : closing.maximum ≤ readingIndex) :
    Data.Gaussian.Norm.Basic.normSq ends.residual ≤ 2 * (((parents.length : InverseRootPolynomial.Coordinate) *
      ((parents.length : InverseRootPolynomial.Coordinate) * (80 * target + 2 * joining))) + (80 * target + 2 *
      joining)) := by
  have initial : ends.FirstBound ends.firstValue ends.firstPotential (80 * target + 2 * joining) := by
    cases ends with
    | nil => trivial
    | cons head tail =>
        change Data.Gaussian.Norm.Basic.normSq (head.firstPotential - head.firstPotential - BoundaryRibbon.area
          head.firstValue head.firstValue) ≤ _
        rw [Data.Gaussian.Basic.sub_self, IncrementArea.area_self, Data.Gaussian.Basic.sub_zero,
          Data.Gaussian.Norm.Basic.normSq_zero]
        exact add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) nonnegative)
          (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) joinNonnegative)
  have sumBound := Data.Gaussian.Norm.Sum.Bounds.normSq_sum_le _ _ (ends.errors_bounded branch small requests later _ _
    initial)
  rw [ends.errors_count] at sumBound
  rw [residual,
    Data.Gaussian.Norm.Basic.normSq_neg]
  exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (add_le_add sumBound (ends.closing_bound branch nonnegative joinNonnegative small closing closingLater)) (by
      decide))

end EnergyEndBank
end SideBank
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
