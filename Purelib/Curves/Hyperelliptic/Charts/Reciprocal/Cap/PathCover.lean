module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EndpointComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocalCurve
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.CheckedPrimitiveNeighborhoods
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathGluing
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PrimitiveComparison
public import Purelib.Riemann.Paths.PreparedPathParentContainment
public import Purelib.Riemann.RootContinuation.PreparedCachedParentRoots
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootJoins
import Init.Data.Fin.Basic
import Init.Data.List.Lemmas
import Init.Data.Nat.Basic
import Init.Prelude
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.SegmentComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.UniformPrimitiveNeighborhoods
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Paths.TracedPrimitiveNeighborhood
import Purelib.Riemann.Readings.PreparedObservationNeighborhoods
import Purelib.Riemann.Readings.SeededPrimitiveBounds
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Approximation

open Purelib.Curves

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalComparison

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalModels

open Purelib.Curves.Hyperelliptic.Integration.Observation

open Purelib.Geometry.Path.Gaussian

open Purelib.Polynomial.Geometry

open Purelib.Riemann.Branches

open Purelib.Riemann.Integration

open Purelib.Riemann.Normalization

open Purelib.Riemann.Normalization.ContinuedInverseRoot

open Purelib.Riemann.Paths

open Purelib.Riemann.Paths.PreparedPathParentCaches

open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels

open Purelib.Riemann.Paths.PreparedPathParentContainment

open Purelib.Riemann.Paths.PreparedPathPrimitiveCover

open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels

open Purelib.Riemann.RootContinuation.PreparedCachedParentRoots

open Purelib.Riemann.Topology

public section

/-!
# Cap comparisons covering an entire retained prepared path

Reuse the actual complete path, its cached centered parents and its uniform
primitive cover. Every parent receives a cap comparison on that same patch,
with both endpoints certified inside the original cap rectangle. The bank is
indexed by the full parent list, preserving its order, multiplicity and owners.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalModels (Terminal)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)
open Purelib.Riemann.Topology.PreparedBankRootChains (ownerName)
open Purelib.Riemann.Integration.CheckedPrimitiveNeighborhoods (grow grow_base)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {collar :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}

/-- An original centered parent on the reciprocal curve with its exact reversed differential. -/
abbrev Parent (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (differential : Differentials.Basic.Differential
  genus) :=
  PreparedSubdivisionModelCore.CenteredEdge (HyperellipticReciprocalCurve.reciprocalCurve curve)
    (HyperellipticReciprocal.reversedDifferential differential)

/-- Reuse the original prepared parent patch as the cap terminal at its cached starting owner. -/
@[expose] public def terminalOfPatch (cap : ReciprocalInnerInverse.Data curve collar) {differential :
  Differentials.Basic.Differential genus}
    {parent : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve differential} (patch :
      UniformPrimitiveSheetCompatibility.PreparedPatch parent) (count : Nat) :
    TerminalModels.Terminal cap parent.edge.cached.preparedOwner count :=
  Terminal.ofNeighborhood cap ⟨patch.neighborhood count,
    (patch.center_eq count).trans parent.edge.point_zero, (by
      change Gaussian.Equivalence.NamedEquivalent (OwnerTraceReadings.ownerName parent.edge.cached.preparedOwner)
        (OwnerTraceReadings.ownerName (CheckedPrimitiveNeighborhoods.grow (patch.seed.neighborhood
          count)).base.seed.owner)
      rw [CheckedPrimitiveNeighborhoods.grow_base]
      exact patch.seed.rootEquivalent)⟩

set_option genInjectivity false in
/-- The exact patch equation ties the comparison model to the original prepared primitive cover, not merely to another
neighborhood at its center. -/
structure ParentData (cap : ReciprocalInnerInverse.Data curve collar) (differential : Differentials.Basic.Differential
  genus)
    (count : Nat) (parent : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve differential) where
  /-- The original retained uniform primitive patch for this exact prepared parent. -/ patch :
    UniformPrimitiveSheetCompatibility.PreparedPatch parent
  /-- The cap terminal using this original parent's cached starting root owner. -/ terminal : TerminalModels.Terminal
    cap parent.edge.cached.preparedOwner count
  /-- The terminal uses exactly the original patch neighborhood at the retained stage. -/ patch_eq :
    terminal.neighborhood.patch = patch.neighborhood count
  /-- The cached terminal comparison for the original differential. -/ comparison : TerminalComparison.Data terminal
    differential
  /-- The retained comparison segment with the original parent endpoints. -/ segment : TerminalComparison.LocalSegment
    comparison
  /-- The retained segment starts at the original parent's parameter-zero point. -/ first_eq : segment.comparison.first
    = parent.edge.point 0
  /-- The retained segment finishes at the original parent's parameter-one point. -/ last_eq : segment.comparison.last =
    parent.edge.point 1
  /-- The original segment's prepared endpoint comparison data. -/ data : PrimitiveComparison.Data segment

constructive_injectivity ParentData

namespace ParentData

/-- Build one retained parent comparison from the original patch and its certified endpoint containment. -/
@[expose] def ofPatch (cap : ReciprocalInnerInverse.Data curve collar) {differential : Differentials.Basic.Differential
  genus}
    (count : Nat) {parent : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve differential} (patch :
      UniformPrimitiveSheetCompatibility.PreparedPatch parent)
    (finishInside : (patch.neighborhood count).box.Contains (parent.edge.point 1))
    (firstCap : collar.box.Contains (parent.edge.point 0)) (lastCap : collar.box.Contains (parent.edge.point 1)) :
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.ParentData cap differential count parent :=
  let terminal := Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.terminalOfPatch cap patch count
  let comparison := TerminalComparison.Data.build terminal differential
  let segment := LocalSegment.build comparison (parent.edge.point 0) (parent.edge.point 1)
    (patch.start_inside count) finishInside firstCap lastCap
  ⟨patch, terminal, rfl, comparison, segment, rfl, rfl, PrimitiveComparison.Data.build segment⟩

/-- Transport the original parent root comparison across equality with its retained neighborhood. -/
@[expose] public def pointEquivalent {differential : Differentials.Basic.Differential genus} {parent :
  Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve differential} {count : Nat}
    (patch : UniformPrimitiveSheetCompatibility.PreparedPatch parent) (neighborhood :
      ContinuedInverseRoot.ContinuedNeighborhood (HyperellipticReciprocal.polynomial curve) count)
    (equal : neighborhood = patch.neighborhood count) (fraction : InverseRootPolynomial.Coordinate) (inside : 0 ≤
      fraction ∧ fraction ≤ 1)
    {point : InverseRootPolynomial.Gaussian} (pointEq : parent.edge.point fraction = point) (contained :
      neighborhood.box.Contains point)
    (sample : ContinuedNeighborhood.Point neighborhood point) :
    Gaussian.Equivalence.NamedEquivalent (parent.edge.rootName fraction inside) sample.certificate.value.name := by
  cases equal
  exact patch.point_equivalent_at count fraction inside pointEq contained sample

/-- Any retained point in the parent's comparison patch keeps that parent's query occurrence at its certified parameter.
-/
@[expose] def point_owner {cap : ReciprocalInnerInverse.Data curve collar} {differential :
  Differentials.Basic.Differential genus} {count : Nat}
    {parent : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve differential} (data :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.ParentData cap differential count parent)
    (fraction : InverseRootPolynomial.Coordinate) (inside : 0 ≤ fraction ∧ fraction ≤ 1) {point :
      InverseRootPolynomial.Gaussian}
    (pointEq : parent.edge.point fraction = point) (prepared : EndpointComparison.PreparedPoint data.comparison point) :
    Gaussian.Equivalence.NamedEquivalent (parent.edge.rootName fraction inside) prepared.point.certificate.value.name :=
  Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.ParentData.pointEquivalent data.patch
    data.terminal.neighborhood.patch data.patch_eq fraction inside pointEq prepared.data.inside prepared.point

/-- The first cap endpoint retains the actual prepared parent's root channel. -/
@[expose] def first_owner {cap : ReciprocalInnerInverse.Data curve collar} {differential :
  Differentials.Basic.Differential genus} {count : Nat}
    {parent : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve differential} (data :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.ParentData cap differential count parent) :
    Gaussian.Equivalence.NamedEquivalent (parent.edge.rootName 0 (by decide))
      data.data.first.point.certificate.value.name :=
  data.point_owner 0 (by decide) data.first_eq.symm data.data.first

/-- The last endpoint uses the same continuation occurrence as the original parent's terminal query, including after
uniform seed reconditioning. -/
@[expose] def last_owner {cap : ReciprocalInnerInverse.Data curve collar} {differential :
  Differentials.Basic.Differential genus} {count : Nat}
    {parent : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve differential} (data :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.ParentData cap differential count parent) :
    Gaussian.Equivalence.NamedEquivalent (parent.edge.rootName 1 (by decide))
      data.data.last.point.certificate.value.name :=
  data.point_owner 1 (by decide) data.last_eq.symm data.data.last

/-- Connect two retained local presentations at the same parent parameter. The supplied point records are consumed
directly, including refined endpoints. -/
@[expose] def point_join {cap : ReciprocalInnerInverse.Data curve collar} {differential :
  Differentials.Basic.Differential genus} {count : Nat}
    {parent : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve differential} (data :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.ParentData cap differential count parent)
    (fraction : InverseRootPolynomial.Coordinate) (inside : 0 ≤ fraction ∧ fraction ≤ 1) {first last :
      InverseRootPolynomial.Gaussian}
    (firstEq : parent.edge.point fraction = first) (lastEq : parent.edge.point fraction = last)
    (firstPoint : EndpointComparison.PreparedPoint data.comparison first)
    (lastPoint : EndpointComparison.PreparedPoint data.comparison last) :
    RootCoordinates.Overlap.Join firstPoint.coordinates lastPoint.coordinates :=
  Join.build firstPoint.coordinates lastPoint.coordinates (firstEq.symm.trans lastEq) (by
    rw [firstPoint.coordinates.reciprocal_eq, lastPoint.coordinates.reciprocal_eq]
    exact (data.point_owner fraction inside firstEq firstPoint).symm.trans (data.point_owner fraction inside lastEq
      lastPoint))

end ParentData

set_option genInjectivity false in
/-- One certified cap comparison for every original parent occurrence. -/
inductive Bank (cap : ReciprocalInnerInverse.Data curve collar) (differential : Differentials.Basic.Differential genus)
  (count : Nat) :
    List (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve differential) → Type 3
  /-- The empty original parent spine carries the required empty comparison data. -/ | nil :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank cap differential count []
  /-- Retain the exact original head parent comparison and the matching ordered tail. -/ | cons {parent :
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve differential} {parents : List
    (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve differential)}
      (data : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.ParentData cap differential count parent) (remaining
        : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank cap differential count parents) :
      Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank cap differential count (parent :: parents)

constructive_injectivity Bank

namespace Bank

open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

/-- Build a cap comparison for every original covered parent while preserving its occurrence order. -/
@[expose] def ofCovered (cap : ReciprocalInnerInverse.Data curve collar) {differential :
  Differentials.Basic.Differential genus} (count : Nat) :
    {parents : List (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve differential)} →
      UniformPreparedMesh.CoveredParents count parents →
      (∀ parent ∈ parents, collar.box.Contains (parent.edge.point 0) ∧ collar.box.Contains (parent.edge.point 1)) →
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank cap differential count parents
  | _, .nil, _ => .nil
  | _, .cons patch inside remaining, contained =>
      .cons (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.ParentData.ofPatch cap count patch inside (contained _
        (List.mem_cons_self ..)).1 (contained _ (List.mem_cons_self ..)).2)
        (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.ofCovered cap count remaining (fun parent
          member => contained parent (List.mem_cons_of_mem _ member)))

variable {cap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus} {count : Nat}

/-- Finite lookup preserves the exact retained occurrence. -/
@[expose] def get : {parents : List (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve differential)} →
  Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank cap differential count parents →
    (index : Fin parents.length) → Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.ParentData cap differential
      count (parents[index])
  | [], .nil, index => Fin.elim0 index
  | _ :: _, .cons data remaining, index =>
      match index with
      | ⟨0, _⟩ => data
      | ⟨index + 1, inside⟩ => remaining.get ⟨index, Nat.lt_of_succ_lt_succ inside⟩

set_option genInjectivity false in
/-- The actual cap endpoint owners are joined in retained parent order. These links include the original path owners at
both external boundaries. -/
inductive RootLinks : {parents : List (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve differential)}
  →
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank cap differential count parents →
      PreparedRefinementRootChains.Named → PreparedRefinementRootChains.Named → Type 3
  /-- Retain the operational root comparison between the external owners of an empty original bank. -/ | nil {first last
    : PreparedRefinementRootChains.Named} (equivalent : Gaussian.Equivalence.NamedEquivalent first last) :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.RootLinks .nil first last
  /-- Retain the original head endpoint ownership comparison and the linked original tail. -/ | cons {parent :
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve differential} {parents : List
    (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve differential)}
      (data : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.ParentData cap differential count parent) (remaining
        : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank cap differential count parents)
      {first last : PreparedRefinementRootChains.Named} (entry : Gaussian.Equivalence.NamedEquivalent first
        data.data.first.point.certificate.value.name)
      (tail : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.RootLinks remaining
        data.data.last.point.certificate.value.name last) :
      Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.RootLinks (.cons data remaining) first last

constructive_injectivity RootLinks

namespace RootLinks

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.RootLinks in
/-- Use the existing local patch ownership comparisons and the root chain of the same cached parents. No new cap
endpoint is prepared here. -/
@[expose] def ofParentChain : ∀ {parents : List (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve
  differential)} (bank : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank cap differential count parents)
    {first last : PreparedRefinementRootChains.Named}, PreparedRefinementRootChains.RootChain parents first last →
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.RootLinks bank first last
  | [], .nil, _, _, .nil equivalent => .nil equivalent
  | _ :: _, .cons data remaining, _, _, .cons _ entry tail =>
      .cons data remaining (entry.trans data.first_owner)
        (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.RootLinks.ofParentChain remaining
          (tail.changeStart data.last_owner.symm))

/-- Read the retained external-to-first-endpoint root comparison. -/
@[expose] def entry {parent : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve differential} {parents :
  List (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve differential)}
    {data : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.ParentData cap differential count parent} {remaining :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank cap differential count parents}
    {first last : PreparedRefinementRootChains.Named} :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.RootLinks (.cons data remaining) first last →
      Gaussian.Equivalence.NamedEquivalent first data.data.first.point.certificate.value.name
  | .cons _ _ equivalent _ => equivalent

/-- Read the retained original tail of the root or coordinate join spine. -/
@[expose] def tail {parent : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve differential} {parents :
  List (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve differential)}
    {data : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.ParentData cap differential count parent} {remaining :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank cap differential count parents}
    {first last : PreparedRefinementRootChains.Named} :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.RootLinks (.cons data remaining) first last →
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.RootLinks remaining
        data.data.last.point.certificate.value.name last
  | .cons _ _ _ remaining => remaining

/-- Extract the next certified join; `tail` exposes all subsequent joins. -/
@[expose] def adjacent {parent next : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve differential}
  {parents : List (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve differential)}
    {data : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.ParentData cap differential count parent} {nextData :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.ParentData cap differential count next}
    {remaining : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank cap differential count parents} {first last :
      PreparedRefinementRootChains.Named}
    (roots : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.RootLinks (.cons data (.cons nextData remaining))
      first last) :
    Gaussian.Equivalence.NamedEquivalent data.data.last.point.certificate.value.name
      nextData.data.first.point.certificate.value.name :=
  roots.tail.entry

end RootLinks

/-- The endpoint coordinates of neighboring comparisons are literally the same. This property is separate from their
operational root ownership. -/
@[expose] def Junctions : {parents : List (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve
  differential)} → Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank cap differential count parents → Prop
  | _, .nil => True
  | _, .cons _ .nil => True
  | _, .cons data (.cons next remaining) =>
      data.segment.comparison.last = next.segment.comparison.first ∧
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.Junctions (.cons next remaining)

/-- The head parent's initial coordinate is the original centered path chain's starting coordinate. -/
public theorem head_coordinate {parent : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve
  differential} {parents : List (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve differential)}
    {first last : Lifted.Basic.LiftedPoint 2}
    (chain : PreparedDirectDyadicRefinements.CenteredPathChain (parent :: parents) (start := first) (finish := last)) :
    parent.edge.point 0 = first.coordinate := by
  cases chain
  exact parent.edge.point_zero

/-- The original centered path chain supplies exact coordinate junctions between retained neighboring cap comparisons.
-/
theorem junctionsOfChain : ∀ {parents : List (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve
  differential)} (bank : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank cap differential count parents)
    {first last : Lifted.Basic.LiftedPoint 2},
    PreparedDirectDyadicRefinements.CenteredPathChain parents (start := first) (finish := last) →
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.Junctions bank
  | [], .nil, _, _, _ => trivial
  | [_], .cons _ .nil, _, _, _ => trivial
  | parent :: _ :: _, .cons data (.cons next remaining), _, _, .cons _ tail =>
      ⟨data.last_eq.trans ((parent.edge.point_one.trans
        (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.head_coordinate tail).symm).trans
        next.first_eq.symm),
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.junctionsOfChain (.cons next remaining) tail⟩

/-- The finite spine of exact cap-coordinate joins between consecutive original parent occurrences. -/
@[expose] public def CoordinateLinkData : {parents : List (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent
  curve
  differential)} → Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank cap differential count parents → Type
  | _, .nil => PUnit
  | _, .cons _ .nil => PUnit
  | _, .cons data (.cons next remaining) =>
      RootCoordinates.Overlap.Join data.data.last.coordinates next.data.first.coordinates ×
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.CoordinateLinkData (.cons next remaining)

set_option genInjectivity false in
/-- Cached cap-coordinate joins for every consecutive parent pair. The record lets concrete consumers access the spine
without unfolding preparation. -/
structure CoordinateLinks {parents : List (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve
  differential)} (bank : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank cap differential count parents) where
  /-- The cached finite spine of original adjacent cap-coordinate joins. -/ retained :
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.CoordinateLinkData bank

constructive_injectivity CoordinateLinks

namespace CoordinateLinks

/-- Construct the original adjacent cap-coordinate joins from retained root links and exact coordinate junctions. -/
@[expose] public def buildData : ∀ {parents : List (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve
  differential)} (bank : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank cap differential count parents)
    {first last : PreparedRefinementRootChains.Named},
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.RootLinks bank first last →
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.Junctions bank →
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.CoordinateLinkData bank
  | [], .nil, _, _, _, _ => ⟨⟩
  | [_], .cons _ .nil, _, _, _, _ => ⟨⟩
  | _ :: _ :: _, .cons data (.cons next remaining), _, _, roots, junctions =>
      ⟨Join.build data.data.last.coordinates next.data.first.coordinates junctions.1 (by
        rw [data.data.last.coordinates.reciprocal_eq, next.data.first.coordinates.reciprocal_eq]
        exact roots.adjacent),
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.CoordinateLinks.buildData (.cons next
          remaining) roots.tail junctions.2⟩

/-- Cache the adjacent cap-coordinate join spine from the original retained root and coordinate links. -/
@[expose] def build {parents : List (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve differential)}
  (bank : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank cap differential count parents)
    {first last : PreparedRefinementRootChains.Named} (roots :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.RootLinks bank first last) (junctions :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.Junctions bank) :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.CoordinateLinks bank :=
  ⟨buildData bank roots junctions⟩

/-- Read the retained cap-coordinate join between the first two original parent occurrences. -/
@[expose] def head {parent next : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve differential}
  {parents : List (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve differential)}
    {data : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.ParentData cap differential count parent} {nextData :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.ParentData cap differential count next}
    {remaining : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank cap differential count parents}
    (links : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.CoordinateLinks (.cons data (.cons nextData
      remaining))) :
    RootCoordinates.Overlap.Join data.data.last.coordinates nextData.data.first.coordinates :=
  links.retained.1

/-- Read the retained original tail of the root or coordinate join spine. -/
@[expose] def tail {parent next : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve differential}
  {parents : List (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve differential)}
    {data : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.ParentData cap differential count parent} {nextData :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.ParentData cap differential count next}
    {remaining : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank cap differential count parents}
    (links : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.CoordinateLinks (.cons data (.cons nextData
      remaining))) : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.CoordinateLinks (.cons nextData
      remaining) :=
  ⟨links.retained.2⟩

end CoordinateLinks

end Bank

variable {cap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {first last :
  Purelib.Riemann.Normalization.InverseRootPolynomial.Gaussian}
  {path : Polynomial.Geometry.ClearPath
    (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.polynomial curve) collar.box first last}
  {owner : Purelib.Riemann.Topology.SquareRootContinuationChain.Owner
    ((Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.polynomial curve).eval first)}

set_option genInjectivity false in
/-- The complete retained path may cross any number of segment boundaries. Its single parent bank preserves the actual
root handoff at every corner. -/
structure Data (cap : ReciprocalInnerInverse.Data curve collar)
    (path : Polynomial.Geometry.ClearPath (HyperellipticReciprocal.polynomial curve) collar.box first last)
    (owner : SquareRootContinuationChain.Owner ((HyperellipticReciprocal.polynomial curve).eval first)) (differential :
      Differentials.Basic.Differential genus) where
  /-- The original complete covered path with its retained root continuation. -/ prepared :
    PreparedClearPathModels.CoveredTracedPath path owner
  /-- The retained centered-parent cache of the same original path and reversed differential. -/ cache :
    PreparedClearPathModels.ParentCache (curve := HyperellipticReciprocalCurve.reciprocalCurve curve)
    prepared (HyperellipticReciprocal.reversedDifferential differential) 0
  /-- The cap comparison bank indexed by that exact cached parent list. -/ bank :
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank cap differential genus cache.parents
  /-- The retained root handoffs along the same parent bank, including both original external owners. -/ roots :
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.RootLinks bank (PreparedBankRootChains.ownerName owner)
    (PreparedBankRootChains.ownerName (PreparedPathGluing.finishOwner prepared.traced.prepared))
  /-- The cached cap-coordinate joins at every original neighboring parent junction. -/ coordinates :
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.CoordinateLinks bank
  /-- The cached length of the exact retained parent list. -/ parentCount : Nat
  /-- The cached parent count equals the original retained list length. -/ parents_length : cache.parents.length =
    parentCount

constructive_injectivity Data

namespace Data

/-- Consume an existing full-path cache, including its original root owners and primitive cover. Canonical parent
extraction is never replayed here. -/
@[expose] def ofCache (cap : ReciprocalInnerInverse.Data curve collar)
    (prepared : PreparedClearPathModels.CoveredTracedPath path owner) (differential : Differentials.Basic.Differential
      genus)
    (cache : PreparedClearPathModels.ParentCache (curve := HyperellipticReciprocalCurve.reciprocalCurve curve)
      prepared (HyperellipticReciprocal.reversedDifferential differential) 0) :
        Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Data cap path owner differential :=
  let bank := Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.ofCovered cap genus cache.covered (fun parent
    member => ParentCache.endpoints_within cache parent member)
  let roots := Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.RootLinks.ofParentChain bank
    (ParentCache.rootChain cache)
  have junctions : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.Junctions bank := by
    obtain ⟨chain⟩ := cache.chain
    exact Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.junctionsOfChain bank chain
  ⟨prepared, cache, bank, roots, Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.CoordinateLinks.build bank
    roots junctions, cache.parents.length, rfl⟩

/-- Prepare the supplied original reciprocal path once, cache its parents, and build their linked cap comparisons. -/
@[expose] def build (cap : ReciprocalInnerInverse.Data curve collar)
    (path : Polynomial.Geometry.ClearPath (HyperellipticReciprocal.polynomial curve) collar.box first last)
    (within : path.WithinAmbient) (owner : SquareRootContinuationChain.Owner ((HyperellipticReciprocal.polynomial
      curve).eval first))
    (differential : Differentials.Basic.Differential genus) : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Data
      cap path owner differential :=
  let prepared := CoveredTracedPath.build path within owner
  Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Data.ofCache cap prepared differential (ParentCache.build (curve
    := HyperellipticReciprocalCurve.reciprocalCurve curve) prepared
    (HyperellipticReciprocal.reversedDifferential differential) 0)

end Data
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
