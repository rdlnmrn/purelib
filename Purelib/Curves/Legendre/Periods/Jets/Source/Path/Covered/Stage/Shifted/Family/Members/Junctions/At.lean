module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Family.Members.Junctions
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Family.Members.Endpoints.Chain
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Strip.Sections
import Purelib.Riemann.RootContinuation.FixedRootBoxPath.At
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Chain
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Occurrences
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Data.List.DependentProduct
import Purelib.Approximation.AccuracyRequest
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Parameter
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Parameter.Strip
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Family.Members
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence

/-! # Actual signed strip overlaps from retained uniform junction continuations

The original zero-member continuation retains the starting sign. GIVEN
per-time endpoint sections supply both actual query references and Steps.
Exact scalar transports place their SAME Owners on the actual junction
path, and the existing finite all-time comparison derives every handoff.
No endpoint section, observation, member or budget acquisition is replayed.
The original comparison root queries remain genuine new work.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.LocalMember

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List (DependentProduct)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Data.Rat.Fraction.Order.Arithmetic (instZeroLEOneClass)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named RootChain)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
  (ownerRootName ownerRootName_castOwnerParameter)
open Purelib.RootIsolation.SquareRoot.Owner.Transport
  (castOwnerParameter castOwnerParameter_heq castOwnerParameter_initial_box)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint finishPoint)

attribute [local irreducible] CertifiedSquareRoot.rawRoot

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {reference : AccuracyRequest}
    {source : Requested covered chain current floor rootStage reference}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {targetCurrent targetFloor targetRootStage : Nat}
    {zeroPaid : Norm.Basic.normSq (0 : Canonical) ≤ allocation.bound}
    {zero : LocalMember source ranges allocation roots widths targetCurrent targetFloor targetRootStage 0 zeroPaid}
    {increment : Canonical} {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    (cached : LocalMember source ranges allocation roots widths
      targetCurrent targetFloor targetRootStage increment admitted)
    {zeroInside : (0 : Rational) ≤ 0 ∧ (0 : Rational) ≤ 1}
    {oneInside : (0 : Rational) ≤ 1 ∧ (1 : Rational) ≤ 1}
    (observed : EndpointObservations source.prepared zeroInside oneInside)
    (time : Rational) (timeInside : 0 ≤ time ∧ time ≤ 1)
    (sections : StripSections cached observed time timeInside)
    {index : Fin (parent :: parents).length}
    (continued : JunctionContinuation roots widths targetCurrent targetFloor targetRootStage
      zero increment admitted index)

namespace JunctionContinuation

/-- The actual last raw query coordinate has the SAME exact radicand as the retained uniform junction path. -/
theorem firstParameter :
    (Paths.polynomial (parameter + (⟨time, 0⟩ : Canonical) * increment)).eval
      ((source.prepared.entry index).preparation.cell.models.coordinate.point 1) = continued.path.point time :=
  (congrArg (Paths.polynomial (parameter + (⟨time, 0⟩ : Canonical) * increment)).eval
    (((source.prepared.entry index).queryPoint_eq 1).trans
      ((parent :: parents)[index.val]'index.isLt).edge.point_one)).trans (continued.point_eq time).symm

/-- The following first query reaches the SAME junction through the original closed-chain incidence. -/
theorem lastParameter :
    (Paths.polynomial (parameter + (⟨time, 0⟩ : Canonical) * increment)).eval
      ((source.prepared.entry (followingIndex parent parents index)).preparation.cell.models.coordinate.point 0) =
        continued.path.point time := by
  have following := congrArg (fun point : LiftedPoint 2 => point.coordinate) (following_point chain index)
  have physical := ((source.prepared.entry (followingIndex parent parents index)).queryPoint_eq 0).trans
    (((parent :: parents)[(followingIndex parent parents index).val]'
      (followingIndex parent parents index).isLt).edge.point_zero.trans
      following)
  exact (congrArg (Paths.polynomial (parameter + (⟨time, 0⟩ : Canonical) * increment)).eval physical).trans
    (continued.point_eq time).symm

/-- Reindex the SAME left actual section reference onto the retained junction path without a new root selection. -/
def firstReferenceAt : Owner (continued.path.point time) :=
  castOwnerParameter (firstParameter (continued := continued) (time := time))
    (DependentProduct.get (parent :: parents) sections index).2.1.reference.val

/-- The left junction view retains its whole original section reference Owner heterogeneously. -/
theorem firstReferenceAt_heq :
    HEq (firstReferenceAt (cached := cached) (observed := observed) (sections := sections)
      (continued := continued) (time := time) (timeInside := timeInside))
      (DependentProduct.get (parent :: parents) sections index).2.1.reference.val := by
  unfold firstReferenceAt
  exact castOwnerParameter_heq _ _

/-- Reindex the SAME independent following section reference at this actual junction. -/
def lastReferenceAt : Owner (continued.path.point time) :=
  castOwnerParameter (lastParameter (continued := continued) (time := time))
    (DependentProduct.get (parent :: parents) sections (followingIndex parent parents index)).1.1.reference.val

/-- The following view retains its whole original section reference Owner heterogeneously. -/
theorem lastReferenceAt_heq :
    HEq (lastReferenceAt (cached := cached) (observed := observed) (sections := sections)
      (continued := continued) (time := time) (timeInside := timeInside))
      (DependentProduct.get (parent :: parents) sections (followingIndex parent parents index)).1.1.reference.val := by
  unfold lastReferenceAt
  exact castOwnerParameter_heq _ _

/-- The left actual reference refines precisely the original first seed box used by the uniform path. -/
theorem firstReferenceAt_box :
    (firstReferenceAt (cached := cached) (observed := observed) (sections := sections)
      (continued := continued) (time := time) (timeInside := timeInside)).track.initial.box =
        ((covered.entry index).val.neighborhood count).base.seed.owner.track.initial.box := by
  unfold firstReferenceAt
  exact (castOwnerParameter_initial_box _ _).trans
    (DependentProduct.get (parent :: parents) sections index).2.1.reference_box

/-- The following actual reference retains the separate original second seed box. -/
theorem lastReferenceAt_box :
    (lastReferenceAt (cached := cached) (observed := observed) (sections := sections)
      (continued := continued) (time := time) (timeInside := timeInside)).track.initial.box =
        ((covered.entry (followingIndex parent parents index)).val.neighborhood
          count).base.seed.owner.track.initial.box := by
  unfold lastReferenceAt
  exact (castOwnerParameter_initial_box _ _).trans
    (DependentProduct.get (parent :: parents) sections (followingIndex parent parents index)).1.1.reference_box

/-- The first exact radicand transport keeps the actual old raw-reference root name. -/
theorem firstReferenceAt_name :
    ownerRootName
      (firstReferenceAt (cached := cached) (observed := observed) (sections := sections)
        (continued := continued) (time := time) (timeInside := timeInside)).parameterNonzero
      (firstReferenceAt (cached := cached) (observed := observed) (sections := sections)
        (continued := continued) (time := time) (timeInside := timeInside)) =
    ownerRootName (DependentProduct.get (parent :: parents) sections index).2.1.reference.val.parameterNonzero
      (DependentProduct.get (parent :: parents) sections index).2.1.reference.val := by
  unfold firstReferenceAt
  exact ownerRootName_castOwnerParameter _ _

/-- The second exact radicand transport keeps the independent following raw-reference root name. -/
theorem lastReferenceAt_name :
    ownerRootName
      (lastReferenceAt (cached := cached) (observed := observed) (sections := sections)
        (continued := continued) (time := time) (timeInside := timeInside)).parameterNonzero
      (lastReferenceAt (cached := cached) (observed := observed) (sections := sections)
        (continued := continued) (time := time) (timeInside := timeInside)) =
    ownerRootName
      (DependentProduct.get (parent :: parents) sections
        (followingIndex parent parents index)).1.1.reference.val.parameterNonzero
      (DependentProduct.get (parent :: parents) sections (followingIndex parent parents index)).1.1.reference.val := by
  unfold lastReferenceAt
  exact ownerRootName_castOwnerParameter _ _

/-- Derive the actual two-reference agreement at every admitted interpolation time from the retained zero-time sign.

The original retainedEquivalentAt selects its real finite comparison depth
from the path scale and two positive clearances. All four actual Owners
are supplied from the retained caches; their separate box refinements are
derived internally. Its original internal root-query work is unchanged.
-/
def referencesAt :
    NamedEquivalent
      (ownerRootName
        (firstReferenceAt (cached := cached) (observed := observed) (sections := sections)
          (continued := continued) (time := time) (timeInside := timeInside)).parameterNonzero
        (firstReferenceAt (cached := cached) (observed := observed) (sections := sections)
          (continued := continued) (time := time) (timeInside := timeInside)))
      (ownerRootName
        (lastReferenceAt (cached := cached) (observed := observed) (sections := sections)
          (continued := continued) (time := time) (timeInside := timeInside)).parameterNonzero
        (lastReferenceAt (cached := cached) (observed := observed) (sections := sections)
          (continued := continued) (time := time) (timeInside := timeInside))) := by
  let first := firstReferenceAt (cached := cached) (observed := observed) (sections := sections)
    (continued := continued) (time := time) (timeInside := timeInside)
  let last := lastReferenceAt (cached := cached) (observed := observed) (sections := sections)
    (continued := continued) (time := time) (timeInside := timeInside)
  have firstName := congrArg (fun owner : Owner (continued.path.point 0) =>
    ownerRootName owner.parameterNonzero owner) continued.first_eq
  have lastName := congrArg (fun owner : Owner (continued.path.point 0) =>
    ownerRootName owner.parameterNonzero owner) continued.last_eq
  let initial := NamedEquivalent.transport firstName.symm lastName.symm (continued.path.expose continued.initial)
  have firstStart := continued.first_box
  have lastStart := continued.last_box
  have firstAt := firstReferenceAt_box (cached := cached) (observed := observed) (sections := sections)
    (continued := continued) (time := time) (timeInside := timeInside)
  have lastAt := lastReferenceAt_box (cached := cached) (observed := observed) (sections := sections)
    (continued := continued) (time := time) (timeInside := timeInside)
  exact continued.path.retainedEquivalentAt time timeInside continued.first continued.last
    (by rewrite [firstStart]; exact Geometry.Rational.Box.refines_refl _)
    (by rewrite [lastStart]; exact Geometry.Rational.Box.refines_refl _)
    initial first last
    (by rewrite [firstAt]; exact Geometry.Rational.Box.refines_refl _)
    (by rewrite [lastAt]; exact Geometry.Rational.Box.refines_refl _)

include continued in
/-- Derive the original StripLink on the SAME actual endpoint Steps through the full uniform parameter continuation.

The given raw-reference comparisons and original endpoint-view name laws
compose with referencesAt. No endpoint Step, observation or member
constructor runs; stationary/repeated source slots retain both sides.
-/
def linkAt : StripLink cached observed time timeInside sections index := by
  let left := (DependentProduct.get (parent :: parents) sections index).2
  let right := (DependentProduct.get (parent :: parents) sections (followingIndex parent parents index)).1
  let middle := referencesAt (cached := cached) (observed := observed) (sections := sections)
    (continued := continued) (time := time) (timeInside := timeInside)
  let before := NamedEquivalent.transport left.2.property.2.symm
    (firstReferenceAt_name (cached := cached) (observed := observed) (sections := sections)
      (continued := continued) (time := time) (timeInside := timeInside)).symm left.1.compared.symm
  let after := NamedEquivalent.transport
    (lastReferenceAt_name (cached := cached) (observed := observed) (sections := sections)
      (continued := continued) (time := time) (timeInside := timeInside)).symm
    right.2.property.2.symm right.1.compared
  exact before.trans (middle.trans after)

end JunctionContinuation

/-- Consume GIVEN section and junction products to derive every actual original StripLink in literal occurrence order.

Only the original all-time operational comparisons are new. The original
source, zero/member caches, endpoint observations, per-time sections and
uniform junction paths are retained inputs, with no second endpoint or
member producer and no assumed strip flatness or closing sign.
-/
def junctionLinksAt
    (continued : JunctionContinuations roots widths targetCurrent targetFloor targetRootStage zero increment admitted) :
    StripLinks cached observed time timeInside sections :=
  DependentProduct.ofFn (parent :: parents) (fun index =>
    JunctionContinuation.linkAt (cached := cached) (observed := observed) (sections := sections)
      (continued := continued.entry index) (time := time) (timeInside := timeInside))

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.LocalMember

end
