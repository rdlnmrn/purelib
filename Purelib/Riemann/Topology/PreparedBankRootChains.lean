module
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
public import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.RootIsolation.SquareRoot.Owner.Transport
public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionAutomaticModels
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence

import Purelib.Curves.Hyperelliptic.Differentials.PreparedModels
import Purelib.Riemann.RootContinuation.PreparedRootConnectedRefinements
public import Purelib.Riemann.Paths.PreparedPathGluing
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Polynomial.Power.Gaussian
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.RootIsolation.Track.Basic
import Purelib.Riemann.Branches.ClearSheetContinuation

@[expose] public section

/-!
# Operational root chains of retained preparation banks

An accepted subdivision passes its actual advanced owner into the next step.
Its query at one precedes only the occurrence-preserving reserve reset, and
the next query at zero follows only occurrence-preserving preparation.
This identifies the roots of the existing centered edge lists, not a newly
prepared substitute bank.
-/

namespace Purelib.Riemann.Topology.PreparedBankRootChains

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge CenterStates centeredEdges edgeOfStep)
open Purelib.Riemann.Branches.PreparedSheetContinuation (Endpoint Subdivision advance transported transportedRootName
  retainedAtReserveRootEquivalent preparedClearanceLower)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Data.Rat in
/-- The exact rational carrier for retained prepared-bank parameters. -/
private abbrev Coordinate := Fraction.Rational
open Purelib.Riemann.Paths.PreparedClearPathModels (CompleteSegment PreparedPath Owner)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named LiftedPoint)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian in
/-- The canonical Gaussian rational carrier for original prepared-bank points. -/
private abbrev Gaussian := Basic.Canonical

open Purelib.Data.Gaussian in
open Purelib.Riemann.RootContinuation in
/-- The original root name of the retained owner at its exact nonzero parameter. -/
abbrev ownerName {parameter : Basic.Canonical} (owner : Owner parameter) : Named :=
  SquareRootTrackEquivalence.ownerRootName owner.parameterNonzero owner

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

namespace RootChain

open Purelib.Approximation.Gaussian in
/-- Compose the final retained name equivalence through the original ordered root chain. -/
def changeFinish : ∀ {children : List (CenteredEdge curve differential)} {first middle last : Named},
    RootChain children first middle → Equivalence.NamedEquivalent middle last → RootChain children first last
  | [], _, _, _, .nil entry, equivalent => .nil (entry.trans equivalent)
  | _ :: _, _, _, _, .cons child entry tail, equivalent => .cons child entry (changeFinish tail equivalent)

/-- Transport a retained root chain along exact equalities of its original endpoint names. -/
def castNames {children : List (CenteredEdge curve differential)} {first last left right : Named}
    (firstEq : first = left) (lastEq : last = right) (roots : RootChain children first last) :
    RootChain children left right := by
  cases firstEq
  cases lastEq
  exact roots

/-- Transport a retained root chain along an exact equality of its original ordered child list. -/
def castChildren {first second : List (CenteredEdge curve differential)} {left right : Named}
    (equal : first = second) (roots : RootChain first left right) : RootChain second left right :=
  equal ▸ roots

end RootChain

open Purelib.Approximation.Gaussian in
open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Integration in
/-- Compare the original prepared edge's finish query with the exact owner produced by its retained advance.

The cached finish-query equation identifies the original transported name, and the retained reserve comparison relates
it to the advanced owner's name. -/
def queryEquivalentAdvance (edge : PreparedEdge curve differential) :
    Equivalence.NamedEquivalent (edge.rootName 1 (by decide))
      (ownerName (advance edge.segment edge.within edge.left edge.owner edge.request edge.small)) := by
  have queryEq : edge.rootName 1 (by decide) =
      transportedRootName edge.segment edge.within edge.left edge.owner edge.request edge.small := by
    unfold PreparedConstantModels.PreparedEdge.rootName
    exact Differentials.PreparedModels.rootAtCached_one_name_eq_transportedRootName curve edge.segment edge.within
      edge.left edge.owner edge.request edge.cached edge.ordered edge.small (by decide)
  rw [queryEq]
  exact retainedAtReserveRootEquivalent (transported edge.segment edge.within edge.left edge.owner edge.request
    edge.small)
    (preparedClearanceLower edge.segment edge.left edge.request)

open Purelib.Approximation.Gaussian in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
/-- Construct the original root-name chain through a retained prepared subdivision and its supplied center states.

Each exact subdivision step retains its cached edge, incoming owner comparison and advanced terminal owner; recursion
preserves the original centered-edge order. -/
def subdivisionRootChain (curve : Basic.HyperellipticCurve genus) (differential : Differentials.Basic.Differential
  genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (sheet : Fin 2) :
    ∀ {left : Endpoint} {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
      (subdivision : Subdivision segment within left owner)
      (centers : CenterStates curve differential sheet subdivision),
      RootChain (centeredEdges curve differential sheet subdivision centers)
        (ownerName owner) (ownerName subdivision.terminalOwner)
  | _, _, .stop _ owner, _ => .nil (Equivalence.NamedEquivalent.refl (ownerName owner))
  | _, _, .next current owner request cached ordered small remaining, centers =>
      let edge := edgeOfStep curve differential segment within current owner request cached ordered small sheet
      let child : CenteredEdge curve differential := ⟨edge, centers.1⟩
      .cons child edge.ownerRootEquivalent_baseQuery
        ((subdivisionRootChain curve differential segment within sheet remaining centers.2).changeStart
          (queryEquivalentAdvance edge))

open Purelib.Data.Gaussian in
/-- Heterogeneous equality of original owners over equal parameters gives equality of their retained root names. -/
public theorem ownerName_eq_of_heq {firstParameter secondParameter : Basic.Canonical}
    (equal : firstParameter = secondParameter) {first : Owner firstParameter} {second : Owner secondParameter}
    (same : HEq first second) : ownerName first = ownerName second := by
  cases equal
  cases same
  rfl

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Riemann.Paths in
open Purelib.RootIsolation in
/-- Casting the original start owner to the segment's exact zero-parameter point preserves its root name. -/
public theorem ownerAtStart_name {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (owner : Owner (curve.polynomial.eval start)) :
    ownerName (PreparedClearPathModels.ownerAtStart segment owner) = ownerName owner := by
  apply ownerName_eq_of_heq (congrArg curve.polynomial.eval segment.pointAt_zero)
  unfold PreparedClearPathModels.ownerAtStart
  exact SquareRoot.Owner.Transport.castOwnerParameter_heq _ _

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
/-- The retained subdivision terminal owner and the exact prepared segment finish owner have equal root names. -/
public theorem finishOwner_name {ambient : Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient} {owner : Owner (curve.polynomial.eval start)}
    (prepared : CompleteSegment segment within owner) :
    ownerName prepared.subdivision.terminalOwner = ownerName prepared.finishOwner :=
  ownerName_eq_of_heq (congrArg curve.polynomial.eval prepared.finish_eq)
    prepared.finishOwner_heq_terminalOwner.symm

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Riemann.Integration in
/-- Read the original root-name chain through the canonical centered cells of a retained complete prepared segment.

The exact original start and finish owners are preserved using their retained name equalities and subdivision chain. -/
def completeSegmentRootChain (curve : Basic.HyperellipticCurve genus) (differential : Differentials.Basic.Differential
  genus)
    {ambient : Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient} {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) (prepared : CompleteSegment segment within owner) :
    RootChain (prepared.centeredEdges curve differential sheet) (ownerName owner) (ownerName prepared.finishOwner) :=
  RootChain.castNames (ownerAtStart_name segment owner) (finishOwner_name prepared)
    (subdivisionRootChain curve differential segment within sheet prepared.subdivision
      (PreparedSubdivisionAutomaticModels.canonicalCenterStates curve differential sheet prepared.subdivision))

open Purelib.Approximation.Gaussian in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Paths in
/-- Construct the original endpoint root-name chain for the exact centered parents of a retained prepared path.

Each complete segment keeps its original start and finish owners, and ordered concatenation composes the retained chains
through the same shared names. -/
def preparedPathRootChain (curve : Basic.HyperellipticCurve genus) (differential : Differentials.Basic.Differential
  genus)
    (sheet : Fin 2) {ambient : Box} :
    ∀ {start finish : Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
      {owner : Owner (curve.polynomial.eval start)} (prepared : PreparedPath path owner),
      RootChain (PreparedDirectDyadicRefinements.CenteredPathChain.ofPreparedPath curve differential sheet
        prepared).parents
        (ownerName owner) (ownerName (PreparedPathGluing.finishOwner prepared))
  | _, _, _, _, .nil _ owner => .nil (Equivalence.NamedEquivalent.refl (ownerName owner))
  | _, _, _, _, .cons _ _ _ _ head tail =>
      let first := RootChain.castChildren
        (PreparedDirectDyadicRefinements.CenteredPathChain.dataOfCompleteSegment_parents curve differential sheet
          head).symm
        (completeSegmentRootChain curve differential sheet head)
      first.append (preparedPathRootChain curve differential sheet tail)

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Paths in
/-- Read the original root-name chain of a retained dyadic bank across all its existing preparation outcomes.

Safe, executed, certified-execution and certified banks keep their exact prepared path and terminal owner; retained
child-list equalities identify the original centered parent list. -/
def dyadicBankRootChain (curve : Basic.HyperellipticCurve genus) (differential : Differentials.Basic.Differential genus)
    (sheet : Fin 2) {depth : Nat} {diameter : Fraction.Rational} {positive : 0 < diameter}
    {ambient : Box} {start finish : Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (bank : PreparedPath.DyadicBank depth diameter positive path owner) :
    RootChain (PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank curve differential sheet bank).parents
      (ownerName owner) (ownerName (PreparedPathGluing.finishOwner bank.prepared)) := by
  cases bank with
  | safe checked => exact preparedPathRootChain curve differential sheet checked.prepared
  | executed within prepared success => exact preparedPathRootChain curve differential sheet prepared
  | executedCertified checked =>
      exact RootChain.castChildren
        (PreparedDirectDyadicRefinements.CenteredPathChain.ofExecutedCheckedDyadic_parents_eq_ofPreparedPath
          curve differential sheet checked).symm
        (preparedPathRootChain curve differential sheet checked.prepared)
  | certified certificate => exact preparedPathRootChain curve differential sheet certificate.prepared

end Purelib.Riemann.Topology.PreparedBankRootChains
