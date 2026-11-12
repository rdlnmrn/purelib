module

import Purelib.Data.Nat.Order
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Accuracy
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Retained.Transport

/-! # Sufficient source requests retaining actual completed family members

A finite original accuracy selection chooses a stage after the incoming
stage. One actual member of the original Completed.family is retained at
that stage. Its whole canonical factory equality supplies the existing
Requested constructor without executing a second attempt or completion.
-/

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt

open Purelib.Data
open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Rational.Geometric.Search (Selection)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

namespace Requested

/-- A sufficient source Request and its actual completed member at the same selected stage.

The original covered parents, chain, lower stage, numerical floors and
accuracy remain indices. The member keeps the entire original attempt
and its exact equality with the Request's retained attempt. This named
type is the existing dependent pair, without a new owner or computation.
-/
@[expose] public def CompletedSource
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count (parent :: parents))
    (chain : CenteredPathChain (parent :: parents)
      (start := PreparedParent.startPoint parent) (finish := PreparedParent.startPoint parent))
    (current floor rootStage : Nat) (accuracy : AccuracyRequest) : Type _ :=
  (paid : Requested covered chain current floor rootStage accuracy) ×
    { member : Completed covered chain paid.selected.stage floor rootStage // member.1 = paid.attempt }

end Requested

namespace Completed

/-- Select a sufficient source stage and retain its same completed canonical attempt as an original Requested value.

The incoming completion and its whole original factory remain genuine
inputs. The stage is chosen strictly after that incoming stage and not
before current. Exactly one completed-family member is materialized; the
original numerical admissions belong to that member's own Targets and
preparations, while the original transported root acquisitions are retained.
-/
public def requested
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count (parent :: parents))
    (chain : CenteredPathChain (parent :: parents)
      (start := PreparedParent.startPoint parent) (finish := PreparedParent.startPoint parent))
    {index floor rootStage : Nat} (incoming : Completed covered chain index floor rootStage)
    (factory : incoming.1 = fromCovered covered chain index floor rootStage)
    (current : Nat) (accuracy : AccuracyRequest) :
    Requested.CompletedSource covered chain (max current (index + 1)) floor rootStage accuracy :=
  let selected := Selection.build 1 (of_decide_eq_true rfl) (max current (index + 1))
    accuracy.tolerance accuracy.positive
  let members := family covered chain incoming factory
  let retained := members selected.stage
  have different : selected.stage ≠ index := by
    intro equal
    have after : index + 1 ≤ index :=
      (Nat.Order.le_max_right current (index + 1)).trans (selected.lower.trans (Nat.le_of_eq equal))
    exact Nat.not_succ_le_self index after
  have canonical : retained.val.1 = fromCovered covered chain selected.stage floor rootStage :=
    retained.property.trans ((incoming.1.attemptFamily_other selected.stage different).trans
      (fromCovered_eq_ofPrepared covered chain selected.stage floor rootStage).symm)
  let paid := Requested.ofRetained covered chain (max current (index + 1)) floor rootStage accuracy
    ⟨selected, rfl⟩ retained.val.1 canonical
  ⟨paid, ⟨retained.val, rfl⟩⟩

/-- The sufficient retained request keeps exactly the original completed-family member at its actual selected stage. -/
public theorem requested_member
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count (parent :: parents))
    (chain : CenteredPathChain (parent :: parents)
      (start := PreparedParent.startPoint parent) (finish := PreparedParent.startPoint parent))
    {index floor rootStage : Nat} (incoming : Completed covered chain index floor rootStage)
    (factory : incoming.1 = fromCovered covered chain index floor rootStage)
    (current : Nat) (accuracy : AccuracyRequest) :
    (requested covered chain incoming factory current accuracy).2.val =
      (family covered chain incoming factory
        (requested covered chain incoming factory current accuracy).1.selected.stage).val := by
  rfl

/-- The actual retained completed member owns precisely the same whole attempt as the returned sufficient request. -/
public theorem requested_attempt
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count (parent :: parents))
    (chain : CenteredPathChain (parent :: parents)
      (start := PreparedParent.startPoint parent) (finish := PreparedParent.startPoint parent))
    {index floor rootStage : Nat} (incoming : Completed covered chain index floor rootStage)
    (factory : incoming.1 = fromCovered covered chain index floor rootStage)
    (current : Nat) (accuracy : AccuracyRequest) :
    (requested covered chain incoming factory current accuracy).2.val.1 =
      (requested covered chain incoming factory current accuracy).1.attempt :=
  (requested covered chain incoming factory current accuracy).2.property

/-- The genuine numerical source selection is strictly later than the incoming stage, including constant geometries. -/
public theorem requested_stage_lt
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count (parent :: parents))
    (chain : CenteredPathChain (parent :: parents)
      (start := PreparedParent.startPoint parent) (finish := PreparedParent.startPoint parent))
    {index floor rootStage : Nat} (incoming : Completed covered chain index floor rootStage)
    (factory : incoming.1 = fromCovered covered chain index floor rootStage)
    (current : Nat) (accuracy : AccuracyRequest) :
    index < (requested covered chain incoming factory current accuracy).1.selected.stage :=
  (Nat.Order.le_max_right current (index + 1)).trans
    (requested covered chain incoming factory current accuracy).1.selected.lower

end Completed

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt
