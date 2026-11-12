module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RootIsolation.Exact.Basic
public import Purelib.RootIsolation.Exact.Ownership.Radius
public import Purelib.RootIsolation.Refinement.Basic
public import Purelib.RootIsolation.State.WindingOne.Raw
import Purelib.RootIsolation.Track.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.RootIsolation.State.WindingOne.Basic

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

/-!
# Retained owner selection for an exact root partition

An owner selection keeps the actual finite index in the original partition
and a strict-interior certificate for the supplied track's assignment-radius
refinement. Both the partition output and that exact refinement remain the
indices of the certificate.
-/

namespace Purelib.RootIsolation.Exact.Ownership.Basic

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

set_option genInjectivity false in
/-- An original partition-track index containing the supplied track's ownership-radius refinement.

The retained strict-interior certificate uses the partition's computed positive assignment radius and that exact track
refinement. -/
public structure OwnerSelection
    {p : CoefficientPolynomial} {ambient : Box} {count : Nat}
    (output : Exact.Basic.Output p ambient count) (track : Track.Basic.WindingOneTrack p ambient)
      where
  /-- The actual index of the selected original partition track. -/ owner : Fin output.tracks.length
  /-- The actual computed assignment-radius state retained by owner selection. -/
  refined : State.WindingOne.Basic.WindingOneState p ambient
  /-- The retained state is the original track's exact assignment-radius refinement. -/
  refined_eq : refined = track.refine track.initial
    (Exact.Ownership.Radius.assignmentRadius p ambient output)
    (Exact.Ownership.Radius.assignmentRadius_pos p ambient output)
  /-- The supplied track's assignment-radius refinement lies strictly inside the selected original owner box. -/ strict
    :
    let radius := Exact.Ownership.Radius.assignmentRadius p ambient output
    let refined := track.refine track.initial radius
      (Exact.Ownership.Radius.assignmentRadius_pos p ambient output)
    refined.box.StrictInterior (output.tracks.get owner).initial.box

set_option cleanup.letToHave false in
constructive_injectivity OwnerSelection

namespace OwnerSelection

variable {p : CoefficientPolynomial}
    {ambient : Box} {count : Nat} {output otherOutput : Exact.Basic.Output p ambient count}
    {track otherTrack : Track.Basic.WindingOneTrack p ambient}

/-- Transport a complete original owner selection along exact partition and track equalities.

The same selected occurrence and whole refined state are retained. Only their
original parent indices change; no partition location or numerical refinement
is performed by the transport.
-/
public def cast (selection : OwnerSelection output track) (sameOutput : output = otherOutput)
    (sameTrack : track = otherTrack) : OwnerSelection otherOutput otherTrack := by
  cases sameOutput
  cases sameTrack
  exact selection

/-- Transport preserves the whole selected bounded occurrence at its original list-length equality. -/
public theorem cast_owner (selection : OwnerSelection output track) (sameOutput : output = otherOutput)
    (sameTrack : track = otherTrack) :
    (selection.cast sameOutput sameTrack).owner =
      Fin.cast (congrArg (fun actual : Exact.Basic.Output p ambient count => actual.tracks.length) sameOutput)
        selection.owner := by
  cases sameOutput
  cases sameTrack
  rfl

/-- Transport preserves the actual original refined state with all its certificates. -/
public theorem cast_refined (selection : OwnerSelection output track) (sameOutput : output = otherOutput)
    (sameTrack : track = otherTrack) : (selection.cast sameOutput sameTrack).refined = selection.refined := by
  cases sameOutput
  cases sameTrack
  rfl

/-- Reflexive parent transports retain the complete supplied selection literally. -/
public theorem cast_self (selection : OwnerSelection output track) : selection.cast rfl rfl = selection := (rfl)

end OwnerSelection

/-- The actual retained refinement lies strictly inside the selected original owner box. -/
public theorem OwnerSelection.refined_strict
    {p : CoefficientPolynomial}
    {ambient : Box} {count : Nat} {output : Exact.Basic.Output p ambient count}
    {track : Track.Basic.WindingOneTrack p ambient} (selection : OwnerSelection output track) :
    selection.refined.box.StrictInterior (output.tracks.get selection.owner).initial.box := by
  rewrite [selection.refined_eq]
  exact selection.strict

/-- The actual retained refinement lies strictly inside the original input track's initial box. -/
public theorem OwnerSelection.refined_strict_source
    {p : CoefficientPolynomial}
    {ambient : Box} {count : Nat} {output : Exact.Basic.Output p ambient count}
    {track : Track.Basic.WindingOneTrack p ambient} (selection : OwnerSelection output track) :
    selection.refined.box.StrictInterior track.initial.box := by
  rewrite [selection.refined_eq]
  exact track.strict _ _ _

set_option genInjectivity false in
/-- An original partition assignment retaining an actual certified refinement.

The retained winding-one state is strictly inside the supplied original raw
region and meets this partition's exact assignment-radius request. Its selected
original cell is independent of any canonical refinement program.
-/
public structure Assignment
    {p : CoefficientPolynomial} {ambient : Box} {count : Nat}
    (output : Exact.Basic.Output p ambient count) (source : State.Raw.RawWindingState p ambient) where
  /-- The actual successful refinement of the original raw region at the original ownership radius. -/
  refinement : Refinement source (Exact.Ownership.Radius.assignmentRadius p ambient output)
  /-- The actual selected index in the original retained partition. -/
  owner : Fin output.tracks.length
  /-- The actual refined box lies strictly inside the selected original cell. -/
  strict : refinement.state.box.StrictInterior (output.tracks.get owner).initial.box

constructive_injectivity Assignment

/-- View a canonical owner selection as an assignment of its same retained state.

The original exact-refinement equality supplies the strict source containment
and requested accuracy; no refinement or owner search is executed again.
-/
@[expose] public def OwnerSelection.toAssignment
    {p : CoefficientPolynomial}
    {ambient : Box} {count : Nat} {output : Exact.Basic.Output p ambient count}
    {track : Track.Basic.WindingOneTrack p ambient} (selection : OwnerSelection output track) :
    Assignment output track.initial.raw where
  refinement :=
    { state := selection.refined
      strict := selection.refined_strict_source
      accurate := by
        rewrite [selection.refined_eq]
        exact track.accurate _ _ _ }
  owner := selection.owner
  strict := selection.refined_strict

/-- A canonical assignment view retains the exact supplied partition index. -/
public theorem OwnerSelection.toAssignment_owner
    {p : CoefficientPolynomial}
    {ambient : Box} {count : Nat} {output : Exact.Basic.Output p ambient count}
    {track : Track.Basic.WindingOneTrack p ambient} (selection : OwnerSelection output track) :
    selection.toAssignment.owner = selection.owner := rfl

/-- A canonical assignment view retains the exact supplied numerical state. -/
public theorem OwnerSelection.toAssignment_state
    {p : CoefficientPolynomial}
    {ambient : Box} {count : Nat} {output : Exact.Basic.Output p ambient count}
    {track : Track.Basic.WindingOneTrack p ambient} (selection : OwnerSelection output track) :
    selection.toAssignment.refinement.state = selection.refined := rfl

end Purelib.RootIsolation.Exact.Ownership.Basic
