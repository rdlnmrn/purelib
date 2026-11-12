module
import Purelib.RootIsolation.Refinement.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.RootIsolation.Exact.Basic
public import Purelib.RootIsolation.Exact.Ownership.Basic
import Purelib.RootIsolation.Exact.Ownership.Radius
public import Purelib.RootIsolation.Exact.Partition.Location
import Purelib.RootIsolation.Exact.Partition.Margin
public import Purelib.RootIsolation.State.WindingOne.Count
public import Purelib.RootIsolation.State.Raw.Interior
public import Purelib.RootIsolation.State.WindingOne.Raw
import Purelib.RootIsolation.Track.Basic

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.RootIsolation.State.WindingOne.Basic

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

/-!
# Selecting the retained isolation-output owner

Refinement at the original ownership radius locates the retained anchor
in the exact partition. A zero-winding remainder cannot contain its state.
-/

namespace Purelib.RootIsolation.Exact.Ownership.Prepare

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic (SquarefreeCertificate)
open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)

/-- Compute the original partition owner of an actual certified ownership-radius refinement.

The original raw region, retained state and its anchor are used directly. The partition
margin supplies strict cell containment, and the squarefree winding count
excludes every zero-winding remainder cell. No desired owner is supplied.
-/
@[expose] public def fromRawRefinement
    {p : CoefficientPolynomial} {ambient : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    {count : Nat} (output : Exact.Basic.Output p ambient count)
    (source : State.Raw.RawWindingState p ambient)
    (supported : source.box.Refines output.support)
    (refinement : Refinement source (Exact.Ownership.Radius.assignmentRadius p ambient output)) :
    Exact.Ownership.Basic.Assignment output source := by
  let radius := Exact.Ownership.Radius.assignmentRadius p ambient output
  let refined := refinement.state
  have refinedSupport : refined.box.Refines output.support :=
    (Box.Refinement.StrictInterior.refines refinement.strict).trans supported
  have anchorSupport : output.support.Contains refined.box.anchor :=
    refinedSupport.contains refined.box.contains_anchor
  let location := Exact.Partition.Location.locatePartition output refined.box.anchor anchorSupport
  have anchorCell : location.box.Contains refined.box.anchor :=
    Exact.Partition.Location.locatePartition_contains output refined.box.anchor anchorSupport
  have diagonal : refined.box.diagonalSq ≤ radius ^ 2 := refinement.accurate
  have degreePositive : 0 < p.natDegree :=
    (show (0 : Nat) < 2 by decide).trans_le degreeAtLeastTwo
  let selected : {owner : Fin output.tracks.length //
      refined.box.StrictInterior (output.tracks.get owner).initial.box} := by
    cases locationEq : location with
    | track index =>
        have anchorTrack : (output.tracks.get index).initial.box.Contains refined.box.anchor := by
          simpa only [locationEq, Exact.Partition.Location.PartitionLocation.box] using anchorCell
        exact ⟨index,
          State.Raw.Interior.strictInterior_of_anchor_mem_of_dominates p refined.raw degreePositive
            (output.tracks.get index).initial.refinesAmbient
            (output.tracks.get index).initial.clearance anchorTrack
            (Exact.Ownership.Radius.assignment_dominates p ambient output refined.box diagonal
              (Exact.Partition.Margin.partitionMargin_le_track output index))⟩
    | remainder index =>
        let region := output.remainder.get index
        have anchorRegion : region.box.Contains refined.box.anchor := by
          simpa only [region, locationEq, Exact.Partition.Location.PartitionLocation.box] using anchorCell
        have strict : refined.box.StrictInterior region.box :=
          State.Raw.Interior.strictInterior_of_anchor_mem_of_dominates p refined.raw degreePositive
            region.refinesAmbient region.clearance anchorRegion
            (Exact.Ownership.Radius.assignment_dominates p ambient output refined.box diagonal
              (Exact.Partition.Margin.partitionMargin_le_remainder output index))
        have atLeastFour := State.WindingOne.Count.region_rawWinding_ge_four_of_strictInterior
          degreeAtLeastTwo squarefree elimination refined region strict
        have zero := output.remainder_rawWinding_zero region (List.get_mem output.remainder index)
        exact (by omega : False).elim
  exact { refinement := refinement, owner := selected.val, strict := selected.property }

/-- Assign an actual refinement of a track's same original initial region.

The track supplies its exact raw source and support witness. The shared finite
locator consumes the supplied refinement without executing the track's own
refinement procedure.
-/
@[expose] public def fromRefinement
    {p : CoefficientPolynomial} {ambient : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    {count : Nat} (output : Exact.Basic.Output p ambient count)
    (track : Track.Basic.WindingOneTrack p ambient)
    (supported : track.initial.box.Refines output.support)
    (refinement : Refinement track.initial.raw (Exact.Ownership.Radius.assignmentRadius p ambient output)) :
    Exact.Ownership.Basic.Assignment output track.initial.raw :=
  fromRawRefinement degreeAtLeastTwo squarefree elimination output track.initial.raw supported refinement

/-- Owner assignment retains the complete supplied refinement certificate. -/
public theorem fromRefinement_refinement
    {p : CoefficientPolynomial} {ambient : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    {count : Nat} (output : Exact.Basic.Output p ambient count)
    (track : Track.Basic.WindingOneTrack p ambient)
    (supported : track.initial.box.Refines output.support)
    (refinement : Refinement track.initial.raw (Exact.Ownership.Radius.assignmentRadius p ambient output)) :
    (fromRefinement degreeAtLeastTwo squarefree elimination output track supported refinement).refinement =
      refinement := rfl

/-- Select the original partition track containing a supplied supported winding track.

The canonical refinement is computed once, then consumed by the same finite
partition assignment as any other certified refinement. The returned record
keeps its original complete canonical-state equality.
-/
@[expose] public def selectOutputOwner
    {p : CoefficientPolynomial} {ambient : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    {count : Nat} (output : Exact.Basic.Output p ambient count)
    (track : Track.Basic.WindingOneTrack p ambient)
    (supported : track.initial.box.Refines output.support) :
    Exact.Ownership.Basic.OwnerSelection output track :=
  let radius := Exact.Ownership.Radius.assignmentRadius p ambient output
  let positive := Exact.Ownership.Radius.assignmentRadius_pos p ambient output
  let refined : Refinement track.initial.raw radius :=
    { state := track.refine track.initial radius positive
      strict := track.strict track.initial radius positive
      accurate := track.accurate track.initial radius positive }
  let assigned := fromRefinement degreeAtLeastTwo squarefree elimination output track supported refined
  { owner := assigned.owner, refined := refined.state, refined_eq := rfl, strict := assigned.strict }

/-- Two certified refinements inside the same winding-four raw region have the same partition owner.

Different selected cells would separate the actual refined winding-one states.
Their strict containment in the same original region contradicts its winding
four through the finite two-state lower bound of eight. No track is executed.
-/
public theorem same_owner
    {p : CoefficientPolynomial} {ambient : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    {count : Nat} {output : Exact.Basic.Output p ambient count}
    {source : State.Raw.RawWindingState p ambient}
    (sourceFour : Winding.Box.Basic.quadrupledBoxWinding p source.box = 4)
    (first second : Exact.Ownership.Basic.Assignment output source) : first.owner = second.owner := by
  by_cases same : first.owner = second.owner
  · exact same
  · have separated := (output.tracks_get_separated first.owner second.owner same).of_refines
      (Box.Refinement.StrictInterior.refines first.strict)
      (Box.Refinement.StrictInterior.refines second.strict)
    let original : Clearance.Box.Region.ClearRegion p ambient :=
      { box := source.box
        refinesAmbient := source.refinesAmbient
        proper := source.proper
        clearance := source.clearance }
    have atLeastEight := State.WindingOne.Count.region_rawWinding_ge_eight_of_separated
      degreeAtLeastTwo squarefree elimination original first.refinement.state second.refinement.state
      first.refinement.strict second.refinement.strict separated
    change 8 ≤ Winding.Box.Basic.quadrupledBoxWinding p source.box at atLeastEight
    rewrite [sourceFour] at atLeastEight
    exact ((by decide : ¬ (8 : Int) ≤ 4) atLeastEight).elim

/-- Actual certified refinement preserves the original deterministic owner index.

This is only index agreement. The actual retained state remains independent
of the canonical refinement state and is not given a false state equality.
-/
public theorem fromRefinement_owner_eq
    {p : CoefficientPolynomial} {ambient : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    {count : Nat} (output : Exact.Basic.Output p ambient count)
    (track : Track.Basic.WindingOneTrack p ambient)
    (supported : track.initial.box.Refines output.support)
    (refinement : Refinement track.initial.raw (Exact.Ownership.Radius.assignmentRadius p ambient output)) :
    (fromRefinement degreeAtLeastTwo squarefree elimination output track supported refinement).owner =
      (selectOutputOwner degreeAtLeastTwo squarefree elimination output track supported).owner := by
  have same := same_owner (output := output) (source := track.initial.raw)
    degreeAtLeastTwo squarefree elimination track.initial.rawWindingFour
    (fromRefinement degreeAtLeastTwo squarefree elimination output track supported refinement)
    (selectOutputOwner degreeAtLeastTwo squarefree elimination output track supported).toAssignment
  exact same.trans (Exact.Ownership.Basic.OwnerSelection.toAssignment_owner _)

/-- Assign an actual refinement using complete retained partition and source-track readbacks.

Only the exact original owners are transported. The supplied successful
refinement remains the numerical input to the finite partition locator.
-/
@[expose] public def fromReadbacks
    {p : CoefficientPolynomial} {ambient : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    {count : Nat} (output : Exact.Basic.Output p ambient count)
    (track : Track.Basic.WindingOneTrack p ambient)
    (supported : track.initial.box.Refines output.support)
    (cachedOutput : Exact.Basic.Output p ambient count) (sameOutput : cachedOutput = output)
    (cachedTrack : Track.Basic.WindingOneTrack p ambient) (sameTrack : cachedTrack = track)
    (refinement : Refinement cachedTrack.initial.raw
      (Exact.Ownership.Radius.assignmentRadius p ambient cachedOutput)) :
    Exact.Ownership.Basic.Assignment output track.initial.raw := by
  subst output
  subst track
  exact fromRefinement degreeAtLeastTwo squarefree elimination cachedOutput cachedTrack supported refinement

/-- Assign a checked raw-source refinement through complete original partition and source readbacks.

The same retained source region and partition are transported along their whole
record equalities. The actual successful refinement supplies the numerical
state; neither a canonical track nor its preliminary extraction is evaluated.
-/
@[expose] public def fromRawReadbacks
    {p : CoefficientPolynomial} {ambient : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    {count : Nat} (output : Exact.Basic.Output p ambient count)
    (source : State.Raw.RawWindingState p ambient)
    (supported : source.box.Refines output.support)
    (cachedOutput : Exact.Basic.Output p ambient count) (sameOutput : cachedOutput = output)
    (cachedSource : State.Raw.RawWindingState p ambient) (sameSource : cachedSource = source)
    (refinement : Refinement cachedSource (Exact.Ownership.Radius.assignmentRadius p ambient cachedOutput)) :
    Exact.Ownership.Basic.Assignment output source := by
  subst output
  subst source
  exact fromRawRefinement degreeAtLeastTwo squarefree elimination cachedOutput cachedSource supported refinement

/-- Exact retained-owner transport preserves the original deterministic selected index. -/
public theorem fromReadbacks_owner_eq
    {p : CoefficientPolynomial} {ambient : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    {count : Nat} (output : Exact.Basic.Output p ambient count)
    (track : Track.Basic.WindingOneTrack p ambient)
    (supported : track.initial.box.Refines output.support)
    (cachedOutput : Exact.Basic.Output p ambient count) (sameOutput : cachedOutput = output)
    (cachedTrack : Track.Basic.WindingOneTrack p ambient) (sameTrack : cachedTrack = track)
    (refinement : Refinement cachedTrack.initial.raw
      (Exact.Ownership.Radius.assignmentRadius p ambient cachedOutput)) :
    (fromReadbacks degreeAtLeastTwo squarefree elimination output track supported
      cachedOutput sameOutput cachedTrack sameTrack refinement).owner =
      (selectOutputOwner degreeAtLeastTwo squarefree elimination output track supported).owner := by
  cases sameOutput
  cases sameTrack
  exact fromRefinement_owner_eq degreeAtLeastTwo squarefree elimination output track supported refinement

end Purelib.RootIsolation.Exact.Ownership.Prepare
