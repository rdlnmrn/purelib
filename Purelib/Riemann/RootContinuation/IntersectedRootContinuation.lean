module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.RootContinuation.SquareRootReconditioning
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Polynomial.Power.Gaussian.Perturbation
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
public import Purelib.Polynomial.Clearance.Box.Boundary.Intersection
import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Dominance.Sum
import Purelib.Polynomial.Winding.Box.Basic
public import Purelib.Polynomial.Winding.Box.Rouche
import Purelib.Polynomial.Winding.Box.Rouche.Connection
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.Newton.Band.Build
import Purelib.RootIsolation.State.Raw
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.State.WindingOne.Count
import Purelib.RootIsolation.Track.Newton.Build
import Purelib.Geometry.Rational.Box.Intersection

public import Purelib.Riemann.Branches.PreparedPrimitiveSheets
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Band.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.RootIsolation.Track.Basic
import Purelib.RootIsolation.FTA.Squarefree.Input
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Clearance.Box.Dominance.Basic
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.RootIsolation.FTA.Squarefree.Prepare
import Purelib.Data.Rat.Fraction
import Purelib.RootIsolation.Newton.Band.Basic
import Mathlib.Order.MinMax
import Purelib.Tactic.QuotientFreeOmega

/-!
# Continuation congruence using intersected source boxes

The source owners share a displayed strict descendant.  Their intersection
therefore has nonzero winding, and its boundary inherits the minimum of the
two original clearances.  Transporting this region and extracting one target
owner identifies the two target occurrences without paying the clearance of
the potentially much smaller common source descendant.
-/

public section

namespace Purelib.Riemann.RootContinuation.IntersectedRootContinuation

open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Polynomial.Clearance.Box
open Purelib.Polynomial.Power
open Purelib.Riemann.RootContinuation
open Purelib.RootIsolation
open Purelib.Riemann.Branches

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence

/-- The canonical Gaussian rational carrier for original root parameters. -/
abbrev Gaussian := Basic.Canonical
/-- The original rational Gaussian box carrier with retained coordinate bounds. -/
abbrev Box := Purelib.Geometry.Rational.Box
/-- The original winding-one quadratic root owner indexed by its exact parameter. -/
abbrev Owner := Purelib.Riemann.Topology.SquareRootContinuationChain.Owner
/-- The original operational equivalence certificate between retained Gaussian names. -/
abbrev NamedEquivalent := Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent

set_option genInjectivity false in
/-- A target-parameter root owner whose initial box lies strictly inside both original source-owner boxes.

The record keeps the two original source owners as indices and retains separate strict interior witnesses for the single
constructed target owner. -/
structure SharedTarget {source : Gaussian} (first second : Owner source) (target : Gaussian) where
  /-- The retained winding-one root owner at the exact target parameter. -/ owner : Owner target
  /-- Its original initial box lies strictly inside the first source owner's initial box. -/ strictFirst :
    owner.track.initial.box.StrictInterior first.track.initial.box
  /-- Its original initial box lies strictly inside the second source owner's initial box. -/ strictSecond :
    owner.track.initial.box.StrictInterior second.track.initial.box

constructive_injectivity SharedTarget

/-- Construct a common target root owner inside the intersection of two original source boxes.

A retained common source owner lies strictly inside both boxes, and parameter movement is below both contour clearances.
The exact intersection clearance and winding comparison certify extraction of a target owner with both original interior
relations. -/
@[expose] def sharedTarget {source target : Gaussian} (targetNonzero : target ≠ 0)
    (first second common : Owner source)
    (strictFirst : common.track.initial.box.StrictInterior first.track.initial.box)
    (strictSecond : common.track.initial.box.StrictInterior second.track.initial.box)
    (firstSmall : normSq (source - target) < first.track.initial.clearance.bound)
    (secondSmall : normSq (source - target) < second.track.initial.clearance.bound) :
    SharedTarget first second target := by
  let overlap := Geometry.Rational.Box.Intersection.intersection first.track.initial.box second.track.initial.box
    common.track.initial.box (Geometry.Rational.Box.Refinement.StrictInterior.refines strictFirst)
      (Geometry.Rational.Box.Refinement.StrictInterior.refines strictSecond)
  have overlapFirst : overlap.Refines first.track.initial.box :=
      Geometry.Rational.Box.Intersection.intersection_refines_first
  have overlapSecond : overlap.Refines second.track.initial.box :=
    Geometry.Rational.Box.Intersection.intersection_refines_second
  have proper : overlap.Proper := Geometry.Rational.Box.Intersection.intersection_proper strictFirst strictSecond
  let clearance := Boundary.Intersection.BoxClearance.BoundaryClearance.intersection first.track.initial.clearance
    second.track.initial.clearance
    (Geometry.Rational.Box.Refinement.StrictInterior.refines strictFirst)
        (Geometry.Rational.Box.Refinement.StrictInterior.refines strictSecond)
  let sourceInput := SquareRootReconditioning.isolationInput first.parameterNonzero
  let supported := supportedInside first.parameterNonzero first.track.initial common.track.initial
    (Geometry.Rational.Box.Refinement.StrictInterior.refines strictFirst)
  have supportedStrict : supported.box.StrictInterior overlap :=
    Geometry.Rational.Box.Refinement.StrictInterior.of_refines
      (Geometry.Rational.Box.Intersection.strictInterior_intersection strictFirst strictSecond)
      (supportedInside_refines_inner first.parameterNonzero first.track.initial common.track.initial
        (Geometry.Rational.Box.Refinement.StrictInterior.refines strictFirst))
  let region : Region.ClearRegion (SquareRootReconditioning.rootPolynomial source) first.track.initial.box :=
    ⟨overlap, overlapFirst, proper, clearance⟩
  have sourcePositive : 4 ≤ Winding.Box.Basic.quadrupledBoxWinding
      (SquareRootReconditioning.rootPolynomial source) overlap :=
    State.WindingOne.Count.region_rawWinding_ge_four_of_strictInterior sourceInput.degreeAtLeastTwo
      sourceInput.squarefree sourceInput.elimination supported region supportedStrict
  let comparison : Winding.Box.Rouche.Connection.OrientedRouche (SquareRootReconditioning.rootPolynomial source)
      (SquareRootReconditioning.rootPolynomial target) overlap :=
    { perturbation := Gaussian.Perturbation.parameterPerturbation source target
      target_eq_add := Gaussian.Perturbation.polynomial_target_eq_add_perturbation source target
        SquareRootDegree.degreeTwo
      dominance :=
        { margin := clearance.bound - normSq (source - target)
          positive := Fraction.Order.Arithmetic.sub_pos_direct (Fraction.Order.Basic.lt_min firstSmall secondSmall)
          lower := by
            intro point boundary
            rw [Gaussian.Perturbation.parameterPerturbation_eval]
            simpa only [SquareRootReconditioning.rootPolynomial, Norm.Basic.normSq_eq_canonical] using
              Fraction.Order.Arithmetic.sub_le_sub_right_direct
              (clearance.lower point boundary) (normSq (source - target)) } }
  have windingSame : Winding.Box.Basic.quadrupledBoxWinding (SquareRootReconditioning.rootPolynomial target) overlap =
      Winding.Box.Basic.quadrupledBoxWinding (SquareRootReconditioning.rootPolynomial source) overlap := by
    rw [comparison.target_eq_add]
    exact Winding.Box.Rouche.quadrupledBoxWinding_add_of_boundaryNormDominance
      _ _ overlap proper clearance comparison.dominance
  let targetClearance : Boundary.Basic.BoundaryClearance (SquareRootReconditioning.rootPolynomial target) overlap := by
    rw [comparison.target_eq_add]
    exact Dominance.Sum.boundaryClearance_add_of_boundaryNormDominance
      _ _ overlap proper comparison.dominance
  let raw : State.Raw.RawWindingState (SquareRootReconditioning.rootPolynomial target) overlap :=
    { box := overlap
      refinesAmbient := overlap.refines_refl
      proper := proper
      clearance := targetClearance
      rawWinding_ne := by rw [windingSame]; omega }
  let targetInput := SquareRootReconditioning.isolationInput targetNonzero
  let output := Newton.Band.Build.extract targetInput.degreeAtLeastTwo targetInput.squarefree
    targetInput.elimination raw (epsilon := 1) (by decide)
  let state : State.WindingOne.Basic.WindingOneState (SquareRootReconditioning.rootPolynomial target) overlap :=
    { box := output.box
      refinesAmbient := output.refinesAmbient
      proper := output.proper
      clearance := output.clearance
      rawWindingFour := output.rawWindingFour
      ambientLeftClearance := output.ambientLeftClearance
      ambientRightClearance := output.ambientRightClearance
      ambientBottomClearance := output.ambientBottomClearance
      ambientTopClearance := output.ambientTopClearance }
  let track := Track.Newton.Build.ofInitial targetInput.degreeAtLeastTwo targetInput.squarefree targetInput.elimination
    state
  exact ⟨⟨targetNonzero, overlap, track⟩, Geometry.Rational.Box.Refinement.StrictInterior.Boxes.trans_refines
      output.strictCurrent
    overlapFirst,
    Geometry.Rational.Box.Refinement.StrictInterior.Boxes.trans_refines output.strictCurrent overlapSecond⟩

/-- Compare two retained target root owners refining two source boxes with a common strict source refinement.

Both original source-to-target movements satisfy their separate contour allowances. The constructed shared target owner
compares the two original target names without replacing either input owner. -/
@[expose] def ownersEquivalent {source target : Gaussian} (targetNonzero : target ≠ 0)
    (first second common : Owner source)
    (strictFirst : common.track.initial.box.StrictInterior first.track.initial.box)
    (strictSecond : common.track.initial.box.StrictInterior second.track.initial.box)
    (firstSmall : normSq (source - target) < first.track.initial.clearance.bound)
    (secondSmall : normSq (source - target) < second.track.initial.clearance.bound)
    (firstTarget secondTarget : Owner target)
    (firstRefines : firstTarget.track.initial.box.Refines first.track.initial.box)
    (secondRefines : secondTarget.track.initial.box.Refines second.track.initial.box) :
    NamedEquivalent (ownerRootName targetNonzero firstTarget) (ownerRootName targetNonzero secondTarget) := by
  let shared := sharedTarget targetNonzero first second common strictFirst strictSecond firstSmall secondSmall
  let firstOuter := transportedTrack targetNonzero first.track (by
      simpa only [Norm.Basic.normSq_eq_canonical]
        using firstSmall)
  let secondOuter := transportedTrack targetNonzero second.track (by
      simpa only [Norm.Basic.normSq_eq_canonical]
        using secondSmall)
  have firstReading := PreparedPrimitiveSheets.rootEquivalent_of_initial_refines targetNonzero firstOuter
    firstTarget.track firstRefines
  have secondReading := PreparedPrimitiveSheets.rootEquivalent_of_initial_refines targetNonzero secondOuter
    secondTarget.track secondRefines
  have firstShared := rootEquivalent_of_initial_strict targetNonzero firstOuter shared.owner.track shared.strictFirst
  have secondShared := rootEquivalent_of_initial_strict targetNonzero secondOuter shared.owner.track shared.strictSecond
  exact firstReading.symm.trans (firstShared.trans (secondShared.symm.trans secondReading))

end Purelib.Riemann.RootContinuation.IntersectedRootContinuation

end
