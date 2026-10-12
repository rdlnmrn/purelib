module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.RootIsolation.Exact.Basic
import Purelib.RootIsolation.Exact.Ownership.Radius

import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.RootContinuation.SquareRootReconditioning

public section

/-!
# Cached complete two-owner frames at regular base points

A frame retains two distinct actual root occurrences and a total finite
classification procedure.  Its semantic interface does not require its
owners to equal one canonical isolation result.  The canonical constructor
shares the isolated endpoint owners and assignment radius, and each new
classification retains one assigned common track and one refinement.
-/

namespace Purelib.Riemann.RootContinuation.RootOwnerFrames

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients renaming CoefficientPolynomial -> Dense

open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)

open Purelib.Approximation in
set_option genInjectivity false in
/-- A checked index and name equivalence to a retained two-entry name bank.

The original queried name is equivalent to the name at the retained bounded index. -/
structure NameSelection (names : Fin 2 → Gaussian.Name.Basic.Named)
    (name : Gaussian.Name.Basic.Named) where
  /-- The selected original name-bank index. -/ index : Fin 2
  /-- The queried name is equivalent to the retained name at that index. -/ equivalent :
    Gaussian.Equivalence.NamedEquivalent name (names index)

constructive_injectivity NameSelection

open Purelib.Data in
/-- A checked owner index with operational equivalence to that actual retained occurrence. -/
abbrev OwnerSelection {parameter : Gaussian.Basic.Canonical}
    (owners : Data.Vector (Owner parameter) 2) (owner : Owner parameter) :=
  NameSelection (fun index => ownerName (owners index)) (ownerName owner)

open Purelib.Approximation in
open Purelib.Data in
set_option genInjectivity false in
/-- Two distinguishable retained occurrences with a total certified classification.

The name map relates each query to a retained occurrence, and equivalence between retained names forces equal indices.
-/
structure OccurrenceFrame (Occurrence : Type) (name : Occurrence → Gaussian.Name.Basic.Named) where
  /-- The two actual retained occurrences. -/ owners : Data.Vector Occurrence 2
  /-- Equivalent retained occurrence names have the same original index. -/ distinguish : ∀ first second,
    Gaussian.Equivalence.NamedEquivalent (name (owners first)) (name (owners second)) → first = second
  /-- Classify each occurrence by a retained index and name-equivalence certificate. -/ select : ∀ owner : Occurrence,
    NameSelection (fun index => name (owners index)) (name owner)

constructive_injectivity OccurrenceFrame

open Purelib.Data in
/-- A complete distinguishable frame of two actual square-root owners at one parameter. -/
abbrev OwnerFrame (parameter : Gaussian.Basic.Canonical) := OccurrenceFrame (Owner parameter) ownerName

namespace OwnerFrame

variable {parameter : Purelib.Data.Gaussian.Basic.Canonical}

open Purelib.Data in
open Purelib.Polynomial in
open Purelib.RootIsolation in
/-- Retain the two original root tracks from one exact isolation output.

Both owners use that output's indexed tracks and retain the same parameter and ambient box. -/
@[expose] def ownersOfIsolation (nonzero : parameter ≠ 0)
    (output : Exact.Basic.Output (SquareRootReconditioning.rootPolynomial parameter)
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (SquareRootReconditioning.rootPolynomial parameter)) 2) :
    Data.Vector (Owner parameter) 2 :=
  Vector.Basic.vectorOfFn fun index =>
    { parameterNonzero := nonzero
      ambient := Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (SquareRootReconditioning.rootPolynomial parameter)
      track := output.trackAt index }

open Purelib.Data in
/-- The owners retained from the canonical isolation are its canonical indexed owners.

Each bounded index selects the original track of the same retained isolation output. -/
theorem canonicalOwners_eq (nonzero : parameter ≠ 0) (index : Fin 2) :
    ownersOfIsolation nonzero (SquareRootReconditioning.isolationInput nonzero).isolation index =
      SquareRootReconditioning.canonicalOwner nonzero index := by
  rw [ownersOfIsolation, Vector.Basic.vectorOfFn_apply]
  rfl

open Purelib.Data in
open Purelib.Polynomial in
open Purelib.RootIsolation in
/-- Classify an owner against cached canonical endpoints and their retained assignment radius.

One assignment and one refinement supply a common-track bridge to the selected original occurrence. -/
@[expose] def selectFromCache (nonzero : parameter ≠ 0)
    (owners : Data.Vector (Owner parameter) 2)
    (canonical : ∀ index, owners index = SquareRootReconditioning.canonicalOwner nonzero index)
    (radius : Rat.Fraction.Rational) (positive : 0 < radius)
    (radius_eq : radius = Exact.Ownership.Radius.assignmentRadius (SquareRootReconditioning.rootPolynomial parameter)
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (SquareRootReconditioning.rootPolynomial parameter))
      (SquareRootReconditioning.isolationInput nonzero).isolation)
    (owner : Owner parameter) : OwnerSelection owners owner := by
  let assigned := SquareRootReconditioning.assignment nonzero owner
  let index : Fin 2 := assigned.owner.owner
  let refined := assigned.track.refine assigned.track.initial radius positive
  have commonStrict : assigned.track.initial.box.StrictInterior owner.track.initial.box := by
    rw [assigned.trackInitial]
    exact SquareRootReconditioning.assignment_state_strict_owner nonzero owner
  have freshStrict : refined.box.StrictInterior (owners index).track.initial.box := by
    rw [canonical index]
    change (assigned.track.refine assigned.track.initial radius positive).box.StrictInterior _
    subst radius
    exact assigned.owner.strict
  exact ⟨index, SquareRootTrackEquivalence.rootEquivalent_of_common_bridge nonzero
    owner.track assigned.track (owners index).track commonStrict radius positive refined rfl freshStrict⟩

open Purelib.Polynomial in
open Purelib.RootIsolation in
/-- Isolate and retain two square-root owners and their assignment radius once.

Classification reuses those endpoints and bridges through the finite assignment's actual common track to certify
operational equivalence. -/
@[expose] def build (nonzero : parameter ≠ 0) : OwnerFrame parameter := by
  let output := (SquareRootReconditioning.isolationInput nonzero).isolation
  let owners := ownersOfIsolation nonzero output
  let radius := Exact.Ownership.Radius.assignmentRadius (SquareRootReconditioning.rootPolynomial parameter)
    (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (SquareRootReconditioning.rootPolynomial parameter))
    output
  have positive : 0 < radius := Exact.Ownership.Radius.assignmentRadius_pos _ _ _
  refine ⟨owners, ?_, ?_⟩
  · intro first second equivalent
    rw [canonicalOwners_eq nonzero first, canonicalOwners_eq nonzero second] at equivalent
    exact SquareRootTrackEquivalence.canonicalOwner_index_eq_of_rootEquivalent nonzero first second equivalent
  · exact selectFromCache nonzero owners (canonicalOwners_eq nonzero) radius positive rfl

/-- Classifying a retained owner returns its original frame index. -/
theorem select_self (frame : OwnerFrame parameter) (index : Fin 2) :
    (frame.select (frame.owners index)).index = index :=
  (frame.distinguish index _ (frame.select (frame.owners index)).equivalent).symm

end OwnerFrame

end Purelib.Riemann.RootContinuation.RootOwnerFrames
