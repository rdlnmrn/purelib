module

public import Purelib.Riemann.RootContinuation.CoherentRoot.Comparison
public import Purelib.Riemann.RootContinuation.CoherentRoot.Polynomial
public import Purelib.Riemann.RootContinuation.CoherentRoot.Refinement
public import Purelib.RootIsolation.Track.Transport
import Purelib.Geometry.Rational.Box.Refinement
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Reconditioning from an original cached winding-one state

The original root certificate pays one finite box request. Its actual cached
state becomes the initial state of the same refinement operation; no global
isolation is repeated. Nested winding certificates compare both original
sample programs while their independent indices and caches remain retained.
-/

public section

namespace Purelib.Riemann.RootContinuation.CoherentRoot

open Purelib.RootIsolation
open Purelib.Geometry.Rational
open Purelib.Approximation.Gaussian
open Purelib.Polynomial.Approximation.Gaussian renaming Residual -> PolynomialResidual

variable {polynomial : GaussianPolynomial} {ambient : Box}
variable {track : WindingOneTrack polynomial ambient}

set_option genInjectivity false in
/-- A restart of an original root program at one paid original cache state.

The paid request retains its original start, stopping stage and state. The new
track keeps the original refinement operation, and its cached name is stored
once with the strict original-owner containment certificate.
-/
structure Reconditioning (original : CertifiedName track) (start : Nat) where
  /-- The actual paid request on the original cache, after a positive state index. -/
  paid : Refinement original (start + 1)
  /-- The restarted track on the same polynomial and original ambient box. -/
  restarted : WindingOneTrack polynomial ambient
  /-- The restart changes only the initial state to that same paid cache state. -/
  restarted_eq : restarted = track.atState paid.current
  /-- The actual retained coherent root certificate of the restarted program. -/
  root : CertifiedName restarted
  /-- The retained certificate is the same deterministic restarted construction. -/
  root_eq : root = certifiedName restarted original.degreePositive
  /-- The restarted initial box lies strictly inside the original initial owner. -/
  nested : restarted.initial.box.StrictInterior track.initial.box

constructive_injectivity Reconditioning

namespace Reconditioning

/-- Restart from the first original cached state satisfying a positive box request.

The bounded paid search uses the original cache. Its returned state initializes
the original refinement procedure, so completed work is reused directly.
-/
@[expose] def ofTarget (original : CertifiedName track) (start : Nat)
    (targetSq : Coordinate) (positive : 0 < targetSq) : Reconditioning original start :=
  let paid := Refinement.ofTarget original (start + 1) targetSq positive
  let restarted := track.atState paid.current
  { paid := paid
    restarted := restarted
    restarted_eq := rfl
    root := certifiedName restarted original.degreePositive
    root_eq := rfl
    nested := by
      have positiveIndex : 0 < paid.index :=
        (Nat.zero_lt_succ start).trans_le paid.index_ge
      have firstStrict : (state track 1).box.StrictInterior track.initial.box :=
        track.strict track.initial (Purelib.Data.Rat.Bounds.AccuracyRadius.accuracyRadius (stepTarget track 0))
          (Purelib.Data.Rat.Bounds.AccuracyRadius.accuracyRadius_pos (stepTarget_positive track 0))
      have contained := (Box.Refinement.StrictInterior.of_refines firstStrict)
        (state_refines_of_le track positiveIndex)
      change paid.current.box.StrictInterior track.initial.box
      rewrite [paid.current_eq, original.stateAt_eq]
      exact contained }

/-- Restart directly from a retained complete original paid refinement.

The payment equality preserves the original start and squared request. Its
actual cached state initializes the same track operation and coherent root
construction, retaining the original strict owner containment certificate.
-/
@[expose] def ofRefinement (original : CertifiedName track) (start : Nat)
    (targetSq : Coordinate) (positive : 0 < targetSq)
    (paid : Refinement original (start + 1))
    (same : paid = Refinement.ofTarget original (start + 1) targetSq positive) :
    Reconditioning original start :=
  { paid := paid
    restarted := track.atState paid.current
    restarted_eq := rfl
    root := certifiedName (track.atState paid.current) original.degreePositive
    root_eq := rfl
    nested := by
      change paid.current.box.StrictInterior track.initial.box
      rewrite [same]
      exact (ofTarget original start targetSq positive).nested }

/-- The retained complete paid refinement gives exactly the original restart construction. -/
theorem ofRefinement_eq (original : CertifiedName track) (start : Nat)
    (targetSq : Coordinate) (positive : 0 < targetSq)
    (paid : Refinement original (start + 1))
    (same : paid = Refinement.ofTarget original (start + 1) targetSq positive) :
    ofRefinement original start targetSq positive paid same = ofTarget original start targetSq positive := by
  cases same
  rfl

/-- Restart a retained original paid state while consuming its cached ambient reading. -/
@[expose] def ofRefinementFromAmbient (cachedAmbient : Box) (ambientSame : cachedAmbient = ambient)
    (original : CertifiedName track) (start : Nat)
    (targetSq : Coordinate) (positive : 0 < targetSq)
    (paid : Refinement original (start + 1))
    (same : paid = Refinement.ofTarget original (start + 1) targetSq positive) :
    Reconditioning original start := by
  subst ambient
  exact ofRefinement original start targetSq positive paid same

/-- Cached ambient and payment readbacks preserve the complete original restart. -/
theorem ofRefinementFromAmbient_eq (cachedAmbient : Box) (ambientSame : cachedAmbient = ambient)
    (original : CertifiedName track) (start : Nat)
    (targetSq : Coordinate) (positive : 0 < targetSq)
    (paid : Refinement original (start + 1))
    (same : paid = Refinement.ofTarget original (start + 1) targetSq positive) :
    ofRefinementFromAmbient cachedAmbient ambientSame original start targetSq positive paid same =
      ofTarget original start targetSq positive := by
  cases ambientSame
  exact ofRefinement_eq original start targetSq positive paid same

/-- Restart the original cache using an exact retained reading of its ambient box.

The supplied equality transports the existing track and certificate together.
The actual cached box initializes the restart; the complete result still has
the original owner, cache, start and squared request as its indices.
-/
@[expose] def ofTargetFromAmbient (cachedAmbient : Box) (same : cachedAmbient = ambient)
    (original : CertifiedName track) (start : Nat)
    (targetSq : Coordinate) (positive : 0 < targetSq) : Reconditioning original start := by
  subst ambient
  exact ofTarget original start targetSq positive

/-- A retained ambient readback gives exactly the original complete restart construction. -/
theorem ofTargetFromAmbient_eq (cachedAmbient : Box) (same : cachedAmbient = ambient)
    (original : CertifiedName track) (start : Nat)
    (targetSq : Coordinate) (positive : 0 < targetSq) :
    ofTargetFromAmbient cachedAmbient same original start targetSq positive =
      ofTarget original start targetSq positive := by
  cases same
  rfl

variable {original : CertifiedName track} {start : Nat}

/-- The reconditioned initial state is literally the retained paid original cache state. -/
theorem initial (prepared : Reconditioning original start) :
    prepared.restarted.initial = prepared.paid.current := by
  rewrite [prepared.restarted_eq]
  rfl

/-- Reconditioning retains the original refinement operation on every supplied state and target. -/
theorem refine (prepared : Reconditioning original start)
    (current : WindingOneState polynomial ambient) (target : Coordinate) (positive : 0 < target) :
    prepared.restarted.refine current target positive = track.refine current target positive := by
  rewrite [prepared.restarted_eq]
  rfl

/-- The retained restart reads the same actual original cache state at its initial sample. -/
theorem first_sample (prepared : Reconditioning original start) :
    prepared.root.approximation.sample 0 = (original.stateAt prepared.paid.index).box.anchor := by
  rewrite [prepared.root.approximation_eq, approximation_sample]
  change prepared.restarted.initial.box.anchor = _
  rewrite [prepared.initial, prepared.paid.current_eq]
  rfl

/-- Compare the two actual original and restarted sample programs at independent requested starts.

The original squarefree input and strict owner containment supply the finite
winding argument. Both paid comparisons consume their actual retained caches.
-/
def equivalent (prepared : Reconditioning original start) (input : FTA.Squarefree.Input polynomial) :
    Equivalence.Equivalent original.approximation prepared.root.approximation :=
  original.compare_nested_prepared input prepared.root prepared.nested

/-- The unchanged original coherent root channel agrees with its retained restarted root channel. -/
def namedEquivalent (prepared : Reconditioning original start) (input : FTA.Squarefree.Input polynomial) :
    Equivalence.NamedEquivalent original.value.name prepared.root.value.name := by
  rewrite [original.value_approximation, prepared.root.value_approximation]
  exact (prepared.equivalent input).toNamed

/-- Compare the original and actual restarted channels through their computed geometric index schedules.

The original input and retained strict nesting supply the root comparison.
The procedure computes sufficient indices from both original refiner schedules
and consumes no numerical state refinement while choosing those indices.
-/
@[expose] def scheduledEquivalent (prepared : Reconditioning original start)
    (input : FTA.Squarefree.Input polynomial) :
    Equivalence.NamedEquivalent original.value.name prepared.root.value.name := by
  rewrite [original.value_approximation, prepared.root.value_approximation]
  exact (original.compare_nested input prepared.root prepared.nested).toNamed

/-- Retain the restarted residual on the unchanged original channel using its explicit computed comparison schedule. -/
@[expose] def scheduledResidual (prepared : Reconditioning original start)
    (input : FTA.Squarefree.Input polynomial) : PolynomialResidual polynomial original.value :=
  prepared.root.residualCertificate.transport (prepared.scheduledEquivalent input)

/-- Read the restarted quantitative residual program as evidence on the unchanged original root channel.

The original owner and cache remain retained by the restart. The numerical
view consumes the actual restarted source program and its own recalibrated
geometric bound, joined to the original channel by the explicit comparison.
-/
@[expose] def residualCertificate (prepared : Reconditioning original start)
    (input : FTA.Squarefree.Input polynomial) : PolynomialResidual polynomial original.value :=
  let numerical := prepared.root.residualCertificate
  { numerical with equivalent := (prepared.namedEquivalent input).trans numerical.equivalent }

/-- The original-channel residual view reads the same actual restarted cache samples. -/
theorem residualCertificate_sample (prepared : Reconditioning original start)
    (input : FTA.Squarefree.Input polynomial) (index : Nat) :
    (prepared.residualCertificate input).source.sample index = prepared.root.approximation.sample index := rfl

/-- The paid restart retains exactly the squared request supplied to its constructor. -/
theorem ofTarget_targetSq (original : CertifiedName track) (start : Nat)
    (targetSq : Coordinate) (positive : 0 < targetSq) :
    (ofTarget original start targetSq positive).paid.targetSq = targetSq :=
  Refinement.ofTarget_targetSq original (start + 1) targetSq positive

end Reconditioning

end Purelib.Riemann.RootContinuation.CoherentRoot

end
