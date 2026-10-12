module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
public import Purelib.Geometry.Rational.Box.Separation.Certificate
import Purelib.Data.Gaussian.Basic
public import Purelib.Riemann.Paths.PreparedPathGluing
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.CoherentRoot
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.RootIsolation.State.WindingOne.Basic

public import Purelib.Riemann.Branches.PreparedPrimitiveSheets
import Purelib.RootIsolation.SquareRoot.Preparation.StationaryObstruction
public import Purelib.Riemann.Topology.PreparedCycleModels

@[expose] public section

/-!
# Evidence-bearing checks of the actual prepared cycle handoffs

The legacy independently seeded A/B banks certify each piece separately.
Their stationary label cells do not certify agreement of the two actual
endpoint roots. Check the retained endpoint boxes before using such a join:
nested winding-one boxes certify agreement, positively separated boxes
certify distinct roots, and the remaining case is explicitly inconclusive.

This bounded check reads only the initial boxes of the supplied owners. It
does not isolate roots, refine an owner, or prepare a replacement path. The
cycle consumers retain each original prepared bank's terminal owner once.
An inconclusive result certifies exactly the three failed box tests, not
inequivalence of roots or failure of any finer attempt.
-/

namespace Purelib.Riemann.Transport.PreparedOwnerHandoffChecks.SquareRootTrace

open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients renaming CoefficientPolynomial -> Dense

open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Geometry.Rational (Box)

open Purelib.Data in
open Purelib.Riemann in
/-- Every operational approximation sample lies in its original owner's initial root box. -/
private theorem sample_inside_initial {parameter : Gaussian.Basic.Canonical} (owner : Owner parameter) (index : Nat) :
    owner.track.initial.box.Contains ((RootContinuation.CertifiedSquareRoot.approximation owner.track).sample index) :=
      by
  rw [RootContinuation.CertifiedSquareRoot.approximation_sample]
  exact (RootContinuation.CoherentRoot.state_refines_of_le owner.track (Nat.zero_le _)).contains
    (RootContinuation.CoherentRoot.state owner.track _).box.contains_anchor

open Purelib.Approximation in
open Purelib.Data in
open Purelib.Data.Rat.Fraction.Order in
open Purelib.Geometry.Rational (Box) in
open Purelib.Riemann in
/-- A positive gap between initial boxes rules out equivalence of the actual operational root names.

The comparison's arbitrarily close later samples contradict the retained geometric separation bound. -/
theorem not_equivalent_of_box_gap {parameter : Gaussian.Basic.Canonical} (left right : Owner parameter)
    (gap : Box.SeparationCertificate left.track.initial.box right.track.initial.box)
    (equivalent : Gaussian.Equivalence.NamedEquivalent (ownerName left) (ownerName right)) : False := by
  let comparison := (RootContinuation.SquareRootTrackEquivalence.approximationEquivalent_of_rootEquivalent
    left.parameterNonzero left.track right.track equivalent).compare 0 0 (gap.gap ^ 2)
      (Arithmetic.pow_pos_direct gap.positive 2)
  have lower := gap.lower (sample_inside_initial left comparison.leftIndex)
    (sample_inside_initial right comparison.rightIndex)
  exact (not_lt_of_ge lower) (comparison.close (Nat.le_refl _) (Nat.le_refl _))

open Purelib.Geometry.Rational (Box) in
/-- The three failed tests of a finite initial-box handoff attempt.

Neither containment direction nor positive separation was established; these retained failures make no claim about a
later refined attempt. -/
structure UnresolvedHandoff (left right : Box) : Prop where
  /-- The left initial box does not refine the right initial box. -/ leftNotInside : ¬left.Refines right
  /-- The right initial box does not refine the left initial box. -/ rightNotInside : ¬right.Refines left
  /-- The retained initial boxes fail the separation test. -/ notSeparated : ¬left.Separated right

open Purelib.Approximation in
open Purelib.Approximation.Gaussian.Name in
open Purelib.Geometry.Rational (Box) in
open Purelib.Geometry.Rational (Box) in
set_option genInjectivity false in
/-- Certified agreement, distinctness or an unresolved finite handoff attempt.

Containment retains a deferred operational comparison. Distinctness retains a positive box gap and proof against
equivalence; inconclusivity retains all three failed tests. -/
inductive HandoffOutcome (first last : Basic.Named) (left right : Box) where
  /-- Left containment with the corresponding deferred operational root equivalence. -/ | leftInside (contained :
    left.Refines right) (equivalent : Unit → Gaussian.Equivalence.NamedEquivalent first last)
  /-- Right containment with the corresponding deferred operational root equivalence. -/ | rightInside (contained :
    right.Refines left) (equivalent : Unit → Gaussian.Equivalence.NamedEquivalent first last)
  /-- A positive geometric gap and proof that the actual root names cannot be equivalent. -/ | distinct (gap :
    Box.SeparationCertificate left right)
      (notEquivalent : Gaussian.Equivalence.NamedEquivalent first last → False)
  /-- The unresolved outcome with every failed initial-box test. -/ | inconclusive (unresolved : UnresolvedHandoff left
    right)

constructive_injectivity HandoffOutcome

open Purelib.Approximation.Gaussian.Name in
open Purelib.Geometry.Rational (Box) in
set_option genInjectivity false in
/-- A checked handoff retaining the actual compared endpoint boxes.

Exact equations tie the cached boxes to the original owners, and the outcome concerns those same retained observations.
-/
structure CachedHandoff (first last : Basic.Named) (leftInitial rightInitial : Box) where
  /-- The actual cached initial box of the left owner. -/ leftBox : Box
  /-- The actual cached initial box of the right owner. -/ rightBox : Box
  /-- The cached left box equals the original initial box. -/ leftBox_eq : leftBox = leftInitial
  /-- The cached right box equals the original initial box. -/ rightBox_eq : rightBox = rightInitial
  /-- The certified outcome for the two retained boxes and original root names. -/ outcome : HandoffOutcome first last
    leftBox rightBox

constructive_injectivity CachedHandoff

open Purelib.Data in
/-- The cached handoff indexed by the two actual square-root owners. -/
abbrev OwnerHandoff {parameter : Gaussian.Basic.Canonical} (left right : Owner parameter) :=
  CachedHandoff (ownerName left) (ownerName right) left.track.initial.box right.track.initial.box

namespace OwnerHandoff

section
/-- Decide rational box refinement by its four coordinate inequalities. -/
private instance (left right : Box) : Decidable (left.Refines right) := by
  unfold Box.Refines
  infer_instance

/-- Decide rational box refinement by its four coordinate inequalities. -/
instance boxRefinesDecidable (left right : Box) : Decidable (left.Refines right) := by
  unfold Box.Refines
  infer_instance

end

open Purelib.Data in
open Purelib.Geometry.Rational (Box) in
open Purelib.Riemann in
/-- Check both containment directions and separation of the actual initial boxes.

The three finite tests reuse cached endpoint boxes and retain complete evidence for success, distinctness or an
unresolved attempt. -/
def check {parameter : Gaussian.Basic.Canonical} (left right : Owner parameter) : OwnerHandoff left right := by
  let leftBox := left.track.initial.box
  let rightBox := right.track.initial.box
  refine ⟨leftBox, rightBox, rfl, rfl, ?_⟩
  if contained : leftBox.Refines rightBox then
    exact .leftInside contained fun _ =>
      (Branches.PreparedPrimitiveSheets.rootEquivalent_of_initial_refines left.parameterNonzero
        right.track left.track contained).symm
  else if containedBack : rightBox.Refines leftBox then
    exact .rightInside containedBack fun _ =>
      (Branches.PreparedPrimitiveSheets.rootEquivalent_of_initial_refines left.parameterNonzero
        left.track right.track containedBack)
  else if separated : leftBox.Separated rightBox then
    let gap := Box.separationCertificate separated
    exact .distinct gap (not_equivalent_of_box_gap left right gap)
  else
    exact .inconclusive ⟨contained, containedBack, separated⟩

open Purelib.Geometry.Rational (Box) in
open Purelib.Geometry.Rational (Box) in
open Purelib.Polynomial.Dense.Gaussian.Basic in
open Purelib.RootIsolation.SquareRoot.Preparation.StationaryObstruction in
open Purelib.RootIsolation.State.WindingOne in
/-- A retained positive endpoint gap rules out a stationary owner-path join.

Any finite trace whose vertices remain at the reference anchor would induce root equivalence, contradicting the actual
checked gap. -/
theorem no_stationary_join {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {ambient : Box}
    (reference : Basic.WindingOneState polynomial ambient)
    {left right : Owner (polynomial.eval reference.box.anchor)}
    (checked : OwnerHandoff left right)
    (gap : Box.SeparationCertificate checked.leftBox checked.rightBox)
    (path : OwnerPath polynomial reference.box.anchor left reference.box.anchor right)
    (stationary : ∀ point ∈ path.vertices, point = reference.box.anchor) : False := by
  let originalGap : Box.SeparationCertificate left.track.initial.box right.track.initial.box :=
    cast (congrArg₂ Box.SeparationCertificate checked.leftBox_eq checked.rightBox_eq) gap
  exact not_equivalent_of_box_gap left right originalGap (OwnerPath.rootEquivalent_of_stationary reference path
    stationary).symm

end OwnerHandoff

end Purelib.Riemann.Transport.PreparedOwnerHandoffChecks.SquareRootTrace

namespace Purelib.Riemann.Transport.PreparedOwnerHandoffChecks.PreparedCycleModels

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Riemann.Topology.PreparedCycleModels (PreparedDoublePath PreparedBoundaryDoublePath)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Transport.PreparedOwnerHandoffChecks.SquareRootTrace (OwnerHandoff)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

variable {genus : Nat} {curve : HyperellipticCurve genus}

set_option genInjectivity false in
/-- A handoff report retaining its original terminal owner.

The exact owner equation keeps the checked occurrence tied to the supplied path endpoint while the abstract check family
preserves dependent report types. -/
structure RetainedHandoff (Occurrence : Type) (Check : Occurrence → Occurrence → Type)
    (original next : Occurrence) where
  /-- The retained actual terminal owner occurrence. -/ finishOwner : Occurrence
  /-- The retained occurrence equals the original path's terminal owner. -/ finishOwner_eq : finishOwner = original
  /-- The handoff check from the retained terminal occurrence to the next owner. -/ report : Check finishOwner next

constructive_injectivity RetainedHandoff

section
open Purelib.Data
/-- A checked square-root handoff retaining the original terminal owner. -/
abbrev CheckedOwnerHandoff {parameter : Gaussian.Basic.Canonical} (original next : Owner parameter) :=
  RetainedHandoff (Owner parameter) OwnerHandoff original next

/-- Retain the actual terminal owner and check its handoff to the next owner. -/
def checkOwnerHandoff {parameter : Gaussian.Basic.Canonical} (original next : Owner parameter) :
    CheckedOwnerHandoff original next :=
  ⟨original, rfl, OwnerHandoff.check original next⟩

end

set_option genInjectivity false in
/-- The two separately retained handoff reports of a doubled path. -/
structure TwoHandoffs (AtFinish AtStart : Type) where
  /-- The handoff report at the forward path's finish. -/ atFinish : AtFinish
  /-- The handoff report at the backward path's finish. -/ atStart : AtStart

constructive_injectivity TwoHandoffs

set_option genInjectivity false in
/-- The four ordered handoff reports of a boundary doubled path. -/
structure FourHandoffs (AfterForward AfterRight AfterBackward AfterLeft : Type) where
  /-- The handoff from the forward connector to the right boundary. -/ afterForward : AfterForward
  /-- The handoff from the right boundary to the backward connector. -/ afterRight : AfterRight
  /-- The handoff from the backward connector to the left boundary. -/ afterBackward : AfterBackward
  /-- The final handoff from the left boundary to the forward connector. -/ afterLeft : AfterLeft

constructive_injectivity FourHandoffs

namespace PreparedDoublePath

open Purelib.Riemann
/-- Both actual endpoint handoffs of the original connector-only doubled path.

Each report retains its terminal owner and remains available independently of the other outcome. -/
abbrev Handoffs (data : PreparedDoublePath curve) :=
  TwoHandoffs (CheckedOwnerHandoff (Paths.PreparedPathGluing.finishOwner data.forward) data.backwardOwner)
    (CheckedOwnerHandoff (Paths.PreparedPathGluing.finishOwner data.backward) data.forwardOwner)

/-- Check both actual owner joins of the retained connector-only doubled path. -/
def checkHandoffs (data : PreparedDoublePath curve) : Handoffs data :=
  ⟨checkOwnerHandoff (Paths.PreparedPathGluing.finishOwner data.forward) data.backwardOwner,
    checkOwnerHandoff (Paths.PreparedPathGluing.finishOwner data.backward) data.forwardOwner⟩

end PreparedDoublePath

namespace PreparedBoundaryDoublePath

open Purelib.Riemann
/-- All four owner handoffs of the original boundary doubled path.

The ordered reports retain both connector joins, both boundary joins and the actual final root return. -/
abbrev Handoffs (data : PreparedBoundaryDoublePath curve) :=
  FourHandoffs (CheckedOwnerHandoff (Paths.PreparedPathGluing.finishOwner data.forward) data.rightBoundaryOwner)
    (CheckedOwnerHandoff (Paths.PreparedPathGluing.finishOwner data.rightBoundary) data.backwardOwner)
    (CheckedOwnerHandoff (Paths.PreparedPathGluing.finishOwner data.backward) data.leftBoundaryOwner)
    (CheckedOwnerHandoff (Paths.PreparedPathGluing.finishOwner data.leftBoundary) data.forwardOwner)

/-- Check the four actual owner joins around the retained boundary doubled path. -/
def checkHandoffs (data : PreparedBoundaryDoublePath curve) : Handoffs data :=
  ⟨checkOwnerHandoff (Paths.PreparedPathGluing.finishOwner data.forward) data.rightBoundaryOwner,
    checkOwnerHandoff (Paths.PreparedPathGluing.finishOwner data.rightBoundary) data.backwardOwner,
    checkOwnerHandoff (Paths.PreparedPathGluing.finishOwner data.backward) data.leftBoundaryOwner,
    checkOwnerHandoff (Paths.PreparedPathGluing.finishOwner data.leftBoundary) data.forwardOwner⟩

end PreparedBoundaryDoublePath

end Purelib.Riemann.Transport.PreparedOwnerHandoffChecks.PreparedCycleModels
