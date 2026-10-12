module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Riemann.Branches.PreparedPrimitiveSheets
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Riemann.Transport.PreparedOwnerHandoffChecks
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Separation.Certificate
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Riemann.RootContinuation.SquareRootReconditioning
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic

open Purelib.Approximation.Gaussian

open Purelib.Data

open Purelib.Geometry.Rational

open Purelib

@[expose] public section

/-!
# Bounded handoff diagnostics on the original owners' actual tails

An inconclusive initial-box check can be retried at displayed finite depths.
Both owners are refined along their own retained tracks. Every outcome is
transported back to the original root names, so a negative certificate
rejects the original handoff, not merely a pair of newly chosen roots.

The result caches both depths and the actual inspected boxes with their exact
provenance. Inconclusivity retains all unresolved box tests at that depth;
this interface makes no unsupported claim that any chosen depth suffices.
-/

namespace Purelib.RootIsolation.SquareRoot.Preparation.Handoff.Refinement

namespace HandoffOutcome

/-- Reindex semantic conclusions without executing an operational comparison
just to decide a box test. Distinctness and inconclusivity remain exact. -/
def reindex {first last leftName rightName : Name.Basic.Named} {left right : Box}
    (outcome : Riemann.Transport.PreparedOwnerHandoffChecks.SquareRootTrace.HandoffOutcome leftName rightName left
      right)
    (firstEquivalent : Unit → Equivalence.NamedEquivalent first leftName)
    (lastEquivalent : Unit → Equivalence.NamedEquivalent last rightName) :
      Riemann.Transport.PreparedOwnerHandoffChecks.SquareRootTrace.HandoffOutcome first last left right :=
  match outcome with
  | .leftInside contained equivalent =>
      .leftInside contained fun _ => (firstEquivalent ()).trans ((equivalent ()).trans (lastEquivalent ()).symm)
  | .rightInside contained equivalent =>
      .rightInside contained fun _ => (firstEquivalent ()).trans ((equivalent ()).trans (lastEquivalent ()).symm)
  | .distinct gap notEquivalent =>
      .distinct gap fun equivalent =>
        notEquivalent ((firstEquivalent ()).symm.trans (equivalent.trans (lastEquivalent ())))
  | .inconclusive unresolved => .inconclusive unresolved

end HandoffOutcome

set_option genInjectivity false in
/-- The depth and inspected boxes are executable data. Their specifications
remain abstract during record generation, avoiding elaboration of concrete
shrinking tracks in the generated dependent projections. -/
structure HandoffAttempt (first last : Name.Basic.Named) (leftAt rightAt : Nat → Box) where
  /-- The finite depth used to inspect the first original owner. -/ leftDepth : Nat
  /-- The finite depth used to inspect the second original owner. -/ rightDepth : Nat
  /-- The actual cached box inspected on the first owner's tail. -/ leftBox : Box
  /-- The actual cached box inspected on the second owner's tail. -/ rightBox : Box
  /-- The cached first box comes from its original tail at the retained depth. -/ leftBox_eq : leftBox = leftAt
    leftDepth
  /-- The cached second box comes from its original tail at the retained depth. -/ rightBox_eq : rightBox = rightAt
    rightDepth
  /-- The certified handoff, distinctness or inconclusive result on these exact cached boxes. -/ outcome :
    Riemann.Transport.PreparedOwnerHandoffChecks.SquareRootTrace.HandoffOutcome first last leftBox rightBox

constructive_injectivity HandoffAttempt

open Purelib.RootIsolation in
/-- A checked handoff attempt indexed by the two original owners and their actual refinement tails.

The retained depths select each owner's inspected box, while the outcome concerns their original root names. -/
abbrev OwnerHandoffAttempt {parameter : Gaussian.Basic.Canonical} (left right :
  Riemann.Topology.SquareRootContinuationChain.Owner parameter) :=
  SquareRoot.Preparation.Handoff.Refinement.HandoffAttempt (Riemann.Paths.OwnerTraceReadings.ownerName left)
    (Riemann.Paths.OwnerTraceReadings.ownerName right)
    (fun index => (left.refineAt index).track.initial.box)
    (fun index => (right.refineAt index).track.initial.box)

namespace OwnerHandoffAttempt

open Purelib.RootIsolation
/-- Reuse already materialized tails across several unequal-depth checks.
The equalities tie them to the original owners; no preparation is replayed. -/
def ofOwners {parameter : Gaussian.Basic.Canonical} (left right : Riemann.Topology.SquareRootContinuationChain.Owner
  parameter) (leftDepth rightDepth : Nat)
    (leftRefined rightRefined : Riemann.Topology.SquareRootContinuationChain.Owner parameter)
    (left_eq : leftRefined = left.refineAt leftDepth)
    (right_eq : rightRefined = right.refineAt rightDepth) :
      SquareRoot.Preparation.Handoff.Refinement.OwnerHandoffAttempt left right :=
  let checked := Riemann.Transport.PreparedOwnerHandoffChecks.SquareRootTrace.OwnerHandoff.check leftRefined
    rightRefined
  let firstEquivalent := fun (_ : Unit) =>
    Riemann.Branches.PreparedPrimitiveSheets.rootEquivalent_of_initial_refines left.parameterNonzero
      left.track leftRefined.track (by rw [left_eq]; exact left.refineAt_initial_refines leftDepth)
  let lastEquivalent := fun (_ : Unit) =>
    Riemann.Branches.PreparedPrimitiveSheets.rootEquivalent_of_initial_refines right.parameterNonzero
      right.track rightRefined.track (by rw [right_eq]; exact right.refineAt_initial_refines rightDepth)
  ⟨leftDepth, rightDepth, checked.leftBox, checked.rightBox,
    checked.leftBox_eq.trans (congrArg (fun owner => owner.track.initial.box) left_eq),
    checked.rightBox_eq.trans (congrArg (fun owner => owner.track.initial.box) right_eq),
    SquareRoot.Preparation.Handoff.Refinement.HandoffOutcome.reindex checked.outcome firstEquivalent lastEquivalent⟩

/-- Refine the two supplied occurrences once at the requested depths, then
check their retained boxes. No canonical owner assignment is performed. -/
def checkAt {parameter : Gaussian.Basic.Canonical} (left right : Riemann.Topology.SquareRootContinuationChain.Owner
  parameter) (leftDepth rightDepth : Nat) :
    SquareRoot.Preparation.Handoff.Refinement.OwnerHandoffAttempt left right :=
  SquareRoot.Preparation.Handoff.Refinement.OwnerHandoffAttempt.ofOwners left right leftDepth rightDepth (left.refineAt
    leftDepth) (right.refineAt rightDepth) rfl rfl

/-- The checked attempt retains exactly the two requested refinement depths. -/
theorem checkAt_depths {parameter : Gaussian.Basic.Canonical} (left right :
  Riemann.Topology.SquareRootContinuationChain.Owner parameter) (leftDepth rightDepth : Nat) :
    (SquareRoot.Preparation.Handoff.Refinement.OwnerHandoffAttempt.checkAt left right leftDepth rightDepth).leftDepth =
      leftDepth ∧
      (SquareRoot.Preparation.Handoff.Refinement.OwnerHandoffAttempt.checkAt left right leftDepth rightDepth).rightDepth
        = rightDepth := ⟨rfl, rfl⟩

end OwnerHandoffAttempt

end Purelib.RootIsolation.SquareRoot.Preparation.Handoff.Refinement
