module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Family
import Purelib.Data.Vector.Dependent
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedRequest.Occurrences
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Jet.Occurrences
import Purelib.Curves.Legendre.Periods.Jets.Basic
import Purelib.Curves.Legendre.Periods.Jets.Connection
import Purelib.Curves.Legendre.Periods.Jets.PicardFuchs
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Parameter.Regular

/-! # Retained local members on a finite parameter sample family

Each entry keeps the original generated Frame, shifted Request, positional
completion family and six-channel jet with its whole factory equations.
The finite vector constructs each entry once; later edge comparisons read
those same cached vertices instead of acquiring a new pair per edge.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Legendre.Periods.Jets.Basic (SynchronizedPeriodJet)
open Purelib.Data.Vector (DependentVector)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named RootChain)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {reference : AccuracyRequest}

variable (source : Requested covered chain current floor rootStage reference)
    (ranges : ParameterRange covered) (allocation : ParameterRange.StripAllocation ranges)
    {root : Named} (roots : RootChain (parent :: parents) root root)
    (widths : Fin (parent :: parents).length → AccuracyRequest)
    (targetCurrent targetFloor targetRootStage : Nat)
    (offset : Canonical) (admitted : Norm.Basic.normSq offset ≤ allocation.bound)

/-- The complete original offset-member caches, with their actual Frame and jet factory equations.

This is the exact dependent tuple returned by the original member
constructor. It retains its shifted blocks, whole geometry, Request,
completion family and connection/residual certificates without copying
fields or replacing any of their owners.
-/
@[expose] def LocalMember :=
  (target : {value : Paths.Frame (parameter + offset) //
    value = ranges.targetFrame offset (admitted.trans allocation.bound_le_regularBound)}) ×
  (member : Shifted (parameter := parameter) (increment := offset) (frame := frame)
    (basis := basis) (target := target.val) (count := count) (parent := parent) (parents := parents)
    (covered := covered) (chain := chain) (current := current) (floor := floor)
    (rootStage := rootStage) (accuracy := reference) source ranges allocation admitted widths roots
    targetCurrent targetFloor targetRootStage) ×
  (completed : member.requested.request.attempt.OccurrenceFamily) ×
  {actual : (jet : SynchronizedPeriodJet target.val) ×
      Jets.Connection.ConnectionCertificate jet × Jets.PicardFuchs.PicardFuchsCertificate jet //
    actual.1 = OccurrenceCompletion.jet (parameter := parameter + offset) (frame := target.val)
      (basis := basis) (count := count) (floor := targetFloor) (rootStage := targetRootStage)
      member.requested.request.covered member.requested.request.chain (fun stage => (completed stage).val)}

namespace LocalMember

/-- Construct the original offset member once and retain the complete output of its continuation. -/
def build : LocalMember source ranges allocation roots widths
    targetCurrent targetFloor targetRootStage offset admitted :=
  source.withLocalMember ranges allocation roots widths targetCurrent targetFloor targetRootStage offset admitted
    (fun target target_eq member completed actual factory =>
      ⟨⟨target, target_eq⟩, member, completed, ⟨actual, factory⟩⟩)

variable {source ranges allocation roots widths targetCurrent targetFloor targetRootStage offset admitted}
    (cached : LocalMember source ranges allocation roots widths
      targetCurrent targetFloor targetRootStage offset admitted)

/-- Read the original generated Frame from this retained member. -/
abbrev targetFrame : Paths.Frame (parameter + offset) := cached.1.val

/-- The stored Frame retains its complete original target-frame factory equation. -/
theorem targetFrame_eq : cached.targetFrame =
    ranges.targetFrame offset (admitted.trans allocation.bound_le_regularBound) := cached.1.property

/-- Read the same shifted blocks, whole geometry and actual reference Request. -/
abbrev member : Shifted (parameter := parameter) (increment := offset) (frame := frame)
    (basis := basis) (target := cached.targetFrame) (count := count) (parent := parent) (parents := parents)
    (covered := covered) (chain := chain) (current := current) (floor := floor)
    (rootStage := rootStage) (accuracy := reference) source ranges allocation admitted widths roots
    targetCurrent targetFloor targetRootStage := cached.2.1

/-- Read the original positional six-channel completion family. -/
abbrev completed : cached.member.requested.request.attempt.OccurrenceFamily := cached.2.2.1

/-- Read the same jet and its internally derived connection and scalar relation certificates. -/
abbrev actual : (jet : SynchronizedPeriodJet cached.targetFrame) ×
    Jets.Connection.ConnectionCertificate jet × Jets.PicardFuchs.PicardFuchsCertificate jet := cached.2.2.2.val

/-- Read the original six-channel jet without reconstructing a programme or member. -/
abbrev jet : SynchronizedPeriodJet cached.targetFrame := cached.actual.1

/-- The stored jet retains its original whole positional-family factory equation. -/
theorem jet_eq : cached.jet =
    OccurrenceCompletion.jet (parameter := parameter + offset) (frame := cached.targetFrame)
    (basis := basis) (count := count) (floor := targetFloor) (rootStage := targetRootStage)
    cached.member.requested.request.covered cached.member.requested.request.chain
    (fun stage => (cached.completed stage).val) := cached.2.2.2.property

end LocalMember

variable {offset admitted}

/-- Construct every original local member once at the supplied finite parameter offsets.

All entries use the same source, root chain, allocation and reference
accuracy. Each stored vertex retains its own admitted offset and actual
Frame. Dependent lookup reads those caches without invoking a producer.
-/
def localMembers {size : Nat} (offsets : Fin size → Canonical)
    (admitted : ∀ index, Norm.Basic.normSq (offsets index) ≤ allocation.bound) :
    DependentVector (fun index => LocalMember source ranges allocation roots widths
      targetCurrent targetFloor targetRootStage (offsets index) (admitted index)) :=
  DependentVector.ofFn (fun index => LocalMember.build source ranges allocation roots widths
    targetCurrent targetFloor targetRootStage (offsets index) (admitted index))

/-- Each stored vertex of the finite family retains its complete original member construction. -/
theorem localMembers_entry {size : Nat} (offsets : Fin size → Canonical)
    (admitted : ∀ index, Norm.Basic.normSq (offsets index) ≤ allocation.bound) (index : Fin size) :
    (localMembers source ranges allocation roots widths
      targetCurrent targetFloor targetRootStage offsets admitted).get index =
        LocalMember.build source ranges allocation roots widths
          targetCurrent targetFloor targetRootStage (offsets index) (admitted index) := by
  unfold localMembers
  exact DependentVector.ofFn_get _ index

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested

end
