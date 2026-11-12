module

public import Purelib.Approximation.Gaussian.Logarithm.Chart.Partial.Run
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Transport.Congruence
public import Purelib.Approximation.Gaussian.Provenance.Algebraic.Comparison
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored.Output
import Purelib.Approximation.Gaussian.Logarithm.Chart.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Difference
import Purelib.Approximation.Gaussian.Name.Coherent.Law.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.LogarithmState
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Comparisons of prepared logarithm transitions

The original source anchor and each target's retained refinement state remain
part of the comparison. Independent anchors require their factor and correction
comparisons; agreement of exponentials supplies no branch identification.
-/

public section
namespace Purelib.Approximation.Gaussian.Logarithm.Chart.Transition.Comparison

open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.Refinement
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Logarithm.Chart
open Purelib.Approximation.Gaussian.Provenance

set_option genInjectivity false in
/-- A transported logarithm retaining its original anchor, target and exact preparation state. -/
structure Prepared (sourceInput target : CoherentNamed)
    (source : Anchored.AnchoredChart sourceInput) : Type 2 where
  /-- The retained state of the original target process. -/
  state : LogarithmState.State target
  /-- The anchored logarithm on that state's original based future. -/
  output : Anchored.AnchoredChart (LogarithmState.preparedTarget state)
  /-- The output was constructed by the retained safe overlap extension. -/
  ready : Partial.Ready sourceInput target source state output

constructive_injectivity Prepared

namespace Prepared

/-- Construct a preparation directly from its original complete overlap extension. -/
@[expose] def ofExtension {sourceInput target : CoherentNamed}
    {source : Anchored.AnchoredChart sourceInput}
    (state : LogarithmState.State target)
    (extension : Transport.SafeOverlapExtension sourceInput (LogarithmState.preparedTarget state) source) :
    Prepared sourceInput target source :=
  ⟨state, extension.transport source, ⟨extension, rfl⟩⟩

/-- Resume a retained exact requirement without repeating its completed safety test. -/
@[expose] def resume {sourceInput target : CoherentNamed}
    (source : Anchored.AnchoredChart sourceInput) (state : LogarithmState.State target)
    (requirement : Partial.Requirement sourceInput target source state)
    (evidence : Partial.Requirement.Evidence requirement) : Prepared sourceInput target source :=
  let satisfied := Partial.Step.satisfy sourceInput target source state requirement evidence
  ⟨state, satisfied.output, satisfied.valid⟩

/-- The actual numerical transition from the original anchor to the retained transported output. -/
@[expose] def transition {sourceInput target : CoherentNamed}
    {source : Anchored.AnchoredChart sourceInput}
    (prepared : Prepared sourceInput target source) : CoherentNamed :=
  Difference.difference source.output prepared.output.output

/-- Relate the two retained based targets using their original input comparison. -/
def targetsEquivalent {leftTarget rightTarget : CoherentNamed}
    (leftState : LogarithmState.State leftTarget)
    (rightState : LogarithmState.State rightTarget)
    (inputs : NamedEquivalent leftTarget.name rightTarget.name) :
    NamedEquivalent (LogarithmState.preparedTarget leftState).name
      (LogarithmState.preparedTarget rightState).name :=
  NamedEquivalent.trans (NamedEquivalent.symm (LogarithmState.preparedTargetEquivalent leftState))
    (NamedEquivalent.trans inputs (LogarithmState.preparedTargetEquivalent rightState))

/-- Compare ready logarithms from independent inputs and explicitly aligned original anchors.

Each readiness certificate supplies its own overlap and clearance. The factor
identity and correction comparison fix the selected branch before congruence.
-/
def outputsEquivalent {leftSource rightSource leftTarget rightTarget : CoherentNamed}
    {leftAnchor : Anchored.AnchoredChart leftSource}
    {rightAnchor : Anchored.AnchoredChart rightSource}
    (left : Prepared leftSource leftTarget leftAnchor)
    (right : Prepared rightSource rightTarget rightAnchor)
    (inputs : NamedEquivalent leftTarget.name rightTarget.name)
    (factors : leftAnchor.chart.factor = rightAnchor.chart.factor)
    (corrections : NamedEquivalent leftAnchor.chart.correction rightAnchor.chart.correction) :
    NamedEquivalent left.output.output.name right.output.output.name := by
  rcases left.ready with ⟨leftExtension, leftOutput⟩
  rcases right.ready with ⟨rightExtension, rightOutput⟩
  rewrite [leftOutput, rightOutput]
  exact Congruence.output_respects _ _ _ _
    (targetsEquivalent left.state right.state inputs) factors corrections

/-- Compare transported logarithms from a common original anchor on independently represented targets. -/
def outputsEquivalentFromSameAnchor {sourceInput leftTarget rightTarget : CoherentNamed}
    {source : Anchored.AnchoredChart sourceInput}
    (left : Prepared sourceInput leftTarget source)
    (right : Prepared sourceInput rightTarget source)
    (inputs : NamedEquivalent leftTarget.name rightTarget.name) :
    NamedEquivalent left.output.output.name right.output.output.name :=
  left.outputsEquivalent right inputs rfl (NamedEquivalent.refl source.chart.correction)

/-- Compare the original transition programs after comparing their source and target outputs. -/
def transitionsEquivalent {leftSource rightSource leftTarget rightTarget : CoherentNamed}
    {leftAnchor : Anchored.AnchoredChart leftSource}
    {rightAnchor : Anchored.AnchoredChart rightSource}
    (left : Prepared leftSource leftTarget leftAnchor)
    (right : Prepared rightSource rightTarget rightAnchor)
    (sourceInputs : NamedEquivalent leftSource.name rightSource.name)
    (targetInputs : NamedEquivalent leftTarget.name rightTarget.name)
    (factors : leftAnchor.chart.factor = rightAnchor.chart.factor)
    (corrections : NamedEquivalent leftAnchor.chart.correction rightAnchor.chart.correction) :
    NamedEquivalent left.transition.name right.transition.name := by
  have sources := Congruence.output_respects _ _ leftAnchor rightAnchor sourceInputs factors corrections
  have targets := left.outputsEquivalent right targetInputs factors corrections
  exact (Law.Arithmetic.subtraction_respects
    left.output.output right.output.output leftAnchor.output rightAnchor.output targets sources).equivalent

end Prepared

set_option genInjectivity false in
/-- Branch alignment evidence between the original anchors of two preparations. -/
structure Alignment {leftSource rightSource : CoherentNamed}
    (leftAnchor : Anchored.AnchoredChart leftSource)
    (rightAnchor : Anchored.AnchoredChart rightSource) where
  /-- Both chart constructions retain this exact common rational factor. -/
  factors : leftAnchor.chart.factor = rightAnchor.chart.factor
  /-- The original correction programs represent the same selected branch. -/
  corrections : NamedEquivalent leftAnchor.chart.correction rightAnchor.chart.correction

constructive_injectivity Alignment

namespace Alignment

/-- Unequal original factors violate precisely the fixed-factor alignment contract. -/
theorem impossible_of_factor_ne {leftSource rightSource : CoherentNamed}
    {leftAnchor : Anchored.AnchoredChart leftSource}
    {rightAnchor : Anchored.AnchoredChart rightSource}
    (different : leftAnchor.chart.factor ≠ rightAnchor.chart.factor)
    (alignment : Alignment leftAnchor rightAnchor) : False := different alignment.factors

end Alignment

/-- The exact comparison proposition between two retained output programs. -/
@[expose] def OutputEquivalent {leftSource rightSource leftTarget rightTarget : CoherentNamed}
    {leftAnchor : Anchored.AnchoredChart leftSource}
    {rightAnchor : Anchored.AnchoredChart rightSource}
    (left : Prepared leftSource leftTarget leftAnchor)
    (right : Prepared rightSource rightTarget rightAnchor) : Type :=
  NamedEquivalent left.output.output.name right.output.output.name

set_option genInjectivity false in
/-- A request for alignment of these exact original chart anchors. -/
inductive AlignmentRequest {leftSource rightSource : CoherentNamed}
    (leftAnchor : Anchored.AnchoredChart leftSource)
    (rightAnchor : Anchored.AnchoredChart rightSource)
  /-- Supply the original factor identity and correction comparison. -/
  | missing

constructive_injectivity AlignmentRequest

namespace AlignmentRequest

/-- The precise evidence needed to discharge the retained anchor request. -/
@[expose] def Evidence {leftSource rightSource : CoherentNamed}
    {leftAnchor : Anchored.AnchoredChart leftSource}
    {rightAnchor : Anchored.AnchoredChart rightSource}
    (_request : AlignmentRequest leftAnchor rightAnchor) : Type := Alignment leftAnchor rightAnchor

end AlignmentRequest

/-- Consume supplied alignment once, reusing the exact prepared output programs.

An absent result is precisely the pending original-anchor alignment request;
both ready preparations remain the inputs and retain their completed work.
-/
@[expose] def comparePrepared {leftSource rightSource leftTarget rightTarget : CoherentNamed}
    {leftAnchor : Anchored.AnchoredChart leftSource}
    {rightAnchor : Anchored.AnchoredChart rightSource}
    (left : Prepared leftSource leftTarget leftAnchor)
    (right : Prepared rightSource rightTarget rightAnchor)
    (inputs : NamedEquivalent leftTarget.name rightTarget.name)
    (alignment : Option (Alignment leftAnchor rightAnchor)) :
    Except (AlignmentRequest leftAnchor rightAnchor) (OutputEquivalent left right) :=
  match alignment with
  | none => .error .missing
  | some evidence => .ok
      (left.outputsEquivalent right inputs evidence.factors evidence.corrections)

/-- The chart result required by the retained comparison of the original target channels. -/
@[expose] def AlgebraicOutput {leftSource rightSource leftTarget rightTarget : CoherentNamed}
    {leftAnchor : Anchored.AnchoredChart leftSource} {rightAnchor : Anchored.AnchoredChart rightSource}
    (left : Prepared leftSource leftTarget leftAnchor) (right : Prepared rightSource rightTarget rightAnchor)
    (comparison : Algebraic.Comparison leftTarget rightTarget) : Type :=
  match comparison with
  | .equal _ => Except (AlignmentRequest leftAnchor rightAnchor) (OutputEquivalent left right)
  | .distinct _ _ => PUnit

/-- Compare algebraic targets and, when equal, their original prepared logarithm outputs.

The result retains the full actual algebraic comparison and its request floors.
Equal target values still require alignment of the original chart anchors;
distinct targets retain their original difference preparation and rejection. -/
@[expose] def compareAlgebraicPrepared {leftSource rightSource leftTarget rightTarget : CoherentNamed}
    {leftAnchor : Anchored.AnchoredChart leftSource} {rightAnchor : Anchored.AnchoredChart rightSource}
    (left : Prepared leftSource leftTarget leftAnchor) (right : Prepared rightSource rightTarget rightAnchor)
    (leftEvidence : Algebraic.Sidecar leftTarget) (rightEvidence : Algebraic.Sidecar rightTarget)
    (alignment : Option (Alignment leftAnchor rightAnchor)) (leftStart rightStart : Nat := 0)
    (inspectInitial : Bool := true) (inspectLocal : Bool := inspectInitial)
    (inspectBound : Bool := inspectInitial) :
    (compared : Algebraic.Sidecar.Compared leftEvidence rightEvidence leftStart rightStart) ×
      AlgebraicOutput left right compared.comparison := by
  let compared := leftEvidence.compare rightEvidence leftStart rightStart inspectInitial inspectLocal inspectBound
  refine ⟨compared, ?_⟩
  match compared.comparison with
  | .equal inputs => exact comparePrepared left right inputs alignment
  | .distinct _ _ => exact PUnit.unit

set_option genInjectivity false in
/-- Two bounded chart preflights retaining original starts, budgets and both terminal certificates.

Each terminal payload records readiness, a safety-certified overlap request, or
exhausted clearance refinement. No failed finite check becomes invalidity.
-/
structure Preflight {sourceInput leftTarget rightTarget : CoherentNamed}
    (source : Anchored.AnchoredChart sourceInput)
    (leftStart : LogarithmState.State leftTarget)
    (rightStart : LogarithmState.State rightTarget) : Type 2 where
  /-- The number of refinements offered to the left original process. -/
  leftFuel : Nat
  /-- The number of refinements offered to the right original process. -/
  rightFuel : Nat
  /-- The retained result of the left finite run. -/
  left : Partial.Run.RunResult sourceInput leftTarget source leftStart
  /-- The retained result of the right finite run. -/
  right : Partial.Run.RunResult sourceInput rightTarget source rightStart
  /-- The left result is from this exact original attempt. -/
  left_eq : left = Partial.Run.attempt sourceInput leftTarget source leftStart leftFuel
  /-- The right result is from this exact original attempt. -/
  right_eq : right = Partial.Run.attempt sourceInput rightTarget source rightStart rightFuel

constructive_injectivity Preflight

/-- Run independent finite chart schedules and retain the actual terminal work for later resumption. -/
@[expose] def preflight {sourceInput leftTarget rightTarget : CoherentNamed}
    (source : Anchored.AnchoredChart sourceInput)
    (leftStart : LogarithmState.State leftTarget)
    (rightStart : LogarithmState.State rightTarget)
    (leftFuel rightFuel : Nat) : Preflight source leftStart rightStart where
  leftFuel := leftFuel
  rightFuel := rightFuel
  left := Partial.Run.attempt sourceInput leftTarget source leftStart leftFuel
  right := Partial.Run.attempt sourceInput rightTarget source rightStart rightFuel
  left_eq := rfl
  right_eq := rfl

end Purelib.Approximation.Gaussian.Logarithm.Chart.Transition.Comparison
end
