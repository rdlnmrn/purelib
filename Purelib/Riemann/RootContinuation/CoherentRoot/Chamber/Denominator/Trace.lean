module

public import Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.Denominator
import Purelib.RootIsolation.Progressive.Chamber.Path.Basic
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.Riemann.RootContinuation.CoherentRoot.Polynomial
import Purelib.RootIsolation.Progressive.Chamber.Overlap
import Purelib.Approximation.Gaussian.Division.Obstruction.Zero
import Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Construction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
meta import Purelib.Elab.ConstructiveInjectivity

public section

namespace Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.Trace.Denominator

open Purelib.RootIsolation.Progressive.Chamber.Frame (ChamberFrame)
open Purelib.RootIsolation.Progressive.Chamber.Overlap (ChamberOverlap)
open Purelib.RootIsolation.Progressive.Chamber.Path.Basic (ChamberPath)
open Purelib.Riemann.RootContinuation.CoherentRoot.Chamber
open Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.InteriorStep
open Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.InteriorStep.Denominator (Kind Point Inspection)
open Purelib.Approximation.Gaussian.Acquisition.Expression
open Purelib.Geometry.Rational (Box)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Norm
open Purelib.Approximation.Gaussian.Division.Obstruction

set_option genInjectivity false in
/-- Once computed inspections along every piece of the exact original prepared family.

Each cons retains the original trace, actual piece, complete remaining family,
computed inspection and all remaining inspections. An inconclusive piece never
causes a later occurrence or an earlier successful margin to be discarded.
-/
inductive Pieces (kind : Kind) : {start finish : ChamberFrame} → {path : ChamberPath start finish} →
    {index : start.Index} → {source : Root start index} → {trace : Trace path index source} →
    Interior trace → Type 2 where
  /-- The empty original family retains its actual original root cache. -/
  | nil {frame : ChamberFrame} {index : frame.Index} (root : Root frame index) : Pieces kind (.nil root)
  /-- Retain the actual original piece and its once computed result beside the complete original tail. -/
  | cons {start middle finish : ChamberFrame} {step : ChamberOverlap start middle}
      {remaining : ChamberPath middle finish} {index : start.Index} {source : Root start index}
      {target : Root middle (step.matching.forward index)} {rest : Trace remaining (step.matching.forward index) target}
      (original : Trace (.cons step remaining) index source)
      (original_eq : original = Trace.cons (source := source) target rest)
      (piece : InteriorStep step index source target) (tail : Interior rest)
      (inspection : Inspection piece kind)
      (computed : inspection = InteriorStep.Denominator.inspectPiece piece kind)
      (remaining : Pieces kind tail) : Pieces kind (.cons original original_eq piece tail)

constructive_injectivity Pieces

/-- Inspect all actual original pieces once, preserving the whole family even after inconclusivity. -/
@[expose] def inspect : {start finish : ChamberFrame} → {path : ChamberPath start finish} →
    {index : start.Index} → {source : Root start index} → {trace : Trace path index source} →
    (family : Interior trace) → (kind : Kind) → Pieces kind family
  | _, _, _, _, _, _, @Interior.nil frame originalIndex root, kind =>
      @Pieces.nil kind frame originalIndex root
  | _, _, _, _, _, _,
      @Interior.cons start middle finish step path originalIndex source target rest original same piece tail, kind =>
      let inspection := InteriorStep.Denominator.inspectPiece piece kind
      let remaining := inspect tail kind
      @Pieces.cons kind start middle finish step path originalIndex source target rest
        original same piece tail inspection rfl remaining

namespace Pieces

/-- A genuine sufficient clearance for every original piece, tied to its actual cached inspection. -/
@[expose] def Ready {kind : Kind} : {start finish : ChamberFrame} → {path : ChamberPath start finish} →
    {index : start.Index} → {source : Root start index} → {trace : Trace path index source} →
    {family : Interior trace} → Pieces kind family → Type
  | _, _, _, _, _, _, _, .nil _ => PUnit
  | _, _, _, _, _, _, _, .cons _ _ piece _ inspection _ remaining =>
      { clearance : Box.OutsideSide.Prepared piece.bridge.val.box kind.pole //
        inspection.result = .apart clearance } × Ready remaining

/-- The structural original occurrence of an unresolved cached box condition.

The left branch is this exact original piece and its actual inconclusive
inspection. The right branch is an occurrence in the retained original tail.
No numeric occurrence identifier or newly selected branch is introduced.
-/
@[expose] def Missing {kind : Kind} : {start finish : ChamberFrame} → {path : ChamberPath start finish} →
    {index : start.Index} → {source : Root start index} → {trace : Trace path index source} →
    {family : Interior trace} → Pieces kind family → Type
  | _, _, _, _, _, _, _, .nil _ => Empty
  | _, _, _, _, _, _, _, .cons _ _ piece _ inspection _ remaining =>
      { contained : piece.bridge.val.box.Contains kind.pole // inspection.result = .inconclusive contained } ⊕
        Missing remaining

/-- Enumerate every unresolved original occurrence from its cached result without re-inspecting any box. -/
@[expose] def missing {kind : Kind} : {start finish : ChamberFrame} → {path : ChamberPath start finish} →
    {index : start.Index} → {source : Root start index} → {trace : Trace path index source} →
    {family : Interior trace} → (pieces : Pieces kind family) → List pieces.Missing
  | _, _, _, _, _, _, _, .nil _ => []
  | _, _, _, _, _, _, _, .cons _ _ _ _ inspection _ remaining =>
      let tail := (missing remaining).map Sum.inr
      match same : inspection.result with
      | .apart _ => tail
      | .inconclusive contained => Sum.inl ⟨contained, same⟩ :: tail

set_option genInjectivity false in
/-- Complete sufficient clearance or the first actual unresolved original occurrence.

The indexed inspection tree retains every successful margin and all other
unresolved occurrences. Inconclusivity establishes no exact denominator zero.
-/
inductive Decision {kind : Kind} {start finish : ChamberFrame} {path : ChamberPath start finish}
    {index : start.Index} {source : Root start index} {trace : Trace path index source}
    {family : Interior trace} (pieces : Pieces kind family) where
  /-- Every original piece has a positive margin from its retained actual box inspection. -/
  | ready (clearance : pieces.Ready)
  /-- Retain the first original unresolved occurrence while the tree keeps every remaining result. -/
  | requested (first : pieces.Missing)

constructive_injectivity Decision

/-- Read the actual cached results in original order, without repeating coordinate tests or margin construction. -/
@[expose] def decide {kind : Kind} : {start finish : ChamberFrame} → {path : ChamberPath start finish} →
    {index : start.Index} → {source : Root start index} → {trace : Trace path index source} →
    {family : Interior trace} → (pieces : Pieces kind family) → pieces.Decision
  | _, _, _, _, _, _, _, .nil _ => .ready PUnit.unit
  | _, _, _, _, _, _, _, .cons _ _ _ _ inspection _ remaining =>
      match same : inspection.result with
      | .inconclusive contained => .requested (.inl ⟨contained, same⟩)
      | .apart clearance =>
          match decide remaining with
          | .ready rest => .ready ⟨⟨clearance, same⟩, rest⟩
          | .requested first => .requested (.inr first)

section

variable {kind : Kind} {start middle finish : ChamberFrame} {step : ChamberOverlap start middle}
    {path : ChamberPath middle finish} {index : start.Index} {source : Root start index}
    {target : Root middle (step.matching.forward index)} {rest : Trace path (step.matching.forward index) target}
    {original : Trace (.cons step path) index source}
    {same : original = Trace.cons (source := source) target rest}
    {piece : InteriorStep step index source target} {tail : Interior rest}
    {inspection : Inspection piece kind}
    {computed : inspection = InteriorStep.Denominator.inspectPiece piece kind}
    {restInspections : Pieces kind tail}

/-- An inconclusive original piece preserves itself and every unresolved actual tail occurrence in order. -/
theorem missing_cons_inconclusive (contained : piece.bridge.val.box.Contains kind.pole)
    (inconclusive : inspection.result = .inconclusive contained) :
    (Pieces.cons original same piece tail inspection computed restInspections).missing =
      Sum.inl ⟨contained, inconclusive⟩ :: restInspections.missing.map Sum.inr := by
  cases inspection with
  | mk original originalEq result resultEq =>
      cases inconclusive
      rfl

/-- A successful original piece retains every unresolved tail occurrence without another coordinate test. -/
theorem missing_cons_apart (clearance : Box.OutsideSide.Prepared piece.bridge.val.box kind.pole)
    (apart : inspection.result = .apart clearance) :
    (Pieces.cons original same piece tail inspection computed restInspections).missing =
      restInspections.missing.map Sum.inr := by
  cases inspection with
  | mk original originalEq result resultEq =>
      cases apart
      rfl

/-- Read the first original piece's genuine computed margin from complete trace clearance. -/
@[expose] def Ready.first (ready : (Pieces.cons original same piece tail inspection computed restInspections).Ready) :
    Box.OutsideSide.Prepared piece.bridge.val.box kind.pole := ready.1.val

/-- Read complete clearance for the actual retained remaining original family. -/
@[expose] def Ready.remaining
    (ready : (Pieces.cons original same piece tail inspection computed restInspections).Ready) :
    restInspections.Ready := ready.2

/-- The first positive margin is exactly the apart branch of the actual cached original inspection. -/
theorem Ready.first_result (ready : (Pieces.cons original same piece tail inspection computed restInspections).Ready) :
    inspection.result = .apart ready.first := ready.1.property

/-- Prepare an actual requested parameter using the retained first-piece margin and original point cache.

The clearance holds at every parameter through the original family containment
bridge. Payment, the original denominator and residual reciprocal cache are
constructed only for this actual retained requested point.
-/
@[expose] def Ready.prepareFirst
    (ready : (Pieces.cons original same piece tail inspection computed restInspections).Ready)
    {time : Rational} {inside : Inside time} (point : Point piece time inside) :=
  point.prepare kind ready.first

/-- Every actual original parameter's denominator has the retained positive first-piece lower quadrance. -/
theorem Ready.lowerFirst
    (ready : (Pieces.cons original same piece tail inspection computed restInspections).Ready)
    {time : Rational} {inside : Inside time} (point : Point piece time inside) (stage : Nat) :
    ready.first.margin ≤ Basic.normSq ((kind.samples point.root.geometric).sample stage) :=
  point.lower kind ready.first stage

/-- An exact original pole at any actual parameter contradicts this complete first-piece clearance. -/
theorem Ready.excludesPole
    (ready : (Pieces.cons original same piece tail inspection computed restInspections).Ready)
    {time : Rational} {inside : Inside time} (point : Point piece time inside)
    (pole : InteriorStep.Denominator.Pole point kind) : False := by
  have sameChannel := congrArg Checked.Completed.channel pole.child_eq
  exact Zero.ZeroIdentity.incompatible_prepared (sameChannel ▸ pole.zero)
    (ready.prepareFirst point).paid.prepared

/-- The positive parameter consumer agrees with consuming this exact retained cached inspection. -/
theorem Ready.prepareFirst_result
    (ready : (Pieces.cons original same piece tail inspection computed restInspections).Ready)
    {time : Rational} {inside : Inside time} (point : Point piece time inside) :
    inspection.prepare point = .prepared point rfl (ready.prepareFirst point) := by
  unfold InteriorStep.Denominator.Inspection.prepare
  rewrite [ready.first_result]
  rfl

end

set_option genInjectivity false in
/-- An exact pole at a retained actual rational parameter of one original prepared piece. -/
structure PointPole {start middle : ChamberFrame} {step : ChamberOverlap start middle} {index : start.Index}
    {source : Root start index} {target : Root middle (step.matching.forward index)}
    (piece : InteriorStep step index source target) (kind : Kind) where
  /-- The actual original rational parameter of the obstruction. -/
  time : Rational
  /-- This parameter belongs to the original closed piece. -/
  inside : Inside time
  /-- The complete actual original point/root cache at that parameter. -/
  point : Point piece time inside
  /-- The same completed original denominator has a proved operational zero identity. -/
  pole : InteriorStep.Denominator.Pole point kind

constructive_injectivity PointPole

/-- Read the existing exact checked inverse obstruction on this same original retained denominator. -/
@[expose] def PointPole.invalid {start middle : ChamberFrame} {step : ChamberOverlap start middle}
    {index : start.Index} {source : Root start index} {target : Root middle (step.matching.forward index)}
    {piece : InteriorStep step index source target} {kind : Kind} (pole : PointPole piece kind) := pole.pole.invalid

/-- The structural original occurrence and actual parameter of a proved denominator-zero obstruction. -/
@[expose] def Obstruction {kind : Kind} : {start finish : ChamberFrame} → {path : ChamberPath start finish} →
    {index : start.Index} → {source : Root start index} → {trace : Trace path index source} →
    {family : Interior trace} → Pieces kind family → Type 2
  | _, _, _, _, _, _, _, .nil _ => PEmpty.{3}
  | _, _, _, _, _, _, _, .cons _ _ piece _ _ _ remaining => PointPole piece kind ⊕ Obstruction remaining

/-- Complete positive clearance refutes an exact original pole at any retained piece and parameter. -/
theorem Ready.noPole {kind : Kind} : {start finish : ChamberFrame} → {path : ChamberPath start finish} →
    {index : start.Index} → {source : Root start index} → {trace : Trace path index source} →
    {family : Interior trace} → (pieces : Pieces kind family) → pieces.Ready → pieces.Obstruction → False
  | _, _, _, _, _, _, _, .nil _, _, obstruction => nomatch obstruction
  | _, _, _, _, _, _, _, .cons _ _ piece _ _ _ remaining, ready, obstruction => by
      change PointPole piece kind ⊕ Obstruction remaining at obstruction
      cases obstruction with
      | inl pole => exact ready.excludesPole pole.point pole.pole
      | inr pole => exact Ready.noPole remaining ready.remaining pole

end Pieces

set_option genInjectivity false in
/-- An original complete prepared family and its once computed whole-trace denominator assessment.

The original trace, family and denominator kind remain actual retained values.
Their cache tree and its decision have complete procedure readbacks; unresolved
pieces remain available even when another piece has a successful margin.
-/
structure Assessment {start finish : ChamberFrame} {path : ChamberPath start finish}
    {index : start.Index} {source : Root start index} {trace : Trace path index source}
    (family : Interior trace) (kind : Kind) where
  /-- The complete actual original trace, including all numerical occurrences. -/
  original : Trace path index source
  /-- The retained trace is the original supplied trace. -/
  original_eq : original = trace
  /-- The complete actual original prepared interior family and endpoint handoffs. -/
  interior : Interior trace
  /-- The retained family is exactly this supplied family. -/
  interior_eq : interior = family
  /-- The actual literal denominator syntax kind is retained. -/
  denominator : Kind
  /-- The retained kind is exactly the requested original denominator. -/
  denominator_eq : denominator = kind
  /-- Every actual original piece and its once computed inspection. -/
  pieces : Pieces kind family
  /-- The cache tree is exactly the original whole-family inspection. -/
  pieces_eq : pieces = inspect family kind
  /-- The once read whole-trace decision on these same cached inspections. -/
  decision : pieces.Decision
  /-- The cached decision is exactly the original finite read of this tree. -/
  decision_eq : decision = pieces.decide

constructive_injectivity Assessment

/-- Assess every original piece and retain its actual cached decision once. -/
@[expose] def assess {start finish : ChamberFrame} {path : ChamberPath start finish}
    {index : start.Index} {source : Root start index} {trace : Trace path index source}
    (family : Interior trace) (kind : Kind) : Assessment family kind :=
  let pieces := inspect family kind
  let decision := pieces.decide
  ⟨trace, rfl, family, rfl, kind, rfl, pieces, rfl, decision, rfl⟩

/-- Assessment retains the complete original input family rather than constructing another family. -/
theorem assess_interior {start finish : ChamberFrame} {path : ChamberPath start finish}
    {index : start.Index} {source : Root start index} {trace : Trace path index source}
    (family : Interior trace) (kind : Kind) : (assess family kind).interior = family := rfl

/-- Assessment retains the original denominator kind as actual data. -/
theorem assess_denominator {start finish : ChamberFrame} {path : ChamberPath start finish}
    {index : start.Index} {source : Root start index} {trace : Trace path index source}
    (family : Interior trace) (kind : Kind) : (assess family kind).denominator = kind := rfl

set_option genInjectivity false in
/-- Whole-trace sufficient clearance, an exact finite unresolved condition or a missing interior family.

A positive branch is conditional on the genuinely supplied original interior
family. Neither absence nor a pole point inside an enclosing box establishes
an actual denominator zero or manufactures a whole-path continuation.
-/
inductive Outcome {start finish : ChamberFrame} {path : ChamberPath start finish}
    {index : start.Index} {source : Root start index} (trace : Trace path index source)
    (offered : Option (Interior trace)) (kind : Kind) : Type 2 where
  /-- All actual original pieces have sufficient computed margins. -/
  | prepared (family : Interior trace) (offered_eq : offered = some family)
      (assessment : Assessment family kind) (clearance : assessment.pieces.Ready)
      (decided : assessment.decision = .ready clearance)
  /-- The complete original assessment retains every unresolved condition and prior successful cache. -/
  | inconclusive (family : Interior trace) (offered_eq : offered = some family)
      (assessment : Assessment family kind) (first : assessment.pieces.Missing)
      (decided : assessment.decision = .requested first)
  /-- A specific actual original parameter and denominator have an exact proved operational pole. -/
  | obstructed (family : Interior trace) (offered_eq : offered = some family)
      (assessment : Assessment family kind) (pole : assessment.pieces.Obstruction)
  /-- The same original trace and source cache lack genuine supplied interior evidence. -/
  | missing (request : InteriorRequest trace offered)

constructive_injectivity Outcome

/-- Consume the exact supplied original family or retain its missing contract, without preparing any geometry. -/
@[expose] def prepare {start finish : ChamberFrame} {path : ChamberPath start finish}
    {index : start.Index} {source : Root start index} (trace : Trace path index source)
    (kind : Kind) : (offered : Option (Interior trace)) → Outcome trace offered kind
  | none => .missing ⟨trace, rfl, source, rfl, rfl⟩
  | some family =>
      let assessment := assess family kind
      match decided : assessment.decision with
      | .ready clearance => .prepared family rfl assessment clearance decided
      | .requested first => .inconclusive family rfl assessment first decided

/-- The absent-family branch retains exactly the original trace and starting cache. -/
theorem prepare_missing {start finish : ChamberFrame} {path : ChamberPath start finish}
    {index : start.Index} {source : Root start index} (trace : Trace path index source) (kind : Kind) :
    prepare trace kind none = .missing ⟨trace, rfl, source, rfl, rfl⟩ := rfl

end Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.Trace.Denominator

end
