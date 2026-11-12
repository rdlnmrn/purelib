module

public import Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.Expression
import Purelib.RootIsolation.Progressive.Chamber.Path.Basic
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.Progressive.Chamber.Overlap
import Purelib.Data.Gaussian.Basic
meta import Purelib.Elab.ConstructiveInjectivity

public section

namespace Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.Trace.Expression

open Purelib.RootIsolation.Progressive.Chamber.Frame (ChamberFrame)
open Purelib.RootIsolation.Progressive.Chamber.Overlap (ChamberOverlap)
open Purelib.RootIsolation.Progressive.Chamber.Path.Basic (ChamberPath)
open Purelib.Approximation.Gaussian.Acquisition.Expression
open Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Geometric
open Purelib.Approximation.Gaussian.Enclosure (Ball)
open Purelib.Data.Gaussian.Basic (Canonical)
open InteriorStep.Expression (Program)

set_option genInjectivity false in
/-- Actual common programmes for every occurrence of one exact original prepared trace.

Each piece retains its complete original parent, computed expression result,
source/target caches and genuine interior family. Failure at one occurrence
does not discard any later occurrence or successful preceding programme.
-/
inductive Pieces (expression : Checked.Expr 1) (displayed : Canonical → Fin 2 → Ball) :
    {start finish : ChamberFrame} → {path : ChamberPath start finish} → {index : start.Index} →
    {source : Root start index} → {trace : Trace path index source} → Interior trace → Type 2 where
  /-- The empty original family retains the same actual root cache. -/
  | nil {frame : ChamberFrame} {index : frame.Index} (root : Root frame index) :
      Pieces expression displayed (.nil root)
  /-- Retain one actual original computed programme and the complete remaining original family. -/
  | cons {start middle finish : ChamberFrame} {step : ChamberOverlap start middle}
      {remaining : ChamberPath middle finish} {index : start.Index} {source : Root start index}
      {target : Root middle (step.matching.forward index)} {rest : Trace remaining (step.matching.forward index) target}
      (original : Trace (.cons step remaining) index source)
      (original_eq : original = Trace.cons (source := source) target rest)
      (piece : InteriorStep step index source target) (tail : Interior rest)
      (program : Program piece expression)
      (computed : program = InteriorStep.Expression.inspect piece expression displayed)
      (remaining : Pieces expression displayed tail) :
      Pieces expression displayed (.cons original original_eq piece tail)

constructive_injectivity Pieces

/-- Compute every original piece's common programme once, including every later unresolved occurrence. -/
@[expose] def inspect {start finish : ChamberFrame} {path : ChamberPath start finish}
    {index : start.Index} {source : Root start index} {trace : Trace path index source}
    (family : Interior trace) (expression : Checked.Expr 1) (displayed : Canonical → Fin 2 → Ball) :
    Pieces expression displayed family :=
  Interior.casesOn
    (motive := fun {_ _ _ _ _ _} family => (expression : Checked.Expr 1) →
      (displayed : Canonical → Fin 2 → Ball) → Pieces expression displayed family)
    family
    (fun {frame originalIndex} root expression displayed =>
      @Pieces.nil expression displayed frame originalIndex root)
    (fun {start middle finish step path originalIndex source target rest} original same piece tail
        expression displayed =>
      let program := InteriorStep.Expression.inspect piece expression displayed
      let remaining := inspect tail expression displayed
      @Pieces.cons expression displayed start middle finish step path originalIndex source target rest
        original same piece tail program rfl remaining)
    expression displayed
termination_by structural family

namespace Pieces

/-- Complete positive common programmes for every exact original trace occurrence. -/
@[expose] def Ready {expression : Checked.Expr 1} {displayed : Canonical → Fin 2 → Ball} :
    {start finish : ChamberFrame} → {path : ChamberPath start finish} → {index : start.Index} →
    {source : Root start index} → {trace : Trace path index source} → {family : Interior trace} →
    Pieces expression displayed family → Type
  | _, _, _, _, _, _, _, .nil _ => PUnit
  | _, _, _, _, _, _, _, .cons _ _ _ _ program _ remaining =>
      { common : Bounds.Common program.balls expression // program.result = .prepared common } × Ready remaining

/-- An exact structural occurrence whose computed common programme has an unresolved denominator condition. -/
@[expose] def Missing {expression : Checked.Expr 1} {displayed : Canonical → Fin 2 → Ball} :
    {start finish : ChamberFrame} → {path : ChamberPath start finish} → {index : start.Index} →
    {source : Root start index} → {trace : Trace path index source} → {family : Interior trace} →
    Pieces expression displayed family → Type
  | _, _, _, _, _, _, _, .nil _ => Empty
  | _, _, _, _, _, _, _, .cons _ _ _ _ program _ remaining =>
      { request : Bounds.Request program.balls expression // program.result = .requested request } ⊕
        Missing remaining

/-- Enumerate every unresolved original trace occurrence from the same cached programmes in original order. -/
@[expose] def missing {expression : Checked.Expr 1} {displayed : Canonical → Fin 2 → Ball}
    {start finish : ChamberFrame} {path : ChamberPath start finish} {index : start.Index}
    {source : Root start index} {trace : Trace path index source} {family : Interior trace}
    (pieces : Pieces expression displayed family) : List pieces.Missing :=
  Pieces.casesOn (motive := fun {_ _ _ _ _ _ _} pieces => List pieces.Missing) pieces
    (fun {_ _} _ => [])
    (fun {_ _ _ _ _ _ _ _ _} _ _ _ _ program _ remaining =>
      let tail := (missing remaining).map Sum.inr
      match program.result.request with
      | none => tail
      | some request => Sum.inl request :: tail)
termination_by structural pieces

set_option genInjectivity false in
/-- All positive original programmes or the first actual unresolved occurrence beside the complete retained tree. -/
inductive Reading {expression : Checked.Expr 1} {displayed : Canonical → Fin 2 → Ball}
    {start finish : ChamberFrame} {path : ChamberPath start finish} {index : start.Index}
    {source : Root start index} {trace : Trace path index source} {family : Interior trace}
    (pieces : Pieces expression displayed family) where
  /-- Every original piece's actual cached programme has its positive common tree. -/
  | ready (programmes : pieces.Ready)
  /-- The first unresolved domain occurrence is retained; all other occurrences remain in the original tree. -/
  | requested (first : pieces.Missing)

constructive_injectivity Reading

/-- Read actual cached outcomes without repeating expression inspection or arithmetic bound construction. -/
def read {expression : Checked.Expr 1} {displayed : Canonical → Fin 2 → Ball}
    {start finish : ChamberFrame} {path : ChamberPath start finish} {index : start.Index}
    {source : Root start index} {trace : Trace path index source} {family : Interior trace}
    (pieces : Pieces expression displayed family) : pieces.Reading :=
  Pieces.casesOn (motive := fun {_ _ _ _ _ _ _} pieces => pieces.Reading) pieces
    (fun {_ _} _ => .ready PUnit.unit)
    (fun {_ _ _ _ _ _ _ _ _} _ _ _ _ program _ remaining =>
      match same : program.result with
      | .requested request => .requested (.inl ⟨request, same⟩)
      | .prepared common =>
          match read remaining with
          | .ready rest => .ready ⟨⟨common, same⟩, rest⟩
          | .requested first => .requested (.inr first))
termination_by structural pieces

set_option genInjectivity false in
/-- A cached reading retaining its complete original trace programme and exact defining computation. -/
structure Decision {expression : Checked.Expr 1} {displayed : Canonical → Fin 2 → Ball}
    {start finish : ChamberFrame} {path : ChamberPath start finish} {index : start.Index}
    {source : Root start index} {trace : Trace path index source} {family : Interior trace}
    (pieces : Pieces expression displayed family) where
  /-- The same entire original programme tree remains physically retained. -/
  original : Pieces expression displayed family
  /-- Its complete original-parent identity. -/
  original_eq : original = pieces
  /-- The actual positive programmes or first unresolved occurrence. -/
  result : original.Reading
  /-- The reading is the actual original finite cached-result computation. -/
  computed : result = read original

constructive_injectivity Decision

/-- Read all original cached programmes while retaining the same physical parent tree and defining equation. -/
def decide {expression : Checked.Expr 1} {displayed : Canonical → Fin 2 → Ball}
    {start finish : ChamberFrame} {path : ChamberPath start finish} {index : start.Index}
    {source : Root start index} {trace : Trace path index source} {family : Interior trace}
    (pieces : Pieces expression displayed family) : pieces.Decision := ⟨pieces, rfl, read pieces, rfl⟩

section

variable {expression : Checked.Expr 1} {displayed : Canonical → Fin 2 → Ball}
    {start middle finish : ChamberFrame} {step : ChamberOverlap start middle}
    {path : ChamberPath middle finish} {index : start.Index} {source : Root start index}
    {target : Root middle (step.matching.forward index)} {rest : Trace path (step.matching.forward index) target}
    {original : Trace (.cons step path) index source}
    {same : original = Trace.cons (source := source) target rest}
    {piece : InteriorStep step index source target} {tail : Interior rest}
    {program : Program piece expression}
    {computed : program = InteriorStep.Expression.inspect piece expression displayed}
    {restPrograms : Pieces expression displayed tail}

/-- The first unresolved programme preserves itself and every actual unresolved tail occurrence in order. -/
private theorem missing_cons_requested_readback (request : Bounds.Request program.balls expression)
    (requested : program.result = .requested request) :
    (Pieces.cons original same piece tail program computed restPrograms).missing =
      Sum.inl ⟨request, requested⟩ :: restPrograms.missing.map Sum.inr := by
  change (match program.result.request with
    | none => restPrograms.missing.map Sum.inr
    | some first => Sum.inl first :: restPrograms.missing.map Sum.inr) = _
  rewrite [Bounds.Outcome.request_of_requested requested]
  rfl

/-- The first unresolved programme preserves itself and every actual unresolved tail occurrence in order. -/
theorem missing_cons_requested (request : Bounds.Request program.balls expression)
    (requested : program.result = .requested request) :
    (Pieces.cons original same piece tail program computed restPrograms).missing =
      Sum.inl ⟨request, requested⟩ :: restPrograms.missing.map Sum.inr :=
  missing_cons_requested_readback request requested

/-- A positive first programme preserves every actual unresolved tail occurrence without re-inspection. -/
private theorem missing_cons_prepared_readback (common : Bounds.Common program.balls expression)
    (prepared : program.result = .prepared common) :
    (Pieces.cons original same piece tail program computed restPrograms).missing =
      restPrograms.missing.map Sum.inr := by
  change (match program.result.request with
    | none => restPrograms.missing.map Sum.inr
    | some first => Sum.inl first :: restPrograms.missing.map Sum.inr) = _
  rewrite [Bounds.Outcome.request_of_prepared prepared]
  rfl

/-- A positive first programme preserves every actual unresolved tail occurrence without re-inspection. -/
theorem missing_cons_prepared (common : Bounds.Common program.balls expression)
    (prepared : program.result = .prepared common) :
    (Pieces.cons original same piece tail program computed restPrograms).missing =
      restPrograms.missing.map Sum.inr :=
  missing_cons_prepared_readback common prepared

/-- Read the actual original first common programme from the complete retained positive decision. -/
@[expose] def Ready.first
    (ready : (Pieces.cons original same piece tail program computed restPrograms).Ready) :
    Bounds.Common program.balls expression := ready.1.val

/-- The retained first common programme is the positive branch of the actual original computation. -/
theorem Ready.first_result
    (ready : (Pieces.cons original same piece tail program computed restPrograms).Ready) :
    program.result = .prepared ready.first := ready.1.property

/-- Read complete positive programmes for the same actual original remaining trace. -/
@[expose] def Ready.remaining
    (ready : (Pieces.cons original same piece tail program computed restPrograms).Ready) :
    restPrograms.Ready := ready.2

/-- Realize the exact first positive common programme on one actual retained same-parameter input. -/
def Ready.realizeFirst
    (ready : (Pieces.cons original same piece tail program computed restPrograms).Ready)
    {time : Purelib.Data.Rat.Fraction.Rational} {inside : InteriorStep.Inside time}
    (input : program.Input time inside) (geometry : Bounds.Inputs program.balls input.admitted) :=
  ready.first.realize input.admitted geometry

/-- Every actual parameter's first positive realization lies in the same stored bound at every index. -/
theorem Ready.containsFirst
    (ready : (Pieces.cons original same piece tail program computed restPrograms).Ready)
    {time : Purelib.Data.Rat.Fraction.Rational} {inside : InteriorStep.Inside time}
    (input : program.Input time inside) (geometry : Bounds.Inputs program.balls input.admitted) (stage : Nat) :
    ready.first.ball.Contains ((ready.realizeFirst input geometry).value.enclosing.source.sample stage) :=
  ready.first.contains input.admitted geometry stage

end

end Pieces

set_option genInjectivity false in
/-- Every computed original piece programme or the exact existing missing-interior request.

Absence is a request for genuine prepared input, not evidence of a pole or
singularity. The original trace and starting cache remain in the existing
request owner for a later retry with actual interior evidence.
-/
inductive Outcome {start finish : ChamberFrame} {path : ChamberPath start finish} {index : start.Index}
    {source : Root start index} (trace : Trace path index source) (expression : Checked.Expr 1)
    (displayed : Canonical → Fin 2 → Ball) (offered : Option (Interior trace)) : Type 2 where
  /-- The genuine supplied original family and every actual computed piece programme remain retained. -/
  | prepared (family : Interior trace) (offered_eq : offered = some family)
      (pieces : Pieces expression displayed family) (computed : pieces = inspect family expression displayed)
  /-- The original geometric family is absent; retain its exact original request. -/
  | requested (request : InteriorRequest trace offered)

constructive_injectivity Outcome

/-- Consume genuine original interior evidence and inspect every piece, or retain the exact absent-input request. -/
@[expose] def prepare {start finish : ChamberFrame} {path : ChamberPath start finish} {index : start.Index}
    {source : Root start index} (trace : Trace path index source) (expression : Checked.Expr 1)
    (displayed : Canonical → Fin 2 → Ball) (offered : Option (Interior trace)) :
    Outcome trace expression displayed offered :=
  match offered with
  | some family => .prepared family rfl (inspect family expression displayed) rfl
  | none => .requested ⟨trace, rfl, source, rfl, rfl⟩

end Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.Trace.Expression
end
