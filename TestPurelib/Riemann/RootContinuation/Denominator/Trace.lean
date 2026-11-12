module

import Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.Denominator.Trace
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.Riemann.RootContinuation.CoherentRoot.Polynomial
import Purelib.RootIsolation.Progressive.Chamber.Overlap
import Purelib.RootIsolation.Progressive.Chamber.Path.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction

namespace TestPurelib.Riemann.RootContinuation.Denominator.Trace

open Purelib.RootIsolation.Progressive.Chamber.Frame (ChamberFrame)
open Purelib.RootIsolation.Progressive.Chamber.Overlap (ChamberOverlap)
open Purelib.RootIsolation.Progressive.Chamber.Path.Basic (ChamberPath)
open Purelib.Riemann.RootContinuation.CoherentRoot.Chamber
open Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.InteriorStep
open Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.InteriorStep.Denominator (Kind Point Inspection)
open Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.Trace.Denominator
open Purelib.Geometry.Rational (Box)
open Purelib.Data.Gaussian.Norm
open Purelib.Data.Rat.Fraction (Rational)

section

variable {start middle finish : ChamberFrame} {step : ChamberOverlap start middle}
    {path : ChamberPath middle finish} {index : start.Index} {source : Root start index}
    {target : Root middle (step.matching.forward index)} {rest : Trace path (step.matching.forward index) target}
    {original : Trace (.cons step path) index source}
    {same : original = Trace.cons (source := source) target rest}
    {piece : InteriorStep step index source target} {tail : Trace.Interior rest}
    {kind : Kind} {inspection : Inspection piece kind}
    {computed : inspection = InteriorStep.Denominator.inspectPiece piece kind}
    {remaining : Pieces kind tail}
    (ready : (Pieces.cons original same piece tail inspection computed remaining).Ready)
    (time : Rational) (inside : Inside time) (point : Point piece time inside)

/-- Whole-trace clearance supplies an actual positive first-piece bound at every retained original parameter. -/
example (stage : Nat) : ready.first.margin ≤ Basic.normSq ((kind.samples point.root.geometric).sample stage) :=
  ready.lowerFirst point stage

/-- An actual parameter consumer reuses the first original cached inspection and margin. -/
example : inspection.prepare point = .prepared point rfl (ready.prepareFirst point) :=
  ready.prepareFirst_result point

/-- Original paid inverse preparation retains the literal original channel's computed reciprocal cache. -/
example : (ready.prepareFirst point).cache.input = (point.completed kind).sidecar.residual :=
  (ready.prepareFirst point).cache.input_eq

/-- The actual payment uses half the original box's retained computed margin. -/
example : (ready.prepareFirst point).paid.target = ready.first.margin / 2 :=
  (ready.prepareFirst point).paid.target_eq

/-- An exact pole at this actual original parameter contradicts complete sufficient trace clearance. -/
example (pole : InteriorStep.Denominator.Pole point kind) : False := ready.excludesPole point pole

/-- An inconclusive original piece retains all unresolved actual tail occurrences in their original order. -/
example (contained : piece.bridge.val.box.Contains kind.pole)
    (inconclusive : inspection.result = .inconclusive contained) :
    (Pieces.cons original same piece tail inspection computed remaining).missing =
      Sum.inl ⟨contained, inconclusive⟩ :: remaining.missing.map Sum.inr :=
  Pieces.missing_cons_inconclusive contained inconclusive

end

section

variable {start finish : ChamberFrame} {path : ChamberPath start finish} {index : start.Index}
    {source : Root start index} (trace : Trace path index source) (family : Trace.Interior trace) (kind : Kind)

/-- Whole-trace preparation honestly retains the missing original interior-family contract. -/
example : prepare trace kind none = Outcome.missing ⟨trace, rfl, source, rfl, rfl⟩ := prepare_missing trace kind

/-- Assessment keeps the complete actual original prepared family and same denominator syntax. -/
example : (assess family kind).interior = family ∧ (assess family kind).denominator = kind :=
  ⟨assess_interior family kind, assess_denominator family kind⟩

/-- No original piece and rational parameter can have an exact operational pole under complete positive clearance. -/
example (pieces : Pieces kind family) (ready : pieces.Ready) (pole : pieces.Obstruction) : False :=
  Pieces.Ready.noPole pieces ready pole

end

end TestPurelib.Riemann.RootContinuation.Denominator.Trace
