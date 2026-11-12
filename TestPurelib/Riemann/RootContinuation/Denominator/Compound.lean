module

import Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.Expression.Trace
import Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.Power.Interior
import Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Geometric.Bounds.Evaluation
import Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Admission
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.Progressive.Chamber.Overlap
import Purelib.RootIsolation.Progressive.Chamber.Path.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Nat.Positive
import Purelib.Geometry.Gaussian.UnitCircle.Basic
import Purelib.Data.Gaussian.Norm.Nonzero
import TestPurelib.Riemann.RootReconditioning

/-!
# Compound bounds on genuine original parameter families

The original piece supplies its regularity inputs, numerical root caches and
endpoint handoffs. Each specialization retains its same original admission
and genuine used geometry. Independent times and sample indices consume the
same computed bound programme; unresolved trace occurrences remain ordered.
-/

namespace TestPurelib.Riemann.RootContinuation.Denominator.Compound

open Purelib.RootIsolation.Progressive.Chamber.Frame (ChamberFrame)
open Purelib.RootIsolation.Progressive.Chamber.Overlap (ChamberOverlap)
open Purelib.RootIsolation.Progressive.Chamber.Path.Basic (ChamberPath)
open Purelib.Riemann.RootContinuation.CoherentRoot.Chamber
open Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.InteriorStep
open Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.InteriorStep.Expression
open Purelib.Approximation.Gaussian.Acquisition.Expression
open Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Geometric
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Nat.Positive (RootDegree)
open Purelib.Approximation.Gaussian.Enclosure (Ball)

section

variable {start finish : ChamberFrame} {step : ChamberOverlap start finish} {index : start.Index}
    {source : Root start index} {target : Root finish (step.matching.forward index)}
    {piece : InteriorStep step index source target} {expression : Checked.Expr 1}
    {program : Program piece expression} (family : Program.Family program)

/-- Each actual parameter assessment keeps the exact entire original point, admission and offered geometry receipt. -/
example (time : Rational) (inside : Inside time) :
    (family.at time inside).originalInput = family.inputs time inside := by
  rw [Program.Family.at_eq_assess]
  exact family.original.assess_input _

/-- Both actual endpoint specializations retain the same whole computed programme parent. -/
example : (family.at 0 zero_inside).bounds = family.original ∧
    (family.at 1 one_inside).bounds = family.original := by
  constructor
  · rw [Program.Family.at_eq_assess]
    exact family.original.assess_bounds _
  · rw [Program.Family.at_eq_assess]
    exact family.original.assess_bounds _

/-- Every actual assessment retains the complete defining finite preparation on its same original inputs. -/
example (time : Rational) (inside : Inside time) :
    (family.at time inside).result = (family.at time inside).bounds.result.prepare
      (family.at time inside).input.admitted (family.at time inside).input.offered :=
  (family.at time inside).computed

/-- Each parameter point retains the exact original root and track cache supplied by that same genuine piece. -/
example (time : Rational) (inside : Inside time) :
    (family.at time inside).originalInput.point.originalRoot = (piece.caches time inside).original :=
  (family.at time inside).originalInput.point.originalRoot_eq

/-- Distinct parameter readings and independent sample indices consume the actual positive inspection's same ball.

The alternative is the actual unresolved bound request. No successful bound
result is supplied to select the positive branch of this statement.
-/
private theorem independent_samples (firstTime otherTime : Rational)
    (firstInside : Inside firstTime) (otherInside : Inside otherTime)
    (firstGeometry : Bounds.Inputs family.original.balls (family.inputs firstTime firstInside).admitted)
    (otherGeometry : Bounds.Inputs family.original.balls (family.inputs otherTime otherInside).admitted)
    (firstIndex secondIndex : Nat) :
    match family.original.result with
    | .prepared common =>
        common.ball.Contains
            ((common.realize (family.inputs firstTime firstInside).admitted firstGeometry).value.enclosing.source.sample
              firstIndex) ∧
          common.ball.Contains
            ((common.realize (family.inputs otherTime otherInside).admitted otherGeometry).value.enclosing.source.sample
              secondIndex)
    | .requested _ => True := by
  cases found : family.original.result with
  | prepared common =>
      exact ⟨family.contains found firstTime firstInside firstGeometry firstIndex,
        family.contains found otherTime otherInside otherGeometry secondIndex⟩
  | requested _ => exact True.intro

/-- Zero and one parameter observations use the same actual common programme at independent original stages. -/
private theorem endpoint_samples (sourceGeometry : Bounds.Inputs family.original.balls
    (family.inputs 0 zero_inside).admitted)
    (targetGeometry : Bounds.Inputs family.original.balls (family.inputs 1 one_inside).admitted)
    (sourceIndex targetIndex : Nat) :
    match family.original.result with
    | .prepared common =>
        common.ball.Contains
            ((common.realize (family.inputs 0 zero_inside).admitted sourceGeometry).value.enclosing.source.sample
              sourceIndex) ∧
          common.ball.Contains
            ((common.realize (family.inputs 1 one_inside).admitted targetGeometry).value.enclosing.source.sample
              targetIndex)
    | .requested _ => True := by
  cases found : family.original.result with
  | prepared common =>
      exact ⟨family.contains found 0 zero_inside sourceGeometry sourceIndex,
        family.contains found 1 one_inside targetGeometry targetIndex⟩
  | requested _ => exact True.intro

/-- Independent original endpoint realizations retain equal computed balls without identifying their sample programs. -/
private theorem endpoint_balls (sourceGeometry : Bounds.Inputs family.original.balls
    (family.inputs 0 zero_inside).admitted)
    (targetGeometry : Bounds.Inputs family.original.balls (family.inputs 1 one_inside).admitted) :
    match family.original.result with
    | .prepared common =>
        (common.realize (family.inputs 0 zero_inside).admitted sourceGeometry).value.enclosing.ball =
          (common.realize (family.inputs 1 one_inside).admitted targetGeometry).value.enclosing.ball
    | .requested _ => True := by
  cases found : family.original.result with
  | prepared common =>
      exact common.same_ball (family.inputs 0 zero_inside).admitted sourceGeometry
        (family.inputs 1 one_inside).admitted targetGeometry
  | requested _ => exact True.intro

/-- Both genuine endpoint handoffs retain their own original numerical source and target programmes. -/
example : NamedEquivalent (piece.caches 0 zero_inside).root.value.name source.certificate.value.name ×
    NamedEquivalent (piece.caches 1 one_inside).root.value.name target.certificate.value.name :=
  ⟨piece.leftEquivalent, piece.rightEquivalent⟩

end

section

variable {start finish : ChamberFrame} {step : ChamberOverlap start finish} {index : start.Index}
    {source : Root start index} {target : Root finish (step.matching.forward index)}
    {piece : InteriorStep step index source target}

/-- The compound original syntax retains its natural power, conjugation and ordered arithmetic children. -/
private def compound : Checked.Expr 1 :=
  .add (.mul (.conj (.pow (Checked.Expr.atom Denominator.Point.atomIndex) 3))
    (Checked.Expr.rational 2)) (Checked.Expr.rational 1)

/-- Authenticate the compound's same original root cache and exact used leaf geometry at one genuine parameter. -/
private def compoundInput (program : Program piece compound) {time : Rational} {inside : Inside time}
    (point : Denominator.Point piece time inside) : program.Input time inside :=
  let root := rootAdmitted point
  let two := Checked.Admitted.rational point.environment 2
  let one := Checked.Admitted.rational point.environment 1
  let admitted := ((root.pow 3).conj.mul two).add one
  let geometry := ((program.rootGeometry point, Bounds.Inputs.rational program.balls point.environment 2),
    Bounds.Inputs.rational program.balls point.environment 1)
  program.input point admitted (some geometry)

/-- Retain all genuine same-parameter compound inputs beside one actual original programme. -/
private def compoundFamily (program : Program piece compound) : Program.Family program :=
  program.family (fun time inside => compoundInput program (Denominator.pointAt piece time inside))

/-- Actual compound endpoint assessments retain their own complete original same-parameter source caches. -/
example (program : Program piece compound) :
    ((compoundFamily program).at 0 zero_inside).originalInput.point.originalRoot =
        (piece.caches 0 zero_inside).original ∧
      ((compoundFamily program).at 1 one_inside).originalInput.point.originalRoot =
        (piece.caches 1 one_inside).original :=
  ⟨((compoundFamily program).at 0 zero_inside).originalInput.point.originalRoot_eq,
    ((compoundFamily program).at 1 one_inside).originalInput.point.originalRoot_eq⟩

/-- Every compound family input is built from that parameter's actual original point cache. -/
example (program : Program piece compound) (time : Rational) (inside : Inside time) :
    (compoundInput program (Denominator.pointAt piece time inside)).point.originalRoot =
      (piece.caches time inside).original :=
  (compoundInput program (Denominator.pointAt piece time inside)).point.originalRoot_eq

/-- The checked reciprocal family keeps the exact original point and its unchanged original geometric source. -/
example (program : Program piece (.inverse (Checked.Expr.atom Denominator.Point.atomIndex)))
    (time : Rational) (inside : Inside time) :
    (program.encloseRoot ((rootInverseFamily program).inputs time inside).point).source =
      ((rootInverseFamily program).inputs time inside).point.root.geometric := by
  exact program.encloseRoot_source _

end

section

open Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.Power
open Purelib.RootIsolation.Progressive.Power
open Purelib.Geometry.Gaussian.UnitCircle.Basic (UnitVertex)
open Purelib.Data.Gaussian.Norm.Nonzero (nonzero_of_normSq_eq_one)

local notation "degree" => (⟨3, by decide⟩ : RootDegree)
local notation "firstVertex" => TestPurelib.Riemann.RootReconditioning.sourceVertex degree (by decide)
local notation "lastVertex" => TestPurelib.Riemann.RootReconditioning.targetVertex degree (by decide)
local notation "small" => TestPurelib.Riemann.RootReconditioning.smallMove degree (by decide)
local notation "initialFrame" => Interior.Source (UnitVertex.unit firstVertex) degree (by decide)

variable {index : (initialFrame).Index} {source : Root initialFrame index}
    (moved : Root (Unit.Move.Frame.unitTransportedFrame (firstVertex).unit (lastVertex).unit degree (by decide) small)
      (Interior.movedIndex (firstVertex).unit (lastVertex).unit degree (by decide) small index))
    (selected : Root (Frame.Basic.chamberFrame (nonzero_of_normSq_eq_one (lastVertex).unit) degree (by decide))
      (Interior.selectedIndex (firstVertex).unit (lastVertex).unit degree (by decide) small index))
    (robust : Root (Unit.Frame.robustChamberFrame (nonzero_of_normSq_eq_one (lastVertex).unit)
      (lastVertex).unit degree (by decide)) ((Interior.Robust (lastVertex).unit degree (by decide)).matching.forward
        (Interior.selectedIndex (firstVertex).unit (lastVertex).unit degree (by decide) small index)))
    (bridges : Interior.Bridges (firstVertex).unit (lastVertex).unit degree (by decide) small index)
    (displayed : Canonical → Fin 2 → Ball)

local notation "actualTrace" => Trace.cons (source := source) moved
  (Trace.cons selected (Trace.cons robust (Trace.nil robust)))

/-- Both original cubic-move endpoints retain their actual same-parameter caches through the full compound construction.

The literal source and target are the existing consecutive cubic circuit
vertices. The original trace and selected bridge receipts supply their actual
roots; the genuine three-piece assembly provides each parameter's regularity,
original owner and handoffs without supplying a successful bound result.
-/
example :
    let actual := Interior.ofTrace (firstVertex).unit (lastVertex).unit degree (by decide) small actualTrace bridges
    let program := inspect actual.first compound displayed
    let family := compoundFamily program
    (family.at 0 zero_inside).originalInput.point.originalRoot = (actual.first.caches 0 zero_inside).original ∧
      (family.at 1 one_inside).originalInput.point.originalRoot = (actual.first.caches 1 one_inside).original := by
  dsimp only
  constructor
  · exact (_ : Denominator.Point _ _ _).originalRoot_eq
  · exact (_ : Denominator.Point _ _ _).originalRoot_eq

end

section

open Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.Trace.Expression (Pieces)

variable {first middle last finish : ChamberFrame}
    {firstStep : ChamberOverlap first middle} {secondStep : ChamberOverlap middle last}
    {path : ChamberPath last finish} {index : first.Index} {source : Root first index}
    {middleRoot : Root middle (firstStep.matching.forward index)}
    {lastRoot : Root last (secondStep.matching.forward (firstStep.matching.forward index))}
    {rest : Trace path (secondStep.matching.forward (firstStep.matching.forward index)) lastRoot}
    (firstPiece : InteriorStep firstStep index source middleRoot)
    (secondPiece : InteriorStep secondStep (firstStep.matching.forward index) middleRoot lastRoot)
    (tail : Trace.Interior rest) (expression : Checked.Expr 1) (displayed : Canonical → Fin 2 → Ball)
    (firstProgram : Program firstPiece expression) (secondProgram : Program secondPiece expression)
    (firstComputed : firstProgram = inspect firstPiece expression displayed)
    (secondComputed : secondProgram = inspect secondPiece expression displayed)
    (remaining : Pieces expression displayed tail)

/-- The exact later occurrence retains its actual programme and complete original remaining trace. -/
private abbrev secondPrograms :=
  Pieces.cons (Trace.cons (source := middleRoot) lastRoot rest) rfl secondPiece tail
    secondProgram secondComputed remaining

/-- The complete original first two occurrences keep their ordered programmes and unchanged actual tail. -/
private abbrev firstPrograms :=
  Pieces.cons (Trace.cons (source := source) middleRoot (Trace.cons (source := middleRoot) lastRoot rest)) rfl
    firstPiece (Trace.Interior.cons (Trace.cons (source := middleRoot) lastRoot rest) rfl secondPiece tail)
    firstProgram firstComputed
    (secondPrograms secondPiece tail expression displayed secondProgram secondComputed remaining)

/-- Two actual insufficient compound bounds retain both original trace occurrences and every unresolved tail case.

Each request carries its actual computed programme equality and violated
sufficient bound. Neither finite request asserts a global pole or divergence.
-/
example (firstRequest : Bounds.Request firstProgram.balls expression)
    (secondRequest : Bounds.Request secondProgram.balls expression)
    (firstRequested : firstProgram.result = .requested firstRequest)
    (secondRequested : secondProgram.result = .requested secondRequest) :
    (firstPrograms firstPiece secondPiece tail expression displayed firstProgram secondProgram
      firstComputed secondComputed remaining).missing =
      Sum.inl ⟨firstRequest, firstRequested⟩ ::
        (Sum.inl ⟨secondRequest, secondRequested⟩ :: remaining.missing.map Sum.inr).map Sum.inr := by
  unfold firstPrograms secondPrograms
  rewrite [Pieces.missing_cons_requested firstRequest firstRequested]
  rewrite [Pieces.missing_cons_requested secondRequest secondRequested]
  rfl

/-- A positive original prefix retains the later actual domain request and every unresolved original tail occurrence. -/
example (common : Bounds.Common firstProgram.balls expression)
    (firstPrepared : firstProgram.result = .prepared common)
    (secondRequest : Bounds.Request secondProgram.balls expression)
    (secondRequested : secondProgram.result = .requested secondRequest) :
    (firstPrograms firstPiece secondPiece tail expression displayed firstProgram secondProgram
      firstComputed secondComputed remaining).missing =
      (Sum.inl ⟨secondRequest, secondRequested⟩ :: remaining.missing.map Sum.inr).map Sum.inr := by
  unfold firstPrograms secondPrograms
  rewrite [Pieces.missing_cons_prepared common firstPrepared]
  rewrite [Pieces.missing_cons_requested secondRequest secondRequested]
  rfl

end

end TestPurelib.Riemann.RootContinuation.Denominator.Compound
