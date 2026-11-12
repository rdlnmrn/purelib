module

import Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.Denominator.Trace
import Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.Interior
import Purelib.RootIsolation.Progressive.Chamber.Path.Basic
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.Progressive.Chamber.Overlap
import Purelib.Geometry.Rational.Box.Outside.Preparation

namespace TestPurelib.Riemann.RootContinuation.Denominator.Trace.Occurrences

open Purelib.RootIsolation.Progressive.Chamber.Frame (ChamberFrame)
open Purelib.RootIsolation.Progressive.Chamber.Overlap (ChamberOverlap)
open Purelib.RootIsolation.Progressive.Chamber.Path.Basic (ChamberPath)
open Purelib.Riemann.RootContinuation.CoherentRoot.Chamber
open Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.InteriorStep.Denominator
open Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.Trace.Denominator
open Purelib.Geometry.Rational (Box)

section

variable {first middle last finish : ChamberFrame}
    {firstStep : ChamberOverlap first middle} {secondStep : ChamberOverlap middle last}
    {path : ChamberPath last finish} {index : first.Index} {source : Root first index}
    {middleRoot : Root middle (firstStep.matching.forward index)}
    {lastRoot : Root last (secondStep.matching.forward (firstStep.matching.forward index))}
    {rest : Trace path (secondStep.matching.forward (firstStep.matching.forward index)) lastRoot}
    (firstPiece : InteriorStep firstStep index source middleRoot)
    (secondPiece : InteriorStep secondStep (firstStep.matching.forward index) middleRoot lastRoot)
    (tail : Trace.Interior rest) (kind : Kind)
    (firstInspection : Inspection firstPiece kind) (secondInspection : Inspection secondPiece kind)
    (firstComputed : firstInspection = inspectPiece firstPiece kind)
    (secondComputed : secondInspection = inspectPiece secondPiece kind)
    (remaining : Pieces kind tail)

/-- The exact second occurrence retains its supplied genuine original piece and complete remaining family. -/
private abbrev secondPieces :=
  Pieces.cons (Trace.cons (source := middleRoot) lastRoot rest) rfl secondPiece tail
    secondInspection secondComputed remaining

/-- The exact first occurrence retains the two actual ordered pieces and the same complete original tail. -/
private abbrev firstPieces :=
  Pieces.cons (Trace.cons (source := source) middleRoot (Trace.cons (source := middleRoot) lastRoot rest)) rfl
    firstPiece (Trace.Interior.cons (Trace.cons (source := middleRoot) lastRoot rest) rfl secondPiece tail)
    firstInspection firstComputed
    (secondPieces secondPiece tail kind secondInspection secondComputed remaining)

/-- Two unresolved original occurrences remain ordered beside every later unresolved occurrence.

All geometry, point caches, regularity and handoffs come from the two supplied
original pieces. The two failed sufficient conditions establish no pole, and
neither the first result nor either original occurrence is substituted away.
-/
example (firstInside : firstPiece.bridge.val.box.Contains kind.pole)
    (secondInside : secondPiece.bridge.val.box.Contains kind.pole)
    (firstFailed : firstInspection.result = .inconclusive firstInside)
    (secondFailed : secondInspection.result = .inconclusive secondInside) :
    (firstPieces firstPiece secondPiece tail kind firstInspection secondInspection
      firstComputed secondComputed remaining).missing =
      Sum.inl ⟨firstInside, firstFailed⟩ ::
        (Sum.inl ⟨secondInside, secondFailed⟩ :: remaining.missing.map Sum.inr).map Sum.inr := by
  unfold firstPieces secondPieces
  rewrite [Pieces.missing_cons_inconclusive firstInside firstFailed]
  rewrite [Pieces.missing_cons_inconclusive secondInside secondFailed]
  rfl

/-- An earlier successful margin preserves a later actual unresolved occurrence and the entire remaining list. -/
example (clearance : Box.OutsideSide.Prepared firstPiece.bridge.val.box kind.pole)
    (firstApart : firstInspection.result = .apart clearance)
    (secondInside : secondPiece.bridge.val.box.Contains kind.pole)
    (secondFailed : secondInspection.result = .inconclusive secondInside) :
    (firstPieces firstPiece secondPiece tail kind firstInspection secondInspection
      firstComputed secondComputed remaining).missing =
      (Sum.inl ⟨secondInside, secondFailed⟩ :: remaining.missing.map Sum.inr).map Sum.inr := by
  unfold firstPieces secondPieces
  rewrite [Pieces.missing_cons_apart clearance firstApart]
  rewrite [Pieces.missing_cons_inconclusive secondInside secondFailed]
  rfl

end

end TestPurelib.Riemann.RootContinuation.Denominator.Trace.Occurrences
