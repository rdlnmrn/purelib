module

import Purelib.Polynomial.Approximation.Gaussian.Residual.Origin
import Purelib.Approximation.Gaussian.Division.Prepared.Decision.Laws
import Purelib.Approximation.Gaussian.Sequence.Equivalence
import Purelib.Polynomial.Dense.Gaussian.LinearFactor
import Purelib.Data.Gaussian.Basic
import Purelib.System.IO

/-! # Retained zero, nonzero and finite-inconclusive origin decisions -/

namespace TestPurelib.Polynomial.Approximation.Gaussian.Residual.Origin

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Approximation.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)

/-- Read the complete retained decision twice, without reconstructing localization or its stable selection. -/
@[noinline] private def repeatedDecision {polynomial} {channel} {residual : Residual polynomial channel}
    {inspection : Residual.Origin.Inspection residual} (completion : Residual.Origin.Completion inspection) :
    Bool × Bool := (completion.decision.isPrepared, completion.decision.isPrepared)

/-- The exact original point program with a deliberately conservative valid movement allowance. -/
private def coarseSource (point : Canonical) : GeometricApproximation :=
  { GeometricApproximation.exact point with
    errorScale := 4
    errorScale_nonneg := by decide
    later_close := by
      intro earlier later order
      change Data.Gaussian.Norm.Basic.normSq (point - point) ≤ _
      rewrite [Data.Gaussian.Basic.sub_self, Data.Gaussian.Norm.Basic.normSq_zero]
      exact Approximation.Rational.Geometric.Basic.quarterRadius_nonneg (by decide) earlier }

/-- Retain the original exact channel and polynomial while using that same coarse original observation program. -/
private def coarseResidual (point : Canonical) : Residual (LinearFactor.linearFactor point)
    (Name.Coherent.CoherentNamed.Coherence.exact point) :=
  let original := Residual.exact point
  let source := coarseSource point
  let compared := Sequence.Equivalence.approximationEquivalentOfSamplesEq
    original.source.toApproximation source.toApproximation (fun _ => rfl)
  ⟨original.degreePositive, source, original.equivalent.trans compared.toNamed,
    original.scale, original.scale_nonnegative, original.bound⟩

/-- Execute exact zero, actual quantitative nonzero and a genuinely inconclusive coarse observation with full fallback.

The finite-inconclusive case supplies neither a successful scan nor a
nonzero floor. Its original linear residual computes complete localization
on the same retained decomposition, which prepares its unchanged channel.
-/
public def check : IO Unit := do
  let zero := Residual.exact 0
  let zeroInitial := Geometric.Preparation.inspectInitial zero.source _ zero.equivalent
  let zeroInspected := Residual.Origin.inspect zero zeroInitial
  match zeroInspected.outcome with
  | .zero _ _ occurrence _ _ _ =>
      let entry := zeroInspected.preparation.decomposition.positiveMultiplicityEntries.get occurrence.index
      unless entry.part.polynomial.eval 0 = 0 do
        throw (IO.userError "origin zero lost its exact original factor occurrence")
  | _ => throw (IO.userError "origin exact zero did not construct its complete comparison")
  let nonzero := Residual.exact 1
  let nonzeroInitial := Geometric.Preparation.inspectInitial nonzero.source _ nonzero.equivalent
  let nonzeroInspected := Residual.Origin.inspect nonzero nonzeroInitial
  match nonzeroInspected.outcome with
  | .prepared _ _ _ => pure ()
  | _ => throw (IO.userError "origin exact nonzero did not retain its actual prepared original ball")
  let coarse := coarseResidual 1
  let coarseInitial := Geometric.Preparation.inspectInitial coarse.source _ coarse.equivalent
  let coarseInspected := Residual.Origin.inspect coarse coarseInitial
  match coarseInspected.outcome with
  | .inconclusive _ _ => pure ()
  | _ => throw (IO.userError "origin coarse original observation did not preserve finite inconclusivity")
  let completed := coarseInspected.complete
  match completed with
  | .localized _ _ _ preparation _ _ selected _ decision _ =>
      unless preparation.source.sample 0 = 1 ∧
          preparation.decomposition.positiveMultiplicityEntries.length =
            coarseInspected.preparation.decomposition.positiveMultiplicityEntries.length do
        throw (IO.userError "origin fallback did not reuse its original source and decomposition")
      unless selected.approximation.sample 0 = 1 ∧ selected.rootPairs.gap > 0 do
        throw (IO.userError "origin fallback did not retain its actual selected root and positive pair budget")
      unless decision.isPrepared ∧ repeatedDecision completed = (true, true) do
        throw (IO.userError "origin repeated decision did not project its same stored nonzero result")
      let compared := selected.namedEquivalent.compare 3 7 (1/16) (by decide)
      unless 3 ≤ compared.leftIndex ∧ 7 ≤ compared.rightIndex do
        throw (IO.userError "origin retained selection comparison lost its independent original starts")
  | _ => throw (IO.userError "origin inconclusive observation did not retain complete localization")
  match completed.decision with
  | .prepared _ => pure ()
  | .excluded _ => throw (IO.userError "origin full fallback incorrectly excluded the original exact one channel")
  System.IO.println "origin decisions: original zero/nonzero certificates and finite-inconclusive full fallback passed"
  (← IO.getStdout).flush

end TestPurelib.Polynomial.Approximation.Gaussian.Residual.Origin
