module
import Purelib.System.IO
import Purelib.Approximation.Gaussian.Geometric.Preparation
import Purelib.Approximation.Gaussian.Geometric.Coherent.Comparison
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Algebraic.Execution.Dispatch
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.LinearAlgebra.Matrix.Basic

namespace TestPurelib.Approximation.Gaussian.Geometric.Preparation

open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.FractionalAction
open Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Approximation.Gaussian.Geometric.Preparation
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.LinearAlgebra.Matrix (matrixOfFn)
open Purelib.LinearAlgebra.Matrix.Basic (IntegralMatrix)

/-- Lower-driven payment retains the actual original process refinement for every source and current state. -/
example (source : GeometricApproximation) (channel : CoherentNamed)
    (equivalent : NamedEquivalent channel.name source.toApproximation.toNamed)
    (initial : State source) (lowerSq : Fraction.Rational) (positive : 0 < lowerSq)
    (lower : ∀ index, lowerSq ≤ Norm.Basic.normSq (source.sample index)) :
    let paid := fromLower source channel equivalent initial lowerSq positive lower
    paid.state.source = (sampledChannel source).name.process.refine initial.source
      paid.target paid.selection.targetPositive :=
  (fromLower source channel equivalent initial lowerSq positive lower).refined

/-- The retained paid ball contains every later actual original sample at arbitrary indices. -/
example {source : GeometricApproximation} {channel : CoherentNamed}
    {equivalent : NamedEquivalent channel.name source.toApproximation.toNamed}
    {initial : State source} {lowerSq : Fraction.Rational}
    (paid : Paid source channel equivalent initial lowerSq) (later : Nat)
    (order : paid.selection.stage ≤ later) : paid.ball.Contains (source.sample later) :=
  paid.contains_later order

/-- Payment retains the existing preparation of exactly the original channel and cached observed ball. -/
example {source : GeometricApproximation} {channel : CoherentNamed}
    {equivalent : NamedEquivalent channel.name source.toApproximation.toNamed}
    {initial : State source} {lowerSq : Fraction.Rational}
    (paid : Paid source channel equivalent initial lowerSq) :
    paid.prepared = fromBall source channel equivalent paid.state paid.ball paid.readback paid.separated :=
  paid.prepared_eq

/-- A retained finite prefix and scan budget bound the actual original paid sample index. -/
example {source : GeometricApproximation} {channel : CoherentNamed}
    {equivalent : NamedEquivalent channel.name source.toApproximation.toNamed}
    {initial : State source} {lowerSq : Fraction.Rational}
    (paid : Paid source channel equivalent initial lowerSq) :
    (show Nat from initial.source) ≤ (show Nat from paid.state.source) ∧
      (show Nat from paid.state.source) ≤ (show Nat from initial.source) + paid.selection.fuel := by
  rewrite [paid.source_eq]
  exact ⟨paid.selection.lower, paid.selection.upper⟩

/-- Every reading of the paid original observed ball satisfies its positive whole-ball lower bound. -/
example {source : GeometricApproximation} {channel : CoherentNamed}
    {equivalent : NamedEquivalent channel.name source.toApproximation.toNamed}
    {initial : State source} {lowerSq : Fraction.Rational}
    (paid : Paid source channel equivalent initial lowerSq) (value : Basic.Canonical)
    (inside : paid.ball.Contains value) :
    (Enclosure.Residual.apartOfCenter paid.ball paid.separated).lowerSq ≤ Norm.Basic.normSq value :=
  paid.lower_bound inside

/-- Constant original samples with a deliberately coarse, nonzero observation schedule. -/
private def coarse : GeometricApproximation where
  sample := fun _ => 1
  errorScale := 4
  errorScale_nonneg := by decide +kernel
  later_close := by
    intro earlier later _
    rewrite [Basic.sub_self, Norm.Basic.normSq_zero]
    exact Purelib.Approximation.Rational.Geometric.Basic.quarterRadius_nonneg
      (by decide +kernel) earlier
  centerBound := 1
  centerBound_nonneg := by decide +kernel
  sample_bounded := fun _ => by decide +kernel

/-- The actual retained coarse original sample program has a positive lower bound at every index. -/
private theorem coarse_lower (index : Nat) : (1 : Fraction.Rational) ≤ Norm.Basic.normSq (coarse.sample index) := by
  change (1 : Fraction.Rational) ≤ Norm.Basic.normSq (1 : Basic.Canonical)
  decide +kernel

/-- Read the retained search index of a computed-head combined cache. -/
private def combinedSearchIndex? {channel : CoherentNamed} {input : Provenance.Algebraic.Sidecar channel}
    {matrices : List IntegralMatrix} {original : Fold.State.Cursor channel matrices}
    (cache : Fold.Algebraic.Cache input matrices original) : Option Nat :=
  match cache with
  | .combinedHead _ _ _ _ _ _ _ search => some search.search.nextIndex
  | _ => none

/-- Check one coarse combined-search step and its retained resumption. -/
private def checkCombinedProgress : IO Unit := do
  let channel := sampledChannel coarse
  let reading : Provenance.Rational.Basic.RationalSidecar channel :=
    ⟨1, (Geometric.Coherent.Comparison.exact_agreesWith 1 coarse (fun _ => rfl)).symm⟩
  let input := Provenance.Algebraic.Sidecar.ofRational reading
  let matrix : IntegralMatrix := matrixOfFn fun row column =>
      if row.val = 0 then 1 else if column.val = 0 then 0 else 1
  let rows := Integral.Algebraic.readRows input matrix
  match rows.step with
  | .error _ => throw (IO.userError "The coarse nonzero head was rejected")
  | .ok ⟨_, head⟩ =>
      let action := Fold.Algebraic.headAction head
      let initial := Fold.State.initial action.1.val []
      match Fold.Step.step action.1.val [] initial with
      | .inl _ => throw (IO.userError "The identity suffix did not finish in its fixed tick")
      | .inr tail =>
          let cursor : Fold.Algebraic.Cursor input [matrix] :=
            ⟨input, rfl, Fold.Algebraic.originalTail head (.inr tail),
              .tail head action.2 rfl .pending⟩
          let work := Fold.Algebraic.Execution.Work.active cursor
          match (Fold.Algebraic.Execution.attempt work 1).val.val with
          | (0, .exhausted (.active combined) _ _ _) =>
              match combined.original with
              | .combined ⟨_, _, search⟩ =>
                  unless search.search.nextIndex == 0 do
                    throw (IO.userError "The original combined search did not start at its retained index")
                  match (Fold.Algebraic.Execution.attempt (.active combined) 1).val.val with
                  | (0, .exhausted (.active advanced) _ _ _) =>
                      match advanced.original with
                      | .combined ⟨_, _, updated⟩ =>
                          unless updated.search.nextIndex == 1 && combinedSearchIndex? advanced.cache == some 1 do
                            throw (IO.userError "The combined progress did not retain its exact updated search")
                          match (Fold.Algebraic.Execution.attempt (.active advanced) 1).val.val with
                          | (0, .ready ..) | (0, .exhausted ..) => pure ()
                          | _ => throw (IO.userError "The retained combined search did not resume")
                      | _ => throw (IO.userError "The progressed combined cache was not retained")
                  | _ => throw (IO.userError "The coarse combined search did not progress in its fixed tick")
              | _ => throw (IO.userError "The completed suffix did not retain its combined search")
          | _ => throw (IO.userError "The completed suffix did not advance in its fixed tick")

/-- Exercise payment of an initially inseparable actual process ball and reuse of a nonempty original prefix. -/
public def check : IO Unit := do
  let channel := sampledChannel coarse
  let equivalent := NamedEquivalent.refl channel.name
  let initial := Refinement.State.initial channel
  let inspected := inspectInitial coarse channel equivalent
  match inspected.outcome with
  | .inconclusive _ => pure ()
  | .prepared .. => throw (IO.userError "The original coarse initial ball must remain inconclusive")
  let paid := fromLower coarse channel equivalent initial 1 (by decide +kernel) coarse_lower
  unless paid.target == 1 / 2 && paid.selection.stage == 2 && (show Nat from paid.state.source) == 2 &&
      paid.ball.center == 1 && paid.ball.radiusSq == 1 / 4 do
    throw (IO.userError "The paid actual observation changed its original target/index/ball")
  let earlier := initial.advance
  let resumed := fromLower coarse channel equivalent earlier 1 (by decide +kernel) coarse_lower
  unless earlier.nextIndex > 0 && resumed.state.nextIndex == earlier.nextIndex &&
      (show Nat from earlier.source) ≤ (show Nat from resumed.state.source) &&
      (show Nat from resumed.state.source) == resumed.selection.stage do
    throw (IO.userError "Lower-driven preparation failed to retain the actual original prefix")
  checkCombinedProgress
  let earlierIndex : Nat := earlier.source
  Purelib.System.IO.println
    s!"Original geometric lower preparation: paid stage {paid.selection.stage}; reused prefix {earlierIndex}"

end TestPurelib.Approximation.Gaussian.Geometric.Preparation
