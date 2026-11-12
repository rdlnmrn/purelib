module
import Purelib.RootIsolation.FTA.Squarefree.Prepare
import Purelib.Approximation.Gaussian.Process.Imaginary.Separation.Root
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Provenance

import scripts.checkpoint.CoherentRootSamples
import Purelib.Riemann.RootContinuation.CoherentRoot.Accelerated
import TestPurelib.Approximation.Gaussian.Geometric
import TestPurelib.Approximation.Gaussian.Geometric.Enclosure
import TestPurelib.Approximation.Gaussian.CheckedGeometric
import TestPurelib.Approximation.Gaussian.CheckedGeometric.Compound
import TestPurelib.Approximation.Gaussian.ExpressionEnclosure
import Purelib.Approximation.Gaussian.Enclosure.Ball.Box
import Purelib.Riemann.RootContinuation.CoherentRoot.Reconditioning.Algebraic
import Purelib.System.FilePath

public import Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Acquisition
public import Purelib.Riemann.RootContinuation.CoherentRoot.Reality
import Purelib.RootIsolation.Track.Newton.Build
import Purelib.Polynomial.Elimination.Axis.Separated
import Purelib.Polynomial.Clearance.Box.Line.Bezout
import Purelib.Polynomial.Dense.Rational.Bezout.GCD
import Purelib.Polynomial.Clearance.Box.Boundary.Lines
import Purelib.Polynomial.Power.Gaussian.Squarefree
import Purelib.RootIsolation.FTA.Squarefree.Input
import Purelib.Polynomial.Power.Gaussian
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.System.IO
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Provenance.Algebraic.Comparison
import Purelib.Riemann.RootContinuation.CoherentRoot.CommonSource
import Purelib.Approximation.Gaussian.Division.Acquisition.State
import Purelib.Approximation.Gaussian.Division.Acquisition.Report
import Purelib.Approximation.Gaussian.Division.Acquisition.Dispatch

/-! # Actual local cubic winding owner in checked-expression acquisition -/

namespace TestPurelib.Approximation.Gaussian.CubicAdmission

open Purelib
open Purelib.Polynomial
open Purelib.RootIsolation
open Purelib.RootIsolation.FTA.Squarefree (Input)
open Purelib.Riemann.RootContinuation
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Approximation.Gaussian.Division.Acquisition.State (Route)
open Purelib.Approximation.Gaussian.Division.Acquisition.Report (Status)
open Purelib.Approximation.Gaussian.Division.Acquisition
open Purelib.Approximation.Gaussian.Acquisition.Expression
open Purelib.Approximation.Gaussian.Acquisition.Expression.Checked
open Purelib.Approximation.Gaussian.Provenance
open Purelib.Approximation.Gaussian.Process.Imaginary
open Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Clearance.Box

/-- The actual original coefficient table for the nonrational cubic root. -/
private def polynomial := Power.Gaussian.rootPolynomial 2 ⟨3, by decide⟩

/-- The small rational ambient box with strictly positive real coordinates and computed positive cubic gap. -/
private def ambient : Box := ⟨1, 3 / 2, -1 / 16, 1 / 16, by decide, by decide⟩

/-- The original cubic coefficient table supplies its finite squarefree and positive-degree input. -/
private def input : Input polynomial where
  squarefree := Power.Gaussian.Squarefree.squarefree (by decide) ⟨3, by decide⟩
  degreeAtLeastTwo := by
    unfold polynomial
    rewrite [Power.Gaussian.rootPolynomial_degree]
    decide

/-- The existing generic coefficient-derived axis certificate of the same original local polynomial. -/
private def elimination := Elimination.Axis.Separated.separatedAxisEliminationCertificate
  polynomial input.nonzero input.degreePositive

/-- The actual retained clear left line, from its original small coordinate-polynomial Euclidean certificate. -/
private def left := Line.Bezout.verticalOfCoprime polynomial ambient ambient.xLower
  (Dense.Rational.Bezout.certificateOfConstantGCD
    (Path.Axis.verticalPathReal polynomial ambient.xLower)
    (Path.Axis.verticalPathImag polynomial ambient.xLower) (by decide +kernel) (by decide +kernel))

/-- The actual retained clear right line, from its original small coordinate-polynomial Euclidean certificate. -/
private def right := Line.Bezout.verticalOfCoprime polynomial ambient ambient.xUpper
  (Dense.Rational.Bezout.certificateOfConstantGCD
    (Path.Axis.verticalPathReal polynomial ambient.xUpper)
    (Path.Axis.verticalPathImag polynomial ambient.xUpper) (by decide +kernel) (by decide +kernel))

/-- The actual retained clear bottom line, from its original small coordinate-polynomial Euclidean certificate. -/
private def bottom := Line.Bezout.horizontalOfCoprime polynomial ambient ambient.yLower
  (Dense.Rational.Bezout.certificateOfConstantGCD
    (Path.Axis.horizontalPathReal polynomial ambient.yLower)
    (Path.Axis.horizontalPathImag polynomial ambient.yLower) (by decide +kernel) (by decide +kernel))

/-- The actual retained clear top line, from its original small coordinate-polynomial Euclidean certificate. -/
private def top := Line.Bezout.horizontalOfCoprime polynomial ambient ambient.yUpper
  (Dense.Rational.Bezout.certificateOfConstantGCD
    (Path.Axis.horizontalPathReal polynomial ambient.yUpper)
    (Path.Axis.horizontalPathImag polynomial ambient.yUpper) (by decide +kernel) (by decide +kernel))

/-- The kernel-checked local winding-one state retaining all four original line clearances. -/
private def initial : State.WindingOne.Basic.WindingOneState polynomial ambient where
  box := ambient
  refinesAmbient := Box.refines_refl ambient
  proper := by constructor <;> decide
  clearance := Clearance.Box.Boundary.Lines.boundaryOfLines left right bottom top
  rawWindingFour := by decide +kernel
  ambientLeftClearance := left
  ambientRightClearance := right
  ambientBottomClearance := bottom
  ambientTopClearance := top

/-- The existing total original Newton track starts from the same checked local winding-one state. -/
private def track := Track.Newton.Build.ofInitial input.degreeAtLeastTwo input.squarefree elimination initial

/-- The original local root name retains that same polynomial, track and actual numerical root-state cache. -/
private def root := CoherentRoot.certifiedName track input.degreePositive

/-- The actual original local winding owner supplies an intrinsic general algebraic root admission. -/
private def sidecar := Algebraic.Sidecar.ofRoot (PolynomialRoot.Sidecar.ofIsolated root input.toPositive)

/-- The original real-root box does not certify an upper imaginary gap. -/
private theorem boxNotAbove : ¬ 0 < track.initial.box.yLower := by
  change ¬ (0 : Rational) < -1 / 16
  decide +kernel

/-- The original real-root box does not certify a lower imaginary gap. -/
private theorem boxNotBelow : ¬ track.initial.box.yUpper < 0 := by
  change ¬ (1 / 16 : Rational) < 0
  decide +kernel

example : Separation.inspectRootBox track = .crossing boxNotAbove boxNotBelow :=
  Separation.inspectRootBox_crossing track boxNotAbove boxNotBelow

/-- The real cubic's retained root view includes its original channel transport. -/
private def originalView := (CoherentRoot.CertifiedName.View.ofRoot root input.toPositive).transport
  (Equivalence.NamedEquivalent.refl _) (some ⟨rfl⟩)

/-- The retained real cubic owner projects its original root view. -/
private theorem originalViewFound :
    (PolynomialRoot.Sidecar.ofIsolated root input.toPositive).view? = some originalView := rfl

/-- Both failed endpoint checks remain attached to the original crossing view. -/
private theorem crossingInspection :
    Provenance.inspectRoot (PolynomialRoot.Sidecar.ofIsolated root input.toPositive) =
      .inr ⟨⟨originalView, originalViewFound⟩, .crossing boxNotAbove boxNotBelow⟩ := by
  change (.inr ⟨⟨originalView, originalViewFound⟩, Separation.inspectRootBox track⟩ :
    Provenance.RootInspection (PolynomialRoot.Sidecar.ofIsolated root input.toPositive)) = _
  rewrite [Separation.inspectRootBox_crossing track boxNotAbove boxNotBelow]
  rfl

example : ∃ reason, Provenance.inspectedRootProvider
    (PolynomialRoot.Sidecar.ofIsolated root input.toPositive) = .inr reason ∧
      reason.val = .inr ⟨⟨originalView, originalViewFound⟩, .crossing boxNotAbove boxNotBelow⟩ := by
  unfold Provenance.inspectedRootProvider
  split
  · rename_i view positive selected
    cases selected.symm.trans crossingInspection
  · rename_i view notAbove negative selected
    cases selected.symm.trans crossingInspection
  · rename_i missing selected
    cases selected.symm.trans crossingInspection
  · rename_i view notAbove notBelow selected
    exact ⟨_, rfl, selected.symm.trans crossingInspection⟩

/-- The input annotation keeps the exact original local root channel without performing arithmetic sidecar work. -/
private def environment : Fin 1 → Annotated := fun _ => Annotated.opaque root.value

/-- Print and flush one native original-owner construction checkpoint. -/
private def progress (message : String) : IO Unit := do
  Purelib.System.IO.println message
  (← IO.getStdout).flush

/-- Exercise the actual positive-real local cubic owner, its original power node and intrinsic checked completion. -/
public def check : IO Unit := do
  progress "local cubic: construct original checked winding-one state"
  let original := root
  let sample := original.approximation.sample 0
  let cachedBox := (original.stateAt 0).box
  unless sample = cachedBox.anchor do
    throw (IO.userError "the original numerical sample did not read its same retained root-state cache")
  let reality := original.inspectCubic 2 0
  match reality.outcome with
  | .ready region =>
      unless reality.box.xLower > 0 do
        throw (IO.userError "the original local cubic reality region is not positive")
      let _comparison := region.real
      progress "local cubic: actual original positive-real branch certificate retained"
      let admitted := Admitted.atom environment ⟨0, by decide⟩ sidecar
      match (admitted.pow 3).run with
      | .completed completed =>
          let completed := completed.materialize
          let exactReading : Option (Rational.Basic.RationalSidecar completed.channel) :=
            Algebraic.Sidecar.scalar? completed.sidecar
          if present : exactReading.isSome then
            let reading := exactReading.get present
            unless reading.value = 2 do
              throw (IO.userError "the original cubic power reading differs from its checked coefficient")
          else throw (IO.userError "the original cubic power equation was not retained as exact evidence")
          progress "local cubic: original power channel completed with exact reading two"
          Geometric.check original.geometric (Enclosure.Ball.ofBox track.initial.box)
            (fun index => Enclosure.Ball.contains_ofBox (original.sample_initial_inside index))
            completed.sidecar.residual.source
          Geometric.Enclosure.check
          let originalEnclosure : Purelib.Approximation.Gaussian.Geometric.Enclosure original.value :=
            { source := original.geometric
              equivalent := original.geometric_agrees
              ball := Enclosure.Ball.ofBox track.initial.box
              contains := fun index => Enclosure.Ball.contains_ofBox (original.sample_initial_inside index) }
          ExpressionEnclosure.check (Annotated.opaque original.value) originalEnclosure
          CheckedGeometric.check
          CheckedGeometric.checkCubic (Annotated.opaque original.value) sidecar originalEnclosure
          CheckedGeometric.Compound.checkCubic (Annotated.opaque original.value) sidecar originalEnclosure
          let conjugated := completed.conj
          let conjugateReading := Algebraic.Sidecar.scalar? conjugated.sidecar
          if present : conjugateReading.isSome then
            unless (conjugateReading.get present).value = 2 do
              throw (IO.userError "the actual conjugated cubic power lost its original exact reading")
          else throw (IO.userError "the actual conjugated cubic power lost its retained scalar evidence")
          match (Admitted.rational environment 2).run with
          | .completed constant =>
              let constant := constant.materialize
              let cancelled := completed.sub constant
              match (Outcome.completed cancelled.toResult).inverse with
              | .invalid _ => progress "local cubic: actual retained cancellation rejected its zero reciprocal"
              | _ => throw (IO.userError "the original zero cubic cancellation was not rejected by checked inversion")
          | _ => throw (IO.userError "the original rational cancellation operand did not complete")
      | _ => throw (IO.userError "the intrinsic local cubic power did not complete")
  | _ => throw (IO.userError "the original local cubic reality check has a retained finite obligation")

/-- The original expanded total syntax for the cubic factor identity, with its repeated original atom. -/
@[expose] public def expanded : Basic.Expr 1 :=
  let atom : Basic.Expr 1 := .atom ⟨0, by decide⟩
  .mul (.add (.rational 1) atom) (.add (.sub (.mul atom atom) atom) (.rational 1))

/-- Retain one original total compilation of the expanded polynomial in its supplied original environment. -/
@[expose] public def expandedCache (environment : Fin 1 → Annotated) :=
  Base.Cached.ofExpression environment expanded

/-- Supply the same intrinsic original root sidecar at the compiler's three actual retained occurrences. -/
private def expandedAdmissions : Base.Admissions (expandedCache environment).compiled.bindings :=
  (sidecar, sidecar, sidecar, PUnit.unit)

/-- Read the original base occurrence count and exact admitted coefficient from its retained construction. -/
private def admittedReduction? {arity : Nat} {environment : Fin arity → Annotated} :
    {expression : Expr arity} → {channel : CoherentNamed} → Construction environment expression channel →
      Option (Nat × Canonical)
  | _, _, .base original (.exact _ _ reduced _ _ _) _ =>
      match reduced.reading with
      | .exact value _ => some (original.compiled.bindings.length, value)
      | _ => none
  | _, _, _ => none

/-- Execute the original expanded cubic factor identity through admitted normalization and checked zero inversion. -/
public def checkExpanded : IO Unit := do
  progress "local cubic expanded: retain original total polynomial and intrinsic binding admissions"
  let original := expandedCache environment
  let first := Base.Admissions.get original.compiled.bindings expandedAdmissions ⟨0, by decide⟩
  let second := Base.Admissions.get original.compiled.bindings expandedAdmissions ⟨1, by decide⟩
  let third := Base.Admissions.get original.compiled.bindings expandedAdmissions ⟨2, by decide⟩
  let firstCache := original.supply ⟨0, by decide⟩ first
  let secondCache := firstCache.supply ⟨1, by decide⟩ second
  let supplied := secondCache.supply ⟨2, by decide⟩ third
  let admitted := Admitted.base supplied expandedAdmissions
  match admitted.run with
  | .completed completed =>
      let completed := completed.materialize
      let reduced := admittedReduction? completed.construction
      unless reduced = some (3, 3) do
        throw (IO.userError "the expanded compiler lost its original occurrences or exact admitted reduction")
      let exactReading := completed.sidecar.scalar?
      if present : exactReading.isSome then
        unless (exactReading.get present).value = 3 do
          throw (IO.userError "the original expanded cubic polynomial did not reduce to exact three")
      else throw (IO.userError "the original expanded polynomial lost its retained admitted power reduction")
      progress "local cubic expanded: actual original polynomial reduced to exact scalar three"
      match (Admitted.rational environment 3).run with
      | .completed constant =>
          let constant := constant.materialize
          let difference := completed.sub constant
          match difference.sidecar.decide with
          | .prepared _ => throw (IO.userError "the original expanded cubic difference was incorrectly nonzero")
          | .excluded _ => pure ()
          match (Outcome.completed difference.toResult).inverse with
          | .invalid first =>
              match first.denominator.1 with
              | .sub (.base original) (.base (.rational value)) =>
                  unless original = expanded ∧ value = 3 ∧ first.prefix.isEmpty do
                    throw (IO.userError "the expanded cubic zero inverse lost its original denominator syntax")
              | _ => throw (IO.userError "the original expanded cubic zero occurrence was replaced")
              progress "local cubic expanded: excluded difference and typed inverse retain original source syntax"
          | _ => throw (IO.userError "the original expanded cubic zero inverse was not rejected")
      | _ => throw (IO.userError "the original exact-three comparison operand did not complete")
  | _ => throw (IO.userError "the original expanded cubic polynomial did not complete from intrinsic admissions")

/-- Acquire a finished denominator and resume its returned cached input without advancing refinement. -/
private def checkAcquisition {arity : Nat} {environment : Fin arity → Annotated}
    {expression : Expr arity} (finished : Finished environment expression)
    (firstFailure retryFailure : String) : IO Unit := do
  let state := Refinement.State.initial finished.source.channel
  let first := finished.acquire state (CoherentNamed.Coherence.exact 1) (1 / 10) (by decide)
  unless first.1.route = Route.cached ∧ first.2.status = Status.ready do
    throw (IO.userError firstFailure)
  let retry := Dispatch.Report.resume first (CoherentNamed.Coherence.exact 2) (1 / 20) (by decide)
  unless retry.1.route = Route.cached ∧ retry.2.status = Status.ready ∧
      retry.1.next.state.nextIndex = first.1.next.state.nextIndex do
    throw (IO.userError retryFailure)

/-- Acquire the original one-plus-cubic denominator, reuse its decision, and execute its actual reciprocal cache. -/
private def checkReciprocalWith (retained : Algebraic.Sidecar root.value)
    (readSample : Bool) (covered : Option Nat := none) : IO Unit := do
  progress "local cubic reciprocal: complete original one-plus-root denominator"
  let atom := Admitted.atom environment ⟨0, by decide⟩ retained
  let one := Admitted.rational environment 1
  match (one.add atom).run with
  | .completed denominator =>
      let denominator := denominator.materialize
      let initial := denominator.sidecar.inspectInitial
      match initial.outcome with
      | .inconclusive _ =>
          throw (IO.userError "the actual original denominator head has a finite separation obligation")
      | .prepared _ _ _ => pure ()
      progress "local cubic reciprocal: actual cached original head is separated"
      checkAcquisition denominator.finish
        "the original cubic denominator was not acquired through its retained exact decision"
        "the original cubic denominator's cached decision was not reused on retry"
      progress "local cubic reciprocal: production acquisition and cached retry retained"
      progress "local cubic reciprocal: construct actual checked reciprocal cache"
      let observe {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
          (inverse : Completed environment expression) (retry : Bool) : IO Unit := do
        progress "local cubic reciprocal: checked inverse construction retained"
        if readSample then
          progress "local cubic reciprocal: read actual retained inverse sample"
          let sample := inverse.sidecar.residual.source.sample 0
          unless 0 < normSq sample do
            throw (IO.userError "the actual paid original reciprocal sample lost its proved positive denominator")
          if retry then
            let repeated := inverse.sidecar.residual.source.sample 0
            unless repeated = sample do
              throw (IO.userError "the cached original reciprocal retry changed its scalar observation")
            progress "local cubic reciprocal: actual cached nonzero inverse sample and retry read"
          else
            progress "local cubic reciprocal: actual cached nonzero inverse sample read"
      match covered with
      | none =>
          match (Outcome.completed denominator.toResult).inverse with
          | .completed inverse => observe inverse.materialize false
          | _ => throw (IO.userError "the original positive-real cubic denominator failed checked inversion")
      | some last =>
          match denominator.sidecar.inverse with
          | .ready prepared cache result computed =>
              unless cache.comparison.leftIndex ≤ last do
                throw (IO.userError "the actual reciprocal source demand exceeds its loaded dyadic prefix")
              observe (denominator.inverse prepared cache result computed) true
          | .obstructed _ =>
              throw (IO.userError "the original positive-real cubic denominator failed checked inversion")
  | _ => throw (IO.userError "the original admitted cubic denominator did not complete")

/-- Acquire the original denominator and sample its retained reciprocal on the original numerical policy. -/
public def checkReciprocal (readSample : Bool := false) : IO Unit :=
  checkReciprocalWith sidecar readSample

/-- Replay the same original reciprocal through a compared loaded dyadic numerical source.

The original root owner and channel remain retained. One loaded new state
supports comparison and demand planning; extension starts from that actual
terminal state. The final production inverse cache is checked before sample
zero and its identical retry, with unchanged acquisition requests.
-/
public def checkDyadicReciprocal (directory : System.FilePath) (savedOnly interrupt : Bool) : IO Unit := do
  let directory := Purelib.System.FilePath.join directory "dyadic-reciprocal-v1"
  let states := Purelib.System.FilePath.join directory "states"
  let columns : ClearanceCheckpoint.Control IO :=
    { savedOnly := savedOnly
      afterSave := if interrupt then
        throw (IO.userError "interruption after a compared dyadic cubic root-column atomic save")
      else pure () }
  let winding : WindingCheckpoint.Control IO := { savedOnly := savedOnly }
  CoherentRootCheckpoint.dyadicFromOriginal root input
    (Input.Elimination.ofCertificate input elimination rfl) columns winding savedOnly states 1
      fun seeded sameOriginal => do
    let numerical : Algebraic.Sidecar root.value := sameOriginal ▸ seeded.algebraic
    let planned := (Algebraic.Sidecar.ofRational (Rational.Basic.RationalSidecar.exact 1)).add numerical
    match planned.inverse with
    | .obstructed _ => throw (IO.userError "the original positive cubic denominator was unexpectedly zero")
    | .ready _ plannedCache _ _ =>
        let demand := plannedCache.comparison.leftIndex
        progress s!"dyadic cubic reciprocal: computed primitive source demand {demand}"
        let loaded ← CoherentRootCheckpoint.extendDyadicRefinements input seeded.elimination
          track.initial columns winding savedOnly states seeded.loaded (demand - seeded.last)
        let prepared := CoherentRoot.Accelerated.fromInitial input root seeded.elimination
          (seeded.last + (demand - seeded.last))
          (seeded.first_covered.trans (Nat.le_add_right _ _)) loaded
        let request := Data.Json.mkObj
          [("protocol", Data.Json.toJson "compared-local-cubic-reciprocal-dyadic-v1"),
           ("polynomial", Data.Json.toJson (polynomial.coeffs.map IntegrationCheckpoint.gaussianData)),
           ("ambient", Data.Json.toJson (RootStateCheckpoint.boxData ambient)),
           ("firstInput", Data.Json.toJson (IntegrationCheckpoint.gaussianData 1)),
           ("firstTarget", Data.Json.toJson (IntegrationCheckpoint.fractionData (1 / 10))),
           ("retryInput", Data.Json.toJson (IntegrationCheckpoint.gaussianData 2)),
           ("retryTarget", Data.Json.toJson (IntegrationCheckpoint.fractionData (1 / 20))),
           ("sampleIndex", Data.Json.toJson (0 : Nat)), ("sourceDemand", Data.Json.toJson demand),
           ("loadedLast", Data.Json.toJson prepared.last)]
        let path := Purelib.System.FilePath.join directory "request.json"
        if ← path.pathExists then
          let saved : Data.Json ← IntegrationCheckpoint.loadJson path
          unless saved == request do
            throw (IO.userError "the compared cubic reciprocal request differs from its exact retained inputs")
        else if savedOnly then
          throw (IO.userError "missing compared cubic reciprocal request; header generation forbidden")
        else IntegrationCheckpoint.saveJson path request
        progress s!"dyadic cubic reciprocal: loaded through {prepared.last}; original channel retained"
        checkReciprocalWith prepared.algebraic true (some prepared.last)

/-- A zero product retains its nonlinear child and reads exact zero through the actual cached scalar operand. -/
public def checkZeroProduct : IO Unit := do
  progress "local cubic zero: retain original zero-times-root construction"
  let atom := Admitted.atom environment ⟨0, by decide⟩ sidecar
  let zero := Admitted.rational environment 0
  match (zero.mul atom).run with
  | .completed product =>
      let product := product.materialize
      let reading := product.sidecar.scalar?
      if present : reading.isSome then
        unless (reading.get present).value = 0 do
          throw (IO.userError "the original zero product's retained scalar operand was read incorrectly")
      else throw (IO.userError "the original nonlinear product lost its exact zero scalar operand")
      let initial := product.sidecar.inspectInitial
      match initial.outcome with
      | .prepared _ _ _ => throw (IO.userError "a zero original numerical observation was wrongly separated")
      | .inconclusive _ => pure ()
      progress "local cubic zero: actual numerical inconclusivity and exact scalar zero retained"
      match (Outcome.completed product.toResult).inverse with
      | .invalid _ => progress "local cubic zero: typed original zero reciprocal rejected"
      | _ => throw (IO.userError "the original zero nonlinear product's inverse was not rejected")
      match (atom.mul zero).run with
      | .completed reversed =>
          let reversed := reversed.materialize
          match (Outcome.completed reversed.toResult).inverse with
          | .invalid _ => progress "local cubic zero: original root-times-zero reciprocal rejected"
          | _ => throw (IO.userError "the original reversed zero product's inverse was not rejected")
      | _ => throw (IO.userError "the original reversed zero product did not complete")
  | _ => throw (IO.userError "the original zero-times-cubic product did not complete")

/-- The original exact-zero residual exercises numerical inconclusivity and the unchanged localization fallback. -/
public def checkZeroFallback : IO Unit := do
  let original := Algebraic.Sidecar.ofRational (Rational.Basic.RationalSidecar.exact 0)
  let initial := original.inspectInitial
  match initial.outcome with
  | .prepared _ _ _ => throw (IO.userError "the exact zero original observation was wrongly separated")
  | .inconclusive _ => progress "local fallback: actual original zero head is inconclusive"
  match original.decideInitial initial with
  | .prepared _ => throw (IO.userError "the exact zero original channel was wrongly prepared by localization")
  | .excluded _ => progress "local fallback: original linear localization certified zero"

/-- Restore the actual reciprocal's required original root prefix and consume it in checked inverse sampling.

The original reciprocal cache computes the exact source floor before any root
sample producer runs. Checked atomic refinements restore that same prefix;
the production checked-expression inverse consumes those saved root entries.
-/
public def checkCachedReciprocal (directory : System.FilePath) (savedOnly interrupt : Bool) : IO Unit := do
  let originalDenominator := (Algebraic.Sidecar.ofRational (Rational.Basic.RationalSidecar.exact 1)).add sidecar
  match originalDenominator.inverse with
  | .obstructed _ => throw (IO.userError "the original positive cubic denominator was unexpectedly zero")
  | .ready _ originalCache _ _ =>
      let last := originalCache.comparison.leftIndex
      progress s!"local cubic saved reciprocal: actual original source floor {last}"
      let columns : ClearanceCheckpoint.Control IO :=
        { savedOnly := savedOnly
          afterSave := if interrupt then
            throw (IO.userError "interruption after original reciprocal root-column atomic save")
          else pure () }
      let winding : WindingCheckpoint.Control IO := { savedOnly := savedOnly }
      let retainedElimination := Thunk.mk fun _ => Input.Elimination.ofCertificate input elimination rfl
      let entries ← CoherentRootCheckpoint.samplePrefix root input retainedElimination (fun _ _ _ => rfl)
        columns winding directory last
      progress "local cubic saved reciprocal: complete original state prefix retained"
      let retained := sidecar.withRootSamples root entries (fun index =>
        ((Algebraic.Sidecar.ofRoot_sample _ index).trans
          (PolynomialRoot.Sidecar.ofIsolated_residual_sample root input.toPositive index)).symm)
      let atom := Admitted.atom environment ⟨0, by decide⟩ retained
      let one := Admitted.rational environment 1
      match (one.add atom).run with
      | .completed denominator =>
          let denominator := denominator.materialize
          checkAcquisition denominator.finish
            "the saved original denominator was not acquired through its retained exact decision"
            "the saved original denominator's cached decision was not reused on retry"
          progress "local cubic saved reciprocal: production acquisition and cached continuation retained"
          match (Outcome.completed denominator.toResult).inverse with
          | .completed inverse =>
              let inverse := inverse.materialize
              progress "local cubic saved reciprocal: production checked inverse consumes saved child samples"
              let sample := inverse.sidecar.residual.source.sample 0
              unless 0 < normSq sample do
                throw (IO.userError "the actual saved original reciprocal observation lost nonzero quadrance")
              let negativeReal := decide (sample.re < 0)
              let negativeImaginary := decide (sample.im < 0)
              progress s!"local cubic saved reciprocal: actual observation signs {negativeReal}, {negativeImaginary}"
              let retry := inverse.sidecar.residual.source.sample 0
              unless retry = sample do
                throw (IO.userError "the cached original reciprocal retry changed its scalar observation")
              progress "local cubic saved reciprocal: actual retained sample retry checked"
          | _ => throw (IO.userError "checked inverse lost its original positive cubic denominator")
      | _ => throw (IO.userError "the admitted saved original cubic denominator did not complete")

/-- Every actual conjugated original cubic sample stays in the reflected original spatial region. -/
private theorem conjugateInside (index : Nat) : ambient.conj.Contains (sidecar.conj.residual.source.sample index) := by
  have same : sidecar.residual.source.sample index = root.approximation.sample index :=
    (Algebraic.Sidecar.ofRoot_sample _ index).trans (PolynomialRoot.Sidecar.ofIsolated_residual_sample _ _ index)
  rewrite [Algebraic.Sidecar.conj_sample, same]
  exact (root.sample_inside index).conj

/-- Each reflected original cached state refines the same reflected source ambient box. -/
private theorem conjugateStateRefines (index : Nat) : (root.stateAt index).box.conj.Refines ambient.conj :=
  (root.stateAt index).refinesAmbient.conj

/-- Inspect the actual direct conjugation constructor with all original cache indices generalized. -/
private def conjugationCache {channel : CoherentNamed} {origin : Algebraic.Origin channel}
    {polynomial : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {residual : Approximation.Gaussian.Residual polynomial channel}
    (cached : Algebraic.Cached origin polynomial residual) : Bool :=
  match cached with
  | .conj _ => true
  | _ => false

/-- Identify actual conjugation of the original positive real cubic root with that same retained root owner.

The original conjugation cache and reflected box are retained before result
selection. The comparison computes its own original-root outcome and pays
an actual conjugated-channel request without using the separate cubic
reality witness or a supplied successful comparison.
-/
public def checkConjugateIdentification : IO Unit := do
  let conjugated := sidecar.conj
  let reflected := ambient.conj
  unless reflected.xLower = ambient.xLower ∧ reflected.xUpper = ambient.xUpper ∧
      reflected.Contains (conjugated.residual.source.sample 0) do
    throw (IO.userError "real cubic conjugation lost its original reflected region or actual child sample")
  progress "real cubic conjugation: compute original residual localization and selected occurrence"
  let identified := conjugated.identify
  match identified with
  | ⟨_, _, _, .selected child _ _ _ retained _ _⟩ =>
      unless retained.owner.polynomial.coeffs = conjugated.polynomial.coeffs do
        throw (IO.userError "real cubic identification lost its complete conjugated annihilator")
      unless conjugationCache child do
        throw (IO.userError "real cubic result selection replaced its actual original conjugation child")
  | _ => throw (IO.userError "real cubic conjugation did not retain its computed selected result")
  progress "real cubic conjugation: retained computed selection and actual original child cache"
  let compared := identified.compare sidecar 2 1
  match compared.cache with
  | .inr _ => throw (IO.userError "identified real cubic conjugation forced the complete difference classifier")
  | .inl intrinsic =>
      match intrinsic.prepared.comparison with
      | .equal _ => pure ()
      | .distinct _ => throw (IO.userError "the original real cubic root and its conjugate were separated")
  match compared.comparison with
  | .distinct _ _ => throw (IO.userError "the identified original real cubic conjugate was classified distinct")
  | .equal agreement =>
      let paid := agreement.compare 1 2 4 (by decide)
      let first := (Name.Sampling.approximation (CoherentNamed.conj root.value).name).sample paid.leftIndex
      let second := (Name.Sampling.approximation root.value.name).sample paid.rightIndex
      unless 1 ≤ paid.leftIndex ∧ 2 ≤ paid.rightIndex ∧ normSq (first - second) < 4 do
        throw (IO.userError "computed real cubic conjugacy did not pay its actual original-channel request")
  progress "real cubic conjugation: computed identified result fixes the actual original positive root"
/-- Produce and check original states zero through two while retaining the actual inverse floor five as open work.

The generic ordered prefix owner restores the same original subdivision and
four Newton-band columns. The scalar receipt binds the complete state-two
readings; a cold saved-only run rechecks that same original construction before
accepting the recorded values. Later original states are not requested here.
-/
public def checkOriginalPrefixTwo (directory : System.FilePath) (savedOnly : Bool) : IO Unit := do
  let denominator := (Algebraic.Sidecar.ofRational (Rational.Basic.RationalSidecar.exact 1)).add sidecar
  match denominator.inverse with
  | .obstructed _ => throw (IO.userError "the original positive cubic denominator was unexpectedly zero")
  | .ready _ cache _ _ =>
      let floor := cache.comparison.leftIndex
      unless floor = 5 do
        throw (IO.userError "the original reciprocal changed its computed source floor")
      progress s!"local cubic prefix two: actual original inverse floor {floor}; retain states zero through two"
      let columns : ClearanceCheckpoint.Control IO := { savedOnly := savedOnly }
      let winding : WindingCheckpoint.Control IO := { savedOnly := savedOnly }
      let retainedElimination := Thunk.mk fun _ => Input.Elimination.ofCertificate input elimination rfl
      let entries ← CoherentRootCheckpoint.samplePrefix root input retainedElimination (fun _ _ _ => rfl)
        columns winding directory (min floor 2)
      match entries.find? (fun entry => entry.index == 2) with
      | none => throw (IO.userError "the original state-two cache entry was not retained")
      | some entry =>
          let current := entry.value.get
          let observations := root.approximationSamples entries
          unless observations.sample 2 = current.box.anchor do
            throw (IO.userError "the original state-two sample did not consume its actual retained entry")
          let recorded := Data.Json.mkObj
            [("protocol", Data.Json.toJson "original-local-cubic-prefix-state-v1"),
              ("inverseFloor", Data.Json.toJson floor), ("index", Data.Json.toJson entry.index),
              ("polynomial", Data.Json.toJson (polynomial.coeffs.map IntegrationCheckpoint.gaussianData)),
              ("ambient", Data.Json.toJson (RootStateCheckpoint.boxData ambient)),
              ("box", Data.Json.toJson (RootStateCheckpoint.boxData current.box)),
              ("boundary", Data.Json.toJson (IntegrationCheckpoint.fractionData current.clearance.bound)),
              ("ambientClearances", Data.Json.toJson
                ([current.ambientLeftClearance.bound, current.ambientRightClearance.bound,
                  current.ambientBottomClearance.bound, current.ambientTopClearance.bound].map
                    IntegrationCheckpoint.fractionData)),
              ("sample", Data.Json.toJson (IntegrationCheckpoint.gaussianData current.box.anchor))]
          let path := Purelib.System.FilePath.join directory "prefix-state-2.json"
          if ← path.pathExists then
            let saved : Data.Json ← IntegrationCheckpoint.loadJson path
            unless saved == recorded do
              throw (IO.userError "the original state-two scalar receipt differs from its checked replay")
          else IntegrationCheckpoint.saveJson path recorded
          progress "local cubic prefix two: checked original state two and actual scalar sample retained"
          progress "local cubic prefix two: original inverse floor five remains open"

/-- Execute checked inversion after the original zero-to-one cached payment and certified restart.

The old complete child cache and actual paid restart remain retained. The new
numerical residual has its own computed schedule and an explicit quantitative
comparison to the unchanged original root channel. Optional sampling consumes
this paid restarted program, including a repeated original request.
-/
public def checkReconditionedReciprocal (directory : System.FilePath) (readSample : Bool) : IO Unit := do
  let columns : ClearanceCheckpoint.Control IO := { savedOnly := true }
  let winding : WindingCheckpoint.Control IO := { savedOnly := true }
  progress "local cubic restart: restore original zero-to-one payment from saved original states"
  let retainedElimination := Thunk.mk fun _ => Input.Elimination.ofCertificate input elimination rfl
  CoherentRootCheckpoint.withReconditioning ambient rfl root input retainedElimination (fun _ _ _ => rfl)
    columns winding directory 0 1 (by decide) fun restart _ => do
      unless restart.paid.index = 1 ∧ restart.root.approximation.sample 0 = restart.paid.current.box.anchor do
        throw (IO.userError "the restarted numerical view lost its actual original paid state")
      progress "local cubic restart: actual original state one, payment and restarted initial reading retained"
      let samePolynomial : polynomial = sidecar.polynomial :=
        ((Algebraic.Sidecar.ofRoot_polynomial _).trans
          (PolynomialRoot.Sidecar.ofIsolated_residual_polynomial root input.toPositive)).symm
      let restarted := Algebraic.Sidecar.withReconditioning root sidecar input restart samePolynomial
      let atom := Admitted.atom environment ⟨0, by decide⟩ restarted
      let one := Admitted.rational environment 1
      match (one.add atom).run with
      | .completed denominator =>
          let denominator := denominator.materialize
          checkAcquisition denominator.finish
            "the reconditioned original denominator lost its actual cached acquisition or retry"
            "the reconditioned original denominator lost its actual cached acquisition or retry"
          progress "local cubic restart: original-channel production acquisition and cached retry retained"
          match denominator.sidecar.inverse with
          | .obstructed _ => throw (IO.userError "the restarted original positive denominator was unexpectedly zero")
          | .ready prepared cache result computed =>
              unless cache.comparison.leftIndex = 0 do
                throw (IO.userError "the paid restarted denominator changed its computed inverse floor")
              progress s!"local cubic restart: computed actual inverse source floor {cache.comparison.leftIndex}"
              let inverse := denominator.inverse prepared cache result computed
              if readSample then
                progress "local cubic restart: execute actual checked reciprocal sample zero"
                let sample := inverse.sidecar.residual.source.sample 0
                unless 0 < normSq sample do
                  throw (IO.userError "the actual paid restarted reciprocal sample lost nonzero quadrance")
                let repeated := inverse.sidecar.residual.source.sample 0
                unless repeated = sample do
                  throw (IO.userError "the repeated paid restarted reciprocal request changed its actual observation")
                progress "local cubic restart: actual nonzero reciprocal sample and identical repeated request retained"
      | _ => throw (IO.userError "the original admitted reconditioned denominator did not complete")

end TestPurelib.Approximation.Gaussian.CubicAdmission
