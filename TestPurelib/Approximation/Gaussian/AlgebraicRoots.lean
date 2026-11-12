module

import Purelib.Approximation.Gaussian.Provenance.Algebraic.Comparison
import Purelib.System.IO
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Algebraic
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Algebraic
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Algebraic
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Algebraic.Run
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Algebraic.Execution
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Algebraic.Execution.Tick
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Algebraic.Execution.Expand
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Algebraic.Execution.Head
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Algebraic.Execution.Snapshot
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Algebraic.Execution.Dispatch
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Algebraic.Execution.Combined
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.State
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Cached
import Purelib.LinearAlgebra.Matrix.Integral.Word
meta import Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Algebraic
meta import Purelib.Approximation.Gaussian.FractionalAction.Integral.Algebraic
meta import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Algebraic
meta import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Algebraic.Execution.Dispatch
meta import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Algebraic.Execution.Combined
meta import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Step
meta import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.State
meta import Purelib.LinearAlgebra.Matrix.Multiplication
meta import Purelib.Algebra.Ring.Int
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Provenance
import Purelib.Approximation.Gaussian.Division.Prepared.Decision.Laws
import Purelib.Approximation.Gaussian.Division.Obstruction.Zero
import Purelib.Approximation.Gaussian.Division.Prepared.Equivalence
import Purelib.Riemann.RootContinuation.CoherentRoot.Polynomial
import Purelib.Riemann.RootContinuation.CoherentRoot.PointSeparation
import Purelib.Polynomial.Power.Gaussian.Squarefree
import Purelib.Tactic.OperationalEquivalence
import Purelib.Riemann.RootContinuation.CoherentRoot.CommonSource

/-!
# Nonlinear identities and original-channel acquisition from admitted roots

The cubic and mixed-generator clients consume arbitrary original certified
tracks. Their equations and inverse preparation are computed from those
intrinsic owners, with no supplied power law or denominator bound.
-/

namespace TestPurelib.Approximation.Gaussian.AlgebraicRoots

open Purelib
open Purelib.Polynomial
open Purelib.RootIsolation
open Purelib.Riemann.RootContinuation
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Provenance
open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)
open Purelib.Approximation.Gaussian.FractionalAction
open Purelib.Approximation.Gaussian.FractionalAction.Integral
open Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition
open Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Algebraic
open Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Fold.Basic (FoldPreparations)
open Purelib.LinearAlgebra.Matrix.Basic (IntegralMatrix)
open Purelib.LinearAlgebra.Matrix (matrixOfFn)
open Purelib.LinearAlgebra.Matrix.Integral
open Purelib.Riemann.Integration.LegendreModularMonodromy (fractionalDenominator)

example {channel : CoherentNamed} (original : Algebraic.Sidecar channel) :
    Preparation.Provenance.infer (some (.algebraic (original.pow 0))) =
      .rational (RationalSidecar.exact 1) :=
  Preparation.Provenance.infer_algebraic_real (original.pow 0)
    (RationalSidecar.exact 1) original.pow_zero_scalar rfl

/-- The exact imaginary unit at its original coherent channel. -/
private def imaginaryReading : RationalSidecar (CoherentNamed.Coherence.exact ⟨0, 1⟩) :=
  ⟨⟨0, 1⟩, NamedEquivalent.refl _⟩

example : Preparation.Provenance.infer
    (some (.algebraic (Algebraic.Sidecar.ofRational imaginaryReading))) =
      .provider (Preparation.Provenance.rationalProvider imaginaryReading (by decide)) :=
  Preparation.Provenance.infer_algebraic_nonreal
    (Algebraic.Sidecar.ofRational imaginaryReading) imaginaryReading rfl (by decide)

example {channel : CoherentNamed} (original : Algebraic.Sidecar channel) (missing : original.scalar? = none)
    (noRoot : original.cached.root? = none) :
    Preparation.Provenance.infer (some (.algebraic original)) =
      .unresolved (.algebraic original rfl missing noRoot) :=
  Preparation.Provenance.infer_algebraic_unresolved original missing noRoot

example {ambient : CoherentRoot.Box}
    {track : CoherentRoot.WindingOneTrack (Power.Gaussian.rootPolynomial 2 ⟨3, by decide⟩) ambient}
    (root : CoherentRoot.CertifiedName track) :
    Provenance.Power.PowerIdentity root.value 3 2 := root.power_identity

example {ambient : CoherentRoot.Box}
    {track : CoherentRoot.WindingOneTrack (Power.Gaussian.rootPolynomial 2 ⟨3, by decide⟩) ambient}
    (root : CoherentRoot.CertifiedName track) :
    NamedEquivalent
      (CoherentNamed.mul (CoherentNamed.add (CoherentNamed.Coherence.exact 1) root.value)
        (CoherentNamed.add
          (CoherentNamed.add (Name.Coherent.Power.namedPower root.value 2) (CoherentNamed.neg root.value))
          (CoherentNamed.Coherence.exact 1))).name
      (CoherentNamed.Coherence.exact 3).name := by
  ccl_equiv [root.power_identity]

example {firstAmbient secondAmbient : CoherentRoot.Box}
    {firstTrack : CoherentRoot.WindingOneTrack (Power.Gaussian.rootPolynomial 2 ⟨2, by decide⟩)
      firstAmbient}
    {secondTrack : CoherentRoot.WindingOneTrack (Power.Gaussian.rootPolynomial 3 ⟨2, by decide⟩)
      secondAmbient}
    (first : CoherentRoot.CertifiedName firstTrack) (second : CoherentRoot.CertifiedName secondTrack) :
    let sum := CoherentNamed.add first.value second.value
    NamedEquivalent
      (CoherentNamed.add
        (CoherentNamed.add (Name.Coherent.Power.namedPower sum 4)
          (CoherentNamed.mul (CoherentNamed.Coherence.exact (-10)) (Name.Coherent.Power.namedPower sum 2)))
        (CoherentNamed.Coherence.exact 1)).name
      (CoherentNamed.Coherence.exact 0).name := by
  dsimp only
  ccl_equiv [first.power_identity, second.power_identity]

/-- The original cubic coefficient table supplies its own positive squarefree admission. -/
private def cubicInput : FTA.Squarefree.Input (Power.Gaussian.rootPolynomial 2 ⟨3, by decide⟩) where
  squarefree := Power.Gaussian.Squarefree.squarefree
    (by decide +kernel : (2 : CoherentRoot.Gaussian) ≠ 0) ⟨3, by decide⟩
  degreeAtLeastTwo := by
    rewrite [Power.Gaussian.rootPolynomial_degree]
    decide +kernel

/-- A fractional request whose original denominator is the row `1 + tau`. -/
private def affineMatrix : IntegralMatrix := matrixOfFn fun row column =>
  if row.val = 0 then 1 else if column.val = 0 then 0 else 1

/-- The exact original cubic root and both actual rows of this request. -/
private def cubicRows {ambient : CoherentRoot.Box}
    {track : CoherentRoot.WindingOneTrack (Power.Gaussian.rootPolynomial 2 ⟨3, by decide⟩) ambient}
    (root : CoherentRoot.CertifiedName track) :=
  Integral.Algebraic.readRows
    (Algebraic.Sidecar.ofRoot (PolynomialRoot.Sidecar.ofIsolated root cubicInput.toPositive)) affineMatrix

/-- Retain the same original cubic root and compute its one-plus-root algebraic denominator cache. -/
private def cubicDenominator {ambient : CoherentRoot.Box}
    {track : CoherentRoot.WindingOneTrack (Power.Gaussian.rootPolynomial 2 ⟨3, by decide⟩) ambient}
    (root : CoherentRoot.CertifiedName track) :
    Algebraic.Sidecar (CoherentNamed.add (CoherentNamed.Coherence.exact 1) root.value) :=
  (Algebraic.Sidecar.ofRational (RationalSidecar.exact 1)).add
    (Algebraic.Sidecar.ofRoot (PolynomialRoot.Sidecar.ofIsolated root cubicInput.toPositive))

/-- The actual affine row keeps the displayed coefficient multiplication. -/
private def affineCubicDenominator {ambient : CoherentRoot.Box}
    {track : CoherentRoot.WindingOneTrack (Power.Gaussian.rootPolynomial 2 ⟨3, by decide⟩) ambient}
    (root : CoherentRoot.CertifiedName track) :=
  (Algebraic.Sidecar.ofRational (RationalSidecar.exact 1)).add
    ((Algebraic.Sidecar.ofRational (RationalSidecar.exact 1)).mul
      (Algebraic.Sidecar.ofRoot (PolynomialRoot.Sidecar.ofIsolated root cubicInput.toPositive)))

example {ambient : CoherentRoot.Box}
    {track : CoherentRoot.WindingOneTrack (Power.Gaussian.rootPolynomial 2 ⟨3, by decide⟩) ambient}
    (root : CoherentRoot.CertifiedName track) (index : Nat) :
    (cubicRows root).denominatorEvidence.residual.source.sample index =
      (affineCubicDenominator root).residual.source.sample index :=
  (affineCubicDenominator root).transport_sample
    (FractionalAction.Integral.Homogeneous.fractionalRow_affine affineMatrix root.value 0) index

example : (Integral.Algebraic.readRows
    (Algebraic.Sidecar.ofRational (RationalSidecar.exact (-1))) affineMatrix).decide.isPrepared =
      false := rfl

example : (match (Integral.Algebraic.readRows
    (Algebraic.Sidecar.ofRational (RationalSidecar.exact (-1))) affineMatrix).step with
  | .error _ => true
  | .ok _ => false) = true := rfl

example : (match (Integral.Algebraic.readRows
    (Algebraic.Sidecar.ofRational (RationalSidecar.exact 0)) affineMatrix).step with
  | .error _ => false
  | .ok _ => true) = true := rfl

example {ambient : CoherentRoot.Box}
    {track : CoherentRoot.WindingOneTrack (Power.Gaussian.rootPolynomial 2 ⟨3, by decide⟩) ambient}
    (root : CoherentRoot.CertifiedName track)
    (prepared : Division.Prepared
      (fractionalDenominator affineMatrix root.value))
    (computed : (cubicRows root).decide = .prepared prepared) :
    ((cubicRows root).toPreparation prepared computed).equivalent = prepared.equivalent := rfl

example {tau : CoherentNamed} (input : Algebraic.Sidecar tau) :
    (FractionalAction.Integral.Words.Step.sidecar input [] (ULift.up ())).2 = input := rfl

example {ambient : CoherentRoot.Box}
    {track : CoherentRoot.WindingOneTrack (Power.Gaussian.rootPolynomial 2 ⟨3, by decide⟩) ambient}
    (root : CoherentRoot.CertifiedName track)
    (preparations : FractionalAction.Integral.Words.Step.StepPreparations root.value [affineMatrix, affineMatrix]) :
    FractionalAction.Integral.Words.Step.Output root.value [affineMatrix, affineMatrix] preparations :=
  FractionalAction.Integral.Words.Step.sidecar
    (Algebraic.Sidecar.ofRoot (PolynomialRoot.Sidecar.ofIsolated root cubicInput.toPositive))
    [affineMatrix, affineMatrix] preparations

example {tau : CoherentNamed} {matrix : IntegralMatrix}
    {preparation : Division.Prepared.DenominatorPreparation
      (fractionalDenominator matrix tau)}
    (action : Integral.Algebraic.Action tau matrix preparation) (remaining : List IntegralMatrix) :
    (match action.startSuffix remaining with
    | .tail _ => true
    | _ => false) = true := rfl

example {tau : CoherentNamed} (input : Algebraic.Sidecar tau) (matrices : List IntegralMatrix) :
    (Fold.Algebraic.Cursor.initial input matrices).source = input ∧
    (Fold.Algebraic.Cursor.initial input matrices).original = Fold.State.initial tau matrices :=
  ⟨rfl, rfl⟩

example {tau : CoherentNamed} (input : Algebraic.Sidecar tau) (matrices : List IntegralMatrix) :
    (Fold.Algebraic.Cursor.initial input matrices).cache = Fold.Algebraic.Cache.pending := rfl

example {tau : CoherentNamed} (input : Algebraic.Sidecar tau) {matrix : IntegralMatrix}
    {rows : Integral.Algebraic.Rows input matrix}
    {preparation : Division.Prepared.DenominatorPreparation
      (fractionalDenominator matrix tau)}
    (head : Integral.Algebraic.Head rows preparation) (remaining : List IntegralMatrix) :
    (Fold.Algebraic.Cursor.ofHead input head remaining).source = input ∧
    (Fold.Algebraic.Cursor.ofHead input head remaining).original = head.action.startSuffix remaining :=
  ⟨rfl, rfl⟩

example {tau : CoherentNamed} (input : Algebraic.Sidecar tau) {matrix : IntegralMatrix}
    {rows : Integral.Algebraic.Rows input matrix}
    {preparation : Division.Prepared.DenominatorPreparation
      (fractionalDenominator matrix tau)}
    (head : Integral.Algebraic.Head rows preparation) (remaining : List IntegralMatrix) :
    (Fold.Algebraic.Cursor.ofHead input head remaining).cache =
      Fold.Algebraic.Cache.tail (child := Fold.State.initial head.action.1.val remaining) head
        head.action.2 rfl Fold.Algebraic.Cache.pending := rfl

example {tau : CoherentNamed} (input : Algebraic.Sidecar tau) {matrix : IntegralMatrix}
    (rows : Integral.Algebraic.Rows input matrix)
    (preparation : Division.Prepared.DenominatorPreparation
      (fractionalDenominator matrix tau))
    (remaining : List IntegralMatrix) :
    (Fold.Algebraic.Cursor.ofPreparation input rows preparation remaining).source = input ∧
    (Fold.Algebraic.Cursor.ofPreparation input rows preparation remaining).original =
      (rows.output preparation).startSuffix remaining ∧
    (Fold.Algebraic.Cursor.ofPreparation input rows preparation remaining).cache =
      Fold.Algebraic.Cache.preparedTail rows (rows.output preparation) rfl (rows.output preparation).2 rfl
        (child := Fold.State.initial (rows.output preparation).1.val remaining) Fold.Algebraic.Cache.pending :=
  ⟨rfl, rfl, rfl⟩

/-- Select the original affine head and attach the input's actual row cache. -/
private def affineHeadRequest {tau : CoherentNamed} (input : Algebraic.Sidecar tau) :
    Fold.Algebraic.Run.HeadRequest input affineMatrix [] :=
  Fold.Algebraic.Run.HeadRequest.create (Fold.Algebraic.Cursor.initial input [affineMatrix])
    (State.initial affineMatrix tau) rfl rfl

example {tau : CoherentNamed} {input : Algebraic.Sidecar tau} {matrix : IntegralMatrix}
    {remaining : List IntegralMatrix} (request : Fold.Algebraic.Run.HeadRequest input matrix remaining) :
    request.preflight.1.val = request ∧
    request.preflight.2.val = Step.step matrix tau request.search ∧
    request.decide.1.val = request ∧ request.decide.2.val = request.rows.step :=
  ⟨rfl, rfl, rfl, rfl⟩

example {tau : CoherentNamed} {input : Algebraic.Sidecar tau} {matrix : IntegralMatrix}
    {remaining : List IntegralMatrix} (request : Fold.Algebraic.Run.HeadRequest input matrix remaining)
    (next : State matrix tau) :
    (request.resume next).rows = request.rows ∧
    (request.resume next).search = next ∧
    (request.resume next).cursor.original = .head next :=
  ⟨rfl, rfl, rfl⟩

example {tau : CoherentNamed} {input : Algebraic.Sidecar tau} {matrix : IntegralMatrix}
    {remaining : List IntegralMatrix} {request : Fold.Algebraic.Run.HeadRequest input matrix remaining}
    (observed : Fold.Algebraic.Run.Preflight request) : observed.advance.1.val = observed :=
  observed.advance.1.property

example {tau : CoherentNamed} {input : Algebraic.Sidecar tau} {matrix : IntegralMatrix}
    {remaining : List IntegralMatrix} {request : Fold.Algebraic.Run.HeadRequest input matrix remaining}
    (observed : Fold.Algebraic.Run.Decision request) : observed.advance.1.val = observed :=
  observed.advance.1.property

namespace ExecutionWork

open Fold.Algebraic.Execution

/-- The affine head search for the exact rational input with zero affine denominator. -/
private def zeroAffineWork :
    Work (Algebraic.Sidecar.ofRational (RationalSidecar.exact (-1))) [affineMatrix] :=
  .active (Fold.Algebraic.Cursor.initial _ [affineMatrix])

/-- Empty-word identity acquisition at the exact rational zero channel. -/
private def emptyWordWork :
    Work (Algebraic.Sidecar.ofRational (RationalSidecar.exact 0)) [] :=
  .active (Fold.Algebraic.Cursor.initial _ [])

example : (match (attempt emptyWordWork 0).val.val with
  | (0, .exhausted work _ _ _) => work = emptyWordWork
  | _ => False) := rfl

example : (match (attempt emptyWordWork 1).val.val with
  | (0, .ready work cursor _ _ _) | (0, .exhausted work cursor _ _) =>
      work = dispatchEmpty emptyWordWork ∧
        cursor.source = emptyWordWork.current.source ∧
        cursor.original = Fold.Step.step _ [] emptyWordWork.current.original
  | _ => False) := ⟨rfl, rfl, rfl⟩

example {tau : CoherentNamed} (input : Algebraic.Sidecar tau) (ready : FoldPreparations tau []) :
    let cursor : Fold.Algebraic.Cursor input [] := ⟨input, rfl, .inr ready, .pending⟩
    let work := Work.active cursor
    (match (attempt work 0).val.val with
    | (0, .ready retained actual _ preparations _) =>
        retained = work ∧ actual = cursor ∧ preparations = ready
    | _ => False) := ⟨rfl, rfl, rfl⟩

example : (match (attempt zeroAffineWork 0).val.val with
  | (0, .exhausted work _ _ _) => work = zeroAffineWork
  | _ => False) := rfl

example {tau : CoherentNamed} (input : Algebraic.Sidecar tau) (matrix : IntegralMatrix)
    (remaining : List IntegralMatrix) (ready : FoldPreparations tau (matrix :: remaining)) :
    let cursor : Fold.Algebraic.Cursor input (matrix :: remaining) := ⟨input, rfl, .ready ready, .pending⟩
    let work := Work.active cursor
    (match (attempt work 0).val.val with
    | (0, .ready retained actual _ preparations _) =>
        retained = work ∧ actual = cursor ∧ preparations = ready
    | _ => False) := ⟨rfl, rfl, rfl⟩

/-- The fixed affine search advances once, then retains the exact zero obstruction. -/
private def checkZeroAffineAttempt : IO Unit := do
  match (attempt zeroAffineWork 1).val.val with
  | (0, .exhausted (.deciding ..) _ _ _) => pure ()
  | _ => throw (IO.userError "affine zero preflight did not retain deciding work")
  match (attempt zeroAffineWork 2).val.val with
  | (0, .zero (.deciding ..) _) => pure ()
  | _ => throw (IO.userError "affine zero decision did not retain its obstruction")

#eval checkZeroAffineAttempt

/-- Attempt one identity word from its original cursor with a fixed four-unit budget. -/
private def checkIdentityWordAttempt : IO Unit := do
  let input := Algebraic.Sidecar.ofRational (RationalSidecar.exact 0)
  let word := [Purelib.LinearAlgebra.Matrix.Multiplication.identity]
  let work := Work.active (Fold.Algebraic.Cursor.initial input word)
  match (attempt work 4).val.val with
  | (_, .ready _ _ _ _ _) => pure ()
  | _ => throw (IO.userError "identity word did not finish within its four-unit budget")

#eval checkIdentityWordAttempt

example {tau : CoherentNamed} {input : Algebraic.Sidecar tau} {matrix : IntegralMatrix}
    {remaining : List IntegralMatrix} (cursor : Fold.Algebraic.Cursor input (matrix :: remaining))
    (search : State matrix tau) (atHead : cursor.original = .head search) :
    let entry := startHead cursor search atHead
    entry.1.val.cursor = cursor ∧ entry.1.val.search = (cursor.actualHead search atHead).val ∧
      entry.1.val.search = search ∧
      entry.1.val.rows = Integral.Algebraic.readRows cursor.source matrix ∧
      entry.2.1.val.1.val = entry.1.val ∧
      entry.2.1.val.2.val = Step.step matrix tau (cursor.actualHead search atHead).val ∧
      entry.2.2.1.val = entry.2.1.val.advance :=
  ⟨rfl, rfl, (cursor.actualHead search atHead).property, rfl, rfl, rfl,
    (startHead cursor search atHead).2.2.1.property⟩

example {tau : CoherentNamed} {input : Algebraic.Sidecar tau} {matrix : IntegralMatrix}
    {remaining : List IntegralMatrix} (cursor : Fold.Algebraic.Cursor input (matrix :: remaining))
    (search : State matrix tau) (atHead : cursor.original = .head search) :
    cursor.headSearch? = some (startHead cursor search atHead).1.val.search := by
  change cursor.headSearch? = some (cursor.actualHead search atHead).val
  rewrite [(cursor.actualHead search atHead).property]
  unfold Fold.Algebraic.Cursor.headSearch?
  rewrite [atHead]
  rfl

example {tau : CoherentNamed} (input : Algebraic.Sidecar tau) (matrix : IntegralMatrix)
    (remaining : List IntegralMatrix) (search : State matrix tau) :
    let cursor : Fold.Algebraic.Cursor input (matrix :: remaining) := ⟨input, rfl, .head search, .pending⟩
    (chooseHead cursor).1.val = cursor ∧
      (match (chooseHead cursor).2 with
      | .inl ⟨selected, entry⟩ => selected.val = search ∧ entry.1.val.cursor = cursor ∧
          entry.2.1.val = entry.1.val.preflight ∧ entry.2.2.1.val = entry.2.1.val.advance
      | .inr _ => False) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

example {tau : CoherentNamed} (input : Algebraic.Sidecar tau) (matrix : IntegralMatrix)
    (remaining : List IntegralMatrix) (ready : FoldPreparations tau (matrix :: remaining)) :
    let cursor : Fold.Algebraic.Cursor input (matrix :: remaining) := ⟨input, rfl, .ready ready, .pending⟩
    (chooseHead cursor).1.val = cursor ∧
      (match (chooseHead cursor).2 with
      | .inl _ => False
      | .inr _ => cursor.headSearch? = none) :=
  ⟨rfl, rfl⟩

/-- Read the actual child channel and sidecar stored by a suspended suffix frame. -/
private def retainedChild? {tau : CoherentNamed} {input : Algebraic.Sidecar tau}
    {matrices : List IntegralMatrix} (work : Work input matrices) :
    Option (Σ channel : CoherentNamed, Algebraic.Sidecar channel) :=
  match work with
  | .tailHead _ _ head childSource _ _ =>
      some ⟨Fold.Algebraic.actionOutput (Fold.Algebraic.headAction head), childSource⟩
  | .tailPrepared _ _ _ action _ childSource _ _ =>
      some ⟨Fold.Algebraic.actionOutput action, childSource⟩
  | _ => none

/-- Assemble a separate sidecar record from the original complete retained fields. -/
@[noinline, nospecialize] private def assembleSidecar {tau : CoherentNamed}
    (origin : Algebraic.Origin tau) (polynomial : CoherentRoot.GaussianPolynomial)
    (residual : Polynomial.Approximation.Gaussian.Residual polynomial tau)
    (cached : Algebraic.Cached origin polynomial residual) : Algebraic.Sidecar tau :=
  ⟨origin, polynomial, residual, cached⟩

/-- Reassembling the original complete fields gives the same indexed sidecar. -/
private theorem assembleSidecar_eq {tau : CoherentNamed} (original : Algebraic.Sidecar tau) :
    assembleSidecar original.origin original.polynomial original.residual original.cached = original := by
  cases original
  rfl

/-- Retain the original sidecar and a separately assembled equal complete sidecar. -/
@[noinline, nospecialize] def separateSources {tau : CoherentNamed} (original : Algebraic.Sidecar tau) :
    (retained : { value : Algebraic.Sidecar tau // value = original }) ×
      { value : Algebraic.Sidecar tau // value = retained.val } :=
  ⟨⟨original, rfl⟩,
    ⟨assembleSidecar original.origin original.polynomial original.residual original.cached,
      assembleSidecar_eq original⟩⟩

/-- Read the child channel and actual child-sidecar field from an existing suffix cache. -/
@[noinline, nospecialize] private def retainedCacheChild? {tau : CoherentNamed} {input : Algebraic.Sidecar tau}
    {matrices : List IntegralMatrix} {original : Fold.State.Cursor tau matrices}
    (cache : Fold.Algebraic.Cache input matrices original) :
    Option (Σ channel : CoherentNamed, Algebraic.Sidecar channel) :=
  match cache with
  | .tail head childSource _ _ =>
      some ⟨Fold.Algebraic.actionOutput (Fold.Algebraic.headAction head), childSource⟩
  | .preparedTail _ action _ childSource _ _ => some ⟨Fold.Algebraic.actionOutput action, childSource⟩
  | _ => none

/-- Attach an independently assembled equal sidecar as the actual suffix-cache source.

The result retains both original and separately supplied source records along
with the source projected from the actual cache. No numerical work is started.
-/
@[noinline, nospecialize] def separateSuffixSource {tau : CoherentNamed} (input : Algebraic.Sidecar tau)
    {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    {preparation : Fold.Algebraic.HeadPreparation tau matrix}
    (rows : Integral.Algebraic.Rows input matrix)
    (action : Fold.Algebraic.PreparedAction preparation)
    (action_eq : Fold.Algebraic.RowActionIdentity rows preparation action)
    (child : Fold.State.Cursor (Fold.Algebraic.actionOutput action) remaining) :
    (Algebraic.Sidecar (Fold.Algebraic.actionOutput action) ×
      Algebraic.Sidecar (Fold.Algebraic.actionOutput action)) ×
      Option (Σ channel : CoherentNamed, Algebraic.Sidecar channel) :=
  let sources := separateSources (Fold.Algebraic.actionEvidence action)
  let cache := Fold.Algebraic.Cache.preparedTail rows action action_eq sources.2.val sources.2.property
    (child := child) Fold.Algebraic.Cache.pending
  ⟨⟨sources.1.val, sources.2.val⟩, retainedCacheChild? cache⟩

example {tau : CoherentNamed} (input : Algebraic.Sidecar tau) {matrix : IntegralMatrix}
    {remaining : List IntegralMatrix} {preparation : Fold.Algebraic.HeadPreparation tau matrix}
    (rows : Integral.Algebraic.Rows input matrix)
    (action : Fold.Algebraic.PreparedAction preparation)
    (action_eq : Fold.Algebraic.RowActionIdentity rows preparation action)
    (child : Fold.State.Cursor (Fold.Algebraic.actionOutput action) remaining) :
    let retained := separateSuffixSource input rows action action_eq child
    retained.2 = some ⟨Fold.Algebraic.actionOutput action, retained.1.2⟩ := rfl

/-- Expand a suffix with a separately supplied equal source and retain the original source pair.

The work projection reads the child sidecar from the original cache while the
two complete source records remain available for independent inspection.
-/
@[noinline, nospecialize] def separateSuffixExpansion {tau : CoherentNamed} (input : Algebraic.Sidecar tau)
    {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    {preparation : Fold.Algebraic.HeadPreparation tau matrix}
    (rows : Integral.Algebraic.Rows input matrix)
    (action : Fold.Algebraic.PreparedAction preparation)
    (action_eq : Fold.Algebraic.RowActionIdentity rows preparation action)
    (child : Fold.State.Cursor (Fold.Algebraic.actionOutput action) remaining) :
    (Algebraic.Sidecar (Fold.Algebraic.actionOutput action) ×
      Algebraic.Sidecar (Fold.Algebraic.actionOutput action)) ×
      Option (Σ channel : CoherentNamed, Algebraic.Sidecar channel) :=
  let sources := separateSources (Fold.Algebraic.actionEvidence action)
  let cache := Fold.Algebraic.Cache.preparedTail rows action action_eq sources.2.val sources.2.property
    (child := child) Fold.Algebraic.Cache.pending
  let cursor : Fold.Algebraic.Cursor input (matrix :: remaining) :=
    ⟨input, rfl, Fold.Algebraic.actionTail action child, cache⟩
  let expanded := Work.expand cursor
  ⟨⟨sources.1.val, sources.2.val⟩, retainedChild? expanded.2.val⟩

example {tau : CoherentNamed} (input : Algebraic.Sidecar tau) {matrix : IntegralMatrix}
    {remaining : List IntegralMatrix} {preparation : Fold.Algebraic.HeadPreparation tau matrix}
    (rows : Integral.Algebraic.Rows input matrix)
    (action : Fold.Algebraic.PreparedAction preparation)
    (action_eq : Fold.Algebraic.RowActionIdentity rows preparation action)
    (child : Fold.State.Cursor (Fold.Algebraic.actionOutput action) remaining) :
    let retained := separateSuffixExpansion input rows action action_eq child
    retained.2 = some ⟨Fold.Algebraic.actionOutput action, retained.1.2⟩ := rfl

example {tau : CoherentNamed} {input : Algebraic.Sidecar tau} {matrices : List IntegralMatrix}
    (cursor : Fold.Algebraic.Cursor input matrices) :
    let expanded := Work.expand cursor
    expanded.1.val = cursor ∧ expanded.2.val.current = expanded.1.val :=
  ⟨(Work.expand cursor).1.property, (Work.expand cursor).2.property⟩

example {tau : CoherentNamed} {input : Algebraic.Sidecar tau} {matrix : IntegralMatrix}
    {remaining : List IntegralMatrix} {request : Fold.Algebraic.Run.HeadRequest input matrix remaining}
    (observed : Fold.Algebraic.Run.Preflight request) :
    (Work.fromPreflight observed).1.val = observed.advance ∧
      (Work.fromPreflight observed).1.val.1.val = observed :=
  ⟨(Work.fromPreflight observed).1.property, (Work.fromPreflight observed).1.val.1.property⟩

example {tau : CoherentNamed} {input : Algebraic.Sidecar tau} {matrix : IntegralMatrix}
    {remaining : List IntegralMatrix} {request : Fold.Algebraic.Run.HeadRequest input matrix remaining}
    (observed : Fold.Algebraic.Run.Preflight request) (next : State matrix tau)
    (progress : Name.Coherent.Refinement.State.Progress observed.1.val.search next)
    (resumed : { value : Fold.Algebraic.Run.HeadRequest input matrix remaining //
      observed.2.val = .progressed next progress ∧ value = observed.1.val.resume next }) :
    let progressed : Progressed observed := ⟨.inr ⟨next, progress, resumed⟩, True.intro⟩
    (Work.deciding observed progressed).current.original = .head next ∧
      (Work.deciding observed progressed).current.source = observed.1.val.cursor.source := by
  change resumed.val.cursor.original = .head next ∧ resumed.val.cursor.source = observed.1.val.cursor.source
  rewrite [resumed.property.2]
  exact ⟨rfl, rfl⟩

example {tau : CoherentNamed} {input : Algebraic.Sidecar tau} {matrix : IntegralMatrix}
    {remaining : List IntegralMatrix} {request : Fold.Algebraic.Run.HeadRequest input matrix remaining}
    (observed : Fold.Algebraic.Run.Preflight request) (next : State matrix tau)
    (progress : Name.Coherent.Refinement.State.Progress observed.1.val.search next)
    (resumed : { value : Fold.Algebraic.Run.HeadRequest input matrix remaining //
      observed.2.val = .progressed next progress ∧ value = observed.1.val.resume next }) :
    resumed.val = observed.1.val.resume next ∧
      (observed.1.val.resume next).rows = observed.1.val.rows :=
  ⟨resumed.property.2, observed.1.val.resume_rows next⟩

example {tau : CoherentNamed} (input : Algebraic.Sidecar tau) {matrix : IntegralMatrix}
    {remaining : List IntegralMatrix} {preparation : Fold.Algebraic.HeadPreparation tau matrix}
    (rows : Integral.Algebraic.Rows input matrix)
    (action : Fold.Algebraic.PreparedAction preparation)
    (action_eq : Fold.Algebraic.RowActionIdentity rows preparation action)
    (childSource : Algebraic.Sidecar (Fold.Algebraic.actionOutput action))
    (childSource_eq : childSource = Fold.Algebraic.actionEvidence action)
    (child : Fold.Algebraic.Cursor childSource remaining) :
    let frame := Work.tailPrepared input rfl rows action action_eq childSource childSource_eq (.active child)
    let retained := frame.observe
    child.source = childSource ∧
      retainedChild? retained.1.val = some ⟨Fold.Algebraic.actionOutput action, childSource⟩ ∧
      retained.2.val.source = input ∧
      retained.2.val.original = Fold.Algebraic.actionTail action child.original :=
  ⟨child.source_eq, rfl, rfl, rfl⟩

example {tau : CoherentNamed} (input : Algebraic.Sidecar tau) {matrix : IntegralMatrix}
    {remaining : List IntegralMatrix} {rows : Integral.Algebraic.Rows input matrix}
    {preparation : Fold.Algebraic.HeadPreparation tau matrix}
    (head : Fold.Algebraic.RetainedHead rows preparation)
    (childSource : Algebraic.Sidecar (Fold.Algebraic.actionOutput (Fold.Algebraic.headAction head)))
    (childSource_eq : childSource = Fold.Algebraic.actionEvidence (Fold.Algebraic.headAction head))
    (child : Fold.Algebraic.Cursor childSource remaining)
    (tail : FoldPreparations (Fold.Step.tailInput tau matrix preparation) remaining)
    (finished : Fold.Step.TailFinished tau matrix remaining preparation
      (Eq.ndrec (motive := fun channel => Fold.State.Cursor channel remaining) child.original
        (Fold.Algebraic.headAction head).1.property) tail) :
    let selected := Fold.Step.View.tailFinished preparation
      (Eq.ndrec (motive := fun channel => Fold.State.Cursor channel remaining) child.original
        (Fold.Algebraic.headAction head).1.property) tail finished
    let result := finishHead input rfl head childSource childSource_eq child tail finished selected rfl
    result.val.source = input ∧ result.val.original =
      .combined ⟨preparation, tail, Cached.cachedInitial tau (Word.matrixProduct (matrix :: remaining))⟩ :=
  ⟨(finishHead input rfl head childSource childSource_eq child tail finished _ rfl).property.1,
    (finishHead input rfl head childSource childSource_eq child tail finished _ rfl).property.2⟩

example {tau : CoherentNamed} (input : Algebraic.Sidecar tau) {matrix : IntegralMatrix}
    {remaining : List IntegralMatrix} {preparation : Fold.Algebraic.HeadPreparation tau matrix}
    (rows : Integral.Algebraic.Rows input matrix)
    (action : Fold.Algebraic.PreparedAction preparation)
    (action_eq : Fold.Algebraic.RowActionIdentity rows preparation action)
    (childSource : Algebraic.Sidecar (Fold.Algebraic.actionOutput action))
    (childSource_eq : childSource = Fold.Algebraic.actionEvidence action)
    (child : Fold.Algebraic.Cursor childSource remaining)
    (tail : FoldPreparations (Fold.Step.tailInput tau matrix preparation) remaining)
    (finished : Fold.Step.TailFinished tau matrix remaining preparation
      (Eq.ndrec (motive := fun channel => Fold.State.Cursor channel remaining) child.original action.1.property) tail) :
    let selected := Fold.Step.View.tailFinished preparation
      (Eq.ndrec (motive := fun channel => Fold.State.Cursor channel remaining) child.original action.1.property)
      tail finished
    let result := finishPreparation input rfl rows action action_eq childSource childSource_eq
      child tail finished selected rfl
    result.val.source = input ∧ result.val.original =
      .combined ⟨preparation, tail, Cached.cachedInitial tau (Word.matrixProduct (matrix :: remaining))⟩ :=
  ⟨(finishPreparation input rfl rows action action_eq childSource childSource_eq child tail finished _ rfl).property.1,
    (finishPreparation input rfl rows action action_eq childSource childSource_eq child tail finished _ rfl).property.2⟩

example {tau : CoherentNamed} (input : Algebraic.Sidecar tau) {matrix : IntegralMatrix}
    {remaining : List IntegralMatrix} {rows : Integral.Algebraic.Rows input matrix}
    {preparation : Fold.Algebraic.HeadPreparation tau matrix}
    (head : Fold.Algebraic.RetainedHead rows preparation)
    (childSource : Algebraic.Sidecar (Fold.Algebraic.actionOutput (Fold.Algebraic.headAction head)))
    (childSource_eq : childSource = Fold.Algebraic.actionEvidence (Fold.Algebraic.headAction head))
    (child : Fold.Algebraic.Cursor childSource remaining) :
    let frame := Work.tailHead input rfl head childSource childSource_eq (.active child)
    let retained := frame.observe
    child.source = childSource ∧ retainedChild? retained.1.val =
      some ⟨Fold.Algebraic.actionOutput (Fold.Algebraic.headAction head), childSource⟩ ∧
      retained.2.val.source = input ∧ retained.2.val.original = Fold.Algebraic.originalTail head child.original :=
  ⟨child.source_eq, rfl, rfl, rfl⟩

example {tau : CoherentNamed} {input : Algebraic.Sidecar tau} {matrices : List IntegralMatrix}
    (cursor : Fold.Algebraic.Cursor input matrices) :
    let work := Work.active cursor
    (resolveHead work).1.val = work ∧ (resolveHead work).2 = ULift.up () :=
  ⟨rfl, rfl⟩

example {tau : CoherentNamed} {input : Algebraic.Sidecar tau} {matrix : IntegralMatrix}
    {remaining : List IntegralMatrix} {request : Fold.Algebraic.Run.HeadRequest input matrix remaining}
    (observed : Fold.Algebraic.Run.Preflight request) (progressed : Progressed observed) :
    let work := Work.deciding observed progressed
    (resolveHead work).1.val = work ∧
      (resolveHead work).2 = (progressedRequest progressed).decide ∧
      work.inspectHead = (progressedRequest progressed).decide :=
  ⟨rfl, rfl, rfl⟩

example {tau : CoherentNamed} {input : Algebraic.Sidecar tau} {matrix : IntegralMatrix}
    {remaining : List IntegralMatrix} {request : Fold.Algebraic.Run.HeadRequest input matrix remaining}
    (observed : Fold.Algebraic.Run.Preflight request) (progressed : Progressed observed)
    (obstruction : Integral.Algebraic.Obstruction (progressedRequest progressed).rows)
    (selected : (progressedRequest progressed).rows.step = .error obstruction) :
    let work := Work.deciding observed progressed
    let result := resolveHead work
    ∃ zero : Zero work, result.1.val = work ∧ result.2.2.val = .error obstruction ∧
      zero = .head observed progressed (progressedRequest progressed).decide ⟨obstruction, selected⟩ :=
  ⟨.head observed progressed (progressedRequest progressed).decide ⟨obstruction, selected⟩, rfl, selected, rfl⟩

end ExecutionWork

example : (match (affineHeadRequest
    (Algebraic.Sidecar.ofRational (RationalSidecar.exact (-1)))).decide.advance.2 with
  | .inr _ => true
  | .inl _ => false) = true := rfl

example : (match (affineHeadRequest
    (Algebraic.Sidecar.ofRational (RationalSidecar.exact 0))).decide.advance.2 with
  | .inr _ => false
  | .inl _ => true) = true := rfl

section

variable {tau : CoherentNamed} (input : Algebraic.Sidecar tau) {matrix : IntegralMatrix}
  {remaining : List IntegralMatrix} {rows : Integral.Algebraic.Rows input matrix}
  {preparation : Fold.Algebraic.HeadPreparation tau matrix}
  (head : Fold.Algebraic.RetainedHead rows preparation)
  (childSource : Algebraic.Sidecar (Fold.Algebraic.actionOutput (Fold.Algebraic.headAction head)))
  (childSource_eq : Fold.Algebraic.ChildSourceIdentity (Fold.Algebraic.headAction head) childSource)
  (child : Fold.State.Cursor (Fold.Algebraic.actionOutput (Fold.Algebraic.headAction head)) remaining)
  (nested : Fold.Algebraic.Cache childSource remaining child)
  (tail : FoldPreparations (Fold.Algebraic.actionOutput (Fold.Algebraic.headAction head)) remaining)
  (finished : Fold.Algebraic.SuffixCompletion (Fold.Algebraic.headAction head) child tail)
  (search : Cached.CachedSearch tau (Word.matrixProduct (matrix :: remaining)))

example :
    (Fold.Algebraic.Cursor.ofCombinedHead input head childSource childSource_eq child nested tail
      finished search).cache =
      Fold.Algebraic.Cache.combinedHead head childSource childSource_eq child nested tail finished search := rfl

example (combined : Fold.Algebraic.SearchPreparation search) :
    (Fold.Algebraic.Cursor.ofReadyHead input head childSource childSource_eq child nested tail
      finished search combined).cache =
      Fold.Algebraic.Cache.readyHead head childSource childSource_eq child nested tail finished search combined := rfl

example (payload : Execution.CombinedPayload tau matrix remaining)
    (same : Fold.State.CursorPayload.combined payload =
      Fold.Algebraic.actionCombined (Fold.Algebraic.headAction head) tail search)
    (transition : Fold.Step.CombinedTransition tau matrix remaining payload.1 payload.2.1 payload.2.2) :
    let actual := Execution.advanceCombinedHead input rfl head childSource childSource_eq
      child nested tail finished search payload same transition
    actual.val.source = input ∧ actual.val.original = transition.2.2.val :=
  (Execution.advanceCombinedHead input rfl head childSource childSource_eq
    child nested tail finished search payload same transition).property

example (payload : Execution.CombinedPayload tau matrix remaining)
    (same : Fold.State.CursorPayload.combined payload =
      Fold.Algebraic.actionCombined (Fold.Algebraic.headAction head) tail search)
    (transition : Fold.Step.CombinedTransition tau matrix remaining payload.1 payload.2.1 payload.2.2)
    (next : State transition.1.val.matrix tau)
    (progress : Name.Coherent.Refinement.State.Progress transition.1.val.search next)
    (observed : transition.2.1.val = .progressed next progress) :
    (Execution.advanceCombinedHead input rfl head childSource childSource_eq
      child nested tail finished search payload same transition).val.original =
      .combined ⟨payload.1, payload.2.1, { transition.1.val with search := next }⟩ := by
  rw [(Execution.advanceCombinedHead input rfl head childSource childSource_eq
    child nested tail finished search payload same transition).property.2, transition.2.2.property, observed]
  rfl

end

section

variable {tau : CoherentNamed} (input : Algebraic.Sidecar tau) {matrix : IntegralMatrix}
  {remaining : List IntegralMatrix} {preparation : Fold.Algebraic.HeadPreparation tau matrix}
  (rows : Integral.Algebraic.Rows input matrix)
  (action : Fold.Algebraic.PreparedAction preparation)
  (action_eq : Fold.Algebraic.RowActionIdentity rows preparation action)
  (childSource : Algebraic.Sidecar (Fold.Algebraic.actionOutput action))
  (childSource_eq : Fold.Algebraic.ChildSourceIdentity action childSource)
  (child : Fold.State.Cursor (Fold.Algebraic.actionOutput action) remaining)
  (nested : Fold.Algebraic.Cache childSource remaining child)
  (tail : FoldPreparations (Fold.Algebraic.actionOutput action) remaining)
  (finished : Fold.Algebraic.SuffixCompletion action child tail)
  (search : Cached.CachedSearch tau (Word.matrixProduct (matrix :: remaining)))

example :
    (Fold.Algebraic.Cursor.ofCombinedPreparation input rows action action_eq childSource childSource_eq
      child nested tail finished search).cache =
      Fold.Algebraic.Cache.combinedPrepared rows action action_eq childSource childSource_eq child nested tail
        finished search := rfl

example (combined : Fold.Algebraic.SearchPreparation search) :
    (Fold.Algebraic.Cursor.ofReadyPreparation input rows action action_eq childSource childSource_eq child nested tail
      finished search combined).cache =
      Fold.Algebraic.Cache.readyPrepared rows action action_eq childSource childSource_eq child nested tail
        finished search combined := rfl

example (payload : Execution.CombinedPayload tau matrix remaining)
    (same : Fold.State.CursorPayload.combined payload = Fold.Algebraic.actionCombined action tail search)
    (transition : Fold.Step.CombinedTransition tau matrix remaining payload.1 payload.2.1 payload.2.2) :
    let actual := Execution.advanceCombinedPreparation input rfl rows action action_eq
      childSource childSource_eq child nested tail finished search payload same transition
    actual.val.source = input ∧ actual.val.original = transition.2.2.val :=
  (Execution.advanceCombinedPreparation input rfl rows action action_eq
    childSource childSource_eq child nested tail finished search payload same transition).property

example (payload : Execution.CombinedPayload tau matrix remaining)
    (same : Fold.State.CursorPayload.combined payload = Fold.Algebraic.actionCombined action tail search)
    (transition : Fold.Step.CombinedTransition tau matrix remaining payload.1 payload.2.1 payload.2.2)
    (next : State transition.1.val.matrix tau)
    (progress : Name.Coherent.Refinement.State.Progress transition.1.val.search next)
    (observed : transition.2.1.val = .progressed next progress) :
    (Execution.advanceCombinedPreparation input rfl rows action action_eq
      childSource childSource_eq child nested tail finished search payload same transition).val.original =
      .combined ⟨payload.1, payload.2.1, { transition.1.val with search := next }⟩ := by
  rw [(Execution.advanceCombinedPreparation input rfl rows action action_eq
    childSource childSource_eq child nested tail finished search payload same transition).property.2,
    transition.2.2.property, observed]
  rfl

end

/-- The actual retained first output reaches a zero denominator at the next occurrence. -/
private def checkLaterZero : IO Unit := do
  match (Integral.Algebraic.readRows
      (Algebraic.Sidecar.ofRational (RationalSidecar.exact (-1)))
        Purelib.LinearAlgebra.Matrix.Multiplication.identity).step with
  | .error _ => throw (IO.userError "identity head unexpectedly has a zero denominator")
  | .ok ⟨_, head⟩ => match head.action.startSuffix [affineMatrix] with
    | .tail _ => match (Integral.Algebraic.readRows head.action.2 affineMatrix).step with
      | .error _ => pure ()
      | .ok _ => throw (IO.userError "later zero denominator was not retained")
    | _ => throw (IO.userError "prepared head did not start the original suffix cursor")

#eval checkLaterZero

/-- Recognize a zero retained inside the exact computed-head suffix frame. -/
private def isLaterHeadZero {tau : CoherentNamed} {input : Algebraic.Sidecar tau}
    {matrices : List IntegralMatrix} {work : Execution.Work input matrices}
    (zero : Execution.Zero work) : Bool :=
  match zero with
  | .tailHead _ _ _ _ _ _ (.head ..) => true
  | _ => false

/-- Run an exact identity head followed by the zero affine denominator, including resumption. -/
private def checkLaterZeroAttempt : IO Unit := do
  let input := Algebraic.Sidecar.ofRational (RationalSidecar.exact (-1))
  let rows := Integral.Algebraic.readRows input
    Purelib.LinearAlgebra.Matrix.Multiplication.identity
  match rows.step with
  | .error _ => throw (IO.userError "identity head unexpectedly has a zero denominator")
  | .ok ⟨_, head⟩ =>
      let cursor := Fold.Algebraic.Cursor.ofHead input head [affineMatrix]
      let initial := Execution.Work.active cursor
      match (Execution.attempt initial 0).val.val with
      | (0, .exhausted _ _ _ _) => pure ()
      | _ => throw (IO.userError "zero fuel did not preserve the unfinished suffix")
      match (Execution.attempt initial 1).val.val with
      | (0, .exhausted saved _ _ _) =>
          if (ExecutionWork.retainedChild? saved).isNone then
            throw (IO.userError "suffix preflight lost its computed head frame")
          match (Execution.attempt saved 1).val.val with
          | (0, .zero _ obstruction) =>
              if !isLaterHeadZero obstruction then
                throw (IO.userError "resumed zero lost the computed head frame")
          | _ => throw (IO.userError "resuming the suffix did not produce the zero")
      | _ => throw (IO.userError "one fuel did not preserve the pending suffix decision")
      match (Execution.attempt initial 2).val.val with
      | (0, .zero _ obstruction) =>
          if !isLaterHeadZero obstruction then
            throw (IO.userError "later zero lost the computed head frame")
      | _ => throw (IO.userError "two fuel units did not reach the later zero")

#eval checkLaterZeroAttempt

/-- Recognize an unattached child retained beneath a computed-head frame. -/
private def isNestedUnattached {tau : CoherentNamed} {input : Algebraic.Sidecar tau}
    {matrices : List IntegralMatrix} {work : Execution.Work input matrices}
    (reason : Execution.Unresolved work) : Bool :=
  match reason with
  | .tailHead _ _ _ _ _ _ (.active _ _) => true
  | _ => false

/-- Preserve the actual nested obstruction and unpaid fuel under a retained head. -/
private def checkNestedUnattached : IO Unit := do
  let input := Algebraic.Sidecar.ofRational (RationalSidecar.exact 0)
  let rows := Integral.Algebraic.readRows input affineMatrix
  match rows.step with
  | .error _ => throw (IO.userError "first affine head unexpectedly has a zero denominator")
  | .ok ⟨_, head⟩ =>
      let childSource := (Fold.Algebraic.headAction head).2
      let childRows := Integral.Algebraic.readRows childSource affineMatrix
      match childRows.step with
      | .error _ => throw (IO.userError "second affine head unexpectedly has a zero denominator")
      | .ok ⟨preparation, _⟩ =>
          let prepared := Fold.Algebraic.Cursor.ofPreparation childSource childRows preparation []
          let unattached : Fold.Algebraic.Cursor childSource [affineMatrix] :=
            ⟨prepared.source, prepared.source_eq, prepared.original, .pending⟩
          let work := Execution.Work.tailHead input rfl head childSource rfl (.active unattached)
          match (Execution.attempt work 1).val.val with
          | (1, .blocked _ _ _ _ reason) =>
              if !isNestedUnattached reason then
                throw (IO.userError "nested blocked result lost its original leaf reason")
          | _ => throw (IO.userError "unattached child did not retain its unpaid work")

#eval checkNestedUnattached

/-- Distinguish the retained combined and ready suffix caches. -/
private def combinedCacheKind {tau : CoherentNamed} {input : Algebraic.Sidecar tau}
    {matrices : List IntegralMatrix} {original : Fold.State.Cursor tau matrices}
    (cache : Fold.Algebraic.Cache input matrices original) : Nat :=
  match cache with
  | .combinedHead .. => 1
  | .combinedPrepared .. => 2
  | .readyHead .. => 3
  | .readyPrepared .. => 4
  | _ => 0

/-- Read the original combined search and its raw preparation from a ready cache. -/
@[noinline, nospecialize] private def readyCacheSearch? {tau : CoherentNamed} {input : Algebraic.Sidecar tau}
    {matrices : List IntegralMatrix} {original : Fold.State.Cursor tau matrices}
    (cache : Fold.Algebraic.Cache input matrices original) :
    Option (Σ search : Cached.CachedSearch tau (Word.matrixProduct matrices),
      Fold.Algebraic.SearchPreparation search) :=
  match cache with
  | .readyHead _ _ _ _ _ _ _ search combined => some ⟨search, combined⟩
  | .readyPrepared _ _ _ _ _ _ _ _ _ search combined => some ⟨search, combined⟩
  | _ => none

/-- Check the bounded transition from an attached, completed suffix. -/
private def checkFinishedSuffix {tau : CoherentNamed} {input : Algebraic.Sidecar tau}
    {matrix : IntegralMatrix} (cursor : Fold.Algebraic.Cursor input [matrix]) (computed : Bool) : IO Unit := do
  match Execution.advanceFinished cursor with
  | none => throw (IO.userError "completed attached suffix did not advance")
  | some _ => pure ()
  match (Execution.attempt (.active cursor) 1).val.val with
  | (0, .exhausted (.active next) _ _ _) =>
      let expected := if computed then 1 else 2
      if combinedCacheKind next.cache != expected then
        throw (IO.userError "combined cursor lost its retained head or suffix cache")
      match (Execution.attempt (.active next) 1).val.val with
      | (0, .ready (.active completed) _ _ _ _) =>
          if combinedCacheKind completed.cache != expected + 2 then
            throw (IO.userError "ready cursor changed its retained head kind")
          match readyCacheSearch? completed.cache with
          | some _ => pure ()
          | none => throw (IO.userError "ready cursor lost its original search or raw preparation")
      | _ => throw (IO.userError "combined preparation did not spend exactly one unit")
  | _ => throw (IO.userError "completed suffix did not spend exactly one unit")

/-- Exercise both retained head kinds using one exact rational affine input. -/
private def checkFinishedSuffixes : IO Unit := do
  let input := Algebraic.Sidecar.ofRational (RationalSidecar.exact 0)
  let rows := Integral.Algebraic.readRows input affineMatrix
  match rows.step with
  | .error _ => throw (IO.userError "affine head unexpectedly has a zero denominator")
  | .ok ⟨preparation, head⟩ =>
      let unfinished := Fold.Algebraic.Cursor.ofPreparation input rows preparation []
      match (Execution.attempt (.active unfinished) 1).val.val with
      | (0, .exhausted _ _ _ _) => pure ()
      | _ => throw (IO.userError "unfinished attached suffix did not spend one unit")
      let action := Fold.Algebraic.headAction head
      let original := Fold.State.initial (Fold.Algebraic.actionOutput action) []
      match Fold.Step.step (Fold.Algebraic.actionOutput action) [] original with
      | .inl _ => throw (IO.userError "identity suffix did not complete in one tick")
      | .inr tail =>
          let unattached : Fold.Algebraic.Cursor input [affineMatrix] :=
            ⟨input, rfl, Fold.Algebraic.originalTail head (.inr tail), .pending⟩
          match (Execution.attempt (.active unattached) 1).val.val with
          | (1, .blocked _ _ _ _ _) => pure ()
          | _ => throw (IO.userError "unattached suffix did not retain its unpaid work")
          let cursor : Fold.Algebraic.Cursor input [affineMatrix] :=
            ⟨input, rfl, Fold.Algebraic.originalTail head (.inr tail),
              .tail head action.2 rfl .pending⟩
          checkFinishedSuffix cursor true
      let supplied := rows.output preparation
      let original := Fold.State.initial (Fold.Algebraic.actionOutput supplied) []
      match Fold.Step.step (Fold.Algebraic.actionOutput supplied) [] original with
      | .inl _ => throw (IO.userError "supplied identity suffix did not complete in one tick")
      | .inr tail =>
          let cursor : Fold.Algebraic.Cursor input [affineMatrix] :=
            ⟨input, rfl, Fold.Algebraic.actionTail supplied (.inr tail),
              .preparedTail rows supplied rfl supplied.2 rfl .pending⟩
          checkFinishedSuffix cursor false

#eval checkFinishedSuffixes

/-- Compute an original cubic denominator's own point exclusion before reading its checked inverse outcome.

The internally computed gap excludes the exact-zero outcome. The successful
algebraic inverse retains its actual preparation and reciprocal child cache;
no denominator bound or successful expression attempt is a caller hypothesis.
-/
private def cubicQuotient {ambient : CoherentRoot.Box}
    {track : CoherentRoot.WindingOneTrack (Power.Gaussian.rootPolynomial 2 ⟨3, by decide⟩) ambient}
    (root : CoherentRoot.CertifiedName track) (start : Nat) :
    Σ prepared : Division.Prepared (CoherentNamed.add (CoherentNamed.Coherence.exact 1) root.value),
      Algebraic.Sidecar (prepared.quotient (CoherentNamed.Coherence.exact 1)) := by
  have polynomialValue : (Power.Gaussian.rootPolynomial 2 ⟨3, by decide⟩).eval (-1) = -3 :=
    (Power.Gaussian.rootPolynomial_eval 2 (-1) ⟨3, by decide⟩).trans (by decide +kernel)
  let exclusion := CoherentRoot.PointSeparation.ofValue root (-1) (-3) polynomialValue
    (by decide +kernel) start
  let reversed := exclusion.prepareDifference
  change Division.Prepared (CoherentNamed.add root.value (CoherentNamed.Coherence.exact 1)) at reversed
  let known : Division.Prepared (CoherentNamed.add (CoherentNamed.Coherence.exact 1) root.value) :=
    reversed.transport (by ccl_equiv)
  cases (cubicDenominator root).inverse with
  | obstructed zero => exact (Division.Obstruction.Zero.ZeroIdentity.incompatible_prepared zero known).elim
  | ready prepared _cache result _result_eq => exact ⟨prepared, result⟩

example {ambient : CoherentRoot.Box}
    {track : CoherentRoot.WindingOneTrack (Power.Gaussian.rootPolynomial 2 ⟨3, by decide⟩) ambient}
    (root : CoherentRoot.CertifiedName track) (start : Nat) :
    Algebraic.Sidecar ((cubicQuotient root start).1.quotient (CoherentNamed.Coherence.exact 1)) :=
  (cubicQuotient root start).2

/-- A prepared original cubic denominator cannot be rejected by its cached row decision.

The row uses the original certified root and the retained affine denominator;
the existing cubic preparation excludes its exact-zero obstruction. -/
private theorem cubicRows_step_prepared {ambient : CoherentRoot.Box}
    {track : CoherentRoot.WindingOneTrack (Power.Gaussian.rootPolynomial 2 ⟨3, by decide⟩) ambient}
    (root : CoherentRoot.CertifiedName track) (start : Nat) :
    ∃ (preparation : Division.Prepared.DenominatorPreparation
        (fractionalDenominator affineMatrix root.value))
      (head : Integral.Algebraic.Head (cubicRows root) preparation),
        (cubicRows root).step = .ok ⟨preparation, head⟩ := by
  have rowEquivalent : NamedEquivalent
      (fractionalDenominator affineMatrix root.value).name
      (CoherentNamed.add (CoherentNamed.Coherence.exact 1) root.value).name := by
    apply NamedEquivalent.trans (Integral.Homogeneous.fractionalRow_affine affineMatrix root.value 0)
    change NamedEquivalent
      (CoherentNamed.add (CoherentNamed.Coherence.exact 1)
        (CoherentNamed.mul (CoherentNamed.Coherence.exact 1) root.value)).name
      (CoherentNamed.add (CoherentNamed.Coherence.exact 1) root.value).name
    ccl_equiv
  let prepared := (cubicQuotient root start).1.transport rowEquivalent.symm
  cases selected : (cubicRows root).step with
  | error obstruction =>
      exact False.elim (Division.Obstruction.Zero.ZeroIdentity.incompatible_prepared obstruction.zero prepared)
  | ok result =>
      rcases result with ⟨preparation, head⟩
      exact ⟨preparation, head, rfl⟩

section ComparisonContract

open Algebraic.Sidecar (Compared)
open CoherentRoot (CommonSource)

/-- The complete original comparison before factoring its ordered root-input inspection.

All three original request bits, starting floors, fallback caches and deferred
materialization remain explicit in this independent reference procedure.
-/
private def originalComparison {first second : CoherentNamed}
    (left : Algebraic.Sidecar first) (right : Algebraic.Sidecar second)
    (firstStart secondStart : Nat := 0) (inspectInitial : Bool := true) (inspectLocal : Bool := inspectInitial)
    (inspectBound : Bool := inspectInitial) :
    Compared left right firstStart secondStart :=
  match leftFound : left.cached.root? with
  | none => Compared.fallback left right firstStart secondStart inspectBound
  | some leftRoot => match rightFound : right.cached.root? with
      | none => Compared.fallback left right firstStart secondStart inspectBound
      | some rightRoot => match leftViewFound : leftRoot.view? with
          | none => Compared.fallback left right firstStart secondStart inspectBound
          | some leftView => match rightViewFound : rightRoot.view? with
              | none => Compared.fallback left right firstStart secondStart inspectBound
              | some rightView =>
                  let first : Compared.RootInput left := ⟨⟨leftRoot, leftFound⟩, ⟨leftView, leftViewFound⟩⟩
                  let second : Compared.RootInput right := ⟨⟨rightRoot, rightFound⟩, ⟨rightView, rightViewFound⟩⟩
                  let prepared := CommonSource.prepareComparison
                    first.view.input second.view.input first.view.root second.view.root firstStart secondStart
                    inspectInitial inspectLocal
                  Compared.ofIntrinsic left right firstStart secondStart ⟨first, second, ⟨prepared, rfl⟩⟩ inspectBound


-- Compare complete retained records at arbitrary request bits and original owners.
example {first second : CoherentNamed} (left : Algebraic.Sidecar first) (right : Algebraic.Sidecar second)
    (firstStart secondStart : Nat) (inspectInitial inspectLocal inspectBound : Bool) :
    left.compare right firstStart secondStart inspectInitial inspectLocal inspectBound =
      originalComparison left right firstStart secondStart inspectInitial inspectLocal inspectBound := by
  symm
  unfold originalComparison Algebraic.Sidecar.compare
  split
  · rename_i missing
    rewrite [Compared.rootInputs_left_absent left right missing]
    rfl
  · rename_i leftRoot leftFound
    split
    · rename_i missing
      rewrite [Compared.rootInputs_right_absent left right missing]
      rfl
    · rename_i rightRoot rightFound
      split
      · rename_i missing
        rewrite [Compared.rootInputs_left_view_absent left right leftRoot leftFound missing]
        rfl
      · rename_i leftView leftViewFound
        split
        · rename_i missing
          rewrite [Compared.rootInputs_right_view_absent left right rightRoot rightFound missing]
          rfl
        · rename_i rightView rightViewFound
          rewrite [Compared.rootInputs_eq_some
            (⟨⟨leftRoot, leftFound⟩, ⟨leftView, leftViewFound⟩⟩ : Compared.RootInput left)
            (⟨⟨rightRoot, rightFound⟩, ⟨rightView, rightViewFound⟩⟩ : Compared.RootInput right)]
          rfl


end ComparisonContract

end TestPurelib.Approximation.Gaussian.AlgebraicRoots
