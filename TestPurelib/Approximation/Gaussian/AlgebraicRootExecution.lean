module

public import Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Acquisition
public import Purelib.RootIsolation.Multiplicity.CCL.Polynomial.Admission
import Purelib.RootIsolation.Multiplicity.Side.CCL.Admission
import Purelib.RootIsolation.Multiplicity.Observation.CCL.Admission
import Purelib.RootIsolation.Multiplicity.Side.Index
import Purelib.Polynomial.Power.Gaussian
import Purelib.Polynomial.Power.Gaussian.Squarefree
import scripts.checkpoint.InitialExtraction
import scripts.checkpoint.Multiplicity
import Purelib.RootIsolation.FTA.Positive.Build
import Purelib.Polynomial.Dense.Gaussian.Power
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.RootContinuation.CoherentRoot.Reality
import Purelib.System.IO
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Actual original algebraic root execution and branch selection

Selections inspect the actual retained root-state boxes at a stated finite
stage. A success retains its original result, bounded dependent root index,
admission, numerical cache and checked branch region. Failure retains the
attempted original candidates and finite stopping stage.
-/

namespace TestPurelib.Approximation.Gaussian.AlgebraicRootExecution

open Purelib.RootIsolation.Multiplicity
open Purelib.RootIsolation.Multiplicity.CCL.Polynomial.Index.NonzeroResult (RootIndex)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity

open Purelib
open Purelib.RootIsolation
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Approximation.Gaussian.Acquisition.Expression.Checked
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Provenance
open Purelib.Geometry.Rational (Box)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic (Canonical)

/-- Read the same actual cached root state from its original indexed observation admission. -/
private def observationBox {source opposite : CoefficientPolynomial}
    {input : Basis.Coprime.Side.PositiveSideInput source opposite}
    {context : Basis.Context.Basic.PositiveContext input.entries}
    {observation : Basis.Coprime.Side.PositiveSideInput.FactorObservation input context}
    {data : Multiplicity.Observation.CCL.Basic.ObservationCCL observation}
    {index : Multiplicity.Observation.Index.ObservationIndex observation}
    (admission : Multiplicity.Observation.CCL.Admission observation data index) (stage : Nat) : Option Box := by
  cases admission.evidence with
  | exact => exact none
  | higher _ _ _ _ realization _ => exact some (realization.root.stateAt stage).box

/-- Read the actual same cached higher-site root state from its original side admission. -/
private def sideBox {source opposite : CoefficientPolynomial} :
    (side : Multiplicity.Side.Basic.SideResult source opposite) →
    (data : Multiplicity.Side.CCL.Basic.SideCCL side) → (index : Multiplicity.Side.Index.SideIndex side) →
    Multiplicity.Side.CCL.Admission side data index → Nat → Option Box
  | .constant _ _ _, _, index, _, _ => nomatch index
  | .positive _ _, _, _, admission, stage => observationBox admission stage

/-- Read the actual original polynomial admission's same cached root box at the finite requested stage. -/
private def rootBox {polynomial : CoefficientPolynomial}
    {result : CCL.Polynomial.Basic.NonzeroResult polynomial}
    {index : RootIndex result}
    (admission : CCL.Polynomial.Admission result index) (stage : Nat) : Option Box :=
  sideBox result.rfap.numeratorSites result.numeratorCCL index admission.site stage

set_option genInjectivity false in
/-- One original indexed admission and its once read retained region at the finite requested stage. -/
private structure Candidate {polynomial : CoefficientPolynomial}
    (result : CCL.Polynomial.Basic.NonzeroResult polynomial)
    (index : RootIndex result) (stage : Nat) where
  /-- The actual original indexed admission, including original source multiplicity and numerical cache. -/
  admission : CCL.Polynomial.Admission result index
  /-- The admission was constructed at this same original source result and dependent index. -/
  admission_eq : admission = CCL.Polynomial.Admission.ofResult result index
  /-- The actual stored original cached box, absent only for an exact terminal. -/
  box : Option Box
  /-- The region was read from that same retained original cached root state. -/
  box_eq : box = rootBox admission stage

constructive_injectivity Candidate

/-- Retain all actual original admissions and once read cached regions at a stated finite stage. -/
private def candidates {polynomial : CoefficientPolynomial}
    (result : CCL.Polynomial.Basic.NonzeroResult polynomial) (stage : Nat) :
    List ((index : RootIndex result) × Candidate result index stage) :=
  (CCL.Polynomial.Index.NonzeroResult.rootIndices result).map fun index =>
    let admission := CCL.Polynomial.Admission.ofResult result index
    let box := rootBox admission stage
    ⟨index, admission, rfl, box, rfl⟩

/-- The displayed finite branch region, referring to actual original rational endpoints. -/
private def positiveRegion (lower : Rational) (box : Box) : Prop :=
  lower < box.xLower ∧ box.yLower < 0 ∧ 0 < box.yUpper

/-- Decide the stated region on its exact retained rational endpoints. -/
private instance positiveRegionDecidable (lower : Rational) (box : Box) : Decidable (positiveRegion lower box) :=
  inferInstanceAs (Decidable (lower < box.xLower ∧ box.yLower < 0 ∧ 0 < box.yUpper))

set_option genInjectivity false in
/-- A checked branch selection at an original dependent source index and finite cache stage. -/
private structure Selected {polynomial : CoefficientPolynomial}
    (result : CCL.Polynomial.Basic.NonzeroResult polynomial) (stage : Nat) (lower : Rational) where
  /-- The same original finite dependent root-site index. -/
  index : RootIndex result
  /-- The original cached admission and once observed region at that index. -/
  candidate : Candidate result index stage
  /-- The actual higher root's retained finite region. -/
  box : Box
  /-- This is the region stored at the same original admission and stage. -/
  box_eq : candidate.box = some box
  /-- This same region meets the checked branch condition. -/
  branch : positiveRegion lower box

constructive_injectivity Selected

/-- The exact retained finite candidate spine of one original source and cache stage. -/
private abbrev CandidateList {polynomial : CoefficientPolynomial}
    (result : CCL.Polynomial.Basic.NonzeroResult polynomial) (stage : Nat) :=
  List ((index : RootIndex result) × Candidate result index stage)

set_option genInjectivity false in
/-- A typed current-stage reason that this exact original candidate has no matching branch-region certificate. -/
private inductive Miss {polynomial : CoefficientPolynomial}
    {result : CCL.Polynomial.Basic.NonzeroResult polynomial} {stage : Nat}
    (lower : Rational) (candidate : (index : RootIndex result) ×
      Candidate result index stage) where
  /-- The same original candidate has an exact terminal rather than a higher-state region. -/
  | exact (absent : candidate.2.box = none)
  /-- The actual retained region fails the stated current-stage branch condition. -/
  | outside (box : Box) (region : candidate.2.box = some box) (failed : ¬ positiveRegion lower box)

constructive_injectivity Miss

set_option genInjectivity false in
/-- Every original attempted candidate's retained current-stage missing-region or failed-region explanation. -/
private inductive Misses {polynomial : CoefficientPolynomial}
    {result : CCL.Polynomial.Basic.NonzeroResult polynomial} {stage : Nat}
    (lower : Rational) : CandidateList result stage → Type 1 where
  /-- The empty original candidate spine has no remaining cases. -/
  | nil : Misses lower []
  /-- Retain the exact first candidate's stopping reason and every remaining original candidate explanation. -/
  | cons {first remaining} (miss : Miss lower first) (later : Misses lower remaining) :
      Misses lower (first :: remaining)

constructive_injectivity Misses

set_option genInjectivity false in
/-- A checked actual-region selection or all retained current-stage unresolved branch obligations. -/
private inductive Selection {polynomial : CoefficientPolynomial}
    {result : CCL.Polynomial.Basic.NonzeroResult polynomial} {stage : Nat}
    (lower : Rational) (original : CandidateList result stage) : Type 1 where
  /-- Retain the actual first matching original candidate, preceding explanations and unchanged remaining spine. -/
  | found (selected : Selected result stage lower) (before : CandidateList result stage)
      (misses : Misses lower before) (remaining : CandidateList result stage)
      (original_eq : original = before ++ (⟨selected.index, selected.candidate⟩ :: remaining))
  /-- Retain every original attempted case and its explanation at this finite stopping stage. -/
  | inconclusive (misses : Misses lower original)

constructive_injectivity Selection

/-- Retain a failed original candidate before the same remaining selection, without rebuilding admissions. -/
private def Selection.prepend {polynomial : CoefficientPolynomial}
    {result : CCL.Polynomial.Basic.NonzeroResult polynomial} {stage : Nat} {lower : Rational}
    {first : (index : RootIndex result) × Candidate result index stage}
    {remaining : CandidateList result stage} (miss : Miss lower first) : Selection lower remaining →
      Selection lower (first :: remaining)
  | .inconclusive misses => .inconclusive (.cons miss misses)
  | .found selected before misses later original_eq =>
      .found selected (first :: before) (.cons miss misses) later (congrArg (List.cons first) original_eq)

/-- Select by actual cached regions, retaining every original current-stage obligation and finite stopping reason. -/
private def select {polynomial : CoefficientPolynomial}
    {result : CCL.Polynomial.Basic.NonzeroResult polynomial} {stage : Nat} (lower : Rational) :
    (original : CandidateList result stage) → Selection lower original
  | [] => .inconclusive .nil
  | first :: remaining => match region : first.2.box with
    | none => (select lower remaining).prepend (.exact region)
    | some box => if branch : positiveRegion lower box then
        .found ⟨first.1, first.2, box, region, branch⟩ [] .nil remaining rfl
      else (select lower remaining).prepend (.outside box region branch)

/-- Inspect the same actual original higher-site root, using its typed cubic reality checker. -/
private def observationReal? {source opposite : CoefficientPolynomial}
    {input : Basis.Coprime.Side.PositiveSideInput source opposite}
    {context : Basis.Context.Basic.PositiveContext input.entries}
    {observation : Basis.Coprime.Side.PositiveSideInput.FactorObservation input context}
    {data : Multiplicity.Observation.CCL.Basic.ObservationCCL observation}
    {index : Multiplicity.Observation.Index.ObservationIndex observation}
    (admission : Multiplicity.Observation.CCL.Admission observation data index) (stage : Nat) :
    Option (Equivalence.NamedEquivalent admission.channel.name (CoherentNamed.conj admission.channel).name) := by
  cases admission.evidence with
  | exact => exact none
  | higher _ _ _ _ realization channelEq =>
      let attempt := realization.root.inspectCubic 2 stage
      cases attempt.outcome with
      | ready region =>
          exact some (by rewrite [channelEq]; exact region.real)
      | polynomialMismatch _ => exact none
      | negativeReal _ => exact none
      | unresolvedGap _ => exact none

/-- Read the same actual original higher-site cubic reality certificate from the side admission. -/
private def sideReal? {source opposite : CoefficientPolynomial} :
    (side : Multiplicity.Side.Basic.SideResult source opposite) →
    (data : Multiplicity.Side.CCL.Basic.SideCCL side) → (index : Multiplicity.Side.Index.SideIndex side) →
    (admission : Multiplicity.Side.CCL.Admission side data index) → Nat →
    Option (Equivalence.NamedEquivalent (Multiplicity.Side.CCL.Admission.channel admission).name
      (CoherentNamed.conj (Multiplicity.Side.CCL.Admission.channel admission)).name)
  | .constant _ _ _, _, index, _, _ => nomatch index
  | .positive _ _, _, _, admission, stage => observationReal? admission stage

/-- Read cubic reality of the same actual original polynomial site without replacing its channel. -/
private def rootReal? {polynomial : CoefficientPolynomial}
    {result : CCL.Polynomial.Basic.NonzeroResult polynomial}
    {index : RootIndex result}
    (admission : CCL.Polynomial.Admission result index) (stage : Nat) :
    Option (Equivalence.NamedEquivalent admission.channel.name (CoherentNamed.conj admission.channel).name) :=
  sideReal? result.rfap.numeratorSites result.numeratorCCL index admission.site stage

set_option genInjectivity false in
/-- The original selected positive region together with actual original-channel conjugacy. -/
private structure RealSelected {polynomial : CoefficientPolynomial}
    (result : CCL.Polynomial.Basic.NonzeroResult polynomial) (stage : Nat) where
  /-- The same original candidate and checked strictly positive real-coordinate region. -/
  selected : Selected result stage 0
  /-- The actual same-channel reality comparison obtained from its original polynomial residual and cached box. -/
  real : Equivalence.NamedEquivalent selected.candidate.admission.channel.name
    (CoherentNamed.conj selected.candidate.admission.channel).name

constructive_injectivity RealSelected

/-- Print and flush one original-construction execution checkpoint. -/
private def progress (message : String) : IO Unit := do
  Purelib.System.IO.println message
  (← IO.getStdout).flush

/-- Construct the original cubic source and select its positive real-axis region using retained boxes. -/
public def checkCubic : IO Unit := do
  progress "cubic: construct original coefficient root source"
  let polynomial := Power.Gaussian.rootPolynomial 2 ⟨3, by decide⟩
  let source := CCL.Polynomial.Build.isolate polynomial
  match source with
  | .zeroNumerator _ _ => throw (IO.userError "the original cubic source was reported identically zero")
  | .nonzero result =>
      progress "cubic: original source retained; observe original candidate boxes"
      let original := candidates result 2
      match select 0 original with
      | .inconclusive _ =>
          throw (IO.userError "finite cubic branch selection stopped at stage 2 with retained unresolved regions")
      | .found selected _ _ _ _ =>
          let real := rootReal? selected.candidate.admission 2
          match real with
          | none =>
              throw (IO.userError "finite cubic reality check stopped with retained polynomial/region obligations")
          | some comparison =>
              let retained : RealSelected result 2 := ⟨selected, comparison⟩
              unless retained.selected.box.xLower > 0 do
                throw (IO.userError "the original certified real branch lost its positive-region condition")
              progress "cubic: actual original positive-real branch certificate retained"
              unless retained.selected.candidate.admission.multiplicity = 1 do
                throw (IO.userError "the selected original cubic admission lost its source multiplicity")
              let admission := retained.selected.candidate.admission
              let sidecar := Algebraic.Sidecar.ofRoot (PolynomialRoot.Sidecar.ofAdmission admission)
              let environment : Fin 1 → Annotated := fun _ => Annotated.opaque admission.channel
              let admitted := Admitted.atom environment ⟨0, by decide⟩ sidecar
              match admitted.run with
              | .completed _ => pure ()
              | _ => throw (IO.userError "the actual admitted cubic atom failed finite checked completion")
              progress "cubic: original intrinsic admission completed"

/-- Restore the complete original cubic isolation with interrupted-work reuse at every saved finite stage.

The cubic invokes the general squarefree coefficient constructor. The
original degree-many family, order and boxes are retained, rather than a
locally supplied single-root isolation replacing the original source.
-/
public def checkCubicIsolation (directory : System.FilePath) (savedOnly : Bool := false) : IO Unit := do
  let polynomial := Power.Gaussian.rootPolynomial 2 ⟨3, by decide⟩
  let input : FTA.Squarefree.Input polynomial :=
    { squarefree := Power.Gaussian.Squarefree.squarefree (by decide) ⟨3, by decide⟩
      degreeAtLeastTwo := by
        rewrite [Power.Gaussian.rootPolynomial_degree]
        decide }
  progress "cubic isolation: restore original complete coefficient-selected family"
  let result ← InitialExtractionCheckpoint.separatedLargeSquare input
    { savedOnly := savedOnly } { savedOnly := savedOnly }
    { savedOnly := savedOnly } directory
  let boxes := FTA.Squarefree.Build.BoxFTA.fromIsolation input result.val
  let _boxesEq : boxes = FTA.Squarefree.Build.BoxFTA.prove input :=
    FTA.Squarefree.Build.BoxFTA.fromIsolation_eq_prove input result.val result.property
  let positiveInput : FTA.Positive.Input.PositiveInput polynomial :=
    ⟨input.squarefree, input.degreePositive⟩
  let positive : FTA.Positive.Basic.PositiveResult polynomial := .higher boxes input.degreeAtLeastTwo
  let _positiveEq : positive = FTA.Positive.Build.provePositive positiveInput :=
    FTA.Positive.Build.fromIsolation_eq_provePositive positiveInput input.degreeAtLeastTwo
      result.val result.property
  unless boxes.isolation.tracks.length = 3 do
    throw (IO.userError "the original cubic isolation lost its complete ordered degree-three family")
  for track in boxes.isolation.tracks do
    let box := Purelib.Data.Json.toJson (RootStateCheckpoint.boxData track.initial.box)
    progress s!"cubic isolation: original initial box {box}"
  progress "cubic isolation: original complete coefficient-selected family retained"

/-- Restore the complete original coefficient-first cubic CCL source from its saved factor-isolation work.

The general multiplicity replay retains cancellation, every original focused
factor, complete ordered root families and their CCL attachments. Its equality
identifies the original full polynomial-source constructor, not a local single
root supplied in place of the original coefficient-first result.
-/
public def checkCubicSource (directory : System.FilePath)
    (savedOnly interrupt : Bool := false) : IO Unit := do
  let polynomial := Power.Gaussian.rootPolynomial 2 ⟨3, by decide⟩
  progress "cubic source: restore original complete coefficient-first CCL result"
  let columns : ClearanceCheckpoint.Control IO :=
    { savedOnly := savedOnly
      afterSave := if interrupt then
        throw (IO.userError "checkpoint interruption after original source column save")
      else pure () }
  let saved ← MultiplicityCheckpoint.polynomial polynomial columns
    { savedOnly := savedOnly } { savedOnly := savedOnly } directory
  match saved.val with
  | .zeroNumerator _ _ => throw (IO.userError "original cubic source replay returned a zero numerator")
  | .nonzero result =>
      let indices := CCL.Polynomial.Index.NonzeroResult.rootIndices result
      unless indices.length = 3 do
        throw (IO.userError "original cubic source lost its complete three-site family")
      for index in indices do
        let admission := CCL.Polynomial.Admission.ofResult result index
        unless admission.multiplicity = 1 do
          throw (IO.userError "original cubic source lost its source multiplicity")
      progress "cubic source: complete original CCL result and indexed admissions retained"

end TestPurelib.Approximation.Gaussian.AlgebraicRootExecution
