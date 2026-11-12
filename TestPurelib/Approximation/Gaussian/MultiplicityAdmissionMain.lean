module

import TestPurelib.Approximation.Gaussian.MultiplicityAdmission
import scripts.checkpoint.Multiplicity
import scripts.checkpoint.RawSubdivision
import scripts.checkpoint.RootRefinement
import Purelib.Data.Rat.Fraction
import Purelib.System.FilePath
import Init.System.FilePath
import Purelib.System.IO
import Purelib.Approximation.Gaussian.Sequence.SamplePrefix
import Purelib.Approximation.Gaussian.Name.Sampling

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.RootIsolation.Multiplicity
open Purelib.RationalFunctions
open TestPurelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian

/-- Retain one original coefficient-produced bank and its exact same-cache admission reader.

The original source, optional request, saved-only controls, prefix selection
and state-directory order are captured by this one preparation. Every consumed
admission comes from the supplied result's bounded index and literal cache.
The optional productive payment retains the original comparison and both
actual observations; its sampling checkpoints use a distinct exact trajectory.
Persistent request controls can prepare outstanding refinements while the
original bank and admission-prefix readers remain saved-only.
-/
private def prepareBank (request : Option Rational) (directory selected : String)
    (columns : ClearanceCheckpoint.Control IO) (savedOnly : Bool) (productive : Bool := false)
    (inputDigest : Option (String → IO String) := none)
    (persistentColumns : Option (ClearanceCheckpoint.Control IO) := none) :
    MultiplicityAdmission.BankPreparation request :=
  fun label source use => do
    let saved ← MultiplicityCheckpoint.polynomial source columns
      { savedOnly := savedOnly, inputDigest := inputDigest }
      { savedOnly := savedOnly, inputDigest := inputDigest }
      (Purelib.System.FilePath.join (System.FilePath.mk directory)
        (System.FilePath.mk label)) request true
    match saved with
    | ⟨⟨.zeroNumerator _ _, _⟩, _⟩ =>
        throw (IO.userError "a displayed nonzero higher-admission source was classified zero")
    | ⟨⟨.nonzero result, cached⟩, same⟩ =>
        have resultEq : ArgumentPrinciple.CCL.Basic.Result.nonzero result =
            CCL.Polynomial.Build.isolate source request := same
        have origins : (ArgumentPrinciple.CCL.Basic.Result.nonzero result).NewtonOrigins := by
          rewrite [resultEq]
          exact CCL.Polynomial.Build.isolate_newtonOrigins source request
        let requestColumns := persistentColumns.getD columns
        let requestWinding : WindingCheckpoint.Control IO :=
          match persistentColumns with
          | none => { savedOnly := savedOnly, inputDigest := inputDigest }
          | some control =>
              { savedOnly := control.savedOnly, afterSave := control.afterSave, inputDigest := inputDigest }
        let admissions : MultiplicityAdmission.AdmissionBuilder result := fun index occurrence count consume => do
          let states := Purelib.System.FilePath.join (System.FilePath.mk directory)
            (System.FilePath.mk s!"root-states/{label}/entry-{occurrence}")
          let retainedCount := if selected == "higher-sturm-states" then 4 else count
          Purelib.System.IO.println
            s!"higher states: BEGIN {label} occurrence {occurrence}, original prefix count {retainedCount}"
          MultiplicityCheckpoint.polynomialAdmission result origins columns
            { savedOnly := savedOnly, inputDigest := inputDigest } states index retainedCount (cached := some cached)
            fun admission complete initial =>
              MultiplicityCheckpoint.withAdmissionStateReaders result.rfap.numeratorSites result.numeratorCCL
                origins.1.1 origins.2.1 columns { savedOnly := savedOnly, inputDigest := inputDigest }
                states index admission.site initial (fun readers => do
                  Purelib.System.IO.println
                    s!"higher states: END {label} occurrence {occurrence}, same original admission"
                  if productive && count == 3 then
                    let equivalent := admission.equivalent
                    let target : {value : Rational // 0 < value} := ⟨1, by decide⟩
                    let paid := equivalent.compare 0 0 target.val target.property
                    Purelib.System.IO.println
                      s!"productive p: BEGIN occurrence {occurrence}, actual indices {paid.leftIndex}/{paid.rightIndex}"
                    let samples ← MultiplicityCheckpoint.polynomialSamples result origins columns
                      { savedOnly := savedOnly, inputDigest := inputDigest }
                      (Purelib.System.FilePath.join states (System.FilePath.mk "productive-samples"))
                      index (paid.leftIndex + 1) (cached := some cached)
                    let right := Name.Sampling.approximation admission.channel.name
                    let rightValue := right.sample paid.rightIndex
                    let rightSamples := Sequence.SamplePrefix.ofEntries right [⟨paid.rightIndex, rightValue, rfl⟩]
                    MultiplicityAdmission.checkAgreement equivalent 0 0 target
                      (some samples) (some rightSamples) ⟨paid, rfl⟩
                    Purelib.System.IO.println
                      s!"productive p: END occurrence {occurrence}, original productive request paid"
                  consume admission complete readers) (cached := some cached.1)
        let persistent : MultiplicityAdmission.PersistentBuilder result :=
          fun index occurrence requestOrdinal current history cursorEq sourceEq epsilon positive count consume =>
            MultiplicityCheckpoint.polynomialRequest result origins requestColumns requestWinding
              (Purelib.System.FilePath.join (System.FilePath.mk directory)
                (System.FilePath.mk s!"root-states/{label}/entry-{occurrence}/persistent/request-{requestOrdinal}"))
              index current history cursorEq sourceEq epsilon positive count consume (cached := some cached)
        use result resultEq admissions persistent

/-- Execute one original comparison case, optionally restoring its complete coefficient-produced banks.

The saved producer returns the original full isolate result with its equality,
so the fixture retains the same input sources, root indices and admissions.
The interruption mode stops only after a completed clearance save; resume and
saved-only replay use that same original checkpoint owner.
-/
private def comparisonCase (selected directory mode : String)
    (inputDigest : Option (String → IO String) := none) : IO Unit := do
  unless mode == "resume" || mode == "replay" || mode == "interrupt" do
    throw (IO.userError "comparison checkpoint mode must be resume, replay or interrupt")
  MultiplicityAdmission.check
  match selected with
  | "nested" => MultiplicityAdmission.checkRequests
  | "coarse-independent" => MultiplicityAdmission.checkIndependent (coarse := true)
  | "persistent-exact" =>
      unless mode == "resume" || mode == "replay" do
        throw (IO.userError "exact persistent admission requires resume or replay")
      let savedOnly := mode == "replay"
      MultiplicityAdmission.checkExactPersistentAdmissions
        (prepareBank none directory selected { savedOnly := savedOnly } savedOnly (inputDigest := inputDigest))
  | "independent" =>
      let savedOnly := mode == "replay"
      let columns : ClearanceCheckpoint.Control IO :=
        { savedOnly := savedOnly
          afterSave := if mode == "interrupt" then
            throw (IO.userError "comparison interruption after original root-state column save")
          else pure () }
      MultiplicityAdmission.checkIndependent
        (some fun label input track refinement count =>
          RawSubdivisionCheckpoint.rootPrefix input
            (RootRefinementCheckpoint.ClearanceLoader.separated columns _ input.nonzero input.degreePositive)
            columns { savedOnly := savedOnly, inputDigest := inputDigest }
            (Purelib.System.FilePath.join (System.FilePath.mk directory) (System.FilePath.mk label))
            track refinement count)
        (controls := some (columns, { savedOnly := savedOnly, inputDigest := inputDigest },
          System.FilePath.mk directory))
  | "retained-p-same-owner" =>
      unless mode == "replay" do
        throw (IO.userError "bounded retained p admission requires saved-only replay")
      let columns : ClearanceCheckpoint.Control IO := { savedOnly := true }
      MultiplicityAdmission.checkRetainedPAdmissions
        (prepareBank (some (1 / 256)) directory selected columns true (inputDigest := inputDigest))
  | "retained-p-persistent" =>
      let requestColumns : ClearanceCheckpoint.Control IO :=
        { savedOnly := mode == "replay"
          afterSave := if mode == "interrupt" then
            throw (IO.userError "persistent request interrupted after original numerical certificate save")
          else pure () }
      MultiplicityAdmission.checkRetainedPAdmissions
        (prepareBank (some (1 / 256)) directory selected { savedOnly := true } true
          (inputDigest := inputDigest) (persistentColumns := some requestColumns))
        (persistent := true)
  | "retained-p-productive" =>
      let savedOnly := mode == "replay"
      let columns : ClearanceCheckpoint.Control IO :=
        { savedOnly := savedOnly
          afterSave := if mode == "interrupt" then
            throw (IO.userError "productive comparison interrupted after original column save")
          else pure () }
      MultiplicityAdmission.checkRetainedPAdmissions
        (prepareBank (some (1 / 256)) directory selected columns savedOnly true
          (inputDigest := inputDigest))
  | "higher" | "higher-sturm" | "higher-sturm-states" | "higher-sturm-demanded-states" |
      "higher-sturm-demanded-general-cubic-states" =>
      let request : Option Rational := if selected == "higher" then none else some (1 / 256)
      let savedOnly := mode == "replay"
      let columns : ClearanceCheckpoint.Control IO :=
        { savedOnly := savedOnly
          afterSave := if mode == "interrupt" then
            throw (IO.userError "comparison interruption after original source column save")
          else pure ()
          generalCubic := selected == "higher-sturm-demanded-general-cubic-states" }
      let produce := fun label source =>
        MultiplicityCheckpoint.polynomial source columns
          { savedOnly := savedOnly, inputDigest := inputDigest }
          { savedOnly := savedOnly, inputDigest := inputDigest }
          (Purelib.System.FilePath.join (System.FilePath.mk directory)
            (System.FilePath.mk label)) request
      if selected == "higher-sturm-states" || selected == "higher-sturm-demanded-states" ||
          selected == "higher-sturm-demanded-general-cubic-states" then
        let prepare := prepareBank request directory selected columns savedOnly (inputDigest := inputDigest)
        MultiplicityAdmission.checkHigherAdmissions request produce
          (prepare := some prepare)
          (comparisons := some (columns, { savedOnly := savedOnly, inputDigest := inputDigest },
            Purelib.System.FilePath.join (System.FilePath.mk directory) "comparisons"))
      else
        MultiplicityAdmission.checkHigherAdmissions request produce
  | _ => throw (IO.userError "comparison case must name an entry of --comparison-cases")

/-- Execute the original intrinsic-site protocol or one checked restartable comparison case. -/
public def main (arguments : List String) : IO Unit := do
  match arguments with
  | ["--comparison-cases"] =>
      for selected in ["nested", "coarse-independent", "independent", "higher", "higher-sturm", "higher-sturm-states",
          "higher-sturm-demanded-states", "higher-sturm-demanded-general-cubic-states",
          "retained-p-same-owner", "retained-p-persistent", "retained-p-productive", "persistent-exact"] do
        Purelib.System.IO.println selected
  | ["--comparison-case", selected, directory, mode, "--input-digest-stdio-v1"] =>
      comparisonCase selected directory mode (some WindingCheckpoint.streamedInputDigest)
  | ["--comparison-case", selected, directory, mode] => comparisonCase selected directory mode
  | _ =>
      MultiplicityAdmission.check
      if arguments == ["--compare"] then
        MultiplicityAdmission.checkRequests
        MultiplicityAdmission.checkIndependent
      if arguments == ["--nested-compare"] then
        MultiplicityAdmission.checkRequests
      if arguments == ["--coarse-compare"] then
        MultiplicityAdmission.checkIndependent (coarse := true)
      if arguments == ["--higher-compare"] then
        MultiplicityAdmission.checkHigherAdmissions
