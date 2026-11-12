module

import Purelib.System.IO
public import TestPurelib.RootIsolation.Newton.InitialSeeds
import Purelib.System.FilePath

import Purelib.Data.Json.Codec
import Purelib.Data.Json.Basic
import Purelib.Data.String.Basic

public import TestPurelib.RootIsolation.Checkpoint.NewtonStages
public import TestPurelib.RootIsolation.Checkpoint.Winding
public import TestPurelib.Polynomial.SeparatedQuadratic
public import TestPurelib.Polynomial.Elimination.Separated.Computation
public import TestPurelib.Polynomial.Elimination.Separated.Replay
public import TestPurelib.Polynomial.Elimination.Separated.Cubic
public import TestPurelib.Polynomial.Dense.Rational.DivisionCodec
public import TestPurelib.Polynomial.Dense.Rational.Evaluation
public import TestPurelib.Data.String.Parsing
public import TestPurelib.Data.String.Regression
public import TestPurelib.RootIsolation.Checkpoint.Multiplicity
public import TestPurelib.Data.Nat.Decimal
public import TestPurelib.Data.Nat.GCD.Scalar
public import TestPurelib.Data.Gaussian.Inverse.Prepared
public import TestPurelib.Polynomial.Dense.Gaussian.Substitution.Negation
public import TestPurelib.Approximation.Gaussian.AlgebraicConstruction
public import TestPurelib.LinearAlgebra.PolynomialMatrix.Pencil
public import TestPurelib.LinearAlgebra.PolynomialMatrix.Schur
public import TestPurelib.Polynomial.Elimination.Separated.Adjugate
public import TestPurelib.Polynomial.Elimination.Axis.Prepared
public import TestPurelib.Polynomial.Dense.Rational.Bounds.Horner
import Init.Prelude
import Init.System.FilePath
import Init.System.IO
import Init.System.IOError
import TestPurelib.RootIsolation.Checkpoint.Core
public import TestPurelib.RootIsolation.Checkpoint.GridStages
import scripts.checkpoint.Integration
import scripts.checkpoint.RootRefinement

-- Use complete constructor eliminators for the original match arms.
set_option backward.match.sparseCases false

open Purelib.Data (Json)
open scoped Purelib.Data.List Purelib.Data.Range Purelib.Data.String
open Purelib.Data.Json (toJson)
open TestPurelib.Polynomial
open TestPurelib.Polynomial.Dense.Rational
open TestPurelib.Data.Gaussian.Inverse
open TestPurelib.Data.String

public section

namespace CanonicalIsolationCheckpointHarness

open IntegrationCheckpoint

/-- Check interrupted isolation recovery, exact original output and generator-free cold replay.

The fresh-directory protocol retains the tested executable, validates rejected requests and exercises family, frame and
subdivision checkpoints. -/
@[expose] def selfTest (directory : System.FilePath) : IO Unit := do
  if ← directory.pathExists then throw (IO.userError "self-test requires a fresh artifact directory")
  IO.FS.createDirAll directory
  let copy ← Purelib.System.IO.Process.output
    { cmd := "/bin/cp", args := #[(← IO.appPath).toString, ((Purelib.System.FilePath.join directory (System.FilePath.mk
      ("tested-harness")))).toString] }
  unless copy.exitCode == 0 do throw (IO.userError ("could not archive tested binary: " ++ copy.stderr))
  let executable := (← IO.appPath).toString
  let child := fun mode => Purelib.System.IO.Process.output
    { cmd := "/usr/bin/timeout", args := #["--signal=KILL", "45s", executable, "child", directory.toString, mode] }
  let count := fun (output : IO.Process.Output) marker =>
    ((Purelib.Data.String.splitOn (output.stdout ++ output.stderr) marker)).length - 1
  let record := fun mode (output : IO.Process.Output) =>
    saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"{mode}-result.json"))))
      (output.exitCode.toNat, output.stdout, output.stderr)
  let calibration ← child "calibrate"
  record "calibrate" calibration
  unless calibration.exitCode == 0 && count calibration "CANONICAL_ISOLATION_GENERATOR_FORCED" == 1 do
    throw (IO.userError ("canonical marker calibration failed\n" ++ calibration.stdout ++ calibration.stderr))
  let crash ← child "crash"
  record "crash" crash
  unless crash.exitCode != 0 && count crash "ROOT_TRACE_ROUNDING_GENERATOR_FORCED" == 1 &&
      count crash "CANONICAL_ISOLATION_GENERATOR_FORCED" == 0 &&
      (← ((Purelib.System.FilePath.join directory (System.FilePath.mk
        ("isolation/step-0/seed-0/proposal-0-rounding.json")))).pathExists) do
    throw (IO.userError ("atomic interruption failed\n" ++ crash.stdout ++ crash.stderr))
  let resumed ← child "resume"
  record "resume" resumed
  unless resumed.exitCode == 0 && count resumed "CANONICAL_ISOLATION_GENERATOR_FORCED" == 0 do
    throw (IO.userError ("isolation resume failed\n" ++ resumed.stdout ++ resumed.stderr))
  let reused : RootRefinementCheckpoint.Counts ← loadJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
    ("counts-resume.json"))))
  unless reused.reusedRounding == 1 do throw (IO.userError "resume did not reuse its completed first proposal")
  let replay ← child "replay"
  record "replay" replay
  unless replay.exitCode == 0 && count replay "CANONICAL_ISOLATION_GENERATOR_FORCED" == 0 &&
      count replay "ROOT_TRACE_ROUNDING_GENERATOR_FORCED" == 0 &&
      count replay "ROOT_TRACE_NEWTON_GENERATOR_FORCED" == 0 do
    throw (IO.userError ("cold isolation replay generated or failed\n" ++ replay.stdout ++ replay.stderr))
  IO.print replay.stdout
  let first : Json ← loadJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
    ("isolation/step-0/result.json"))))
  let trials ← match first.getObjValAs? Nat "tried" with
    | .ok value => pure value
    | .error message => throw (IO.userError message)
  unless 1 < trials do throw (IO.userError "fixture did not test first-seed rejection and later-seed success")
  let headerPath := (Purelib.System.FilePath.join directory (System.FilePath.mk ("isolation/step-0/request.json")))
  let header : Json ← loadJson headerPath
  saveJson headerPath (Json.mkObj [("format", toJson "wrong-source")])
  let invalid ← child "replay"
  record "bad-request" invalid
  unless invalid.exitCode != 0 &&
      (← ((Purelib.System.FilePath.join directory (System.FilePath.mk
        ("isolation/step-0/invalid-request.json")))).pathExists) do
    throw (IO.userError "changed isolation request was accepted")
  saveJson headerPath header
  let recovered ← child "replay"
  record "recovered" recovered
  unless recovered.exitCode == 0 && count recovered "CANONICAL_ISOLATION_GENERATOR_FORCED" == 0 &&
      count recovered "ROOT_TRACE_ROUNDING_GENERATOR_FORCED" == 0 &&
      count recovered "ROOT_TRACE_NEWTON_GENERATOR_FORCED" == 0 do
    throw (IO.userError "restoring the valid request did not recover generator-free replay")
  Purelib.System.IO.println
    "Canonical isolation: atomic restart, first-success ordering, full-state equality and generator-free replay passed."
  familySelfTest ((Purelib.System.FilePath.join directory (System.FilePath.mk ("family"))))
  frameSelfTest ((Purelib.System.FilePath.join directory (System.FilePath.mk ("frame"))))
  gridFramesSelfTest ((Purelib.System.FilePath.join directory (System.FilePath.mk ("grid-frames"))))
  subdivisionSelfTest ((Purelib.System.FilePath.join directory (System.FilePath.mk ("subdivision"))))

/-- Import only the previous reference and proposal checkpoints into a fresh directory. The shared loader checks every
consumed request and witness; the original artifact is never modified. Missing old binary provenance is stated
explicitly and is not inferred from a directory name. -/
@[expose] def resumeTest (source directory : System.FilePath) (family : Bool := false) : IO Unit := do
  if ← directory.pathExists then throw (IO.userError "resume-test requires a fresh destination")
  IO.FS.createDirAll directory
  let executable := (← IO.appPath).toString
  let copy := fun (sourcePath destinationPath : System.FilePath) => do
    let result ← Purelib.System.IO.Process.output
      { cmd := "/bin/cp", args := #["-a", sourcePath.toString, destinationPath.toString] }
    unless result.exitCode == 0 do throw (IO.userError result.stderr)
  let reference := if family then "family-canonical.json" else "canonical.json"
  copy ((Purelib.System.FilePath.join source (System.FilePath.mk (reference)))) ((Purelib.System.FilePath.join directory
    (System.FilePath.mk (reference))))
  copy ((Purelib.System.FilePath.join source (System.FilePath.mk ("isolation")))) ((Purelib.System.FilePath.join
    directory (System.FilePath.mk ("isolation"))))
  copy (← IO.appPath) ((Purelib.System.FilePath.join directory (System.FilePath.mk ("tested-harness"))))
  let fingerprint := fun (path : System.FilePath) => do
    if !(← path.pathExists) then return "unknown: previous executable was not archived"
    let result ← Purelib.System.IO.Process.output { cmd := "/usr/bin/sha256sum", args := #[path.toString] }
    unless result.exitCode == 0 do throw (IO.userError result.stderr)
    return result.stdout
  saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("import.json")))) (Json.mkObj
    [("source", toJson source.toString),
     ("sourceBinary", toJson (← fingerprint ((Purelib.System.FilePath.join source (System.FilePath.mk
       ("tested-harness")))))),
     ("destinationBinary", toJson (← fingerprint ((Purelib.System.FilePath.join directory (System.FilePath.mk
       ("tested-harness")))))),
     ("validation", toJson "exact requests, checked proposals, and full original output comparison")])
  for mode in ["resume", "replay"] do
    let result ← Purelib.System.IO.Process.output
      { cmd := "/usr/bin/timeout", args := #["--signal=KILL", "45s", executable,
          (if family then "family-child" else "child"), directory.toString, mode] }
    saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"{mode}-result.json"))))
      (result.exitCode.toNat, result.stdout, result.stderr)
    unless result.exitCode == 0 &&
        !(1 < (Purelib.Data.String.splitOn (result.stdout ++ result.stderr)
          "CANONICAL_ISOLATION_GENERATOR_FORCED").length) &&
        !(1 < (Purelib.Data.String.splitOn (result.stdout ++ result.stderr) "CANONICAL_FAMILY_GENERATOR_FORCED").length)
          do
      throw (IO.userError ("imported isolation resume/replay failed\n" ++ result.stdout ++ result.stderr))
    let counts : RootRefinementCheckpoint.Counts ← loadJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
      (s!"counts-{mode}.json"))))
    unless 0 < counts.reusedRounding do throw (IO.userError "imported completed work was not reused")
    if mode == "replay" then
      unless counts.generatedNewton == 0 && counts.generatedRounding == 0 do
        throw (IO.userError "imported cold replay regenerated proposals")
    Purelib.System.IO.println s!"Imported {mode}: {(toJson counts).compress}"

end CanonicalIsolationCheckpointHarness

/-- Dispatch finite root-isolation checkpoints and retained polynomial-arithmetic diagnostics.

Each branch consumes its supplied checkpoint directory, artifact path or
fixed regression input. Stored rational profiles read the original column
and coordinate without changing the numerical request.
-/
@[expose] def main (arguments : List String) : IO Unit := do
  match arguments with
  | ["prepared-inverse-self-test"] => Prepared.check
  | ["prepared-inverse-profile", path] => do
      let raw : ClearanceCheckpoint.RawColumn ← IntegrationCheckpoint.loadJson (System.FilePath.mk path)
      let coordinate ← IntegrationCheckpoint.checked "original saved axis coordinate"
        (IntegrationCheckpoint.decodeFraction raw.parameter)
      Prepared.profile ⟨coordinate, 0⟩
  | ["sturm-seed-check"] => TestPurelib.RootIsolation.Newton.InitialSeeds.check
  | ["sturm-extraction-check", directory, mode] =>
      TestPurelib.RootIsolation.Newton.InitialSeeds.checkExtraction directory mode
  | ["sturm-isolation-check", directory, mode] =>
      TestPurelib.RootIsolation.Newton.InitialSeeds.checkIsolation directory mode
  | ["winding-child", directory, mode, "--input-digest-stdio-v1"] =>
      TestPurelib.RootIsolation.Checkpoint.Winding.child directory mode (some WindingCheckpoint.streamedInputDigest)
  | ["winding-child", directory, mode] => TestPurelib.RootIsolation.Checkpoint.Winding.child directory mode
  | ["winding-self-test", directory] => TestPurelib.RootIsolation.Checkpoint.Winding.selfTest directory
  | ["quadratic-self-test", directory] => TestPurelib.Polynomial.SeparatedQuadratic.selfTest directory
  | "quadratic-columns" :: paths =>
      for path in paths do TestPurelib.Polynomial.SeparatedQuadratic.compareStored path
  | "quadratic-reciprocal-profile" :: paths =>
      for path in paths do TestPurelib.Polynomial.SeparatedQuadratic.profileStored path
  | ["column-dispatch-self-test", directory] =>
      Elimination.Separated.Computation.selfTest directory
  | ["cubic-columns-self-test"] => Elimination.Separated.Cubic.check
  | ["rational-evaluation-self-test"] => Evaluation.check
  | "rational-evaluation-profile" :: paths =>
      for path in paths do Evaluation.checkStored (System.FilePath.mk path) false
  | "rational-original-profile" :: paths =>
      for path in paths do Evaluation.checkStored (System.FilePath.mk path) true
  | "division-codec-profile" :: paths =>
      for path in paths do Dense.Rational.DivisionCodec.profile path
  | "division-check-profile" :: path :: paths =>
      for input in path :: paths do Dense.Rational.DivisionCodec.profile input false
  | "fraction-decoding-profile" :: path :: paths =>
      for input in path :: paths do Dense.Rational.DivisionCodec.profileDecoding input
  | ["decimal-parser-self-test"] => Parsing.check
  | ["decimal-parser-profile", path] => do
      let raw : ClearanceCheckpoint.RawColumn ← IntegrationCheckpoint.loadJson (System.FilePath.mk path)
      Parsing.profile raw.parameter.denominator
  | ["string-length-self-test"] => TestPurelib.Data.String.checkLength
  | ["multiplicity-replay-self-test", directory] =>
      TestPurelib.RootIsolation.Checkpoint.Multiplicity.check (System.FilePath.mk directory)
  | "decimal-render-profile" :: paths =>
      for path in paths do Dense.Rational.DivisionCodec.profileRendering path
  | ["decimal-render-self-test"] => TestPurelib.Data.Nat.Decimal.check
  | ["scalar-gcd-self-test"] => TestPurelib.Data.Nat.GCD.Scalar.check
  | ["polynomial-negation-self-test"] =>
      Dense.Gaussian.Substitution.Negation.check
      TestPurelib.Approximation.Gaussian.AlgebraicConstruction.checkNegation
  | ["compact-pencil-self-test"] => TestPurelib.LinearAlgebra.PolynomialMatrix.Pencil.checkProposal
  | ["generated-pencil-self-test"] => TestPurelib.LinearAlgebra.PolynomialMatrix.Pencil.checkGenerated
  | "schur-cache-profile" :: paths =>
      for path in paths do TestPurelib.LinearAlgebra.PolynomialMatrix.Schur.checkStored path
  | "schur-scalar-profile" :: paths =>
      for path in paths do TestPurelib.LinearAlgebra.PolynomialMatrix.Schur.checkScalarStored path
  | "polynomial-adjugate-profile" :: paths =>
      for path in paths do Elimination.Separated.Adjugate.checkStored path
  | "prepared-cofactor-profile" :: paths =>
      for path in paths do Elimination.Axis.Prepared.profileStored path
  | "horner-square-profile" :: paths =>
      for path in paths do Dense.Rational.Bounds.Horner.profileStored path

  | ["column-path-profile", "vertical", path] =>
      Elimination.Separated.Replay.profileStored path false
  | ["column-path-profile", "horizontal", path] =>
      Elimination.Separated.Replay.profileStored path true
  | "column-product-profile" :: path :: paths =>
      for input in path :: paths do Elimination.Separated.Replay.profileProductsStored input
  | ["initial-fallback-child", directory, mode] =>
    CanonicalIsolationCheckpointHarness.InitialFallback.child directory mode
  | ["counts", directory] => CanonicalIsolationCheckpointHarness.checkCounts directory
  | ["self-test", directory] => CanonicalIsolationCheckpointHarness.selfTest directory
  | ["child", directory, mode] => CanonicalIsolationCheckpointHarness.child directory mode
  | ["newton-child", directory, mode] => CanonicalIsolationCheckpointHarness.NewtonRefinement.child directory mode
  | ["newton-resume-test", directory] => CanonicalIsolationCheckpointHarness.newtonSelfTest directory true
  | ["newton-self-test", directory] => CanonicalIsolationCheckpointHarness.newtonSelfTest directory
  | ["newton-depth"] => CanonicalIsolationCheckpointHarness.Subdivision.newtonDepth
  | ["subdivision-child", directory, mode] => CanonicalIsolationCheckpointHarness.Subdivision.child directory mode
  | ["subdivision-self-test", directory] => CanonicalIsolationCheckpointHarness.subdivisionSelfTest directory
  | ["grid-frames-child", directory, mode] => CanonicalIsolationCheckpointHarness.FrameGrid.child directory mode
  | ["grid-frames-self-test", directory] => CanonicalIsolationCheckpointHarness.gridFramesSelfTest directory
  | ["frame-child", directory, mode] => CanonicalIsolationCheckpointHarness.frameChild directory mode
  | ["frame-self-test", directory] => CanonicalIsolationCheckpointHarness.frameSelfTest directory
  | ["family-child", directory, mode] => CanonicalIsolationCheckpointHarness.familyChild directory mode
  | ["family-self-test", directory] => CanonicalIsolationCheckpointHarness.familySelfTest directory
  | ["resume-test", source, directory] => CanonicalIsolationCheckpointHarness.resumeTest source directory
  | ["family-resume-test", source, directory] => CanonicalIsolationCheckpointHarness.resumeTest source directory true
  | _ => throw (IO.userError
    "usage: canonical_isolation_checkpoint_harness self-test FRESH_DIRECTORY | family-self-test FRESH_DIRECTORY | \
      frame-self-test FRESH_DIRECTORY | grid-frames-self-test FRESH_DIRECTORY | subdivision-self-test FRESH_DIRECTORY \
      | newton-self-test FRESH_DIRECTORY | newton-resume-test DIRECTORY | resume-test SOURCE FRESH_DIRECTORY | \
      family-resume-test SOURCE FRESH_DIRECTORY | scalar-gcd-self-test | string-length-self-test | \
      rational-evaluation-self-test | rational-evaluation-profile PATH... | rational-original-profile PATH...")
