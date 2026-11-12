module

import TestPurelib.Curves.Hyperelliptic.NormalizedCapLoop.Observation
import Purelib.System.IO

open TestPurelib.Curves.Hyperelliptic

/-- Select the actual cap requests and construction phases through the original finite checkpoint protocol. -/
public def main (arguments : List String) : IO Unit :=
  match arguments with
  | ["--compound-cases"] => do
      Purelib.System.IO.println "fixture-inputs"
      Purelib.System.IO.println "origin-preparation"
      Purelib.System.IO.println "origin-attachment"
      Purelib.System.IO.println "origin-anchor"
      Purelib.System.IO.println "origin-assignment"
      Purelib.System.IO.println "origin-readings"
      Purelib.System.IO.println "anchor-request"
      Purelib.System.IO.println "anchor-sample"
      Purelib.System.IO.println "exact-seed"
      Purelib.System.IO.println "exact-seed-anchor"
      Purelib.System.IO.println "exact-seed-assignment"
      Purelib.System.IO.println "exact-seed-attachment"
      Purelib.System.IO.println "exact-seed-normalized-loop"
      Purelib.System.IO.println "exact-seed-payment"
      Purelib.System.IO.println "exact-seed-certified-loop"
      Purelib.System.IO.println "normalized-loop"
  | ["--compound-case", "fixture-inputs"] =>
      NormalizedCapLoop.Observation.checkInputs
  | ["--compound-case", "origin-preparation"] =>
      NormalizedCapLoop.Observation.checkOriginPreparation ⟨0, by decide⟩
  | ["--compound-case", "origin-attachment"] =>
      NormalizedCapLoop.Observation.checkOriginAttachment ⟨0, by decide⟩
  | ["--compound-case", "origin-anchor"] =>
      NormalizedCapLoop.Observation.checkOriginAnchor ⟨0, by decide⟩
  | ["--compound-case", "origin-assignment"] =>
      NormalizedCapLoop.Observation.checkOriginAssignment ⟨0, by decide⟩
  | ["--compound-case", "origin-readings"] =>
      NormalizedCapLoop.Observation.checkOriginReadings ⟨0, by decide⟩
  | ["--compound-case", "anchor-request"] =>
      NormalizedCapLoop.Observation.checkAnchorRequest ⟨0, by decide⟩
  | ["--compound-case", "anchor-sample"] =>
      NormalizedCapLoop.Observation.checkAnchorSample ⟨0, by decide⟩
  | ["--compound-case", "exact-seed"] =>
      NormalizedCapLoop.Observation.checkExactSeed ⟨0, by decide⟩
  | ["--compound-case", "exact-seed-anchor"] =>
      NormalizedCapLoop.Observation.checkExactSeedAnchor ⟨0, by decide⟩
  | ["--compound-case", "exact-seed-assignment"] =>
      NormalizedCapLoop.Observation.checkExactSeedAssignment ⟨0, by decide⟩
  | ["--compound-case", "exact-seed-attachment"] =>
      NormalizedCapLoop.Observation.checkExactSeedAttachment ⟨0, by decide⟩
  | ["--compound-case", "exact-seed-normalized-loop"] =>
      NormalizedCapLoop.Observation.runExactSeed ⟨0, by decide⟩
  | ["--compound-case", "exact-seed-payment"] =>
      NormalizedCapLoop.Observation.runExactSeed ⟨0, by decide⟩ true
  | ["--compound-case", "exact-seed-certified-loop"] =>
      NormalizedCapLoop.Observation.runExactSeed ⟨0, by decide⟩ false true
  | ["--compound-case", "normalized-loop"] =>
      NormalizedCapLoop.Observation.run ⟨0, by decide⟩
  | _ => throw (IO.userError "select --compound-cases or one --compound-case")
