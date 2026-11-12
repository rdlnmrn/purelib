module

import TestPurelib.Approximation.Gaussian.AlgebraicRootExecution
import TestPurelib.Riemann.RootReconditioning
import scripts.checkpoint.RootRefinement
import Purelib.System.IO

open TestPurelib.Approximation.Gaussian

/-- Execute original coefficient-root and prepared continuation requests. -/
public def main (arguments : List String) : IO Unit := do
  match arguments with
  | [] => AlgebraicRootExecution.checkCubic
  | ["--prepare-source", directory] =>
      AlgebraicRootExecution.checkCubicSource directory
  | ["--interrupt-source-after-column", directory] =>
      AlgebraicRootExecution.checkCubicSource directory false true
  | ["--prepare-source-saved-only", directory] =>
      AlgebraicRootExecution.checkCubicSource directory true
  | ["--prepare-isolation", directory] =>
      AlgebraicRootExecution.checkCubicIsolation directory
  | ["--prepare-isolation-saved-only", directory] =>
      AlgebraicRootExecution.checkCubicIsolation directory true
  | ["--comparison-cases"] => Purelib.System.IO.println "prepared-cubic-endpoint"
  | ["--comparison-case", "prepared-cubic-endpoint", directory, "resume", "--input-digest-stdio-v1"] =>
      TestPurelib.Riemann.RootReconditioning.checkPreparedCubicEndpoint directory false
        (some WindingCheckpoint.streamedInputDigest)
  | ["--comparison-case", "prepared-cubic-endpoint", directory, "replay", "--input-digest-stdio-v1"] =>
      TestPurelib.Riemann.RootReconditioning.checkPreparedCubicEndpoint directory true
        (some WindingCheckpoint.streamedInputDigest)
  | ["--comparison-case", "prepared-cubic-endpoint", directory, "resume"] =>
      TestPurelib.Riemann.RootReconditioning.checkPreparedCubicEndpoint directory
  | ["--comparison-case", "prepared-cubic-endpoint", directory, "replay"] =>
      TestPurelib.Riemann.RootReconditioning.checkPreparedCubicEndpoint directory true
  | _ => throw (IO.userError
      "usage: algebraic_root_execution_harness [--prepare-isolation DIRECTORY | \
        --prepare-isolation-saved-only DIRECTORY | --prepare-source DIRECTORY | \
        --prepare-source-saved-only DIRECTORY | --interrupt-source-after-column DIRECTORY | \
        --comparison-cases | --comparison-case prepared-cubic-endpoint DIRECTORY resume|replay \
        [--input-digest-stdio-v1]]")
