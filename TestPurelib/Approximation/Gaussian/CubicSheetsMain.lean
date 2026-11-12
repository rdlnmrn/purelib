module

import Purelib.System.IO
import TestPurelib.Approximation.Gaussian.CubicSheets
import TestPurelib.Polynomial.Approximation.Gaussian.Residual.Origin
import TestPurelib.Polynomial.RootLocalization

open Purelib
open TestPurelib.Approximation.Gaussian

/-- Execute an original upper cubic owner and its actual distinct conjugated branch in native code. -/
public def main (arguments : List String) : IO Unit :=
  match arguments with
  | ["--root-comparison-cases"] => do
      System.IO.println "independent"
      System.IO.println "conjugate-identification"
      System.IO.println "conjugate-selection"
  | ["--root-comparison-case", "independent"] => CubicSheets.checkGeneralIndependent
  | ["--root-comparison-case", "conjugate-identification"] => CubicSheets.checkConjugateIdentification
  | ["--root-comparison-case", "conjugate-identification", directory, mode] =>
      match mode with
      | "resume" => CubicSheets.checkConjugateIdentification (some (.mk directory)) false false
      | "replay" => CubicSheets.checkConjugateIdentification (some (.mk directory)) true true
      | _ => throw (IO.userError "original cubic identification requires resume or replay selection mode")
  | ["--root-comparison-case", "conjugate-selection", directory, mode] =>
      match mode with
      | "resume" => CubicSheets.checkCachedConjugateSelection (.mk directory) false false
      | "replay" => CubicSheets.checkCachedConjugateSelection (.mk directory) true true
      | _ => throw (IO.userError "original cubic selection requires resume or replay mode")
  | ["--root-comparison-case", "conjugate-selection"] =>
      throw (IO.userError "original cubic selection requires a checkpoint directory and resume or replay mode")
  | "--root-comparison-case" :: _ => throw (IO.userError "invalid original cubic root-comparison request")
  | ["--identify-conjugate"] => CubicSheets.checkConjugateIdentification
  | ["--general-distinct"] => CubicSheets.checkGeneralDistinct
  | ["--general-independent"] => CubicSheets.checkGeneralIndependent
  | ["--compound-inverses"] => CubicSheets.checkCompoundInverses
  | ["--compound-case", name] => CubicSheets.checkCompoundInverseCase name
  | ["--compound-cases"] => do
      for name in CubicSheets.compoundInverseCases do
        System.IO.println name
  | ["--formal-zero"] => CubicSheets.checkFormalZero
  | ["--general-zero"] => CubicSheets.checkGeneralZero
  | ["--dyadic-general-zero-request", directory] =>
      CubicSheets.checkDyadicGeneralZeroRequest (System.FilePath.mk directory) false false
  | ["--dyadic-general-zero-request-saved-only", directory] =>
      CubicSheets.checkDyadicGeneralZeroRequest (System.FilePath.mk directory) true false
  | ["--interrupt-dyadic-general-zero-request", directory] =>
      CubicSheets.checkDyadicGeneralZeroRequest (System.FilePath.mk directory) false true
  | ["--general-zero-request"] => CubicSheets.checkGeneralZeroRequest
  | ["--cached-general-zero-request", directory] =>
      CubicSheets.checkCachedGeneralZeroRequest (System.FilePath.mk directory) false false
  | ["--cached-general-zero-request-saved-only", directory] =>
      CubicSheets.checkCachedGeneralZeroRequest (System.FilePath.mk directory) true false
  | ["--interrupt-cached-general-zero-request", directory] =>
      CubicSheets.checkCachedGeneralZeroRequest (System.FilePath.mk directory) false true
  | ["--cached-general-zero-request-indices", directory] =>
      CubicSheets.checkCachedGeneralZeroRequest
        (System.FilePath.mk directory) true false false
  | ["--line-cache"] => CubicSheets.checkLineCache
  | ["--origin-cache"] => CubicSheets.checkOriginCache
  | ["--bounded-word"] => CubicSheets.checkBoundedWord
  | ["--origin-regressions"] => TestPurelib.Polynomial.Approximation.Gaussian.Residual.Origin.check
  | ["--localization-coverage"] => do
      CubicSheets.checkInitialCache
      TestPurelib.Polynomial.RootLocalization.checkCoverage
  | _ => CubicSheets.check
