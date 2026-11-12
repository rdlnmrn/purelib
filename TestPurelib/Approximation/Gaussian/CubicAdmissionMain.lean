module

import TestPurelib.Approximation.Gaussian.CubicAdmission

open TestPurelib.Approximation.Gaussian

/-- Execute original local cubic acquisition, cached retries and exact-zero classifications in native code. -/
public def main (arguments : List String) : IO Unit := do
  match arguments with
  | ["--identify-conjugate"] =>
      TestPurelib.Approximation.Gaussian.CubicAdmission.checkConjugateIdentification
      return
  | ["--dyadic-inverse-sample", directory] =>
      CubicAdmission.checkDyadicReciprocal (System.FilePath.mk directory) false false
      return
  | ["--dyadic-inverse-sample-saved-only", directory] =>
      CubicAdmission.checkDyadicReciprocal (System.FilePath.mk directory) true false
      return
  | ["--interrupt-dyadic-inverse-sample", directory] =>
      CubicAdmission.checkDyadicReciprocal (System.FilePath.mk directory) false true
      return
  | ["--original-prefix-two", directory] =>
      CubicAdmission.checkOriginalPrefixTwo (System.FilePath.mk directory) false
      return
  | ["--original-prefix-two-saved-only", directory] =>
      CubicAdmission.checkOriginalPrefixTwo (System.FilePath.mk directory) true
      return
  | ["--reconditioned-inverse-sample", directory] =>
      CubicAdmission.checkReconditionedReciprocal (System.FilePath.mk directory) true
      return
  | ["--expanded-polynomial"] =>
      CubicAdmission.checkExpanded
      return
  | ["--reconditioned-inverse-floor", directory] =>
      CubicAdmission.checkReconditionedReciprocal (System.FilePath.mk directory) false
      return
  | ["--cached-inverse-sample", directory] =>
      CubicAdmission.checkCachedReciprocal (System.FilePath.mk directory) false false
      return
  | ["--cached-inverse-sample-saved-only", directory] =>
      CubicAdmission.checkCachedReciprocal (System.FilePath.mk directory) true false
      return
  | ["--interrupt-inverse-sample", directory] =>
      CubicAdmission.checkCachedReciprocal (System.FilePath.mk directory) false true
      return
  | _ => pure ()
  CubicAdmission.check
  CubicAdmission.checkReciprocal (arguments == ["--inverse-sample"])
  CubicAdmission.checkZeroProduct
  CubicAdmission.checkZeroFallback
