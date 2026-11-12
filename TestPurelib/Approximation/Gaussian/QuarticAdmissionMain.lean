module

import TestPurelib.Approximation.Gaussian.QuarticAdmission

open TestPurelib.Approximation.Gaussian

/-- Execute the original positive quadratic sum and independent local quartic comparison in native code. -/
public def main (arguments : List String) : IO Unit := do
  match arguments with
  | ["--identify"] =>
      TestPurelib.Approximation.Gaussian.QuarticAdmission.checkIdentification
      return
  | ["--correlated"] =>
      TestPurelib.Approximation.Gaussian.QuarticAdmission.checkCorrelation
      return
  | ["--dyadic-cached-compare", directory] =>
      QuarticAdmission.checkDyadicCachedRequests (System.FilePath.mk directory) false false
      return
  | ["--dyadic-cached-compare-saved-only", directory] =>
      QuarticAdmission.checkDyadicCachedRequests (System.FilePath.mk directory) true false
      return
  | ["--interrupt-dyadic-cached-compare", directory] =>
      QuarticAdmission.checkDyadicCachedRequests (System.FilePath.mk directory) false true
      return
  | ["--cached-compare", directory] =>
      QuarticAdmission.checkCachedRequests (System.FilePath.mk directory) false false
      return
  | ["--cached-compare-saved-only", directory] =>
      QuarticAdmission.checkCachedRequests (System.FilePath.mk directory) true false
      return
  | ["--interrupt-cached-compare", directory] =>
      QuarticAdmission.checkCachedRequests (System.FilePath.mk directory) false true
      return
  | _ => pure ()
  QuarticAdmission.check
  if arguments == ["--compare"] then QuarticAdmission.checkRequests
