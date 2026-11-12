module
public import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Data.Gaussian.Basic
public import Purelib.Integration.Program.Gaussian.Exact
import Purelib.Polynomial.Ascending.Gaussian.Basic
import Purelib.Integration.CertifiedProgram
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic

@[expose] public section

/-!
Exact constant integration programs with retained polynomial models.
-/

namespace Purelib.Examples.Integration.Program.Gaussian.Cached.Constant.WorkedExamples

open Purelib.Data
open Purelib.Integration
open Purelib.Polynomial

/-- The certified cached integration program for a supplied Gaussian constant on [0,1]. -/
def program (value :
  Gaussian.Basic.Canonical) : Program.Gaussian.Cached.Basic.CachedProgram :=
  (Program.Gaussian.Basic.RefinementProgram.exactPolynomial 0 1 (Ascending.Gaussian.Basic.constant
    value)).certifiedView.program

end Purelib.Examples.Integration.Program.Gaussian.Cached.Constant.WorkedExamples

end
