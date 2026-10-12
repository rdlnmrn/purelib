module

import Purelib.Data.CCL.Transducer.Machine.Advance
public import Purelib.Data.CCL.Transducer.Machine.Semantics.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
import Purelib.RootIsolation.Progressive.Chamber.Basic
public import Purelib.RootIsolation.Progressive.Closure.Basic
import Purelib.Tactic.Ring
public import Purelib.Approximation.Gaussian.Name.CCL.Output
import Purelib.RootIsolation.Progressive.Continuation.CCL.Output
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.RootIsolation.Progressive.Continuation.Approximation
import Purelib.RootIsolation.Progressive.Continuation.Basic

open Purelib.Data.CCL.Transducer (Machine)

open Purelib

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.RootIsolation.Progressive.Closure.Basic
open Purelib.Data.Gaussian
namespace EffectiveAlgebraicClosure

/-- Every finite prefix of a retained root name has exact raw-parser semantics for the same continuation process. -/
theorem roots_exact
    {reference : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {chamber :
      Progressive.Chamber.Basic.SimpleRootChamber reference}
    (closure : Progressive.Closure.Basic.EffectiveAlgebraicClosure chamber)
    (index : Fin reference.degree) (count : Nat) :
    Data.CCL.Transducer.Machine.Semantics.Basic.ExactCursor
      (closure.continuation.toProcess index) closure.continuation.initial
      (Machine.Advance.advance
        (closure.roots index).machine count) := by
  rw [closure.roots_eq]
  exact closure.continuation.rootNameAt_exact index count
end EffectiveAlgebraicClosure

end Purelib.RootIsolation.Progressive.Closure.Basic

end

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.RootIsolation.Progressive.Closure.Basic
open Purelib.Data.Gaussian
namespace EffectiveAlgebraicClosure

/-- Every retained root name emits exactly the requested number of bits extending its initial word. -/
theorem roots_productive
    {reference : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {chamber :
      Progressive.Chamber.Basic.SimpleRootChamber reference}
    (closure : Progressive.Closure.Basic.EffectiveAlgebraicClosure chamber)
    (index : Fin reference.degree) (count : Nat) :
    (closure.roots index).machine.emitted.IsPrefix
        (Machine.Advance.advance
          (closure.roots index).machine count).emitted ∧
      (Machine.Advance.advance
          (closure.roots index).machine count).emitted.length = count := by
  rw [closure.roots_eq]
  exact closure.continuation.rootNameAt_productive index count
end EffectiveAlgebraicClosure

end Purelib.RootIsolation.Progressive.Closure.Basic

end
