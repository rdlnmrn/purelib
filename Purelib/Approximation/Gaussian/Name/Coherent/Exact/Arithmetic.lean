module
import Purelib.Data.Gaussian.Basic
public import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Init.Prelude
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Sequence

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

section
@[expose] public section

/-! # Transporting exact rational provenance through finite arithmetic -/

namespace Purelib.Approximation.Gaussian.Name.Coherent.Exact.Arithmetic

/-- The computed sum of two exact coherent Gaussian names is operationally equivalent to the exact name of their
displayed sum. -/
def exact_add (first second :
  Data.Gaussian.Basic.Canonical) :
    Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.add
        (Coherence.exact first)
        (Coherence.exact second)).name
      (Coherence.exact (first + second)).name :=
  Equivalent.of_constant_samples _ _ (first + second)
    (fun _ => rfl) (fun _ => rfl)

/-- The computed product of two exact coherent Gaussian names is operationally equivalent to the exact name of their
displayed product. -/
def exact_mul (first second :
  Data.Gaussian.Basic.Canonical) :
    Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.mul
        (Coherence.exact first)
        (Coherence.exact second)).name
      (Coherence.exact (first * second)).name :=
  Equivalent.of_constant_samples _ _ (first * second)
    (fun _ => rfl) (fun _ => rfl)
end Purelib.Approximation.Gaussian.Name.Coherent.Exact.Arithmetic

end
