module

import Purelib.Approximation.Gaussian.Acquisition.Expression.Compile
import Purelib.Approximation.Gaussian.Acquisition.Expression.Normalization
import Purelib.Approximation.Gaussian.Acquisition.Annotated.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Provenance.Rational.Basic
import Purelib.Polynomial.Multivariate.Sparse

/-!
# Distribution over three original opaque channels

The computed constant form supplies exact provenance at the unchanged original
numerical evaluator. No relation between the three inputs is assumed.
-/

namespace TestPurelib.Approximation.Gaussian.ExpressionDistribution

open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Approximation.Gaussian.Acquisition.Expression.Basic
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)
open Purelib.Polynomial.Multivariate (Sparse)

/-- The original opaque annotations at their three independent source indices. -/
private def environment (first second third : CoherentNamed) : Fin 3 → Annotated :=
  Fin.cases (Annotated.opaque first) (Fin.cases (Annotated.opaque second) (fun _ => Annotated.opaque third))

/-- The distributed product difference over the three original indexed inputs. -/
private def distributed : Expr 3 :=
  .sub (.mul (.atom ⟨0, by decide⟩) (.add (.atom ⟨1, by decide⟩) (.atom ⟨2, by decide⟩)))
    (.add (.mul (.atom ⟨0, by decide⟩) (.atom ⟨1, by decide⟩)) (.mul (.atom ⟨0, by decide⟩) (.atom ⟨2, by decide⟩)))

/-- The complete retained compiler and normalizer compute canonical zero for the distributed difference. -/
private theorem distributed_form (first second third : CoherentNamed) :
    (distributed.normalize (environment first second third)).polynomial.form.terms = [] := by
  unfold Expr.normalize Compiled.normalize
  dsimp only
  rewrite [Construction.normalize_form]
  dsimp only [Compiled.bindings]
  change (Sparse.sub
    (Sparse.mul
      (Sparse.atom (⟨0, by decide⟩ : Fin 7))
      (Sparse.add
        (Sparse.atom (⟨1, by decide⟩ : Fin 7))
        (Sparse.atom (⟨2, by decide⟩ : Fin 7))))
    (Sparse.add
      (Sparse.mul
        (Sparse.atom (⟨0, by decide⟩ : Fin 7))
        (Sparse.atom (⟨1, by decide⟩ : Fin 7)))
      (Sparse.mul
        (Sparse.atom (⟨0, by decide⟩ : Fin 7))
        (Sparse.atom (⟨2, by decide⟩ : Fin 7))))).terms = []
  decide +kernel

example (first second third : CoherentNamed) :
    RationalSidecar (distributed.normalize (environment first second third)).compiled.annotation.channel :=
  (distributed.normalize (environment first second third)).polynomial.rational 0 (distributed_form first second third)

example (first second third : CoherentNamed) :
    (distributed.compile (environment first second third)).rationalValue = some 0 :=
  distributed.compile_inferred_value (environment first second third) 0 (by rfl) (distributed_form first second third)

example (first second third : CoherentNamed) :
    (distributed.compile (environment first second third)).channel =
      distributed.denote (environment first second third) :=
  distributed.compile_channel (environment first second third)

end TestPurelib.Approximation.Gaussian.ExpressionDistribution
