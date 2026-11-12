module

import Purelib.Polynomial.Multivariate.Renaming
import Purelib.Polynomial.Multivariate.Gaussian.Renaming
import Purelib.Polynomial.Multivariate.Sparse
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Equivalence

/-!
# Finite variable renaming regressions

Permutation and collision checks inspect the actual computed coefficients.
Operational soundness transports explicit comparisons of retained original
channels; a collision is justified by supplied channel evidence.
-/

namespace TestPurelib.Polynomial.MultivariateRenaming

open Purelib.Polynomial.Multivariate
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

/-- Exchange the two original bounded variable indices. -/
private def exchange : Fin 2 → Fin 2 := Fin.cases 1 (fun _ => 0)

/-- Identify two formal variables at a supplied common bounded target position. -/
private def identify : Fin 2 → Fin 1 := fun _ => 0

/-- The formal difference of two distinct original variables. -/
private def difference : Sparse Canonical 2 := Sparse.sub (Sparse.atom 0) (Sparse.atom 1)

example : ((Sparse.atom 0 : Sparse Canonical 2).rename exchange).terms =
    (Sparse.atom 1 : Sparse Canonical 2).terms := by decide

example : (difference.rename identify).terms = [] := by decide

example (environment : Fin 1 → Canonical) :
    (difference.rename identify).eval environment = difference.eval (fun index => environment (identify index)) :=
  difference.eval_rename identify environment

example (input : CoherentNamed) :
    NamedEquivalent ((difference.rename identify).denote (fun _ => input)).name
      (difference.denote (fun _ => input)).name :=
  difference.denote_rename identify (fun _ => input) (fun _ => input) (fun _ => NamedEquivalent.refl _)

end TestPurelib.Polynomial.MultivariateRenaming
