module

import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Ascending.Gaussian.Basic
import Purelib.Polynomial.Ascending.Gaussian.Evaluation
public import Purelib.Polynomial.Ascending.Gaussian.Integral

public import Purelib.Polynomial.Ascending.Gaussian.Restriction.Basic
import Purelib.Polynomial.Ascending.Gaussian.Restriction.Integral
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Cached Gaussian polynomial restrictions

A source polynomial and two original endpoints index a retained restricted
polynomial and exact unit-parameter integral. Cache identities, evaluation,
transport and adjacent splitting concern those exact stored data.
-/

namespace Purelib.Polynomial.Ascending.Gaussian.Restriction

open Purelib.Data
open Purelib.Polynomial

public section
open Purelib.Data.Gaussian.Basic.Canonical

set_option genInjectivity false in
/-- Retain the compiled child polynomial and its exact unit-parameter integral.

The source and endpoints index this original cache. Specification equalities
identify its stored polynomial and sample with the exact finite calculations;
readback and transport consume those same stored values. -/
structure Cached (source : CoefficientPolynomial) (start finish : Gaussian.Basic.Canonical) where
  /-- The cached affine restriction of the original source polynomial. -/ polynomial :
    CoefficientPolynomial
  /-- The cached polynomial equals the canonical restriction at the retained source endpoints. -/ polynomial_eq :
    polynomial = Ascending.Gaussian.Restriction.Basic.restrict source start finish
  /-- The cached integral of the stored restricted polynomial over the unit parameter interval. -/ sample :
    Gaussian.Basic.Canonical
  /-- The stored sample equals the exact unit-interval integral of the stored polynomial. -/ sample_eq : sample =
    Ascending.Gaussian.Integral.definiteIntegral polynomial 0 1

constructive_injectivity Cached

namespace Cached.mk

end Cached.mk

namespace Cached.mk

end Cached.mk

namespace Cached

/-- Compile and cache the canonical restriction and its unit-interval integral.

The source and endpoints remain indices of the result, and both specification fields identify the stored data with their
exact finite calculations. -/
@[expose] def canonical (source : CoefficientPolynomial) (start finish :
  Gaussian.Basic.Canonical) : Cached source start finish :=
  let polynomial := Ascending.Gaussian.Restriction.Basic.restrict source start finish
  { polynomial := polynomial
    polynomial_eq := rfl
    sample := Ascending.Gaussian.Integral.definiteIntegral polynomial 0 1
    sample_eq := rfl }

end Cached

namespace Cached

/-- Evaluate the cached restriction at the affine image of its retained source endpoints. -/
theorem eval_eq {source : CoefficientPolynomial} {start finish : Gaussian.Basic.Canonical}
    (restriction : Cached source start finish) (input : Gaussian.Basic.Canonical) :
    Ascending.Gaussian.Evaluation.eval restriction.polynomial input = Ascending.Gaussian.Evaluation.eval source (start +
      (finish - start) * input) := by
  rw [restriction.polynomial_eq, Ascending.Gaussian.Restriction.Basic.eval_restrict]

end Cached

namespace Cached

/-- The endpoint displacement times the cached unit-interval sample equals the source integral.

The displacement supplies the affine factor once; the identity holds for repeated or reversed endpoints. -/
theorem transported_sample {source : CoefficientPolynomial} {start finish :
  Gaussian.Basic.Canonical}
    (restriction : Cached source start finish) :
    (finish - start) * restriction.sample = Ascending.Gaussian.Integral.definiteIntegral source start finish := by
  rw [restriction.sample_eq, restriction.polynomial_eq,
    Ascending.Gaussian.Restriction.Integral.definiteIntegral_restrict]

end Cached

namespace Cached

/-- Adjacent cached restrictions telescope for arbitrary displayed endpoints. -/
theorem split_samples {source : CoefficientPolynomial} {start cut finish :
  Gaussian.Basic.Canonical}
    (left : Cached source start cut) (right : Cached source cut finish) :
    (cut - start) * left.sample + (finish - cut) * right.sample =
      Ascending.Gaussian.Integral.definiteIntegral source start finish := by
  rw [left.transported_sample, right.transported_sample,
    ← Ascending.Gaussian.Integral.definiteIntegral_concat source start cut finish]

end Cached

end

end Purelib.Polynomial.Ascending.Gaussian.Restriction
