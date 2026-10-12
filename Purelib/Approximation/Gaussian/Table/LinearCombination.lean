module
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
public import Purelib.Polynomial.Ascending.Gaussian.Progressive.Coefficients
import Init.Prelude

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Polynomial.Ascending.Gaussian.Progressive

section
@[expose] public section

/-!
# Progressive finite Taylor and multivariable CCL tables

The displayed higher-jet layer stores Gaussian rationals.  Here every entry is
instead a coherent productive CCL channel.  All operations recurse over the
displayed finite coefficient lists, and every resulting table inherits one
computable joint request from `ProgressiveFiniteTable`.
-/

namespace Purelib.Approximation.Gaussian.Table.LinearCombination

/-! ## Displayed finite-arity multivariable channels -/

/-- Add the finite lists of coherent partial coefficients using the existing productive coefficient addition. -/
def addPartials : List CoherentNamed → List
  CoherentNamed → List Coherent.CoherentNamed :=
  Coefficients.addCoefficients

/-- Multiply each finite partial coefficient by the same retained coherent factor. -/
def scalePartials (factor : CoherentNamed)
  (partials : List CoherentNamed) :
    List Coherent.CoherentNamed :=
  Coefficients.scaleCoefficients factor partials

set_option backward.match.sparseCases false in
/-- Sum the products of paired coherent coefficients and exact Gaussian directions.

The recursion consumes the common prefix of the two finite lists and returns exact zero when either remaining list is
empty. -/
def directionalSum : List
  Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed → List Purelib.Data.Gaussian.Basic.Canonical →
  Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
  | coefficient :: coefficients, direction :: directions =>
      Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed.add
        (Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed.mul coefficient
        (Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed.Coherence.exact direction))
        (directionalSum coefficients directions)
  | _, _ => Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed.Coherence.exact 0

end Purelib.Approximation.Gaussian.Table.LinearCombination

end
