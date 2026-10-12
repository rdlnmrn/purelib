module
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Table.Exact
import Purelib.Data.Gaussian.RationalEmbedding
public import Purelib.Polynomial.Ascending.Gaussian.Progressive.Table
public import Purelib.Polynomial.Ascending.Rational.Jet.Basic
import Purelib.Approximation.Gaussian.Table.Basic
import Purelib.Approximation.Gaussian.Table.Request
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Ascending.Gaussian.Progressive.Basic

open Purelib.Polynomial.Ascending.Gaussian.Progressive.Basic (TaylorJet)

open Purelib.Approximation.Gaussian

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Progressive finite Taylor and multivariable CCL tables

The displayed higher-jet layer stores Gaussian rationals.  Here every entry is
instead a coherent productive CCL channel.  All operations recurse over the
displayed finite coefficient lists, and every resulting table inherits one
computable joint request from `ProgressiveFiniteTable`.
-/

namespace Purelib.Polynomial.Ascending.Gaussian.Progressive.Basic.TaylorJet
section

/-- Exact specialization of the already proved displayed rational Taylor
table. -/
def ofDisplayed (jet :
  Ascending.Rational.Jet.Basic.TaylorJet) : TaylorJet :=
  ⟨jet.coefficients.map (fun value => Name.Coherent.CoherentNamed.Coherence.exact
    (TaylorJet.coordinateGaussian value))⟩

open Purelib.Data.List in
/-- Every same-budget centre of an exact specialization is literally the
corresponding displayed coefficient. -/
theorem ofDisplayed_requestCenters
    (jet : Ascending.Rational.Jet.Basic.TaylorJet) (target : Fraction.Rational)
    (positive : 0 < target) :
    (ofDisplayed jet).table.requestCenters target positive =
      jet.coefficients.map TaylorJet.coordinateGaussian := by
  simpa only [ofDisplayed,
    TaylorJet.table,
    Table.Basic.ChannelTable.exact, Map.map_map,
    Function.comp_def] using
      Table.Basic.ChannelTable.exact_requestCenters
        (jet.coefficients.map TaylorJet.coordinateGaussian) target positive

end

end Purelib.Polynomial.Ascending.Gaussian.Progressive.Basic.TaylorJet

end
