module

meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Approximation.Gaussian.Name.Coherent.State
import Purelib.Data.Gaussian.Basic
public import Purelib.Polynomial.Dense.Basic
public import Purelib.Data.Gaussian.Field
import Purelib.Data.List.DropWhile.Basic
import Purelib.Data.List.Map

open Purelib.Approximation.Gaussian
open Purelib.Data
open Purelib.Polynomial

/-!
# Retained coherent coefficient tables for monic Gaussian polynomials

The original ordered coefficient states determine their current values and the
monic polynomial with those non-leading coefficients. Direct finite certificates
retain normalization and the same coefficient count as its natural degree.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table

set_option genInjectivity false in
/-- A displayed finite table of the non-leading coefficients of a monic
polynomial.  Coefficients are stored in the same high-to-low order as the RFAP
dense polynomial implementation.

Each retained state supplies the current Gaussian value and its certified
allowance. The original list order is the high-to-low order of the monic
polynomial's non-leading coefficients. -/
public structure CoefficientTable where
  /-- The retained finite coefficient states, ordered from highest to lowest non-leading degree. -/ entries : List
    Approximation.Gaussian.Name.Coherent.State.CoefficientState

constructive_injectivity CoefficientTable

namespace CoefficientTable

/-- The number of non-leading coefficient states in the monic table. -/
@[expose] public def degree (table : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable) : Nat :=
  table.entries.length

/-- Read the exact current Gaussian value of each retained coefficient state.

Project the current Gaussian value of each original retained state.
The finite map preserves every coefficient position and occurrence. -/
@[expose] public def values (table : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable) : List
  Gaussian.Basic.Canonical :=
  table.entries.map Approximation.Gaussian.Name.Coherent.State.CoefficientState.value

/-- The monic Gaussian-rational polynomial read from the retained coefficient states.

Its descending coefficient list is one followed by the current table values. -/
@[expose] public def polynomial (table : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable) :
  (Dense.Basic.DensePolynomial Gaussian.Basic.Canonical) :=
  ⟨1 :: table.values⟩

/-- The monic polynomial read from a table is already normalized.

The first coefficient is the nonzero Gaussian one. The leading-prefix
scan therefore retains that entry and the complete ordered table values. -/
public theorem polynomial_normalized (table : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable) :
    table.polynomial.normalize = table.polynomial := by
  apply Dense.Basic.DensePolynomial.ext
  change ((1 :: table.values).dropWhile
    (fun value : Gaussian.Basic.Canonical => decide (value = 0))) = 1 :: table.values
  exact List.DropWhile.cons_of_false
    (fun value : Gaussian.Basic.Canonical => decide (value = 0)) 1 table.values
    (decide_eq_false Gaussian.BoundaryCanonical.one_ne_zero)

/-- The number of current coefficient values equals the table degree.

Every retained state contributes one current value. The structural map
preserves the original list length, which is the table's displayed degree. -/
@[simp] public theorem values_length (table : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable) :
    table.values.length = table.degree := by
  exact List.Map.length_map Name.Coherent.State.CoefficientState.value table.entries

/-- The polynomial read from a table has exactly the displayed table degree.

The monic coefficient list is already normalized. Its initial one adds
one entry before the original degree-many values; the natural degree
subtracts that same leading entry. -/
@[simp] public theorem polynomial_natDegree (table : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable) :
    table.polynomial.natDegree = table.degree := by
  change table.polynomial.normalize.coeffs.length - 1 = table.degree
  rewrite [table.polynomial_normalized]
  change table.values.length + 1 - 1 = table.degree
  rewrite [table.values_length]
  exact Eq.refl _

end CoefficientTable

namespace ExplicitLegendreConnectors

/-- The existing finite table of non-leading coefficient states for a monic Gaussian polynomial. -/
public abbrev CoefficientTable :=
  Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable

end ExplicitLegendreConnectors

namespace ExplicitLegendreFrame

/-- The existing finite table of non-leading coefficient states for a monic Gaussian polynomial. -/
public abbrev CoefficientTable :=
  Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable

end ExplicitLegendreFrame

namespace ExplicitLegendreSegment

/-- The existing finite table of non-leading coefficient states for a monic Gaussian polynomial. -/
public abbrev CoefficientTable :=
  Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable

end ExplicitLegendreSegment

namespace ExplicitLegendreZeroLoop

/-- The existing finite table of non-leading coefficient states for a monic Gaussian polynomial. -/
public abbrev CoefficientTable :=
  Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable

end ExplicitLegendreZeroLoop

end Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
