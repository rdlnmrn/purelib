module
import Purelib.Data.Gaussian.Basic
public import Purelib.Calculus.Jet.Multivariable.First.Basic
public import Purelib.Data.List.Gaussian.Arithmetic

section
@[expose] public section

/-!
# Finite higher, Taylor, directional, and multivariable jets

The one-variable Taylor object below is a wrapper around the repository's
low-to-high finite rational polynomial program.  Repeated differentiation is
structural recursion on a requested natural order.  Multivariable first jets
store a displayed finite list of Gaussian-rational partial coefficients; a
directional coefficient is a finite dot-product recursion.

These are finite tables, not function spaces or infinite formal series.
-/

namespace Purelib.Calculus.Jet.Multivariable.First.Basic
namespace MultivariableFirstJet

open Purelib.Calculus.Jet.Multivariable.First.Basic in
open Purelib.Data.Gaussian in
/-- Form a constant jet with the requested number of zero partial coefficients. -/
def constant (dimension : Nat) (value :
  Basic.Canonical) :
    MultivariableFirstJet :=
  ⟨value, List.replicate dimension 0⟩

section
open Purelib.Calculus.Jet.Multivariable.First.Basic
open Purelib.Data.List.Gaussian
/-- Add values and partial-coefficient lists.

Paired partials are added entrywise; when one list ends, the remaining entries of the other list are retained. -/
def add (left right : MultivariableFirstJet)
  :
    MultivariableFirstJet :=
  ⟨left.value + right.value, Arithmetic.addCoefficients left.partials right.partials⟩

/-- Negate the value and every displayed partial coefficient. -/
def neg (jet : MultivariableFirstJet) :
  MultivariableFirstJet :=
  ⟨-jet.value, Arithmetic.scalePartials (-1) jet.partials⟩

/-- Multiply jets using the finite coordinatewise product rule.

Scale each partial list by the other jet's value, then add the lists with zero-padding semantics for unequal lengths. -/
def mul (left right : MultivariableFirstJet)
  :
    MultivariableFirstJet :=
  ⟨left.value * right.value,
    Arithmetic.addCoefficients
      (Arithmetic.scalePartials right.value left.partials)
      (Arithmetic.scalePartials left.value right.partials)⟩

end

open Purelib.Calculus.Jet.Multivariable.First.Basic in
open Purelib.Data.Gaussian in
open Purelib.Data.List.Gaussian in
/-- Compose a displayed outer value and slope with an inner first jet.

The result retains the supplied outer value and scales every inner partial by the supplied outer slope. No relation
between the supplied outer data and inner value is required by this constructor. -/
def compose (outerValue outerSlope :
  Basic.Canonical)
    (inner : MultivariableFirstJet) : MultivariableFirstJet :=
  ⟨outerValue, Arithmetic.scalePartials outerSlope inner.partials⟩
end MultivariableFirstJet

end Purelib.Calculus.Jet.Multivariable.First.Basic

end
