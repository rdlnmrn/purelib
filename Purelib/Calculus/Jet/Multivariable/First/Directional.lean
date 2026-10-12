module
import Purelib.Data.Gaussian.Basic
import Purelib.Calculus.Jet.Multivariable.First.Basic
import Purelib.Data.List.Gaussian.Arithmetic
public import Purelib.LinearAlgebra.List.Gaussian.Dot
public import Purelib.Calculus.Jet.Multivariable.First.Arithmetic

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

section
open Purelib.Calculus.Jet.Multivariable.First.Basic
open Purelib.Data.Gaussian
/-- The direction list has exactly as many coordinates as the jet has partials. -/
def DirectionValid (jet :
  MultivariableFirstJet)
    (direction : List Basic.Canonical) : Prop :=
  direction.length = jet.dimension

section
open Purelib.LinearAlgebra.List.Gaussian
/-- Compute a directional coefficient by finite Gaussian dot product.

The recursion pairs displayed partials with direction entries and stops when either list ends. It does not require
DirectionValid evidence. -/
def directional (jet :
  MultivariableFirstJet)
    (direction : List Basic.Canonical) : Basic.Canonical :=
  Dot.dot jet.partials direction

/-- Taking a directional coefficient commutes with addition of first jets.

The identity holds for arbitrary finite direction and partial lists, including unequal lengths under the retained list
arithmetic conventions. -/
theorem directional_add (left right :
  MultivariableFirstJet)
    (direction : List Basic.Canonical) :
    (left.add right).directional direction =
      left.directional direction + right.directional direction :=
  Dot.dot_addPartials left.partials right.partials direction

end

open Purelib.Data.List.Gaussian in
open Purelib.LinearAlgebra.List.Gaussian in
/-- The directional coefficient of a product obeys the finite product rule.

Each jet's directional coefficient is multiplied by the other value; no equality of list dimensions is required. -/
theorem directional_mul (left right :
  MultivariableFirstJet)
    (direction : List Basic.Canonical) :
    (left.mul right).directional direction =
      right.value * left.directional direction +
        left.value * right.directional direction := by
  change Dot.dot
      (Arithmetic.addCoefficients
        (Arithmetic.scalePartials right.value left.partials)
        (Arithmetic.scalePartials left.value right.partials)) direction =
    right.value * Dot.dot left.partials direction +
      left.value * Dot.dot right.partials direction
  rw [Dot.dot_addPartials,
    Dot.dot_scalePartials, Dot.dot_scalePartials]

open Purelib.LinearAlgebra.List.Gaussian in
/-- Composition multiplies the inner directional coefficient by the supplied outer slope. -/
theorem directional_compose (outerValue
  outerSlope : Basic.Canonical)
    (inner : MultivariableFirstJet) (direction : List Basic.Canonical) :
    (inner.compose outerValue outerSlope).directional direction =
      outerSlope * inner.directional direction :=
  Dot.dot_scalePartials outerSlope inner.partials direction

end

end MultivariableFirstJet

end Purelib.Calculus.Jet.Multivariable.First.Basic

end
