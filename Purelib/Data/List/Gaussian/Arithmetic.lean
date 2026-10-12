module
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Field

open Purelib.Data.Gaussian.Basic

section
@[expose] public section

/-!
# Coefficient algebra for finite Gaussian polynomial integration

All equalities are proved from finite coefficient lists.  In particular,
coefficient equality is not obtained by testing a polynomial on an infinite
carrier.  This small layer supplies the algebraic FTC used by generated path
subdivisions; it adds no analytic or antiderivative certificate assumptions.
-/

namespace Purelib.Data.List.Gaussian.Arithmetic

/-- Add two finite Gaussian-rational lists entrywise, retaining the longer remainder.

The recursion adds paired heads. Once either input is empty it returns the other tail
unchanged, as addition of zero-padded coefficient lists. -/
def addCoefficients : List Canonical → List Canonical → List Canonical
  | [], right => right
  | left, [] => left
  | left :: leftTail, right :: rightTail =>
      (left + right) :: addCoefficients leftTail rightTail
end Purelib.Data.List.Gaussian.Arithmetic

end

end

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

namespace Purelib.Data.List.Gaussian.Arithmetic

/-- Multiply every entry of a retained Gaussian-rational list by one displayed factor. -/
def scalePartials (factor : Canonical) (partials : List Canonical) :
    List Canonical :=
  partials.map (factor * ·)

end Purelib.Data.List.Gaussian.Arithmetic

end
