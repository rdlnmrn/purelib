module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Polygon.Chain
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Winding.Polygon.Basic
public import Purelib.Polynomial.Winding.Polygon.Phase
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Polynomial

section
@[expose] public section

/-!
# Constructive winding on finite closed polygonal walks

The box winding developed earlier is sufficient for root counting, but a
finite monodromy calculation also has to follow one displayed rational sample
through a finite chain of owner boxes.  The resulting trace is a polygonal
walk rather than the boundary of one rectangle.

This file folds the existing affine-edge Cauchy index over an explicit list
of rational Gaussian vertices.  Product and Rouché endpoint corrections are
kept locally and telescope only because the list is explicitly closed.  No
completed curve, limiting path, or topological winding construction occurs.
-/

namespace Purelib.Polynomial.Winding.Polygon

/-! ## Explicit normalization certificates -/

set_option genInjectivity false in
/-- A finite certificate that the raw Cauchy-index sum is four times an
ordinary integer winding.  The equality is decidable from the displayed
vertices; recording it avoids importing a completed-curve degree theorem. -/
structure Normalized
    (p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (base : Gaussian.Basic.Canonical)
    (vertices : List Gaussian.Basic.Canonical) where
  /-- The retained integer winding of the closed polygon. -/ winding : Int
  /-- The computed closed raw index equals four times the retained integer winding. -/ raw_eq :
    Winding.Polygon.Basic.closedRaw p base vertices = 4 * winding

constructive_injectivity Normalized

namespace Normalized

/-- Kernel-checkable constructor for an already displayed integer candidate. -/
def ofCheck
    (p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (base : Gaussian.Basic.Canonical)
    (vertices : List Gaussian.Basic.Canonical) (winding : Int)
    (checked : decide (Winding.Polygon.Basic.closedRaw p base vertices = 4 * winding) = true) :
    Normalized p base vertices where
  winding := winding
  raw_eq := by exact of_decide_eq_true checked

end Normalized

namespace Normalized

/-- A closed chain of explicitly nonvanishing rational edges is normalized
without any appeal to a completed curve: its finite endpoint phases telescope
and leave four times the accumulated integer turn count. -/
def ofPhaseFormula
    (p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (base : Gaussian.Basic.Canonical)
    (vertices : List Gaussian.Basic.Canonical)
    (formula : Winding.Polygon.Phase.ClosedPhaseFormula p base vertices) :
    Normalized p base vertices where
  winding := formula.turns
  raw_eq := by
    unfold Winding.Polygon.Basic.closedRaw
    rw [formula.raw_eq, Purelib.Geometry.Rational.Polygon.Chain.terminal_append_singleton]
    ring1

end Normalized

end Purelib.Polynomial.Winding.Polygon

end
