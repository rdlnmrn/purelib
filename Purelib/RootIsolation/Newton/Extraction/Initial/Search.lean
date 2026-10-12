module
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
public import Purelib.RootIsolation.Newton.Search.Iteration
import Purelib.RootIsolation.Refinement.Basic
import Purelib.RootIsolation.State.Raw

import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

/-!
# Checked initial root extraction

The initial positive-winding region can contain several roots.  In particular,
its midpoint may be a critical point even when the polynomial is squarefree.
Try its midpoint and four off-centre seeds before using the total extractor.
These seeds are only proposals: the existing finite checker proves strict
containment, winding four, full-line clearance and the requested accuracy.

No Newton-convergence hypothesis or caller search budget is needed.  Failure
of the bounded shortcut retains the original unconditional finite fallback.
The selected root is whichever checked seed succeeds first; no equality with
the old extractor's ordering of independent roots is asserted.
-/

namespace Purelib.RootIsolation.Newton.Extraction.Initial.Search

/-- Retain the first completely checked root refinement in the supplied seed list.

Each seed supplies the original bounded Newton search. The first accepted
certificate is returned directly; exhaustion returns none without repeating
an accepted iteration or certificate construction. -/
@[expose] public def search {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient
  : Box} {degreeBound :
  Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (current : State.Raw.RawWindingState p ambient)
    (epsilon : Fraction.Rational) : List Gaussian.Basic.Canonical →
    Option (Refinement current epsilon)
  | [] => none
  | center :: rest =>
      match Newton.Search.Iteration.search elimination current epsilon 6 0 center with
      | some accepted => some accepted
      | none => Purelib.RootIsolation.Newton.Extraction.Initial.Search.search elimination current epsilon rest
end Purelib.RootIsolation.Newton.Extraction.Initial.Search
