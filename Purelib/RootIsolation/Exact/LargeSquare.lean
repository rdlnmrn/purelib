module
import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Geometry.Rational.Box.Refinement
public import Purelib.Polynomial.Clearance.Box.Boundary.RootRadius
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Polynomial.Winding.Box.Basic
public import Purelib.Polynomial.Winding.Box.Global
import Purelib.RootIsolation.Exact.Basic
public import Purelib.RootIsolation.Exact.Build

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Data.Nat.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Choice-free exact finite isolation

A finite list of clear constructive-rational regions carries an exact raw
winding total.  Each step selects the first positive region, extracts one
strictly interior Newton band of raw winding four, and replaces the region by
the eight clear cells of its complement.  Global nonnegativity makes exactly
`count` such steps possible when the initial raw winding is `4 * count`.
-/

namespace Purelib.RootIsolation.Exact.LargeSquare

/-- Exact isolation on the coefficient-computed constructive large square. -/
def isolateLargeSquare
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound) :
    Exact.Basic.Output p (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p) p.natDegree := by
  have degreePositive : 0 < p.natDegree :=
    (show (0 : Nat) < 2 by decide).trans_le degreeAtLeastTwo
  let initial : Clearance.Box.Region.ClearRegion p (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p) :=
    { box := Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p
      refinesAmbient := Box.refines_refl
        (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p)
      proper := Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox_proper p
      clearance := Clearance.Box.Boundary.RootRadius.largeSquare_boundaryClearance degreePositive }
  have raw : Winding.Box.Basic.quadrupledBoxWinding p initial.box =
      (4 : Int) * p.natDegree := by
    simpa only [initial] using
      Winding.Box.Global.quadrupledBoxWinding_largeSquare_eq_degree degreePositive
  exact Exact.Build.isolateFromRegion degreeAtLeastTwo squarefree elimination initial
    p.natDegree raw

end Purelib.RootIsolation.Exact.LargeSquare

end

section
@[expose] public section

/-!
# Choice-free degree-sharp maximality

The finite exact-isolation partition assigns every sufficiently refined
winding-one track to one displayed output cell.  Zero-winding remainder cells
cannot own such a track, and a raw-winding-four output cell cannot own two
separated tracks.  All searches below scan finite lists directly.
-/

namespace Purelib.RootIsolation.Exact.LargeSquare

/-- The original large-square isolation output retains the coefficient-computed large square as its exact support. -/
theorem isolateLargeSquare_support
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound) :
    (isolateLargeSquare degreeAtLeastTwo
      squarefree elimination).support =
        Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p := rfl
end Purelib.RootIsolation.Exact.LargeSquare

end
