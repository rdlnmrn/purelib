module

import Purelib.Data.Rat.Fraction
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
public import Purelib.RootIsolation.Exact.LargeSquare.Region

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Data.Nat.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic

open Purelib.Polynomial.Elimination.Axis.Certificate
open Purelib.Polynomial.Dense.Gaussian

open Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius

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

/-- Isolate all original roots inside a displayed symmetric square at least as large as the coefficient radius.

The original finite extraction run consumes this same square, its computed
boundary clearance and degree winding. The radius may be enlarged to contain
other original input ambients without changing the polynomial owner.
-/
def isolateSymmetric
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Squarefree.Basic.SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination : AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    {radius : Purelib.Data.Rat.Fraction.Rational}
    (radiusLe : Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p ≤ radius)
    (request : Option Data.Rat.Fraction.Rational := none) :
    Exact.Basic.Output p
      (Box.symmetric radius ((Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius_pos p).trans_le radiusLe).le)
      p.natDegree :=
  Exact.Build.isolateFromRegion degreeAtLeastTwo squarefree elimination
    (Region.symmetricRegion degreeAtLeastTwo radiusLe) p.natDegree
    (Region.symmetricRegion_winding degreeAtLeastTwo radiusLe) request

/-- Exact isolation on the coefficient-computed constructive large square. -/
def isolateLargeSquare
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Squarefree.Basic.SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination : AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (request : Option Data.Rat.Fraction.Rational := none) :
    Basic.Output p (Box.largeSquareBox p) p.natDegree := by
  have degreePositive : 0 < p.natDegree :=
    (show (0 : Nat) < 2 by decide).trans_le degreeAtLeastTwo
  let initial : Clearance.Box.Region.ClearRegion p (Box.largeSquareBox p) :=
    { box := Box.largeSquareBox p
      refinesAmbient := Box.refines_refl
        (Box.largeSquareBox p)
      proper := Box.largeSquareBox_proper p
      clearance := Clearance.Box.Boundary.RootRadius.largeSquare_boundaryClearance degreePositive }
  have raw : Winding.Box.Basic.quadrupledBoxWinding p initial.box =
      (4 : Int) * p.natDegree := by
    simpa only [initial] using
      Winding.Box.Global.quadrupledBoxWinding_largeSquare_eq_degree degreePositive
  exact Build.isolateFromRegion degreeAtLeastTwo squarefree elimination initial
    p.natDegree raw request

/-- Each coefficient-square isolation track retains its actual complete original Newton constructor. -/
theorem isolateLargeSquare_tracks_origin
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Squarefree.Basic.SquarefreeCertificate p) {degreeBound : Nat}
    (elimination : AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (request : Option Data.Rat.Fraction.Rational) :
    ∀ track ∈ (isolateLargeSquare degreeAtLeastTwo squarefree elimination request).tracks,
      Track.Newton.Build.Origin degreeAtLeastTwo squarefree elimination track := by
  dsimp only [isolateLargeSquare]
  exact Build.isolateFromRegion_tracks_origin degreeAtLeastTwo squarefree elimination _ _ _ request

/-- A degree-indexed original coefficient-square root uses that same cached elimination refiner pointwise. -/
theorem isolateLargeSquare_trackAt_refine
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Squarefree.Basic.SquarefreeCertificate p) {degreeBound : Nat}
    (elimination : AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (request : Option Data.Rat.Fraction.Rational) (index : Fin p.natDegree)
    (current : State.WindingOne.Basic.WindingOneState p (Box.largeSquareBox p))
    (epsilon : Data.Rat.Fraction.Rational) (positive : 0 < epsilon) :
    ((isolateLargeSquare degreeAtLeastTwo squarefree elimination request).trackAt index).refine
      current epsilon positive =
      Track.Newton.Refinement.refineState degreeAtLeastTwo squarefree elimination current epsilon positive := by
  dsimp only [isolateLargeSquare]
  exact Build.isolateFromRegion_trackAt_refine degreeAtLeastTwo squarefree elimination _ _ _ request
    index current epsilon positive

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

/-- Every original large-square isolation track retains the exact Newton refinement function. -/
theorem isolateLargeSquare_refine
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Squarefree.Basic.SquarefreeCertificate p) {degreeBound : Nat}
    (elimination : AxisSafeCuts.AxisEliminationCertificate p degreeBound) :
    ∀ track ∈ (isolateLargeSquare degreeAtLeastTwo squarefree elimination).tracks,
      track.refine = Track.Newton.Refinement.refineState degreeAtLeastTwo squarefree elimination := by
  apply Build.isolateFromRegion_refine
  exact Winding.Box.Global.quadrupledBoxWinding_largeSquare_eq_degree
    ((show (0 : Nat) < 2 by decide).trans_le degreeAtLeastTwo)

/-- The original large-square isolation output retains the coefficient-computed large square as its exact support. -/
theorem isolateLargeSquare_support
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Squarefree.Basic.SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination : AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (request : Option Data.Rat.Fraction.Rational := none) :
    (isolateLargeSquare degreeAtLeastTwo
      squarefree elimination request).support =
        Box.largeSquareBox p := rfl
end Purelib.RootIsolation.Exact.LargeSquare

end
