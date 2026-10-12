module
import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
public import Purelib.Polynomial.Clearance.Box.Boundary.RootRadius
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
public import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Winding.Box.Global
public import Purelib.Polynomial.Winding.Box.Region.Sum
public import Purelib.RootIsolation.Exact.State
import Mathlib.Data.Nat.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Exact isolation steps from checked extraction checkpoints

Rebuild the numerical fields of an isolation state and retain the original
track constructors.  Equality is to the canonical step, not to an arbitrary
equivalent root family.  Proof-only references to that step disappear from
the executable replay.  This imports only existing finite isolation modules.
-/

namespace Purelib.RootIsolation.Exact.LargeSquare.Region

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound
  : Nat}
variable (degreeAtLeastTwo : 2 ≤ p.natDegree) (squarefree :
  Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
  (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
section Steps

variable (state : Exact.State.IsolationState p ambient)
  (nonnegative : ∀ region ∈ state.regions, 0 ≤ Winding.Box.Basic.quadrupledBoxWinding p region.box)
  (positive : 0 < Winding.Box.Region.Sum.totalRaw state.regions)
end Steps

section Runs

variable {state : Exact.State.IsolationState p ambient}
end Runs

/-- The original coefficient-computed initial region, with its original
boundary bound.  No alternative box or clearance is selected here. -/
def largeSquareRegion : Clearance.Box.Region.ClearRegion p
  (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p) where
  box := Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p
  refinesAmbient := Box.refines_refl _
  proper := Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox_proper p
  clearance := Clearance.Box.Boundary.RootRadius.largeSquare_boundaryClearance
    ((show (0 : Nat) < 2 by decide).trans_le degreeAtLeastTwo)

/-- The original large-square region has raw winding four times the polynomial degree. -/
theorem largeSquareRegion_winding :
    Winding.Box.Basic.quadrupledBoxWinding p (largeSquareRegion degreeAtLeastTwo).box = (4 :
      Int) * p.natDegree :=
  Winding.Box.Global.quadrupledBoxWinding_largeSquare_eq_degree
    ((show (0 : Nat) < 2 by decide).trans_le degreeAtLeastTwo)
end Purelib.RootIsolation.Exact.LargeSquare.Region

end
