module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Residual
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Squarefree
public import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Threshold
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
public import Purelib.Polynomial.Winding.Box.Newton.Prepare.Squarefree
public import Purelib.RootIsolation.Newton.Refinement.Basic
import Purelib.RootIsolation.State.Raw
public import Purelib.RootIsolation.Subdivision.Raw.Request
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Basic

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic (SquarefreeCertificate)
open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)
open Purelib.RootIsolation.State.Raw (RawWindingState)

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Choice-free refinement to a certified Newton point

The raw nonzero-winding subdivision is iterated to a coefficient-computed
positive diagonal threshold.  Its explicit contraction bound then supplies
the small residual required by the finite Bézout derivative argument.
-/

namespace Purelib.RootIsolation.Newton.Refinement.Build

/-- Deterministically refine raw winding until the Newton residual threshold
is guaranteed. -/
def refineForNewton
    {p : CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (squarefree : SquarefreeCertificate p)
    (state : RawWindingState p ambient) : RawWindingState p ambient :=
  Subdivision.Raw.Request.refineTo elimination state
    (Dense.Gaussian.Newton.Box.Threshold.newtonDiagonalThreshold p ambient squarefree)

/-- Refinement to the Newton threshold preserves containment in the original input box. -/
theorem refineForNewton_refines
    {p : CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (squarefree : SquarefreeCertificate p)
    (state : RawWindingState p ambient) :
    (refineForNewton elimination squarefree state).box.Refines state.box :=
  Subdivision.Raw.Request.refineTo_refines elimination state
    (Dense.Gaussian.Newton.Box.Threshold.newtonDiagonalThreshold p ambient squarefree)

/-- The retained Newton-preparation box has anchor residual bound at most the original squarefree derivative threshold.
-/
theorem refineForNewton_residualBound_le
    {p : CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (squarefree : SquarefreeCertificate p)
    (state : RawWindingState p ambient) :
    Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p ambient
        (refineForNewton elimination squarefree state).box ≤
      Dense.Gaussian.Derivative.Separation.Squarefree.derivativeThreshold squarefree ambient := open Purelib.Data.Rat in
        by
  let refined := refineForNewton elimination squarefree state
  have diagonal := Subdivision.Raw.Request.refineTo_diagonalSq_le elimination state
    (Dense.Gaussian.Newton.Box.Threshold.newtonDiagonalThreshold_pos p ambient squarefree)
  have lipschitzPositive := Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos p ambient
  have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    diagonal lipschitzPositive.le
  change Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient * refined.box.diagonalSq ≤
    Dense.Gaussian.Derivative.Separation.Squarefree.derivativeThreshold squarefree ambient
  calc
    Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient * refined.box.diagonalSq ≤
        Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient *
          Dense.Gaussian.Newton.Box.Threshold.newtonDiagonalThreshold p ambient squarefree := scaled
    _ = Dense.Gaussian.Derivative.Separation.Squarefree.derivativeThreshold squarefree ambient := by
      rw [Fraction.Field.mul_comm]
      exact Fraction.Field.div_mul_cancel_of_ne
        (Dense.Gaussian.Derivative.Separation.Squarefree.derivativeThreshold squarefree ambient)
        (Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient) (ne_of_gt lipschitzPositive)

/-- One finite raw subdivision followed by the certified local Newton step. -/
def extractNewton
    {p : CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (degreePositive : 0 < p.natDegree)
    (elimination : AxisEliminationCertificate p degreeBound)
    (squarefree : SquarefreeCertificate p)
    (state : RawWindingState p ambient) : Newton.Refinement.Basic.Output p ambient squarefree := by
  let refined := refineForNewton elimination squarefree state
  exact
    { state := refined
      newton := Winding.Box.Newton.Prepare.Squarefree.computeNewtonCenterOfRawWinding p degreePositive squarefree
        refined.refinesAmbient refined.proper refined.rawWinding_ne
        (refineForNewton_residualBound_le elimination squarefree state) }

end Purelib.RootIsolation.Newton.Refinement.Build

end
