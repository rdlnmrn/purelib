module
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Separated
public import Purelib.Polynomial.Winding.Box.Basic
import Purelib.RootIsolation.Newton.Restart.Anchored.Seed
import Purelib.RootIsolation.Newton.Restart.Uniform.Anchored
public import Purelib.RootIsolation.Newton.Restart.Uniform.Budget
import Purelib.RootIsolation.State.WindingOne.Count

import Purelib.Data.Rat.Fraction.Order
public import Purelib.Polynomial.Clearance.Box.Region
import Purelib.Tactic.QuotientFreeOmega
import Purelib.RootIsolation.Newton.Restart.Seed.State
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Uniform polynomial clearance on a zero-winding rectangle

A sufficiently small rational residual in a protected rectangle constructs a
strictly interior winding-one state.  Global nonnegativity would then force
the parent winding to be at least four.  A zero-winding parent therefore has
the point-independent positive residual target as a lower bound everywhere,
including its boundary.  Only the finite target is executable output; the
hypothetical Newton extraction and elimination are confined to the proof.
-/

namespace Purelib.Polynomial.Clearance.Box.Region

namespace RegionClearance

variable {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box}

/-- Construct full-box clearance from the finite zero-winding certificate.
The radius cap is the fixed positive rational one; the residual constructor
internally pays the box geometry, derivative, and Taylor bounds. -/
def ofZeroWinding {ambient : Box}
  (degreeAtLeastTwo : 2 ≤ p.natDegree) (nonzero : p.isZero = false)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (current : Clearance.Box.Region.ProtectedAmbient p ambient)
    (zero : Winding.Box.Basic.quadrupledBoxWinding p current.box = 0) : Clearance.Box.Region.RegionClearance p
      current.box where
  bound := Newton.Restart.Uniform.Budget.uniformAnchoredResidualTarget squarefree current 1
  positive := Newton.Restart.Uniform.Budget.uniformAnchoredResidualTarget_pos squarefree current (by decide)
  lower := by
    intro point inside
    apply le_of_not_gt
    intro small
    have localized := Purelib.RootIsolation.Newton.Restart.Uniform.Anchored.uniform_residual_strict_and_anchored
      squarefree current point inside
      (show (0 : Fraction.Rational) < 1 by decide) small
    let elimination := Purelib.Polynomial.Elimination.Axis.Separated.separatedAxisEliminationCertificate p nonzero
      ((show 0 < 2 by decide).trans_le degreeAtLeastTwo)
    let seed := Purelib.RootIsolation.Newton.Restart.Anchored.Seed.seedOfResidual squarefree elimination current point
      localized.1
      (show (0 : Fraction.Rational) < 1 by decide) localized.2
    let region : Clearance.Box.Region.ClearRegion p ambient :=
      ⟨current.box, current.refinesAmbient, current.proper, current.clearance⟩
    have positiveWinding := Purelib.RootIsolation.State.WindingOne.Count.region_rawWinding_ge_four_of_strictInterior
      degreeAtLeastTwo squarefree elimination (seed.state degreeAtLeastTwo) region (seed.state_strict_current
        degreeAtLeastTwo)
    change 4 ≤ Winding.Box.Basic.quadrupledBoxWinding p current.box at positiveWinding
    rw [zero] at positiveWinding
    omega

end RegionClearance

end Purelib.Polynomial.Clearance.Box.Region

end
