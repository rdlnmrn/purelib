module
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Process.Normalization.Decision
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Enclosure.Ball.Apart
import Purelib.Approximation.Gaussian.Enclosure.Ball.Data
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Data.Bounds
import Purelib.Approximation.Gaussian.Enclosure.Sector.Large
import Purelib.Approximation.Gaussian.Process.Basic
public import Purelib.Approximation.Gaussian.Process.Gamma.Downscale
public import Purelib.Approximation.Gaussian.Process.Gamma.Inverse.Scale
import Purelib.Approximation.Gaussian.Process.Normalization.Basic
public import Purelib.Approximation.Gaussian.Process.Normalization.Data
import Purelib.Data.CCL.Encoding.Padding.Residual
import Purelib.Data.Gaussian.Basic

import Purelib.Data.Gaussian.Norm.Comparison
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Enclosure.Ball

open Purelib.Approximation.Gaussian.Enclosure

open Purelib.Approximation.Gaussian.Enclosure.Ball.Data

open Purelib.Approximation.Gaussian.Enclosure.Sector

open Purelib.Approximation.Gaussian.Process.Gamma

open Purelib.Approximation.Gaussian.Process.Gamma.Inverse

open Purelib.Approximation.Gaussian.Process.Normalization

open Purelib.Approximation.Gaussian.Process.Normalization.Data

open Purelib.Data.CCL.Encoding.Padding

open Purelib.Data.Gaussian.Basic.Canonical.Norm

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Projection from the finite replay controller to certified execution

The relation is proof-facing only.  Its process and source-index map never
enter the executable replay state.  Chart constructors derive the relation
from the original cached program; clients do not supply a simulation oracle.
-/

namespace Purelib.Approximation.Gaussian.Process.Normalization.Data.Correspondence.Domain

open Purelib.Data.Gaussian.Basic.Canonical
namespace CursorRep
end CursorRep

/-- Read the retained rational lower norm and weight from an actual certified loop domain. -/
def ofActual {process :
  Approximation.Gaussian.Process} (domain : Gaussian.Process.Normalization.Basic.LoopDomain process) : Data.Domain :=
  ⟨domain.lowerSq, domain.weight⟩

/-- Reading the actual loop domain preserves its exact decision target. -/
theorem target_ofActual {process
  : Approximation.Gaussian.Process} (domain : Gaussian.Process.Normalization.Basic.LoopDomain process) :
    (ofActual domain).target =
      domain.decisionTarget := rfl

/-- Reading the unary-scaled loop domain gives the domain computed from the same cached rational ball. -/
theorem unary_ofActual (process :
  Approximation.Gaussian.Process) (state : process.State)
    (certificate : Large.UnaryBall (process.ball state)) :
    ofActual (Downscale.unaryScaledLoopDomain
      process state certificate) =
      Domain.ofLower (Data.Bounds.unaryLower (BallData.ofBall (process.ball state))) := by
  simp only [Data.Bounds.unaryLower, Comparison.normSqFromReduced_eq]
  rfl

/-- Reading the normalized inverse loop domain gives the finite inverse-domain data for the same padding count and
residual upper bound. -/
theorem inverse_ofActual (process
  : Approximation.Gaussian.Process) (state : process.State)
    (certificate : Approximation.Gaussian.Enclosure.Ball.Apart (process.ball state)) (count : Nat) (upper :
        Fraction.Rational)
    (bounded : ∀ {value : Data.Gaussian.Basic.Canonical}, process.Possible state value →
      Data.Gaussian.Norm.Basic.normSq value ≤ upper)
    (strict : upper < Residual.paddingTarget count) :
    ofActual (Scale.normalizedInverseLoopDomain
      process state certificate count upper bounded strict) =
      Data.inverseDomain count upper := rfl
end Purelib.Approximation.Gaussian.Process.Normalization.Data.Correspondence.Domain

end
