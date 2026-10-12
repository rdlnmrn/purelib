module

import Purelib.Data.GaussianInt.Basic
public import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Data.GaussianInt.Norm.Bounds
public import Purelib.Data.Int.BitWidth
import Purelib.Data.Nat.BitWidth
import Purelib.Data.Nat.Order
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

/-!
# Binary-width envelopes for Gaussian integers
-/

namespace Purelib.Data.GaussianInt.Resource

open Purelib.Data
open Purelib.Data.GaussianInt.Norm
open Purelib.Data.Int
open Purelib.Data.Nat

open Purelib.Data.GaussianInt

public section

/-- Measure a Gaussian integer by the maximum binary width of its two integral
coordinates. -/
@[expose] def gaussianIntWidth (value : GaussianInt) : Nat :=
  max (BitWidth.intWidth value.re) (BitWidth.intWidth value.im)

/-- Each integral coordinate's binary width is bounded by the width of the natural
quadrance.

Each coordinate magnitude is bounded by the original natural quadrance. Monotonicity of the retained binary-width
operation bounds their maximum. -/
theorem gaussianIntWidth_le_natWidth_normNat (value : GaussianInt) :
    Resource.gaussianIntWidth value ≤ BitWidth.natWidth (normNat value) := by
  unfold Resource.gaussianIntWidth
  rw [Order.max_eq_natMax]
  apply Order.max_le
  · exact BitWidth.natWidth_mono (Bounds.realComponent_le_normNat value)
  · exact BitWidth.natWidth_mono (Bounds.imaginaryComponent_le_normNat value)

/-- A natural quadrance budget also bounds the maximum coordinate width by that budget's
binary width.

The supplied quadrance bound transports the original coordinate-width bound to the displayed natural budget, without
changing either coordinate. -/
theorem gaussianIntWidth_le_budget {value : GaussianInt} {budget : Nat}
    (bounded : normNat value ≤ budget) :
    Resource.gaussianIntWidth value ≤ BitWidth.natWidth budget :=
  (Resource.gaussianIntWidth_le_natWidth_normNat value).trans (BitWidth.natWidth_mono bounded)

end

end Purelib.Data.GaussianInt.Resource
