module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Prefix.Take
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Nat.Order
import Purelib.Data.CCL.Encoding.Encoder.Integral
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Data.CCL.Encoding.Prefix.Tower
import Purelib.NumberTheory.Approximation.Best.Consecutive.Basic
import Purelib.NumberTheory.Approximation.Best.Error
public import Purelib.NumberTheory.Approximation.Dirichlet.Critical.CCL.Reserve.Basic
import Purelib.NumberTheory.Approximation.Dirichlet.Sharpness.BadWindow
import Purelib.NumberTheory.Approximation.Dirichlet.Window.SourceBound
import Purelib.Data.List.Basic
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Robust.Run
import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Run

open Purelib

open Purelib.Data

open Purelib.Data.Rat

open Purelib.NumberTheory.Approximation

section
public section

/-!
# Finite CCL prefixes for robust approximation-sharpness runs

The RFAP construction can compute any requested finite same-source run, but
its displayed rational source depends on the final run length.  This module
therefore reserves one finite final run before exposing intermediate states.
Every state uses the same robust box, rational sample, and complete finite CCL
encoding, and reveals only initial segments of the reserved windows and word.
This is the finite prefix-coherent statement: it neither forms an infinite
stream nor asserts compatibility between independently constructed final
runs.
-/

namespace Purelib.NumberTheory.Approximation.Dirichlet.Critical.CCL.Reserve
section ReservedTower

namespace Basic.ReservedTower

set_option genInjectivity false in
/-- A state records how much of the already computed finite reserve has been
revealed.  Both bounds are data, so all later prefix statements are ordinary
finite-list calculations. -/
structure Stage
    {threshold : Fraction.Rational} {requestedScale totalWindows : Nat}
    (tower : Dirichlet.Critical.CCL.Reserve.Basic.ReservedTower threshold requestedScale totalWindows) where
  /-- The denominator scale currently exposed by the stage. -/ scale : Nat
  /-- The exposed scale does not exceed the reserve request. -/ scaleBound : scale ≤ requestedScale
  /-- The number of windows revealed from the retained run. -/ windowCount : Nat
  /-- The revealed window count does not exceed the retained finite total. -/ windowBound : windowCount ≤ totalWindows
  /-- The number of bits revealed from the cached CCL word. -/ bitCount : Nat
  /-- The revealed bit count does not exceed the cached word length. -/ bitBound : bitCount ≤ tower.fullWord.length

constructive_injectivity Stage

end Basic.ReservedTower

namespace Stage.ReservedTower.Level

variable {threshold : Fraction.Rational} {requestedScale totalWindows : Nat}
variable {tower : Dirichlet.Critical.CCL.Reserve.Basic.ReservedTower threshold requestedScale totalWindows}

/-- Every stage retains the one robust box fixed by the reserve. -/
@[expose] def box
  (_stage : Dirichlet.Critical.CCL.Reserve.Basic.ReservedTower.Stage tower) : Geometry.Rational.Box :=
  tower.robust.box

/-- The currently revealed initial segment of certified bad windows. -/
@[expose] def windows
  (stage : Dirichlet.Critical.CCL.Reserve.Basic.ReservedTower.Stage tower) :
    List { window : Sharpness.BadWindow threshold requestedScale //
      window.source = tower.robust.exact.source } :=
  tower.robust.exact.windows.take stage.windowCount

/-- The currently revealed initial segment of the sample's finite CCL word. -/
@[expose] def word
  (stage : Dirichlet.Critical.CCL.Reserve.Basic.ReservedTower.Stage tower) :
  List.Basic.BinaryWord :=
  tower.fullWord.take stage.bitCount

/-- The revealed window list has exactly the retained stage window count. -/
theorem
  windows_length
  (stage : Dirichlet.Critical.CCL.Reserve.Basic.ReservedTower.Stage tower) :
    (windows stage).length = stage.windowCount := by
  apply List.Prefix.Take.length_take_of_le
  rw [tower.robust.exact.length_eq]
  exact stage.windowBound

/-- The revealed CCL word has exactly the retained stage bit count. -/
theorem word_length
  (stage : Dirichlet.Critical.CCL.Reserve.Basic.ReservedTower.Stage tower) :
    (word stage).length = stage.bitCount :=
  List.Prefix.Take.length_take_of_le stage.bitBound

/-- The displayed rational sample remains in the stage box. -/
theorem sample_inside
  (stage : Dirichlet.Critical.CCL.Reserve.Basic.ReservedTower.Stage tower) :
    (box stage).Contains tower.sample.point :=
  tower.sample.inside

/-- The displayed sample is exactly the value encoded by the stage prefix. -/
theorem
  fraction_value
  (_stage : Dirichlet.Critical.CCL.Reserve.Basic.ReservedTower.Stage tower) :
    tower.fraction.value = tower.sample.point :=
  tower.fractionValue

/-- Every revealed window lies beyond the scale currently exposed by the
stage.  The reserve constructs the stronger bound at its final scale. -/
theorem beyondScale
  (stage : Dirichlet.Critical.CCL.Reserve.Basic.ReservedTower.Stage tower)
    (window : { window : Sharpness.BadWindow threshold requestedScale //
      window.source = tower.robust.exact.source }) :
    stage.scale < Best.Error.denominatorQuadrance
      window.1.upper := by
  have reserved := window.1.beyondScale
  exact stage.scaleBound.trans_lt reserved

/-- Each revealed word is a genuine CCL prefix cylinder for the displayed
rational sample. -/
theorem cylinder
  (stage : Dirichlet.Critical.CCL.Reserve.Basic.ReservedTower.Stage tower) :
    Data.CCL.Encoding.Prefix.Tower.Cylinder (word stage)
      tower.fraction
      tower.numeratorNonzero := by
  unfold word Data.CCL.Encoding.Prefix.Tower.Cylinder
  rw [tower.fullWord_eq]
  exact List.take_prefix stage.bitCount
    (Data.CCL.Encoding.Encoder.Integral.encode tower.fraction tower.numeratorNonzero)

/-- Every revealed window remains consecutive best throughout the common
robust source box. -/
theorem
  uniformConsecutive
  (stage : Dirichlet.Critical.CCL.Reserve.Basic.ReservedTower.Stage tower)
    (sample : Gaussian.Basic.Canonical) (inside : (box
      stage).Contains sample)
    (window : { window : Sharpness.BadWindow threshold requestedScale //
      window.source = tower.robust.exact.source })
    (member : window ∈ (windows stage)) :
    Best.Consecutive.Basic.AreConsecutiveBest sample
      window.1.lower window.1.upper := by
  apply tower.robust.uniformConsecutive sample inside window
  exact (List.take_prefix stage.windowCount
    tower.robust.exact.windows).subset member

/-- Every revealed window violates the sharper Dirichlet-window threshold
uniformly throughout the common robust source box. -/
theorem
  uniformViolation
  (stage : Dirichlet.Critical.CCL.Reserve.Basic.ReservedTower.Stage tower)
    (sample : Gaussian.Basic.Canonical) (inside : (box
      stage).Contains sample)
    (window : { window : Sharpness.BadWindow threshold requestedScale //
      window.source = tower.robust.exact.source })
    (member : window ∈ (windows stage)) :
    1 < threshold *
      Dirichlet.Window.SourceBound.dirichletWindowQuadrance sample
        window.1.lower window.1.upper := by
  apply tower.robust.uniformViolation sample inside window
  exact (List.take_prefix stage.windowCount
    tower.robust.exact.windows).subset member

/-- Upper denominator quadrances remain strictly increasing in every
revealed initial segment. -/
theorem scalesStrict
  (stage : Dirichlet.Critical.CCL.Reserve.Basic.ReservedTower.Stage tower) :
    (windows stage).Pairwise fun earlier later =>
      Best.Error.denominatorQuadrance earlier.1.upper <
        Best.Error.denominatorQuadrance later.1.upper :=
  tower.robust.exact.scalesStrict.take

end Stage.ReservedTower.Level

namespace Basic.ReservedTower

/-- Reveal at most the requested number of reserved windows and encoded bits.
Requests past either explicit finite reserve are saturated at its endpoint. -/
@[expose] def stage
    {threshold : Fraction.Rational} {requestedScale totalWindows : Nat}
    (tower : Dirichlet.Critical.CCL.Reserve.Basic.ReservedTower threshold requestedScale totalWindows)
    (revealedScale requestedWindows requestedBits : Nat) : Stage
      tower where
  scale := min revealedScale requestedScale
  scaleBound := by change (if _ ≤ _ then _ else _) ≤ _; split <;> omega0
  windowCount := min requestedWindows totalWindows
  windowBound := by change (if _ ≤ _ then _ else _) ≤ _; split <;> omega0
  bitCount := min requestedBits tower.fullWord.length
  bitBound := by change (if _ ≤ _ then _ else _) ≤ _; split <;> omega0

end Basic.ReservedTower

namespace Basic.ReservedTower

/-- A scale request within the reserve is retained exactly by the saturated stage constructor. -/
theorem stage_scale_of_le
    {threshold : Fraction.Rational} {requestedScale totalWindows : Nat}
    (tower : Dirichlet.Critical.CCL.Reserve.Basic.ReservedTower threshold requestedScale totalWindows)
    (revealedScale requestedWindows requestedBits : Nat)
    (within : revealedScale ≤ requestedScale) :
    (tower.stage revealedScale requestedWindows requestedBits).scale =
      revealedScale :=
  Nat.min_eq_left within

end Basic.ReservedTower

namespace Basic.ReservedTower

/-- A window request within the reserve is retained exactly by the saturated stage constructor. -/
theorem
  stage_windowCount_of_le
    {threshold : Fraction.Rational} {requestedScale totalWindows : Nat}
    (tower : Dirichlet.Critical.CCL.Reserve.Basic.ReservedTower threshold requestedScale totalWindows)
    (revealedScale requestedWindows requestedBits : Nat)
    (within : requestedWindows ≤ totalWindows) :
    (tower.stage revealedScale requestedWindows requestedBits).windowCount =
      requestedWindows :=
  Nat.min_eq_left within

end Basic.ReservedTower

namespace Basic.ReservedTower

/-- A bit request within the cached word length is retained exactly by the saturated stage constructor. -/
theorem
  stage_bitCount_of_le
    {threshold : Fraction.Rational} {requestedScale totalWindows : Nat}
    (tower : Dirichlet.Critical.CCL.Reserve.Basic.ReservedTower threshold requestedScale totalWindows)
    (revealedScale requestedWindows requestedBits : Nat)
    (within : requestedBits ≤ tower.fullWord.length) :
    (tower.stage revealedScale requestedWindows requestedBits).bitCount =
      requestedBits :=
  Nat.min_eq_left within

end Basic.ReservedTower

namespace Basic.ReservedTower

/-- The empty initial state of a finite reserve. -/
@[expose] def initial
    {threshold : Fraction.Rational} {requestedScale totalWindows : Nat}
    (tower : Dirichlet.Critical.CCL.Reserve.Basic.ReservedTower threshold requestedScale totalWindows) :
    Stage tower :=
  tower.stage 0 0 0

end Basic.ReservedTower

namespace Basic.ReservedTower

/-- Reveal the complete reserved run and the complete finite sample word. -/
@[expose] def complete
    {threshold : Fraction.Rational} {requestedScale totalWindows : Nat}
    (tower : Dirichlet.Critical.CCL.Reserve.Basic.ReservedTower threshold requestedScale totalWindows) :
    Stage tower :=
  tower.stage requestedScale totalWindows tower.fullWord.length

end Basic.ReservedTower

end ReservedTower
end Purelib.NumberTheory.Approximation.Dirichlet.Critical.CCL.Reserve

end
