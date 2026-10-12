module
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.Prefix.Take
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.NumberTheory.Approximation.Dirichlet.Critical.CCL.Reserve.Basic
public import Purelib.NumberTheory.Approximation.Dirichlet.Critical.CCL.Reserve.Stage
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Robust.Run
import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Run
import Purelib.NumberTheory.Approximation.Dirichlet.Sharpness.BadWindow

open Purelib.Data.Rat

open Purelib

open Purelib.Data

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

namespace Stage.ReservedTower.Level

/-- Extend a stage by finite requested increments, saturating at the two
limits fixed by the reserve. -/
@[expose] def extend
    {threshold : Fraction.Rational} {requestedScale totalWindows : Nat}
    {tower : Dirichlet.Critical.CCL.Reserve.Basic.ReservedTower threshold requestedScale totalWindows}
    (current : Dirichlet.Critical.CCL.Reserve.Basic.ReservedTower.Stage tower) (newScale additionalWindows
      additionalBits : Nat) :
    Dirichlet.Critical.CCL.Reserve.Basic.ReservedTower.Stage tower :=
  tower.stage (max current.scale newScale)
    (current.windowCount + additionalWindows)
    (current.bitCount + additionalBits)

end Stage.ReservedTower.Level

namespace Basic.ReservedTower

/-- Joint refinement relation for reserved finite sharpness states. -/
structure StageExtends
    {threshold : Fraction.Rational} {requestedScale totalWindows : Nat}
    {tower : Dirichlet.Critical.CCL.Reserve.Basic.ReservedTower threshold requestedScale totalWindows}
    (earlier later : Dirichlet.Critical.CCL.Reserve.Basic.ReservedTower.Stage tower) : Prop where
  /-- The later stage exposes at least the earlier denominator scale. -/ scaleLe : earlier.scale ≤ later.scale
  /-- The later retained box refines the earlier retained box. -/ boxRefines :
    (Stage.ReservedTower.Level.box later).Refines
    (Stage.ReservedTower.Level.box earlier)
  /-- The earlier revealed CCL word is a prefix of the later word. -/ wordPrefix :
    (Stage.ReservedTower.Level.word earlier).IsPrefix
    (Stage.ReservedTower.Level.word later)
  /-- The earlier revealed window list is a prefix of the later list. -/ windowsPrefix :
    (Stage.ReservedTower.Level.windows earlier).IsPrefix
    (Stage.ReservedTower.Level.windows later)

end Basic.ReservedTower

namespace Basic.ReservedTower

/-- Increasing all three retained stage bounds gives a joint stage extension.

Both stages belong to the same reserve, so the box is unchanged and the shorter window and word segments are prefixes of
the longer segments. -/
theorem stageExtends_of_le
    {threshold : Fraction.Rational} {requestedScale totalWindows : Nat}
    {tower : Dirichlet.Critical.CCL.Reserve.Basic.ReservedTower threshold requestedScale totalWindows}
    {earlier later : Dirichlet.Critical.CCL.Reserve.Basic.ReservedTower.Stage tower}
    (scaleLe : earlier.scale ≤ later.scale)
    (windowsLe : earlier.windowCount ≤ later.windowCount)
    (bitsLe : earlier.bitCount ≤ later.bitCount) :
    Dirichlet.Critical.CCL.Reserve.Basic.ReservedTower.StageExtends earlier later :=
  { scaleLe := scaleLe
    boxRefines := Geometry.Rational.Box.refines_refl tower.robust.box
    wordPrefix :=
      Purelib.Data.List.Prefix.Take.takePrefixTakeDirect tower.fullWord earlier.bitCount
        later.bitCount bitsLe
    windowsPrefix :=
      Purelib.Data.List.Prefix.Take.takePrefixTakeDirect tower.robust.exact.windows
        earlier.windowCount later.windowCount windowsLe }

end Basic.ReservedTower

namespace Basic.ReservedTower

/-- Increasing any of the three finite requests produces a joint extension,
including when one or more requests saturate at a reserved endpoint. -/
theorem stage_monotone
    {threshold : Fraction.Rational} {requestedScale totalWindows : Nat}
    (tower : Dirichlet.Critical.CCL.Reserve.Basic.ReservedTower threshold requestedScale totalWindows)
    {earlierScale laterScale earlierWindows laterWindows
      earlierBits laterBits : Nat}
    (scaleLe : earlierScale ≤ laterScale)
    (windowsLe : earlierWindows ≤ laterWindows)
    (bitsLe : earlierBits ≤ laterBits) :
    Dirichlet.Critical.CCL.Reserve.Basic.ReservedTower.StageExtends
      (tower.stage earlierScale earlierWindows earlierBits)
      (tower.stage laterScale laterWindows laterBits) := by
  apply Dirichlet.Critical.CCL.Reserve.Basic.ReservedTower.stageExtends_of_le
  · change (if _ ≤ _ then _ else _) ≤ (if _ ≤ _ then _ else _)
    split <;> split <;> omega0
  · change (if _ ≤ _ then _ else _) ≤ (if _ ≤ _ then _ else _)
    split <;> split <;> omega0
  · change (if _ ≤ _ then _ else _) ≤ (if _ ≤ _ then _ else _)
    split <;> split <;> omega0

end Basic.ReservedTower

namespace Stage.ReservedTower.Level

/-- Every finite extension preserves the box, word prefix, and previously
revealed window prefix. -/
theorem
  extend_extends
    {threshold : Fraction.Rational} {requestedScale totalWindows : Nat}
    {tower : Dirichlet.Critical.CCL.Reserve.Basic.ReservedTower threshold requestedScale totalWindows}
    (current : Dirichlet.Critical.CCL.Reserve.Basic.ReservedTower.Stage tower) (newScale additionalWindows
      additionalBits : Nat) :
    Dirichlet.Critical.CCL.Reserve.Basic.ReservedTower.StageExtends current
      ((extend current) newScale additionalWindows
        additionalBits) := by
  apply Dirichlet.Critical.CCL.Reserve.Basic.ReservedTower.stageExtends_of_le
  · dsimp only [extend,
      Dirichlet.Critical.CCL.Reserve.Basic.ReservedTower.stage]
    change current.scale ≤ if max current.scale newScale ≤ requestedScale then
      max current.scale newScale else requestedScale
    split
    · exact Nat.Order.le_max_left current.scale newScale
    · exact current.scaleBound
  · dsimp only [extend,
      Dirichlet.Critical.CCL.Reserve.Basic.ReservedTower.stage]
    change current.windowCount ≤ if current.windowCount + additionalWindows ≤ totalWindows then
      current.windowCount + additionalWindows else totalWindows
    split
    · exact Nat.le_add_right _ _
    · exact current.windowBound
  · dsimp only [extend,
      Dirichlet.Critical.CCL.Reserve.Basic.ReservedTower.stage]
    change current.bitCount ≤ if current.bitCount + additionalBits ≤ tower.fullWord.length then
      current.bitCount + additionalBits else tower.fullWord.length
    split
    · exact Nat.le_add_right _ _
    · exact current.bitBound

end Stage.ReservedTower.Level

namespace Stage.ReservedTower.Level

/-- When the requested window increment fits in the reserve, exactly that
many windows are added. -/
theorem
  extend_windowCount_of_fits
    {threshold : Fraction.Rational} {requestedScale totalWindows : Nat}
    {tower : Dirichlet.Critical.CCL.Reserve.Basic.ReservedTower threshold requestedScale totalWindows}
    (current : Dirichlet.Critical.CCL.Reserve.Basic.ReservedTower.Stage tower) (newScale additionalWindows
      additionalBits : Nat)
    (fits : current.windowCount + additionalWindows ≤ totalWindows) :
    ((extend current) newScale additionalWindows
      additionalBits).windowCount =
      current.windowCount + additionalWindows :=
  Nat.min_eq_left fits

end Stage.ReservedTower.Level

namespace Stage.ReservedTower.Level

/-- When the requested bit increment fits before the terminal finite word,
exactly that many bits are added. -/
theorem
  extend_bitCount_of_fits
    {threshold : Fraction.Rational} {requestedScale totalWindows : Nat}
    {tower : Dirichlet.Critical.CCL.Reserve.Basic.ReservedTower threshold requestedScale totalWindows}
    (current : Dirichlet.Critical.CCL.Reserve.Basic.ReservedTower.Stage tower) (newScale additionalWindows
      additionalBits : Nat)
    (fits : current.bitCount + additionalBits ≤ tower.fullWord.length) :
    ((extend current) newScale additionalWindows
      additionalBits).bitCount =
      current.bitCount + additionalBits :=
  Nat.min_eq_left fits

end Stage.ReservedTower.Level

namespace Stage.ReservedTower.Level

/-- A fitting extension has the advertised window-list length. -/
theorem
  extend_windows_length_of_fits
    {threshold : Fraction.Rational} {requestedScale totalWindows : Nat}
    {tower : Dirichlet.Critical.CCL.Reserve.Basic.ReservedTower threshold requestedScale totalWindows}
    (current : Dirichlet.Critical.CCL.Reserve.Basic.ReservedTower.Stage tower) (newScale additionalWindows
      additionalBits : Nat)
    (fits : current.windowCount + additionalWindows ≤ totalWindows) :
    (windows
      ((extend current) newScale additionalWindows
      additionalBits)).length =
      current.windowCount + additionalWindows := by
  rw [(windows_length
    ((extend current) newScale additionalWindows
    additionalBits)),
    (extend_windowCount_of_fits current) newScale
      additionalWindows additionalBits fits]

end Stage.ReservedTower.Level

namespace Stage.ReservedTower.Level

/-- A fitting extension has the advertised finite-prefix length. -/
theorem
  extend_word_length_of_fits
    {threshold : Fraction.Rational} {requestedScale totalWindows : Nat}
    {tower : Dirichlet.Critical.CCL.Reserve.Basic.ReservedTower threshold requestedScale totalWindows}
    (current : Dirichlet.Critical.CCL.Reserve.Basic.ReservedTower.Stage tower) (newScale additionalWindows
      additionalBits : Nat)
    (fits : current.bitCount + additionalBits ≤ tower.fullWord.length) :
    (word
      ((extend current) newScale additionalWindows
      additionalBits)).length =
      current.bitCount + additionalBits := by
  rw [(word_length
    ((extend current) newScale additionalWindows
    additionalBits)),
    (extend_bitCount_of_fits current) newScale
      additionalWindows additionalBits fits]

end Stage.ReservedTower.Level

end ReservedTower
end Purelib.NumberTheory.Approximation.Dirichlet.Critical.CCL.Reserve

end
