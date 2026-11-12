module

import Purelib.Polynomial.Recurrence.Mode.Bounds

/-!
# Computed finite generalized-mode requests

The actual original entry producer exhibits startup growth, exact zero
transients, an inside tail paid by a computed request, and individual
outside witnesses with real and nonreal roots.
-/

namespace TestPurelib.Polynomial.Recurrence.Mode.Bounds

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Polynomial.Recurrence.Mode

/-- The original uniform inside request has quadrance ceiling one quarter and generalized order one. -/
private def inside := Inside.prepare (1/4) (by decide +kernel) (by decide +kernel) 1 (1/4) (by decide +kernel)

/-- The original bounded contraction search computes the finite threshold twenty-four. -/
private theorem inside_index : inside.index = 24 := by decide +kernel

/-- The same request bounds the actual real-root mode at its computed threshold. -/
private theorem inside_at_threshold : Norm.Basic.normSq (entry (⟨1/2, 0⟩ : Canonical) 1 24) ≤ 1/4 :=
  inside.bound _ (by decide +kernel) 24 (inside_index.symm ▸ Nat.le_refl 24)

/-- The same request bounds a later window entry of a different compatible nonreal root. -/
private theorem nonreal_window :
    Norm.Basic.normSq (window (⟨1/4, 1/4⟩ : Canonical) 1 27 ⟨25, by decide +kernel⟩) ≤ 1/4 :=
  inside.window_bound (by decide +kernel) 27 ⟨25, by decide +kernel⟩
    (inside_index.symm ▸ (by decide +kernel : 24 ≤ 25))

/-- A repeated inside mode can initially exceed one, so the finite tail threshold carries real information. -/
private theorem startup_growth :
    entry (⟨1/2, 0⟩ : Canonical) 2 4 = ⟨3/2, 0⟩ ∧
      Norm.Basic.normSq (entry (⟨1/2, 0⟩ : Canonical) 2 4) = 9/4 := by decide +kernel

/-- The original zero-root generalized mode is exactly its one-coordinate transient. -/
private theorem actual_zero_transient :
    entry (0 : Canonical) 3 2 = 0 ∧ entry (0 : Canonical) 3 3 = 1 ∧ entry (0 : Canonical) 3 4 = 0 :=
  by decide +kernel

/-- Every later original zero-root window coordinate is exactly zero without a contraction request. -/
private theorem zero_later_window (count : Nat) (index : Fin count) (later : 3 < index.val) :
    window (0 : Canonical) 3 count index = 0 := zero_window_after 3 count index later

/-- An actual outside request fixes a finite observation of an order-two real-root mode. -/
private def outside := Outside.prepare 3 1 (by decide +kernel) (by decide +kernel) 2 4 (by decide +kernel)

/-- The original ceiling computation retains the startup offset and returns index four. -/
private theorem outside_index : outside.extra = 2 ∧ outside.index = 4 := by decide +kernel

/-- The retained outside request supplies its actual finite witness on the original mode. -/
private theorem outside_witness : 4 ≤ Norm.Basic.normSq (1 * entry (2 : Canonical) 2 outside.index) :=
  outside.bound 2 1 (by decide +kernel) (by decide +kernel)

/-- Direct scalar computation independently checks the original real-root witness. -/
private theorem actual_outside_value :
    entry (2 : Canonical) 2 4 = 24 ∧ Norm.Basic.normSq (entry (2 : Canonical) 2 4) = 576 := by decide +kernel

/-- A nonreal outside root and a nonunit Gaussian coefficient use their actual positive quadrance gaps. -/
private def nonrealOutside :=
  Outside.prepare 1 (1/4) (by decide +kernel) (by decide +kernel) 1 2 (by decide +kernel)

/-- The computed nonreal-root witness retains index nine and reaches the requested quadrance. -/
private theorem nonreal_outside :
    nonrealOutside.index = 9 ∧
      2 ≤ Norm.Basic.normSq ((⟨1/2, 0⟩ : Canonical) * entry (⟨1, 1⟩ : Canonical) 1 nonrealOutside.index) :=
  ⟨by decide +kernel, nonrealOutside.bound _ _ (by decide +kernel) (by decide +kernel)⟩

end TestPurelib.Polynomial.Recurrence.Mode.Bounds
