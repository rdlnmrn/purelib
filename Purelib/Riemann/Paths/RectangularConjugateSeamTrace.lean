module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic

public import Purelib.Riemann.Paths.RectangularSeamTraceBounds
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Tactic.Ring

@[expose] public section

/-! Conjugation preserves the scalar seam error, increment and drift bounds.
This permits the existing paired ribbon estimate to compare energy traces. -/
namespace Purelib.Riemann.Paths.RectangularConjugateSeamTrace

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Riemann.Paths.RectangularSeamTraceBounds (SeamTraceBounds)

/-- Transport the original seam trace bounds through Gaussian conjugation.

The same error, slope and drift constants remain valid for the exact pointwise conjugated traces and their ordered
increments. -/
theorem SeamTraceBounds.conjugated {left right : Coordinate → Gaussian} {error slope drift : Coordinate}
    (bounds : SeamTraceBounds left right error slope drift) :
    SeamTraceBounds (fun parameter => conj (left parameter)) (fun parameter => conj (right parameter)) error slope drift
      := by
  constructor
  · intro parameter inside
    rw [normSq_conj_sub]
    exact bounds.errors parameter inside
  · intro first last firstInside lastInside
    rw [normSq_conj_sub]
    exact bounds.increments first last firstInside lastInside
  · intro first last firstInside lastInside
    rw [← conj_sub, ← conj_sub, normSq_conj_sub]
    exact bounds.drifts first last firstInside lastInside

end Purelib.Riemann.Paths.RectangularConjugateSeamTrace
