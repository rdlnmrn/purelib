module

public import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Data.Gaussian.Basic
import Purelib.Tactic.Ring

/-! # Constant-coefficient quadrature on the SAME ordered clear edges

Every original physical edge contributes its original target-minus-source
weight. The finite scalar sum telescopes exactly without constructing any
new path, source model, root Owner or integral agreement certificate.
-/

public section

namespace Purelib.Polynomial.Geometry.ClearPath

open Purelib.Data.Gaussian.Basic (Canonical)

variable {polynomial : GaussianPolynomial} {ambient : Purelib.Geometry.Rational.Box}

/-- Sum one supplied scalar coefficient against the SAME original ordered physical edge displacements. -/
def constantSample : {start finish : Canonical} → ClearPath polynomial ambient start finish → Canonical → Canonical
  | _, _, .nil _, _ => 0
  | start, _, .cons (middle := corner) _ tail, coefficient =>
      (corner - start) * coefficient + constantSample tail coefficient

/-- The actual finite sum of original oriented edge weights equals the original endpoint displacement. -/
theorem constantSample_eq : {start finish : Canonical} → (path : ClearPath polynomial ambient start finish) →
    (coefficient : Canonical) → path.constantSample coefficient = (finish - start) * coefficient
  | _, _, .nil point, coefficient => by
      unfold constantSample
      ring1
  | start, _, .cons (middle := corner) _head tail, coefficient => by
      unfold constantSample
      rewrite [constantSample_eq tail coefficient]
      ring1

end Purelib.Polynomial.Geometry.ClearPath
