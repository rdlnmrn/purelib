module
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.CCL.Transducer.Mode.Basic
import Purelib.Data.Gaussian.Constants
public import Purelib.Data.Gaussian.Power
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Gaussian
import Purelib.Data.Gaussian.Field
import Purelib.Approximation.Gaussian.Process.Basic

section
@[expose] public section

/-!
# Exact projective semantics of progressive arithmetic cursors

The raw `Machine` remains the original bit-only cursor.  This module adds a
separate proof wrapper relating its quantitative mode to the ordinary raw
parser matrix.  In particular, residual modes are interpreted homogeneously
as `[1 : γr]`; this is an affine inverse tail when `r ≠ 0` and is exactly
`ω` when `r = 0`.  No equality decision on a completed value is needed.
-/

namespace Purelib.Data.CCL.Transducer.Mode.Semantics
namespace SemanticMode

open Purelib.Data.CCL.Transducer in
open Purelib.Data.Gaussian in
/-- Read the retained mode's possible-value predicate from its exact process and dependent state. -/
def possible : (mode : Data.CCL.Transducer.Mode) →
  Basic.Canonical
  → Prop
  | .initial current => current.process.Possible current.state
  | .low current => current.process.Possible current.state
  | .loop current => current.process.Possible current.state
  | .residual current => current.process.Possible current.state

open Purelib.Data.CCL.Transducer
open Purelib.Data.Gaussian
open Purelib.Geometry.Projective
/-- Construct the exact projective parser tail modeled by a possible mode value.

Initial mode uses the affine value; low and loop modes undo their retained normalization counts in opposite directions.
Residual mode keeps the homogeneous pair one over gamma times the residual, including zero residuals. -/
def parserTail : (mode : Data.CCL.Transducer.Mode) →
  Basic.Canonical → Line.GaussianLine
  | .initial _current, value => Line.Proj.affine value
  | .low current, value =>
      Line.Proj.affine ((Power.natPow Basic.Canonical.gamma current.count)⁻¹ * value)
  | .loop current, value =>
      Line.Proj.affine (Power.natPow Basic.Canonical.gamma current.count * value)
  | .residual _current, value => ⟨1, Basic.Canonical.gamma * value⟩

/-- Every mode's exact projective parser tail has a nonzero coordinate. -/
theorem parserTail_valid (mode :
  Data.CCL.Transducer.Mode) (value
  : Basic.Canonical) :
    Line.Gaussian.Proj.HasNonzeroCoordinate
      (parserTail mode value) := by
  cases mode with
  | initial current | low current | loop current =>
      exact Line.Gaussian.Proj.affine_hasNonzeroCoordinate _
  | residual current =>
      change (1 : Basic.Canonical) ≠ 0 ∨ Basic.Canonical.gamma * value ≠ 0
      exact Or.inl (by decide)

end SemanticMode

end Purelib.Data.CCL.Transducer.Mode.Semantics

end
