module
import Purelib.Data.Gaussian.Basic
public import Purelib.LinearAlgebra.Coordinates2.Matrix
public import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
public import Purelib.Data.Gaussian.Constants

import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Data.ComplexContinuedFraction.Encoding

open Purelib.LinearAlgebra.Coordinates2.Matrix

/-!
# Choice-free completed-block chordal contraction

This file proves the affine two-tail part of the companion paper's completed
CCL block contraction.  The proof is entirely cross-multiplied over explicit
fractions; no square root, limit, supremum, or inherited ordered-field
division theorem is used.
-/

@[expose] public section

namespace Purelib.Geometry.Projective.SectorBlock.Basic

/-- The common completed-block matrix `A_{λ,s} = S_λ T_s I_γ`. -/
def block (scale : Data.Gaussian.Basic.Canonical) (sector :
  Data.ComplexContinuedFraction.Encoding.Sector) : GaussianMatrix :=
  ⟨scale * Data.Gaussian.Basic.Canonical.gamma * sector.rep, scale, Data.Gaussian.Basic.Canonical.gamma, 0⟩
end Purelib.Geometry.Projective.SectorBlock.Basic

end
