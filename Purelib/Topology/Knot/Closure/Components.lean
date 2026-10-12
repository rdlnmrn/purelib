module

import Purelib.Data.Fin.Bijection.Iteration
public import Purelib.Topology.Knot.Closure.Basic
meta import Mathlib.Tactic.Linter.Lint
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.Fin.Bijection.Basic

section
public section

/-!
# Finite closure-component certificates

A finite permutation decomposes into finite cycles.  For the torus family all
cycles have the same displayed length, so an exact component result is most
economically represented by a uniform-cycle certificate: component count
times orbit length is the strand count, every strand returns at that orbit
length, and no positive shorter return is possible.

For `(σ₁…σₚ₋₁)^q`, the component count is the output of the
project's structurally recursive certified Euclidean algorithm.  The proof
uses its divisibility data and quotient Bézout certificate; it does not use
upstream `Nat.gcd`.
-/

namespace Purelib.Topology.Knot.Closure.Components

open Purelib.Topology.Knot.Braid

section Closure

-- Preserve this original duplicated nominal/API name; the source formerly suppressed the linter module-wide.
set_option genInjectivity false in
/-- Exact finite evidence for a closure whose permutation cycles all have the same displayed length. -/
structure UniformComponentCertificate (closure : Closure) where
  /-- The displayed number of permutation cycles. -/ componentCount : Nat
  /-- The common finite length of each strand orbit. -/ orbitLength : Nat
  /-- The component count times the common orbit length equals the strand count. -/ count_mul_orbitLength :
    componentCount * orbitLength = closure.strands
  /-- Every strand returns after the retained common orbit length. -/ return_at_orbitLength : ∀ index : Fin
    closure.strands,
    Data.Fin.Bijection.iterateForward
      closure.permutation orbitLength index = index
  /-- No strand returns at a positive iteration count below the retained orbit length. -/ no_early_return : ∀ (index :
    Fin closure.strands) (steps : Nat),
    0 < steps → steps < orbitLength →
      Data.Fin.Bijection.iterateForward
        closure.permutation steps index ≠ index

-- Preserve the original constructor certificate names of this unchanged nominal datatype.

constructive_injectivity UniformComponentCertificate

namespace UniformComponentCertificate.mk

end UniformComponentCertificate.mk

namespace UniformComponentCertificate.mk

end UniformComponentCertificate.mk

end Closure

end Purelib.Topology.Knot.Closure.Components

namespace Purelib.Topology.Knot.TorusBraid.PowerSingularity

open Purelib.Topology.Knot.Braid
end Purelib.Topology.Knot.TorusBraid.PowerSingularity

end
