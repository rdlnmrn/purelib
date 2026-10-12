module
import Purelib.Data.Nat.GCD.Extended
import Purelib.Data.Nat.Positive
public import Purelib.RootIsolation.Progressive.Braid.Power.Torus
import Purelib.Topology.Knot.Closure.Components
public import Purelib.Topology.Knot.Torus.Components
import Purelib.Topology.Knot.Torus.Knot
import Purelib.RootIsolation.Progressive.Braid.Relabeled.Basic
import Purelib.Topology.Knot.Closure.Basic
import Purelib.Topology.Knot.Torus.Basic

open Purelib

open Purelib.RootIsolation

section
@[expose] public section

/-!
# The explicit power-polynomial loop has torus-band monodromy

For every displayed degree `p >= 2`, `PowerMonodromy` supplies an explicit
rational coefficient circuit for `Z^p-w`, all of its finite Rouché chamber
steps, and a proof that the resulting owner permutation is one `p`-cycle.
Inverse-orbit labelling identifies that cycle with the cyclic predecessor,
which is exactly the endpoint permutation of the positive Artin band
`sigma_1 ... sigma_(p-1)`.

Repeating the rational circuit `q` times therefore produces the precise word
`(sigma_1 ... sigma_(p-1))^q` in the displayed labelling.  The extracted
closure is definitionally the finite torus-link model after the word theorem,
so the component, knot, surface, and Alexander interfaces apply directly.
-/

namespace Purelib.RootIsolation.Progressive.Braid.Power.Invariants

open Purelib.Topology.Knot

/-- The explicit polynomial closure inherits the exact constructive
`gcd(p,q)` component certificate of the torus-link model. -/
def componentCertificate (degree :
  Data.Nat.Positive.RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value)
    (q : Nat) (qPositive : 0 < q) :
    Closure.Components.UniformComponentCertificate
      (Progressive.Braid.Power.Torus.repeatedBraid degree degreeAtLeastTwo q).closure := by
  rw [Progressive.Braid.Power.Torus.closure_eq_torus degree degreeAtLeastTwo q qPositive]
  exact Topology.Knot.Torus.Basic.PowerSingularity.componentCertificate
    (Progressive.Braid.Power.Torus.singularity degree degreeAtLeastTwo q qPositive)

/-- The repeated rational power-circuit closure is a knot when the computed degree–repetition gcd is one. -/
theorem closure_isKnot_of_gcdOne (degree :
  Data.Nat.Positive.RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value)
    (q : Nat) (qPositive : 0 < q)
    (gcdOne :
      (Data.Nat.GCD.Extended.compute degree.value q).gcd = 1) :
    (Progressive.Braid.Power.Torus.repeatedBraid degree degreeAtLeastTwo q).closure.IsKnot := by
  rw [Progressive.Braid.Power.Torus.closure_eq_torus degree degreeAtLeastTwo q qPositive]
  apply Torus.PowerSingularity.closure_isKnot_of_gcdOne
  change (Data.Nat.GCD.Extended.compute
    (Progressive.Braid.Power.Torus.frame degree degreeAtLeastTwo).degree q).gcd = 1
  rw [Progressive.Braid.Power.Torus.frame_degree]
  exact gcdOne

end Purelib.RootIsolation.Progressive.Braid.Power.Invariants

end
