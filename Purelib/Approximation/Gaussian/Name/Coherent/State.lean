module

public import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Tactic.Ring
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Process.Coherence.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Approximation.Gaussian.Name

open Purelib.Data.Rat

section

/-!
# One explicit rational Legendre crossing segment

This module certifies a single positive projected crossing of the moving
Legendre root over the fixed root at zero.  The parameter moves horizontally
from `1/4 + 2i` to `-1/4 + 2i`.  Broad chamber-owner boxes retain the
same three roots across the coefficient overlap, while much smaller sample
owners certify the change in left-to-right projection order.
-/

end

section
section

/-!
# One explicit rational Legendre root frame

This module constructs the base fibre at `lambda = 2` from three displayed
rational winding-one boxes around `0`, `1`, and `2`.  The chamber owners,
logical root labels, and left-to-right projection order all come from the same
finite boxes.  No generic owner ordering is guessed after isolation.
-/

end

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.Approximation.Gaussian.Name.Coherent.State
open Purelib.Data.Gaussian

/-! ## Finite simultaneous coefficient readings -/

set_option genInjectivity false in
/-- One coherent coefficient at one explicitly displayed finite process state. The state is dependent on the coefficient
channel and is stored with it rather than selected from a completed value. -/
structure CoefficientState where
  /-- The original coherent Gaussian coefficient channel. -/ channel : Coherent.CoherentNamed
  /-- The retained process state belonging to this exact coefficient channel. -/ state : channel.name.process.State

constructive_injectivity CoefficientState

end Purelib.Approximation.Gaussian.Name.Coherent.State

end

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.Approximation.Gaussian.Name.Coherent.State
open Purelib.Data.Gaussian
namespace CoefficientState

/-- The coherence allowance at the coefficient's retained dependent process state. -/
def allowance (entry :
  Approximation.Gaussian.Name.Coherent.State.CoefficientState) : Fraction.Rational :=
  entry.channel.coherent.allowance entry.state
end CoefficientState

end Purelib.Approximation.Gaussian.Name.Coherent.State

end

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.Approximation.Gaussian.Name.Coherent.State
open Purelib.Data.Gaussian
namespace CoefficientState

/-- The coefficient's retained coherence allowance is nonnegative. -/
theorem allowance_nonneg (entry :
  Approximation.Gaussian.Name.Coherent.State.CoefficientState) :
    0 ≤ entry.allowance :=
  entry.channel.coherent.allowance_nonneg entry.state
end CoefficientState

end Purelib.Approximation.Gaussian.Name.Coherent.State

end

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.Approximation.Gaussian.Name.Coherent.State
open Purelib.Data.Gaussian
namespace CoefficientState

/-- Refine one coefficient state by one displayed positive rational request. -/
def refine (entry :
  Approximation.Gaussian.Name.Coherent.State.CoefficientState) (request : Fraction.Rational)
    (positive : 0 < request) : Approximation.Gaussian.Name.Coherent.State.CoefficientState :=
  { channel := entry.channel
    state := entry.channel.name.process.refine entry.state request positive }
end CoefficientState

end Purelib.Approximation.Gaussian.Name.Coherent.State

end

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.Approximation.Gaussian.Name.Coherent.State
open Purelib.Data.Gaussian
namespace CoefficientState

/-- Refining a coefficient state preserves its original coherent channel. -/
@[simp] theorem refine_channel (entry :
  Approximation.Gaussian.Name.Coherent.State.CoefficientState)
    (request : Fraction.Rational) (positive : 0 < request) :
    (entry.refine request positive).channel = entry.channel := rfl
end CoefficientState

end Purelib.Approximation.Gaussian.Name.Coherent.State

end

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.Approximation.Gaussian.Name.Coherent.State
open Purelib.Data.Gaussian
namespace CoefficientState

/-- The process's constructive witness at this finite state. -/
def value (entry :
  Approximation.Gaussian.Name.Coherent.State.CoefficientState) : Data.Gaussian.Basic.Canonical :=
  (entry.channel.name.process.witness entry.state).val
end CoefficientState

end Purelib.Approximation.Gaussian.Name.Coherent.State

end
section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.Approximation.Gaussian.Name.Coherent.State
open Purelib.Data.Gaussian
namespace CoefficientState

/-- The displayed coefficient witness is possible at its retained process state. -/
theorem value_possible (entry :
  Approximation.Gaussian.Name.Coherent.State.CoefficientState) :
    entry.channel.name.process.Possible entry.state entry.value :=
  (entry.channel.name.process.witness entry.state).property
end CoefficientState

end Purelib.Approximation.Gaussian.Name.Coherent.State

end

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.Approximation.Gaussian.Name.Coherent.State
open Purelib.Data.Gaussian
namespace CoefficientState

/-- The witness produced after coefficient refinement remains possible at the preceding state. -/
theorem refine_value_possible_before (entry :
  Approximation.Gaussian.Name.Coherent.State.CoefficientState)
    (request : Fraction.Rational) (positive : 0 < request) :
    entry.channel.name.process.Possible entry.state
      (entry.refine request positive).value :=
  entry.channel.name.process.refine_persists entry.state request positive
    (entry.refine request positive).value_possible

end CoefficientState

end Purelib.Approximation.Gaussian.Name.Coherent.State

end

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.CCL.Progressive.PowerMonodromy
end Purelib.CCL.Progressive.PowerMonodromy

end

section
@[expose] public section

/-!
# One explicit rational Legendre root frame

This module constructs the base fibre at `lambda = 2` from three displayed
rational winding-one boxes around `0`, `1`, and `2`.  The chamber owners,
logical root labels, and left-to-right projection order all come from the same
finite boxes.  No generic owner ordering is guessed after isolation.
-/

namespace Purelib.Approximation.Gaussian.Name.Coherent.State.ExplicitLegendreFrame

/-- The exact coherent coefficient-state type, retaining the original channel and its dependent process state. -/
abbrev CoefficientState :=
  Approximation.Gaussian.Name.Coherent.State.CoefficientState
end Purelib.Approximation.Gaussian.Name.Coherent.State.ExplicitLegendreFrame

end

section
@[expose] public section

/-!
# One explicit rational Legendre crossing segment

This module certifies a single positive projected crossing of the moving
Legendre root over the fixed root at zero.  The parameter moves horizontally
from `1/4 + 2i` to `-1/4 + 2i`.  Broad chamber-owner boxes retain the
same three roots across the coefficient overlap, while much smaller sample
owners certify the change in left-to-right projection order.
-/

namespace Purelib.Approximation.Gaussian.Name.Coherent.State.ExplicitLegendreSegment

/-- The exact coherent coefficient-state type, retaining the original channel and its dependent process state. -/
abbrev CoefficientState :=
  Approximation.Gaussian.Name.Coherent.State.CoefficientState
end Purelib.Approximation.Gaussian.Name.Coherent.State.ExplicitLegendreSegment

end
