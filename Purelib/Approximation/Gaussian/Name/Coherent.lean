module

import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Coherence.Basic
import Purelib.Approximation.Gaussian.Sequence
public import Purelib.Approximation.Gaussian.Sequence.Coherence

import Purelib.Tactic.QuotientFreeOmega
public import Purelib.Approximation.Gaussian.Sequence.Name
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Name.Basic

open Purelib.Approximation.Gaussian.Sequence

section
@[expose] public section

/-!
# Finite coherence certificates for progressive CCL processes

`Process` deliberately permits branching refinement strategies: it promises
that every requested branch becomes accurate, but does not by itself say that
two independently refined branches describe one operational value.  This
module adds exactly that missing, finite certificate.

A coherent process assigns a nonnegative rational squared allowance to every
finite state.  The current enclosure radius is no larger than that allowance,
every pair of explicitly possible Gaussian-rational readings is close at the
sum of their allowances, and one ordinary refinement makes the allowance
smaller than any requested positive rational target.  There is no completed
value, infinite carrier, limit, or choice of a value common to all states.
-/

namespace Purelib.Approximation.Gaussian.Name.Coherent

/-! ## Coherent names as an arithmetic interface -/

set_option genInjectivity false in
/-- A progressive process name with a certificate comparing its independent finite branches.

The original process and state are retained; coherence provides rational semantic allowances and a terminating finite
refinement request. -/
structure CoherentNamed where
  /-- The retained progressive process and its displayed finite state. -/ name : Gaussian.Name.Basic.Named
  /-- The coherence certificate for that same retained process. -/ coherent : Gaussian.Process.Coherence.Basic.Coherent
    name.process

constructive_injectivity CoherentNamed

namespace CoherentNamed

/-- A displayed exact Gaussian rational as a coherent productive name. -/
def Coherence.exact (value :
  Data.Gaussian.Basic.Canonical) : Approximation.Gaussian.Name.Coherent.CoherentNamed :=
  { name := Named.exact value
    coherent := Gaussian.Process.Coherence.Basic.Coherent.exact value }

/-- Turn a limit-free finite approximation directly into a coherent name. -/
def ofApproximation (approximation :
  ApproximationData) : Approximation.Gaussian.Name.Coherent.CoherentNamed :=
  { name := approximation.toNamed
    coherent := Gaussian.Process.Coherence.Basic.Coherent.ofApproximation approximation }
end CoherentNamed

end Purelib.Approximation.Gaussian.Name.Coherent

end
