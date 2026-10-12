module

public import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Name.Coherent
meta import Purelib.Elab.ConstructiveInjectivity

namespace Purelib.Approximation.Gaussian.Name.Coherent.Law.Basic

open Purelib
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name.Coherent

public section

/-!
# Operational laws at the persistent CCL-prefix layer

Operational equivalence compares two finite approximation programs by a
computed pair of later natural indices for every positive rational target.
This file carries that comparison all the way to persistent raw CCL cursors.
The two cursors may follow different displayed finite request schedules and
may emit different redundant words.  Each word nevertheless extends its own
earlier prefix, retains exact parser semantics for its certified origin, and
ends in a cylinder of the requested squared-chordal diameter.

The `BitLaw` wrapper then exposes the established arithmetic and exp/log laws
at precisely this bit-producing interface.  It does not identify completed
values or quantify over an infinite bitstream.
-/

open Purelib.Approximation

set_option genInjectivity false in
/-- A progressive law is an operational equivalence equipped, by `request`, with the complete persistent-prefix contract
above. -/
structure BitLaw (left right : CoherentNamed) : Type where
  /-- The retained finite-request operational equivalence of the two original coherent names. -/ equivalent :
    Gaussian.Equivalence.NamedEquivalent left.name right.name

constructive_injectivity BitLaw

namespace BitLaw

/-- Package a retained finite-request equivalence as a law between the original coherent names. -/
@[expose] def ofEquivalent {left right : CoherentNamed}
    (equivalent : Gaussian.Equivalence.NamedEquivalent left.name right.name) :
      Approximation.Gaussian.Name.Coherent.Law.Basic.BitLaw left right :=
  ⟨equivalent⟩
end BitLaw

end

end Purelib.Approximation.Gaussian.Name.Coherent.Law.Basic
