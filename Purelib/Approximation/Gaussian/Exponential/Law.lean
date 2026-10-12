module
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Addition
public import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Coherent
public import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
public import Purelib.Approximation.Gaussian.Name.Coherent.Law.Basic

namespace Purelib.Approximation.Gaussian.Exponential.Law

open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.Law.Basic

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

/-- Lift operational equivalence of coherent inputs through the total exponential to its retained CCL-prefix law. -/
@[expose] def exponential_respects (left right : CoherentNamed)
    (equivalent : Gaussian.Equivalence.NamedEquivalent left.name right.name) :
    Law.Basic.BitLaw (Exponential.Progressive.Range.Coherent.exp left.name)
      (Exponential.Progressive.Range.Coherent.exp right.name) :=
  BitLaw.ofEquivalent
    (Exponential.Progressive.Range.Congruence.automaticExp_respects
      left right equivalent)

/-! ## Principal arithmetic laws on emitted CCL prefixes -/

/-- The product of the two total exponential outputs and the exponential of the coherent sum satisfy the retained
CCL-prefix law. -/
@[expose] def exponential_addition (left right : CoherentNamed) :
    Law.Basic.BitLaw
      (CoherentNamed.mul
        (Exponential.Progressive.Range.Coherent.exp left.name)
        (Exponential.Progressive.Range.Coherent.exp right.name))
      (Exponential.Progressive.Range.Coherent.exp
        (CoherentNamed.add left right).name) :=
  BitLaw.ofEquivalent
    (Exponential.Progressive.Range.Addition.automaticExp_add left right)

end

end Purelib.Approximation.Gaussian.Exponential.Law
