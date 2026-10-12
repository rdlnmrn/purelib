module
public import Purelib.Data.Gaussian.Constants
import Purelib.Approximation.Gaussian.Name.Apart
public import Purelib.Approximation.Gaussian.Name.Arithmetic
public import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Process.Coherence.Addition
public import Purelib.Approximation.Gaussian.Process.Coherence.Division
import Purelib.Approximation.Gaussian.Process.Coherence.Multiplication
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Data.Gaussian.Basic

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Basic

open Purelib.Approximation.Gaussian.Name.Coherent

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
namespace CoherentNamed

/-- Add two coherent Gaussian names and retain the coherence certificate of their computed sum process. -/
def add (left right : Coherent.CoherentNamed) :
  Coherent.CoherentNamed :=
  { name := left.name.add right.name
    coherent := Gaussian.Process.Coherence.Basic.Coherent.add left.coherent right.coherent }

/-- Negate a coherent Gaussian name and retain the coherence certificate of its computed process. -/
def neg (value : Coherent.CoherentNamed) :
  Coherent.CoherentNamed :=
  { name := value.name.neg
    coherent := Gaussian.Process.Coherence.Basic.Coherent.neg value.coherent }

/-- Subtract two coherent Gaussian names and retain the coherence certificate of their computed difference process. -/
def sub (left right : Coherent.CoherentNamed) :
  Coherent.CoherentNamed :=
  { name := left.name.sub right.name
    coherent := Gaussian.Process.Coherence.Basic.Coherent.sub left.coherent right.coherent }

/-- Multiply two coherent Gaussian names and retain the coherence certificate of their computed product process. -/
def mul (left right : Coherent.CoherentNamed) :
  Coherent.CoherentNamed :=
  { name := left.name.mul right.name
    coherent := Gaussian.Process.Coherence.Basic.Coherent.mul left.coherent right.coherent }

/-- Apartness-certified division of two coherent productive names. -/
def div (left right : Coherent.CoherentNamed)
    (apart : Named.Apart right.name) :
    Coherent.CoherentNamed :=
  { name := left.name.div right.name apart
    coherent := Gaussian.Process.Coherence.Basic.Coherent.div left.coherent right.coherent apart.certificate }
/-- Rotate a coherent Gaussian name by multiplication with the exact imaginary unit. -/
def rotate
    (input : Coherent.CoherentNamed) : Coherent.CoherentNamed :=
  mul
    (CoherentNamed.Coherence.exact Data.Gaussian.Constants.imaginaryUnit) input

end CoherentNamed

end Purelib.Approximation.Gaussian.Name.Coherent

end

section
@[expose] public section

/-!
# Synchronized first jets over progressive CCL inputs

The displayed-input evaluator in `JetData` computes two rational
coordinates.  This module lifts the same algebra to arbitrary coherent
progressive inputs.  A jet contains two coherent names, one for the value
channel and one for the slope channel, together with an indexed finite program
which proves that the channels were produced by the same differentiation
calculation.  Thus an arbitrary unrelated pair of names is not a jet.  A joint
request computes one positive rational budget below the requested value error,
the requested slope error, and both semantic-coherence moduli.

No derivative is represented as a function.  Every observation consists of
two finite process states and two finite raw CCL prefixes.
-/

namespace Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic

/-- Apartness-certified reciprocal channel. -/
def reciprocalChannel (value : CoherentNamed)
    (apart : Named.Apart value.name) :
    Coherent.CoherentNamed :=
  Approximation.Gaussian.Name.Coherent.CoherentNamed.div (CoherentNamed.Coherence.exact 1)
    value apart

end Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic

end

section
@[expose] public section

/-!
# Progressive finite Taylor and multivariable CCL tables

The displayed higher-jet layer stores Gaussian rationals.  Here every entry is
instead a coherent productive CCL channel.  All operations recurse over the
displayed finite coefficient lists, and every resulting table inherits one
computable joint request from `ProgressiveFiniteTable`.
-/

namespace Purelib.CCL.Progressive.HigherJet

end Purelib.CCL.Progressive.HigherJet

end
