module
meta import Purelib.Elab.ConstructiveInjectivity

import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
import Purelib.RootIsolation.Progressive.Chamber.Basic
public import Purelib.RootIsolation.Progressive.Chamber.Ownership
import Purelib.RootIsolation.Progressive.Continuation.Basic
import Purelib.RootIsolation.Track.Basic
import Purelib.Tactic.Ring
public import Purelib.RootIsolation.Progressive.Continuation.Approximation
import Purelib.Geometry.Rational.Box.Separation
import Purelib.RootIsolation.Progressive.Chamber.Continuation
import Purelib.RootIsolation.State.WindingOne.Basic

open Purelib.Approximation.Gaussian

open Purelib.Polynomial

open Purelib.RootIsolation

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

namespace Purelib.RootIsolation.Progressive.Closure.Basic
open Purelib.Data.Gaussian

set_option genInjectivity false in
/-- Headline output.  The `Fin reference.degree` index is the exact finite
root count; `continuation` contains the executable simultaneous coefficient
and owner refinement, while `roots` exposes those same owners as productive
arithmetic-ready CCL names.  Maximality is certified at the chamber's exact
reference reading, from which every later owner keeps a unique identity. -/
structure EffectiveAlgebraicClosure
    {reference : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} (chamber :
      Progressive.Chamber.Basic.SimpleRootChamber reference)
    where
  /-- The retained executable simultaneous coefficient and owner refinement. -/ continuation :
    Progressive.Continuation.Basic.RootContinuation reference
  /-- The productive arithmetic CCL names indexed by the original reference degree. -/ roots : Fin reference.degree →
    Name.Basic.Named
  /-- The retained root names are exactly those of the retained continuation. -/ roots_eq : roots =
    continuation.rootNames
  /-- The retained continuation is exactly the original chamber's continuation. -/ continuation_eq : continuation =
    chamber.continuation
  /-- Every retained live box has its original unique finite chamber owner index. -/ ownership : ∀ history index,
    Progressive.Chamber.Ownership.ChamberOwnership chamber (continuation.box history index)
  /-- Every finite pairwise-separated family of reference-polynomial tracks has cardinality at most the exact reference
    degree. -/ referenceMaximality : ∀ {familyCount : Nat}
    (family : Fin familyCount → Track.Basic.WindingOneTrack
      reference.polynomial
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox reference.polynomial)),
    (∀ left right, left ≠ right →
      (family left).initial.box.Separated (family right).initial.box) →
    familyCount ≤ reference.degree

constructive_injectivity EffectiveAlgebraicClosure

end Purelib.RootIsolation.Progressive.Closure.Basic

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

namespace Purelib.RootIsolation.Progressive.Chamber.Basic.SimpleRootChamber
open Purelib.Data.Gaussian

/-- Effective algebraic closure for a monic progressive polynomial on a
finitely certified simple-root chamber.  The construction performs only
finite coefficient refinements, rational winding transport, bounded safe-cut
searches, and exact rational Newton calculations. -/
def effectiveAlgebraicClosure
    {reference : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} (chamber :
      Progressive.Chamber.Basic.SimpleRootChamber reference) :
    Progressive.Closure.Basic.EffectiveAlgebraicClosure chamber where
  continuation := chamber.continuation
  roots := chamber.continuation.rootNames
  roots_eq := rfl
  continuation_eq := rfl
  ownership := chamber.ownershipAt
  referenceMaximality := chamber.referenceMaximality

end Purelib.RootIsolation.Progressive.Chamber.Basic.SimpleRootChamber

end
