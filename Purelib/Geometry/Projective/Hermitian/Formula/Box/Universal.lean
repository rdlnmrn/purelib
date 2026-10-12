module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Projective.Hermitian.Atom
import Purelib.Geometry.Projective.Hermitian.Box.Sign
import Purelib.Geometry.Projective.Hermitian.Formula.Basic
public import Purelib.Geometry.Projective.Hermitian.Formula.Box.Inspection
import Purelib.Geometry.Projective.Hermitian.Formula.Box.Override
import Purelib.Geometry.Projective.Hermitian.Formula.Box.Stability
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Geometry.Projective.Hermitian.Basic
import Purelib.Geometry.Rational.Box.Refinement

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Hermitian

open Purelib.Geometry.Projective.Hermitian.Formula.Box

section
@[expose] public section

/-!
# Finite equality ownership for CCL formula atoms

The parser's weak/strict convention decides every atom exactly at a zero of
its Hermitian form.  This module records that decision as finite data and
lets formula inspection reuse boundaries already proved identically zero.
Consequently a universal boundary is discharged once, and structural
reinspection either proves the complete formula stable or returns a
different unresolved atom.
-/

namespace Purelib.Geometry.Projective.Hermitian.Formula.Box

set_option genInjectivity false in
/-- Reinspection after resolving an identically-zero atom either certifies the entire formula or exposes a genuinely
different boundary. -/
inductive UniversalResolution
    (bounding current : Rational.Box) (refines : current.Refines bounding)
    (sample : Data.Gaussian.Basic.Canonical) (sampleInside : current.Contains sample)
    (formula : Formula.BoundaryFormula) (resolved : Hermitian.Atom) where
  /-- Resolving the universal boundary leaves a certified stable formula. -/ | stable (result : Formula.Box.Stable
    bounding current formula)
  /-- Retain a different unresolved atom, its occurrence, and its failed sign comparison. -/ | boundary (atom :
    Hermitian.Atom) (member : atom ∈ formula.atoms)
      (different : atom ≠ resolved)
      (failure : Hermitian.Box.certificate?
        atom.form bounding current refines sample sampleInside = none)

constructive_injectivity UniversalResolution

/-- A singleton override cache finds its own retained atom. -/
private theorem singleOverride_self_ne_none
    {bounding current : Rational.Box} (override : Formula.Box.Override bounding current) :
    Formula.Box.findOverride [override]
      override.atom ≠ none := by
  unfold Formula.Box.findOverride
  rewrite [dif_pos rfl]
  exact Option.some_ne_none _

/-- Cache one universal boundary and continue the finite structural inspection. The `different` field is the progress
measure needed by a bounded multi-atom owner loop. -/
def resolveUniversal
    (bounding current : Rational.Box) (refines : current.Refines bounding)
    (sample : Data.Gaussian.Basic.Canonical) (sampleInside : current.Contains sample)
    (formula : Formula.BoundaryFormula) (resolved : Hermitian.Atom)
    (zero : ∀ value, resolved.form.eval value = 0) :
    UniversalResolution bounding current refines sample sampleInside
      formula resolved := by
  let override : Formula.Box.Override bounding current :=
    Override.zero resolved
      (fun value _inside => zero value)
  match Formula.Box.inspectWith bounding current
      [override] formula refines sample sampleInside with
  | .stable stable => exact .stable stable
  | .unresolved atom member notResolved failure =>
      exact .boundary atom member (by
        intro equal
        subst atom
        exact singleOverride_self_ne_none override notResolved) failure
end Purelib.Geometry.Projective.Hermitian.Formula.Box

end
