module
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Projective.Hermitian.Box.Sign
import Purelib.Geometry.Projective.Hermitian.Formula.Basic
public import Purelib.Geometry.Projective.Hermitian.Formula.Box.Override
import Purelib.Geometry.Projective.Hermitian.Formula.Box.Stability
import Purelib.Geometry.Rational.Box.Basic
import Init.Prelude
import Purelib.Geometry.Projective.Hermitian.Atom
import Purelib.Geometry.Rational.Box.Refinement

section
@[expose] public section

/-!
# Box stability of finite CCL formulas

If every Hermitian atom in a finite branch formula has a strict box-sign
certificate, evaluating the formula at any one point decides it everywhere
in that box.  The certificate search is structural recursion over the finite
formula; it neither enumerates points nor forms a root set.
-/

namespace Purelib.Geometry.Projective.Hermitian.Formula.Box

/-- Execute all of the finitely many atom-margin comparisons in a formula. -/
def stable?
    (formula : Purelib.Geometry.Projective.Hermitian.Formula.BoundaryFormula) (bounding current :
      Purelib.Geometry.Rational.Box)
    (refines : current.Refines bounding) (sample : Purelib.Data.Gaussian.Basic.Canonical)
    (sampleInside : current.Contains sample) :
    Option (Purelib.Geometry.Projective.Hermitian.Formula.Box.Stable bounding current formula) :=
  match formula with
  | .truth => some .truth
  | .falsity => some .falsity
  | .atom value =>
      match Purelib.Geometry.Projective.Hermitian.Box.certificate?
          value.form bounding current refines sample sampleInside with
      | none => none
      | some certificate => some (.atom value (.strict certificate))
  | .and left right =>
      match stable? left bounding current refines sample sampleInside
        with
      | none => none
      | some leftStable =>
          match stable? right bounding current refines sample
            sampleInside with
          | none => none
          | some rightStable => some (.and leftStable rightStable)
  | .or left right =>
      match stable? left bounding current refines sample sampleInside
        with
      | none => none
      | some leftStable =>
          match stable? right bounding current refines sample
            sampleInside with
          | none => none
          | some rightStable => some (.or leftStable rightStable)

/-- Execute formula stability while reusing a finite list of exact boundary decisions already made by the equality-owner
layer. -/
def stableWith?
    (bounding current : Purelib.Geometry.Rational.Box)
    (overrides : List (Purelib.Geometry.Projective.Hermitian.Formula.Box.Override bounding current))
    (formula : Purelib.Geometry.Projective.Hermitian.Formula.BoundaryFormula)
    (refines : current.Refines bounding) (sample : Purelib.Data.Gaussian.Basic.Canonical)
    (sampleInside : current.Contains sample) :
    Option (Purelib.Geometry.Projective.Hermitian.Formula.Box.Stable bounding current formula) :=
  match formula with
  | .truth => some .truth
  | .falsity => some .falsity
  | .atom value =>
      match Purelib.Geometry.Projective.Hermitian.Formula.Box.atomStability? overrides refines sample sampleInside value
        with
      | none => none
      | some stability => some (.atom value stability)
  | .and left right =>
      match stableWith? bounding current overrides left refines sample
          sampleInside with
      | none => none
      | some leftStable =>
          match stableWith? bounding current overrides right refines
            sample
              sampleInside with
          | none => none
          | some rightStable => some (.and leftStable rightStable)
  | .or left right =>
      match stableWith? bounding current overrides left refines sample
          sampleInside with
      | none => none
      | some leftStable =>
          match stableWith? bounding current overrides right refines
            sample
              sampleInside with
          | none => none
          | some rightStable => some (.or leftStable rightStable)
end Purelib.Geometry.Projective.Hermitian.Formula.Box

end
