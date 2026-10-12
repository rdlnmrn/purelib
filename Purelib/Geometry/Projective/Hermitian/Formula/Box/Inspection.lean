module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Projective.Hermitian.Atom
import Purelib.Geometry.Projective.Hermitian.Box.Sign
import Purelib.Geometry.Projective.Hermitian.Formula.Basic
public import Purelib.Geometry.Projective.Hermitian.Formula.Box.Override
import Purelib.Geometry.Projective.Hermitian.Formula.Box.Stability
import Purelib.Geometry.Rational.Box.Basic
import Init.Data.List.Lemmas
import Init.Prelude
import Purelib.Geometry.Rational.Box.Refinement

public section

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Hermitian

/-!
# Box stability of finite CCL formulas

If every Hermitian atom in a finite branch formula has a strict box-sign
certificate, evaluating the formula at any one point decides it everywhere
in that box.  The certificate search is structural recursion over the finite
formula; it neither enumerates points nor forms a root set.
-/

namespace Purelib.Geometry.Projective.Hermitian.Formula.Box

set_option genInjectivity false in
/-- Proof-bearing result of the same structural inspection as `stable?`. Failure retains the first concrete atom whose
strict margin comparison did not succeed, rather than erasing its boundary provenance into `none`. -/
inductive Inspection
    (bounding current : Rational.Box) (refines : current.Refines bounding)
    (sample : Data.Gaussian.Basic.Canonical) (sampleInside : current.Contains sample) :
    (formula : Formula.BoundaryFormula) → Type where
  /-- Retain a certificate that the complete formula is stable on the box. -/ | stable {formula :
    Formula.BoundaryFormula} (result : Formula.Box.Stable bounding current formula) :
      Inspection bounding current refines sample sampleInside formula
  /-- Retain an atom occurrence and the failed strict-sign comparison. -/ | unresolved {formula :
    Formula.BoundaryFormula} (atom : Hermitian.Atom)
      (member : atom ∈ formula.atoms)
      (failure : Hermitian.Box.certificate?
        atom.form bounding current refines sample sampleInside = none) :
      Inspection bounding current refines sample sampleInside formula

constructive_injectivity Inspection

/-- Inspect a finite formula and retain the first unresolved atom when it is not box-stable. -/
@[expose] def inspect
    (formula : Purelib.Geometry.Projective.Hermitian.Formula.BoundaryFormula) (bounding current :
      Purelib.Geometry.Rational.Box)
    (refines : current.Refines bounding) (sample : Purelib.Data.Gaussian.Basic.Canonical)
    (sampleInside : current.Contains sample) :
    Inspection bounding current refines sample sampleInside formula :=
  match formula with
  | .truth => .stable .truth
  | .falsity => .stable .falsity
  | .atom value =>
      match result : Purelib.Geometry.Projective.Hermitian.Box.certificate?
          value.form bounding current refines sample sampleInside with
      | none => .unresolved value (by exact List.Mem.head []) result
      | some certificate => .stable (.atom value (.strict certificate))
  | .and left right =>
      match inspect left bounding current refines sample sampleInside
        with
      | .unresolved atom member failure =>
          .unresolved atom (by
            exact Purelib.Data.List.Membership.mem_append.mpr (Or.inl member)) failure
      | .stable leftStable =>
          match inspect right bounding current refines sample
            sampleInside with
          | .unresolved atom member failure =>
              .unresolved atom (by
                exact Purelib.Data.List.Membership.mem_append.mpr (Or.inr member)) failure
          | .stable rightStable => .stable (.and leftStable rightStable)
  | .or left right =>
      match inspect left bounding current refines sample sampleInside
        with
      | .unresolved atom member failure =>
          .unresolved atom (by
            exact Purelib.Data.List.Membership.mem_append.mpr (Or.inl member)) failure
      | .stable leftStable =>
          match inspect right bounding current refines sample
            sampleInside with
          | .unresolved atom member failure =>
              .unresolved atom (by
                exact Purelib.Data.List.Membership.mem_append.mpr (Or.inr member)) failure
          | .stable rightStable => .stable (.or leftStable rightStable)

set_option genInjectivity false in
/-- Reinspection records that a returned failure was not already present in the finite equality-owner cache. -/
inductive Reinspection
    (bounding current : Rational.Box) (refines : current.Refines bounding)
    (sample : Data.Gaussian.Basic.Canonical) (sampleInside : current.Contains sample)
    (overrides : List (Formula.Box.Override bounding current)) :
    (formula : Formula.BoundaryFormula) → Type where
  /-- Retain stability of the formula after reusing cached atom certificates. -/ | stable {formula :
    Formula.BoundaryFormula} (result : Formula.Box.Stable bounding current formula) :
      Reinspection bounding current refines sample sampleInside
        overrides
        formula
  /-- Retain an atom occurrence absent from the cache and its failed strict-sign comparison. -/ | unresolved {formula :
    Formula.BoundaryFormula} (atom : Hermitian.Atom)
      (member : atom ∈ formula.atoms)
      (notResolved : Formula.Box.findOverride overrides atom = none)
      (failure : Hermitian.Box.certificate?
        atom.form bounding current refines sample sampleInside = none) :
      Reinspection bounding current refines sample sampleInside
        overrides
        formula

constructive_injectivity Reinspection

/-- Structural inspection with a finite cache of equality-owned atoms. A new failure is therefore a genuinely different
unresolved boundary, so adding its resolution makes finite progress through the formula's atom list. -/
@[expose] def inspectWith
    (bounding current : Purelib.Geometry.Rational.Box)
    (overrides : List (Purelib.Geometry.Projective.Hermitian.Formula.Box.Override bounding current))
    (formula : Purelib.Geometry.Projective.Hermitian.Formula.BoundaryFormula)
    (refines : current.Refines bounding) (sample : Purelib.Data.Gaussian.Basic.Canonical)
    (sampleInside : current.Contains sample) :
    Reinspection bounding current refines sample sampleInside
      overrides
      formula :=
  match formula with
  | .truth => .stable .truth
  | .falsity => .stable .falsity
  | .atom value =>
      match found : Purelib.Geometry.Projective.Hermitian.Formula.Box.findOverride overrides value with
      | some stability => .stable (.atom value stability)
      | none =>
          match result : Purelib.Geometry.Projective.Hermitian.Box.certificate?
              value.form bounding current refines sample sampleInside with
          | none => .unresolved value (by exact List.Mem.head []) found result
          | some certificate => .stable (.atom value (.strict certificate))
  | .and left right =>
      match inspectWith bounding current overrides left refines sample
          sampleInside with
      | .unresolved atom member notResolved failure =>
          .unresolved atom (by
            exact Purelib.Data.List.Membership.mem_append.mpr (Or.inl member)) notResolved failure
      | .stable leftStable =>
          match inspectWith bounding current overrides right refines
            sample
              sampleInside with
          | .unresolved atom member notResolved failure =>
              .unresolved atom (by
                exact Purelib.Data.List.Membership.mem_append.mpr (Or.inr member)) notResolved failure
          | .stable rightStable => .stable (.and leftStable rightStable)
  | .or left right =>
      match inspectWith bounding current overrides left refines sample
          sampleInside with
      | .unresolved atom member notResolved failure =>
          .unresolved atom (by
            exact Purelib.Data.List.Membership.mem_append.mpr (Or.inl member)) notResolved failure
      | .stable leftStable =>
          match inspectWith bounding current overrides right refines
            sample
              sampleInside with
          | .unresolved atom member notResolved failure =>
              .unresolved atom (by
                exact Purelib.Data.List.Membership.mem_append.mpr (Or.inr member)) notResolved failure
          | .stable rightStable => .stable (.or leftStable rightStable)

end Purelib.Geometry.Projective.Hermitian.Formula.Box

end
