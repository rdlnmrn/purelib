module
import Purelib.Data.Rat.Fraction
import Purelib.Data.CCL.Progressive.Cursor.Image
import Purelib.Data.CCL.Transducer.Mode.Semantics
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RationalFunctions.ArgumentPrinciple.CCL.Basic
public import Purelib.RootIsolation.Multiplicity.Side.CCL.Persistent
public import Purelib.RationalFunctions.ArgumentPrinciple.CCL.Index

open Purelib.RootIsolation.Multiplicity.Side.CCL
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients

section
public section

/-!
# CCL-2 data for the rational-function argument principle

Paper I returns exact rational sites or independently shrinking zero/pole
tracks after finite cancellation.  This module adds CCL observations to those
existing results without duplicating any RFAP isolation or winding proof.
-/

namespace Purelib.RationalFunctions.ArgumentPrinciple.CCL.Basic
namespace NonzeroResult

section
open Purelib.Polynomial
open Purelib.RootIsolation
open Purelib.RationalFunctions
/-- The persistent CCL observation state of an indexed retained zero site. -/
abbrev ZeroPersistentState
    {numerator denominator : CoefficientPolynomial}
    (result : NonzeroResult numerator denominator)
    (index : (ZeroIndex result)) :=
  Persistent.SidePersistentState result.rfap.numeratorSites result.numeratorCCL index

/-- The persistent CCL observation state of an indexed retained pole site. -/
abbrev PolePersistentState
    {numerator denominator : CoefficientPolynomial}
    (result : NonzeroResult numerator denominator)
    (index : (PoleIndex result)) :=
  Persistent.SidePersistentState result.rfap.denominatorSites result.denominatorCCL index

/-- Initialize the persistent CCL state for the selected retained zero site. -/
@[expose] def zeroPersistentInitial
    {numerator denominator : CoefficientPolynomial}
    (result : NonzeroResult numerator denominator)
    (index : (ZeroIndex result)) :
      (ZeroPersistentState result) index :=
  Persistent.sidePersistentInitial result.rfap.numeratorSites result.numeratorCCL index

/-- Initialize the persistent CCL state for the selected retained pole site. -/
@[expose] def polePersistentInitial
    {numerator denominator : CoefficientPolynomial}
    (result : NonzeroResult numerator denominator)
    (index : (PoleIndex result)) :
      (PolePersistentState result) index :=
  Persistent.sidePersistentInitial result.rfap.denominatorSites result.denominatorCCL index

end

section
open Purelib.Data
open Purelib.Polynomial
section
open Purelib.RootIsolation
open Purelib.RationalFunctions
/-- Refine an existing zero-site observation to a positive accuracy request and requested bit count.

The resulting state remains indexed by the same retained zero site and CCL family. -/
@[expose] def zeroPersistentRequest
    {numerator denominator : CoefficientPolynomial}
    (result : NonzeroResult numerator denominator)
    (index : (ZeroIndex result)) (current :
      (ZeroPersistentState result) index)
    (epsilon : Rat.Fraction.Rational)
    (positive : 0 < epsilon) (count : Nat) :
    (ZeroPersistentState result) index :=
  Persistent.sidePersistentRequest result.rfap.numeratorSites result.numeratorCCL index
    current epsilon positive count

/-- Refine an existing pole-site observation to a positive accuracy request and requested bit count.

The resulting state remains indexed by the same retained pole site and CCL family. -/
@[expose] def polePersistentRequest
    {numerator denominator : CoefficientPolynomial}
    (result : NonzeroResult numerator denominator)
    (index : (PoleIndex result)) (current :
      (PolePersistentState result) index)
    (epsilon : Rat.Fraction.Rational)
    (positive : 0 < epsilon) (count : Nat) :
    (PolePersistentState result) index :=
  Persistent.sidePersistentRequest result.rfap.denominatorSites result.denominatorCCL index
    current epsilon positive count

/-- A persistent zero-site request extends the emitted word of its input state. -/
theorem zeroPersistentRequest_word_extends
    {numerator denominator : CoefficientPolynomial}
    (result : NonzeroResult numerator denominator)
    (index : (ZeroIndex result)) (current :
      (ZeroPersistentState result) index)
    (epsilon : Rat.Fraction.Rational)
    (positive : 0 < epsilon) (count : Nat) :
    (Persistent.sidePersistentMachine result.rfap.numeratorSites result.numeratorCCL index
      current).emitted.IsPrefix
      (Persistent.sidePersistentMachine result.rfap.numeratorSites result.numeratorCCL index
        ((zeroPersistentRequest result) index current epsilon positive
          count)).emitted :=
  Persistent.sidePersistentRequest_word_extends result.rfap.numeratorSites
    result.numeratorCCL index current epsilon positive count

/-- A persistent pole-site request extends the emitted word of its input state. -/
theorem polePersistentRequest_word_extends
    {numerator denominator : CoefficientPolynomial}
    (result : NonzeroResult numerator denominator)
    (index : (PoleIndex result)) (current :
      (PolePersistentState result) index)
    (epsilon : Rat.Fraction.Rational)
    (positive : 0 < epsilon) (count : Nat) :
    (Persistent.sidePersistentMachine result.rfap.denominatorSites result.denominatorCCL index
      current).emitted.IsPrefix
      (Persistent.sidePersistentMachine result.rfap.denominatorSites result.denominatorCCL index
        ((polePersistentRequest result) index current epsilon positive
          count)).emitted :=
  Persistent.sidePersistentRequest_word_extends result.rfap.denominatorSites
    result.denominatorCCL index current epsilon positive count

/-- Any retained box returned by a zero-site request has squared diagonal at most epsilon squared.

An exact-site observation may have no box; the statement then has no additional box obligation. -/
theorem zeroPersistentRequest_box_accurate
    {numerator denominator : CoefficientPolynomial}
    (result : NonzeroResult numerator denominator)
    (index : (ZeroIndex result)) (current :
      (ZeroPersistentState result) index)
    (epsilon : Rat.Fraction.Rational)
    (positive : 0 < epsilon) (count : Nat) :
    match Persistent.sidePersistentBox? result.rfap.numeratorSites result.numeratorCCL index
      ((zeroPersistentRequest result) index current epsilon positive count)
        with
    | none => True
    | some box => box.diagonalSq ≤ epsilon ^ 2 :=
  Persistent.sidePersistentRequest_box_accurate result.rfap.numeratorSites
    result.numeratorCCL index current epsilon positive count

/-- Any retained box returned by a pole-site request has squared diagonal at most epsilon squared.

An exact-site observation may have no box; the statement then has no additional box obligation. -/
theorem polePersistentRequest_box_accurate
    {numerator denominator : CoefficientPolynomial}
    (result : NonzeroResult numerator denominator)
    (index : (PoleIndex result)) (current :
      (PolePersistentState result) index)
    (epsilon : Rat.Fraction.Rational)
    (positive : 0 < epsilon) (count : Nat) :
    match Persistent.sidePersistentBox? result.rfap.denominatorSites result.denominatorCCL
      index ((polePersistentRequest result) index current epsilon positive
        count) with
    | none => True
    | some box => box.diagonalSq ≤ epsilon ^ 2 :=
  Persistent.sidePersistentRequest_box_accurate result.rfap.denominatorSites
    result.denominatorCCL index current epsilon positive count

end

open Purelib.Geometry
open Purelib.RootIsolation
open Purelib.RationalFunctions
/-- The requested zero-site cylinder has squared chordal diameter at most epsilon squared.

Both displayed values are possible in the resulting semantic mode; their images use that exact persistent machine. -/
theorem zeroPersistentRequest_cylinder_accurate
    {numerator denominator : CoefficientPolynomial}
    (result : NonzeroResult numerator denominator)
    (index : (ZeroIndex result)) (current :
      (ZeroPersistentState result) index)
    (epsilon : Rat.Fraction.Rational)
    (positive : 0 < epsilon) (count : Nat)
    {left right : Gaussian.Basic.Canonical}
    (leftPossible :
      CCL.Transducer.Mode.Semantics.SemanticMode.possible
        (Persistent.sidePersistentMachine result.rfap.numeratorSites result.numeratorCCL index
          ((zeroPersistentRequest result) index current epsilon positive
            count)).mode
        left)
    (rightPossible :
      CCL.Transducer.Mode.Semantics.SemanticMode.possible
        (Persistent.sidePersistentMachine result.rfap.numeratorSites result.numeratorCCL index
          ((zeroPersistentRequest result) index current epsilon positive
            count)).mode
        right) :
    Projective.Chordal.Basic.chordalSq
        (CCL.Progressive.Cursor.Image.Machine.image
          (Persistent.sidePersistentMachine result.rfap.numeratorSites result.numeratorCCL
            index ((zeroPersistentRequest result) index current epsilon
              positive count))
          left)
        (CCL.Progressive.Cursor.Image.Machine.image
          (Persistent.sidePersistentMachine result.rfap.numeratorSites result.numeratorCCL
            index ((zeroPersistentRequest result) index current epsilon
              positive count))
          right) ≤ epsilon ^ 2 :=
  Persistent.sidePersistentRequest_cylinder_accurate result.rfap.numeratorSites
    result.numeratorCCL index current epsilon positive count
      leftPossible rightPossible

/-- The requested pole-site cylinder has squared chordal diameter at most epsilon squared.

Both displayed values are possible in the resulting semantic mode; their images use that exact persistent machine. -/
theorem polePersistentRequest_cylinder_accurate
    {numerator denominator : CoefficientPolynomial}
    (result : NonzeroResult numerator denominator)
    (index : (PoleIndex result)) (current :
      (PolePersistentState result) index)
    (epsilon : Rat.Fraction.Rational)
    (positive : 0 < epsilon) (count : Nat)
    {left right : Gaussian.Basic.Canonical}
    (leftPossible :
      CCL.Transducer.Mode.Semantics.SemanticMode.possible
        (Persistent.sidePersistentMachine result.rfap.denominatorSites result.denominatorCCL
          index ((polePersistentRequest result) index current epsilon positive
            count)).mode
        left)
    (rightPossible :
      CCL.Transducer.Mode.Semantics.SemanticMode.possible
        (Persistent.sidePersistentMachine result.rfap.denominatorSites result.denominatorCCL
          index ((polePersistentRequest result) index current epsilon positive
            count)).mode
        right) :
    Projective.Chordal.Basic.chordalSq
        (CCL.Progressive.Cursor.Image.Machine.image
          (Persistent.sidePersistentMachine result.rfap.denominatorSites result.denominatorCCL
            index ((polePersistentRequest result) index current epsilon
              positive count))
          left)
        (CCL.Progressive.Cursor.Image.Machine.image
          (Persistent.sidePersistentMachine result.rfap.denominatorSites result.denominatorCCL
            index ((polePersistentRequest result) index current epsilon
              positive count))
          right) ≤ epsilon ^ 2 :=
  Persistent.sidePersistentRequest_cylinder_accurate result.rfap.denominatorSites
    result.denominatorCCL index current epsilon positive count
      leftPossible rightPossible
end

end NonzeroResult
end Purelib.RationalFunctions.ArgumentPrinciple.CCL.Basic

end
