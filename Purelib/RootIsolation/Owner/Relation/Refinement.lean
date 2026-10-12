module
import Purelib.RootIsolation.Owner.Family.Basic
public import Purelib.RootIsolation.Owner.Family.Refinement
public import Purelib.Approximation.Relation.Refinement
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
public import Purelib.RootIsolation.Owner.Relation.Basic
import Purelib.Geometry.Rational.Box.Relation
import Purelib.Approximation.Relation.Fibre
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.Owner.Local.Basic

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation.Owner.Family.Basic (OwnerFamily)

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Persistent polynomial roots as a finite multivalued relation

The simple-root chamber already supplies the strongest collision-free case:
degree-many pairwise-separated rational owner boxes with fixed persistent
indices.  This adapter exposes those owners through the generic finite
relation interface while retaining exact box refinement as the continuation
witness.
-/

namespace Purelib.RootIsolation.Owner.Relation.Refinement

/-- The same underlying finite label transported between two owner fibres
whose common count is explicit at this adapter boundary. -/
def sameLabelForward
    {firstPolynomial secondPolynomial : CoefficientPolynomial}
      {count : Nat}
    (first : OwnerFamily firstPolynomial count)
    (second : OwnerFamily secondPolynomial count) :
    Fin (Owner.Relation.Basic.ownerFibre first).count → Fin (Owner.Relation.Basic.ownerFibre second).count :=
  Fin.cast (by rw [Owner.Relation.Basic.ownerFibre_count, Owner.Relation.Basic.ownerFibre_count])

/-- Transport the same finite label back between owner fibres with the supplied common count. -/
def sameLabelBackward
    {firstPolynomial secondPolynomial : CoefficientPolynomial}
      {count : Nat}
    (first : OwnerFamily firstPolynomial count)
    (second : OwnerFamily secondPolynomial count) :
    Fin (Owner.Relation.Basic.ownerFibre second).count → Fin (Owner.Relation.Basic.ownerFibre first).count :=
  Fin.cast (by rw [Owner.Relation.Basic.ownerFibre_count, Owner.Relation.Basic.ownerFibre_count])

/-- Forward transport after backward same-label transport restores the original label. -/
theorem sameLabel_rightInverse
    {firstPolynomial secondPolynomial : CoefficientPolynomial}
      {count : Nat}
    (first : OwnerFamily firstPolynomial count)
    (second : OwnerFamily secondPolynomial count)
    (label : Fin (Owner.Relation.Basic.ownerFibre second).count) :
    sameLabelForward first second (sameLabelBackward first second
      label) =
      label := by
  apply Fin.ext
  rfl

/-- Adapt a root-specific same-label nesting theorem to the generic finite
relation refinement. -/
def sameLabelRefinement
    {firstPolynomial secondPolynomial : CoefficientPolynomial}
      {count : Nat}
    (first : OwnerFamily firstPolynomial count)
    (second : OwnerFamily secondPolynomial count)
    (nested : ∀ label : Fin count,
      (second.owner label).box.Refines (first.owner label).box) :
    Approximation.Relation.Refinement (Owner.Relation.Basic.ownerFibre first)
      (Owner.Relation.Basic.ownerFibre second) Box.Relation.BoxContinues :=
  Approximation.Relation.Refinement.ofLabelEquivalence
    (sameLabelForward first second) (sameLabelBackward first second)
    (sameLabel_rightInverse first second)
    (by
      intro label
      let oldIndex : Fin count :=
        Fin.cast (Owner.Relation.Basic.ownerFibre_count first) label
      let newIndex : Fin count :=
        Fin.cast (Owner.Relation.Basic.ownerFibre_count second)
          (sameLabelForward first second label)
      have equal : newIndex = oldIndex := by
        apply Fin.ext
        rfl
      change (second.owner newIndex).box.Refines (first.owner oldIndex).box
      rw [equal]
      exact nested oldIndex)

/-- Fixed-polynomial simultaneous shrinking is a singleton-labelled finite
relation refinement. -/
def refineRelation
    {polynomial : CoefficientPolynomial} {count : Nat}
    (family : OwnerFamily polynomial count)
    (degreeAtLeastTwo : 2 ≤ polynomial.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate polynomial)
    (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) :
    Approximation.Relation.Refinement (Owner.Relation.Basic.ownerFibre family)
      (Owner.Relation.Basic.ownerFibre (family.refine degreeAtLeastTwo squarefree epsilon positive))
      Box.Relation.BoxContinues :=
  sameLabelRefinement family
    (family.refine degreeAtLeastTwo squarefree epsilon positive)
    (family.refine_nested degreeAtLeastTwo squarefree epsilon positive)
end Purelib.RootIsolation.Owner.Relation.Refinement

end
