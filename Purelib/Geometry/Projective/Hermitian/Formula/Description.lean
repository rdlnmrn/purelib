module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Data.List.Search
import Purelib.Data.List.Map
import Purelib.Geometry.Projective.Hermitian.Atom
public import Purelib.Geometry.Projective.Hermitian.Boundary.Description
public import Purelib.Geometry.Projective.Hermitian.Formula.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix
public import Init.Data.List.Find
import Init.Data.List.Lemmas
import Init.Prelude
import Purelib.Geometry.Projective.Hermitian.Basic

public section

open Purelib

open Purelib.Data.List

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Hermitian

open Purelib.Geometry.Projective.Hermitian.Boundary

open Purelib.LinearAlgebra.Coordinates2.Matrix

/-!
# Boundary provenance for finite CCL formulas

This module follows the syntax tree of each next-bit formula.  Every atom is
paired with a constructive description of its exact zero boundary.  Formula
inspection can therefore hand an unresolved atom directly to the finite
curve-event layer without guessing its geometric origin from coefficients.
-/

namespace Purelib.Geometry.Projective.Hermitian.Formula

set_option genInjectivity false in
/-- One formula atom with its exact boundary provenance and the shared affine denominator matrix used by every
parameterized source. -/
structure DescribedAtom (reference :
  GaussianMatrix) where
  /-- The retained formula atom. -/ atom : Hermitian.Atom
  /-- The zero-boundary description of this exact atom form. -/ boundary : Boundary.BoundaryDescription reference
    atom.form

constructive_injectivity DescribedAtom

set_option genInjectivity false in
/-- Boundary descriptions in exactly the same finite order as `Purelib.CCL.Boundary.Formula.BoundaryFormula.atoms`. -/
structure Descriptions (reference :
  GaussianMatrix) (formula : Formula.BoundaryFormula) where
  /-- The retained descriptions in formula atom order. -/ entries : List
    (DescribedAtom reference)
  /-- Reading the entry atoms gives exactly the formula atom list. -/ atoms_eq : entries.map (fun entry => entry.atom) =
    formula.atoms

constructive_injectivity Descriptions

namespace Descriptions

/-- The true formula has an empty boundary-description list. -/
@[expose] def truth {reference :
  GaussianMatrix} : Descriptions reference .truth := ⟨[],
  rfl⟩
/-- The false formula has an empty boundary-description list. -/
@[expose] def falsity {reference :
  GaussianMatrix} : Descriptions reference .falsity := ⟨[],
  rfl⟩

/-- Pair a single atom with its supplied boundary description. -/
@[expose] def atom {reference :
  GaussianMatrix} (value : Hermitian.Atom)
    (boundary : Boundary.BoundaryDescription reference value.form) :
    Descriptions reference (.atom value) :=
  ⟨[⟨value, boundary⟩], rfl⟩

/-- Append the left and right boundary descriptions in conjunction order. -/
@[expose] def and {reference :
  GaussianMatrix} {left right : Formula.BoundaryFormula}
    (leftDescriptions : Descriptions reference left)
    (rightDescriptions : Descriptions reference right) :
    Descriptions reference (.and left right) :=
  ⟨leftDescriptions.entries ++ rightDescriptions.entries, by
    rw [Purelib.Data.List.Map.map_append, leftDescriptions.atoms_eq,
      rightDescriptions.atoms_eq]
    rfl⟩

/-- Append the left and right boundary descriptions in disjunction order. -/
@[expose] def or {reference :
  GaussianMatrix} {left right : Formula.BoundaryFormula}
    (leftDescriptions : Descriptions reference left)
    (rightDescriptions : Descriptions reference right) :
    Descriptions reference (.or left right) :=
  ⟨leftDescriptions.entries ++ rightDescriptions.entries, by
    rw [Purelib.Data.List.Map.map_append, leftDescriptions.atoms_eq,
      rightDescriptions.atoms_eq]
    rfl⟩

/-- Transport the retained descriptions along an equality of formulas. -/
@[expose] def cast {reference :
  GaussianMatrix} {left right : Formula.BoundaryFormula} (equal : left = right)
    (descriptions : Descriptions reference left) :
    Descriptions reference right := by
  subst right
  exact descriptions

/-- Search for the first entry whose retained atom equals the target. -/
@[expose] def find? {reference :
  GaussianMatrix} {formula : Formula.BoundaryFormula}
    (descriptions : Descriptions reference formula)
    (target : Hermitian.Atom) : Option (DescribedAtom reference) :=
  descriptions.entries.find? fun entry => decide (entry.atom = target)

/-- Every atom occurring in the formula has a successful boundary-description lookup. -/
theorem find?_isSome_of_mem
    {reference : GaussianMatrix} {formula : Formula.BoundaryFormula}
    (descriptions : Descriptions reference formula)
    (target : Hermitian.Atom) (member : target ∈ formula.atoms) :
    (descriptions.find? target).isSome := by
  apply Search.find?_isSome.mpr
  have mappedMember : target ∈
      descriptions.entries.map (fun entry => entry.atom) := by
    rw [descriptions.atoms_eq]
    exact member
  rcases Map.mem_map.mp mappedMember with ⟨entry, entryMember, equal⟩
  refine ⟨entry, entryMember, ?_⟩
  exact decide_eq_true equal

set_option genInjectivity false in
/-- A selected boundary entry retaining equality with the requested atom. -/
structure Selected (reference :
  GaussianMatrix) (target : Hermitian.Atom) where
  /-- The selected entry with its retained boundary description. -/ entry :
    DescribedAtom reference
  /-- The entry describes exactly the requested atom. -/ equal : entry.atom = target

constructive_injectivity Selected

/-- Computationally select the description at a proved atom occurrence. -/
@[expose] def select {reference :
  GaussianMatrix} {formula : Formula.BoundaryFormula}
    (descriptions : Descriptions reference formula)
    (target : Hermitian.Atom) (member : target ∈ formula.atoms) :
    Selected reference target := by
  match found : descriptions.find? target with
  | none =>
      have impossible : False := by
        have present := descriptions.find?_isSome_of_mem target member
        rw [found] at present
        exact Bool.noConfusion present
      exact impossible.elim
  | some entry =>
      have checked := Search.find?_eq_some_accepts_certificate found
      change decide (entry.atom = target) = true at checked
      exact ⟨entry, of_decide_eq_true checked⟩

/-- Exact boundary description of a proved formula atom occurrence. -/
@[expose] def boundaryFor
    {reference : GaussianMatrix} {formula : Formula.BoundaryFormula}
    (descriptions : Descriptions reference formula)
    (target : Hermitian.Atom) (member : target ∈ formula.atoms) :
    Boundary.BoundaryDescription reference target.form := by
  let selected := descriptions.select target member
  exact BoundaryDescription.cast
    (congrArg (fun atom : Hermitian.Atom => atom.form) selected.equal)
    selected.entry.boundary

end Descriptions
end Purelib.Geometry.Projective.Hermitian.Formula

end
