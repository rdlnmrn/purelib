module

public import Purelib.Geometry.Projective.Hermitian.Box.Neighborhood
import Purelib.Data.List.Map
import Purelib.Data.List.Membership

/-!
# Proper rational neighbourhoods with a constant finite formula

A finite formula supplies its original ordered atom forms to the regular
sampling and sign-neighbourhood constructors. Structural stability retains
each atom's exact sign convention, including universal zero forms.
-/

public section

namespace Purelib.Geometry.Projective.Hermitian.Formula.Box

open Purelib.Data
open Purelib.Geometry
open Purelib.Geometry.Projective.Hermitian

namespace Stable

/-- Assemble structural formula stability from certificates for every original atom occurrence. -/
def ofAtoms {bounding current : Rational.Box} :
    (formula : BoundaryFormula) →
    (∀ atom ∈ formula.atoms, AtomStability atom bounding current) → Stable bounding current formula
  | BoundaryFormula.truth, _ => .truth
  | BoundaryFormula.falsity, _ => .falsity
  | BoundaryFormula.atom testAtom, certificates => .atom testAtom (certificates testAtom (List.Mem.head []))
  | BoundaryFormula.and left right, certificates =>
      .and
        (ofAtoms left fun atom member => certificates atom
          (List.Membership.mem_append.mpr (Or.inl member)))
        (ofAtoms right fun atom member => certificates atom
          (List.Membership.mem_append.mpr (Or.inr member)))
  | BoundaryFormula.or left right, certificates =>
      .or
        (ofAtoms left fun atom member => certificates atom
          (List.Membership.mem_append.mpr (Or.inl member)))
        (ofAtoms right fun atom member => certificates atom
          (List.Membership.mem_append.mpr (Or.inr member)))

end Stable

set_option genInjectivity false in
/-- Retain a proper strictly nested box on which one original finite Hermitian formula has constant truth.

The original ordered atom-form family owns the exact retained sample,
restriction polynomials, product and sign payments. Structural stability
uses those same original forms and preserves every atom's sign tag.
-/
structure Neighborhood (formula : BoundaryFormula) (outer : Rational.Box) where
  /-- The actual retained sign neighbourhood for the original formula's atom forms. -/ signs :
    Hermitian.Box.SignNeighborhood (formula.atoms.map (fun atom => atom.form)) outer
  /-- The original formula is stable on the exact returned sign-neighbourhood box. -/ stable :
    Stable outer signs.box formula

namespace Neighborhood

/-- Compute a proper neighbourhood with a constant original formula using a finite regular rational sample. -/
def ofFormula (formula : BoundaryFormula) (outer : Rational.Box) (proper : outer.Proper) :
    Neighborhood formula outer := by
  let forms := formula.atoms.map (fun atom => atom.form)
  let sample := Hermitian.Box.sampleAvoidingForms forms outer proper
  let signs := (Hermitian.Box.signNeighborhoodOfSample sample).1
  refine ⟨signs, Stable.ofAtoms formula ?_⟩
  intro atom member
  have formMember : atom.form ∈ forms := List.Map.mem_map_of_mem (f := fun retained => retained.form) member
  exact (signs.formStability atom.form formMember).toAtom

/-- Project the actual cached proper box from the original formula neighbourhood. -/
@[expose] def box {formula : BoundaryFormula} {outer : Rational.Box}
    (neighborhood : Neighborhood formula outer) : Rational.Box := neighborhood.signs.box

/-- Project the exact retained rational sample without repeating its finite search. -/
@[expose] def sample {formula : BoundaryFormula} {outer : Rational.Box}
    (neighborhood : Neighborhood formula outer) : Gaussian.Basic.Canonical := neighborhood.signs.sample.point

/-- The projected box retains the original strict positive-width certificate. -/
theorem proper {formula : BoundaryFormula} {outer : Rational.Box}
    (neighborhood : Neighborhood formula outer) : neighborhood.box.Proper := neighborhood.signs.proper

/-- The projected box retains its strict nesting inside the original parent. -/
theorem nested {formula : BoundaryFormula} {outer : Rational.Box}
    (neighborhood : Neighborhood formula outer) : neighborhood.box.StrictInterior outer := neighborhood.signs.nested

/-- The projected sample remains strictly inside the actual projected box. -/
theorem sampleInside {formula : BoundaryFormula} {outer : Rational.Box}
    (neighborhood : Neighborhood formula outer) : neighborhood.box.StrictContains neighborhood.sample :=
  neighborhood.signs.sampleInside

/-- The original formula holds at any point of the returned box exactly when it holds at the same retained sample. -/
theorem holds_iff_sample {formula : BoundaryFormula} {outer : Rational.Box}
    (neighborhood : Neighborhood formula outer) {point : Gaussian.Basic.Canonical}
    (inside : neighborhood.box.Contains point) : formula.Holds point ↔ formula.Holds neighborhood.sample :=
  neighborhood.stable.holds_iff inside
    ⟨neighborhood.sampleInside.1.le, neighborhood.sampleInside.2.1.le,
      neighborhood.sampleInside.2.2.1.le, neighborhood.sampleInside.2.2.2.le⟩

end Neighborhood

end Purelib.Geometry.Projective.Hermitian.Formula.Box
