module

public import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
public import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
public import Purelib.Riemann.Integration.PreparedCoveredParentLists

/-! # Original covering patches at retained bounded parent occurrences

Lookup follows the original CoveredParents spine. It returns the same
prepared patch and physical endpoint-containment certificate at the exact
parent list occurrence, without another preparation or owner query.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredParents

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}

/-- Transport the complete original covering spine along an exact equality of its original parent list. -/
@[expose] def castParents {first second : List (CenteredEdge curve differential)}
    (covered : CoveredParents count first) (equal : first = second) : CoveredParents count second := by
  cases equal
  exact covered

/-- Exact parent-list transport retains every original covering patch and witness heterogeneously. -/
theorem castParents_heq {first second : List (CenteredEdge curve differential)}
    (equal : first = second) (covered : CoveredParents count first) : HEq (covered.castParents equal) covered := by
  cases equal
  rfl

/-- The original whole-cover parent transport equals ordinary equality transport on that SAME cache. -/
theorem castParents_eq_mp {first second : List (CenteredEdge curve differential)}
    (covered : CoveredParents count first) (equal : first = second) :
    covered.castParents equal = Eq.mp (congrArg (CoveredParents count) equal) covered := by
  cases equal
  rfl

/-- Concatenate the SAME original covering patches in literal parent order.

The existing first covering spine supplies each retained patch and finish
witness. Its terminal nil returns the unchanged second spine; no patch,
neighborhood or containment inspection is executed.
-/
abbrev append {first second : List (CenteredEdge curve differential)}
    (covered : CoveredParents count first) (remaining : CoveredParents count second) :
    CoveredParents count (first ++ second) :=
  Purelib.Riemann.Integration.PreparedCoveredParentLists.CoveredParents.append covered remaining

/-- Read the original patch and finish admission at one exact retained parent-list occurrence. -/
@[expose] def entry : {parents : List (CenteredEdge curve differential)} →
    CoveredParents count parents → (index : Fin parents.length) →
    { patch : PreparedPatch (parents[index.val]'index.isLt) //
      (patch.neighborhood count).box.Contains ((parents[index.val]'index.isLt).edge.point 1) }
  | [], .nil, index => Fin.elim0 index
  | _ :: _remaining, .cons patch inside tail, index =>
      Fin.cases ⟨patch, inside⟩ (fun next => entry tail next) index

/-- The zero occurrence retains the complete original covering patch and containment certificate. -/
theorem entry_zero {parent : CenteredEdge curve differential} {parents : List (CenteredEdge curve differential)}
    (patch : PreparedPatch parent) (inside : (patch.neighborhood count).box.Contains (parent.edge.point 1))
    (tail : CoveredParents count parents) :
    (CoveredParents.cons patch inside tail).entry 0 = ⟨patch, inside⟩ := by rfl

/-- A successor occurrence reads the identical original tail patch without visiting another producer. -/
theorem entry_succ {parent : CenteredEdge curve differential} {parents : List (CenteredEdge curve differential)}
    (patch : PreparedPatch parent) (inside : (patch.neighborhood count).box.Contains (parent.edge.point 1))
    (tail : CoveredParents count parents) (index : Fin parents.length) :
    (CoveredParents.cons patch inside tail).entry index.succ = tail.entry index := by rfl

end Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredParents

end
