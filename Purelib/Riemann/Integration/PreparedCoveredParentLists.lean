module
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

public import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
public import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Riemann.Integration.UniformPrimitiveNeighborhoods
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Integration.PreparedSubdivisionAutomaticModels
import Purelib.Riemann.Normalization.ContinuedInverseRoot

@[expose] public section

/-!
# Primitive covers of the actual centered and recast parent lists

The cover reads the retained segment budgets and preparation spine.  Recasting
to another basis differential reuses the same root seeds, bounds and boxes;
only the coefficient centers are changed by the existing recaster.
-/

namespace Purelib.Riemann.Integration.PreparedCoveredParentLists.CoveredParents

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {source :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

open Purelib.Curves.Hyperelliptic.Integration in
/-- Retain the actual concatenated list together with its original coverage and exact suffix identity.

The empty case consumes the second covering spine's own parent readback.
Every nonempty case retains the same original patch and actual cached tail;
no centered numerical producer is called to supply an implicit suffix index.
-/
def appendCache {first second : List (CenteredEdge curve source)}
    (covered : CoveredParents count first) (tail : CoveredParents count second) :
    Σ data : List (CenteredEdge curve source), {_covered : CoveredParents count data // data = first ++ second} :=
  match covered with
  | .nil => ⟨tail.parentList, ⟨Eq.mp (congrArg (CoveredParents count) tail.parentList_eq.symm) tail,
      tail.parentList_eq⟩⟩
  | .cons patch inside rest =>
      let joined := appendCache rest tail
      ⟨_ :: joined.1, ⟨.cons patch inside joined.2.val, congrArg (List.cons _) joined.2.property⟩⟩

/-- Concatenate primitive cover certificates in the exact order of their original parent lists.

The actual retained concatenation supplies every dependent tail index.
Structural readback keeps each original patch and containment proof while
preserving the complete original output at the specified concatenation.
-/
def append {first second : List (CenteredEdge curve source)}
    (covered : CoveredParents count first) (tail : CoveredParents count second) :
    CoveredParents count (first ++ second) :=
  let joined := appendCache covered tail
  Eq.mp (congrArg (CoveredParents count) joined.2.property) joined.2.val

/-- An empty covered prefix preserves the entire original suffix covering spine. -/
theorem append_nil {remaining : List (CenteredEdge curve source)} (tail : CoveredParents count remaining) :
    append (.nil : CoveredParents count []) tail = tail := by cases tail <;> rfl

/-- Exact list transport changes only a covered cons tail, preserving its actual patch and endpoint evidence. -/
private theorem cast_cons {parent : CenteredEdge curve source} {first second : List (CenteredEdge curve source)}
    (same : first = second) (patch : PreparedPatch parent)
    (inside : (patch.neighborhood count).box.Contains (parent.edge.point 1)) (tail : CoveredParents count first) :
    Eq.mp (congrArg (CoveredParents count) (congrArg (List.cons parent) same)) (.cons patch inside tail) =
      CoveredParents.cons patch inside (Eq.mp (congrArg (CoveredParents count) same) tail) := by
  cases same
  rfl

/-- A covered cons retains the exact original head patch and recursively appended suffix. -/
theorem append_cons {parent : CenteredEdge curve source} {first second : List (CenteredEdge curve source)}
    (patch : PreparedPatch parent) (inside : (patch.neighborhood count).box.Contains (parent.edge.point 1))
    (rest : CoveredParents count first) (tail : CoveredParents count second) :
    append (.cons patch inside rest) tail = CoveredParents.cons patch inside (append rest tail) := by
  change Eq.mp (congrArg (CoveredParents count) (congrArg (List.cons parent) (appendCache rest tail).2.property))
    (.cons patch inside (appendCache rest tail).2.val) = _
  exact cast_cons (appendCache rest tail).2.property patch inside (appendCache rest tail).2.val

open Purelib.Curves.Hyperelliptic in
open Purelib.Curves.Hyperelliptic.Integration in
/-- Change the differential of a covered parent list while retaining its original geometric patches.

Each recast centered edge reuses the original bounds, seed and containment certificate, with unchanged parent ordering.
-/
def recast (target : Differentials.Basic.Differential genus) : ∀ {parents : List (CenteredEdge curve source)},
    Observation.UniformPreparedMesh.CoveredParents count parents → Observation.UniformPreparedMesh.CoveredParents count
      (parents.map (recastCenteredEdge target))
  | _, .nil => .nil
  | _, .cons patch inside remaining =>
      .cons ⟨patch.bounds, patch.seed⟩ inside (recast target remaining)

end Purelib.Riemann.Integration.PreparedCoveredParentLists.CoveredParents

namespace Purelib.Riemann.Integration.PreparedCoveredParentLists.PrimitiveCover

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.PreparedPath (PrimitiveCover)
open Purelib.Riemann.Paths.PreparedClearPathModels (PreparedPath Owner)
open Purelib.Data.Gaussian in
/-- The exact rational Gaussian carrier. -/
private abbrev Gaussian := Basic.Canonical
/-- The original rational Gaussian box carrier. -/
private abbrev Box := Purelib.Geometry.Rational.Box
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedCoveredParentLists.CoveredParents (append)

open Purelib.Curves.Hyperelliptic in
open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
/-- Construct covered centered parents from the exact primitive cover of an original prepared path.

The original curve, differential, sheet and count determine each centered segment. Its mesh-edge equation supplies the
subdivision cover, which is appended to the recursively retained tail. -/
def coveredParents {genus : Nat} (curve : Basic.HyperellipticCurve genus) (source : Differentials.Basic.Differential
  genus)
    (sheet : Fin 2) (count : Nat) {ambient : Box} :
    ∀ {start finish : Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
      {owner : Owner (curve.polynomial.eval start)} {prepared : PreparedPath path owner},
      PrimitiveCover prepared →
        Observation.UniformPreparedMesh.CoveredParents count (CenteredPathChain.ofPreparedPath curve source sheet
          prepared).parents
  | _, _, _, _, _, .nil _ _ => .nil
  | _, _, _, _, _, .cons bounds mesh meshEq remaining => by
      change Observation.UniformPreparedMesh.CoveredParents count ((CenteredPathChain.dataOfCompleteSegment curve source
        sheet _).parents ++ _)
      rw [CenteredPathChain.dataOfCompleteSegment_parents]
      exact append (Observation.UniformPreparedMesh.CoveredParents.ofSubdivision bounds mesh sheet count _ _ (fun edge
        member => by
        rw [meshEq] at member
        exact member)) (coveredParents curve source sheet count remaining)

end Purelib.Riemann.Integration.PreparedCoveredParentLists.PrimitiveCover
