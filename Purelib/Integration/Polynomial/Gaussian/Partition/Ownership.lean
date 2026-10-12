module
meta import Purelib.Elab.ConstructiveInjectivity
-- The source-ownership certificate publicly retains optional finite-list coordinates.
public import Purelib.Data.List.GetD
import Purelib.Data.List.Membership
import Purelib.Data.List.Map
public import Purelib.Integration.Polynomial.Gaussian.Partition.Cells
import Purelib.Integration.Polynomial.Gaussian.Partition.Child
import Purelib.Integration.Polynomial.Gaussian.Partition.Source
import Purelib.Integration.Polynomial.Gaussian.Segment.Basic
import Purelib.Integration.Polynomial.Gaussian.Partition.Segment
import Purelib.Tactic.QuotientFreeOmega

/-!
# Source-indexed Gaussian polynomial partitions

The ordered source segments retain their cut requests, child restrictions and
cached integral samples. Compilation and comparison preserve the nominal
source owners, dependent indices and exact ordered model readbacks.
-/

public section
namespace Purelib.Integration.Polynomial.Gaussian.Partition

open Purelib.Data.List

open Purelib.Integration.Polynomial.Gaussian.Segment.Basic (PolynomialSegment)
set_option genInjectivity false in
/-- A compiled child retaining its original source index, nominal source segment and dependent ownership.

The child remains indexed by that exact source segment, while the source index supports readback into the original
ordered path. -/
structure Ownership.OwnedChild where
  /-- The retained original source-segment index. -/ sourceIndex : Nat
  /-- The original nominal polynomial-segment owner. -/ source : PolynomialSegment
  /-- The retained compiled child indexed by that exact source owner. -/ child : Child source

constructive_injectivity Ownership.OwnedChild

/-- Read compiled children in original source order with retained source owners and successive source indices.

Each entry retains its nominal source and dependent child. The ordered readback advances the source index once per
segment. -/
@[expose] def Cells.CompiledCells.ownedChildren (offset : Nat) : {source : Source.PolynomialPath} → Cells.CompiledCells
  source → List Ownership.OwnedChild
  | [], .nil => []
  | source :: _, .cons head tail =>
      (head.children.map fun child => ⟨offset, source, child⟩) ++ tail.ownedChildren (offset + 1)

/-- Every retained compiled child reads back its exact source segment at the original offset-adjusted index.

Membership identifies either the retained head source or an entry in the unchanged tail. The optional coordinate reads
that exact source with the same offset-adjusted index. -/
theorem Cells.CompiledCells.ownedChildren_source (offset : Nat) :
    ∀ {source : Source.PolynomialPath} (compiled : Cells.CompiledCells source) {entry : Ownership.OwnedChild},
      entry ∈ compiled.ownedChildren offset →
        ∃ index, entry.sourceIndex = offset + index ∧ Purelib.Data.List.getElem? source index = some entry.source
  | [], .nil, _, member => by nomatch member
  | source :: rest, .cons head tail, entry, member => by
      rcases Membership.mem_append.mp member with inHead | inTail
      · obtain ⟨child, _, equal⟩ := Map.mem_map.mp inHead
        subst entry
        exact ⟨0, rfl, rfl⟩
      · obtain ⟨index, identity, lookup⟩ := tail.ownedChildren_source (offset + 1) inTail
        refine ⟨index + 1, ?_, ?_⟩
        · rw [identity]
          omega
        · exact lookup

end Purelib.Integration.Polynomial.Gaussian.Partition
end
