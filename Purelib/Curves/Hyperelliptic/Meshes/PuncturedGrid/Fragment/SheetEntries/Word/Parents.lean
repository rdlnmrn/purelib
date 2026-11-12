module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.Word.Joins
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Data.List.Append
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

/-! # The actual closed original fragment word and its signed outgoing gaps

The original SplitSheets supplies the actual parent/fragment order. One
stored word per parent shares all endpoint caches across internal,
adjacent and literal closing joins. Empty words keep the real empty root
comparison and create no fragment Point or numerical closing gap.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SplitSheets

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.PointBanks
open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes (FaceMeshBudgets FaceSharedMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
  (RegularPrimitiveFragments RegularPrimitiveSplits)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes PrimitiveSplits)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment.SheetEntry
  (Finish)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Geometry.Rectangle (AxisPartition)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest RequestedParents)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)
open Purelib.Riemann.Topology.PreparedBankRootChains.RootChain (castChildren)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum gaussianSum_append)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
variable {frames : RootFrames base.bank.grid} {source : Differential genus} {axes : PrimitiveAxes base.bank.grid}
variable {domains : FaceDomainBank frames base.faces.regulars} {target tolerance : Rational}
variable {points : List Canonical} {index : Nat}
variable {numerator : CoefficientPolynomial}
variable {budgets : FaceMeshBudgets source points tolerance (numerator := numerator) domains}
variable {numerics : Face.PrimitiveData.FacePrimitiveBank source index (numerator := numerator) domains}
variable (shared : FaceSharedMeshes (numerator := numerator) budgets numerics)

section Block

variable {parent : CenteredEdge curve source} {partition : AxisPartition 0 1 (axes.parameters parent)}
variable {fragments : RegularPrimitiveFragments axes parent partition partition.intervals}
variable {request : LocalRequest parent count target} (entries : FragmentSheets domains request fragments)

/-- One actual parent word and its original inherited point-bank inclusion and complete word factory. -/
abbrev Block :=
  Σ included : {_value : Unit // ∀ value ∈
      PointBanks.RegularPrimitiveFragments.SheetEntries.points entries, value ∈ points},
  {value : FragmentSheets.Word shared entries included.property //
    value = FragmentSheets.word shared entries included.property}

namespace Block

variable {shared entries} (kept : Block shared entries)

include kept in
/-- Read the actual inherited parent inclusion without another endpoint selection. -/
theorem included : ∀ value ∈ PointBanks.RegularPrimitiveFragments.SheetEntries.points entries, value ∈ points :=
  kept.1.property

/-- Read the same original cached parent word, all its leaves and actual internal joins. -/
@[expose] def word : FragmentSheets.Word shared entries kept.included := kept.2.val

/-- The complete parent word retains its actual original factory. -/
theorem word_eq : kept.word = FragmentSheets.word shared entries kept.included := kept.2.property

/-- Complete retained block factories identify the canonical two-field block at any proof of the same inclusion. -/
private theorem eq_fromIncluded
    (included : ∀ value ∈ PointBanks.RegularPrimitiveFragments.SheetEntries.points entries, value ∈ points) :
    kept = ⟨⟨(), included⟩, ⟨FragmentSheets.word shared entries included, rfl⟩⟩ := by
  rcases kept with ⟨⟨token, retained⟩, word⟩
  cases token
  have same : word = ⟨FragmentSheets.word shared entries retained, rfl⟩ := Subtype.ext word.property
  cases same
  rfl

section Numerator

variable {newNumerator : CoefficientPolynomial} {newIndex : Nat} {newTolerance : Rational}
variable {newBudgets : FaceMeshBudgets source points newTolerance (numerator := newNumerator) domains}
variable {newNumerics : Face.PrimitiveData.FacePrimitiveBank source newIndex
  (numerator := newNumerator) domains}
variable (newShared : FaceSharedMeshes (numerator := newNumerator) newBudgets newNumerics)

/-- Retain the SAME parent inclusion and genuine physical word while preparing its actual new-numerator values. -/
def revalue : Block newShared entries := ⟨kept.1, kept.word.revalue newShared⟩

/-- The revalued block keeps the entire original first-boundary metadata. -/
theorem revalue_first : (kept.revalue newShared).word.first = kept.word.first :=
  FragmentSheets.Word.revalue_first kept.word newShared

/-- The revalued block keeps the entire original final-boundary metadata. -/
theorem revalue_last : (kept.revalue newShared).word.last = kept.word.last :=
  FragmentSheets.Word.revalue_last kept.word newShared

/-- The actual original terminal Finish is the SAME physical cache used after numerical replacement. -/
theorem revalue_terminal_finish : HEq (kept.revalue newShared).word.terminal.finish kept.word.terminal.finish :=
  FragmentSheets.Word.revalue_terminal_finish kept.word newShared

end Numerator

end Block
end Block

/-- Exact parent-indexed products of the same supplied SplitSheets, using ordinary pairs and the empty product. -/
@[expose] def Blocks : ∀ {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
    {fragments : RegularPrimitiveSplits (base := base) axes splits} {requests : RequestedParents count target parents},
    SplitSheets domains fragments requests → Type 3
  | _, _, _, _, .nil => PUnit
  | _, _, _, _, .cons first remaining => Block shared first × Blocks remaining

/-- Construct each parent word once in literal original order using only the inherited global point inclusion. -/
def buildBlocks : ∀ {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
    {fragments : RegularPrimitiveSplits (base := base) axes splits} {requests : RequestedParents count target parents}
    (entries : SplitSheets domains fragments requests),
    (∀ value ∈ RegularPrimitiveSplits.SheetEntries.points entries, value ∈ points) → Blocks shared entries
  | _, _, _, _, .nil, _included => PUnit.unit
  | _, _, _, _, .cons first remaining, included =>
      let member : {_value : Unit // ∀ value ∈
          PointBanks.RegularPrimitiveFragments.SheetEntries.points first, value ∈ points} :=
        ⟨(), fun value present => included value (List.mem_append_left _ present)⟩
      let word : {value : FragmentSheets.Word shared first member.property //
          value = FragmentSheets.word shared first member.property} :=
        ⟨FragmentSheets.word shared first member.property, rfl⟩
      let block : Block shared first := ⟨member, word⟩
      let following := buildBlocks remaining
        (fun value present => included value (List.mem_append_right _ present))
      (block, following)

section NumeratorBlocks

variable {newNumerator : CoefficientPolynomial} {newIndex : Nat} {newTolerance : Rational}
variable {newBudgets : FaceMeshBudgets source points newTolerance (numerator := newNumerator) domains}
variable {newNumerics : Face.PrimitiveData.FacePrimitiveBank source newIndex
  (numerator := newNumerator) domains}
variable (newShared : FaceSharedMeshes (numerator := newNumerator) newBudgets newNumerics)

/-- Traverse the SAME actual parent product and reuse every retained physical block for the true new numerator.

The exact pair/PUnit recursion follows the given SplitSheets tail. Each
old parent word supplies its cached leaves and physical joins. Only the
real new numerical views and attempts are evaluated.
-/
def revalueBlocks : ∀ {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
    {fragments : RegularPrimitiveSplits (base := base) axes splits} {requests : RequestedParents count target parents}
    (entries : SplitSheets domains fragments requests) (_oldBank : Blocks shared entries)
    (included : ∀ value ∈ RegularPrimitiveSplits.SheetEntries.points entries, value ∈ points),
    {value : Blocks newShared entries // value = buildBlocks newShared entries included}
  | _, _, _, _, .nil, _oldBank, _included => ⟨PUnit.unit, rfl⟩
  | _, _, _, _, .cons first remaining, oldBank, included =>
      let block := oldBank.1.revalue newShared
      let following := revalueBlocks remaining oldBank.2
        (fun value present => included value (List.mem_append_right _ present))
      have headEq := Block.eq_fromIncluded block
        (fun value present => included value (List.mem_append_left _ present))
      ⟨(block, following.val),
        (congrArg (fun head : Block newShared first => (head, following.val)) headEq).trans
          (congrArg (fun tail : Blocks newShared remaining =>
            ((⟨⟨(), fun value present => included value (List.mem_append_left _ present)⟩,
              ⟨FragmentSheets.word newShared first
                (fun value present => included value (List.mem_append_left _ present)), rfl⟩⟩ :
                Block newShared first), tail))
            following.property)⟩

end NumeratorBlocks

/-- The exact final block, its original parent/request/fragment indices and the literal prefix decomposition. -/
abbrev LastBlock (parents : List (CenteredEdge curve source)) :=
  Σ before : List (CenteredEdge curve source),
  Σ parent : CenteredEdge curve source,
  Σ partition : AxisPartition 0 1 (axes.parameters parent),
  Σ fragments : RegularPrimitiveFragments axes parent partition partition.intervals,
  Σ request : LocalRequest parent count target,
  Σ entries : FragmentSheets domains request fragments,
  {_value : Unit // parents = before ++ [parent]} × Block shared entries

namespace LastBlock

variable {shared} {parents : List (CenteredEdge curve source)}
variable (kept : LastBlock (axes := axes) (count := count) (target := target) shared parents)

/-- Read the actual literal parent prefix preceding the final block. -/
@[expose] def before : List (CenteredEdge curve source) := kept.1

/-- Read the actual original final parent. -/
@[expose] def parent : CenteredEdge curve source := kept.2.1

/-- Read the actual original final partition. -/
@[expose] def partition : AxisPartition 0 1 (axes.parameters kept.parent) := kept.2.2.1

/-- Read the same original final regular fragment spine. -/
@[expose] def fragments : RegularPrimitiveFragments axes kept.parent kept.partition kept.partition.intervals :=
  kept.2.2.2.1

/-- Read the same actual final request. -/
@[expose] def request : LocalRequest kept.parent count target := kept.2.2.2.2.1

/-- Read the same complete original final sheet-entry spine. -/
@[expose] def entries : FragmentSheets domains kept.request kept.fragments := kept.2.2.2.2.2.1

/-- The final block belongs to this exact original parent list, with its literal preceding prefix. -/
theorem parents_eq : parents = kept.before ++ [kept.parent] := kept.2.2.2.2.2.2.1.property

/-- Read the same already prepared final block, preserving its terminal occurrence object. -/
@[expose] def block : Block shared kept.entries := kept.2.2.2.2.2.2.2

/-- Read the same final old reading, never another finish or endpoint view. -/
@[expose] def terminal : Canonical := kept.block.word.terminal.terminal

/-- The exact source prefix of the original LastBlock, without its numerator-dependent numerical block. -/
private abbrev SourceShape (parents : List (CenteredEdge curve source)) :=
  Σ before : List (CenteredEdge curve source),
  Σ parent : CenteredEdge curve source,
  Σ partition : AxisPartition 0 1 (axes.parameters parent),
  Σ fragments : RegularPrimitiveFragments axes parent partition partition.intervals,
  Σ request : LocalRequest parent count target,
  Σ _entries : FragmentSheets domains request fragments,
  {_value : Unit // parents = before ++ [parent]}

/-- Read the original nominal source metadata verbatim; no geometric or numerical producer is executed. -/
private def sourceShape : SourceShape (frames := frames) (domains := domains)
    (axes := axes) (count := count) (target := target) parents :=
  ⟨kept.before, kept.parent, kept.partition, kept.fragments, kept.request, kept.entries, ⟨(), kept.parents_eq⟩⟩

/-- Prefix one actual parent onto the same original retained source metadata. -/
private def prependShape (parent : CenteredEdge curve source)
    (following : SourceShape (frames := frames) (domains := domains)
      (axes := axes) (count := count) (target := target) parents) :
    SourceShape (frames := frames) (domains := domains)
      (axes := axes) (count := count) (target := target) (parent :: parents) :=
  ⟨parent :: following.1, following.2.1, following.2.2.1, following.2.2.2.1,
    following.2.2.2.2.1, following.2.2.2.2.2.1,
    ⟨(), congrArg (List.cons parent) following.2.2.2.2.2.2.property⟩⟩

end LastBlock

/-- Read the final actual cached block and derive its exact prefix structurally, without preparing any endpoint. -/
def lastBlock : ∀ {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
    {fragments : RegularPrimitiveSplits (base := base) axes splits} {requests : RequestedParents count target parents}
    (entries : SplitSheets domains fragments requests) (_bank : Blocks shared entries),
    parents ≠ [] → LastBlock (axes := axes) (count := count) (target := target) shared parents
  | _, _, _, _, .nil, _bank, nonempty => False.elim (nonempty rfl)
  | _, _, _, _, .cons (parent := parent) (partition := partition) (head := head) (request := request)
      first .nil, bank, _nonempty =>
      ⟨[], parent, partition, head, request, first, ⟨(), rfl⟩, bank.1⟩
  | _, _, _, _, .cons (parent := parent) _first (.cons second remaining), bank, _nonempty =>
      let following := lastBlock (.cons second remaining) bank.2 (fun equal => List.noConfusion rfl (heq_of_eq equal))
      have parentsEq : parent :: _ = (parent :: following.before) ++ [following.parent] :=
        congrArg (List.cons parent) following.parents_eq
      ⟨parent :: following.before, following.parent, following.partition, following.fragments,
        following.request, following.entries, ⟨(), parentsEq⟩, following.block⟩

section FinalReading

variable {firstParent secondParent : CenteredEdge curve source} {parents : List (CenteredEdge curve source)}
variable {firstPartition : AxisPartition 0 1 (axes.parameters firstParent)}
variable {secondPartition : AxisPartition 0 1 (axes.parameters secondParent)} {splits : PrimitiveSplits axes parents}
variable {firstFragments : RegularPrimitiveFragments axes firstParent firstPartition firstPartition.intervals}
variable {secondFragments : RegularPrimitiveFragments axes secondParent secondPartition secondPartition.intervals}
variable {tail : RegularPrimitiveSplits (base := base) axes splits}
variable {firstRequest : LocalRequest firstParent count target} {secondRequest : LocalRequest secondParent count target}
variable {requests : RequestedParents count target parents}
variable (first : FragmentSheets domains firstRequest firstFragments)
variable (second : FragmentSheets domains secondRequest secondFragments) (remaining : SplitSheets domains tail requests)
variable (bank : Blocks shared (.cons first (.cons second remaining)))

/-- Extending an abstract final-block prefix preserves its literal stored block and terminal reading. -/
private theorem terminal_prefix
    (following : LastBlock (axes := axes) (count := count) (target := target) shared (secondParent :: parents)) :
    LastBlock.terminal (axes := axes) (count := count) (target := target) (shared := shared)
      (parents := firstParent :: secondParent :: parents)
      (⟨firstParent :: following.before, following.parent, following.partition, following.fragments,
        following.request, following.entries,
        ⟨(), congrArg (List.cons firstParent) following.parents_eq⟩, following.block⟩) =
    LastBlock.terminal (axes := axes) (count := count) (target := target) (shared := shared)
      (parents := secondParent :: parents) following := rfl

/-- Prepending a source parent preserves the complete original final source tuple. -/
private theorem sourceShape_prefix
    (following : LastBlock (axes := axes) (count := count) (target := target) shared (secondParent :: parents)) :
    LastBlock.sourceShape
      (⟨firstParent :: following.before, following.parent, following.partition, following.fragments,
        following.request, following.entries,
        ⟨(), congrArg (List.cons firstParent) following.parents_eq⟩, following.block⟩ :
        LastBlock (axes := axes) (count := count) (target := target) shared
          (firstParent :: secondParent :: parents)) =
      LastBlock.prependShape firstParent (LastBlock.sourceShape following) := rfl

/-- The actual original last-block reader prepends only the literal source prefix. -/
private theorem lastBlock_sourceShape_cons :
    LastBlock.sourceShape (lastBlock shared (.cons first (.cons second remaining)) bank
      (fun equal => List.noConfusion rfl (heq_of_eq equal))) =
      LastBlock.prependShape firstParent
        (LastBlock.sourceShape (lastBlock shared (.cons second remaining) bank.2
          (fun equal => List.noConfusion rfl (heq_of_eq equal)))) := by
  let following : LastBlock (axes := axes) (count := count) (target := target) shared (secondParent :: parents) :=
    lastBlock shared (.cons second remaining) bank.2 (fun equal => List.noConfusion rfl (heq_of_eq equal))
  have actual : lastBlock shared (.cons first (.cons second remaining)) bank
      (fun equal => List.noConfusion rfl (heq_of_eq equal)) =
      (⟨firstParent :: following.before, following.parent, following.partition, following.fragments,
        following.request, following.entries,
        ⟨(), congrArg (List.cons firstParent) following.parents_eq⟩, following.block⟩ :
        LastBlock (axes := axes) (count := count) (target := target) shared
          (firstParent :: secondParent :: parents)) := rfl
  exact (congrArg (fun value : LastBlock (axes := axes) (count := count) (target := target) shared
      (firstParent :: secondParent :: parents) => LastBlock.sourceShape value) actual).trans
    (sourceShape_prefix shared following)

/-- Prepending an actual parent preserves the same stored final old reading of a nonempty tail. -/
theorem lastBlock_terminal_cons :
    LastBlock.terminal (axes := axes) (count := count) (target := target) (shared := shared)
      (parents := firstParent :: secondParent :: parents)
      (lastBlock (axes := axes) (count := count) (target := target)
        (parents := firstParent :: secondParent :: parents) shared (.cons first (.cons second remaining)) bank
        (fun equal => List.noConfusion rfl (heq_of_eq equal))) =
    LastBlock.terminal (axes := axes) (count := count) (target := target) (shared := shared)
      (parents := secondParent :: parents)
      (lastBlock (axes := axes) (count := count) (target := target)
        (parents := secondParent :: parents) shared (.cons second remaining) bank.2
        (fun equal => List.noConfusion rfl (heq_of_eq equal))) := by
  let following : LastBlock (axes := axes) (count := count) (target := target) shared (secondParent :: parents) :=
    lastBlock (axes := axes) (count := count) (target := target) (parents := secondParent :: parents)
      shared (.cons second remaining) bank.2 (fun equal => List.noConfusion rfl (heq_of_eq equal))
  have actual : lastBlock (axes := axes) (count := count) (target := target)
      (parents := firstParent :: secondParent :: parents) shared (.cons first (.cons second remaining)) bank
        (fun equal => List.noConfusion rfl (heq_of_eq equal)) =
      (⟨firstParent :: following.before, following.parent, following.partition, following.fragments,
        following.request, following.entries,
        ⟨(), congrArg (List.cons firstParent) following.parents_eq⟩, following.block⟩ :
        LastBlock (axes := axes) (count := count) (target := target) shared
          (firstParent :: secondParent :: parents)) := rfl
  exact (congrArg (fun cached : LastBlock (axes := axes) (count := count) (target := target) shared
      (firstParent :: secondParent :: parents) =>
    LastBlock.terminal (axes := axes) (count := count) (target := target) (shared := shared)
      (parents := firstParent :: secondParent :: parents) cached) actual).trans
        (terminal_prefix (firstParent := firstParent) shared following)

end FinalReading

section NumeratorFinalSource

variable {newNumerator : CoefficientPolynomial} {newIndex : Nat} {newTolerance : Rational}
variable {newBudgets : FaceMeshBudgets source points newTolerance (numerator := newNumerator) domains}
variable {newNumerics : Face.PrimitiveData.FacePrimitiveBank source newIndex
  (numerator := newNumerator) domains}
variable (newShared : FaceSharedMeshes (numerator := newNumerator) newBudgets newNumerics)

/-- The final source tuple depends on the SAME original SplitSheets, independently of its numerical bank.

This is equality of the complete original nominal parent, partition,
request and sheet-entry metadata. It is not a coordinate, sheet-label,
root-owner, primitive or integral identity.
-/
private theorem lastBlock_sourceShape_independent :
    ∀ {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
    {fragments : RegularPrimitiveSplits (base := base) axes splits} {requests : RequestedParents count target parents}
    (entries : SplitSheets domains fragments requests) (oldBank : Blocks shared entries)
    (newBank : Blocks newShared entries) (nonempty : parents ≠ []),
    LastBlock.sourceShape (lastBlock shared entries oldBank nonempty) =
      LastBlock.sourceShape (lastBlock newShared entries newBank nonempty)
  | _, _, _, _, .nil, _oldBank, _newBank, nonempty => False.elim (nonempty rfl)
  | _, _, _, _, .cons _first .nil, _oldBank, _newBank, _nonempty => rfl
  | _, _, _, _, .cons (parent := firstParent) first (.cons second remaining),
      oldBank, newBank, _nonempty =>
      (lastBlock_sourceShape_cons shared first second remaining oldBank).trans
        ((congrArg (LastBlock.prependShape (axes := axes) (count := count) (target := target) firstParent)
          (lastBlock_sourceShape_independent (.cons second remaining) oldBank.2 newBank.2
            (fun equal => List.noConfusion rfl (heq_of_eq equal)))).trans
          (lastBlock_sourceShape_cons newShared first second remaining newBank).symm)

end NumeratorFinalSource

/-- Read every literal old increment in actual original parent/fragment order. -/
@[expose] def increments : ∀ {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
    {fragments : RegularPrimitiveSplits (base := base) axes splits} {requests : RequestedParents count target parents}
    (entries : SplitSheets domains fragments requests), Blocks shared entries → List Canonical
  | _, _, _, _, .nil, _bank => []
  | _, _, _, _, .cons _first remaining, bank => bank.1.word.increments ++ increments remaining bank.2

/-- Count the literal actual fragment occurrences before or after numerical observations. -/
@[expose] def fragmentCount : ∀ {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
    {fragments : RegularPrimitiveSplits (base := base) axes splits} {requests : RequestedParents count target parents},
    SplitSheets domains fragments requests → Nat
  | _, _, _, _, .nil => 0
  | _, _, _, _, .cons (partition := partition) _first remaining =>
      partition.intervals.length + fragmentCount remaining

/-- Every actual fragment contributes exactly one stored increment, including stationary and repeated occurrences. -/
theorem increments_length : ∀ {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
    {fragments : RegularPrimitiveSplits (base := base) axes splits} {requests : RequestedParents count target parents}
    (entries : SplitSheets domains fragments requests) (bank : Blocks shared entries),
    (increments shared entries bank).length = fragmentCount entries
  | _, _, _, _, .nil, _bank => rfl
  | _, _, _, _, .cons _first remaining, bank =>
      (Data.List.Append.length_append _ _).trans
        (congrArg₂ Nat.add bank.1.word.increments_length (increments_length remaining bank.2))

/-- The ordered actual adjacent-parent joins on the given products and unchanged geometric/root suffixes. -/
@[expose] def Links : ∀ {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
    {fragments : RegularPrimitiveSplits (base := base) axes splits} {requests : RequestedParents count target parents}
    (entries : SplitSheets domains fragments requests) (_bank : Blocks shared entries)
    {start finish : LiftedPoint 2} (_geometry : CenteredPathChain parents (start := start) (finish := finish))
    {initial terminal : Named} (_roots : RootChain parents initial terminal), Type 2
  | _, _, _, _, .nil, _bank, _, _, _geometry, _, _, _roots => PUnit
  | _, _, _, _, .cons _first .nil, _bank, _, _, _geometry, _, _, _roots => PUnit
  | _, _, _, _, .cons _first (.cons second remaining), bank, _, _, geometry, _, _, roots =>
      FragmentSheets.Word.Adjacent bank.1.word bank.2.1.word geometry roots ×
        Links (.cons second remaining) bank.2 geometry.remaining roots.remaining

/-- Construct each actual adjacent-parent comparison once, reusing the SAME boundary occurrence caches. -/
def buildLinks : ∀ {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
    {fragments : RegularPrimitiveSplits (base := base) axes splits} {requests : RequestedParents count target parents}
    (entries : SplitSheets domains fragments requests) (bank : Blocks shared entries)
    {start finish : LiftedPoint 2} (geometry : CenteredPathChain parents (start := start) (finish := finish))
    {initial terminal : Named} (roots : RootChain parents initial terminal), Links shared entries bank geometry roots
  | _, _, _, _, .nil, _bank, _, _, _geometry, _, _, _roots => PUnit.unit
  | _, _, _, _, .cons _first .nil, _bank, _, _, _geometry, _, _, _roots => PUnit.unit
  | _, _, _, _, .cons _first (.cons second remaining), bank, _, _, geometry, _, _, roots =>
      let joined := FragmentSheets.Word.joinNext bank.1.word bank.2.1.word geometry roots
      let following := buildLinks (.cons second remaining) bank.2 geometry.remaining roots.remaining
      (joined, following)

section NumeratorLinks

variable {newNumerator : CoefficientPolynomial} {newIndex : Nat} {newTolerance : Rational}
variable {newBudgets : FaceMeshBudgets source points newTolerance (numerator := newNumerator) domains}
variable {newNumerics : Face.PrimitiveData.FacePrimitiveBank source newIndex
  (numerator := newNumerator) domains}
variable (newShared : FaceSharedMeshes (numerator := newNumerator) newBudgets newNumerics)

/-- Reuse every actual adjacent physical cache on the SAME geometric/root suffixes for genuine new-numerator gaps. -/
def revalueLinks : ∀ {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
    {fragments : RegularPrimitiveSplits (base := base) axes splits} {requests : RequestedParents count target parents}
    (entries : SplitSheets domains fragments requests) (oldBank : Blocks shared entries)
    (newBank : Blocks newShared entries)
    {start finish : LiftedPoint 2} (geometry : CenteredPathChain parents (start := start) (finish := finish))
    {initial terminal : Named} (roots : RootChain parents initial terminal)
    (_oldLinks : Links shared entries oldBank geometry roots),
    {value : Links newShared entries newBank geometry roots //
      value = buildLinks newShared entries newBank geometry roots}
  | _, _, _, _, .nil, _oldBank, _newBank, _, _, _geometry, _, _, _roots, _oldLinks => ⟨PUnit.unit, rfl⟩
  | _, _, _, _, .cons _first .nil, _oldBank, _newBank, _, _, _geometry, _, _, _roots, _oldLinks =>
      ⟨PUnit.unit, rfl⟩
  | _, _, _, _, .cons _first (.cons second remaining), oldBank, newBank,
      _, _, geometry, _, _, roots, oldLinks =>
      let first := FragmentSheets.Word.Adjacent.revalue
        (leftWord := oldBank.1.word) (rightWord := oldBank.2.1.word) (kept := oldLinks.1)
        (newShared := newShared) newBank.1.word newBank.2.1.word
      let remaining := revalueLinks (.cons second remaining)
        oldBank.2 newBank.2 geometry.remaining roots.remaining oldLinks.2
      ⟨(first.val, remaining.val),
        (congrArg (fun head => (head, remaining.val)) first.property).trans
          (congrArg (fun tail =>
            (FragmentSheets.Word.joinNext newBank.1.word newBank.2.1.word geometry roots, tail))
            remaining.property)⟩

end NumeratorLinks

/-- Read actual internal then adjacent gaps in their literal original word order, before the single closing slot. -/
@[expose] def openGaps : ∀ {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
    {fragments : RegularPrimitiveSplits (base := base) axes splits} {requests : RequestedParents count target parents}
    (entries : SplitSheets domains fragments requests) (bank : Blocks shared entries)
    {start finish : LiftedPoint 2} (geometry : CenteredPathChain parents (start := start) (finish := finish))
    {initial terminal : Named} (roots : RootChain parents initial terminal),
    Links shared entries bank geometry roots → List Canonical
  | _, _, _, _, .nil, _bank, _, _, _geometry, _, _, _roots, _links => []
  | _, _, _, _, .cons _first .nil, bank, _, _, _geometry, _, _, _roots, _links => bank.1.word.gaps
  | _, _, _, _, .cons _first (.cons second remaining), bank, _, _, geometry, _, _, roots, links =>
      bank.1.word.gaps ++ links.1.value ::
        openGaps (.cons second remaining) bank.2 geometry.remaining roots.remaining links.2

/-- A nonempty block has exactly one fewer internal slots than fragments. -/
private theorem count_terminal (size gapCount : Nat) (positive : 0 < size) (gapEq : gapCount = size - 1) :
    gapCount + 1 = size := by omega0

/-- Adding the next actual parent preserves the exact open-gap count. -/
private theorem count_step (size following gapCount followingGaps : Nat)
    (positive : 0 < size) (gapEq : gapCount = size - 1) (followingEq : followingGaps + 1 = following) :
    gapCount + (followingGaps + 1) + 1 = size + following := by omega0

/-- A nonempty original word has exactly one fewer open gap than its actual fragment occurrences. -/
theorem openGaps_length : ∀ {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
    {fragments : RegularPrimitiveSplits (base := base) axes splits} {requests : RequestedParents count target parents}
    (entries : SplitSheets domains fragments requests) (bank : Blocks shared entries)
    {start finish : LiftedPoint 2} (geometry : CenteredPathChain parents (start := start) (finish := finish))
    {initial terminal : Named} (roots : RootChain parents initial terminal)
    (links : Links shared entries bank geometry roots), parents ≠ [] →
    (openGaps shared entries bank geometry roots links).length + 1 = fragmentCount entries
  | _, _, _, _, .nil, _bank, _, _, _geometry, _, _, _roots, _links, nonempty => False.elim (nonempty rfl)
  | _, _, _, _, .cons _first .nil, bank, _, _, _geometry, _, _, _roots, _links, _nonempty => by
      have positive := (Nat.lt_of_le_of_lt (Nat.zero_le _) bank.1.word.first.selected.position.isLt)
      exact count_terminal _ _ positive bank.1.word.gaps_length
  | _, _, _, _, .cons _first (.cons second remaining), bank, _, _, geometry, _, _, roots, links, _nonempty => by
      have following := openGaps_length (.cons second remaining) bank.2 geometry.remaining roots.remaining links.2
        (fun equal => List.noConfusion rfl (heq_of_eq equal))
      have positive := (Nat.lt_of_le_of_lt (Nat.zero_le _) bank.1.word.first.selected.position.isLt)
      have lengthEq := Data.List.Append.length_append bank.1.word.gaps
        (links.1.value :: openGaps shared (.cons second remaining) bank.2 geometry.remaining roots.remaining links.2)
      exact (congrArg (fun value => value + 1) lengthEq).trans
        (count_step _ _ _ _ positive bank.1.word.gaps_length following)

/-- Read only the original first incoming scalar from a nonempty retained block product. -/
private def firstValue : ∀ {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
    {fragments : RegularPrimitiveSplits (base := base) axes splits} {requests : RequestedParents count target parents}
    (entries : SplitSheets domains fragments requests), Blocks shared entries → parents ≠ [] → Canonical
  | _, _, _, _, .nil, _bank, nonempty => False.elim (nonempty rfl)
  | _, _, _, _, .cons _first _remaining, bank, _nonempty => bank.1.word.initial.initial

/-- Two actual open scalar telescopes compose through their signed adjacent gap. -/
private theorem scalar_join (leftIncrement leftGaps leftFinish leftStart rightIncrement rightGaps rightFinish
    rightStart adjacent : Canonical)
    (leftEq : leftIncrement = leftGaps + (leftFinish - leftStart))
    (rightEq : rightIncrement = rightGaps + (rightFinish - rightStart))
    (adjacentEq : adjacent = leftFinish - rightStart) :
    leftIncrement + rightIncrement = leftGaps + (adjacent + rightGaps) + (rightFinish - leftStart) := by
  rewrite [leftEq, rightEq, adjacentEq]
  ring1

/-- Concatenated scalar lists telescope through the given signed adjacent difference. -/
private theorem scalar_append (leftIncrements rightIncrements leftGaps rightGaps : List Canonical)
    (leftFinish leftStart rightFinish rightStart adjacent : Canonical)
    (leftEq : gaussianSum leftIncrements = gaussianSum leftGaps + (leftFinish - leftStart))
    (rightEq : gaussianSum rightIncrements = gaussianSum rightGaps + (rightFinish - rightStart))
    (adjacentEq : adjacent = leftFinish - rightStart) :
    gaussianSum (leftIncrements ++ rightIncrements) = gaussianSum (leftGaps ++ adjacent :: rightGaps) +
      (rightFinish - leftStart) :=
  (gaussianSum_append _ _).trans
    ((scalar_join _ _ _ _ _ _ _ _ _ leftEq rightEq adjacentEq).trans
      (congrArg (fun value : Canonical => value + (rightFinish - leftStart))
        (gaussianSum_append leftGaps (adjacent :: rightGaps)).symm))

/-- The exact scalar telescope statement on the given open-word caches and literal boundary readings. -/
private def OpenTelescope {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
    {fragments : RegularPrimitiveSplits (base := base) axes splits} {requests : RequestedParents count target parents}
    (entries : SplitSheets domains fragments requests) (bank : Blocks shared entries)
    {start finish : LiftedPoint 2} (geometry : CenteredPathChain parents (start := start) (finish := finish))
    {initial terminal : Named} (roots : RootChain parents initial terminal)
    (links : Links shared entries bank geometry roots) (nonempty : parents ≠ []) : Prop :=
  gaussianSum (increments shared entries bank) = gaussianSum (openGaps shared entries bank geometry roots links) +
    ((lastBlock shared entries bank nonempty).terminal - firstValue shared entries bank nonempty)

/-- The same open-word proposition with every original index and retained cache argument free in its motive. -/
private def OpenFamily {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
    {fragments : RegularPrimitiveSplits (base := base) axes splits} {requests : RequestedParents count target parents}
    (entries : SplitSheets domains fragments requests) : Prop :=
  ∀ (bank : Blocks shared entries) {start finish : LiftedPoint 2}
    (geometry : CenteredPathChain parents (start := start) (finish := finish)) {initial terminal : Named}
    (roots : RootChain parents initial terminal) (links : Links shared entries bank geometry roots)
    (nonempty : parents ≠ []), OpenTelescope shared entries bank geometry roots links nonempty

/-- The actual open word retains the separate final-minus-initial contribution. -/
private theorem open_telescope : ∀ {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
    {fragments : RegularPrimitiveSplits (base := base) axes splits} {requests : RequestedParents count target parents}
    (entries : SplitSheets domains fragments requests) (bank : Blocks shared entries)
    {start finish : LiftedPoint 2} (geometry : CenteredPathChain parents (start := start) (finish := finish))
    {initial terminal : Named} (roots : RootChain parents initial terminal)
    (links : Links shared entries bank geometry roots) (nonempty : parents ≠ []),
    OpenTelescope shared entries bank geometry roots links nonempty := by
  intro allParents allSplits allFragments allRequests originalEntries originalBank originalStart originalFinish
    originalGeometry originalInitial originalTerminal originalRoots originalLinks originalNonempty
  refine (SplitSheets.rec
    (motive := fun {parents} {splits} fragments requests entries => OpenFamily shared entries)
    ?_ ?_ originalEntries) originalBank originalGeometry originalRoots originalLinks originalNonempty
  · intro _bank _start _finish _geometry _initial _terminal _roots _links nonempty
    exact False.elim (nonempty rfl)
  · intro _parent _parents _partition _splits _head _tail _request _requests first remaining following
    refine SplitSheets.casesOn
      (motive := fun {parents} {splits} fragments requests tail =>
        OpenFamily shared tail → OpenFamily shared (.cons first tail))
      remaining ?_ ?_ following
    · intro _following bank _start _finish _geometry _initial _terminal _roots _links _nonempty
      change gaussianSum (bank.1.word.increments ++ []) =
        gaussianSum bank.1.word.gaps + (bank.1.word.terminal.terminal - bank.1.word.initial.initial)
      exact (gaussianSum_append _ []).trans
        ((congrArg (fun value : Canonical => value + 0) bank.1.word.telescope).trans (by ring1))
    · intro _nextParent _nextParents _nextPartition _nextSplits _nextHead _nextTail
        _nextRequest _nextRequests second rest tailIH bank _start _finish geometry
        _initial _terminal roots links _nonempty
      have following := tailIH bank.2 geometry.remaining roots.remaining links.2
        (fun equal => List.noConfusion rfl (heq_of_eq equal))
      change gaussianSum (increments shared (.cons second rest) bank.2) =
        gaussianSum (openGaps shared (.cons second rest) bank.2 geometry.remaining roots.remaining links.2) +
          ((lastBlock shared (.cons second rest) bank.2
            (fun equal => List.noConfusion rfl (heq_of_eq equal))).terminal -
            bank.2.1.word.initial.initial) at following
      unfold OpenTelescope
      rewrite [lastBlock_terminal_cons shared first second rest bank]
      change gaussianSum (bank.1.word.increments ++ increments shared (.cons second rest) bank.2) =
        gaussianSum (bank.1.word.gaps ++ links.1.value ::
          openGaps shared (.cons second rest) bank.2 geometry.remaining roots.remaining links.2) +
          ((lastBlock shared (.cons second rest) bank.2
            (fun equal => List.noConfusion rfl (heq_of_eq equal))).terminal - bank.1.word.initial.initial)
      exact scalar_append bank.1.word.increments (increments shared (.cons second rest) bank.2)
        bank.1.word.gaps (openGaps shared (.cons second rest) bank.2 geometry.remaining roots.remaining links.2)
        bank.1.word.terminal.terminal bank.1.word.initial.initial
        (lastBlock shared (.cons second rest) bank.2
          (fun equal => List.noConfusion rfl (heq_of_eq equal))).terminal
        bank.2.1.word.initial.initial links.1.value bank.1.word.telescope following links.1.value_eq

section Closing

variable {parent : CenteredEdge curve source} {parents : List (CenteredEdge curve source)}
variable {partition : AxisPartition 0 1 (axes.parameters parent)} {splits : PrimitiveSplits axes parents}
variable {head : RegularPrimitiveFragments axes parent partition partition.intervals}
variable {tail : RegularPrimitiveSplits (base := base) axes splits}
variable {request : LocalRequest parent count target} {requests : RequestedParents count target parents}
variable (first : FragmentSheets domains request head) (remaining : SplitSheets domains tail requests)
variable (bank : Blocks shared (.cons first remaining))
variable (last : LastBlock (axes := axes) (count := count) (target := target) shared (parent :: parents))
variable {point : LiftedPoint 2} {root : Named}
variable (geometry : CenteredPathChain (parent :: parents) (start := point) (finish := point))
variable (roots : RootChain (parent :: parents) root root)

/-- One actual literal closing comparison and old-bank gap on the SAME stored final and first occurrences. -/
abbrev ClosingGap :=
  Σ physical : {value : FragmentSheets.Closing last.block.word.last bank.1.word.first
      last.block.word.terminal.finish last.before parents last.parents_eq.symm
      (geometry.castParents last.parents_eq) (castChildren last.parents_eq roots) //
    value = FragmentSheets.close last.block.word.last bank.1.word.first
      last.block.word.terminal.finish last.before parents last.parents_eq.symm
      (geometry.castParents last.parents_eq) (castChildren last.parents_eq roots)},
  {value : FragmentSheets.Joined.NumericalGap last.block.word.terminal bank.1.word.initial physical.val.joined //
    value = FragmentSheets.Joined.readingsGap last.block.word.terminal bank.1.word.initial physical.val.joined}

/-- Compute the closing numerical gap on the GIVEN complete original root-return physical cache. -/
def closeGapFrom
    (physical : {value : FragmentSheets.Closing last.block.word.last bank.1.word.first
      last.block.word.terminal.finish last.before parents last.parents_eq.symm
      (geometry.castParents last.parents_eq) (castChildren last.parents_eq roots) //
    value = FragmentSheets.close last.block.word.last bank.1.word.first
      last.block.word.terminal.finish last.before parents last.parents_eq.symm
      (geometry.castParents last.parents_eq) (castChildren last.parents_eq roots)}) :
    ClosingGap shared first remaining bank last geometry roots :=
  let gap := FragmentSheets.Joined.readingsGap last.block.word.terminal bank.1.word.initial physical.val.joined
  ⟨physical, ⟨gap, rfl⟩⟩

/-- Construct the genuine original root-return join once and cache its actual old-primitive closing gap. -/
def closeGap : ClosingGap shared first remaining bank last geometry roots :=
  let physical : {value : FragmentSheets.Closing last.block.word.last bank.1.word.first
      last.block.word.terminal.finish last.before parents last.parents_eq.symm
      (geometry.castParents last.parents_eq) (castChildren last.parents_eq roots) //
    value = FragmentSheets.close last.block.word.last bank.1.word.first
      last.block.word.terminal.finish last.before parents last.parents_eq.symm
      (geometry.castParents last.parents_eq) (castChildren last.parents_eq roots)} :=
    ⟨FragmentSheets.close last.block.word.last bank.1.word.first
      last.block.word.terminal.finish last.before parents last.parents_eq.symm
      (geometry.castParents last.parents_eq) (castChildren last.parents_eq roots), rfl⟩
  closeGapFrom shared first remaining bank last geometry roots physical

/-- The given original closing cache agrees with the complete original numerical constructor. -/
theorem closeGapFrom_eq
    (physical : {value : FragmentSheets.Closing last.block.word.last bank.1.word.first
      last.block.word.terminal.finish last.before parents last.parents_eq.symm
      (geometry.castParents last.parents_eq) (castChildren last.parents_eq roots) //
    value = FragmentSheets.close last.block.word.last bank.1.word.first
      last.block.word.terminal.finish last.before parents last.parents_eq.symm
      (geometry.castParents last.parents_eq) (castChildren last.parents_eq roots)}) :
    closeGapFrom shared first remaining bank last geometry roots physical =
      closeGap shared first remaining bank last geometry roots := by
  have same : physical = ⟨FragmentSheets.close last.block.word.last bank.1.word.first
      last.block.word.terminal.finish last.before parents last.parents_eq.symm
      (geometry.castParents last.parents_eq) (castChildren last.parents_eq roots), rfl⟩ :=
    Subtype.ext physical.property
  cases same
  unfold closeGap closeGapFrom
  rfl

namespace ClosingGap

variable {shared first remaining bank last geometry roots}
variable (kept : ClosingGap shared first remaining bank last geometry roots)

/-- Read the exact complete original literal closing Point/Entry/root/OwnerJoin cache. -/
@[expose] def physical := kept.1.val

/-- Read the old numerical attempt/reading/preparation cache used at the literal closing slot. -/
@[expose] def numerical := kept.2.val

/-- Read the same actual signed closing scalar. -/
@[expose] def value : Canonical := FragmentSheets.Joined.NumericalGap.value kept.numerical

/-- The complete closing physical cache retains the original constructor on the same source and root chains. -/
theorem physical_eq : kept.physical = FragmentSheets.close last.block.word.last bank.1.word.first
    last.block.word.terminal.finish last.before parents last.parents_eq.symm
    (geometry.castParents last.parents_eq) (castChildren last.parents_eq roots) := kept.1.property

/-- The complete closing numerical cache uses the same original terminal/initial observations and real join. -/
theorem numerical_eq : kept.numerical = FragmentSheets.Joined.readingsGap
    last.block.word.terminal bank.1.word.initial kept.physical.joined := kept.2.property

/-- The literal closing scalar retains the original final and first old readings, never equalizing them. -/
theorem value_eq : kept.value = last.terminal - bank.1.word.initial.initial :=
  FragmentSheets.Joined.NumericalGap.value_eq kept.numerical

section Numerator

variable {newNumerator : CoefficientPolynomial} {newIndex : Nat} {newTolerance : Rational}
variable {newBudgets : FaceMeshBudgets source points newTolerance (numerator := newNumerator) domains}
variable {newNumerics : Face.PrimitiveData.FacePrimitiveBank source newIndex
  (numerator := newNumerator) domains}
variable (newShared : FaceSharedMeshes (numerator := newNumerator) newBudgets newNumerics)

/-- Transport a literal physical closing cache along whole boundary/Finish identities on the same source prefix. -/
private def transportReturn
    {lastParent : CenteredEdge curve source} {before : List (CenteredEdge curve source)}
    {lastPartition : AxisPartition 0 1 (axes.parameters lastParent)}
    {lastFragments : RegularPrimitiveFragments axes lastParent lastPartition lastPartition.intervals}
    {lastRequest : LocalRequest lastParent count target}
    {lastEntries : FragmentSheets domains lastRequest lastFragments}
    {oldEnd newEnd : FragmentSheets.Last lastEntries} {oldFirst newFirst : FragmentSheets.First first}
    {oldFinish : Finish oldEnd.selected.assigned} {newFinish : Finish newEnd.selected.assigned}
    {parentsEq : parent :: parents = before ++ [lastParent]}
    (endEq : oldEnd = newEnd) (firstEq : oldFirst = newFirst) (finishEq : HEq oldFinish newFinish)
    (physical : FragmentSheets.Closing oldEnd oldFirst oldFinish before parents parentsEq.symm
      (geometry.castParents parentsEq) (castChildren parentsEq roots)) :
    FragmentSheets.Closing newEnd newFirst newFinish before parents parentsEq.symm
      (geometry.castParents parentsEq) (castChildren parentsEq roots) := by
  cases endEq
  cases firstEq
  cases finishEq
  exact physical

/-- The exact original root-return producer equation survives transport of its whole cached inputs. -/
private theorem transportReturn_factory
    {lastParent : CenteredEdge curve source} {before : List (CenteredEdge curve source)}
    {lastPartition : AxisPartition 0 1 (axes.parameters lastParent)}
    {lastFragments : RegularPrimitiveFragments axes lastParent lastPartition lastPartition.intervals}
    {lastRequest : LocalRequest lastParent count target}
    {lastEntries : FragmentSheets domains lastRequest lastFragments}
    {oldEnd newEnd : FragmentSheets.Last lastEntries} {oldFirst newFirst : FragmentSheets.First first}
    {oldFinish : Finish oldEnd.selected.assigned} {newFinish : Finish newEnd.selected.assigned}
    {parentsEq : parent :: parents = before ++ [lastParent]}
    (endEq : oldEnd = newEnd) (firstEq : oldFirst = newFirst) (finishEq : HEq oldFinish newFinish)
    (physical : FragmentSheets.Closing oldEnd oldFirst oldFinish before parents parentsEq.symm
      (geometry.castParents parentsEq) (castChildren parentsEq roots))
    (factory : physical = FragmentSheets.close oldEnd oldFirst oldFinish before parents parentsEq.symm
      (geometry.castParents parentsEq) (castChildren parentsEq roots)) :
    transportReturn endEq firstEq finishEq physical =
      FragmentSheets.close newEnd newFirst newFinish before parents parentsEq.symm
        (geometry.castParents parentsEq) (castChildren parentsEq roots) := by
  cases endEq
  cases firstEq
  cases finishEq
  unfold transportReturn
  exact factory

/-- Reuse the complete old return cache after deriving equality of the SAME original final source prefix. -/
private def fromSource
    (newBank : Blocks newShared (.cons first remaining))
    (newLast : LastBlock (axes := axes) (count := count) (target := target) newShared (parent :: parents))
    (sourceEq : LastBlock.sourceShape last = LastBlock.sourceShape newLast) :
    ClosingGap newShared first remaining newBank newLast geometry roots := by
  rcases last with ⟨before, lastParent, lastPartition, lastFragments, lastRequest, lastEntries, parentsEq, oldBlock⟩
  rcases newLast with
    ⟨nextBefore, nextParent, nextPartition, nextFragments, nextRequest, nextEntries, nextParentsEq, newBlock⟩
  change (⟨before, lastParent, lastPartition, lastFragments, lastRequest, lastEntries,
      ⟨(), parentsEq.property⟩⟩ : LastBlock.SourceShape (frames := frames) (domains := domains)
        (axes := axes) (count := count) (target := target)
        (parent :: parents)) =
    ⟨nextBefore, nextParent, nextPartition, nextFragments, nextRequest, nextEntries,
      ⟨(), nextParentsEq.property⟩⟩ at sourceEq
  cases sourceEq
  have endEq : oldBlock.word.last = newBlock.word.last := oldBlock.word.last_eq.trans newBlock.word.last_eq.symm
  have firstEq : bank.1.word.first = newBank.1.word.first :=
    bank.1.word.first_eq.trans newBank.1.word.first_eq.symm
  have finishEq : HEq oldBlock.word.terminal.finish newBlock.word.terminal.finish :=
    (FragmentSheets.Word.terminalFinish_heq (shared := shared) (newShared := newShared) endEq.symm
      newBlock.word.terminal oldBlock.word.terminal).symm
  let physical : {value : FragmentSheets.Closing newBlock.word.last newBank.1.word.first
      newBlock.word.terminal.finish before parents parentsEq.property.symm
      (geometry.castParents parentsEq.property) (castChildren parentsEq.property roots) //
    value = FragmentSheets.close newBlock.word.last newBank.1.word.first
      newBlock.word.terminal.finish before parents parentsEq.property.symm
      (geometry.castParents parentsEq.property) (castChildren parentsEq.property roots)} :=
    ⟨transportReturn (first := first) (geometry := geometry) (roots := roots)
        endEq firstEq finishEq kept.physical,
      transportReturn_factory (first := first) (geometry := geometry) (roots := roots)
        endEq firstEq finishEq kept.physical kept.physical_eq⟩
  exact closeGapFrom newShared first remaining newBank _ geometry roots physical

/-- Reuse the actual original literal closing cache and both old endpoints for one true new-numerator gap.

The required whole last-reader factories are the existing retained inputs
of the actual Closed word. They derive complete source-prefix identity
internally; no desired root return, coordinate identity or primitive bound
is accepted. The actual old physical root-return cache is never rebuilt.
-/
def revalue
    (oldFactory : last = lastBlock shared (.cons first remaining) bank
      (fun equal => List.noConfusion rfl (heq_of_eq equal)))
    (newBank : Blocks newShared (.cons first remaining))
    (newLast : LastBlock (axes := axes) (count := count) (target := target) newShared (parent :: parents))
    (newFactory : newLast = lastBlock newShared (.cons first remaining) newBank
      (fun equal => List.noConfusion rfl (heq_of_eq equal))) :
    ClosingGap newShared first remaining newBank newLast geometry roots :=
  have sourceEq : LastBlock.sourceShape last = LastBlock.sourceShape newLast :=
    (congrArg (fun value : LastBlock (axes := axes) (count := count) (target := target) shared
        (parent :: parents) => LastBlock.sourceShape value) oldFactory).trans
      ((lastBlock_sourceShape_independent (shared := shared) (newShared := newShared)
        (.cons first remaining) bank newBank (fun equal => List.noConfusion rfl (heq_of_eq equal))).trans
        (congrArg (fun value : LastBlock (axes := axes) (count := count) (target := target) newShared
          (parent :: parents) => LastBlock.sourceShape value) newFactory).symm)
  fromSource (kept := kept) (newShared := newShared) newBank newLast sourceEq

end Numerator

end ClosingGap
end Closing

section NonemptyWord

variable {parent : CenteredEdge curve source} {parents : List (CenteredEdge curve source)}
variable {partition : AxisPartition 0 1 (axes.parameters parent)} {splits : PrimitiveSplits axes parents}
variable {head : RegularPrimitiveFragments axes parent partition partition.intervals}
variable {tail : RegularPrimitiveSplits (base := base) axes splits}
variable {request : LocalRequest parent count target} {requests : RequestedParents count target parents}
variable (first : FragmentSheets domains request head) (remaining : SplitSheets domains tail requests)
variable {point : LiftedPoint 2} {root : Named}
variable (geometry : CenteredPathChain (parent :: parents) (start := point) (finish := point))
variable (roots : RootChain (parent :: parents) root root)
variable (included : ∀ value ∈ RegularPrimitiveSplits.SheetEntries.points (.cons first remaining),
  value ∈ points)

namespace NonemptyWord

/-- The same whole original parent bank with its single materialization factory. -/
@[expose] def Bank :=
  {value : Blocks shared (.cons first remaining) //
    value = buildBlocks shared (.cons first remaining) included}

/-- The exact ordered adjacent cache and factory on the same given parent bank. -/
@[expose] def Links (bank : Bank shared first remaining included) :=
  {value : SplitSheets.Links shared (.cons first remaining) bank.val geometry roots //
    value = buildLinks shared (.cons first remaining) bank.val geometry roots}

/-- The structural final-block reader and its factory on that same parent bank. -/
@[expose] def Last (bank : Bank shared first remaining included) :=
  {value : LastBlock (axes := axes) (count := count) (target := target) shared (parent :: parents) //
    value = lastBlock shared (.cons first remaining) bank.val
      (fun equal => List.noConfusion rfl (heq_of_eq equal))}

/-- The literal original closing cache on the already retained final and initial occurrences. -/
@[expose] def Return (bank : Bank shared first remaining included)
    (last : Last shared first remaining included bank) :=
  ClosingGap shared first remaining bank.val last.val geometry roots

end NonemptyWord

/-- The exact nonempty closed-word caches, retaining every complete original materialization factory. -/
abbrev NonemptyWord :=
  Σ bank : NonemptyWord.Bank shared first remaining included,
  Σ _links : NonemptyWord.Links shared first remaining geometry roots included bank,
  Σ last : NonemptyWord.Last shared first remaining included bank,
  NonemptyWord.Return shared first remaining geometry roots included bank last

/-- Package abstract certified caches without reducing any of their materialization factories. -/
private def packNonempty
    (bank : NonemptyWord.Bank shared first remaining included)
    (links : NonemptyWord.Links shared first remaining geometry roots included bank)
    (last : NonemptyWord.Last shared first remaining included bank)
    (closing : NonemptyWord.Return shared first remaining geometry roots included bank last) :
    NonemptyWord shared first remaining geometry roots included :=
  ⟨bank, links, last, closing⟩

/-- Build each actual nonempty word cache once before placing it in the whole closed-word family. -/
def nonemptyWord : NonemptyWord shared first remaining geometry roots included :=
  let bank : NonemptyWord.Bank shared first remaining included :=
    ⟨buildBlocks shared (.cons first remaining) included, rfl⟩
  let links : NonemptyWord.Links shared first remaining geometry roots included bank :=
    ⟨buildLinks shared (.cons first remaining) bank.val geometry roots, rfl⟩
  let last : NonemptyWord.Last shared first remaining included bank :=
    ⟨lastBlock shared (.cons first remaining) bank.val
      (fun equal => List.noConfusion rfl (heq_of_eq equal)), rfl⟩
  let closing : NonemptyWord.Return shared first remaining geometry roots included bank last :=
    closeGap shared first remaining bank.val last.val geometry roots
  packNonempty shared first remaining geometry roots included bank links last closing

end NonemptyWord

variable {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
variable {fragments : RegularPrimitiveSplits (base := base) axes splits}
variable {requests : RequestedParents count target parents}
variable (entries : SplitSheets domains fragments requests) {point : LiftedPoint 2} {root : Named}
variable (geometry : CenteredPathChain parents (start := point) (finish := point))
variable (roots : RootChain parents root root)

/-- All given whole original source, geometric/root and numerical caches, retained without reconstruction. -/
abbrev Originals :=
  {value : Face.PrimitiveData.FacePrimitiveBank source index (numerator := numerator) domains ×
      FaceMeshBudgets source points tolerance (numerator := numerator) domains ×
      FaceSharedMeshes (numerator := numerator) budgets numerics ×
      SplitSheets domains fragments requests ×
      CenteredPathChain parents (start := point) (finish := point) × RootChain parents root root //
    value = (numerics, budgets, shared, entries, geometry, roots)}

/-- The complete actual closed word, retaining its original inputs and every observed physical/numerical cache.

An empty word retains the genuine empty root comparison and no endpoint
Point. A nonempty word keeps one parent product, adjacent bank, actual
final-block read and literal closing cache, each with its whole factory.
-/
@[expose] def Closed : ∀ {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
    {fragments : RegularPrimitiveSplits (base := base) axes splits} {requests : RequestedParents count target parents}
    (entries : SplitSheets domains fragments requests) {point : LiftedPoint 2} {root : Named}
    (_geometry : CenteredPathChain parents (start := point) (finish := point)) (_roots : RootChain parents root root),
    (∀ value ∈ RegularPrimitiveSplits.SheetEntries.points entries, value ∈ points) → Type 3
  | _, _, _, _, .nil, _, root, geometry, roots, _included =>
      Originals (axes := axes) (count := count) (target := target) shared .nil geometry roots ×
        {value : Approximation.Gaussian.Equivalence.NamedEquivalent root root // value = roots.emptyEquivalent} ×
          PUnit.{4}
  | _, _, _, _, .cons first remaining, _, _, geometry, roots, included =>
      Originals (axes := axes) (count := count) (target := target) shared (.cons first remaining) geometry roots ×
        NonemptyWord shared first remaining geometry roots included

/-- Assemble the actual whole closed word, preserving all old banks and one actual cache per original occurrence. -/
def closedWord : ∀ {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
    {fragments : RegularPrimitiveSplits (base := base) axes splits} {requests : RequestedParents count target parents}
    (entries : SplitSheets domains fragments requests) {point : LiftedPoint 2} {root : Named}
    (geometry : CenteredPathChain parents (start := point) (finish := point)) (roots : RootChain parents root root)
    (included : ∀ value ∈ RegularPrimitiveSplits.SheetEntries.points entries, value ∈ points),
    Closed (axes := axes) (count := count) (target := target) shared entries geometry roots included
  | _, _, _, _, .nil, _, _, geometry, roots, _included =>
      ⟨⟨(numerics, budgets, shared, .nil, geometry, roots), rfl⟩, ⟨roots.emptyEquivalent, rfl⟩, PUnit.unit⟩
  | _, _, _, _, .cons first remaining, _, _, geometry, roots, included =>
      let originals : Originals (axes := axes) (count := count) (target := target)
          shared (.cons first remaining) geometry roots :=
        ⟨(numerics, budgets, shared, .cons first remaining, geometry, roots), rfl⟩
      ⟨originals, nonemptyWord shared first remaining geometry roots included⟩

namespace Closed

section GivenNumerics

variable {shared entries geometry roots}

variable {newNumerator : CoefficientPolynomial} {newIndex : Nat} {newTolerance : Rational}
variable {newBudgets : FaceMeshBudgets source points newTolerance (numerator := newNumerator) domains}
variable {newNumerics : Face.PrimitiveData.FacePrimitiveBank source newIndex
  (numerator := newNumerator) domains}
variable (newShared : FaceSharedMeshes (numerator := newNumerator) newBudgets newNumerics)

/-- Reuse the complete original physical closed word and prepare only its true new-numerator numerical realization. -/
private def revalueImpl : ∀ {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
    {fragments : RegularPrimitiveSplits (base := base) axes splits} {requests : RequestedParents count target parents}
    (entries : SplitSheets domains fragments requests) {point : LiftedPoint 2} {root : Named}
    (geometry : CenteredPathChain parents (start := point) (finish := point)) (roots : RootChain parents root root)
    {included : ∀ value ∈ RegularPrimitiveSplits.SheetEntries.points entries, value ∈ points},
    Closed (axes := axes) (count := count) (target := target) shared entries geometry roots included →
      Closed (axes := axes) (count := count) (target := target) newShared entries geometry roots included
  | _, _, _, _, .nil, _, _, geometry, roots, _, kept =>
      ⟨⟨(newNumerics, newBudgets, newShared, .nil, geometry, roots), rfl⟩, kept.2.1, PUnit.unit⟩
  | _, _, _, _, .cons first remaining, _, _, geometry, roots, included, kept =>
      let bank : NonemptyWord.Bank newShared first remaining included :=
        revalueBlocks (shared := shared) (newShared := newShared) (.cons first remaining) kept.2.1.val included
      let links : NonemptyWord.Links newShared first remaining geometry roots included bank :=
        revalueLinks (shared := shared) (newShared := newShared) (.cons first remaining)
          kept.2.1.val bank.val geometry roots kept.2.2.1.val
      let last : NonemptyWord.Last newShared first remaining included bank :=
        ⟨lastBlock newShared (.cons first remaining) bank.val
          (fun equal => List.noConfusion rfl (heq_of_eq equal)), rfl⟩
      let closing : NonemptyWord.Return newShared first remaining geometry roots included bank last :=
        ClosingGap.revalue (kept := kept.2.2.2.2) (newShared := newShared)
          kept.2.2.2.1.property bank.val last.val last.property
      let originals : Originals (axes := axes) (count := count) (target := target)
          newShared (.cons first remaining) geometry roots :=
        ⟨(newNumerics, newBudgets, newShared, .cons first remaining, geometry, roots), rfl⟩
      ⟨originals, packNonempty newShared first remaining geometry roots included bank links last closing⟩

/-- A new numerical realization retains the whole given old cache as data, on the same source/geometric/root indices. -/
abbrev NumeratorWord {included : ∀ value ∈ RegularPrimitiveSplits.SheetEntries.points entries,
    value ∈ points} (kept : Closed shared entries geometry roots included) :=
  {value : Closed shared entries geometry roots included ×
      Closed newShared entries geometry roots included // value.1 = kept}

/-- Prepare the genuine new numerator on every SAME retained physical leaf and join, preserving the old whole input.

A nonempty word reuses its internal, adjacent and literal return caches.
Every outgoing numerical attempt/readGap is new work on the actual new
bank. A wholly empty word retains its real emptyEquivalent and creates no
Point, Finish or numerical closing slot.
-/
def withNumerics {included : ∀ value ∈ RegularPrimitiveSplits.SheetEntries.points entries,
    value ∈ points} (kept : Closed shared entries geometry roots included)
    (newShared : FaceSharedMeshes (numerator := newNumerator) newBudgets newNumerics) : NumeratorWord newShared kept :=
  let actual := revalueImpl (shared := shared) (newShared := newShared) entries geometry roots kept
  ⟨(kept, actual), rfl⟩

end GivenNumerics

/-- Read every original increment in parent/fragment order, keeping both slots even for stationary fragments. -/
@[expose] def increments : ∀ {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
    {fragments : RegularPrimitiveSplits (base := base) axes splits} {requests : RequestedParents count target parents}
    (entries : SplitSheets domains fragments requests) {point : LiftedPoint 2} {root : Named}
    (geometry : CenteredPathChain parents (start := point) (finish := point)) (roots : RootChain parents root root)
    {included : ∀ value ∈ RegularPrimitiveSplits.SheetEntries.points entries, value ∈ points},
    Closed (axes := axes) (count := count) (target := target) shared entries geometry roots included → List Canonical
  | _, _, _, _, .nil, _, _, _geometry, _roots, _, _kept => []
  | _, _, _, _, .cons first remaining, _, _, _geometry, _roots, _, kept =>
      SplitSheets.increments shared (.cons first remaining) kept.2.1.val

/-- Read every actual outgoing gap in literal original order, ending with exactly one genuine closing slot. -/
@[expose] def gaps : ∀ {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
    {fragments : RegularPrimitiveSplits (base := base) axes splits} {requests : RequestedParents count target parents}
    (entries : SplitSheets domains fragments requests) {point : LiftedPoint 2} {root : Named}
    (geometry : CenteredPathChain parents (start := point) (finish := point)) (roots : RootChain parents root root)
    {included : ∀ value ∈ RegularPrimitiveSplits.SheetEntries.points entries, value ∈ points},
    Closed (axes := axes) (count := count) (target := target) shared entries geometry roots included → List Canonical
  | _, _, _, _, .nil, _, _, _geometry, _roots, _, _kept => []
  | _, _, _, _, .cons first remaining, _, _, geometry, roots, _, kept =>
      openGaps shared (.cons first remaining) kept.2.1.val geometry roots kept.2.2.1.val ++
        [ClosingGap.value kept.2.2.2.2]

/-- Read the complete given old geometric, root, source and numerical inputs from either actual branch. -/
@[expose] def originals : ∀ {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
    {fragments : RegularPrimitiveSplits (base := base) axes splits} {requests : RequestedParents count target parents}
    (entries : SplitSheets domains fragments requests) {point : LiftedPoint 2} {root : Named}
    (geometry : CenteredPathChain parents (start := point) (finish := point)) (roots : RootChain parents root root)
    {included : ∀ value ∈ RegularPrimitiveSplits.SheetEntries.points entries, value ∈ points},
    Closed (axes := axes) (count := count) (target := target)

      shared entries geometry roots included → Originals (axes := axes) (count := count) (target := target)
      shared entries geometry roots
  | _, _, _, _, .nil, _, _, _geometry, _roots, _, kept => kept.1
  | _, _, _, _, .cons _first _remaining, _, _, _geometry, _roots, _, kept => kept.1

/-- The complete original inputs remain the same given values on both actual word branches. -/
theorem originals_eq
    {included : ∀ value ∈ RegularPrimitiveSplits.SheetEntries.points entries, value ∈ points}
    (kept : Closed (axes := axes) (count := count) (target := target) shared entries geometry roots included) :
    (originals shared entries geometry roots kept).val = (numerics, budgets, shared, entries, geometry, roots) :=
  (originals shared entries geometry roots kept).property

section Empty

variable {point : LiftedPoint 2} {root : Named}
variable {geometry : CenteredPathChain (curve := curve) (differential := source) []
  (start := point) (finish := point)}
variable {roots : RootChain (curve := curve) (differential := source) [] root root}
variable {included : ∀ value ∈ RegularPrimitiveSplits.SheetEntries.points
  (SplitSheets.nil (domains := domains) (axes := axes) (count := count) (target := target)), value ∈ points}
variable (kept : Closed (axes := axes) (count := count) (target := target)
  shared .nil geometry roots included)

/-- Read the actual operational empty-root comparison, without creating any fragment endpoint or observation. -/
@[expose] def emptyEquivalent : Approximation.Gaussian.Equivalence.NamedEquivalent root root := kept.2.1.val

/-- The empty branch retains the SAME original empty root reader and its whole factory. -/
theorem emptyEquivalent_eq : kept.emptyEquivalent = roots.emptyEquivalent := kept.2.1.property

end Empty

section Nonempty

variable {parent : CenteredEdge curve source} {parents : List (CenteredEdge curve source)}
variable {partition : AxisPartition 0 1 (axes.parameters parent)} {splits : PrimitiveSplits axes parents}
variable {head : RegularPrimitiveFragments axes parent partition partition.intervals}
variable {tail : RegularPrimitiveSplits (base := base) axes splits}
variable {request : LocalRequest parent count target} {requests : RequestedParents count target parents}
variable {first : FragmentSheets domains request head} {remaining : SplitSheets domains tail requests}
variable {point : LiftedPoint 2} {root : Named}
variable {geometry : CenteredPathChain (parent :: parents) (start := point) (finish := point)}
variable {roots : RootChain (parent :: parents) root root}
variable {included : ∀ value ∈ RegularPrimitiveSplits.SheetEntries.points (.cons first remaining),
  value ∈ points}
variable (kept : Closed (axes := axes) (count := count) (target := target)
  shared (.cons first remaining) geometry roots included)

/-- Read the same actual whole parent/occurrence product, with no bank builder replay. -/
@[expose] def bank : Blocks shared (.cons first remaining) := kept.2.1.val

/-- Read the same complete adjacent-parent physical and numerical cache product. -/
@[expose] def links : Links shared (.cons first remaining) kept.bank geometry roots := kept.2.2.1.val

/-- Read the structurally selected original last block and its SAME terminal leaf. -/
@[expose] def last : LastBlock (axes := axes) (count := count) (target := target)
    shared (parent :: parents) := kept.2.2.2.1.val

/-- Read the complete literal closing cache on those same already retained endpoint occurrences. -/
@[expose] def closing : ClosingGap shared first remaining kept.bank kept.last geometry roots := kept.2.2.2.2

/-- The complete parent product is its single original materialization. -/
theorem bank_eq : kept.bank = buildBlocks shared (.cons first remaining) included := kept.2.1.property

/-- The complete adjacent product is its single original constructor on that same stored bank. -/
theorem links_eq : kept.links = buildLinks shared (.cons first remaining) kept.bank geometry roots :=
  kept.2.2.1.property

/-- The final block is the original structural reader on that same stored bank, never a new preparation. -/
theorem last_eq : kept.last = SplitSheets.lastBlock shared (.cons first remaining) kept.bank
    (fun equal => List.noConfusion rfl (heq_of_eq equal)) := kept.2.2.2.1.property

end Nonempty

/-- Appending the actual literal closing scalar adds its same original list sum. -/
private theorem sum_snoc (values : List Canonical) (last : Canonical) :
    gaussianSum values + last = gaussianSum (values ++ [last]) := by
  have singleton : gaussianSum [last] = last := by
    change last + 0 = last
    ring1
  exact (congrArg (fun value : Canonical => gaussianSum values + value) singleton.symm).trans
    (gaussianSum_append values [last]).symm

/-- The complete ordered actual old increment sum equals the complete ordered actual outgoing-gap sum.

This retains nonzero gaps, both old constants and the literal closing
contribution. It assumes no absolute normalization, numerical closeness,
physical integral equality, canonical homology or monodromy action.
-/
theorem telescope : ∀ {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
    {fragments : RegularPrimitiveSplits (base := base) axes splits} {requests : RequestedParents count target parents}
    (entries : SplitSheets domains fragments requests) {point : LiftedPoint 2} {root : Named}
    (geometry : CenteredPathChain parents (start := point) (finish := point)) (roots : RootChain parents root root)
    {included : ∀ value ∈ RegularPrimitiveSplits.SheetEntries.points entries, value ∈ points}
    (kept : Closed (axes := axes) (count := count) (target := target) shared entries geometry roots included),
    gaussianSum (increments shared entries geometry roots kept) = gaussianSum (gaps shared entries geometry roots kept)
  | _, _, _, _, .nil, _, _, _geometry, _roots, _, _kept => rfl
  | _, _, _, _, .cons first remaining, _, _, geometry, roots, _, kept => by
      let bank := kept.2.1.val
      let links := kept.2.2.1.val
      let last := kept.2.2.2.1.val
      let closing := kept.2.2.2.2
      have opening := open_telescope shared (.cons first remaining) bank geometry roots links
        (fun equal => List.noConfusion rfl (heq_of_eq equal))
      have lastEq : (lastBlock shared (.cons first remaining) bank
          (fun equal => List.noConfusion rfl (heq_of_eq equal))).terminal = last.terminal :=
        (congrArg (fun value => LastBlock.terminal value) kept.2.2.2.1.property).symm
      have boundary : (lastBlock shared (.cons first remaining) bank
          (fun equal => List.noConfusion rfl (heq_of_eq equal))).terminal -
            bank.1.word.initial.initial = closing.value :=
        (congrArg (fun value : Canonical => value - bank.1.word.initial.initial) lastEq).trans closing.value_eq.symm
      exact opening.trans ((congrArg (fun value : Canonical =>
        gaussianSum (openGaps shared (.cons first remaining) bank geometry roots links) + value) boundary).trans
          (sum_snoc _ closing.value))

/-- Every original fragment contributes exactly one ordered outgoing scalar, including the literal closing slot. -/
theorem gaps_length : ∀ {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
    {fragments : RegularPrimitiveSplits (base := base) axes splits} {requests : RequestedParents count target parents}
    (entries : SplitSheets domains fragments requests) {point : LiftedPoint 2} {root : Named}
    (geometry : CenteredPathChain parents (start := point) (finish := point)) (roots : RootChain parents root root)
    {included : ∀ value ∈ RegularPrimitiveSplits.SheetEntries.points entries, value ∈ points}
    (kept : Closed (axes := axes) (count := count) (target := target) shared entries geometry roots included),
    (gaps shared entries geometry roots kept).length = fragmentCount entries
  | _, _, _, _, .nil, _, _, _geometry, _roots, _, _kept => rfl
  | _, _, _, _, .cons first remaining, _, _, geometry, roots, _, kept =>
      (Data.List.Append.length_append _ _).trans
        (openGaps_length shared (.cons first remaining) kept.2.1.val geometry roots kept.2.2.1.val
          (fun equal => List.noConfusion rfl (heq_of_eq equal)))

/-- The exact same number of old increments is retained as actual outgoing gaps. -/
theorem increments_length : ∀ {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
    {fragments : RegularPrimitiveSplits (base := base) axes splits} {requests : RequestedParents count target parents}
    (entries : SplitSheets domains fragments requests) {point : LiftedPoint 2} {root : Named}
    (geometry : CenteredPathChain parents (start := point) (finish := point)) (roots : RootChain parents root root)
    {included : ∀ value ∈ RegularPrimitiveSplits.SheetEntries.points entries, value ∈ points}
    (kept : Closed (axes := axes) (count := count) (target := target) shared entries geometry roots included),
    (increments shared entries geometry roots kept).length = fragmentCount entries
  | _, _, _, _, .nil, _, _, _geometry, _roots, _, _kept => rfl
  | _, _, _, _, .cons first remaining, _, _, _geometry, _roots, _, kept =>
      SplitSheets.increments_length shared (.cons first remaining) kept.2.1.val

end Closed

namespace Closed

/-- Read the same whole given block bank; an empty word has only its actual empty product. -/
@[expose] def blocks : ∀ {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
    {fragments : RegularPrimitiveSplits (base := base) axes splits} {requests : RequestedParents count target parents}
    (entries : SplitSheets domains fragments requests) {point : LiftedPoint 2} {root : Named}
    (geometry : CenteredPathChain parents (start := point) (finish := point)) (roots : RootChain parents root root)
    {included : ∀ value ∈ RegularPrimitiveSplits.SheetEntries.points entries, value ∈ points},
    Closed shared entries geometry roots included → Blocks shared entries
  | _, _, _, _, .nil, _, _, _geometry, _roots, _, _kept => PUnit.unit
  | _, _, _, _, .cons _first _remaining, _, _, _geometry, _roots, _, kept => kept.bank

/-- Reading the unified actual block product preserves the original whole closed-word increment list. -/
theorem increments_blocks : ∀ {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
    {fragments : RegularPrimitiveSplits (base := base) axes splits} {requests : RequestedParents count target parents}
    (entries : SplitSheets domains fragments requests) {point : LiftedPoint 2} {root : Named}
    (geometry : CenteredPathChain parents (start := point) (finish := point)) (roots : RootChain parents root root)
    {included : ∀ value ∈ RegularPrimitiveSplits.SheetEntries.points entries, value ∈ points}
    (kept : Closed shared entries geometry roots included),
    SplitSheets.increments shared entries (blocks shared entries geometry roots kept) =
      Closed.increments shared entries geometry roots kept
  | _, _, _, _, .nil, _, _, _geometry, _roots, _, _kept => rfl
  | _, _, _, _, .cons _first _remaining, _, _, _geometry, _roots, _, _kept => rfl

end Closed

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SplitSheets
