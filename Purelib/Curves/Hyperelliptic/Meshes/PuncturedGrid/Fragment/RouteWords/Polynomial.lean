module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteContacts.Polynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.Word.Readings
import Purelib.Data.List.DependentProduct
import Purelib.Data.List.Map
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Approximation.Gaussian.Budget.Aggregate
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Tactic.Ring

/-! # Actual polynomial route comparisons on a given closed fragment word

The supplied physical word provides every original left endpoint cache.
A finite product retains one genuinely new right view and one original
common polynomial comparison per route request. The original signed
closing-gap telescope remains separate from individual primitive jumps.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic.OddPowerDifferential (Ordinary)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes (FaceMeshBudgets FaceSharedMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.BankReadings
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
  (RegularPrimitiveFragment RegularPrimitiveFragments RegularPrimitiveSplits)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment (SheetEntry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords (LiftedFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes PrimitiveSplits)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteContacts.RouteContact
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.List (DependentProduct)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Geometry.Rectangle (AxisPartition)
open Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions (Interval)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest RequestedParents)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames RootEdgeBank)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
    {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
    {frames : RootFrames base.bank.grid} {vertices : VertexBank base.bank.grid} {edges : RootEdgeBank frames}
    {source : Differential genus} {axes : PrimitiveAxes base.bank.grid}
    {domains : FaceDomainBank frames base.faces.regulars} {mesh : LiftedMesh vertices edges base.faces}
    {target tolerance : Rational} {points : List Canonical} {index : Nat}
    {ordinary : Ordinary curve.polynomial}
    {budgets : FaceMeshBudgets source points tolerance (numerator := ordinary.numerator) domains}
    {numerics : FacePrimitiveBank source index (numerator := ordinary.numerator) domains}
    (shared : FaceSharedMeshes budgets numerics)

namespace RouteRequests

/-- A supplied current-numerator endpoint view and its same original split-point membership. -/
abbrev PointInput (piece : LiftedFragment axes domains mesh source count target) :=
  (included : {_value : Unit // ∀ value ∈ piece.assigned.split.points, value ∈ points}) ×
    EndpointReadings.Cache piece.assigned shared included.property

/-- The exact existing finite product of supplied endpoint views at every literal original piece. -/
abbrev PointInputs (pieces : List (LiftedFragment axes domains mesh source count target)) :=
  DependentProduct pieces fun position => PointInput (ordinary := ordinary) shared (pieces[position.val]'position.isLt)

section ParentInputs

open LiftedReadings.ClearGrid.RegularPrimitiveFragments.SheetEntries
  renaming LiftedSources -> ParentSources
open RootedWords.RegularPrimitiveFragments.SheetEntries

variable {parent : CenteredEdge curve source} {partition : AxisPartition 0 1 (axes.parameters parent)}
    {request : LocalRequest parent count target}

/-- Forward a whole supplied occurrence's membership and SAME cached numerical view to its actual lifted piece. -/
private def fromOccurrence {interval : Interval}
    {fragment : RegularPrimitiveFragment axes parent partition interval}
    {assigned : SheetEntry fragment domains request}
    (_located : LiftedEdges.SheetEntry.LiftedSource assigned mesh)
    (kept : FragmentSheets.Occurrence shared assigned) :
    PointInput (ordinary := ordinary) shared (⟨parent, axes.parameters parent, partition, interval, fragment,
        request, assigned, _located⟩ :
      LiftedFragment axes domains mesh source count target) :=
  ⟨⟨(), kept.included⟩, kept.view⟩

/-- Consume the original lifted-source spine and inherited whole occurrence reads in the same order.

Each original finite index is read once. Only original whole-pair equality
transports are applied; no Finish, endpoint view, query, contact or geometry
is acquired to recover a numerical input.
-/
private def parentInputs {followingPieces : List (LiftedFragment axes domains mesh source count target)}
    (following : PointInputs (ordinary := ordinary) shared followingPieces) :
    ∀ {intervals : List Interval} {fragments : RegularPrimitiveFragments axes parent partition intervals}
      {entries : FragmentSheets domains request fragments} (sources : ParentSources mesh entries),
      ((position : Fin intervals.length) → FragmentSheets.Occurrence shared (entries.at position).2) →
        PointInputs (ordinary := ordinary) shared (LiftedSources.pieces sources ++ followingPieces)
  | _, _, _, .nil, _read => following
  | _, _, _, .cons (entry := assigned) (entries := entries) first remaining, read =>
      let original := FragmentSheets.Occurrence.castPair (FragmentSheets.at_zero assigned entries) (read 0)
      let head := fromOccurrence (ordinary := ordinary) shared first original
      let tail := parentInputs following remaining (fun position =>
        FragmentSheets.Occurrence.castPair (FragmentSheets.at_succ assigned entries position) (read position.succ))
      Eq.mpr (congrArg (fun pieces => PointInputs (ordinary := ordinary) shared (pieces ++ followingPieces))
        (LiftedSources.pieces_cons first remaining)) (head, tail)

/-- Read every original parent leaf through its actual pair identity and forward its retained numerical view. -/
private def fromParent {followingPieces : List (LiftedFragment axes domains mesh source count target)}
    {fragments : RegularPrimitiveFragments axes parent partition partition.intervals}
    {entries : FragmentSheets domains request fragments} (sources : ParentSources mesh entries)
    {included : ∀ value ∈ PointBanks.RegularPrimitiveFragments.SheetEntries.points entries, value ∈ points}
    (bank : FragmentSheets.Word shared entries included)
    (following : PointInputs (ordinary := ordinary) shared followingPieces) :
    PointInputs (ordinary := ordinary) shared (LiftedSources.pieces sources ++ followingPieces) :=
  parentInputs (ordinary := ordinary) shared following sources (fun position =>
    let leaf := FragmentSheets.leafAt shared entries bank.leaves position
    FragmentSheets.Occurrence.castPair leaf.pair_eq leaf.occurrence)

end ParentInputs

section WholeInputs

open LiftedReadings.ClearGrid.RegularPrimitiveSplits.SheetEntries renaming LiftedSources -> WholeSources
open RootedWords.RegularPrimitiveSplits.SheetEntries

/-- Flatten only the supplied numerical views from the SAME retained parent products and lifted source spine. -/
private def fromBlocks :
    ∀ {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
      {fragments : RegularPrimitiveSplits (base := base) axes splits}
      {requests : RequestedParents count target parents} {entries : SplitSheets domains fragments requests}
      (sources : WholeSources mesh entries), SplitSheets.Blocks shared entries →
        PointInputs (ordinary := ordinary) shared (LiftedSources.pieces sources)
  | _, _, _, _, _, .nil, _bank => PUnit.unit
  | _, _, _, _, _, .cons first remaining, bank =>
      let following := fromBlocks remaining bank.2
      fromParent (ordinary := ordinary) shared first bank.1.word following

/-- Forward the actual closed word's supplied left endpoint views to its exact cached rooted fragment list.

The actual source spine and Blocks are consumed once. Whole leaf-pair
transports preserve the original view values; the final complete list
identity transports the product to the SAME retained rooted word. No
root, Finish, geometry, query, view or numerical bank is reconstructed.
-/
def pointInputs {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
    {fragments : RegularPrimitiveSplits (base := base) axes splits}
    {requests : RequestedParents count target parents} {entries : SplitSheets domains fragments requests}
    {point : LiftedPoint 2} {root : Named}
    {geometry : CenteredPathChain parents (start := point) (finish := point)} {roots : RootChain parents root root}
    {included : ∀ value ∈ PointBanks.RegularPrimitiveSplits.SheetEntries.points entries, value ∈ points}
    (kept : SplitSheets.Closed shared entries geometry roots included)
    {first last : Canonical} {firstName lastName : Named}
    (word : LiftedSources.Rooted entries mesh first firstName last lastName) : PointInputs (ordinary := ordinary)
        shared word.pieces :=
  let inputs := fromBlocks (ordinary := ordinary) shared word.sources (SplitSheets.Closed.blocks shared entries
      geometry roots kept)
  Eq.mpr (congrArg (PointInputs (ordinary := ordinary) shared) word.pieces_eq) inputs

end WholeInputs

variable {allowance : Rational}

/-- One certified actual comparison on a supplied input view and the original bounded route/contact/request entry. -/
@[expose] def PointHead {piece : LiftedFragment axes domains mesh source count target}
    (entry : Entry (allowance := allowance) piece (some ordinary)) (input : PointInput (ordinary := ordinary)
        shared piece)
    (later : Budget.index entry.2.2 ≤ index) : Type _ :=
  {value : PointComparison entry.2.1 entry.2.2 input.2 //
    value = entry.2.1.comparePoints entry.2.2 input.2 later}

/-- Build precisely one original comparison and its actual new right numerical view on the given input caches. -/
private def compareHead {piece : LiftedFragment axes domains mesh source count target}
    (entry : Entry (allowance := allowance) piece (some ordinary)) (input : PointInput (ordinary := ordinary)
        shared piece)
    (later : Budget.index entry.2.2 ≤ index) : PointHead (ordinary := ordinary) shared entry input later :=
  ⟨entry.2.1.comparePoints entry.2.2 input.2 later, rfl⟩

/-- The existing finite product retains one actual full-P comparison per literal bounded request occurrence. -/
@[expose] def PointComparisons {pieces : List (LiftedFragment axes domains mesh source count target)}
    (requests : RouteRequests allowance pieces (some ordinary)) (inputs : PointInputs (ordinary := ordinary) shared
        pieces)
    (later : requests.index ≤ index) :=
  DependentProduct pieces fun position => PointHead (ordinary := ordinary) shared (requests.at position)
    (DependentProduct.get pieces inputs position) ((requests.at_index_le position).trans later)

/-- Read the actual original bounded request and supplied endpoint input once, then store their one comparison.

The finite product uses the original list occurrences. Its producer does
not rebuild contacts, source fragments, physical roots or left numerical
views. Each right view and common comparison is new retained work.
-/
def compareInputs {pieces : List (LiftedFragment axes domains mesh source count target)}
    (requests : RouteRequests allowance pieces (some ordinary)) (inputs : PointInputs (ordinary := ordinary) shared
        pieces)
    (later : requests.index ≤ index) : PointComparisons (ordinary := ordinary) shared requests inputs later :=
  DependentProduct.ofFn pieces fun position =>
    let entry := requests.at position
    let input := DependentProduct.get pieces inputs position
    compareHead (ordinary := ordinary) shared entry input ((requests.at_index_le position).trans later)

namespace PointComparisons

variable {shared} {pieces : List (LiftedFragment axes domains mesh source count target)}
    {requests : RouteRequests allowance pieces (some ordinary)} {inputs : PointInputs (ordinary := ordinary) shared
        pieces}
    {later : requests.index ≤ index} (kept : PointComparisons (ordinary := ordinary) shared requests inputs later)

/-- Read the same certified actual comparison at its original bounded word occurrence. -/
@[expose] def entry (position : Fin pieces.length) : PointHead (ordinary := ordinary) shared (requests.at position)
    (DependentProduct.get pieces inputs position) ((requests.at_index_le position).trans later) :=
  DependentProduct.get pieces kept position

/-- Read every actual cached contact residual in its original order. -/
def errors : List Canonical := List.ofFn fun position => (kept.entry position).val.value

/-- Read the actual retained right endpoint increments without evaluating route atPoint or a comparison again. -/
def values : List Canonical := List.ofFn fun position =>
  let endpoints := (kept.entry position).val.endpoints
  endpoints.reading.values 1 - endpoints.reading.values 0

/-- The cached actual residuals are precisely the original request's complete ordered discrepancy list. -/
theorem errors_eq : kept.errors = requests.errors shared :=
  (Data.List.OfFn.Basic.ofFn_congr fun position => (kept.entry position).val.value_eq).trans
    (requests.errors_eq_ofFn shared).symm

/-- The cached actual right endpoint increments are precisely the original selected-route value list. -/
theorem values_eq : kept.values = requests.values shared :=
  (Data.List.OfFn.Basic.ofFn_congr fun position => (kept.entry position).val.endpoints.increment_eq).trans
    (requests.values_eq_ofFn shared).symm

/-- The cached residual count includes every repeated and stationary original occurrence. -/
theorem errors_length : kept.errors.length = pieces.length :=
  (congrArg List.length kept.errors_eq).trans (requests.errors_length shared)

/-- Each actual cached residual meets its original independently allocated request. -/
theorem errors_bounded : ∀ value ∈ kept.errors, normSq value ≤ allowance := by
  intro value member
  unfold errors at member
  rcases Data.List.OfFn.Basic.mem_ofFn.mp member with ⟨position, same⟩
  exact Eq.mp (congrArg (fun actual : Canonical => normSq actual ≤ allowance) same)
    (kept.entry position).val.accurate.le

/-- The same actual cached residual sum is the source-piece sum minus the actual cached route-increment sum. -/
theorem errors_sum : gaussianSum kept.errors = gaussianSum (pieces.map (fun piece => piece.value shared)) -
    gaussianSum kept.values :=
  (congrArg gaussianSum kept.errors_eq).trans
    ((requests.errors_sum shared).trans (congrArg
      (fun routed : List Canonical => gaussianSum (pieces.map (fun piece => piece.value shared)) - gaussianSum routed)
      kept.values_eq.symm))

end PointComparisons

/-- The actual cached per-occurrence comparisons pay the positive whole route request using one global Cauchy bound.

The count and residuals come from the SAME given finite product. No new
comparison or source reading is executed to prove the aggregate bound.
-/
theorem pointComparisons_accurate {pieces : List (LiftedFragment axes domains mesh source count target)}
    {requested : Rational} (positive : 0 < requested)
    {requests : RouteRequests (Approximation.Rational.Budget.Aggregate.perTerm requested pieces.length)
      pieces (some ordinary)} {inputs : PointInputs (ordinary := ordinary) shared pieces} {later : requests.index ≤
          index}
    (kept : PointComparisons (ordinary := ordinary) shared requests inputs later) :
    normSq (gaussianSum (pieces.map (fun piece => piece.value shared)) - gaussianSum kept.values) < requested := by
  have paid : normSq (gaussianSum kept.errors) < requested := by
    apply Approximation.Gaussian.Budget.Aggregate.normSq_sum_lt _ positive
    rewrite [kept.errors_length]
    exact kept.errors_bounded
  exact Eq.mp (congrArg (fun value : Canonical => normSq value < requested) kept.errors_sum) paid

end RouteRequests

namespace RouteRequest

open RootedWords.RegularPrimitiveSplits.SheetEntries.LiftedSources (Rooted)

variable {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
    {fragments : RegularPrimitiveSplits (base := base) axes splits}
    {requests : RequestedParents count target parents} {entries : SplitSheets domains fragments requests}
    {point : LiftedPoint 2} {root : Named}
    {geometry : CenteredPathChain parents (start := point) (finish := point)} {roots : RootChain parents root root}
    {included : ∀ value ∈ PointBanks.RegularPrimitiveSplits.SheetEntries.points entries, value ∈ points}
    (closed : SplitSheets.Closed shared entries geometry roots included)
    {first last : Canonical} {firstName lastName : Named}
    (word : Rooted entries mesh first firstName last lastName) {allowance : Rational}
    (original : RouteRequest word.pieces allowance)
    (request : {value : RouteRequest word.pieces allowance (some ordinary) //
      value = original.onNumerator ordinary})

namespace PolynomialReadings

/-- The whole original closed/source/request objects and SAME numerical bank, with actual selected-stage coverage. -/
abbrev Inputs :=
  {value : SplitSheets.Closed shared entries geometry roots included ×
      Rooted entries mesh first firstName last lastName × RouteRequest word.pieces allowance ×
      {value : RouteRequest word.pieces allowance (some ordinary) // value = original.onNumerator ordinary} ×
      FaceMeshBudgets source points tolerance (numerator := ordinary.numerator) domains ×
      FacePrimitiveBank source index (numerator := ordinary.numerator) domains ×
      FaceSharedMeshes budgets numerics × Ordinary curve.polynomial //
    value = (closed, word, original, request, budgets, numerics, shared, ordinary) ∧ request.val.index ≤ index}

end PolynomialReadings

/-- Actual paid polynomial route readings on the SAME whole closed fragment word.

The complete old and genuine-P requests, source word, closed physical
caches and numerical bank remain data. Each output reading and residual
comes from its one retained comparison. The strict bound uses the actual
ordered closing-gap sum and preserves every independent primitive jump.
-/
@[expose] def PolynomialReadings (later : request.val.index ≤ index) : Type _ :=
  PolynomialReadings.Inputs shared closed word original request ×
  (inputs : {value : RouteRequests.PointInputs (ordinary := ordinary) shared word.pieces //
    value = RouteRequests.pointInputs (ordinary := ordinary) shared closed word}) ×
  (compared : {value : RouteRequests.PointComparisons (ordinary := ordinary) shared request.val.requests inputs.val
      (Eq.mp (congrArg (fun stage : Nat => stage ≤ index) request.val.index_eq) later) //
    value = RouteRequests.compareInputs (ordinary := ordinary) shared request.val.requests inputs.val
      (Eq.mp (congrArg (fun stage : Nat => stage ≤ index) request.val.index_eq) later)}) ×
  (values : {value : List Canonical // value = compared.val.values}) ×
  (_errors : {value : List Canonical // value = compared.val.errors}) ×
  {value : Canonical // value = gaussianSum values.val ∧
    normSq (gaussianSum (SplitSheets.Closed.gaps shared entries geometry roots closed) - value) < allowance}

/-- Consume the given closed/source word and true-P request once, retaining every actual numerical comparison.

All contact floors precede this operation in the supplied rebudgeted
request. The given bank genuinely meets their maximum. No bank, root,
Finish, source word, query, contact geometry or left endpoint view is
rebuilt to produce the complete paid routing comparison.
-/
def compareClosed (later : request.val.index ≤ index) : PolynomialReadings shared closed word original request later :=
  let originals : PolynomialReadings.Inputs shared closed word original request :=
    ⟨(closed, word, original, request, budgets, numerics, shared, ordinary), rfl, later⟩
  let inputs : {value : RouteRequests.PointInputs (ordinary := ordinary) shared word.pieces //
      value = RouteRequests.pointInputs (ordinary := ordinary) shared closed word} :=
    ⟨RouteRequests.pointInputs (ordinary := ordinary) shared closed word, rfl⟩
  let paid : request.val.requests.index ≤ index :=
    Eq.mp (congrArg (fun stage : Nat => stage ≤ index) request.val.index_eq) later
  let compared : {value : RouteRequests.PointComparisons (ordinary := ordinary) shared request.val.requests
      inputs.val paid //
      value = RouteRequests.compareInputs (ordinary := ordinary) shared request.val.requests inputs.val paid} :=
    ⟨RouteRequests.compareInputs (ordinary := ordinary) shared request.val.requests inputs.val paid, rfl⟩
  let values : {value : List Canonical // value = compared.val.values} := ⟨compared.val.values, rfl⟩
  let errors : {value : List Canonical // value = compared.val.errors} := ⟨compared.val.errors, rfl⟩
  let value := gaussianSum values.val
  have actual := RouteRequests.pointComparisons_accurate (ordinary := ordinary) shared request.val.positive compared.val
  have stored : normSq (gaussianSum (word.pieces.map (fun piece => piece.value shared)) - value) < allowance :=
    Eq.mpr (congrArg (fun table : List Canonical =>
      normSq (gaussianSum (word.pieces.map (fun piece => piece.value shared)) - gaussianSum table) < allowance)
      values.property) actual
  have same : gaussianSum (word.pieces.map (fun piece => piece.value shared)) =
      gaussianSum (SplitSheets.Closed.gaps shared entries geometry roots closed) :=
    (congrArg gaussianSum (word.values_eq shared)).trans
      (SplitSheets.Closed.lifted_sum_eq_gaps shared closed word.sources)
  have bounded : normSq (gaussianSum (SplitSheets.Closed.gaps shared entries geometry roots closed) - value) <
      allowance := Eq.mp (congrArg (fun total : Canonical => normSq (total - value) < allowance) same) stored
  ⟨originals, inputs, compared, values, errors, ⟨value, rfl, bounded⟩⟩

namespace PolynomialReadings

variable {shared closed word original request} {stagePaid : request.val.index ≤ index}
    (kept : PolynomialReadings shared closed word original request stagePaid)

/-- Read the complete retained original inputs and actual independent floor certificate. -/
@[expose] def inputs : Inputs shared closed word original request := kept.1

/-- Read the SAME supplied left endpoint-view product, derived through whole original source identities. -/
@[expose] def pointInputs : RouteRequests.PointInputs (ordinary := ordinary) shared word.pieces := kept.2.1.val

/-- Read every actual new right view and original common comparison, preserving their complete factories. -/
@[expose] def comparisons : RouteRequests.PointComparisons (ordinary := ordinary) shared request.val.requests
    kept.pointInputs
    (Eq.mp (congrArg (fun stage : Nat => stage ≤ index) request.val.index_eq) stagePaid) := kept.2.2.1.val

/-- Read the actual cached right endpoint-increment list. -/
@[expose] def values : List Canonical := kept.2.2.2.1.val

/-- Read the complete actual cached per-occurrence residual list. -/
@[expose] def errors : List Canonical := kept.2.2.2.2.1.val

/-- Read the one cached routed scalar sum. -/
@[expose] def value : Canonical := kept.2.2.2.2.2.val

/-- The whole old/new requests, closed/source inputs and numerical bank remain the actual supplied data. -/
theorem inputs_eq : kept.inputs.val =
    (closed, word, original, request, budgets, numerics, shared, ordinary) := kept.1.property.1

include kept in
/-- The genuine P request's actual selected index is paid by the retained numerical stage. -/
theorem later : request.val.index ≤ index := kept.1.property.2

/-- The whole endpoint-view product comes from those actual supplied closed/source caches. -/
theorem pointInputs_eq : kept.pointInputs = RouteRequests.pointInputs (ordinary := ordinary) shared closed word :=
    kept.2.1.property

/-- The original comparisons were each built once on the SAME whole supplied left-view product. -/
theorem comparisons_eq : kept.comparisons = RouteRequests.compareInputs (ordinary := ordinary) shared
    request.val.requests kept.pointInputs
    (Eq.mp (congrArg (fun stage : Nat => stage ≤ index) request.val.index_eq) stagePaid) := kept.2.2.1.property

/-- The retained right increment list reads only the actual comparison endpoint caches. -/
theorem values_eq : kept.values = kept.comparisons.values := kept.2.2.2.1.property

/-- The retained residual list reads only the actual comparison scalar caches. -/
theorem errors_eq : kept.errors = kept.comparisons.errors := kept.2.2.2.2.1.property

/-- The cached routed scalar is the actual finite sum of the SAME retained right endpoint increments. -/
theorem value_eq : kept.value = gaussianSum kept.values := kept.2.2.2.2.2.property.1

/-- All repeated, stationary and closing occurrences contribute through their actual paid ordered routing bound. -/
theorem accurate :
    normSq (gaussianSum (SplitSheets.Closed.gaps shared entries geometry roots closed) - kept.value) < allowance :=
  kept.2.2.2.2.2.property.2

/-- The actual cached routing residuals have exactly the original flattened source occurrence count. -/
theorem errors_length : kept.errors.length = word.pieces.length :=
  (congrArg List.length kept.errors_eq).trans kept.comparisons.errors_length

/-- Every actual residual corresponds to one literal outgoing gap, including the actual closing occurrence. -/
theorem errors_length_eq_gaps : kept.errors.length =
    (SplitSheets.Closed.gaps shared entries geometry roots closed).length := by
  have lists : SplitSheets.Closed.increments shared entries geometry roots closed =
      word.pieces.map (fun piece => piece.value shared) :=
    (SplitSheets.Closed.increments_eq_lifted shared closed word.sources).trans (word.values_eq shared).symm
  have countEq : (SplitSheets.Closed.increments shared entries geometry roots closed).length =
      word.pieces.length :=
    (congrArg List.length lists).trans (Data.List.Map.length_map (fun piece => piece.value shared) word.pieces)
  exact kept.errors_length.trans (countEq.symm.trans
    ((SplitSheets.Closed.increments_length shared entries geometry roots closed).trans
      (SplitSheets.Closed.gaps_length shared entries geometry roots closed).symm))

/-- The same actual supplied source-spine readings satisfy the derived routing allowance. -/
theorem source_accurate : normSq (gaussianSum (word.sources.values shared) - kept.value) < allowance :=
  Eq.mpr (congrArg (fun total : Canonical => normSq (total - kept.value) < allowance)
    (SplitSheets.Closed.lifted_sum_eq_gaps shared closed word.sources)) kept.accurate

/-- The actual retained right endpoint increments read the original selected route word, with no second evaluation. -/
theorem routed_values_eq : kept.values = request.val.requests.values shared :=
  kept.values_eq.trans kept.comparisons.values_eq

end PolynomialReadings

end RouteRequest

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords
