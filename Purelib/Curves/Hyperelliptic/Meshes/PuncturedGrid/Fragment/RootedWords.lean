module
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Data.List.Map
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedEdges
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Polynomial.Geometry.Grid.AxisWalks
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedReadings
import Purelib.Riemann.Topology.PreparedRecastRootChains
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces

open Purelib.Geometry.Rectangle.Partition

/-!
# Rooted words of the actual original period fragments

Flatten the retained fragment spine without preparing any new owners.
The original parent root chain and cached interval walks certify every
junction, including those between parents. Displayed sheet switches remain
in the original coordinate proof and are never used as root equivalences.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords

public section

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Polynomial

open Purelib.Riemann

open Purelib.RootIsolation

open Purelib.Data.List

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open
  LiftedReadings.ClearGrid.RegularPrimitiveFragments.SheetEntries
  (LiftedSources)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment renaming FragmentSheets -> SheetEntries
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment renaming SplitSheets -> SheetEntries
open
  LiftedReadings.ClearGrid.RegularPrimitiveSplits.SheetEntries
  (LiftedSources)

open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

variable {numerator : CoefficientPolynomial}

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {frames : SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
      SquareRoot.Grid.LiftedVertices.VertexBank
    base.bank.grid} {edges : SquareRoot.Grid.RootEdgeBank frames}
  {source : Differentials.Basic.Differential genus} {axes :
    PreparedPrimitiveSplits.PrimitiveAxes base.bank.grid}
  {domains : Face.DomainBanks.FaceDomainBank frames base.faces.regulars} {mesh :
    Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces}
  {count : Nat} {target : Fraction.Rational}

set_option genInjectivity false in
/-- A retained occurrence of an original fragment with its parent and lifted edge.

Its request, interval and cached face assignment refer to that same original parent and mesh. The retained
containing-edge occurrence preserves the fragment's actual location and sheet ownership. -/
structure LiftedFragment (axes : PreparedPrimitiveSplits.PrimitiveAxes
  base.bank.grid)
    (domains : Face.DomainBanks.FaceDomainBank frames base.faces.regulars) (mesh :
      Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces)
    (source : Differentials.Basic.Differential genus) (count : Nat) (target : Fraction.Rational) : Type 2
      where
  /-- The original centered parent edge. -/ parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve source
  /-- The retained actual cut list for this parent occurrence. -/ cuts : List Fraction.Rational
  /-- The actual axis partition of this same parent occurrence. -/ partition : Rectangle.AxisPartition 0 1 cuts
  /-- The actual retained parameter interval. -/ interval : PreparedAxisPartitions.Interval
  /-- The original located fragment on that interval. -/ fragment :
    RegularFaces.RegularPrimitiveFragment axes parent partition interval
  /-- The original parent's local accuracy request. -/ request : Readings.UniformPreparedRequests.LocalRequest parent
    count target
  /-- The retained sheet-aware face assignment. -/ assigned :
    SheetEntries.RegularPrimitiveFragment.SheetEntry fragment domains
    request
  /-- The actual lifted containing-edge occurrence. -/ occurrence :
    LiftedEdges.SheetEntry.LiftedSource assigned mesh

constructive_injectivity LiftedFragment

namespace LiftedFragment

/-- Read the original fragment's initial coordinate. -/
@[expose] def first (piece : LiftedFragment axes domains mesh
  source count target) : Gaussian := piece.fragment.located.first

/-- Read the original fragment's terminal coordinate. -/
@[expose] def last (piece : LiftedFragment axes domains mesh
  source count target) : Gaussian := piece.fragment.located.last

/-- These query names occur only in proof contracts; flattening a word does
not run either endpoint query. -/
@[expose] def firstName (piece : LiftedFragment axes domains
  mesh source count target) : Gaussian.Name.Basic.Named :=
  piece.parent.edge.rootName piece.interval.lower piece.assigned.fractionInside

/-- The original parent's root query name at the retained fragment's terminal parameter. -/
@[expose] def lastName (piece : LiftedFragment axes domains mesh
  source count target) : Gaussian.Name.Basic.Named :=
  piece.parent.edge.rootName piece.interval.upper piece.occurrence.finishInside

/-- Read the retained lifted source on the supplied shared face meshes. -/
@[expose] def value (piece : LiftedFragment axes domains mesh
  source count target)
    {points : List Gaussian.Basic.Canonical} {tolerance : Fraction.Rational} {index : Nat}
    {budgets : Face.CommonMeshes.FaceMeshBudgets source points tolerance (numerator := numerator) domains}
      {numerics : Face.PrimitiveData.FacePrimitiveBank source index (numerator := numerator) domains}
    (shared : Face.CommonMeshes.FaceSharedMeshes budgets numerics) : Gaussian :=

    LiftedReadings.ClearGrid.RegularPrimitiveFragment.SheetEntry.LiftedSource.value
    piece.occurrence shared

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment in
/-- The displayed fragment word retains both coordinate and actual root
agreement at every junction. Numerical primitive offsets are separate. -/
inductive RootedWord : List (LiftedFragment axes domains mesh
  source count target) →
    Gaussian.Basic.Canonical → Gaussian.Name.Basic.Named → Gaussian.Basic.Canonical → Gaussian.Name.Basic.Named → Prop
  /-- An empty fragment word retaining coordinate equality and actual root equivalence. -/ | nil {first last :
    Gaussian.Basic.Canonical} {firstName lastName : Gaussian.Name.Basic.Named}
      (coordinate : first = last) (root : Nonempty (NamedEquivalent firstName lastName)) :
      RootedWord [] first
        firstName last lastName
  /-- One original fragment with its initial coordinate and root junction, followed by the exact rooted tail. -/ | cons
    (piece : LiftedFragment axes domains mesh source count
    target)
      {pieces : List (LiftedFragment axes domains mesh source
        count target)}
      {first last : Gaussian.Basic.Canonical} {firstName lastName : Gaussian.Name.Basic.Named}
      (coordinate : first = piece.first) (root : Nonempty (NamedEquivalent firstName
        piece.firstName))
      (tail : RootedWord pieces
        piece.last piece.lastName last lastName) :
      RootedWord (piece :: pieces)
        first firstName last lastName

namespace RootedWord

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment
/-- Transport the original rooted word along the supplied initial coordinate equality and actual root equivalence. -/
theorem changeStart {pieces : List (LiftedFragment axes domains
  mesh source count target)}
    {first middle last : Gaussian.Basic.Canonical} {firstName middleName lastName : Gaussian.Name.Basic.Named}
    (word : RootedWord pieces middle middleName
      last lastName) (coordinate : first = middle)
    (root : Nonempty (NamedEquivalent firstName middleName)) :
      RootedWord pieces first firstName last
      lastName := by
  obtain ⟨root⟩ := root
  cases word with
  | nil equal equivalent =>
      obtain ⟨equivalent⟩ := equivalent
      exact .nil (coordinate.trans equal) ⟨root.trans equivalent⟩
  | cons piece equal equivalent tail =>
      obtain ⟨equivalent⟩ := equivalent
      exact .cons piece (coordinate.trans equal) ⟨root.trans equivalent⟩ tail

/-- Transport only the retained terminal coordinate, preserving its original root name. -/
theorem castFinish {pieces : List (LiftedFragment axes domains
  mesh source count target)}
    {first last next : Gaussian.Basic.Canonical} {firstName lastName : Gaussian.Name.Basic.Named}
    (word : RootedWord pieces first firstName
      last lastName) (coordinate : last = next) :
    RootedWord pieces first firstName next
      lastName := coordinate ▸ word

/-- Concatenate two actual rooted words sharing the same intermediate coordinate and root name. -/
theorem append {firstPieces lastPieces : List (LiftedFragment
  axes domains mesh source count target)}
    {first middle last : Gaussian.Basic.Canonical} {firstName middleName lastName : Gaussian.Name.Basic.Named}
    (left : RootedWord firstPieces first
      firstName middle middleName)
    (right : RootedWord lastPieces middle
      middleName last lastName) :
    RootedWord (firstPieces ++ lastPieces) first
      firstName last lastName := by
  induction left with
  | nil coordinate root => exact right.changeStart coordinate root
  | cons piece coordinate root tail ih => exact .cons piece coordinate root (ih right)

end RootedWord
end LiftedFragment

namespace RegularPrimitiveFragments.SheetEntries.LiftedSources

variable {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve source} {partition :
  Rectangle.AxisPartition 0 1 (axes.parameters parent)}
  {request : Readings.UniformPreparedRequests.LocalRequest parent count target}

open
  SheetEntries.LiftedSources
  in
/-- Flatten the original one-parent source spine without preparing new owners.

The actual cut list is materialized once for this parent and shared by all
retained occurrences. Every partition, fragment, request, sheet entry and
lifted source remains the supplied original cache in its original order. -/
@[expose] def pieces : ∀ {intervals : List PreparedAxisPartitions.Interval}
    {fragments : RegularFaces.RegularPrimitiveFragments axes parent
      partition intervals}
    {entries : SheetEntries domains request fragments}, LiftedSources mesh entries →
      List (LiftedFragment axes domains mesh source count
        target) :=
  let Payload (storedCuts : List Fraction.Rational) (interval : PreparedAxisPartitions.Interval) :=
    Σ retainedPartition : Rectangle.AxisPartition 0 1 storedCuts,
    Σ retainedFragment : RegularFaces.RegularPrimitiveFragment axes parent retainedPartition interval,
    Σ retainedEntry : SheetEntries.RegularPrimitiveFragment.SheetEntry retainedFragment domains request,
    LiftedEdges.SheetEntry.LiftedSource retainedEntry mesh
  let rec collect (cachedCuts : List Fraction.Rational) (same : axes.parameters parent = cachedCuts) :
      ∀ {intervals : List PreparedAxisPartitions.Interval}
        {fragments : RegularFaces.RegularPrimitiveFragments axes parent partition intervals}
        {entries : SheetEntries domains request fragments}, LiftedSources mesh entries →
          List (LiftedFragment axes domains mesh source count target)
    | _, _, _, .nil => []
    | _, _, _, .cons (interval := interval) (head := fragment) (entry := assigned) first rest =>
        let original : Payload (axes.parameters parent) interval := ⟨partition, fragment, assigned, first⟩
        let retained : Payload cachedCuts interval :=
          Eq.mp (congrArg (fun storedCuts => Payload storedCuts interval) same) original
        ⟨parent, cachedCuts, retained.1, interval, retained.2.1, request, retained.2.2.1, retained.2.2.2⟩ ::
          collect cachedCuts same rest
  let cachedCuts := axes.parameters parent
  collect cachedCuts rfl

/-- The original flattened head is its complete supplied parent, partition, request, entry and lifted occurrence.

Only the original pointwise application is reduced. The shared cut cache
and unchanged source tail are the same expressions as in the producer.
-/
theorem pieces_cons {interval : PreparedAxisPartitions.Interval} {intervals : List PreparedAxisPartitions.Interval}
    {head : RegularFaces.RegularPrimitiveFragment axes parent partition interval}
    {tail : RegularFaces.RegularPrimitiveFragments axes parent partition intervals}
    {entry : SheetEntries.RegularPrimitiveFragment.SheetEntry head domains request}
    {entries : SheetEntries domains request tail}
    (first : LiftedEdges.SheetEntry.LiftedSource entry mesh)
    (remaining : LiftedReadings.ClearGrid.RegularPrimitiveFragments.SheetEntries.LiftedSources mesh entries) :
    pieces (.cons first remaining) =
      (⟨parent, axes.parameters parent, partition, interval, head, request, entry, first⟩ :
        LiftedFragment axes domains mesh source count target) :: pieces remaining := rfl

/-- Equal retained parameters give equal original parent root query names. -/
private theorem name_eq {a b : Fraction.Rational} (aInside : 0 ≤ a ∧ a ≤ 1) (bInside : 0 ≤ b ∧ b ≤ 1) (equal : a = b) :
    parent.edge.rootName a aInside = parent.edge.rootName b bInside := by
  cases equal
  rfl

open
  SheetEntries.LiftedSources
  in
/-- The original increasing interval walk certifies all coordinate and root junctions of its retained fragments. -/
theorem rooted_of_walk {intervals : List PreparedAxisPartitions.Interval}
    {fragments : RegularFaces.RegularPrimitiveFragments axes parent
      partition intervals}
    {entries : SheetEntries domains request fragments} (sources : LiftedSources mesh entries)
    {available : List PreparedAxisPartitions.Interval} {lower upper : Fraction.Rational}
    (walk : Geometry.Grid.AxisWalks.IncreasingWalk available lower upper) (ordered : intervals = walk.edges)
    (lowerInside : 0 ≤ lower ∧ lower ≤ 1) (upperInside : 0 ≤ upper ∧ upper ≤ 1) :
    LiftedFragment.RootedWord (pieces sources)
      (parent.edge.point lower) (parent.edge.rootName lower lowerInside)
      (parent.edge.point upper) (parent.edge.rootName upper upperInside) := by
  induction sources generalizing lower upper with
  | nil =>
      cases walk with
      | nil => exact .nil rfl ⟨NamedEquivalent.refl _⟩
      | cons => cases ordered
  | @cons interval intervals fragment fragments assigned entries first rest ih =>
      cases walk with
      | nil => cases ordered
      | cons head member walk =>
          have equations := List.cons.inj ordered
          have lowerEq := congrArg (fun interval : PreparedAxisPartitions.Interval =>
            interval.lower) equations.1
          have upperEq := congrArg (fun interval : PreparedAxisPartitions.Interval =>
            interval.upper) equations.1
          have nextInside : 0 ≤ head.upper ∧ head.upper ≤ 1 := upperEq ▸ first.finishInside
          have tail := ih walk equations.2 nextInside upperInside
          have firstNameEq :=
            name_eq
            (parent := parent) assigned.fractionInside lowerInside lowerEq
          have lastNameEq :=
            name_eq
            (parent := parent) first.finishInside nextInside upperEq
          refine .cons _ (fragment.located.first_eq.trans (congrArg parent.edge.point lowerEq)).symm
            ⟨firstNameEq.symm ▸ NamedEquivalent.refl _⟩ ?_
          exact tail.changeStart (fragment.located.last_eq.trans (congrArg parent.edge.point upperEq))
            ⟨lastNameEq ▸ NamedEquivalent.refl _⟩

open
  SheetEntries.LiftedSources
  in
/-- The original one-parent source readings equal the readings of its exact flattened fragments. -/
theorem values_eq_pieces {intervals : List PreparedAxisPartitions.Interval}
    {fragments : RegularFaces.RegularPrimitiveFragments axes parent
      partition intervals}
    {entries : SheetEntries domains request fragments} (sources : LiftedSources mesh entries)
    {points : List Gaussian.Basic.Canonical} {tolerance : Fraction.Rational} {index : Nat}
    {budgets : Face.CommonMeshes.FaceMeshBudgets source points tolerance (numerator := numerator) domains}
      {numerics : Face.PrimitiveData.FacePrimitiveBank source index (numerator := numerator) domains}
    (shared : Face.CommonMeshes.FaceSharedMeshes budgets numerics) : sources.values
      shared = (pieces sources).map (fun piece => piece.value shared) := by
  induction sources with
  | nil => rfl
  | cons first rest ih =>
    exact congrArg (List.cons
      (LiftedReadings.ClearGrid.RegularPrimitiveFragment.SheetEntry.LiftedSource.value first shared)) ih

end RegularPrimitiveFragments.SheetEntries.LiftedSources

/-- The original parent coordinates in order, independently of root names.
Stationary sheet transitions do not change these coordinates. -/
inductive ParentCoordinates : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve source) →
  Gaussian.Basic.Canonical → Gaussian.Basic.Canonical → Prop
  /-- The empty parent chain at its retained coordinate. -/ | nil (point : Gaussian.Basic.Canonical) :
    ParentCoordinates [] point point
  /-- One original parent edge followed by a tail at its exact terminal coordinate. -/ | cons (parent :
    Integration.PreparedSubdivisionModelCore.CenteredEdge curve source) {parents : List
    (Integration.PreparedSubdivisionModelCore.CenteredEdge curve source)} {last : Gaussian.Basic.Canonical}
      (tail : ParentCoordinates parents
        (parent.edge.point 1) last) :
      ParentCoordinates (parent :: parents)
        (parent.edge.point 0) last

namespace ParentCoordinates

/-- Read the original parent coordinate chain while preserving every stationary sheet transition's unchanged coordinate.
-/
theorem ofSwitched : ∀ {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve source)} {first last
  : Path.Gaussian.Lifted.Basic.LiftedPoint 2},
    Integration.PreparedSwitchedRefinements.SwitchedPathChain parents (start := first) (finish := last) →
      ParentCoordinates parents first.coordinate last.coordinate
  | _, _, _, .nil _ => .nil _
  | _, _, _, .edge parent tail => by
      have remaining :=
        ofSwitched tail
      have word := ParentCoordinates.cons parent (last := _) (by
        rw [Integration.PreparedConstantModels.PreparedEdge.point_one]
        exact remaining)
      rw [Integration.PreparedConstantModels.PreparedEdge.point_zero] at word
      exact word
  | _, _, _, .stationary coordinate sheet tail =>
      ofSwitched (first := {
        coordinate := coordinate, sheet := Branches.BranchCutLifts.otherSheet sheet }) tail

/-- Recasting the differential preserves the original parent-coordinate chain. -/
theorem recast (differential : Differentials.Basic.Differential genus) {parents : List
  (Integration.PreparedSubdivisionModelCore.CenteredEdge curve source)} {first last : Gaussian.Basic.Canonical}
    (coordinates : ParentCoordinates parents first last) :
    ParentCoordinates (parents.map
      (Integration.PreparedEdgeRecasting.recastCenteredEdge differential)) first last := by
  induction coordinates with
  | nil => exact .nil _
  | cons parent tail ih => exact .cons (Integration.PreparedEdgeRecasting.recastCenteredEdge differential parent) ih

end ParentCoordinates

namespace RegularPrimitiveSplits.SheetEntries.LiftedSources

open
  SheetEntries.LiftedSources
  in
/-- Flatten all original parent fragment spines in their retained order. -/
@[expose] def pieces : ∀ {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve source)} {splits :
  PreparedPrimitiveSplits.PrimitiveSplits axes parents}
    {fragments : RegularFaces.RegularPrimitiveSplits (base := base) axes
      splits} {requests : Readings.UniformPreparedRequests.RequestedParents count target parents}
    {entries : SheetEntries domains fragments requests}, LiftedSources mesh entries →
      List (LiftedFragment axes domains mesh source count
        target)
  | _, _, _, _, _, .nil => []
  | _, _, _, _, _, .cons first rest =>

        RegularPrimitiveFragments.SheetEntries.LiftedSources.pieces
        first ++ pieces rest

open
  SheetEntries.LiftedSources
  in
/-- The original coordinate and root chains supply every cross-parent
junction. No fragment or stationary handoff is dropped by a root test. -/
theorem rooted {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve source)} {splits :
  PreparedPrimitiveSplits.PrimitiveSplits axes parents}
    {fragments : RegularFaces.RegularPrimitiveSplits (base := base) axes
      splits} {requests : Readings.UniformPreparedRequests.RequestedParents count target parents}
    {entries : SheetEntries domains fragments requests} (sources : LiftedSources mesh entries)
    {first last : Gaussian.Basic.Canonical} {firstName lastName : Gaussian.Name.Basic.Named}
    (coordinates : ParentCoordinates parents first last) (roots
      : Topology.PreparedRefinementRootChains.RootChain parents firstName lastName) :
    LiftedFragment.RootedWord (pieces sources) first firstName
      last lastName := by
  induction sources generalizing first last firstName lastName with
  | nil =>
      cases coordinates
      cases roots with
      | nil equivalent => exact .nil rfl ⟨equivalent⟩
  | @cons parent parents partition splits head tail request requests firstEntries restEntries firstSources restSources
    ih =>
      cases coordinates with
      | cons _ tailCoordinates =>
          cases roots with
          | cons _ entry tailRoots =>
              have initial :=
                RegularPrimitiveFragments.SheetEntries.LiftedSources.rooted_of_walk
                firstSources partition.walk partition.walk_edges.symm
                parent.edge.baseInside (by decide)
              exact (initial.changeStart rfl ⟨entry⟩).append (ih tailCoordinates tailRoots)

open
  SheetEntries.LiftedSources
  in
/-- The actual original source readings equal the values of the complete flattened fragment word.

Each head source bank retains its original readings and flattened occurrences. Ordered concatenation combines the same
head and tail lists before mapping their retained values. -/
theorem values_eq_pieces {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve source)} {splits :
  PreparedPrimitiveSplits.PrimitiveSplits axes parents}
    {fragments : RegularFaces.RegularPrimitiveSplits (base := base) axes
      splits} {requests : Readings.UniformPreparedRequests.RequestedParents count target parents}
    {entries : SheetEntries domains fragments requests} (sources : LiftedSources mesh entries)
    {points : List Gaussian.Basic.Canonical} {tolerance : Fraction.Rational} {index : Nat}
    {budgets : Face.CommonMeshes.FaceMeshBudgets source points tolerance (numerator := numerator) domains}
      {numerics : Face.PrimitiveData.FacePrimitiveBank source index (numerator := numerator) domains}
    (shared : Face.CommonMeshes.FaceSharedMeshes budgets numerics) : sources.values
      shared = (pieces sources).map (fun piece => piece.value shared) := by
  induction sources with
  | nil => rfl
  | cons first rest ih =>
      exact (congrArg₂ List.append
        (RegularPrimitiveFragments.SheetEntries.LiftedSources.values_eq_pieces
        first shared) ih).trans (Map.map_append _ _ _).symm

set_option genInjectivity false in
open
  SheetEntries.LiftedSources
  in
/-- Cache the original flattened fragment word and its root-junction certificate.

The exact original source spine determines the retained ordered piece list. Its coordinate and root certificate joins
the supplied first and last names through those same cached occurrences. -/
structure Rooted {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve source)} {splits :
  PreparedPrimitiveSplits.PrimitiveSplits axes parents}
    {fragments : RegularFaces.RegularPrimitiveSplits (base := base) axes
      splits} {requests : Readings.UniformPreparedRequests.RequestedParents count target parents}
    (entries : SheetEntries domains fragments requests) (mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges
      base.faces)
    (first : Gaussian.Basic.Canonical) (firstName : Gaussian.Name.Basic.Named)
    (last : Gaussian.Basic.Canonical) (lastName : Gaussian.Name.Basic.Named) : Type 2 where
  /-- The original lifted source spine. -/ sources : LiftedSources mesh entries
  /-- The cached original flattened fragments. -/ pieces : List
    (LiftedFragment axes domains mesh source count target)
  /-- The cached list equals the exact original source-spine flattening. -/ pieces_eq : pieces =
    LiftedSources.pieces
    sources
  /-- The actual coordinate and root junction certificate for that retained list. -/ rooted :
    LiftedFragment.RootedWord pieces first firstName last
    lastName

constructive_injectivity Rooted

namespace Rooted

variable {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve source)} {splits :
  PreparedPrimitiveSplits.PrimitiveSplits axes parents}
  {fragments : RegularFaces.RegularPrimitiveSplits (base := base) axes
    splits} {requests : Readings.UniformPreparedRequests.RequestedParents count target parents}
  {entries : SheetEntries domains fragments requests}
  {first last : Gaussian.Basic.Canonical} {firstName lastName : Gaussian.Name.Basic.Named}

/-- Cache the original flattened fragments once and certify their junctions from the retained parent coordinate and root
chains. -/
@[expose] def build (sources : LiftedSources mesh entries) (coordinates :
  ParentCoordinates parents first last)
    (roots : Topology.PreparedRefinementRootChains.RootChain parents firstName lastName) :
      Rooted
      entries mesh first firstName last lastName :=
  ⟨sources,
    LiftedSources.pieces
    sources,
    rfl,
      LiftedSources.rooted
      sources coordinates roots⟩

variable {points : List Gaussian.Basic.Canonical} {tolerance : Fraction.Rational} {index : Nat}
  {budgets : Face.CommonMeshes.FaceMeshBudgets source points tolerance (numerator := numerator) domains}
    {numerics : Face.PrimitiveData.FacePrimitiveBank source index (numerator := numerator) domains}

/-- Read the exact cached fragment word on the supplied shared meshes. -/
@[expose] def values (word :
  Rooted
  entries mesh first firstName last lastName) (shared :
  Face.CommonMeshes.FaceSharedMeshes budgets numerics) : List Gaussian :=
  word.pieces.map (fun piece => piece.value shared)

/-- The cached rooted word has exactly the original source-spine readings. -/
theorem values_eq (word :
  Rooted
  entries mesh first firstName last lastName) (shared :
  Face.CommonMeshes.FaceSharedMeshes budgets numerics) :
    word.values shared = word.sources.values shared := by
  rw
    [values,
    word.pieces_eq,
    values_eq_pieces
    word.sources shared]

/-- The rooted word's actual Gaussian sum equals the retained original shared summary. -/
theorem sum_eq {budgets : Face.CommonMeshes.FaceMeshBudgets source points tolerance domains}
    {numerics : Face.PrimitiveData.FacePrimitiveBank source index domains} (word :
  Rooted
  entries mesh first firstName last lastName) {shared :
  Face.CommonMeshes.FaceSharedMeshes budgets numerics}
    (summary : SharedSums.RegularPrimitiveSplits.SheetEntries.SharedSum
      shared entries) : Gaussian.Norm.Sum.Basic.gaussianSum (word.values shared) = summary.value := by
  rw [word.values_eq, word.sources.sum_eq summary]

end Rooted

end RegularPrimitiveSplits.SheetEntries.LiftedSources
end
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
