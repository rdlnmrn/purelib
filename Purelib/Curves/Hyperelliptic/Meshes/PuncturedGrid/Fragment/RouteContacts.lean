module
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContactRequests.Polynomial
public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Ordinary
import Purelib.Polynomial.Dense.Gaussian.Basic
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContactRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshContactRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.BankReadings
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.ChartContacts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.EndpointSheets
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.JunctionSheets
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Riemann.Integration.PreparedQueryNegation
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Paths.ClearBoxPathWinding
import Purelib.Riemann.Paths.ClearBoxPaths
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Readings.RectangularPrimitiveBoundary
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamContacts
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedEdges
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.EdgeSides
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Integration.RectangularSharedPrimitives
import Purelib.Riemann.Meshes.PuncturedEdgeFaces
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularExteriorBoundary
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Riemann
open Purelib.RootIsolation

public section

/-! Requested transport of original partial increments to actual grid-edge routes. -/

open Purelib.Riemann.Integration.RectangularSharedPrimitives renaming SharedPrimitiveValues -> SharedValues

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteContacts

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
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

/-- The original incoming query owner is materialized once for the shared
partial-edge preparation. Its named-root certificate remains proof data. -/
@[expose] def startOwner (piece : RootedWords.LiftedFragment axes domains
  mesh source count target) : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval piece.first) :=
  Integration.PreparedQueryNegation.PreparedEdge.ownerAtPoint piece.parent.edge piece.interval.lower
    piece.assigned.fractionInside piece.first piece.fragment.located.first_eq.symm

/-- Read the same partial endpoints in another retained occurrence of the
actual lifted containing edge. The complete edge is never substituted for
its partial increment. -/
@[expose] def routeValue (piece : RootedWords.LiftedFragment axes domains
  mesh source count target)
    (location : MeshPathWalks.EdgeRoute mesh piece.occurrence.side.edge)
    {points : List Gaussian.Basic.Canonical} {tolerance : Fraction.Rational} {index : Nat}
    {budgets : Face.CommonMeshes.FaceMeshBudgets source points tolerance (numerator := numerator) domains}
      {numerics : Face.PrimitiveData.FacePrimitiveBank source index (numerator := numerator) domains}
    (shared : Face.CommonMeshes.FaceSharedMeshes budgets numerics) : Gaussian :=
  let readings := ((Face.MeshWords.FaceSharedMeshes.atRoute shared location).atSheet
    location.sheet).readings
  SharedValues.atPoint readings piece.last -
    SharedValues.atPoint readings piece.first

/-- Both partial endpoints lie in every retained face occurrence of their
actual lifted containing edge, regardless of the fragment's direction. -/
theorem route_endpoints_inside (piece : RootedWords.LiftedFragment axes
  domains mesh source count target)
    (location : MeshPathWalks.EdgeRoute mesh piece.occurrence.side.edge) :
    location.face.cell.box.Contains piece.first ∧ location.face.cell.box.Contains piece.last := by
  have first : location.face.cell.box.Contains piece.fragment.source.start :=
    (congrArg location.face.cell.box.Contains piece.occurrence.side.start_eq).mp location.endpoints_inside.1
  have last : location.face.cell.box.Contains piece.fragment.source.finish :=
    (congrArg location.face.cell.box.Contains piece.occurrence.side.finish_eq).mp location.endpoints_inside.2
  exact ⟨piece.fragment.source.first.contained first last, piece.fragment.source.last.contained first last⟩

/-- Transport the original query occurrence through the common edge prefix
into the other face. A matching coordinate is not used as root agreement. -/
theorem route_start_reached (piece : RootedWords.LiftedFragment axes domains
  mesh source count target)
    (location : MeshPathWalks.EdgeRoute mesh piece.occurrence.side.edge) :
    Integration.Observation.PreparedFaceTracePrefixes.Reached location.face.cell.box ((domains.atRoute
      location).models.frame.owners location.sheet)
      (RouteContacts.startOwner piece) := by
  let firstFace := base.faces.regulars[piece.fragment.face.located.index.val]
  have firstInside : firstFace.cell.box.Contains (vertices.coordinate piece.occurrence.side.edge.start) := by
    dsimp only [firstFace]
    rw [← piece.occurrence.side.face_eq]
    exact piece.occurrence.side.route.endpoints_inside.1
  have queryInside : firstFace.cell.box.Contains piece.first := by
    dsimp only [firstFace]
    rw [piece.fragment.face.located.indexed, piece.fragment.face.located.cell_eq]
    exact piece.fragment.first_inside
  let raw := piece.fragment.source.edge.segment.restrict piece.fragment.source.edge.withinAmbient
    0 piece.fragment.source.first.parameter (by decide) piece.fragment.source.first.inside
  let edgePrefix := (raw.castStart (piece.fragment.source.edge.segment.pointAt_zero.trans
    piece.occurrence.side.start_eq.symm)).castFinish
    piece.fragment.source.first.point_eq
  have reached := JunctionSheets.Reached.change_box_along
    piece.occurrence.first_reached firstFace.clearance location.face.clearance
    (Branches.BranchIsolation.degreePositive curve) edgePrefix firstInside queryInside
      location.endpoints_inside.1
    (RouteContacts.route_endpoints_inside piece location).1
  exact (location.endpoints_reached (domains.atRoute location).models).1.append reached

set_option genInjectivity false in
/-- The common partial path, owner, and parent cache are retained once.
Both entries use the existing face domains and the actual lifted edge sheet. -/
structure RouteContact (piece : RootedWords.LiftedFragment axes domains mesh
  source count target)
    (location : MeshPathWalks.EdgeRoute mesh piece.occurrence.side.edge) : Type 2
      where
  /-- The shared original query owner at the fragment's first endpoint. -/ owner :
    Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval piece.first)
  /-- The shared owner is exactly the materialized original fragment query owner. -/ owner_eq : owner =
    RouteContacts.startOwner piece
  /-- The actual partial route between the fragment's original endpoints. -/ route : Paths.ClearBoxPaths.Route
    curve.polynomial piece.fragment.face.located.face.cell.box piece.first piece.last
  /-- The retained traced preparation of that same partial path and owner. -/ prepared :
    Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath route.path owner
  /-- The shared parent cache for that exact prepared partial path. -/ cache :
    Paths.PreparedPathParentCaches.PreparedClearPathModels.ParentCache prepared source 0
  /-- The original fragment face entry on the shared preparation. -/ left :
    Face.EnteredPaths.EnteredPath
    (SheetEntries.RegularPrimitiveFragment.domainCache piece.fragment
    domains).models prepared source 0
  /-- The actual route face entry on the shared preparation. -/ right :
    Face.EnteredPaths.EnteredPath (domains.atRoute location).models prepared source 0
  /-- The left entry reuses the exact retained parent cache. -/ left_cache : left.cache = cache
  /-- The right entry reuses the exact retained parent cache. -/ right_cache : right.cache = cache
  /-- The left entry retains the original fragment's assigned sheet. -/ left_sheet : left.entry.sheet =
    piece.assigned.entry.sheet
  /-- The right entry retains the actual lifted route occurrence's sheet. -/ right_sheet : right.entry.sheet =
    location.sheet
  /-- The left entry retains the original fragment's domain. -/ left_domain : HEq left.domain piece.assigned.domain
  /-- The right entry retains the actual route occurrence's original domain. -/ right_domain : HEq right.domain
    ((domains.atRoute location).domain location.sheet)

constructive_injectivity RouteContact

namespace RouteContact

/-- Retain the supplied common owner, partial path and parent cache in both original face-domain entries with their
exact sheets. -/
@[expose] public def ofPrepared (piece : RootedWords.LiftedFragment axes
  domains mesh
  source count target)
    (location : MeshPathWalks.EdgeRoute mesh piece.occurrence.side.edge)
    (owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval piece.first)) (ownerEq : owner =
      RouteContacts.startOwner piece)
    (route : Paths.ClearBoxPaths.Route curve.polynomial piece.fragment.face.located.face.cell.box piece.first
      piece.last)
    (prepared : Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath route.path owner) (cache :
      Paths.PreparedPathParentCaches.PreparedClearPathModels.ParentCache prepared source 0)
    (leftWithin : route.path.InBox piece.fragment.face.located.face.cell.box)
    (rightWithin : route.path.InBox location.face.cell.box) :
      RouteContact piece location := by
  let leftEntry : Face.Entries.FaceModels.Entry
    (SheetEntries.RegularPrimitiveFragment.domainCache piece.fragment
    domains).models piece.first owner :=
    ⟨piece.assigned.entry.sheet, (congrArg (fun current =>
      Integration.Observation.PreparedFaceTracePrefixes.Reached piece.fragment.face.located.face.cell.box
      ((SheetEntries.RegularPrimitiveFragment.domainCache piece.fragment
        domains).models.frame.owners piece.assigned.entry.sheet) current) ownerEq).mpr
      (EndpointSheets.SheetEntry.first_query_reached piece.assigned)⟩
  let rightEntry : Face.Entries.FaceModels.Entry (domains.atRoute location).models
    piece.first owner :=
    ⟨location.sheet, (congrArg (fun current => Integration.Observation.PreparedFaceTracePrefixes.Reached
      location.face.cell.box
      ((domains.atRoute location).models.frame.owners location.sheet) current) ownerEq).mpr
      (RouteContacts.route_start_reached piece location)⟩
  let left : Face.EnteredPaths.EnteredPath
    (SheetEntries.RegularPrimitiveFragment.domainCache piece.fragment
    domains).models prepared source 0 :=
    Face.EnteredPaths.EnteredPath.ofEntry leftEntry piece.assigned.domain prepared
    leftWithin source 0 cache
  let right : Face.EnteredPaths.EnteredPath (domains.atRoute location).models
    prepared source 0 :=
    Face.EnteredPaths.EnteredPath.ofEntry rightEntry ((domains.atRoute
      location).domain location.sheet) prepared
    rightWithin source 0 cache
  exact ⟨owner, ownerEq, route, prepared, cache, left, right, rfl, rfl, rfl, rfl, HEq.rfl, HEq.rfl⟩

/-- Prepare the actual fragment's partial path once and enter that same retained owner and cache in the two original
face occurrences. -/
@[expose] def build (piece : RootedWords.LiftedFragment axes domains mesh
  source count target)
    (location : MeshPathWalks.EdgeRoute mesh piece.occurrence.side.edge) :
      RouteContact piece location := by
  have firstInside : piece.fragment.face.located.face.cell.box.Contains piece.first := by
    rw [piece.fragment.face.located.cell_eq]
    exact piece.fragment.first_inside
  have lastInside : piece.fragment.face.located.face.cell.box.Contains piece.last := by
    rw [piece.fragment.face.located.cell_eq]
    exact piece.fragment.last_inside
  let owner := RouteContacts.startOwner piece
  let route := Paths.ClearBoxPaths.Route.build piece.fragment.face.located.face.clearance piece.first piece.last
    firstInside lastInside
  let prepared := Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath.build route.path
    route.within owner
  let cache := Paths.PreparedPathParentCaches.PreparedClearPathModels.ParentCache.build prepared source 0
  exact RouteContact.ofPrepared piece location owner
    rfl route prepared cache
    (Geometry.ClearPath.InBox.ofWithin route.path route.within firstInside)
    (ChartContacts.Route.build_inBox
      piece.fragment.face.located.face.clearance _ _ firstInside lastInside
      (RouteContacts.route_endpoints_inside piece location).1
        (RouteContacts.route_endpoints_inside piece location).2)

/-- Prepare a positive accuracy allowance on the two actual retained contact entries. -/
@[expose] def budget {piece : RootedWords.LiftedFragment axes domains mesh
  source count target}
    {location : MeshPathWalks.EdgeRoute mesh piece.occurrence.side.edge}
    (contact : RouteContact piece location) (allowance :
      Fraction.Rational) (positive : 0 < allowance) :
    ContactRequests.ContactBudget contact.left contact.right allowance :=
  ContactRequests.ContactBudget.build contact.left contact.right allowance
    positive

section NumeratorBudgets

open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic.OddPowerDifferential (Ordinary)

variable {piece : RootedWords.LiftedFragment axes domains mesh source count target}
    {location : MeshPathWalks.EdgeRoute mesh piece.occurrence.side.edge}
    (contact : RouteContact piece location)

/-- The original route contact's legacy budget or genuine ordinary-polynomial allocation on the SAME entries.

The absent specification is exactly the original budget type. A supplied
ordinary specification retains its positive allowance and original P-bound
preparation without changing the route, root Owner, ParentCache or Entries.
-/
@[expose] def Budget (allowance : Fraction.Rational)
    (polynomial : Option (Ordinary curve.polynomial) := none) : Type _ :=
  match polynomial with
  | none => ContactRequests.ContactBudget contact.left contact.right allowance
  | some ordinary =>
      (positive : {_value : Unit // 0 < allowance}) ×
        ContactRequests.ContactBudget.PolynomialPreparation contact.left contact.right
          ordinary.val allowance positive.property

/-- Allocate only the numerical request on the two GIVEN contact entries, preserving every geometric cache.

The legacy branch calls the original unchanged producer. The polynomial
branch constructs actual P bounds and independent source/face floors before
any primitive bank or common-model observations are prepared.
-/
def prepareBudget (allowance : Fraction.Rational) (positive : 0 < allowance)
    (polynomial : Option (Ordinary curve.polynomial) := none) : contact.Budget allowance polynomial :=
  match polynomial with
  | none => contact.budget allowance positive
  | some ordinary =>
      ⟨⟨(), positive⟩, ContactRequests.ContactBudget.preparePolynomial
        (owner := contact.owner) (prepared := contact.prepared) contact.left contact.right
        ordinary.val ordinary.property allowance positive⟩

/-- The absent specification retains the literal original contact budget. -/
theorem prepareBudget_none (allowance : Fraction.Rational) (positive : 0 < allowance) :
    contact.prepareBudget allowance positive none = contact.budget allowance positive := by
  unfold prepareBudget
  rfl

/-- The polynomial branch retains the original whole P preparation on the actual supplied entries. -/
theorem prepareBudget_some (allowance : Fraction.Rational) (positive : 0 < allowance)
    (ordinary : Ordinary curve.polynomial) :
    (contact.prepareBudget allowance positive (some ordinary)).2 =
      ContactRequests.ContactBudget.preparePolynomial
        (owner := contact.owner) (prepared := contact.prepared) contact.left contact.right
        ordinary.val ordinary.property allowance positive := by
  unfold prepareBudget
  rfl

namespace Budget

variable {contact} {allowance : Fraction.Rational} {polynomial : Option (Ordinary curve.polynomial)}

/-- Read the selected request's actual independent face-model floor. -/
@[expose] def index (kept : Budget contact allowance polynomial) : Nat :=
  match polynomial with
  | none => ContactRequests.ContactBudget.index kept
  | some _ordinary => ContactRequests.ContactBudget.index kept.2.budget

/-- The default floor remains the actual original cached legacy index. -/
theorem index_none (kept : Budget contact allowance none) :
    index kept = ContactRequests.ContactBudget.index kept := rfl

/-- The genuine P floor is the actual cached polynomial budget index. -/
theorem index_some {ordinary : Ordinary curve.polynomial}
    (kept : Budget contact allowance (some ordinary)) :
    index kept = ContactRequests.ContactBudget.index kept.2.budget := rfl

end Budget

end NumeratorBudgets

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteContacts.RouteContact in
/-- At a sufficiently late common face reading, the original fragment increment and actual route occurrence reading
differ by less than the retained allowance. -/
theorem accurate {piece : RootedWords.LiftedFragment axes domains mesh
  source count target}
    {location : MeshPathWalks.EdgeRoute mesh piece.occurrence.side.edge}
    (contact : RouteContact piece location) {allowance :
      Fraction.Rational}
    (budget : ContactRequests.ContactBudget contact.left contact.right
      allowance)
    {points : List Gaussian.Basic.Canonical} {tolerance : Fraction.Rational} {index : Nat}
    {budgets : Face.CommonMeshes.FaceMeshBudgets source points tolerance domains}
      {numerics : Face.PrimitiveData.FacePrimitiveBank source index domains}
    (shared : Face.CommonMeshes.FaceSharedMeshes budgets numerics) (later :
      budget.index ≤ index)
    (firstPresent : piece.first ∈ points) (lastPresent : piece.last ∈ points) :
    Gaussian.Norm.Basic.normSq (piece.value shared -
      RouteContacts.routeValue piece location shared) < allowance := by
  have estimate :=
    Face.MeshContactRequests.ContactBudget.transition_accurate_of_domains budget
    later piece.assigned.domain
    ((domains.atRoute location).domain location.sheet) contact.left_sheet contact.right_sheet contact.left_domain
      contact.right_domain
    (BankReadings.meshReadings piece.assigned shared)
      ((Face.MeshWords.FaceSharedMeshes.atRoute shared location).atSheet
      location.sheet)
    firstPresent lastPresent firstPresent lastPresent
  rw [SeamReadings.assigned_atPoint piece shared piece.last,
    SeamReadings.assigned_atPoint piece shared piece.first] at estimate
  rw [SeamReadings.value_eq_atPoint piece shared]
  exact (congrArg Gaussian.Norm.Basic.normSq (by
    dsimp only [RouteContacts.routeValue]
    ring1 : _ = _)).trans_lt estimate

end RouteContact
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteContacts
