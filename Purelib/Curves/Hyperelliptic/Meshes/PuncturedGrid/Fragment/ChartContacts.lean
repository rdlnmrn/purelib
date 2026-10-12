module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Clearance.Box.Region

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.EndpointSheets
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshFaceEntries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Riemann.Integration.PreparedQueryNegation
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Paths.ClearBoxPathWinding
import Purelib.Riemann.Paths.ClearBoxPaths
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshContactRequests
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings
import Init.Prelude
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Polynomial.Clearance.Box.Line.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.EdgeSides
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedEdgeFaces
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Approximation

open Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.EndpointSheets

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries

open Purelib.Geometry

open Purelib.Polynomial.Clearance.Box

open Purelib.Polynomial.Geometry

open Purelib.Polynomial.Geometry.ClearPath

open Purelib.Riemann.Integration.PreparedQueryNegation

open Purelib.Riemann.Paths

open Purelib.Riemann.Paths.ClearBoxPaths

open Purelib.Riemann.Paths.PreparedPathParentCaches

open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels

open Purelib.Riemann.Paths.PreparedPathPrimitiveCover

open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels

open Purelib.Riemann.Topology

public section

/-!
# One retained path for matching original chart transitions

Two transitions of the same actual chart pair lie in the intersection of
those two clear rectangles. Prepare one finite path in that intersection,
starting with the original first transition's query owner. Both face entries
reuse that owner and the same parent cache; their sheets are inherited.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.ChartContacts.Route

open Purelib.Riemann.Paths.ClearBoxPaths (Route)

/-- The coordinate connector also stays in any other rectangle containing both endpoints. Its original clearance and
preparation remain unchanged. -/
theorem build_inBox {polynomial : ClearPath.GaussianPolynomial} {box other : Rational.Box}
    (clearance : Region.RegionClearance polynomial box)
    (start finish : Data.Gaussian.Basic.Canonical) (first : box.Contains start) (last : box.Contains finish)
    (otherFirst : other.Contains start) (otherLast : other.Contains finish) :
    (Purelib.Riemann.Paths.ClearBoxPaths.Route.build clearance start finish first last).path.InBox other := by
  unfold Route.build
  split
  · rename_i equal
    subst finish
    exact otherFirst
  · dsimp only
    split
    · exact ⟨otherFirst, otherLast⟩
    · split
      · exact ⟨otherFirst, otherLast⟩
      · exact ⟨otherFirst, ⟨otherLast.1, otherLast.2.1, otherFirst.2.2⟩, otherLast⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.ChartContacts.Route

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.ChartContacts.LiftedFragment

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes (Reached)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords (LiftedFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SeamReadings (chart)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank base.bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {source : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus} {axes :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits.PrimitiveAxes base.bank.grid}
  {domains : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames
    base.faces.regulars} {mesh : Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces}
  {count : Nat} {target : Purelib.Data.Rat.Fraction.Rational}

/-- The actual original prepared query owner at the retained fragment's last point. -/
@[expose] def finishOwner (piece : RootedWords.LiftedFragment axes domains mesh source count target) :
  SquareRootContinuationChain.Owner (curve.polynomial.eval piece.last) :=
  PreparedEdge.ownerAtPoint piece.parent.edge piece.interval.upper piece.occurrence.finishInside piece.last
    piece.fragment.located.last_eq.symm

/-- The last-point query owner has exactly the original retained fragment's final root name. -/
theorem finishOwner_name (piece : RootedWords.LiftedFragment axes domains mesh source count target) :
    OwnerTraceReadings.ownerName
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.ChartContacts.LiftedFragment.finishOwner piece) =
      piece.lastName := PreparedEdge.ownerAtPoint_name ..

/-- The retained fragment's last point lies in its actual located regular face box. -/
public theorem last_inside (piece : RootedWords.LiftedFragment axes domains mesh source count target) :
    piece.fragment.face.located.face.cell.box.Contains piece.last := by
  rw [piece.fragment.face.located.cell_eq]
  exact piece.fragment.last_inside

/-- The retained fragment's first point lies in its actual located regular face box. -/
public theorem first_inside (piece : RootedWords.LiftedFragment axes domains mesh source count target) :
    piece.fragment.face.located.face.cell.box.Contains piece.first := by
  rw [piece.fragment.face.located.cell_eq]
  exact piece.fragment.first_inside

/-- Equality of the retained chart identities gives equality of their original located regular faces. -/
theorem face_eq_of_chart {first last : RootedWords.LiftedFragment axes domains mesh source count target}
    (equal : SeamReadings.chart first = SeamReadings.chart last) : first.fragment.face.located.face =
      last.fragment.face.located.face :=
  first.fragment.face.located.indexed.symm.trans
    ((congrArg (fun index : Fin base.faces.regulars.length => base.faces.regulars[index.val])
      (congrArg Prod.fst equal)).trans last.fragment.face.located.indexed)

set_option genInjectivity false in
/-- Shared preparation and both expensive entered-path meshes are cached. Domain and sheet certificates tie them to the
original numerical bank. -/
structure ChartContact (firstLeft firstRight lastLeft lastRight : RootedWords.LiftedFragment axes domains mesh source
  count target) : Type 2 where
  /-- The retained original query owner at the first left transition's last point. -/ owner :
    SquareRootContinuationChain.Owner (curve.polynomial.eval firstLeft.last)
  /-- The contact owner is exactly the original fragment's final prepared query owner. -/ owner_eq : owner =
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.ChartContacts.LiftedFragment.finishOwner firstLeft
  /-- The actual retained clear connector in the original left face rectangle. -/ route : ClearBoxPaths.Route
    curve.polynomial firstLeft.fragment.face.located.face.cell.box firstLeft.last lastLeft.last
  /-- The shared covered connector preparation starting at the original retained query owner. -/ prepared :
    PreparedClearPathModels.CoveredTracedPath route.path owner
  /-- The single retained parent cache shared by both entered connector paths. -/ cache :
    PreparedClearPathModels.ParentCache prepared source 0
  /-- The cached entered connector path in the original left chart's models. -/ left : EnteredPaths.EnteredPath
    ((RegularPrimitiveFragment.domainCache firstLeft.fragment domains)).models prepared source 0
  /-- The cached entered connector path in the original right chart's models. -/ right : EnteredPaths.EnteredPath
    ((RegularPrimitiveFragment.domainCache firstRight.fragment domains)).models prepared source 0
  /-- The left entered path reuses the exact shared original parent cache. -/ left_cache : left.cache = cache
  /-- The right entered path reuses the exact shared original parent cache. -/ right_cache : right.cache = cache
  /-- The left path retains the actual original fragment's assigned sheet. -/ left_sheet : left.entry.sheet =
    firstLeft.assigned.entry.sheet
  /-- The right path retains the actual original fragment's assigned sheet. -/ right_sheet : right.entry.sheet =
    firstRight.assigned.entry.sheet
  /-- The left path retains the original assigned numerical domain. -/ left_domain : HEq left.domain
    firstLeft.assigned.domain
  /-- The right path retains the original assigned numerical domain. -/ right_domain : HEq right.domain
    firstRight.assigned.domain
  /-- Both original left transitions have the same retained chart identity. -/ same_left : SeamReadings.chart firstLeft
    = SeamReadings.chart lastLeft
  /-- Both original right transitions have the same retained chart identity. -/ same_right : SeamReadings.chart
    firstRight = SeamReadings.chart lastRight
  /-- The first original left endpoint equals the first right starting coordinate. -/ first_coordinate : firstLeft.last
    = firstRight.first
  /-- The last original left endpoint equals the last right starting coordinate. -/ last_coordinate : lastLeft.last =
    lastRight.first

constructive_injectivity ChartContact

namespace ChartContact

/-- Prepare one connector in both original chart rectangles using the retained first query owner.

Both entered paths share its original preparation and parent cache; supplied root-name agreement transports the right
sheet without rebuilding its domain. -/
@[expose] def build (firstLeft firstRight lastLeft lastRight : RootedWords.LiftedFragment axes domains mesh source count
  target)
    (firstCoordinate : firstLeft.last = firstRight.first) (lastCoordinate : lastLeft.last = lastRight.first)
    (firstRoots : Nonempty (Gaussian.Equivalence.NamedEquivalent firstLeft.lastName firstRight.firstName))
    (sameLeft : SeamReadings.chart firstLeft = SeamReadings.chart lastLeft) (sameRight : SeamReadings.chart firstRight =
      SeamReadings.chart lastRight) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.ChartContacts.LiftedFragment.ChartContact firstLeft firstRight
      lastLeft lastRight := by
  let leftFace := firstLeft.fragment.face.located.face
  let rightFace := firstRight.fragment.face.located.face
  have leftStart : leftFace.cell.box.Contains firstLeft.last :=
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.ChartContacts.LiftedFragment.last_inside firstLeft
  have leftFinish : leftFace.cell.box.Contains lastLeft.last := by
    rw [show leftFace = lastLeft.fragment.face.located.face from
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.ChartContacts.LiftedFragment.face_eq_of_chart sameLeft]
    exact Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.ChartContacts.LiftedFragment.last_inside lastLeft
  have rightStart : rightFace.cell.box.Contains firstLeft.last := firstCoordinate.symm ▸
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.ChartContacts.LiftedFragment.first_inside firstRight
  have rightFinish : rightFace.cell.box.Contains lastLeft.last := by
    rw [show rightFace = lastRight.fragment.face.located.face from
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.ChartContacts.LiftedFragment.face_eq_of_chart sameRight,
      lastCoordinate]
    exact Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.ChartContacts.LiftedFragment.first_inside lastRight
  let owner := Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.ChartContacts.LiftedFragment.finishOwner firstLeft
  let route := Route.build leftFace.clearance firstLeft.last lastLeft.last leftStart leftFinish
  let prepared := CoveredTracedPath.build route.path route.within owner
  let cache := ParentCache.build prepared source 0
  let leftEntry : FaceModels.Entry ((RegularPrimitiveFragment.domainCache firstLeft.fragment domains)).models
    firstLeft.last owner :=
    ⟨firstLeft.assigned.entry.sheet, SheetEntry.finish_query_reached firstLeft.assigned
      firstLeft.occurrence.finishInside⟩
  let rightEntry : FaceModels.Entry ((RegularPrimitiveFragment.domainCache firstRight.fragment domains)).models
    firstLeft.last owner :=
    ⟨firstRight.assigned.entry.sheet, by
      have reached := SheetEntry.first_query_reached firstRight.assigned
      obtain ⟨roots⟩ := firstRoots
      have equivalent : Gaussian.Equivalence.NamedEquivalent
          (OwnerTraceReadings.ownerName (PreparedEdge.ownerAtPoint firstRight.parent.edge firstRight.interval.lower
            firstRight.assigned.fractionInside
            firstRight.first firstRight.fragment.located.first_eq.symm)) (OwnerTraceReadings.ownerName owner) := by
        rw [PreparedEdge.ownerAtPoint_name,
          Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.ChartContacts.LiftedFragment.finishOwner_name]
        exact roots.symm
      exact reached.append (Reached.ofEquivalentAt firstCoordinate.symm equivalent)⟩
  let left := EnteredPath.ofEntry leftEntry firstLeft.assigned.domain prepared
    (Polynomial.Geometry.ClearPath.InBox.ofWithin route.path route.within leftStart) source 0 cache
  let right := EnteredPath.ofEntry rightEntry firstRight.assigned.domain prepared
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.ChartContacts.Route.build_inBox leftFace.clearance _ _ leftStart
      leftFinish rightStart rightFinish) source 0 cache
  exact ⟨owner, rfl, route, prepared, cache, left, right, rfl, rfl, rfl, rfl, HEq.rfl, HEq.rfl,
    sameLeft, sameRight, firstCoordinate, lastCoordinate⟩

end ChartContact
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.ChartContacts.LiftedFragment
