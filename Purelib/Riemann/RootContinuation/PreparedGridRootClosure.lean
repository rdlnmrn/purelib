module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Integration.PreparedOwnerClosedBridges
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Paths.PreparedPathClosure
import Purelib.Riemann.Readings.PreparedBoundaryClosure
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchGrid

import Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
public import Purelib.Curves.Hyperelliptic.Branches.BranchGridPaths
public import Purelib.Riemann.Paths.PreparedPathPrimitiveCover

@[expose] public section

/-!
# Operational root closure on the actual subdivided grid tours

Prepare adjacent grid edges from one retained starting owner.  Winding
preservation supplies the final operational return; a coordinate or sheet
label is never used as a root-return witness.  The same preparation retains
uniform primitive coverage and strict parameter widths, so both primitive
requests and the root-safe scheduler consume its actual cells.

This does not identify the resulting integrals with the older unsplit period
names.  That comparison still needs the local primitive estimates.
-/

namespace Purelib.Riemann.RootContinuation.PreparedGridRootClosure.Grid

open Purelib.Riemann.Paths.PreparedClearPathModels (PreparedPath)
open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open Purelib.Polynomial.Geometry.Grid.Walks (Walk)
open Purelib.Riemann.Paths.PreparedPathWinding.ClearPath (rawWinding)

open Purelib.Riemann in
open Purelib.Approximation in
open Purelib.Data in
open Purelib.Polynomial in
open Purelib.Geometry in
set_option genInjectivity false in
/-- Retain a grid walk and its actual root-closed integration preparation.

The original starting owner, traced subdivision, primitive coverage and two operational root names remain linked by the
supplied return equivalence. -/
structure RootClosedWalk {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Rational.Box}
    (grid : Polynomial.Geometry.Grid.ClearGrid polynomial ambient) (base : Gaussian.Basic.Canonical) (owner : Owner
      (polynomial.eval base)) : Type 2 where
  /-- The actual closed grid walk based at the original starting point. -/ walk : Geometry.Grid.Walks.Walk grid base
    base
  /-- The retained traced preparation beginning at the original owner. -/ traced : TracedPath walk.path owner
  /-- Primitive coverage on the exact traced preparation. -/ cover :
    Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.PreparedPath.PrimitiveCover traced.prepared
  /-- The cached original starting root name. -/ firstRoot : Gaussian.Name.Basic.Named
  /-- The cached actual terminal root name. -/ lastRoot : Gaussian.Name.Basic.Named
  /-- The cached first name is exactly the original owner's operational name. -/ firstRoot_eq : firstRoot = ownerName
    owner
  /-- The cached last name is exactly the traced terminal owner's operational name. -/ lastRoot_eq : lastRoot =
    ownerName traced.finishOwner
  /-- The actual terminal root name is operationally equivalent to the original starting root name. -/ returned :
    Gaussian.Equivalence.NamedEquivalent lastRoot firstRoot

constructive_injectivity RootClosedWalk

namespace RootClosedWalk

variable {polynomial : Purelib.Polynomial.Geometry.ClearPath.GaussianPolynomial} {ambient :
  Purelib.Geometry.Rational.Box} {grid : Polynomial.Geometry.Grid.ClearGrid polynomial
  ambient}

open Purelib.Riemann in
open Purelib.Data in
/-- Every actual prepared edge has a strict parameter width from the retained primitive cover. -/
theorem proper {base : Gaussian.Basic.Canonical} {owner : Owner (polynomial.eval base)}
    (closed : RootClosedWalk grid base owner) : Paths.PreparedClearPathModels.PreparedPath.AllEdgesProper
      closed.traced.prepared :=
  Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.PreparedPath.PrimitiveCover.proper closed.cover

open Purelib.Approximation in
open Purelib.Data in
/-- Read the retained operational return at the original starting and terminal owner names. -/
def rootReturn {base : Gaussian.Basic.Canonical} {owner : Owner (polynomial.eval base)}
    (closed : RootClosedWalk grid base owner) :
    Gaussian.Equivalence.NamedEquivalent (ownerName closed.traced.finishOwner) (ownerName owner) := by
  rw [← closed.firstRoot_eq, ← closed.lastRoot_eq]
  exact closed.returned

open Purelib.Riemann in
open Purelib.Polynomial in
open Purelib.Geometry in
open Purelib.RootIsolation in
/-- Prepare an actual grid walk from the original owner and certify its operational return.

The supplied winding equality with eight times an integer combines with retained primitive coverage and winding
preservation along the actual traced subdivision. -/
def ofEven {referenceAmbient : Rational.Box}
    (reference : State.WindingOne.Basic.WindingOneState polynomial referenceAmbient)
    (walk : Geometry.Grid.Walks.Walk grid reference.box.anchor reference.box.anchor)
    (owner : Owner (polynomial.eval reference.box.anchor)) (turns : Int)
    (even : rawWinding walk.path = 8 * turns) : RootClosedWalk grid reference.box.anchor owner :=
  let prepared := Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath.build walk.path
    walk.withinAmbient owner
  ⟨walk, prepared.traced, prepared.cover,
    ownerName owner, ownerName prepared.traced.finishOwner, rfl, rfl,
    Paths.PreparedPathClosure.TracedPath.rootEquivalent_of_original_even
      reference prepared.traced turns even⟩

section
open Purelib.Riemann
open Purelib.Curves
open Purelib.Polynomial
open Purelib.Geometry
/-- Root-closed walks indexed by the exact starting point and owner of the original tour. -/
abbrev ForTour {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {ambient : Rational.Box} (grid : Polynomial.Geometry.Grid.ClearGrid curve.polynomial ambient)
    (tour : Readings.PreparedBoundaryClosure.ClosedBoundaryDoublePath curve) : Type 2 :=
  RootClosedWalk grid tour.joined.data.leftState.box.anchor tour.joined.data.forwardOwner

/-- Prepare the original tour's split grid walk with its supplied even-winding certificate.

The original tour's forward owner starts the traced path and remains the owner used by the return certificate. -/
def ofTour {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {ambient : Rational.Box} (grid : Polynomial.Geometry.Grid.ClearGrid curve.polynomial ambient)
    (tour : Readings.PreparedBoundaryClosure.ClosedBoundaryDoublePath curve)
    (onGrid : Hyperelliptic.Meshes.PuncturedGrid.BranchGrid.Grid.ContainsTourVertices grid tour) (turns : Int)
    (even : rawWinding (Hyperelliptic.Branches.BranchGridPaths.Grid.splitTour grid tour onGrid).path = 8 * turns) :
      ForTour grid tour :=
  ofEven tour.joined.data.leftState (Hyperelliptic.Branches.BranchGridPaths.Grid.splitTour grid tour onGrid)
    tour.joined.data.forwardOwner turns even

end

open Purelib.Approximation in
open Purelib.Data in
/-- Compare the actual terminal owner with another returned owner through their shared original starting root. -/
def finishEquivalent {base : Gaussian.Basic.Canonical} {owner other : Owner (polynomial.eval base)}
    (closed : RootClosedWalk grid base owner)
    (returned : Gaussian.Equivalence.NamedEquivalent (ownerName other) (ownerName owner)) :
    Gaussian.Equivalence.NamedEquivalent (ownerName closed.traced.finishOwner) (ownerName other) :=
  (rootReturn closed).trans returned.symm

end RootClosedWalk

end Purelib.Riemann.RootContinuation.PreparedGridRootClosure.Grid

namespace Purelib.Riemann.RootContinuation.PreparedGridRootClosure.ClearGrid

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Riemann.Integration.PreparedOwnerClosedBridges (OwnerClosedCyclePair)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchGrid (branchGrid branchGrid_aTour branchGrid_bTour)
open Purelib.Curves.Hyperelliptic.Branches.BranchGridPaths
  (aTourWalkOfData bTourWalkOfData aTourWalkOfData_winding bTourWalkOfData_winding)

open Purelib.Curves
/-- Construct the canonical A-tour root-closed preparation on the retained branch grid.

The original splitter supplies the winding certificate, while the actual traced preparation supplies primitive coverage
and operational return. -/
def aRootClosedWalkOfData {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (branches : Hyperelliptic.Branches.BranchIsolation.Data curve) (higher : 1 < curve.polynomial.natDegree) (index :
      Fin genus) :
    Grid.RootClosedWalk.ForTour
      (Hyperelliptic.Meshes.PuncturedGrid.BranchGrid.branchGrid curve
        (Hyperelliptic.Branches.BranchConfiguration.configurationOfData curve branches).branches higher 0)
      (OwnerClosedCyclePair.ofData curve branches index).aTour :=
  Grid.RootClosedWalk.ofTour _ _ (Hyperelliptic.Meshes.PuncturedGrid.BranchGrid.branchGrid_aTour curve branches higher
    index) 1
    (Hyperelliptic.Branches.BranchGridPaths.aTourWalkOfData_winding curve branches higher index)

/-- Construct the canonical B-tour root-closed preparation on the retained branch grid.

The original splitter supplies the winding certificate, while the actual traced preparation supplies primitive coverage
and operational return. -/
def bRootClosedWalkOfData {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (branches : Hyperelliptic.Branches.BranchIsolation.Data curve) (higher : 1 < curve.polynomial.natDegree) (index :
      Fin genus) :
    Grid.RootClosedWalk.ForTour
      (Hyperelliptic.Meshes.PuncturedGrid.BranchGrid.branchGrid curve
        (Hyperelliptic.Branches.BranchConfiguration.configurationOfData curve branches).branches higher 0)
      (OwnerClosedCyclePair.ofData curve branches index).bTour :=
  Grid.RootClosedWalk.ofTour _ _ (Hyperelliptic.Meshes.PuncturedGrid.BranchGrid.branchGrid_bTour curve branches higher
    index) 1
    (Hyperelliptic.Branches.BranchGridPaths.bTourWalkOfData_winding curve branches higher index)

/-- The retained A preparation has exactly the original canonical A-tour grid walk. -/
theorem aRootClosedWalkOfData_walk {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (branches : Hyperelliptic.Branches.BranchIsolation.Data curve) (higher : 1 < curve.polynomial.natDegree) (index :
      Fin genus) :
    (aRootClosedWalkOfData curve branches higher index).walk = Hyperelliptic.Branches.BranchGridPaths.aTourWalkOfData
      curve branches higher index := rfl

/-- The retained B preparation has exactly the original canonical B-tour grid walk. -/
theorem bRootClosedWalkOfData_walk {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (branches : Hyperelliptic.Branches.BranchIsolation.Data curve) (higher : 1 < curve.polynomial.natDegree) (index :
      Fin genus) :
    (bRootClosedWalkOfData curve branches higher index).walk = Hyperelliptic.Branches.BranchGridPaths.bTourWalkOfData
      curve branches higher index := rfl

end Purelib.Riemann.RootContinuation.PreparedGridRootClosure.ClearGrid
