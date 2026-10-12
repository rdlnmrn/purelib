module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.RootContinuation.PreparedNewtonBandBoundary
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Dependent
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Polynomial.Elimination.Axis.Separated
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.RootIsolation.State.Raw
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
public import Purelib.Riemann.RootContinuation.PreparedNewtonBandFamilies
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Polynomial.Geometry.Grid.FramedClearGrid
import Purelib.RootIsolation.SquareRoot.Grid.Branch.Neighborhoods
import Purelib.RootIsolation.SquareRoot.Grid.Branch.Location
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Curves.Hyperelliptic.Branches.BranchCellWinding
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Band.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.RootIsolation.Newton.Band.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.RootIsolation.State.WindingOne.Raw
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank

public section

/-!
# Actual shrinking holes inside retained common Newton bands

The same extracted bands supply the clear grid lines, the located holes and
the differential requests. Profiles and elimination data are cached before
requests; each request retains the samples, axes, locations and classified
faces. No proof identifies a thin grid cell with its enclosing Newton band.
-/

open Purelib.Riemann.RootContinuation.NewtonBandBounds (Profile Sample)
open Purelib.Data.Rat.Fraction renaming Rational -> Coordinate
open Purelib.Riemann.RootContinuation.PreparedNewtonBandFamilies (DifferentialFamily)
namespace Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.NewtonBandBounds

open Purelib.RootIsolation.Newton.Band

open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.RootIsolation in
/-- Retain the original extracted band as a winding-one branch state with its exact boundary clearances. -/
@[expose] def Sample.branchState {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {ambient : Box} {squarefree :
  Squarefree.Basic.SquarefreeCertificate p}
    {current : State.Raw.RawWindingState p ambient} {profile : Profile squarefree current.box} {epsilon :
      Fraction.Rational}
    (sample : Sample profile epsilon) : State.WindingOne.Basic.WindingOneState p ambient where
  box := sample.output.box
  refinesAmbient := sample.output.refinesAmbient
  proper := sample.output.proper
  clearance := sample.output.clearance
  rawWindingFour := sample.output.rawWindingFour
  ambientLeftClearance := sample.output.ambientLeftClearance
  ambientRightClearance := sample.output.ambientRightClearance
  ambientBottomClearance := sample.output.ambientBottomClearance
  ambientTopClearance := sample.output.ambientTopClearance

open Purelib.Geometry.Rational in
open Purelib.Polynomial.Dense.Gaussian in
set_option genInjectivity false in
/-- An original Newton profile together with its exact indexed family of differential bounds.

The retained squarefree polynomial, current box and family size remain indices of both stored components. -/
structure BranchProfile {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (squarefree :
  Squarefree.Basic.SquarefreeCertificate p)
  (box : Box) (count : Nat) where
  /-- The original Newton-band profile on the retained branch-state box. -/ profile : Profile squarefree box
  /-- The exact retained differential family for the original Newton profile. -/ differentials : DifferentialFamily
    profile count

constructive_injectivity BranchProfile

open Purelib.Geometry.Rational in
open Purelib.Polynomial.Dense.Gaussian in
/-- Build the original Newton profile and its exact finite differential family on the retained branch-state box. -/
@[expose] def BranchProfile.build {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  (squarefree :
  Squarefree.Basic.SquarefreeCertificate p) (box : Box) (count : Nat) :
    BranchProfile squarefree box count :=
  let profile := Profile.build squarefree box
  ⟨profile, DifferentialFamily.build profile count⟩

end Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.NewtonBandBounds

namespace Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank

open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.NewtonBandBounds (BranchProfile)

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.RootContinuation.NewtonBandBounds
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Curves.Hyperelliptic.Branches.BranchCellWinding (state state_strict_cell)
open Purelib.Riemann.Meshes.ShrinkingPuncturedGrid.BranchCellBank (ShrinkingPreparation Shrunk)
open Purelib.Riemann.Meshes.ShrinkingPuncturedGrid.BranchCellBank (prepareShrinking)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandFamilies (DifferentialFamily PreparedBandFamily)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandBoundary (RequestedPreparedBoundary)
open Purelib.RootIsolation.SquareRoot.Grid.Branch.Neighborhoods (BranchNeighborhoods)
open Purelib.RootIsolation.SquareRoot.Grid.Branch.Neighborhoods.BranchNeighborhoods (Locations)
open _root_.Purelib.Polynomial.Geometry.Grid.FramedClearGrid (FramedExtension)
open Purelib.Polynomial.Geometry.Grid.ClearGrid (VerticalLine HorizontalLine)
open _root_.Purelib.Polynomial.Geometry.Grid.FromStates (ofStates_x_bounds ofStates_y_bounds)
open Purelib.RootIsolation.SquareRoot.Grid.Branch.Location (BranchBudget)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces BranchHole)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}

open Purelib in
open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.Data in
open Purelib.Polynomial in
set_option genInjectivity false in
/-- Cached shrinking, elimination and branch-profile data for the original branch-cell bank.

Every profile retains its original branch index and state box, while the elimination certificate keeps its exact degree
bound. -/
structure NewtonPreparation (original : Curves.Hyperelliptic.Branches.BranchCellBank curve branches higher) where
  /-- The original cached ambient boundary clearance for grid shrinking. -/ shrinking : ShrinkingPreparation original
  /-- The retained degree bound of the original axis-elimination certificate. -/ degreeBound : Nat
  /-- The original executable axis-elimination certificate with its exact degree bound. -/ elimination :
    Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate curve.polynomial degreeBound
  /-- The retained original branch profiles indexed by their exact branch-state boxes. -/ profiles :
    Vector.DependentVector (fun index : BranchIsolation.Data.Index branches =>
    BranchProfile
      curve.squarefree (BranchCellWinding.state original index).box genus)

constructive_injectivity NewtonPreparation

namespace NewtonPreparation

variable {original : BranchCellBank curve branches higher}

open Purelib in
open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.Data in
open Purelib.Polynomial in
open Purelib.Riemann.Meshes in
/-- Prepare the original branch bank's shrinking clearance, elimination certificate and indexed Newton differential
profiles.

The original branch states determine every profile box, and the exact axis-elimination witness is cached once for
subsequent band requests. -/
@[expose] def build (original : Curves.Hyperelliptic.Branches.BranchCellBank curve branches higher) : NewtonPreparation
  original :=
  { shrinking := ShrinkingPuncturedGrid.BranchCellBank.prepareShrinking original
    degreeBound := Elimination.Axis.Separated.separatedEliminationDegree curve.polynomial
    elimination := Elimination.Axis.Separated.separatedAxisEliminationCertificate curve.polynomial curve.nonzero
      (BranchIsolation.degreePositive curve)
    profiles := Vector.DependentVector.ofFn fun index =>
    BranchProfile.build
        curve.squarefree (BranchCellWinding.state original index).box genus }

open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.Data in
open Purelib.Riemann.RootContinuation in
open Purelib.RootIsolation in
set_option genInjectivity false in
/-- An original indexed family of prepared Newton bands with exact winding-state neighborhood readbacks.

The retained entries share the requested target and radius; the neighborhood state equation identifies each original
extracted sample exactly. -/
structure Bands (preparation : NewtonPreparation original) (target radius : Coordinate) where
  /-- The original prepared band families indexed by the retained branches. -/ entries : Vector.DependentVector (fun
    index : BranchIsolation.Data.Index branches =>
    PreparedBandFamily (current := (BranchCellWinding.state original index).raw) (preparation.profiles.get
      index).differentials target radius)
  /-- The retained original winding-state neighborhoods of the same band samples. -/ neighborhoods :
    SquareRoot.Grid.Branch.Neighborhoods.BranchNeighborhoods (fun index => BranchCellWinding.state original index)
    radius
  /-- Each neighborhood state equals the exact original extracted band state. -/ states_eq : ∀ index,
    neighborhoods.states index =
    NewtonPuncturedGrid.NewtonBandBounds.Sample.branchState (entries.get index).selection.sample

constructive_injectivity Bands

namespace Bands

variable {preparation : NewtonPreparation original} {target radius : Coordinate}

open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.Data in
open Purelib.Geometry.Rational in
open Purelib.Riemann.RootContinuation in
/-- Package the original prepared band entries as retained branch neighborhoods without recomputing their samples.

The state vector reads those exact entries, preserving their refinements, radius bounds and indexed state equations. -/
@[expose] def ofEntries (entries : Vector.DependentVector (fun index : BranchIsolation.Data.Index branches =>
    PreparedBandFamily (current := (BranchCellWinding.state original index).raw) (preparation.profiles.get
      index).differentials target radius))
    (radiusPositive : 0 < radius) : Bands preparation target radius :=
  let states := Vector.Basic.vectorOfFn fun index =>
    NewtonPuncturedGrid.NewtonBandBounds.Sample.branchState
      (entries.get index).selection.sample
  { entries := entries
    neighborhoods :=
      { positive := radiusPositive
        states := states
        refines := fun index => by rw [Vector.Basic.vectorOfFn_apply]; exact
            (Geometry.Rational.Box.Refinement.StrictInterior.refines
          (entries.get index).selection.sample.output.strictCurrent)
        diagonal := fun index => by rw [Vector.Basic.vectorOfFn_apply]; exact (entries.get index).diagonal
        listed := List.ofFn states
        listed_eq := rfl }
    states_eq := Vector.Basic.vectorOfFn_apply _ }

open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.Data in
/-- Acquire the original prepared band family at each retained branch index.

The stored branch profiles and elimination certificate are reused for the same positive target and radius, then packaged
with their exact neighborhood readbacks. -/
@[expose] def build (preparation : NewtonPreparation original) {target radius : Coordinate}
    (positive : 0 < target) (radiusPositive : 0 < radius) : Bands preparation target radius :=
  ofEntries (Vector.DependentVector.ofFn fun index => PreparedBandFamily.build (current := (BranchCellWinding.state
    original index).raw)
    (preparation.profiles.get index).differentials higher preparation.elimination positive radiusPositive)
      radiusPositive

open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.Geometry.Rational in
/-- The exact original extracted box at the retained branch index. -/
@[expose] def box (bands : Bands preparation target radius) (index : BranchIsolation.Data.Index branches) :
  Box :=
  (bands.entries.get index).selection.sample.output.box

open Purelib.Curves.Hyperelliptic.Branches in
/-- The retained neighborhood state has exactly the corresponding original band box. -/
theorem state_box (bands : Bands preparation target radius) (index : BranchIsolation.Data.Index branches) :
    (bands.neighborhoods.states index).box = bands.box index := congrArg (·.box) (bands.states_eq index)

open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Geometry.Rational
/-- Every original extracted band lies strictly inside its corresponding original branch cell. -/
theorem strict_original (bands : Bands preparation target radius) (index : BranchIsolation.Data.Index branches) :
    (bands.box index).StrictInterior (original.cell index).box :=
  Geometry.Rational.Box.Refinement.StrictInterior.of_refines
    (BranchCellWinding.state_strict_cell original index)
    (Geometry.Rational.Box.Refinement.StrictInterior.refines (bands.entries.get
        index).selection.sample.output.strictCurrent)

/-- Original extracted bands at distinct retained branch indices have separated boxes. -/
theorem separated (bands : Bands preparation target radius) (first second : BranchIsolation.Data.Index branches)
    (different : first ≠ second) : (bands.box first).Separated (bands.box second) :=
  (original.cells_separated first second different).of_refines (Geometry.Rational.Box.Refinement.StrictInterior.refines
    (bands.strict_original first)) (Geometry.Rational.Box.Refinement.StrictInterior.refines (bands.strict_original
        second))

end Bands

end NewtonPreparation

open Purelib in
open Purelib.Polynomial in
open Purelib.RootIsolation in
set_option genInjectivity false in
/-- A retained punctured grid built around original Newton bands and their exact located cells.

The original framed extension, neighborhood locations and shrunk bank remain stored with exact grid and cell equations,
alongside the same punctured-face partition. -/
structure NewtonGrid {original : Curves.Hyperelliptic.Branches.BranchCellBank curve branches higher} (preparation :
  NewtonPreparation original)
    (target radius : Coordinate) where
  /-- The retained original indexed Newton-band families and neighborhood readbacks. -/ bands : preparation.Bands target
    radius
  /-- The original framed grid extension containing those exact listed neighborhoods. -/ extension :
    Polynomial.Geometry.Grid.FramedClearGrid.FramedExtension original.grid bands.neighborhoods.listed
  /-- The retained original neighborhood locations in the exact framed extension. -/ locations :
    SquareRoot.Grid.Branch.Neighborhoods.BranchNeighborhoods.Locations bands.neighborhoods extension
  /-- The retained original shrunk branch-cell bank at the requested radius. -/ shrunk : Shrunk original radius
  /-- The shrunk bank grid equals the exact original framed extension grid. -/ grid_eq : shrunk.prepared.grid =
    extension.grid
  /-- Each stored shrunk branch cell equals its exact original located cell. -/ cell_eq : ∀ index,
    shrunk.prepared.toBranchCellBank.cell index = (locations.entries.get index).cell
  /-- The retained punctured-face partition of the exact stored shrunk bank. -/ faces : PuncturedFaces
    shrunk.prepared.toBranchCellBank

constructive_injectivity NewtonGrid

namespace NewtonGrid

variable {original : BranchCellBank curve branches higher} {preparation :
  NewtonPreparation original} {target radius : Coordinate}

open Purelib.Polynomial in
open Purelib.RootIsolation in
/-- Build the original Newton grid from retained bands, framed extension and exact neighborhood locations.

The shrunk bank consumes those same locations, and its exact grid/cell equations connect the retained punctured faces to
the original band data. -/
@[expose] def ofLocations (bands : preparation.Bands target radius)
    (extension : Polynomial.Geometry.Grid.FramedClearGrid.FramedExtension original.grid bands.neighborhoods.listed)
      (locations
      : SquareRoot.Grid.Branch.Neighborhoods.BranchNeighborhoods.Locations bands.neighborhoods extension) :
    NewtonGrid preparation target radius :=
  let shrunk := Shrunk.ofLocations bands.neighborhoods extension locations
  { bands := bands
    extension := extension
    locations := locations
    shrunk := shrunk
    grid_eq := rfl
    cell_eq := Shrunk.ofLocations_cell bands.neighborhoods extension locations
    faces := PuncturedFaces.build shrunk.prepared.toBranchCellBank }

open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.Polynomial in
open Purelib.RootIsolation in
/-- Construct the original Newton grid from its retained preparation and positive target/radius request.

The exact band neighborhoods extend the original grid; retained branch tracks locate those neighborhoods, and the same
locations form the shrunk bank and punctured faces. -/
@[expose] def build (preparation : NewtonPreparation original) {target radius : Coordinate}
    (positive : 0 < target) (radiusPositive : 0 < radius) : NewtonGrid preparation target radius :=
  let bands := NewtonPreparation.Bands.build preparation positive radiusPositive
  let extension := Polynomial.Geometry.Grid.FramedClearGrid.FramedExtension.build original.grid
    preparation.shrinking.clearance bands.neighborhoods.listed
  let locations := SquareRoot.Grid.Branch.Neighborhoods.BranchNeighborhoods.Locations.build bands.neighborhoods
    extension (SquareRoot.Grid.Branch.Location.BranchBudget.ofGrid extension.grid)
    (BranchIsolation.degreePositive curve) (fun index => branches.track higher index)
  ofLocations bands extension locations

/-- Read the original framed punctured grid from the retained Newton grid and its exact face partition. -/
@[expose] def punctured (grid : NewtonGrid preparation target radius) : FramedPuncturedGrid curve branches higher :=
  ⟨grid.shrunk.prepared, grid.faces⟩

open Purelib.Curves.Hyperelliptic.Branches in
/-- The retained original branch cell refines its exact corresponding Newton-band box. -/
theorem cell_refines_band (grid : NewtonGrid preparation target radius) (index : BranchIsolation.Data.Index branches) :
    (grid.shrunk.prepared.toBranchCellBank.cell index).box.Refines (grid.bands.box index) := by
  rw [grid.cell_eq, ← grid.bands.state_box]
  exact (grid.locations.entries.get index).cell_refines

/-- The retained original hole refines its exact indexed Newton band. -/
theorem hole_refines_band (grid : NewtonGrid preparation target radius) (hole : BranchHole
  grid.punctured.bank.toBranchCellBank) :
    hole.cell.box.Refines (grid.bands.box hole.index) := by
  rw [hole.cell_eq]
  exact grid.cell_refines_band hole.index

open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.Geometry.Rational in
/-- An original retained hole is separated from every Newton band with a different branch index. -/
theorem other_hole_separated (grid : NewtonGrid preparation target radius) (hole : BranchHole
  grid.punctured.bank.toBranchCellBank)
    (index : BranchIsolation.Data.Index branches) (different : hole.index ≠ index) : hole.cell.box.Separated
      (grid.bands.box index) := by
  rw [hole.cell_eq]
  exact (original.cells_separated hole.index index different).of_refines
    (Geometry.Rational.Box.Refinement.StrictInterior.refines (grid.shrunk.cell_strict hole.index))
      (Geometry.Rational.Box.Refinement.StrictInterior.refines (grid.bands.strict_original index))

open Purelib.Curves.Hyperelliptic.Branches in
/-- Refinement of a retained Newton band identifies the original hole's exact branch index. -/
theorem hole_index (grid : NewtonGrid preparation target radius) (hole : BranchHole
  grid.punctured.bank.toBranchCellBank)
    (index : BranchIsolation.Data.Index branches) (inside : hole.cell.box.Refines (grid.bands.box index)) : hole.index =
      index := by
  by_cases same : hole.index = index
  · exact same
  · exact ((grid.other_hole_separated hole index same).points_ne hole.cell.box.contains_anchor
      (inside.contains hole.cell.box.contains_anchor) rfl).elim

section
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Polynomial
/-- Both original Newton-band real boundary coordinates occur in the retained grid's vertical lines. -/
theorem band_x_lines (grid : NewtonGrid preparation target radius) (index : BranchIsolation.Data.Index branches) :
    (grid.bands.box index).xLower ∈ grid.punctured.bank.grid.vertical.map
      Geometry.Grid.ClearGrid.VerticalLine.coordinate ∧
      (grid.bands.box index).xUpper ∈ grid.punctured.bank.grid.vertical.map VerticalLine.coordinate := by
  change _ ∈ grid.shrunk.prepared.grid.vertical.map Geometry.Grid.ClearGrid.VerticalLine.coordinate ∧ _ ∈
    grid.shrunk.prepared.grid.vertical.map Geometry.Grid.ClearGrid.VerticalLine.coordinate
  rw [grid.grid_eq, ← grid.bands.state_box]
  have members := Polynomial.Geometry.Grid.FromStates.ofStates_x_bounds grid.bands.neighborhoods.listed
    (grid.bands.neighborhoods.state_mem index)
  exact ⟨grid.extension.statesIncluded.vertical _ members.1, grid.extension.statesIncluded.vertical _ members.2⟩

/-- Both original Newton-band imaginary boundary coordinates occur in the retained grid's horizontal lines. -/
theorem band_y_lines (grid : NewtonGrid preparation target radius) (index : BranchIsolation.Data.Index branches) :
    (grid.bands.box index).yLower ∈ grid.punctured.bank.grid.horizontal.map
      Geometry.Grid.ClearGrid.HorizontalLine.coordinate ∧
      (grid.bands.box index).yUpper ∈ grid.punctured.bank.grid.horizontal.map HorizontalLine.coordinate := by
  change _ ∈ grid.shrunk.prepared.grid.horizontal.map Geometry.Grid.ClearGrid.HorizontalLine.coordinate ∧ _ ∈
    grid.shrunk.prepared.grid.horizontal.map Geometry.Grid.ClearGrid.HorizontalLine.coordinate
  rw [grid.grid_eq, ← grid.bands.state_box]
  have members := Polynomial.Geometry.Grid.FromStates.ofStates_y_bounds grid.bands.neighborhoods.listed
    (grid.bands.neighborhoods.state_mem index)
  exact ⟨grid.extension.statesIncluded.horizontal _ members.1, grid.extension.statesIncluded.horizontal _ members.2⟩

end

open Purelib.Curves.Hyperelliptic in
open Purelib.Curves.Hyperelliptic.Branches in
/-- Read a prepared boundary for the exact original branch, differential and sheet from the retained band family. -/
  @[expose] def boundary (grid : NewtonGrid preparation target radius) (index : BranchIsolation.Data.Index branches)
    (differential : Fin genus) (sheet : Fin 2) :
    RequestedPreparedBoundary
      (curve := curve)
      (differential := (⟨differential⟩ : Differentials.Basic.Differential genus))
      (current := (BranchCellWinding.state original index).raw)
      (profile := (preparation.profiles.get index).profile)
      (fixed := (preparation.profiles.get index).differentials.profiles.get differential)
      target sheet :=
  (grid.bands.entries.get index).boundary differential sheet

open Purelib.Curves.Hyperelliptic.Branches in
/-- The retained requested boundary uses exactly the original indexed Newton-band box. -/
theorem boundary_box (grid : NewtonGrid preparation target radius) (index : BranchIsolation.Data.Index branches)
    (differential : Fin genus) (sheet : Fin 2) :
    (grid.boundary index differential sheet).request.sample.output.box = grid.bands.box index := rfl

end NewtonGrid

end Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank
