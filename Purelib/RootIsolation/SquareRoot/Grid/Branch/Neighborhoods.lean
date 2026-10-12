module
import Purelib.Data.List.OfFn.Basic
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.RootIsolation.Track.Basic
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Polynomial.Geometry.Grid.ClearGrid
public import Purelib.Polynomial.Geometry.Grid.FramedClearGrid
public import Purelib.RootIsolation.SquareRoot.Grid.Branch.Location
public import Purelib.Data.Vector.Dependent
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.State.WindingOne.Basic

/-!
# Requested small branch neighborhoods on an extended grid

Refine the retained branch states before adding their sides to the grid.
The subsequent location step then selects genuinely small cells, rather than
only shrinking a root witness inside an unchanged hole. All arrays and the
shared numeric location budget are retained as executable data.
-/

public section

namespace Purelib.RootIsolation.SquareRoot.Grid.Branch.Neighborhoods

open Purelib.Data.Rat
open Purelib
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.RootIsolation
open Purelib.Data.List

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box} {count : Nat}

set_option genInjectivity false in
/-- A finite family of refined branch states meeting one positive radius request.

Each indexed state refines its original branch box; the retained list is exactly the enumeration of those same states.
-/
structure BranchNeighborhoods (original : Fin count → Geometry.Grid.FromStates.BranchState polynomial ambient) (radius :
  Fraction.Rational) where
  /-- The common branch-neighborhood radius is strictly positive. -/ positive : 0 < radius
  /-- The actual vector of retained refined branch states. -/ states : Data.Vector
    (Geometry.Grid.FromStates.BranchState polynomial ambient) count
  /-- Each retained state refines its own original indexed branch box. -/ refines : ∀ index, (states index).box.Refines
    (original index).box
  /-- Each retained state meets the common squared-diagonal request. -/ diagonal : ∀ index, (states
    index).box.diagonalSq ≤ radius ^ 2
  /-- The retained finite list of those exact refined states. -/ listed : List (Geometry.Grid.FromStates.BranchState
    polynomial ambient)
  /-- The list is exactly the enumeration of the original retained state vector. -/ listed_eq : listed = List.ofFn
    states

constructive_injectivity BranchNeighborhoods

namespace BranchNeighborhoods

variable {original : Fin count → Geometry.Grid.FromStates.BranchState polynomial ambient} {radius : Fraction.Rational}

/-- Refine every original branch state through its retained track at the common positive radius.

Cache both the indexed refined states and their exact finite list enumeration. -/
@[expose] def build (original : Fin count → Geometry.Grid.FromStates.BranchState polynomial ambient)
    (tracks : Fin count → Track.Basic.WindingOneTrack polynomial ambient) (radius : Fraction.Rational) (positive : 0 <
      radius) :
    BranchNeighborhoods original radius :=
  let states := Data.Vector.Basic.vectorOfFn fun index => (tracks index).refine (original index) radius positive
  { positive := positive
    states := states
    refines := fun index => by
      rw [Data.Vector.Basic.vectorOfFn_apply]; exact (tracks index).nested (original index) radius positive
    diagonal := fun index => by
      rw [Data.Vector.Basic.vectorOfFn_apply]; exact (tracks index).accurate (original index) radius positive
    listed := List.ofFn states
    listed_eq := rfl }

/-- Every indexed refined branch state occurs in the retained enumeration.

The exact cached list equation identifies the materialized state family; the
original bounded index supplies its explicit enumeration witness. -/
theorem state_mem (sample : BranchNeighborhoods original radius) (index : Fin count) :
    sample.states index ∈ sample.listed := by
  rw [sample.listed_eq]
  exact OfFn.Basic.mem_ofFn.mpr ⟨index, rfl⟩

set_option genInjectivity false in
/-- Retained locations identify each branch state in the exact framed grid extension.

The dependent entries share the supplied extension and common branch-location
budget, preserving the original refined state at every bounded index. -/
structure Locations (sample : BranchNeighborhoods original radius) {grid : Polynomial.Geometry.Grid.ClearGrid polynomial
  ambient}
    (extension : Polynomial.Geometry.Grid.FramedClearGrid.FramedExtension grid sample.listed) where
  /-- The retained branch-location budget for the exact extended grid. -/ budget :
    SquareRoot.Grid.Branch.Location.BranchBudget extension.grid
  /-- The dependent vector of actual grid locations of the retained branch states. -/ entries :
    Data.Vector.DependentVector fun index => SquareRoot.Grid.Branch.Location.BranchLocation extension.grid
    (sample.states index)

constructive_injectivity Locations

namespace Locations

variable {sample : BranchNeighborhoods original radius} {grid : Polynomial.Geometry.Grid.ClearGrid polynomial ambient}
  {extension : Polynomial.Geometry.Grid.FramedClearGrid.FramedExtension grid sample.listed}

/-- Locate one retained branch state in the exact framed grid extension.

The supplied track and grid inclusion bounds retain the original indexed state and budget. -/
@[expose] def acquire (sample : BranchNeighborhoods original radius) (extension :
  Polynomial.Geometry.Grid.FramedClearGrid.FramedExtension grid sample.listed)
    (budget : SquareRoot.Grid.Branch.Location.BranchBudget extension.grid) (positive : 0 < polynomial.natDegree)
    (tracks : Fin count → Track.Basic.WindingOneTrack polynomial ambient) (index : Fin count) :
    SquareRoot.Grid.Branch.Location.BranchLocation extension.grid (sample.states index) :=
  let member := sample.state_mem index
  let x := Polynomial.Geometry.Grid.FromStates.ofStates_x_bounds sample.listed member
  let y := Polynomial.Geometry.Grid.FromStates.ofStates_y_bounds sample.listed member
  SquareRoot.Grid.Branch.Location.BranchLocation.acquire budget positive (tracks index) (sample.states index)
    (extension.statesIncluded.vertical _ x.1) (extension.statesIncluded.vertical _ x.2)
    (extension.statesIncluded.horizontal _ y.1) (extension.statesIncluded.horizontal _ y.2)

/-- Acquire and retain a grid location for each original refined branch state.

The dependent vector is computed from the supplied common budget and original track family. -/
@[expose] def build (sample : BranchNeighborhoods original radius) (extension :
  Polynomial.Geometry.Grid.FramedClearGrid.FramedExtension grid sample.listed)
    (budget : SquareRoot.Grid.Branch.Location.BranchBudget extension.grid) (positive : 0 < polynomial.natDegree)
    (tracks : Fin count → Track.Basic.WindingOneTrack polynomial ambient) : BranchNeighborhoods.Locations sample
      extension :=
  ⟨budget, Data.Vector.DependentVector.ofFn (BranchNeighborhoods.Locations.acquire sample extension budget positive
    tracks)⟩

/-- Each retained located cell refines its original indexed branch box. -/
theorem cell_refines (locations : BranchNeighborhoods.Locations sample extension) (index : Fin count) :
    (locations.entries.get index).cell.box.Refines (original index).box :=
  (locations.entries.get index).cell_refines.trans (sample.refines index)

/-- Each retained located cell meets the original common squared-diagonal request. -/
theorem cell_diagonal (locations : BranchNeighborhoods.Locations sample extension) (index : Fin count) :
    (locations.entries.get index).cell.box.diagonalSq ≤ radius ^ 2 :=
  (Box.diagonalSq_le_of_refines (locations.entries.get index).cell_refines).trans (sample.diagonal
    index)

end Locations
end BranchNeighborhoods
end Purelib.RootIsolation.SquareRoot.Grid.Branch.Neighborhoods

end
