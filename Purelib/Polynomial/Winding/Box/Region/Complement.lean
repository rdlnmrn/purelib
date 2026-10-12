module

import Purelib.Data.List.Map
import Purelib.Data.List.Pairwise
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Grid.Central.Cell
import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Winding.Box.Basic
public import Purelib.Polynomial.Winding.Box.Grid.Central.Basic
public import Purelib.Polynomial.Winding.Box.Region.Sum
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Polynomial.Clearance.Box.Grid.Central.Separation
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Tactic.Ring

open Purelib.Geometry.Rational
open Purelib.Polynomial

/-!
# Reading retained complement cells as clear regions

The original eight-cell grid determines the same ordered region list.
Finite membership and pairwise certificates retain each source cell.
-/

namespace Purelib.Polynomial.Winding.Box.Region.Complement

/-- View a clear complement cell inside a larger ambient box.

Compose its existing outer refinement with the supplied ambient refinement, retaining the exact cell box, properness and
clearance certificate. -/
@[expose] public def cellToRegion
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient outer center : Box}
    (cell : Clearance.Box.Grid.Central.Cell.ClearCell p outer center) (outerRefines : outer.Refines ambient) :
    Clearance.Box.Region.ClearRegion p ambient where
  box := cell.box
  refinesAmbient := cell.refines.trans outerRefines
  proper := cell.proper
  clearance := cell.clearance

/-- Read the eight clear complement cells as regions of the supplied ambient box.

The original grid order and individual cell certificates are preserved. -/
@[expose] public def complementRegions
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient outer center : Box}
    (grid : Grid.Central.Basic.Arrangement p outer center) (outerRefines : outer.Refines ambient) :
    List (Clearance.Box.Region.ClearRegion p ambient) :=
  grid.complements.map fun cell => Winding.Box.Region.Complement.cellToRegion cell outerRefines

/-- The retained complement regions have pairwise separated interiors.

Each original grid cell supplies its own box and separation certificate.
Mapping those cells to regions changes neither box nor the ordered relation. -/
public theorem complementRegions_pairwise
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient outer center : Box}
    (grid : Grid.Central.Basic.Arrangement p outer center) (outerRefines : outer.Refines ambient) :
    (Winding.Box.Region.Complement.complementRegions grid outerRefines).Pairwise
      Clearance.Box.Region.Basic.regionInteriorSeparated := open Purelib in by
  change (grid.complements.map fun cell =>
    Winding.Box.Region.Complement.cellToRegion cell outerRefines).Pairwise
      Clearance.Box.Region.Basic.regionInteriorSeparated
  exact Data.List.Pairwise.pairwise_map.mpr grid.complements_pairwise

/-- Every retained complement region refines the original outer box.

Finite membership provides the actual source cell in the displayed grid.
Its existing outer-refinement certificate concerns that same region box. -/
public theorem complementRegions_refine_outer
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient outer center : Box}
    (grid : Grid.Central.Basic.Arrangement p outer center) (outerRefines : outer.Refines ambient)
    {region : Clearance.Box.Region.ClearRegion p ambient}
    (member : region ∈ Winding.Box.Region.Complement.complementRegions grid outerRefines) :
    region.box.Refines outer := open Purelib in by
  change region ∈ grid.complements.map (fun cell =>
    Winding.Box.Region.Complement.cellToRegion cell outerRefines) at member
  rcases Data.List.Map.mem_map.mp member with ⟨cell, _cellMember, rfl⟩
  exact cell.refines

/-- A strict inner box of a complement region is separated from the center.

Membership retains its original source cell. That cell's coordinate contact
and the supplied strict interior witness give the same positive separation. -/
public theorem center_separated_from_complement_strictInterior
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient outer center : Box}
    (grid : Grid.Central.Basic.Arrangement p outer center) (outerRefines : outer.Refines ambient)
    {region : Clearance.Box.Region.ClearRegion p ambient}
    (member : region ∈ Winding.Box.Region.Complement.complementRegions grid outerRefines)
    {small : Box} (strict : small.StrictInterior region.box) :
    center.Separated small := open Purelib in by
  change region ∈ grid.complements.map (fun cell =>
    Winding.Box.Region.Complement.cellToRegion cell outerRefines) at member
  rcases Data.List.Map.mem_map.mp member with ⟨cell, _cellMember, rfl⟩
  exact Clearance.Box.Grid.Central.Cell.ClearCell.center_separated_from_strictInterior cell strict

/-- The total complement raw winding equals the outer winding minus the central winding. -/
public theorem totalRaw_complementRegions
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient outer center : Box}
    (grid : Grid.Central.Basic.Arrangement p outer center) (outerRefines : outer.Refines ambient) :
    Winding.Box.Region.Sum.totalRaw (Winding.Box.Region.Complement.complementRegions grid outerRefines) =
      Winding.Box.Basic.quadrupledBoxWinding p outer - Winding.Box.Basic.quadrupledBoxWinding p center := by
  have additive := grid.additive
  simp only [Winding.Box.Region.Complement.complementRegions, Grid.Central.Basic.Arrangement.complements, List.map,
    Winding.Box.Region.Complement.cellToRegion,
    Winding.Box.Region.Sum.totalRaw, List.sum_cons, List.sum_nil] at *
  rw [additive]
  ring1

end Purelib.Polynomial.Winding.Box.Region.Complement
