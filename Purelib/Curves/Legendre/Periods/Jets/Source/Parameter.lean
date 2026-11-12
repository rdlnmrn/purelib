module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Observations
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared
public import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range

/-! # Uniform parameter continuation of actual retained source queries

The fixed physical patch supplies one positive parameter range. An actual
six-observation answer is retained once, and its identical original point
owner is advanced at that range. Original prepared endpoint samples use
their exact acquisition readbacks; coordinate labels do not identify owners.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedCell LiftedPath)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Integration.Path.Primitive.PrimitiveEdge

variable {parameter : Canonical}

namespace Cell.Query

variable {start finish : LiftedPoint 2} {lifted : LiftedCell start finish}
    {cell : Cell (parameter := parameter) lifted}

/-- Retain one actual six-channel answer and continue its identical acquired source owner at the common patch range.

The original query, requests, model and selected readings remain in the
first component. The second component advances precisely that retained
point; the original answer is neither replaced nor requested again.
-/
def advance (query : Query cell) (frame : Paths.Frame parameter)
    (range : Variation.Point.Range cell.patch)
    (input : Rational) (lower : 0 ≤ input) (upper : input ≤ 1)
    (increment : Canonical) (admitted : Norm.Basic.normSq increment ≤ range.bound) :
    (observed : CellModels.Observations frame lifted cell.models query.requests input) ×
      Variation.Point.Step observed.retained.sample increment :=
  let observed := query.observe frame input lower upper
  let inside := cell.models.coordinate.point_inside cell.startInside cell.finishInside lower upper
  let next := range.advance observed.retained.sample inside
    (query.observe_sample frame input lower upper) increment admitted
  ⟨observed, next⟩

/-- Parameter continuation retains the complete actual six-channel observation bundle without alteration. -/
theorem advance_observation (query : Query cell) (frame : Paths.Frame parameter)
    (range : Variation.Point.Range cell.patch)
    (input : Rational) (lower : 0 ≤ input) (upper : input ≤ 1)
    (increment : Canonical) (admitted : Norm.Basic.normSq increment ≤ range.bound) :
    (query.advance frame range input lower upper increment admitted).1 = query.observe frame input lower upper := by
  rfl

end Cell.Query

namespace Cell.PreparedParent

variable {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count floor : Nat}
    {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}

/-- Continue the already retained original starting sample of the actual prepared-parent factory.

The exact factory equality certifies the existing sample's complete owner
and cache, rather than inferring them from a coordinate or sheet label.
The fixed patch's computed range pays the original point increment request.
-/
def firstStep (prepared : PreparedParent patch count floor covered targets)
    (fromFactory : prepared = prepareParent patch count floor covered targets)
    (range : Variation.Point.Range (patch.neighborhood count))
    (increment : Canonical) (admitted : Norm.Basic.normSq increment ≤ range.bound) :
    Variation.Point.Step prepared.firstSample increment :=
  let same : prepared.firstSample = ContinuedNeighborhood.Point.acquire (patch.neighborhood count)
      (startPoint parent).coordinate (start_inside patch count) := by
    rewrite [fromFactory]
    exact prepareParent_firstSample patch count floor covered targets
  range.advance prepared.firstSample (start_inside patch count) same increment admitted

/-- Continue the retained original finishing sample using the same fixed patch range and acquisition identity. -/
def lastStep (prepared : PreparedParent patch count floor covered targets)
    (fromFactory : prepared = prepareParent patch count floor covered targets)
    (range : Variation.Point.Range (patch.neighborhood count))
    (increment : Canonical) (admitted : Norm.Basic.normSq increment ≤ range.bound) :
    Variation.Point.Step prepared.lastSample increment :=
  let same : prepared.lastSample = ContinuedNeighborhood.Point.acquire (patch.neighborhood count)
      (finishPoint parent).coordinate (finish_inside patch count covered) := by
    rewrite [fromFactory]
    exact prepareParent_lastSample patch count floor covered targets
  range.advance prepared.lastSample (finish_inside patch count covered) same increment admitted

end Cell.PreparedParent

end Purelib.Curves.Legendre.Periods.Jets.Source

end
