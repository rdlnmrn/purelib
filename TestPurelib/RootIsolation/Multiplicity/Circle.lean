module

public import Purelib.RootIsolation.Multiplicity.Circle.Inventory
import Purelib.RootIsolation.Multiplicity.Circle.CenterProduct.Sample
import Purelib.RootIsolation.Multiplicity.Circle.Comparison
import Purelib.System.IO

/-!
# Complete radial multiplicity inventory regressions

The fixtures construct the original multiplicity side and its materialized
radial locations from whole-circle certificates. The retained theorem checks
also cover arbitrary higher-degree original owner lists without replacing
them with rational centers.
-/

namespace TestPurelib.RootIsolation.Multiplicity.Circle

open Purelib
open Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Polynomial.Clearance.Circle (Certificate)
open RationalFunctions.Curve.Canonical.Circle
open Purelib.RootIsolation
open Purelib.RootIsolation.Multiplicity.Circle (Inventory HigherLocations)
open Purelib.RootIsolation.Multiplicity.Circle
open CenterProduct (Approximation)
open Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side (PositiveSideInput)

/-- The original materialized family returns the complete same original observation at every context occurrence. -/
public theorem stored_family_lookup {source opposite : CoefficientPolynomial}
    (input : PositiveSideInput source opposite) (index : Fin input.contexts.length) :
    input.buildFamily.observationAt index = input.observe (input.contexts.get index) :=
  input.buildFamily_observationAt index

/-- Automatic construction retains the complete multiplicity total for every admissible normalized input. -/
public theorem constructed_total {polynomial : CoefficientPolynomial} (clearance : Certificate polynomial)
    (normalized : polynomial.normalize = polynomial) :
    (Inventory.prepare clearance normalized).insideCount +
      (Inventory.prepare clearance normalized).outsideCount = polynomial.natDegree :=
  (Inventory.prepare clearance normalized).total

/-- Arbitrary original higher owners retain complete actual sufficient-request refinement results. -/
public theorem higher_stored {polynomial : CoefficientPolynomial} (clearance : Certificate polynomial)
    (boxes : FTA.Squarefree.BoxResult polynomial) (degreePositive : 0 < polynomial.natDegree)
    (index : Fin boxes.isolation.tracks.length) :
    (HigherLocations.prepare clearance boxes degreePositive).refinementAt index =
      Track.Circle.Refinement.prepare
        (HigherLocations.prepare clearance boxes degreePositive).request
        (boxes.isolation.tracks.get index) (boxes.isolation.tracks.get index).initial degreePositive :=
  (HigherLocations.prepare clearance boxes degreePositive).refinementAt_eq index

/-- The automatic sufficient center product retains its complete whole-circle error certificate. -/
private theorem automatic_center_close {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {boxes : FTA.Squarefree.BoxResult polynomial} (locations : HigherLocations clearance boxes) :
    clearance.Close (Approximation.prepare locations).target := (Approximation.prepare locations).close

/-- The actual automatic center list preserves the complete original higher-owner degree. -/
private theorem automatic_center_count {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {boxes : FTA.Squarefree.BoxResult polynomial} (locations : HigherLocations clearance boxes) :
    (Approximation.prepare locations).samples.points.length = polynomial.natDegree :=
  (Approximation.prepare locations).samples.count

/-- The automatic sample bank keeps each complete original additional refinement at its actual occurrence. -/
private theorem automatic_center_sample {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {boxes : FTA.Squarefree.BoxResult polynomial} (locations : HigherLocations clearance boxes)
    (index : Fin (Approximation.prepare locations).request.regions.length) :
    (Approximation.prepare locations).samples.sampleAt index =
      CenterProduct.Sample.prepare locations (Approximation.prepare locations).request index :=
  (Approximation.prepare locations).samples.sampleAt_eq index

/-- A sufficient preceding original state is retained by the automatic sample constructor. -/
private theorem automatic_sample_reuses {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {boxes : FTA.Squarefree.BoxResult polynomial} (locations : HigherLocations clearance boxes)
    (request : CenterProduct.Request clearance boxes) (index : Fin request.regions.length)
    (accurate : (locations.refinementAt (request.trackIndex index)).next.box.diagonalSq ≤
      request.residualRadius ^ 2) :
    (CenterProduct.Sample.prepare locations request index).state =
        (locations.refinementAt (request.trackIndex index)).next ∧
      (CenterProduct.Sample.prepare locations request index).selection.isReused = true := by
  rw [CenterProduct.Sample.prepare_eq, dif_pos accurate]
  exact ⟨rfl, rfl⟩

/-- An insufficient preceding state invokes the same original strict refiner in the automatic sample constructor. -/
private theorem automatic_sample_refines {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {boxes : FTA.Squarefree.BoxResult polynomial} (locations : HigherLocations clearance boxes)
    (request : CenterProduct.Request clearance boxes) (index : Fin request.regions.length)
    (needed : ¬ (locations.refinementAt (request.trackIndex index)).next.box.diagonalSq ≤
      request.residualRadius ^ 2) :
    (CenterProduct.Sample.prepare locations request index).state =
        (boxes.isolation.tracks.get (request.trackIndex index)).refine
          (locations.refinementAt (request.trackIndex index)).next
          request.residualRadius request.residualRadius_positive ∧
      (CenterProduct.Sample.prepare locations request index).selection.isReused = false := by
  rw [CenterProduct.Sample.prepare_eq, dif_neg needed]
  exact ⟨rfl, rfl⟩

/-- A requested continuation of an actual cached approximation pays its source target and original geometric bounds. -/
private theorem requested_sample_payments {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {boxes : FTA.Squarefree.BoxResult polynomial} {locations : HigherLocations clearance boxes}
    (approximation : Approximation locations) (index : Fin approximation.request.regions.length)
    (target : Data.Rat.Fraction.Rational) (positive : 0 < target) :
    let request := CenterProduct.Sample.Request.prepare locations target positive
    let selected := CenterProduct.Sample.Refinement.prepare (approximation.samples.sampleAt index) request
    Data.Gaussian.Norm.Basic.normSq (polynomial.eval selected.point) < target ∧
      Data.Gaussian.Norm.Basic.normSq selected.point ≤ approximation.request.radius ∧
        locations.request.collar.width ^ 2 < (selected.point.normSq - 1) ^ 2 := by
  let selected := CenterProduct.Sample.Refinement.prepare (approximation.samples.sampleAt index)
    (CenterProduct.Sample.Request.prepare locations target positive)
  exact ⟨selected.residual_lt, selected.node_bound, selected.radial_gap⟩

/-- An already sufficient actual cached approximation sample retains its same point and selected-state evidence. -/
private theorem requested_sample_reuses {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {boxes : FTA.Squarefree.BoxResult polynomial} {locations : HigherLocations clearance boxes}
    (approximation : Approximation locations) (index : Fin approximation.request.regions.length)
    (target : Data.Rat.Fraction.Rational) (positive : 0 < target)
    (accurate : (approximation.samples.sampleAt index).state.box.diagonalSq ≤
      (CenterProduct.Sample.Request.prepare locations target positive).radius ^ 2) :
    let sample := approximation.samples.sampleAt index
    let selected := CenterProduct.Sample.Refinement.prepare sample
      (CenterProduct.Sample.Request.prepare locations target positive)
    selected.state = sample.state ∧ selected.point = sample.point ∧ selected.selection.isReused = true :=
  CenterProduct.Sample.Refinement.prepare_reuses (approximation.samples.sampleAt index)
    (CenterProduct.Sample.Request.prepare locations target positive) accurate

/-- The independent original chart reading agrees with the same retained sufficient center product. -/
private theorem original_center_winding {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {boxes : FTA.Squarefree.BoxResult polynomial} {locations : HigherLocations clearance boxes}
    (approximation : Approximation locations) (paths : Boundary.Substitutions polynomial)
    (centerPaths : Boundary.Substitutions approximation.target) :
    Polynomial.Winding.Circle.raw centerPaths = Polynomial.Winding.Circle.raw paths :=
  approximation.raw_eq paths centerPaths

/-- The same actual retained higher approximation proves the complete original inside count. -/
private theorem original_higher_argument {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {boxes : FTA.Squarefree.BoxResult polynomial} {locations : HigherLocations clearance boxes}
    (approximation : Approximation locations) (paths : Boundary.Substitutions polynomial) :
    Polynomial.Winding.Circle.raw paths = 4 * (locations.insideCount : Int) :=
  approximation.raw_eq_insideCount paths

/-- The automatic comparison keeps the independently executed original reading equal to the original full inventory. -/
private theorem automatic_argument_principle {polynomial : CoefficientPolynomial}
    (paths : Boundary.Substitutions polynomial) (clearance : Boundary.Clearance paths)
    (normalized : polynomial.normalize = polynomial) :
    let comparison := Comparison.prepare paths clearance normalized
    comparison.reading.winding = (comparison.inventory.insideCount : Int) :=
  (Comparison.prepare paths clearance normalized).winding_eq

/-- Check the actual automatic inventory after sufficient bounded chart preparation. -/
private def check (polynomial : CoefficientPolynomial) (normalized : polynomial.normalize = polynomial)
    (depth inside outside : Nat) : IO Unit := do
  let prepared := Boundary.prepare polynomial depth
  match prepared.2 with
  | .clear clearance =>
      let comparison := Comparison.prepare prepared.1.paths clearance normalized
      let inventory := comparison.inventory
      unless inventory.insideCount == inside && inventory.outsideCount == outside &&
          inventory.insideCount + inventory.outsideCount == polynomial.natDegree &&
          comparison.reading.winding == (inside : Int) &&
          Polynomial.Winding.Circle.raw prepared.1.paths == 4 * (inside : Int) do
        throw (IO.userError "radial inventory lost an original owner or its retained multiplicity")
  | .contact _ _ _ => throw (IO.userError "a radial inventory fixture met the unit boundary")
  | .inconclusive _ _ _ _ _ => throw (IO.userError "a radial inventory fixture lacked sufficient chart clearance")

/-- Run the automatic constant, zero-root, repeated-zero and strict exterior construction chains. -/
public def run : IO Unit := do
  check ⟨[1]⟩ (by decide +kernel) 0 0 0
  check ⟨[1, 0]⟩ (by decide +kernel) 3 1 0
  check ⟨[1, 0, 0]⟩ (by decide +kernel) 5 2 0
  check ⟨[1, -2]⟩ (by decide +kernel) 3 0 1

end TestPurelib.RootIsolation.Multiplicity.Circle
