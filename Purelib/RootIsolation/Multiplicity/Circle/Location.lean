module

public import Purelib.RootIsolation.Track.Circle
public import Purelib.RootIsolation.Multiplicity.Observation.Basic
public import Purelib.Data.List.DependentProduct
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Radial locations of original multiplicity observations

Linear observations retain their exact rational root. Higher observations
retain every original winding-one owner and its actual two-step radial
refinement. The two counts partition these same owners; no box sample is
identified with an algebraic root.
-/

namespace Purelib.RootIsolation.Multiplicity.Circle

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Geometry.Projective
open Purelib.Polynomial
open Dense.Gaussian
open Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Clearance.Circle (Certificate)
open Roots.Certificate (ExactRoot)
open Rat.Fraction.Order
open Rat.Fraction (Rational)
open Dense.Gaussian.Multiplicity.Basis.Coprime.Side (PositiveSideInput)
open Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput (FactorObservation)
open Dense.Gaussian.Multiplicity.Basis.Context.Basic (PositiveContext)

/-- An original exact root lies strictly inside or strictly outside the unit circle.

The original polynomial clearance excludes equality. Each constructor retains
the actual root's strict rational norm comparison.
-/
public inductive ExactLocation {polynomial : CoefficientPolynomial}
    (clearance : Certificate polynomial) (root : ExactRoot polynomial) : Type
  /-- The original exact root has quadrance less than one. -/
  | inside (holds : root.point.normSq < 1)
  /-- The original exact root has quadrance greater than one. -/
  | outside (holds : 1 < root.point.normSq)

namespace ExactLocation

/-- Decide the strict radial location of the same original exact root. -/
@[expose] public def prepare {polynomial : CoefficientPolynomial}
    (clearance : Certificate polynomial) (root : ExactRoot polynomial) : ExactLocation clearance root := by
  if inside : root.point.normSq < 1 then
    exact .inside inside
  else
    have notBoundary : root.point.normSq ≠ 1 := by
      intro unit
      have lower := clearance.lower root.point unit
      rw [root.root, Gaussian.Norm.Basic.normSq_zero] at lower
      exact (not_lt_of_ge lower) clearance.positive
    exact .outside (lt_of_le_of_ne (le_of_not_gt inside) (Ne.symm notBoundary))

/-- Count the original exact root when its certified location is inside. -/
@[expose] public def insideCount {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {root : ExactRoot polynomial} : ExactLocation clearance root → Nat
  | .inside _ => 1
  | .outside _ => 0

/-- Count the original exact root when its certified location is outside. -/
@[expose] public def outsideCount {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {root : ExactRoot polynomial} : ExactLocation clearance root → Nat
  | .inside _ => 0
  | .outside _ => 1

/-- The two strict locations partition the same one original exact root. -/
public theorem total {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {root : ExactRoot polynomial} (location : ExactLocation clearance root) :
    location.insideCount + location.outsideCount = 1 := by
  cases location <;> rfl

end ExactLocation

set_option genInjectivity false in
/-- Stored radial refinements of every original ordered winding-one owner.

The original complete squarefree isolation remains the index. A single
coefficient-computed request is shared by a materialized product containing
the actual refinement of each original track from its original initial state.
-/
public structure HigherLocations {polynomial : CoefficientPolynomial}
    (clearance : Certificate polynomial) (boxes : FTA.Squarefree.BoxResult polynomial) where
  /-- The original higher observation supplies positive factor degree. -/
  degreePositive : 0 < polynomial.natDegree
  /-- The once-computed sufficient request shared by all original owners. -/
  request : Track.Circle.Request clearance (Bounds.RootRadius.Box.largeSquareBox polynomial)
  /-- The request uses the original factor and its original root-radius box. -/
  request_eq : request = Track.Circle.Request.prepare clearance (Bounds.RootRadius.Box.largeSquareBox polynomial)
  /-- The actual refinement at every original bounded track occurrence. -/
  refinements : List.DependentProduct boxes.isolation.tracks (fun index =>
    Track.Circle.Refinement request (boxes.isolation.tracks.get index) (boxes.isolation.tracks.get index).initial)
  /-- Every stored refinement is produced by the original sufficient-request constructor. -/
  refinements_eq : refinements = List.DependentProduct.ofFn boxes.isolation.tracks (fun index =>
    Track.Circle.Refinement.prepare request (boxes.isolation.tracks.get index)
      (boxes.isolation.tracks.get index).initial degreePositive)

constructive_injectivity HigherLocations

namespace HigherLocations

/-- Assemble the same original family from checked retained sufficient radial refinements. -/
@[expose] public def ofRefinements {polynomial : CoefficientPolynomial}
    (clearance : Certificate polynomial) (boxes : FTA.Squarefree.BoxResult polynomial)
    (degreePositive : 0 < polynomial.natDegree)
    (request : Track.Circle.Request clearance (Bounds.RootRadius.Box.largeSquareBox polynomial))
    (requestEq : request = Track.Circle.Request.prepare clearance (Bounds.RootRadius.Box.largeSquareBox polynomial))
    (refinements : List.DependentProduct boxes.isolation.tracks (fun index =>
      Track.Circle.Refinement request (boxes.isolation.tracks.get index) (boxes.isolation.tracks.get index).initial))
    (refinementsEq : refinements = List.DependentProduct.ofFn boxes.isolation.tracks (fun index =>
      Track.Circle.Refinement.prepare request (boxes.isolation.tracks.get index)
        (boxes.isolation.tracks.get index).initial degreePositive)) : HigherLocations clearance boxes :=
  { degreePositive, request, request_eq := requestEq, refinements, refinements_eq := refinementsEq }

/-- Materialize the actual sufficient radial refinement of every original track exactly once. -/
@[expose] public def prepare {polynomial : CoefficientPolynomial}
    (clearance : Certificate polynomial) (boxes : FTA.Squarefree.BoxResult polynomial)
    (degreePositive : 0 < polynomial.natDegree) :
    HigherLocations clearance boxes :=
  let request := Track.Circle.Request.prepare clearance (Bounds.RootRadius.Box.largeSquareBox polynomial)
  let refinements := List.DependentProduct.ofFn boxes.isolation.tracks (fun index =>
    Track.Circle.Refinement.prepare request (boxes.isolation.tracks.get index)
      (boxes.isolation.tracks.get index).initial degreePositive)
  ofRefinements clearance boxes degreePositive request rfl refinements rfl

/-- Checked retained radial entries preserve the complete original family constructor result. -/
public theorem ofRefinements_eq_prepare {polynomial : CoefficientPolynomial}
    (clearance : Certificate polynomial) (boxes : FTA.Squarefree.BoxResult polynomial)
    (degreePositive : 0 < polynomial.natDegree)
    (request : Track.Circle.Request clearance (Bounds.RootRadius.Box.largeSquareBox polynomial))
    (requestEq : request = Track.Circle.Request.prepare clearance (Bounds.RootRadius.Box.largeSquareBox polynomial))
    (refinements : List.DependentProduct boxes.isolation.tracks (fun index =>
      Track.Circle.Refinement request (boxes.isolation.tracks.get index) (boxes.isolation.tracks.get index).initial))
    (refinementsEq : refinements = List.DependentProduct.ofFn boxes.isolation.tracks (fun index =>
      Track.Circle.Refinement.prepare request (boxes.isolation.tracks.get index)
        (boxes.isolation.tracks.get index).initial degreePositive)) :
    ofRefinements clearance boxes degreePositive request requestEq refinements refinementsEq =
      prepare clearance boxes degreePositive := by
  cases requestEq
  cases refinementsEq
  rfl

/-- Read the same stored radial refinement at its original bounded owner occurrence. -/
@[expose] public def refinementAt {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {boxes : FTA.Squarefree.BoxResult polynomial} (locations : HigherLocations clearance boxes)
    (index : Fin boxes.isolation.tracks.length) :
    Track.Circle.Refinement locations.request (boxes.isolation.tracks.get index)
      (boxes.isolation.tracks.get index).initial :=
  List.DependentProduct.get boxes.isolation.tracks locations.refinements index

/-- A stored refinement is the complete original constructor result on the same track and shared requests. -/
public theorem refinementAt_eq {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {boxes : FTA.Squarefree.BoxResult polynomial} (locations : HigherLocations clearance boxes)
    (index : Fin boxes.isolation.tracks.length) :
    locations.refinementAt index = Track.Circle.Refinement.prepare locations.request
      (boxes.isolation.tracks.get index) (boxes.isolation.tracks.get index).initial locations.degreePositive := by
  exact (congrArg (fun entries => List.DependentProduct.get boxes.isolation.tracks entries index)
    locations.refinements_eq).trans (List.DependentProduct.get_ofFn _ _ index)

/-- Count the original owners whose actual refined box has uniformly negative radial form. -/
@[expose] public def insideCount {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {boxes : FTA.Squarefree.BoxResult polynomial} (locations : HigherLocations clearance boxes) : Nat :=
  List.DependentProduct.sum boxes.isolation.tracks (fun _ refinement =>
    match refinement.side with
    | .negative _ => 1
    | .positive _ => 0) locations.refinements

/-- Read the strict negative label of the same already retained radial refinement. -/
@[expose] public def insideAt {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {boxes : FTA.Squarefree.BoxResult polynomial} (locations : HigherLocations clearance boxes)
    (index : Fin boxes.isolation.tracks.length) : Bool :=
  (locations.refinementAt index).side.isNegative

/-- The original finite label table sums to the same stored-entry radial count. -/
public theorem insideAt_sum {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {boxes : FTA.Squarefree.BoxResult polynomial} (locations : HigherLocations clearance boxes) :
    (List.ofFn (fun index : Fin boxes.isolation.tracks.length =>
      if locations.insideAt index then 1 else 0)).foldr Nat.add 0 = locations.insideCount := by
  have displayed := List.DependentProduct.sum_ofFn boxes.isolation.tracks locations.refinements
    (fun _ refinement => if refinement.side.isNegative then (1 : Nat) else 0) (fun value : Nat => value)
  apply displayed.trans
  apply List.DependentProduct.sum_congr
  intro index
  cases (List.DependentProduct.get boxes.isolation.tracks locations.refinements index).side <;> rfl

/-- Count the original owners whose actual refined box has uniformly positive radial form. -/
@[expose] public def outsideCount {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {boxes : FTA.Squarefree.BoxResult polynomial} (locations : HigherLocations clearance boxes) : Nat :=
  List.DependentProduct.sum boxes.isolation.tracks (fun _ refinement =>
    match refinement.side with
    | .negative _ => 0
    | .positive _ => 1) locations.refinements

/-- The two strict radial classes partition exactly the original degree-sized ordered owner list. -/
public theorem total {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {boxes : FTA.Squarefree.BoxResult polynomial} (locations : HigherLocations clearance boxes) :
    locations.insideCount + locations.outsideCount = polynomial.natDegree := by
  rw [insideCount, outsideCount, ← List.DependentProduct.sum_add]
  calc
    _ = List.DependentProduct.sum boxes.isolation.tracks (fun _ _ => 1) locations.refinements := by
      apply List.DependentProduct.sum_congr
      intro index
      cases (List.DependentProduct.get boxes.isolation.tracks locations.refinements index).side <;> rfl
    _ = boxes.isolation.tracks.length := List.DependentProduct.sum_one _ _
    _ = polynomial.natDegree := boxes.isolation.tracks_length

end HigherLocations

/-- The strict radial locations attached to one same original factor observation. -/
@[expose] public def Locations {source opposite : CoefficientPolynomial} {input : PositiveSideInput source opposite}
    {context : PositiveContext input.entries}
    (clearance : Certificate context.focus.part.polynomial) : FactorObservation input context → Type
  | .exact root _ _ => ExactLocation clearance root
  | .higher boxes _ => HigherLocations clearance boxes

namespace Locations

/-- Locate the same original exact root or complete higher owner family without another isolation call. -/
@[expose] public def prepare {source opposite : CoefficientPolynomial} {input : PositiveSideInput source opposite}
    {context : PositiveContext input.entries}
    (clearance : Certificate context.focus.part.polynomial) (observation : FactorObservation input context) :
    Locations clearance observation :=
  match observation with
  | .exact root _ _ => ExactLocation.prepare clearance root
  | .higher boxes degree => HigherLocations.prepare clearance boxes (Nat.lt_of_lt_of_le (by decide) degree)

/-- Count inside sites of the same retained original observation. -/
@[expose] public def insideCount {source opposite : CoefficientPolynomial} {input : PositiveSideInput source opposite}
    {context : PositiveContext input.entries}
    {clearance : Certificate context.focus.part.polynomial} :
    (observation : FactorObservation input context) → Locations clearance observation → Nat
  | .exact _ _ _, locations => ExactLocation.insideCount locations
  | .higher _ _, locations => HigherLocations.insideCount locations

/-- Read the strict radial label at the same original degree-bounded geometric occurrence.

Exact observations have their single retained root. Higher observations use
the identical natural coordinate in the original degree-sized track list and
read its already stored radial refinement, without invoking a refiner.
-/
@[expose] public def insideAt {source opposite : CoefficientPolynomial} {input : PositiveSideInput source opposite}
    {context : PositiveContext input.entries} {clearance : Certificate context.focus.part.polynomial}
    (observation : FactorObservation input context) (locations : Locations clearance observation)
    (index : Fin context.focus.part.polynomial.natDegree) : Bool :=
  match observation with
  | .exact _ _ _ =>
      match locations with
      | .inside _ => true
      | .outside _ => false
  | .higher boxes _ =>
      let stored : HigherLocations clearance boxes := locations
      let original : Fin boxes.isolation.tracks.length := ⟨index.val, boxes.isolation.tracks_length.symm ▸ index.isLt⟩
      stored.insideAt original

/-- Summing the original occurrence labels reads the same retained geometric inside count. -/
public theorem insideAt_sum {source opposite : CoefficientPolynomial} {input : PositiveSideInput source opposite}
    {context : PositiveContext input.entries} {clearance : Certificate context.focus.part.polynomial}
    (observation : FactorObservation input context) (locations : Locations clearance observation) :
    (List.ofFn (fun index : Fin context.focus.part.polynomial.natDegree =>
      if insideAt observation locations index then 1 else 0)).foldr Nat.add 0 = insideCount observation locations := by
  cases observation with
  | exact root degree oppositeAtRoot =>
      have table : List.ofFn (fun index : Fin context.focus.part.polynomial.natDegree =>
          if insideAt (.exact root degree oppositeAtRoot) locations index then 1 else 0) =
          List.ofFn (fun _ : Fin 1 => ExactLocation.insideCount locations) := by
        apply List.OfFn.Basic.ofFn_congr_size degree
        intro first second same
        cases locations <;> rfl
      rewrite [table, List.OfFn.Basic.ofFn_succ, List.ofFn_zero]
      exact Nat.add_zero _
  | higher boxes degree =>
      let stored : HigherLocations clearance boxes := locations
      have table : List.ofFn (fun index : Fin context.focus.part.polynomial.natDegree =>
          if insideAt (.higher boxes degree) locations index then 1 else 0) =
          List.ofFn (fun index : Fin boxes.isolation.tracks.length =>
            if stored.insideAt index then 1 else 0) := by
        apply List.OfFn.Basic.ofFn_congr_size boxes.isolation.tracks_length.symm
        intro first second same
        change (if stored.insideAt ⟨first.val, _⟩ then 1 else 0) = _
        have original : (⟨first.val, boxes.isolation.tracks_length.symm ▸ first.isLt⟩ :
            Fin boxes.isolation.tracks.length) = second := Fin.ext same
        exact congrArg (fun index => if stored.insideAt index then (1 : Nat) else 0) original
      exact (congrArg (fun values : List Nat => values.foldr Nat.add 0) table).trans stored.insideAt_sum

/-- Count outside sites of the same retained original observation. -/
@[expose] public def outsideCount {source opposite : CoefficientPolynomial} {input : PositiveSideInput source opposite}
    {context : PositiveContext input.entries}
    {clearance : Certificate context.focus.part.polynomial} :
    (observation : FactorObservation input context) → Locations clearance observation → Nat
  | .exact _ _ _, locations => ExactLocation.outsideCount locations
  | .higher _ _, locations => HigherLocations.outsideCount locations

/-- The observation's two strict location counts sum to its original factor degree. -/
public theorem total {source opposite : CoefficientPolynomial} {input : PositiveSideInput source opposite}
    {context : PositiveContext input.entries}
    {clearance : Certificate context.focus.part.polynomial} (observation : FactorObservation input context)
    (locations : Locations clearance observation) :
    insideCount observation locations + outsideCount observation locations =
      context.focus.part.polynomial.natDegree := by
  cases observation with
  | exact root degree oppositeAtRoot => exact (ExactLocation.total locations).trans degree.symm
  | higher boxes degree => exact HigherLocations.total locations

end Locations
end Purelib.RootIsolation.Multiplicity.Circle
