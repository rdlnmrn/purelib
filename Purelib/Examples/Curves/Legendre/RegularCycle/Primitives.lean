module

public import Purelib.Examples.Curves.Legendre.RegularCycle
public import Purelib.Curves.Legendre.Periods.Jets.Source.Endpoint.Bank
public import Purelib.Curves.Legendre.Periods.Jets.Source.Vertices.Bank
public import Purelib.Integration.Path.Primitive.Cells.Targets
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Original primitive vertices of the regular cycle

The four original continued corner points each supply three exact primitive
denotations at their own selected generator. Their vertex records keep the
original chart, lifted coordinate and selected owner, rather than rebuilding
an owner from a sheet label.
-/

public section

namespace Purelib.Examples.Curves.Legendre.RegularCycle

open Purelib.Curves.Legendre.Periods.Jets.Source
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)

attribute [local irreducible] patch lowerLeft lowerRight upperRight upperLeft

/-- The original lowerLeft and lowerRight corners are distinct by the strict box width. -/
theorem lowerLeft_ne_lowerRight (sheet : Fin 2) : lowerLeft sheet ≠ lowerRight sheet := by
  intro same
  have scalar := congrArg (fun point : LiftedPoint 2 => point.coordinate.re) same
  unfold lowerLeft lowerRight at scalar
  change (patch sheet).box.xLower = (patch sheet).box.xUpper at scalar
  have strict := (patch sheet).box_proper.1
  rewrite [scalar] at strict
  exact lt_irrefl _ strict

/-- The original lowerLeft and upperRight corners are distinct by the strict box width. -/
theorem lowerLeft_ne_upperRight (sheet : Fin 2) : lowerLeft sheet ≠ upperRight sheet := by
  intro same
  have scalar := congrArg (fun point : LiftedPoint 2 => point.coordinate.re) same
  unfold lowerLeft upperRight at scalar
  change (patch sheet).box.xLower = (patch sheet).box.xUpper at scalar
  have strict := (patch sheet).box_proper.1
  rewrite [scalar] at strict
  exact lt_irrefl _ strict

/-- The original lowerLeft and upperLeft corners are distinct by the strict box width. -/
theorem lowerLeft_ne_upperLeft (sheet : Fin 2) : lowerLeft sheet ≠ upperLeft sheet := by
  intro same
  have scalar := congrArg (fun point : LiftedPoint 2 => point.coordinate.im) same
  unfold lowerLeft upperLeft at scalar
  change (patch sheet).box.yLower = (patch sheet).box.yUpper at scalar
  have strict := (patch sheet).box_proper.2
  rewrite [scalar] at strict
  exact lt_irrefl _ strict

/-- The original lowerRight and upperRight corners are distinct by the strict box width. -/
theorem lowerRight_ne_upperRight (sheet : Fin 2) : lowerRight sheet ≠ upperRight sheet := by
  intro same
  have scalar := congrArg (fun point : LiftedPoint 2 => point.coordinate.im) same
  unfold lowerRight upperRight at scalar
  change (patch sheet).box.yLower = (patch sheet).box.yUpper at scalar
  have strict := (patch sheet).box_proper.2
  rewrite [scalar] at strict
  exact lt_irrefl _ strict

/-- The original lowerRight and upperLeft corners are distinct by the strict box width. -/
theorem lowerRight_ne_upperLeft (sheet : Fin 2) : lowerRight sheet ≠ upperLeft sheet := by
  intro same
  have scalar := congrArg (fun point : LiftedPoint 2 => point.coordinate.re) same
  unfold lowerRight upperLeft at scalar
  change (patch sheet).box.xUpper = (patch sheet).box.xLower at scalar
  have strict := (patch sheet).box_proper.1
  rewrite [scalar] at strict
  exact lt_irrefl _ strict

/-- The original upperRight and upperLeft corners are distinct by the strict box width. -/
theorem upperRight_ne_upperLeft (sheet : Fin 2) : upperRight sheet ≠ upperLeft sheet := by
  intro same
  have scalar := congrArg (fun point : LiftedPoint 2 => point.coordinate.re) same
  unfold upperRight upperLeft at scalar
  change (patch sheet).box.xUpper = (patch sheet).box.xLower at scalar
  have strict := (patch sheet).box_proper.1
  rewrite [scalar] at strict
  exact lt_irrefl _ strict

set_option genInjectivity false in
/-- The four original corner owners and their three retained primitive channels on one selected sheet. -/
structure Vertices (sheet : Fin 2) where
  /-- The lower-left original vertex and its three same-generator primitive denotations. -/
  lowerLeft : Vertex 2 (lowerLeft sheet)
  /-- The lower-right original vertex and its retained original continued point. -/
  lowerRight : Vertex 2 (lowerRight sheet)
  /-- The upper-right original vertex and its three actual primitive coefficient pairs. -/
  upperRight : Vertex 2 (upperRight sheet)
  /-- The upper-left original vertex and its same-point primitive channels. -/
  upperLeft : Vertex 2 (upperLeft sheet)

constructive_injectivity Vertices

namespace Vertices

/-- Construct the four retained vertices from the same original continued corner point caches. -/
@[expose] def build (sheet : Fin 2) : Vertices sheet :=
  let lowerLeft := Vertex.ofPoint (lowerLeftRoot sheet)
  let lowerRight := Vertex.ofPoint (lowerRightRoot sheet)
  let upperRight := Vertex.ofPoint (upperRightRoot sheet)
  let upperLeft := Vertex.ofPoint (upperLeftRoot sheet)
  ⟨lowerLeft, lowerRight, upperRight, upperLeft⟩

/-- The lower-left bank vertex retains the actual original continued corner point. -/
theorem build_lowerLeft_sample (sheet : Fin 2) : (build sheet).lowerLeft.sample = lowerLeftRoot sheet := rfl

/-- The lower-right bank vertex retains its distinct original continued corner point. -/
theorem build_lowerRight_sample (sheet : Fin 2) : (build sheet).lowerRight.sample = lowerRightRoot sheet := rfl

/-- The upper-right bank vertex retains that corner's original selected generator and owner. -/
theorem build_upperRight_sample (sheet : Fin 2) : (build sheet).upperRight.sample = upperRightRoot sheet := rfl

/-- The upper-left bank vertex retains the actual original continued point at that lifted endpoint. -/
theorem build_upperLeft_sample (sheet : Fin 2) : (build sheet).upperLeft.sample = upperLeftRoot sheet := rfl

set_option genInjectivity false in
/-- A cached original four-vertex bank and its actual successful corner lookups.

The three bank readings are computed once at each original point. The
finite lookups select those retained original entries, with owner equations
preserving the original vertices rather than identifying roots by labels.
-/
structure Bank (vertices : Vertices sheet) (allocation : Rational) where
  /-- The actual finite original entries and paid channel readings. -/
  entries : Vertex.Bank 2 allocation
  /-- The actual successful finite lookup at the original lowerLeft point. -/
  lowerLeft : Vertex.Bank.Found entries (RegularCycle.lowerLeft sheet)
  /-- The lookup preserves this original retained vertex and all its caches. -/
  lowerLeft_eq : lowerLeft.original = vertices.lowerLeft
  /-- The actual successful finite lookup at the original lowerRight point. -/
  lowerRight : Vertex.Bank.Found entries (RegularCycle.lowerRight sheet)
  /-- The lookup preserves this original retained vertex and all its caches. -/
  lowerRight_eq : lowerRight.original = vertices.lowerRight
  /-- The actual successful finite lookup at the original upperRight point. -/
  upperRight : Vertex.Bank.Found entries (RegularCycle.upperRight sheet)
  /-- The lookup preserves this original retained vertex and all its caches. -/
  upperRight_eq : upperRight.original = vertices.upperRight
  /-- The actual successful finite lookup at the original upperLeft point. -/
  upperLeft : Vertex.Bank.Found entries (RegularCycle.upperLeft sheet)
  /-- The lookup preserves this original retained vertex and all its caches. -/
  upperLeft_eq : upperLeft.original = vertices.upperLeft

constructive_injectivity Bank

namespace Bank

/-- Request four original bank entries once and retain their exact successful finite lookups. -/
def build (vertices : Vertices sheet) (allocation : Rational) (positive : 0 < allocation) :
    Bank vertices allocation := by
  let lowerLeft := Vertex.Entry.request vertices.lowerLeft allocation positive
  let lowerRight := Vertex.Entry.request vertices.lowerRight allocation positive
  let upperRight := Vertex.Entry.request vertices.upperRight allocation positive
  let upperLeft := Vertex.Entry.request vertices.upperLeft allocation positive
  let entries : Vertex.Bank 2 allocation := [lowerLeft, lowerRight, upperRight, upperLeft]
  let first := Vertex.Bank.Found.head lowerLeft [lowerRight, upperRight, upperLeft]
  let second := Vertex.Bank.Found.prepend lowerLeft
    (Vertex.Bank.Found.head lowerRight [upperRight, upperLeft]) (lowerLeft_ne_lowerRight sheet)
  let third := Vertex.Bank.Found.prepend lowerLeft
    (Vertex.Bank.Found.prepend lowerRight (Vertex.Bank.Found.head upperRight [upperLeft])
      (lowerRight_ne_upperRight sheet)) (lowerLeft_ne_upperRight sheet)
  let fourth := Vertex.Bank.Found.prepend lowerLeft
    (Vertex.Bank.Found.prepend lowerRight
      (Vertex.Bank.Found.prepend upperRight (Vertex.Bank.Found.head upperLeft [])
        (upperRight_ne_upperLeft sheet)) (lowerRight_ne_upperLeft sheet)) (lowerLeft_ne_upperLeft sheet)
  exact ⟨entries, first, rfl, second, rfl, third, rfl, fourth, rfl⟩

end Bank

end Vertices

/-- The retained upper cost given by the actual four original displacement quadrances. -/
@[expose] def geometricCost (sheet : Fin 2) : Rational :=
  Norm.Basic.normSq ((lowerRight sheet).coordinate - (lowerLeft sheet).coordinate) +
    (Norm.Basic.normSq ((upperRight sheet).coordinate - (lowerRight sheet).coordinate) +
      (Norm.Basic.normSq ((upperLeft sheet).coordinate - (upperRight sheet).coordinate) +
        Norm.Basic.normSq ((lowerLeft sheet).coordinate - (upperLeft sheet).coordinate)))

/-- The computed four-side displacement cost is nonnegative. -/
theorem geometricCost_nonnegative (sheet : Fin 2) : 0 ≤ geometricCost sheet :=
  add_nonneg (Norm.Basic.normSq_nonneg _) (add_nonneg (Norm.Basic.normSq_nonneg _)
    (add_nonneg (Norm.Basic.normSq_nonneg _) (Norm.Basic.normSq_nonneg _)))

/-- Each original side's displacement quadrance is bounded by the retained four-side cost. -/
theorem geometricCost_bounds (sheet : Fin 2) :
    Norm.Basic.normSq ((lowerRight sheet).coordinate - (lowerLeft sheet).coordinate) ≤ geometricCost sheet ∧
    Norm.Basic.normSq ((upperRight sheet).coordinate - (lowerRight sheet).coordinate) ≤ geometricCost sheet ∧
    Norm.Basic.normSq ((upperLeft sheet).coordinate - (upperRight sheet).coordinate) ≤ geometricCost sheet ∧
    Norm.Basic.normSq ((lowerLeft sheet).coordinate - (upperLeft sheet).coordinate) ≤ geometricCost sheet := by
  let a := Norm.Basic.normSq ((lowerRight sheet).coordinate - (lowerLeft sheet).coordinate)
  let b := Norm.Basic.normSq ((upperRight sheet).coordinate - (lowerRight sheet).coordinate)
  let c := Norm.Basic.normSq ((upperLeft sheet).coordinate - (upperRight sheet).coordinate)
  let d := Norm.Basic.normSq ((lowerLeft sheet).coordinate - (upperLeft sheet).coordinate)
  have ha : 0 ≤ a := Norm.Basic.normSq_nonneg _
  have hb : 0 ≤ b := Norm.Basic.normSq_nonneg _
  have hc : 0 ≤ c := Norm.Basic.normSq_nonneg _
  have hd : 0 ≤ d := Norm.Basic.normSq_nonneg _
  change a ≤ a + (b + (c + d)) ∧ b ≤ a + (b + (c + d)) ∧
    c ≤ a + (b + (c + d)) ∧ d ≤ a + (b + (c + d))
  have addRight (left right : Rational) (nonnegative : 0 ≤ right) : left ≤ left + right := by
    calc
      left = left + 0 := by ring1
      _ ≤ left + right := Order.Arithmetic.add_le_add_direct (le_refl left) nonnegative
  have addLeft (left right : Rational) (nonnegative : 0 ≤ left) : right ≤ left + right := by
    calc
      right = 0 + right := by ring1
      _ ≤ left + right := Order.Arithmetic.add_le_add_direct nonnegative (le_refl right)
  have into : b + (c + d) ≤ a + (b + (c + d)) := addLeft a _ ha
  exact ⟨addRight a _ (add_nonneg hb (add_nonneg hc hd)),
    (addRight b _ (add_nonneg hc hd)).trans into,
    ((addRight c d hd).trans (addLeft b _ hb)).trans into,
    ((addLeft c d hc).trans (addLeft b _ hb)).trans into⟩

set_option genInjectivity false in
/-- The precomputed count-paid endpoint budgets and four original primitive plans before the common model.

Each corner plan serves both incident ordered endpoint occurrences. The
cached maximum pays all eight occurrences while retaining four original
points and their exact primitive factors and denotations.
-/
structure EndpointPlans (vertices : Vertices sheet) (index : Nat) where
  /-- The original finite path's count-paid target cache. -/
  targets : CellEndpoints.Targets (loop sheet).path index
  /-- The same target cache is the actual original count procedure. -/
  targets_eq : targets = CellEndpoints.Targets.build (loop sheet).path index
  /-- The lower-left point's three primitive floors and shared root precision. -/
  lowerLeft : EndpointPlan vertices.lowerLeft.sample index targets.endpoint
  /-- The lower-right point's original endpoint preparation. -/
  lowerRight : EndpointPlan vertices.lowerRight.sample index targets.endpoint
  /-- The upper-right point's original endpoint preparation. -/
  upperRight : EndpointPlan vertices.upperRight.sample index targets.endpoint
  /-- The upper-left point's original endpoint preparation. -/
  upperLeft : EndpointPlan vertices.upperLeft.sample index targets.endpoint
  /-- The retained common floor paying all four actual plans and eight occurrences. -/
  stage : Nat
  /-- The common endpoint floor is exactly the maximum of the four original source selections. -/
  stage_eq : stage = max lowerLeft.requests.stage
    (max lowerRight.requests.stage (max upperRight.requests.stage upperLeft.requests.stage))

constructive_injectivity EndpointPlans

namespace EndpointPlans

variable {vertices : Vertices sheet} {index : Nat}

/-- Cache the four original endpoint plans and their maximum before refining the common inverse model. -/
def build (vertices : Vertices sheet) (index : Nat) : EndpointPlans vertices index :=
  let targets := CellEndpoints.Targets.build (loop sheet).path index
  let lowerLeft := EndpointPlan.ofVertex vertices.lowerLeft index targets.endpoint targets.endpoint_positive
  let lowerRight := EndpointPlan.ofVertex vertices.lowerRight index targets.endpoint targets.endpoint_positive
  let upperRight := EndpointPlan.ofVertex vertices.upperRight index targets.endpoint targets.endpoint_positive
  let upperLeft := EndpointPlan.ofVertex vertices.upperLeft index targets.endpoint targets.endpoint_positive
  let stage := max lowerLeft.requests.stage
    (max lowerRight.requests.stage (max upperRight.requests.stage upperLeft.requests.stage))
  ⟨targets, rfl, lowerLeft, lowerRight, upperRight, upperLeft, stage, rfl⟩

/-- The lower-left original endpoint floor lies below the shared retained selection. -/
theorem lowerLeft_stage_le (plans : EndpointPlans vertices index) : plans.lowerLeft.requests.stage ≤ plans.stage := by
  rewrite [plans.stage_eq]
  exact Data.Nat.Order.le_max_left _ _

/-- The lower-right original endpoint floor is paid by the same shared selection. -/
theorem lowerRight_stage_le (plans : EndpointPlans vertices index) : plans.lowerRight.requests.stage ≤ plans.stage := by
  rewrite [plans.stage_eq]
  exact (Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_right _ _)

/-- The upper-right original endpoint floor is paid before constructing the common model. -/
theorem upperRight_stage_le (plans : EndpointPlans vertices index) : plans.upperRight.requests.stage ≤ plans.stage := by
  rewrite [plans.stage_eq]
  exact (Data.Nat.Order.le_max_left _ _).trans
    ((Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_right _ _))

/-- The upper-left original endpoint floor is paid before all eight ordered occurrences are attached. -/
theorem upperLeft_stage_le (plans : EndpointPlans vertices index) : plans.upperLeft.requests.stage ≤ plans.stage := by
  rewrite [plans.stage_eq]
  exact (Data.Nat.Order.le_max_right _ _).trans
    ((Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_right _ _))

end EndpointPlans

end Purelib.Examples.Curves.Legendre.RegularCycle

end
