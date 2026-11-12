module

public import Purelib.RootIsolation.Multiplicity.Circle.Location
public import Purelib.RootIsolation.Multiplicity.Family.Basic
public import Purelib.RootIsolation.Multiplicity.Side.Build
public import Purelib.Polynomial.Clearance.Circle.Factor
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Product
import Purelib.Polynomial.Dense.Gaussian.Coprime.Operations
import Purelib.Polynomial.Dense.Leading
import Purelib.Data.List.Map
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Stored multiplicity-aware radial inventories

Each original positive context supplies its original observation once. The
materialized row keeps that same observation, its transferred source margin
and its actual strict radial locations. Weighted folds consume these rows,
and their combined count is the original source degree.
-/

namespace Purelib.RootIsolation.Multiplicity.Circle

open Purelib.Data
open Purelib.Polynomial
open Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Clearance.Circle (Certificate FactorMargin)
open Dense.Gaussian.Multiplicity.Basis.Coprime.Side (PositiveSideInput)
open Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput
  (FactorObservation PositiveFamily ObservationInternallySeparated ObservationAtomicMaximality ObservationsSeparated)
open Dense.Gaussian.Multiplicity.Basis.Context.Basic (PositiveContext positiveContexts)
open Dense.Gaussian.Multiplicity.Basis
open Dense.Basic (DensePolynomial)
open Purelib.RootIsolation.Multiplicity.Side.Basic (SideResult)

set_option genInjectivity false in
/-- A materialized location row retaining the same original factor observation.

The expected observation is only a correctness index. Its actual value is
stored once, and the original source factorization supplies one cached factor
margin. All radial data are constructed from these same stored values.
-/
public structure Factor {source opposite : CoefficientPolynomial}
    (clearance : Certificate source) (input : PositiveSideInput source opposite)
    (context : PositiveContext input.entries) (expected : FactorObservation input context) where
  /-- The actual once-read original observation. -/
  observation : FactorObservation input context
  /-- The retained observation belongs to the same original family occurrence. -/
  observation_eq : observation = expected
  /-- The once-computed original factor margin from the source factorization. -/
  margin : FactorMargin clearance (input.focusFactorization context)
  /-- The factor margin is the original coefficient-bound constructor's result. -/
  margin_eq : margin = FactorMargin.prepare clearance (input.focusFactorization context)
  /-- The actual strict radial locations of this same stored observation. -/
  locations : Locations margin.toCertificate observation
  /-- The stored locations use the same retained observation and margin. -/
  locations_eq : locations = Locations.prepare margin.toCertificate observation

constructive_injectivity Factor

namespace Factor

/-- Retain the same checked observation, transferred margin and original radial locations without replay. -/
@[expose] public def ofCaches {source opposite : CoefficientPolynomial}
    (clearance : Certificate source) (input : PositiveSideInput source opposite)
    (context : PositiveContext input.entries) (expected : FactorObservation input context)
    (observation : FactorObservation input context) (observationEq : observation = expected)
    (margin : FactorMargin clearance (input.focusFactorization context))
    (marginEq : margin = FactorMargin.prepare clearance (input.focusFactorization context))
    (locations : Locations margin.toCertificate observation)
    (locationsEq : locations = Locations.prepare margin.toCertificate observation) :
    Factor clearance input context expected :=
  { observation, observation_eq := observationEq, margin, margin_eq := marginEq
    locations, locations_eq := locationsEq }

/-- Locate one supplied original observation without repeating its isolation. -/
@[expose] public def prepare {source opposite : CoefficientPolynomial}
    (clearance : Certificate source) (input : PositiveSideInput source opposite)
    (context : PositiveContext input.entries) (observation : FactorObservation input context) :
    Factor clearance input context observation :=
  let margin := FactorMargin.prepare clearance (input.focusFactorization context)
  let locations := Locations.prepare margin.toCertificate observation
  ofCaches clearance input context observation observation rfl margin rfl locations rfl

/-- Checked complete original caches recover the same factor preparation. -/
public theorem ofCaches_eq_prepare {source opposite : CoefficientPolynomial}
    (clearance : Certificate source) (input : PositiveSideInput source opposite)
    (context : PositiveContext input.entries) (expected : FactorObservation input context)
    (observation : FactorObservation input context) (observationEq : observation = expected)
    (margin : FactorMargin clearance (input.focusFactorization context))
    (marginEq : margin = FactorMargin.prepare clearance (input.focusFactorization context))
    (locations : Locations margin.toCertificate observation)
    (locationsEq : locations = Locations.prepare margin.toCertificate observation) :
    ofCaches clearance input context expected observation observationEq margin marginEq locations locationsEq =
      prepare clearance input context expected := by
  cases observationEq
  cases marginEq
  cases locationsEq
  rfl

/-- Restore the same complete original factor construction from its retained caches. -/
public theorem restore {source opposite : CoefficientPolynomial} {clearance : Certificate source}
    {input : PositiveSideInput source opposite} {context : PositiveContext input.entries}
    {expected : FactorObservation input context} (factor : Factor clearance input context expected) :
    factor = prepare clearance input context expected := by
  cases factor with
  | mk observation observationEq margin marginEq locations locationsEq =>
      exact ofCaches_eq_prepare clearance input context expected observation observationEq margin marginEq
        locations locationsEq

/-- Count the inside sites of the stored original observation. -/
@[expose] public def insideCount {source opposite : CoefficientPolynomial} {clearance : Certificate source}
    {input : PositiveSideInput source opposite} {context : PositiveContext input.entries}
    {expected : FactorObservation input context} (factor : Factor clearance input context expected) : Nat :=
  Locations.insideCount factor.observation factor.locations

/-- Count the outside sites of the stored original observation. -/
@[expose] public def outsideCount {source opposite : CoefficientPolynomial} {clearance : Certificate source}
    {input : PositiveSideInput source opposite} {context : PositiveContext input.entries}
    {expected : FactorObservation input context} (factor : Factor clearance input context expected) : Nat :=
  Locations.outsideCount factor.observation factor.locations

/-- The two stored location counts partition the original focused factor degree. -/
public theorem total {source opposite : CoefficientPolynomial} {clearance : Certificate source}
    {input : PositiveSideInput source opposite} {context : PositiveContext input.entries}
    {expected : FactorObservation input context} (factor : Factor clearance input context expected) :
    factor.insideCount + factor.outsideCount = context.focus.part.polynomial.natDegree :=
  Locations.total factor.observation factor.locations

end Factor

set_option genInjectivity false in
/-- A materialized radial inventory of the original positive multiplicity family.

Every stored row is indexed by its original context and original family
observation. Materialization evaluates each observation once; subsequent
readbacks and weighted counts consume the retained product spine.
-/
public structure PositiveInventory {source opposite : CoefficientPolynomial}
    (clearance : Certificate source) (input : PositiveSideInput source opposite) (family : PositiveFamily input) where
  /-- One stored radial factor row at every original context occurrence. -/
  factors : List.DependentProduct input.contexts (fun index =>
    Factor clearance input (input.contexts.get index) (family.observationAt index))
  /-- Each row is built once from its same original family observation. -/
  factors_eq : factors = List.DependentProduct.ofFn input.contexts (fun index =>
    Factor.prepare clearance input (input.contexts.get index) (family.observationAt index))

constructive_injectivity PositiveInventory

namespace PositiveInventory

/-- Retain checked same-context factor rows without observing or locating a factor again. -/
@[expose] public def ofFactors {source opposite : CoefficientPolynomial}
    (clearance : Certificate source) (input : PositiveSideInput source opposite) (family : PositiveFamily input)
    (factors : List.DependentProduct input.contexts (fun index =>
      Factor clearance input (input.contexts.get index) (family.observationAt index)))
    (factorsEq : factors = List.DependentProduct.ofFn input.contexts (fun index =>
      Factor.prepare clearance input (input.contexts.get index) (family.observationAt index))) :
    PositiveInventory clearance input family :=
  { factors, factors_eq := factorsEq }

/-- Materialize all original observations and their radial locations once in original context order. -/
@[expose] public def prepare {source opposite : CoefficientPolynomial}
    (clearance : Certificate source) (input : PositiveSideInput source opposite) (family : PositiveFamily input) :
    PositiveInventory clearance input family :=
  let factors := List.DependentProduct.ofFn input.contexts (fun index =>
    Factor.prepare clearance input (input.contexts.get index) (family.observationAt index))
  ofFactors clearance input family factors rfl

/-- Checked original factor rows recover the complete original inventory producer. -/
public theorem ofFactors_eq_prepare {source opposite : CoefficientPolynomial}
    (clearance : Certificate source) (input : PositiveSideInput source opposite) (family : PositiveFamily input)
    (factors : List.DependentProduct input.contexts (fun index =>
      Factor clearance input (input.contexts.get index) (family.observationAt index)))
    (factorsEq : factors = List.DependentProduct.ofFn input.contexts (fun index =>
      Factor.prepare clearance input (input.contexts.get index) (family.observationAt index))) :
    ofFactors clearance input family factors factorsEq = prepare clearance input family := by
  cases factorsEq
  rfl

/-- Restore the same complete original positive inventory from its retained product spine. -/
public theorem restore {source opposite : CoefficientPolynomial} {clearance : Certificate source}
    {input : PositiveSideInput source opposite} {family : PositiveFamily input}
    (inventory : PositiveInventory clearance input family) : inventory = prepare clearance input family := by
  cases inventory with
  | mk factors factorsEq => exact ofFactors_eq_prepare clearance input family factors factorsEq

/-- Read the same stored factor row at its original bounded context occurrence. -/
@[expose] public def factorAt {source opposite : CoefficientPolynomial} {clearance : Certificate source}
    {input : PositiveSideInput source opposite} {family : PositiveFamily input}
    (inventory : PositiveInventory clearance input family) (index : Fin input.contexts.length) :
    Factor clearance input (input.contexts.get index) (family.observationAt index) :=
  List.DependentProduct.get input.contexts inventory.factors index

/-- The stored row preserves its same original family's internal owner separation. -/
@[expose] public def internallySeparated {source opposite : CoefficientPolynomial} {clearance : Certificate source}
    {input : PositiveSideInput source opposite} {family : PositiveFamily input}
    (inventory : PositiveInventory clearance input family) (index : Fin input.contexts.length) :
    ObservationInternallySeparated (inventory.factorAt index).observation := by
  rw [(inventory.factorAt index).observation_eq]
  exact family.internallySeparated index

/-- The stored row preserves its same original family's atomic maximality. -/
@[expose] public def atomicMaximality {source opposite : CoefficientPolynomial} {clearance : Certificate source}
    {input : PositiveSideInput source opposite} {family : PositiveFamily input}
    (inventory : PositiveInventory clearance input family) (index : Fin input.contexts.length) :
    ObservationAtomicMaximality (inventory.factorAt index).observation := by
  rw [(inventory.factorAt index).observation_eq]
  exact family.atomicMaximality index

/-- Distinct stored rows preserve the original family's cross-observation separation. -/
@[expose] public def pairwiseSeparated {source opposite : CoefficientPolynomial} {clearance : Certificate source}
    {input : PositiveSideInput source opposite} {family : PositiveFamily input}
    (inventory : PositiveInventory clearance input family) (left right : Fin input.contexts.length)
    (different : left ≠ right) :
    ObservationsSeparated (inventory.factorAt left).observation
      (inventory.factorAt right).observation := by
  rw [(inventory.factorAt left).observation_eq, (inventory.factorAt right).observation_eq]
  exact family.pairwiseSeparated left right different

/-- Sum the inside owner counts with their original focused multiplicities. -/
@[expose] public def insideCount {source opposite : CoefficientPolynomial} {clearance : Certificate source}
    {input : PositiveSideInput source opposite} {family : PositiveFamily input}
    (inventory : PositiveInventory clearance input family) : Nat :=
  List.DependentProduct.sum input.contexts (fun index factor =>
    (input.contexts.get index).focus.multiplicity * factor.insideCount) inventory.factors

/-- Sum the outside owner counts with their original focused multiplicities. -/
@[expose] public def outsideCount {source opposite : CoefficientPolynomial} {clearance : Certificate source}
    {input : PositiveSideInput source opposite} {family : PositiveFamily input}
    (inventory : PositiveInventory clearance input family) : Nat :=
  List.DependentProduct.sum input.contexts (fun index factor =>
    (input.contexts.get index).focus.multiplicity * factor.outsideCount) inventory.factors

/-- Prepending an original entry changes no focused weight in the lifted context tail. -/
private theorem lifted_weights (head : Positive.PositiveEntry) {entries : List Positive.PositiveEntry}
    (contexts : List (PositiveContext entries)) :
    (contexts.map (PositiveContext.lift head)).foldr
        (fun context total => context.focus.multiplicity * context.focus.part.polynomial.natDegree + total) 0 =
      contexts.foldr
        (fun context total => context.focus.multiplicity * context.focus.part.polynomial.natDegree + total) 0 := by
  induction contexts with
  | nil => rfl
  | cons context contexts tail =>
      change context.focus.multiplicity * context.focus.part.polynomial.natDegree +
          (contexts.map (PositiveContext.lift head)).foldr _ 0 =
        context.focus.multiplicity * context.focus.part.polynomial.natDegree + contexts.foldr _ 0
      exact congrArg (fun total => context.focus.multiplicity * context.focus.part.polynomial.natDegree + total) tail

/-- The complete original context list counts every original positive multiplicity entry once. -/
private theorem context_weights : (entries : List Positive.PositiveEntry) →
    (positiveContexts entries).foldr
        (fun context total => context.focus.multiplicity * context.focus.part.polynomial.natDegree + total) 0 =
      Product.positiveDegree entries
  | [] => rfl
  | head :: entries => by
      change head.multiplicity * head.part.polynomial.natDegree +
          ((positiveContexts entries).map (PositiveContext.lift head)).foldr _ 0 =
        head.multiplicity * head.part.polynomial.natDegree + Product.positiveDegree entries
      rw [lifted_weights head (positiveContexts entries), context_weights entries]

/-- The weighted strict radial classes partition exactly the original source degree.

This count uses the same stored original observations and the same original
multiplicity decomposition. Higher observations contribute their complete
degree-sized owner lists, rather than one sample per squarefree factor.
-/
public theorem total {source opposite : CoefficientPolynomial} {clearance : Certificate source}
    {input : PositiveSideInput source opposite} {family : PositiveFamily input}
    (inventory : PositiveInventory clearance input family) :
    inventory.insideCount + inventory.outsideCount = source.natDegree := by
  rw [insideCount, outsideCount, ← List.DependentProduct.sum_add]
  calc
    _ = List.DependentProduct.sum input.contexts
        (fun index _ => (input.contexts.get index).focus.multiplicity *
          (input.contexts.get index).focus.part.polynomial.natDegree) inventory.factors := by
      apply List.DependentProduct.sum_congr
      intro index
      rw [← Nat.mul_add]
      exact congrArg (fun count => (input.contexts.get index).focus.multiplicity * count)
        (inventory.factorAt index).total
    _ = input.contexts.foldr
        (fun context total => context.focus.multiplicity * context.focus.part.polynomial.natDegree + total) 0 :=
      List.DependentProduct.sum_items input.contexts inventory.factors
        (fun context => context.focus.multiplicity * context.focus.part.polynomial.natDegree)
    _ = Product.positiveDegree input.entries := context_weights input.entries
    _ = source.natDegree := family.weightedDegree

end PositiveInventory

/-- The stored radial payload of the same original constant or positive side result. -/
@[expose] public def SideLocations {source opposite : CoefficientPolynomial} (clearance : Certificate source) :
    SideResult source opposite → Type
  | .constant _ _ _ => PUnit
  | .positive input family => PositiveInventory clearance input family

namespace SideLocations

/-- Materialize the radial payload of the supplied original side result without rebuilding the side. -/
@[expose] public def prepare {source opposite : CoefficientPolynomial} (clearance : Certificate source) :
    (side : SideResult source opposite) → SideLocations clearance side
  | .constant _ _ _ => PUnit.unit
  | .positive input family => PositiveInventory.prepare clearance input family

/-- Read the multiplicity-weighted inside count from the retained original side payload. -/
@[expose] public def insideCount {source opposite : CoefficientPolynomial} {clearance : Certificate source} :
    (side : SideResult source opposite) → SideLocations clearance side → Nat
  | .constant _ _ _, _ => 0
  | .positive _ _, locations => PositiveInventory.insideCount locations

/-- Read the multiplicity-weighted outside count from the retained original side payload. -/
@[expose] public def outsideCount {source opposite : CoefficientPolynomial} {clearance : Certificate source} :
    (side : SideResult source opposite) → SideLocations clearance side → Nat
  | .constant _ _ _, _ => 0
  | .positive _ _, locations => PositiveInventory.outsideCount locations

/-- The original side's two weighted radial classes account for its complete source degree. -/
public theorem total {source opposite : CoefficientPolynomial} {clearance : Certificate source}
    (side : SideResult source opposite) (locations : SideLocations clearance side) :
    insideCount side locations + outsideCount side locations = source.natDegree := by
  cases side with
  | constant sourceNonzero degreeZero oppositeNonzero => exact degreeZero.symm
  | positive input family => exact PositiveInventory.total locations

end SideLocations

set_option genInjectivity false in
/-- An automatic complete radial inventory retaining the original multiplicity side construction.

The original normalized polynomial and whole-circle margin remain indices.
The constructor derives nonzeroness and coprimality to one, executes the
original side builder once, and materializes all of its original observations.
No root list or sufficient refinement budget is supplied by a caller.
-/
public structure Inventory {source : CoefficientPolynomial} (clearance : Certificate source) where
  /-- The retained source is already normalized. -/
  normalized : source.normalize = source
  /-- The actual original multiplicity-aware side result against constant one. -/
  side : SideResult source (DensePolynomial.constant 1)
  /-- The side is the actual original builder's result on the same source. -/
  side_eq : side = Side.Build.buildSide source (DensePolynomial.constant 1) normalized clearance.nonzero
    (Dense.Leading.LeadingTerm.constant (by decide : (1 : Gaussian.Basic.Canonical) ≠ 0)).nonzero
    (Dense.Gaussian.Coprime.Operations.CoprimeCertificate.constantRight clearance.nonzero)
  /-- The materialized payload of this same original side result. -/
  locations : SideLocations clearance side
  /-- The payload is constructed from the stored original side, without another side construction. -/
  locations_eq : locations = SideLocations.prepare clearance side

constructive_injectivity Inventory

namespace Inventory

/-- Retain a checked complete original side and its same radial payload without running either producer. -/
@[expose] public def ofCaches {source : CoefficientPolynomial} (clearance : Certificate source)
    (normalized : source.normalize = source) (side : SideResult source (DensePolynomial.constant 1))
    (sideEq : side = Side.Build.buildSide source (DensePolynomial.constant 1) normalized clearance.nonzero
      (Dense.Leading.LeadingTerm.constant (by decide : (1 : Gaussian.Basic.Canonical) ≠ 0)).nonzero
      (Dense.Gaussian.Coprime.Operations.CoprimeCertificate.constantRight clearance.nonzero))
    (locations : SideLocations clearance side) (locationsEq : locations = SideLocations.prepare clearance side) :
    Inventory clearance :=
  { normalized, side, side_eq := sideEq, locations, locations_eq := locationsEq }

/-- Construct the complete original multiplicity inventory and its sufficient radial refinements automatically. -/
@[expose] public def prepare {source : CoefficientPolynomial} (clearance : Certificate source)
    (normalized : source.normalize = source) : Inventory clearance :=
  let side := Side.Build.buildSide source (DensePolynomial.constant 1) normalized clearance.nonzero
    (Dense.Leading.LeadingTerm.constant (by decide : (1 : Gaussian.Basic.Canonical) ≠ 0)).nonzero
    (Dense.Gaussian.Coprime.Operations.CoprimeCertificate.constantRight clearance.nonzero)
  let locations := SideLocations.prepare clearance side
  ofCaches clearance normalized side rfl locations rfl

/-- Checked complete original side and location caches restore the same automatic inventory. -/
public theorem ofCaches_eq_prepare {source : CoefficientPolynomial} (clearance : Certificate source)
    (normalized : source.normalize = source) (side : SideResult source (DensePolynomial.constant 1))
    (sideEq : side = Side.Build.buildSide source (DensePolynomial.constant 1) normalized clearance.nonzero
      (Dense.Leading.LeadingTerm.constant (by decide : (1 : Gaussian.Basic.Canonical) ≠ 0)).nonzero
      (Dense.Gaussian.Coprime.Operations.CoprimeCertificate.constantRight clearance.nonzero))
    (locations : SideLocations clearance side) (locationsEq : locations = SideLocations.prepare clearance side) :
    ofCaches clearance normalized side sideEq locations locationsEq = prepare clearance normalized := by
  cases sideEq
  cases locationsEq
  rfl

/-- Restore the same automatic inventory from its retained original side and radial caches. -/
public theorem restore {source : CoefficientPolynomial} {clearance : Certificate source}
    (inventory : Inventory clearance) : inventory = prepare clearance inventory.normalized := by
  cases inventory with
  | mk normalized side sideEq locations locationsEq =>
      exact ofCaches_eq_prepare clearance normalized side sideEq locations locationsEq

/-- Read the complete original inventory's multiplicity-weighted inside count. -/
@[expose] public def insideCount {source : CoefficientPolynomial} {clearance : Certificate source}
    (inventory : Inventory clearance) : Nat :=
  SideLocations.insideCount inventory.side inventory.locations

/-- Read the complete original inventory's multiplicity-weighted outside count. -/
@[expose] public def outsideCount {source : CoefficientPolynomial} {clearance : Certificate source}
    (inventory : Inventory clearance) : Nat :=
  SideLocations.outsideCount inventory.side inventory.locations

/-- The automatically constructed inventory accounts for every original source multiplicity. -/
public theorem total {source : CoefficientPolynomial} {clearance : Certificate source}
    (inventory : Inventory clearance) :
    inventory.insideCount + inventory.outsideCount = source.natDegree :=
  SideLocations.total inventory.side inventory.locations

end Inventory
end Purelib.RootIsolation.Multiplicity.Circle
