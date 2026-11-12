module

public import Purelib.RootIsolation.Multiplicity.Circle.CenterProduct
public import Purelib.RootIsolation.Multiplicity.Circle.Inventory
public import Purelib.Polynomial.Winding.Circle.Operations
import Purelib.Polynomial.Winding.Circle.Multiplicity
import Purelib.Data.List.OfFn.Basic
import Purelib.Polynomial.Dense.Gaussian.Roots.Linear
import Purelib.Polynomial.Winding.Circle.Comparison
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Original radial owner counts and independent circle winding

The retained sufficient center product compares the original polynomial with
its actual refined rational centers. Each center has the same strict side as
its original geometric owner. Original product and rational-linear index laws
therefore identify the independent winding with the original inside count.
-/

namespace Purelib.RootIsolation.Multiplicity.Circle.CenterProduct

open Purelib.Data
open Purelib.RationalFunctions.Curve.Canonical.Circle
open Purelib.Polynomial
open Dense.Gaussian
open Basic.CanonicalCoefficients (CoefficientPolynomial)
open Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Clearance.Circle (Certificate)
open Gaussian.Basic (Canonical)
open Rat.Fraction (Rational)
open Rat.Fraction.Order

/-- The same retained sample is strictly apart from the rational unit circle. -/
private theorem sample_apart {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {source : FTA.Squarefree.BoxResult polynomial} {locations : HigherLocations clearance source}
    {request : Request clearance source} {index : Fin request.regions.length}
    (sample : Sample locations request index) : sample.point.normSq ≠ 1 := by
  have radial := sample.radial
  cases side : (locations.refinementAt (request.trackIndex index)).side with
  | negative _ =>
      rw [side] at radial
      exact ne_of_lt radial
  | positive _ =>
      rw [side] at radial
      exact ne_of_gt radial

/-- Every point of the actual stored sample list is strictly apart from the rational unit circle. -/
private theorem points_apart {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {source : FTA.Squarefree.BoxResult polynomial} {locations : HigherLocations clearance source}
    {request : Request clearance source} (samples : Samples locations request) :
    ∀ point ∈ samples.points, point.normSq ≠ 1 := by
  intro point member
  rw [samples.points_eq] at member
  rcases List.OfFn.Basic.mem_ofFn.mp member with ⟨index, equal⟩
  rw [← equal]
  exact sample_apart (samples.sampleAt index)

/-- The same actual sample list counts exactly the retained negative original owner sides. -/
private theorem inside_count {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {source : FTA.Squarefree.BoxResult polynomial} {locations : HigherLocations clearance source}
    {request : Request clearance source} (samples : Samples locations request) :
    samples.points.foldr (fun point total => (if point.normSq < 1 then 1 else 0) + total) 0 =
      locations.insideCount := by
  let counts := fun index : Fin source.isolation.tracks.length =>
    match (locations.refinementAt index).side with
    | .negative _ => 1
    | .positive _ => 0
  have entriesCount :
      samples.points.foldr (fun point total => (if point.normSq < 1 then 1 else 0) + total) 0 =
      List.DependentProduct.sum request.regions (fun index _ => counts (request.trackIndex index)) samples.entries := by
    rw [samples.points_eq, List.DependentProduct.sum_ofFn]
    apply List.DependentProduct.sum_congr
    intro index
    have radial := (samples.sampleAt index).radial
    change (if (samples.sampleAt index).point.normSq < 1 then 1 else 0) = counts (request.trackIndex index)
    dsimp only [counts]
    cases side : (locations.refinementAt (request.trackIndex index)).side with
    | negative _ =>
        rw [side] at radial
        rw [if_pos radial]
    | positive _ =>
        rw [side] at radial
        rw [if_neg (not_lt_of_ge radial.le)]
  have sameIndices : List.ofFn (fun index : Fin request.regions.length => counts (request.trackIndex index)) =
      List.ofFn counts := by
    calc
      _ = List.ofFn (fun index : Fin request.regions.length => counts (Fin.cast request.regions_length index)) :=
        List.OfFn.Basic.ofFn_congr (fun _ => congrArg counts (Fin.ext rfl))
      _ = List.ofFn counts := List.OfFn.Basic.ofFn_cast request.regions_length counts
  calc
    _ = List.DependentProduct.sum request.regions
        (fun index _ => counts (request.trackIndex index)) samples.entries := entriesCount
    _ = (List.ofFn (fun index : Fin request.regions.length => counts (request.trackIndex index))).foldr Nat.add 0 :=
      (List.DependentProduct.sum_ofFn request.regions samples.entries
        (fun index _ => counts (request.trackIndex index)) (fun value => value)).symm
    _ = (List.ofFn counts).foldr Nat.add 0 := congrArg (fun values => values.foldr Nat.add 0) sameIndices
    _ = locations.insideCount := by
      have reading := List.DependentProduct.sum_ofFn source.isolation.tracks locations.refinements
        (fun _ refinement => match refinement.side with | .negative _ => 1 | .positive _ => 0)
        (fun value => value)
      refine Eq.trans ?_ (Eq.trans reading ?_)
      · apply congrArg (fun values : List Nat => values.foldr Nat.add 0)
        apply List.OfFn.Basic.ofFn_congr
        intro index
        dsimp only [counts, HigherLocations.refinementAt]
        cases (List.DependentProduct.get source.isolation.tracks locations.refinements index).side <;> rfl
      · unfold HigherLocations.insideCount
        apply List.DependentProduct.sum_congr
        intro index
        cases (List.DependentProduct.get source.isolation.tracks locations.refinements index).side <;> rfl

/-- Strict rational radial apartness supplies the actual linear factor margin. -/
private def point_margin (point : Canonical) (apart : point.normSq ≠ 1) :
    Certificate (LinearFactor.linearFactor point) :=
  if inside : point.normSq < 1 then Certificate.linearInside point inside
  else Certificate.linearOutside point (lt_of_le_of_ne (le_of_not_gt inside) (Ne.symm apart))

/-- The independently computed linear raw reading matches its strict rational inside indicator. -/
private theorem point_reading (point : Canonical) (apart : point.normSq ≠ 1)
    (paths : Boundary.Substitutions (LinearFactor.linearFactor point)) :
    Winding.Circle.raw paths = 4 * ((if point.normSq < 1 then 1 else 0 : Nat) : Int) := by
  if inside : point.normSq < 1 then
    rw [if_pos inside]
    exact Winding.Circle.raw_linearInside point inside paths
  else
    rw [if_neg inside]
    exact Winding.Circle.raw_linearOutside point (lt_of_le_of_ne (le_of_not_gt inside) (Ne.symm apart)) paths

/-- The retained automatic higher-factor approximation proves the full independent argument principle.

The source is the same original squarefree factor and every counted owner is
from its retained complete isolation. The sufficient approximation is built
from those same radial locations, with no caller roots, tolerances or fuel.
Its rational centers are used only in the finite perturbation and product
proof; none is identified with an algebraic root.
-/
public theorem Approximation.raw_eq_insideCount {polynomial : CoefficientPolynomial}
    {clearance : Certificate polynomial} {source : FTA.Squarefree.BoxResult polynomial}
    {locations : HigherLocations clearance source} (approximation : Approximation locations)
    (paths : Boundary.Substitutions polynomial) :
    Winding.Circle.raw paths = 4 * (locations.insideCount : Int) := by
  let points := approximation.samples.points
  let margins := fun point member => point_margin point (points_apart approximation.samples point member)
  let monicPaths := Boundary.Substitutions.prepare (Split.splitPolynomial points)
  let targetPaths := Boundary.Substitutions.prepare approximation.target
  have monicReading := Winding.Circle.raw_splitProduct
    (fun point => if point.normSq < 1 then 1 else 0) points margins
    (fun point member => point_reading point (points_apart approximation.samples point member)) monicPaths
  have targetEq : approximation.target =
      DensePolynomial.scale polynomial.leadingCoeff (Split.splitPolynomial points) := by
    rw [approximation.target_eq, approximation.monic_eq]
  let scaledPaths : Boundary.Substitutions
      (DensePolynomial.scale polynomial.leadingCoeff (Split.splitPolynomial points)) := targetEq ▸ targetPaths
  have scaling := Winding.Circle.raw_scale (Certificate.splitProduct points margins) polynomial.leadingCoeff
    (DensePolynomial.leadingCoeff_ne_zero clearance.nonzero) monicPaths scaledPaths
  calc
    Winding.Circle.raw paths = Winding.Circle.raw targetPaths := (approximation.raw_eq paths targetPaths).symm
    _ = Winding.Circle.raw scaledPaths := (Winding.Circle.raw_transport targetEq targetPaths).symm
    _ = Winding.Circle.raw monicPaths := scaling
    _ = 4 * ((points.foldr (fun point total => (if point.normSq < 1 then 1 else 0) + total) 0 : Nat) : Int) :=
      monicReading
    _ = 4 * (locations.insideCount : Int) := congrArg (fun count : Nat => 4 * (count : Int))
      (inside_count approximation.samples)

end Purelib.RootIsolation.Multiplicity.Circle.CenterProduct

namespace Purelib.RootIsolation.Multiplicity.Circle

open Purelib.Data
open Purelib.Polynomial
open Purelib.RationalFunctions.Curve.Canonical.Circle
open Dense.Gaussian
open Basic.CanonicalCoefficients (CoefficientPolynomial)
open Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Clearance.Circle (Certificate)
open Dense.Gaussian.Multiplicity.Basis.Coprime.Side (PositiveSideInput)
open Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput (FactorObservation)
open Dense.Gaussian.Multiplicity.Basis.Context.Basic (PositiveContext)
open Roots.Certificate (ExactRoot)

/-- The original exact root's stored strict location supplies its linear-factor margin. -/
@[expose] public def ExactLocation.linearMargin {polynomial : CoefficientPolynomial}
    {clearance : Certificate polynomial} {root : ExactRoot polynomial} :
    ExactLocation clearance root → Certificate (LinearFactor.linearFactor root.point)
  | .inside holds => Certificate.linearInside root.point holds
  | .outside holds => Certificate.linearOutside root.point holds

/-- The independent raw winding of the same exact rational linear factor counts its stored strict side. -/
public theorem ExactLocation.raw_linear {polynomial : CoefficientPolynomial}
    {clearance : Certificate polynomial} {root : ExactRoot polynomial} (location : ExactLocation clearance root)
    (paths : Boundary.Substitutions (LinearFactor.linearFactor root.point)) :
    Winding.Circle.raw paths = 4 * (location.insideCount : Int) := by
  cases location with
  | inside inside => exact Winding.Circle.raw_linearInside root.point inside paths
  | outside outside => exact Winding.Circle.raw_linearOutside root.point outside paths

/-- The original degree-one factor's independent raw winding counts its same retained exact root. -/
public theorem ExactLocation.raw_eq_insideCount {polynomial : CoefficientPolynomial}
    {clearance : Certificate polynomial} {root : ExactRoot polynomial} (location : ExactLocation clearance root)
    (degree : polynomial.natDegree = 1) (paths : Boundary.Substitutions polynomial) :
    Winding.Circle.raw paths = 4 * (location.insideCount : Int) := by
  let linearPaths := Boundary.Substitutions.prepare (LinearFactor.linearFactor root.point)
  let scaledPaths := Boundary.Substitutions.prepare
    (DensePolynomial.scale polynomial.leadingCoeff (LinearFactor.linearFactor root.point))
  have comparison := Winding.Circle.Comparison.raw_eq_of_eval_eq clearance paths scaledPaths
    (fun point _ => by
      rw [DensePolynomial.eval_scale, LinearFactor.linearFactor_eval]
      exact (Roots.Linear.eval_eq_leading_mul_sub degree root.point root.root point).symm)
  calc
    Winding.Circle.raw paths = Winding.Circle.raw scaledPaths := comparison.symm
    _ = Winding.Circle.raw linearPaths := Winding.Circle.raw_scale location.linearMargin
      polynomial.leadingCoeff (DensePolynomial.leadingCoeff_ne_zero clearance.nonzero) linearPaths scaledPaths
    _ = 4 * (location.insideCount : Int) := location.raw_linear linearPaths

/-- The retained additional approximation required by one same original factor observation.

Exact rational observations need no extra samples. A higher observation keeps
the actual sufficient center-product approximation of its same already stored
radial locations; it never re-isolates or replaces that original observation.
-/
@[expose] public def ObservationArgument {source opposite : CoefficientPolynomial}
    {input : PositiveSideInput source opposite} {context : PositiveContext input.entries}
    {clearance : Certificate context.focus.part.polynomial} :
    (observation : FactorObservation input context) → Locations clearance observation → Type
  | .exact _ _ _, _ => PUnit
  | .higher _ _, locations => CenterProduct.Approximation locations

namespace ObservationArgument

/-- Retain the actual sufficient approximation of the same higher locations, or the empty exact-root payload. -/
@[expose] public def prepare {source opposite : CoefficientPolynomial}
    {input : PositiveSideInput source opposite} {context : PositiveContext input.entries}
    {clearance : Certificate context.focus.part.polynomial} :
    (observation : FactorObservation input context) → (locations : Locations clearance observation) →
    ObservationArgument observation locations
  | .exact _ _ _, _ => PUnit.unit
  | .higher _ _, locations => CenterProduct.Approximation.prepare locations

/-- The same stored exact or higher original factor has independent winding equal to its retained inside count. -/
public theorem raw_eq_insideCount {source opposite : CoefficientPolynomial}
    {input : PositiveSideInput source opposite} {context : PositiveContext input.entries}
    {clearance : Certificate context.focus.part.polynomial} (observation : FactorObservation input context)
    (locations : Locations clearance observation) (argument : ObservationArgument observation locations)
    (paths : Boundary.Substitutions context.focus.part.polynomial) :
    Winding.Circle.raw paths = 4 * (Locations.insideCount observation locations : Int) := by
  cases observation with
  | exact root degree oppositeAtRoot => exact ExactLocation.raw_eq_insideCount locations degree paths
  | higher boxes degree => exact CenterProduct.Approximation.raw_eq_insideCount argument paths

end ObservationArgument
namespace Factor

/-- The additional argument payload of this same stored original factor row. -/
@[expose] public def Argument {source opposite : CoefficientPolynomial} {clearance : Certificate source}
    {input : PositiveSideInput source opposite} {context : PositiveContext input.entries}
    {expected : FactorObservation input context} (factor : Factor clearance input context expected) : Type :=
  ObservationArgument factor.observation factor.locations

namespace Argument

/-- Construct the argument payload from this same original stored observation and its radial locations. -/
@[expose] public def prepare {source opposite : CoefficientPolynomial} {clearance : Certificate source}
    {input : PositiveSideInput source opposite} {context : PositiveContext input.entries}
    {expected : FactorObservation input context} (factor : Factor clearance input context expected) : factor.Argument :=
  ObservationArgument.prepare factor.observation factor.locations

/-- This same original factor row has independent winding equal to its retained inside count. -/
public theorem raw_eq_insideCount {source opposite : CoefficientPolynomial} {clearance : Certificate source}
    {input : PositiveSideInput source opposite} {context : PositiveContext input.entries}
    {expected : FactorObservation input context} {factor : Factor clearance input context expected}
    (argument : factor.Argument) (paths : Boundary.Substitutions context.focus.part.polynomial) :
    Winding.Circle.raw paths = 4 * (factor.insideCount : Int) :=
  ObservationArgument.raw_eq_insideCount factor.observation factor.locations argument paths

end Argument
end Factor

set_option genInjectivity false in
/-- Stored sufficient argument payloads for the same original positive inventory.

Each row keeps its actual higher center-product approximation, including the
original further samples, cached split polynomial and synthetic divisions.
Exact rows retain an empty payload. Every row is constructed from the same
already stored original observation and radial locations.
-/
public structure PositiveArgument {source opposite : CoefficientPolynomial} {clearance : Certificate source}
    {input : PositiveSideInput source opposite}
    {family : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput.PositiveFamily input}
    (inventory : PositiveInventory clearance input family) where
  /-- One stored argument payload per original context occurrence. -/
  factors : List.DependentProduct input.contexts (fun index => (inventory.factorAt index).Argument)
  /-- The payloads are the actual materialized same-row constructors. -/
  factors_eq : factors = List.DependentProduct.ofFn input.contexts (fun index =>
    Factor.Argument.prepare (inventory.factorAt index))

constructive_injectivity PositiveArgument

namespace PositiveArgument

open Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput (PositiveFamily)
open Dense.Gaussian.Multiplicity.Basis

/-- Retain checked argument payloads at the same original inventory contexts without requesting new samples. -/
@[expose] public def ofFactors {source opposite : CoefficientPolynomial} {clearance : Certificate source}
    {input : PositiveSideInput source opposite} {family : PositiveFamily input}
    (inventory : PositiveInventory clearance input family)
    (factors : List.DependentProduct input.contexts (fun index => (inventory.factorAt index).Argument))
    (factorsEq : factors = List.DependentProduct.ofFn input.contexts (fun index =>
      Factor.Argument.prepare (inventory.factorAt index))) : PositiveArgument inventory :=
  { factors, factors_eq := factorsEq }

/-- Materialize each same-row sufficient argument payload once without rebuilding its original observation. -/
@[expose] public def prepare {source opposite : CoefficientPolynomial} {clearance : Certificate source}
    {input : PositiveSideInput source opposite} {family : PositiveFamily input}
    (inventory : PositiveInventory clearance input family) : PositiveArgument inventory :=
  let factors := List.DependentProduct.ofFn input.contexts (fun index =>
    Factor.Argument.prepare (inventory.factorAt index))
  ofFactors inventory factors rfl

/-- Checked complete argument entries restore the same original positive argument producer. -/
public theorem ofFactors_eq_prepare {source opposite : CoefficientPolynomial} {clearance : Certificate source}
    {input : PositiveSideInput source opposite} {family : PositiveFamily input}
    (inventory : PositiveInventory clearance input family)
    (factors : List.DependentProduct input.contexts (fun index => (inventory.factorAt index).Argument))
    (factorsEq : factors = List.DependentProduct.ofFn input.contexts (fun index =>
      Factor.Argument.prepare (inventory.factorAt index))) :
    ofFactors inventory factors factorsEq = prepare inventory := by
  cases factorsEq
  rfl

/-- Restore the complete same-context original argument from its retained payload product. -/
public theorem restore {source opposite : CoefficientPolynomial} {clearance : Certificate source}
    {input : PositiveSideInput source opposite} {family : PositiveFamily input}
    {inventory : PositiveInventory clearance input family} (argument : PositiveArgument inventory) :
    argument = prepare inventory := by
  cases argument with
  | mk factors factorsEq => exact ofFactors_eq_prepare inventory factors factorsEq

/-- Read the same stored argument at its original bounded context occurrence. -/
@[expose] public def argumentAt {source opposite : CoefficientPolynomial} {clearance : Certificate source}
    {input : PositiveSideInput source opposite} {family : PositiveFamily input}
    {inventory : PositiveInventory clearance input family} (argument : PositiveArgument inventory)
    (index : Fin input.contexts.length) : (inventory.factorAt index).Argument :=
  List.DependentProduct.get input.contexts argument.factors index

/-- Stored argument lookup returns its complete same-row constructor result. -/
public theorem argumentAt_eq {source opposite : CoefficientPolynomial} {clearance : Certificate source}
    {input : PositiveSideInput source opposite} {family : PositiveFamily input}
    {inventory : PositiveInventory clearance input family} (argument : PositiveArgument inventory)
    (index : Fin input.contexts.length) :
    argument.argumentAt index = Factor.Argument.prepare (inventory.factorAt index) :=
  (congrArg (fun entries => List.DependentProduct.get input.contexts entries index) argument.factors_eq).trans
    (List.DependentProduct.get_ofFn _ _ index)

/-- Preserve the natural entry occurrence while transporting its same context-count bound. -/
private def contextIndex {source opposite : CoefficientPolynomial} (input : PositiveSideInput source opposite)
    (index : Fin input.entries.length) : Fin input.contexts.length :=
  ⟨index.val, input.contexts_length.symm ▸ index.isLt⟩

/-- The retained context focuses the same original entry at this natural occurrence. -/
private theorem contextFocus {source opposite : CoefficientPolynomial} (input : PositiveSideInput source opposite)
    (index : Fin input.entries.length) :
    (input.contexts.get (contextIndex input index)).focus = input.entries.get index := by
  have focus := Context.Basic.positiveContexts_get_focus input.entries (contextIndex input index)
  have same : Fin.cast (Context.Basic.positiveContexts_length input.entries) (contextIndex input index) = index :=
    Fin.ext rfl
  rw [same] at focus
  exact focus

/-- Read the original stored factor margin under its same original entry identity. -/
private def entryMargin {source opposite : CoefficientPolynomial} {clearance : Certificate source}
    {input : PositiveSideInput source opposite} {family : PositiveFamily input}
    (inventory : PositiveInventory clearance input family) (index : Fin input.entries.length) :
    Certificate (input.entries.get index).part.polynomial :=
  congrArg (fun entry : Positive.PositiveEntry => entry.part.polynomial) (contextFocus input index) ▸
    (inventory.factorAt (contextIndex input index)).margin.toCertificate

/-- Transport the actual stored factor reading along its same original entry identity. -/
private theorem entryReading {source opposite : CoefficientPolynomial} {clearance : Certificate source}
    {input : PositiveSideInput source opposite} {family : PositiveFamily input}
    {inventory : PositiveInventory clearance input family} (argument : PositiveArgument inventory)
    (index : Fin input.entries.length) (paths : Boundary.Substitutions (input.entries.get index).part.polynomial) :
    Winding.Circle.raw paths = 4 * ((inventory.factorAt (contextIndex input index)).insideCount : Int) := by
  have same := congrArg (fun entry : Positive.PositiveEntry => entry.part.polynomial) (contextFocus input index)
  let originalPaths : Boundary.Substitutions (input.contexts.get (contextIndex input index)).focus.part.polynomial :=
    same.symm ▸ paths
  calc
    Winding.Circle.raw paths = Winding.Circle.raw originalPaths :=
      (Winding.Circle.raw_transport same.symm paths).symm
    _ = 4 * ((inventory.factorAt (contextIndex input index)).insideCount : Int) :=
      Factor.Argument.raw_eq_insideCount (argument.argumentAt (contextIndex input index)) originalPaths

/-- The entry-indexed weighted fold is exactly the same retained original inventory fold. -/
private theorem entryCounts {source opposite : CoefficientPolynomial} {clearance : Certificate source}
    {input : PositiveSideInput source opposite} {family : PositiveFamily input}
    (inventory : PositiveInventory clearance input family) :
    (List.ofFn (fun index : Fin input.entries.length =>
      (input.entries.get index).multiplicity * (inventory.factorAt (contextIndex input index)).insideCount)).foldr
        Nat.add 0 = inventory.insideCount := by
  let weights := fun index : Fin input.contexts.length =>
    (input.contexts.get index).focus.multiplicity * (inventory.factorAt index).insideCount
  have same : List.ofFn (fun index : Fin input.entries.length =>
      (input.entries.get index).multiplicity * (inventory.factorAt (contextIndex input index)).insideCount) =
      List.ofFn weights := by
    calc
      _ = List.ofFn (fun index : Fin input.entries.length => weights (Fin.cast input.contexts_length.symm index)) := by
        apply List.OfFn.Basic.ofFn_congr
        intro index
        have sameIndex : contextIndex input index = Fin.cast input.contexts_length.symm index := Fin.ext rfl
        rw [← sameIndex]
        exact congrArg (fun entry : Positive.PositiveEntry =>
          entry.multiplicity * (inventory.factorAt (contextIndex input index)).insideCount)
          (contextFocus input index).symm
      _ = List.ofFn weights := List.OfFn.Basic.ofFn_cast input.contexts_length.symm weights
  calc
    _ = (List.ofFn weights).foldr Nat.add 0 := congrArg (fun values => values.foldr Nat.add 0) same
    _ = inventory.insideCount := by
      unfold PositiveInventory.insideCount
      exact List.DependentProduct.sum_ofFn input.contexts inventory.factors
        (fun index factor => (input.contexts.get index).focus.multiplicity * factor.insideCount)
        (fun value => value)

/-- The independent original polynomial reading equals its complete original multiplicity-weighted inside count.

The exact original positive decomposition contributes its own nonzero constant
unit, which has zero winding. Every original factor reading is supplied by
its same stored exact or higher argument payload and carries its original
natural multiplicity in the ordered dense product.
-/
public theorem raw_eq_insideCount {source opposite : CoefficientPolynomial} {clearance : Certificate source}
    {input : PositiveSideInput source opposite} {family : PositiveFamily input}
    {inventory : PositiveInventory clearance input family} (argument : PositiveArgument inventory)
    (paths : Boundary.Substitutions source) :
    Winding.Circle.raw paths = 4 * (inventory.insideCount : Int) := by
  let counts := fun index : Fin input.entries.length =>
    (inventory.factorAt (contextIndex input index)).insideCount
  let unit := Positive.unitValue input.preprocessing.decomposition.multiplicityBasis.entries
  let productPaths := Boundary.Substitutions.prepare (Product.positivePolynomial input.entries)
  let scaledPaths := Boundary.Substitutions.prepare
    (DensePolynomial.scale unit (Product.positivePolynomial input.entries))
  have comparison := Winding.Circle.Comparison.raw_eq_of_eval_eq clearance paths scaledPaths
    (fun point _ => by
      rw [DensePolynomial.eval_scale]
      exact ((DensePolynomial.eval_normalize source point).symm.trans
        (input.preprocessing.decomposition.eval_positivePolynomial point)).symm)
  have product := Winding.Circle.raw_positiveProduct input.entries (entryMargin inventory) counts
    (fun index => entryReading argument index) productPaths
  calc
    Winding.Circle.raw paths = Winding.Circle.raw scaledPaths := comparison.symm
    _ = Winding.Circle.raw productPaths := Winding.Circle.raw_scale
      (Certificate.positiveProduct input.entries (entryMargin inventory)) unit
      input.preprocessing.decomposition.multiplicityUnit_ne_zero productPaths scaledPaths
    _ = 4 * (((List.ofFn (fun index : Fin input.entries.length =>
        (input.entries.get index).multiplicity * counts index)).foldr Nat.add 0 : Nat) : Int) := product
    _ = 4 * (inventory.insideCount : Int) := congrArg (fun count : Nat => 4 * (count : Int)) (entryCounts inventory)

end PositiveArgument

/-- The retained argument payload of the same original constant or positive side result. -/
@[expose] public def SideArgument {source opposite : CoefficientPolynomial} {clearance : Certificate source} :
    (side : Side.Basic.SideResult source opposite) → SideLocations clearance side → Type
  | .constant _ _ _, _ => PUnit
  | .positive _ _, inventory => PositiveArgument inventory

namespace SideArgument

/-- Materialize the argument payload from the same already stored original side and radial inventory. -/
@[expose] public def prepare {source opposite : CoefficientPolynomial} {clearance : Certificate source} :
    (side : Side.Basic.SideResult source opposite) → (locations : SideLocations clearance side) →
    SideArgument side locations
  | .constant _ _ _, _ => PUnit.unit
  | .positive _ _, inventory => PositiveArgument.prepare inventory

/-- The same original constant or positive source has independent winding equal to its complete inside count. -/
public theorem raw_eq_insideCount {source opposite : CoefficientPolynomial} {clearance : Certificate source}
    (side : Side.Basic.SideResult source opposite) (locations : SideLocations clearance side)
    (argument : SideArgument side locations) (paths : Boundary.Substitutions source) :
    Winding.Circle.raw paths = 4 * (SideLocations.insideCount side locations : Int) := by
  cases side with
  | constant sourceNonzero degreeZero oppositeNonzero =>
      let constantPaths := Boundary.Substitutions.prepare (DensePolynomial.constant source.leadingCoeff)
      have same := DensePolynomial.normalize_eq_constant_leadingCoeff_of_degree_zero sourceNonzero degreeZero
      have comparison := Winding.Circle.Comparison.raw_eq_of_eval_eq clearance paths constantPaths
        (fun point _ =>
          (congrArg (fun polynomial : CoefficientPolynomial => polynomial.eval point) same).symm.trans
            (DensePolynomial.eval_normalize source point))
      change Winding.Circle.raw paths = 0
      exact comparison.symm.trans (Winding.Circle.raw_constant source.leadingCoeff constantPaths)
  | positive input family => exact PositiveArgument.raw_eq_insideCount argument paths

end SideArgument

namespace Inventory

/-- The sufficient argument data indexed by this same original automatically constructed radial inventory. -/
public abbrev Argument {source : CoefficientPolynomial} {clearance : Certificate source}
    (inventory : Inventory clearance) : Type := SideArgument inventory.side inventory.locations

namespace Argument

/-- Build the argument payload from the same original side, cached observations and stored radial refinements. -/
@[expose] public def prepare {source : CoefficientPolynomial} {clearance : Certificate source}
    (inventory : Inventory clearance) : inventory.Argument :=
  SideArgument.prepare inventory.side inventory.locations

/-- The original source's independent raw winding is four times this same complete automatic inside count. -/
public theorem raw_eq_insideCount {source : CoefficientPolynomial} {clearance : Certificate source}
    {inventory : Inventory clearance} (argument : inventory.Argument) (paths : Boundary.Substitutions source) :
    Winding.Circle.raw paths = 4 * (inventory.insideCount : Int) :=
  SideArgument.raw_eq_insideCount inventory.side inventory.locations argument paths

end Argument
end Inventory

end Purelib.RootIsolation.Multiplicity.Circle
