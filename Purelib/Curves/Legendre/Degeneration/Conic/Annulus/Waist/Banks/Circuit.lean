module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Banks.Reversal
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Transport
import Purelib.Curves.Legendre.Degeneration.UnitRoot.Transport
import Purelib.Curves.Legendre.Degeneration.Conic
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Geometry.Rational.Box.Refinement
public import Purelib.Data.Fin.Bijection.Transposition
import Purelib.Approximation.Gaussian.Equivalence
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# The original curved waist circuit with retained signed cofactor traces

Each of the four original rational quarters retains its actual accepted root
advances and cached original cubic endpoint channels. Internally derived
operational seam comparisons assemble them in their geometric order. The two
real branch endpoints carry the explicit two-sheet switches.

This is a curved circuit owner. An affine lifted-cycle or canonical A/B owner
additionally requires a complete trace/refinement certificate, oriented cut
attachment and finite homotopy comparison. Corrected B-prefix and infinity
occurrences must remain those of the original canonical period owner.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Banks

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
  (ownerRootName ownerRootName_castOwnerParameter)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Geometry.Rational
open Purelib.RootIsolation

namespace Leg

variable (site : Fin 2) (parameter : Canonical) (quarter : UnitCircuitQuarter)
variable (regular : parameter ≠ criticalValue site)
variable (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational))

/-- The original complete preparation of this same curved quarter. -/
@[expose] def Preparation := Transport.Quarter site parameter quarter regular bound

/-- The original source conic point of this curved quarter. -/
@[expose] def sourcePoint : Point site parameter := point site parameter (direction quarter 0) regular bound

/-- The original target conic point of this curved quarter. -/
@[expose] def targetPoint : Point site parameter := point site parameter (direction quarter 1) regular bound

/-- The original complete source cofactor owner at the retained source conic point. -/
@[expose] def SourceOwner : Type := Lift.CofactorOwner (sourcePoint site parameter quarter regular bound)

/-- The original complete target cofactor owner at the retained target conic point. -/
@[expose] def TargetOwner : Type := Lift.CofactorOwner (targetPoint site parameter quarter regular bound)

/-- The original cubic source lift retaining this exact source point and cofactor owner. -/
@[expose] def SourceLift (unit : SourceOwner site parameter quarter regular bound) :=
  Lift (sourcePoint site parameter quarter regular bound) unit

/-- The original cubic target lift retaining this exact target point and cofactor owner. -/
@[expose] def TargetLift (unit : TargetOwner site parameter quarter regular bound) :=
  Lift (targetPoint site parameter quarter regular bound) unit

/-- The source cofactor cache is the original prepared owner transported by the same original source-point equality. -/
@[expose] def SourceOwnerEquation (transport : Preparation site parameter quarter regular bound)
    (unit : SourceOwner site parameter quarter regular bound) : Prop :=
  unit = SquareRoot.Owner.Transport.castOwnerParameter (transport.data.point_eq 0) transport.prepared.source

/-- The target cofactor cache is the original advanced finish owner of this same quarter preparation. -/
@[expose] def TargetOwnerEquation (transport : Preparation site parameter quarter regular bound)
    (unit : TargetOwner site parameter quarter regular bound) : Prop :=
  unit = transport.finishUnit

/-- The actual cached cubic source agrees with the original independent signed source channel. -/
@[expose] def SourceComparison (unit : SourceOwner site parameter quarter regular bound)
    (source : SourceLift site parameter quarter regular bound unit) : Type :=
  NamedEquivalent source.value.name (lift site parameter (direction quarter 0) regular bound).value.name

/-- The actual cached cubic target agrees with the original independent signed target channel. -/
@[expose] def TargetComparison (unit : TargetOwner site parameter quarter regular bound)
    (target : TargetLift site parameter quarter regular bound unit) : Type :=
  NamedEquivalent target.value.name (lift site parameter (direction quarter 1) regular bound).value.name

end Leg

section

attribute [local irreducible] Leg.Preparation Leg.sourcePoint Leg.targetPoint
  Leg.SourceOwner Leg.TargetOwner Leg.SourceLift Leg.TargetLift
  Leg.SourceOwnerEquation Leg.TargetOwnerEquation Leg.SourceComparison Leg.TargetComparison
  Lift.cofactor Lift.CofactorOwner Lift.CofactorRoot Lift.Coordinates
  Lift.RootEquation Lift.ValueEquation Lift.SquareComparison
  Lift.CoordinateRootEquation Lift.PlusComparison Lift.MinusComparison

set_option genInjectivity false in
/-- One original curved quarter with its actual cofactor trace and cached original cubic endpoint lifts.

The independent signed patch channels remain comparison inputs at both ends.
The retained actual trace uses its own original prepared source and advanced
finish owners; both endpoint comparisons are derived from that preparation.
-/
structure Leg (site : Fin 2) (parameter : Canonical) (quarter : UnitCircuitQuarter)
    (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational)) where
  /-- The original entire curved quarter preparation, with actual accepted cofactor advances. -/
  transport : Leg.Preparation site parameter quarter regular bound
  /-- The complete original prepared source transported to the original cubic cofactor index. -/
  sourceUnit : Leg.SourceOwner site parameter quarter regular bound
  /-- The source cache is the exact transported original prepared owner. -/
  sourceUnit_eq : Leg.SourceOwnerEquation site parameter quarter regular bound transport sourceUnit
  /-- The original source cubic lift built on that retained actual source owner. -/
  source : Leg.SourceLift site parameter quarter regular bound sourceUnit
  /-- The complete original advanced finish owner retained as a cache. -/
  targetUnit : Leg.TargetOwner site parameter quarter regular bound
  /-- The finish cache is the actual advanced finish transported by the same original quarter preparation. -/
  targetUnit_eq : Leg.TargetOwnerEquation site parameter quarter regular bound transport targetUnit
  /-- The original finish cubic lift built on that actual retained advanced owner. -/
  target : Leg.TargetLift site parameter quarter regular bound targetUnit
  /-- The actual source cubic channel agrees with its original independent signed patch channel. -/
  source_agrees : Leg.SourceComparison site parameter quarter regular bound sourceUnit source
  /-- The actual finish cubic channel agrees with its original independent signed patch channel. -/
  target_agrees : Leg.TargetComparison site parameter quarter regular bound targetUnit target

constructive_injectivity Leg

end

namespace Leg

/-- Build a whole curved leg while acquiring each actual endpoint cofactor certificate once. -/
def ofQuarter {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
    {regular : parameter ≠ criticalValue site}
    {bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational)}
    (actual : Transport.Quarter site parameter quarter regular bound) : Leg site parameter quarter regular bound := by
  let sourceUnit := SquareRoot.Owner.Transport.castOwnerParameter (actual.data.point_eq 0) actual.prepared.source
  let source := Lift.ofUnit (point site parameter (direction quarter 0) regular bound) sourceUnit
  let independent := UnitRoot.owner site (point site parameter (direction quarter 0) regular bound).base
    (point_inside _ _ _ regular bound)
  let atPath := SquareRoot.Owner.Transport.castOwnerParameter (actual.data.point_eq 0).symm independent
  have refines : atPath.track.initial.box.Refines actual.data.source.track.initial.box := by
    rewrite [SquareRoot.Owner.Transport.castOwnerParameter_initial_box, UnitRoot.owner_initial_box,
      actual.data.source_eq, UnitRoot.Transport.source_box]
    exact Box.refines_refl _
  have independentAgreement := actual.data.path.firstRetained 0 (by decide +kernel) atPath refines
  have sourceName := congrArg (fun owner : Owner (actual.data.path.point 0) =>
    ownerRootName owner.parameterNonzero owner) actual.prepared.source_eq
  have atPathAgreement := NamedEquivalent.transport sourceName.symm rfl independentAgreement
  have unitAgreement := NamedEquivalent.transport
    (ownerRootName_castOwnerParameter (actual.data.point_eq 0) actual.prepared.source).symm
    (ownerRootName_castOwnerParameter (actual.data.point_eq 0).symm independent) atPathAgreement
  let original := lift site parameter (direction quarter 0) regular bound
  have sourceAgreement : NamedEquivalent source.value.name original.value.name :=
    Lift.value_agrees source original (NamedEquivalent.transport source.unitRoot_name.symm
      original.unitRoot_name.symm unitAgreement)
  let targetUnit := actual.finishUnit
  let target := actual.finishLift
  exact
    { transport := actual
      sourceUnit := sourceUnit
      sourceUnit_eq := rfl
      source := source
      targetUnit := targetUnit
      targetUnit_eq := rfl
      target := target
      source_agrees := sourceAgreement
      target_agrees := actual.finishLift_agrees }

/-- Construct the original whole-quarter cofactor trace and its two actual cubic endpoint caches. -/
def build (site : Fin 2) (parameter : Canonical) (quarter : UnitCircuitQuarter)
    (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational)) :
    Leg site parameter quarter regular bound :=
  ofQuarter (Transport.Quarter.build site parameter quarter regular bound)

/-- The actual retained source lift carries the original signed window required by residual-controlled integration. -/
theorem source_signed {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
    {regular : parameter ≠ criticalValue site}
    {bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational)}
    (leg : Leg site parameter quarter regular bound) :
    leg.source.unitOwner.track.initial.box.Refines (UnitRoot.box site) := by
  rewrite [leg.source.unitOwner_eq, leg.sourceUnit_eq,
    SquareRoot.Owner.Transport.castOwnerParameter_initial_box, leg.transport.prepared.source_eq,
    leg.transport.data.path.first_box, leg.transport.data.source_eq, UnitRoot.Transport.source_box]
  exact Box.refines_refl _

end Leg

namespace Circuit

variable (site : Fin 2) (parameter : Canonical)
variable (regular : parameter ≠ criticalValue site)
variable (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational))

/-- The original geometric leg at one retained quarter of the same waist circuit. -/
@[expose] def QuarterLeg (quarter : UnitCircuitQuarter) := Leg site parameter quarter regular bound

/-- The actual cached target-to-source channel comparison between two original circuit legs. -/
@[expose] def Seam {firstQuarter lastQuarter : UnitCircuitQuarter}
    (first : QuarterLeg site parameter regular bound firstQuarter)
    (last : QuarterLeg site parameter regular bound lastQuarter) : Type :=
  NamedEquivalent first.target.value.name last.source.value.name

end Circuit

section

attribute [local irreducible] Circuit.QuarterLeg Circuit.Seam
  Leg.Preparation Leg.sourcePoint Leg.targetPoint
  Leg.SourceOwner Leg.TargetOwner Leg.SourceLift Leg.TargetLift
  Leg.SourceOwnerEquation Leg.TargetOwnerEquation Leg.SourceComparison Leg.TargetComparison
  Lift.cofactor Lift.CofactorOwner Lift.CofactorRoot Lift.Coordinates
  Lift.RootEquation Lift.ValueEquation Lift.SquareComparison
  Lift.CoordinateRootEquation Lift.PlusComparison Lift.MinusComparison

set_option genInjectivity false in
/-- The four original curved quarters in geometric order, retaining actual cofactor traces and operational cubic seams.

This owner is independent of a homology action or matrix. Its two opposite
banks are the original first/second and third/fourth quarters. Endpoint equality
is certified on the actual cached cubic channels, including both branch points.
-/
structure Circuit (site : Fin 2) (parameter : Canonical) (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational)) where
  /-- The retained original first curved quarter, leaving the moving branch. -/
  first : Circuit.QuarterLeg site parameter regular bound .first
  /-- The retained original second curved quarter, reaching the fixed branch. -/
  second : Circuit.QuarterLeg site parameter regular bound .second
  /-- The retained original third curved quarter, leaving the fixed branch on the opposite bank. -/
  third : Circuit.QuarterLeg site parameter regular bound .third
  /-- The retained original fourth curved quarter, returning to the moving branch. -/
  fourth : Circuit.QuarterLeg site parameter regular bound .fourth
  /-- The actual first finish agrees with the actual second source. -/
  first_second : Circuit.Seam site parameter regular bound first second
  /-- The actual second finish agrees with the actual third source at the fixed branch. -/
  second_third : Circuit.Seam site parameter regular bound second third
  /-- The actual third finish agrees with the actual fourth source. -/
  third_fourth : Circuit.Seam site parameter regular bound third fourth
  /-- The actual fourth finish agrees with the actual first source at the moving branch. -/
  fourth_first : Circuit.Seam site parameter regular bound fourth first

constructive_injectivity Circuit

end

namespace Circuit

/-- Construct the entire original curved circuit, caching each original quarter and endpoint lift once. -/
def build (site : Fin 2) (parameter : Canonical) (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational)) :
    Circuit site parameter regular bound := by
  let first := Leg.build site parameter .first regular bound
  let second := Leg.build site parameter .second regular bound
  let third := Leg.build site parameter .third regular bound
  let fourth := Leg.build site parameter .fourth regular bound
  have seams := values_join site parameter regular bound
  have join {firstQuarter lastQuarter : UnitCircuitQuarter}
      (first : Leg site parameter firstQuarter regular bound) (last : Leg site parameter lastQuarter regular bound)
      (equal : (lift site parameter (direction firstQuarter 1) regular bound).value =
        (lift site parameter (direction lastQuarter 0) regular bound).value) :
      NamedEquivalent first.target.value.name last.source.value.name :=
    first.target_agrees.trans
      (NamedEquivalent.transport (congrArg (fun value => value.name) equal).symm rfl last.source_agrees.symm)
  exact
    { first := first
      second := second
      third := third
      fourth := fourth
      first_second := join first second seams.1
      second_third := join second third seams.2.1
      third_fourth := join third fourth seams.2.2.1
      fourth_first := join fourth first seams.2.2.2 }

/-- Select the identical original cached curved quarter by its original finite quarter label. -/
@[expose] def leg {site : Fin 2} {parameter : Canonical} {regular : parameter ≠ criticalValue site}
    {bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational)}
    (circuit : Circuit site parameter regular bound) :
    (quarter : UnitCircuitQuarter) → Leg site parameter quarter regular bound
  | .first => circuit.first
  | .second => circuit.second
  | .third => circuit.third
  | .fourth => circuit.fourth

/-- The bank label used along each of the four original oriented quarter charts. -/
@[expose] def sheet : UnitCircuitQuarter → Fin 2
  | .first => 0
  | .second => 0
  | .third => 1
  | .fourth => 1

/-- The exact branch switch on the original two labelled banks. -/
@[expose] def branchSwitch : Data.Fin.Bijection 2 2 := Data.Fin.Bijection.Transposition.transposition 0 1

/-- The retained fixed-branch switch takes the second quarter's bank to the third quarter's bank. -/
theorem fixed_branch_switch : branchSwitch.forward (sheet .second) = sheet .third :=
  Data.Fin.Bijection.Transposition.swapIndices_left 0 1

/-- The retained moving-branch switch takes the fourth quarter's bank back to the first quarter's bank. -/
theorem moving_branch_switch : branchSwitch.forward (sheet .fourth) = sheet .first :=
  Data.Fin.Bijection.Transposition.swapIndices_right 0 1

/-- The fixed branch switch occurs exactly at the original fixed labelled branch with zero normalized ordinate. -/
theorem fixed_branch_geometry (site : Fin 2) (parameter : Canonical) (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational)) :
    (point site parameter (direction .second 1) regular bound).base =
        Paths.branchPoint parameter (fixedLabel site) ∧
      (point site parameter (direction .second 1) regular bound).ordinate = 0 ∧
      (point site parameter (direction .third 0) regular bound).base =
        Paths.branchPoint parameter (fixedLabel site) ∧
      (point site parameter (direction .third 0) regular bound).ordinate = 0 :=
  ⟨(forward_endpoints site parameter regular bound).2,
    (forward_endpoint_ordinates site parameter regular bound).2,
    (point_third_start site parameter regular bound).1, (point_third_start site parameter regular bound).2⟩

/-- The moving branch switch closes exactly at the original moving labelled branch with zero normalized ordinate. -/
theorem moving_branch_geometry (site : Fin 2) (parameter : Canonical) (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational)) :
    (point site parameter (direction .fourth 1) regular bound).base = Paths.branchPoint parameter 1 ∧
      (point site parameter (direction .fourth 1) regular bound).ordinate = 0 ∧
      (point site parameter (direction .first 0) regular bound).base = Paths.branchPoint parameter 1 ∧
      (point site parameter (direction .first 0) regular bound).ordinate = 0 := by
  have seam := (points_join site parameter regular bound).2.2.2
  have source := point_first_start site parameter regular bound
  exact ⟨(congrArg Point.base seam).trans source.1,
    (congrArg Point.ordinate seam).trans source.2, source.1, source.2⟩

end Circuit

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Banks
