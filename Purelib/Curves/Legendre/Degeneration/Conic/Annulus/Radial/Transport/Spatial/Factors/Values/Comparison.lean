module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Values
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Budgets
import Purelib.Riemann.Topology.SquareRootContinuationChain.Exact.Transport
import Purelib.Riemann.RootContinuation.FixedRootBoxBudget
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Gaussian.Norm.Basic

/-! # Signed comparison of retained factor products in one source square

Both complete original Values caches remain inputs. The original normalized
Seed and cofactor Budget compare their actual factor Owners by retained box
refinements. The same operation also compares a supplied full product with
an independent original curved Reading whose exact ordinate lies in that
source Seed box. No factor certificate, observation or target is replaced.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Values

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Rational
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Topology
open Purelib.Riemann.Topology.SquareRootContinuationChain.Owner
open Purelib.RootIsolation
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {reference : Fraction.Rational} {referenceInside : FixedRootBoxPath.Inside reference}
variable {source : Transport.Reading actual reference referenceInside} {anchor : Parameter.Anchor source.lift}
variable {budgets : Budgets anchor} {firstPoint lastPoint : Canonical}
variable {firstUnit : SquareRootContinuationChain.Owner ((unitPolynomial site).eval firstPoint)}
variable {firstNormal : SquareRootContinuationChain.Owner (Clearance.normalizedRadicand site parameter firstPoint)}
variable {lastUnit : SquareRootContinuationChain.Owner ((unitPolynomial site).eval lastPoint)}
variable {lastNormal : SquareRootContinuationChain.Owner (Clearance.normalizedRadicand site parameter lastPoint)}

/-- Compare two original full products at the same physical point through the identical source factor budgets.

All four actual factor Owners and both complete certificate/product caches
remain unchanged. The exact point equality transports only the radicand
indices. Each signed relation follows from the supplied original refinement
into the SAME source box, rather than from equality of squares alone.
-/
def equivalent (budgets : Budgets anchor)
    (first : Values site parameter firstPoint firstUnit firstNormal)
    (last : Values site parameter lastPoint lastUnit lastNormal)
    (inside : (sourceBox anchor).Contains firstPoint) (point_eq : firstPoint = lastPoint)
    (firstUnitRefines : firstUnit.track.initial.box.Refines actual.data.source.track.initial.box)
    (firstNormalRefines : firstNormal.track.initial.box.Refines anchor.seed.owner.track.initial.box)
    (lastUnitRefines : lastUnit.track.initial.box.Refines actual.data.source.track.initial.box)
    (lastNormalRefines : lastNormal.track.initial.box.Refines anchor.seed.owner.track.initial.box) :
    NamedEquivalent first.value.name last.value.name := by
  have normalMovement := budgets.normalized_movement inside
  have unitMovement := budgets.unit_movement inside
  rewrite [Norm.Basic.normSq_eq_canonical] at normalMovement unitMovement
  let normalCompared := budgets.normalized.retainedOwnersEquivalentOfEq
    (congrArg (Clearance.normalizedRadicand site parameter) point_eq)
    (budgets.normalized_nonzero inside) normalMovement firstNormal lastNormal
    firstNormalRefines lastNormalRefines
  let unitCompared := budgets.unit.retainedOwnersEquivalentOfEq
    (congrArg (fun point : Canonical => (unitPolynomial site).eval point) point_eq)
    (budgets.unit_nonzero inside) unitMovement firstUnit lastUnit firstUnitRefines lastUnitRefines
  have normalName : NamedEquivalent first.normalRoot.value.name last.normalRoot.value.name := by
    have firstName : first.normalRoot.value.name = ownerRootName firstNormal.parameterNonzero firstNormal := by
      rewrite [first.normalRoot_eq]
      rfl
    have lastName : last.normalRoot.value.name = ownerRootName lastNormal.parameterNonzero lastNormal := by
      rewrite [last.normalRoot_eq]
      rfl
    exact NamedEquivalent.transport firstName.symm lastName.symm normalCompared
  have unitName : NamedEquivalent first.unitRoot.value.name last.unitRoot.value.name := by
    have firstName : first.unitRoot.value.name = ownerRootName firstUnit.parameterNonzero firstUnit := by
      rewrite [first.unitRoot_eq]
      rfl
    have lastName : last.unitRoot.value.name = ownerRootName lastUnit.parameterNonzero lastUnit := by
      rewrite [last.unitRoot_eq]
      rfl
    exact NamedEquivalent.transport firstName.symm lastName.symm unitCompared
  rewrite [first.value_eq, last.value_eq]
  exact Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects
    first.unitRoot.value last.unitRoot.value first.normalRoot.value last.normalRoot.value unitName normalName

/-- Compare an actual retained factor product with an independent original curved Reading on the paid short arc.

The original source Seed proves the normalized sign, including its exact
ordinate-square identity and signed-square containment. The original quarter
cofactor Budget compares the distinct retained cofactor Owners. Their actual
full cubic products are then compared by original product congruence.
-/
def agrees_geometric (budgets : Budgets anchor)
    (values : Values site parameter firstPoint firstUnit firstNormal)
    (inside : (sourceBox anchor).Contains firstPoint)
    (unitRefines : firstUnit.track.initial.box.Refines actual.data.source.track.initial.box)
    (normalRefines : firstNormal.track.initial.box.Refines anchor.seed.owner.track.initial.box)
    {time : Fraction.Rational} {timeInside : FixedRootBoxPath.Inside time}
    (target : Transport.Reading actual time timeInside)
    (point_eq : firstPoint = (Parameter.sourcePoint site parameter (Waist.direction quarter time)).base)
    (paid : (time - reference) ^ 2 ≤ Approximation.Rational.Geometric.Basic.quarterRadius 1 7) :
    NamedEquivalent values.value.name target.lift.value.name := by
  have square := (Parameter.sourcePoint site parameter (Waist.direction quarter time)).quadratic
  rewrite [← (Parameter.sourcePoint site parameter (Waist.direction quarter time)).coordinate_base,
    ← point_eq] at square
  have targetInside := Clearance.quarter_ordinate_inside site parameter quarter reference time
    anchor.seed.separation paid
  let normalCompared := anchor.seed.retained_agrees_exact firstNormal values.normalRoot values.normalRoot_eq
    normalRefines (Parameter.sourcePoint site parameter (Waist.direction quarter time)).ordinate square targetInside
  have targetRefines : target.unit.track.initial.box.Refines actual.data.source.track.initial.box := by
    rewrite [target.unit_eq, SquareRoot.Owner.Transport.castOwnerParameter_initial_box]
    exact target.trace.refines
  have movement := budgets.unit_movement inside
  rewrite [Norm.Basic.normSq_eq_canonical] at movement
  let unitCompared := budgets.unit.retainedOwnersEquivalentOfEq
    (congrArg (fun point : Canonical => (unitPolynomial site).eval point) point_eq)
    (budgets.unit_nonzero inside) movement firstUnit target.unit unitRefines targetRefines
  have unitName : values.unitRoot.value.name = ownerRootName firstUnit.parameterNonzero firstUnit := by
    rewrite [values.unitRoot_eq]
    rfl
  have unitEquivalent : NamedEquivalent values.unitRoot.value.name target.lift.unitRoot.value.name :=
    NamedEquivalent.transport unitName.symm target.lift.unitRoot_name.symm unitCompared
  rewrite [values.value_eq, target.lift.value_eq]
  exact Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects
    values.unitRoot.value target.lift.unitRoot.value values.normalRoot.value
    (Coherence.exact (Parameter.sourcePoint site parameter (Waist.direction quarter time)).ordinate)
    unitEquivalent normalCompared

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Values
