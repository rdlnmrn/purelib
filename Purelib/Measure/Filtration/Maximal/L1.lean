module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Conditioning.Mean
import Purelib.Measure.Distribution.Expectation
public import Purelib.Measure.Distribution.Maximal.FirstCrossing
import Purelib.Measure.Distribution.Partition.Cellwise
import Purelib.Measure.Distribution.Partition.ConditionalExpectation
import Purelib.Measure.Distribution.Partition.Positive
import Purelib.Measure.Distribution.Partition.Refinement.Cellwise
import Purelib.Measure.Event.Family
import Purelib.Measure.Event.FirstCrossing
import Purelib.Measure.Filtration.Basic
public import Purelib.Measure.Filtration.Cellwise
public import Purelib.Measure.Filtration.ConditionalExpectation
import Purelib.Measure.Weighted.Event
import Purelib.Measure.Weighted.Integral
import Purelib.Data.Rat.Fraction
import Purelib.Measure.Event.RationalOrder
import Purelib.Measure.Content.Basic
import Purelib.Measure.Classified.Basic
import Purelib.Measure.Distribution.Partition.Basic
import Purelib.Measure.EventAlgebra.Simple.Basic
import Purelib.Measure.Event.Chain
import Purelib.Approximation.OneSided.Basic
import Purelib.Measure.Classified.FixedLawProcess
import Purelib.Approximation.OneSided.Located
import Purelib.Measure.Distribution.Partition.Projection
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.EventAlgebra.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic

section
public section

/-!
# Finite first-crossing maximal inequality

A displayed list of rational observables has explicit first-crossing events
at every positive threshold.  These events are disjoint.  If each crossing
value transfers its restricted integral to one nonnegative terminal
observable, finite subadditivity and disjoint additivity give the sharp
Doob-style L1 maximal inequality.  The transfer property is explicit data;
there is no unbounded time, stopping-time space, or optional-limit theorem.
-/

namespace Purelib.Measure

open Purelib Purelib.Data.Rat

namespace Filtration

/-- Certify first-crossing transfer and finest-partition cellwise survival for the exact conditional-expectation list.

Both clauses retain the same filtration, terminal observable, initial active event and threshold used to compute its
first-crossing events. -/
structure CanonicalCrossingCertificate {α : Type}
    {distribution : Measure.Distribution α}
    {finest : Measure.PositiveEventPartition distribution}
    (filtration : Measure.Filtration distribution finest)
    (terminal : α → Fraction.Rational) (active : α → Bool)
    (threshold : Fraction.Rational) : Prop where
  /-- The exact terminal observable transfers expectations from the retained first-crossing events of the original
    conditional-expectation list. -/ transfer : distribution.CrossingTransferFrom active threshold terminal
    (filtration.conditionalExpectationValues terminal)
  /-- The indicator of the exact surviving event is cellwise on the original finest partition. -/ survivingCellwise :
    finest.IsCellwiseObservable
    (Distribution.indicator
      (survivingEventFrom active threshold
        (filtration.conditionalExpectationValues terminal)))

/-- Construct the exact crossing certificate from filtration compatibility and a cellwise initial active indicator. -/
theorem canonicalCrossingCertificate {α : Type}
    {distribution : Measure.Distribution α}
    {finest : Measure.PositiveEventPartition distribution}
    (filtration : Measure.Filtration distribution finest)
    (compatible : filtration.CellwiseCompatible)
    (terminal : α → Fraction.Rational) (active : α → Bool)
    (threshold : Fraction.Rational)
    (activeCellwise : filtration.coarsest.IsCellwiseObservable
      (Distribution.indicator active)) :
    CanonicalCrossingCertificate filtration terminal active threshold := by
  induction filtration generalizing active with
  | base partition =>
      rcases activeCellwise with ⟨activeCellwise⟩
      let projected := partition.conditionalExpectation terminal
      let projectedCellwise :=
        partition.conditionalExpectation_cellwise terminal
      let aboveCellwise := projectedCellwise.indicatorAtLeast threshold
      let crossingCellwise :=
        activeCellwise.indicatorIntersection aboveCellwise
      let remainingCellwise := activeCellwise.indicatorIntersection
        aboveCellwise.indicatorComplement
      refine { transfer := ?_, survivingCellwise := ?_ }
      · change distribution.eventIntegral
            (intersectionEvent active
              (Measure.atLeastEvent threshold projected)) projected ≤
          distribution.eventIntegral
            (intersectionEvent active
              (Measure.atLeastEvent threshold projected)) terminal ∧ True
        constructor
        · exact
            (distribution
              |>.eventIntegral_conditionalExpectation_of_indicator_cellwise
                partition terminal
                (intersectionEvent active
                  (Measure.atLeastEvent threshold projected))
                crossingCellwise).le
        · trivial
      · exact ⟨remainingCellwise⟩
  | @extend coarse earlier fine refinement inductionHypothesis =>
      change earlier.CellwiseCompatible ∧
        refinement.LiftsCellwiseObservables at compatible
      let past := inductionHypothesis compatible.1 active activeCellwise
      let pastValues := earlier.conditionalExpectationValues terminal
      let laterActive := survivingEventFrom active threshold pastValues
      have laterActiveCellwiseExists : fine.IsCellwiseObservable
          (Distribution.indicator laterActive) :=
        compatible.2 past.survivingCellwise
      rcases laterActiveCellwiseExists with ⟨laterActiveCellwise⟩
      let projected := fine.conditionalExpectation terminal
      let projectedCellwise := fine.conditionalExpectation_cellwise terminal
      let aboveCellwise := projectedCellwise.indicatorAtLeast threshold
      let crossingCellwise :=
        laterActiveCellwise.indicatorIntersection aboveCellwise
      let remainingCellwise := laterActiveCellwise.indicatorIntersection
        aboveCellwise.indicatorComplement
      have lastTransfer : distribution.CrossingTransferFrom laterActive
          threshold terminal [projected] := by
        constructor
        · exact
            (distribution
              |>.eventIntegral_conditionalExpectation_of_indicator_cellwise
                fine terminal
                (intersectionEvent laterActive
                  (Measure.atLeastEvent threshold projected))
                crossingCellwise).le
        · trivial
      have appended : distribution.CrossingTransferFrom active threshold
          terminal (pastValues ++ [projected]) :=
        distribution.crossingTransferFrom_append active threshold terminal
          pastValues [projected] past.transfer lastTransfer
      refine { transfer := ?_, survivingCellwise := ?_ }
      · rw [conditionalExpectationValues_extend]
        exact appended
      · rw [conditionalExpectationValues_extend,
          survivingEventFrom_append]
        exact ⟨remainingCellwise⟩

/-- Construct first-crossing transfer for the canonical conditional-expectation list starting with every item active. -/
theorem canonicalCrossingTransfer {α : Type}
    {distribution : Measure.Distribution α}
    {finest : Measure.PositiveEventPartition distribution}
    (filtration : Measure.Filtration distribution finest)
    (compatible : filtration.CellwiseCompatible)
    (terminal : α → Fraction.Rational) (threshold : Fraction.Rational) :
    distribution.CrossingTransferFrom (fun _ => true) threshold terminal
      (filtration.conditionalExpectationValues terminal) :=
    (filtration.canonicalCrossingCertificate compatible terminal
    (fun _ => true) threshold
    ⟨PositiveEventPartition.CellwiseObservable.indicatorTrue
      filtration.coarsest⟩).transfer

/-- A positive threshold times its maximal-event probability is at most the terminal observable's expectation.

The retained filtration must be cellwise compatible, and the terminal observable must be nonnegative on every original
atom. -/
theorem conditionalExpectation_l1_maximal {α : Type}
    {distribution : Measure.Distribution α}
    {finest : Measure.PositiveEventPartition distribution}
    (filtration : Measure.Filtration distribution finest)
    (compatible : filtration.CellwiseCompatible)
    (terminal : α → Fraction.Rational) (threshold : Fraction.Rational)
    (positive : 0 < threshold)
    (terminalNonnegative : ∀ atom, atom ∈ distribution.atoms →
      0 ≤ terminal atom.item) :
    threshold * distribution.probability
        (unionEvents
          ((filtration.conditionalExpectationValues terminal).map
            (Measure.atLeastEvent threshold))) ≤
      distribution.expectation terminal :=
  distribution.firstCrossing_l1_maximal threshold positive
    (filtration.conditionalExpectationValues terminal) terminal
    terminalNonnegative
    (filtration.canonicalCrossingTransfer compatible terminal threshold)
end Filtration

end Purelib.Measure

end
