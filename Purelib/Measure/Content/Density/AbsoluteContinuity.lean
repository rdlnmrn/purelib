module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Measure.Content.Density.Aligned
import Purelib.Measure.Content.Density.Witness
import Purelib.Measure.Weighted.Integral
import Purelib.Data.Rat.Fraction

import Purelib.Data.Rat.Fraction.Order
public import Purelib.Measure.Content.AbsoluteContinuity.Basic
import Purelib.Measure.Content.Basic
import Purelib.Measure.Content.Density.Basic
import Purelib.Measure.Content.Integral
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

section
@[expose] public section

/-!
# Absolute continuity of finite contents

Absolute continuity is the preservation of zero content for every executable
event.  It is a direct relation between displayed finite contents; every
nonnegative reweighting and every finite Radon--Nikodym witness supplies it.
-/

namespace Purelib.Measure

namespace Content
end Content

namespace Content.DensityWitness

open Purelib.Data.Rat in
/-- Certify the supplied nonnegative density as a witness from the original content to its exact reweighted content. -/
def ofReweight {α : Type} (content : Content α)
    (density : α → Fraction.Rational) (nonnegative : ∀ item, 0 ≤ density item) :
    AtomicChange.Witness content (content.reweight density nonnegative) where
  density := density
  nonnegative := nonnegative
  integral_eq value := content.reweight_integral density nonnegative value

open Purelib.Measure
/-- A retained density witness makes its exact target absolutely continuous with respect to its original source. -/
theorem absolutelyContinuous {α : Type}
    {source target : Content α}
    (witness : AtomicChange.Witness source target) :
    target.AbsolutelyContinuous source := by
  intro event zero
  have reweightedZero := source.reweight_measure_zero witness.density
    witness.nonnegative event zero
  rw [source.reweight_measure] at reweightedZero
  calc
    target.measure event = source.integral (fun item =>
          witness.density item * Distribution.indicator event item) :=
      Content.DensityWitness.measure_eq witness event
    _ = 0 := reweightedZero

/-- Density witnesses in both directions give the two original contents the same null events. -/
theorem sameNullEvents_of_reverse {α : Type}
    {source target : Content α}
    (forward : AtomicChange.Witness source target)
    (backward : AtomicChange.Witness target source) :
    target.SameNullEvents source :=
  ⟨absolutelyContinuous forward, absolutelyContinuous backward⟩

end Content.DensityWitness

namespace AtomicChange

open Purelib.Measure in
/-- An aligned atomic change's exact target is absolutely continuous with respect to its exact source. -/
theorem target_absolutelyContinuous_source {α : Type} [DecidableEq α]
    (change : AtomicChange α) :
    change.target.AbsolutelyContinuous change.source :=
  Content.DensityWitness.absolutelyContinuous change.witness

end AtomicChange

end Purelib.Measure

end
