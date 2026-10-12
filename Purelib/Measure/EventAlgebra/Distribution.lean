module
public import Purelib.Measure.Distribution.Consolidation
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Kernel.Basic
public import Purelib.Measure.EventAlgebra.Basic
import Purelib.Measure.Weighted.Consolidation
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.EventAlgebra.Simple.Basic
import Purelib.Data.Rat.Fraction
import Mathlib.Order.Basic

section
@[expose] public section

/-!
# Explicit finite event algebras

An event algebra here is finite presented data: an explicitly enumerated code
type, an executable interpretation of each code as a Boolean event, and
certified Boolean operations.  No powerset, sigma-algebra, generated closure,
or enumeration of an ambient carrier is formed.
-/

namespace Purelib.Measure
namespace EventAlgebra

/-- Push the exact original law onto its complete retained event-algebra signatures. -/
def signatureDistribution {α : Type}
    (algebra : EventAlgebra α) (distribution : Distribution α) :
    Distribution (List Bool) :=
  distribution.map algebra.signature

/-- A coded event's original probability equals its signature-event probability under the retained signature law. -/
theorem probability_eq_signatureDistribution_probability {α : Type}
    (algebra : EventAlgebra α) (distribution : Distribution α)
    (event : algebra.Code) :
    distribution.probability (algebra.evaluate event) =
      (algebra.signatureDistribution distribution).probability
        (algebra.signatureEvent event) := by
  symm
  calc
    (algebra.signatureDistribution distribution).probability
          (algebra.signatureEvent event) =
        distribution.probability (fun item =>
          algebra.signatureEvent event (algebra.signature item)) :=
      distribution.map_probability algebra.signature
        (algebra.signatureEvent event)
    _ = distribution.probability (algebra.evaluate event) := by
      exact distribution.probability_congr _ _ (fun item =>
        algebra.signatureEvent_signature event item)

/-- Consolidate equal signatures in the exact original signature distribution. -/
def atomDistribution {α : Type} (algebra : EventAlgebra α)
    (distribution : Distribution α) : Distribution (List Bool) :=
  (algebra.signatureDistribution distribution).consolidate

/-- The consolidated algebra atom law has no repeated retained signatures. -/
theorem atomDistribution_noRepeatedSignatures {α : Type}
    (algebra : EventAlgebra α) (distribution : Distribution α) :
    NoRepeatedPayloads (algebra.atomDistribution distribution).atoms :=
  (algebra.signatureDistribution distribution).consolidate_noRepeatedPayloads

/-- The consolidated algebra atom law has no more retained rows than the original distribution. -/
theorem atomDistribution_atoms_length_le {α : Type}
    (algebra : EventAlgebra α) (distribution : Distribution α) :
    (algebra.atomDistribution distribution).atoms.length ≤
      distribution.atoms.length := by
  exact (algebra.signatureDistribution distribution).consolidate_atoms_length_le
    |>.trans_eq (distribution.map_atoms_length algebra.signature)

/-- The consolidated algebra atom law preserves every original coded-event probability. -/
theorem probability_eq_atomDistribution_probability {α : Type}
    (algebra : EventAlgebra α) (distribution : Distribution α)
    (event : algebra.Code) :
    distribution.probability (algebra.evaluate event) =
      (algebra.atomDistribution distribution).probability
        (algebra.signatureEvent event) := by
  calc
    distribution.probability (algebra.evaluate event) =
        (algebra.signatureDistribution distribution).probability
          (algebra.signatureEvent event) :=
      algebra.probability_eq_signatureDistribution_probability
        distribution event
    _ = (algebra.atomDistribution distribution).probability
          (algebra.signatureEvent event) :=
      ((algebra.signatureDistribution distribution)
        |>.consolidate_evaluationEquivalent.probability_eq
          (algebra.signatureEvent event)).symm
end EventAlgebra
end Purelib.Measure

end
