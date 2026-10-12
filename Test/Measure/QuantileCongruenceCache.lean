module
import Purelib.Measure.Weighted.Consolidation
import Purelib.Measure.Content.Histogram
import Purelib.Measure.Distribution.TotalVariation.Basic
meta import Lean.Elab.Command
meta import Lean.Meta.CongrTheorems

namespace Test.Measure.QuantileCongruenceCache
open Purelib.Measure

open Lean Elab Command in
run_elab do
  for (operation, kinds) in [( ``atomEvent, #[Meta.CongrArgKind.fixed, .subsingletonInst, .eq, .eq]),
      (``Distribution.totalVariationDistance, #[.fixed, .subsingletonInst, .eq, .eq]),
      (``Content.atomMassSum, #[.fixed, .subsingletonInst, .eq, .eq, .eq])] do
    let name := Name.str operation "congr_simp"
    let some congrThm ← Meta.mkCongrSimpForConst? operation []
      | throwError "imported automatic congruence lookup failed"
    unless congrThm.proof.isConstOf name &&
        congrThm.argKinds == kinds do
      throwError "imported lookup changed the original public cache"

/-- Scalar singleton rewrites reuse the original public congruence theorem after import. -/
private theorem singleton_imported_reuse {α : Type} {first : DecidableEq α}
    [second : DecidableEq α] (target target' candidate candidate' : α)
    (sameTarget : target = target') (sameCandidate : candidate = candidate') :
    @atomEvent α first target candidate = @atomEvent α second target' candidate' := by
  simp only [-eq_self, -iff_self, sameTarget, sameCandidate]
  exact atomEvent_eq_of_decidableEq first second target' candidate'

/-- Scalar law rewrites reuse the original total variation congruence theorem after import. -/
private theorem distance_imported_reuse {α : Type} {first : DecidableEq α}
    [second : DecidableEq α] (left left' right right' : Distribution α)
    (sameLeft : left = left') (sameRight : right = right') :
    @Distribution.totalVariationDistance α first left right =
      @Distribution.totalVariationDistance α second left' right' := by
  simp only [-eq_self, -iff_self, sameLeft, sameRight]
  exact Distribution.totalVariationDistance_eq_of_decidableEq first second left' right'

open Purelib.Data.Rat in
/-- Imported singleton-mass rewrites reuse the original public congruence certificate. -/
private theorem mass_sum_imported_reuse {α : Type} {first : DecidableEq α}
    [second : DecidableEq α] (content content' : Content α)
    (keys keys' : List (Weighted α)) (value value' : α → Fraction.Rational)
    (sameContent : content = content') (sameKeys : keys = keys') (sameValue : value = value') :
    @Content.atomMassSum α first content keys value =
      @Content.atomMassSum α second content' keys' value' := by
  simp only [-eq_self, -iff_self, sameContent, sameKeys, sameValue]
  exact Content.atomMassSum_eq_of_decidableEq first second content' keys' value'

end Test.Measure.QuantileCongruenceCache
