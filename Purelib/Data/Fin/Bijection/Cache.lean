module

public import Purelib.Data.Fin.Bijection.Basic

/-!
# Retained values of finite bijections

One checked source/target pair supplies both forward and backward cache hits.
Other queries use the original maps. Pointwise readbacks preserve the complete
bijection without identifying functions by extensionality.
-/

public section

namespace Purelib.Data.Fin.Bijection

/-- Cache both directions of one checked value of the original finite bijection.

The supplied target is the original forward image of the supplied source.
Both maps return those retained indices at that pair and use the original maps
elsewhere. Their pointwise readbacks transport the two original inverse laws.
-/
@[expose] def cache {sourceCount targetCount : Nat}
    (original : Bijection sourceCount targetCount) (source : Fin sourceCount)
    (target : Fin targetCount) (same : target = original.forward source) :
    Bijection sourceCount targetCount :=
  let forward := fun index => if index = source then target else original.forward index
  let backward := fun index => if index = target then source else original.backward index
  have forwardEq (index : Fin sourceCount) : forward index = original.forward index := by
    change (if index = source then target else original.forward index) = original.forward index
    by_cases equal : index = source
    · cases equal
      exact (if_pos rfl).trans same
    · exact if_neg equal
  have backwardEq (index : Fin targetCount) : backward index = original.backward index := by
    change (if index = target then source else original.backward index) = original.backward index
    by_cases equal : index = target
    · cases equal
      have inverse : original.backward target = source :=
        (congrArg original.backward same).trans (original.backward_forward source)
      exact (if_pos rfl).trans inverse.symm
    · exact if_neg equal
  { forward := forward
    backward := backward
    backward_forward := fun index =>
      (backwardEq (forward index)).trans
        ((congrArg original.backward (forwardEq index)).trans (original.backward_forward index))
    forward_backward := fun index =>
      (forwardEq (backward index)).trans
        ((congrArg original.forward (backwardEq index)).trans (original.forward_backward index)) }

/-- Every cached forward reading equals the original forward reading at that same index. -/
theorem cache_forward {sourceCount targetCount : Nat}
    (original : Bijection sourceCount targetCount) (source : Fin sourceCount)
    (target : Fin targetCount) (same : target = original.forward source) (index : Fin sourceCount) :
    (original.cache source target same).forward index = original.forward index := by
  change (if index = source then target else original.forward index) = original.forward index
  by_cases equal : index = source
  · cases equal
    exact (if_pos rfl).trans same
  · exact if_neg equal

/-- Every cached backward reading equals the original backward reading at that same index. -/
theorem cache_backward {sourceCount targetCount : Nat}
    (original : Bijection sourceCount targetCount) (source : Fin sourceCount)
    (target : Fin targetCount) (same : target = original.forward source) (index : Fin targetCount) :
    (original.cache source target same).backward index = original.backward index := by
  change (if index = target then source else original.backward index) = original.backward index
  by_cases equal : index = target
  · cases equal
    have inverse : original.backward target = source :=
      (congrArg original.backward same).trans (original.backward_forward source)
    exact (if_pos rfl).trans inverse.symm
  · exact if_neg equal

/-- The retained source query reads the supplied target without evaluating the original forward map. -/
theorem cache_forward_source {sourceCount targetCount : Nat}
    (original : Bijection sourceCount targetCount) (source : Fin sourceCount)
    (target : Fin targetCount) (same : target = original.forward source) :
    (original.cache source target same).forward source = target := by
  change (if source = source then target else original.forward source) = target
  exact if_pos rfl

/-- The retained target query reads the supplied source without evaluating the original backward map. -/
theorem cache_backward_target {sourceCount targetCount : Nat}
    (original : Bijection sourceCount targetCount) (source : Fin sourceCount)
    (target : Fin targetCount) (same : target = original.forward source) :
    (original.cache source target same).backward target = source := by
  change (if target = target then source else original.backward target) = source
  exact if_pos rfl

/-- Caching a checked pair preserves the complete original finite matching pointwise. -/
theorem cache_same {sourceCount targetCount : Nat}
    (original : Bijection sourceCount targetCount) (source : Fin sourceCount)
    (target : Fin targetCount) (same : target = original.forward source) :
    Same (original.cache source target same) original :=
  cache_forward original source target same

end Purelib.Data.Fin.Bijection

end
