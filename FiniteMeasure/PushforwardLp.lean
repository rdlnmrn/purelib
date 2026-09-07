import FiniteMeasure.EssentialMaximum
import FiniteMeasure.Stochastic

/-!
# Finite pushforward laws for powered Lp and essential maxima

An executable pushforward retains every displayed source row and merely
changes its payload.  Consequently rational L1, natural-powered Lp, finite
almost-everywhere equality, and computed essential maxima all obey exact
change-of-variables laws.  No quotient function space or measurable-map
side condition is needed on a displayed finite table.
-/

namespace FiniteMeasure

private theorem essentialMaximumMagnitudeOn_mapAtoms {α β : Type}
    (function : α → β) (value : β → Coordinate) :
    ∀ atoms : List (Weighted α),
      essentialMaximumMagnitudeOn value (mapAtoms function atoms) =
        essentialMaximumMagnitudeOn (fun item => value (function item)) atoms
  | [] => rfl
  | atom :: remaining => by
      simp only [mapAtoms, essentialMaximumMagnitudeOn,
        essentialMaximumMagnitudeOn_mapAtoms function value remaining]

namespace FiniteContent

theorem map_poweredLp {α β : Type} (content : FiniteContent α)
    (function : α → β) (exponent : Nat) (value : β → Coordinate) :
    (content.map function).poweredLp exponent value =
      content.poweredLp exponent (fun item => value (function item)) := by
  unfold poweredLp
  exact content.map_integral function _

theorem map_poweredLpDistance {α β : Type}
    (content : FiniteContent α) (function : α → β) (exponent : Nat)
    (left right : β → Coordinate) :
    (content.map function).poweredLpDistance exponent left right =
      content.poweredLpDistance exponent
        (fun item => left (function item))
        (fun item => right (function item)) := by
  unfold poweredLpDistance
  exact content.map_integral function _

theorem map_poweredL1 {α β : Type} (content : FiniteContent α)
    (function : α → β) (value : β → Coordinate) :
    (content.map function).poweredL1 value =
      content.poweredL1 (fun item => value (function item)) := by
  unfold poweredL1
  exact content.map_integral function _

theorem map_l1Distance {α β : Type} (content : FiniteContent α)
    (function : α → β) (left right : β → Coordinate) :
    (content.map function).l1Distance left right =
      content.l1Distance (fun item => left (function item))
        (fun item => right (function item)) := by
  unfold l1Distance
  exact content.map_integral function _

theorem map_poweredL2 {α β : Type} (content : FiniteContent α)
    (function : α → β) (value : β → Coordinate) :
    (content.map function).poweredL2 value =
      content.poweredL2 (fun item => value (function item)) := by
  unfold poweredL2
  exact content.map_integral function _

theorem map_poweredL2Distance {α β : Type}
    (content : FiniteContent α) (function : α → β)
    (left right : β → Coordinate) :
    (content.map function).poweredL2Distance left right =
      content.poweredL2Distance (fun item => left (function item))
        (fun item => right (function item)) := by
  unfold poweredL2Distance
  rw [content.map_poweredL2]

theorem map_essentialMaximumMagnitude {α β : Type}
    (content : FiniteContent α) (function : α → β)
    (value : β → Coordinate) :
    (content.map function).essentialMaximumMagnitude value =
      content.essentialMaximumMagnitude
        (fun item => value (function item)) :=
  essentialMaximumMagnitudeOn_mapAtoms function value content.atoms

theorem map_essentialMaximumDistance {α β : Type}
    (content : FiniteContent α) (function : α → β)
    (left right : β → Coordinate) :
    (content.map function).essentialMaximumDistance left right =
      content.essentialMaximumDistance
        (fun item => left (function item))
        (fun item => right (function item)) := by
  unfold essentialMaximumDistance
  exact content.map_essentialMaximumMagnitude function _

theorem map_equalAlmostEverywhere_iff {α β : Type}
    (content : FiniteContent α) (function : α → β)
    (left right : β → Coordinate) :
    (content.map function).EqualAlmostEverywhere left right ↔
      content.EqualAlmostEverywhere
        (fun item => left (function item))
        (fun item => right (function item)) := by
  constructor
  · intro equal
    have zero :=
      ((content.map function).essentialMaximumDistance_eq_zero_iff
        left right).mpr equal
    rw [content.map_essentialMaximumDistance function left right] at zero
    exact (content.essentialMaximumDistance_eq_zero_iff _ _).mp zero
  · intro equal
    apply ((content.map function).essentialMaximumDistance_eq_zero_iff
      left right).mp
    rw [content.map_essentialMaximumDistance function left right]
    exact (content.essentialMaximumDistance_eq_zero_iff _ _).mpr equal

end FiniteContent

private theorem bindAtoms_pure_eq_mapAtoms {α β : Type}
    (function : α → β) : ∀ atoms : List (Weighted α),
    bindAtoms atoms (fun item => Distribution.pure (function item)) =
      mapAtoms function atoms
  | [] => rfl
  | atom :: remaining => by
      rw [bindAtoms,
        bindAtoms_pure_eq_mapAtoms function remaining]
      simp only [Distribution.pure, scaleAtoms, List.singleton_append,
        mapAtoms, mul_one]

namespace Distribution

theorem map_atoms_eq_mapAtoms {α β : Type} (source : Distribution α)
    (function : α → β) :
    (source.map function).atoms = mapAtoms function source.atoms := by
  unfold map bind
  exact bindAtoms_pure_eq_mapAtoms function source.atoms

theorem map_toFiniteContent {α β : Type} (source : Distribution α)
    (function : α → β) :
    (source.map function).toFiniteContent =
      source.toFiniteContent.map function := by
  unfold toFiniteContent FiniteContent.map
  rw [source.map_atoms_eq_mapAtoms function]

theorem map_poweredLp {α β : Type} (source : Distribution α)
    (function : α → β) (exponent : Nat) (value : β → Coordinate) :
    (source.map function).poweredLp exponent value =
      source.poweredLp exponent (fun item => value (function item)) := by
  unfold poweredLp
  rw [source.map_toFiniteContent function]
  exact source.toFiniteContent.map_poweredLp function exponent value

theorem map_poweredLpDistance {α β : Type}
    (source : Distribution α) (function : α → β) (exponent : Nat)
    (left right : β → Coordinate) :
    (source.map function).poweredLpDistance exponent left right =
      source.poweredLpDistance exponent
        (fun item => left (function item))
        (fun item => right (function item)) := by
  unfold poweredLpDistance
  rw [source.map_toFiniteContent function]
  exact source.toFiniteContent.map_poweredLpDistance
    function exponent left right

theorem map_poweredL1 {α β : Type} (source : Distribution α)
    (function : α → β) (value : β → Coordinate) :
    (source.map function).poweredL1 value =
      source.poweredL1 (fun item => value (function item)) := by
  unfold poweredL1
  rw [source.map_toFiniteContent function]
  exact source.toFiniteContent.map_poweredL1 function value

theorem map_l1Distance {α β : Type} (source : Distribution α)
    (function : α → β) (left right : β → Coordinate) :
    (source.map function).l1Distance left right =
      source.l1Distance (fun item => left (function item))
        (fun item => right (function item)) := by
  unfold l1Distance
  rw [source.map_expectation]

theorem map_poweredL2 {α β : Type} (source : Distribution α)
    (function : α → β) (value : β → Coordinate) :
    (source.map function).poweredL2 value =
      source.poweredL2 (fun item => value (function item)) := by
  unfold poweredL2
  rw [source.map_toFiniteContent function]
  exact source.toFiniteContent.map_poweredL2 function value

theorem map_poweredL2Distance {α β : Type}
    (source : Distribution α) (function : α → β)
    (left right : β → Coordinate) :
    (source.map function).poweredL2Distance left right =
      source.poweredL2Distance (fun item => left (function item))
        (fun item => right (function item)) := by
  unfold poweredL2Distance
  rw [source.map_toFiniteContent function]
  exact source.toFiniteContent.map_poweredL2Distance function left right

theorem map_essentialMaximumMagnitude {α β : Type}
    (source : Distribution α) (function : α → β)
    (value : β → Coordinate) :
    (source.map function).essentialMaximumMagnitude value =
      source.essentialMaximumMagnitude
        (fun item => value (function item)) := by
  unfold essentialMaximumMagnitude
  rw [source.map_toFiniteContent function]
  exact source.toFiniteContent.map_essentialMaximumMagnitude function value

theorem map_essentialMaximumDistance {α β : Type}
    (source : Distribution α) (function : α → β)
    (left right : β → Coordinate) :
    (source.map function).essentialMaximumDistance left right =
      source.essentialMaximumDistance
        (fun item => left (function item))
        (fun item => right (function item)) := by
  unfold essentialMaximumDistance
  rw [source.map_toFiniteContent function]
  exact source.toFiniteContent.map_essentialMaximumDistance
    function left right

theorem map_equalAlmostEverywhere_iff {α β : Type}
    (source : Distribution α) (function : α → β)
    (left right : β → Coordinate) :
    (source.map function).EqualAlmostEverywhere left right ↔
      source.EqualAlmostEverywhere
        (fun item => left (function item))
        (fun item => right (function item)) := by
  rw [← (source.map function).essentialMaximumDistance_eq_zero_iff,
    source.map_essentialMaximumDistance,
    source.essentialMaximumDistance_eq_zero_iff]

end Distribution

end FiniteMeasure
