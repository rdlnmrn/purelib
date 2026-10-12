module
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Four-edge integer telescoping

Integer correction differences cancel around the original four-edge cycle.
The retained equations identify the two ordered four-term totals.
-/

namespace Purelib.Data.Int.Telescope.Four

/-- Cancel two sets of integer differences around a four-edge cycle.

If each difference between the two displayed edge totals is a sum of successive
correction differences, and the intermediate terms themselves telescope cyclically,
the two four-term totals are equal. -/
public theorem fourEdgeRoucheTelescope
    {p₀ p₁ p₂ p₃ s₀ s₁ s₂ s₃ h₀ h₁ h₂ h₃ : Int}
    {c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃ : Int}
    (product₀ : h₀ = -p₀ + s₀ - c₀ + c₁)
    (product₁ : h₁ = -p₁ + s₁ - c₁ + c₂)
    (product₂ : h₂ = -p₂ + s₂ - c₂ + c₃)
    (product₃ : h₃ = -p₃ + s₃ - c₃ + c₀)
    (half₀ : h₀ = d₀ - d₁) (half₁ : h₁ = d₁ - d₂)
    (half₂ : h₂ = d₂ - d₃) (half₃ : h₃ = d₃ - d₀) :
    s₀ + s₁ + s₂ + s₃ = p₀ + p₁ + p₂ + p₃ := by
  have s₀Identity : s₀ = p₀ + h₀ + c₀ - c₁ := by
    rw [product₀]
    ring1
  have s₁Identity : s₁ = p₁ + h₁ + c₁ - c₂ := by
    rw [product₁]
    ring1
  have s₂Identity : s₂ = p₂ + h₂ + c₂ - c₃ := by
    rw [product₂]
    ring1
  have s₃Identity : s₃ = p₃ + h₃ + c₃ - c₀ := by
    rw [product₃]
    ring1
  rw [s₀Identity, s₁Identity, s₂Identity, s₃Identity,
    half₀, half₁, half₂, half₃]
  ring1
end Purelib.Data.Int.Telescope.Four

end
