module

public import Purelib.Polynomial.Geometry.Grid.AxisWalks
public import Purelib.Topology.Chain.PathBoundary
import Purelib.Data.List.Map
import Purelib.Data.List.Reverse
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction.Order.Basic

/-! # Ordered coordinate steps of the same retained axis walk

The original adjacent intervals remain the walk's data. Reading their
oriented coordinates keeps order and reversal, exact endpoints, and each
step's strict interval bounds. Equal requested endpoints have no inner
steps; this fact does not remove an enclosing path occurrence.
-/

public section

namespace Purelib.Polynomial.Geometry.Grid.AxisWalks

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.List
open Purelib.Topology.Chain.PathBoundary (PathEndpoints)

universe u

variable {Alpha : Type u} {key : Alpha → Rational} {intervals : List (ClearGrid.Interval key)}

namespace IncreasingWalk

/-- Read the same retained adjacent intervals as their ordered coordinate endpoint pairs. -/
@[expose] def steps {first last : Rational} (walk : IncreasingWalk intervals first last) :
    List (Rational × Rational) := walk.edges.map (fun interval => (key interval.lower, key interval.upper))

/-- The original interval walk gives exact endpoints of the same ordered coordinate steps. -/
theorem steps_path : {first last : Rational} → (walk : IncreasingWalk intervals first last) →
    PathEndpoints Prod.fst Prod.snd walk.steps first last
  | _, _, .nil point => .nil point
  | _, _, .cons _ _ tail => .cons (steps_path tail)

/-- Each original coordinate step is strictly increasing and stays between the walk's original endpoints. -/
theorem steps_bounds {first last : Rational} (walk : IncreasingWalk intervals first last)
    {step : Rational × Rational} (present : step ∈ walk.steps) :
    first ≤ step.1 ∧ step.1 < step.2 ∧ step.2 ≤ last := by
  rcases Map.mem_map.mp present with ⟨interval, member, equal⟩
  cases equal
  have bounds := walk.edge_bounds interval member
  exact ⟨bounds.1, interval.ordered, bounds.2⟩

/-- Strict original adjacent intervals forbid a nonempty increasing walk at equal endpoints. -/
theorem edges_nil_of_eq {first last : Rational} (walk : IncreasingWalk intervals first last)
    (same : first = last) : walk.edges = [] := by
  cases walk with
  | nil => rfl
  | cons interval _ tail =>
      have strict := interval.ordered.trans_le tail.ordered
      rewrite [← same] at strict
      exact False.elim (strict.2 (Purelib.Data.Rat.Fraction.Order.Basic.le_refl _))

end IncreasingWalk

namespace Walk

/-- Read the original traversal order, reversing both occurrence order and coordinate direction when required. -/
@[expose] def steps {first last : Rational} : Walk intervals first last → List (Rational × Rational)
  | .forward path => path.steps
  | .backward path => path.steps.reverse.map Prod.swap

/-- The same oriented coordinate steps retain their exact requested start and finish. -/
theorem steps_path {first last : Rational} (walk : Walk intervals first last) :
    PathEndpoints Prod.fst Prod.snd walk.steps first last := by
  cases walk with
  | forward path => exact path.steps_path
  | backward path => exact PathEndpoints.reverse Prod.swap (fun _ => rfl) (fun _ => rfl) path.steps_path

/-- Each same oriented step stays in the original interval and has the direction of the retained traversal. -/
theorem steps_bounds {first last : Rational} (walk : Walk intervals first last)
    {step : Rational × Rational} (present : step ∈ walk.steps) :
    (first ≤ step.1 ∧ step.1 < step.2 ∧ step.2 ≤ last) ∨
      (last ≤ step.2 ∧ step.2 < step.1 ∧ step.1 ≤ first) := by
  cases walk with
  | forward path => exact Or.inl (path.steps_bounds present)
  | backward path =>
      rcases Map.mem_map.mp present with ⟨original, member, equal⟩
      cases equal
      exact Or.inr (path.steps_bounds ((Reverse.mem_reverse _).mp member))

/-- Equal endpoints leave an empty inner step list in either retained orientation. -/
theorem steps_nil_of_eq {first last : Rational} (walk : Walk intervals first last)
    (same : first = last) : walk.steps = [] := by
  cases walk with
  | forward path =>
      change path.edges.map _ = []
      rewrite [path.edges_nil_of_eq same]
      rfl
  | backward path =>
      change (path.edges.map _).reverse.map Prod.swap = []
      rewrite [path.edges_nil_of_eq same.symm]
      rfl

end Walk

end Purelib.Polynomial.Geometry.Grid.AxisWalks

end
