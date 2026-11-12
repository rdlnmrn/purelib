module

public import Purelib.Polynomial.Multivariate.Gaussian.PowerCoordinates
public import Purelib.Data.Gaussian.Cast.Real
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Exact rational readback of bounded power coordinates

The original Gaussian coordinate cache remains a parameter of the rational
readback. Its bounded exponents and exact rational coefficients reconstruct
that same cache; a failed readback retains all actual coefficient inspections.
-/

public section

namespace Purelib.Polynomial.Multivariate.Sparse.PowerCoordinates

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

set_option genInjectivity false in
/-- Cached exact rational coefficients indexed by their original bounded Gaussian power-coordinate cache. -/
structure RationalCoordinates {arity degree : Nat} {polynomial : Sparse Canonical arity} {index : Fin arity}
    (coordinates : PowerCoordinates polynomial index degree) where
  /-- Original bounded exponents with their exact rational real-axis coefficients. -/
  entries : List (Fin degree × Rational)
  /-- The rational readback reconstructs every entry of the original coordinate cache. -/
  entries_eq : coordinates.entries = entries.map (fun entry => (entry.1, Cast.CoordinateTaylor.ofCoordinate entry.2))

constructive_injectivity RationalCoordinates

set_option genInjectivity false in
/-- Exact real-coordinate success or every retained nonreal coefficient obligation at the original cache. -/
inductive RealCheck {arity degree : Nat} {polynomial : Sparse Canonical arity} {index : Fin arity}
    (coordinates : PowerCoordinates polynomial index degree) where
  /-- Retain the exact rational cache and its original Gaussian readback law. -/
  | real (result : RationalCoordinates coordinates)
  /-- Retain all actual coefficient inspections, including every unsupported nonreal coefficient. -/
  | unresolved (view : Cast.RealListView coordinates.entries) (incomplete : ¬ view.Complete)

constructive_injectivity RealCheck

/-- Read every original coefficient once, returning exact rational coordinates or all retained unresolved conditions. -/
@[expose] def inspectReal {arity degree : Nat} {polynomial : Sparse Canonical arity} {index : Fin arity}
    (coordinates : PowerCoordinates polynomial index degree) : RealCheck coordinates :=
  let view := Cast.inspectRealList coordinates.entries
  if complete : view.Complete then .real ⟨view.coordinates complete, view.coordinates_eq complete⟩
  else .unresolved view complete

/-- Interpret actual cached rational coefficients at the same original selected coherent generator. -/
@[expose] def RationalCoordinates.denote {arity degree : Nat} {polynomial : Sparse Canonical arity} {index : Fin arity}
    {coordinates : PowerCoordinates polynomial index degree} (rational : RationalCoordinates coordinates)
    (environment : Fin arity → CoherentNamed) : CoherentNamed :=
  Terms.denotePowers (environment index)
    (rational.entries.map (fun entry => (entry.1, Cast.CoordinateTaylor.ofCoordinate entry.2)))

/-- Exact rational readback preserves the original polynomial's operational interpretation. -/
def RationalCoordinates.equivalent {arity degree : Nat} {polynomial : Sparse Canonical arity} {index : Fin arity}
    {coordinates : PowerCoordinates polynomial index degree} (rational : RationalCoordinates coordinates)
    (environment : Fin arity → CoherentNamed) :
    NamedEquivalent (polynomial.denote environment).name (rational.denote environment).name := by
  have comparison := coordinates.equivalent environment
  unfold PowerCoordinates.denote at comparison
  rewrite [rational.entries_eq] at comparison
  exact comparison

end Purelib.Polynomial.Multivariate.Sparse.PowerCoordinates

end
