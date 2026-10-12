module
import Purelib.Data.Fin.Cardinality
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
public import Purelib.Polynomial.Elimination.Axis.Certificate
public import Purelib.RootIsolation.Exact.Basic
import Purelib.RootIsolation.Exact.LargeSquare
import Purelib.RootIsolation.Exact.Ownership.Injective
import Purelib.RootIsolation.Exact.Ownership.Prepare
import Purelib.RootIsolation.Track.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.State.WindingOne.Basic

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Choice-free degree-sharp maximality

The finite exact-isolation partition assigns every sufficiently refined
winding-one track to one displayed output cell.  Zero-winding remainder cells
cannot own such a track, and a raw-winding-four output cell cannot own two
separated tracks.  All searches below scan finite lists directly.
-/

namespace Purelib.RootIsolation.Exact.Ownership.Cardinality

/-- A supported pairwise-separated finite track family has size at most the original isolation output count.

The exact retained output-owner map is injective, so direct finite cardinality bounds apply to its original indices. -/
theorem family_card_le_output_count
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    {count familyCount : Nat} (output : Exact.Basic.Output p ambient count)
    (family : Fin familyCount → Track.Basic.WindingOneTrack p ambient)
    (supported : ∀ index, (family index).initial.box.Refines output.support)
    (pairwise : ∀ left right, left ≠ right →
      (family left).initial.box.Separated (family right).initial.box) :
    familyCount ≤ count := open Purelib in by
  let owner : Fin familyCount → Fin output.tracks.length := fun index =>
    (Exact.Ownership.Prepare.selectOutputOwner degreeAtLeastTwo squarefree elimination output
      (family index) (supported index)).owner
  have ownerInjective : Function.Injective owner :=
    Exact.Ownership.Injective.selectedOwner_injective degreeAtLeastTwo squarefree elimination output
      family supported pairwise
  have cardinality :=
    Data.Fin.Cardinality.fin_card_le_of_injective_direct
      owner ownerInjective
  rw [output.tracks_length] at cardinality
  exact cardinality

/-- A pairwise-separated family on the coefficient-computed large square has size at most the original polynomial
degree.

Use the original degree-many isolation output and its exact support equality to retain the finite owner-cardinality
proof. -/
theorem family_card_le_natDegree
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    {familyCount : Nat}
    (family : Fin familyCount → Track.Basic.WindingOneTrack p
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p))
    (pairwise : ∀ left right, left ≠ right →
      (family left).initial.box.Separated (family right).initial.box) :
    familyCount ≤ p.natDegree := by
  let output := Exact.LargeSquare.isolateLargeSquare
    degreeAtLeastTwo squarefree elimination
  apply family_card_le_output_count degreeAtLeastTwo squarefree
    elimination output family
  · intro index
    rw [Exact.LargeSquare.isolateLargeSquare_support degreeAtLeastTwo squarefree elimination]
    exact (family index).initial.refinesAmbient
  · exact pairwise

end Purelib.RootIsolation.Exact.Ownership.Cardinality

end
