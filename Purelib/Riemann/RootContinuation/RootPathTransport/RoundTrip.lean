module

public import Purelib.Riemann.RootContinuation.RootPathTransport
import Purelib.Data.Fin.Bijection.Search
import Purelib.Tactic.QuotientFreeOmega

/-! # Both inverse laws from one retained endpoint reference

The two actual transports already select maps on the same two-element
frames. One endpoint's original winding reference pays their left inverse.
Constructive finite surjectivity then pays the other composite, without a
reference loop at the possibly interior opposite endpoint.
-/

public section

open Purelib.Polynomial.Winding

namespace Purelib.Riemann.RootContinuation.RootPathTransport.OwnerPath

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (GaussianPolynomial)
open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame)

/-- The opposite framed owner-path composite is identity from the same actual source reference.

The original round-trip theorem makes the retained forward map injective.
Constructive finite preimage search supplies the displayed target index;
all following equalities concern those same supplied maps and paths.
-/
theorem reverseRoundTrip_index {polynomial : GaussianPolynomial} {start finish : Canonical}
    (first : OwnerFrame (polynomial.eval start)) (last : OwnerFrame (polynomial.eval finish))
    (reference : WindingOneLoop polynomial start) (forward backward : Fin 2 → Fin 2)
    (outward : (index : Fin 2) →
      OwnerPath polynomial start (first.owners index) finish (last.owners (forward index)))
    (returned : (index : Fin 2) →
      OwnerPath polynomial finish (last.owners index) start (first.owners (backward index)))
    (cancel : (index : Fin 2) →
      Polygon.Basic.chainRaw polynomial start (outward index).vertices +
        Polygon.Basic.chainRaw polynomial finish (returned (forward index)).vertices = 0)
    (index : Fin 2) : forward (backward index) = index := by
  have leftInverse := roundTrip_index first last reference forward backward outward returned cancel
  have injective : Function.Injective forward := by
    intro left right same
    exact (leftInverse left).symm.trans ((congrArg backward same).trans (leftInverse right))
  obtain ⟨source, atTarget⟩ := Data.Fin.Bijection.fin_surjective_of_injective forward injective index
  exact (congrArg (fun target => forward (backward target)) atTarget.symm).trans
    ((congrArg forward (leftInverse source)).trans atTarget)

/-- An actual alternative owner path selects the original target index from the opposite endpoint reference.

Both retained framed path families have fixed opposite windings. Replacing
only the displayed outward occurrence preserves that inverse calculation;
finite preimage search therefore identifies its actual selected target.
The alternative path may have heterogeneous local ambients.
-/
theorem target_index {polynomial : GaussianPolynomial} {start finish : Canonical}
    (first : OwnerFrame (polynomial.eval start)) (last : OwnerFrame (polynomial.eval finish))
    (reference : WindingOneLoop polynomial finish) (forward backward : Fin 2 → Fin 2)
    (outward : (index : Fin 2) →
      OwnerPath polynomial start (first.owners index) finish (last.owners (forward index)))
    (returned : (index : Fin 2) →
      OwnerPath polynomial finish (last.owners index) start (first.owners (backward index)))
    (winding : Int)
    (outwardWinding : (index : Fin 2) →
      Polygon.Basic.chainRaw polynomial start (outward index).vertices = winding)
    (returnWinding : (index : Fin 2) →
      Polygon.Basic.chainRaw polynomial finish (returned index).vertices = -winding)
    (index selected : Fin 2)
    (alternative : OwnerPath polynomial start (first.owners index) finish (last.owners selected))
    (sameWinding : Polygon.Basic.chainRaw polynomial start alternative.vertices = winding) :
    selected = forward index := by
  have originalReturn (chosen : Fin 2) : forward (backward chosen) = chosen :=
    roundTrip_index last first reference backward forward returned outward (fun chosen => by
      rewrite [returnWinding, outwardWinding]
      omega0) chosen
  have atIndex (index : Fin 2) : (selected : Fin 2) →
      (alternative : OwnerPath polynomial start (first.owners index) finish (last.owners selected)) →
      Polygon.Basic.chainRaw polynomial start alternative.vertices = winding →
      selected = forward index := by
    refine Data.Fin.cases_induction ?_
      (fun next => Data.Fin.cases_induction ?_ (fun empty => Fin.elim0 empty) next) index
    · intro chosen path paid
      let mixedTarget : Fin 2 → Fin 2 := Data.Fin.cases chosen (fun next => forward next.succ)
      let mixed : (chosen : Fin 2) →
          OwnerPath polynomial start (first.owners chosen) finish (last.owners (mixedTarget chosen)) :=
        Data.Fin.casesDependent path (fun next => outward next.succ)
      have mixedWinding (chosen : Fin 2) :
          Polygon.Basic.chainRaw polynomial start (mixed chosen).vertices = winding :=
        Data.Fin.cases_induction paid (fun next => outwardWinding next.succ) chosen
      have inverse := reverseRoundTrip_index last first reference backward mixedTarget returned mixed
        (fun chosen => by rewrite [returnWinding, mixedWinding]; omega0) 0
      change backward chosen = 0 at inverse
      exact (originalReturn chosen).symm.trans (congrArg forward inverse)
    · intro chosen path paid
      let mixedTarget : Fin 2 → Fin 2 := Data.Fin.cases (forward 0) (fun _next => chosen)
      let mixed : (chosen : Fin 2) →
          OwnerPath polynomial start (first.owners chosen) finish (last.owners (mixedTarget chosen)) :=
        Data.Fin.casesDependent (outward 0)
          (fun next => Data.Fin.casesDependent
            (motive := fun tail : Fin 1 =>
              OwnerPath polynomial start (first.owners tail.succ) finish (last.owners chosen))
            path (fun empty => Fin.elim0 empty) next)
      have mixedWinding (chosen : Fin 2) :
          Polygon.Basic.chainRaw polynomial start (mixed chosen).vertices = winding :=
        Data.Fin.cases_induction (outwardWinding 0)
          (fun next => Data.Fin.cases_induction paid (fun empty => Fin.elim0 empty) next) chosen
      have inverse := reverseRoundTrip_index last first reference backward mixedTarget returned mixed
        (fun chosen => by rewrite [returnWinding, mixedWinding]; omega0) 1
      change backward chosen = 1 at inverse
      exact (originalReturn chosen).symm.trans (congrArg forward inverse)
  exact atIndex index selected alternative sameWinding

end Purelib.Riemann.RootContinuation.RootPathTransport.OwnerPath

namespace Purelib.Riemann.RootContinuation.RootPathTransport.PathTransport

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Polynomial.Geometry.ClearPath (GaussianPolynomial)
open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame)

variable {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Canonical}
variable {path : ClearPath polynomial ambient start finish}
variable {first : OwnerFrame (polynomial.eval start)} {last : OwnerFrame (polynomial.eval finish)}

/-- The opposite transport composite is identity from the same retained source reference and zero round-trip winding.

The original roundTrip_index makes the forward map injective. Bounded
finite preimage search supplies a source for the displayed target; all
subsequent equalities concern those same two cached target functions.
-/
theorem reverseRoundTrip_index {backPath : ClearPath polynomial ambient finish start}
    (reference : WindingOneLoop polynomial start)
    (forward : PathTransport path first last) (backward : PathTransport backPath last first)
    (cancel : Paths.PreparedPathWinding.ClearPath.rawWinding path +
      Paths.PreparedPathWinding.ClearPath.rawWinding backPath = 0)
    (index : Fin 2) : forward.target (backward.target index) = index := by
  exact OwnerPath.reverseRoundTrip_index first last reference forward.target backward.target
    (fun selected => (forward.row selected).joined) (fun selected => (backward.row selected).joined)
    (fun selected =>
      (congrArg (fun value : Int => value + Polygon.Basic.chainRaw polynomial finish
        (backward.row (forward.target selected)).joined.vertices) (forward.row selected).joined_winding).trans
        ((congrArg (fun value : Int => Paths.PreparedPathWinding.ClearPath.rawWinding path + value)
          (backward.row (forward.target selected)).joined_winding).trans cancel)) index

end Purelib.Riemann.RootContinuation.RootPathTransport.PathTransport

end
