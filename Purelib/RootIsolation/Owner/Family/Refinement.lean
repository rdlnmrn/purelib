module

import Purelib.Data.Gaussian.Basic
public import Purelib.RootIsolation.Owner.Local.Track
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
public import Purelib.RootIsolation.Owner.Family.Basic
import Purelib.RootIsolation.Track.Basic
import Purelib.Tactic.Ring
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.RootIsolation.Owner.Local.Basic
import Purelib.RootIsolation.State.WindingOne.Basic

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic (SquarefreeCertificate)

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.RootIsolation.Owner.Family.Basic
open Purelib.Data.Gaussian
namespace OwnerFamily

/-- Construct the original winding-one refinement track for the indexed owner of the squarefree polynomial. -/
def trackAt
    {p : CoefficientPolynomial} {count : Nat}
    (family : Owner.Family.Basic.OwnerFamily p count)
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (index : Fin count) :
    Track.Basic.WindingOneTrack p (family.owner index).box :=
  (family.owner index).track degreeAtLeastTwo squarefree
end OwnerFamily

end Purelib.RootIsolation.Owner.Family.Basic

end

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.RootIsolation.Owner.Family.Basic
open Purelib.Data.Gaussian
namespace OwnerFamily

/-- Simultaneously shrink every member of a finite owner family for the same
fixed displayed polynomial. -/
def refine
    {p : CoefficientPolynomial} {count : Nat}
    (family : Owner.Family.Basic.OwnerFamily p count)
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    Owner.Family.Basic.OwnerFamily p count where
  owner index :=
    let track := family.trackAt degreeAtLeastTwo squarefree index
    let next := track.refine track.initial epsilon positive
    { box := next.box
      proper := next.proper
      clearance := next.clearance
      rawWindingFour := next.rawWindingFour }
  pairwiseSeparated := by
    intro left right different
    let leftTrack := family.trackAt degreeAtLeastTwo squarefree left
    let rightTrack := family.trackAt degreeAtLeastTwo squarefree right
    exact Box.Separated.of_refines
      (family.pairwiseSeparated left right different)
      (leftTrack.nested leftTrack.initial epsilon positive)
      (rightTrack.nested rightTrack.initial epsilon positive)
end OwnerFamily

end Purelib.RootIsolation.Owner.Family.Basic

end

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.RootIsolation.Owner.Family.Basic
open Purelib.Data.Gaussian
namespace OwnerFamily

/-- Every simultaneously refined owner box meets the supplied positive accuracy target. -/
theorem refine_accurate
    {p : CoefficientPolynomial} {count : Nat}
    (family : Owner.Family.Basic.OwnerFamily p count)
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) (index : Fin count) :
    ((family.refine degreeAtLeastTwo squarefree epsilon positive).owner
      index).box.diagonalSq ≤ epsilon ^ 2 :=
  (family.trackAt degreeAtLeastTwo squarefree index).accurate
    (family.trackAt degreeAtLeastTwo squarefree index).initial epsilon positive

end OwnerFamily

end Purelib.RootIsolation.Owner.Family.Basic

end

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.RootIsolation.Owner.Family.Basic
open Purelib.Data.Gaussian
namespace OwnerFamily

/-- Every simultaneously refined owner box refines its own original family box. -/
theorem refine_nested
    {p : CoefficientPolynomial} {count : Nat}
    (family : Owner.Family.Basic.OwnerFamily p count)
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) (index : Fin count) :
    ((family.refine degreeAtLeastTwo squarefree epsilon positive).owner
      index).box.Refines (family.owner index).box :=
  (family.trackAt degreeAtLeastTwo squarefree index).nested
    (family.trackAt degreeAtLeastTwo squarefree index).initial epsilon positive
end OwnerFamily

end Purelib.RootIsolation.Owner.Family.Basic

end

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.RootIsolation.Owner.Family.Basic
open Purelib.Data.Gaussian
namespace OwnerFamily

/-- Every simultaneously refined owner box lies strictly inside its own original family box. -/
theorem refine_strict
    {p : CoefficientPolynomial} {count : Nat}
    (family : Owner.Family.Basic.OwnerFamily p count)
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) (index : Fin count) :
    ((family.refine degreeAtLeastTwo squarefree epsilon positive).owner
      index).box.StrictInterior (family.owner index).box :=
  (family.trackAt degreeAtLeastTwo squarefree index).strict
    (family.trackAt degreeAtLeastTwo squarefree index).initial epsilon positive
end OwnerFamily

end Purelib.RootIsolation.Owner.Family.Basic

end

