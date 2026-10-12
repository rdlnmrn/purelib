module
meta import Purelib.Elab.ConstructiveInjectivity

import Purelib.Data.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Relation
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.RootIsolation.Owner.Family.Basic
public import Purelib.RootIsolation.Progressive.Chamber.Target
public import Purelib.RootIsolation.Track.Basic
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Bezout
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Stability
import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.RootIsolation.Owner.Local.Basic
import Purelib.RootIsolation.State.WindingOne.Basic

open Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table (CoefficientTable)

open Purelib.Data.Rat

open Purelib.Polynomial

open Purelib.RootIsolation

section
public section

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

namespace Purelib.RootIsolation.Progressive.Chamber.Basic
open Purelib.Data.Gaussian

set_option genInjectivity false in
/-- Finite input certificate for one progressive simple-root chamber.  The
reference polynomial is exact and squarefree, its degree-many owners are
already isolated, and the currently displayed coefficient states have
crossed the single computed chamber target. -/
structure SimpleRootChamber (reference :
  CoefficientTable) where
  /-- The reference polynomial has degree at least two. -/ degreeAtLeastTwo : 2 ≤ reference.degree
  /-- The retained squarefree certificate of the exact reference polynomial. -/ squarefree :
    Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate reference.polynomial
  /-- The degree-many original isolated owners of the reference polynomial. -/ owners : Owner.Family.Basic.OwnerFamily
    reference.polynomial reference.degree
  /-- The displayed reference coefficient allowances lie below the computed chamber target. -/ referenceSmall :
    Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable.AllowancesLt reference.entries
    (Progressive.Chamber.Target.simpleRootChamberTarget reference squarefree owners)
  /-- Every separated family of tracks in the reference large square has size at most the reference degree. -/
    referenceMaximality : ∀ {familyCount : Nat}
    (family : Fin familyCount → Track.Basic.WindingOneTrack
      reference.polynomial
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox reference.polynomial)),
    (∀ left right, left ≠ right →
      (family left).initial.box.Separated (family right).initial.box) →
    familyCount ≤ reference.degree

constructive_injectivity SimpleRootChamber

end Purelib.RootIsolation.Progressive.Chamber.Basic

end

section
public section

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

namespace Purelib.RootIsolation.Progressive.Chamber.Basic
open Purelib.Data.Gaussian
namespace SimpleRootChamber

/-- A degree-bounded index into the original chamber's retained owners. -/
abbrev Index {reference :
  CoefficientTable}
    (_chamber : Progressive.Chamber.Basic.SimpleRootChamber reference) := Fin reference.degree
end SimpleRootChamber

end Purelib.RootIsolation.Progressive.Chamber.Basic

end

section
public section

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

namespace Purelib.RootIsolation.Progressive.Chamber.Basic
open Purelib.Data.Gaussian
namespace SimpleRootChamber

/-- Read the single coefficient-stability target of the original simple-root chamber. -/
@[expose] def target {reference :
  CoefficientTable}
    (chamber : Progressive.Chamber.Basic.SimpleRootChamber reference) : Fraction.Rational :=
  Progressive.Chamber.Target.simpleRootChamberTarget reference chamber.squarefree chamber.owners
end SimpleRootChamber

end Purelib.RootIsolation.Progressive.Chamber.Basic

end

section
public section

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

namespace Purelib.RootIsolation.Progressive.Chamber.Basic
open Purelib.Data.Gaussian
namespace SimpleRootChamber

/-- The chamber target fits the Bézout stability budget of every retained owner box. -/
theorem target_le_bezout {reference :
  CoefficientTable}
    (chamber : Progressive.Chamber.Basic.SimpleRootChamber reference) (index : chamber.Index) :
    chamber.target ≤ reference.bezoutStabilityTarget chamber.squarefree
      (chamber.owners.owner index).box :=
  Progressive.Chamber.Target.simpleRootChamberTarget_le_bezout reference chamber.squarefree
    chamber.owners index
end SimpleRootChamber

end Purelib.RootIsolation.Progressive.Chamber.Basic

end

section
public section

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

namespace Purelib.RootIsolation.Progressive.Chamber.Basic
open Purelib.Data.Gaussian
namespace SimpleRootChamber

/-- The chamber target fits the coefficient-stability budget of every retained owner clearance. -/
theorem target_le_stability {reference :
  CoefficientTable}
    (chamber : Progressive.Chamber.Basic.SimpleRootChamber reference) (index : chamber.Index) :
    chamber.target ≤ reference.stabilityTarget
      (chamber.owners.owner index).box
      (chamber.owners.owner index).clearance :=
  Progressive.Chamber.Target.simpleRootChamberTarget_le_stability reference chamber.squarefree
    chamber.owners index
end SimpleRootChamber

end Purelib.RootIsolation.Progressive.Chamber.Basic

end

section
public section

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

namespace Purelib.RootIsolation.Progressive.Chamber.Basic
open Purelib.Data.Gaussian
namespace SimpleRootChamber

/-- The original simple-root chamber target is strictly positive. -/
theorem target_pos {reference :
  CoefficientTable}
    (chamber : Progressive.Chamber.Basic.SimpleRootChamber reference) : 0 < chamber.target :=
  Progressive.Chamber.Target.simpleRootChamberTarget_pos reference chamber.squarefree chamber.owners
end SimpleRootChamber

end Purelib.RootIsolation.Progressive.Chamber.Basic

end

section
section
public section

/-!
# Finite monodromy of persistent root owners

This file turns the local owner identity supplied by progressive polynomial
root continuation into a pathwise construction.  A path is an inductive
finite chain of certified chamber overlaps.  Each overlap carries rational
boxes on which the two displayed polynomials are connected by an explicit
finite Rouché certificate, together with the two-sided owner matching proved
by those boxes.  Folding the matchings returns a finite bijection; for a
closed chain this is the monodromy permutation.

There is no completed coefficient path, root, loop, or root space here.  All
objects are finite coefficient tables, rational boxes, finite winding
certificates, and functions between displayed finite index types.
-/

namespace Purelib.CCL.Progressive.Monodromy
end Purelib.CCL.Progressive.Monodromy

end

end
