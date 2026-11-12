module

public import Purelib.Polynomial.Elimination.Axis.Certificate
public import Purelib.Polynomial.Elimination.Axis.Separated.Prepared
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Retained checked preparations of the two original axis systems -/

public section

namespace Purelib.Polynomial.Elimination.Axis.Preparation

open Purelib
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Substitution.QuarterTurn

set_option genInjectivity false in
/-- The two retained checked Sylvester preparations of the same original source polynomial.

Each axis keeps its actual scaled inverse, nonzero scalar and acceptance or
fallback evidence. The horizontal system is the original quarter-turn of the
same source, rather than a separately supplied coefficient owner.
-/
structure Prepared (p : CoefficientPolynomial) where
  /-- The original vertical source's retained Sylvester preparation. -/
  vertical : Elimination.Separated.Preparation.Prepared p
  /-- The same source's original quarter-turned horizontal preparation. -/
  horizontal : Elimination.Separated.Preparation.Prepared (quarterTurn p)

constructive_injectivity Prepared

/-- Prepare both original axis systems with checked proposals and total certified fallback. -/
def prepare (p : CoefficientPolynomial) (nonzero : p.isZero = false) : Prepared p :=
  ⟨Elimination.Separated.Preparation.prepare p nonzero,
    Elimination.Separated.Preparation.prepare (quarterTurn p) (quarterTurn_nonzero p nonzero)⟩

namespace Prepared

/-- Read the actual maximum degree of the two retained rational eliminants.

The defining bound remains reducible when clients construct certificates and
checked loaders on these same two retained axis preparations. -/
@[expose] def degree {p : CoefficientPolynomial} (prepared : Prepared p) : Nat :=
  max prepared.vertical.eliminant.natDegree prepared.horizontal.eliminant.natDegree

/-- Supply the axis certificate from these same retained nonzero polynomials and checked cofactor laws.

The finite search bound is their actual maximum degree. The constructor remains
reducible for clients retaining its original line callbacks. Nonzero evaluations
produce coprime certificates from the same retained inverses, without invoking
the original symbolic scalar or inverse construction again.
-/
@[expose] def certificate {p : CoefficientPolynomial} (prepared : Prepared p)
    (nonzero : p.isZero = false) (positive : 0 < p.natDegree) :
    Certificate.AxisSafeCuts.AxisEliminationCertificate p prepared.degree :=
  { vertical := prepared.vertical.eliminant
    horizontal := prepared.horizontal.eliminant
    vertical_nonzero := prepared.vertical.eliminant_nonzero
    horizontal_nonzero := prepared.horizontal.eliminant_nonzero
    vertical_degree := Data.Nat.Order.le_max_left _ _
    horizontal_degree := Data.Nat.Order.le_max_right _ _
    vertical_coprime := fun parameter safe =>
      Separated.Prepared.vertical prepared.vertical nonzero positive parameter safe
    horizontal_coprime := fun parameter safe =>
      Separated.Prepared.horizontal prepared.horizontal nonzero positive parameter safe }

end Prepared

end Purelib.Polynomial.Elimination.Axis.Preparation

end
