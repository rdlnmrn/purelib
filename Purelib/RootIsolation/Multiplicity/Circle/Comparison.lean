module

public import Purelib.RootIsolation.Multiplicity.Circle.Argument
public import Purelib.Polynomial.Winding.Circle
import Purelib.Data.Int.Arithmetic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# The automatic rational-circle argument-principle comparison

The independent original chart-event reading and complete multiplicity-aware
original geometric inventory are constructed separately and retained together.
The same sufficient center-product payloads prove their agreement. No caller
root list, sufficient search budget or exact algebraic-root model is supplied.
-/

namespace Purelib.RootIsolation.Multiplicity.Circle

open Purelib.Polynomial
open Purelib.RationalFunctions.Curve.Canonical.Circle
open Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Clearance.Circle (Margin)

set_option genInjectivity false in
/-- An independently computed winding compared with the complete original radial multiplicity inventory.

The original whole-boundary paths and clearance remain indices. The result
stores the original phase computation, source margin, automatic original
inventory and actual sufficient argument payloads exactly once, with their
complete constructor equalities and resulting integer agreement.
-/
public structure Comparison {polynomial : CoefficientPolynomial} (paths : Boundary.Substitutions polynomial)
    (clearance : Boundary.Clearance paths) where
  /-- The original source coefficient table is normalized. -/
  normalized : polynomial.normalize = polynomial
  /-- The once-computed uniform original-polynomial circle margin. -/
  margin : Margin paths clearance
  /-- The margin is computed from these same retained boundary paths and certificate. -/
  margin_eq : margin = Margin.prepare paths clearance
  /-- The independent original chart-event phase reading. -/
  reading : Winding.Circle.Reading paths clearance
  /-- The reading is the actual original independent phase construction. -/
  reading_eq : reading = Winding.Circle.Reading.prepare paths clearance
  /-- The original automatic complete multiplicity-aware radial inventory. -/
  inventory : Inventory margin.toCertificate
  /-- The inventory is the original automatic constructor on the same source and margin. -/
  inventory_eq : inventory = Inventory.prepare margin.toCertificate normalized
  /-- The actual retained sufficient argument payloads for these same original observations and locations. -/
  argument : inventory.Argument
  /-- The argument consumes this same stored inventory without another side construction. -/
  argument_eq : argument = Inventory.Argument.prepare inventory
  /-- The original independent raw reading is four times the complete original inside count. -/
  raw_eq : Winding.Circle.raw paths = 4 * (inventory.insideCount : Int)
  /-- The actual independent integer winding equals the complete multiplicity-weighted inside count. -/
  winding_eq : reading.winding = (inventory.insideCount : Int)

constructive_injectivity Comparison

namespace Comparison

/-- Retain checked complete margin, independent reading, inventory and same-owner argument caches.

The original argument supplies the winding equality. Its stored numerical
observations are reused without invoking any isolation or refinement producer.
-/
@[expose] public def ofCaches {polynomial : CoefficientPolynomial} (paths : Boundary.Substitutions polynomial)
    (clearance : Boundary.Clearance paths) (normalized : polynomial.normalize = polynomial)
    (margin : Margin paths clearance) (marginEq : margin = Margin.prepare paths clearance)
    (reading : Winding.Circle.Reading paths clearance)
    (readingEq : reading = Winding.Circle.Reading.prepare paths clearance)
    (inventory : Inventory margin.toCertificate)
    (inventoryEq : inventory = Inventory.prepare margin.toCertificate normalized)
    (argument : inventory.Argument) (argumentEq : argument = Inventory.Argument.prepare inventory) :
    Comparison paths clearance :=
  let equality := argument.raw_eq_insideCount paths
  { normalized, margin, margin_eq := marginEq, reading, reading_eq := readingEq
    inventory, inventory_eq := inventoryEq, argument, argument_eq := argumentEq
    raw_eq := equality
    winding_eq := Purelib.Data.Int.Arithmetic.eq_of_mul_eq_mul_left (by decide : (4 : Int) ≠ 0)
      (reading.raw_eq.symm.trans equality) }

/-- Construct the independent reading, complete original inventory and same-cache sufficient comparison automatically.

The supplied complete boundary certificate computes every subsequent margin,
isolation request and sufficient refinement. The caller supplies no roots,
center approximations, refinement depth or comparison certificate.
-/
@[expose] public def prepare {polynomial : CoefficientPolynomial} (paths : Boundary.Substitutions polynomial)
    (clearance : Boundary.Clearance paths) (normalized : polynomial.normalize = polynomial) :
    Comparison paths clearance :=
  let margin := Margin.prepare paths clearance
  let reading := Winding.Circle.Reading.prepare paths clearance
  let inventory := Inventory.prepare margin.toCertificate normalized
  let argument := Inventory.Argument.prepare inventory
  ofCaches paths clearance normalized margin rfl reading rfl inventory rfl argument rfl

/-- Checked complete original caches recover the same independent circle comparison. -/
public theorem ofCaches_eq_prepare {polynomial : CoefficientPolynomial} (paths : Boundary.Substitutions polynomial)
    (clearance : Boundary.Clearance paths) (normalized : polynomial.normalize = polynomial)
    (margin : Margin paths clearance) (marginEq : margin = Margin.prepare paths clearance)
    (reading : Winding.Circle.Reading paths clearance)
    (readingEq : reading = Winding.Circle.Reading.prepare paths clearance)
    (inventory : Inventory margin.toCertificate)
    (inventoryEq : inventory = Inventory.prepare margin.toCertificate normalized)
    (argument : inventory.Argument) (argumentEq : argument = Inventory.Argument.prepare inventory) :
    ofCaches paths clearance normalized margin marginEq reading readingEq inventory inventoryEq argument argumentEq =
      prepare paths clearance normalized := by
  cases marginEq
  cases readingEq
  cases inventoryEq
  cases argumentEq
  rfl

/-- Restore the complete original polynomial circle comparison from its retained caches. -/
public theorem restore {polynomial : CoefficientPolynomial} {paths : Boundary.Substitutions polynomial}
    {clearance : Boundary.Clearance paths} (comparison : Comparison paths clearance) :
    comparison = prepare paths clearance comparison.normalized := by
  cases comparison with
  | mk normalized margin marginEq reading readingEq inventory inventoryEq argument argumentEq rawEq windingEq =>
      cases marginEq
      cases readingEq
      cases inventoryEq
      cases argumentEq
      rfl

/-- Both stored strict radial classes account for every original polynomial multiplicity. -/
public theorem total {polynomial : CoefficientPolynomial} {paths : Boundary.Substitutions polynomial}
    {clearance : Boundary.Clearance paths} (comparison : Comparison paths clearance) :
    comparison.inventory.insideCount + comparison.inventory.outsideCount = polynomial.natDegree :=
  comparison.inventory.total

end Comparison
end Purelib.RootIsolation.Multiplicity.Circle
