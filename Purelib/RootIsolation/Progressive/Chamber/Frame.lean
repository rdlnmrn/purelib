module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.RootIsolation.Owner.Local.Basic
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
public import Purelib.RootIsolation.Progressive.Chamber.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.Owner.Family.Basic

open Purelib.Data

open Purelib.Polynomial

open Purelib.RootIsolation

/-!
# Frames of retained simple-root chambers

The original coefficient table indexes its complete simple-root chamber.
Its polynomial, degree and owner projections all read that same retained
table and certificate, with distinct finite indices selecting separated boxes.
-/

namespace Purelib.RootIsolation.Progressive.Chamber.Frame

set_option genInjectivity false in
/-- A complete degree-indexed frame retaining its original simple-root chamber.

The coefficient table and chamber certificate remain paired. That same
certificate retains squarefree data, original isolated owners and the
polynomial-degree maximality bound. -/
public structure ChamberFrame where
  /-- The original coefficient table defining this chamber frame. -/ reference :
    Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable
  /-- The complete simple-root chamber certificate for the retained reference table. -/ chamber :
    Basic.SimpleRootChamber reference

constructive_injectivity ChamberFrame

namespace ChamberFrame

/-- The degree of the frame's retained reference coefficient table. -/
public abbrev degree (frame : Progressive.Chamber.Frame.ChamberFrame) : Nat := frame.reference.degree
/-- A degree-bounded index of the original chamber frame. -/
public abbrev Index (frame : Progressive.Chamber.Frame.ChamberFrame) := Fin frame.degree

/-- Read the exact polynomial of the retained reference table. -/
@[expose] public def polynomial (frame : Progressive.Chamber.Frame.ChamberFrame) : (Dense.Basic.DensePolynomial
  Gaussian.Basic.Canonical) :=
  frame.reference.polynomial

/-- Read the original isolated owner at the supplied chamber index. -/
@[expose] public def owner (frame : Progressive.Chamber.Frame.ChamberFrame) (index : frame.Index) :
    Owner.Local.Basic.LocalOwner frame.polynomial :=
  frame.chamber.owners.owner index

/-- Distinct original chamber indices have positively separated owner boxes. -/
public theorem pairwiseSeparated (frame : Progressive.Chamber.Frame.ChamberFrame)
    (left right : frame.Index) (different : left ≠ right) :
    (frame.owner left).box.Separated (frame.owner right).box :=
  frame.chamber.owners.pairwiseSeparated left right different

end ChamberFrame

end Purelib.RootIsolation.Progressive.Chamber.Frame
