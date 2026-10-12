module
import Purelib.Data.Gaussian.Basic
public import Purelib.Approximation.Gaussian.Name.Coherent.CCL.Table
public import Purelib.Calculus.Jet.Progressive.Quadratic.Displayed

section
@[expose] public section

/-!
# Persistent CCL cursors for finite progressive calculus tables

The joint-request modules prove that every channel can emit a requested finite
prefix.  This module retains those cursors between requests.  A table state is
one displayed finite list of proof-bearing cursors; requesting more accuracy
and more bits maps the ordinary persistent CCL request over that list.  Hence
later words extend earlier words instead of restarting an encoder.

There is no stream or completed table.  Every operation consumes and returns
one finite list and one natural number of additional bits.
-/

namespace Purelib.Calculus.Gaussian.Progressive.QuadraticJet.CCL.Cursor

open Purelib.Approximation.Gaussian.Name.Coherent.CCL in
open Purelib.Data in
open Purelib.Calculus.Jet.Progressive.Quadratic.Displayed in
/-- Initialize a table of persistent CCL cursors for a displayed quadratic calculation.

The channels appear in the order increment, base, value, slope and remainder. Each cursor starts from its retained
coherent channel and can be passed to subsequent table requests. -/
def quadraticCursor {increment :
  Gaussian.Basic.Canonical}
    (calculation :
      CertifiedCalculation increment) :
    Table.TableCursor :=
  Table.TableCursor.initial
    [calculation.incrementChannel, calculation.baseChannel,
      calculation.valueChannel, calculation.slopeChannel,
      calculation.remainderChannel]

open Purelib.Approximation.Gaussian.Name.Coherent.CCL in
open Purelib.Data in
open Purelib.Calculus.Jet.Progressive.Quadratic.Displayed in
open Purelib.Calculus.Gaussian.Progressive.QuadraticJet.CCL in
/-- The initial cursor table retains exactly increment, base, value, slope and remainder. -/
@[simp] theorem quadraticCursor_channels {increment
  : Gaussian.Basic.Canonical}
    (calculation :
      CertifiedCalculation increment) :
    (quadraticCursor calculation).channels =
      [calculation.incrementChannel, calculation.baseChannel,
        calculation.valueChannel, calculation.slopeChannel,
        calculation.remainderChannel] :=
  Table.TableCursor.initial_channels _
end Purelib.Calculus.Gaussian.Progressive.QuadraticJet.CCL.Cursor

end
