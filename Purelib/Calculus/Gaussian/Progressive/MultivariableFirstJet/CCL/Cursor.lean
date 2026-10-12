module
public import Purelib.Approximation.Gaussian.Name.Coherent.CCL.Table
public import Purelib.Calculus.Jet.Progressive.Multivariable.First

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

namespace Purelib.Calculus.Gaussian.Progressive.MultivariableFirstJet.CCL.Cursor

open Purelib.Approximation.Gaussian.Name.Coherent.CCL in
open Purelib.Calculus.Jet.Progressive.Multivariable.First in
/-- Initialize a table of persistent CCL cursors for a finite progressive multivariable first jet.

The channels appear in the order value followed by all partial coefficients. Each cursor starts from its retained
coherent channel and can be passed to subsequent table requests. -/
def multivariableCursor
    (jet : MultivariableFirstJet) :
    Table.TableCursor :=
  Table.TableCursor.initial (jet.value :: jet.partials)

open Purelib.Approximation.Gaussian.Name.Coherent.CCL in
open Purelib.Calculus.Jet.Progressive.Multivariable.First in
open Purelib.Calculus.Gaussian.Progressive.MultivariableFirstJet.CCL in
/-- The initial cursor table retains exactly value followed by all partial coefficients. -/
@[simp] theorem
  multivariableCursor_channels
    (jet : MultivariableFirstJet) :
    (multivariableCursor jet).channels = jet.value :: jet.partials :=
  Table.TableCursor.initial_channels _

end Purelib.Calculus.Gaussian.Progressive.MultivariableFirstJet.CCL.Cursor

end
