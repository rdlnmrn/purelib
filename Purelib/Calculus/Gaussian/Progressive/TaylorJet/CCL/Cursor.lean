module
public import Purelib.Approximation.Gaussian.Name.Coherent.CCL.Table
public import Purelib.Polynomial.Ascending.Gaussian.Progressive.Basic

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

namespace Purelib.Calculus.Gaussian.Progressive.TaylorJet.CCL.Cursor

open Purelib.Approximation.Gaussian.Name.Coherent.CCL in
open Purelib.Polynomial.Ascending.Gaussian.Progressive in
/-- Initialize a table of persistent CCL cursors for a finite progressive Taylor jet.

The channels appear in the order the retained coefficient list. Each cursor starts from its retained coherent channel
and can be passed to subsequent table requests. -/
def taylorCursor
    (jet : Basic.TaylorJet) : Table.TableCursor :=
  Table.TableCursor.initial jet.coefficients

open Purelib.Approximation.Gaussian.Name.Coherent.CCL in
open Purelib.Polynomial.Ascending.Gaussian.Progressive in
open Purelib.Calculus.Gaussian.Progressive.TaylorJet.CCL in
/-- The initial cursor table retains exactly the retained coefficient list. -/
@[simp] theorem taylorCursor_channels
    (jet : Basic.TaylorJet) :
    (taylorCursor jet).channels = jet.coefficients :=
  Table.TableCursor.initial_channels _
end Purelib.Calculus.Gaussian.Progressive.TaylorJet.CCL.Cursor

end
