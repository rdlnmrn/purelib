module

import Purelib.Elab.Deriving.Repr
meta import Purelib.Elab.ConstructiveInjectivity

section
@[expose] public section

/-!
# Explicit finite failure states for partial progressive operations

Reciprocal, division, logarithm, chart transition, and branch selection are
not total operations on opaque CCL names.  Their constructors below consume a
finite evidence state and return either a constructed program or a visible
reason why the request cannot proceed.  Thus failure is data; it is never a
silent appeal to a completed nonzero value or a globally chosen branch.
-/

namespace Purelib.Calculus.Jet.Preparation.Diagnostic

/-- Identify the kind of finite evidence still needed by a partial construction.

Each tag names an unmet certificate obligation. A tag alone asserts neither invalidity of the input nor impossibility of
supplying that certificate. -/
inductive MissingCertificate where
  /-- A certificate separating the denominator from zero is missing. -/ | denominatorApartness
  /-- A certificate separating the output from zero is missing. -/ | outputApartness
  /-- A certificate for a safe logarithm chart is missing. -/ | safeLogarithmChart
  /-- A certificate for the required chart overlap is missing. -/ | chartOverlap
  /-- A certificate aligning the selected branches is missing. -/ | branchAlignment
  /-- A certificate for the quadratic transport law is missing. -/ | quadraticTransport
  /-- A certificate placing the input in the required disk is missing. -/ | inputDisk
deriving DecidableEq
derive_exposed_repr MissingCertificate

universe u

open Purelib.Calculus.Jet.Preparation in
set_option genInjectivity false in
/-- Return a constructed value or a tag describing missing finite evidence.

The rejected case records an outstanding certificate kind; it carries no proof that the value cannot be constructed. -/
inductive Decision (α : Type u) : Type u where
  /-- Retain the constructed value. -/ | accepted : α → Decision α
  /-- Record the kind of certificate still required. -/ | rejected : MissingCertificate →
    Decision α

constructive_injectivity Decision

namespace Decision

open Purelib.Calculus.Jet.Preparation
/-- Read the missing-certificate tag, returning none for an accepted value. -/
def missing? {α : Type u} : Diagnostic.Decision α → Option
  Diagnostic.MissingCertificate
  | .accepted _ => none
  | .rejected missing => some missing

/-- An accepted value has no missing-certificate tag. -/
@[simp] theorem missing?_accepted {α : Type u} (value : α) :
    (Diagnostic.Decision.accepted value).missing? = none := rfl

/-- A rejected construction reports its retained missing-certificate tag. -/
@[simp] theorem missing?_rejected {α : Type u}
    (missing : Diagnostic.MissingCertificate) :
    (Diagnostic.Decision.rejected (α := α) missing).missing? = some missing := rfl

end Decision
end Purelib.Calculus.Jet.Preparation.Diagnostic

end

section
@[expose] public section

/-!
# One certified finite program for progressive quadratic CCL calculus

The lower trace modules construct the arithmetic and analytic certificates.
This file packages those constructors into one indexed finite program.  The
index is the actual semantic `Trace`, so a program cannot pair unrelated value
and slope names: every node computes one common increment, base, output,
slope, remainder, and rational quadratic factor.

Partial nodes store their displayed lower-quadrance or disk evidence in the
constructor.  The total decision wrappers expose a precise missing
certificate.  Finally, the strengthened request contract combines the
quadratic law with persistent word extension, exact raw-parser semantics, and
the requested projective-cylinder diameter for every one of the five live CCL
channels.
-/

namespace Purelib.CCL.Progressive.TraceProgram
end Purelib.CCL.Progressive.TraceProgram

end
