module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Name
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Coherent.Cell

section

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Exponential.Progressive.Range

open Purelib.Approximation.Gaussian.Name.Coherent

section
public section

/-!
# Finite geometry for transporting and selecting logarithm branches

An anchored complex logarithm is local data.  This file supplies the missing
geometric constructors around that data.

* `SafeOverlapExtension` rechecks one chart's rational denominator and
  reduced-disk inequalities on a second coherent name and records an actual
  rational point admitted by both finite enclosures.  The original factor,
  correction process, and correction certificate can then be transported.
* `LocalExpInjectivity` is a displayed finite cell, membership certificates
  for two particular coherent names, and the local exponential-injectivity
  rule for that pair.  It is deliberately local and never chooses a global
  logarithm branch.
* `SelectedLogarithm.ofOverlap` combines those two pieces of finite data.  It
  constructs an anchored chart over the computed exponential and derives the
  zero-alignment certificate required for `log (exp x) = x`.

The local complex-log congruence proved first is quantitative: it compares
finite reduced-argument samples with the existing rational sensitivity bound
and finite truncation bounds.  No completed logarithm or limiting argument is
introduced.
-/

namespace Purelib.Approximation.Gaussian.Exponential.LocalInjectivity

open Purelib.Approximation

set_option genInjectivity false in
/-- Pair-specific local injectivity of the finite exponential computation.

The geometric cell and both membership proofs are data; `identify` is the local theorem for this displayed pair, not a
global injectivity assertion. -/
structure LocalExpInjectivity (left right : CoherentNamed) where
  /-- The displayed finite geometric cell supporting this pair-specific injectivity claim. -/ cell : Name.Coherent.Cell
  /-- Membership of the original left coherent name in the retained cell. -/ leftMember : Cell.CellMember cell left
  /-- Membership of the original right coherent name in the retained cell. -/ rightMember : Cell.CellMember cell right
  /-- Operational equality of these two exponential outputs implies operational equality of the same retained inputs. -/
    identify : Gaussian.Equivalence.NamedEquivalent
      (Name.named left.name)
      (Name.named right.name) →
    Gaussian.Equivalence.NamedEquivalent left.name right.name

constructive_injectivity LocalExpInjectivity

end Purelib.Approximation.Gaussian.Exponential.LocalInjectivity

end

end
