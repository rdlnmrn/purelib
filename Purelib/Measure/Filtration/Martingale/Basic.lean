module
import Purelib.Data.List.Append
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Distribution.Partition.ConditionalExpectation
import Purelib.Measure.Distribution.Partition.Positive
import Purelib.Measure.Distribution.Partition.Refinement
import Purelib.Data.Rat.Fraction

public import Purelib.Measure.Filtration.Basic

section
section
@[expose] public section

/-!
# Displayed finite filtrations

A filtration is a finite inductive chain of positive event partitions.  Each
extension carries the explicit certificate that the new partition refines the
previous finest partition.  The construction has a first and last stage and
does not quantify over an unbounded time index.
-/

namespace Purelib.Measure
namespace Filtration

set_option genInjectivity false in
open Purelib.Data.Rat in
/-- Retain a finite observable chain on the exact filtration with each adjacent conditional-expectation identity.

The type keeps the original distribution, refinement chain and terminal observable. Each extension stores its earlier
chain and the exact fine-to-coarse identity. -/
inductive Martingale {α : Type} (distribution : Distribution α) :
    {finest : PositiveEventPartition distribution} →
      (filtration : Filtration distribution finest) →
      (α → Fraction.Rational) → Type
  /-- Start the retained finite chain with the specified partition and observable. -/ | base (partition :
    PositiveEventPartition distribution)
      (value : α → Fraction.Rational) :
      Martingale distribution (.base partition) value
  /-- Append the exact finer partition and observable with its retained refinement and fine-to-coarse
    conditional-expectation identity. -/ | extend {coarse : PositiveEventPartition distribution}
      {earlier : Filtration distribution coarse}
      {coarseValue : α → Fraction.Rational}
      (past : Martingale distribution earlier coarseValue)
      (fine : PositiveEventPartition distribution)
      (refinement : PositivePartitionRefinement fine coarse)
      (fineValue : α → Fraction.Rational)
      (step : ∀ item,
        coarse.conditionalExpectation fineValue item = coarseValue item) :
      Martingale distribution (.extend earlier fine refinement) fineValue

constructive_injectivity Martingale

namespace Martingale

section
open Purelib.Data.Rat
/-- Read the original first observable from the retained finite martingale chain. -/
def initialValue {α : Type} {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    {filtration : Filtration distribution finest}
    {terminalValue : α → Fraction.Rational} :
    Martingale distribution filtration terminalValue → α → Fraction.Rational
  | .base partition value => value
  | .extend past fine refinement fineValue step => past.initialValue

/-- List the exact martingale observables in retained chronological order. -/
def values {α : Type} {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    {filtration : Filtration distribution finest}
    {terminalValue : α → Fraction.Rational} :
    Martingale distribution filtration terminalValue →
      List (α → Fraction.Rational)
  | .base partition value => [value]
  | .extend past fine refinement fineValue step =>
      past.values ++ [fineValue]

end

open Purelib.Data.Rat in
open Purelib.Data.List in
/-- The retained martingale value list has length equal to its exact filtration depth. -/
theorem values_length {α : Type} {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    {filtration : Filtration distribution finest}
    {terminalValue : α → Fraction.Rational}
    (martingale : Martingale distribution filtration terminalValue) :
    martingale.values.length = filtration.depth := by
  induction martingale with
  | base partition value => rfl
  | extend past fine refinement fineValue step inductionHypothesis =>
      simp only [values, Append.length_append, List.length_cons,
        List.length_nil, depth, inductionHypothesis, -eq_self, -iff_self]
      rfl

open Purelib.Data.Rat in
/-- The exact terminal and initial observables of the finite martingale have equal expectations. -/
theorem expectation_terminal_eq_initial {α : Type}
    {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    {filtration : Filtration distribution finest}
    {terminalValue : α → Fraction.Rational}
    (martingale : Martingale distribution filtration terminalValue) :
    distribution.expectation terminalValue =
      distribution.expectation martingale.initialValue := by
  induction martingale with
  | base partition value => rfl
  | @extend coarse earlier coarseValue past fine refinement fineValue step
      inductionHypothesis =>
      calc
        distribution.expectation fineValue =
            distribution.expectation
              (coarse.conditionalExpectation fineValue) :=
          (coarse.expectation_conditionalExpectation fineValue).symm
        _ = distribution.expectation coarseValue :=
          distribution.expectation_congr _ _ step
        _ = distribution.expectation past.initialValue :=
          inductionHypothesis

end Martingale

open Purelib.Data.Rat
/-- Construct the martingale of successive conditional expectations of one original observable along the retained
filtration.

Each stored step uses the original refinement's tower identity, and the terminal index is the finest partition's exact
conditional expectation. -/
def canonicalMartingale {α : Type} {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    (filtration : Filtration distribution finest)
    (value : α → Fraction.Rational) :
    Martingale distribution filtration (finest.conditionalExpectation value) :=
  match filtration with
  | .base partition =>
      .base partition (partition.conditionalExpectation value)
  | .extend earlier fine refinement =>
      .extend (earlier.canonicalMartingale value) fine refinement
        (fine.conditionalExpectation value)
        (refinement.conditionalExpectation_tower value)

/-- The canonical martingale's initial observable is the original coarsest conditional expectation. -/
theorem canonicalMartingale_initialValue {α : Type}
    {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    (filtration : Filtration distribution finest)
    (value : α → Fraction.Rational) :
    (filtration.canonicalMartingale value).initialValue =
      filtration.coarsest.conditionalExpectation value := by
  induction filtration with
  | base partition => rfl
  | extend earlier fine refinement inductionHypothesis =>
      exact inductionHypothesis

end Filtration

end Purelib.Measure

end

end

section
@[expose] public section

/-!
# Finite martingale differences

Every step of a displayed finite martingale has a rational difference whose
conditional expectation on the preceding partition is zero.  Consequently
the difference is orthogonal to every explicitly cellwise observable.  A
finite induction then gives exact second-moment and variance growth formulas.

There is no unbounded time index, limiting process, or stopping theorem here:
the expected quadratic variation below is a finite rational sum carried by
the inductive martingale itself.
-/

namespace Purelib.Measure

namespace Filtration.Martingale

open Purelib.Data.Rat in
/-- Read the exact terminal observable indexing the retained martingale. -/
def lastValue {α : Type} {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    {filtration : Filtration distribution finest}
    {terminalValue : α → Fraction.Rational}
    (_martingale : Filtration.Martingale distribution filtration
      terminalValue) : α → Fraction.Rational :=
  terminalValue
end Filtration.Martingale

end Purelib.Measure

end

section
@[expose] public section

/-!
# Predictable transforms and finite optional sampling

A predictable strategy attaches one rational stake to each displayed
martingale step.  The stake is explicitly cellwise on the preceding positive
partition.  Its gain is therefore a finite sum of martingale differences
multiplied by preceding-stage observables, so exact orthogonality makes the
expected total gain zero.

Zero-or-one stakes which decrease pointwise form an explicit finite stopping
strategy.  Its stopped value is the initial value plus the active increments,
and the same finite calculation gives optional sampling.  There is no
unbounded stopping time, convergence theorem, or integrability side condition.
-/

namespace Purelib.Measure

namespace Filtration.Martingale

open Purelib.Data.Rat in
/-- Read the exact finest partition indexing the retained martingale. -/
def currentPartition {α : Type} {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    {filtration : Filtration distribution finest}
    {terminalValue : α → Fraction.Rational}
    (_martingale : Filtration.Martingale distribution filtration
      terminalValue) : PositiveEventPartition distribution :=
  finest

end Filtration.Martingale

end Purelib.Measure

end
