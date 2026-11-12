module

public import Purelib.Data.Presentation
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Data
import Purelib.Data.Rat.Fraction.Order.Basic

namespace Purelib.Approximation.Gaussian.Enclosure.Ball.Presentation

open Purelib.Approximation.Gaussian.Enclosure
open Purelib.Approximation.Gaussian.Enclosure.Ball.Data

/-- A ball datum is admissible precisely when its squared radius is nonnegative. -/
@[expose] public def Valid (code : BallData) : Prop := 0 ≤ code.radiusSq

set_option genInjectivity false in
/-- The result of checking the squared radius of original ball data. -/
public inductive Check (code : BallData) where
  /-- The squared radius is nonnegative. -/ | valid (nonnegative : Valid code)
  /-- The squared radius is strictly negative. -/ | negativeRadius (negative : code.radiusSq < 0)

/-- Check the squared radius, retaining the applicable rational-order proof. -/
@[expose] public def check (code : BallData) : Check code :=
  if nonnegative : 0 ≤ code.radiusSq then .valid nonnegative
  else .negativeRadius (lt_of_not_ge nonnegative)

/-- Decide validity using the typed result of `check`. -/
@[expose] public def recognize (code : BallData) : Decidable (Valid code) :=
  match check code with
  | .valid nonnegative => .isTrue nonnegative
  | .negativeRadius negative => .isFalse (fun nonnegative => (not_lt_of_ge nonnegative) negative)

/-- Decide ball-data validity with the typed radius checker. -/
public instance (code : BallData) : Decidable (Valid code) := recognize code

/-- Ball data with a certified nonnegative squared radius. -/
public abbrev Display := {code : BallData // Valid code}

/-- Construct the original ball from its accepted numerical data. -/
@[expose] public def read (display : Display) : Ball :=
  ⟨display.val.center, display.val.radiusSq, display.property⟩

/-- Quote the retained numerical fields and certificate of an original ball. -/
@[expose] public def quote (ball : Ball) : Display :=
  ⟨BallData.ofBall ball, ball.radiusSq_nonneg⟩

/-- Two accepted displays have the same retained centre and squared radius. -/
@[expose] public def Same (left right : Display) : Prop := left.val = right.val

/-- Compare the original finite ball data by their structural equality decision. -/
@[expose] public def compare (left right : Display) : Decidable (Same left right) :=
  inferInstanceAs (Decidable (left.val = right.val))

/-- Decide equality of the retained fields of two valid ball displays. -/
public instance (left right : Display) : Decidable (Same left right) := compare left right

/-- Reading a quoted ball recovers the original ball, including its proof field. -/
public theorem read_quote (ball : Ball) : read (quote ball) = ball :=
  Ball.ext rfl rfl

/-- Quoting a read display recovers its original data and validity certificate. -/
public theorem quote_read (display : Display) : quote (read display) = display := by
  apply Subtype.ext
  rfl

/-- Display equality agrees exactly with equality of the original certified balls. -/
public theorem same_iff_read_eq (left right : Display) :
    Same left right ↔ read left = read right := by
  constructor
  · intro same
    exact Ball.ext (congrArg BallData.center same) (congrArg BallData.radiusSq same)
  · intro same
    exact congrArg BallData.ofBall same

/-!
## Gaussian ball data

* **Object and expressions:** `BallData` is the existing typed finite pair of a
  Gaussian rational centre and a rational squared radius; no text parser is used.
* **Recognition:** `check` accepts exactly nonnegative squared radii and gives
  `Check.negativeRadius` with a proof of strict negativity otherwise.
* **Equality:** `compare` decides equality of the retained fields, and
  `same_iff_read_eq` relates it to equality of the original `Ball`. Overlap or
  equal readings of distinct balls is a separate relation.
* **Constructions and operations:** `read` constructs the original ball;
  `quote` uses `BallData.ofBall`. `read_quote` and `quote_read` establish both
  round trips, including proof irrelevance for the certificate fields.
* **Termination and dependencies:** rational ordering and structural equality
  are finite decisions inherited from the original rational and Gaussian owners.
  The pinned proof system and runtime assumptions remain separate obligations.
* **Examples and non-examples:** zero squared radius is admissible; a negative
  squared radius is rejected. The reachable regression checks both cases and
  equality independent of the chosen nonnegativity proofs.
-/
/-- The explicit presentation of original Gaussian balls by their retained data. -/
@[expose] public def ball : Purelib.Data.Presentation BallData where
  Valid := Valid
  recognize := recognize
  Same := Same
  compare := compare
  same_laws := ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩

end Purelib.Approximation.Gaussian.Enclosure.Ball.Presentation
