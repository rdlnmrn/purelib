import CCL.Calculus.HigherJet
import CCL.Progressive.FiniteTable

/-!
# Progressive finite Taylor and multivariable CCL tables

The displayed higher-jet layer stores Gaussian rationals.  Here every entry is
instead a coherent productive CCL channel.  All operations recurse over the
displayed finite coefficient lists, and every resulting table inherits one
computable joint request from `ProgressiveFiniteTable`.
-/

namespace CCL.ProgressiveHigherJet

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed
abbrev Table := CCL.ProgressiveFiniteTable.Table
abbrev RequestContract :=
  CCL.ProgressiveFiniteTable.RequestContract

def exactChannel (value : Gaussian) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.exact value

def addChannel (left right : CoherentNamed) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.add left right

def negChannel (value : CoherentNamed) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.neg value

def mulChannel (left right : CoherentNamed) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.mul left right

/-- Addition of low-to-high finite coefficient lists, retaining an unmatched
displayed tail exactly as the rational polynomial kernel does. -/
def addCoefficients : List CoherentNamed → List CoherentNamed →
    List CoherentNamed
  | [], right => right
  | left, [] => left
  | left :: leftTail, right :: rightTail =>
      addChannel left right :: addCoefficients leftTail rightTail

/-- Multiply every displayed coefficient by one coherent scalar. -/
def scaleCoefficients (factor : CoherentNamed) (coefficients : List CoherentNamed) :
    List CoherentNamed :=
  coefficients.map (mulChannel factor)

/-- Finite Cauchy multiplication of coherent coefficient channels. -/
def mulCoefficients : List CoherentNamed → List CoherentNamed →
    List CoherentNamed
  | [], _ => []
  | left :: leftTail, right =>
      addCoefficients (scaleCoefficients left right)
        (exactChannel 0 :: mulCoefficients leftTail right)

/-- Finite Horner composition of coherent coefficient tables. -/
def composeCoefficients : List CoherentNamed → List CoherentNamed →
    List CoherentNamed
  | [], _ => []
  | coefficient :: remaining, inner =>
      addCoefficients [coefficient]
        (mulCoefficients inner (composeCoefficients remaining inner))

def naturalChannel (degree : Nat) : CoherentNamed :=
  exactChannel ⟨(degree : Coordinate), 0⟩

/-- Formal differentiation of a finite coherent coefficient table. -/
def derivativeFrom : Nat → List CoherentNamed → List CoherentNamed
  | _, [] => []
  | degree, coefficient :: remaining =>
      mulChannel (naturalChannel degree) coefficient ::
        derivativeFrom (degree + 1) remaining

/-- A finite low-to-high table of productive CCL coefficient channels. -/
structure TaylorJet where
  coefficients : List CoherentNamed

namespace TaylorJet

def table (jet : TaylorJet) : Table := ⟨jet.coefficients⟩

def length (jet : TaylorJet) : Nat := jet.coefficients.length

def constant (value : CoherentNamed) : TaylorJet := ⟨[value]⟩

def add (left right : TaylorJet) : TaylorJet :=
  ⟨addCoefficients left.coefficients right.coefficients⟩

def neg (jet : TaylorJet) : TaylorJet :=
  ⟨jet.coefficients.map negChannel⟩

def scale (factor : CoherentNamed) (jet : TaylorJet) : TaylorJet :=
  ⟨scaleCoefficients factor jet.coefficients⟩

def mul (left right : TaylorJet) : TaylorJet :=
  ⟨mulCoefficients left.coefficients right.coefficients⟩

def compose (outer inner : TaylorJet) : TaylorJet :=
  ⟨composeCoefficients outer.coefficients inner.coefficients⟩

def truncate (count : Nat) (jet : TaylorJet) : TaylorJet :=
  ⟨jet.coefficients.take count⟩

def derivative (jet : TaylorJet) : TaylorJet :=
  match jet.coefficients with
  | [] => ⟨[]⟩
  | _constant :: remaining => ⟨derivativeFrom 1 remaining⟩

def derivativeOrder : TaylorJet → Nat → TaylorJet
  | jet, 0 => jet
  | jet, order + 1 => derivative (derivativeOrder jet order)

/-- Every coefficient of every constructed arithmetic or composition table
answers one common finite accuracy and CCL-bit request. -/
theorem coefficient_bitstream_and_allowance (jet : TaylorJet)
    {coefficient : CoherentNamed} (member : coefficient ∈ jet.coefficients)
    (target : Coordinate) (positive : 0 < target) (count : Nat) :
    RequestContract jet.coefficients coefficient target positive count :=
  jet.table.member_bitstream_and_allowance member target positive count

/-- Truncation transports the complete finite request contract for every
retained coefficient; discarded entries create no hidden obligation. -/
theorem truncated_coefficient_bitstream_and_allowance (jet : TaylorJet)
    (keep : Nat) {coefficient : CoherentNamed}
    (member : coefficient ∈ (jet.truncate keep).coefficients)
    (target : Coordinate) (positive : 0 < target) (count : Nat) :
    RequestContract (jet.truncate keep).coefficients coefficient target positive
      count :=
  (jet.truncate keep).coefficient_bitstream_and_allowance member target positive
    count

/-- The requested output list retains the displayed finite coefficient
arity. -/
theorem requestNames_length (jet : TaylorJet) (target : Coordinate)
    (positive : 0 < target) :
    (jet.table.requestNames target positive).length = jet.length :=
  jet.table.requestNames_length target positive

def coordinateGaussian (value : Coordinate) : Gaussian := ⟨value, 0⟩

/-- Exact specialization of the already proved displayed rational Taylor
table. -/
def ofDisplayed (jet : CCL.HigherJet.TaylorJet) : TaylorJet :=
  ⟨jet.coefficients.map (fun value => exactChannel (coordinateGaussian value))⟩

/-- Every same-budget centre of an exact specialization is literally the
corresponding displayed coefficient. -/
theorem ofDisplayed_requestCenters
    (jet : CCL.HigherJet.TaylorJet) (target : Coordinate)
    (positive : 0 < target) :
    (ofDisplayed jet).table.requestCenters target positive =
      jet.coefficients.map coordinateGaussian := by
  simpa only [ofDisplayed, table, exactChannel,
    CCL.ProgressiveFiniteTable.Table.exact, List.map_map,
    Function.comp_def] using
      CCL.ProgressiveFiniteTable.Table.exact_requestCenters
        (jet.coefficients.map coordinateGaussian) target positive

end TaylorJet

/-! ## Displayed finite-arity multivariable channels -/

def addPartials : List CoherentNamed → List CoherentNamed → List CoherentNamed :=
  addCoefficients

def scalePartials (factor : CoherentNamed) (partials : List CoherentNamed) :
    List CoherentNamed :=
  scaleCoefficients factor partials

def directionalSum : List CoherentNamed → List Gaussian → CoherentNamed
  | coefficient :: coefficients, direction :: directions =>
      addChannel (mulChannel coefficient (exactChannel direction))
        (directionalSum coefficients directions)
  | _, _ => exactChannel 0

/-- One progressive value channel and a displayed finite list of progressive
partial-coefficient channels. -/
structure MultivariableFirstJet where
  value : CoherentNamed
  partials : List CoherentNamed

namespace MultivariableFirstJet

def dimension (jet : MultivariableFirstJet) : Nat := jet.partials.length

def table (jet : MultivariableFirstJet) : Table :=
  ⟨jet.value :: jet.partials⟩

def constant (dimension : Nat) (value : CoherentNamed) :
    MultivariableFirstJet :=
  ⟨value, List.replicate dimension (exactChannel 0)⟩

def add (left right : MultivariableFirstJet) : MultivariableFirstJet :=
  ⟨addChannel left.value right.value,
    addPartials left.partials right.partials⟩

def neg (jet : MultivariableFirstJet) : MultivariableFirstJet :=
  ⟨negChannel jet.value, jet.partials.map negChannel⟩

def mul (left right : MultivariableFirstJet) : MultivariableFirstJet :=
  ⟨mulChannel left.value right.value,
    addPartials (scalePartials right.value left.partials)
      (scalePartials left.value right.partials)⟩

def compose (outerValue outerSlope : CoherentNamed)
    (inner : MultivariableFirstJet) : MultivariableFirstJet :=
  ⟨outerValue, scalePartials outerSlope inner.partials⟩

def DirectionValid (jet : MultivariableFirstJet)
    (direction : List Gaussian) : Prop :=
  direction.length = jet.dimension

/-- A finite directional channel.  The length certificate rules out silently
dropping a coordinate; the recursion itself remains total. -/
def directional (jet : MultivariableFirstJet) (direction : List Gaussian)
    (_valid : jet.DirectionValid direction) : CoherentNamed :=
  directionalSum jet.partials direction

/-- The constructed directional coefficient is itself a productive CCL
channel with an explicit finite request contract. -/
theorem directional_bitstream_and_allowance (jet : MultivariableFirstJet)
    (direction : List Gaussian) (valid : jet.DirectionValid direction)
    (target : Coordinate) (positive : 0 < target) (count : Nat) :
    RequestContract [jet.directional direction valid]
      (jet.directional direction valid) target positive count :=
  CCL.ProgressiveFiniteTable.sharedName_bitstream_and_allowance
    [jet.directional direction valid] List.mem_cons_self
    target positive count

/-- Every value or partial channel answers one joint finite request. -/
theorem channel_bitstream_and_allowance (jet : MultivariableFirstJet)
    {channel : CoherentNamed} (member : channel ∈ jet.table.channels)
    (target : Coordinate) (positive : 0 < target) (count : Nat) :
    RequestContract jet.table.channels channel target positive count :=
  jet.table.member_bitstream_and_allowance member target positive count

end MultivariableFirstJet

end CCL.ProgressiveHigherJet
