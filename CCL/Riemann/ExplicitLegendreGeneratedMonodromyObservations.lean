import CCL.Riemann.ExplicitLegendreGeneratedMonodromy

/-!
# Finite observations of the generated Legendre monodromy example

This downstream facade exposes the concrete rational base point, certified
paths and braid words, exact homology matrices, and caller-bounded CCL
observations of the normalized ratio and all three dual loop transforms.
Every observation is one finite refinement with a rational ball, a rational
semantic allowance, and a productive prefix contract.  No completed complex
period or global upper-half-plane point is introduced.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

abbrev ObservationBall := CCL.ArithmeticEnclosures.Ball
abbrev ObservationName := CCL.ProgressiveTransducer.Named

/-! ## Concrete paths, words, and exact matrices -/

/-- The explicit Gaussian-rational base parameter `1/4 + 2 i`. -/
def generatedBaseParameter : Gaussian :=
  CCL.Riemann.ExplicitLegendreSegment.sourceParameter

@[simp] theorem generatedBaseParameter_eq :
    generatedBaseParameter = (show Gaussian from ⟨1 / 4, 2⟩) := rfl

def generatedZeroPath :=
  CCL.Riemann.ExplicitLegendreOneLoop.standardLoops.zeroPath

def generatedOnePath :=
  CCL.Riemann.ExplicitLegendreOneLoop.standardLoops.onePath

def generatedInfinityPath :=
  CCL.Riemann.ExplicitLegendreOneLoop.standardLoops.infinityPath

def generatedProductPath :=
  CCL.Riemann.ExplicitLegendreOneLoop.standardLoops.productPath

def generatedZeroWord : CCL.Knot.FiniteBraid.Word 3 := generatedZeroPath.word

def generatedOneWord : CCL.Knot.FiniteBraid.Word 3 := generatedOnePath.word

def generatedInfinityWord : CCL.Knot.FiniteBraid.Word 3 :=
  generatedInfinityPath.word

def generatedProductWord : CCL.Knot.FiniteBraid.Word 3 :=
  generatedProductPath.word

/-- The displayed zero-loop word is certified as the standard pure braid. -/
theorem generatedZeroWord_standard :
    CCL.Knot.ArtinRelations.Equivalent generatedZeroWord
      CCL.Riemann.LegendreMonodromy.zeroBraid :=
  CCL.Riemann.ExplicitLegendreOneLoop.standardLoops.zeroWord

/-- The displayed one-loop word is certified as the standard pure braid. -/
theorem generatedOneWord_standard :
    CCL.Knot.ArtinRelations.Equivalent generatedOneWord
      CCL.Riemann.LegendreMonodromy.oneBraid :=
  CCL.Riemann.ExplicitLegendreOneLoop.standardLoops.oneWord

def generatedZeroHomologyMatrix :
    CCL.Riemann.LegendrePicardLefschetz.IntegralMatrix :=
  CCL.Riemann.LegendrePicardLefschetz.wordMatrix generatedZeroWord

def generatedOneHomologyMatrix :
    CCL.Riemann.LegendrePicardLefschetz.IntegralMatrix :=
  CCL.Riemann.LegendrePicardLefschetz.wordMatrix generatedOneWord

def generatedInfinityHomologyMatrix :
    CCL.Riemann.LegendrePicardLefschetz.IntegralMatrix :=
  CCL.Riemann.LegendrePicardLefschetz.wordMatrix generatedInfinityWord

def generatedProductHomologyMatrix :
    CCL.Riemann.LegendrePicardLefschetz.IntegralMatrix :=
  CCL.Riemann.LegendrePicardLefschetz.wordMatrix generatedProductWord

/-- Dual matrices acting on the columns of periods evaluated on the
transported homology bases. -/
def generatedZeroPeriodMatrix :
    CCL.Riemann.LegendrePicardLefschetz.IntegralMatrix :=
  CCL.Riemann.LegendrePicardLefschetz.periodMatrix generatedZeroWord

def generatedOnePeriodMatrix :
    CCL.Riemann.LegendrePicardLefschetz.IntegralMatrix :=
  CCL.Riemann.LegendrePicardLefschetz.periodMatrix generatedOneWord

def generatedInfinityPeriodMatrix :
    CCL.Riemann.LegendrePicardLefschetz.IntegralMatrix :=
  CCL.Riemann.LegendrePicardLefschetz.periodMatrix generatedInfinityWord

def generatedProductPeriodMatrix :
    CCL.Riemann.LegendrePicardLefschetz.IntegralMatrix :=
  CCL.Riemann.LegendrePicardLefschetz.periodMatrix generatedProductWord

theorem generatedZeroHomologyMatrix_eq :
    generatedZeroHomologyMatrix =
      CCL.Riemann.LegendreMonodromy.zeroMatrix :=
  CCL.Riemann.ExplicitLegendreOneLoop.standardLoops.zeroPath_matrix

theorem generatedOneHomologyMatrix_eq :
    generatedOneHomologyMatrix =
      CCL.Riemann.LegendreMonodromy.oneMatrix :=
  CCL.Riemann.ExplicitLegendreOneLoop.standardLoops.onePath_matrix

theorem generatedInfinityHomologyMatrix_eq :
    generatedInfinityHomologyMatrix =
      CCL.Riemann.LegendreMonodromy.infinityMatrix :=
  CCL.Riemann.ExplicitLegendreOneLoop.standardLoops.infinityPath_matrix

theorem generatedProductHomologyMatrix_eq :
    generatedProductHomologyMatrix =
      RFAP.ConstructiveFiniteMatrix.identity :=
  CCL.Riemann.ExplicitLegendreOneLoop.standardLoops.productPath_matrix

theorem generatedZeroPeriodMatrix_eq :
    generatedZeroPeriodMatrix =
      CCL.Riemann.LegendreMonodromy.zeroPeriodMatrix :=
  CCL.Riemann.ExplicitLegendreOneLoop.standardLoops.zeroPath_periodMatrix

theorem generatedOnePeriodMatrix_eq :
    generatedOnePeriodMatrix =
      CCL.Riemann.LegendreMonodromy.onePeriodMatrix :=
  CCL.Riemann.ExplicitLegendreOneLoop.standardLoops.onePath_periodMatrix

theorem generatedInfinityPeriodMatrix_eq :
    generatedInfinityPeriodMatrix =
      CCL.Riemann.LegendreMonodromy.infinityPeriodMatrix :=
  CCL.Riemann.ExplicitLegendreOneLoop.standardLoops.infinityPath_periodMatrix

theorem generatedProductPeriodMatrix_eq :
    generatedProductPeriodMatrix =
      RFAP.ConstructiveFiniteMatrix.identity :=
  CCL.Riemann.ExplicitLegendreOneLoop.standardLoops.productPath_periodMatrix

/-! ## Productive outputs at the generated normalized fibre -/

def generatedNormalizedOutput (token : Unit) : CoherentNamed :=
  (generatedMonodromyBase token).ratio

def generatedZeroOutput (token : Unit) : CoherentNamed :=
  CCL.Riemann.LegendrePeriodMonodromy.zeroAffineTransform
    (generatedMonodromyBase token).ratio

def generatedOneOutput (token : Unit) : CoherentNamed :=
  CCL.Riemann.LegendrePeriodMonodromy.oneTransform
    (generatedOnePreparation token)

def generatedInfinityOutput (token : Unit) : CoherentNamed :=
  CCL.Riemann.LegendrePeriodMonodromy.infinityTransform
    (generatedInfinityPreparation token)

/-- The public zero-loop observation channel is the productive ratio of the
two actual zero-loop transported period coordinates. -/
def generatedZeroOutput_transport (token : Unit) :
    CCL.OperationalEquivalence.NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        ((generatedMonodromyData token).zeroPeriods 0)
        (generatedZeroOutput token)).name
      ((generatedMonodromyData token).zeroPeriods 1).name := by
  simpa only [generatedZeroOutput] using generatedZeroProductiveTransport token

/-- The public one-loop observation channel is the productive ratio of the
two actual one-loop transported period coordinates. -/
def generatedOneOutput_transport (token : Unit) :
    CCL.OperationalEquivalence.NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        ((generatedMonodromyData token).onePeriods 0)
        (generatedOneOutput token)).name
      ((generatedMonodromyData token).onePeriods 1).name := by
  simpa only [generatedOneOutput] using generatedOneProductiveTransport token

/-- The public infinity-loop observation channel is the productive ratio of
the two actual infinity-loop transported period coordinates. -/
def generatedInfinityOutput_transport (token : Unit) :
    CCL.OperationalEquivalence.NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        ((generatedMonodromyData token).infinityPeriods 0)
        (generatedInfinityOutput token)).name
      ((generatedMonodromyData token).infinityPeriods 1).name := by
  simpa only [generatedInfinityOutput] using
    generatedInfinityProductiveTransport token

/-- One finite table keeps the base ratio and all three transformed outputs
on the same caller-selected request budget. -/
def generatedObservationChannels (token : Unit) : List CoherentNamed :=
  [generatedNormalizedOutput token, generatedZeroOutput token,
    generatedOneOutput token, generatedInfinityOutput token]

theorem generatedNormalizedOutput_mem (token : Unit) :
    generatedNormalizedOutput token ∈ generatedObservationChannels token :=
  List.Mem.head _

theorem generatedZeroOutput_mem (token : Unit) :
    generatedZeroOutput token ∈ generatedObservationChannels token :=
  List.Mem.tail _ (List.Mem.head _)

theorem generatedOneOutput_mem (token : Unit) :
    generatedOneOutput token ∈ generatedObservationChannels token :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

theorem generatedInfinityOutput_mem (token : Unit) :
    generatedInfinityOutput token ∈ generatedObservationChannels token :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

/-- The retained finite name after the common request for one selected
channel. -/
def generatedObservationName (token : Unit) (value : CoherentNamed)
    (target : Coordinate) (positive : 0 < target) : ObservationName :=
  CCL.ProgressiveFiniteTable.sharedName (generatedObservationChannels token)
    value target positive

def generatedObservationBall (token : Unit) (value : CoherentNamed)
    (target : Coordinate) (positive : 0 < target) : ObservationBall :=
  let observed := generatedObservationName token value target positive
  observed.process.ball observed.state

/-- Semantic coherence allowance retained for the same finite state as the
displayed observation ball. -/
def generatedObservationAllowance (token : Unit) (value : CoherentNamed)
    (target : Coordinate) (positive : 0 < target) : Coordinate :=
  value.coherent.allowance
    (generatedObservationName token value target positive).state

def generatedNormalizedObservation (token : Unit) (target : Coordinate)
    (positive : 0 < target) : ObservationName :=
  generatedObservationName token (generatedNormalizedOutput token)
    target positive

def generatedZeroObservation (token : Unit) (target : Coordinate)
    (positive : 0 < target) : ObservationName :=
  generatedObservationName token (generatedZeroOutput token) target positive

def generatedOneObservation (token : Unit) (target : Coordinate)
    (positive : 0 < target) : ObservationName :=
  generatedObservationName token (generatedOneOutput token) target positive

def generatedInfinityObservation (token : Unit) (target : Coordinate)
    (positive : 0 < target) : ObservationName :=
  generatedObservationName token (generatedInfinityOutput token)
    target positive

/-! ## Caller-bounded enclosure, allowance, and prefix contracts -/

theorem generatedObservationBall_radius_lt (token : Unit)
    (value : CoherentNamed) (target : Coordinate) (positive : 0 < target) :
    (generatedObservationBall token value target positive).radiusSq < target :=
  CCL.ProgressiveFiniteTable.sharedName_radius_lt
    (generatedObservationChannels token) value positive

theorem generatedNormalizedAllowance_lt (token : Unit)
    (target : Coordinate) (positive : 0 < target) :
    generatedObservationAllowance token (generatedNormalizedOutput token)
      target positive < target :=
  CCL.ProgressiveFiniteTable.sharedName_allowance_lt
    (generatedObservationChannels token) (generatedNormalizedOutput_mem token)
    positive

theorem generatedZeroAllowance_lt (token : Unit)
    (target : Coordinate) (positive : 0 < target) :
    generatedObservationAllowance token (generatedZeroOutput token)
      target positive < target :=
  CCL.ProgressiveFiniteTable.sharedName_allowance_lt
    (generatedObservationChannels token) (generatedZeroOutput_mem token)
    positive

theorem generatedOneAllowance_lt (token : Unit)
    (target : Coordinate) (positive : 0 < target) :
    generatedObservationAllowance token (generatedOneOutput token)
      target positive < target :=
  CCL.ProgressiveFiniteTable.sharedName_allowance_lt
    (generatedObservationChannels token) (generatedOneOutput_mem token)
    positive

theorem generatedInfinityAllowance_lt (token : Unit)
    (target : Coordinate) (positive : 0 < target) :
    generatedObservationAllowance token (generatedInfinityOutput token)
      target positive < target :=
  CCL.ProgressiveFiniteTable.sharedName_allowance_lt
    (generatedObservationChannels token) (generatedInfinityOutput_mem token)
    positive

theorem generatedNormalizedRequest (token : Unit) (target : Coordinate)
    (positive : 0 < target) (count : Nat) :
    CCL.ProgressiveFiniteTable.RequestContract
      (generatedObservationChannels token) (generatedNormalizedOutput token)
      target positive count :=
  CCL.ProgressiveFiniteTable.sharedName_bitstream_and_allowance
    (generatedObservationChannels token) (generatedNormalizedOutput_mem token)
    target positive count

theorem generatedZeroRequest (token : Unit) (target : Coordinate)
    (positive : 0 < target) (count : Nat) :
    CCL.ProgressiveFiniteTable.RequestContract
      (generatedObservationChannels token) (generatedZeroOutput token)
      target positive count :=
  CCL.ProgressiveFiniteTable.sharedName_bitstream_and_allowance
    (generatedObservationChannels token) (generatedZeroOutput_mem token)
    target positive count

theorem generatedOneRequest (token : Unit) (target : Coordinate)
    (positive : 0 < target) (count : Nat) :
    CCL.ProgressiveFiniteTable.RequestContract
      (generatedObservationChannels token) (generatedOneOutput token)
      target positive count :=
  CCL.ProgressiveFiniteTable.sharedName_bitstream_and_allowance
    (generatedObservationChannels token) (generatedOneOutput_mem token)
    target positive count

theorem generatedInfinityRequest (token : Unit) (target : Coordinate)
    (positive : 0 < target) (count : Nat) :
    CCL.ProgressiveFiniteTable.RequestContract
      (generatedObservationChannels token) (generatedInfinityOutput token)
      target positive count :=
  CCL.ProgressiveFiniteTable.sharedName_bitstream_and_allowance
    (generatedObservationChannels token) (generatedInfinityOutput_mem token)
    target positive count

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
