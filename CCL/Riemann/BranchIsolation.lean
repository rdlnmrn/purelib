import CCL.Riemann.AlgebraicDifferentials
import CCL.Bridge.Box
import CCL.Riemann.CoherentRoot

/-!
# Finite branch-point isolation for hyperelliptic curves

The squarefree certificate already stored in a `HyperellipticCurve` is fed
directly to the project-owned finite box theorem.  The result is a single
exact terminal in degree one or a degree-indexed family of pairwise-separated
shrinking tracks in higher degree.  Every site has one persistent arithmetic
CCL name and every finite prefix has exact parser semantics.
-/

namespace CCL.Riemann.BranchIsolation

open CCL.Riemann.AlgebraicDifferentials

abbrev Named := CCL.ProgressiveTransducer.Named
abbrev CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev PositiveResult (polynomial : GaussianPolynomial) :=
  CCL.BoxRFAPBridge.PositiveResult polynomial

/-- Both admitted hyperelliptic degree shapes have positive degree. -/
theorem degreePositive {genus : Nat}
    (curve : HyperellipticCurve genus) :
    0 < curve.polynomial.natDegree := by
  cases curve.degreeShape with
  | odd degreeEqual =>
      rw [degreeEqual]
      omega0
  | even degreeEqual =>
      rw [degreeEqual]
      omega0

/-- Automatically run finite squarefree branch isolation on the defining
polynomial. -/
def branchIsolation {genus : Nat}
    (curve : HyperellipticCurve genus) :
    PositiveResult curve.polynomial :=
  CCL.BoxRFAPBridge.provePositive
    { squarefree := curve.squarefree
      degreePositive := degreePositive curve }

/-- Number of displayed finite branch sites in a unified positive-degree
isolation result. -/
def siteCount {polynomial : GaussianPolynomial}
    (result : PositiveResult polynomial) : Nat :=
  match result with
  | .terminal _ _ => 1
  | .higher _ _ => polynomial.natDegree

theorem siteCount_eq_natDegree {polynomial : GaussianPolynomial}
    (result : PositiveResult polynomial) :
    siteCount result = polynomial.natDegree := by
  cases result with
  | terminal terminal degree =>
      exact degree.symm
  | higher boxes degree =>
      rfl

abbrev SiteIndex {polynomial : GaussianPolynomial}
    (result : PositiveResult polynomial) := Fin (siteCount result)

/-- Uniform persistent arithmetic name of a finite branch site.  A linear
terminal is named by its exact rational point; a higher-degree site uses the
corresponding shrinking winding-one track. -/
def siteName {polynomial : GaussianPolynomial}
    (result : PositiveResult polynomial) : SiteIndex result -> Named :=
  match result with
  | .terminal terminal _ => fun _ =>
      CCL.ProgressiveTransducer.Named.exact terminal.point
  | .higher boxes _ => fun index => boxes.arithmeticNameAt index

/-- Coherent arithmetic name of the same finite branch site.  Higher-degree
sites use one deterministic nested anchor sequence; the linear terminal is
the exact rational name. -/
def siteCoherentName {polynomial : GaussianPolynomial}
    (result : PositiveResult polynomial) : SiteIndex result -> CoherentNamed :=
  match result with
  | .terminal terminal _ => fun _ =>
      CCL.ProgressiveCoherence.CoherentNamed.exact terminal.point
  | .higher boxes _ => fun index =>
      CCL.Riemann.CoherentRoot.named (boxes.trackAt index)

/-- A displayed rational anchor for each finite site.  In higher degree it is
the anchor of the site's initial isolated box; the persistent name refines
that same box rather than replacing the site. -/
def siteAnchor {polynomial : GaussianPolynomial}
    (result : PositiveResult polynomial) : SiteIndex result -> Gaussian :=
  match result with
  | .terminal terminal _ => fun _ => terminal.point
  | .higher boxes _ => fun index => (boxes.trackAt index).initial.box.anchor

/-- Every branch site produces exactly every requested finite prefix. -/
theorem siteName_productive {polynomial : GaussianPolynomial}
    (result : PositiveResult polynomial) (index : SiteIndex result)
    (count : Nat) :
    (siteName result index).machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          (siteName result index).machine count).emitted /\
      (CCL.ProgressiveTransducer.advance
        (siteName result index).machine count).emitted.length = count :=
  (siteName result index).productive count

/-- Every emitted branch prefix retains exact finite parser semantics for the
same initial terminal or root box. -/
theorem siteName_exact {polynomial : GaussianPolynomial}
    (result : PositiveResult polynomial) (index : SiteIndex result)
    (count : Nat) :
    CCL.ProgressiveMachineSemantics.ExactCursor
      (siteName result index).process (siteName result index).state
      (CCL.ProgressiveTransducer.advance
        (siteName result index).machine count) :=
  CCL.ProgressiveMachineSemantics.Named.advance_exact
    (siteName result index) count

/-- Pairwise separation evidence.  The degree-one branch is empty because
`Fin 1` has no distinct pair; the higher branch returns the actual separated
initial root boxes. -/
def Separation {polynomial : GaussianPolynomial}
    (result : PositiveResult polynomial)
    (left right : SiteIndex result) : Prop :=
  match result with
  | .terminal _ _ => False
  | .higher boxes _ =>
      (boxes.trackAt left).initial.box.Separated
        (boxes.trackAt right).initial.box

theorem pairwiseSeparated {polynomial : GaussianPolynomial}
    (result : PositiveResult polynomial)
    (left right : SiteIndex result) (different : left ≠ right) :
    Separation result left right := by
  cases result with
  | terminal terminal degree =>
      have equal : left = right := by
        apply Fin.ext
        have leftBound := left.isLt
        have rightBound := right.isLt
        change left.val < 1 at leftBound
        change right.val < 1 at rightBound
        omega0
      exact (different equal).elim
  | higher boxes degree =>
      exact boxes.trackAt_pairwiseSeparated left right different

theorem siteAnchor_ne {polynomial : GaussianPolynomial}
    (result : PositiveResult polynomial)
    (left right : SiteIndex result) (different : left ≠ right) :
    siteAnchor result left ≠ siteAnchor result right := by
  cases result with
  | terminal terminal degree =>
      have equal : left = right := by
        apply Fin.ext
        have leftBound := left.isLt
        have rightBound := right.isLt
        change left.val < 1 at leftBound
        change right.val < 1 at rightBound
        omega0
      exact (different equal).elim
  | higher boxes degree =>
      exact (boxes.trackAt_pairwiseSeparated left right different).points_ne
        (boxes.trackAt left).initial.box.contains_anchor
        (boxes.trackAt right).initial.box.contains_anchor

/-- The exact finite branch-track interface consumed by the Riemann
construction.  It deliberately records only persistent site names, their
shrinking winding-one tracks, and pairwise separation.  The expensive global
maximality proof used to construct the automatic family is not repeated by
downstream topology or integration. -/
structure Data {genus : Nat} (curve : HyperellipticCurve genus) where
  siteCount : Nat
  count_eq : siteCount = curve.polynomial.natDegree
  nameAt : Fin siteCount -> Named
  coherentNameAt : Fin siteCount -> CoherentNamed
  anchorAt : Fin siteCount -> Gaussian
  trackAt : (degreeGtOne : 1 < curve.polynomial.natDegree) ->
    Fin siteCount ->
      CCL.BoxRFAPBridge.WindingOneTrack curve.polynomial
        (RFAP.GlobalWinding.largeSquareBox curve.polynomial)
  track_anchor_eq : forall
    (degreeGtOne : 1 < curve.polynomial.natDegree) (index : Fin siteCount),
    (trackAt degreeGtOne index).initial.box.anchor = anchorAt index
  trackAt_pairwiseSeparated : forall
    (degreeGtOne : 1 < curve.polynomial.natDegree)
    (left right : Fin siteCount), left ≠ right ->
      (trackAt degreeGtOne left).initial.box.Separated
        (trackAt degreeGtOne right).initial.box

/-- Convert the project-owned global finite isolator into the smaller branch
interface actually used by the Riemann modules. -/
def data {genus : Nat} (curve : HyperellipticCurve genus) : Data curve := by
  let result := branchIsolation curve
  cases resultEq : result with
  | terminal terminal degree =>
      exact
        { siteCount := 1
          count_eq := degree.symm
          nameAt := fun _ =>
            CCL.ProgressiveTransducer.Named.exact terminal.point
          coherentNameAt := fun _ =>
            CCL.ProgressiveCoherence.CoherentNamed.exact terminal.point
          anchorAt := fun _ => terminal.point
          trackAt := fun degreeGtOne => by
            have impossible : ¬1 < curve.polynomial.natDegree := by
              rw [degree]
              omega0
            exact (impossible degreeGtOne).elim
          track_anchor_eq := fun degreeGtOne => by
            have impossible : ¬1 < curve.polynomial.natDegree := by
              rw [degree]
              omega0
            exact (impossible degreeGtOne).elim
          trackAt_pairwiseSeparated := fun degreeGtOne => by
            have impossible : ¬1 < curve.polynomial.natDegree := by
              rw [degree]
              omega0
            exact (impossible degreeGtOne).elim }
  | higher boxes degree =>
      exact
        { siteCount := curve.polynomial.natDegree
          count_eq := rfl
          nameAt := boxes.arithmeticNameAt
          coherentNameAt := fun index =>
            CCL.Riemann.CoherentRoot.named (boxes.trackAt index)
          anchorAt := fun index => (boxes.trackAt index).initial.box.anchor
          trackAt := fun _ index => boxes.trackAt index
          track_anchor_eq := fun _ _ => rfl
          trackAt_pairwiseSeparated := fun _ left right different =>
            boxes.trackAt_pairwiseSeparated left right different }

/-- Build branch data directly from a displayed degree-indexed family of
pairwise-separated shrinking winding-one tracks.  This is the finite input
form used by small worked examples and externally audited isolations. -/
def Data.ofTracks {genus : Nat} (curve : HyperellipticCurve genus)
    (_degreeGtOne : 1 < curve.polynomial.natDegree)
    (tracks : Fin curve.polynomial.natDegree ->
      CCL.BoxRFAPBridge.WindingOneTrack curve.polynomial
        (RFAP.GlobalWinding.largeSquareBox curve.polynomial))
    (pairwise : forall left right, left ≠ right ->
      (tracks left).initial.box.Separated (tracks right).initial.box) :
    Data curve where
  siteCount := curve.polynomial.natDegree
  count_eq := rfl
  nameAt := fun index =>
    (CCL.Riemann.CoherentRoot.named (tracks index)).name
  coherentNameAt := fun index => CCL.Riemann.CoherentRoot.named (tracks index)
  anchorAt := fun index => (tracks index).initial.box.anchor
  trackAt := fun _ index => tracks index
  track_anchor_eq := fun _ _ => rfl
  trackAt_pairwiseSeparated := fun _ left right different =>
    pairwise left right different

/-- Extend one fully displayed winding-one state to a total shrinking track.
Unlike `trackOfRaw`, this constructor performs no preliminary extraction;
the caller has already supplied the four ambient-line clearances needed by
branch-cut construction. -/
def trackOfState {genus : Nat} (curve : HyperellipticCurve genus)
    (degreeGtOne : 1 < curve.polynomial.natDegree)
    (initial : RFAP.ShrinkingTrack.WindingOneState curve.polynomial
      (RFAP.GlobalWinding.largeSquareBox curve.polynomial)) :
    CCL.BoxRFAPBridge.WindingOneTrack curve.polynomial
      (RFAP.GlobalWinding.largeSquareBox curve.polynomial) := by
  have degreeAtLeastTwo : 2 ≤ curve.polynomial.natDegree := by omega0
  exact
    { initial := initial
      refine := fun current epsilon positive =>
        RFAP.ShrinkingTrack.refineState degreeAtLeastTwo curve.squarefree
          (RFAP.AxisSafeCuts.separatedAxisEliminationCertificate
            curve.polynomial curve.nonzero (degreePositive curve))
          current epsilon positive
      nested := by
        intro current epsilon positive
        exact RFAP.ShrinkingTrack.refineState_refines degreeAtLeastTwo
          curve.squarefree
          (RFAP.AxisSafeCuts.separatedAxisEliminationCertificate
            curve.polynomial curve.nonzero (degreePositive curve))
          current epsilon positive
      strict := by
        intro current epsilon positive
        exact RFAP.ShrinkingTrack.refineState_strict degreeAtLeastTwo
          curve.squarefree
          (RFAP.AxisSafeCuts.separatedAxisEliminationCertificate
            curve.polynomial curve.nonzero (degreePositive curve))
          current epsilon positive
      accurate := by
        intro current epsilon positive
        exact RFAP.ShrinkingTrack.refineState_accurate degreeAtLeastTwo
          curve.squarefree
          (RFAP.AxisSafeCuts.separatedAxisEliminationCertificate
            curve.polynomial curve.nonzero (degreePositive curve))
          current epsilon positive }

/-- Assemble explicit branch data from pairwise-separated winding-one
states.  The original states become refinement zero literally. -/
def Data.ofStates {genus : Nat} (curve : HyperellipticCurve genus)
    (degreeGtOne : 1 < curve.polynomial.natDegree)
    (states : Fin curve.polynomial.natDegree ->
      RFAP.ShrinkingTrack.WindingOneState curve.polynomial
        (RFAP.GlobalWinding.largeSquareBox curve.polynomial))
    (pairwise : forall left right, left ≠ right ->
      (states left).box.Separated (states right).box) :
    Data curve :=
  Data.ofTracks curve degreeGtOne
    (fun index => trackOfState curve degreeGtOne (states index))
    pairwise

/-- Turn one explicit nonzero-winding raw box into a total shrinking
winding-one track.  The Newton extraction supplies the four ambient-line
clearances required by branch-cut construction; all later refinements reuse
the curve's finite squarefree and axis-elimination certificates. -/
def trackOfRaw {genus : Nat} (curve : HyperellipticCurve genus)
    (degreeGtOne : 1 < curve.polynomial.natDegree)
    (raw : RFAP.RawSubdivision.RawWindingState curve.polynomial
      (RFAP.GlobalWinding.largeSquareBox curve.polynomial)) :
    CCL.BoxRFAPBridge.WindingOneTrack curve.polynomial
      (RFAP.GlobalWinding.largeSquareBox curve.polynomial) := by
  have degreeAtLeastTwo : 2 ≤ curve.polynomial.natDegree := by omega0
  let elimination :=
    RFAP.AxisSafeCuts.separatedAxisEliminationCertificate curve.polynomial
      curve.nonzero (degreePositive curve)
  let output := RFAP.NewtonBand.extract degreeAtLeastTwo curve.squarefree
    elimination raw (by decide :
      (0 : RFAP.ConstructiveFraction.Rational) < 1)
  let initial : RFAP.ShrinkingTrack.WindingOneState curve.polynomial
      (RFAP.GlobalWinding.largeSquareBox curve.polynomial) :=
    { box := output.box
      refinesAmbient := output.refinesAmbient
      proper := output.proper
      clearance := output.clearance
      rawWindingFour := output.rawWindingFour
      ambientLeftClearance := output.ambientLeftClearance
      ambientRightClearance := output.ambientRightClearance
      ambientBottomClearance := output.ambientBottomClearance
      ambientTopClearance := output.ambientTopClearance }
  exact RFAP.ShrinkingTrack.ofInitial degreeAtLeastTwo curve.squarefree
    elimination initial

/-- The extracted initial winding-one box lies strictly inside the raw box
from which its track was constructed. -/
theorem trackOfRaw_initial_strict {genus : Nat}
    (curve : HyperellipticCurve genus)
    (degreeGtOne : 1 < curve.polynomial.natDegree)
    (raw : RFAP.RawSubdivision.RawWindingState curve.polynomial
      (RFAP.GlobalWinding.largeSquareBox curve.polynomial)) :
    (trackOfRaw curve degreeGtOne raw).initial.box.StrictInterior raw.box := by
  unfold trackOfRaw
  exact (RFAP.NewtonBand.extract _ curve.squarefree _ raw _).strictCurrent

/-- Build branch data from a degree-indexed family of raw winding boxes whose
interiors are pairwise disjoint.  Strict Newton extraction turns those weak
interior separations into the positive closed-box gaps required downstream. -/
def Data.ofRawStates {genus : Nat} (curve : HyperellipticCurve genus)
    (degreeGtOne : 1 < curve.polynomial.natDegree)
    (raw : Fin curve.polynomial.natDegree ->
      RFAP.RawSubdivision.RawWindingState curve.polynomial
        (RFAP.GlobalWinding.largeSquareBox curve.polynomial))
    (pairwise : forall left right, left ≠ right ->
      (raw left).box.InteriorSeparated (raw right).box) :
    Data curve :=
  Data.ofTracks curve degreeGtOne
    (fun index => trackOfRaw curve degreeGtOne (raw index))
    (by
      intro left right different
      exact (pairwise left right different).strict_refinements
        (trackOfRaw_initial_strict curve degreeGtOne (raw left))
        (trackOfRaw_initial_strict curve degreeGtOne (raw right)))

namespace Data

abbrev Index {genus : Nat} {curve : HyperellipticCurve genus}
    (data : Data curve) := Fin data.siteCount

def name {genus : Nat} {curve : HyperellipticCurve genus}
    (data : Data curve) (index : Index data) : Named :=
  data.nameAt index

def coherentName {genus : Nat} {curve : HyperellipticCurve genus}
    (data : Data curve) (index : Index data) : CoherentNamed :=
  data.coherentNameAt index

def anchor {genus : Nat} {curve : HyperellipticCurve genus}
    (data : Data curve) (index : Index data) : Gaussian :=
  data.anchorAt index

/-- Reindex a displayed branch site by the polynomial degree.  This is a
definitionally finite cast justified by the exact root count returned by the
isolator. -/
def degreeIndex {genus : Nat} {curve : HyperellipticCurve genus}
    (data : Data curve) (index : Index data) :
    Fin curve.polynomial.natDegree :=
  Fin.cast data.count_eq index

/-- The actual shrinking track of a displayed finite branch site, available
whenever the curve has higher degree. -/
def track {genus : Nat} {curve : HyperellipticCurve genus}
    (data : Data curve) (degreeGtOne : 1 < curve.polynomial.natDegree)
    (index : Index data) :
    CCL.BoxRFAPBridge.WindingOneTrack curve.polynomial
      (RFAP.GlobalWinding.largeSquareBox curve.polynomial) :=
  data.trackAt degreeGtOne index

theorem track_initial_anchor {genus : Nat}
    {curve : HyperellipticCurve genus} (data : Data curve)
    (degreeGtOne : 1 < curve.polynomial.natDegree) (index : Index data) :
    (data.track degreeGtOne index).initial.box.anchor = data.anchor index := by
  exact data.track_anchor_eq degreeGtOne index

theorem name_productive {genus : Nat} {curve : HyperellipticCurve genus}
    (data : Data curve) (index : Index data) (count : Nat) :
    (name data index).machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          (name data index).machine count).emitted /\
      (CCL.ProgressiveTransducer.advance
        (name data index).machine count).emitted.length = count :=
  (name data index).productive count

theorem name_exact {genus : Nat} {curve : HyperellipticCurve genus}
    (data : Data curve) (index : Index data) (count : Nat) :
    CCL.ProgressiveMachineSemantics.ExactCursor
      (name data index).process (name data index).state
      (CCL.ProgressiveTransducer.advance
        (name data index).machine count) :=
  CCL.ProgressiveMachineSemantics.Named.advance_exact (name data index) count

theorem separated {genus : Nat} {curve : HyperellipticCurve genus}
    (data : Data curve) (degreeGtOne : 1 < curve.polynomial.natDegree)
    (left right : Index data) (different : left ≠ right) :
    (data.track degreeGtOne left).initial.box.Separated
      (data.track degreeGtOne right).initial.box :=
  data.trackAt_pairwiseSeparated degreeGtOne left right different

theorem anchor_ne {genus : Nat} {curve : HyperellipticCurve genus}
    (data : Data curve) (left right : Index data) (different : left ≠ right) :
    anchor data left ≠ anchor data right :=
  by
    have degreeGtOne : 1 < curve.polynomial.natDegree := by
      rw [← data.count_eq]
      by_contra small
      have countLeOne : data.siteCount <= 1 := Nat.le_of_not_gt small
      apply different
      apply Fin.ext
      have leftBound := left.isLt
      have rightBound := right.isLt
      omega0
    change data.anchorAt left ≠ data.anchorAt right
    rw [← data.track_anchor_eq degreeGtOne left,
      ← data.track_anchor_eq degreeGtOne right]
    exact (data.separated degreeGtOne left right different).points_ne
      (data.track degreeGtOne left).initial.box.contains_anchor
      (data.track degreeGtOne right).initial.box.contains_anchor

end Data

end CCL.Riemann.BranchIsolation
