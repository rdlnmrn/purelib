module

public import Purelib.Riemann.RootContinuation.CoherentRoot.Comparison
public import Purelib.Riemann.RootContinuation.CoherentRoot.Family
public import Purelib.RootIsolation.Exact.Ownership.Prepare
public import Purelib.RootIsolation.Track.Transport
import Purelib.Data.List.Pairwise
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Identification through an original prepared root partition

Owner selection retains its actual assignment-radius state. Reusing that state
as the start of the original refinement program gives a common nested track,
and comparisons connect both original channels to the partition's cached root.
The finite owner index then decides equality for these prepared same-polynomial
inputs, with a quantitative certificate at distinct original partition owners.
-/

public section

namespace Purelib.Riemann.RootContinuation.CoherentRoot

open Purelib.RootIsolation
open Purelib.Polynomial
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Geometry.Rational

set_option genInjectivity false in
/-- A root's original channel, retained assignment state and comparisons to a cached partition owner.

Both comparisons consume the same retained intermediate root certificate. The
partition index and its cache remain dependent on the original isolation output.
-/
structure Assignment {polynomial : GaussianPolynomial} {ambient : Box} {count : Nat}
    (output : Exact.Basic.Output polynomial ambient count) (cache : Family output.tracks)
    {track : WindingOneTrack polynomial ambient} (root : CertifiedName track) where
  /-- The actual selection and assignment-radius state computed from the original track. -/
  selection : Exact.Ownership.Basic.OwnerSelection output track
  /-- The cached root using the original refiner from its retained assignment state. -/
  intermediate : CertifiedName (track.atState selection.refined)
  /-- The original input channel agrees with the actual intermediate root channel. -/
  source_intermediate : NamedEquivalent root.value.name intermediate.value.name
  /-- The selected original cached owner agrees with that same intermediate root channel. -/
  owner_intermediate : NamedEquivalent (cache.get selection.owner).value.name intermediate.value.name

constructive_injectivity Assignment

namespace Assignment

/-- Connect an original cached root to a supplied original owner selection using its retained state.

The intermediate root is built once from the selection's actual state. Strict
containment in both original boxes proves the two all-input comparisons without
rerunning either isolation or the assignment-radius refinement.
-/
@[expose] def ofSelection {polynomial : GaussianPolynomial} {ambient : Box} {count : Nat}
    (input : FTA.Squarefree.Input polynomial)
    (output : Exact.Basic.Output polynomial ambient count) (cache : Family output.tracks)
    {track : WindingOneTrack polynomial ambient} (root : CertifiedName track)
    (selection : Exact.Ownership.Basic.OwnerSelection output track) : Assignment output cache root :=
  let intermediate := certifiedName (track.atState selection.refined) input.degreePositive
  { selection := selection
    intermediate := intermediate
    source_intermediate := root.equivalent_nested input intermediate selection.refined_strict_source
    owner_intermediate := (cache.get selection.owner).equivalent_nested input intermediate selection.refined_strict }

/-- Compute one original owner selection and connect the actual root channel to its cached owner. -/
@[expose] def select {polynomial : GaussianPolynomial} {ambient : Box} {count : Nat}
    (input : FTA.Squarefree.Input polynomial)
    (output : Exact.Basic.Output polynomial ambient count) (cache : Family output.tracks)
    {track : WindingOneTrack polynomial ambient} (root : CertifiedName track)
    (supported : track.initial.box.Refines output.support) : Assignment output cache root :=
  let selection := Exact.Ownership.Prepare.selectOutputOwner input.degreeAtLeastTwo input.squarefree
    input.elimination output track supported
  ofSelection input output cache root selection

/-- Compare the original input channel with the actual cached root at its retained owner index. -/
@[expose] def equivalent {polynomial : GaussianPolynomial} {ambient : Box} {count : Nat}
    {output : Exact.Basic.Output polynomial ambient count} {cache : Family output.tracks}
    {track : WindingOneTrack polynomial ambient} {root : CertifiedName track}
    (assignment : Assignment output cache root) :
    NamedEquivalent root.value.name (cache.get assignment.selection.owner).value.name :=
  assignment.source_intermediate.trans assignment.owner_intermediate.symm

/-- Equal original owner indices give a comparison between both original input channels. -/
@[expose] def sameOwner {polynomial : GaussianPolynomial} {ambient : Box} {count : Nat}
    {output : Exact.Basic.Output polynomial ambient count} {cache : Family output.tracks}
    {firstTrack secondTrack : WindingOneTrack polynomial ambient}
    {first : CertifiedName firstTrack} {second : CertifiedName secondTrack}
    (left : Assignment output cache first) (right : Assignment output cache second)
    (same : left.selection.owner = right.selection.owner) : NamedEquivalent first.value.name second.value.name := by
  have leftComparison := left.equivalent
  rewrite [same] at leftComparison
  exact leftComparison.trans right.equivalent.symm

end Assignment

set_option genInjectivity false in
/-- A quantitative difference between original input roots assigned to distinct cached partition owners.

The positive gap belongs to their actual original owner boxes. The two retained
assignments link that gap to the original numerical inputs and reject any
claimed operational comparison between those original channels.
-/
structure Distinction {polynomial : GaussianPolynomial} {ambient : Box} {count : Nat}
    {output : Exact.Basic.Output polynomial ambient count} {cache : Family output.tracks}
    {firstTrack secondTrack : WindingOneTrack polynomial ambient}
    {first : CertifiedName firstTrack} {second : CertifiedName secondTrack}
    (left : Assignment output cache first) (right : Assignment output cache second) where
  /-- The original retained partition indices differ. -/
  different : left.selection.owner ≠ right.selection.owner
  /-- The computed positive coordinate gap at those same original owner boxes. -/
  separation : Box.SeparationCertificate (output.tracks.get left.selection.owner).initial.box
    (output.tracks.get right.selection.owner).initial.box
  /-- This positive gap excludes any comparison between the original input channels. -/
  rejects : NamedEquivalent first.value.name second.value.name → False

constructive_injectivity Distinction

namespace Assignment

/-- Compute a quantitative distinction from unequal original owner indices and retained comparisons. -/
@[expose] def distinguish {polynomial : GaussianPolynomial} {ambient : Box} {count : Nat}
    {output : Exact.Basic.Output polynomial ambient count} {cache : Family output.tracks}
    {firstTrack secondTrack : WindingOneTrack polynomial ambient}
    {first : CertifiedName firstTrack} {second : CertifiedName secondTrack}
    (left : Assignment output cache first) (right : Assignment output cache second)
    (different : left.selection.owner ≠ right.selection.owner) : Distinction left right :=
  let separation := Box.separationCertificate (output.tracks_get_separated _ _ different)
  { different := different
    separation := separation
    rejects := fun equivalent =>
      (cache.get left.selection.owner).not_equivalent_of_separation (cache.get right.selection.owner) separation
        (left.equivalent.symm.trans (equivalent.trans right.equivalent)) }

end Assignment

set_option genInjectivity false in
/-- A checked equality or quantitative distinction for two original roots in one prepared partition. -/
inductive Comparison {polynomial : GaussianPolynomial} {ambient : Box} {count : Nat}
    {output : Exact.Basic.Output polynomial ambient count} {cache : Family output.tracks}
    {firstTrack secondTrack : WindingOneTrack polynomial ambient}
    {first : CertifiedName firstTrack} {second : CertifiedName secondTrack}
    (left : Assignment output cache first) (right : Assignment output cache second) : Type 1 where
  /-- The same retained owner index and its original-channel comparison. -/
  | equal (same : left.selection.owner = right.selection.owner)
      (equivalent : NamedEquivalent first.value.name second.value.name)
  /-- Distinct retained owners with their positive gap and original-channel rejection. -/
  | distinct (distinction : Distinction left right)

constructive_injectivity Comparison

/-- Decide equality at the retained original owner indices and return a typed original-channel certificate.

All expensive work is retained in the supplied assignments and partition cache.
The only new runtime operations are bounded-index comparison and, when needed,
the finite coordinate-gap calculation at the actual selected owner boxes.
-/
@[expose] def Assignment.compare {polynomial : GaussianPolynomial} {ambient : Box} {count : Nat}
    {output : Exact.Basic.Output polynomial ambient count} {cache : Family output.tracks}
    {firstTrack secondTrack : WindingOneTrack polynomial ambient}
    {first : CertifiedName firstTrack} {second : CertifiedName secondTrack}
    (left : Assignment output cache first) (right : Assignment output cache second) : Comparison left right :=
  if same : left.selection.owner = right.selection.owner then
    .equal same (left.sameOwner right same)
  else
    .distinct (left.distinguish right same)

set_option genInjectivity false in
/-- Two original root assignments and their checked equality or quantitative distinction. -/
structure ComparisonResult {polynomial : GaussianPolynomial} {ambient : Box} {count : Nat}
    (output : Exact.Basic.Output polynomial ambient count) (cache : Family output.tracks)
    {firstTrack secondTrack : WindingOneTrack polynomial ambient}
    (first : CertifiedName firstTrack) (second : CertifiedName secondTrack) where
  /-- The actual assignment of the original first root to its retained partition owner. -/
  left : Assignment output cache first
  /-- The actual assignment of the original second root to its retained partition owner. -/
  right : Assignment output cache second
  /-- The finite decision and its certificate referring to those same retained assignments. -/
  comparison : Comparison left right

constructive_injectivity ComparisonResult

set_option genInjectivity false in
/-- An original coefficient-computed isolation with its cached coherent root family.

The isolation retains the original polynomial and exact degree on its stated
ambient box. The coefficient-computed square is the default; sufficiently large
symmetric squares support other original input ambients. The support identity
makes original tracks in that same ambient eligible for identification.
-/
structure Partition {polynomial : GaussianPolynomial} (input : FTA.Squarefree.Input polynomial)
    (ambient : Box := Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox polynomial) where
  /-- The actual exact isolation in this same retained ambient box. -/
  output : Exact.Basic.Output polynomial ambient polynomial.natDegree
  /-- The retained support is exactly this same original ambient box. -/
  support_eq : output.support = ambient
  /-- One actual coherent root cache for each original ordered isolation track. -/
  roots : Family output.tracks

constructive_injectivity Partition

namespace Partition

/-- Compute the original squarefree isolation once and build each original root cache once. -/
@[expose] def ofInput {polynomial : GaussianPolynomial} (input : FTA.Squarefree.Input polynomial) : Partition input :=
  let output := input.isolation
  { output := output
    support_eq := Exact.LargeSquare.isolateLargeSquare_support input.degreeAtLeastTwo input.squarefree input.elimination
    roots := Family.ofTracks input.degreePositive output.tracks }

/-- Prepare the original polynomial's isolation and root cache on a sufficiently large symmetric support square. -/
@[expose] def ofSymmetric {polynomial : GaussianPolynomial} (input : FTA.Squarefree.Input polynomial)
    {radius : Purelib.Data.Rat.Fraction.Rational}
    (radiusLe : Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius polynomial ≤ radius) :
    Partition input
      (Box.symmetric radius
        ((Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius_pos polynomial).trans_le radiusLe).le) :=
  let output := Exact.LargeSquare.isolateSymmetric input.degreeAtLeastTwo input.squarefree input.elimination radiusLe
  { output := output
    support_eq := rfl
    roots := Family.ofTracks input.degreePositive output.tracks }

/-- Prepare one original-polynomial partition on a computed support containing every original input ambient.

The original coefficient radius and the finite ordered box list determine the
support square. Isolation and each root cache are constructed once and retained
on that same support; no supplied containment radius or successful search is required.
-/
@[expose] def ofBoxes {polynomial : GaussianPolynomial} (input : FTA.Squarefree.Input polynomial)
    (boxes : List Box) : Partition input (Dense.Gaussian.Bounds.RootRadius.Box.enclosingSquare polynomial boxes) :=
  ofSymmetric input (Dense.Gaussian.Bounds.RootRadius.Box.enclosingRadius_ge_coefficients polynomial boxes)

/-- Identify an original root in the prepared polynomial's ambient box using its intrinsic support witness. -/
@[expose] def assign {polynomial : GaussianPolynomial} {input : FTA.Squarefree.Input polynomial} {ambient : Box}
    (partition : Partition input ambient)
    {track : WindingOneTrack polynomial ambient}
    (root : CertifiedName track) : Assignment partition.output partition.roots root :=
  Assignment.select input partition.output partition.roots root (by
    rewrite [partition.support_eq]
    exact track.initial.refinesAmbient)

/-- Decide the two original root channels using the same prepared isolation and actual cached family.

Both computed assignments are retained in the result alongside its original
channel certificate. All isolation and root-family caches are reused from the
supplied partition; there is no extra successful-search hypothesis.
-/
@[expose] def compare {polynomial : GaussianPolynomial} {input : FTA.Squarefree.Input polynomial} {ambient : Box}
    (partition : Partition input ambient)
    {firstTrack secondTrack : WindingOneTrack polynomial ambient}
    (first : CertifiedName firstTrack) (second : CertifiedName secondTrack) :
    ComparisonResult partition.output partition.roots first second :=
  let left := partition.assign first
  let right := partition.assign second
  { left := left
    right := right
    comparison := left.compare right }

end Partition

end Purelib.Riemann.RootContinuation.CoherentRoot

end
