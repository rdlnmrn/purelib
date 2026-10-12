import CylinderExplorer from "./components/CylinderExplorer"
import { EncodingFamily, PrecisionFigure } from "./components/FiniteExperiments"
import MeasureLab from "./components/MeasureLab"

function SourceLink({ href, children }: { href: string; children: React.ReactNode }) {
  return <a className="source-link" href={href}>{children} <span aria-hidden="true">↗</span></a>
}

export default function App() {
  return (
    <>
      <a className="skip-link" href="#article">Skip to the essay</a>
      <header className="page-header">
        <a className="small-mark" href="#top">CCL notes</a>
        <nav aria-label="Page contents">
          <a href="#encoding">Encoding</a>
          <a href="#refinement">Refinement</a>
          <a href="#measure">Measure</a>
          <a href="#approximation">Approximation</a>
        </nav>
        <a href="../../CCL/Paper.lean">Lean index</a>
      </header>

      <main id="article">
        <article>
          <header className="article-header" id="top">
            <p className="kicker">An informal guide to a formal development</p>
            <h1>Complex continued logarithms, finitely</h1>
            <p className="standfirst">
              What remains of exact real and complex analysis if every object we manipulate
              must be finite, rational, and executable? More than one might expect. The main
              change is not that approximation replaces mathematics, but that a finite
              request and its checkable evidence replace a presumed completed infinity.
            </p>
            <p className="reading-note">
              This is an explanatory essay, not the specification. Links in the margin of the
              argument lead to the corresponding Lean declarations.
            </p>
            <p className="reading-note">
              The interactive demonstrations have not been properly tested. Their behaviour
              and numerical displays may contain errors; consult the linked Lean proofs for
              the formal results.
            </p>
          </header>

          <section className="prose-section" id="finite-requests">
            <p className="section-number">1</p>
            <h2>Finite requests in place of completed values</h2>
            <p>
              The primitive data are deliberately ordinary: integers; fractions with positive
              denominators; pairs of fractions for Gaussian rationals; finite lists and finite
              trees; decidable predicates; and records carrying explicit witnesses. A projective
              value is a pair <code>[p:q]</code>. When <code>q ≠ 0</code> it denotes the affine
              value <code>p/q</code>, while <code>[1:0]</code> records the point at infinity. Two
              pairs represent the same value when cross multiplication says so. Nothing in this
              representation asks us to construct a quotient space or a completed complex plane.
            </p>
            <p>
              A general number-like process is therefore not introduced as an infinite digit
              sequence. It is an interface that answers any supplied finite request: give a
              positive rational tolerance, or ask for a finite number of bits, and it returns
              finite output together with a rational enclosure. A later request may refine the
              same stored state and extend the old word. “Arbitrary accuracy” means that each
              such finite request has a finite answer; it does not mean that all answers have
              already been assembled into an infinite object.
            </p>
            <aside className="margin-note">
              One could use the successive prefixes as intuition for a real number, but this
              development does not formalize the completed sequence. The finite request process
              is the object being used.
            </aside>
            <p>
              This costs some familiar shortcuts. One cannot simply choose an element from an
              unspecified nonempty set, pass silently to a limit, or decide equality of arbitrary
              completed reals. In exchange, positive assertions have computational content:
              division asks for evidence that zero has been excluded, logarithms carry branch
              data, and existence theorems return witnesses which can actually be inspected.
            </p>
            <SourceLink href="../../CCL/Geometry/Projective.lean">The finite projective core</SourceLink>
          </section>

          <section className="prose-section" id="encoding">
            <p className="section-number">2</p>
            <h2>The CCL word and the region it describes</h2>
            <p>
              Put <code>γ = 1 + i</code>. A regular CCL block has the binary form
              <code>[k,s] = 1<sup>k</sup>0 β(s)</code>. The unary prefix records a scale by a power
              of γ; the final three bits choose one of eight representatives
              <code>0, …, 7</code> arranged as the compass directions E, NE, N, NW, W, SW, S,
              and SE. There is also a specially marked low-scale block, permitted only at the
              beginning of a word.
            </p>

            <div className="sector-table">
              <div><span>E</span><code>000</code><span>NE</span><code>001</code><span>N</span><code>010</code><span>NW</span><code>011</code></div>
              <div><span>W</span><code>100</code><span>SW</span><code>101</code><span>S</span><code>110</code><span>SE</span><code>111</code></div>
            </div>

            <p>
              The controller scales a nonzero Gaussian rational into the annulus
              <code>1 ≤ |z|² ≤ 2</code>, selects its sector using rational comparisons with
              <code>±1/2</code>, subtracts the representative, and inverts. On projective pairs
              these operations are transparent two-by-two matrices. Exact Gaussian rationals
              have terminating encodings, and their finite decoders reconstruct them exactly.
            </p>
            <p>
              A prefix says rather more than “these are the first few digits.” It describes a
              projective cylinder: the region of all tails which still satisfy its completed
              block constraints. The formal development never gathers all compatible values
              into a global set. It reasons from a finite witness of compatibility. After
              <em>n</em> completed blocks, any two witnessed compatible values have squared
              chordal separation at most <code>2<sup>−n</sup></code>.
            </p>
            <SourceLink href="../../CCL/Encoding/Decoder.lean">Block syntax and decoder matrices</SourceLink>
            <CylinderExplorer />
          </section>

          <section className="prose-section" id="family">
            <p className="section-number">3</p>
            <h2>Related finite encodings</h2>
            <p>
              CCL is easier to place after looking at three relatives. An ordinary continued
              fraction uses integer digits and Euclidean descent. A continued logarithm replaces
              those digits by binary scale choices. A coordinate-floor complex continued
              fraction repeatedly folds a point back into a half-open unit square. CCL combines
              the binary scale idea with eight rationally decidable complex directions.
            </p>
            <p>
              The experiments below are intentionally modest. Their inputs are displayed
              rationals, their loops have finite descent measures, and the graphics are aids to
              reading those finite algorithms. They do not simulate an unbounded stream.
            </p>
            <EncodingFamily />
          </section>

          <section className="prose-section" id="refinement">
            <p className="section-number">4</p>
            <h2>Refinement and arithmetic</h2>
            <p>
              The cylinder estimate supplies a simple universal precision budget. If one wants
              squared chordal spread below a positive rational ε, a finite search finds
              <em>n</em> with <code>2<sup>−n</sup> &lt; ε</code>. Particular scale blocks may contract
              more strongly, and a bounded affine chart turns the projective statement into a
              rational box estimate with an explicit conversion factor.
            </p>
            <PrecisionFigure />
            <p>
              Rational boxes are the working currency for subsequent analysis. Addition,
              subtraction and multiplication transport them directly; division additionally
              requires a finite certificate separating the denominator from zero. Persistent
              transducers answer each request with ordinary CCL bits and an accuracy sidecar
              obtained from the same refined state. Coherence records that a later answer really
              extends what was said earlier.
            </p>
            <p>
              The same pattern supports more than field arithmetic. The library contains
              finite-request exponential, positive-real logarithm and charted complex logarithm,
              sine and cosine, with operational algebraic laws. Its calculus uses divided
              differences, finite jets, Taylor remainder budgets, finite polynomial integration,
              and rational path refinement. Polynomial roots and poles are isolated by finite
              winding certificates and rational boxes; the Paper-I interface remains independent
              of CCL, while a one-way CCL-2 bridge may attach persistent prefixes afterwards.
            </p>
            <div className="source-list" aria-label="Selected formal sources">
              <SourceLink href="../../CCL/Arithmetic/BoxedNameProcess.lean">Boxed arithmetic</SourceLink>
              <SourceLink href="../../CCL/Transcendental/Output.lean">Transcendental outputs</SourceLink>
              <SourceLink href="../../CCL/Calculus/DividedDifference.lean">Finite calculus</SourceLink>
              <SourceLink href="../../papers/RFAP/Chapters/Paper.lean">RFAP root isolation</SourceLink>
            </div>
          </section>

          <section className="prose-section" id="measure">
            <p className="section-number">5</p>
            <h2>Measure theory on explicit finite laws</h2>
            <p>
              In this regime measure theory does indeed begin to resemble a careful remix of
              finite combinatorics. A law is a displayed finite list of outcomes with
              nonnegative rational weights. An event is a decidable predicate on those outcomes.
              Integration is a weighted finite sum. “AE” means <em>almost everywhere</em>: two
              functions agree away from a displayed collection of atoms whose total weight is
              zero. Conditioning is division by the positive rational weight of an event or a
              finite partition cell.
            </p>
            <MeasureLab />
            <p>
              These primitives retain the algebraic heart of a surprising fraction of an
              introductory course: finite additivity and monotonicity; indicator functions and
              expectation; variance and covariance; Markov and Chebyshev inequalities; Jensen
              for the finite convexity notions in use; conditional expectation on finite
              partitions; total expectation and total variance; finite kernels, stationarity,
              and return or maximal bounds; densities and finite Radon–Nikodym and Lebesgue
              decomposition statements; and root-free powered L<sup>p</sup> geometry.
            </p>
            <p>
              What has disappeared is exactly the machinery whose force comes from completed
              infinity: σ-algebras closed under countable unions, countable additivity,
              monotone and dominated convergence for arbitrary sequences, completion of L<sup>p</sup>
              spaces, product constructions over infinitely many coordinates, and asymptotic
              ergodic theorems. Finite analogues can be strong and quantitative, but they do not
              become those theorems merely by suggestive notation.
            </p>
            <p>
              CCL prefixes fit this finite theory naturally. A completed prefix is a finite
              observable with a dyadic word weight and a certified geometric diameter. Any
              finite law supported by witnessed points in one cylinder inherits explicit
              expectation enclosures, variance bounds, and exact zero probability outside a
              computable prefix radius.
            </p>
            <div className="source-list">
              <SourceLink href="../../Purelib/Measure.lean">Finite-measure theorem index</SourceLink>
              <SourceLink href="../../CCL/Measure/CylinderConcentration.lean">CCL cylinder concentration</SourceLink>
            </div>
          </section>

          <section className="prose-section" id="approximation">
            <p className="section-number">6</p>
            <h2>Best approximation to rational anchors</h2>
            <p>
              A finite root-isolation request returns a rational box and a rational anchor. The
              approximation development can enumerate a nonempty finite table containing all and
              only the Gaussian-rational best approximants to that displayed anchor. From adjacent
              occupied best levels, a coefficient-local finite search returns the next occupied
              level and skips none; it emits only a genuinely consecutive best pair, or reports
              exact termination. Its candidate list has the explicit quadratic bound
              <code>64(B+1)²</code>.
            </p>
            <p>
              There is also a Chevallier-style finite global boundary. For each displayed rational
              source and each natural squared-denominator request above one, a global selector
              returns a bounded nonzero denominator satisfying the formal rational-cut error
              bound. Separate positive rational boxes give arbitrarily late <em>finite</em>
              counterexample runs against every strictly sharper permitted cut. This is a finite
              global and finite sharpness statement, not an asymptotic assertion about an already
              completed irrational root.
            </p>
            <aside className="margin-note">
              At every root-track request, the “best approximation” theorem applies exactly to
              the rational anchor in that response. A finer request produces a finer anchor and a
              new verified finite best-approximation calculation. The polynomial residual and
              root box are maintained separately.
            </aside>
            <div className="source-list">
              <SourceLink href="../../RFAP/Approximation/RATBestApproximation.lean">RAT best-response interface</SourceLink>
              <SourceLink href="../../RFAP/Approximation/LocalSuccessor.lean">Local successor theorem</SourceLink>
              <SourceLink href="../../RFAP/Approximation/FiniteDirichletGlobal.lean">Finite global boundary</SourceLink>
            </div>
          </section>

          <section className="prose-section boundaries" id="boundaries">
            <p className="section-number">7</p>
            <h2>The boundary of the claim</h2>
            <p>
              The development asserts executable finite constructions over explicit arithmetic.
              It proves a finite response for every supplied positive rational accuracy and
              bit-count request, and the response comes with kernel-checked specifications. It
              does not postulate a completed infinite digit stream, a global set of all points in
              a cylinder, or an ambient space obtained by completion.
            </p>
            <p>
              Accordingly, compactness, infinite series, unrestricted countable choice, and
              asymptotic limit arguments are not hidden behind familiar terminology. Nor is
              uncertified division by a possibly zero quantity, or a complex logarithm without
              branch information. The point is not that finite mathematics secretly proves every
              classical theorem. It is that many useful conclusions can be stated in the form
              actually needed by a calculation, and proved with arguments whose witnesses survive
              extraction.
            </p>
          </section>

          <footer className="article-footer">
            <h2>Reading the formal source</h2>
            <p>
              The commented <a href="../../CCL/Paper.lean"><code>CCL.Paper</code> facade</a> is the
              shortest map of the public results. The three exact encodings are collected in
              <a href="../../CCL/Encoding/Examples.lean"><code> CCL.Encoding.Examples</code></a>.
              For the architecture, build instructions and paper boundary, continue with the
              <a href="../../README.md"> repository README</a>. The linked Lean declarations,
              rather than this informal prose, are the authority for formal claims.
            </p>
          </footer>
        </article>
      </main>
    </>
  )
}
