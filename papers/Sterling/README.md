# Sterling arithmetic and construction definitions

`SterlingArithmetic.tex` is the introductory exposition. It starts with the
challenge of interpreting `e + pi + sqrt(2)`, explains finite accuracy
requests and CCL observations, and presents two procedures each for e and pi.
It describes the generated rational algebra up to certified equivalence,
with no general numerical equality test. Its assumed natural, integer and
rational definitions are supplied by the box constructions in `Definitions.tex`.
The Horner construction is presented as the exponential at one, with a
brief account of the CCL exponential and prospective further comparisons
such as `exp(pi * i) ≈ -1`.
When a concept is introduced, the exposition cites its matching entry in
bold, including the companion's entry type and number. An opening note links
to `Definitions.pdf`.

`Definitions.tex` and `Definitions.pdf` are the definitions-only
companion for the example. They use the recognition and decidable equality
requirements of Norman J. Wildberger's *Rebuilding Pure Mathematics*
(October 2026). The objects are finite constructions with explicit recognition
and equality procedures; numerical equivalence is a separate relation.
Object definitions, numerical contracts and evaluation operations are labelled
separately. Each operation identifies the earlier recognition and equality
procedures used for its finite data.
Ordered lists use Box Arithmetic's multiset of successive prefix boxes.
Pairs, tuples, tagged records, construction trees, words and matrices use
that encoding. Natural arithmetic is defined on boxes of empty boxes;
integers use signed-magnitude box pairs and rationals use reduced signed
fraction triples, with arithmetic and order on those representations.
Projective fields also have canonical box forms.
The companion defines the constant recipes, addition, retained states,
frontiers, comparison derivations and CCL observations with accuracy sidecars.
CCL parser records, cursor records, finite advances, the reading contract and
accuracy observations have separate entries with their relevant checks.
Its comparison arguments refer to `SterlingArithmetic.pdf`; its productive
CCL cursor is specified by the Purelib transducer source definitions.

From the repository root, run the following command twice to build the PDF
and resolve its cross-references. It uses pdfLaTeX with shell escape disabled
and a fixed source date:

```sh
timeout --signal=TERM --kill-after=15s 300s env SOURCE_DATE_EPOCH=1793841348 FORCE_SOURCE_DATE=1 /usr/bin/pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error -file-line-error -output-directory=papers/Sterling papers/Sterling/Definitions.tex
```

Substitute `SterlingArithmetic.tex` to rebuild the introductory exposition.
The build uses standard pdfLaTeX packages and Latin Modern fonts.
Auxiliary files are ignored in this
directory; both PDFs are tracked.
