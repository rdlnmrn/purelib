# Informal CCL essay

This directory contains the prose-led, interactive introduction to the CCL
development.  It is a small Vite, React, and TypeScript package; the mathematical
figures use Mafs rather than hand-written canvas code.

The interactive demonstrations have not been properly tested. Their behaviour
and numerical displays may contain errors; the linked Lean proofs are the
authority for formal results.

`static.html` is a generated, self-contained copy with JavaScript, styles, and
fonts embedded. Download it and open it directly in a browser, or serve it on
GitHub Pages / an HTML host. GitHub and Gitea repository code viewers may show
HTML source instead of rendering the page. No Node installation is needed to
view this copy, but JavaScript must be enabled. Source links work when the file
remains at `docs/ccl/static.html` within a checkout or a hosted repository tree.

Regenerate the checked-in copy after changing the essay:

```sh
npm run build:static
```

From this directory:

```sh
npm install
npm run dev
```

Then open the local URL printed by Vite.  For a production check, run:

```sh
npm run build
npm run preview
```

`vite.config.ts` uses a relative asset base so the generated `dist/` contents
can be hosted below any path.  The essay's source links assume that those
contents are published at the repository's `docs/ccl/` URL, so that `../../`
continues to point at the repository root.

The cylinder plot is deliberately described as a sampled visualization.  Its
block syntax, sector predicates, and affine Möbius actions mirror
`CCL.Encoding.Decoder`, `CCL.Encoding.Sectors`, and
`CCL.Encoding.Cylinder`; plotted points use floating-point coordinates, while
the displayed `2^-n` contraction certificate is an exact rational Lean theorem.
Formal claims in the essay link to their authoritative source files.
