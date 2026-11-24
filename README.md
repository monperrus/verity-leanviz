# verity-leanviz

A browsable map of [verity](https://github.com/lfglabs-dev/verity) at
[`4089965f70`](https://github.com/lfglabs-dev/verity/tree/4089965f70c1032383981eb8556953c12a621516), served at
https://monperrus.github.io/verity-leanviz/.

Ways in:
- [Architecture](https://monperrus.github.io/verity-leanviz/#/arch): verity's areas in columns, what is used on the
  left, references against the layering in red. Click a box to go one level down, e.g.
  [`Compiler.Proofs`](https://monperrus.github.io/verity-leanviz/#/arch/Compiler.Proofs).
- [What carries the results](https://monperrus.github.io/verity-leanviz/#/owners/Compiler.Proofs.EndToEnd): the
  intermediate results the end-to-end theorems rest on, as a dominator outline.
- Search, any declaration's page, the treemap: as in [LeanViz](https://github.com/keithadler/leanviz).

Partial build: the bundle covers the 691 of verity's 896 modules that built; the others need `solc`, which was not
installed.

## What is here

A static site, no server code: `index.html`, `app.js`, `arch.js`, `style.css`, `sw.js` are the `site/` of the
[monperrus/leanviz](https://github.com/monperrus/leanviz) fork at `9a7bd9b`, with one footer sentence added to
`index.html` (the partial-build note). `data/` is the bundle the LeanViz generator wrote from verity's `.olean` files.
GitHub Pages serves the `main` branch as is (`.nojekyll`).

## Rebuilding

```sh
# verity, built with its pinned toolchain
git clone https://github.com/lfglabs-dev/verity && (cd verity && lake exe cache get && lake build)
# the generator (monperrus/leanviz, with Tenet built into lib/ as its README says)
ELAN_HOME=~/.elan dotnet generator/bin/Release/net10.0/leanviz.dll path/to/verity --out out
# then replace data/ here with out/data, and the five site files with the fork's site/
```
