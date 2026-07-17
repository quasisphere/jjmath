# JJMath

My own private (semi)-autoformalized experimental Lean math library.

The formalization is grounded on Mathlib and the goal of this experiment is to see whether I can eventually start formalizing my own research. For this reason the formalization so-far is rather crude and just aiming to get certain central results to a "merely-true" state.

## Philosophy

The general philosophy is to move fast and reiterate when needed. LLMs are already quite capable of rewriting stuff when needed, and will probably become even better in the future, so when need arises I can simply refactor.

Moreover, as Mathlib advances or other better maintained repositories emerge, I'm intending to migrate the library to use those when possible.

A central feature of the repository at the moment is the usage of Handwave metadata in docstrings of theorems and definitions. Handwave is a VS Code extension that can be used to explore the codebase and render previews of theorems and their dependencies. It also allows to create Markdown documents that include theorems from the Lean files to generate coherent stories about the theory. At the moment these documents are mostly LLM generated, but eventually the idea is to also write them by hand for more interesting results and new research.

## Highlights

- Uniformization theorem for simply-connected Riemann surfaces
- Constructing harmonic functions using Perron method
- Rado's theorem that Riemann surfaces are second countable
- $W^{1,2}$ Sobolev functions on manifolds with basic results such as Rellich and Poincare inequality
- Stokes theorem for simplicial chains
- Basics of de Rham cohomology
- Solving the Schwarzian differential equation using Frobenius method
- Correspondence between hyperbolic metrics and complex projective structures with real holonomy
- Koebe 1/4 theorem

## Sources

Most of the work has been vibe-formalized without explicit sources outside of my own head and the LLM itself. For a couple of parts I have however given the LLM references.

- Rado's theorem used https://willierushrush.github.io/posts/2020/05/second-countability/ as a general strategy
- For the ACL characterisation of Sobolev functions I used the lecture notes by Kinnunen at https://math.aalto.fi/~jkkinnun/files/sobolev_spaces.pdf
- The uniformization proof used the proof in `Hubbard, J. H. - Teichmüller Theory And Applications To Geometry, Topology, And Dynamic` as a basis, although there were some modifications along the way.

