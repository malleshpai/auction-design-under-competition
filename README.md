# Auction Design under Competition

**Mallesh M. Pai** (Rice University)

Paper, slides, and Lean 4 formalization for *Auction Design under Competition*.

## Overview

We study $m \ge 2$ sellers, each with one unit, competing for $n \ge 2$ private-value buyers via hierarchical mechanisms (auctions with a reserve price and finitely many pooling intervals). Expressing a seller's revenue in quantity coordinates shows that it equals a weighted integral of Cournot oligopoly revenues subject to Border's feasibility constraint, so Cournot's marginal revenue $\psi_m(v) = v - \frac{1}{m}\frac{1-F(v)}{f(v)}$ replaces Myerson's virtual valuation:

- **Covered markets ($a > 0$):** If $\psi_m$ is nondecreasing on $[a, 1]$ and $\psi_m(a) \ge 0$, symmetric second price auctions with Virág's slack reserve $\rho^*$ form an equilibrium against all hierarchical deviations for every $n \ge 2$ (Theorem 2). Monotonicity of $\psi_m$ cannot be weakened uniformly across $n$ (Theorem 5).
- **Binding reserves ($\rho \ge a$):** Symmetric second price auctions never survive—an asking price captures marginal buyers at first order (Theorem 3)—and in duopoly ($a = 0$), asymmetric reserve profiles whose higher reserve has negative monopoly virtual valuation also fail against a pool for large $n$ (Theorem 4).

## Repository Layout

- `paper/` — LaTeX source (`auction-design-under-competition.tex`), compiled PDF (`auction-design-under-competition.pdf`), and figures (`figs/`).
- `lean/` — Lean 4 (`v4.36.0`) + Mathlib formalization of the main results (503 theorems, zero `sorry`, standard axioms only). See [`lean/README.md`](lean/README.md).
- `slides/` — Beamer deck (`slides.tex`, `slides.pdf`), handout (`slides-handout.pdf`), and speaker notes (`speaker-notes.txt`).

## Building

Paper:
```bash
cd paper && latexmk -pdf auction-design-under-competition.tex
```

Lean proofs (requires `elan` / Lean `v4.36.0`):
```bash
cd lean
lake exe cache get
lake build AuctionCompetition
lake env lean AxiomCheck.lean
```
