# Lean 4 Formalization

Lean 4 (`v4.36.0`) + Mathlib formalization of the main theorems in `../paper/auction-design-under-competition.tex`.

All 503 theorems across the library compile with zero `sorry`, zero `admit`, and zero custom axioms (`AxiomCheck.lean` verifies every theorem depends solely on `propext`, `Classical.choice`, and `Quot.sound`).

## Modules

| File | Lines | Contents |
|---|---:|---|
| `AuctionCompetition/Defs.lean` | 306 | Standing assumptions (`Market`, `SmoothMarket`), `HierarchicalMech`, `SPA`, `VisitStrategy`, `effDist`, `alloc`, `surplus`, `payment`, `sellerRev`, `IsSR`, `InverseDemand`, `psi`, `psi1`, `rhoStar`, `W`, `cournotRev`, `curvatureE`, `varpi`, `Xbar`, `BorderFeasible`, `pathRev`. |
| `AuctionCompetition/VisitStage.lean` | 8,311 | **Prop. 1** (potential game, concavity, directional derivative, unique symmetric split, continuous/monotone cutoffs $w$), **Prop. 2(i)–(iii)** (rival symmetry, uniqueness via 1D sign propagation across gaps and pools, finite-component localization), and **Lemma 1 / A.5** (band structure, $q^*$, pool–band bijection, top-reaching bands). |
| `AuctionCompetition/Cournot.lean` | 3,767 | `exists_inverseDemand`, diagonal and generalized tangent bounds, **Prop. 3 & Lemma B.1** (`prop3_quantity_path_rev`, `prop3_border_q`, `lemmaB1_rent_lower_bound` including $\hat v = 1$), **Theorem 1** (interior pools and Cournot's condition), and **Corollary 1**. |
| `AuctionCompetition/CoveredMarkets.lean` | 2,576 | **Theorem 2** (Cases 1–2, Jensen's inequality, Virág's reserve game) and **Example 1** (truncated Pareto on $[1/2, 1]$: monopolist irons, duopolists do not). |
| `AuctionCompetition/BindingReserves.lean` | 8,254 | **Theorem 3** (explicit asking-price `IsSR` split, $O(\beta - \rho)$ gain, $\rho \in \{0, 1\}$ boundary cases) and **Theorem 4** (cutoff asymptotics, explicit `IsSR` deviation, eq. (22) rescaled limit, small-$u$ Taylor expansion, $\psi_2(r_H)=0$ identity $r_H(\frac{\sinh u}{u}-1)$, and failure for large $n$). |
| `AuctionCompetition/Sharpness.lean` | 3,708 | **Prop. C.1 & Theorem 5(i)** ($d^3$ expansion, $\bar X = 1 + 1/\varpi(m)$, narrow pool $\implies$ narrow interior band), **Prop. C.2 & Theorem 5(ii)** (many-buyers limit $\mathcal{J}$, $E \le 2m$ narrow-band bound, explicit $C^1$ covered-market counterexample for every $X > m+1$), `mbar_finite_for_smooth_F`, and `sup_mbar_infinite`. |
| `AuctionCompetition/Integration.lean` | 943 | End-to-end `IsSR` $\to$ `sellerRev` bridges: `unilateralContinuation_of_isSR`, `end_to_end_theorem2_covered_markets`, `end_to_end_example1`, and `end_to_end_theorem5_many_buyers`. |
| `AxiomCheck.lean` | 33 | Metaprogram auditing every theorem in `AuctionCompetition` for non-standard axioms. |

## Scope Notes

- **General SR existence (Glicksberg's fixed-point theorem)** for arbitrary mechanism profiles in $\mathcal{M}^m$ (and arbitrary asymmetric reserve profiles in Prop. 1) is omitted because Mathlib does not currently contain Kakutani–Fan–Glicksberg. Every main theorem either bounds *all* SR continuations (Theorems 1–2) or explicitly constructs and verifies `IsSR` (Theorems 3, 4, and 5(ii)).
- **Theorem 5(i)** (`theorem5_small_pools`) proves the $d^3$ expansion and narrow-pool interior-band implication at the reduced-form level (universal quantification over all narrow pools at `sellerRev` level would likewise require general SR existence).

## Verification

```bash
lake exe cache get
lake build AuctionCompetition
lake env lean AxiomCheck.lean
```
