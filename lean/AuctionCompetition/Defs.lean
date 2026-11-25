import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Auction Design under Competition: Core Definitions

Shared definitions and standing assumptions for Mallesh M. Pai,
*Auction Design under Competition* (`paper/auction-design-under-competition.tex`).

All downstream modules (`VisitStage`, `Cournot`, `CoveredMarkets`,
`BindingReserves`, `Sharpness`) import this file so that every theorem uses
identical types, notation, and standing hypotheses.
-/

open MeasureTheory Set Filter

namespace AuctionCompetition

/-- Standing model primitives (Section 2.1, Assumption 1).
We have `m ≥ 2` sellers, `n ≥ 2` buyers, support `[a, 1]` with `0 ≤ a < 1`,
CDF `F` with continuous strictly positive density `f` on `[a, 1]`, extended by
`F ≡ 0` and `f ≡ 0` on `(-∞, a)`. -/
structure Market where
  m : ℕ
  n : ℕ
  hm : 2 ≤ m
  hn : 2 ≤ n
  a : ℝ
  ha0 : 0 ≤ a
  ha1 : a < 1
  F : ℝ → ℝ
  f : ℝ → ℝ
  hF_a : F a = 0
  hF_1 : F 1 = 1
  hF_below : ∀ v ≤ a, F v = 0
  hf_below : ∀ v < a, f v = 0
  hf_cont : ContinuousOn f (Icc a 1)
  hf_pos : ∀ v ∈ Icc a 1, 0 < f v
  hF_deriv_within : ∀ v ∈ Icc a 1, HasDerivWithinAt F (f v) (Icc a 1) v
  hF_deriv_open : ∀ v ∈ Ioo a 1, HasDerivAt F (f v) v

/-- Smooth density assumption (Assumption 2): `f ∈ C¹([a, 1])`. -/
structure SmoothMarket extends Market where
  f' : ℝ → ℝ
  hf'_cont : ContinuousOn f' (Icc a 1)
  hf_deriv_within : ∀ v ∈ Icc a 1, HasDerivWithinAt f (f' v) (Icc a 1) v
  hf_deriv_open : ∀ v ∈ Ioo a 1, HasDerivAt f (f' v) v

namespace Market

variable (M : Market)

lemma m_pos_real : (0 : ℝ) < M.m := by
  exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) M.hm)

lemma m_sub_one_pos_real : (0 : ℝ) < (M.m : ℝ) - 1 := by
  have : (2 : ℝ) ≤ M.m := by exact_mod_cast M.hm
  linarith

lemma n_pos_real : (0 : ℝ) < M.n := by
  exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) M.hn)

lemma n_sub_one_pos_real : (0 : ℝ) < (M.n : ℝ) - 1 := by
  have : (2 : ℝ) ≤ M.n := by exact_mod_cast M.hn
  linarith

/-- Symmetric effective distribution `A(v) = 1 - (1 - F(v)) / m`. -/
noncomputable def A (v : ℝ) : ℝ :=
  1 - (1 - M.F v) / M.m

/-- Cournot marginal revenue `ψ_m(v) = v - (1 / m) * (1 - F(v)) / f(v)`. -/
noncomputable def psi (v : ℝ) : ℝ :=
  v - (1 - M.F v) / ((M.m : ℝ) * M.f v)

/-- Myerson monopoly virtual valuation `ψ_1(v) = v - (1 - F(v)) / f(v)`. -/
noncomputable def psi1 (v : ℝ) : ℝ :=
  v - (1 - M.F v) / M.f v

/-- Virág (2010) covered-market candidate reserve `ρ* = (n - 1)a / ((m - 1)² + n - 1)`. -/
noncomputable def rhoStar : ℝ :=
  ((M.n : ℝ) - 1) * M.a / (((M.m : ℝ) - 1) ^ 2 + ((M.n : ℝ) - 1))

/-- Weighting density `W(q) = n(n - 1)(1 - q)^(n - 2)`. -/
noncomputable def W (q : ℝ) : ℝ :=
  (M.n : ℝ) * ((M.n : ℝ) - 1) * (1 - q) ^ (M.n - 2)

/-- Inverse demand `P : [0, 1] → [a, 1]` satisfying `F (P z) = 1 - z`. -/
structure InverseDemand where
  P : ℝ → ℝ
  hP_mem : ∀ z ∈ Icc (0 : ℝ) 1, P z ∈ Icc M.a 1
  hP_right : ∀ z ∈ Icc (0 : ℝ) 1, M.F (P z) = 1 - z
  hP_left : ∀ v ∈ Icc M.a 1, P (1 - M.F v) = v
  hP_zero : P 0 = 1
  hP_one : P 1 = M.a
  hP_cont : ContinuousOn P (Icc 0 1)
  hP_strictAnti : StrictAntiOn P (Icc 0 1)
  hP_deriv_open : ∀ z ∈ Ioo (0 : ℝ) 1, HasDerivAt P (-1 / M.f (P z)) z
  hP_deriv_within : ∀ z ∈ Icc (0 : ℝ) 1, HasDerivWithinAt P (-1 / M.f (P z)) (Icc 0 1) z

/-- Cournot oligopoly revenue `Π(t, q) = t * P(t + (m - 1)q)`. -/
noncomputable def cournotRev (P : ℝ → ℝ) (t q : ℝ) : ℝ :=
  t * P (t + ((M.m : ℝ) - 1) * q)

lemma F_continuousOn : ContinuousOn M.F (Icc M.a 1) :=
  fun v hv => (M.hF_deriv_within v hv).continuousWithinAt

lemma F_strictMonoOn : StrictMonoOn M.F (Icc M.a 1) := by
  intro x hx y hy hxy
  have hcont : ContinuousOn M.F (Icc x y) :=
    M.F_continuousOn.mono (Icc_subset_Icc hx.1 hy.2)
  have hdiff : DifferentiableOn ℝ M.F (Ioo x y) := fun z hz =>
    (M.hF_deriv_open z ⟨lt_of_le_of_lt hx.1 hz.1, lt_of_lt_of_le hz.2 hy.2⟩).differentiableAt.differentiableWithinAt
  obtain ⟨c, hc, hslope⟩ := exists_deriv_eq_slope M.F hxy hcont hdiff
  have hc_open : c ∈ Ioo M.a 1 := ⟨lt_of_le_of_lt hx.1 hc.1, lt_of_lt_of_le hc.2 hy.2⟩
  have hpos : 0 < deriv M.F c := by
    rw [(M.hF_deriv_open c hc_open).deriv]
    exact M.hf_pos c (Ioo_subset_Icc_self hc_open)
  rw [hslope, div_pos_iff_of_pos_right (sub_pos.mpr hxy)] at hpos
  linarith

lemma F_mem_Icc {v : ℝ} (hv : v ∈ Icc M.a 1) : M.F v ∈ Icc (0 : ℝ) 1 := by
  constructor
  · rw [← M.hF_a]
    exact M.F_strictMonoOn.monotoneOn (left_mem_Icc.mpr M.ha1.le) hv hv.1
  · rw [← M.hF_1]
    exact M.F_strictMonoOn.monotoneOn hv (right_mem_Icc.mpr M.ha1.le) hv.2

lemma rhoStar_lt_a (ha : 0 < M.a) : M.rhoStar < M.a := by
  unfold rhoStar
  have hm1 : (0 : ℝ) < ((M.m : ℝ) - 1) ^ 2 := sq_pos_of_pos M.m_sub_one_pos_real
  have hn1 : (0 : ℝ) < (M.n : ℝ) - 1 := M.n_sub_one_pos_real
  rw [div_lt_iff₀ (by linarith)]
  nlinarith

lemma rhoStar_nonneg : 0 ≤ M.rhoStar := by
  unfold rhoStar
  have hm1 : (0 : ℝ) < ((M.m : ℝ) - 1) ^ 2 := sq_pos_of_pos M.m_sub_one_pos_real
  have hn1 : (0 : ℝ) < (M.n : ℝ) - 1 := M.n_sub_one_pos_real
  apply div_nonneg
  · exact mul_nonneg hn1.le M.ha0
  · linarith

end Market

/-- Demand curvature `E(v) = -(1 - F(v)) f'(v) / f(v)²`. -/
noncomputable def curvatureE (M : SmoothMarket) (v : ℝ) : ℝ :=
  -((1 - M.F v) * M.f' v) / (M.f v) ^ 2

/-- Small-pool markup weight `ϖ(m) = (m + 1) / (m² + 2m - 1)`. -/
noncomputable def varpi (m : ℕ) : ℝ :=
  ((m : ℝ) + 1) / ((m : ℝ) ^ 2 + 2 * (m : ℝ) - 1)

/-- Small-pool curvature threshold `X̄(m) = 1 + 1 / ϖ(m) = m(m + 3) / (m + 1)`. -/
noncomputable def Xbar (m : ℕ) : ℝ :=
  1 + 1 / varpi m

lemma varpi_lt_inv_m {m : ℕ} (hm : 2 ≤ m) : varpi m < 1 / (m : ℝ) := by
  unfold varpi
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hden : (0 : ℝ) < (m : ℝ) ^ 2 + 2 * (m : ℝ) - 1 := by nlinarith
  have hmpos : (0 : ℝ) < m := by linarith
  rw [div_lt_div_iff₀ hden hmpos]
  nlinarith

lemma Xbar_eq {m : ℕ} (hm : 2 ≤ m) :
    Xbar m = ((m : ℝ) * ((m : ℝ) + 3)) / ((m : ℝ) + 1) := by
  unfold Xbar varpi
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have h1 : (m : ℝ) + 1 ≠ 0 := by linarith
  have h2 : (m : ℝ) ^ 2 + 2 * (m : ℝ) - 1 ≠ 0 := by nlinarith
  field_simp
  ring

/-! ### Hierarchical Mechanisms and the Visit Stage -/

/-- An open pooling interval `(α, β)` with `α < β`. -/
structure Pool where
  α : ℝ
  β : ℝ
  hαβ : α < β

/-- A hierarchical mechanism `(r, P)` (Definition 1): reserve `r ∈ [0, 1]` and a finite
list of pairwise disjoint open pooling intervals contained in `[r, 1]`
(allowing `α = r` for asking prices and `β = 1` for posted prices). -/
structure HierarchicalMech where
  r : ℝ
  hr0 : 0 ≤ r
  hr1 : r ≤ 1
  pools : List Pool
  hpools_in : ∀ I ∈ pools, r ≤ I.α ∧ I.β ≤ 1
  hpools_disj : pools.Pairwise (fun I J => I.β ≤ J.α ∨ J.β ≤ I.α)

/-- Standard second price auction with reserve `r`, `SPA(r) = (r, ∅)`. -/
def SPA (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : HierarchicalMech where
  r := r
  hr0 := hr0
  hr1 := hr1
  pools := []
  hpools_in := by simp
  hpools_disj := List.Pairwise.nil

/-- Pooled interim winning probability formula `g(x, y)` from equation (2):
`(y^n - x^n) / (n (y - x))` for `x ≠ y`, and `x^(n - 1)` for `x = y`. -/
noncomputable def poolAvg (n : ℕ) (x y : ℝ) : ℝ :=
  if x = y then x ^ (n - 1) else (y ^ n - x ^ n) / ((n : ℝ) * (y - x))

lemma poolAvg_eq_sum (n : ℕ) (hn : 1 ≤ n) (x y : ℝ) :
    poolAvg n x y = (∑ k ∈ Finset.range n, x ^ k * y ^ (n - 1 - k)) / (n : ℝ) := by
  unfold poolAvg
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_ne_zero (by omega)).ne'
  split_ifs with hxy
  · subst hxy
    have hsum : ∑ k ∈ Finset.range n, x ^ k * x ^ (n - 1 - k) = (n : ℝ) * x ^ (n - 1) := by
      have : ∀ k ∈ Finset.range n, x ^ k * x ^ (n - 1 - k) = x ^ (n - 1) := by
        intro k hk
        rw [Finset.mem_range] at hk
        rw [← pow_add, Nat.add_sub_cancel' (by omega)]
      rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hsum, mul_div_cancel_left₀ _ hnR]
  · have hgeom : (y - x) * ∑ k ∈ Finset.range n, x ^ k * y ^ (n - 1 - k) = y ^ n - x ^ n := by
      have := geom_sum₂_mul y x n
      have hcomm : ∑ k ∈ Finset.range n, x ^ k * y ^ (n - 1 - k) =
          ∑ k ∈ Finset.range n, y ^ k * x ^ (n - 1 - k) := by
        rw [← Finset.sum_range_reflect (fun k => y ^ k * x ^ (n - 1 - k)) n]
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_range] at hk
        have hsub : n - 1 - (n - 1 - k) = k := by omega
        rw [hsub, mul_comm]
      rw [hcomm, mul_comm, this]
    rw [div_eq_div_iff (mul_ne_zero hnR (sub_ne_zero.mpr (Ne.symm hxy))) hnR]
    rw [← hgeom]
    ring

/-- A buyer-symmetric visit strategy `θ : [a, 1] → Δ^m`. -/
structure VisitStrategy (M : Market) where
  θ : Fin M.m → ℝ → ℝ
  hmeas : ∀ j, Measurable (θ j)
  hnonneg : ∀ j v, 0 ≤ θ j v
  hsum : ∀ v ∈ Icc M.a 1, ∑ j : Fin M.m, θ j v = 1

/-- Effective distribution induced at seller `j`: `F_j(v) = 1 - ∫_v^1 θ_j(u) f(u) du`. -/
noncomputable def effDist (M : Market) (θ : VisitStrategy M) (j : Fin M.m) (v : ℝ) : ℝ :=
  1 - ∫ u in v..1, θ.θ j u * M.f u

/-- Interim winning probability `x_j(v)` under hierarchical mechanism `mech` and
effective distribution `Fj` (equation (2)). -/
noncomputable def alloc (M : Market) (mech : HierarchicalMech) (Fj : ℝ → ℝ) (v : ℝ) : ℝ :=
  if v < mech.r then 0
  else
    match mech.pools.find? (fun I => decide (I.α < v ∧ v < I.β)) with
    | some I => poolAvg M.n (Fj I.α) (Fj I.β)
    | none => (Fj v) ^ (M.n - 1)

/-- Interim buyer surplus `s_j(v) = ∫_0^v x_j(u) du` (equation (3)). -/
noncomputable def surplus (M : Market) (mech : HierarchicalMech) (Fj : ℝ → ℝ) (v : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..v, alloc M mech Fj u

/-- Expected payment of a type-`v` visitor `p_j(v) = v x_j(v) - s_j(v)` (equation (3)). -/
noncomputable def payment (M : Market) (mech : HierarchicalMech) (Fj : ℝ → ℝ) (v : ℝ) : ℝ :=
  v * alloc M mech Fj v - surplus M mech Fj v

/-- Seller `j`'s expected revenue `R_j = n ∫_a^1 p_j(v) θ_j(v) f(v) dv` (equation (3)). -/
noncomputable def sellerRev (M : Market) (mech : HierarchicalMech)
    (θ : VisitStrategy M) (j : Fin M.m) : ℝ :=
  (M.n : ℝ) * ∫ v in M.a..1, payment M mech (effDist M θ j) v * θ.θ j v * M.f v

/-- Sequential rationality (SR): for a.e. `v ∈ [a, 1]`, if `θ_j(v) > 0` then
`s_j(v) ≥ s_k(v)` for all `k`. -/
def IsSR (M : Market) (mechs : Fin M.m → HierarchicalMech) (θ : VisitStrategy M) : Prop :=
  ∀ᵐ v ∂(volume.restrict (Icc M.a 1)),
    ∀ j k : Fin M.m, 0 < θ.θ j v →
      surplus M (mechs k) (effDist M θ k) v ≤ surplus M (mechs j) (effDist M θ j) v

/-! ### Quantity-Path Representation and Border's Constraint -/

/-- Border's feasibility constraint in quantity coordinates (equation (7)):
`∫_0^q (t(u) - u)(1 - u)^(n - 2) du ≤ 0` for all `q ∈ [0, q0]`. -/
def BorderFeasible (M : Market) (q0 : ℝ) (t : ℝ → ℝ) : Prop :=
  ∀ q ∈ Icc (0 : ℝ) q0, ∫ u in (0 : ℝ)..q, (t u - u) * (1 - u) ^ (M.n - 2) ≤ 0

/-- Quantity-path revenue functional (equation (6)):
`n ρ t0 (1 - q0)^(n - 1) + ∫_0^{q0} Π(t(q), q) W(q) dq - ℓ`. -/
noncomputable def pathRev (M : Market) (P : ℝ → ℝ) (ρ q0 t0 ℓ : ℝ) (t : ℝ → ℝ) : ℝ :=
  (M.n : ℝ) * ρ * t0 * (1 - q0) ^ (M.n - 1) +
    (∫ q in (0 : ℝ)..q0, M.cournotRev P (t q) q * M.W q) - ℓ

/-- Weighted excess supply functional `E(q) = (n - 1) ∫_0^q (t(u) - u)(1 - u)^(n - 2) du`. -/
noncomputable def excessSupply (M : Market) (t : ℝ → ℝ) (q : ℝ) : ℝ :=
  ((M.n : ℝ) - 1) * ∫ u in (0 : ℝ)..q, (t u - u) * (1 - u) ^ (M.n - 2)

/-- Reserve-increase quantity path `t^S(q) = min(q, t0)` for `t0 ≤ q0`. -/
def reserveIncreasePath (t0 : ℝ) (q : ℝ) : ℝ := min q t0

/-- Revenue of the standard auction `SPA(r)` inducing final traffic `t0 ≤ 1/m`
in a covered market against rivals at `SPA(ρ)` (equation (6) at `t^S(q) = min(q, t0)`). -/
noncomputable def reserveIncreaseRev (M : Market) (P : ℝ → ℝ) (ρ t0 : ℝ) : ℝ :=
  let q0 := (1 - t0) / ((M.m : ℝ) - 1)
  pathRev M P ρ q0 t0 0 (reserveIncreasePath t0)

end AuctionCompetition
