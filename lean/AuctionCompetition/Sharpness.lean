import AuctionCompetition.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.Compact

/-!
# Sharpness of Cournot's Condition (Section 6 and Appendix C)

Formalization of Section 6 (Theorem 5, small-numbers phenomenon, and smooth truncated Pareto
family with `sup_F m̄(F) = ∞`) and Appendix C (Propositions C.1 and C.2) of Mallesh M. Pai,
*Auction Design under Competition*.

## Main Results
- `propC1_curvature_sign`: `2 ∂_{tt}Π + ∂_{tq}Π = P'(mq)((m + 3) - ((m + 1)/m) E(v))`,
  strictly negative iff `E(v) < X̄(m)` and strictly positive iff `E(v) > X̄(m)`.
- `propC1_small_pool_expansion`: Leading-order `O(d³)` expansion of the single interior pool
  revenue gain `D` as band width `d = q_hi - q_lo → 0` (equation (23)).
- `propC1_narrow_pool_induces_interior_band`: Every sufficiently narrow pool `(α, β)` containing
  `v ∈ (max ρ a, 1)` induces a narrow interior band `[v₁, v₄] ⊂ (max ρ a, 1)` with
  `d ≤ F(β) - F(α) → 0`.
- `theorem5_small_pools`: Theorem 5(i) — at any fixed `n ≥ 2`, narrow pools containing `v`
  strictly lower revenue if `E(v) < X̄(m)` and strictly raise revenue if `E(v) > X̄(m)`.
- `propC2_many_buyers_limit`: Proposition C.2(i) — `lim_{n → ∞} D_n / (1 - q_lo)^n = J(q_lo, q_hi)`.
- `propC2_narrow_band_2m`: Proposition C.2(ii) — tangent equivalence and narrow-band expansion
  `J(q, q + d) = (1/2) ∂_{tt}Π(q, q) d + o(d)` yielding the `E ≤ 2m` necessary condition.
- `propC2_covered_counterexample`: Proposition C.2(iii) — explicit `C¹` covered-market
  distribution (`a > 0`, `ψ_m(a) > 0`, `E ≤ X` on `[a, 1]`) for every `X > m + 1` admitting an
  interior band with `J(q_lo, q_hi) > 0`.
- `theorem5_many_buyers`: Theorem 5(ii) — for every `X > m + 1`, the covered-market distribution
  admits an interior band with `D_n > 0` for all sufficiently large `n`.
- `mbar_finite_for_smooth_F`: For any fixed `SmoothMarket`, `|E(v)| ≤ K / f_min²`, so `ψ_m` is
  nondecreasing for all sufficiently large `m`.
- `sup_mbar_infinite`: For any `m ≥ 2`, the smooth truncated Pareto family satisfies
  `E(a) = (α + 1) / (2α) > X̄(m)` for `α < 1 / (2 X̄(m) - 1)`.
-/

open MeasureTheory Set Filter Topology

namespace AuctionCompetition

/-! ### Shared Cournot & Single-Band Primitives -/

/-- Cournot oligopoly revenue `Π(t, q) = t * P(t + (m - 1)q)` parameterized by `m`. -/
noncomputable def cournotRevOf (m : ℕ) (P : ℝ → ℝ) (t q : ℝ) : ℝ :=
  t * P (t + ((m : ℝ) - 1) * q)

/-- First own-quantity derivative `∂_t Π(t, q) = P(z) + t P'(z)` where `z = t + (m - 1)q`. -/
noncomputable def d_t_Pi (m : ℕ) (P P' : ℝ → ℝ) (t q : ℝ) : ℝ :=
  P (t + ((m : ℝ) - 1) * q) + t * P' (t + ((m : ℝ) - 1) * q)

/-- Second own-quantity derivative `∂_{tt} Π(t, q) = 2 P'(z) + t P''(z)`. -/
noncomputable def d_tt_Pi (m : ℕ) (P' P'' : ℝ → ℝ) (t q : ℝ) : ℝ :=
  2 * P' (t + ((m : ℝ) - 1) * q) + t * P'' (t + ((m : ℝ) - 1) * q)

/-- Cross derivative `∂_{tq} Π(t, q) = (m - 1)(P'(z) + t P''(z))`. -/
noncomputable def d_tq_Pi (m : ℕ) (P' P'' : ℝ → ℝ) (t q : ℝ) : ℝ :=
  ((m : ℝ) - 1) * (P' (t + ((m : ℝ) - 1) * q) + t * P'' (t + ((m : ℝ) - 1) * q))

/-- Weighting density `W_n(q) = n(n - 1)(1 - q)^(n - 2)` parameterized by `n`. -/
noncomputable def W_of (n : ℕ) (q : ℝ) : ℝ :=
  (n : ℝ) * ((n : ℝ) - 1) * (1 - q) ^ (n - 2)

/-- Split quantity `q*` of an interior band `[q_lo, q_hi]` defined by equation (5):
`(1 - q*)^(n - 1) = ((1 - q_lo)^n - (1 - q_hi)^n) / (n (q_hi - q_lo))`. -/
noncomputable def qStar (n : ℕ) (q_lo q_hi : ℝ) : ℝ :=
  1 - (poolAvg n (1 - q_hi) (1 - q_lo)) ^ ((1 : ℝ) / ((n : ℝ) - 1))

/-- Revenue change `D` of a single interior pool band `[q_lo, q_hi]` (Theorem 1, eq. (8)). -/
noncomputable def singleBandGainOf (m n : ℕ) (P : ℝ → ℝ) (q_lo q_hi : ℝ) : ℝ :=
  let qs := qStar n q_lo q_hi
  (∫ q in q_lo..qs, (cournotRevOf m P q_lo q - cournotRevOf m P q q) * W_of n q) +
  (∫ q in qs..q_hi, (cournotRevOf m P q_hi q - cournotRevOf m P q q) * W_of n q)

/-- Revenue change `D` of a single interior pool band for a given `M : Market`. -/
noncomputable def singleBandGain (M : Market) (P : ℝ → ℝ) (q_lo q_hi : ℝ) : ℝ :=
  singleBandGainOf M.m M.n P q_lo q_hi

/-- Many-buyers secant-minus-tangent limit `J(q_lo, q_hi)` (Proposition C.2, eq. (24)). -/
noncomputable def J_secant (m : ℕ) (P P' : ℝ → ℝ) (q_lo q_hi : ℝ) : ℝ :=
  (cournotRevOf m P q_hi q_lo - cournotRevOf m P q_lo q_lo) / (q_hi - q_lo) -
    d_t_Pi m P P' q_lo q_lo

/-- First derivative of inverse demand `P'(z) = -1 / f(P(z))`. -/
noncomputable def invDemandDeriv (M : Market) (inv : M.InverseDemand) (z : ℝ) : ℝ :=
  -1 / M.f (inv.P z)

/-- Second derivative of inverse demand `P''(z) = -f'(P(z)) / f(P(z))³`. -/
noncomputable def invDemandDeriv2 (M : SmoothMarket) (inv : M.toMarket.InverseDemand) (z : ℝ) : ℝ :=
  -M.f' (inv.P z) / (M.f (inv.P z)) ^ 3

/-! ### Inverse Demand `C²` Calculus Helpers -/

lemma invDemand_P_mem_Ioo (M : Market) (inv : M.InverseDemand) {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) :
    inv.P z ∈ Ioo M.a 1 := by
  constructor
  · rw [← inv.hP_one]
    exact inv.hP_strictAnti (Ioo_subset_Icc_self hz) (right_mem_Icc.mpr zero_le_one) hz.2
  · rw [← inv.hP_zero]
    exact inv.hP_strictAnti (left_mem_Icc.mpr zero_le_one) (Ioo_subset_Icc_self hz) hz.1

lemma invDemandDeriv_neg (M : Market) (inv : M.InverseDemand) {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    invDemandDeriv M inv z < 0 := by
  unfold invDemandDeriv
  have hfpos : 0 < M.f (inv.P z) := M.hf_pos (inv.P z) (inv.hP_mem z hz)
  exact div_neg_of_neg_of_pos (by norm_num) hfpos

lemma invDemandDeriv_continuousOn (M : Market) (inv : M.InverseDemand) :
    ContinuousOn (invDemandDeriv M inv) (Icc 0 1) := by
  unfold invDemandDeriv
  refine ContinuousOn.div continuousOn_const (M.hf_cont.comp inv.hP_cont inv.hP_mem) ?_
  intro z hz
  exact (M.hf_pos (inv.P z) (inv.hP_mem z hz)).ne'

lemma invDemandDeriv2_continuousOn (M : SmoothMarket) (inv : M.toMarket.InverseDemand) :
    ContinuousOn (invDemandDeriv2 M inv) (Icc 0 1) := by
  unfold invDemandDeriv2
  refine ContinuousOn.div (M.hf'_cont.comp inv.hP_cont inv.hP_mem).neg
    ((M.hf_cont.comp inv.hP_cont inv.hP_mem).pow 3) ?_
  intro z hz
  exact pow_ne_zero 3 (M.hf_pos (inv.P z) (inv.hP_mem z hz)).ne'

lemma hasDerivAt_invDemandDeriv (M : SmoothMarket) (inv : M.toMarket.InverseDemand)
    {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (invDemandDeriv M.toMarket inv) (invDemandDeriv2 M inv z) z := by
  have hPz : inv.P z ∈ Ioo M.a 1 := invDemand_P_mem_Ioo M.toMarket inv hz
  have hfpos : 0 < M.f (inv.P z) := M.hf_pos (inv.P z) (Ioo_subset_Icc_self hPz)
  have hfne : M.f (inv.P z) ≠ 0 := hfpos.ne'
  have hP : HasDerivAt inv.P (-1 / M.f (inv.P z)) z := inv.hP_deriv_open z hz
  have hf : HasDerivAt M.f (M.f' (inv.P z)) (inv.P z) := M.hf_deriv_open (inv.P z) hPz
  have hcomp : HasDerivAt (fun x => M.f (inv.P x)) (M.f' (inv.P z) * (-1 / M.f (inv.P z))) z :=
    hf.comp z hP
  have hdiv : HasDerivAt (fun x => -1 / M.f (inv.P x))
      ((0 * M.f (inv.P z) - (-1) * (M.f' (inv.P z) * (-1 / M.f (inv.P z)))) /
        (M.f (inv.P z)) ^ 2) z :=
    (hasDerivAt_const z (-1 : ℝ)).div hcomp hfne
  have hfun : invDemandDeriv M.toMarket inv = fun x => -1 / M.f (inv.P x) := rfl
  rw [hfun]
  refine hdiv.congr_deriv ?_
  unfold invDemandDeriv2
  field_simp
  ring

lemma hasDerivAt_cournotRev_t (M : Market) (inv : M.InverseDemand)
    {t q : ℝ} (hz : t + ((M.m : ℝ) - 1) * q ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun s => cournotRevOf M.m inv.P s q)
      (d_t_Pi M.m inv.P (invDemandDeriv M inv) t q) t := by
  have hlin : HasDerivAt (fun s => s + ((M.m : ℝ) - 1) * q) 1 t := by
    simpa using (hasDerivAt_id t).add_const (((M.m : ℝ) - 1) * q)
  have hP : HasDerivAt (fun s => inv.P (s + ((M.m : ℝ) - 1) * q))
      (invDemandDeriv M inv (t + ((M.m : ℝ) - 1) * q) * 1) t :=
    (inv.hP_deriv_open _ hz).comp t hlin
  have hmul : HasDerivAt (fun s => s * inv.P (s + ((M.m : ℝ) - 1) * q))
      (1 * inv.P (t + ((M.m : ℝ) - 1) * q) +
        t * (invDemandDeriv M inv (t + ((M.m : ℝ) - 1) * q) * 1)) t :=
    (hasDerivAt_id t).mul hP
  have hfun : (fun s => cournotRevOf M.m inv.P s q) =
      fun s => s * inv.P (s + ((M.m : ℝ) - 1) * q) := rfl
  rw [hfun]
  refine hmul.congr_deriv ?_
  unfold d_t_Pi
  ring

lemma hasDerivAt_d_t_Pi_t (M : SmoothMarket) (inv : M.toMarket.InverseDemand)
    {t q : ℝ} (hz : t + ((M.m : ℝ) - 1) * q ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun s => d_t_Pi M.m inv.P (invDemandDeriv M.toMarket inv) s q)
      (d_tt_Pi M.m (invDemandDeriv M.toMarket inv) (invDemandDeriv2 M inv) t q) t := by
  have hlin : HasDerivAt (fun s => s + ((M.m : ℝ) - 1) * q) 1 t := by
    simpa using (hasDerivAt_id t).add_const (((M.m : ℝ) - 1) * q)
  have hP : HasDerivAt (fun s => inv.P (s + ((M.m : ℝ) - 1) * q))
      (invDemandDeriv M.toMarket inv (t + ((M.m : ℝ) - 1) * q) * 1) t :=
    (inv.hP_deriv_open _ hz).comp t hlin
  have hP' : HasDerivAt (fun s => invDemandDeriv M.toMarket inv (s + ((M.m : ℝ) - 1) * q))
      (invDemandDeriv2 M inv (t + ((M.m : ℝ) - 1) * q) * 1) t :=
    HasDerivAt.comp t (h₂ := invDemandDeriv M.toMarket inv) (hasDerivAt_invDemandDeriv M inv hz) hlin
  have hadd : HasDerivAt (fun s => inv.P (s + ((M.m : ℝ) - 1) * q) +
        s * invDemandDeriv M.toMarket inv (s + ((M.m : ℝ) - 1) * q)) _ t :=
    hP.add ((hasDerivAt_id t).mul hP')
  have hfun : (fun s => d_t_Pi M.m inv.P (invDemandDeriv M.toMarket inv) s q) =
      fun s => inv.P (s + ((M.m : ℝ) - 1) * q) +
        s * invDemandDeriv M.toMarket inv (s + ((M.m : ℝ) - 1) * q) := rfl
  rw [hfun]
  refine hadd.congr_deriv ?_
  unfold d_tt_Pi
  simp only [id_eq]
  ring

lemma hasDerivAt_d_t_Pi_q (M : SmoothMarket) (inv : M.toMarket.InverseDemand)
    {t q : ℝ} (hz : t + ((M.m : ℝ) - 1) * q ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun w => d_t_Pi M.m inv.P (invDemandDeriv M.toMarket inv) t w)
      (d_tq_Pi M.m (invDemandDeriv M.toMarket inv) (invDemandDeriv2 M inv) t q) q := by
  have hlin : HasDerivAt (fun w => t + ((M.m : ℝ) - 1) * w) ((M.m : ℝ) - 1) q := by
    simpa using ((hasDerivAt_id q).const_mul ((M.m : ℝ) - 1)).const_add t
  have hP : HasDerivAt (fun w => inv.P (t + ((M.m : ℝ) - 1) * w))
      (invDemandDeriv M.toMarket inv (t + ((M.m : ℝ) - 1) * q) * ((M.m : ℝ) - 1)) q :=
    (inv.hP_deriv_open _ hz).comp q hlin
  have hP' : HasDerivAt (fun w => invDemandDeriv M.toMarket inv (t + ((M.m : ℝ) - 1) * w))
      (invDemandDeriv2 M inv (t + ((M.m : ℝ) - 1) * q) * ((M.m : ℝ) - 1)) q :=
    HasDerivAt.comp q (h₂ := invDemandDeriv M.toMarket inv) (hasDerivAt_invDemandDeriv M inv hz) hlin
  have hadd : HasDerivAt (fun w => inv.P (t + ((M.m : ℝ) - 1) * w) +
        t * invDemandDeriv M.toMarket inv (t + ((M.m : ℝ) - 1) * w)) _ q :=
    hP.add (hP'.const_mul t)
  have hfun : (fun w => d_t_Pi M.m inv.P (invDemandDeriv M.toMarket inv) t w) =
      fun w => inv.P (t + ((M.m : ℝ) - 1) * w) +
        t * invDemandDeriv M.toMarket inv (t + ((M.m : ℝ) - 1) * w) := rfl
  rw [hfun]
  refine hadd.congr_deriv ?_
  unfold d_tq_Pi
  ring

/-! ### Properties of `qStar` and Exact Zero-Mean Identity -/

lemma sh_poolAvg_bounds {n : ℕ} (hn : 2 ≤ n) {x y : ℝ} (hx0 : 0 < x) (hxy : x < y) :
    x ^ (n - 1) < poolAvg n x y ∧ poolAvg n x y < y ^ (n - 1) := by
  rw [poolAvg_eq_sum n (by omega)]
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hle_lo : ∀ k ∈ Finset.range n, x ^ (n - 1) ≤ x ^ k * y ^ (n - 1 - k) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have h1 : x ^ (n - 1 - k) ≤ y ^ (n - 1 - k) := pow_le_pow_left₀ hx0.le hxy.le _
    calc x ^ (n - 1) = x ^ k * x ^ (n - 1 - k) := by rw [← pow_add, Nat.add_sub_cancel' (by omega)]
      _ ≤ x ^ k * y ^ (n - 1 - k) := mul_le_mul_of_nonneg_left h1 (pow_nonneg hx0.le k)
  have hle_hi : ∀ k ∈ Finset.range n, x ^ k * y ^ (n - 1 - k) ≤ y ^ (n - 1) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have h1 : x ^ k ≤ y ^ k := pow_le_pow_left₀ hx0.le hxy.le _
    calc x ^ k * y ^ (n - 1 - k) ≤ y ^ k * y ^ (n - 1 - k) :=
          mul_le_mul_of_nonneg_right h1 (pow_nonneg (hx0.trans hxy).le _)
      _ = y ^ (n - 1) := by rw [← pow_add, Nat.add_sub_cancel' (by omega)]
  constructor
  · rw [lt_div_iff₀ hnR]
    have hlt0 : x ^ (n - 1) < x ^ 0 * y ^ (n - 1 - 0) := by
      simp only [pow_zero, one_mul, Nat.sub_zero]
      exact pow_lt_pow_left₀ hxy hx0.le (by omega)
    have hsum := Finset.sum_lt_sum hle_lo ⟨0, Finset.mem_range.mpr (by omega), hlt0⟩
    simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using hsum
  · rw [div_lt_iff₀ hnR]
    have hltn : x ^ (n - 1) * y ^ (n - 1 - (n - 1)) < y ^ (n - 1) := by
      simp only [Nat.sub_self, pow_zero, mul_one]
      exact pow_lt_pow_left₀ hxy hx0.le (by omega)
    have hsum := Finset.sum_lt_sum hle_hi ⟨n - 1, Finset.mem_range.mpr (by omega), hltn⟩
    simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using hsum

lemma one_sub_qStar_pow {n : ℕ} (hn : 2 ≤ n) {q_lo q_hi : ℝ}
    (hq_lt : q_lo < q_hi) (hq_hi1 : q_hi < 1) :
    (1 - qStar n q_lo q_hi) ^ (n - 1) = poolAvg n (1 - q_hi) (1 - q_lo) := by
  have hx0 : 0 < 1 - q_hi := by linarith
  have hxy : 1 - q_hi < 1 - q_lo := by linarith
  have havg_pos : 0 < poolAvg n (1 - q_hi) (1 - q_lo) :=
    lt_trans (pow_pos hx0 _) (sh_poolAvg_bounds hn hx0 hxy).1
  unfold qStar
  rw [sub_sub_cancel]
  have hn1 : ((n : ℝ) - 1) ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [← Real.rpow_natCast, hcast, ← Real.rpow_mul havg_pos.le, one_div_mul_cancel hn1,
    Real.rpow_one]

lemma qStar_mem_Ioo {n : ℕ} (hn : 2 ≤ n) {q_lo q_hi : ℝ}
    (hq_lt : q_lo < q_hi) (hq_hi1 : q_hi < 1) :
    qStar n q_lo q_hi ∈ Ioo q_lo q_hi := by
  have hx0 : 0 < 1 - q_hi := by linarith
  have hxy : 1 - q_hi < 1 - q_lo := by linarith
  have hbounds := sh_poolAvg_bounds hn hx0 hxy
  have hpow := one_sub_qStar_pow hn hq_lt hq_hi1
  have hpos : 0 ≤ 1 - qStar n q_lo q_hi := by
    unfold qStar; rw [sub_sub_cancel]
    exact Real.rpow_nonneg (lt_trans (pow_pos hx0 _) hbounds.1).le _
  have hlt1 : 1 - q_hi < 1 - qStar n q_lo q_hi := by
    by_contra h
    push Not at h
    have := pow_le_pow_left₀ hpos h (n - 1)
    linarith [hbounds.1, hpow]
  have hlt2 : 1 - qStar n q_lo q_hi < 1 - q_lo := by
    by_contra h
    push Not at h
    have := pow_le_pow_left₀ (hx0.trans hxy).le h (n - 1)
    linarith [hbounds.2, hpow]
  exact ⟨by linarith, by linarith⟩

/-- Exact algebraic sandwich for `(q* - q_lo) / (q_hi - q_lo)`:
`(1/2) * ((1 - q_hi)/(1 - q_lo))^(n - 2) ≤ (q* - q_lo) / d ≤ (1/2) * ((1 - q_lo)/(1 - q_hi))^(n - 2)`. -/
lemma qStar_ratio_sandwich {n : ℕ} (hn : 2 ≤ n) {q_lo q_hi : ℝ}
    (hq_lt : q_lo < q_hi) (hq_hi1 : q_hi < 1) :
    (1 / 2 : ℝ) * ((1 - q_hi) / (1 - q_lo)) ^ (n - 2) ≤
      (qStar n q_lo q_hi - q_lo) / (q_hi - q_lo) ∧
    (qStar n q_lo q_hi - q_lo) / (q_hi - q_lo) ≤
      (1 / 2 : ℝ) * ((1 - q_lo) / (1 - q_hi)) ^ (n - 2) := by
  set A4 := 1 - q_lo
  set A1 := 1 - q_hi
  set B := 1 - qStar n q_lo q_hi
  set d := q_hi - q_lo
  set y := qStar n q_lo q_hi - q_lo
  have hA1 : 0 < A1 := by linarith
  have hA4 : 0 < A4 := by linarith
  have hd : 0 < d := by linarith
  have hqs := qStar_mem_Ioo hn hq_lt hq_hi1
  have hA1B : A1 < B := by simp only [A1, B]; linarith [hqs.2]
  have hBA4 : B < A4 := by simp only [B, A4]; linarith [hqs.1]
  have hB : 0 < B := hA1.trans hA1B
  have hA4_sub_A1 : A4 - A1 = d := by simp only [A4, A1, d]; ring
  have hA4_sub_B : A4 - B = y := by simp only [A4, B, y]; ring
  have hpow : B ^ (n - 1) = poolAvg n A1 A4 := one_sub_qStar_pow hn hq_lt hq_hi1
  -- Express A4^(n-1) - poolAvg n A1 A4 as a double sum of (n-2)-degree monomials
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1R : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hLHS_eq : A4 ^ (n - 1) - poolAvg n A1 A4 =
      (d / n) * ∑ k ∈ Finset.range n,
        ∑ j ∈ Finset.range k, A4 ^ (n - 1 - k + j) * A1 ^ (k - 1 - j) := by
    rw [poolAvg_eq_sum n (by omega)]
    have h1 : A4 ^ (n - 1) = (∑ _k ∈ Finset.range n, A4 ^ (n - 1)) / (n : ℝ) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_div_cancel_left₀ _ hnR.ne']
    rw [h1, ← sub_div, ← Finset.sum_sub_distrib]
    have hterm : ∀ k ∈ Finset.range n,
        A4 ^ (n - 1) - A1 ^ k * A4 ^ (n - 1 - k) =
        d * ∑ j ∈ Finset.range k, A4 ^ (n - 1 - k + j) * A1 ^ (k - 1 - j) := by
      intro k hk
      rw [Finset.mem_range] at hk
      have hfactor : A4 ^ (n - 1) - A1 ^ k * A4 ^ (n - 1 - k) =
          A4 ^ (n - 1 - k) * (A4 ^ k - A1 ^ k) := by
        rw [mul_sub, ← pow_add, Nat.sub_add_cancel (by omega), mul_comm (A4 ^ (n - 1 - k))]
      rw [hfactor, ← geom_sum₂_mul A4 A1 k, hA4_sub_A1, mul_comm _ d, ← mul_assoc, mul_comm _ d,
        mul_assoc, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      rw [pow_add]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, mul_div_right_comm]
  have hcount : (∑ k ∈ Finset.range n, (k : ℝ)) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
    have hnat : 2 * ∑ k ∈ Finset.range n, k = n * (n - 1) := by
      simpa [mul_comm] using Finset.sum_range_id_mul_two n
    have hcast : (2 : ℝ) * ∑ k ∈ Finset.range n, (k : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
      have := congrArg (Nat.cast (R := ℝ)) hnat
      push_cast [Nat.cast_sub (by omega : 1 ≤ n)] at this
      exact this
    linarith
  have hsum_lo : ((n : ℝ) * ((n : ℝ) - 1) / 2) * A1 ^ (n - 2) ≤
      ∑ k ∈ Finset.range n, ∑ j ∈ Finset.range k, A4 ^ (n - 1 - k + j) * A1 ^ (k - 1 - j) := by
    rw [← hcount, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro k hk
    rw [Finset.mem_range] at hk
    calc (k : ℝ) * A1 ^ (n - 2) = ∑ _j ∈ Finset.range k, A1 ^ (n - 2) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ j ∈ Finset.range k, A4 ^ (n - 1 - k + j) * A1 ^ (k - 1 - j) := by
          apply Finset.sum_le_sum
          intro j hj
          rw [Finset.mem_range] at hj
          have hexp : (n - 1 - k + j) + (k - 1 - j) = n - 2 := by omega
          calc A1 ^ (n - 2) = A1 ^ (n - 1 - k + j) * A1 ^ (k - 1 - j) := by
                rw [← pow_add, hexp]
            _ ≤ A4 ^ (n - 1 - k + j) * A1 ^ (k - 1 - j) :=
                mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hA1.le (hA1B.trans hBA4).le _)
                  (pow_nonneg hA1.le _)
  have hsum_hi : ∑ k ∈ Finset.range n, ∑ j ∈ Finset.range k,
      A4 ^ (n - 1 - k + j) * A1 ^ (k - 1 - j) ≤
      ((n : ℝ) * ((n : ℝ) - 1) / 2) * A4 ^ (n - 2) := by
    rw [← hcount, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro k hk
    rw [Finset.mem_range] at hk
    calc ∑ j ∈ Finset.range k, A4 ^ (n - 1 - k + j) * A1 ^ (k - 1 - j)
        ≤ ∑ _j ∈ Finset.range k, A4 ^ (n - 2) := by
          apply Finset.sum_le_sum
          intro j hj
          rw [Finset.mem_range] at hj
          have hexp : (n - 1 - k + j) + (k - 1 - j) = n - 2 := by omega
          calc A4 ^ (n - 1 - k + j) * A1 ^ (k - 1 - j)
              ≤ A4 ^ (n - 1 - k + j) * A4 ^ (k - 1 - j) :=
                mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hA1.le (hA1B.trans hBA4).le _)
                  (pow_nonneg hA4.le _)
            _ = A4 ^ (n - 2) := by rw [← pow_add, hexp]
      _ = (k : ℝ) * A4 ^ (n - 2) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- Express A4^(n-1) - B^(n-1) via geom_sum₂_mul
  have hRHS_eq : A4 ^ (n - 1) - B ^ (n - 1) =
      y * ∑ j ∈ Finset.range (n - 1), A4 ^ j * B ^ (n - 2 - j) := by
    rw [← geom_sum₂_mul A4 B (n - 1), hA4_sub_B, mul_comm]
    simp only [Nat.sub_sub]
  have hBsum_lo : ((n : ℝ) - 1) * A1 ^ (n - 2) ≤
      ∑ j ∈ Finset.range (n - 1), A4 ^ j * B ^ (n - 2 - j) := by
    have hcard : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
    rw [← hcard]
    calc ((n - 1 : ℕ) : ℝ) * A1 ^ (n - 2) = ∑ _j ∈ Finset.range (n - 1), A1 ^ (n - 2) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ j ∈ Finset.range (n - 1), A4 ^ j * B ^ (n - 2 - j) := by
          apply Finset.sum_le_sum
          intro j hj
          rw [Finset.mem_range] at hj
          have hexp : j + (n - 2 - j) = n - 2 := by omega
          calc A1 ^ (n - 2) = A1 ^ j * A1 ^ (n - 2 - j) := by rw [← pow_add, hexp]
            _ ≤ A4 ^ j * B ^ (n - 2 - j) :=
                mul_le_mul (pow_le_pow_left₀ hA1.le (hA1B.trans hBA4).le _)
                  (pow_le_pow_left₀ hA1.le hA1B.le _) (pow_nonneg hA1.le _) (pow_nonneg hA4.le _)
  have hBsum_hi : ∑ j ∈ Finset.range (n - 1), A4 ^ j * B ^ (n - 2 - j) ≤
      ((n : ℝ) - 1) * A4 ^ (n - 2) := by
    have hcard : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
    rw [← hcard]
    calc ∑ j ∈ Finset.range (n - 1), A4 ^ j * B ^ (n - 2 - j)
        ≤ ∑ _j ∈ Finset.range (n - 1), A4 ^ (n - 2) := by
          apply Finset.sum_le_sum
          intro j hj
          rw [Finset.mem_range] at hj
          have hexp : j + (n - 2 - j) = n - 2 := by omega
          calc A4 ^ j * B ^ (n - 2 - j) ≤ A4 ^ j * A4 ^ (n - 2 - j) :=
                mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hB.le hBA4.le _) (pow_nonneg hA4.le _)
            _ = A4 ^ (n - 2) := by rw [← pow_add, hexp]
      _ = ((n - 1 : ℕ) : ℝ) * A4 ^ (n - 2) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- Combine both sandwiches
  have hdn : 0 < d / n := div_pos hd hnR
  have hy_pos : 0 < y := by simp only [y]; linarith [hqs.1]
  have h1 : (d / 2) * ((n : ℝ) - 1) * A1 ^ (n - 2) ≤ A4 ^ (n - 1) - B ^ (n - 1) := by
    rw [hpow, hLHS_eq]
    have := mul_le_mul_of_nonneg_left hsum_lo hdn.le
    calc (d / 2) * ((n : ℝ) - 1) * A1 ^ (n - 2)
        = (d / n) * ((n : ℝ) * ((n : ℝ) - 1) / 2 * A1 ^ (n - 2)) := by field_simp
      _ ≤ _ := this
  have h2 : A4 ^ (n - 1) - B ^ (n - 1) ≤ (d / 2) * ((n : ℝ) - 1) * A4 ^ (n - 2) := by
    rw [hpow, hLHS_eq]
    have := mul_le_mul_of_nonneg_left hsum_hi hdn.le
    calc _ ≤ (d / n) * ((n : ℝ) * ((n : ℝ) - 1) / 2 * A4 ^ (n - 2)) := this
      _ = (d / 2) * ((n : ℝ) - 1) * A4 ^ (n - 2) := by field_simp
  have h3 : y * (((n : ℝ) - 1) * A1 ^ (n - 2)) ≤ A4 ^ (n - 1) - B ^ (n - 1) := by
    rw [hRHS_eq]; exact mul_le_mul_of_nonneg_left hBsum_lo hy_pos.le
  have h4 : A4 ^ (n - 1) - B ^ (n - 1) ≤ y * (((n : ℝ) - 1) * A4 ^ (n - 2)) := by
    rw [hRHS_eq]; exact mul_le_mul_of_nonneg_left hBsum_hi hy_pos.le
  constructor
  · rw [le_div_iff₀ hd, div_pow]
    have hcomb : (d / 2) * ((n : ℝ) - 1) * A1 ^ (n - 2) ≤ y * (((n : ℝ) - 1) * A4 ^ (n - 2)) :=
      h1.trans h4
    have hden : 0 < ((n : ℝ) - 1) * A4 ^ (n - 2) := mul_pos hn1R (pow_pos hA4 _)
    have hle : (1 / 2 : ℝ) * (A1 ^ (n - 2) / A4 ^ (n - 2)) * d * (((n : ℝ) - 1) * A4 ^ (n - 2)) ≤
        y * (((n : ℝ) - 1) * A4 ^ (n - 2)) := by
      have heq : (1 / 2 : ℝ) * (A1 ^ (n - 2) / A4 ^ (n - 2)) * d * (((n : ℝ) - 1) * A4 ^ (n - 2)) =
          (d / 2) * ((n : ℝ) - 1) * A1 ^ (n - 2) := by
        have hA4p : A4 ^ (n - 2) ≠ 0 := (pow_pos hA4 _).ne'
        field_simp
      rw [heq]; exact hcomb
    exact le_of_mul_le_mul_right hle hden
  · rw [div_le_iff₀ hd, div_pow]
    have hcomb : y * (((n : ℝ) - 1) * A1 ^ (n - 2)) ≤ (d / 2) * ((n : ℝ) - 1) * A4 ^ (n - 2) :=
      h3.trans h2
    have hden : 0 < ((n : ℝ) - 1) * A1 ^ (n - 2) := mul_pos hn1R (pow_pos hA1 _)
    have hle : y * (((n : ℝ) - 1) * A1 ^ (n - 2)) ≤
        (1 / 2 : ℝ) * (A4 ^ (n - 2) / A1 ^ (n - 2)) * d * (((n : ℝ) - 1) * A1 ^ (n - 2)) := by
      have heq : (1 / 2 : ℝ) * (A4 ^ (n - 2) / A1 ^ (n - 2)) * d * (((n : ℝ) - 1) * A1 ^ (n - 2)) =
          (d / 2) * ((n : ℝ) - 1) * A4 ^ (n - 2) := by
        have hA1p : A1 ^ (n - 2) ≠ 0 := (pow_pos hA1 _).ne'
        field_simp
      rw [heq]; exact hcomb
    exact le_of_mul_le_mul_right hle hden

/-- Exact integral `∫ a..b (1 - q)^(n - 2) dq = ((1 - a)^(n - 1) - (1 - b)^(n - 1)) / (n - 1)`. -/
lemma integral_one_sub_pow {n : ℕ} (hn : 2 ≤ n) (a b : ℝ) :
    ∫ q in a..b, (1 - q) ^ (n - 2) =
      ((1 - a) ^ (n - 1) - (1 - b) ^ (n - 1)) / ((n : ℝ) - 1) := by
  have hn1 : ((n : ℝ) - 1) ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hderiv : ∀ x ∈ uIcc a b,
      HasDerivAt (fun q => -(1 - q) ^ (n - 1) / ((n : ℝ) - 1)) ((1 - x) ^ (n - 2)) x := by
    intro x _
    have h1 : HasDerivAt (fun q : ℝ => 1 - q) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub (1 : ℝ)
    have h2 : HasDerivAt (fun q => (1 - q) ^ (n - 1))
        (((n - 1 : ℕ) : ℝ) * (1 - x) ^ (n - 1 - 1) * (-1)) x :=
      h1.pow (n - 1)
    have h3 : HasDerivAt (fun q => -(1 - q) ^ (n - 1) / ((n : ℝ) - 1))
        (-(((n - 1 : ℕ) : ℝ) * (1 - x) ^ (n - 1 - 1) * (-1)) / ((n : ℝ) - 1)) x :=
      h2.neg.div_const _
    refine h3.congr_deriv ?_
    have hsub : n - 1 - 1 = n - 2 := by omega
    rw [hsub, hcast]
    field_simp
  have hint : IntervalIntegrable (fun q => (1 - q) ^ (n - 2)) volume a b :=
    ((continuous_const.sub continuous_id).pow (n - 2)).intervalIntegrable a b
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  ring

/-- Exact integral `∫ a..b (q - c) * (1 - q)^(n - 2) dq`. -/
lemma integral_linear_mul_one_sub_pow {n : ℕ} (hn : 2 ≤ n) (c a b : ℝ) :
    ∫ q in a..b, (q - c) * (1 - q) ^ (n - 2) =
      ((a - c) * (1 - a) ^ (n - 1) - (b - c) * (1 - b) ^ (n - 1)) / ((n : ℝ) - 1) +
        ((1 - a) ^ n - (1 - b) ^ n) / ((n : ℝ) * ((n : ℝ) - 1)) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hn1 : ((n : ℝ) - 1) ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hderiv : ∀ x ∈ uIcc a b,
      HasDerivAt (fun q => -(q - c) * (1 - q) ^ (n - 1) / ((n : ℝ) - 1) -
        (1 - q) ^ n / ((n : ℝ) * ((n : ℝ) - 1))) ((x - c) * (1 - x) ^ (n - 2)) x := by
    intro x _
    have h1 : HasDerivAt (fun q : ℝ => 1 - q) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub (1 : ℝ)
    have hqc : HasDerivAt (fun q : ℝ => -(q - c)) (-1) x := by
      have h := ((hasDerivAt_id x).sub_const c).neg
      exact h
    have hp1 : HasDerivAt (fun q => (1 - q) ^ (n - 1))
        (((n - 1 : ℕ) : ℝ) * (1 - x) ^ (n - 1 - 1) * (-1)) x := h1.pow (n - 1)
    have hpn : HasDerivAt (fun q => (1 - q) ^ n)
        ((n : ℝ) * (1 - x) ^ (n - 1) * (-1)) x := h1.pow n
    have ht1 : HasDerivAt (fun q => -(q - c) * (1 - q) ^ (n - 1) / ((n : ℝ) - 1)) _ x :=
      (hqc.mul hp1).div_const ((n : ℝ) - 1)
    have ht2 : HasDerivAt (fun q => (1 - q) ^ n / ((n : ℝ) * ((n : ℝ) - 1))) _ x :=
      hpn.div_const ((n : ℝ) * ((n : ℝ) - 1))
    refine (ht1.sub ht2).congr_deriv ?_
    have hsub : n - 1 - 1 = n - 2 := by omega
    rw [hsub, hcast]
    field_simp
    ring
  have hint : IntervalIntegrable (fun q => (q - c) * (1 - q) ^ (n - 2)) volume a b :=
    ((continuous_id.sub continuous_const).mul
      ((continuous_const.sub continuous_id).pow (n - 2))).intervalIntegrable a b
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  ring

/-- Exact zero-mean identity (eq. (10)) for a single interior band `[q_lo, q_hi]` with split `q*`. -/
lemma singleBand_zero_mean {n : ℕ} (hn : 2 ≤ n) {q_lo q_hi : ℝ}
    (hq_lt : q_lo < q_hi) (hq_hi1 : q_hi < 1) :
    (∫ q in q_lo..(qStar n q_lo q_hi), (q_lo - q) * W_of n q) +
    (∫ q in (qStar n q_lo q_hi)..q_hi, (q_hi - q) * W_of n q) = 0 := by
  set qs := qStar n q_lo q_hi
  have h1 : ∫ q in q_lo..qs, (q_lo - q) * W_of n q =
      ((n : ℝ) * ((n : ℝ) - 1)) * ∫ q in q_lo..qs, -((q - q_lo) * (1 - q) ^ (n - 2)) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; ext q; unfold W_of; ring
  have h2 : ∫ q in qs..q_hi, (q_hi - q) * W_of n q =
      ((n : ℝ) * ((n : ℝ) - 1)) *
        ((q_hi - q_lo) * (∫ q in qs..q_hi, (1 - q) ^ (n - 2)) -
         (∫ q in qs..q_hi, (q - q_lo) * (1 - q) ^ (n - 2))) := by
    have hc1 : IntervalIntegrable (fun q => (q_hi - q_lo) * (1 - q) ^ (n - 2)) volume qs q_hi :=
      (continuous_const.mul ((continuous_const.sub continuous_id).pow (n - 2))).intervalIntegrable _ _
    have hc2 : IntervalIntegrable (fun q => (q - q_lo) * (1 - q) ^ (n - 2)) volume qs q_hi :=
      ((continuous_id.sub continuous_const).mul
        ((continuous_const.sub continuous_id).pow (n - 2))).intervalIntegrable _ _
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hc1 hc2,
      ← intervalIntegral.integral_const_mul]
    congr 1; ext q; unfold W_of; ring
  rw [h1, h2, intervalIntegral.integral_neg, ← mul_add]
  have hlin_comb : -(∫ q in q_lo..qs, (q - q_lo) * (1 - q) ^ (n - 2)) +
      ((q_hi - q_lo) * (∫ q in qs..q_hi, (1 - q) ^ (n - 2)) -
       (∫ q in qs..q_hi, (q - q_lo) * (1 - q) ^ (n - 2))) =
      (q_hi - q_lo) * (∫ q in qs..q_hi, (1 - q) ^ (n - 2)) -
      (∫ q in q_lo..q_hi, (q - q_lo) * (1 - q) ^ (n - 2)) := by
    have hint1 : IntervalIntegrable (fun q => (q - q_lo) * (1 - q) ^ (n - 2)) volume q_lo qs :=
      ((continuous_id.sub continuous_const).mul
        ((continuous_const.sub continuous_id).pow (n - 2))).intervalIntegrable _ _
    have hint2 : IntervalIntegrable (fun q => (q - q_lo) * (1 - q) ^ (n - 2)) volume qs q_hi :=
      ((continuous_id.sub continuous_const).mul
        ((continuous_const.sub continuous_id).pow (n - 2))).intervalIntegrable _ _
    rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
    ring
  rw [hlin_comb, integral_one_sub_pow hn qs q_hi, integral_linear_mul_one_sub_pow hn q_lo q_lo q_hi]
  have hpow : (1 - qs) ^ (n - 1) = poolAvg n (1 - q_hi) (1 - q_lo) :=
    one_sub_qStar_pow hn hq_lt hq_hi1
  have hne : (1 - q_hi : ℝ) ≠ 1 - q_lo := by linarith
  have havg : poolAvg n (1 - q_hi) (1 - q_lo) =
      ((1 - q_lo) ^ n - (1 - q_hi) ^ n) / ((n : ℝ) * (q_hi - q_lo)) := by
    unfold poolAvg
    rw [ite_eq_right_iff.mpr (fun h => absurd h hne)]
    congr 1; ring
  rw [hpow, havg]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hn1 : ((n : ℝ) - 1) ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hd : q_hi - q_lo ≠ 0 := by linarith
  field_simp
  ring

/-! ### Proposition C.1 and Theorem 5(i): Small Pools at Fixed `n` -/

/-- **Proposition C.1 (curvature sign identity)**:
At `v ∈ (a, 1)` with `q = (1 - F(v))/m`,
`2 ∂_{tt}Π(q, q) + ∂_{tq}Π(q, q) = P'(mq) * ((m + 3) - ((m + 1)/m) * E(v))`,
which is strictly negative iff `E(v) < X̄(m)` and strictly positive iff `E(v) > X̄(m)`. -/
theorem propC1_curvature_sign (M : SmoothMarket) (inv : M.toMarket.InverseDemand)
    {v : ℝ} (hv : v ∈ Ioo M.a 1) :
    let q := (1 - M.F v) / (M.m : ℝ)
    let P' := invDemandDeriv M.toMarket inv
    let P'' := invDemandDeriv2 M inv
    (2 * d_tt_Pi M.m P' P'' q q + d_tq_Pi M.m P' P'' q q =
      P' ((M.m : ℝ) * q) * (((M.m : ℝ) + 3) - (((M.m : ℝ) + 1) / (M.m : ℝ)) * curvatureE M v)) ∧
    (2 * d_tt_Pi M.m P' P'' q q + d_tq_Pi M.m P' P'' q q < 0 ↔ curvatureE M v < Xbar M.m) ∧
    (0 < 2 * d_tt_Pi M.m P' P'' q q + d_tq_Pi M.m P' P'' q q ↔ Xbar M.m < curvatureE M v) := by
  intro q P' P''
  have hmpos : (0 : ℝ) < M.m := M.toMarket.m_pos_real
  have hmR : (2 : ℝ) ≤ M.m := by exact_mod_cast M.hm
  have hmq : (M.m : ℝ) * q = 1 - M.F v := mul_div_cancel₀ _ hmpos.ne'
  have hPmq : inv.P ((M.m : ℝ) * q) = v := by
    rw [hmq]
    exact inv.hP_left v (Ioo_subset_Icc_self hv)
  have hfpos : 0 < M.f v := M.hf_pos v (Ioo_subset_Icc_self hv)
  have hP'_val : P' ((M.m : ℝ) * q) = -1 / M.f v := by
    simp only [P', invDemandDeriv, hPmq]
  have hP''_val : P'' ((M.m : ℝ) * q) = -M.f' v / (M.f v) ^ 3 := by
    simp only [P'', invDemandDeriv2, hPmq]
  have harg : q + ((M.m : ℝ) - 1) * q = (M.m : ℝ) * q := by ring
  have hid : 2 * d_tt_Pi M.m P' P'' q q + d_tq_Pi M.m P' P'' q q =
      P' ((M.m : ℝ) * q) * (((M.m : ℝ) + 3) - (((M.m : ℝ) + 1) / (M.m : ℝ)) * curvatureE M v) := by
    unfold d_tt_Pi d_tq_Pi curvatureE
    rw [harg, hP'_val, hP''_val]
    have hq_def : q = (1 - M.F v) / (M.m : ℝ) := rfl
    rw [hq_def]
    have hfne : M.f v ≠ 0 := hfpos.ne'
    have hmne : (M.m : ℝ) ≠ 0 := hmpos.ne'
    field_simp
    ring
  have hP'_neg : P' ((M.m : ℝ) * q) < 0 := by
    rw [hP'_val]; exact div_neg_of_neg_of_pos (by norm_num) hfpos
  have hXbar : Xbar M.m = ((M.m : ℝ) * ((M.m : ℝ) + 3)) / ((M.m : ℝ) + 1) := Xbar_eq M.hm
  have hfactor : ((M.m : ℝ) + 3) - (((M.m : ℝ) + 1) / (M.m : ℝ)) * curvatureE M v =
      (((M.m : ℝ) + 1) / (M.m : ℝ)) * (Xbar M.m - curvatureE M v) := by
    rw [hXbar]
    have hm1 : (M.m : ℝ) + 1 ≠ 0 := by linarith
    have hmne : (M.m : ℝ) ≠ 0 := hmpos.ne'
    field_simp
  have hcpos : 0 < ((M.m : ℝ) + 1) / (M.m : ℝ) := div_pos (by linarith) hmpos
  refine ⟨hid, ?_, ?_⟩
  · rw [hid, hfactor, mul_neg_iff]
    constructor
    · rintro (⟨h1, _⟩ | ⟨_, h2⟩)
      · linarith
      · have : 0 < Xbar M.m - curvatureE M v := (mul_pos_iff_of_pos_left hcpos).mp h2
        linarith
    · intro hlt
      right
      exact ⟨hP'_neg, mul_pos hcpos (by linarith)⟩
  · rw [hid, hfactor, mul_pos_iff]
    constructor
    · rintro (⟨h1, _⟩ | ⟨_, h2⟩)
      · linarith
      · have : Xbar M.m - curvatureE M v < 0 := (mul_neg_iff.mp h2).resolve_right (fun h => by linarith) |>.2
        linarith
    · intro hlt
      right
      exact ⟨hP'_neg, mul_neg_of_pos_of_neg hcpos (by linarith)⟩

/-- Helper: exact evaluation of the two polynomial integrals in the Proposition C.1 expansion. -/
private lemma propC1_poly_integrals (q_lo q_hi qs : ℝ) :
    ((∫ q in q_lo..qs, -((q - q_lo) ^ 2)) +
      (∫ q in qs..q_hi, (q_hi - q_lo) ^ 2 - (q - q_lo) ^ 2) =
        (q_hi - q_lo) ^ 2 * (q_hi - qs) - (q_hi - q_lo) ^ 3 / 3) ∧
    ((∫ q in q_lo..qs, (q - q_lo) * (q_lo - q)) +
      (∫ q in qs..q_hi, (q - q_lo) * (q_hi - q)) =
        (q_hi - q_lo) * ((q_hi - q_lo) ^ 2 - (qs - q_lo) ^ 2) / 2 - (q_hi - q_lo) ^ 3 / 3) := by
  have hint_sq : ∀ a b : ℝ, ∫ q in a..b, (q - q_lo) ^ 2 =
      ((b - q_lo) ^ 3 - (a - q_lo) ^ 3) / 3 := by
    intro a b
    have hderiv : ∀ x ∈ uIcc a b,
        HasDerivAt (fun q => (q - q_lo) ^ 3 / 3) ((x - q_lo) ^ 2) x := by
      intro x _
      have h1 : HasDerivAt (fun q => (q - q_lo) ^ 3 / 3)
          (((3 : ℕ) : ℝ) * (x - q_lo) ^ (3 - 1) * 1 / 3) x :=
        (((hasDerivAt_id x).sub_const q_lo).pow 3).div_const 3
      refine h1.congr_deriv ?_; norm_num
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (((continuous_id.sub continuous_const).pow 2).intervalIntegrable a b)]
    ring
  have hint_lin : ∀ a b : ℝ, ∫ q in a..b, (q - q_lo) =
      ((b - q_lo) ^ 2 - (a - q_lo) ^ 2) / 2 := by
    intro a b
    have hderiv : ∀ x ∈ uIcc a b,
        HasDerivAt (fun q => (q - q_lo) ^ 2 / 2) (x - q_lo) x := by
      intro x _
      have h1 : HasDerivAt (fun q => (q - q_lo) ^ 2 / 2)
          (((2 : ℕ) : ℝ) * (x - q_lo) ^ (2 - 1) * 1 / 2) x :=
        (((hasDerivAt_id x).sub_const q_lo).pow 2).div_const 2
      refine h1.congr_deriv ?_; norm_num
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((continuous_id.sub continuous_const).intervalIntegrable a b)]
    ring
  constructor
  · have hsub : ∫ q in qs..q_hi, (q_hi - q_lo) ^ 2 - (q - q_lo) ^ 2 =
        (∫ q in qs..q_hi, (q_hi - q_lo) ^ 2) - (∫ q in qs..q_hi, (q - q_lo) ^ 2) :=
      intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
        (((continuous_id.sub continuous_const).pow 2).intervalIntegrable _ _)
    rw [intervalIntegral.integral_neg, hsub, intervalIntegral.integral_const, smul_eq_mul,
      hint_sq q_lo qs, hint_sq qs q_hi]
    ring
  · have h1 : ∫ q in q_lo..qs, (q - q_lo) * (q_lo - q) =
        -(∫ q in q_lo..qs, (q - q_lo) ^ 2) := by
      rw [← intervalIntegral.integral_neg]
      congr 1; ext q; ring
    have h2 : ∫ q in qs..q_hi, (q - q_lo) * (q_hi - q) =
        (q_hi - q_lo) * (∫ q in qs..q_hi, (q - q_lo)) - (∫ q in qs..q_hi, (q - q_lo) ^ 2) := by
      have hi1 : IntervalIntegrable (fun q => (q_hi - q_lo) * (q - q_lo)) volume qs q_hi :=
        (continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable _ _
      have hi2 : IntervalIntegrable (fun q => (q - q_lo) ^ 2) volume qs q_hi :=
        ((continuous_id.sub continuous_const).pow 2).intervalIntegrable _ _
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hi1 hi2]
      congr 1; ext q; ring
    rw [h1, h2, hint_sq q_lo qs, hint_sq qs q_hi, hint_lin qs q_hi]
    ring

/-- Helper: quadratic approximation of `Π(t, r) - Π(r, r) - ∂_t Π(q_lo, q_lo)(t - r)` on `[q_lo, q_hi]`. -/
private lemma propC1_quad_approx (M : SmoothMarket) (inv : M.toMarket.InverseDemand)
    {q_lo q_hi A_tt A_tq η : ℝ} (hq_lt : q_lo < q_hi) (hη_pos : 0 < η)
    (hmem_Ioo : ∀ u w : ℝ, u ∈ Icc q_lo q_hi → w ∈ Icc q_lo q_hi →
      u + ((M.m : ℝ) - 1) * w ∈ Ioo (0 : ℝ) 1)
    (htt_close : ∀ u w : ℝ, u ∈ Icc q_lo q_hi → w ∈ Icc q_lo q_hi →
      |d_tt_Pi M.m (invDemandDeriv M.toMarket inv) (invDemandDeriv2 M inv) u w - A_tt| < η)
    (htq_close : ∀ u w : ℝ, u ∈ Icc q_lo q_hi → w ∈ Icc q_lo q_hi →
      |d_tq_Pi M.m (invDemandDeriv M.toMarket inv) (invDemandDeriv2 M inv) u w - A_tq| < η)
    {t r : ℝ} (ht : t ∈ Icc q_lo q_hi) (hr : r ∈ Icc q_lo q_hi) :
    |(cournotRevOf M.m inv.P t r - cournotRevOf M.m inv.P r r) -
      d_t_Pi M.m inv.P (invDemandDeriv M.toMarket inv) q_lo q_lo * (t - r) -
      ((1 / 2 : ℝ) * A_tt * ((t - q_lo) ^ 2 - (r - q_lo) ^ 2) +
        A_tq * (r - q_lo) * (t - r))| ≤ 2 * η * (q_hi - q_lo) ^ 2 := by
  set P' := invDemandDeriv M.toMarket inv
  set P'' := invDemandDeriv2 M inv
  set d := q_hi - q_lo
  have hdt_bound : ∀ s ∈ Icc q_lo q_hi,
      |d_t_Pi M.m inv.P P' s r - d_t_Pi M.m inv.P P' q_lo q_lo -
        A_tt * (s - q_lo) - A_tq * (r - q_lo)| ≤ 2 * η * d := by
    intro s hs
    have h1 : d_t_Pi M.m inv.P P' s r - d_t_Pi M.m inv.P P' q_lo r - A_tt * (s - q_lo) =
        ∫ u in q_lo..s, (d_tt_Pi M.m P' P'' u r - A_tt) := by
      have hd1 : ∀ u ∈ uIcc q_lo s,
          HasDerivAt (fun x => d_t_Pi M.m inv.P P' x r - A_tt * x)
            (d_tt_Pi M.m P' P'' u r - A_tt) u := by
        intro u hu
        rw [uIcc_of_le hs.1] at hu
        have hmem := hmem_Ioo u r ⟨hu.1, hu.2.trans hs.2⟩ hr
        exact (hasDerivAt_d_t_Pi_t M inv hmem).sub ((hasDerivAt_id u).const_mul A_tt |>.congr_deriv (mul_one A_tt))
      have hint : IntervalIntegrable (fun u => d_tt_Pi M.m P' P'' u r - A_tt) volume q_lo s := by
        apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le hs.1]
        have hlin : ContinuousOn (fun u => u + ((M.m : ℝ) - 1) * r) (Icc q_lo s) :=
          continuousOn_id.add continuousOn_const
        have hmap : MapsTo (fun u => u + ((M.m : ℝ) - 1) * r) (Icc q_lo s) (Icc 0 1) :=
          fun u hu => Ioo_subset_Icc_self (hmem_Ioo u r ⟨hu.1, hu.2.trans hs.2⟩ hr)
        exact (((continuousOn_const.mul ((invDemandDeriv_continuousOn M.toMarket inv).comp hlin hmap)).add
          (continuousOn_id.mul ((invDemandDeriv2_continuousOn M inv).comp hlin hmap))).sub
            continuousOn_const)
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd1 hint]; ring
    have h2 : d_t_Pi M.m inv.P P' q_lo r - d_t_Pi M.m inv.P P' q_lo q_lo - A_tq * (r - q_lo) =
        ∫ w in q_lo..r, (d_tq_Pi M.m P' P'' q_lo w - A_tq) := by
      have hd2 : ∀ w ∈ uIcc q_lo r,
          HasDerivAt (fun x => d_t_Pi M.m inv.P P' q_lo x - A_tq * x)
            (d_tq_Pi M.m P' P'' q_lo w - A_tq) w := by
        intro w hw
        rw [uIcc_of_le hr.1] at hw
        have hmem := hmem_Ioo q_lo w (left_mem_Icc.mpr hq_lt.le) ⟨hw.1, hw.2.trans hr.2⟩
        exact (hasDerivAt_d_t_Pi_q M inv hmem).sub ((hasDerivAt_id w).const_mul A_tq |>.congr_deriv (mul_one A_tq))
      have hint : IntervalIntegrable (fun w => d_tq_Pi M.m P' P'' q_lo w - A_tq) volume q_lo r := by
        apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le hr.1]
        have hlin : ContinuousOn (fun w => q_lo + ((M.m : ℝ) - 1) * w) (Icc q_lo r) :=
          continuousOn_const.add (continuousOn_const.mul continuousOn_id)
        have hmap : MapsTo (fun w => q_lo + ((M.m : ℝ) - 1) * w) (Icc q_lo r) (Icc 0 1) :=
          fun w hw => Ioo_subset_Icc_self (hmem_Ioo q_lo w (left_mem_Icc.mpr hq_lt.le) ⟨hw.1, hw.2.trans hr.2⟩)
        exact ((continuousOn_const.mul (((invDemandDeriv_continuousOn M.toMarket inv).comp hlin hmap).add
          (continuousOn_const.mul ((invDemandDeriv2_continuousOn M inv).comp hlin hmap)))).sub
            continuousOn_const)
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd2 hint]; ring
    have hb1 : |∫ u in q_lo..s, (d_tt_Pi M.m P' P'' u r - A_tt)| ≤ η * (s - q_lo) := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := q_lo) (b := s) (C := η)
        (f := fun u => d_tt_Pi M.m P' P'' u r - A_tt) (by
          intro u hu
          rw [uIoc_of_le hs.1] at hu
          rw [Real.norm_eq_abs]
          exact (htt_close u r ⟨hu.1.le, hu.2.trans hs.2⟩ hr).le)
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hs.1)] at h
      exact h
    have hb2 : |∫ w in q_lo..r, (d_tq_Pi M.m P' P'' q_lo w - A_tq)| ≤ η * (r - q_lo) := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := q_lo) (b := r) (C := η)
        (f := fun w => d_tq_Pi M.m P' P'' q_lo w - A_tq) (by
          intro w hw
          rw [uIoc_of_le hr.1] at hw
          rw [Real.norm_eq_abs]
          exact (htq_close q_lo w (left_mem_Icc.mpr hq_lt.le) ⟨hw.1.le, hw.2.trans hr.2⟩).le)
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hr.1)] at h
      exact h
    have hsplit : d_t_Pi M.m inv.P P' s r - d_t_Pi M.m inv.P P' q_lo q_lo -
        A_tt * (s - q_lo) - A_tq * (r - q_lo) =
        (d_t_Pi M.m inv.P P' s r - d_t_Pi M.m inv.P P' q_lo r - A_tt * (s - q_lo)) +
        (d_t_Pi M.m inv.P P' q_lo r - d_t_Pi M.m inv.P P' q_lo q_lo - A_tq * (r - q_lo)) := by ring
    rw [hsplit, h1, h2]
    calc |(∫ u in q_lo..s, (d_tt_Pi M.m P' P'' u r - A_tt)) +
            (∫ w in q_lo..r, (d_tq_Pi M.m P' P'' q_lo w - A_tq))|
        ≤ |∫ u in q_lo..s, (d_tt_Pi M.m P' P'' u r - A_tt)| +
          |∫ w in q_lo..r, (d_tq_Pi M.m P' P'' q_lo w - A_tq)| := abs_add_le _ _
      _ ≤ η * (s - q_lo) + η * (r - q_lo) := add_le_add hb1 hb2
      _ ≤ η * d + η * d := add_le_add
          (mul_le_mul_of_nonneg_left (by linarith [hs.2]) hη_pos.le)
          (mul_le_mul_of_nonneg_left (by linarith [hr.2]) hη_pos.le)
      _ = 2 * η * d := by ring
  have hftc : (cournotRevOf M.m inv.P t r - cournotRevOf M.m inv.P r r) -
      d_t_Pi M.m inv.P P' q_lo q_lo * (t - r) -
      ((1 / 2 : ℝ) * A_tt * ((t - q_lo) ^ 2 - (r - q_lo) ^ 2) +
        A_tq * (r - q_lo) * (t - r)) =
      ∫ s in r..t, (d_t_Pi M.m inv.P P' s r - d_t_Pi M.m inv.P P' q_lo q_lo -
        A_tt * (s - q_lo) - A_tq * (r - q_lo)) := by
    have hderiv : ∀ s ∈ uIcc r t,
        HasDerivAt (fun x => cournotRevOf M.m inv.P x r -
          d_t_Pi M.m inv.P P' q_lo q_lo * x -
          ((1 / 2 : ℝ) * A_tt * (x - q_lo) ^ 2 + A_tq * (r - q_lo) * x))
          (d_t_Pi M.m inv.P P' s r - d_t_Pi M.m inv.P P' q_lo q_lo -
            A_tt * (s - q_lo) - A_tq * (r - q_lo)) s := by
      intro s hs
      have hs_in : s ∈ Icc q_lo q_hi := (uIcc_subset_Icc hr ht) hs
      have h1 : HasDerivAt (fun x => cournotRevOf M.m inv.P x r)
          (d_t_Pi M.m inv.P P' s r) s :=
        hasDerivAt_cournotRev_t M.toMarket inv (hmem_Ioo s r hs_in hr)
      have h2 : HasDerivAt (fun x => d_t_Pi M.m inv.P P' q_lo q_lo * x)
          (d_t_Pi M.m inv.P P' q_lo q_lo * 1) s :=
        (hasDerivAt_id s).const_mul (d_t_Pi M.m inv.P P' q_lo q_lo)
      have h3 : HasDerivAt (fun x => (1 / 2 : ℝ) * A_tt * (x - q_lo) ^ 2)
          ((1 / 2 : ℝ) * A_tt * (((2 : ℕ) : ℝ) * (s - q_lo) ^ (2 - 1) * 1)) s :=
        (((hasDerivAt_id s).sub_const q_lo).pow 2).const_mul ((1 / 2 : ℝ) * A_tt)
      have h4 : HasDerivAt (fun x => A_tq * (r - q_lo) * x)
          (A_tq * (r - q_lo) * 1) s :=
        (hasDerivAt_id s).const_mul (A_tq * (r - q_lo))
      refine ((h1.sub h2).sub (h3.add h4)).congr_deriv ?_
      norm_num
      ring
    have hint : IntervalIntegrable (fun s => d_t_Pi M.m inv.P P' s r -
        d_t_Pi M.m inv.P P' q_lo q_lo - A_tt * (s - q_lo) - A_tq * (r - q_lo)) volume r t := by
      apply ContinuousOn.intervalIntegrable
      have hsub : uIcc r t ⊆ Icc q_lo q_hi := uIcc_subset_Icc hr ht
      have hlin : ContinuousOn (fun s => s + ((M.m : ℝ) - 1) * r) (uIcc r t) :=
        continuousOn_id.add continuousOn_const
      have hmap : MapsTo (fun s => s + ((M.m : ℝ) - 1) * r) (uIcc r t) (Icc 0 1) :=
        fun s hs => Ioo_subset_Icc_self (hmem_Ioo s r (hsub hs) hr)
      exact ((((inv.hP_cont.comp hlin hmap).add
        (continuousOn_id.mul ((invDemandDeriv_continuousOn M.toMarket inv).comp hlin hmap))).sub
          continuousOn_const).sub
        (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))).sub continuousOn_const
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    ring
  rw [hftc]
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const (a := r) (b := t)
    (C := 2 * η * d) (f := fun s => d_t_Pi M.m inv.P P' s r -
      d_t_Pi M.m inv.P P' q_lo q_lo - A_tt * (s - q_lo) - A_tq * (r - q_lo)) (by
      intro s hs
      have hs_in : s ∈ Icc q_lo q_hi := (uIoc_subset_uIcc.trans (uIcc_subset_Icc hr ht)) hs
      rw [Real.norm_eq_abs]
      exact hdt_bound s hs_in)
  rw [Real.norm_eq_abs] at hnorm
  have htr : |t - r| ≤ d := by
    rw [abs_le]; constructor <;> linarith [ht.1, ht.2, hr.1, hr.2]
  have hd_pos : 0 < d := by linarith
  calc |∫ s in r..t, (d_t_Pi M.m inv.P P' s r - d_t_Pi M.m inv.P P' q_lo q_lo -
          A_tt * (s - q_lo) - A_tq * (r - q_lo))|
      ≤ 2 * η * d * |t - r| := hnorm
    _ ≤ 2 * η * d * d := mul_le_mul_of_nonneg_left htr (by positivity)
    _ = 2 * η * d ^ 2 := by ring

set_option maxHeartbeats 400000 in
/-- **Proposition C.1 (small-pool Taylor expansion, equation (23))**:
Under `M : SmoothMarket` and `inv : M.toMarket.InverseDemand`, fix `n ≥ 2` and `v ∈ (a, 1)`
with `q = (1 - F(v))/m`. For every `ε > 0`, there exists `δ > 0` such that for every band
`[q_lo, q_hi]` with `q_lo < q_hi` and `|q_lo - q| < δ`, `|q_hi - q| < δ`,
`|D - (n(n - 1)/24) * (1 - q_lo)^(n - 2) * (2 ∂_{tt}Π(q, q) + ∂_{tq}Π(q, q)) * d³| ≤ ε * d³`,
where `d = q_hi - q_lo` and `1 - q_lo = A(v₄)`. -/
theorem propC1_small_pool_expansion (M : SmoothMarket) (inv : M.toMarket.InverseDemand)
    {v : ℝ} (hv : v ∈ Ioo M.a 1) :
    let q := (1 - M.F v) / (M.m : ℝ)
    let P' := invDemandDeriv M.toMarket inv
    let P'' := invDemandDeriv2 M inv
    let coeff := ((M.n : ℝ) * ((M.n : ℝ) - 1) / 24) *
      (2 * d_tt_Pi M.m P' P'' q q + d_tq_Pi M.m P' P'' q q)
    ∀ ε > 0, ∃ δ > 0, ∀ q_lo q_hi : ℝ,
      q_lo < q_hi → |q_lo - q| < δ → |q_hi - q| < δ →
      |singleBandGain M.toMarket inv.P q_lo q_hi -
        coeff * (1 - q_lo) ^ (M.n - 2) * (q_hi - q_lo) ^ 3| ≤ ε * (q_hi - q_lo) ^ 3 := by
  intro q P' P'' coeff ε hε
  have hmpos : (0 : ℝ) < M.m := M.toMarket.m_pos_real
  have hmR : (2 : ℝ) ≤ M.m := by exact_mod_cast M.hm
  have hnR : (2 : ℝ) ≤ M.n := by exact_mod_cast M.hn
  have hFv : M.F v ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · rw [← M.hF_a]; exact M.toMarket.F_strictMonoOn (left_mem_Icc.mpr M.ha1.le) (Ioo_subset_Icc_self hv) hv.1
    · rw [← M.hF_1]; exact M.toMarket.F_strictMonoOn (Ioo_subset_Icc_self hv) (right_mem_Icc.mpr M.ha1.le) hv.2
  have hmq : (M.m : ℝ) * q = 1 - M.F v := mul_div_cancel₀ _ hmpos.ne'
  have hmq_mem : (M.m : ℝ) * q ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hFv.2], by linarith [hFv.1]⟩
  have hq_pos : 0 < q := by
    have : 0 < (M.m : ℝ) * q := hmq_mem.1
    nlinarith
  have hq_lt1 : q < 1 := by
    have : (M.m : ℝ) * q < 1 := hmq_mem.2
    nlinarith
  -- Choose δ₀ so that [q - δ₀, q + δ₀] stays strictly inside (0, 1/m)
  set δ₀ : ℝ := min (q / 2) (min ((1 - (M.m : ℝ) * q) / (2 * (M.m : ℝ))) ((1 - q) / 4))
  have hδ₀_pos : 0 < δ₀ := by
    refine lt_min (by linarith) (lt_min ?_ (by linarith))
    exact div_pos (by linarith [hmq_mem.2]) (by linarith)
  -- Constants for bounding second derivatives and W
  set A_tt := d_tt_Pi M.m P' P'' q q
  set A_tq := d_tq_Pi M.m P' P'' q q
  set M_2 := |A_tt| + |A_tq| + 1
  have hM2_pos : 0 < M_2 := by positivity
  set C_W : ℝ := (M.n : ℝ) * ((M.n : ℝ) - 1)
  have hCW_pos : 0 < C_W := by nlinarith
  -- Choose η > 0 small enough that all error terms sum to ≤ ε
  set η : ℝ := min 1 (ε / (10 * C_W * M_2 + 1))
  have hη_pos : 0 < η := lt_min zero_lt_one (div_pos hε (by positivity))
  -- Continuity of P' and P'' at mq
  have hP'_cont : ContinuousAt P' ((M.m : ℝ) * q) :=
    (invDemandDeriv_continuousOn M.toMarket inv).continuousAt (Icc_mem_nhds hmq_mem.1 hmq_mem.2)
  have hP''_cont : ContinuousAt P'' ((M.m : ℝ) * q) :=
    (invDemandDeriv2_continuousOn M inv).continuousAt (Icc_mem_nhds hmq_mem.1 hmq_mem.2)
  -- Continuity of (u, w) ↦ d_tt_Pi and d_tq_Pi at (q, q)
  have hval : q + ((M.m : ℝ) - 1) * q = (M.m : ℝ) * q := by ring
  have hP'_at : ContinuousAt P' (q + ((M.m : ℝ) - 1) * q) := by rwa [hval]
  have hP''_at : ContinuousAt P'' (q + ((M.m : ℝ) - 1) * q) := by rwa [hval]
  have hlin_c : ContinuousAt (fun p : ℝ × ℝ => p.1 + ((M.m : ℝ) - 1) * p.2) (q, q) :=
    continuousAt_fst.add (continuousAt_const.mul continuousAt_snd)
  have hP'_comp : ContinuousAt (fun p : ℝ × ℝ => P' (p.1 + ((M.m : ℝ) - 1) * p.2)) (q, q) :=
    ContinuousAt.comp (g := P') (f := fun p : ℝ × ℝ => p.1 + ((M.m : ℝ) - 1) * p.2) hP'_at hlin_c
  have hP''_comp : ContinuousAt (fun p : ℝ × ℝ => P'' (p.1 + ((M.m : ℝ) - 1) * p.2)) (q, q) :=
    ContinuousAt.comp (g := P'') (f := fun p : ℝ × ℝ => p.1 + ((M.m : ℝ) - 1) * p.2) hP''_at hlin_c
  have htt_cont : ContinuousAt (fun p : ℝ × ℝ => d_tt_Pi M.m P' P'' p.1 p.2) (q, q) := by
    unfold d_tt_Pi
    exact (continuousAt_const.mul hP'_comp).add (continuousAt_fst.mul hP''_comp)
  have htq_cont : ContinuousAt (fun p : ℝ × ℝ => d_tq_Pi M.m P' P'' p.1 p.2) (q, q) := by
    unfold d_tq_Pi
    exact continuousAt_const.mul (hP'_comp.add (continuousAt_fst.mul hP''_comp))
  -- Continuity of W_of M.n at q
  have hW_cont : ContinuousAt (W_of M.n) q :=
    (continuous_const.mul ((continuous_const.sub continuous_id).pow (M.n - 2))).continuousAt
  -- Continuity of r ↦ (1/2) * r^(n - 2) at 1 (for qStar ratio sandwich)
  have hpow_cont : ContinuousAt (fun r : ℝ => r ^ (M.n - 2)) 1 :=
    (continuous_pow (M.n - 2)).continuousAt
  -- Extract δ₁, δ₂, δ₃, δ₄ from continuity
  obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := Metric.continuousAt_iff.mp htt_cont η hη_pos
  obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ := Metric.continuousAt_iff.mp htq_cont η hη_pos
  obtain ⟨δ₃, hδ₃_pos, hδ₃⟩ := Metric.continuousAt_iff.mp hW_cont (η * C_W / 2)
    (by positivity)
  obtain ⟨δ₄, hδ₄_pos, hδ₄⟩ := Metric.continuousAt_iff.mp hpow_cont η hη_pos
  -- Choose final δ
  set δ_pow : ℝ := min ((1 - q) / 4) ((1 - q) * δ₄ / 8)
  have hδ_pow_pos : 0 < δ_pow := lt_min (by linarith) (div_pos (mul_pos (by linarith) hδ₄_pos) (by norm_num))
  set δ : ℝ := min δ₀ (min δ₁ (min δ₂ (min δ₃ δ_pow)))
  refine ⟨δ, lt_min hδ₀_pos (lt_min hδ₁_pos (lt_min hδ₂_pos (lt_min hδ₃_pos hδ_pow_pos))), ?_⟩
  intro q_lo q_hi hq_lt hlo hhi
  have hδ_le_δ₀ : δ ≤ δ₀ := min_le_left _ _
  have hδ_le_δ₁ : δ ≤ δ₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hδ_le_δ₂ : δ ≤ δ₂ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδ_le_δ₃ : δ ≤ δ₃ := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hδ_le_δpow : δ ≤ δ_pow := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  set d := q_hi - q_lo
  have hd_pos : 0 < d := by linarith
  have hq_lo_pos : 0 < q_lo := by
    have h1 : |q_lo - q| < q / 2 := lt_of_lt_of_le hlo (hδ_le_δ₀.trans (min_le_left _ _))
    linarith [(abs_lt.mp h1).1]
  have hq_hi_lt1 : q_hi < 1 := by
    have h1 : |q_hi - q| < (1 - q) / 4 :=
      lt_of_lt_of_le hhi (hδ_le_δ₀.trans ((min_le_right _ _).trans (min_le_right _ _)))
    linarith [(abs_lt.mp h1).2]
  have hq_lo_lt1 : q_lo < 1 := hq_lt.trans hq_hi_lt1
  -- Every u, w ∈ [q_lo, q_hi] satisfies u + (m - 1) * w ∈ (0, 1) and close to (q, q)
  have hmem_Ioo : ∀ u w : ℝ, u ∈ Icc q_lo q_hi → w ∈ Icc q_lo q_hi →
      u + ((M.m : ℝ) - 1) * w ∈ Ioo (0 : ℝ) 1 := by
    intro u w hu hw
    have hu_lo : |u - q| < δ := abs_lt.mpr
      ⟨by linarith [(abs_lt.mp hlo).1, hu.1], by linarith [(abs_lt.mp hhi).2, hu.2]⟩
    have hw_lo : |w - q| < δ := abs_lt.mpr
      ⟨by linarith [(abs_lt.mp hlo).1, hw.1], by linarith [(abs_lt.mp hhi).2, hw.2]⟩
    have hu_pos : 0 < u := lt_of_lt_of_le hq_lo_pos hu.1
    have hw_pos : 0 < w := lt_of_lt_of_le hq_lo_pos hw.1
    constructor
    · nlinarith
    · have hδ_m : δ ≤ (1 - (M.m : ℝ) * q) / (2 * (M.m : ℝ)) :=
        hδ_le_δ₀.trans ((min_le_right _ _).trans (min_le_left _ _))
      have h1 : u - q < (1 - (M.m : ℝ) * q) / (2 * (M.m : ℝ)) :=
        lt_of_lt_of_le (abs_lt.mp hu_lo).2 hδ_m
      have h2 : w - q < (1 - (M.m : ℝ) * q) / (2 * (M.m : ℝ)) :=
        lt_of_lt_of_le (abs_lt.mp hw_lo).2 hδ_m
      have h3 : (u - q) + ((M.m : ℝ) - 1) * (w - q) < (1 - (M.m : ℝ) * q) / 2 := by
        have : (M.m : ℝ) * ((1 - (M.m : ℝ) * q) / (2 * (M.m : ℝ))) = (1 - (M.m : ℝ) * q) / 2 := by
          field_simp
        nlinarith
      linarith [hmq_mem.2]
  have htt_close : ∀ u w : ℝ, u ∈ Icc q_lo q_hi → w ∈ Icc q_lo q_hi →
      |d_tt_Pi M.m P' P'' u w - A_tt| < η := by
    intro u w hu hw
    have hu_d : |u - q| < δ₁ := (abs_lt.mpr
      ⟨by linarith [(abs_lt.mp hlo).1, hu.1], by linarith [(abs_lt.mp hhi).2, hu.2]⟩).trans_le hδ_le_δ₁
    have hw_d : |w - q| < δ₁ := (abs_lt.mpr
      ⟨by linarith [(abs_lt.mp hlo).1, hw.1], by linarith [(abs_lt.mp hhi).2, hw.2]⟩).trans_le hδ_le_δ₁
    have hdist : dist (u, w) (q, q) < δ₁ := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      exact max_lt hu_d hw_d
    simpa [Real.dist_eq] using hδ₁ hdist
  have htq_close : ∀ u w : ℝ, u ∈ Icc q_lo q_hi → w ∈ Icc q_lo q_hi →
      |d_tq_Pi M.m P' P'' u w - A_tq| < η := by
    intro u w hu hw
    have hu_d : |u - q| < δ₂ := (abs_lt.mpr
      ⟨by linarith [(abs_lt.mp hlo).1, hu.1], by linarith [(abs_lt.mp hhi).2, hu.2]⟩).trans_le hδ_le_δ₂
    have hw_d : |w - q| < δ₂ := (abs_lt.mpr
      ⟨by linarith [(abs_lt.mp hlo).1, hw.1], by linarith [(abs_lt.mp hhi).2, hw.2]⟩).trans_le hδ_le_δ₂
    have hdist : dist (u, w) (q, q) < δ₂ := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      exact max_lt hu_d hw_d
    simpa [Real.dist_eq] using hδ₂ hdist
  -- Quadratic approximation of Π(t, r) - Π(r, r) - ∂_t Π(q_lo, q_lo) * (t - r) for t, r ∈ [q_lo, q_hi]
  have hquad : ∀ t r : ℝ, t ∈ Icc q_lo q_hi → r ∈ Icc q_lo q_hi →
      |(cournotRevOf M.m inv.P t r - cournotRevOf M.m inv.P r r) -
        d_t_Pi M.m inv.P P' q_lo q_lo * (t - r) -
        ((1 / 2 : ℝ) * A_tt * ((t - q_lo) ^ 2 - (r - q_lo) ^ 2) +
          A_tq * (r - q_lo) * (t - r))| ≤ 2 * η * d ^ 2 :=
    fun _ _ ht hr => propC1_quad_approx M inv hq_lt hη_pos hmem_Ioo htt_close htq_close ht hr
  -- Now assemble the integral decomposition on [q_lo, q*] and [q*, q_hi]
  set qs := qStar M.n q_lo q_hi
  have hqs := qStar_mem_Ioo M.hn hq_lt hq_hi_lt1
  set W0 := W_of M.n q_lo
  have hW_close : ∀ r ∈ Icc q_lo q_hi, |W_of M.n r - W0| ≤ η * C_W := by
    intro r hr
    have hr_d : |r - q| < δ₃ := (abs_lt.mpr
      ⟨by linarith [(abs_lt.mp hlo).1, hr.1], by linarith [(abs_lt.mp hhi).2, hr.2]⟩).trans_le hδ_le_δ₃
    have hlo_d : |q_lo - q| < δ₃ := hlo.trans_le hδ_le_δ₃
    have h1 := hδ₃ (by simpa [Real.dist_eq] using hr_d)
    have h2 := hδ₃ (by simpa [Real.dist_eq] using hlo_d)
    rw [Real.dist_eq] at h1 h2
    calc |W_of M.n r - W0| = |(W_of M.n r - W_of M.n q) - (W0 - W_of M.n q)| := by ring_nf
      _ ≤ |W_of M.n r - W_of M.n q| + |W0 - W_of M.n q| := abs_sub _ _
      _ ≤ η * C_W / 2 + η * C_W / 2 := add_le_add h1.le h2.le
      _ = η * C_W := by ring
  have hW_le : ∀ r ∈ Icc q_lo q_hi, |W_of M.n r| ≤ C_W := by
    intro r hr
    have hr0 : 0 ≤ 1 - r := by linarith [hr.2, hq_hi_lt1]
    have hr1 : 1 - r ≤ 1 := by linarith [hr.1, hq_lo_pos]
    unfold W_of
    rw [abs_of_nonneg (mul_nonneg hCW_pos.le (pow_nonneg hr0 _))]
    calc C_W * (1 - r) ^ (M.n - 2) ≤ C_W * 1 ^ (M.n - 2) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hr1 _) hCW_pos.le
      _ = C_W := by simp
  -- Define quadratic approximation Q1(r), Q2(r)
  let Q : ℝ → ℝ → ℝ := fun t r =>
    (1 / 2 : ℝ) * A_tt * ((t - q_lo) ^ 2 - (r - q_lo) ^ 2) + A_tq * (r - q_lo) * (t - r)
  let R : ℝ → ℝ → ℝ := fun t r =>
    (cournotRevOf M.m inv.P t r - cournotRevOf M.m inv.P r r) -
      d_t_Pi M.m inv.P P' q_lo q_lo * (t - r) - Q t r
  have hQ_bound : ∀ t r : ℝ, t ∈ Icc q_lo q_hi → r ∈ Icc q_lo q_hi → |Q t r| ≤ M_2 * d ^ 2 := by
    intro t r ht hr
    have h1 : |(t - q_lo) ^ 2 - (r - q_lo) ^ 2| ≤ d ^ 2 := by
      have ht0 : 0 ≤ t - q_lo := by linarith [ht.1]
      have htd : t - q_lo ≤ d := by linarith [ht.2]
      have hr0 : 0 ≤ r - q_lo := by linarith [hr.1]
      have hrd : r - q_lo ≤ d := by linarith [hr.2]
      rw [abs_le]; constructor <;> nlinarith
    have h2 : |(r - q_lo) * (t - r)| ≤ d ^ 2 := by
      rw [abs_mul, abs_of_nonneg (by linarith [hr.1])]
      have htr : |t - r| ≤ d := abs_le.mpr ⟨by linarith [ht.1, hr.2], by linarith [ht.2, hr.1]⟩
      calc (r - q_lo) * |t - r| ≤ d * d :=
            mul_le_mul (by linarith [hr.2]) htr (abs_nonneg _) hd_pos.le
        _ = d ^ 2 := by ring
    dsimp only [Q]
    calc |(1 / 2 : ℝ) * A_tt * ((t - q_lo) ^ 2 - (r - q_lo) ^ 2) + A_tq * (r - q_lo) * (t - r)|
        ≤ |(1 / 2 : ℝ) * A_tt * ((t - q_lo) ^ 2 - (r - q_lo) ^ 2)| +
          |A_tq * (r - q_lo) * (t - r)| := abs_add_le _ _
      _ = (1 / 2 : ℝ) * |A_tt| * |(t - q_lo) ^ 2 - (r - q_lo) ^ 2| +
          |A_tq| * |(r - q_lo) * (t - r)| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
            mul_assoc A_tq, abs_mul]
      _ ≤ (1 / 2 : ℝ) * |A_tt| * d ^ 2 + |A_tq| * d ^ 2 :=
          add_le_add (mul_le_mul_of_nonneg_left h1 (by positivity))
            (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
      _ ≤ M_2 * d ^ 2 := by
          have h1 : (1 / 2 : ℝ) * |A_tt| + |A_tq| ≤ M_2 := by
            simp only [M_2]; linarith [abs_nonneg A_tt]
          have h2 : (1 / 2 : ℝ) * |A_tt| * d ^ 2 + |A_tq| * d ^ 2 =
              ((1 / 2 : ℝ) * |A_tt| + |A_tq|) * d ^ 2 := by ring
          rw [h2]
          exact mul_le_mul_of_nonneg_right h1 (sq_nonneg d)
  -- Continuity of integrand pieces for splitting integrals
  have hcont_Pi : ∀ t ∈ Icc q_lo q_hi,
      ContinuousOn (fun r => cournotRevOf M.m inv.P t r - cournotRevOf M.m inv.P r r) (Icc q_lo q_hi) := by
    intro t ht
    have hlin1 : ContinuousOn (fun r => t + ((M.m : ℝ) - 1) * r) (Icc q_lo q_hi) :=
      continuousOn_const.add (continuousOn_const.mul continuousOn_id)
    have hmap1 : MapsTo (fun r => t + ((M.m : ℝ) - 1) * r) (Icc q_lo q_hi) (Icc 0 1) :=
      fun r hr => Ioo_subset_Icc_self (hmem_Ioo t r ht hr)
    have hlin2 : ContinuousOn (fun r => r + ((M.m : ℝ) - 1) * r) (Icc q_lo q_hi) :=
      continuousOn_id.add (continuousOn_const.mul continuousOn_id)
    have hmap2 : MapsTo (fun r => r + ((M.m : ℝ) - 1) * r) (Icc q_lo q_hi) (Icc 0 1) :=
      fun r hr => Ioo_subset_Icc_self (hmem_Ioo r r hr hr)
    exact (continuousOn_const.mul (inv.hP_cont.comp hlin1 hmap1)).sub
      (continuousOn_id.mul (inv.hP_cont.comp hlin2 hmap2))
  have hcont_W : Continuous (W_of M.n) :=
    continuous_const.mul ((continuous_const.sub continuous_id).pow (M.n - 2))
  have hcont_Q : ∀ t : ℝ, Continuous (fun r => Q t r) := by
    intro t; dsimp only [Q]; fun_prop
  -- Zero-mean cancellation identity for singleBandGain
  have hD_decomp : singleBandGain M.toMarket inv.P q_lo q_hi -
      W0 * ((∫ r in q_lo..qs, Q q_lo r) + (∫ r in qs..q_hi, Q q_hi r)) =
      (∫ r in q_lo..qs, (R q_lo r * W_of M.n r + Q q_lo r * (W_of M.n r - W0))) +
      (∫ r in qs..q_hi, (R q_hi r * W_of M.n r + Q q_hi r * (W_of M.n r - W0))) := by
    have hzm := singleBand_zero_mean M.hn hq_lt hq_hi_lt1
    have hD_def : singleBandGain M.toMarket inv.P q_lo q_hi =
        (∫ r in q_lo..qs, (cournotRevOf M.m inv.P q_lo r - cournotRevOf M.m inv.P r r) * W_of M.n r) +
        (∫ r in qs..q_hi, (cournotRevOf M.m inv.P q_hi r - cournotRevOf M.m inv.P r r) * W_of M.n r) := rfl
    have hsub1 : (∫ r in q_lo..qs, (cournotRevOf M.m inv.P q_lo r - cournotRevOf M.m inv.P r r) * W_of M.n r) -
        d_t_Pi M.m inv.P P' q_lo q_lo * (∫ r in q_lo..qs, (q_lo - r) * W_of M.n r) -
        W0 * (∫ r in q_lo..qs, Q q_lo r) =
        ∫ r in q_lo..qs, (R q_lo r * W_of M.n r + Q q_lo r * (W_of M.n r - W0)) := by
      have hi1 : IntervalIntegrable (fun r => (cournotRevOf M.m inv.P q_lo r - cournotRevOf M.m inv.P r r) * W_of M.n r) volume q_lo qs :=
        ((hcont_Pi q_lo (left_mem_Icc.mpr hq_lt.le)).mono (Icc_subset_Icc_right hqs.2.le) |>.mul
          hcont_W.continuousOn).intervalIntegrable_of_Icc hqs.1.le
      have hi2 : IntervalIntegrable (fun r => d_t_Pi M.m inv.P P' q_lo q_lo * ((q_lo - r) * W_of M.n r)) volume q_lo qs :=
        (continuous_const.mul ((continuous_const.sub continuous_id).mul hcont_W)).intervalIntegrable _ _
      have hi3 : IntervalIntegrable (fun r => W0 * Q q_lo r) volume q_lo qs :=
        (continuous_const.mul (hcont_Q q_lo)).intervalIntegrable _ _
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_sub hi1 hi2, ← intervalIntegral.integral_sub (hi1.sub hi2) hi3]
      congr 1; ext r; dsimp only [R]; ring
    have hsub2 : (∫ r in qs..q_hi, (cournotRevOf M.m inv.P q_hi r - cournotRevOf M.m inv.P r r) * W_of M.n r) -
        d_t_Pi M.m inv.P P' q_lo q_lo * (∫ r in qs..q_hi, (q_hi - r) * W_of M.n r) -
        W0 * (∫ r in qs..q_hi, Q q_hi r) =
        ∫ r in qs..q_hi, (R q_hi r * W_of M.n r + Q q_hi r * (W_of M.n r - W0)) := by
      have hi1 : IntervalIntegrable (fun r => (cournotRevOf M.m inv.P q_hi r - cournotRevOf M.m inv.P r r) * W_of M.n r) volume qs q_hi :=
        ((hcont_Pi q_hi (right_mem_Icc.mpr hq_lt.le)).mono (Icc_subset_Icc_left hqs.1.le) |>.mul
          hcont_W.continuousOn).intervalIntegrable_of_Icc hqs.2.le
      have hi2 : IntervalIntegrable (fun r => d_t_Pi M.m inv.P P' q_lo q_lo * ((q_hi - r) * W_of M.n r)) volume qs q_hi :=
        (continuous_const.mul ((continuous_const.sub continuous_id).mul hcont_W)).intervalIntegrable _ _
      have hi3 : IntervalIntegrable (fun r => W0 * Q q_hi r) volume qs q_hi :=
        (continuous_const.mul (hcont_Q q_hi)).intervalIntegrable _ _
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_sub hi1 hi2, ← intervalIntegral.integral_sub (hi1.sub hi2) hi3]
      congr 1; ext r; dsimp only [R]; ring
    rw [hD_def]
    calc (∫ r in q_lo..qs, (cournotRevOf M.m inv.P q_lo r - cournotRevOf M.m inv.P r r) * W_of M.n r) +
          (∫ r in qs..q_hi, (cournotRevOf M.m inv.P q_hi r - cournotRevOf M.m inv.P r r) * W_of M.n r) -
          W0 * ((∫ r in q_lo..qs, Q q_lo r) + (∫ r in qs..q_hi, Q q_hi r))
        = ((∫ r in q_lo..qs, (cournotRevOf M.m inv.P q_lo r - cournotRevOf M.m inv.P r r) * W_of M.n r) -
            d_t_Pi M.m inv.P P' q_lo q_lo * (∫ r in q_lo..qs, (q_lo - r) * W_of M.n r) -
            W0 * (∫ r in q_lo..qs, Q q_lo r)) +
          ((∫ r in qs..q_hi, (cournotRevOf M.m inv.P q_hi r - cournotRevOf M.m inv.P r r) * W_of M.n r) -
            d_t_Pi M.m inv.P P' q_lo q_lo * (∫ r in qs..q_hi, (q_hi - r) * W_of M.n r) -
            W0 * (∫ r in qs..q_hi, Q q_hi r)) +
          d_t_Pi M.m inv.P P' q_lo q_lo *
            ((∫ r in q_lo..qs, (q_lo - r) * W_of M.n r) + (∫ r in qs..q_hi, (q_hi - r) * W_of M.n r)) := by ring
      _ = _ := by rw [hsub1, hsub2, hzm, mul_zero, add_zero]
  -- Bound the integral remainder by 3 * η * C_W * M_2 * d^3
  have herr_pt : ∀ t r : ℝ, t ∈ Icc q_lo q_hi → r ∈ Icc q_lo q_hi →
      |R t r * W_of M.n r + Q t r * (W_of M.n r - W0)| ≤ (2 + M_2) * η * C_W * d ^ 2 := by
    intro t r ht hr
    calc |R t r * W_of M.n r + Q t r * (W_of M.n r - W0)|
        ≤ |R t r * W_of M.n r| + |Q t r * (W_of M.n r - W0)| := abs_add_le _ _
      _ = |R t r| * |W_of M.n r| + |Q t r| * |W_of M.n r - W0| := by rw [abs_mul, abs_mul]
      _ ≤ (2 * η * d ^ 2) * C_W + (M_2 * d ^ 2) * (η * C_W) :=
          add_le_add
            (mul_le_mul (hquad t r ht hr) (hW_le r hr) (abs_nonneg _)
              (mul_nonneg (mul_nonneg (by norm_num) hη_pos.le) (sq_nonneg d)))
            (mul_le_mul (hQ_bound t r ht hr) (hW_close r hr) (abs_nonneg _)
              (mul_nonneg hM2_pos.le (sq_nonneg d)))
      _ = (2 + M_2) * η * C_W * d ^ 2 := by ring
  have herr_int1 : |∫ r in q_lo..qs, (R q_lo r * W_of M.n r + Q q_lo r * (W_of M.n r - W0))| ≤
      (2 + M_2) * η * C_W * d ^ 2 * (qs - q_lo) := by
    have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (a := q_lo) (b := qs)
      (C := (2 + M_2) * η * C_W * d ^ 2) (by
        intro r hr
        rw [uIoc_of_le hqs.1.le] at hr
        rw [Real.norm_eq_abs]
        exact herr_pt q_lo r (left_mem_Icc.mpr hq_lt.le) ⟨hr.1.le, hr.2.trans hqs.2.le⟩)
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hqs.1.le)] at h1
    exact h1
  have herr_int2 : |∫ r in qs..q_hi, (R q_hi r * W_of M.n r + Q q_hi r * (W_of M.n r - W0))| ≤
      (2 + M_2) * η * C_W * d ^ 2 * (q_hi - qs) := by
    have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (a := qs) (b := q_hi)
      (C := (2 + M_2) * η * C_W * d ^ 2) (by
        intro r hr
        rw [uIoc_of_le hqs.2.le] at hr
        rw [Real.norm_eq_abs]
        exact herr_pt q_hi r (right_mem_Icc.mpr hq_lt.le) ⟨hqs.1.le.trans hr.1.le, hr.2⟩)
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hqs.2.le)] at h1
    exact h1
  have herr_tot : |singleBandGain M.toMarket inv.P q_lo q_hi -
      W0 * ((∫ r in q_lo..qs, Q q_lo r) + (∫ r in qs..q_hi, Q q_hi r))| ≤
      3 * M_2 * η * C_W * d ^ 3 := by
    rw [hD_decomp]
    calc |(∫ r in q_lo..qs, (R q_lo r * W_of M.n r + Q q_lo r * (W_of M.n r - W0))) +
          (∫ r in qs..q_hi, (R q_hi r * W_of M.n r + Q q_hi r * (W_of M.n r - W0)))|
        ≤ (2 + M_2) * η * C_W * d ^ 2 * (qs - q_lo) +
          (2 + M_2) * η * C_W * d ^ 2 * (q_hi - qs) :=
          (abs_add_le _ _).trans (add_le_add herr_int1 herr_int2)
      _ = (2 + M_2) * η * C_W * d ^ 3 := by ring
      _ ≤ 3 * M_2 * η * C_W * d ^ 3 := by
          have h1 : 2 + M_2 ≤ 3 * M_2 := by simp only [M_2]; linarith [abs_nonneg A_tt, abs_nonneg A_tq]
          have hpos : 0 ≤ η * C_W * d ^ 3 := by positivity
          calc (2 + M_2) * η * C_W * d ^ 3 = (2 + M_2) * (η * C_W * d ^ 3) := by ring
            _ ≤ (3 * M_2) * (η * C_W * d ^ 3) := mul_le_mul_of_nonneg_right h1 hpos
            _ = 3 * M_2 * η * C_W * d ^ 3 := by ring
  -- Evaluate the main quadratic integral explicitly using propC1_poly_integrals
  set s := (qs - q_lo) / d
  have hQ_eval : (∫ r in q_lo..qs, Q q_lo r) + (∫ r in qs..q_hi, Q q_hi r) =
      ((1 / 2 : ℝ) * A_tt * (2 / 3 - s) + A_tq * (1 / 6 - s ^ 2 / 2)) * d ^ 3 := by
    have hpoly := propC1_poly_integrals q_lo q_hi qs
    have hQ1 : ∫ r in q_lo..qs, Q q_lo r =
        (1 / 2 : ℝ) * A_tt * (∫ r in q_lo..qs, -((r - q_lo) ^ 2)) +
        A_tq * (∫ r in q_lo..qs, (r - q_lo) * (q_lo - r)) := by
      dsimp only [Q]
      have h1 : IntervalIntegrable (fun r => (1 / 2 : ℝ) * A_tt * ((q_lo - q_lo) ^ 2 - (r - q_lo) ^ 2)) volume q_lo qs := by
        exact (continuous_const.mul (continuous_const.sub ((continuous_id.sub continuous_const).pow 2))).intervalIntegrable _ _
      have h2 : IntervalIntegrable (fun r => A_tq * (r - q_lo) * (q_lo - r)) volume q_lo qs := by
        exact ((continuous_const.mul (continuous_id.sub continuous_const)).mul (continuous_const.sub continuous_id)).intervalIntegrable _ _
      rw [intervalIntegral.integral_add h1 h2]
      congr 1
      · rw [← intervalIntegral.integral_const_mul]; congr 1; ext r; ring
      · rw [← intervalIntegral.integral_const_mul]; congr 1; ext r; ring
    have hQ2 : ∫ r in qs..q_hi, Q q_hi r =
        (1 / 2 : ℝ) * A_tt * (∫ r in qs..q_hi, (q_hi - q_lo) ^ 2 - (r - q_lo) ^ 2) +
        A_tq * (∫ r in qs..q_hi, (r - q_lo) * (q_hi - r)) := by
      dsimp only [Q]
      have h1 : IntervalIntegrable (fun r => (1 / 2 : ℝ) * A_tt * ((q_hi - q_lo) ^ 2 - (r - q_lo) ^ 2)) volume qs q_hi := by
        exact (continuous_const.mul (continuous_const.sub ((continuous_id.sub continuous_const).pow 2))).intervalIntegrable _ _
      have h2 : IntervalIntegrable (fun r => A_tq * (r - q_lo) * (q_hi - r)) volume qs q_hi := by
        exact ((continuous_const.mul (continuous_id.sub continuous_const)).mul (continuous_const.sub continuous_id)).intervalIntegrable _ _
      rw [intervalIntegral.integral_add h1 h2]
      congr 1
      · rw [← intervalIntegral.integral_const_mul]
      · rw [← intervalIntegral.integral_const_mul]; congr 1; ext r; ring
    rw [hQ1, hQ2]
    have hcomb : (1 / 2 : ℝ) * A_tt * (∫ r in q_lo..qs, -((r - q_lo) ^ 2)) +
        A_tq * (∫ r in q_lo..qs, (r - q_lo) * (q_lo - r)) +
        ((1 / 2 : ℝ) * A_tt * (∫ r in qs..q_hi, (q_hi - q_lo) ^ 2 - (r - q_lo) ^ 2) +
        A_tq * (∫ r in qs..q_hi, (r - q_lo) * (q_hi - r))) =
        (1 / 2 : ℝ) * A_tt * ((∫ r in q_lo..qs, -((r - q_lo) ^ 2)) +
          (∫ r in qs..q_hi, (q_hi - q_lo) ^ 2 - (r - q_lo) ^ 2)) +
        A_tq * ((∫ r in q_lo..qs, (r - q_lo) * (q_lo - r)) +
          (∫ r in qs..q_hi, (r - q_lo) * (q_hi - r))) := by ring
    rw [hcomb, hpoly.1, hpoly.2]
    have hs_eq : qs - q_lo = s * d := (div_mul_cancel₀ _ hd_pos.ne').symm
    have hqs_hi : q_hi - qs = (1 - s) * d := by
      calc q_hi - qs = (q_hi - q_lo) - (qs - q_lo) := by ring
        _ = d - s * d := by rw [hs_eq]
        _ = (1 - s) * d := by ring
    have hd_def : q_hi - q_lo = d := rfl
    rw [hd_def, hs_eq, hqs_hi]
    ring
  -- Bound |s - 1/2| ≤ η / 2 using qStar_ratio_sandwich
  have hs_close : |s - 1 / 2| ≤ η / 2 := by
    have hsw := qStar_ratio_sandwich M.hn hq_lt hq_hi_lt1
    have h1q_hi_lb : (1 - q) / 2 ≤ 1 - q_hi := by
      have h1 : |q_hi - q| < (1 - q) / 4 := lt_of_lt_of_le hhi (hδ_le_δpow.trans (min_le_left _ _))
      linarith [(abs_lt.mp h1).2]
    have h1q_lo_lb : (1 - q) / 2 ≤ 1 - q_lo := by linarith
    have hd_lt : d < (1 - q) * δ₄ / 4 := by
      have h1 : |q_lo - q| < (1 - q) * δ₄ / 8 := lt_of_lt_of_le hlo (hδ_le_δpow.trans (min_le_right _ _))
      have h2 : |q_hi - q| < (1 - q) * δ₄ / 8 := lt_of_lt_of_le hhi (hδ_le_δpow.trans (min_le_right _ _))
      linarith [(abs_lt.mp h1).1, (abs_lt.mp h2).2]
    have hr1_dist : |(1 - q_hi) / (1 - q_lo) - 1| < δ₄ := by
      have heq : (1 - q_hi) / (1 - q_lo) - 1 = -d / (1 - q_lo) := by
        have : (1 - q_lo : ℝ) ≠ 0 := by linarith
        field_simp; ring
      rw [heq, abs_div, abs_neg, abs_of_pos hd_pos, abs_of_pos (by linarith : 0 < 1 - q_lo),
        div_lt_iff₀ (by linarith : 0 < 1 - q_lo)]
      calc d < (1 - q) * δ₄ / 4 := hd_lt
        _ < δ₄ * ((1 - q) / 2) := by
            have : 0 < (1 - q) * δ₄ := mul_pos (by linarith) hδ₄_pos
            linarith
        _ ≤ δ₄ * (1 - q_lo) := mul_le_mul_of_nonneg_left h1q_lo_lb hδ₄_pos.le
    have hr2_dist : |(1 - q_lo) / (1 - q_hi) - 1| < δ₄ := by
      have heq : (1 - q_lo) / (1 - q_hi) - 1 = d / (1 - q_hi) := by
        have : (1 - q_hi : ℝ) ≠ 0 := by linarith
        field_simp; ring
      rw [heq, abs_div, abs_of_pos hd_pos, abs_of_pos (by linarith : 0 < 1 - q_hi),
        div_lt_iff₀ (by linarith : 0 < 1 - q_hi)]
      calc d < (1 - q) * δ₄ / 4 := hd_lt
        _ < δ₄ * ((1 - q) / 2) := by
            have : 0 < (1 - q) * δ₄ := mul_pos (by linarith) hδ₄_pos
            linarith
        _ ≤ δ₄ * (1 - q_hi) := mul_le_mul_of_nonneg_left h1q_hi_lb hδ₄_pos.le
    have hp1 := hδ₄ (by simpa [Real.dist_eq] using hr1_dist)
    have hp2 := hδ₄ (by simpa [Real.dist_eq] using hr2_dist)
    simp only [Real.dist_eq, one_pow] at hp1 hp2
    rw [abs_le]
    constructor
    · linarith [hsw.1, (abs_lt.mp hp1).1]
    · linarith [hsw.2, (abs_lt.mp hp2).2]
  have hs_mem : s ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact div_pos (by linarith [hqs.1]) hd_pos
    · rw [div_lt_one hd_pos]; linarith [hqs.2]
  -- Compare W0 * Q_eval with coeff * (1 - q_lo)^(n - 2) * d^3
  have hmain_diff : |W0 * ((∫ r in q_lo..qs, Q q_lo r) + (∫ r in qs..q_hi, Q q_hi r)) -
      coeff * (1 - q_lo) ^ (M.n - 2) * d ^ 3| ≤ M_2 * η * C_W * d ^ 3 := by
    rw [hQ_eval]
    have hcoeff_eq : coeff * (1 - q_lo) ^ (M.n - 2) * d ^ 3 =
        W0 * ((1 / 2 : ℝ) * A_tt * (2 / 3 - 1 / 2) + A_tq * (1 / 6 - (1 / 2) ^ 2 / 2)) * d ^ 3 := by
      simp only [coeff, W0, W_of, A_tt, A_tq]
      ring
    rw [hcoeff_eq]
    have hfact : W0 * (((1 / 2 : ℝ) * A_tt * (2 / 3 - s) + A_tq * (1 / 6 - s ^ 2 / 2)) * d ^ 3) -
        W0 * ((1 / 2 : ℝ) * A_tt * (2 / 3 - 1 / 2) + A_tq * (1 / 6 - (1 / 2) ^ 2 / 2)) * d ^ 3 =
        W0 * (-(1 / 2 : ℝ) * A_tt * (s - 1 / 2) - (1 / 2 : ℝ) * A_tq * (s + 1 / 2) * (s - 1 / 2)) * d ^ 3 := by
      ring
    rw [hfact, abs_mul, abs_mul, abs_of_pos (pow_pos hd_pos 3)]
    have hW0_le : |W0| ≤ C_W := hW_le q_lo (left_mem_Icc.mpr hq_lt.le)
    have hbr : |-(1 / 2 : ℝ) * A_tt * (s - 1 / 2) - (1 / 2 : ℝ) * A_tq * (s + 1 / 2) * (s - 1 / 2)| ≤
        M_2 * η := by
      have hs12 : |s + 1 / 2| ≤ 2 := by rw [abs_le]; constructor <;> linarith [hs_mem.1, hs_mem.2]
      calc |-(1 / 2 : ℝ) * A_tt * (s - 1 / 2) - (1 / 2 : ℝ) * A_tq * (s + 1 / 2) * (s - 1 / 2)|
          ≤ |-(1 / 2 : ℝ) * A_tt * (s - 1 / 2)| + |(1 / 2 : ℝ) * A_tq * (s + 1 / 2) * (s - 1 / 2)| :=
            abs_sub _ _
        _ = (1 / 2 : ℝ) * |A_tt| * |s - 1 / 2| +
            (1 / 2 : ℝ) * |A_tq| * |s + 1 / 2| * |s - 1 / 2| := by
            simp only [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        _ ≤ (1 / 2 : ℝ) * |A_tt| * (η / 2) + (1 / 2 : ℝ) * |A_tq| * 2 * (η / 2) := by
            refine add_le_add (mul_le_mul_of_nonneg_left hs_close (by positivity)) ?_
            exact mul_le_mul (mul_le_mul_of_nonneg_left hs12 (by positivity)) hs_close
              (abs_nonneg _) (by positivity)
        _ ≤ M_2 * η := by
            have hsum : (1 / 2 : ℝ) * |A_tt| * (η / 2) + (1 / 2 : ℝ) * |A_tq| * 2 * (η / 2) =
                ((1 / 4 : ℝ) * |A_tt| + (1 / 2 : ℝ) * |A_tq|) * η := by ring
            rw [hsum]
            have hle : (1 / 4 : ℝ) * |A_tt| + (1 / 2 : ℝ) * |A_tq| ≤ M_2 := by
              simp only [M_2]; linarith [abs_nonneg A_tt, abs_nonneg A_tq]
            exact mul_le_mul_of_nonneg_right hle hη_pos.le
    calc |W0| * |-(1 / 2 : ℝ) * A_tt * (s - 1 / 2) - (1 / 2 : ℝ) * A_tq * (s + 1 / 2) * (s - 1 / 2)| * d ^ 3
        ≤ C_W * (M_2 * η) * d ^ 3 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hW0_le hbr (abs_nonneg _) hCW_pos.le) (pow_nonneg hd_pos.le 3)
      _ = M_2 * η * C_W * d ^ 3 := by ring
  -- Combine both errors
  calc |singleBandGain M.toMarket inv.P q_lo q_hi - coeff * (1 - q_lo) ^ (M.n - 2) * d ^ 3|
      = |(singleBandGain M.toMarket inv.P q_lo q_hi -
            W0 * ((∫ r in q_lo..qs, Q q_lo r) + (∫ r in qs..q_hi, Q q_hi r))) +
          (W0 * ((∫ r in q_lo..qs, Q q_lo r) + (∫ r in qs..q_hi, Q q_hi r)) -
            coeff * (1 - q_lo) ^ (M.n - 2) * d ^ 3)| := by ring_nf
    _ ≤ 3 * M_2 * η * C_W * d ^ 3 + M_2 * η * C_W * d ^ 3 :=
        (abs_add_le _ _).trans (add_le_add herr_tot hmain_diff)
    _ = (4 * C_W * M_2 * η) * d ^ 3 := by ring
    _ ≤ ε * d ^ 3 := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hd_pos.le 3)
        have hη_le : η ≤ ε / (10 * C_W * M_2 + 1) := min_le_right _ _
        have hden : 0 < 10 * C_W * M_2 + 1 := by positivity
        have h1 : η * (10 * C_W * M_2 + 1) ≤ ε := (le_div_iff₀ hden).mp hη_le
        have h2 : 4 * C_W * M_2 ≤ 10 * C_W * M_2 + 1 := by
          have := mul_pos hCW_pos hM2_pos; linarith
        calc 4 * C_W * M_2 * η ≤ (10 * C_W * M_2 + 1) * η :=
              mul_le_mul_of_nonneg_right h2 hη_pos.le
          _ = η * (10 * C_W * M_2 + 1) := mul_comm _ _
          _ ≤ ε := h1

/-- **Proposition C.1 (narrow pool induces narrow interior band)**:
For a single pool `(α, β) ⊂ (max ρ a, 1)` with `η_p := F(β) - F(α) < min((1 - F(β))/m, (F(α) - F(v_lo))/m)`,
any maximal non-uniform interval `[v₁, v₄] ⊆ [v_lo, 1]` containing `(α, β)` of an SR continuation
under `r₁ = ρ` (characterized by its induced `F₁, F_riv, σ` satisfying the sub-interval properties
of Lemma A.5) must be strictly interior (`v_lo < v₁ < v₄ < 1`) with band width
`d = (F(v₄) - F(v₁)) / m ≤ F(β) - F(α)`. -/
theorem propC1_narrow_pool_induces_interior_band (M : Market)
    {ρ α β v₁ v₄ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hvlo_α : max ρ M.a < α) (hαβ : α < β) (hβ1 : β < 1)
    (hv1_lo : max ρ M.a ≤ v₁) (hv1_α : v₁ ≤ α) (hβ_v4 : β ≤ v₄) (hv4_1 : v₄ ≤ 1)
    (hη1 : M.F β - M.F α < (1 - M.F β) / (M.m : ℝ))
    (hη2 : M.F β - M.F α < (M.F α - M.F (max ρ M.a)) / (M.m : ℝ))
    (F₁ F_riv σ : ℝ → ℝ)
    -- Effective distribution and surplus-gap properties of the SR continuation on [v₁, v₄]
    (hF1_mono : MonotoneOn F₁ (Icc v₁ v₄))
    (hF1_const_lo : ∀ u ∈ Icc v₁ α, F₁ u = F₁ α)
    (hF1_const_hi : ∀ u ∈ Icc β v₄, F₁ u = F₁ β)
    (hF1_step : F₁ β - F₁ α ≤ M.F β - M.F α)
    (hF1_top : v₄ = 1 → F₁ 1 = 1)
    (hF1_v4 : v₄ < 1 → F₁ v₄ = M.A v₄)
    (hF1_v1 : max ρ M.a < v₁ → F₁ v₁ = M.A v₁)
    (hadd : ∀ u ∈ Icc v₁ v₄, F₁ u + ((M.m : ℝ) - 1) * F_riv u = (M.m : ℝ) * M.A u)
    (hFriv_cont : ContinuousOn F_riv (Icc v₁ v₄))
    (hσ_nonpos : ∀ u ∈ Icc v₁ v₄, σ u ≤ 0)
    (hσ_v1 : σ v₁ = 0)
    (hσ_int : ∀ u ∈ Icc v₁ v₄, σ u - σ v₁ =
      ∫ t in v₁..u, (alloc M ⟨ρ, hρ0, hρ1.le, [⟨α, β, hαβ⟩],
        by intro I hI; simp only [List.mem_singleton] at hI; subst hI
           exact ⟨(le_max_left ρ M.a).trans hvlo_α.le, hβ1.le⟩,
        List.pairwise_singleton _ _⟩ F₁ t - (F_riv t) ^ (M.n - 1))) :
    max ρ M.a < v₁ ∧ v₄ < 1 ∧ (M.F v₄ - M.F v₁) / (M.m : ℝ) ≤ M.F β - M.F α := by
  set v_lo := max ρ M.a
  set η_p := M.F β - M.F α
  set mech : HierarchicalMech := ⟨ρ, hρ0, hρ1.le, [⟨α, β, hαβ⟩],
    by intro I hI; simp only [List.mem_singleton] at hI; subst hI
       exact ⟨(le_max_left ρ M.a).trans hvlo_α.le, hβ1.le⟩,
    List.pairwise_singleton _ _⟩
  have hmpos : (0 : ℝ) < M.m := M.m_pos_real
  have hm1pos : (0 : ℝ) < (M.m : ℝ) - 1 := M.m_sub_one_pos_real
  have ha_vlo : M.a ≤ v_lo := le_max_right ρ M.a
  have hρ_vlo : ρ ≤ v_lo := le_max_left ρ M.a
  have hv1_lt_v4 : v₁ < v₄ := lt_of_le_of_lt hv1_α (hαβ.trans_le hβ_v4)
  -- Helper: evaluate alloc M mech F₁ t for t ≥ ρ
  have halloc_lo : ∀ t ∈ Icc v₁ α, alloc M mech F₁ t = (F₁ α) ^ (M.n - 1) := by
    intro t ht
    have htρ : ¬ (t < ρ) := not_lt.mpr (hρ_vlo.trans (hv1_lo.trans ht.1))
    unfold alloc
    simp only [mech, htρ, ↓reduceIte, List.find?_cons, List.find?_nil]
    have hnot : ¬ (α < t ∧ t < β) := fun h => by linarith [ht.2, h.1]
    simp only [hnot, decide_false, hF1_const_lo t ht]
  have halloc_mid : ∀ t ∈ Ioo α β, alloc M mech F₁ t = poolAvg M.n (F₁ α) (F₁ β) := by
    intro t ht
    have htρ : ¬ (t < ρ) := not_lt.mpr (hρ_vlo.trans (hvlo_α.le.trans ht.1.le))
    unfold alloc
    simp only [mech, htρ, ↓reduceIte, List.find?_cons]
    have hcond : α < t ∧ t < β := ht
    simp [hcond]
  have halloc_hi : ∀ t ∈ Icc β v₄, alloc M mech F₁ t = (F₁ β) ^ (M.n - 1) := by
    intro t ht
    have htρ : ¬ (t < ρ) := not_lt.mpr (hρ_vlo.trans (hvlo_α.le.trans (hαβ.le.trans ht.1)))
    unfold alloc
    simp only [mech, htρ, ↓reduceIte, List.find?_cons, List.find?_nil]
    have hnot : ¬ (α < t ∧ t < β) := fun h => by linarith [ht.1, h.2]
    simp only [hnot, decide_false, hF1_const_hi t ht]
  -- Helper: express F_riv u from hadd
  have hFriv_eq : ∀ u ∈ Icc v₁ v₄, F_riv u = 1 - (F₁ u - M.F u) / ((M.m : ℝ) - 1) := by
    intro u hu
    have h := hadd u hu
    unfold Market.A at h
    have hm1ne : (M.m : ℝ) - 1 ≠ 0 := hm1pos.ne'
    have hmne : (M.m : ℝ) ≠ 0 := hmpos.ne'
    field_simp at h ⊢
    linarith
  -- Step 1: Rule out v₄ = 1
  have hv4_lt1 : v₄ < 1 := by
    by_contra h
    have hv4_eq : v₄ = 1 := le_antisymm hv4_1 (not_lt.mp h)
    have hF1_β : F₁ β = 1 := by
      have := hF1_const_hi 1 ⟨hβ_v4.trans hv4_eq.le, hv4_eq.ge⟩
      rw [hF1_top hv4_eq] at this
      exact this.symm
    have hF1_α_ge : 1 - η_p ≤ F₁ α := by linarith [hF1_step, hF1_β]
    have hFβ_lt1 : M.F β < 1 := by
      rw [← M.hF_1]
      exact M.F_strictMonoOn ⟨ha_vlo.trans (hvlo_α.le.trans hαβ.le), hβ1.le⟩ (right_mem_Icc.mpr M.ha1.le) hβ1
    have hη_pos : 0 < η_p := by
      have := M.F_strictMonoOn ⟨ha_vlo.trans hvlo_α.le, (hαβ.trans hβ1).le⟩
        ⟨ha_vlo.trans (hvlo_α.le.trans hαβ.le), hβ1.le⟩ hαβ
      linarith
    have h1η_pos : 0 < 1 - η_p := by
      have : η_p * (M.m : ℝ) < 1 - M.F β := (lt_div_iff₀ hmpos).mp hη1
      have hm2 : (2 : ℝ) ≤ M.m := by exact_mod_cast M.hm
      have hFβ_ge0 : 0 ≤ M.F β := (M.F_mem_Icc ⟨ha_vlo.trans (hvlo_α.le.trans hαβ.le), hβ1.le⟩).1
      nlinarith
    -- On [v₁, β], F_riv u < 1 - η_p ≤ F₁ α
    have hFriv_lt_on_lo : ∀ u ∈ Icc v₁ β, F_riv u < 1 - η_p := by
      intro u hu
      have hu_in : u ∈ Icc v₁ v₄ := ⟨hu.1, hu.2.trans hβ_v4⟩
      rw [hFriv_eq u hu_in]
      have hF1u : 1 - η_p ≤ F₁ u := by
        have := hF1_mono (left_mem_Icc.mpr hv1_lt_v4.le) hu_in hu.1
        rw [hF1_const_lo v₁ (left_mem_Icc.mpr hv1_α)] at this
        linarith
      have hFu : M.F u ≤ M.F β := M.F_strictMonoOn.monotoneOn
        ⟨ha_vlo.trans (hv1_lo.trans hu.1), (hu.2.trans hβ1.le)⟩
        ⟨ha_vlo.trans (hvlo_α.le.trans hαβ.le), hβ1.le⟩ hu.2
      have hkey : η_p * (M.m : ℝ) < 1 - M.F β := (lt_div_iff₀ hmpos).mp hη1
      have hdiv : η_p < (1 - η_p - M.F β) / ((M.m : ℝ) - 1) := by
        rw [lt_div_iff₀ hm1pos]; linarith
      have hdiv2 : (1 - η_p - M.F β) / ((M.m : ℝ) - 1) ≤ (F₁ u - M.F u) / ((M.m : ℝ) - 1) :=
        div_le_div_of_nonneg_right (by linarith) hm1pos.le
      linarith
    have hFriv_nonneg : ∀ u ∈ Icc v₁ v₄, 0 ≤ F_riv u := by
      intro u hu
      rw [hFriv_eq u hu]
      have hF1u : F₁ u ≤ 1 := by
        have := hF1_mono hu (right_mem_Icc.mpr hv1_lt_v4.le) hu.2
        rw [hv4_eq, hF1_top hv4_eq] at this; exact this
      have hFu : 0 ≤ M.F u := (M.F_mem_Icc ⟨ha_vlo.trans (hv1_lo.trans hu.1), hu.2.trans hv4_1⟩).1
      have hm1ge1 : (1 : ℝ) ≤ (M.m : ℝ) - 1 := by
        have : (2 : ℝ) ≤ M.m := by exact_mod_cast M.hm
        linarith
      have : (F₁ u - M.F u) / ((M.m : ℝ) - 1) ≤ 1 := by
        rw [div_le_one hm1pos]; linarith
      linarith
    have hpool_ge : (1 - η_p) ^ (M.n - 1) ≤ poolAvg M.n (F₁ α) (F₁ β) := by
      by_cases heq : F₁ α = F₁ β
      · unfold poolAvg; simp only [heq, ↓reduceIte]; rw [← heq]; exact pow_le_pow_left₀ h1η_pos.le hF1_α_ge _
      · have hlt : F₁ α < F₁ β := lt_of_le_of_ne (hF1_mono ⟨hv1_α, hαβ.le.trans hβ_v4⟩ ⟨hv1_α.trans hαβ.le, hβ_v4⟩ hαβ.le) heq
        have hb := (sh_poolAvg_bounds M.hn (lt_of_lt_of_le h1η_pos hF1_α_ge) hlt).1
        exact (pow_le_pow_left₀ h1η_pos.le hF1_α_ge _).trans hb.le
    -- Nonnegativity of integrand on [v₁, 1] and strict positivity on (α, β)
    have hnonneg : ∀ t ∈ Icc v₁ v₄, 0 ≤ alloc M mech F₁ t - (F_riv t) ^ (M.n - 1) := by
      intro t ht
      have hFr0 := hFriv_nonneg t ht
      by_cases htα : t ≤ α
      · rw [halloc_lo t ⟨ht.1, htα⟩]
        have hlt := (hFriv_lt_on_lo t ⟨ht.1, htα.trans hαβ.le⟩).le.trans hF1_α_ge
        linarith [pow_le_pow_left₀ hFr0 hlt (M.n - 1)]
      · by_cases htβ : t < β
        · rw [halloc_mid t ⟨not_le.mp htα, htβ⟩]
          have hlt := (hFriv_lt_on_lo t ⟨ht.1, htβ.le⟩).le
          linarith [pow_le_pow_left₀ hFr0 hlt (M.n - 1), hpool_ge]
        · rw [halloc_hi t ⟨not_lt.mp htβ, ht.2⟩, hF1_β, one_pow]
          have hFr1 : F_riv t ≤ 1 := by
            rw [hFriv_eq t ht, hF1_const_hi t ⟨not_lt.mp htβ, ht.2⟩, hF1_β]
            have hFt : M.F t ≤ 1 := (M.F_mem_Icc ⟨ha_vlo.trans (hv1_lo.trans ht.1), ht.2.trans hv4_1⟩).2
            have : 0 ≤ (1 - M.F t) / ((M.m : ℝ) - 1) := div_nonneg (by linarith) hm1pos.le
            linarith
          linarith [pow_le_one₀ hFr0 hFr1 (n := M.n - 1)]
    -- Strict positive lower bound on (α, β)
    have hcomp : IsCompact (Icc α β) := isCompact_Icc
    obtain ⟨u_max, hu_max_mem, hu_max⟩ := hcomp.exists_isMaxOn (nonempty_Icc.mpr hαβ.le)
      (hFriv_cont.mono (Icc_subset_Icc hv1_α hβ_v4))
    have hmax_lt : F_riv u_max < 1 - η_p := hFriv_lt_on_lo u_max ⟨hv1_α.trans hu_max_mem.1, hu_max_mem.2⟩
    set c_gap : ℝ := (1 - η_p) ^ (M.n - 1) - (F_riv u_max) ^ (M.n - 1)
    have hc_pos : 0 < c_gap := by
      have hFr0 := hFriv_nonneg u_max ⟨hv1_α.trans hu_max_mem.1, hu_max_mem.2.trans hβ_v4⟩
      have := pow_lt_pow_left₀ hmax_lt hFr0 (by have := M.hn; omega : M.n - 1 ≠ 0)
      linarith
    -- Split integral ∫_{v₁}^{v₄} into [v₁, α], [α, β], [β, v₄]
    have hint_lo : IntervalIntegrable (fun t => alloc M mech F₁ t - (F_riv t) ^ (M.n - 1)) volume v₁ α := by
      have heq : EqOn (fun t => alloc M mech F₁ t - (F_riv t) ^ (M.n - 1))
          (fun t => (F₁ α) ^ (M.n - 1) - (F_riv t) ^ (M.n - 1)) (Icc v₁ α) :=
        fun t ht => by dsimp only; rw [halloc_lo t ht]
      exact (ContinuousOn.intervalIntegrable_of_Icc hv1_α
        (continuousOn_const.sub ((hFriv_cont.mono (Icc_subset_Icc_right (hαβ.le.trans hβ_v4))).pow (M.n - 1)))).congr
          (fun t ht => (heq (Ioc_subset_Icc_self (uIoc_of_le hv1_α ▸ ht))).symm)
    have hint_mid : IntervalIntegrable (fun t => alloc M mech F₁ t - (F_riv t) ^ (M.n - 1)) volume α β := by
      have hcont : IntervalIntegrable (fun t => poolAvg M.n (F₁ α) (F₁ β) - (F_riv t) ^ (M.n - 1)) volume α β :=
        ContinuousOn.intervalIntegrable_of_Icc hαβ.le
          (continuousOn_const.sub ((hFriv_cont.mono (Icc_subset_Icc hv1_α hβ_v4)).pow (M.n - 1)))
      refine hcont.congr_ae ?_
      have hdiff : ∀ t ∈ Ioo α β, poolAvg M.n (F₁ α) (F₁ β) - (F_riv t) ^ (M.n - 1) =
          alloc M mech F₁ t - (F_riv t) ^ (M.n - 1) :=
        fun t ht => by rw [halloc_mid t ht]
      filter_upwards [ae_restrict_mem measurableSet_uIoc,
        ae_restrict_of_ae (show ∀ᵐ t ∂volume, t ≠ β from by simp [ae_iff])] with t ht hne
      rw [uIoc_of_le hαβ.le] at ht
      exact hdiff t ⟨ht.1, lt_of_le_of_ne ht.2 hne⟩
    have hint_hi : IntervalIntegrable (fun t => alloc M mech F₁ t - (F_riv t) ^ (M.n - 1)) volume β v₄ := by
      have heq : EqOn (fun t => alloc M mech F₁ t - (F_riv t) ^ (M.n - 1))
          (fun t => (F₁ β) ^ (M.n - 1) - (F_riv t) ^ (M.n - 1)) (Icc β v₄) :=
        fun t ht => by dsimp only; rw [halloc_hi t ht]
      exact (ContinuousOn.intervalIntegrable_of_Icc hβ_v4
        (continuousOn_const.sub ((hFriv_cont.mono (Icc_subset_Icc_left (hv1_α.trans hαβ.le))).pow (M.n - 1)))).congr
          (fun t ht => (heq (Ioc_subset_Icc_self (uIoc_of_le hβ_v4 ▸ ht))).symm)
    have hsplit : σ v₄ - σ v₁ =
        (∫ t in v₁..α, (alloc M mech F₁ t - (F_riv t) ^ (M.n - 1))) +
        (∫ t in α..β, (alloc M mech F₁ t - (F_riv t) ^ (M.n - 1))) +
        (∫ t in β..v₄, (alloc M mech F₁ t - (F_riv t) ^ (M.n - 1))) := by
      rw [hσ_int v₄ (right_mem_Icc.mpr hv1_lt_v4.le),
        intervalIntegral.integral_add_adjacent_intervals hint_lo hint_mid,
        intervalIntegral.integral_add_adjacent_intervals (hint_lo.trans hint_mid) hint_hi]
    have hI1 : 0 ≤ ∫ t in v₁..α, (alloc M mech F₁ t - (F_riv t) ^ (M.n - 1)) :=
      intervalIntegral.integral_nonneg hv1_α (fun t ht => hnonneg t ⟨ht.1, ht.2.trans (hαβ.le.trans hβ_v4)⟩)
    have hI3 : 0 ≤ ∫ t in β..v₄, (alloc M mech F₁ t - (F_riv t) ^ (M.n - 1)) :=
      intervalIntegral.integral_nonneg hβ_v4 (fun t ht => hnonneg t ⟨(hv1_α.trans hαβ.le).trans ht.1, ht.2⟩)
    have hI2 : c_gap * (β - α) ≤ ∫ t in α..β, (alloc M mech F₁ t - (F_riv t) ^ (M.n - 1)) := by
      have hconst : ∫ _t in α..β, c_gap = c_gap * (β - α) := by
        rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
      rw [← hconst]
      refine intervalIntegral.integral_mono_ae_restrict hαβ.le
        (continuous_const.intervalIntegrable α β) hint_mid ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc,
        ae_restrict_of_ae (show ∀ᵐ t ∂volume, t ≠ α from by simp [ae_iff]),
        ae_restrict_of_ae (show ∀ᵐ t ∂volume, t ≠ β from by simp [ae_iff])] with t ht hneα hneβ
      have ht_oo : t ∈ Ioo α β := ⟨lt_of_le_of_ne ht.1 hneα.symm, lt_of_le_of_ne ht.2 hneβ⟩
      rw [halloc_mid t ht_oo]
      have hFr0 := hFriv_nonneg t ⟨hv1_α.trans ht.1, ht.2.trans hβ_v4⟩
      have hle_max : F_riv t ≤ F_riv u_max := hu_max ht
      have hpow_le := pow_le_pow_left₀ hFr0 hle_max (M.n - 1)
      linarith [hpool_ge]
    have hσv4_pos : 0 < σ v₄ := by
      have : 0 < c_gap * (β - α) := mul_pos hc_pos (by linarith)
      linarith [hsplit, hσ_v1, hI1, hI2, hI3]
    linarith [hσ_nonpos v₄ (right_mem_Icc.mpr hv1_lt_v4.le)]
  -- Step 2: Rule out v₁ = v_lo
  have hv1_gt : v_lo < v₁ := by
    by_contra h
    have hv1_eq : v₁ = v_lo := le_antisymm (not_lt.mp h) hv1_lo
    have hF1_v4_eq : F₁ v₄ = M.A v₄ := hF1_v4 hv4_lt1
    have hF1_β_eq : F₁ β = M.A v₄ := by
      rw [← hF1_v4_eq]
      exact (hF1_const_hi v₄ (right_mem_Icc.mpr hβ_v4)).symm
    have hAv4_ge : M.A β ≤ M.A v₄ := by
      unfold Market.A
      have hFβv4 : M.F β ≤ M.F v₄ := M.F_strictMonoOn.monotoneOn
        ⟨ha_vlo.trans (hvlo_α.le.trans hαβ.le), hβ1.le⟩
        ⟨ha_vlo.trans (hvlo_α.le.trans (hαβ.le.trans hβ_v4)), hv4_1⟩ hβ_v4
      linarith [div_le_div_of_nonneg_right (show 1 - M.F v₄ ≤ 1 - M.F β by linarith) hmpos.le]
    have hAβ_gap : η_p < M.A β - M.A v_lo := by
      unfold Market.A
      have heq : (1 - (1 - M.F β) / (M.m : ℝ)) - (1 - (1 - M.F v_lo) / (M.m : ℝ)) =
          (M.F β - M.F v_lo) / (M.m : ℝ) := by ring
      rw [heq]
      have hFαβ : M.F α < M.F β := M.F_strictMonoOn
        ⟨ha_vlo.trans hvlo_α.le, (hαβ.trans hβ1).le⟩
        ⟨ha_vlo.trans (hvlo_α.le.trans hαβ.le), hβ1.le⟩ hαβ
      have hmono : (M.F α - M.F v_lo) / (M.m : ℝ) < (M.F β - M.F v_lo) / (M.m : ℝ) :=
        div_lt_div_of_pos_right (by linarith) hmpos
      exact hη2.trans hmono
    have hF1_α_gt : M.A v_lo < F₁ α := by linarith [hF1_step, hF1_β_eq, hAv4_ge, hAβ_gap]
    have hF1_v1_eq : F₁ v₁ = F₁ α := hF1_const_lo v₁ (left_mem_Icc.mpr hv1_α)
    have hFriv_lt : F_riv v₁ < F₁ α := by
      have ha := hadd v₁ (left_mem_Icc.mpr hv1_lt_v4.le)
      rw [hF1_v1_eq, hv1_eq] at ha
      rw [hv1_eq]
      nlinarith [hm1pos, hF1_α_gt]
    have hFriv_nonneg_lo : ∀ u ∈ Icc v₁ α, 0 ≤ F_riv u := by
      intro u hu
      have hu_in : u ∈ Icc v₁ v₄ := ⟨hu.1, hu.2.trans (hαβ.le.trans hβ_v4)⟩
      rw [hFriv_eq u hu_in, hF1_const_lo u hu]
      have hF1α_le1 : F₁ α ≤ 1 := by
        have hF1v4_le1 : M.A v₄ ≤ 1 := by
          unfold Market.A
          have h1 : M.F v₄ ≤ 1 := (M.F_mem_Icc ⟨ha_vlo.trans (hvlo_α.le.trans (hαβ.le.trans hβ_v4)), hv4_1⟩).2
          linarith [div_nonneg (show 0 ≤ 1 - M.F v₄ by linarith) hmpos.le]
        have := hF1_mono ⟨hv1_α, hαβ.le.trans hβ_v4⟩ (right_mem_Icc.mpr hv1_lt_v4.le) (hαβ.le.trans hβ_v4)
        linarith
      have hFu : 0 ≤ M.F u := (M.F_mem_Icc ⟨ha_vlo.trans (hv1_lo.trans hu.1), hu.2.trans (hαβ.trans hβ1).le⟩).1
      have : (F₁ α - M.F u) / ((M.m : ℝ) - 1) ≤ 1 := by
        rw [div_le_one hm1pos]
        have : (2 : ℝ) ≤ M.m := by exact_mod_cast M.hm
        linarith
      linarith
    -- By continuity of F_riv at v₁ within [v₁, v₄], there exists u ∈ (v₁, α] with F_riv < F₁ α on [v₁, u]
    have hcont_at : ContinuousWithinAt F_riv (Icc v₁ v₄) v₁ :=
      hFriv_cont v₁ (left_mem_Icc.mpr hv1_lt_v4.le)
    set mid := (F_riv v₁ + F₁ α) / 2
    have hmid_gt : F_riv v₁ < mid := by simp only [mid]; linarith
    have hmid_lt : mid < F₁ α := by simp only [mid]; linarith
    have hmem_nhds : Iio mid ∈ 𝓝 (F_riv v₁) := Iio_mem_nhds hmid_gt
    have hev := hcont_at.preimage_mem_nhdsWithin hmem_nhds
    rw [Metric.mem_nhdsWithin_iff] at hev
    obtain ⟨δ, hδ_pos, hδ⟩ := hev
    set u := min α (v₁ + δ / 2)
    have hv1_lt_α : v₁ < α := by rw [hv1_eq]; exact hvlo_α
    have hv1_lt_u : v₁ < u := lt_min hv1_lt_α (by linarith)
    have hu_le_α : u ≤ α := min_le_left _ _
    have hu_in : u ∈ Icc v₁ v₄ := ⟨hv1_lt_u.le, hu_le_α.trans (hαβ.le.trans hβ_v4)⟩
    have hgap_pos : 0 < (F₁ α) ^ (M.n - 1) - mid ^ (M.n - 1) := by
      have hmid0 : 0 ≤ mid := by linarith [hFriv_nonneg_lo v₁ (left_mem_Icc.mpr hv1_α), hmid_gt]
      have := pow_lt_pow_left₀ hmid_lt hmid0 (by have := M.hn; omega : M.n - 1 ≠ 0)
      linarith
    have hint_u : IntervalIntegrable (fun t => alloc M mech F₁ t - (F_riv t) ^ (M.n - 1)) volume v₁ u := by
      have heq : EqOn (fun t => alloc M mech F₁ t - (F_riv t) ^ (M.n - 1))
          (fun t => (F₁ α) ^ (M.n - 1) - (F_riv t) ^ (M.n - 1)) (Icc v₁ u) :=
        fun t ht => by dsimp only; rw [halloc_lo t ⟨ht.1, ht.2.trans hu_le_α⟩]
      exact (ContinuousOn.intervalIntegrable_of_Icc hv1_lt_u.le
        (continuousOn_const.sub ((hFriv_cont.mono (Icc_subset_Icc_right (hu_le_α.trans (hαβ.le.trans hβ_v4)))).pow (M.n - 1)))).congr
          (fun t ht => (heq (Ioc_subset_Icc_self (uIoc_of_le hv1_lt_u.le ▸ ht))).symm)
    have hσu_ge : ((F₁ α) ^ (M.n - 1) - mid ^ (M.n - 1)) * (u - v₁) ≤ σ u - σ v₁ := by
      rw [hσ_int u hu_in]
      have hconst : ∫ _t in v₁..u, ((F₁ α) ^ (M.n - 1) - mid ^ (M.n - 1)) =
          ((F₁ α) ^ (M.n - 1) - mid ^ (M.n - 1)) * (u - v₁) := by
        rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
      rw [← hconst]
      refine intervalIntegral.integral_mono_on hv1_lt_u.le
        (continuous_const.intervalIntegrable v₁ u) hint_u ?_
      intro t ht
      rw [halloc_lo t ⟨ht.1, ht.2.trans hu_le_α⟩]
      have ht_ball : t ∈ Metric.ball v₁ δ ∩ Icc v₁ v₄ := by
        refine ⟨?_, ⟨ht.1, ht.2.trans hu_in.2⟩⟩
        rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)]
        have : u ≤ v₁ + δ / 2 := min_le_right _ _
        linarith [ht.2]
      have hFr_lt : F_riv t < mid := hδ ht_ball
      have hFr0 := hFriv_nonneg_lo t ⟨ht.1, ht.2.trans hu_le_α⟩
      have := pow_le_pow_left₀ hFr0 hFr_lt.le (M.n - 1)
      linarith
    have hσu_pos : 0 < σ u := by
      have : 0 < ((F₁ α) ^ (M.n - 1) - mid ^ (M.n - 1)) * (u - v₁) := mul_pos hgap_pos (by linarith)
      linarith [hσ_v1, hσu_ge]
    linarith [hσ_nonpos u hu_in]
  -- Step 3: Width bound d = (F(v₄) - F(v₁))/m ≤ F(β) - F(α)
  have hd_le : (M.F v₄ - M.F v₁) / (M.m : ℝ) ≤ η_p := by
    have h1 := hF1_v1 hv1_gt
    have h4 := hF1_v4 hv4_lt1
    have hc1 := hF1_const_lo v₁ (left_mem_Icc.mpr hv1_α)
    have hc4 := hF1_const_hi v₄ (right_mem_Icc.mpr hβ_v4)
    have hAdiff : M.A v₄ - M.A v₁ = (M.F v₄ - M.F v₁) / (M.m : ℝ) := by
      unfold Market.A; ring
    linarith [hF1_step]
  exact ⟨hv1_gt, hv4_lt1, hd_le⟩

/-- **Theorem 5(i) (Small Pools at Fixed `n`)**:
Under `M : SmoothMarket` and `inv : M.toMarket.InverseDemand`, fix `v ∈ (max ρ a, 1)`.
1. If `E(v) < X̄(m)`, there exists `η > 0` such that every interior band `[v₁, v₄]`
   induced by a pool `(α, β)` with `α < v < β`, `β - α < η`, and width
   `(F(v₄) - F(v₁)) / m ≤ F(β) - F(α)` (guaranteed by `propC1_narrow_pool_induces_interior_band`)
   strictly lowers seller 1's revenue (`D < 0`).
2. Conversely, if `E(v) > X̄(m)`, there exists `η > 0` such that every such narrow pool
   strictly raises seller 1's revenue (`D > 0`). -/
theorem theorem5_small_pools (M : SmoothMarket) (inv : M.toMarket.InverseDemand)
    {ρ v : ℝ} (hv_lo : max ρ M.a < v) (hv_hi : v < 1) :
    (curvatureE M v < Xbar M.m →
      ∃ η > 0, ∀ α β v₁ v₄ : ℝ,
        max ρ M.a < v₁ → v₁ ≤ α → α < v → v < β → β ≤ v₄ → v₄ < 1 →
        β - α < η → (M.F v₄ - M.F v₁) / (M.m : ℝ) ≤ M.F β - M.F α →
        singleBandGain M.toMarket inv.P ((1 - M.F v₄) / M.m) ((1 - M.F v₁) / M.m) < 0) ∧
    (Xbar M.m < curvatureE M v →
      ∃ η > 0, ∀ α β v₁ v₄ : ℝ,
        max ρ M.a < v₁ → v₁ ≤ α → α < v → v < β → β ≤ v₄ → v₄ < 1 →
        β - α < η → (M.F v₄ - M.F v₁) / (M.m : ℝ) ≤ M.F β - M.F α →
        0 < singleBandGain M.toMarket inv.P ((1 - M.F v₄) / M.m) ((1 - M.F v₁) / M.m)) := by
  have hv : v ∈ Ioo M.a 1 := ⟨(le_max_right ρ M.a).trans_lt hv_lo, hv_hi⟩
  set q := (1 - M.F v) / (M.m : ℝ)
  set P' := invDemandDeriv M.toMarket inv
  set P'' := invDemandDeriv2 M inv
  set C := 2 * d_tt_Pi M.m P' P'' q q + d_tq_Pi M.m P' P'' q q
  set coeff := ((M.n : ℝ) * ((M.n : ℝ) - 1) / 24) * C
  have hsign := propC1_curvature_sign M inv hv
  have hmpos : (0 : ℝ) < M.m := M.toMarket.m_pos_real
  have hAv_pos : 0 < 1 - q := by
    have hFv_pos : 0 < M.F v := by
      rw [← M.hF_a]
      exact M.toMarket.F_strictMonoOn (left_mem_Icc.mpr M.ha1.le) (Ioo_subset_Icc_self hv) hv.1
    have : q < 1 / (M.m : ℝ) := div_lt_div_of_pos_right (by linarith) hmpos
    have hm2 : (2 : ℝ) ≤ M.m := by exact_mod_cast M.hm
    have : 1 / (M.m : ℝ) < 1 := by rw [div_lt_one hmpos]; linarith
    linarith
  have hF_cont : ContinuousAt M.F v :=
    M.toMarket.F_continuousOn.continuousAt (Icc_mem_nhds hv.1 hv.2)
  -- Helper: given any δ > 0, find η > 0 such that α < v < β, β - α < η, width ≤ F(β) - F(α)
  -- implies |q_lo - q| < δ and |q_hi - q| < δ
  have hη_of_δ : ∀ δ > 0, ∃ η > 0, ∀ α β v₁ v₄ : ℝ,
      max ρ M.a < v₁ → v₁ ≤ α → α < v → v < β → β ≤ v₄ → v₄ < 1 →
      β - α < η → (M.F v₄ - M.F v₁) / (M.m : ℝ) ≤ M.F β - M.F α →
      |(1 - M.F v₄) / (M.m : ℝ) - q| < δ ∧ |(1 - M.F v₁) / (M.m : ℝ) - q| < δ := by
    intro δ hδ
    obtain ⟨η, hη_pos, hη⟩ := Metric.continuousAt_iff.mp hF_cont (δ / 2) (by linarith)
    refine ⟨η, hη_pos, ?_⟩
    intro α β v₁ v₄ hv1_lo hv1_α hαv hvβ hβv4 hv4_1 hβα hwidth
    have hα_dist : |M.F α - M.F v| < δ / 2 := by
      have : dist α v < η := by rw [Real.dist_eq, abs_of_neg (by linarith)]; linarith
      simpa [Real.dist_eq] using hη this
    have hβ_dist : |M.F β - M.F v| < δ / 2 := by
      have : dist β v < η := by rw [Real.dist_eq, abs_of_pos (by linarith)]; linarith
      simpa [Real.dist_eq] using hη this
    have hFβ_sub_Fα : M.F β - M.F α < δ := by
      linarith [(abs_lt.mp hα_dist).1, (abs_lt.mp hβ_dist).2]
    have hv1_a : M.a ≤ v₁ := (le_max_right ρ M.a).trans hv1_lo.le
    have hFv1_le_Fv : M.F v₁ ≤ M.F v := M.toMarket.F_strictMonoOn.monotoneOn
      ⟨hv1_a, (hv1_α.trans hαv.le).trans hv_hi.le⟩ (Ioo_subset_Icc_self hv) (hv1_α.trans hαv.le)
    have hFv_le_Fv4 : M.F v ≤ M.F v₄ := M.toMarket.F_strictMonoOn.monotoneOn
      (Ioo_subset_Icc_self hv) ⟨hv1_a.trans (hv1_α.trans (hαv.trans (hvβ.trans_le hβv4)).le), hv4_1.le⟩
      (hvβ.le.trans hβv4)
    have hq_lo_le : (1 - M.F v₄) / (M.m : ℝ) ≤ q :=
      div_le_div_of_nonneg_right (by linarith) hmpos.le
    have hq_le_hi : q ≤ (1 - M.F v₁) / (M.m : ℝ) :=
      div_le_div_of_nonneg_right (by linarith) hmpos.le
    have hgap : (1 - M.F v₁) / (M.m : ℝ) - (1 - M.F v₄) / (M.m : ℝ) < δ := by
      have heq : (1 - M.F v₁) / (M.m : ℝ) - (1 - M.F v₄) / (M.m : ℝ) =
          (M.F v₄ - M.F v₁) / (M.m : ℝ) := by ring
      rw [heq]; exact hwidth.trans_lt hFβ_sub_Fα
    constructor
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; linarith
  have hCW_pos : (0 : ℝ) < (M.n : ℝ) * ((M.n : ℝ) - 1) / 24 := by
    have : (2 : ℝ) ≤ M.n := by exact_mod_cast M.hn
    nlinarith
  constructor
  · intro hE
    have hC_neg : C < 0 := hsign.2.1.mpr hE
    have hcoeff_neg : coeff < 0 := mul_neg_of_pos_of_neg hCW_pos hC_neg
    set ε : ℝ := (-coeff) * ((1 - q) / 2) ^ (M.n - 2) / 2
    have hε_pos : 0 < ε := by
      have hnc : 0 < -coeff := by linarith
      positivity
    obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := propC1_small_pool_expansion M inv hv ε hε_pos
    set δ : ℝ := min δ₁ ((1 - q) / 2)
    have hδ_pos : 0 < δ := lt_min hδ₁_pos (by linarith)
    obtain ⟨η, hη_pos, hη⟩ := hη_of_δ δ hδ_pos
    refine ⟨η, hη_pos, ?_⟩
    intro α β v₁ v₄ hv1_lo hv1_α hαv hvβ hβv4 hv4_1 hβα hwidth
    obtain ⟨hlo, hhi⟩ := hη α β v₁ v₄ hv1_lo hv1_α hαv hvβ hβv4 hv4_1 hβα hwidth
    set q_lo := (1 - M.F v₄) / (M.m : ℝ)
    set q_hi := (1 - M.F v₁) / (M.m : ℝ)
    have hv1_lt_v4 : v₁ < v₄ := (hv1_α.trans_lt (hαv.trans hvβ)).trans_le hβv4
    have hv1_a : M.a ≤ v₁ := (le_max_right ρ M.a).trans hv1_lo.le
    have hFv_lt : M.F v₁ < M.F v₄ := M.toMarket.F_strictMonoOn
      ⟨hv1_a, (hv1_lt_v4.trans hv4_1).le⟩ ⟨hv1_a.trans hv1_lt_v4.le, hv4_1.le⟩ hv1_lt_v4
    have hq_lt : q_lo < q_hi := div_lt_div_of_pos_right (by linarith) hmpos
    have hexp := hδ₁ q_lo q_hi hq_lt (hlo.trans_le (min_le_left _ _)) (hhi.trans_le (min_le_left _ _))
    have h1qlo : (1 - q) / 2 ≤ 1 - q_lo := by
      have : |q_lo - q| < (1 - q) / 2 := hlo.trans_le (min_le_right _ _)
      linarith [(abs_lt.mp this).2]
    have hpow : ((1 - q) / 2) ^ (M.n - 2) ≤ (1 - q_lo) ^ (M.n - 2) :=
      pow_le_pow_left₀ (by linarith) h1qlo _
    have hd3 : 0 < (q_hi - q_lo) ^ 3 := pow_pos (by linarith) 3
    have hup : singleBandGain M.toMarket inv.P q_lo q_hi -
        coeff * (1 - q_lo) ^ (M.n - 2) * (q_hi - q_lo) ^ 3 ≤ ε * (q_hi - q_lo) ^ 3 :=
      (abs_le.mp hexp).2
    have hlead : coeff * (1 - q_lo) ^ (M.n - 2) + ε < 0 := by
      have : coeff * (1 - q_lo) ^ (M.n - 2) ≤ coeff * ((1 - q) / 2) ^ (M.n - 2) :=
        mul_le_mul_of_nonpos_left hpow hcoeff_neg.le
      have : coeff * ((1 - q) / 2) ^ (M.n - 2) + ε = -ε := by simp only [ε]; ring
      linarith
    nlinarith
  · intro hE
    have hC_pos : 0 < C := hsign.2.2.mpr hE
    have hcoeff_pos : 0 < coeff := mul_pos hCW_pos hC_pos
    set ε : ℝ := coeff * ((1 - q) / 2) ^ (M.n - 2) / 2
    have hε_pos : 0 < ε := by positivity
    obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := propC1_small_pool_expansion M inv hv ε hε_pos
    set δ : ℝ := min δ₁ ((1 - q) / 2)
    have hδ_pos : 0 < δ := lt_min hδ₁_pos (by linarith)
    obtain ⟨η, hη_pos, hη⟩ := hη_of_δ δ hδ_pos
    refine ⟨η, hη_pos, ?_⟩
    intro α β v₁ v₄ hv1_lo hv1_α hαv hvβ hβv4 hv4_1 hβα hwidth
    obtain ⟨hlo, hhi⟩ := hη α β v₁ v₄ hv1_lo hv1_α hαv hvβ hβv4 hv4_1 hβα hwidth
    set q_lo := (1 - M.F v₄) / (M.m : ℝ)
    set q_hi := (1 - M.F v₁) / (M.m : ℝ)
    have hv1_lt_v4 : v₁ < v₄ := (hv1_α.trans_lt (hαv.trans hvβ)).trans_le hβv4
    have hv1_a : M.a ≤ v₁ := (le_max_right ρ M.a).trans hv1_lo.le
    have hFv_lt : M.F v₁ < M.F v₄ := M.toMarket.F_strictMonoOn
      ⟨hv1_a, (hv1_lt_v4.trans hv4_1).le⟩ ⟨hv1_a.trans hv1_lt_v4.le, hv4_1.le⟩ hv1_lt_v4
    have hq_lt : q_lo < q_hi := div_lt_div_of_pos_right (by linarith) hmpos
    have hexp := hδ₁ q_lo q_hi hq_lt (hlo.trans_le (min_le_left _ _)) (hhi.trans_le (min_le_left _ _))
    have h1qlo : (1 - q) / 2 ≤ 1 - q_lo := by
      have : |q_lo - q| < (1 - q) / 2 := hlo.trans_le (min_le_right _ _)
      linarith [(abs_lt.mp this).2]
    have hpow : ((1 - q) / 2) ^ (M.n - 2) ≤ (1 - q_lo) ^ (M.n - 2) :=
      pow_le_pow_left₀ (by linarith) h1qlo _
    have hd3 : 0 < (q_hi - q_lo) ^ 3 := pow_pos (by linarith) 3
    have hlo_b : -(ε * (q_hi - q_lo) ^ 3) ≤ singleBandGain M.toMarket inv.P q_lo q_hi -
        coeff * (1 - q_lo) ^ (M.n - 2) * (q_hi - q_lo) ^ 3 :=
      (abs_le.mp hexp).1
    have hlead : 0 < coeff * (1 - q_lo) ^ (M.n - 2) - ε := by
      have : coeff * ((1 - q) / 2) ^ (M.n - 2) ≤ coeff * (1 - q_lo) ^ (M.n - 2) :=
        mul_le_mul_of_nonneg_left hpow hcoeff_pos.le
      have : coeff * ((1 - q) / 2) ^ (M.n - 2) - ε = ε := by simp only [ε]; ring
      linarith
    nlinarith

/-! ### Proposition C.2(i)–(ii): Many Buyers Limit and `E ≤ 2m` Narrow-Band Condition -/

/-- Elementary quadratic lower bound `(1 + δ)^n ≥ 1 + n δ + (n(n - 1)/2) δ²` for `δ ≥ 0`. -/
private lemma one_add_pow_ge_quad {δ : ℝ} (hδ : 0 ≤ δ) :
    ∀ n : ℕ, 1 + (n : ℝ) * δ + ((n : ℝ) * ((n : ℝ) - 1) / 2) * δ ^ 2 ≤ (1 + δ) ^ n
  | 0 => by simp
  | n + 1 => by
    have ih := one_add_pow_ge_quad hδ n
    have h1 : 0 ≤ 1 + δ := by linarith
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hquad0 : 0 ≤ ((n : ℝ) * ((n : ℝ) - 1) / 2) * δ ^ 3 := by
      cases n with
      | zero => simp
      | succ k =>
        have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        push_cast
        have : ((k : ℝ) + 1) * ((k : ℝ) + 1 - 1) / 2 = ((k : ℝ) + 1) * (k : ℝ) / 2 := by ring
        rw [this]
        positivity
    calc 1 + ((n + 1 : ℕ) : ℝ) * δ + (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) - 1) / 2) * δ ^ 2
        ≤ (1 + δ) * (1 + (n : ℝ) * δ + ((n : ℝ) * ((n : ℝ) - 1) / 2) * δ ^ 2) := by
          push_cast; nlinarith [hquad0]
      _ ≤ (1 + δ) * (1 + δ) ^ n := mul_le_mul_of_nonneg_left ih h1
      _ = (1 + δ) ^ (n + 1) := by rw [pow_succ']

/-- For `0 ≤ c < 1`, `(n : ℝ) * c ^ (n - 1) → 0` as `n → ∞`. -/
private lemma tendsto_nat_mul_pow_sub_one_zero {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    Tendsto (fun n : ℕ => (n : ℝ) * c ^ (n - 1)) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  by_cases hc : c = 0
  · refine ⟨2, fun n hn => ?_⟩
    rw [Real.dist_eq, sub_zero, hc, zero_pow (by omega : n - 1 ≠ 0), mul_zero, abs_zero]
    exact hε
  · have hc_pos : 0 < c := lt_of_le_of_ne hc0 (Ne.symm hc)
    set δ : ℝ := 1 / c - 1
    have hδ_pos : 0 < δ := by
      have : 1 < 1 / c := (one_lt_div hc_pos).mpr hc1
      linarith
    have h1δ : 1 + δ = 1 / c := by simp only [δ]; ring
    obtain ⟨N, hN⟩ := exists_nat_gt (4 / (ε * δ ^ 2 * c) + 3)
    refine ⟨max N 3, fun n hn => ?_⟩
    have hn3 : 3 ≤ n := (le_max_right N 3).trans hn
    have hnN : N ≤ n := (le_max_left N 3).trans hn
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    have hpow_ge : ((n - 1 : ℕ) : ℝ) * (((n - 1 : ℕ) : ℝ) - 1) / 2 * δ ^ 2 ≤ (1 + δ) ^ (n - 1) := by
      have hq := one_add_pow_ge_quad hδ_pos.le (n - 1)
      have hlin : 0 ≤ 1 + ((n - 1 : ℕ) : ℝ) * δ := by positivity
      linarith
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
    rw [hcast, show (n : ℝ) - 1 - 1 = (n : ℝ) - 2 by ring] at hpow_ge
    have h1δ_pow : (1 + δ) ^ (n - 1) = (c ^ (n - 1))⁻¹ := by
      rw [h1δ, one_div, inv_pow]
    have hn2_pos : 0 < (n : ℝ) - 2 := by linarith
    have hden_pos : 0 < ((n : ℝ) - 1) * ((n : ℝ) - 2) / 2 * δ ^ 2 := by
      have h1 : 0 < (n : ℝ) - 1 := by linarith
      positivity
    have hc_pow_le : c ^ (n - 1) ≤ 2 / (((n : ℝ) - 1) * ((n : ℝ) - 2) * δ ^ 2) := by
      rw [h1δ_pow] at hpow_ge
      have hinv := inv_anti₀ hden_pos hpow_ge
      rw [inv_inv] at hinv
      have heq : (((n : ℝ) - 1) * ((n : ℝ) - 2) / 2 * δ ^ 2)⁻¹ =
          2 / (((n : ℝ) - 1) * ((n : ℝ) - 2) * δ ^ 2) := by
        field_simp
      rwa [heq] at hinv
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg n) (pow_nonneg hc0 _))]
    have hratio : (n : ℝ) / ((n : ℝ) - 1) ≤ 2 := by
      rw [div_le_iff₀ (by linarith : 0 < (n : ℝ) - 1)]; linarith
    have hN_lt : 4 / (ε * δ ^ 2 * c) + 3 < (n : ℝ) := lt_of_lt_of_le hN (by exact_mod_cast hnN)
    have h4_lt : 4 / (ε * δ ^ 2) < (n : ℝ) - 2 := by
      have h1 : 4 / (ε * δ ^ 2) ≤ 4 / (ε * δ ^ 2 * c) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        have hpos : 0 < ε * δ ^ 2 := by positivity
        nlinarith
      linarith
    calc (n : ℝ) * c ^ (n - 1)
        ≤ (n : ℝ) * (2 / (((n : ℝ) - 1) * ((n : ℝ) - 2) * δ ^ 2)) :=
          mul_le_mul_of_nonneg_left hc_pow_le (Nat.cast_nonneg n)
      _ = ((n : ℝ) / ((n : ℝ) - 1)) * (2 / (((n : ℝ) - 2) * δ ^ 2)) := by
          have : (n : ℝ) - 1 ≠ 0 := by linarith
          have : (n : ℝ) - 2 ≠ 0 := by linarith
          field_simp
      _ ≤ 2 * (2 / (((n : ℝ) - 2) * δ ^ 2)) :=
          mul_le_mul_of_nonneg_right hratio (by positivity)
      _ = 4 / (((n : ℝ) - 2) * δ ^ 2) := by ring
      _ < ε := by
          rw [div_lt_iff₀ (mul_pos hn2_pos (sq_pos_of_pos hδ_pos))]
          have hmul : 4 < ((n : ℝ) - 2) * (ε * δ ^ 2) := (div_lt_iff₀ (by positivity)).mp h4_lt
          linarith

/-- As `n → ∞`, `qStar n q_lo q_hi → q_lo` for any fixed `0 < q_lo < q_hi < 1`. -/
private lemma tendsto_qStar_atTop {q_lo q_hi : ℝ} (hq_lo_pos : 0 < q_lo) (hq_lt : q_lo < q_hi)
    (hq_hi1 : q_hi < 1) :
    Tendsto (fun n : ℕ => qStar n q_lo q_hi) atTop (nhds q_lo) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set A4 := 1 - q_lo
  set A1 := 1 - q_hi
  set d := q_hi - q_lo
  set δ := min (ε / 2) (d / 2)
  have hA4 : 0 < A4 := by linarith
  have hA1 : 0 < A1 := by linarith
  have hd : 0 < d := by linarith
  have hδ_pos : 0 < δ := lt_min (by linarith) (by linarith)
  have hδ_lt_d : δ < d := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  set c := (A4 - δ) / A4
  have hc0 : 0 ≤ c := div_nonneg (by linarith [hδ_lt_d]) hA4.le
  have hc1 : c < 1 := (div_lt_one hA4).mpr (by linarith)
  set r := A1 / A4
  have hr0 : 0 ≤ r := div_nonneg hA1.le hA4.le
  have hr1 : r < 1 := (div_lt_one hA4).mpr (by linarith)
  have hlim1 : Tendsto (fun n : ℕ => d * ((n : ℝ) * c ^ (n - 1))) atTop (nhds 0) := by
    simpa using (tendsto_nat_mul_pow_sub_one_zero hc0 hc1).const_mul d
  have hlim2 : Tendsto (fun n : ℕ => r ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  obtain ⟨N1, hN1⟩ := (Metric.tendsto_atTop.mp hlim1) (A4 / 2) (by linarith)
  obtain ⟨N2, hN2⟩ := (Metric.tendsto_atTop.mp hlim2) (1 / 2) (by norm_num)
  refine ⟨max (max N1 N2) 2, fun n hn => ?_⟩
  have hn2 : 2 ≤ n := (le_max_right _ _).trans hn
  have hn1 : N1 ≤ n := ((le_max_left _ _).trans (le_max_left _ _)).trans hn
  have hn2' : N2 ≤ n := ((le_max_right _ _).trans (le_max_left _ _)).trans hn
  have hqs := qStar_mem_Ioo hn2 hq_lt hq_hi1
  have h1 := hN1 n hn1
  have h2 := hN2 n hn2'
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h1 h2
  have hpow := one_sub_qStar_pow hn2 hq_lt hq_hi1
  have hne : (1 - q_hi : ℝ) ≠ 1 - q_lo := by linarith
  have havg : poolAvg n A1 A4 = (A4 ^ n - A1 ^ n) / ((n : ℝ) * d) := by
    unfold poolAvg; rw [ite_eq_right_iff.mpr (fun h => absurd h hne)]; congr 1; ring
  have hB_gt : A4 - δ < 1 - qStar n q_lo q_hi := by
    by_contra hle
    push Not at hle
    have hA4δ_pos : 0 < A4 - δ := by linarith
    have hpow_le : (1 - qStar n q_lo q_hi) ^ (n - 1) ≤ (A4 - δ) ^ (n - 1) :=
      pow_le_pow_left₀ (by linarith [hqs.2]) hle _
    rw [hpow, havg] at hpow_le
    have hnd_pos : 0 < (n : ℝ) * d := mul_pos (by exact_mod_cast (by omega : 0 < n)) hd
    have hmul : A4 ^ n - A1 ^ n ≤ (n : ℝ) * d * (A4 - δ) ^ (n - 1) :=
      (div_le_iff₀ hnd_pos).mp hpow_le |>.trans (by ring_nf; rfl)
    have hA4_n_pos : 0 < A4 ^ (n - 1) := pow_pos hA4 _
    have hdiv : A4 * (1 - r ^ n) ≤ d * ((n : ℝ) * c ^ (n - 1)) := by
      have hLHS : A4 * (1 - r ^ n) = (A4 ^ n - A1 ^ n) / A4 ^ (n - 1) := by
        have h1 : A4 ^ n = A4 * A4 ^ (n - 1) := by
          conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ n), pow_succ']
        rw [div_pow, h1]
        have : A4 ^ (n - 1) ≠ 0 := hA4_n_pos.ne'
        have : A4 ^ n ≠ 0 := (pow_pos hA4 n).ne'
        field_simp
      have hRHS : d * ((n : ℝ) * c ^ (n - 1)) = ((n : ℝ) * d * (A4 - δ) ^ (n - 1)) / A4 ^ (n - 1) := by
        simp only [c]; rw [div_pow]; ring
      rw [hLHS, hRHS]
      exact div_le_div_of_nonneg_right hmul hA4_n_pos.le
    have : A4 / 2 < A4 * (1 - r ^ n) := by nlinarith
    linarith
  rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hqs.1)]
  have hδ_le : δ ≤ ε / 2 := min_le_left _ _
  linarith

/-- **Proposition C.2(i) (Many Buyers Limit, equation (24))**:
For any fixed interior band with quantities `0 < q_lo < q_hi < 1 / m`,
`lim_{n → ∞} D_n / (1 - q_lo)^n = J(q_lo, q_hi) = (Π(q_hi, q_lo) - Π(q_lo, q_lo)) / (q_hi - q_lo) - ∂_t Π(q_lo, q_lo)`. -/
theorem propC2_many_buyers_limit (M : Market) (inv : M.InverseDemand)
    {q_lo q_hi : ℝ} (hq_lo_pos : 0 < q_lo) (hq_lt : q_lo < q_hi)
    (hq_hi_m : (M.m : ℝ) * q_hi < 1) :
    Tendsto (fun n : ℕ => singleBandGainOf M.m n inv.P q_lo q_hi / (1 - q_lo) ^ n)
      atTop (nhds (J_secant M.m inv.P (invDemandDeriv M inv) q_lo q_hi)) := by
  set P' := invDemandDeriv M inv
  set A4 := 1 - q_lo
  set A1 := 1 - q_hi
  set d := q_hi - q_lo
  set r := A1 / A4
  have hm2 : (2 : ℝ) ≤ M.m := by exact_mod_cast M.hm
  have hq_hi1 : q_hi < 1 := by nlinarith
  have hA4 : 0 < A4 := by linarith
  have hA1 : 0 < A1 := by linarith
  have hd : 0 < d := by linarith
  have hr0 : 0 ≤ r := div_nonneg hA1.le hA4.le
  have hr1 : r < 1 := (div_lt_one hA4).mpr (by linarith)
  have hmem_Ioo : ∀ u w : ℝ, u ∈ Icc q_lo q_hi → w ∈ Icc q_lo q_hi →
      u + ((M.m : ℝ) - 1) * w ∈ Ioo (0 : ℝ) 1 := by
    intro u w hu hw
    constructor
    · nlinarith [hu.1, hw.1]
    · nlinarith [hu.2, hw.2, hq_hi_m]
  have hqs_lim : Tendsto (fun n : ℕ => qStar n q_lo q_hi) atTop (nhds q_lo) :=
    tendsto_qStar_atTop hq_lo_pos hq_lt hq_hi1
  -- Split into I1_n → -∂_t Π(q_lo, q_lo) and I2_n → (Π(q_hi, q_lo) - Π(q_lo, q_lo)) / d
  set c1 := d_t_Pi M.m inv.P P' q_lo q_lo
  set g : ℝ → ℝ := fun q => cournotRevOf M.m inv.P q_hi q - cournotRevOf M.m inv.P q q
  have hlim1 : Tendsto (fun n : ℕ =>
      (∫ q in q_lo..(qStar n q_lo q_hi),
        (cournotRevOf M.m inv.P q_lo q - cournotRevOf M.m inv.P q q) * W_of n q) / A4 ^ n)
      atTop (nhds (-c1)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    -- Continuity of (s, q) ↦ d_t_Pi at (q_lo, q_lo)
    have hmq_lo : (M.m : ℝ) * q_lo ∈ Ioo (0 : ℝ) 1 := by
      have := hmem_Ioo q_lo q_lo (left_mem_Icc.mpr hq_lt.le) (left_mem_Icc.mpr hq_lt.le)
      rwa [show q_lo + ((M.m : ℝ) - 1) * q_lo = (M.m : ℝ) * q_lo by ring] at this
    have hP_at : ContinuousAt inv.P (q_lo + ((M.m : ℝ) - 1) * q_lo) := by
      rw [show q_lo + ((M.m : ℝ) - 1) * q_lo = (M.m : ℝ) * q_lo by ring]
      exact inv.hP_cont.continuousAt (Icc_mem_nhds hmq_lo.1 hmq_lo.2)
    have hP'_at : ContinuousAt P' (q_lo + ((M.m : ℝ) - 1) * q_lo) := by
      rw [show q_lo + ((M.m : ℝ) - 1) * q_lo = (M.m : ℝ) * q_lo by ring]
      exact (invDemandDeriv_continuousOn M inv).continuousAt (Icc_mem_nhds hmq_lo.1 hmq_lo.2)
    have hlin_c : ContinuousAt (fun p : ℝ × ℝ => p.1 + ((M.m : ℝ) - 1) * p.2) (q_lo, q_lo) :=
      continuousAt_fst.add (continuousAt_const.mul continuousAt_snd)
    have hP_comp : ContinuousAt (fun p : ℝ × ℝ => inv.P (p.1 + ((M.m : ℝ) - 1) * p.2)) (q_lo, q_lo) :=
      ContinuousAt.comp (g := inv.P) (f := fun p : ℝ × ℝ => p.1 + ((M.m : ℝ) - 1) * p.2) hP_at hlin_c
    have hP'_comp : ContinuousAt (fun p : ℝ × ℝ => P' (p.1 + ((M.m : ℝ) - 1) * p.2)) (q_lo, q_lo) :=
      ContinuousAt.comp (g := P') (f := fun p : ℝ × ℝ => p.1 + ((M.m : ℝ) - 1) * p.2) hP'_at hlin_c
    have hdt_cont : ContinuousAt (fun p : ℝ × ℝ => d_t_Pi M.m inv.P P' p.1 p.2) (q_lo, q_lo) := by
      unfold d_t_Pi
      exact hP_comp.add (continuousAt_fst.mul hP'_comp)
    obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := Metric.continuousAt_iff.mp hdt_cont (ε / 2) (by linarith)
    set δ := min δ₁ (min (d / 2) (ε * d / (4 * (|c1| + 1))))
    have hδ_pos : 0 < δ := lt_min hδ₁_pos (lt_min (by linarith) (by positivity))
    obtain ⟨N1, hN1⟩ := (Metric.tendsto_atTop.mp hqs_lim) δ hδ_pos
    obtain ⟨N2, hN2⟩ := exists_nat_gt (4 * (|c1| + 1) / (ε * d) + 2)
    refine ⟨max (max N1 N2) 2, fun n hn => ?_⟩
    have hn2 : 2 ≤ n := (le_max_right _ _).trans hn
    have hn1 : N1 ≤ n := ((le_max_left _ _).trans (le_max_left _ _)).trans hn
    have hn2' : N2 ≤ n := ((le_max_right _ _).trans (le_max_left _ _)).trans hn
    set qs := qStar n q_lo q_hi
    have hqs := qStar_mem_Ioo hn2 hq_lt hq_hi1
    have hqs_close : qs - q_lo < δ := by
      have h := hN1 n hn1
      rwa [Real.dist_eq, abs_of_pos (sub_pos.mpr hqs.1)] at h
    -- Pointwise linear approximation on [q_lo, qs]
    have hlin_err : ∀ q ∈ Icc q_lo qs,
        |(cournotRevOf M.m inv.P q_lo q - cournotRevOf M.m inv.P q q) + c1 * (q - q_lo)| ≤
          (ε / 2) * (q - q_lo) := by
      intro q hq
      have hftc : (cournotRevOf M.m inv.P q_lo q - cournotRevOf M.m inv.P q q) + c1 * (q - q_lo) =
          -(∫ s in q_lo..q, (d_t_Pi M.m inv.P P' s q - c1)) := by
        have hderiv : ∀ s ∈ uIcc q_lo q,
            HasDerivAt (fun x => cournotRevOf M.m inv.P x q - c1 * x)
              (d_t_Pi M.m inv.P P' s q - c1) s := by
          intro s hs
          rw [uIcc_of_le hq.1] at hs
          exact (hasDerivAt_cournotRev_t M inv
            (hmem_Ioo s q ⟨hs.1, hs.2.trans (hq.2.trans hqs.2.le)⟩ ⟨hq.1, hq.2.trans hqs.2.le⟩)).sub
            ((hasDerivAt_id s).const_mul c1 |>.congr_deriv (mul_one c1))
        have hint : IntervalIntegrable (fun s => d_t_Pi M.m inv.P P' s q - c1) volume q_lo q := by
          apply ContinuousOn.intervalIntegrable
          rw [uIcc_of_le hq.1]
          have hlin : ContinuousOn (fun s => s + ((M.m : ℝ) - 1) * q) (Icc q_lo q) :=
            continuousOn_id.add continuousOn_const
          have hmap : MapsTo (fun s => s + ((M.m : ℝ) - 1) * q) (Icc q_lo q) (Icc 0 1) :=
            fun s hs => Ioo_subset_Icc_self (hmem_Ioo s q ⟨hs.1, hs.2.trans (hq.2.trans hqs.2.le)⟩
              ⟨hq.1, hq.2.trans hqs.2.le⟩)
          exact ((inv.hP_cont.comp hlin hmap).add
            (continuousOn_id.mul ((invDemandDeriv_continuousOn M inv).comp hlin hmap))).sub continuousOn_const
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]; ring
      rw [hftc, abs_neg]
      have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const (a := q_lo) (b := q)
        (C := ε / 2) (f := fun s => d_t_Pi M.m inv.P P' s q - c1) (by
          intro s hs
          rw [uIoc_of_le hq.1] at hs
          rw [Real.norm_eq_abs]
          have hdist : dist (s, q) (q_lo, q_lo) < δ₁ := by
            rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq,
              abs_of_nonneg (sub_nonneg.mpr hs.1.le), abs_of_nonneg (sub_nonneg.mpr hq.1)]
            have hδ_le : δ ≤ δ₁ := min_le_left _ _
            exact max_lt (by linarith [hs.2, hq.2, hqs_close, hδ_le])
              (by linarith [hq.2, hqs_close, hδ_le])
          exact (by simpa [Real.dist_eq] using hδ₁ hdist : |d_t_Pi M.m inv.P P' s q - c1| < ε / 2).le)
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hq.1)] at hnorm
      exact hnorm
    -- Exact evaluation of S_n = (∫ q in q_lo..qs, (q - q_lo) * W_of n q) / A4^n
    set S_n := (∫ q in q_lo..qs, (q - q_lo) * W_of n q) / A4 ^ n
    set B := 1 - qs
    have hB_pos : 0 < B := by linarith [hqs.2]
    have hB_le1 : B ≤ 1 := by linarith [hqs.1]
    have hB_pow : B ^ (n - 1) = (A4 ^ n - A1 ^ n) / ((n : ℝ) * d) := by
      have hp := one_sub_qStar_pow hn2 hq_lt hq_hi1
      have hne : (1 - q_hi : ℝ) ≠ 1 - q_lo := by linarith
      unfold poolAvg at hp
      rw [ite_eq_right_iff.mpr (fun h => absurd h hne)] at hp
      simpa [B, A4, A1, d, sub_sub_sub_cancel_left] using hp
    have hSn_eq : S_n = 1 - (B / A4) ^ n - (n : ℝ) * (qs - q_lo) * B ^ (n - 1) / A4 ^ n := by
      have hint_eq : ∫ q in q_lo..qs, (q - q_lo) * W_of n q =
          ((n : ℝ) * ((n : ℝ) - 1)) * ∫ q in q_lo..qs, (q - q_lo) * (1 - q) ^ (n - 2) := by
        rw [← intervalIntegral.integral_const_mul]; congr 1; ext q; unfold W_of; ring
      simp only [S_n]
      rw [hint_eq, integral_linear_mul_one_sub_pow hn2 q_lo q_lo qs]
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
      have hn1 : ((n : ℝ) - 1) ≠ 0 := by
        have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
        linarith
      have hA4n : A4 ^ n ≠ 0 := (pow_pos hA4 n).ne'
      rw [div_pow]
      field_simp
      simp only [A4, B]
      ring
    have hSn_le1 : S_n ≤ 1 := by
      rw [hSn_eq]
      have h1 : 0 ≤ (B / A4) ^ n := by positivity
      have h2 : 0 ≤ (n : ℝ) * (qs - q_lo) * B ^ (n - 1) / A4 ^ n := by
        have : 0 ≤ qs - q_lo := by linarith [hqs.1]
        positivity
      linarith
    have h1_sub_Sn : |1 - S_n| ≤ 1 / ((n : ℝ) * d) + (qs - q_lo) / d := by
      have h1sub : 1 - S_n = (B / A4) ^ n + (n : ℝ) * (qs - q_lo) * B ^ (n - 1) / A4 ^ n := by
        linarith [hSn_eq]
      have hnonneg : 0 ≤ 1 - S_n := by
        rw [h1sub]
        have : 0 ≤ qs - q_lo := by linarith [hqs.1]
        positivity
      rw [abs_of_nonneg hnonneg, h1sub]
      have hBn_div : B ^ (n - 1) / A4 ^ n = (1 - r ^ n) / ((n : ℝ) * d) := by
        rw [hB_pow, div_div, div_pow]
        have hA4n : A4 ^ n ≠ 0 := (pow_pos hA4 n).ne'
        have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
        field_simp
      have h1rn_le1 : 1 - r ^ n ≤ 1 := by linarith [pow_nonneg hr0 n]
      have h1rn_pos : 0 ≤ 1 - r ^ n := by
        have : r ^ n ≤ 1 := pow_le_one₀ hr0 hr1.le; linarith
      have hterm1 : (B / A4) ^ n ≤ 1 / ((n : ℝ) * d) := by
        have hBn : (B / A4) ^ n = B * (B ^ (n - 1) / A4 ^ n) := by
          rw [div_pow]
          have : B ^ n = B * B ^ (n - 1) := by
            conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ n), pow_succ']
          rw [this]; ring
        rw [hBn, hBn_div]
        calc B * ((1 - r ^ n) / ((n : ℝ) * d)) ≤ 1 * (1 / ((n : ℝ) * d)) :=
              mul_le_mul hB_le1 (div_le_div_of_nonneg_right h1rn_le1 (by positivity))
                (div_nonneg h1rn_pos (by positivity)) zero_le_one
          _ = 1 / ((n : ℝ) * d) := one_mul _
      have hterm2 : (n : ℝ) * (qs - q_lo) * B ^ (n - 1) / A4 ^ n ≤ (qs - q_lo) / d := by
        have heq : (n : ℝ) * (qs - q_lo) * B ^ (n - 1) / A4 ^ n =
            (n : ℝ) * (qs - q_lo) * (B ^ (n - 1) / A4 ^ n) := by ring
        rw [heq, hBn_div]
        have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
        have heq2 : (n : ℝ) * (qs - q_lo) * ((1 - r ^ n) / ((n : ℝ) * d)) =
            ((qs - q_lo) / d) * (1 - r ^ n) := by field_simp
        rw [heq2]
        calc ((qs - q_lo) / d) * (1 - r ^ n) ≤ ((qs - q_lo) / d) * 1 :=
              mul_le_mul_of_nonneg_left h1rn_le1 (div_nonneg (by linarith [hqs.1]) hd.le)
          _ = (qs - q_lo) / d := mul_one _
      linarith
    -- Bound |I1_n - (-c1 * S_n)| ≤ (ε / 2) * S_n ≤ ε / 2
    have hcont_Pi : ContinuousOn (fun q => cournotRevOf M.m inv.P q_lo q - cournotRevOf M.m inv.P q q) (Icc q_lo qs) := by
      have hlin1 : ContinuousOn (fun q => q_lo + ((M.m : ℝ) - 1) * q) (Icc q_lo qs) :=
        continuousOn_const.add (continuousOn_const.mul continuousOn_id)
      have hmap1 : MapsTo (fun q => q_lo + ((M.m : ℝ) - 1) * q) (Icc q_lo qs) (Icc 0 1) :=
        fun q hq => Ioo_subset_Icc_self (hmem_Ioo q_lo q (left_mem_Icc.mpr hq_lt.le) ⟨hq.1, hq.2.trans hqs.2.le⟩)
      have hlin2 : ContinuousOn (fun q => q + ((M.m : ℝ) - 1) * q) (Icc q_lo qs) :=
        continuousOn_id.add (continuousOn_const.mul continuousOn_id)
      have hmap2 : MapsTo (fun q => q + ((M.m : ℝ) - 1) * q) (Icc q_lo qs) (Icc 0 1) :=
        fun q hq => Ioo_subset_Icc_self (hmem_Ioo q q ⟨hq.1, hq.2.trans hqs.2.le⟩ ⟨hq.1, hq.2.trans hqs.2.le⟩)
      exact (continuousOn_const.mul (inv.hP_cont.comp hlin1 hmap1)).sub
        (continuousOn_id.mul (inv.hP_cont.comp hlin2 hmap2))
    have hW_cont : Continuous (W_of n) :=
      continuous_const.mul ((continuous_const.sub continuous_id).pow (n - 2))
    have hi1 : IntervalIntegrable (fun q => (cournotRevOf M.m inv.P q_lo q - cournotRevOf M.m inv.P q q) * W_of n q) volume q_lo qs :=
      (hcont_Pi.mul hW_cont.continuousOn).intervalIntegrable_of_Icc hqs.1.le
    have hi2 : IntervalIntegrable (fun q => c1 * ((q - q_lo) * W_of n q)) volume q_lo qs :=
      (continuous_const.mul ((continuous_id.sub continuous_const).mul hW_cont)).intervalIntegrable _ _
    have hdiff_eq : (∫ q in q_lo..qs, (cournotRevOf M.m inv.P q_lo q - cournotRevOf M.m inv.P q q) * W_of n q) / A4 ^ n -
        (-c1 * S_n) =
        (∫ q in q_lo..qs, ((cournotRevOf M.m inv.P q_lo q - cournotRevOf M.m inv.P q q) + c1 * (q - q_lo)) * W_of n q) / A4 ^ n := by
      simp only [S_n]
      rw [show -c1 * ((∫ q in q_lo..qs, (q - q_lo) * W_of n q) / A4 ^ n) =
          -((c1 * (∫ q in q_lo..qs, (q - q_lo) * W_of n q)) / A4 ^ n) by ring,
        sub_neg_eq_add, ← add_div, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_add hi1 hi2]
      congr 2; ext q; ring
    have hI1_close : |(∫ q in q_lo..qs, (cournotRevOf M.m inv.P q_lo q - cournotRevOf M.m inv.P q q) * W_of n q) / A4 ^ n -
        (-c1 * S_n)| ≤ ε / 2 := by
      rw [hdiff_eq, abs_div, abs_of_pos (pow_pos hA4 n)]
      have hnorm_le : |∫ q in q_lo..qs, ((cournotRevOf M.m inv.P q_lo q - cournotRevOf M.m inv.P q q) + c1 * (q - q_lo)) * W_of n q| ≤
          ∫ q in q_lo..qs, (ε / 2) * ((q - q_lo) * W_of n q) := by
        have hint_lhs : IntervalIntegrable (fun q => ((cournotRevOf M.m inv.P q_lo q - cournotRevOf M.m inv.P q q) + c1 * (q - q_lo)) * W_of n q) volume q_lo qs :=
          (hi1.add hi2).congr (fun q _ => by ring)
        have hint_rhs : IntervalIntegrable (fun q => (ε / 2) * ((q - q_lo) * W_of n q)) volume q_lo qs :=
          (continuous_const.mul ((continuous_id.sub continuous_const).mul hW_cont)).intervalIntegrable _ _
        calc |∫ q in q_lo..qs, ((cournotRevOf M.m inv.P q_lo q - cournotRevOf M.m inv.P q q) + c1 * (q - q_lo)) * W_of n q|
            ≤ ∫ q in q_lo..qs, |((cournotRevOf M.m inv.P q_lo q - cournotRevOf M.m inv.P q q) + c1 * (q - q_lo)) * W_of n q| := by
              have h := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
                (f := fun q => ((cournotRevOf M.m inv.P q_lo q - cournotRevOf M.m inv.P q q) + c1 * (q - q_lo)) * W_of n q)
                hqs.1.le
              simpa only [Real.norm_eq_abs] using h
          _ ≤ ∫ q in q_lo..qs, (ε / 2) * ((q - q_lo) * W_of n q) := by
              refine intervalIntegral.integral_mono_on hqs.1.le hint_lhs.norm hint_rhs ?_
              intro q hq
              have hWnn : 0 ≤ W_of n q := by
                unfold W_of
                have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
                have hn1 : 0 ≤ (n : ℝ) - 1 := by linarith
                have : 0 ≤ 1 - q := by linarith [hq.2, hqs.2, hq_hi1]
                positivity
              rw [abs_mul, abs_of_nonneg hWnn]
              calc |(cournotRevOf M.m inv.P q_lo q - cournotRevOf M.m inv.P q q) + c1 * (q - q_lo)| * W_of n q
                  ≤ ((ε / 2) * (q - q_lo)) * W_of n q := mul_le_mul_of_nonneg_right (hlin_err q hq) hWnn
                _ = (ε / 2) * ((q - q_lo) * W_of n q) := by ring
      rw [intervalIntegral.integral_const_mul] at hnorm_le
      calc |∫ q in q_lo..qs, ((cournotRevOf M.m inv.P q_lo q - cournotRevOf M.m inv.P q q) + c1 * (q - q_lo)) * W_of n q| / A4 ^ n
          ≤ ((ε / 2) * (∫ q in q_lo..qs, (q - q_lo) * W_of n q)) / A4 ^ n :=
            div_le_div_of_nonneg_right hnorm_le (pow_nonneg hA4.le n)
        _ = (ε / 2) * S_n := by simp only [S_n]; ring
        _ ≤ (ε / 2) * 1 := mul_le_mul_of_nonneg_left hSn_le1 (by linarith)
        _ = ε / 2 := mul_one _
    have htail : |(-c1 * S_n) - (-c1)| < ε / 2 := by
      have heq : (-c1 * S_n) - (-c1) = c1 * (1 - S_n) := by ring
      rw [heq, abs_mul]
      have hN2_lt : 4 * (|c1| + 1) / (ε * d) + 2 < (n : ℝ) := lt_of_lt_of_le hN2 (by exact_mod_cast hn2')
      have h1nd : 1 / ((n : ℝ) * d) < ε / (4 * (|c1| + 1)) := by
        have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
        rw [div_lt_div_iff₀ (mul_pos hn_pos hd) (by positivity)]
        have h1 : 4 * (|c1| + 1) < (n : ℝ) * (ε * d) := (div_lt_iff₀ (by positivity)).mp (by linarith)
        linarith
      have hqsd : (qs - q_lo) / d < ε / (4 * (|c1| + 1)) := by
        have hδ_le : δ ≤ ε * d / (4 * (|c1| + 1)) := (min_le_right _ _).trans (min_le_right _ _)
        rw [div_lt_iff₀ hd]
        have : ε / (4 * (|c1| + 1)) * d = ε * d / (4 * (|c1| + 1)) := by ring
        linarith
      have hsum : |1 - S_n| < ε / (2 * (|c1| + 1)) := by
        have h1 : ε / (4 * (|c1| + 1)) + ε / (4 * (|c1| + 1)) = ε / (2 * (|c1| + 1)) := by
          have : |c1| + 1 ≠ 0 := by positivity
          field_simp; ring
        linarith [h1_sub_Sn, h1nd, hqsd, h1]
      calc |c1| * |1 - S_n| < (|c1| + 1) * (ε / (2 * (|c1| + 1))) := by
            have h1 : |c1| * |1 - S_n| ≤ (|c1| + 1) * |1 - S_n| :=
              mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
            have h2 : (|c1| + 1) * |1 - S_n| < (|c1| + 1) * (ε / (2 * (|c1| + 1))) :=
              mul_lt_mul_of_pos_left hsum (by positivity)
            exact h1.trans_lt h2
        _ = ε / 2 := by
            have : |c1| + 1 ≠ 0 := by positivity
            field_simp
    rw [Real.dist_eq]
    calc |(∫ q in q_lo..qs, (cournotRevOf M.m inv.P q_lo q - cournotRevOf M.m inv.P q q) * W_of n q) / A4 ^ n - (-c1)|
        = |((∫ q in q_lo..qs, (cournotRevOf M.m inv.P q_lo q - cournotRevOf M.m inv.P q q) * W_of n q) / A4 ^ n - (-c1 * S_n)) +
            ((-c1 * S_n) - (-c1))| := by ring_nf
      _ ≤ |(∫ q in q_lo..qs, (cournotRevOf M.m inv.P q_lo q - cournotRevOf M.m inv.P q q) * W_of n q) / A4 ^ n - (-c1 * S_n)| +
            |(-c1 * S_n) - (-c1)| := abs_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt hI1_close htail
      _ = ε := by ring
  -- Part 2: I2_n → g q_lo / d
  have hlim2 : Tendsto (fun n : ℕ =>
      (∫ q in (qStar n q_lo q_hi)..q_hi, g q * W_of n q) / A4 ^ n)
      atTop (nhds (g q_lo / d)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    -- Continuity and boundedness of g on [q_lo, q_hi]
    have hg_cont : ContinuousOn g (Icc q_lo q_hi) := by
      have hlin1 : ContinuousOn (fun q => q_hi + ((M.m : ℝ) - 1) * q) (Icc q_lo q_hi) :=
        continuousOn_const.add (continuousOn_const.mul continuousOn_id)
      have hmap1 : MapsTo (fun q => q_hi + ((M.m : ℝ) - 1) * q) (Icc q_lo q_hi) (Icc 0 1) :=
        fun q hq => Ioo_subset_Icc_self (hmem_Ioo q_hi q (right_mem_Icc.mpr hq_lt.le) hq)
      have hlin2 : ContinuousOn (fun q => q + ((M.m : ℝ) - 1) * q) (Icc q_lo q_hi) :=
        continuousOn_id.add (continuousOn_const.mul continuousOn_id)
      have hmap2 : MapsTo (fun q => q + ((M.m : ℝ) - 1) * q) (Icc q_lo q_hi) (Icc 0 1) :=
        fun q hq => Ioo_subset_Icc_self (hmem_Ioo q q hq hq)
      exact (continuousOn_const.mul (inv.hP_cont.comp hlin1 hmap1)).sub
        (continuousOn_id.mul (inv.hP_cont.comp hlin2 hmap2))
    obtain ⟨u_max, _, hu_max⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hq_lt.le) hg_cont.abs
    set M_g := |g u_max| + 1
    have hMg_pos : 0 < M_g := by positivity
    have hg_bound : ∀ q ∈ Icc q_lo q_hi, |g q| ≤ M_g := fun q hq => by
      have h : |g q| ≤ |g u_max| := hu_max hq
      simp only [M_g]; linarith
    -- Continuity of g at q_lo within [q_lo, q_hi]
    have hg_at : ContinuousWithinAt g (Icc q_lo q_hi) q_lo :=
      hg_cont q_lo (left_mem_Icc.mpr hq_lt.le)
    rw [Metric.continuousWithinAt_iff] at hg_at
    obtain ⟨δ₀, hδ₀_pos, hδ₀⟩ := hg_at (ε * d / 4) (by positivity)
    set δ := min (δ₀ / 2) (d / 2)
    have hδ_pos : 0 < δ := lt_min (by linarith) (by linarith)
    have hδ_lt_d : δ < d := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    set c_tail := (A4 - δ) / A4
    have hct0 : 0 ≤ c_tail := div_nonneg (by linarith [hδ_lt_d]) hA4.le
    have hct1 : c_tail < 1 := (div_lt_one hA4).mpr (by linarith)
    -- Limits for tail mass and total mass M_n → 1/d
    have hlim_tail : Tendsto (fun n : ℕ => (2 * M_g / A4) * ((n : ℝ) * c_tail ^ (n - 1))) atTop (nhds 0) := by
      simpa using (tendsto_nat_mul_pow_sub_one_zero hct0 hct1).const_mul (2 * M_g / A4)
    have hlim_rn : Tendsto (fun n : ℕ => r ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
    have hlim_nr : Tendsto (fun n : ℕ => (n : ℝ) * r ^ (n - 1)) atTop (nhds 0) :=
      tendsto_nat_mul_pow_sub_one_zero hr0 hr1
    obtain ⟨N1, hN1⟩ := (Metric.tendsto_atTop.mp hqs_lim) δ hδ_pos
    obtain ⟨N2, hN2⟩ := (Metric.tendsto_atTop.mp hlim_tail) (ε / 4) (by linarith)
    obtain ⟨N3, hN3⟩ := (Metric.tendsto_atTop.mp hlim_rn) (ε * d / (8 * (|g q_lo| + 1))) (by positivity)
    obtain ⟨N4, hN4⟩ := (Metric.tendsto_atTop.mp hlim_nr) (ε * A4 / (8 * (|g q_lo| + 1))) (by positivity)
    refine ⟨max (max (max N1 N2) (max N3 N4)) 2, fun n hn => ?_⟩
    have hn2 : 2 ≤ n := (le_max_right _ _).trans hn
    have h1234 : max (max N1 N2) (max N3 N4) ≤ n := (le_max_left _ _).trans hn
    have hn1 : N1 ≤ n := ((le_max_left _ _).trans (le_max_left _ _)).trans h1234
    have hn2' : N2 ≤ n := ((le_max_right _ _).trans (le_max_left _ _)).trans h1234
    have hn3 : N3 ≤ n := ((le_max_left _ _).trans (le_max_right _ _)).trans h1234
    have hn4 : N4 ≤ n := ((le_max_right _ _).trans (le_max_right _ _)).trans h1234
    set qs := qStar n q_lo q_hi
    have hqs := qStar_mem_Ioo hn2 hq_lt hq_hi1
    have hqs_lt_δ : qs < q_lo + δ := by
      have h := hN1 n hn1
      rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hqs.1)] at h
      linarith
    -- Total mass M_n = (∫ q in qs..q_hi, W_of n q) / A4^n
    set M_n := (∫ q in qs..q_hi, W_of n q) / A4 ^ n
    have hMn_eq : M_n = (1 - r ^ n) / d - ((n : ℝ) * r ^ (n - 1)) / A4 := by
      have hw : ∫ q in qs..q_hi, W_of n q =
          ((n : ℝ) * ((n : ℝ) - 1)) * ∫ q in qs..q_hi, (1 - q) ^ (n - 2) := by
        rw [← intervalIntegral.integral_const_mul]; rfl
      simp only [M_n]
      rw [hw, integral_one_sub_pow hn2 qs q_hi]
      have hpow := one_sub_qStar_pow hn2 hq_lt hq_hi1
      have hne : (1 - q_hi : ℝ) ≠ 1 - q_lo := by linarith
      unfold poolAvg at hpow
      rw [ite_eq_right_iff.mpr (fun h => absurd h hne)] at hpow
      have hBpow : (1 - qs) ^ (n - 1) = (A4 ^ n - A1 ^ n) / ((n : ℝ) * d) := by
        simpa [A4, A1, d, sub_sub_sub_cancel_left] using hpow
      rw [hBpow]
      have hn1 : ((n : ℝ) - 1) ≠ 0 := by
        have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
        linarith
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
      have hA4n : A4 ^ n ≠ 0 := (pow_pos hA4 n).ne'
      have hA4pow : A4 ^ n = A4 * A4 ^ (n - 1) := by
        conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ n), pow_succ']
      simp only [r]
      rw [div_pow, div_pow, hA4pow]
      have hA4n1 : A4 ^ (n - 1) ≠ 0 := (pow_pos hA4 (n - 1)).ne'
      field_simp
      simp only [A1]
    have hMn_le : M_n ≤ 1 / d := by
      rw [hMn_eq]
      have h1 : (1 - r ^ n) / d ≤ 1 / d := div_le_div_of_nonneg_right (by linarith [pow_nonneg hr0 n]) hd.le
      have h2 : 0 ≤ ((n : ℝ) * r ^ (n - 1)) / A4 := by positivity
      linarith
    have hMn_close : |g q_lo * M_n - g q_lo / d| < ε / 4 := by
      have heq : g q_lo * M_n - g q_lo / d = g q_lo * (M_n - 1 / d) := by ring
      rw [heq, abs_mul]
      have hdiff : |M_n - 1 / d| ≤ r ^ n / d + ((n : ℝ) * r ^ (n - 1)) / A4 := by
        have h1 : M_n - 1 / d = -(r ^ n / d + ((n : ℝ) * r ^ (n - 1)) / A4) := by
          rw [hMn_eq]; ring
        rw [h1, abs_neg, abs_of_nonneg (by positivity)]
      have h3 := hN3 n hn3
      have h4 := hN4 n hn4
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h3 h4
      have h3' : r ^ n / d < ε / (8 * (|g q_lo| + 1)) := by
        rw [div_lt_iff₀ hd]
        have : ε / (8 * (|g q_lo| + 1)) * d = ε * d / (8 * (|g q_lo| + 1)) := by ring
        linarith
      have h4' : ((n : ℝ) * r ^ (n - 1)) / A4 < ε / (8 * (|g q_lo| + 1)) := by
        rw [div_lt_iff₀ hA4]
        have : ε / (8 * (|g q_lo| + 1)) * A4 = ε * A4 / (8 * (|g q_lo| + 1)) := by ring
        linarith
      have hsum : |M_n - 1 / d| < ε / (4 * (|g q_lo| + 1)) := by
        have h1 : ε / (8 * (|g q_lo| + 1)) + ε / (8 * (|g q_lo| + 1)) = ε / (4 * (|g q_lo| + 1)) := by
          have : |g q_lo| + 1 ≠ 0 := by positivity
          field_simp; ring
        linarith [hdiff, h3', h4', h1]
      calc |g q_lo| * |M_n - 1 / d| < (|g q_lo| + 1) * (ε / (4 * (|g q_lo| + 1))) := by
            have h1 : |g q_lo| * |M_n - 1 / d| ≤ (|g q_lo| + 1) * |M_n - 1 / d| :=
              mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
            exact h1.trans_lt (mul_lt_mul_of_pos_left hsum (by positivity))
        _ = ε / 4 := by
            have : |g q_lo| + 1 ≠ 0 := by positivity
            field_simp
    -- Split ∫_{qs}^{q_hi} (g q - g q_lo) * W_of n q at q_lo + δ
    have hW_cont : Continuous (W_of n) :=
      continuous_const.mul ((continuous_const.sub continuous_id).pow (n - 2))
    have hdiff_cont : ContinuousOn (fun q => (g q - g q_lo) * W_of n q) (Icc q_lo q_hi) :=
      (hg_cont.sub continuousOn_const).mul hW_cont.continuousOn
    have hi_g : IntervalIntegrable (fun q => g q * W_of n q) volume qs q_hi :=
      ((hg_cont.mono (Icc_subset_Icc_left hqs.1.le)).mul hW_cont.continuousOn).intervalIntegrable_of_Icc hqs.2.le
    have hi_c : IntervalIntegrable (fun q => g q_lo * W_of n q) volume qs q_hi :=
      (continuous_const.mul hW_cont).intervalIntegrable _ _
    have hsplit_g : (∫ q in qs..q_hi, g q * W_of n q) / A4 ^ n - g q_lo * M_n =
        ((∫ q in qs..(q_lo + δ), (g q - g q_lo) * W_of n q) +
         (∫ q in (q_lo + δ)..q_hi, (g q - g q_lo) * W_of n q)) / A4 ^ n := by
      simp only [M_n]
      rw [show g q_lo * ((∫ q in qs..q_hi, W_of n q) / A4 ^ n) =
          (g q_lo * (∫ q in qs..q_hi, W_of n q)) / A4 ^ n by ring,
        ← sub_div, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hi_g hi_c]
      congr 1
      have h1 : IntervalIntegrable (fun q => (g q - g q_lo) * W_of n q) volume qs (q_lo + δ) :=
        (hdiff_cont.mono (Icc_subset_Icc hqs.1.le (by linarith))).intervalIntegrable_of_Icc hqs_lt_δ.le
      have h2 : IntervalIntegrable (fun q => (g q - g q_lo) * W_of n q) volume (q_lo + δ) q_hi :=
        (hdiff_cont.mono (Icc_subset_Icc (by linarith) le_rfl)).intervalIntegrable_of_Icc (by linarith)
      rw [intervalIntegral.integral_add_adjacent_intervals h1 h2]
      congr 1; ext q; ring
    have hW_nn : ∀ q ∈ Icc q_lo q_hi, 0 ≤ W_of n q := fun q hq => by
      unfold W_of
      have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
      have hn1 : 0 ≤ (n : ℝ) - 1 := by linarith
      have : 0 ≤ 1 - q := by linarith [hq.2, hq_hi1]
      positivity
    -- Bound part A on [qs, q_lo + δ]
    have hpartA : |∫ q in qs..(q_lo + δ), (g q - g q_lo) * W_of n q| / A4 ^ n ≤ ε / 4 := by
      have hi_A : IntervalIntegrable (fun q => (g q - g q_lo) * W_of n q) volume qs (q_lo + δ) :=
        (hdiff_cont.mono (Icc_subset_Icc hqs.1.le (by linarith))).intervalIntegrable_of_Icc hqs_lt_δ.le
      have hle1 : |∫ q in qs..(q_lo + δ), (g q - g q_lo) * W_of n q| ≤
          ∫ q in qs..(q_lo + δ), (ε * d / 4) * W_of n q := by
        calc |∫ q in qs..(q_lo + δ), (g q - g q_lo) * W_of n q|
            ≤ ∫ q in qs..(q_lo + δ), |(g q - g q_lo) * W_of n q| := by
              have h := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
                (f := fun q => (g q - g q_lo) * W_of n q) hqs_lt_δ.le
              simpa only [Real.norm_eq_abs] using h
          _ ≤ ∫ q in qs..(q_lo + δ), (ε * d / 4) * W_of n q := by
              refine intervalIntegral.integral_mono_on hqs_lt_δ.le hi_A.norm
                ((continuous_const.mul hW_cont).intervalIntegrable _ _) ?_
              intro q hq
              have hq_in : q ∈ Icc q_lo q_hi := ⟨hqs.1.le.trans hq.1, hq.2.trans (by linarith)⟩
              rw [abs_mul, abs_of_nonneg (hW_nn q hq_in)]
              have hdist : dist q q_lo < δ₀ := by
                rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hq_in.1)]
                have : δ ≤ δ₀ / 2 := min_le_left _ _
                linarith [hq.2]
              have hgd : |g q - g q_lo| < ε * d / 4 := by
                simpa [Real.dist_eq] using hδ₀ hq_in hdist
              exact mul_le_mul_of_nonneg_right hgd.le (hW_nn q hq_in)
      have hle2 : ∫ q in qs..(q_lo + δ), W_of n q ≤ ∫ q in qs..q_hi, W_of n q := by
        have htail_nn : 0 ≤ ∫ q in (q_lo + δ)..q_hi, W_of n q :=
          intervalIntegral.integral_nonneg (by linarith) (fun q hq => hW_nn q ⟨by linarith [hq.1], hq.2⟩)
        rw [← intervalIntegral.integral_add_adjacent_intervals
          (hW_cont.intervalIntegrable qs (q_lo + δ)) (hW_cont.intervalIntegrable (q_lo + δ) q_hi)]
        linarith
      rw [intervalIntegral.integral_const_mul] at hle1
      calc |∫ q in qs..(q_lo + δ), (g q - g q_lo) * W_of n q| / A4 ^ n
          ≤ ((ε * d / 4) * (∫ q in qs..q_hi, W_of n q)) / A4 ^ n :=
            div_le_div_of_nonneg_right (hle1.trans (mul_le_mul_of_nonneg_left hle2 (by positivity)))
              (pow_nonneg hA4.le n)
        _ = (ε * d / 4) * M_n := by simp only [M_n]; ring
        _ ≤ (ε * d / 4) * (1 / d) := mul_le_mul_of_nonneg_left hMn_le (by positivity)
        _ = ε / 4 := by field_simp
    -- Bound part B on [q_lo + δ, q_hi]
    have hpartB : |∫ q in (q_lo + δ)..q_hi, (g q - g q_lo) * W_of n q| / A4 ^ n < ε / 4 := by
      have hi_B : IntervalIntegrable (fun q => (g q - g q_lo) * W_of n q) volume (q_lo + δ) q_hi :=
        (hdiff_cont.mono (Icc_subset_Icc (by linarith) le_rfl)).intervalIntegrable_of_Icc (by linarith)
      have hle1 : |∫ q in (q_lo + δ)..q_hi, (g q - g q_lo) * W_of n q| ≤
          (2 * M_g) * ∫ q in (q_lo + δ)..q_hi, W_of n q := by
        rw [← intervalIntegral.integral_const_mul]
        calc |∫ q in (q_lo + δ)..q_hi, (g q - g q_lo) * W_of n q|
            ≤ ∫ q in (q_lo + δ)..q_hi, |(g q - g q_lo) * W_of n q| := by
              have h := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
                (f := fun q => (g q - g q_lo) * W_of n q) (by linarith : q_lo + δ ≤ q_hi)
              simpa only [Real.norm_eq_abs] using h
          _ ≤ ∫ q in (q_lo + δ)..q_hi, (2 * M_g) * W_of n q := by
              refine intervalIntegral.integral_mono_on (by linarith) hi_B.norm
                ((continuous_const.mul hW_cont).intervalIntegrable _ _) ?_
              intro q hq
              have hq_in : q ∈ Icc q_lo q_hi := ⟨by linarith [hq.1], hq.2⟩
              rw [abs_mul, abs_of_nonneg (hW_nn q hq_in)]
              have hdiff_le : |g q - g q_lo| ≤ 2 * M_g := by
                calc |g q - g q_lo| ≤ |g q| + |g q_lo| := abs_sub _ _
                  _ ≤ M_g + M_g := add_le_add (hg_bound q hq_in) (hg_bound q_lo (left_mem_Icc.mpr hq_lt.le))
                  _ = 2 * M_g := by ring
              exact mul_le_mul_of_nonneg_right hdiff_le (hW_nn q hq_in)
      have hW_tail : ∫ q in (q_lo + δ)..q_hi, W_of n q ≤ (n : ℝ) * (A4 - δ) ^ (n - 1) := by
        have hw : ∫ q in (q_lo + δ)..q_hi, W_of n q =
            ((n : ℝ) * ((n : ℝ) - 1)) * ∫ q in (q_lo + δ)..q_hi, (1 - q) ^ (n - 2) := by
          rw [← intervalIntegral.integral_const_mul]; rfl
        rw [hw, integral_one_sub_pow hn2 (q_lo + δ) q_hi]
        have hn1 : ((n : ℝ) - 1) ≠ 0 := by
          have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
          linarith
        have heq : (n : ℝ) * ((n : ℝ) - 1) * (((1 - (q_lo + δ)) ^ (n - 1) - (1 - q_hi) ^ (n - 1)) / ((n : ℝ) - 1)) =
            (n : ℝ) * ((A4 - δ) ^ (n - 1) - A1 ^ (n - 1)) := by
          field_simp; simp only [A4, A1]; ring
        rw [heq]
        have : 0 ≤ (n : ℝ) * A1 ^ (n - 1) := by positivity
        linarith
      have h2 := hN2 n hn2'
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h2
      have hA4pow : A4 ^ n = A4 * A4 ^ (n - 1) := by
        conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ n), pow_succ']
      calc |∫ q in (q_lo + δ)..q_hi, (g q - g q_lo) * W_of n q| / A4 ^ n
          ≤ ((2 * M_g) * ((n : ℝ) * (A4 - δ) ^ (n - 1))) / A4 ^ n :=
            div_le_div_of_nonneg_right (hle1.trans (mul_le_mul_of_nonneg_left hW_tail (by positivity)))
              (pow_nonneg hA4.le n)
        _ = (2 * M_g / A4) * ((n : ℝ) * c_tail ^ (n - 1)) := by
            simp only [c_tail]; rw [div_pow, hA4pow]
            have : A4 ^ (n - 1) ≠ 0 := (pow_pos hA4 (n - 1)).ne'
            field_simp
        _ < ε / 4 := h2
    rw [Real.dist_eq]
    have hsplit_abs : |(∫ q in qs..q_hi, g q * W_of n q) / A4 ^ n - g q_lo * M_n| < ε / 2 := by
      rw [hsplit_g, add_div]
      calc |(∫ q in qs..(q_lo + δ), (g q - g q_lo) * W_of n q) / A4 ^ n +
              (∫ q in (q_lo + δ)..q_hi, (g q - g q_lo) * W_of n q) / A4 ^ n|
          ≤ |(∫ q in qs..(q_lo + δ), (g q - g q_lo) * W_of n q) / A4 ^ n| +
            |(∫ q in (q_lo + δ)..q_hi, (g q - g q_lo) * W_of n q) / A4 ^ n| := abs_add_le _ _
        _ = |∫ q in qs..(q_lo + δ), (g q - g q_lo) * W_of n q| / A4 ^ n +
            |∫ q in (q_lo + δ)..q_hi, (g q - g q_lo) * W_of n q| / A4 ^ n := by
            rw [abs_div, abs_div, abs_of_pos (pow_pos hA4 n)]
        _ < ε / 4 + ε / 4 := add_lt_add_of_le_of_lt hpartA hpartB
        _ = ε / 2 := by ring
    calc |(∫ q in qs..q_hi, g q * W_of n q) / A4 ^ n - g q_lo / d|
        = |((∫ q in qs..q_hi, g q * W_of n q) / A4 ^ n - g q_lo * M_n) +
            (g q_lo * M_n - g q_lo / d)| := by ring_nf
      _ ≤ |(∫ q in qs..q_hi, g q * W_of n q) / A4 ^ n - g q_lo * M_n| +
            |g q_lo * M_n - g q_lo / d| := abs_add_le _ _
      _ < ε / 2 + ε / 4 := add_lt_add hsplit_abs hMn_close
      _ < ε := by linarith
  -- Add the two limits
  have hsum := hlim1.add hlim2
  have hfun_eq : (fun n : ℕ => singleBandGainOf M.m n inv.P q_lo q_hi / (1 - q_lo) ^ n) =
      fun n : ℕ =>
        (∫ q in q_lo..(qStar n q_lo q_hi),
          (cournotRevOf M.m inv.P q_lo q - cournotRevOf M.m inv.P q q) * W_of n q) / A4 ^ n +
        (∫ q in (qStar n q_lo q_hi)..q_hi, g q * W_of n q) / A4 ^ n := by
    ext n; unfold singleBandGainOf; simp only [A4, g, add_div]
  have hlim_eq : -c1 + g q_lo / d = J_secant M.m inv.P P' q_lo q_hi := by
    unfold J_secant; simp only [c1, g, d]; ring
  rw [hfun_eq, ← hlim_eq]
  exact hsum

/-- **Proposition C.2(ii) (Tangent Equivalence and Narrow-Band `E ≤ 2m` Condition)**:
1. `J(q_lo, q_hi) ≤ 0` iff `Π(q_hi, q_lo) ≤ Π(q_lo, q_lo) + ∂_t Π(q_lo, q_lo) * (q_hi - q_lo)`.
2. Under `M : SmoothMarket`, at `v ∈ (a, 1)` with `q = (1 - F(v)) / m`,
   `∂_{tt}Π(q, q) = P'(mq) * (2 - E(v) / m)`, and as `d ↓ 0`,
   `J(q, q + d) = (1/2) ∂_{tt}Π(q, q) * d + o(d)`.
3. Consequently, `J(q, q + d) ≤ 0` for all small `d > 0` implies `E(v) ≤ 2m`, while `E(v) > 2m`
   implies `J(q, q + d) > 0` for all sufficiently small `d > 0`. -/
theorem propC2_narrow_band_2m (M : SmoothMarket) (inv : M.toMarket.InverseDemand)
    {v : ℝ} (hv : v ∈ Ioo M.a 1) :
    let q := (1 - M.F v) / (M.m : ℝ)
    let P' := invDemandDeriv M.toMarket inv
    let P'' := invDemandDeriv2 M inv
    -- (1) Tangent equivalence
    (∀ q_lo q_hi : ℝ, q_lo < q_hi →
      (J_secant M.m inv.P P' q_lo q_hi ≤ 0 ↔
        cournotRevOf M.m inv.P q_hi q_lo ≤
          cournotRevOf M.m inv.P q_lo q_lo + d_t_Pi M.m inv.P P' q_lo q_lo * (q_hi - q_lo))) ∧
    -- (2) Curvature identity for ∂_{tt}Π
    (d_tt_Pi M.m P' P'' q q = P' ((M.m : ℝ) * q) * (2 - curvatureE M v / (M.m : ℝ))) ∧
    -- (3) Narrow-band expansion J(q, q + d) = (1/2) ∂_{tt}Π(q, q) d + o(d)
    (∀ ε > 0, ∃ δ > 0, ∀ d ∈ Ioo (0 : ℝ) δ,
      |J_secant M.m inv.P P' q (q + d) - (1 / 2 : ℝ) * d_tt_Pi M.m P' P'' q q * d| ≤ ε * d) ∧
    -- (4) E ≤ 2m necessary for fixed narrow bands, and E > 2m implies J > 0 for small d
    ((∃ δ > 0, ∀ d ∈ Ioo (0 : ℝ) δ, J_secant M.m inv.P P' q (q + d) ≤ 0) →
      curvatureE M v ≤ 2 * (M.m : ℝ)) ∧
    (2 * (M.m : ℝ) < curvatureE M v →
      ∃ δ > 0, ∀ d ∈ Ioo (0 : ℝ) δ, 0 < J_secant M.m inv.P P' q (q + d)) := by
  intro q P' P''
  have hmpos : (0 : ℝ) < M.m := M.toMarket.m_pos_real
  have hmq : (M.m : ℝ) * q = 1 - M.F v := mul_div_cancel₀ _ hmpos.ne'
  have hFv : M.F v ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · rw [← M.hF_a]; exact M.toMarket.F_strictMonoOn (left_mem_Icc.mpr M.ha1.le) (Ioo_subset_Icc_self hv) hv.1
    · rw [← M.hF_1]; exact M.toMarket.F_strictMonoOn (Ioo_subset_Icc_self hv) (right_mem_Icc.mpr M.ha1.le) hv.2
  have hmq_mem : (M.m : ℝ) * q ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hFv.2], by linarith [hFv.1]⟩
  have hPmq : inv.P ((M.m : ℝ) * q) = v := by
    rw [hmq]; exact inv.hP_left v (Ioo_subset_Icc_self hv)
  have hfpos : 0 < M.f v := M.hf_pos v (Ioo_subset_Icc_self hv)
  have hP'_neg : P' ((M.m : ℝ) * q) < 0 := by
    simp only [P', invDemandDeriv, hPmq]; exact div_neg_of_neg_of_pos (by norm_num) hfpos
  -- (1) Tangent equivalence
  have h1 : ∀ q_lo q_hi : ℝ, q_lo < q_hi →
      (J_secant M.m inv.P P' q_lo q_hi ≤ 0 ↔
        cournotRevOf M.m inv.P q_hi q_lo ≤
          cournotRevOf M.m inv.P q_lo q_lo + d_t_Pi M.m inv.P P' q_lo q_lo * (q_hi - q_lo)) := by
    intro q_lo q_hi hlt
    unfold J_secant
    rw [sub_nonpos, div_le_iff₀ (sub_pos.mpr hlt)]
    constructor <;> intro h <;> linarith
  -- (2) Curvature identity for ∂_{tt}Π
  have h2 : d_tt_Pi M.m P' P'' q q = P' ((M.m : ℝ) * q) * (2 - curvatureE M v / (M.m : ℝ)) := by
    unfold d_tt_Pi curvatureE
    rw [show q + ((M.m : ℝ) - 1) * q = (M.m : ℝ) * q by ring]
    simp only [P', P'', invDemandDeriv, invDemandDeriv2, hPmq]
    have hq_def : q = (1 - M.F v) / (M.m : ℝ) := rfl
    rw [hq_def]
    have hfne : M.f v ≠ 0 := hfpos.ne'
    have hmne : (M.m : ℝ) ≠ 0 := hmpos.ne'
    field_simp
    ring
  -- (3) Narrow-band expansion
  have h3 : ∀ ε > 0, ∃ δ > 0, ∀ d ∈ Ioo (0 : ℝ) δ,
      |J_secant M.m inv.P P' q (q + d) - (1 / 2 : ℝ) * d_tt_Pi M.m P' P'' q q * d| ≤ ε * d := by
    intro ε hε
    set A_tt := d_tt_Pi M.m P' P'' q q
    have hP'_at : ContinuousAt P' (q + ((M.m : ℝ) - 1) * q) := by
      rw [show q + ((M.m : ℝ) - 1) * q = (M.m : ℝ) * q by ring]
      exact (invDemandDeriv_continuousOn M.toMarket inv).continuousAt (Icc_mem_nhds hmq_mem.1 hmq_mem.2)
    have hP''_at : ContinuousAt P'' (q + ((M.m : ℝ) - 1) * q) := by
      rw [show q + ((M.m : ℝ) - 1) * q = (M.m : ℝ) * q by ring]
      exact (invDemandDeriv2_continuousOn M inv).continuousAt (Icc_mem_nhds hmq_mem.1 hmq_mem.2)
    have hlin_u : ContinuousAt (fun u : ℝ => u + ((M.m : ℝ) - 1) * q) q :=
      continuousAt_id.add continuousAt_const
    have htt_cont : ContinuousAt (fun u : ℝ => d_tt_Pi M.m P' P'' u q) q := by
      unfold d_tt_Pi
      exact (continuousAt_const.mul (ContinuousAt.comp (g := P') (f := fun u : ℝ => u + ((M.m : ℝ) - 1) * q) hP'_at hlin_u)).add
        (continuousAt_id.mul (ContinuousAt.comp (g := P'') (f := fun u : ℝ => u + ((M.m : ℝ) - 1) * q) hP''_at hlin_u))
    obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := Metric.continuousAt_iff.mp htt_cont (2 * ε) (by linarith)
    set δ := min δ₁ ((1 - (M.m : ℝ) * q) / 2)
    refine ⟨δ, lt_min hδ₁_pos (by linarith [hmq_mem.2]), ?_⟩
    intro d hd
    have hmem : ∀ u ∈ Icc q (q + d), u + ((M.m : ℝ) - 1) * q ∈ Ioo (0 : ℝ) 1 := by
      intro u hu
      have hδ_le : δ ≤ (1 - (M.m : ℝ) * q) / 2 := min_le_right _ _
      constructor
      · linarith [hu.1, hmq_mem.1]
      · linarith [hu.2, hd.2, hδ_le, hmq_mem.2]
    -- First FTC: ∂_t Π(s, q) - ∂_t Π(q, q) - A_tt*(s - q) = ∫ u in q..s, (d_tt_Pi u q - A_tt)
    have hdt_err : ∀ s ∈ Icc q (q + d),
        |d_t_Pi M.m inv.P P' s q - d_t_Pi M.m inv.P P' q q - A_tt * (s - q)| ≤ (2 * ε) * (s - q) := by
      intro s hs
      have hftc1 : d_t_Pi M.m inv.P P' s q - d_t_Pi M.m inv.P P' q q - A_tt * (s - q) =
          ∫ u in q..s, (d_tt_Pi M.m P' P'' u q - A_tt) := by
        have hderiv : ∀ u ∈ uIcc q s,
            HasDerivAt (fun x => d_t_Pi M.m inv.P P' x q - A_tt * x)
              (d_tt_Pi M.m P' P'' u q - A_tt) u := by
          intro u hu
          rw [uIcc_of_le hs.1] at hu
          exact (hasDerivAt_d_t_Pi_t M inv (hmem u ⟨hu.1, hu.2.trans hs.2⟩)).sub
            ((hasDerivAt_id u).const_mul A_tt |>.congr_deriv (mul_one A_tt))
        have hint : IntervalIntegrable (fun u => d_tt_Pi M.m P' P'' u q - A_tt) volume q s := by
          apply ContinuousOn.intervalIntegrable
          rw [uIcc_of_le hs.1]
          have hlin : ContinuousOn (fun u => u + ((M.m : ℝ) - 1) * q) (Icc q s) :=
            continuousOn_id.add continuousOn_const
          have hmap : MapsTo (fun u => u + ((M.m : ℝ) - 1) * q) (Icc q s) (Icc 0 1) :=
            fun u hu => Ioo_subset_Icc_self (hmem u ⟨hu.1, hu.2.trans hs.2⟩)
          exact ((continuousOn_const.mul ((invDemandDeriv_continuousOn M.toMarket inv).comp hlin hmap)).add
            (continuousOn_id.mul ((invDemandDeriv2_continuousOn M inv).comp hlin hmap))).sub continuousOn_const
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]; ring
      rw [hftc1]
      have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const (a := q) (b := s) (C := 2 * ε)
        (f := fun u => d_tt_Pi M.m P' P'' u q - A_tt) (by
          intro u hu
          rw [uIoc_of_le hs.1] at hu
          rw [Real.norm_eq_abs]
          have hdist : dist u q < δ₁ := by
            rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hu.1.le)]
            have hle : u - q ≤ d := by linarith [hu.2, hs.2]
            exact lt_of_le_of_lt hle (lt_of_lt_of_le hd.2 (min_le_left _ _))
          exact (by simpa [Real.dist_eq] using hδ₁ hdist : |d_tt_Pi M.m P' P'' u q - A_tt| < 2 * ε).le)
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hs.1)] at hnorm
      exact hnorm
    -- Second FTC: integrate s from q to q + d
    have hftc2 : cournotRevOf M.m inv.P (q + d) q - cournotRevOf M.m inv.P q q -
        d_t_Pi M.m inv.P P' q q * d - (1 / 2 : ℝ) * A_tt * d ^ 2 =
        ∫ s in q..(q + d), (d_t_Pi M.m inv.P P' s q - d_t_Pi M.m inv.P P' q q - A_tt * (s - q)) := by
      have hderiv : ∀ s ∈ uIcc q (q + d),
          HasDerivAt (fun x => cournotRevOf M.m inv.P x q -
            d_t_Pi M.m inv.P P' q q * x - (1 / 2 : ℝ) * A_tt * (x - q) ^ 2)
            (d_t_Pi M.m inv.P P' s q - d_t_Pi M.m inv.P P' q q - A_tt * (s - q)) s := by
        intro s hs
        rw [uIcc_of_le (by linarith [hd.1])] at hs
        have h1' : HasDerivAt (fun x => cournotRevOf M.m inv.P x q)
            (d_t_Pi M.m inv.P P' s q) s := hasDerivAt_cournotRev_t M.toMarket inv (hmem s hs)
        have h2' : HasDerivAt (fun x => d_t_Pi M.m inv.P P' q q * x)
            (d_t_Pi M.m inv.P P' q q * 1) s := (hasDerivAt_id s).const_mul _
        have h3' : HasDerivAt (fun x => (1 / 2 : ℝ) * A_tt * (x - q) ^ 2)
            ((1 / 2 : ℝ) * A_tt * (((2 : ℕ) : ℝ) * (s - q) ^ (2 - 1) * 1)) s :=
          (((hasDerivAt_id s).sub_const q).pow 2).const_mul _
        refine ((h1'.sub h2').sub h3').congr_deriv ?_
        norm_num; ring
      have hint : IntervalIntegrable (fun s => d_t_Pi M.m inv.P P' s q -
          d_t_Pi M.m inv.P P' q q - A_tt * (s - q)) volume q (q + d) := by
        apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le (by linarith [hd.1])]
        have hlin : ContinuousOn (fun s => s + ((M.m : ℝ) - 1) * q) (Icc q (q + d)) :=
          continuousOn_id.add continuousOn_const
        have hmap : MapsTo (fun s => s + ((M.m : ℝ) - 1) * q) (Icc q (q + d)) (Icc 0 1) :=
          fun s hs => Ioo_subset_Icc_self (hmem s hs)
        exact (((inv.hP_cont.comp hlin hmap).add
          (continuousOn_id.mul ((invDemandDeriv_continuousOn M.toMarket inv).comp hlin hmap))).sub
            continuousOn_const).sub (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]; ring
    have hint_lin : ∫ s in q..(q + d), (2 * ε) * (s - q) = ε * d ^ 2 := by
      have hderiv : ∀ s ∈ uIcc q (q + d),
          HasDerivAt (fun x => ε * (x - q) ^ 2) ((2 * ε) * (s - q)) s := by
        intro s _
        have h := (((hasDerivAt_id s).sub_const q).pow 2).const_mul ε
        refine h.congr_deriv ?_; norm_num; ring
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
        ((continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable _ _)]
      ring
    have hJ_eq : J_secant M.m inv.P P' q (q + d) - (1 / 2 : ℝ) * A_tt * d =
        (cournotRevOf M.m inv.P (q + d) q - cournotRevOf M.m inv.P q q -
          d_t_Pi M.m inv.P P' q q * d - (1 / 2 : ℝ) * A_tt * d ^ 2) / d := by
      unfold J_secant
      have hd_ne : d ≠ 0 := hd.1.ne'
      have : q + d - q = d := by ring
      rw [this]
      field_simp
    rw [hJ_eq, hftc2, abs_div, abs_of_pos hd.1, div_le_iff₀ hd.1]
    have hint_err : IntervalIntegrable (fun s => d_t_Pi M.m inv.P P' s q -
        d_t_Pi M.m inv.P P' q q - A_tt * (s - q)) volume q (q + d) := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le (by linarith [hd.1])]
      have hlin : ContinuousOn (fun s => s + ((M.m : ℝ) - 1) * q) (Icc q (q + d)) :=
        continuousOn_id.add continuousOn_const
      have hmap : MapsTo (fun s => s + ((M.m : ℝ) - 1) * q) (Icc q (q + d)) (Icc 0 1) :=
        fun s hs => Ioo_subset_Icc_self (hmem s hs)
      exact (((inv.hP_cont.comp hlin hmap).add
        (continuousOn_id.mul ((invDemandDeriv_continuousOn M.toMarket inv).comp hlin hmap))).sub
          continuousOn_const).sub (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))
    calc |∫ s in q..(q + d), (d_t_Pi M.m inv.P P' s q - d_t_Pi M.m inv.P P' q q - A_tt * (s - q))|
        ≤ ∫ s in q..(q + d), |d_t_Pi M.m inv.P P' s q - d_t_Pi M.m inv.P P' q q - A_tt * (s - q)| := by
          have h := intervalIntegral.norm_integral_le_integral_norm (a := q) (b := q + d) (μ := volume)
            (f := fun s => d_t_Pi M.m inv.P P' s q - d_t_Pi M.m inv.P P' q q - A_tt * (s - q))
            (by linarith [hd.1])
          simpa only [Real.norm_eq_abs] using h
      _ ≤ ∫ s in q..(q + d), (2 * ε) * (s - q) :=
          intervalIntegral.integral_mono_on (by linarith [hd.1]) hint_err.norm
            ((continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable _ _) hdt_err
      _ = ε * d ^ 2 := hint_lin
      _ = ε * d * d := by ring
  -- (4) E ≤ 2m necessary and E > 2m sufficient for J > 0
  have h4a : (∃ δ > 0, ∀ d ∈ Ioo (0 : ℝ) δ, J_secant M.m inv.P P' q (q + d) ≤ 0) →
      curvatureE M v ≤ 2 * (M.m : ℝ) := by
    rintro ⟨δ₀, hδ₀_pos, hJ_le⟩
    by_contra hgt
    push Not at hgt
    have htt_pos : 0 < d_tt_Pi M.m P' P'' q q := by
      rw [h2]
      have hneg : 2 - curvatureE M v / (M.m : ℝ) < 0 := by
        have : 2 < curvatureE M v / (M.m : ℝ) := (lt_div_iff₀ hmpos).mpr (by linarith)
        linarith
      exact mul_pos_of_neg_of_neg hP'_neg hneg
    obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := h3 ((1 / 4 : ℝ) * d_tt_Pi M.m P' P'' q q) (by linarith)
    set d := min δ₀ δ₁ / 2
    have hd0 : 0 < d := by positivity
    have hd_in0 : d ∈ Ioo (0 : ℝ) δ₀ := ⟨hd0, by simp only [d]; linarith [min_le_left δ₀ δ₁]⟩
    have hd_in1 : d ∈ Ioo (0 : ℝ) δ₁ := ⟨hd0, by simp only [d]; linarith [min_le_right δ₀ δ₁]⟩
    have hlo := (abs_le.mp (hδ₁ d hd_in1)).1
    have hle := hJ_le d hd_in0
    nlinarith
  have h4b : 2 * (M.m : ℝ) < curvatureE M v →
      ∃ δ > 0, ∀ d ∈ Ioo (0 : ℝ) δ, 0 < J_secant M.m inv.P P' q (q + d) := by
    intro hgt
    have htt_pos : 0 < d_tt_Pi M.m P' P'' q q := by
      rw [h2]
      have hneg : 2 - curvatureE M v / (M.m : ℝ) < 0 := by
        have : 2 < curvatureE M v / (M.m : ℝ) := (lt_div_iff₀ hmpos).mpr (by linarith)
        linarith
      exact mul_pos_of_neg_of_neg hP'_neg hneg
    obtain ⟨δ, hδ_pos, hδ⟩ := h3 ((1 / 4 : ℝ) * d_tt_Pi M.m P' P'' q q) (by linarith)
    refine ⟨δ, hδ_pos, fun d hd => ?_⟩
    have hlo := (abs_le.mp (hδ d hd)).1
    nlinarith [hd.1]
  exact ⟨h1, h2, h3, h4a, h4b⟩

/-! ### Proposition C.2(iii) and Theorem 5(ii): `C¹` Covered-Market Counterexample for Any `X > m + 1` -/

/-- Auxiliary function `φ_X(u) = u(u + m - 1)^(1 - X) - m^(1 - X) u + (X - 1) m^(-X) (u - 1)`
from Appendix C, Proposition C.2(iii). -/
noncomputable def phiX (m : ℕ) (X u : ℝ) : ℝ :=
  u * (u + (m : ℝ) - 1) ^ (1 - X) - (m : ℝ) ^ (1 - X) * u +
    (X - 1) * (m : ℝ) ^ (-X) * (u - 1)

private lemma exists_u_phiX_pos {m : ℕ} (hm : 2 ≤ m) {X : ℝ} (hX : (m : ℝ) + 1 < X) :
    ∃ u : ℝ, 1 < u ∧ 0 < phiX m X u := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hgap : 0 < X - 1 - (m : ℝ) := by linarith
  have hX1 : 0 < X - 1 := by linarith
  set u : ℝ := (X - 1) / (X - 1 - (m : ℝ)) + 1
  have hu1 : 1 < u := by
    simp only [u]; linarith [div_pos hX1 hgap]
  refine ⟨u, hu1, ?_⟩
  unfold phiX
  have hm_pow : (m : ℝ) ^ (1 - X) = (m : ℝ) * (m : ℝ) ^ (-X) := by
    rw [show (1 - X : ℝ) = 1 + (-X) by ring, Real.rpow_add hmpos, Real.rpow_one]
  have hterm1 : 0 < u * (u + (m : ℝ) - 1) ^ (1 - X) := by
    have h1 : 0 < u := by linarith
    have h2 : 0 < u + (m : ℝ) - 1 := by linarith
    exact mul_pos h1 (Real.rpow_pos_of_pos h2 _)
  have hterm2 : -(m : ℝ) ^ (1 - X) * u + (X - 1) * (m : ℝ) ^ (-X) * (u - 1) =
      ((X - 1 - (m : ℝ)) * u - (X - 1)) * (m : ℝ) ^ (-X) := by
    rw [hm_pow]; ring
  have hbr_pos : 0 < (X - 1 - (m : ℝ)) * u - (X - 1) := by
    simp only [u]
    have hmul : (X - 1 - (m : ℝ)) * ((X - 1) / (X - 1 - (m : ℝ))) = X - 1 :=
      mul_div_cancel₀ _ hgap.ne'
    have heq : (X - 1 - (m : ℝ)) * ((X - 1) / (X - 1 - (m : ℝ)) + 1) - (X - 1) =
        X - 1 - (m : ℝ) := by
      rw [mul_add, hmul]; ring
    rw [heq]; exact hgap
  have hterm2_pos : 0 < -(m : ℝ) ^ (1 - X) * u + (X - 1) * (m : ℝ) ^ (-X) * (u - 1) := by
    rw [hterm2]
    exact mul_pos hbr_pos (Real.rpow_pos_of_pos hmpos _)
  linarith

/-- Helper: invert any strictly decreasing `C²` inverse demand `P : [0, 1] → [a, 1]` into a
`SmoothMarket` together with its `InverseDemand`. -/
private lemma smoothMarket_of_invDemand (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (P P' P'' : ℝ → ℝ) (hP0 : P 0 = 1) (hP1_pos : 0 < P 1) (hP1_lt1 : P 1 < 1)
    (hP_deriv : ∀ z : ℝ, HasDerivAt P (P' z) z)
    (hP'_deriv : ∀ z : ℝ, HasDerivAt P' (P'' z) z)
    (hP'_neg : ∀ z ∈ Icc (0 : ℝ) 1, P' z < 0)
    (hP''_cont : ContinuousOn P'' (Icc 0 1)) :
    ∃ (M : SmoothMarket) (inv : M.toMarket.InverseDemand),
      M.m = m ∧ M.n = n ∧ M.a = P 1 ∧
      inv.P = P ∧
      (∀ z ∈ Icc (0 : ℝ) 1, M.f (P z) = -1 / P' z) ∧
      (∀ z ∈ Icc (0 : ℝ) 1, M.f' (P z) = P'' z / (P' z) ^ 3) ∧
      (∀ z ∈ Icc (0 : ℝ) 1, curvatureE M (P z) = -z * P'' z / P' z) := by
  set a := P 1
  have hP_cont : Continuous P := continuous_iff_continuousAt.mpr fun z => (hP_deriv z).continuousAt
  have hP'_cont : Continuous P' := continuous_iff_continuousAt.mpr fun z => (hP'_deriv z).continuousAt
  -- Strict antitonicity of P on [0, 1]
  have hP_anti : StrictAntiOn P (Icc 0 1) := by
    intro x hx y hy hxy
    have hcont : ContinuousOn P (Icc x y) := hP_cont.continuousOn
    have hdiff : DifferentiableOn ℝ P (Ioo x y) := fun z _ => (hP_deriv z).differentiableAt.differentiableWithinAt
    obtain ⟨c, hc, hslope⟩ := exists_deriv_eq_slope P hxy hcont hdiff
    have hc_in : c ∈ Icc (0 : ℝ) 1 := ⟨hx.1.trans hc.1.le, hc.2.le.trans hy.2⟩
    have hneg : deriv P c < 0 := by
      rw [(hP_deriv c).deriv]; exact hP'_neg c hc_in
    rw [hslope, div_neg_iff] at hneg
    rcases hneg with ⟨_, h2⟩ | ⟨h1, _⟩
    · linarith
    · linarith
  -- Surjectivity of P on [0, 1] onto [a, 1]
  have hsurj : ∀ v ∈ Icc a 1, ∃ z ∈ Icc (0 : ℝ) 1, P z = v := by
    intro v hv
    have hivt := intermediate_value_Icc' (zero_le_one : (0 : ℝ) ≤ 1) hP_cont.continuousOn
    have hmem : v ∈ Icc (P 1) (P 0) := by rwa [hP0]
    exact hivt hmem
  -- Define inverse Q : ℝ → ℝ
  let Q : ℝ → ℝ := fun v =>
    if hv : v ∈ Icc a 1 then (hsurj v hv).choose else if v < a then 1 else 0
  have hQ_mem : ∀ v ∈ Icc a 1, Q v ∈ Icc (0 : ℝ) 1 := by
    intro v hv; simp only [Q, hv, ↓reduceDIte]; exact (hsurj v hv).choose_spec.1
  have hPQ : ∀ v ∈ Icc a 1, P (Q v) = v := by
    intro v hv; simp only [Q, hv, ↓reduceDIte]; exact (hsurj v hv).choose_spec.2
  have hQP : ∀ z ∈ Icc (0 : ℝ) 1, Q (P z) = z := by
    intro z hz
    have hPz : P z ∈ Icc a 1 := by
      constructor
      · exact hP_anti.antitoneOn hz (right_mem_Icc.mpr zero_le_one) hz.2
      · rw [← hP0]; exact hP_anti.antitoneOn (left_mem_Icc.mpr zero_le_one) hz hz.1
    exact hP_anti.injOn (hQ_mem (P z) hPz) hz (hPQ (P z) hPz)
  have hQa : Q a = 1 := by simpa [a] using hQP 1 (right_mem_Icc.mpr zero_le_one)
  have hQ1 : Q 1 = 0 := by simpa [hP0] using hQP 0 (left_mem_Icc.mpr zero_le_one)
  have hQ_below : ∀ v ≤ a, Q v = 1 := by
    intro v hv
    by_cases hva : v = a
    · subst hva; exact hQa
    · have hlt : v < a := lt_of_le_of_ne hv hva
      have hnot : v ∉ Icc a 1 := fun h => by linarith [h.1]
      simp only [Q, hnot, ↓reduceDIte, hlt, ↓reduceIte]
  have hQ_anti : StrictAntiOn Q (Icc a 1) := by
    intro u hu v hv huv
    by_contra hle
    push Not at hle
    have := hP_anti.antitoneOn (hQ_mem u hu) (hQ_mem v hv) hle
    rw [hPQ u hu, hPQ v hv] at this
    linarith
  -- Continuity of Q on [a, 1]
  have hQ_cont : ContinuousOn Q (Icc a 1) := by
    intro v hv
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    set z := Q v
    have hz : z ∈ Icc (0 : ℝ) 1 := hQ_mem v hv
    set z_lo := max 0 (z - ε / 2)
    set z_hi := min 1 (z + ε / 2)
    have hz_lo_mem : z_lo ∈ Icc (0 : ℝ) 1 := ⟨le_max_left _ _, max_le zero_le_one (by linarith [hz.2])⟩
    have hz_hi_mem : z_hi ∈ Icc (0 : ℝ) 1 := ⟨le_min zero_le_one (by linarith [hz.1]), min_le_left _ _⟩
    set δ_up : ℝ := if z = 0 then 1 else P z_lo - v
    set δ_dn : ℝ := if z = 1 then 1 else v - P z_hi
    have hδ_up_pos : 0 < δ_up := by
      by_cases hz0 : z = 0
      · simp only [δ_up, hz0, ↓reduceIte]; norm_num
      · simp only [δ_up, hz0, ↓reduceIte]
        have hlt : z_lo < z := max_lt (lt_of_le_of_ne hz.1 (Ne.symm hz0)) (by linarith)
        have := hP_anti hz_lo_mem hz hlt
        rw [hPQ v hv] at this; linarith
    have hδ_dn_pos : 0 < δ_dn := by
      by_cases hz1 : z = 1
      · simp only [δ_dn, hz1, ↓reduceIte]; norm_num
      · simp only [δ_dn, hz1, ↓reduceIte]
        have hlt : z < z_hi := lt_min (lt_of_le_of_ne hz.2 hz1) (by linarith)
        have := hP_anti hz hz_hi_mem hlt
        rw [hPQ v hv] at this; linarith
    refine ⟨min δ_up δ_dn, lt_min hδ_up_pos hδ_dn_pos, ?_⟩
    intro u hu hdist
    rw [Real.dist_eq] at hdist ⊢
    have hQu_ge : z_lo ≤ Q u := by
      by_cases hz0 : z = 0
      · have : z_lo = 0 := max_eq_left (by linarith)
        rw [this]; exact (hQ_mem u hu).1
      · have hup : u < P z_lo := by
          have : u - v < δ_up := lt_of_lt_of_le (abs_lt.mp hdist).2 (min_le_left _ _)
          simp only [δ_up, hz0, ↓reduceIte] at this; linarith
        have hP_lo_in : P z_lo ∈ Icc a 1 :=
          ⟨hP_anti.antitoneOn hz_lo_mem (right_mem_Icc.mpr zero_le_one) hz_lo_mem.2,
           by rw [← hP0]; exact hP_anti.antitoneOn (left_mem_Icc.mpr zero_le_one) hz_lo_mem hz_lo_mem.1⟩
        have := hQ_anti.antitoneOn hu hP_lo_in hup.le
        rwa [hQP z_lo hz_lo_mem] at this
    have hQu_le : Q u ≤ z_hi := by
      by_cases hz1 : z = 1
      · have : z_hi = 1 := min_eq_left (by linarith)
        rw [this]; exact (hQ_mem u hu).2
      · have hdn : P z_hi < u := by
          have : -(δ_dn) < u - v := lt_of_le_of_lt (neg_le_neg (min_le_right _ _)) (abs_lt.mp hdist).1
          simp only [δ_dn, hz1, ↓reduceIte] at this; linarith
        have hP_hi_in : P z_hi ∈ Icc a 1 :=
          ⟨hP_anti.antitoneOn hz_hi_mem (right_mem_Icc.mpr zero_le_one) hz_hi_mem.2,
           by rw [← hP0]; exact hP_anti.antitoneOn (left_mem_Icc.mpr zero_le_one) hz_hi_mem hz_hi_mem.1⟩
        have := hQ_anti.antitoneOn hP_hi_in hu hdn.le
        rwa [hQP z_hi hz_hi_mem] at this
    have h1 : z - ε / 2 ≤ z_lo := le_max_right _ _
    have h2 : z_hi ≤ z + ε / 2 := min_le_right _ _
    rw [abs_lt]; constructor <;> linarith
  -- Derivative of Q within [a, 1] via slope inversion
  have hQ_deriv_within : ∀ v ∈ Icc a 1, HasDerivWithinAt Q (1 / P' (Q v)) (Icc a 1) v := by
    intro v hv
    rw [hasDerivWithinAt_iff_tendsto_slope]
    have hP'_ne : P' (Q v) ≠ 0 := (hP'_neg (Q v) (hQ_mem v hv)).ne
    have hP_slope : Tendsto (slope P (Q v)) (𝓝[≠] (Q v)) (nhds (P' (Q v))) :=
      hasDerivAt_iff_tendsto_slope.mp (hP_deriv (Q v))
    have hQ_tendsto : Tendsto Q (𝓝[Icc a 1 \ {v}] v) (𝓝[≠] (Q v)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨(hQ_cont v hv).mono sdiff_subset, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with u hu
      intro heq
      have : u = v := hQ_anti.injOn hu.1 hv heq
      exact hu.2 this
    have hcomp : Tendsto (fun u => (slope P (Q v) (Q u))⁻¹) (𝓝[Icc a 1 \ {v}] v) (nhds ((P' (Q v))⁻¹)) :=
      (hP_slope.comp hQ_tendsto).inv₀ hP'_ne
    rw [one_div]
    refine hcomp.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with u hu
    simp only [slope_def_field, hPQ u hu.1, hPQ v hv, inv_div]
  have hQ_deriv_open : ∀ v ∈ Ioo a 1, HasDerivAt Q (1 / P' (Q v)) v :=
    fun v hv => (hQ_deriv_within v (Ioo_subset_Icc_self hv)).hasDerivAt (Icc_mem_nhds hv.1 hv.2)
  -- Define F, f, f'
  let F : ℝ → ℝ := fun v => 1 - Q v
  let f : ℝ → ℝ := fun v => if v < a then 0 else -1 / P' (Q v)
  let f' : ℝ → ℝ := fun v => P'' (Q v) / (P' (Q v)) ^ 3
  have hf_eq : ∀ v ∈ Icc a 1, f v = -1 / P' (Q v) := by
    intro v hv; simp only [f, not_lt.mpr hv.1, ↓reduceIte]
  have hf_pos : ∀ v ∈ Icc a 1, 0 < f v := by
    intro v hv
    rw [hf_eq v hv]
    exact div_pos_of_neg_of_neg (by norm_num) (hP'_neg (Q v) (hQ_mem v hv))
  have hf_cont : ContinuousOn f (Icc a 1) := by
    have hcont_rhs : ContinuousOn (fun v => -1 / P' (Q v)) (Icc a 1) := by
      refine ContinuousOn.div continuousOn_const (hP'_cont.comp_continuousOn hQ_cont) ?_
      intro v hv; exact (hP'_neg (Q v) (hQ_mem v hv)).ne
    exact hcont_rhs.congr hf_eq
  have hf'_cont : ContinuousOn f' (Icc a 1) := by
    refine ContinuousOn.div (hP''_cont.comp hQ_cont hQ_mem)
      ((hP'_cont.comp_continuousOn hQ_cont).pow 3) ?_
    intro v hv; exact pow_ne_zero 3 (hP'_neg (Q v) (hQ_mem v hv)).ne
  have hF_deriv_within : ∀ v ∈ Icc a 1, HasDerivWithinAt F (f v) (Icc a 1) v := by
    intro v hv
    rw [hf_eq v hv]
    have h := (hasDerivWithinAt_const v (Icc a 1) (1 : ℝ)).sub (hQ_deriv_within v hv)
    refine h.congr_deriv ?_; ring
  have hF_deriv_open : ∀ v ∈ Ioo a 1, HasDerivAt F (f v) v :=
    fun v hv => (hF_deriv_within v (Ioo_subset_Icc_self hv)).hasDerivAt (Icc_mem_nhds hv.1 hv.2)
  have hf_deriv_within : ∀ v ∈ Icc a 1, HasDerivWithinAt f (f' v) (Icc a 1) v := by
    intro v hv
    have hPQ_d : HasDerivWithinAt (fun u => P' (Q u)) (P'' (Q v) * (1 / P' (Q v))) (Icc a 1) v :=
      (hP'_deriv (Q v)).comp_hasDerivWithinAt v (hQ_deriv_within v hv)
    have hP'_ne : P' (Q v) ≠ 0 := (hP'_neg (Q v) (hQ_mem v hv)).ne
    have hdiv := (hasDerivWithinAt_const v (Icc a 1) (-1 : ℝ)).div hPQ_d hP'_ne
    have hdiv' : HasDerivWithinAt (fun u => -1 / P' (Q u)) (f' v) (Icc a 1) v := by
      refine hdiv.congr_deriv ?_
      simp only [f']
      field_simp
      ring
    exact hdiv'.congr hf_eq (hf_eq v hv)
  have hf_deriv_open : ∀ v ∈ Ioo a 1, HasDerivAt f (f' v) v :=
    fun v hv => (hf_deriv_within v (Ioo_subset_Icc_self hv)).hasDerivAt (Icc_mem_nhds hv.1 hv.2)
  let M : SmoothMarket := {
    m := m
    n := n
    hm := hm
    hn := hn
    a := a
    ha0 := hP1_pos.le
    ha1 := hP1_lt1
    F := F
    f := f
    f' := f'
    hF_a := by simp only [F, hQa, sub_self]
    hF_1 := by simp only [F, hQ1, sub_zero]
    hF_below := fun v hv => by simp only [F, hQ_below v hv, sub_self]
    hf_below := fun v hv => by simp only [f, hv, ↓reduceIte]
    hf_cont := hf_cont
    hf_pos := hf_pos
    hF_deriv_within := hF_deriv_within
    hF_deriv_open := hF_deriv_open
    hf'_cont := hf'_cont
    hf_deriv_within := hf_deriv_within
    hf_deriv_open := hf_deriv_open
  }
  have hP_mem_Icc : ∀ z ∈ Icc (0 : ℝ) 1, P z ∈ Icc a 1 := by
    intro z hz
    constructor
    · exact hP_anti.antitoneOn hz (right_mem_Icc.mpr zero_le_one) hz.2
    · rw [← hP0]; exact hP_anti.antitoneOn (left_mem_Icc.mpr zero_le_one) hz hz.1
  have hP_deriv_val : ∀ z ∈ Icc (0 : ℝ) 1, -1 / M.f (P z) = P' z := by
    intro z hz
    have hPz : P z ∈ Icc a 1 := hP_mem_Icc z hz
    change -1 / f (P z) = P' z
    rw [hf_eq (P z) hPz, hQP z hz]
    have hne : P' z ≠ 0 := (hP'_neg z hz).ne
    field_simp
  let inv : M.toMarket.InverseDemand := {
    P := P
    hP_mem := hP_mem_Icc
    hP_right := fun z hz => by change 1 - Q (P z) = 1 - z; rw [hQP z hz]
    hP_left := fun v hv => by
      change P (1 - (1 - Q v)) = v
      rw [sub_sub_cancel]; exact hPQ v hv
    hP_zero := hP0
    hP_one := rfl
    hP_cont := hP_cont.continuousOn
    hP_strictAnti := hP_anti
    hP_deriv_open := fun z hz => by
      rw [hP_deriv_val z (Ioo_subset_Icc_self hz)]; exact hP_deriv z
    hP_deriv_within := fun z hz => by
      rw [hP_deriv_val z hz]; exact (hP_deriv z).hasDerivWithinAt
  }
  refine ⟨M, inv, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro z hz
    change f (P z) = -1 / P' z
    rw [hf_eq (P z) (hP_mem_Icc z hz), hQP z hz]
  · intro z hz
    change f' (P z) = P'' z / (P' z) ^ 3
    simp only [f', hQP z hz]
  · intro z hz
    unfold curvatureE
    have hF_val : M.F (P z) = 1 - z := inv.hP_right z hz
    have hf_val : M.f (P z) = -1 / P' z := by
      change f (P z) = -1 / P' z
      rw [hf_eq (P z) (hP_mem_Icc z hz), hQP z hz]
    have hf'_val : M.f' (P z) = P'' z / (P' z) ^ 3 := by
      change f' (P z) = P'' z / (P' z) ^ 3
      simp only [f', hQP z hz]
    rw [hF_val, hf_val, hf'_val]
    have hne : P' z ≠ 0 := (hP'_neg z hz).ne
    field_simp
    ring

/-- **Proposition C.2(iii) (`C¹` Covered-Market Counterexample for Any `X > m + 1`)**:
For every `m ≥ 2`, `n₀ ≥ 2`, and `X > m + 1`, there exists a covered-market `SmoothMarket` `M`
(with `M.m = m`, `M.n = n₀`, `M.a > 0`) and its `InverseDemand` `inv` satisfying:
1. `0 < M.toMarket.psi M.a` (positive Cournot marginal revenue at the bottom),
2. `curvatureE M v ∈ Icc 0 X` for all `v ∈ Icc M.a 1` (in particular `E ≤ X` everywhere), and
3. there exists an interior band `[v₁, v₄] ⊂ (M.a, 1)` with quantities `0 < q_lo < q_hi < 1 / m`
   such that `J(q_lo, q_hi) > 0`. -/
theorem propC2_covered_counterexample (m n₀ : ℕ) (hm : 2 ≤ m) (hn₀ : 2 ≤ n₀)
    {X : ℝ} (hX : (m : ℝ) + 1 < X) :
    ∃ (M : SmoothMarket) (inv : M.toMarket.InverseDemand) (q_lo q_hi : ℝ),
      M.m = m ∧ M.n = n₀ ∧ 0 < M.a ∧
      0 < M.toMarket.psi M.a ∧
      (∀ v ∈ Icc M.a 1, curvatureE M v ∈ Icc 0 X) ∧
      0 < q_lo ∧ q_lo < q_hi ∧ (m : ℝ) * q_hi < 1 ∧
      0 < J_secant m inv.P (invDemandDeriv M.toMarket inv) q_lo q_hi := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hXpos : 0 < X := by linarith
  have hX1 : 0 < X - 1 := by linarith
  obtain ⟨u, hu1, hphi_pos⟩ := exists_u_phiX_pos hm hX
  have hu_pos : 0 < u := by linarith
  set z₀ : ℝ := 1 / (2 * u)
  have hz₀_pos : 0 < z₀ := by positivity
  have huz₀ : u * z₀ = 1 / 2 := by simp only [z₀]; field_simp
  set z₁ : ℝ := ((u + (m : ℝ) - 1) / (m : ℝ)) * z₀
  have hz₀_lt_z₁ : z₀ < z₁ := by
    simp only [z₁]
    have h1 : (1 : ℝ) < (u + (m : ℝ) - 1) / (m : ℝ) := (one_lt_div hmpos).mpr (by linarith)
    nlinarith
  have hz₁_lt_half : z₁ < 1 / 2 := by
    rw [← huz₀]; simp only [z₁]
    have h1 : (u + (m : ℝ) - 1) / (m : ℝ) < u := by
      rw [div_lt_iff₀ hmpos]; nlinarith
    exact mul_lt_mul_of_pos_right h1 hz₀_pos
  have hz₁_lt1 : z₁ < 1 := by linarith
  have hz₀_lt1 : z₀ < 1 := hz₀_lt_z₁.trans hz₁_lt1
  -- Smoothly ramped curvature profile E_tilde(s) and continuous integrand g(s) = E_tilde(s) / max(z₀/2, s)
  let E_tilde : ℝ → ℝ := fun s => X * min 1 (max 0 ((s - z₀ / 2) / (z₀ / 2)))
  let g : ℝ → ℝ := fun s => E_tilde s / max (z₀ / 2) s
  have hE_mem : ∀ s : ℝ, E_tilde s ∈ Icc 0 X := by
    intro s
    have h0 : 0 ≤ min 1 (max 0 ((s - z₀ / 2) / (z₀ / 2))) := le_min zero_le_one (le_max_left _ _)
    have h1 : min 1 (max 0 ((s - z₀ / 2) / (z₀ / 2))) ≤ 1 := min_le_left _ _
    exact ⟨mul_nonneg hXpos.le h0, mul_le_of_le_one_right hXpos.le h1⟩
  have hE_lo : ∀ s ≤ z₀ / 2, E_tilde s = 0 := by
    intro s hs
    have hdiv : (s - z₀ / 2) / (z₀ / 2) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    simp only [E_tilde, max_eq_left hdiv, min_eq_right zero_le_one, mul_zero]
  have hE_hi : ∀ s ≥ z₀, E_tilde s = X := by
    intro s hs
    have hdiv : 1 ≤ (s - z₀ / 2) / (z₀ / 2) := by
      rw [one_le_div (by linarith)]; linarith
    have hmax : max 0 ((s - z₀ / 2) / (z₀ / 2)) = (s - z₀ / 2) / (z₀ / 2) := max_eq_right (by linarith)
    simp only [E_tilde, hmax, min_eq_left hdiv, mul_one]
  have hg_cont : Continuous g := by
    have hlin : Continuous (fun s : ℝ => (s - z₀ / 2) / (z₀ / 2)) :=
      (continuous_id.sub continuous_const).div_const (z₀ / 2)
    have hmax : Continuous (fun s : ℝ => max (0 : ℝ) ((s - z₀ / 2) / (z₀ / 2))) :=
      continuous_const.max hlin
    have hmin : Continuous (fun s : ℝ => min (1 : ℝ) (max (0 : ℝ) ((s - z₀ / 2) / (z₀ / 2)))) :=
      continuous_const.min hmax
    have hE_cont : Continuous E_tilde := continuous_const.mul hmin
    exact hE_cont.div (continuous_const.max continuous_id)
      (fun s => (lt_of_lt_of_le (by linarith : 0 < z₀ / 2) (le_max_left _ _)).ne')
  have hsg_eq : ∀ s : ℝ, 0 ≤ s → s * g s = E_tilde s := by
    intro s hs
    by_cases hle : s ≤ z₀ / 2
    · simp only [g, hE_lo s hle, zero_div, mul_zero]
    · push Not at hle
      simp only [g, max_eq_right hle.le]
      exact mul_div_cancel₀ _ (by linarith : s ≠ 0)
  have hg_hi : ∀ s ≥ z₀, g s = X / s := by
    intro s hs
    simp only [g, hE_hi s hs, max_eq_right (by linarith : z₀ / 2 ≤ s)]
  -- Define h(z) = exp(- ∫_{z₀}^z g(s) ds)
  let h : ℝ → ℝ := fun z => Real.exp (-(∫ s in z₀..z, g s))
  have hh_pos : ∀ z : ℝ, 0 < h z := fun z => Real.exp_pos _
  have hh_deriv : ∀ z : ℝ, HasDerivAt h (-g z * h z) z := by
    intro z
    have hint : HasDerivAt (fun x => ∫ s in z₀..x, g s) (g z) z :=
      intervalIntegral.integral_hasDerivAt_right (hg_cont.intervalIntegrable z₀ z)
        (hg_cont.stronglyMeasurableAtFilter volume (nhds z)) hg_cont.continuousAt
    have h1 : HasDerivAt (fun x => Real.exp (-(∫ s in z₀..x, g s)))
        (Real.exp (-(∫ s in z₀..z, g s)) * (-g z)) z := hint.neg.exp
    change HasDerivAt (fun x => Real.exp (-(∫ s in z₀..x, g s))) (-g z * h z) z
    refine h1.congr_deriv ?_
    simp only [h]; ring
  have hh_cont : Continuous h := continuous_iff_continuousAt.mpr fun z => (hh_deriv z).continuousAt
  -- Evaluate h on [z₀, ∞): h(z) = z₀^X * z^(-X)
  have hh_hi : ∀ z ≥ z₀, h z = z₀ ^ X * z ^ (-X) := by
    intro z hz
    have hlog_int : ∫ s in z₀..z, g s = X * (Real.log z - Real.log z₀) := by
      have hcongr : ∫ s in z₀..z, g s = ∫ s in z₀..z, X / s := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le hz] at hs
        exact hg_hi s hs.1
      rw [hcongr]
      have hderiv : ∀ s ∈ uIcc z₀ z, HasDerivAt (fun x => X * Real.log x) (X / s) s := by
        intro s hs
        rw [uIcc_of_le hz] at hs
        have hs_pos : 0 < s := lt_of_lt_of_le hz₀_pos hs.1
        have h1 := (Real.hasDerivAt_log hs_pos.ne').const_mul X
        refine h1.congr_deriv ?_; ring
      have hint : IntervalIntegrable (fun s => X / s) volume z₀ z := by
        apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le hz]
        exact ContinuousOn.div continuousOn_const continuousOn_id
          (fun s hs => (lt_of_lt_of_le hz₀_pos hs.1).ne')
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
      ring
    simp only [h, hlog_int]
    have hz_pos : 0 < z := lt_of_lt_of_le hz₀_pos hz
    rw [Real.rpow_def_of_pos hz₀_pos, Real.rpow_def_of_pos hz_pos, ← Real.exp_add]
    congr 1; ring
  have hh_z₀ : h z₀ = 1 := by simp only [h, intervalIntegral.integral_same, neg_zero, Real.exp_zero]
  -- Choose κ > 0 so that a = 1 - κ C₀ > 0 and ψ_m(a) = 1 - κ(C₀ + h(1)/m) > 0
  set C₀ : ℝ := ∫ s in (0 : ℝ)..1, h s
  have hC₀_pos : 0 < C₀ :=
    intervalIntegral.integral_pos zero_lt_one hh_cont.continuousOn
      (fun s _ => (hh_pos s).le) ⟨0, left_mem_Icc.mpr zero_le_one, hh_pos 0⟩
  set κ : ℝ := 1 / (2 * (C₀ + h 1 / (m : ℝ)))
  have hκ_pos : 0 < κ := by
    have : 0 < C₀ + h 1 / (m : ℝ) := add_pos hC₀_pos (div_pos (hh_pos 1) hmpos)
    positivity
  -- Define P, P', P''
  let P : ℝ → ℝ := fun z => 1 - κ * ∫ s in (0 : ℝ)..z, h s
  let P' : ℝ → ℝ := fun z => -κ * h z
  let P'' : ℝ → ℝ := fun z => κ * g z * h z
  have hP0 : P 0 = 1 := by simp [P]
  have hP1 : P 1 = 1 - κ * C₀ := rfl
  have hP1_pos : 0 < P 1 := by
    rw [hP1]
    have hden : 0 < C₀ + h 1 / (m : ℝ) := add_pos hC₀_pos (div_pos (hh_pos 1) hmpos)
    have h1 : κ * C₀ < 1 / 2 := by
      simp only [κ]
      have hmul : 1 / (2 * (C₀ + h 1 / (m : ℝ))) * C₀ = C₀ / (2 * (C₀ + h 1 / (m : ℝ))) := by ring
      rw [hmul, div_lt_iff₀ (by linarith)]
      have : 0 < h 1 / (m : ℝ) := div_pos (hh_pos 1) hmpos
      linarith
    linarith
  have hP1_lt1 : P 1 < 1 := by
    rw [hP1]; linarith [mul_pos hκ_pos hC₀_pos]
  have hP_deriv : ∀ z : ℝ, HasDerivAt P (P' z) z := by
    intro z
    have hint : HasDerivAt (fun x => ∫ s in (0 : ℝ)..x, h s) (h z) z :=
      intervalIntegral.integral_hasDerivAt_right (hh_cont.intervalIntegrable 0 z)
        (hh_cont.stronglyMeasurableAtFilter volume (nhds z)) hh_cont.continuousAt
    have h1 := (hasDerivAt_const z (1 : ℝ)).sub (hint.const_mul κ)
    refine h1.congr_deriv ?_
    simp only [P']; ring
  have hP'_deriv : ∀ z : ℝ, HasDerivAt P' (P'' z) z := by
    intro z
    have h1 := (hh_deriv z).const_mul (-κ)
    refine h1.congr_deriv ?_
    simp only [P'']; ring
  have hP'_neg : ∀ z ∈ Icc (0 : ℝ) 1, P' z < 0 := fun z _ => by
    simp only [P']; exact mul_neg_of_neg_of_pos (by linarith) (hh_pos z)
  have hP''_cont : ContinuousOn P'' (Icc 0 1) :=
    ((continuous_const.mul hg_cont).mul hh_cont).continuousOn
  -- Build SmoothMarket M and InverseDemand inv
  obtain ⟨M, inv, hMm, hMn, hMa, hinvP, hf_val, _, hE_val⟩ :=
    smoothMarket_of_invDemand m n₀ hm hn₀ P P' P'' hP0 hP1_pos hP1_lt1
      hP_deriv hP'_deriv hP'_neg hP''_cont
  -- Verify ψ_m(a) > 0
  have hpsi_a_pos : 0 < M.toMarket.psi M.a := by
    unfold Market.psi
    rw [M.hF_a, sub_zero, hMm, hMa, hf_val 1 (right_mem_Icc.mpr zero_le_one)]
    have hP'1_ne : P' 1 ≠ 0 := (hP'_neg 1 (right_mem_Icc.mpr zero_le_one)).ne
    have hdiv : 1 / ((m : ℝ) * (-1 / P' 1)) = -P' 1 / (m : ℝ) := by field_simp
    rw [hdiv]
    simp only [P', hP1]
    have hden : C₀ + h 1 / (m : ℝ) ≠ 0 := (add_pos hC₀_pos (div_pos (hh_pos 1) hmpos)).ne'
    have heq : 1 - κ * C₀ - -(-κ * h 1) / (m : ℝ) = 1 - κ * (C₀ + h 1 / (m : ℝ)) := by ring
    rw [heq]
    simp only [κ]
    have : 1 / (2 * (C₀ + h 1 / (m : ℝ))) * (C₀ + h 1 / (m : ℝ)) = 1 / 2 := by
      rw [one_div, mul_inv, mul_assoc, inv_mul_cancel₀ hden, mul_one, one_div]
    linarith
  -- Verify E(v) ∈ [0, X] for all v ∈ [a, 1]
  have hE_bound : ∀ v ∈ Icc M.a 1, curvatureE M v ∈ Icc 0 X := by
    intro v hv
    set z := 1 - M.F v
    have hz : z ∈ Icc (0 : ℝ) 1 := by
      have hFv := M.toMarket.F_mem_Icc hv
      exact ⟨by linarith [hFv.2], by linarith [hFv.1]⟩
    have hPz : P z = v := by
      rw [← hinvP]; exact inv.hP_left v hv
    rw [← hPz, hE_val z hz]
    have hneg_eq : -z * P'' z / P' z = z * g z := by
      simp only [P', P'']
      have hhne : h z ≠ 0 := (hh_pos z).ne'
      have hκne : κ ≠ 0 := hκ_pos.ne'
      field_simp
    rw [hneg_eq, hsg_eq z hz.1]
    exact hE_mem z
  -- Set q_lo = z₀ / m, q_hi = u * q_lo and compute J_secant > 0
  set q_lo : ℝ := z₀ / (m : ℝ)
  set q_hi : ℝ := u * q_lo
  have hq_lo_pos : 0 < q_lo := div_pos hz₀_pos hmpos
  have hq_lt : q_lo < q_hi := by simp only [q_hi]; nlinarith
  have hmq_lo : (m : ℝ) * q_lo = z₀ := mul_div_cancel₀ _ hmpos.ne'
  have hmq_hi : (m : ℝ) * q_hi < 1 := by
    have heq : (m : ℝ) * q_hi = u * z₀ := by simp only [q_hi, q_lo]; field_simp
    rw [heq, huz₀]; norm_num
  have hsum_q : q_hi + ((m : ℝ) - 1) * q_lo = z₁ := by
    simp only [q_hi, q_lo, z₁]; field_simp; ring
  -- Evaluate P z₁ - P z₀ explicitly
  have hP_diff : P z₁ - P z₀ = (κ * z₀ ^ X / (X - 1)) * (z₁ ^ (1 - X) - z₀ ^ (1 - X)) := by
    have hsub : P z₁ - P z₀ = -κ * ∫ s in z₀..z₁, h s := by
      simp only [P]
      have hadd := intervalIntegral.integral_add_adjacent_intervals
        (hh_cont.intervalIntegrable (μ := volume) 0 z₀)
        (hh_cont.intervalIntegrable (μ := volume) z₀ z₁)
      rw [← hadd]; ring
    rw [hsub]
    have hcongr : ∫ s in z₀..z₁, h s = ∫ s in z₀..z₁, z₀ ^ X * s ^ (-X) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hz₀_lt_z₁.le] at hs
      exact hh_hi s hs.1
    rw [hcongr]
    have hderiv : ∀ s ∈ uIcc z₀ z₁,
        HasDerivAt (fun x => (z₀ ^ X / (1 - X)) * x ^ (1 - X)) (z₀ ^ X * s ^ (-X)) s := by
      intro s hs
      rw [uIcc_of_le hz₀_lt_z₁.le] at hs
      have hs_pos : 0 < s := lt_of_lt_of_le hz₀_pos hs.1
      have h1 : HasDerivAt (fun x : ℝ => x ^ (1 - X)) ((1 - X) * s ^ ((1 - X) - 1)) s :=
        Real.hasDerivAt_rpow_const (Or.inl hs_pos.ne')
      have h2 := h1.const_mul (z₀ ^ X / (1 - X))
      refine h2.congr_deriv ?_
      have h1X : 1 - X ≠ 0 := by linarith
      have hexp : (1 - X) - 1 = -X := by ring
      rw [hexp]; field_simp
    have hint : IntervalIntegrable (fun s => z₀ ^ X * s ^ (-X)) volume z₀ z₁ := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hz₀_lt_z₁.le]
      refine continuousOn_const.mul (ContinuousOn.rpow_const continuousOn_id ?_)
      intro s hs; exact Or.inl (lt_of_lt_of_le hz₀_pos hs.1).ne'
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    have h1X : 1 - X ≠ 0 := by linarith
    have hX1' : X - 1 ≠ 0 := hX1.ne'
    field_simp
    ring
  -- Compute J_secant m inv.P (invDemandDeriv M.toMarket inv) q_lo q_hi > 0
  have hJ_pos : 0 < J_secant m inv.P (invDemandDeriv M.toMarket inv) q_lo q_hi := by
    unfold J_secant
    rw [sub_pos, lt_div_iff₀ (sub_pos.mpr hq_lt)]
    have hP'_at_z₀ : invDemandDeriv M.toMarket inv z₀ = -κ := by
      unfold invDemandDeriv
      rw [hinvP, hf_val z₀ ⟨hz₀_pos.le, hz₀_lt1.le⟩]
      simp only [P', hh_z₀, mul_one]
      have hκne : κ ≠ 0 := hκ_pos.ne'
      field_simp
    have harg1 : q_lo + ((m : ℝ) - 1) * q_lo = z₀ := by rw [← hmq_lo]; ring
    unfold cournotRevOf d_t_Pi
    rw [hinvP, hsum_q, harg1, hP'_at_z₀]
    -- Show LHS - RHS = (κ * z₀^X / (X - 1)) * q_lo^(2 - X) * phiX m X u > 0
    have hnum_eq : q_hi * P z₁ - q_lo * P z₀ - (P z₀ + q_lo * (-κ)) * (q_hi - q_lo) =
        (κ * z₀ ^ X / (X - 1)) * q_lo ^ (2 - X) * phiX m X u := by
      have hstep1 : q_hi * P z₁ - q_lo * P z₀ - (P z₀ + q_lo * (-κ)) * (q_hi - q_lo) =
          q_hi * (P z₁ - P z₀) + κ * q_lo * (q_hi - q_lo) := by ring
      rw [hstep1, hP_diff]
      have hz1_fac : z₁ ^ (1 - X) = (u + (m : ℝ) - 1) ^ (1 - X) * q_lo ^ (1 - X) := by
        have heq : z₁ = (u + (m : ℝ) - 1) * q_lo := by simp only [z₁, q_lo]; ring
        rw [heq, Real.mul_rpow (by linarith) hq_lo_pos.le]
      have hz0_fac : z₀ ^ (1 - X) = (m : ℝ) ^ (1 - X) * q_lo ^ (1 - X) := by
        rw [← hmq_lo, Real.mul_rpow hmpos.le hq_lo_pos.le]
      have hz0X_fac : z₀ ^ X = (m : ℝ) ^ X * q_lo ^ X := by
        rw [← hmq_lo, Real.mul_rpow hmpos.le hq_lo_pos.le]
      have hq_pow : q_lo * q_lo ^ (1 - X) = q_lo ^ (2 - X) := by
        calc q_lo * q_lo ^ (1 - X) = q_lo ^ (1 : ℝ) * q_lo ^ (1 - X) := by rw [Real.rpow_one]
          _ = q_lo ^ (1 + (1 - X)) := (Real.rpow_add hq_lo_pos 1 (1 - X)).symm
          _ = q_lo ^ (2 - X) := by ring_nf
      have hq_pow2 : q_lo ^ X * q_lo ^ (2 - X) = q_lo ^ 2 := by
        rw [← Real.rpow_add hq_lo_pos, show X + (2 - X) = ((2 : ℕ) : ℝ) by push_cast; ring,
          Real.rpow_natCast]
      have hm_inv : (m : ℝ) ^ X * (m : ℝ) ^ (-X) = 1 := by
        rw [← Real.rpow_add hmpos, add_neg_cancel, Real.rpow_zero]
      rw [hz1_fac, hz0_fac]
      simp only [phiX, q_hi]
      have hX1ne : X - 1 ≠ 0 := hX1.ne'
      have hleft : u * q_lo * (κ * z₀ ^ X / (X - 1) * ((u + (m : ℝ) - 1) ^ (1 - X) * q_lo ^ (1 - X) -
            (m : ℝ) ^ (1 - X) * q_lo ^ (1 - X))) =
          (κ * z₀ ^ X / (X - 1)) * q_lo ^ (2 - X) *
            (u * (u + (m : ℝ) - 1) ^ (1 - X) - (m : ℝ) ^ (1 - X) * u) := by
        rw [← hq_pow]; ring
      have hright : κ * q_lo * (u * q_lo - q_lo) =
          (κ * z₀ ^ X / (X - 1)) * q_lo ^ (2 - X) * ((X - 1) * (m : ℝ) ^ (-X) * (u - 1)) := by
        rw [hz0X_fac]
        have heq1 : κ * ((m : ℝ) ^ X * q_lo ^ X) / (X - 1) * q_lo ^ (2 - X) *
            ((X - 1) * (m : ℝ) ^ (-X) * (u - 1)) =
            κ * ((m : ℝ) ^ X * (m : ℝ) ^ (-X)) * (q_lo ^ X * q_lo ^ (2 - X)) * (u - 1) := by
          field_simp
        rw [heq1, hm_inv, hq_pow2]; ring
      rw [hleft, hright]; ring
    have hpos_prod : 0 < (κ * z₀ ^ X / (X - 1)) * q_lo ^ (2 - X) * phiX m X u := by
      have h1 : 0 < κ * z₀ ^ X / (X - 1) := div_pos (mul_pos hκ_pos (Real.rpow_pos_of_pos hz₀_pos X)) hX1
      have h2 : 0 < q_lo ^ (2 - X) := Real.rpow_pos_of_pos hq_lo_pos _
      exact mul_pos (mul_pos h1 h2) hphi_pos
    linarith
  exact ⟨M, inv, q_lo, q_hi, hMm, hMn, by rw [hMa]; exact hP1_pos, hpsi_a_pos,
    hE_bound, hq_lo_pos, hq_lt, hmq_hi, hJ_pos⟩

/-- **Theorem 5(ii) (Many Buyers Sharpness of Cournot's `m + 1` Bound)**:
For every `m ≥ 2` and every `X > m + 1`, there exists a covered-market `SmoothMarket` `M`
(with `M.a > 0`, `M.toMarket.psi M.a > 0`, and `E(v) ∈ [0, X]` everywhere on `[M.a, 1]`) and
an interior band with quantities `0 < q_lo < q_hi < 1 / m` such that for all sufficiently large
`n`, seller 1's single-pool revenue gain `D_n` is strictly positive. -/
theorem theorem5_many_buyers (m : ℕ) (hm : 2 ≤ m) {X : ℝ} (hX : (m : ℝ) + 1 < X) :
    ∃ (M : SmoothMarket) (inv : M.toMarket.InverseDemand) (q_lo q_hi : ℝ),
      M.m = m ∧ 0 < M.a ∧ 0 < M.toMarket.psi M.a ∧
      (∀ v ∈ Icc M.a 1, curvatureE M v ∈ Icc 0 X) ∧
      0 < q_lo ∧ q_lo < q_hi ∧ (m : ℝ) * q_hi < 1 ∧
      ∃ N : ℕ, ∀ n ≥ N, 0 < singleBandGainOf m n inv.P q_lo q_hi := by
  obtain ⟨M, inv, q_lo, q_hi, hMm, _, hMa, hpsi, hE, hq_lo_pos, hq_lt, hmq_hi, hJ_pos⟩ :=
    propC2_covered_counterexample m 2 hm le_rfl hX
  have hlim := propC2_many_buyers_limit M.toMarket inv hq_lo_pos hq_lt (by rwa [hMm])
  rw [hMm] at hlim
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨N, hN⟩ := hlim (J_secant m inv.P (invDemandDeriv M.toMarket inv) q_lo q_hi / 2)
    (by linarith)
  refine ⟨M, inv, q_lo, q_hi, hMm, hMa, hpsi, hE, hq_lo_pos, hq_lt, hmq_hi, N, ?_⟩
  intro n hn
  have hdist := hN n hn
  rw [Real.dist_eq] at hdist
  have hlo : J_secant m inv.P (invDemandDeriv M.toMarket inv) q_lo q_hi / 2 <
      singleBandGainOf m n inv.P q_lo q_hi / (1 - q_lo) ^ n := by
    linarith [(abs_lt.mp hdist).1]
  have hA4_pos : 0 < (1 - q_lo) ^ n := by
    have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
    have hq_lo_lt1 : q_lo < 1 := by nlinarith
    exact pow_pos (by linarith) n
  have hpos_div : 0 < singleBandGainOf m n inv.P q_lo q_hi / (1 - q_lo) ^ n := by linarith
  exact (div_pos_iff_of_pos_right hA4_pos).mp hpos_div

/-! ### Small-Numbers Phenomenon: Finite `m̄(F)` for Fixed Smooth `F` and `sup_F m̄(F) = ∞` -/

/-- **Small-numbers phenomenon (Part 1: `m̄(F) < ∞` for every fixed smooth `F`)**:
For any fixed `M : SmoothMarket`, there exist `f_min > 0` and `K ≥ 0` such that
`|E(v)| ≤ K / f_min²` on `[M.a, 1]`, and hence for all sufficiently large `m'`
(specifically `m' ≥ ⌈K / f_min²⌉`), Cournot's marginal revenue `ψ_{m'}` is nondecreasing on `[M.a, 1]`. -/
theorem mbar_finite_for_smooth_F (M : SmoothMarket) :
    ∃ (f_min K : ℝ), 0 < f_min ∧ 0 ≤ K ∧
      (∀ v ∈ Icc M.a 1, |curvatureE M v| ≤ K / f_min ^ 2) ∧
      ∃ m_bar : ℕ, ∀ (m' : ℕ) (hm' : 2 ≤ m'), m_bar ≤ m' →
        MonotoneOn ({ M.toMarket with m := m', hm := hm' } : Market).psi (Icc M.a 1) := by
  have hne : (Icc M.a 1).Nonempty := nonempty_Icc.mpr M.ha1.le
  obtain ⟨v_min, hv_min_mem, hv_min⟩ := isCompact_Icc.exists_isMinOn hne M.hf_cont
  obtain ⟨v_max, _, hv_max⟩ := isCompact_Icc.exists_isMaxOn hne M.hf'_cont.abs
  set f_min := M.f v_min
  set K := |M.f' v_max|
  have hf_min_pos : 0 < f_min := M.hf_pos v_min hv_min_mem
  have hK_nonneg : 0 ≤ K := abs_nonneg _
  have hE_bound : ∀ v ∈ Icc M.a 1, |curvatureE M v| ≤ K / f_min ^ 2 := by
    intro v hv
    unfold curvatureE
    have hf_ge : f_min ≤ M.f v := hv_min hv
    have hf_pos : 0 < M.f v := M.hf_pos v hv
    have hK_ge : |M.f' v| ≤ K := hv_max hv
    have hFv := M.toMarket.F_mem_Icc hv
    rw [abs_div, abs_neg, abs_mul, abs_of_nonneg (by linarith [hFv.2] : 0 ≤ 1 - M.F v),
      abs_of_pos (sq_pos_of_pos hf_pos)]
    have hnum : (1 - M.F v) * |M.f' v| ≤ K := by
      calc (1 - M.F v) * |M.f' v| ≤ 1 * K :=
            mul_le_mul (by linarith [hFv.1]) hK_ge (abs_nonneg _) zero_le_one
        _ = K := one_mul _
    have hden : f_min ^ 2 ≤ (M.f v) ^ 2 := pow_le_pow_left₀ hf_min_pos.le hf_ge 2
    calc (1 - M.F v) * |M.f' v| / (M.f v) ^ 2 ≤ K / (M.f v) ^ 2 :=
          div_le_div_of_nonneg_right hnum (sq_nonneg _)
      _ ≤ K / f_min ^ 2 := div_le_div_of_nonneg_left hK_nonneg (sq_pos_of_pos hf_min_pos) hden
  obtain ⟨m_bar, hm_bar⟩ := exists_nat_ge (K / f_min ^ 2)
  refine ⟨f_min, K, hf_min_pos, hK_nonneg, hE_bound, m_bar, ?_⟩
  intro m' hm' hm'_ge
  let M' : Market := { M.toMarket with m := m', hm := hm' }
  have hm'_pos : (0 : ℝ) < m' := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hm')
  have hpsi_cont : ContinuousOn M'.psi (Icc M.a 1) := by
    unfold Market.psi
    refine continuousOn_id.sub ?_
    refine ContinuousOn.div (continuousOn_const.sub M.toMarket.F_continuousOn)
      (continuousOn_const.mul M.hf_cont) ?_
    intro v hv
    exact mul_ne_zero hm'_pos.ne' (M.hf_pos v hv).ne'
  have hpsi_deriv : ∀ v ∈ Ioo M.a 1,
      HasDerivAt M'.psi (((m' : ℝ) + 1 - curvatureE M v) / (m' : ℝ)) v := by
    intro v hv
    have hF := M.hF_deriv_open v hv
    have hf := M.hf_deriv_open v hv
    have hfpos : 0 < M.f v := M.hf_pos v (Ioo_subset_Icc_self hv)
    have hnum : HasDerivAt (fun x => 1 - M.F x) (-M.f v) v := by
      have h := (hasDerivAt_const v (1 : ℝ)).sub hF
      refine h.congr_deriv ?_; ring
    have hden : HasDerivAt (fun x => (m' : ℝ) * M.f x) ((m' : ℝ) * M.f' v) v :=
      hf.const_mul (m' : ℝ)
    have hdiv := hnum.div hden (mul_ne_zero hm'_pos.ne' hfpos.ne')
    have hsub : HasDerivAt (fun x => x - (1 - M.F x) / ((m' : ℝ) * M.f x)) _ v :=
      (hasDerivAt_id v).sub hdiv
    change HasDerivAt (fun x => x - (1 - M.F x) / ((m' : ℝ) * M.f x)) _ v
    refine hsub.congr_deriv ?_
    unfold curvatureE
    have hfne : M.f v ≠ 0 := hfpos.ne'
    have hmne : (m' : ℝ) ≠ 0 := hm'_pos.ne'
    field_simp
    ring
  apply monotoneOn_of_deriv_nonneg (convex_Icc M.a 1) hpsi_cont
  · intro v hv
    rw [interior_Icc] at hv
    exact (hpsi_deriv v hv).differentiableAt.differentiableWithinAt
  · intro v hv
    rw [interior_Icc] at hv
    rw [(hpsi_deriv v hv).deriv]
    apply div_nonneg _ hm'_pos.le
    have hEb := (abs_le.mp (hE_bound v (Ioo_subset_Icc_self hv))).2
    have hm_ge_R : K / f_min ^ 2 ≤ (m' : ℝ) := hm_bar.trans (by exact_mod_cast hm'_ge)
    linarith

/-- **Small-numbers phenomenon (Part 2: `sup_F m̄(F) = ∞` via smooth truncated Pareto family)**:
For any `m ≥ 2`, `n ≥ 2`, `0 ≤ a < 1`, and any tail exponent `0 < α < 1 / (2 X̄(m) - 1)`,
the smooth truncated Pareto distribution `1 - F(v) = (S(v) - S(1)) / (1 - S(1))` with
`S(v) = (1 + c (v - a))^(-α)` and `S(1) = 1 / 2` defines a valid `SmoothMarket` with
`E(a) = (α + 1) / (2α) > X̄(m)`, `E(v) > X̄(m)` on an interval `(a, a + δ)`, and non-monotone
Cournot marginal revenue `ψ_m` on `[a, 1]`. -/
theorem sup_mbar_infinite (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    {α : ℝ} (hα_pos : 0 < α) (hα_lt : α < 1 / (2 * Xbar m - 1)) :
    ∃ M : SmoothMarket,
      M.m = m ∧ M.n = n ∧ M.a = a ∧
      curvatureE M a = (α + 1) / (2 * α) ∧
      Xbar m < curvatureE M a ∧
      (∃ δ > 0, ∀ v ∈ Ioo a (min 1 (a + δ)), Xbar m < curvatureE M v) ∧
      ¬ MonotoneOn M.toMarket.psi (Icc a 1) := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hXbar_eq : Xbar m = (m : ℝ) * ((m : ℝ) + 3) / ((m : ℝ) + 1) := Xbar_eq hm
  have hXbar_gt_m1 : (m : ℝ) + 1 < Xbar m := by
    rw [hXbar_eq, lt_div_iff₀ (by linarith : (0 : ℝ) < (m : ℝ) + 1)]
    nlinarith
  have hden_Xbar : 0 < 2 * Xbar m - 1 := by linarith
  have hEa_gt_Xbar : Xbar m < (α + 1) / (2 * α) := by
    have hmul : α * (2 * Xbar m - 1) < 1 := (lt_div_iff₀ hden_Xbar).mp hα_lt
    rw [lt_div_iff₀ (by linarith : 0 < 2 * α)]
    linarith
  -- Choose scale c > 0 so that 1 + c(1 - a) = 2^(1/α), hence S(1) = 1/2
  set c : ℝ := ((2 : ℝ) ^ (1 / α) - 1) / (1 - a)
  have h2pow_gt1 : 1 < (2 : ℝ) ^ (1 / α) :=
    Real.one_lt_rpow (by norm_num) (div_pos one_pos hα_pos)
  have hc_pos : 0 < c := div_pos (by linarith) (by linarith)
  let u : ℝ → ℝ := fun v => 1 + c * (v - a)
  have hu_pos : ∀ v ∈ Icc a 1, 0 < u v := fun v hv => by
    simp only [u]; have : 0 ≤ c * (v - a) := mul_nonneg hc_pos.le (by linarith [hv.1]); linarith
  have hu_a : u a = 1 := by simp [u]
  have hu_1 : u 1 = (2 : ℝ) ^ (1 / α) := by
    simp only [u, c]
    have : 1 - a ≠ 0 := by linarith
    field_simp
    ring
  let S : ℝ → ℝ := fun v => (u v) ^ (-α)
  have hS_a : S a = 1 := by simp [S, hu_a]
  have hS_1 : S 1 = 1 / 2 := by
    simp only [S, hu_1]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      show (1 / α) * (-α) = -1 by field_simp,
      Real.rpow_neg_one, one_div]
  -- Define F, f, f'
  let F : ℝ → ℝ := fun v => if v ≤ a then 0 else 2 - 2 * S v
  let f : ℝ → ℝ := fun v => if v < a then 0 else 2 * α * c * (u v) ^ (-α - 1)
  let f' : ℝ → ℝ := fun v => -2 * α * (α + 1) * c ^ 2 * (u v) ^ (-α - 2)
  have hF_on : ∀ v ∈ Icc a 1, F v = 2 - 2 * S v := by
    intro v hv
    by_cases hva : v ≤ a
    · have : v = a := le_antisymm hva hv.1
      subst this; simp only [F, le_rfl, ↓reduceIte, hS_a]; ring
    · simp only [F, hva, ↓reduceIte]
  have hf_on : ∀ v ∈ Icc a 1, f v = 2 * α * c * (u v) ^ (-α - 1) := by
    intro v hv; simp only [f, not_lt.mpr hv.1, ↓reduceIte]
  have hu_deriv : ∀ v : ℝ, HasDerivAt u c v := by
    intro v
    have h := (((hasDerivAt_id v).sub_const a).const_mul c).const_add 1
    refine h.congr_deriv ?_; ring
  have hF_deriv_within : ∀ v ∈ Icc a 1, HasDerivWithinAt F (f v) (Icc a 1) v := by
    intro v hv
    have hu_ne : u v ≠ 0 := (hu_pos v hv).ne'
    have hS_d : HasDerivAt S ((-α) * (u v) ^ (-α - 1) * c) v := by
      have h1 : HasDerivAt (fun x : ℝ => x ^ (-α)) ((-α) * (u v) ^ (-α - 1)) (u v) :=
        Real.hasDerivAt_rpow_const (Or.inl hu_ne)
      exact h1.comp v (hu_deriv v)
    have h2 : HasDerivAt (fun x => 2 - 2 * S x) (2 * α * c * (u v) ^ (-α - 1)) v := by
      have h := (hasDerivAt_const v (2 : ℝ)).sub (hS_d.const_mul 2)
      refine h.congr_deriv ?_; ring
    rw [hf_on v hv]
    exact h2.hasDerivWithinAt.congr hF_on (hF_on v hv)
  have hF_deriv_open : ∀ v ∈ Ioo a 1, HasDerivAt F (f v) v :=
    fun v hv => (hF_deriv_within v (Ioo_subset_Icc_self hv)).hasDerivAt (Icc_mem_nhds hv.1 hv.2)
  have hf_deriv_within : ∀ v ∈ Icc a 1, HasDerivWithinAt f (f' v) (Icc a 1) v := by
    intro v hv
    have hu_ne : u v ≠ 0 := (hu_pos v hv).ne'
    have h1 : HasDerivAt (fun x : ℝ => x ^ (-α - 1)) ((-α - 1) * (u v) ^ ((-α - 1) - 1)) (u v) :=
      Real.hasDerivAt_rpow_const (Or.inl hu_ne)
    have h2 : HasDerivAt (fun x => 2 * α * c * (u x) ^ (-α - 1)) (f' v) v := by
      have h := (h1.comp v (hu_deriv v)).const_mul (2 * α * c)
      refine h.congr_deriv ?_
      simp only [f', show (-α - 1) - 1 = -α - 2 by ring]; ring
    exact h2.hasDerivWithinAt.congr hf_on (hf_on v hv)
  have hf_deriv_open : ∀ v ∈ Ioo a 1, HasDerivAt f (f' v) v :=
    fun v hv => (hf_deriv_within v (Ioo_subset_Icc_self hv)).hasDerivAt (Icc_mem_nhds hv.1 hv.2)
  have hf_cont : ContinuousOn f (Icc a 1) := by
    have hcont : ContinuousOn (fun v => 2 * α * c * (u v) ^ (-α - 1)) (Icc a 1) := by
      refine continuousOn_const.mul (ContinuousOn.rpow_const ?_ ?_)
      · exact (continuous_const.add (continuous_const.mul (continuous_id.sub continuous_const))).continuousOn
      · intro v hv; exact Or.inl (hu_pos v hv).ne'
    exact hcont.congr hf_on
  have hf'_cont : ContinuousOn f' (Icc a 1) := by
    refine continuousOn_const.mul (ContinuousOn.rpow_const ?_ ?_)
    · exact (continuous_const.add (continuous_const.mul (continuous_id.sub continuous_const))).continuousOn
    · intro v hv; exact Or.inl (hu_pos v hv).ne'
  have hf_pos : ∀ v ∈ Icc a 1, 0 < f v := by
    intro v hv
    rw [hf_on v hv]
    exact mul_pos (by positivity) (Real.rpow_pos_of_pos (hu_pos v hv) _)
  let M : SmoothMarket := {
    m := m
    n := n
    hm := hm
    hn := hn
    a := a
    ha0 := ha0
    ha1 := ha1
    F := F
    f := f
    f' := f'
    hF_a := by simp [F]
    hF_1 := by rw [hF_on 1 (right_mem_Icc.mpr ha1.le), hS_1]; ring
    hF_below := fun v hv => by simp [F, hv]
    hf_below := fun v hv => by simp [f, hv]
    hf_cont := hf_cont
    hf_pos := hf_pos
    hF_deriv_within := hF_deriv_within
    hF_deriv_open := hF_deriv_open
    hf'_cont := hf'_cont
    hf_deriv_within := hf_deriv_within
    hf_deriv_open := hf_deriv_open
  }
  -- Exact formula for curvatureE M v on [a, 1]
  have hE_formula : ∀ v ∈ Icc a 1, curvatureE M v = ((α + 1) / α) * (1 - 1 / (2 * S v)) := by
    intro v hv
    unfold curvatureE
    change -((1 - F v) * f' v) / (f v) ^ 2 = _
    rw [hF_on v hv, hf_on v hv]
    simp only [f']
    have huv : 0 < u v := hu_pos v hv
    have hSpos : 0 < S v := Real.rpow_pos_of_pos huv _
    have hpow_ratio : (u v) ^ (-α - 2) / ((u v) ^ (-α - 1)) ^ 2 = 1 / S v := by
      have hsq : ((u v) ^ (-α - 1)) ^ 2 = (u v) ^ (-2 * α - 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul huv.le]; congr 1; norm_num; ring
      rw [hsq, ← Real.rpow_sub huv, show (-α - 2) - (-2 * α - 2) = α by ring]
      simp only [S, Real.rpow_neg huv.le, one_div, inv_inv]
    have h1 : -((1 - (2 - 2 * S v)) * (-2 * α * (α + 1) * c ^ 2 * (u v) ^ (-α - 2))) /
        (2 * α * c * (u v) ^ (-α - 1)) ^ 2 =
        ((2 * S v - 1) * (α + 1) / (2 * α)) * ((u v) ^ (-α - 2) / ((u v) ^ (-α - 1)) ^ 2) := by
      have hαne : α ≠ 0 := hα_pos.ne'
      have hcne : c ≠ 0 := hc_pos.ne'
      have hpne : (u v) ^ (-α - 1) ≠ 0 := (Real.rpow_pos_of_pos huv _).ne'
      field_simp
      ring
    rw [h1, hpow_ratio]
    have hαne : α ≠ 0 := hα_pos.ne'
    have hSne : S v ≠ 0 := hSpos.ne'
    field_simp
  have hEa : curvatureE M a = (α + 1) / (2 * α) := by
    rw [hE_formula a (left_mem_Icc.mpr ha1.le), hS_a]
    have hαne : α ≠ 0 := hα_pos.ne'
    field_simp
    ring
  -- Continuity of E at a within [a, 1] gives an interval (a, min 1 (a + δ)) where E(v) > Xbar m
  have hE_cont : ContinuousOn (curvatureE M) (Icc a 1) := by
    unfold curvatureE
    refine ContinuousOn.div ((continuousOn_const.sub M.toMarket.F_continuousOn).mul M.hf'_cont).neg
      (M.hf_cont.pow 2) ?_
    intro v hv; exact pow_ne_zero 2 (M.hf_pos v hv).ne'
  have hE_at : ContinuousWithinAt (curvatureE M) (Icc a 1) a :=
    hE_cont a (left_mem_Icc.mpr ha1.le)
  rw [Metric.continuousWithinAt_iff] at hE_at
  obtain ⟨δ, hδ_pos, hδ⟩ := hE_at ((curvatureE M a - Xbar m) / 2) (by linarith)
  have hE_interval : ∀ v ∈ Ioo a (min 1 (a + δ)), Xbar m < curvatureE M v := by
    intro v hv
    have hv_in : v ∈ Icc a 1 := ⟨hv.1.le, hv.2.le.trans (min_le_left _ _)⟩
    have hdist : dist v a < δ := by
      rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hv.1)]
      linarith [hv.2, min_le_right 1 (a + δ)]
    have h := hδ hv_in hdist
    rw [Real.dist_eq] at h
    linarith [(abs_lt.mp h).1]
  -- Non-monotonicity of ψ_m on [a, 1]: on (a, min 1 (a + δ)), E(v) > Xbar m > m + 1 so ψ_m' < 0
  have hnot_mono : ¬ MonotoneOn M.toMarket.psi (Icc a 1) := by
    intro hmono
    set b := (a + min 1 (a + δ)) / 2
    have ha_lt_min : a < min 1 (a + δ) := lt_min ha1 (by linarith)
    have ha_lt_b : a < b := by simp only [b]; linarith
    have hb_lt_min : b < min 1 (a + δ) := by simp only [b]; linarith
    have hb_in : b ∈ Icc a 1 := ⟨ha_lt_b.le, hb_lt_min.le.trans (min_le_left _ _)⟩
    have hpsi_cont : ContinuousOn M.toMarket.psi (Icc a b) := by
      unfold Market.psi
      refine continuousOn_id.sub (ContinuousOn.div
        (continuousOn_const.sub (M.toMarket.F_continuousOn.mono (Icc_subset_Icc_right hb_in.2)))
        (continuousOn_const.mul (M.hf_cont.mono (Icc_subset_Icc_right hb_in.2))) ?_)
      intro v hv
      exact mul_ne_zero (by rw [show M.toMarket.m = m from rfl]; exact hmpos.ne')
        (M.hf_pos v ⟨hv.1, hv.2.trans hb_in.2⟩).ne'
    have hpsi_deriv : ∀ v ∈ Ioo a b,
        HasDerivAt M.toMarket.psi (((m : ℝ) + 1 - curvatureE M v) / (m : ℝ)) v := by
      intro v hv
      have hv_oo : v ∈ Ioo a 1 := ⟨hv.1, hv.2.trans_le hb_in.2⟩
      have hF' := M.hF_deriv_open v hv_oo
      have hf' := M.hf_deriv_open v hv_oo
      have hfpos : 0 < M.f v := M.hf_pos v (Ioo_subset_Icc_self hv_oo)
      have hnum : HasDerivAt (fun x => 1 - M.F x) (-M.f v) v := by
        have h := (hasDerivAt_const v (1 : ℝ)).sub hF'
        refine h.congr_deriv ?_; ring
      have hden : HasDerivAt (fun x => (m : ℝ) * M.f x) ((m : ℝ) * M.f' v) v :=
        hf'.const_mul (m : ℝ)
      have hdiv := hnum.div hden (mul_ne_zero hmpos.ne' hfpos.ne')
      have hsub : HasDerivAt (fun x => x - (1 - M.F x) / ((m : ℝ) * M.f x)) _ v :=
        (hasDerivAt_id v).sub hdiv
      change HasDerivAt (fun x => x - (1 - M.F x) / ((m : ℝ) * M.f x)) _ v
      refine hsub.congr_deriv ?_
      unfold curvatureE
      have hfne : M.f v ≠ 0 := hfpos.ne'
      have hmne : (m : ℝ) ≠ 0 := hmpos.ne'
      field_simp
      ring
    have hpsi_diff : DifferentiableOn ℝ M.toMarket.psi (Ioo a b) :=
      fun v hv => (hpsi_deriv v hv).differentiableAt.differentiableWithinAt
    obtain ⟨ξ, hξ, hslope⟩ := exists_deriv_eq_slope M.toMarket.psi ha_lt_b hpsi_cont hpsi_diff
    have hξ_in : ξ ∈ Ioo a (min 1 (a + δ)) := ⟨hξ.1, hξ.2.trans hb_lt_min⟩
    have hEξ : (m : ℝ) + 1 < curvatureE M ξ := hXbar_gt_m1.trans (hE_interval ξ hξ_in)
    have hderiv_neg : deriv M.toMarket.psi ξ < 0 := by
      rw [(hpsi_deriv ξ hξ).deriv]
      exact div_neg_of_neg_of_pos (by linarith) hmpos
    have hslope_nn : 0 ≤ (M.toMarket.psi b - M.toMarket.psi a) / (b - a) :=
      div_nonneg (sub_nonneg.mpr (hmono (left_mem_Icc.mpr ha1.le) hb_in ha_lt_b.le))
        (sub_pos.mpr ha_lt_b).le
    linarith
  exact ⟨M, rfl, rfl, rfl, hEa, by linarith, ⟨δ, hδ_pos, hE_interval⟩, hnot_mono⟩

end AuctionCompetition
