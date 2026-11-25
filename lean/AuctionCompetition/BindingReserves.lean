import AuctionCompetition.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Section 5 & Appendix B: Binding Reserves (Theorems 3 and 4)

Formalization of:
* **Theorem 3** (`theorem3_asking_price_sr`, `theorem3_asking_price_gain`,
  `theorem3_rho_one_fails`, `theorem3_zero_reserve_fails`):
  Symmetric binding reserves fail via asking-price deviations `(ρ, {(ρ, β)})`,
  together with the boundary cases `ρ = 1` and `a = ρ = 0`.
* **Theorem 4** (`theorem4_cutoff_asymptotics`, `theorem4_deviation_sr`,
  `theorem4_revenue_limit`, `theorem4_asymmetric_duopoly_fails`):
  Asymmetric duopoly profiles `(SPA(r_{L,n}), SPA(r_{H,n}))` with `a = 0`,
  `r_{L,n} → r_L < r_H ← r_{H,n}`, and `ψ₁(r_H) < 0` fail for all large `n`.
-/

open MeasureTheory Set Filter Topology Asymptotics

namespace AuctionCompetition

/-! ### Shared Helpers -/

/-- Seller `0` (the deviating / low-reserve seller). -/
def seller0 (M : Market) : Fin M.m := ⟨0, lt_of_lt_of_le (by decide) M.hm⟩

/-- Replace the number of buyers `n` in a `Market`, keeping `m`, `a`, `F`, `f` fixed. -/
def Market.withBuyers (M : Market) (n : ℕ) (hn : 2 ≤ n) : Market where
  m := M.m
  n := n
  hm := M.hm
  hn := hn
  a := M.a
  ha0 := M.ha0
  ha1 := M.ha1
  F := M.F
  f := M.f
  hF_a := M.hF_a
  hF_1 := M.hF_1
  hF_below := M.hF_below
  hf_below := M.hf_below
  hf_cont := M.hf_cont
  hf_pos := M.hf_pos
  hF_deriv_within := M.hF_deriv_within
  hF_deriv_open := M.hF_deriv_open

lemma Market.n_sub_one_ne_zero (M : Market) : M.n - 1 ≠ 0 := by
  have := M.hn; omega

section IntegralConventions

/-- Almost every point of `uIoc a b` (for `a ≤ b`) lies in the open interval `Ioo a b`. -/
lemma ae_Ioo_of_uIoc {a b : ℝ} (hab : a ≤ b) :
    ∀ᵐ u ∂(volume.restrict (uIoc a b)), u ∈ Ioo a b := by
  have hne : ∀ᵐ u ∂volume, u ≠ b := by
    rw [ae_iff]; simp
  have hne' : ∀ᵐ u ∂(volume.restrict (uIoc a b)), u ≠ b :=
    ae_restrict_of_ae hne
  filter_upwards [ae_restrict_mem measurableSet_uIoc, hne'] with u hu hub
  rw [uIoc_of_le hab] at hu
  exact ⟨hu.1, lt_of_le_of_ne hu.2 hub⟩

lemma intervalIntegrable_congr_Ioo {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ}
    (h : ∀ u ∈ Ioo a b, f u = g u) :
    IntervalIntegrable f volume a b ↔ IntervalIntegrable g volume a b := by
  apply intervalIntegrable_congr_ae
  filter_upwards [ae_Ioo_of_uIoc hab] with u hu using h u hu

lemma intervalIntegral_congr_Ioo {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ}
    (h : ∀ u ∈ Ioo a b, f u = g u) :
    ∫ u in a..b, f u = ∫ u in a..b, g u := by
  apply intervalIntegral.integral_congr_ae
  have h1 : ∀ᵐ u ∂(volume.restrict (uIoc a b)), f u = g u := by
    filter_upwards [ae_Ioo_of_uIoc hab] with u hu using h u hu
  rw [ae_restrict_iff' measurableSet_uIoc] at h1
  filter_upwards [h1] with u hu hmem
  exact hu hmem

lemma ibp_of_hasDerivAt_of_le {a b : ℝ} (hab : a ≤ b) {u v u' v' : ℝ → ℝ}
    (hu_cont : ContinuousOn u (Icc a b)) (hv_cont : ContinuousOn v (Icc a b))
    (hu_deriv : ∀ x ∈ Ioo a b, HasDerivAt u (u' x) x)
    (hv_deriv : ∀ x ∈ Ioo a b, HasDerivAt v (v' x) x)
    (hu'_int : IntervalIntegrable (fun x => u' x * v x) volume a b)
    (hv'_int : IntervalIntegrable (fun x => u x * v' x) volume a b) :
    ∫ x in a..b, u x * v' x = u b * v b - u a * v a - ∫ x in a..b, u' x * v x := by
  have huv_cont : ContinuousOn (fun x => u x * v x) (Icc a b) := hu_cont.mul hv_cont
  have huv_deriv : ∀ x ∈ Ioo a b, HasDerivAt (fun x => u x * v x) (u' x * v x + u x * v' x) x :=
    fun x hx => (hu_deriv x hx).mul (hv_deriv x hx)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab huv_cont huv_deriv
    (hu'_int.add hv'_int)
  rw [intervalIntegral.integral_add hu'_int hv'_int] at hftc
  linarith

lemma continuousOn_primitive_Icc {a b : ℝ} (hab : a ≤ b) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc a b)) :
    ContinuousOn (fun x => ∫ u in a..x, g u) (Icc a b) := by
  have hint : IntegrableOn g (uIcc a b) volume := by
    rw [uIcc_of_le hab]; exact hg.integrableOn_Icc
  have h := intervalIntegral.continuousOn_primitive_interval hint
  rwa [uIcc_of_le hab] at h

lemma integral_hasDerivAt_right_of_continuousOn {a b x : ℝ} {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc a b)) (hx : x ∈ Ioo a b) :
    HasDerivAt (fun v => ∫ u in a..v, g u) (g x) x := by
  have hint : IntervalIntegrable g volume a x :=
    (hg.mono (by rw [uIcc_of_le hx.1.le]; exact Icc_subset_Icc le_rfl hx.2.le)).intervalIntegrable
  have hmeas : StronglyMeasurableAtFilter g (𝓝 x) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (hg.mono Ioo_subset_Icc_self) x hx
  have hcat : ContinuousAt g x := hg.continuousAt (Icc_mem_nhds hx.1 hx.2)
  exact intervalIntegral.integral_hasDerivAt_right hint hmeas hcat

lemma intervalIntegral_finset_sum_local {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ} {a b : ℝ}
    (hf : ∀ i ∈ s, IntervalIntegrable (f i) volume a b) :
    ∫ x in a..b, ∑ i ∈ s, f i x = ∑ i ∈ s, ∫ x in a..b, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have h1 : IntervalIntegrable (f i) volume a b := hf i (Finset.mem_insert_self i s)
    have h2 : IntervalIntegrable (fun x => ∑ j ∈ s, f j x) volume a b := by
      have : (fun x => ∑ j ∈ s, f j x) = ∑ j ∈ s, f j := by ext x; simp
      rw [this]
      exact IntervalIntegrable.sum s fun j hj => hf j (Finset.mem_insert_of_mem hj)
    simp_rw [Finset.sum_insert hi]
    rw [intervalIntegral.integral_add h1 h2, ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

lemma continuousOn_finset_sum_local {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ} {t : Set ℝ}
    (hf : ∀ i ∈ s, ContinuousOn (f i) t) :
    ContinuousOn (fun x => ∑ i ∈ s, f i x) t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [continuousOn_const]
  | @insert i s hi ih =>
    simp_rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self i s)).add (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

end IntegralConventions

namespace Market

variable (M : Market)

/-- Uniform positive lower bound `f_min > 0` on `f` over `[M.a, 1]`. -/
lemma exists_f_min : ∃ fmin > 0, ∀ v ∈ Icc M.a 1, fmin ≤ M.f v := by
  have hne : (Icc M.a 1).Nonempty := ⟨M.a, left_mem_Icc.mpr M.ha1.le⟩
  obtain ⟨v₀, hv₀, hmin⟩ := isCompact_Icc.exists_isMinOn hne M.hf_cont
  exact ⟨M.f v₀, M.hf_pos v₀ hv₀, fun v hv => hmin hv⟩

/-- Uniform positive upper bound `f_max > 0` on `f` over `[M.a, 1]`. -/
lemma exists_f_max : ∃ fmax > 0, ∀ v ∈ Icc M.a 1, M.f v ≤ fmax := by
  have hne : (Icc M.a 1).Nonempty := ⟨M.a, left_mem_Icc.mpr M.ha1.le⟩
  obtain ⟨v₀, hv₀, hmax⟩ := isCompact_Icc.exists_isMaxOn hne M.hf_cont
  exact ⟨M.f v₀, M.hf_pos v₀ hv₀, fun v hv => hmax hv⟩

/-- `F(y) - F(x) = ∫_x^y f(u) du` for `M.a ≤ x ≤ y ≤ 1`. -/
lemma F_sub_eq_integral {x y : ℝ} (hxa : M.a ≤ x) (hxy : x ≤ y) (hy1 : y ≤ 1) :
    M.F y - M.F x = ∫ u in x..y, M.f u := by
  have hsub : uIcc x y ⊆ Icc M.a 1 := by
    rw [uIcc_of_le hxy]
    exact Icc_subset_Icc hxa hy1
  have hint : IntervalIntegrable M.f volume x y :=
    (M.hf_cont.mono hsub).intervalIntegrable
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hxy
    (M.F_continuousOn.mono (by rw [← uIcc_of_le hxy]; exact hsub))
    (fun u hu => M.hF_deriv_open u ⟨lt_of_le_of_lt hxa hu.1, lt_of_lt_of_le hu.2 hy1⟩)
    hint
  exact hftc.symm

/-- Existence and uniqueness of `v ∈ [M.a, 1]` with `M.F v = y` for any `y ∈ [0, 1]`. -/
lemma exists_unique_F_eq {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ∃! v, v ∈ Icc M.a 1 ∧ M.F v = y := by
  have hmem : y ∈ Icc (M.F M.a) (M.F 1) := by
    rw [M.hF_a, M.hF_1]; exact ⟨hy0, hy1⟩
  obtain ⟨v, hv, hFv⟩ := intermediate_value_Icc M.ha1.le M.F_continuousOn hmem
  refine ⟨v, ⟨hv, hFv⟩, ?_⟩
  rintro w ⟨hw, hFw⟩
  exact M.F_strictMonoOn.injOn hw hv (hFw.trans hFv.symm)

/-- Inverse CDF `invF M y` for `y ∈ [0, 1]`, satisfying `F (invF M y) = y`. -/
noncomputable def invF (y : ℝ) : ℝ :=
  if h : 0 ≤ y ∧ y ≤ 1 then (M.exists_unique_F_eq h.1 h.2).choose else M.a

lemma invF_mem {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : M.invF y ∈ Icc M.a 1 := by
  unfold invF
  simp only [hy0, hy1, and_self, ↓reduceDIte]
  exact (M.exists_unique_F_eq hy0 hy1).choose_spec.1.1

lemma F_invF {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : M.F (M.invF y) = y := by
  unfold invF
  simp only [hy0, hy1, and_self, ↓reduceDIte]
  exact (M.exists_unique_F_eq hy0 hy1).choose_spec.1.2

lemma invF_F {v : ℝ} (hv : v ∈ Icc M.a 1) : M.invF (M.F v) = v := by
  have hF := M.F_mem_Icc hv
  exact M.F_strictMonoOn.injOn (M.invF_mem hF.1 hF.2) hv (M.F_invF hF.1 hF.2)

lemma invF_strictMonoOn : StrictMonoOn M.invF (Icc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  by_contra hle
  push Not at hle
  have h1 := M.F_strictMonoOn.monotoneOn (M.invF_mem hy.1 hy.2) (M.invF_mem hx.1 hx.2) hle
  rw [M.F_invF hy.1 hy.2, M.F_invF hx.1 hx.2] at h1
  linarith

lemma F_lipschitz_bounds {x y : ℝ} (hx : x ∈ Icc M.a 1) (hy : y ∈ Icc M.a 1) (hxy : x ≤ y)
    {fmin fmax : ℝ} (hlo : ∀ v ∈ Icc M.a 1, fmin ≤ M.f v) (hhi : ∀ v ∈ Icc M.a 1, M.f v ≤ fmax) :
    fmin * (y - x) ≤ M.F y - M.F x ∧ M.F y - M.F x ≤ fmax * (y - x) := by
  rw [M.F_sub_eq_integral hx.1 hxy hy.2]
  have hint : IntervalIntegrable M.f volume x y :=
    (M.hf_cont.mono (by rw [uIcc_of_le hxy]; exact Icc_subset_Icc hx.1 hy.2)).intervalIntegrable
  constructor
  · have hc : ∫ _ in x..y, fmin = fmin * (y - x) := by
      rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
    rw [← hc]
    exact intervalIntegral.integral_mono_on hxy intervalIntegrable_const hint
      (fun u hu => hlo u ⟨le_trans hx.1 hu.1, le_trans hu.2 hy.2⟩)
  · have hc : ∫ _ in x..y, fmax = fmax * (y - x) := by
      rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
    rw [← hc]
    exact intervalIntegral.integral_mono_on hxy hint intervalIntegrable_const
      (fun u hu => hhi u ⟨le_trans hx.1 hu.1, le_trans hu.2 hy.2⟩)

lemma invF_continuousOn : ContinuousOn M.invF (Icc (0 : ℝ) 1) := by
  obtain ⟨fmin, hfmin, hf_lo⟩ := M.exists_f_min
  obtain ⟨fmax, _, hf_hi⟩ := M.exists_f_max
  intro x hx
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  refine ⟨fmin * ε, mul_pos hfmin hε, fun y hy hdist => ?_⟩
  rw [Real.dist_eq] at hdist ⊢
  have hx_mem := M.invF_mem hx.1 hx.2
  have hy_mem := M.invF_mem hy.1 hy.2
  have hlip : fmin * |M.invF y - M.invF x| ≤ |y - x| := by
    rcases le_total (M.invF x) (M.invF y) with hle | hle
    · rw [abs_of_nonneg (sub_nonneg.mpr hle)]
      have h := (M.F_lipschitz_bounds hx_mem hy_mem hle hf_lo hf_hi).1
      rw [M.F_invF hy.1 hy.2, M.F_invF hx.1 hx.2] at h
      exact le_trans h (le_abs_self _)
    · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hle)]
      have h := (M.F_lipschitz_bounds hy_mem hx_mem hle hf_lo hf_hi).1
      rw [M.F_invF hx.1 hx.2, M.F_invF hy.1 hy.2] at h
      rw [abs_sub_comm]
      exact le_trans h (le_abs_self _)
  exact lt_of_mul_lt_mul_left (lt_of_le_of_lt hlip hdist) hfmin.le

lemma A_continuousOn : ContinuousOn M.A (Icc M.a 1) := by
  unfold Market.A
  have hF := M.F_continuousOn
  fun_prop

lemma A_deriv_open {v : ℝ} (hv : v ∈ Ioo M.a 1) :
    HasDerivAt M.A (M.f v / (M.m : ℝ)) v := by
  unfold Market.A
  have h := ((hasDerivAt_const v (1 : ℝ)).sub (M.hF_deriv_open v hv)).div_const (M.m : ℝ)
  have h2 := (hasDerivAt_const v (1 : ℝ)).sub h
  convert h2 using 1
  ring

lemma br_A_mem_Icc {v : ℝ} (hv : v ∈ Icc M.a 1) : M.A v ∈ Icc (1 - 1 / (M.m : ℝ)) 1 := by
  unfold Market.A
  have hF := M.F_mem_Icc hv
  have hm : (0 : ℝ) < M.m := M.m_pos_real
  constructor
  · have : (1 - M.F v) / (M.m : ℝ) ≤ 1 / (M.m : ℝ) :=
      div_le_div_of_nonneg_right (by linarith [hF.1]) hm.le
    linarith
  · have : 0 ≤ (1 - M.F v) / (M.m : ℝ) := div_nonneg (by linarith [hF.2]) hm.le
    linarith

lemma br_A_pos {v : ℝ} (hv : v ∈ Icc M.a 1) : 0 < M.A v := by
  have hA := (M.br_A_mem_Icc hv).1
  have hm : (2 : ℝ) ≤ M.m := by exact_mod_cast M.hm
  have : 1 / (M.m : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hm
  linarith

end Market

/-! ### `poolAvg` and Power Expansion Helpers -/

lemma poolAvg_strict_bounds {n : ℕ} (hn : 2 ≤ n) {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) :
    x ^ (n - 1) < poolAvg n x y ∧ poolAvg n x y < y ^ (n - 1) := by
  rw [poolAvg_eq_sum n (by omega)]
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h1 : (n : ℝ) * x ^ (n - 1) < ∑ k ∈ Finset.range n, x ^ k * y ^ (n - 1 - k) := by
    have hsum : (n : ℝ) * x ^ (n - 1) = ∑ k ∈ Finset.range n, x ^ k * x ^ (n - 1 - k) := by
      have : ∀ k ∈ Finset.range n, x ^ k * x ^ (n - 1 - k) = x ^ (n - 1) := by
        intro k hk; rw [Finset.mem_range] at hk; rw [← pow_add, Nat.add_sub_cancel' (by omega)]
      rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hsum]
    apply Finset.sum_lt_sum
    · intro k _
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hxy.le _) (pow_nonneg hx _)
    · refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
      simp only [pow_zero, one_mul, Nat.sub_zero]
      exact pow_lt_pow_left₀ hxy hx (by omega)
  have h2 : ∑ k ∈ Finset.range n, x ^ k * y ^ (n - 1 - k) < (n : ℝ) * y ^ (n - 1) := by
    have hsum : (n : ℝ) * y ^ (n - 1) = ∑ k ∈ Finset.range n, y ^ k * y ^ (n - 1 - k) := by
      have : ∀ k ∈ Finset.range n, y ^ k * y ^ (n - 1 - k) = y ^ (n - 1) := by
        intro k hk; rw [Finset.mem_range] at hk; rw [← pow_add, Nat.add_sub_cancel' (by omega)]
      rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hsum]
    apply Finset.sum_lt_sum
    · intro k _
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx hxy.le _) (pow_nonneg (le_trans hx hxy.le) _)
    · refine ⟨n - 1, Finset.mem_range.mpr (by omega), ?_⟩
      simp only [Nat.sub_self, pow_zero, mul_one]
      exact pow_lt_pow_left₀ hxy hx (by omega)
  exact ⟨(lt_div_iff₀ hnR).mpr (by linarith), (div_lt_iff₀ hnR).mpr (by linarith)⟩

lemma poolAvg_strictMono {n : ℕ} (hn : 2 ≤ n) {x₁ y₁ x₂ y₂ : ℝ}
    (hx₁ : 0 < x₁) (hy₁ : 0 < y₁) (hx : x₁ < x₂) (hy : y₁ < y₂) :
    poolAvg n x₁ y₁ < poolAvg n x₂ y₂ := by
  rw [poolAvg_eq_sum n (by omega), poolAvg_eq_sum n (by omega)]
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  apply div_lt_div_of_pos_right _ hnR
  apply Finset.sum_lt_sum
  · intro k _
    exact mul_le_mul (pow_le_pow_left₀ hx₁.le hx.le _) (pow_le_pow_left₀ hy₁.le hy.le _)
      (pow_nonneg hy₁.le _) (pow_nonneg (le_trans hx₁.le hx.le) _)
  · refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
    simp only [pow_zero, one_mul, Nat.sub_zero]
    exact pow_lt_pow_left₀ hy hy₁.le (by omega)

lemma poolAvg_continuous (n : ℕ) (hn : 1 ≤ n) :
    Continuous (fun p : ℝ × ℝ => poolAvg n p.1 p.2) := by
  have heq : (fun p : ℝ × ℝ => poolAvg n p.1 p.2) =
      fun p => (∑ k ∈ Finset.range n, p.1 ^ k * p.2 ^ (n - 1 - k)) / (n : ℝ) := by
    ext p; exact poolAvg_eq_sum n hn p.1 p.2
  rw [heq]
  fun_prop

/-- First-order Taylor bound for `(A + h)^k` on `|h| ≤ 1`. -/
lemma pow_first_order_bound (k : ℕ) (A : ℝ) :
    ∃ C ≥ 0, ∀ h : ℝ, |h| ≤ 1 →
      |(A + h) ^ k - A ^ k - (k : ℝ) * A ^ (k - 1) * h| ≤ C * h ^ 2 := by
  induction k with
  | zero =>
    refine ⟨0, le_rfl, fun h _ => ?_⟩
    simp
  | succ k ih =>
    cases k with
    | zero =>
      refine ⟨0, le_rfl, fun h _ => ?_⟩
      simp
    | succ m =>
      obtain ⟨C, hC, hbound⟩ := ih
      refine ⟨(|A| + 1) * C + ((m + 1 : ℕ) : ℝ) * |A| ^ m, by positivity, fun h hh => ?_⟩
      have hid : (A + h) ^ (m + 2) - A ^ (m + 2) - ((m + 2 : ℕ) : ℝ) * A ^ (m + 1) * h =
          (A + h) * ((A + h) ^ (m + 1) - A ^ (m + 1) - ((m + 1 : ℕ) : ℝ) * A ^ m * h) +
            ((m + 1 : ℕ) : ℝ) * A ^ m * h ^ 2 := by
        push_cast; ring
      rw [show m + 1 + 1 - 1 = m + 1 by omega, hid]
      have h1 : |A + h| ≤ |A| + 1 := le_trans (abs_add_le A h) (by linarith)
      have h2' : |(A + h) ^ (m + 1) - A ^ (m + 1) - ((m + 1 : ℕ) : ℝ) * A ^ m * h| ≤ C * h ^ 2 := by
        simpa using hbound h hh
      calc |(A + h) * ((A + h) ^ (m + 1) - A ^ (m + 1) - ((m + 1 : ℕ) : ℝ) * A ^ m * h) +
              ((m + 1 : ℕ) : ℝ) * A ^ m * h ^ 2|
          ≤ |A + h| * |(A + h) ^ (m + 1) - A ^ (m + 1) - ((m + 1 : ℕ) : ℝ) * A ^ m * h| +
              |((m + 1 : ℕ) : ℝ) * A ^ m * h ^ 2| := by
            rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ (|A| + 1) * (C * h ^ 2) + ((m + 1 : ℕ) : ℝ) * |A| ^ m * h ^ 2 := by
            gcongr
            rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (m + 1 : ℕ)),
              abs_pow, abs_of_nonneg (sq_nonneg h)]
        _ = ((|A| + 1) * C + ((m + 1 : ℕ) : ℝ) * |A| ^ m) * h ^ 2 := by ring

/-- First-order Taylor bound for `poolAvg n (A + h₁) (A + h₂)` on `|h₁|, |h₂| ≤ 1`. -/
lemma poolAvg_first_order_bound (n : ℕ) (hn : 2 ≤ n) (A : ℝ) :
    ∃ C ≥ 0, ∀ h₁ h₂ : ℝ, |h₁| ≤ 1 → |h₂| ≤ 1 →
      |poolAvg n (A + h₁) (A + h₂) - A ^ (n - 1) -
        ((n : ℝ) - 1) * A ^ (n - 2) * ((h₁ + h₂) / 2)| ≤ C * (|h₁| + |h₂|) ^ 2 := by
  have hterm : ∀ k ∈ Finset.range n,
      ∃ Ck ≥ 0, ∀ h₁ h₂ : ℝ, |h₁| ≤ 1 → |h₂| ≤ 1 →
        |(A + h₁) ^ k * (A + h₂) ^ (n - 1 - k) - A ^ (n - 1) -
          ((k : ℝ) * h₁ + ((n - 1 - k : ℕ) : ℝ) * h₂) * A ^ (n - 2)| ≤
          Ck * (|h₁| + |h₂|) ^ 2 := by
    intro k hk
    rw [Finset.mem_range] at hk
    obtain ⟨C₁, hC₁, hb₁⟩ := pow_first_order_bound k A
    obtain ⟨C₂, hC₂, hb₂⟩ := pow_first_order_bound (n - 1 - k) A
    set j := n - 1 - k with hj_def
    let M₁ := (|A| + 1) ^ j
    let M₂ := |A| ^ k
    let M₃ := (k : ℝ) * |A| ^ (k - 1) * ((j : ℝ) * |A| ^ (j - 1))
    let M₄ := (k : ℝ) * |A| ^ (k - 1) * C₂
    refine ⟨C₁ * M₁ + M₂ * C₂ + M₃ + M₄, by positivity, fun h₁ h₂ hh₁ hh₂ => ?_⟩
    set r₁ := (A + h₁) ^ k - A ^ k - (k : ℝ) * A ^ (k - 1) * h₁
    set r₂ := (A + h₂) ^ j - A ^ j - (j : ℝ) * A ^ (j - 1) * h₂
    have hr₁ : |r₁| ≤ C₁ * h₁ ^ 2 := hb₁ h₁ hh₁
    have hr₂ : |r₂| ≤ C₂ * h₂ ^ 2 := hb₂ h₂ hh₂
    have hkj : k + j = n - 1 := by omega
    have hpow : A ^ k * A ^ j = A ^ (n - 1) := by rw [← pow_add, hkj]
    have hpow1 : (k : ℝ) * A ^ (k - 1) * A ^ j = (k : ℝ) * A ^ (n - 2) := by
      cases k with
      | zero => simp
      | succ k' =>
        have : k' + j = n - 2 := by omega
        rw [Nat.add_sub_cancel, mul_assoc, ← pow_add, this]
    have hpow2 : A ^ k * ((j : ℝ) * A ^ (j - 1)) = (j : ℝ) * A ^ (n - 2) := by
      cases hj : j with
      | zero => simp
      | succ j' =>
        have : k + j' = n - 2 := by omega
        rw [Nat.add_sub_cancel, mul_left_comm, ← pow_add, this]
    have hexpand : (A + h₁) ^ k * (A + h₂) ^ j - A ^ (n - 1) -
        ((k : ℝ) * h₁ + (j : ℝ) * h₂) * A ^ (n - 2) =
        r₁ * (A + h₂) ^ j + A ^ k * r₂ +
          (k : ℝ) * A ^ (k - 1) * h₁ * ((j : ℝ) * A ^ (j - 1) * h₂) +
          (k : ℝ) * A ^ (k - 1) * h₁ * r₂ := by
      have hA1 : (A + h₁) ^ k = A ^ k + (k : ℝ) * A ^ (k - 1) * h₁ + r₁ := by
        dsimp [r₁]; ring
      have hA2 : (A + h₂) ^ j = A ^ j + (j : ℝ) * A ^ (j - 1) * h₂ + r₂ := by
        dsimp [r₂]; ring
      calc (A + h₁) ^ k * (A + h₂) ^ j - A ^ (n - 1) -
              ((k : ℝ) * h₁ + (j : ℝ) * h₂) * A ^ (n - 2)
          = (A ^ k + (k : ℝ) * A ^ (k - 1) * h₁) * (A ^ j + (j : ℝ) * A ^ (j - 1) * h₂ + r₂) +
              r₁ * (A + h₂) ^ j - A ^ k * A ^ j -
              ((k : ℝ) * A ^ (k - 1) * A ^ j * h₁ + A ^ k * ((j : ℝ) * A ^ (j - 1)) * h₂) := by
            rw [hpow, hpow1, hpow2]
            conv_lhs => rw [hA1]
            rw [add_mul, hA2]
            ring
        _ = r₁ * (A + h₂) ^ j + A ^ k * r₂ +
              (k : ℝ) * A ^ (k - 1) * h₁ * ((j : ℝ) * A ^ (j - 1) * h₂) +
              (k : ℝ) * A ^ (k - 1) * h₁ * r₂ := by ring
    rw [hexpand]
    have h1le : h₁ ^ 2 ≤ (|h₁| + |h₂|) ^ 2 := by nlinarith [abs_nonneg h₁, abs_nonneg h₂, sq_abs h₁]
    have h2le : h₂ ^ 2 ≤ (|h₁| + |h₂|) ^ 2 := by nlinarith [abs_nonneg h₁, abs_nonneg h₂, sq_abs h₂]
    have h12le : |h₁| * |h₂| ≤ (|h₁| + |h₂|) ^ 2 := by nlinarith [abs_nonneg h₁, abs_nonneg h₂]
    have h122le : |h₁| * h₂ ^ 2 ≤ (|h₁| + |h₂|) ^ 2 := by
      calc |h₁| * h₂ ^ 2 ≤ 1 * h₂ ^ 2 := by gcongr
        _ = h₂ ^ 2 := one_mul _
        _ ≤ (|h₁| + |h₂|) ^ 2 := h2le
    have hA2b : |(A + h₂) ^ j| ≤ M₁ := by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (le_trans (abs_add_le A h₂) (by linarith)) j
    have hb_t1 : |r₁ * (A + h₂) ^ j| ≤ C₁ * M₁ * (|h₁| + |h₂|) ^ 2 := by
      rw [abs_mul]
      calc |r₁| * |(A + h₂) ^ j| ≤ (C₁ * h₁ ^ 2) * M₁ := by gcongr
        _ = C₁ * M₁ * h₁ ^ 2 := by ring
        _ ≤ C₁ * M₁ * (|h₁| + |h₂|) ^ 2 := by gcongr
    have hb_t2 : |A ^ k * r₂| ≤ M₂ * C₂ * (|h₁| + |h₂|) ^ 2 := by
      rw [abs_mul, abs_pow]
      calc |A| ^ k * |r₂| ≤ M₂ * (C₂ * h₂ ^ 2) := by gcongr
        _ = M₂ * C₂ * h₂ ^ 2 := by ring
        _ ≤ M₂ * C₂ * (|h₁| + |h₂|) ^ 2 := by gcongr
    have hb_t3 : |(k : ℝ) * A ^ (k - 1) * h₁ * ((j : ℝ) * A ^ (j - 1) * h₂)| ≤
        M₃ * (|h₁| + |h₂|) ^ 2 := by
      have heq : |(k : ℝ) * A ^ (k - 1) * h₁ * ((j : ℝ) * A ^ (j - 1) * h₂)| =
          M₃ * (|h₁| * |h₂|) := by
        simp only [M₃, abs_mul, abs_pow, Nat.abs_cast]
        ring
      rw [heq]; gcongr
    have hb_t4 : |(k : ℝ) * A ^ (k - 1) * h₁ * r₂| ≤ M₄ * (|h₁| + |h₂|) ^ 2 := by
      have heq : |(k : ℝ) * A ^ (k - 1) * h₁ * r₂| =
          (k : ℝ) * |A| ^ (k - 1) * |h₁| * |r₂| := by
        simp only [abs_mul, abs_pow, Nat.abs_cast]
      rw [heq]
      calc (k : ℝ) * |A| ^ (k - 1) * |h₁| * |r₂|
          ≤ (k : ℝ) * |A| ^ (k - 1) * |h₁| * (C₂ * h₂ ^ 2) := by gcongr
        _ = M₄ * (|h₁| * h₂ ^ 2) := by dsimp [M₄]; ring
        _ ≤ M₄ * (|h₁| + |h₂|) ^ 2 := by gcongr
    have ht1 := abs_add_le (r₁ * (A + h₂) ^ j + A ^ k * r₂ +
      (k : ℝ) * A ^ (k - 1) * h₁ * ((j : ℝ) * A ^ (j - 1) * h₂)) ((k : ℝ) * A ^ (k - 1) * h₁ * r₂)
    have ht2 := abs_add_le (r₁ * (A + h₂) ^ j + A ^ k * r₂)
      ((k : ℝ) * A ^ (k - 1) * h₁ * ((j : ℝ) * A ^ (j - 1) * h₂))
    have ht3 := abs_add_le (r₁ * (A + h₂) ^ j) (A ^ k * r₂)
    linarith
  choose Ck hCk_nonneg hCk using hterm
  refine ⟨(∑ k ∈ Finset.range n, if hk : k ∈ Finset.range n then Ck k hk else 0) / (n : ℝ),
    by apply div_nonneg (Finset.sum_nonneg (fun k hk => by simp only [hk, ↓reduceDIte]; exact hCk_nonneg k hk)) (by positivity),
    fun h₁ h₂ hh₁ hh₂ => ?_⟩
  rw [poolAvg_eq_sum n (by omega)]
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hsum_k : ∑ k ∈ Finset.range n, (k : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
    have hnat : 2 * ∑ k ∈ Finset.range n, k = n * (n - 1) := by
      simpa [Nat.mul_comm] using Finset.sum_range_id_mul_two n
    have hreal : (2 : ℝ) * ∑ k ∈ Finset.range n, (k : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
      have hcast : ((2 * ∑ k ∈ Finset.range n, k : ℕ) : ℝ) = ((n * (n - 1) : ℕ) : ℝ) := by
        exact_mod_cast hnat
      push_cast [Nat.cast_sub (by omega : 1 ≤ n)] at hcast
      linarith
    linarith
  have hsum_nk : ∑ k ∈ Finset.range n, ((n - 1 - k : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
    have h := Finset.sum_range_reflect (fun k => (k : ℝ)) n
    rw [hsum_k] at h
    exact h
  have hdiff : (∑ k ∈ Finset.range n, (A + h₁) ^ k * (A + h₂) ^ (n - 1 - k)) / (n : ℝ) -
      A ^ (n - 1) - ((n : ℝ) - 1) * A ^ (n - 2) * ((h₁ + h₂) / 2) =
      (∑ k ∈ Finset.range n, ((A + h₁) ^ k * (A + h₂) ^ (n - 1 - k) - A ^ (n - 1) -
        ((k : ℝ) * h₁ + ((n - 1 - k : ℕ) : ℝ) * h₂) * A ^ (n - 2))) / (n : ℝ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, ← Finset.sum_mul]
    simp_rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsum_k, hsum_nk]
    field_simp [hnR.ne']
  rw [hdiff, abs_div, abs_of_pos hnR]
  calc |∑ k ∈ Finset.range n, ((A + h₁) ^ k * (A + h₂) ^ (n - 1 - k) - A ^ (n - 1) -
          ((k : ℝ) * h₁ + ((n - 1 - k : ℕ) : ℝ) * h₂) * A ^ (n - 2))| / (n : ℝ)
      ≤ (∑ k ∈ Finset.range n, |(A + h₁) ^ k * (A + h₂) ^ (n - 1 - k) - A ^ (n - 1) -
          ((k : ℝ) * h₁ + ((n - 1 - k : ℕ) : ℝ) * h₂) * A ^ (n - 2)|) / (n : ℝ) := by
        gcongr; exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (∑ k ∈ Finset.range n, (if hk : k ∈ Finset.range n then Ck k hk else 0) * (|h₁| + |h₂|) ^ 2) / (n : ℝ) := by
        gcongr with k hk
        simp only [hk, ↓reduceDIte]
        exact hCk k hk h₁ h₂ hh₁ hh₂
    _ = ((∑ k ∈ Finset.range n, if hk : k ∈ Finset.range n then Ck k hk else 0) / (n : ℝ)) *
          (|h₁| + |h₂|) ^ 2 := by
        rw [← Finset.sum_mul, div_mul_eq_mul_div]

/-! ### Uniform Visit Strategy -/

/-- The uniform visit strategy `θ_j(v) = 1 / m` for all `j, v`. -/
noncomputable def unifVisit (M : Market) : VisitStrategy M where
  θ := fun _ _ => 1 / (M.m : ℝ)
  hmeas := fun _ => measurable_const
  hnonneg := fun _ _ => by positivity
  hsum := fun _ _ => by
    rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_one_div_cancel M.m_pos_real.ne']

lemma effDist_unif (M : Market) (j : Fin M.m) {v : ℝ} (hv : v ∈ Icc M.a 1) :
    effDist M (unifVisit M) j v = M.A v := by
  unfold effDist unifVisit Market.A
  simp only [intervalIntegral.integral_const_mul]
  rw [← M.F_sub_eq_integral hv.1 hv.2 le_rfl, M.hF_1]
  ring

lemma alloc_SPA_unif (M : Market) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hρa : M.a ≤ ρ)
    (j : Fin M.m) {v : ℝ} (hv1 : v ≤ 1) :
    alloc M (SPA ρ hρ0 hρ1) (effDist M (unifVisit M) j) v =
      if v < ρ then 0 else M.A v ^ (M.n - 1) := by
  unfold alloc SPA
  simp only [List.find?_nil]
  split_ifs with h
  · rfl
  · push Not at h
    rw [effDist_unif M j ⟨le_trans hρa h, hv1⟩]

lemma surplus_SPA_unif (M : Market) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hρa : M.a ≤ ρ)
    (j : Fin M.m) {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    surplus M (SPA ρ hρ0 hρ1) (effDist M (unifVisit M) j) v =
      if v ≤ ρ then 0 else ∫ u in ρ..v, M.A u ^ (M.n - 1) := by
  unfold surplus
  split_ifs with hvρ
  · rw [intervalIntegral_congr_Ioo hv0 (g := fun _ => (0 : ℝ)) (fun u hu => by
      rw [alloc_SPA_unif M hρ0 hρ1 hρa j (le_trans hu.2.le hv1)]
      simp [lt_of_lt_of_le hu.2 hvρ])]
    simp
  · push Not at hvρ
    have hcontA : ContinuousOn (fun u => M.A u ^ (M.n - 1)) (Icc ρ v) :=
      (M.A_continuousOn.mono (Icc_subset_Icc hρa hv1)).pow _
    have hint1 : IntervalIntegrable (alloc M (SPA ρ hρ0 hρ1) (effDist M (unifVisit M) j)) volume 0 ρ := by
      rw [intervalIntegrable_congr_Ioo hρ0 (g := fun _ => (0 : ℝ)) (fun u hu => by
        rw [alloc_SPA_unif M hρ0 hρ1 hρa j (le_trans hu.2.le hρ1)]
        simp [hu.2])]
      exact intervalIntegrable_const
    have hint2 : IntervalIntegrable (alloc M (SPA ρ hρ0 hρ1) (effDist M (unifVisit M) j)) volume ρ v := by
      rw [intervalIntegrable_congr_Ioo hvρ.le (g := fun u => M.A u ^ (M.n - 1)) (fun u hu => by
        rw [alloc_SPA_unif M hρ0 hρ1 hρa j (le_trans hu.2.le hv1)]
        simp [not_lt.mpr hu.1.le])]
      exact (hcontA.mono (by rw [uIcc_of_le hvρ.le])).intervalIntegrable
    rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
    have h0 : ∫ u in (0 : ℝ)..ρ, alloc M (SPA ρ hρ0 hρ1) (effDist M (unifVisit M) j) u = 0 := by
      rw [intervalIntegral_congr_Ioo hρ0 (g := fun _ => (0 : ℝ)) (fun u hu => by
        rw [alloc_SPA_unif M hρ0 hρ1 hρa j (le_trans hu.2.le hρ1)]
        simp [hu.2])]
      simp
    rw [h0, zero_add]
    exact intervalIntegral_congr_Ioo hvρ.le (fun u hu => by
      rw [alloc_SPA_unif M hρ0 hρ1 hρa j (le_trans hu.2.le hv1)]
      simp [not_lt.mpr hu.1.le])

lemma isSR_SPA_unif (M : Market) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hρa : M.a ≤ ρ) :
    IsSR M (fun _ => SPA ρ hρ0 hρ1) (unifVisit M) := by
  filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv j k _
  have hv0 : 0 ≤ v := le_trans M.ha0 hv.1
  rw [surplus_SPA_unif M hρ0 hρ1 hρa k hv0 hv.2, surplus_SPA_unif M hρ0 hρ1 hρa j hv0 hv.2]

/-! ### Theorem 3: Asking-Price Deviation at Binding Reserves -/

section Theorem3

/-- Symmetric per-seller upper-tail traffic above `ρ`: `q_ρ = (1 - F(ρ)) / m`. -/
noncomputable def qRho (M : Market) (ρ : ℝ) : ℝ :=
  (1 - M.F ρ) / (M.m : ℝ)

lemma qRho_pos (M : Market) {ρ : ℝ} (hρa : M.a ≤ ρ) (hρ1 : ρ < 1) : 0 < qRho M ρ := by
  unfold qRho
  have hF : M.F ρ < 1 := by
    rw [← M.hF_1]
    exact M.F_strictMonoOn ⟨hρa, hρ1.le⟩ (right_mem_Icc.mpr M.ha1.le) hρ1
  exact div_pos (sub_pos.mpr hF) M.m_pos_real

lemma qRho_le_half (M : Market) {ρ : ℝ} (hρa : M.a ≤ ρ) (hρ1 : ρ ≤ 1) : qRho M ρ ≤ 1 / 2 := by
  unfold qRho
  have hF0 : 0 ≤ M.F ρ := (M.F_mem_Icc ⟨hρa, hρ1⟩).1
  have hm : (2 : ℝ) ≤ M.m := by exact_mod_cast M.hm
  calc (1 - M.F ρ) / (M.m : ℝ) ≤ 1 / (M.m : ℝ) := div_le_div_of_nonneg_right (by linarith) M.m_pos_real.le
    _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hm

/-- Indifference residual for the asking-price construction:
`φ(e, y) = (1 - q₀(y))^(n-1) - poolAvg n (1 - t₀(y)) (1 - q₁(y))`. -/
noncomputable def askingPhi (M : Market) (ρ e y : ℝ) : ℝ :=
  (1 - (qRho M ρ + (y - e) / ((M.m : ℝ) - 1))) ^ (M.n - 1) -
    poolAvg M.n (1 - (qRho M ρ - y + e)) (1 - (qRho M ρ - y))

lemma askingPhi_strictAntiOn (M : Market) {ρ : ℝ} (hρa : M.a ≤ ρ) (hρ1 : ρ < 1)
    {e : ℝ} (he0 : 0 < e) (heq : e < qRho M ρ) :
    StrictAntiOn (askingPhi M ρ e) (Icc (e / (M.m : ℝ)) e) := by
  intro y₁ hy₁ y₂ hy₂ hlt
  unfold askingPhi
  have hqhalf := qRho_le_half M hρa hρ1.le
  have hm1 : (0 : ℝ) < (M.m : ℝ) - 1 := M.m_sub_one_pos_real
  have hq0_lt : qRho M ρ + (y₁ - e) / ((M.m : ℝ) - 1) < qRho M ρ + (y₂ - e) / ((M.m : ℝ) - 1) := by
    have : (y₁ - e) / ((M.m : ℝ) - 1) < (y₂ - e) / ((M.m : ℝ) - 1) :=
      div_lt_div_of_pos_right (by linarith) hm1
    linarith
  have h1q0_pos : 0 ≤ 1 - (qRho M ρ + (y₂ - e) / ((M.m : ℝ) - 1)) := by
    have : (y₂ - e) / ((M.m : ℝ) - 1) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith [hy₂.2]) hm1.le
    linarith
  have hpow : (1 - (qRho M ρ + (y₂ - e) / ((M.m : ℝ) - 1))) ^ (M.n - 1) <
      (1 - (qRho M ρ + (y₁ - e) / ((M.m : ℝ) - 1))) ^ (M.n - 1) :=
    pow_lt_pow_left₀ (by linarith) h1q0_pos M.n_sub_one_ne_zero
  have h1t0_pos : 0 < 1 - (qRho M ρ - y₁ + e) := by
    have : 0 < y₁ := lt_of_lt_of_le (div_pos he0 M.m_pos_real) hy₁.1
    linarith
  have h1q1_pos : 0 < 1 - (qRho M ρ - y₁) := by linarith
  have hpool : poolAvg M.n (1 - (qRho M ρ - y₁ + e)) (1 - (qRho M ρ - y₁)) <
      poolAvg M.n (1 - (qRho M ρ - y₂ + e)) (1 - (qRho M ρ - y₂)) :=
    poolAvg_strictMono M.hn h1t0_pos h1q1_pos (by linarith) (by linarith)
  linarith

lemma askingPhi_left_pos (M : Market) {ρ : ℝ} (hρa : M.a ≤ ρ) (hρ1 : ρ < 1)
    {e : ℝ} (he0 : 0 < e) (heq : e < qRho M ρ) :
    0 < askingPhi M ρ e (e / (M.m : ℝ)) := by
  unfold askingPhi
  have hqhalf := qRho_le_half M hρa hρ1.le
  have hm : (0 : ℝ) < M.m := M.m_pos_real
  have hm1 : (0 : ℝ) < (M.m : ℝ) - 1 := M.m_sub_one_pos_real
  have h1 : qRho M ρ + (e / (M.m : ℝ) - e) / ((M.m : ℝ) - 1) = qRho M ρ - e / (M.m : ℝ) := by
    field_simp [hm.ne', hm1.ne']; ring
  rw [h1]
  have hx : 0 ≤ 1 - (qRho M ρ - e / (M.m : ℝ) + e) := by
    have : 0 < e / (M.m : ℝ) := div_pos he0 hm
    linarith
  have hbounds := poolAvg_strict_bounds M.hn hx
    (by linarith : 1 - (qRho M ρ - e / (M.m : ℝ) + e) < 1 - (qRho M ρ - e / (M.m : ℝ)))
  linarith [hbounds.2]

lemma askingPhi_right_neg (M : Market) {ρ : ℝ} (hρa : M.a ≤ ρ) (hρ1 : ρ < 1)
    {e : ℝ} (he0 : 0 < e) (heq : e < qRho M ρ) :
    askingPhi M ρ e e < 0 := by
  unfold askingPhi
  have hqhalf := qRho_le_half M hρa hρ1.le
  have h1 : qRho M ρ + (e - e) / ((M.m : ℝ) - 1) = qRho M ρ := by simp
  have h2 : qRho M ρ - e + e = qRho M ρ := by ring
  rw [h1, h2]
  have hx : 0 ≤ 1 - qRho M ρ := by linarith
  have hbounds := poolAvg_strict_bounds M.hn hx (by linarith : 1 - qRho M ρ < 1 - (qRho M ρ - e))
  linarith [hbounds.1]

lemma exists_unique_askingY (M : Market) {ρ : ℝ} (hρa : M.a ≤ ρ) (hρ1 : ρ < 1)
    {e : ℝ} (he0 : 0 < e) (heq : e < qRho M ρ) :
    ∃! y, y ∈ Ioo (e / (M.m : ℝ)) e ∧ askingPhi M ρ e y = 0 := by
  have hm : (2 : ℝ) ≤ M.m := by exact_mod_cast M.hm
  have hle : e / (M.m : ℝ) ≤ e := by
    rw [div_le_iff₀ M.m_pos_real]; nlinarith
  have hcont : ContinuousOn (askingPhi M ρ e) (Icc (e / (M.m : ℝ)) e) := by
    have hc : Continuous (askingPhi M ρ e) := by
      unfold askingPhi
      have hp := poolAvg_continuous M.n (by have := M.hn; omega)
      have h1 : Continuous (fun y : ℝ => (1 - (qRho M ρ + (y - e) / ((M.m : ℝ) - 1))) ^ (M.n - 1)) := by
        fun_prop
      have h2 : Continuous (fun y : ℝ => poolAvg M.n (1 - (qRho M ρ - y + e)) (1 - (qRho M ρ - y))) :=
        hp.comp (Continuous.prodMk (by fun_prop) (by fun_prop))
      exact h1.sub h2
    exact hc.continuousOn
  have hpos := askingPhi_left_pos M hρa hρ1 he0 heq
  have hneg := askingPhi_right_neg M hρa hρ1 he0 heq
  obtain ⟨y, hy, hzy⟩ := intermediate_value_Icc' hle hcont ⟨hneg.le, hpos.le⟩
  have hy_open : y ∈ Ioo (e / (M.m : ℝ)) e := by
    refine ⟨lt_of_le_of_ne hy.1 ?_, lt_of_le_of_ne hy.2 ?_⟩
    · intro h; rw [← h] at hzy; linarith
    · intro h; rw [h] at hzy; linarith
  refine ⟨y, ⟨hy_open, hzy⟩, ?_⟩
  rintro y' ⟨hy', hzy'⟩
  exact (askingPhi_strictAntiOn M hρa hρ1 he0 heq).injOn
    (Ioo_subset_Icc_self hy') hy (hzy'.trans hzy.symm)

/-- The unique indifference parameter `y(e) ∈ (e/m, e)` for the asking-price deviation. -/
noncomputable def askingY (M : Market) (ρ e : ℝ) : ℝ :=
  if h : M.a ≤ ρ ∧ ρ < 1 ∧ 0 < e ∧ e < qRho M ρ then
    (exists_unique_askingY M h.1 h.2.1 h.2.2.1 h.2.2.2).choose
  else 0

lemma askingY_spec (M : Market) {ρ : ℝ} (hρa : M.a ≤ ρ) (hρ1 : ρ < 1)
    {e : ℝ} (he0 : 0 < e) (heq : e < qRho M ρ) :
    askingY M ρ e ∈ Ioo (e / (M.m : ℝ)) e ∧ askingPhi M ρ e (askingY M ρ e) = 0 := by
  unfold askingY
  simp only [hρa, hρ1, he0, heq, and_self, ↓reduceDIte]
  exact (exists_unique_askingY M hρa hρ1 he0 heq).choose_spec.1

/-- Derived asking-price quantities: `q₁, t₀, q₀, v₁, v₂, barx, F_riv, β`. -/
noncomputable def askingQ1 (M : Market) (ρ e : ℝ) : ℝ := qRho M ρ - askingY M ρ e
noncomputable def askingT0 (M : Market) (ρ e : ℝ) : ℝ := askingQ1 M ρ e + e
noncomputable def askingQ0 (M : Market) (ρ e : ℝ) : ℝ :=
  qRho M ρ + (askingY M ρ e - e) / ((M.m : ℝ) - 1)
noncomputable def askingV1 (M : Market) (ρ e : ℝ) : ℝ := M.invF (M.F ρ + e)
noncomputable def askingV2 (M : Market) (ρ e : ℝ) : ℝ := M.invF (M.F ρ + (M.m : ℝ) * askingY M ρ e)
noncomputable def askingBarX (M : Market) (ρ e : ℝ) : ℝ := (1 - askingQ0 M ρ e) ^ (M.n - 1)
noncomputable def askingFriv (M : Market) (ρ e v : ℝ) : ℝ :=
  1 - askingQ1 M ρ e - (M.F (askingV2 M ρ e) - M.F v) / ((M.m : ℝ) - 1)
noncomputable def askingBeta (M : Market) (ρ e : ℝ) : ℝ :=
  askingV2 M ρ e -
    (∫ v in askingV1 M ρ e..askingV2 M ρ e, (askingFriv M ρ e v ^ (M.n - 1) - askingBarX M ρ e)) /
      ((1 - askingQ1 M ρ e) ^ (M.n - 1) - askingBarX M ρ e)

lemma asking_coords (M : Market) {ρ : ℝ} (hρa : M.a ≤ ρ) (hρ1 : ρ < 1)
    {e : ℝ} (he0 : 0 < e) (heq : e < qRho M ρ) :
    0 < askingQ1 M ρ e ∧ askingQ1 M ρ e < askingQ0 M ρ e ∧
    askingQ0 M ρ e < qRho M ρ ∧ qRho M ρ < askingT0 M ρ e ∧ askingT0 M ρ e < 1 ∧
    ρ < askingV1 M ρ e ∧ askingV1 M ρ e < askingV2 M ρ e ∧ askingV2 M ρ e < 1 ∧
    M.F (askingV1 M ρ e) = M.F ρ + e ∧ M.F (askingV2 M ρ e) = M.F ρ + (M.m : ℝ) * askingY M ρ e ∧
    M.A (askingV2 M ρ e) = 1 - askingQ1 M ρ e ∧
    askingFriv M ρ e (askingV1 M ρ e) = 1 - askingQ0 M ρ e ∧
    askingFriv M ρ e (askingV2 M ρ e) = 1 - askingQ1 M ρ e ∧
    askingBarX M ρ e = poolAvg M.n (1 - askingT0 M ρ e) (1 - askingQ1 M ρ e) ∧
    askingV1 M ρ e < askingBeta M ρ e ∧ askingBeta M ρ e < askingV2 M ρ e := by
  have hys := askingY_spec M hρa hρ1 he0 heq
  have hy_lo : e / (M.m : ℝ) < askingY M ρ e := hys.1.1
  have hy_hi : askingY M ρ e < e := hys.1.2
  have hm : (0 : ℝ) < M.m := M.m_pos_real
  have hm1 : (0 : ℝ) < (M.m : ℝ) - 1 := M.m_sub_one_pos_real
  have hqhalf := qRho_le_half M hρa hρ1.le
  have hFρ_mem := M.F_mem_Icc ⟨hρa, hρ1.le⟩
  have hq1_pos : 0 < askingQ1 M ρ e := by unfold askingQ1; linarith
  have hmy_gt_e : e < (M.m : ℝ) * askingY M ρ e := by
    rwa [div_lt_iff₀ hm, mul_comm] at hy_lo
  have hq1_lt_q0 : askingQ1 M ρ e < askingQ0 M ρ e := by
    unfold askingQ1 askingQ0
    have : 0 < ((M.m : ℝ) * askingY M ρ e - e) / ((M.m : ℝ) - 1) :=
      div_pos (by linarith) hm1
    have hid : (qRho M ρ + (askingY M ρ e - e) / ((M.m : ℝ) - 1)) - (qRho M ρ - askingY M ρ e) =
        ((M.m : ℝ) * askingY M ρ e - e) / ((M.m : ℝ) - 1) := by
      field_simp [hm1.ne']; ring
    linarith
  have hq0_lt_qr : askingQ0 M ρ e < qRho M ρ := by
    unfold askingQ0
    have : (askingY M ρ e - e) / ((M.m : ℝ) - 1) < 0 := div_neg_of_neg_of_pos (by linarith) hm1
    linarith
  have hqr_lt_t0 : qRho M ρ < askingT0 M ρ e := by unfold askingT0 askingQ1; linarith
  have ht0_lt_1 : askingT0 M ρ e < 1 := by
    unfold askingT0 askingQ1
    have : 0 < askingY M ρ e := lt_trans (div_pos he0 hm) hy_lo
    linarith
  have hFe_le1 : M.F ρ + e < 1 := by
    have : (M.m : ℝ) * qRho M ρ = 1 - M.F ρ := by unfold qRho; field_simp [hm.ne']
    have hm2 : (2 : ℝ) ≤ M.m := by exact_mod_cast M.hm
    nlinarith
  have hFmy_lt1 : M.F ρ + (M.m : ℝ) * askingY M ρ e < 1 := by
    have : (M.m : ℝ) * qRho M ρ = 1 - M.F ρ := by unfold qRho; field_simp [hm.ne']
    nlinarith
  have hFv1 : M.F (askingV1 M ρ e) = M.F ρ + e :=
    M.F_invF (by linarith [hFρ_mem.1]) hFe_le1.le
  have hFv2 : M.F (askingV2 M ρ e) = M.F ρ + (M.m : ℝ) * askingY M ρ e :=
    M.F_invF (by linarith [hFρ_mem.1]) hFmy_lt1.le
  have hρ_lt_v1 : ρ < askingV1 M ρ e := by
    have : M.invF (M.F ρ) < M.invF (M.F ρ + e) :=
      M.invF_strictMonoOn hFρ_mem ⟨by linarith [hFρ_mem.1], hFe_le1.le⟩ (by linarith)
    rwa [M.invF_F ⟨hρa, hρ1.le⟩] at this
  have hv1_lt_v2 : askingV1 M ρ e < askingV2 M ρ e :=
    M.invF_strictMonoOn ⟨by linarith [hFρ_mem.1], hFe_le1.le⟩
      ⟨by linarith [hFρ_mem.1], hFmy_lt1.le⟩ (by linarith)
  have hv2_lt_1 : askingV2 M ρ e < 1 := by
    have : M.invF (M.F ρ + (M.m : ℝ) * askingY M ρ e) < M.invF (M.F 1) :=
      M.invF_strictMonoOn ⟨by linarith [hFρ_mem.1], hFmy_lt1.le⟩
        (by rw [M.hF_1]; exact right_mem_Icc.mpr zero_le_one) (by rw [M.hF_1]; exact hFmy_lt1)
    rwa [M.invF_F (right_mem_Icc.mpr M.ha1.le)] at this
  have hAv2 : M.A (askingV2 M ρ e) = 1 - askingQ1 M ρ e := by
    unfold Market.A askingQ1 qRho
    rw [hFv2]
    field_simp [hm.ne']
    ring
  have hFriv_v1 : askingFriv M ρ e (askingV1 M ρ e) = 1 - askingQ0 M ρ e := by
    unfold askingFriv askingQ1 askingQ0
    rw [hFv2, hFv1]
    field_simp [hm1.ne']
    ring
  have hFriv_v2 : askingFriv M ρ e (askingV2 M ρ e) = 1 - askingQ1 M ρ e := by
    unfold askingFriv; simp
  have hbarx : askingBarX M ρ e = poolAvg M.n (1 - askingT0 M ρ e) (1 - askingQ1 M ρ e) := by
    have h0 := hys.2
    unfold askingPhi at h0
    unfold askingBarX askingQ0 askingT0 askingQ1
    linarith
  have hden_pos : 0 < (1 - askingQ1 M ρ e) ^ (M.n - 1) - askingBarX M ρ e := by
    unfold askingBarX
    have : (1 - askingQ0 M ρ e) ^ (M.n - 1) < (1 - askingQ1 M ρ e) ^ (M.n - 1) :=
      pow_lt_pow_left₀ (by linarith) (by linarith) M.n_sub_one_ne_zero
    linarith
  have hFriv_cont : ContinuousOn (fun v => askingFriv M ρ e v ^ (M.n - 1) - askingBarX M ρ e)
      (Icc (askingV1 M ρ e) (askingV2 M ρ e)) := by
    have hF_sub : ContinuousOn M.F (Icc (askingV1 M ρ e) (askingV2 M ρ e)) :=
      M.F_continuousOn.mono (Icc_subset_Icc (le_trans hρa hρ_lt_v1.le) hv2_lt_1.le)
    unfold askingFriv
    fun_prop
  have hFriv_bounds : ∀ v ∈ Ioo (askingV1 M ρ e) (askingV2 M ρ e),
      0 < askingFriv M ρ e v ^ (M.n - 1) - askingBarX M ρ e ∧
      askingFriv M ρ e v ^ (M.n - 1) - askingBarX M ρ e <
        (1 - askingQ1 M ρ e) ^ (M.n - 1) - askingBarX M ρ e := by
    intro v hv
    have hv_mem : v ∈ Icc M.a 1 := ⟨le_trans hρa (le_trans hρ_lt_v1.le hv.1.le), le_trans hv.2.le hv2_lt_1.le⟩
    have hv1_mem : askingV1 M ρ e ∈ Icc M.a 1 := ⟨le_trans hρa hρ_lt_v1.le, le_trans hv1_lt_v2.le hv2_lt_1.le⟩
    have hv2_mem : askingV2 M ρ e ∈ Icc M.a 1 := ⟨le_trans hρa (le_trans hρ_lt_v1.le hv1_lt_v2.le), hv2_lt_1.le⟩
    have hFv1_lt : M.F (askingV1 M ρ e) < M.F v := M.F_strictMonoOn hv1_mem hv_mem hv.1
    have hFv_lt : M.F v < M.F (askingV2 M ρ e) := M.F_strictMonoOn hv_mem hv2_mem hv.2
    have hlo : 1 - askingQ0 M ρ e < askingFriv M ρ e v := by
      rw [← hFriv_v1]; unfold askingFriv
      have : (M.F (askingV2 M ρ e) - M.F v) / ((M.m : ℝ) - 1) <
          (M.F (askingV2 M ρ e) - M.F (askingV1 M ρ e)) / ((M.m : ℝ) - 1) :=
        div_lt_div_of_pos_right (by linarith) hm1
      linarith
    have hhi : askingFriv M ρ e v < 1 - askingQ1 M ρ e := by
      unfold askingFriv
      have : 0 < (M.F (askingV2 M ρ e) - M.F v) / ((M.m : ℝ) - 1) := div_pos (by linarith) hm1
      linarith
    unfold askingBarX
    constructor
    · have := pow_lt_pow_left₀ hlo (by linarith : 0 ≤ 1 - askingQ0 M ρ e) M.n_sub_one_ne_zero
      linarith
    · have := pow_lt_pow_left₀ hhi (by linarith : 0 ≤ askingFriv M ρ e v) M.n_sub_one_ne_zero
      linarith
  have hvm_mem : (askingV1 M ρ e + askingV2 M ρ e) / 2 ∈ Ioo (askingV1 M ρ e) (askingV2 M ρ e) :=
    ⟨by linarith, by linarith⟩
  have hint_pos : 0 < ∫ v in askingV1 M ρ e..askingV2 M ρ e,
      (askingFriv M ρ e v ^ (M.n - 1) - askingBarX M ρ e) := by
    apply intervalIntegral.integral_pos hv1_lt_v2 hFriv_cont
    · intro v hv
      rcases eq_or_lt_of_le hv.2 with rfl | hlt
      · rw [hFriv_v2]; exact hden_pos.le
      · exact (hFriv_bounds v ⟨hv.1, hlt⟩).1.le
    · exact ⟨(askingV1 M ρ e + askingV2 M ρ e) / 2, Ioo_subset_Icc_self hvm_mem, (hFriv_bounds _ hvm_mem).1⟩
  have hint_lt : ∫ v in askingV1 M ρ e..askingV2 M ρ e,
      (askingFriv M ρ e v ^ (M.n - 1) - askingBarX M ρ e) <
      (askingV2 M ρ e - askingV1 M ρ e) * ((1 - askingQ1 M ρ e) ^ (M.n - 1) - askingBarX M ρ e) := by
    set D := (1 - askingQ1 M ρ e) ^ (M.n - 1) - askingBarX M ρ e
    have hconst : ∫ _ in askingV1 M ρ e..askingV2 M ρ e, D = (askingV2 M ρ e - askingV1 M ρ e) * D := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
    rw [← hconst, ← sub_pos, ← intervalIntegral.integral_sub intervalIntegrable_const
      (hFriv_cont.mono (by rw [uIcc_of_le hv1_lt_v2.le])).intervalIntegrable]
    apply intervalIntegral.integral_pos hv1_lt_v2 (continuousOn_const.sub hFriv_cont)
    · intro v hv
      rcases eq_or_lt_of_le hv.2 with rfl | hlt
      · change 0 ≤ D - (askingFriv M ρ e (askingV2 M ρ e) ^ (M.n - 1) - askingBarX M ρ e)
        rw [hFriv_v2]; dsimp [D]; linarith
      · exact sub_nonneg.mpr (hFriv_bounds v ⟨hv.1, hlt⟩).2.le
    · exact ⟨(askingV1 M ρ e + askingV2 M ρ e) / 2, Ioo_subset_Icc_self hvm_mem,
        sub_pos.mpr (hFriv_bounds _ hvm_mem).2⟩
  have hv1_lt_beta : askingV1 M ρ e < askingBeta M ρ e := by
    unfold askingBeta
    have hdiv : (∫ v in askingV1 M ρ e..askingV2 M ρ e,
        (askingFriv M ρ e v ^ (M.n - 1) - askingBarX M ρ e)) /
        ((1 - askingQ1 M ρ e) ^ (M.n - 1) - askingBarX M ρ e) <
        askingV2 M ρ e - askingV1 M ρ e :=
      (div_lt_iff₀ hden_pos).mpr hint_lt
    linarith
  have hbeta_lt_v2 : askingBeta M ρ e < askingV2 M ρ e := by
    unfold askingBeta
    have : 0 < (∫ v in askingV1 M ρ e..askingV2 M ρ e,
        (askingFriv M ρ e v ^ (M.n - 1) - askingBarX M ρ e)) /
        ((1 - askingQ1 M ρ e) ^ (M.n - 1) - askingBarX M ρ e) :=
      div_pos hint_pos hden_pos
    linarith
  exact ⟨hq1_pos, hq1_lt_q0, hq0_lt_qr, hqr_lt_t0, ht0_lt_1,
    hρ_lt_v1, hv1_lt_v2, hv2_lt_1, hFv1, hFv2, hAv2, hFriv_v1, hFriv_v2, hbarx,
    hv1_lt_beta, hbeta_lt_v2⟩

/-- The asking-price mechanism `(ρ, {(ρ, β)})`. -/
def askingMech (ρ β : ℝ) (hρ0 : 0 ≤ ρ) (hρβ : ρ < β) (hβ1 : β ≤ 1) : HierarchicalMech where
  r := ρ
  hr0 := hρ0
  hr1 := le_trans hρβ.le hβ1
  pools := [⟨ρ, β, hρβ⟩]
  hpools_in := by
    intro I hI
    simp only [List.mem_singleton] at hI
    subst hI
    exact ⟨le_rfl, hβ1⟩
  hpools_disj := List.pairwise_singleton _ _

/-- Mechanism profile where seller `0` posts the asking price `(ρ, {(ρ, β)})`
and all `m - 1` rivals post `SPA(ρ)`. -/
def askingProfile (M : Market) (ρ β : ℝ) (hρ0 : 0 ≤ ρ) (hρβ : ρ < β) (hβ1 : β ≤ 1) :
    Fin M.m → HierarchicalMech :=
  fun j => if j = seller0 M then askingMech ρ β hρ0 hρβ hβ1
           else SPA ρ hρ0 (le_trans hρβ.le hβ1)

lemma askingMech_eq_of_eq {ρ β₁ β₂ : ℝ} (hβ : β₁ = β₂) (hρ0 : 0 ≤ ρ)
    (h1 : ρ < β₁) (h1' : β₁ ≤ 1) (h2 : ρ < β₂) (h2' : β₂ ≤ 1) :
    askingMech ρ β₁ hρ0 h1 h1' = askingMech ρ β₂ hρ0 h2 h2' := by
  subst hβ; rfl

lemma askingProfile_eq_of_eq (M : Market) {ρ β₁ β₂ : ℝ} (hβ : β₁ = β₂) (hρ0 : 0 ≤ ρ)
    (h1 : ρ < β₁) (h1' : β₁ ≤ 1) (h2 : ρ < β₂) (h2' : β₂ ≤ 1) :
    askingProfile M ρ β₁ hρ0 h1 h1' = askingProfile M ρ β₂ hρ0 h2 h2' := by
  subst hβ; rfl

/-- Explicit SR visit strategy for the asking-price deviation:
`θ_0 = 1` on `[ρ, v₁]`, `θ_0 = 0` on `(v₁, v₂)`, and `θ_j = 1/m` elsewhere. -/
noncomputable def askingVisit (M : Market) (ρ e : ℝ) : VisitStrategy M where
  θ := fun j v =>
    if v ∈ Icc ρ (askingV1 M ρ e) then
      if j = seller0 M then 1 else 0
    else if v ∈ Ioo (askingV1 M ρ e) (askingV2 M ρ e) then
      if j = seller0 M then 0 else 1 / ((M.m : ℝ) - 1)
    else
      1 / (M.m : ℝ)
  hmeas := fun _ => by
    apply Measurable.ite measurableSet_Icc measurable_const
    apply Measurable.ite measurableSet_Ioo measurable_const
    exact measurable_const
  hnonneg := fun _ _ => by
    have := M.m_sub_one_pos_real
    have := M.m_pos_real
    split_ifs <;> positivity
  hsum := fun v _ => by
    have hcard : (Finset.univ.erase (seller0 M)).card = M.m - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_fin]
    have hsplit : ∀ g : Fin M.m → ℝ, ∑ j : Fin M.m, g j =
        g (seller0 M) + ∑ j ∈ Finset.univ.erase (seller0 M), g j := fun g =>
      (Finset.add_sum_erase _ g (Finset.mem_univ _)).symm
    by_cases h1 : v ∈ Icc ρ (askingV1 M ρ e)
    · simp only [h1, ↓reduceIte]
      rw [hsplit]; simp only [↓reduceIte]
      have h0 : ∑ j ∈ Finset.univ.erase (seller0 M), (if j = seller0 M then (1 : ℝ) else 0) = 0 :=
        Finset.sum_eq_zero fun j hj => by simp [Finset.ne_of_mem_erase hj]
      rw [h0, add_zero]
    · by_cases h2 : v ∈ Ioo (askingV1 M ρ e) (askingV2 M ρ e)
      · simp only [h1, h2, ↓reduceIte]
        rw [hsplit]; simp only [↓reduceIte, zero_add]
        have hconst : ∑ j ∈ Finset.univ.erase (seller0 M),
            (if j = seller0 M then (0 : ℝ) else 1 / ((M.m : ℝ) - 1)) =
            ∑ _ ∈ Finset.univ.erase (seller0 M), (1 / ((M.m : ℝ) - 1)) :=
          Finset.sum_congr rfl fun j hj => by simp [Finset.ne_of_mem_erase hj]
        rw [hconst, Finset.sum_const, hcard, nsmul_eq_mul,
          Nat.cast_sub (by have := M.hm; omega), Nat.cast_one,
          mul_one_div_cancel M.m_sub_one_pos_real.ne']
      · simp only [h1, h2, ↓reduceIte]
        rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul,
          mul_one_div_cancel M.m_pos_real.ne']

lemma effDist_askingVisit_seller0 (M : Market) {ρ : ℝ} (hρa : M.a ≤ ρ) (hρ1 : ρ < 1)
    {e : ℝ} (he0 : 0 < e) (heq : e < qRho M ρ) {v : ℝ} (hvρ : ρ ≤ v) (hv1 : v ≤ 1) :
    effDist M (askingVisit M ρ e) (seller0 M) v =
      if v ≤ askingV1 M ρ e then
        1 - askingQ1 M ρ e - (M.F (askingV1 M ρ e) - M.F v)
      else if v ≤ askingV2 M ρ e then
        1 - askingQ1 M ρ e
      else M.A v := by
  have hc := asking_coords M hρa hρ1 he0 heq
  rcases hc with ⟨_, _, _, _, _, hρv1, hv1v2, hv21, _, _, hAv2, _, _, _, _, _⟩
  set v₁ := askingV1 M ρ e
  set v₂ := askingV2 M ρ e
  set q₁ := askingQ1 M ρ e
  unfold effDist
  have hf_int : ∀ x y, M.a ≤ x → x ≤ y → y ≤ 1 → IntervalIntegrable M.f volume x y :=
    fun x y hx hxy hy => (M.hf_cont.mono (by rw [uIcc_of_le hxy]; exact Icc_subset_Icc hx hy)).intervalIntegrable
  have hθ_top : ∀ u ∈ Ioo v₂ 1, (askingVisit M ρ e).θ (seller0 M) u * M.f u = (1 / (M.m : ℝ)) * M.f u := by
    intro u hu
    unfold askingVisit; dsimp
    have h1 : ¬(ρ ≤ u ∧ u ≤ askingV1 M ρ e) := fun h => by linarith [h.2, hu.1]
    have h2 : ¬(askingV1 M ρ e < u ∧ u < askingV2 M ρ e) := fun h => by linarith [h.2, hu.1]
    simp [h1, h2]
  have hθ_mid : ∀ u ∈ Ioo v₁ v₂, (askingVisit M ρ e).θ (seller0 M) u * M.f u = 0 := by
    intro u hu
    unfold askingVisit; dsimp
    have h1 : ¬(ρ ≤ u ∧ u ≤ askingV1 M ρ e) := fun h => by linarith [h.2, hu.1]
    have h2 : askingV1 M ρ e < u ∧ u < askingV2 M ρ e := hu
    simp [h1, h2]
  have hθ_bot : ∀ u ∈ Ioo ρ v₁, (askingVisit M ρ e).θ (seller0 M) u * M.f u = M.f u := by
    intro u hu
    unfold askingVisit; dsimp
    have h1 : ρ ≤ u ∧ u ≤ askingV1 M ρ e := ⟨hu.1.le, hu.2.le⟩
    simp [h1]
  have hint_top : ∀ x, v₂ ≤ x → x ≤ 1 →
      IntervalIntegrable (fun u => (askingVisit M ρ e).θ (seller0 M) u * M.f u) volume x 1 ∧
      ∫ u in x..1, (askingVisit M ρ e).θ (seller0 M) u * M.f u = (1 - M.F x) / (M.m : ℝ) := by
    intro x hx2 hx1
    have hcongr : ∀ u ∈ Ioo x 1, (askingVisit M ρ e).θ (seller0 M) u * M.f u = (1 / (M.m : ℝ)) * M.f u :=
      fun u hu => hθ_top u ⟨lt_of_le_of_lt hx2 hu.1, hu.2⟩
    refine ⟨(intervalIntegrable_congr_Ioo hx1 hcongr).mpr ((hf_int x 1 (le_trans hρa (by linarith)) hx1 le_rfl).const_mul _), ?_⟩
    rw [intervalIntegral_congr_Ioo hx1 hcongr, intervalIntegral.integral_const_mul,
      ← M.F_sub_eq_integral (le_trans hρa (by linarith)) hx1 le_rfl, M.hF_1]
    ring
  have hI_v2 : ∫ u in v₂..1, (askingVisit M ρ e).θ (seller0 M) u * M.f u = q₁ := by
    rw [(hint_top v₂ le_rfl hv21.le).2]
    have : 1 - (1 - M.F v₂) / (M.m : ℝ) = 1 - q₁ := hAv2
    linarith
  split_ifs with h1 h2
  · have h_bot_int : IntervalIntegrable (fun u => (askingVisit M ρ e).θ (seller0 M) u * M.f u) volume v v₁ := by
      rw [intervalIntegrable_congr_Ioo h1 (fun u hu => hθ_bot u ⟨lt_of_le_of_lt hvρ hu.1, hu.2⟩)]
      exact hf_int v v₁ (le_trans hρa hvρ) h1 (le_trans hv1v2.le hv21.le)
    have h_mid_int : IntervalIntegrable (fun u => (askingVisit M ρ e).θ (seller0 M) u * M.f u) volume v₁ v₂ := by
      rw [intervalIntegrable_congr_Ioo hv1v2.le hθ_mid]
      exact intervalIntegrable_const
    have h_mid_0 : ∫ u in v₁..v₂, (askingVisit M ρ e).θ (seller0 M) u * M.f u = 0 := by
      rw [intervalIntegral_congr_Ioo hv1v2.le hθ_mid]; simp
    have h_bot_val : ∫ u in v..v₁, (askingVisit M ρ e).θ (seller0 M) u * M.f u = M.F v₁ - M.F v := by
      rw [intervalIntegral_congr_Ioo h1 (fun u hu => hθ_bot u ⟨lt_of_le_of_lt hvρ hu.1, hu.2⟩)]
      exact (M.F_sub_eq_integral (le_trans hρa hvρ) h1 (le_trans hv1v2.le hv21.le)).symm
    rw [← intervalIntegral.integral_add_adjacent_intervals h_bot_int (h_mid_int.trans (hint_top v₂ le_rfl hv21.le).1),
      ← intervalIntegral.integral_add_adjacent_intervals h_mid_int (hint_top v₂ le_rfl hv21.le).1,
      h_bot_val, h_mid_0, hI_v2]
    ring
  · push Not at h1
    have h_mid_int : IntervalIntegrable (fun u => (askingVisit M ρ e).θ (seller0 M) u * M.f u) volume v v₂ := by
      rw [intervalIntegrable_congr_Ioo h2 (fun u hu => hθ_mid u ⟨lt_trans h1 hu.1, hu.2⟩)]
      exact intervalIntegrable_const
    have h_mid_0 : ∫ u in v..v₂, (askingVisit M ρ e).θ (seller0 M) u * M.f u = 0 := by
      rw [intervalIntegral_congr_Ioo h2 (fun u hu => hθ_mid u ⟨lt_trans h1 hu.1, hu.2⟩)]; simp
    rw [← intervalIntegral.integral_add_adjacent_intervals h_mid_int (hint_top v₂ le_rfl hv21.le).1,
      h_mid_0, hI_v2, zero_add]
  · push Not at h2
    rw [(hint_top v h2.le hv1).2]
    rfl

lemma effDist_askingVisit_rival (M : Market) {ρ : ℝ} (hρa : M.a ≤ ρ) (hρ1 : ρ < 1)
    {e : ℝ} (he0 : 0 < e) (heq : e < qRho M ρ) {j : Fin M.m} (hj : j ≠ seller0 M)
    {v : ℝ} (hvρ : ρ ≤ v) (hv1 : v ≤ 1) :
    effDist M (askingVisit M ρ e) j v =
      if v ≤ askingV1 M ρ e then
        1 - askingQ0 M ρ e
      else if v ≤ askingV2 M ρ e then
        askingFriv M ρ e v
      else M.A v := by
  have hc := asking_coords M hρa hρ1 he0 heq
  rcases hc with ⟨_, _, _, _, _, hρv1, hv1v2, hv21, _, _, hAv2, hFriv1, _, _, _, _⟩
  set v₁ := askingV1 M ρ e
  set v₂ := askingV2 M ρ e
  set q₁ := askingQ1 M ρ e
  unfold effDist
  have hf_int : ∀ x y, M.a ≤ x → x ≤ y → y ≤ 1 → IntervalIntegrable M.f volume x y :=
    fun x y hx hxy hy => (M.hf_cont.mono (by rw [uIcc_of_le hxy]; exact Icc_subset_Icc hx hy)).intervalIntegrable
  have hθ_top : ∀ u ∈ Ioo v₂ 1, (askingVisit M ρ e).θ j u * M.f u = (1 / (M.m : ℝ)) * M.f u := by
    intro u hu
    unfold askingVisit; dsimp
    have h1 : ¬(ρ ≤ u ∧ u ≤ askingV1 M ρ e) := fun h => by linarith [h.2, hu.1]
    have h2 : ¬(askingV1 M ρ e < u ∧ u < askingV2 M ρ e) := fun h => by linarith [h.2, hu.1]
    simp [h1, h2]
  have hθ_mid : ∀ u ∈ Ioo v₁ v₂, (askingVisit M ρ e).θ j u * M.f u = (1 / ((M.m : ℝ) - 1)) * M.f u := by
    intro u hu
    unfold askingVisit; dsimp
    have h1 : ¬(ρ ≤ u ∧ u ≤ askingV1 M ρ e) := fun h => by linarith [h.2, hu.1]
    have h2 : askingV1 M ρ e < u ∧ u < askingV2 M ρ e := hu
    simp [h1, h2, hj]
  have hθ_bot : ∀ u ∈ Ioo ρ v₁, (askingVisit M ρ e).θ j u * M.f u = 0 := by
    intro u hu
    unfold askingVisit; dsimp
    have h1 : ρ ≤ u ∧ u ≤ askingV1 M ρ e := ⟨hu.1.le, hu.2.le⟩
    simp [h1, hj]
  have hint_top : ∀ x, v₂ ≤ x → x ≤ 1 →
      IntervalIntegrable (fun u => (askingVisit M ρ e).θ j u * M.f u) volume x 1 ∧
      ∫ u in x..1, (askingVisit M ρ e).θ j u * M.f u = (1 - M.F x) / (M.m : ℝ) := by
    intro x hx2 hx1
    have hcongr : ∀ u ∈ Ioo x 1, (askingVisit M ρ e).θ j u * M.f u = (1 / (M.m : ℝ)) * M.f u :=
      fun u hu => hθ_top u ⟨lt_of_le_of_lt hx2 hu.1, hu.2⟩
    refine ⟨(intervalIntegrable_congr_Ioo hx1 hcongr).mpr ((hf_int x 1 (le_trans hρa (by linarith)) hx1 le_rfl).const_mul _), ?_⟩
    rw [intervalIntegral_congr_Ioo hx1 hcongr, intervalIntegral.integral_const_mul,
      ← M.F_sub_eq_integral (le_trans hρa (by linarith)) hx1 le_rfl, M.hF_1]
    ring
  have hI_v2 : ∫ u in v₂..1, (askingVisit M ρ e).θ j u * M.f u = q₁ := by
    rw [(hint_top v₂ le_rfl hv21.le).2]
    have : 1 - (1 - M.F v₂) / (M.m : ℝ) = 1 - q₁ := hAv2
    linarith
  have hint_mid : ∀ x, v₁ ≤ x → x ≤ v₂ →
      IntervalIntegrable (fun u => (askingVisit M ρ e).θ j u * M.f u) volume x v₂ ∧
      ∫ u in x..v₂, (askingVisit M ρ e).θ j u * M.f u = (M.F v₂ - M.F x) / ((M.m : ℝ) - 1) := by
    intro x hx1 hx2
    have hcongr : ∀ u ∈ Ioo x v₂, (askingVisit M ρ e).θ j u * M.f u = (1 / ((M.m : ℝ) - 1)) * M.f u :=
      fun u hu => hθ_mid u ⟨lt_of_le_of_lt hx1 hu.1, hu.2⟩
    refine ⟨(intervalIntegrable_congr_Ioo hx2 hcongr).mpr
      ((hf_int x v₂ (le_trans hρa (by linarith)) hx2 hv21.le).const_mul _), ?_⟩
    rw [intervalIntegral_congr_Ioo hx2 hcongr, intervalIntegral.integral_const_mul,
      ← M.F_sub_eq_integral (le_trans hρa (by linarith)) hx2 hv21.le]
    ring
  split_ifs with h1 h2
  · have h_bot_int : IntervalIntegrable (fun u => (askingVisit M ρ e).θ j u * M.f u) volume v v₁ := by
      rw [intervalIntegrable_congr_Ioo h1 (fun u hu => hθ_bot u ⟨lt_of_le_of_lt hvρ hu.1, hu.2⟩)]
      exact intervalIntegrable_const
    have h_bot_0 : ∫ u in v..v₁, (askingVisit M ρ e).θ j u * M.f u = 0 := by
      rw [intervalIntegral_congr_Ioo h1 (fun u hu => hθ_bot u ⟨lt_of_le_of_lt hvρ hu.1, hu.2⟩)]; simp
    rw [← intervalIntegral.integral_add_adjacent_intervals h_bot_int
        ((hint_mid v₁ le_rfl hv1v2.le).1.trans (hint_top v₂ le_rfl hv21.le).1),
      ← intervalIntegral.integral_add_adjacent_intervals (hint_mid v₁ le_rfl hv1v2.le).1 (hint_top v₂ le_rfl hv21.le).1,
      h_bot_0, (hint_mid v₁ le_rfl hv1v2.le).2, hI_v2, zero_add]
    have : 1 - ((M.F v₂ - M.F v₁) / ((M.m : ℝ) - 1) + q₁) = askingFriv M ρ e v₁ := by
      unfold askingFriv; ring
    rw [this, hFriv1]
  · push Not at h1
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint_mid v h1.le h2).1 (hint_top v₂ le_rfl hv21.le).1,
      (hint_mid v h1.le h2).2, hI_v2]
    unfold askingFriv; ring
  · push Not at h2
    rw [(hint_top v h2.le hv1).2]
    rfl

lemma surplus_askingVisit_seller0 (M : Market) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hρa : M.a ≤ ρ) {e : ℝ} (he0 : 0 < e) (heq : e < qRho M ρ)
    {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hρβ : ρ < askingBeta M ρ e) (hβ1 : askingBeta M ρ e ≤ 1) :
    surplus M (askingMech ρ (askingBeta M ρ e) hρ0.le hρβ hβ1)
      (effDist M (askingVisit M ρ e) (seller0 M)) v =
      if v ≤ ρ then 0
      else if v ≤ askingBeta M ρ e then (v - ρ) * askingBarX M ρ e
      else if v ≤ askingV2 M ρ e then
        (askingBeta M ρ e - ρ) * askingBarX M ρ e +
          (v - askingBeta M ρ e) * (1 - askingQ1 M ρ e) ^ (M.n - 1)
      else
        (askingBeta M ρ e - ρ) * askingBarX M ρ e +
          (askingV2 M ρ e - askingBeta M ρ e) * (1 - askingQ1 M ρ e) ^ (M.n - 1) +
          ∫ u in askingV2 M ρ e..v, M.A u ^ (M.n - 1) := by
  have hc := asking_coords M hρa hρ1 he0 heq
  rcases hc with ⟨_, _, _, _, _, hρv1, hv1v2, hv21, hFv1, _, _, _, _, hbarx, hv1β, hβv2⟩
  set β := askingBeta M ρ e
  set v₁ := askingV1 M ρ e
  set v₂ := askingV2 M ρ e
  set q₁ := askingQ1 M ρ e
  set t₀ := askingT0 M ρ e
  set barx := askingBarX M ρ e
  set mech := askingMech ρ β hρ0.le hρβ hβ1
  set F0 := effDist M (askingVisit M ρ e) (seller0 M)
  have hF0_ρ : F0 ρ = 1 - t₀ := by
    dsimp [F0]
    rw [effDist_askingVisit_seller0 M hρa hρ1 he0 heq le_rfl hρ1.le]
    have hle : ρ ≤ askingV1 M ρ e := hρv1.le
    simp only [hle, ↓reduceIte]
    change 1 - askingQ1 M ρ e - (M.F v₁ - M.F ρ) = 1 - t₀
    rw [hFv1]; dsimp [t₀]; unfold askingT0; ring
  have hF0_β : F0 β = 1 - q₁ := by
    dsimp [F0]
    rw [effDist_askingVisit_seller0 M hρa hρ1 he0 heq hρβ.le hβ1]
    have h1 : ¬askingBeta M ρ e ≤ askingV1 M ρ e := not_le.mpr hv1β
    have h2 : askingBeta M ρ e ≤ askingV2 M ρ e := hβv2.le
    simp only [β, h1, h2, ↓reduceIte]; rfl
  have ha_0 : ∀ u ∈ Ioo (0 : ℝ) ρ, alloc M mech F0 u = 0 := by
    intro u hu; unfold alloc mech askingMech; dsimp; simp [hu.2]
  have ha_1 : ∀ u ∈ Ioo ρ β, alloc M mech F0 u = barx := by
    intro u hu; unfold alloc mech askingMech; dsimp
    have hnot : ¬u < ρ := not_lt.mpr hu.1.le
    simp only [hnot, hu.1, hu.2, and_self, decide_true, List.find?_cons_of_pos, ↓reduceIte]
    change poolAvg M.n (F0 ρ) (F0 β) = barx
    rw [hF0_ρ, hF0_β]; exact hbarx.symm
  have ha_2 : ∀ u ∈ Ioo β v₂, alloc M mech F0 u = (1 - q₁) ^ (M.n - 1) := by
    intro u hu; unfold alloc mech askingMech; dsimp
    have hlt1 : ¬u < ρ := not_lt.mpr (le_trans hρβ.le hu.1.le)
    have hnot : ¬(ρ < u ∧ u < β) := fun h => not_lt.mpr hu.1.le h.2
    simp only [hlt1, hnot, decide_false, List.find?_cons_of_neg, List.find?_nil, Bool.false_eq_true,
      not_false_eq_true, ↓reduceIte]
    dsimp [F0]
    rw [effDist_askingVisit_seller0 M hρa hρ1 he0 heq (le_trans hρβ.le hu.1.le) (le_trans hu.2.le hv21.le)]
    have h1 : ¬u ≤ askingV1 M ρ e := not_le.mpr (lt_trans hv1β hu.1)
    have h2 : u ≤ askingV2 M ρ e := hu.2.le
    simp only [h1, h2, ↓reduceIte]; rfl
  have ha_3 : ∀ u ∈ Ioo v₂ 1, alloc M mech F0 u = M.A u ^ (M.n - 1) := by
    intro u hu; unfold alloc mech askingMech; dsimp
    have hlt1 : ¬u < ρ := not_lt.mpr (le_trans hρβ.le (le_trans hβv2.le hu.1.le))
    have hnot : ¬(ρ < u ∧ u < β) := fun h => not_lt.mpr (le_trans hβv2.le hu.1.le) h.2
    simp only [hlt1, hnot, decide_false, List.find?_cons_of_neg, List.find?_nil, Bool.false_eq_true,
      not_false_eq_true, ↓reduceIte]
    dsimp [F0]
    rw [effDist_askingVisit_seller0 M hρa hρ1 he0 heq (le_trans hρβ.le (le_trans hβv2.le hu.1.le)) hu.2.le]
    have h1 : ¬u ≤ askingV1 M ρ e := not_le.mpr (lt_trans hv1v2 hu.1)
    have h2 : ¬u ≤ askingV2 M ρ e := not_le.mpr hu.1
    simp only [h1, h2, ↓reduceIte]
  have hi0 : IntervalIntegrable (alloc M mech F0) volume 0 ρ :=
    (intervalIntegrable_congr_Ioo hρ0.le ha_0).mpr intervalIntegrable_const
  have hv0_eq : ∫ u in (0 : ℝ)..ρ, alloc M mech F0 u = 0 := by
    rw [intervalIntegral_congr_Ioo hρ0.le ha_0]; simp
  have hi1 : ∀ x, ρ ≤ x → x ≤ β →
      IntervalIntegrable (alloc M mech F0) volume ρ x ∧
      ∫ u in ρ..x, alloc M mech F0 u = (x - ρ) * barx := by
    intro x h1 h2
    have hc' : ∀ u ∈ Ioo ρ x, alloc M mech F0 u = barx := fun u hu => ha_1 u ⟨hu.1, lt_of_lt_of_le hu.2 h2⟩
    refine ⟨(intervalIntegrable_congr_Ioo h1 hc').mpr intervalIntegrable_const, ?_⟩
    rw [intervalIntegral_congr_Ioo h1 hc', intervalIntegral.integral_const, smul_eq_mul]
  have hi2 : ∀ x, β ≤ x → x ≤ v₂ →
      IntervalIntegrable (alloc M mech F0) volume β x ∧
      ∫ u in β..x, alloc M mech F0 u = (x - β) * (1 - q₁) ^ (M.n - 1) := by
    intro x h1 h2
    have hc' : ∀ u ∈ Ioo β x, alloc M mech F0 u = (1 - q₁) ^ (M.n - 1) :=
      fun u hu => ha_2 u ⟨hu.1, lt_of_lt_of_le hu.2 h2⟩
    refine ⟨(intervalIntegrable_congr_Ioo h1 hc').mpr intervalIntegrable_const, ?_⟩
    rw [intervalIntegral_congr_Ioo h1 hc', intervalIntegral.integral_const, smul_eq_mul]
  unfold surplus
  split_ifs with hvρ hvβ hvv2
  · rw [intervalIntegral_congr_Ioo hv0 (g := fun _ => (0 : ℝ))
      (fun u hu => ha_0 u ⟨hu.1, lt_of_lt_of_le hu.2 hvρ⟩)]
    simp
  · push Not at hvρ
    rw [← intervalIntegral.integral_add_adjacent_intervals hi0 (hi1 v hvρ.le hvβ).1,
      hv0_eq, (hi1 v hvρ.le hvβ).2, zero_add]
  · push Not at hvρ hvβ
    rw [← intervalIntegral.integral_add_adjacent_intervals (hi0.trans (hi1 β hρβ.le le_rfl).1) (hi2 v hvβ.le hvv2).1,
      ← intervalIntegral.integral_add_adjacent_intervals hi0 (hi1 β hρβ.le le_rfl).1,
      hv0_eq, (hi1 β hρβ.le le_rfl).2, (hi2 v hvβ.le hvv2).2, zero_add]
  · push Not at hvρ hvβ hvv2
    have hc3 : ∀ u ∈ Ioo v₂ v, alloc M mech F0 u = M.A u ^ (M.n - 1) :=
      fun u hu => ha_3 u ⟨hu.1, lt_of_lt_of_le hu.2 hv1⟩
    have hcontA : ContinuousOn (fun u => M.A u ^ (M.n - 1)) (Icc v₂ v) :=
      (M.A_continuousOn.mono (Icc_subset_Icc (le_trans hρa (by linarith)) hv1)).pow _
    have hi3 : IntervalIntegrable (alloc M mech F0) volume v₂ v :=
      (intervalIntegrable_congr_Ioo hvv2.le hc3).mpr
        (hcontA.mono (by rw [uIcc_of_le hvv2.le])).intervalIntegrable
    rw [← intervalIntegral.integral_add_adjacent_intervals
        ((hi0.trans (hi1 β hρβ.le le_rfl).1).trans (hi2 v₂ hβv2.le le_rfl).1) hi3,
      ← intervalIntegral.integral_add_adjacent_intervals (hi0.trans (hi1 β hρβ.le le_rfl).1) (hi2 v₂ hβv2.le le_rfl).1,
      ← intervalIntegral.integral_add_adjacent_intervals hi0 (hi1 β hρβ.le le_rfl).1,
      hv0_eq, (hi1 β hρβ.le le_rfl).2, (hi2 v₂ hβv2.le le_rfl).2, zero_add,
      intervalIntegral_congr_Ioo hvv2.le hc3]

lemma surplus_askingVisit_rival (M : Market) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hρa : M.a ≤ ρ) {e : ℝ} (he0 : 0 < e) (heq : e < qRho M ρ)
    {j : Fin M.m} (hj : j ≠ seller0 M) {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    surplus M (SPA ρ hρ0.le hρ1.le) (effDist M (askingVisit M ρ e) j) v =
      if v ≤ ρ then 0
      else if v ≤ askingV1 M ρ e then (v - ρ) * askingBarX M ρ e
      else if v ≤ askingV2 M ρ e then
        (askingV1 M ρ e - ρ) * askingBarX M ρ e +
          ∫ u in askingV1 M ρ e..v, askingFriv M ρ e u ^ (M.n - 1)
      else
        (askingV1 M ρ e - ρ) * askingBarX M ρ e +
          (∫ u in askingV1 M ρ e..askingV2 M ρ e, askingFriv M ρ e u ^ (M.n - 1)) +
          ∫ u in askingV2 M ρ e..v, M.A u ^ (M.n - 1) := by
  have hc := asking_coords M hρa hρ1 he0 heq
  rcases hc with ⟨_, _, _, _, _, hρv1, hv1v2, hv21, _, _, _, _, _, _, _, _⟩
  set v₁ := askingV1 M ρ e
  set v₂ := askingV2 M ρ e
  set barx := askingBarX M ρ e
  set mech := SPA ρ hρ0.le hρ1.le
  set Fj := effDist M (askingVisit M ρ e) j
  have ha_0 : ∀ u ∈ Ioo (0 : ℝ) ρ, alloc M mech Fj u = 0 := by
    intro u hu; unfold alloc mech SPA; dsimp; simp [hu.2]
  have ha_1 : ∀ u ∈ Ioo ρ v₁, alloc M mech Fj u = barx := by
    intro u hu; unfold alloc mech SPA; dsimp
    simp only [not_lt.mpr hu.1.le, ↓reduceIte]
    dsimp [Fj]
    rw [effDist_askingVisit_rival M hρa hρ1 he0 heq hj hu.1.le (le_trans hu.2.le (le_trans hv1v2.le hv21.le))]
    have h1 : u ≤ askingV1 M ρ e := hu.2.le
    simp only [h1, ↓reduceIte]; rfl
  have ha_2 : ∀ u ∈ Ioo v₁ v₂, alloc M mech Fj u = askingFriv M ρ e u ^ (M.n - 1) := by
    intro u hu; unfold alloc mech SPA; dsimp
    simp only [not_lt.mpr (le_trans hρv1.le hu.1.le), ↓reduceIte]
    dsimp [Fj]
    rw [effDist_askingVisit_rival M hρa hρ1 he0 heq hj (le_trans hρv1.le hu.1.le) (le_trans hu.2.le hv21.le)]
    have h1 : ¬u ≤ askingV1 M ρ e := not_le.mpr hu.1
    have h2 : u ≤ askingV2 M ρ e := hu.2.le
    simp only [h1, h2, ↓reduceIte]
  have ha_3 : ∀ u ∈ Ioo v₂ 1, alloc M mech Fj u = M.A u ^ (M.n - 1) := by
    intro u hu; unfold alloc mech SPA; dsimp
    simp only [not_lt.mpr (le_trans hρv1.le (le_trans hv1v2.le hu.1.le)), ↓reduceIte]
    dsimp [Fj]
    rw [effDist_askingVisit_rival M hρa hρ1 he0 heq hj (le_trans hρv1.le (le_trans hv1v2.le hu.1.le)) hu.2.le]
    have h1 : ¬u ≤ askingV1 M ρ e := not_le.mpr (lt_trans hv1v2 hu.1)
    have h2 : ¬u ≤ askingV2 M ρ e := not_le.mpr hu.1
    simp only [h1, h2, ↓reduceIte]
  have hi0 : IntervalIntegrable (alloc M mech Fj) volume 0 ρ :=
    (intervalIntegrable_congr_Ioo hρ0.le ha_0).mpr intervalIntegrable_const
  have hv0_eq : ∫ u in (0 : ℝ)..ρ, alloc M mech Fj u = 0 := by
    rw [intervalIntegral_congr_Ioo hρ0.le ha_0]; simp
  have hi1 : ∀ x, ρ ≤ x → x ≤ v₁ →
      IntervalIntegrable (alloc M mech Fj) volume ρ x ∧
      ∫ u in ρ..x, alloc M mech Fj u = (x - ρ) * barx := by
    intro x h1 h2
    have hc' : ∀ u ∈ Ioo ρ x, alloc M mech Fj u = barx := fun u hu => ha_1 u ⟨hu.1, lt_of_lt_of_le hu.2 h2⟩
    refine ⟨(intervalIntegrable_congr_Ioo h1 hc').mpr intervalIntegrable_const, ?_⟩
    rw [intervalIntegral_congr_Ioo h1 hc', intervalIntegral.integral_const, smul_eq_mul]
  have hcontFriv : ContinuousOn (fun u => askingFriv M ρ e u ^ (M.n - 1)) (Icc v₁ v₂) := by
    have hF_sub : ContinuousOn M.F (Icc v₁ v₂) :=
      M.F_continuousOn.mono (Icc_subset_Icc (le_trans hρa hρv1.le) hv21.le)
    unfold askingFriv; fun_prop
  have hi2 : ∀ x, v₁ ≤ x → x ≤ v₂ →
      IntervalIntegrable (alloc M mech Fj) volume v₁ x ∧
      ∫ u in v₁..x, alloc M mech Fj u = ∫ u in v₁..x, askingFriv M ρ e u ^ (M.n - 1) := by
    intro x h1 h2
    have hc' : ∀ u ∈ Ioo v₁ x, alloc M mech Fj u = askingFriv M ρ e u ^ (M.n - 1) :=
      fun u hu => ha_2 u ⟨hu.1, lt_of_lt_of_le hu.2 h2⟩
    refine ⟨(intervalIntegrable_congr_Ioo h1 hc').mpr
      ((hcontFriv.mono (by rw [uIcc_of_le h1]; exact Icc_subset_Icc le_rfl h2)).intervalIntegrable),
      intervalIntegral_congr_Ioo h1 hc'⟩
  unfold surplus
  split_ifs with hvρ hvv1 hvv2
  · rw [intervalIntegral_congr_Ioo hv0 (g := fun _ => (0 : ℝ))
      (fun u hu => ha_0 u ⟨hu.1, lt_of_lt_of_le hu.2 hvρ⟩)]
    simp
  · push Not at hvρ
    rw [← intervalIntegral.integral_add_adjacent_intervals hi0 (hi1 v hvρ.le hvv1).1,
      hv0_eq, (hi1 v hvρ.le hvv1).2, zero_add]
  · push Not at hvρ hvv1
    rw [← intervalIntegral.integral_add_adjacent_intervals (hi0.trans (hi1 v₁ hρv1.le le_rfl).1) (hi2 v hvv1.le hvv2).1,
      ← intervalIntegral.integral_add_adjacent_intervals hi0 (hi1 v₁ hρv1.le le_rfl).1,
      hv0_eq, (hi1 v₁ hρv1.le le_rfl).2, (hi2 v hvv1.le hvv2).2, zero_add]
  · push Not at hvρ hvv1 hvv2
    have hc3 : ∀ u ∈ Ioo v₂ v, alloc M mech Fj u = M.A u ^ (M.n - 1) :=
      fun u hu => ha_3 u ⟨hu.1, lt_of_lt_of_le hu.2 hv1⟩
    have hcontA : ContinuousOn (fun u => M.A u ^ (M.n - 1)) (Icc v₂ v) :=
      (M.A_continuousOn.mono (Icc_subset_Icc (le_trans hρa (by linarith)) hv1)).pow _
    have hi3 : IntervalIntegrable (alloc M mech Fj) volume v₂ v :=
      (intervalIntegrable_congr_Ioo hvv2.le hc3).mpr
        (hcontA.mono (by rw [uIcc_of_le hvv2.le])).intervalIntegrable
    rw [← intervalIntegral.integral_add_adjacent_intervals
        ((hi0.trans (hi1 v₁ hρv1.le le_rfl).1).trans (hi2 v₂ hv1v2.le le_rfl).1) hi3,
      ← intervalIntegral.integral_add_adjacent_intervals (hi0.trans (hi1 v₁ hρv1.le le_rfl).1) (hi2 v₂ hv1v2.le le_rfl).1,
      ← intervalIntegral.integral_add_adjacent_intervals hi0 (hi1 v₁ hρv1.le le_rfl).1,
      hv0_eq, (hi1 v₁ hρv1.le le_rfl).2, (hi2 v₂ hv1v2.le le_rfl).2, zero_add,
      intervalIntegral_congr_Ioo hvv2.le hc3]

lemma askingBeta_balance (M : Market) {ρ : ℝ} (hρa : M.a ≤ ρ) (hρ1 : ρ < 1)
    {e : ℝ} (he0 : 0 < e) (heq : e < qRho M ρ) :
    (askingBeta M ρ e - ρ) * askingBarX M ρ e +
      (askingV2 M ρ e - askingBeta M ρ e) * (1 - askingQ1 M ρ e) ^ (M.n - 1) =
    (askingV1 M ρ e - ρ) * askingBarX M ρ e +
      ∫ u in askingV1 M ρ e..askingV2 M ρ e, askingFriv M ρ e u ^ (M.n - 1) := by
  have hc := asking_coords M hρa hρ1 he0 heq
  rcases hc with ⟨_, hq1_lt_q0, hq0_lt_qr, _, _, hρv1, hv1v2, hv21, _, _, _, _, _, _, _, _⟩
  set β := askingBeta M ρ e
  set v₁ := askingV1 M ρ e
  set v₂ := askingV2 M ρ e
  set q₁ := askingQ1 M ρ e
  set barx := askingBarX M ρ e
  have hqhalf := qRho_le_half M hρa hρ1.le
  have hden_pos : 0 < (1 - q₁) ^ (M.n - 1) - barx := by
    dsimp [barx]; unfold askingBarX
    have := pow_lt_pow_left₀ (by linarith : 1 - askingQ0 M ρ e < 1 - q₁)
      (by linarith) M.n_sub_one_ne_zero
    linarith
  have hcontFriv : ContinuousOn (fun u => askingFriv M ρ e u ^ (M.n - 1)) (Icc v₁ v₂) := by
    have hF_sub : ContinuousOn M.F (Icc v₁ v₂) :=
      M.F_continuousOn.mono (Icc_subset_Icc (le_trans hρa hρv1.le) hv21.le)
    unfold askingFriv; fun_prop
  have hβ_def : (v₂ - β) * ((1 - q₁) ^ (M.n - 1) - barx) =
      ∫ u in v₁..v₂, (askingFriv M ρ e u ^ (M.n - 1) - barx) := by
    dsimp [β]; unfold askingBeta
    have hsub : v₂ - (v₂ - (∫ u in v₁..v₂, (askingFriv M ρ e u ^ (M.n - 1) - barx)) /
        ((1 - q₁) ^ (M.n - 1) - barx)) =
        (∫ u in v₁..v₂, (askingFriv M ρ e u ^ (M.n - 1) - barx)) /
          ((1 - q₁) ^ (M.n - 1) - barx) := by ring
    rw [hsub, div_mul_cancel₀ _ hden_pos.ne']
  rw [intervalIntegral.integral_sub (hcontFriv.mono (by rw [uIcc_of_le hv1v2.le])).intervalIntegrable
    intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul] at hβ_def
  linarith

/-- **Theorem 3 (Part 1 — Sequential Rationality)**:
For any binding reserve `ρ ∈ (0, 1)` (`M.a ≤ ρ`) and any served pooled mass `e ∈ (0, q_ρ)`,
the asking-price deviation `(ρ, {(ρ, β(e))})` induces the explicit SR continuation
`askingVisit M ρ e` (`θ₁ = 1` on `[ρ, v₁]`, `θ₁ = 0` on `(v₁, v₂)`, `θ₁ = 1/m` above `v₂`). -/
theorem theorem3_asking_price_sr (M : Market) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hρa : M.a ≤ ρ) {e : ℝ} (he0 : 0 < e) (heq : e < qRho M ρ)
    (hρβ : ρ < askingBeta M ρ e) (hβ1 : askingBeta M ρ e ≤ 1) :
    IsSR M (askingProfile M ρ (askingBeta M ρ e) hρ0.le hρβ hβ1) (askingVisit M ρ e) := by
  have hc := asking_coords M hρa hρ1 he0 heq
  rcases hc with ⟨_, _, hq0_lt_qr, _, _, hρv1, hv1v2, hv21, _, _, _, hFriv1, _, _, hv1β, hβv2⟩
  set β := askingBeta M ρ e
  set v₁ := askingV1 M ρ e
  set v₂ := askingV2 M ρ e
  set q₁ := askingQ1 M ρ e
  set q₀ := askingQ0 M ρ e
  set barx := askingBarX M ρ e
  set prof := askingProfile M ρ β hρ0.le hρβ hβ1
  set θ := askingVisit M ρ e
  have hbal := askingBeta_balance M hρa hρ1 he0 heq
  have hqhalf := qRho_le_half M hρa hρ1.le
  have hFriv_range : ∀ u ∈ Icc v₁ v₂, barx ≤ askingFriv M ρ e u ^ (M.n - 1) ∧
      askingFriv M ρ e u ^ (M.n - 1) ≤ (1 - q₁) ^ (M.n - 1) := by
    intro u hu
    have hu_mem : u ∈ Icc M.a 1 := ⟨le_trans hρa (le_trans hρv1.le hu.1), le_trans hu.2 hv21.le⟩
    have hv1_mem : v₁ ∈ Icc M.a 1 := ⟨le_trans hρa hρv1.le, le_trans hv1v2.le hv21.le⟩
    have hv2_mem : v₂ ∈ Icc M.a 1 := ⟨le_trans hρa (le_trans hρv1.le hv1v2.le), hv21.le⟩
    have hF1 := M.F_strictMonoOn.monotoneOn hv1_mem hu_mem hu.1
    have hF2 := M.F_strictMonoOn.monotoneOn hu_mem hv2_mem hu.2
    have hlo : 1 - q₀ ≤ askingFriv M ρ e u := by
      rw [← hFriv1]; unfold askingFriv
      have := div_le_div_of_nonneg_right (by linarith : M.F v₂ - M.F u ≤ M.F v₂ - M.F v₁) M.m_sub_one_pos_real.le
      linarith
    have hhi : askingFriv M ρ e u ≤ 1 - q₁ := by
      unfold askingFriv
      have : 0 ≤ (M.F v₂ - M.F u) / ((M.m : ℝ) - 1) := div_nonneg (by linarith) M.m_sub_one_pos_real.le
      linarith
    dsimp [barx]; unfold askingBarX
    exact ⟨pow_le_pow_left₀ (by linarith) hlo _, pow_le_pow_left₀ (by linarith) hhi _⟩
  have hcontFriv : ContinuousOn (fun u => askingFriv M ρ e u ^ (M.n - 1)) (Icc v₁ v₂) := by
    have hF_sub : ContinuousOn M.F (Icc v₁ v₂) :=
      M.F_continuousOn.mono (Icc_subset_Icc (le_trans hρa hρv1.le) hv21.le)
    unfold askingFriv; fun_prop
  have hcomp : ∀ v ∈ Icc M.a 1, ∀ j : Fin M.m, j ≠ seller0 M →
      (v ∉ Ioo v₁ v₂ → surplus M (prof (seller0 M)) (effDist M θ (seller0 M)) v =
          surplus M (prof j) (effDist M θ j) v) ∧
      (surplus M (prof (seller0 M)) (effDist M θ (seller0 M)) v ≤
          surplus M (prof j) (effDist M θ j) v) := by
    intro v hv j hj
    have hv0 : 0 ≤ v := le_trans M.ha0 hv.1
    have hp0 : prof (seller0 M) = askingMech ρ β hρ0.le hρβ hβ1 := by simp [prof, askingProfile]
    have hpj : prof j = SPA ρ hρ0.le (le_trans hρβ.le hβ1) := by simp [prof, askingProfile, hj]
    rw [hp0, hpj]
    have hs0 := surplus_askingVisit_seller0 M hρ0 hρ1 hρa he0 heq hv0 hv.2 hρβ hβ1
    have hsj := surplus_askingVisit_rival M hρ0 hρ1 hρa he0 heq hj hv0 hv.2
    rw [hs0, hsj]
    by_cases hvρ : v ≤ ρ
    · simp [hvρ]
    · by_cases hvv1 : v ≤ v₁
      · have hvβ : v ≤ askingBeta M ρ e := le_trans hvv1 hv1β.le
        have hv1' : v ≤ askingV1 M ρ e := hvv1
        simp [hvρ, hv1', hvβ]
      · push Not at hvv1
        by_cases hvv2 : v < v₂
        · refine ⟨fun hnot => absurd ⟨hvv1, hvv2⟩ hnot, ?_⟩
          have hv1' : ¬v ≤ askingV1 M ρ e := not_le.mpr hvv1
          have hv2' : v ≤ askingV2 M ρ e := hvv2.le
          simp only [hvρ, hv1', hv2', ↓reduceIte]
          by_cases hvβ : v ≤ β
          · have hvβ' : v ≤ askingBeta M ρ e := hvβ
            simp only [hvβ', ↓reduceIte]
            have hint : IntervalIntegrable (fun u => askingFriv M ρ e u ^ (M.n - 1)) volume v₁ v :=
              (hcontFriv.mono (by rw [uIcc_of_le hvv1.le]; exact Icc_subset_Icc le_rfl hvv2.le)).intervalIntegrable
            have hle : (v - v₁) * barx ≤ ∫ u in v₁..v, askingFriv M ρ e u ^ (M.n - 1) := by
              have hc' : ∫ _ in v₁..v, barx = (v - v₁) * barx := by
                rw [intervalIntegral.integral_const, smul_eq_mul]
              rw [← hc']
              exact intervalIntegral.integral_mono_on hvv1.le intervalIntegrable_const hint
                (fun u hu => (hFriv_range u ⟨hu.1, le_trans hu.2 hvv2.le⟩).1)
            linarith
          · push Not at hvβ
            have hvβ' : ¬v ≤ askingBeta M ρ e := not_le.mpr hvβ
            simp only [hvβ', ↓reduceIte]
            have hint1 : IntervalIntegrable (fun u => askingFriv M ρ e u ^ (M.n - 1)) volume v₁ v :=
              (hcontFriv.mono (by rw [uIcc_of_le hvv1.le]; exact Icc_subset_Icc le_rfl hvv2.le)).intervalIntegrable
            have hint2 : IntervalIntegrable (fun u => askingFriv M ρ e u ^ (M.n - 1)) volume v v₂ :=
              (hcontFriv.mono (by rw [uIcc_of_le hvv2.le]; exact Icc_subset_Icc hvv1.le le_rfl)).intervalIntegrable
            have hsplit : (∫ u in v₁..v, askingFriv M ρ e u ^ (M.n - 1)) +
                (∫ u in v..v₂, askingFriv M ρ e u ^ (M.n - 1)) =
                ∫ u in v₁..v₂, askingFriv M ρ e u ^ (M.n - 1) :=
              intervalIntegral.integral_add_adjacent_intervals hint1 hint2
            have hle : ∫ u in v..v₂, askingFriv M ρ e u ^ (M.n - 1) ≤ (v₂ - v) * (1 - q₁) ^ (M.n - 1) := by
              have hc' : ∫ _ in v..v₂, (1 - q₁) ^ (M.n - 1) = (v₂ - v) * (1 - q₁) ^ (M.n - 1) := by
                rw [intervalIntegral.integral_const, smul_eq_mul]
              rw [← hc']
              exact intervalIntegral.integral_mono_on hvv2.le hint2 intervalIntegrable_const
                (fun u hu => (hFriv_range u ⟨le_trans hvv1.le hu.1, hu.2⟩).2)
            linarith [hbal]
        · push Not at hvv2
          have hvβ' : ¬v ≤ askingBeta M ρ e := not_le.mpr (lt_of_lt_of_le hβv2 hvv2)
          have hv1' : ¬v ≤ askingV1 M ρ e := not_le.mpr hvv1
          by_cases hveq : v = v₂
          · subst hveq
            have hv2' : askingV2 M ρ e ≤ askingV2 M ρ e := le_rfl
            simp only [hvρ, hvβ', hv1', v₂, hv2', ↓reduceIte]
            exact ⟨fun _ => hbal, hbal.le⟩
          · have hgt : v₂ < v := lt_of_le_of_ne hvv2 (Ne.symm hveq)
            have hv2' : ¬v ≤ askingV2 M ρ e := not_le.mpr hgt
            simp only [hvρ, hvβ', hv1', hv2', ↓reduceIte]
            have heq : (askingBeta M ρ e - ρ) * askingBarX M ρ e +
                (askingV2 M ρ e - askingBeta M ρ e) * (1 - askingQ1 M ρ e) ^ (M.n - 1) +
                ∫ u in askingV2 M ρ e..v, M.A u ^ (M.n - 1) =
                (askingV1 M ρ e - ρ) * askingBarX M ρ e +
                (∫ u in askingV1 M ρ e..askingV2 M ρ e, askingFriv M ρ e u ^ (M.n - 1)) +
                ∫ u in askingV2 M ρ e..v, M.A u ^ (M.n - 1) := by linarith [hbal]
            exact ⟨fun _ => heq, heq.le⟩
  filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv j k hjpos
  have hriv_eq : ∀ j₁ j₂ : Fin M.m, j₁ ≠ seller0 M → j₂ ≠ seller0 M →
      surplus M (prof j₁) (effDist M θ j₁) v = surplus M (prof j₂) (effDist M θ j₂) v := by
    intro j₁ j₂ hj₁ hj₂
    have hv0 : 0 ≤ v := le_trans M.ha0 hv.1
    have hp1 : prof j₁ = SPA ρ hρ0.le (le_trans hρβ.le hβ1) := by simp [prof, askingProfile, hj₁]
    have hp2 : prof j₂ = SPA ρ hρ0.le (le_trans hρβ.le hβ1) := by simp [prof, askingProfile, hj₂]
    rw [hp1, hp2, surplus_askingVisit_rival M hρ0 hρ1 hρa he0 heq hj₁ hv0 hv.2,
      surplus_askingVisit_rival M hρ0 hρ1 hρa he0 heq hj₂ hv0 hv.2]
  by_cases hj0 : j = seller0 M
  · subst hj0
    by_cases hk0 : k = seller0 M
    · subst hk0; exact le_rfl
    · have hnot : v ∉ Ioo v₁ v₂ := by
        intro hmem
        have hθ0 : θ.θ (seller0 M) v = 0 := by
          dsimp [θ]; unfold askingVisit; dsimp
          have h1 : ¬(ρ ≤ v ∧ v ≤ askingV1 M ρ e) := fun h => by linarith [h.2, hmem.1]
          have h2 : askingV1 M ρ e < v ∧ v < askingV2 M ρ e := hmem
          simp [h1, h2]
        linarith
      exact ((hcomp v hv k hk0).1 hnot).symm.le
  · by_cases hk0 : k = seller0 M
    · subst hk0; exact (hcomp v hv j hj0).2
    · exact (hriv_eq k j hk0 hj0).le

/-! #### Asymptotics of `askingY`, `askingBeta`, and Asking-Price Revenue Gain -/

lemma askingY_asymptotic (M : Market) {ρ : ℝ} (hρa : M.a ≤ ρ) (hρ1 : ρ < 1) :
    ∃ C ≥ 0, ∀ e ∈ Ioo (0 : ℝ) (qRho M ρ),
      |askingY M ρ e - (((M.m : ℝ) + 1) / (2 * (M.m : ℝ))) * e| ≤ C * e ^ 2 := by
  set A := 1 - qRho M ρ
  have hqhalf := qRho_le_half M hρa hρ1.le
  have hApos : 0 < A := by linarith
  have hm : (0 : ℝ) < M.m := M.m_pos_real
  have hm1 : (0 : ℝ) < (M.m : ℝ) - 1 := M.m_sub_one_pos_real
  have hn1 : (0 : ℝ) < (M.n : ℝ) - 1 := M.n_sub_one_pos_real
  obtain ⟨C₁, hC₁, hpow⟩ := pow_first_order_bound (M.n - 1) A
  obtain ⟨C₂, hC₂, hpool⟩ := poolAvg_first_order_bound M.n M.hn A
  have hcoef_pos : 0 < ((M.n : ℝ) - 1) * A ^ (M.n - 2) * ((M.m : ℝ) / ((M.m : ℝ) - 1)) := by
    positivity
  let C := (C₁ / ((M.m : ℝ) - 1) ^ 2 + 4 * C₂) /
    (((M.n : ℝ) - 1) * A ^ (M.n - 2) * ((M.m : ℝ) / ((M.m : ℝ) - 1)))
  refine ⟨C, by positivity, fun e he => ?_⟩
  have hys := askingY_spec M hρa hρ1 he.1 he.2
  set y := askingY M ρ e
  have hy0 : 0 < y := lt_trans (div_pos he.1 hm) hys.1.1
  have hye : y < e := hys.1.2
  have he1 : e ≤ 1 := by linarith [he.2, hqhalf]
  let h₀ := -(y - e) / ((M.m : ℝ) - 1)
  have hh₀_le : |h₀| ≤ e / ((M.m : ℝ) - 1) := by
    dsimp [h₀]
    rw [abs_div, abs_neg, abs_of_pos hm1, abs_of_neg (by linarith)]
    exact div_le_div_of_nonneg_right (by linarith) hm1.le
  have hh₀_1 : |h₀| ≤ 1 := by
    have hm2 : (2 : ℝ) ≤ M.m := by exact_mod_cast M.hm
    calc |h₀| ≤ e / ((M.m : ℝ) - 1) := hh₀_le
      _ ≤ 1 / 1 := div_le_div₀ zero_le_one he1 (by norm_num) (by linarith)
      _ = 1 := div_one 1
  have h1 := hpow h₀ hh₀_1
  have h1' : |(1 - (qRho M ρ + (y - e) / ((M.m : ℝ) - 1))) ^ (M.n - 1) - A ^ (M.n - 1) -
      ((M.n : ℝ) - 1) * A ^ (M.n - 2) * h₀| ≤ C₁ * (e / ((M.m : ℝ) - 1)) ^ 2 := by
    have hEq : A + h₀ = 1 - (qRho M ρ + (y - e) / ((M.m : ℝ) - 1)) := by dsimp [A, h₀]; ring
    have hcast : ((M.n - 1 : ℕ) : ℝ) = (M.n : ℝ) - 1 := by
      rw [Nat.cast_sub (by have := M.hn; omega), Nat.cast_one]
    have hsub : M.n - 1 - 1 = M.n - 2 := by omega
    rw [hEq, hcast, hsub] at h1
    calc _ ≤ C₁ * h₀ ^ 2 := h1
      _ = C₁ * |h₀| ^ 2 := by rw [sq_abs]
      _ ≤ C₁ * (e / ((M.m : ℝ) - 1)) ^ 2 := by gcongr
  have hh1_le : |y - e| ≤ e := by rw [abs_of_neg (by linarith)]; linarith
  have hh2_le : |y| ≤ e := by rw [abs_of_pos hy0]; linarith
  have h2 := hpool (y - e) y (le_trans hh1_le he1) (le_trans hh2_le he1)
  have h2' : |poolAvg M.n (1 - (qRho M ρ - y + e)) (1 - (qRho M ρ - y)) - A ^ (M.n - 1) -
      ((M.n : ℝ) - 1) * A ^ (M.n - 2) * ((y - e + y) / 2)| ≤ 4 * C₂ * e ^ 2 := by
    have heq1 : A + (y - e) = 1 - (qRho M ρ - y + e) := by dsimp [A]; ring
    have heq2 : A + y = 1 - (qRho M ρ - y) := by dsimp [A]; ring
    rw [heq1, heq2] at h2
    calc _ ≤ C₂ * (|y - e| + |y|) ^ 2 := h2
      _ ≤ C₂ * (e + e) ^ 2 := by gcongr
      _ = 4 * C₂ * e ^ 2 := by ring
  have hphi : (1 - (qRho M ρ + (y - e) / ((M.m : ℝ) - 1))) ^ (M.n - 1) =
      poolAvg M.n (1 - (qRho M ρ - y + e)) (1 - (qRho M ρ - y)) := by
    have := hys.2; unfold askingPhi at this; linarith
  have hlin : ((M.n : ℝ) - 1) * A ^ (M.n - 2) * ((M.m : ℝ) / ((M.m : ℝ) - 1)) *
      (y - (((M.m : ℝ) + 1) / (2 * (M.m : ℝ))) * e) =
      ((1 - (qRho M ρ + (y - e) / ((M.m : ℝ) - 1))) ^ (M.n - 1) - A ^ (M.n - 1) -
        ((M.n : ℝ) - 1) * A ^ (M.n - 2) * h₀) -
      (poolAvg M.n (1 - (qRho M ρ - y + e)) (1 - (qRho M ρ - y)) - A ^ (M.n - 1) -
        ((M.n : ℝ) - 1) * A ^ (M.n - 2) * ((y - e + y) / 2)) := by
    rw [hphi]; dsimp [h₀]
    field_simp [hm.ne', hm1.ne']
    ring
  have habs : ((M.n : ℝ) - 1) * A ^ (M.n - 2) * ((M.m : ℝ) / ((M.m : ℝ) - 1)) *
      |y - (((M.m : ℝ) + 1) / (2 * (M.m : ℝ))) * e| ≤
      (C₁ / ((M.m : ℝ) - 1) ^ 2 + 4 * C₂) * e ^ 2 := by
    rw [← abs_of_pos hcoef_pos, ← abs_mul, hlin]
    set X₁ := (1 - (qRho M ρ + (y - e) / ((M.m : ℝ) - 1))) ^ (M.n - 1) - A ^ (M.n - 1) -
        ((M.n : ℝ) - 1) * A ^ (M.n - 2) * h₀
    set X₂ := poolAvg M.n (1 - (qRho M ρ - y + e)) (1 - (qRho M ρ - y)) - A ^ (M.n - 1) -
        ((M.n : ℝ) - 1) * A ^ (M.n - 2) * ((y - e + y) / 2)
    have htri : |X₁ - X₂| ≤ |X₁| + |X₂| := by
      have h := abs_sub_le X₁ 0 X₂
      rw [sub_zero, zero_sub, abs_neg] at h; exact h
    calc |X₁ - X₂| ≤ C₁ * (e / ((M.m : ℝ) - 1)) ^ 2 + 4 * C₂ * e ^ 2 := by linarith
      _ = (C₁ / ((M.m : ℝ) - 1) ^ 2 + 4 * C₂) * e ^ 2 := by field_simp [hm1.ne']
  dsimp [C]
  have hdiv := (le_div_iff₀' hcoef_pos).mpr habs
  convert hdiv using 1; ring

lemma askingY_continuousOn (M : Market) {ρ : ℝ} (hρa : M.a ≤ ρ) (hρ1 : ρ < 1) :
    ContinuousOn (askingY M ρ) (Ioo (0 : ℝ) (qRho M ρ)) := by
  intro e₀ he₀
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hys₀ := askingY_spec M hρa hρ1 he₀.1 he₀.2
  set y₀ := askingY M ρ e₀
  let δy := min (ε / 2) (min ((y₀ - e₀ / (M.m : ℝ)) / 2) ((e₀ - y₀) / 2))
  have hδy : 0 < δy := by
    apply lt_min (by linarith)
    apply lt_min <;> linarith [hys₀.1.1, hys₀.1.2]
  have hδy1 : δy ≤ (y₀ - e₀ / (M.m : ℝ)) / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδy2 : δy ≤ (e₀ - y₀) / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  let y_lo := y₀ - δy
  let y_hi := y₀ + δy
  have hlo_gt : e₀ / (M.m : ℝ) < y_lo := by dsimp [y_lo]; linarith [hys₀.1.1]
  have hhi_lt : y_hi < e₀ := by dsimp [y_hi]; linarith [hys₀.1.2]
  have hlo_in : y_lo ∈ Icc (e₀ / (M.m : ℝ)) e₀ := ⟨hlo_gt.le, by linarith [hys₀.1.2]⟩
  have hhi_in : y_hi ∈ Icc (e₀ / (M.m : ℝ)) e₀ := ⟨by linarith [hys₀.1.1], hhi_lt.le⟩
  have hanti₀ := askingPhi_strictAntiOn M hρa hρ1 he₀.1 he₀.2
  have hpos_lo : 0 < askingPhi M ρ e₀ y_lo := by
    rw [← hys₀.2]; exact hanti₀ hlo_in (Ioo_subset_Icc_self hys₀.1) (by linarith)
  have hneg_hi : askingPhi M ρ e₀ y_hi < 0 := by
    rw [← hys₀.2]; exact hanti₀ (Ioo_subset_Icc_self hys₀.1) hhi_in (by linarith)
  have hcont_phi : ∀ y : ℝ, Continuous (fun e => askingPhi M ρ e y) := by
    intro y; unfold askingPhi
    have hp := poolAvg_continuous M.n (by have := M.hn; omega)
    exact (by fun_prop : Continuous (fun e => (1 - (qRho M ρ + (y - e) / ((M.m : ℝ) - 1))) ^ (M.n - 1))).sub
      (hp.comp (Continuous.prodMk (by fun_prop) continuous_const))
  obtain ⟨δ₁, hδ₁, h1⟩ := Metric.continuousAt_iff.mp (hcont_phi y_lo).continuousAt (askingPhi M ρ e₀ y_lo) hpos_lo
  obtain ⟨δ₂, hδ₂, h2⟩ := Metric.continuousAt_iff.mp (hcont_phi y_hi).continuousAt (-askingPhi M ρ e₀ y_hi) (by linarith)
  have hm : (0 : ℝ) < M.m := M.m_pos_real
  let δ₃ := min ((y_lo - e₀ / (M.m : ℝ)) * (M.m : ℝ) / 2) ((e₀ - y_hi) / 2)
  have hδ₃ : 0 < δ₃ := lt_min (by positivity) (by linarith)
  refine ⟨min δ₁ (min δ₂ δ₃), lt_min hδ₁ (lt_min hδ₂ hδ₃), fun e he hdist => ?_⟩
  have hd1 : dist e e₀ < δ₁ := lt_of_lt_of_le hdist (min_le_left _ _)
  have hd2 : dist e e₀ < δ₂ := lt_of_lt_of_le hdist (le_trans (min_le_right _ _) (min_le_left _ _))
  have hd3 : dist e e₀ < δ₃ := lt_of_lt_of_le hdist (le_trans (min_le_right _ _) (min_le_right _ _))
  rw [Real.dist_eq] at hd3 ⊢
  have hphi_lo : 0 < askingPhi M ρ e y_lo := by
    have := h1 hd1; rw [Real.dist_eq] at this; linarith [(abs_lt.mp this).1]
  have hphi_hi : askingPhi M ρ e y_hi < 0 := by
    have := h2 hd2; rw [Real.dist_eq] at this; linarith [(abs_lt.mp this).2]
  have hlo_e : y_lo ∈ Icc (e / (M.m : ℝ)) e := by
    have hd3a : |e - e₀| < (y_lo - e₀ / (M.m : ℝ)) * (M.m : ℝ) / 2 :=
      lt_of_lt_of_le hd3 (min_le_left _ _)
    have hd3b : |e - e₀| < (e₀ - y_hi) / 2 := lt_of_lt_of_le hd3 (min_le_right _ _)
    constructor
    · rw [div_le_iff₀ hm]
      have : e < e₀ + (y_lo - e₀ / (M.m : ℝ)) * (M.m : ℝ) / 2 := by linarith [(abs_lt.mp hd3a).2]
      have hmul : (y_lo - e₀ / (M.m : ℝ)) * (M.m : ℝ) = y_lo * (M.m : ℝ) - e₀ := by
        field_simp [hm.ne']
      have hgt : e₀ < y_lo * (M.m : ℝ) := (div_lt_iff₀ hm).mp hlo_gt
      linarith
    · have : e₀ - (e₀ - y_hi) / 2 < e := by linarith [(abs_lt.mp hd3b).1]
      linarith
  have hhi_e : y_hi ∈ Icc (e / (M.m : ℝ)) e := by
    have hd3b : |e - e₀| < (e₀ - y_hi) / 2 := lt_of_lt_of_le hd3 (min_le_right _ _)
    have hy_le : y_lo ≤ y_hi := by dsimp [y_lo, y_hi]; linarith
    exact ⟨le_trans hlo_e.1 hy_le, by linarith [(abs_lt.mp hd3b).1]⟩
  have hys := askingY_spec M hρa hρ1 he.1 he.2
  have hanti := askingPhi_strictAntiOn M hρa hρ1 he.1 he.2
  have hgt_lo : y_lo < askingY M ρ e := by
    by_contra hle; push Not at hle
    rcases eq_or_lt_of_le hle with h | h
    · rw [← h, hys.2] at hphi_lo; linarith
    · have := hanti (Ioo_subset_Icc_self hys.1) hlo_e h
      rw [hys.2] at this; linarith
  have hlt_hi : askingY M ρ e < y_hi := by
    by_contra hle; push Not at hle
    rcases eq_or_lt_of_le hle with h | h
    · rw [h, hys.2] at hphi_hi; linarith
    · have := hanti hhi_e (Ioo_subset_Icc_self hys.1) h
      rw [hys.2] at this; linarith
  have hδy_ε : δy ≤ ε / 2 := min_le_left _ _
  rw [abs_lt]
  constructor <;> linarith

lemma askingBeta_continuousOn (M : Market) {ρ : ℝ} (hρa : M.a ≤ ρ) (hρ1 : ρ < 1) :
    ContinuousOn (askingBeta M ρ) (Ioo (0 : ℝ) (qRho M ρ)) := by
  have hy_cont := askingY_continuousOn M hρa hρ1
  have hq1_cont : ContinuousOn (askingQ1 M ρ) (Ioo 0 (qRho M ρ)) := continuousOn_const.sub hy_cont
  have hq0_cont : ContinuousOn (askingQ0 M ρ) (Ioo 0 (qRho M ρ)) :=
    continuousOn_const.add ((hy_cont.sub continuousOn_id).div_const _)
  have hbarx_cont : ContinuousOn (askingBarX M ρ) (Ioo 0 (qRho M ρ)) :=
    (continuousOn_const.sub hq0_cont).pow _
  have hFρ_mem := M.F_mem_Icc ⟨hρa, hρ1.le⟩
  have hm : (0 : ℝ) < M.m := M.m_pos_real
  have hmq : (M.m : ℝ) * qRho M ρ = 1 - M.F ρ := by unfold qRho; field_simp [hm.ne']
  have hv1_cont : ContinuousOn (askingV1 M ρ) (Ioo 0 (qRho M ρ)) := by
    refine M.invF_continuousOn.comp (continuousOn_const.add continuousOn_id) ?_
    intro e he
    have hm2 : (2 : ℝ) ≤ M.m := by exact_mod_cast M.hm
    have he1 : e ≤ (M.m : ℝ) * qRho M ρ := by nlinarith [he.1, he.2]
    exact ⟨by linarith [hFρ_mem.1, he.1], by linarith [hmq]⟩
  have hv2_cont : ContinuousOn (askingV2 M ρ) (Ioo 0 (qRho M ρ)) := by
    refine M.invF_continuousOn.comp (continuousOn_const.add (continuousOn_const.mul hy_cont)) ?_
    intro e he
    have hys := askingY_spec M hρa hρ1 he.1 he.2
    have hy0 : 0 < askingY M ρ e := lt_trans (div_pos he.1 hm) hys.1.1
    exact ⟨by linarith [hFρ_mem.1, mul_pos hm hy0], by nlinarith [hys.1.2, he.2, hmq]⟩
  let c : ℝ → ℝ := fun e => 1 - askingQ1 M ρ e - M.F (askingV2 M ρ e) / ((M.m : ℝ) - 1)
  have hv2_in : MapsTo (askingV2 M ρ) (Ioo 0 (qRho M ρ)) (Icc M.a 1) := fun e he => by
    have hc := asking_coords M hρa hρ1 he.1 he.2
    exact ⟨le_trans hρa (le_trans hc.2.2.2.2.2.1.le hc.2.2.2.2.2.2.1.le), hc.2.2.2.2.2.2.2.1.le⟩
  have hv1_in : MapsTo (askingV1 M ρ) (Ioo 0 (qRho M ρ)) (Icc M.a 1) := fun e he => by
    have hc := asking_coords M hρa hρ1 he.1 he.2
    exact ⟨le_trans hρa hc.2.2.2.2.2.1.le, le_trans hc.2.2.2.2.2.2.1.le hc.2.2.2.2.2.2.2.1.le⟩
  have hc_cont : ContinuousOn c (Ioo 0 (qRho M ρ)) :=
    (continuousOn_const.sub hq1_cont).sub ((M.F_continuousOn.comp hv2_cont hv2_in).div_const _)
  have hH_cont : ∀ k : ℕ, ContinuousOn (fun x => ∫ v in M.a..x, (M.F v / ((M.m : ℝ) - 1)) ^ k) (Icc M.a 1) :=
    fun k => continuousOn_primitive_Icc M.ha1.le ((M.F_continuousOn.div_const _).pow k)
  have hint_eq : ∀ e ∈ Ioo 0 (qRho M ρ),
      (∫ v in askingV1 M ρ e..askingV2 M ρ e, (askingFriv M ρ e v ^ (M.n - 1) - askingBarX M ρ e)) =
      (∑ k ∈ Finset.range M.n,
        ((M.n - 1).choose k : ℝ) * (c e) ^ (M.n - 1 - k) *
          ((∫ v in M.a..askingV2 M ρ e, (M.F v / ((M.m : ℝ) - 1)) ^ k) -
           (∫ v in M.a..askingV1 M ρ e, (M.F v / ((M.m : ℝ) - 1)) ^ k))) -
      askingBarX M ρ e * (askingV2 M ρ e - askingV1 M ρ e) := by
    intro e he
    have hc := asking_coords M hρa hρ1 he.1 he.2
    rcases hc with ⟨_, _, _, _, _, hρv1, hv1v2, hv21, _, _, _, _, _, _, _, _⟩
    set v₁ := askingV1 M ρ e
    set v₂ := askingV2 M ρ e
    have hFriv_eq : ∀ v, askingFriv M ρ e v ^ (M.n - 1) =
        ∑ k ∈ Finset.range M.n,
          ((M.n - 1).choose k : ℝ) * (c e) ^ (M.n - 1 - k) * (M.F v / ((M.m : ℝ) - 1)) ^ k := by
      intro v
      have hsum : askingFriv M ρ e v = M.F v / ((M.m : ℝ) - 1) + c e := by
        unfold askingFriv; dsimp [c]; ring
      rw [hsum, add_pow, show M.n - 1 + 1 = M.n by have := M.hn; omega]
      apply Finset.sum_congr rfl; intro k _; ring
    have hint_k : ∀ k, IntervalIntegrable (fun v => (M.F v / ((M.m : ℝ) - 1)) ^ k) volume v₁ v₂ :=
      fun k => (((M.F_continuousOn.div_const _).pow k).mono
        (by rw [uIcc_of_le hv1v2.le]; exact Icc_subset_Icc (le_trans hρa hρv1.le) hv21.le)).intervalIntegrable
    have hint_Friv : IntervalIntegrable (fun v => askingFriv M ρ e v ^ (M.n - 1)) volume v₁ v₂ := by
      have hF_sub := M.F_continuousOn.mono (Icc_subset_Icc (le_trans hρa hρv1.le) hv21.le)
      have hcF : ContinuousOn (fun v => askingFriv M ρ e v ^ (M.n - 1)) (Icc v₁ v₂) := by
        unfold askingFriv; fun_prop
      exact (hcF.mono (by rw [uIcc_of_le hv1v2.le])).intervalIntegrable
    rw [intervalIntegral.integral_sub hint_Friv intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul, mul_comm (v₂ - v₁)]
    congr 1
    simp_rw [hFriv_eq]
    rw [intervalIntegral_finset_sum_local _ (fun k _ => (hint_k k).const_mul _)]
    apply Finset.sum_congr rfl
    intro k _
    rw [intervalIntegral.integral_const_mul]
    congr 1
    have hi1 : IntervalIntegrable (fun v => (M.F v / ((M.m : ℝ) - 1)) ^ k) volume M.a v₁ :=
      (((M.F_continuousOn.div_const _).pow k).mono
        (by rw [uIcc_of_le (le_trans hρa hρv1.le)]; exact Icc_subset_Icc le_rfl (le_trans hv1v2.le hv21.le))).intervalIntegrable
    have hadd := intervalIntegral.integral_add_adjacent_intervals hi1 (hint_k k)
    linarith
  have hint_cont : ContinuousOn
      (fun e => ∫ v in askingV1 M ρ e..askingV2 M ρ e, (askingFriv M ρ e v ^ (M.n - 1) - askingBarX M ρ e))
      (Ioo 0 (qRho M ρ)) := by
    apply ContinuousOn.congr _ hint_eq
    refine ContinuousOn.sub ?_ (hbarx_cont.mul (hv2_cont.sub hv1_cont))
    exact continuousOn_finset_sum_local (Finset.range M.n) (fun k _ =>
      (continuousOn_const.mul (hc_cont.pow (M.n - 1 - k))).mul
        (((hH_cont k).comp hv2_cont hv2_in).sub ((hH_cont k).comp hv1_cont hv1_in)))
  unfold askingBeta
  refine hv2_cont.sub (hint_cont.div ((continuousOn_const.sub hq1_cont).pow _ |>.sub hbarx_cont) ?_)
  intro e he
  have hc := asking_coords M hρa hρ1 he.1 he.2
  have hqhalf := qRho_le_half M hρa hρ1.le
  unfold askingBarX
  have hlt := pow_lt_pow_left₀ (by linarith [hc.2.1] : 1 - askingQ0 M ρ e < 1 - askingQ1 M ρ e)
    (by linarith [hc.2.2.1]) M.n_sub_one_ne_zero
  linarith

/-! #### Modular Sub-Lemmas for `askingBeta_asymptotic` -/

lemma askingY_div_e_tendsto (M : Market) {ρ : ℝ} (hρa : M.a ≤ ρ) (hρ1 : ρ < 1) :
    Tendsto (fun e => askingY M ρ e / e) (𝓝[>] 0) (nhds (((M.m : ℝ) + 1) / (2 * (M.m : ℝ)))) := by
  have hqpos := qRho_pos M hρa hρ1
  obtain ⟨Cy, hCy, hy_asym⟩ := askingY_asymptotic M hρa hρ1
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [Ioo_mem_nhdsGT hqpos, Ioo_mem_nhdsGT (div_pos hε (by linarith : 0 < Cy + 1))] with e he1 he2
  rw [Real.dist_eq]
  have h1 := hy_asym e he1
  have hdiv : |askingY M ρ e / e - (((M.m : ℝ) + 1) / (2 * (M.m : ℝ)))| ≤ Cy * e := by
    have hid : askingY M ρ e / e - (((M.m : ℝ) + 1) / (2 * (M.m : ℝ))) =
        (askingY M ρ e - (((M.m : ℝ) + 1) / (2 * (M.m : ℝ))) * e) / e := by
      field_simp [he1.1.ne']
    rw [hid, abs_div, abs_of_pos he1.1, div_le_iff₀ he1.1]
    linarith [show Cy * e * e = Cy * e ^ 2 by ring]
  calc _ ≤ Cy * e := hdiv
    _ ≤ (Cy + 1) * e := by nlinarith [he1.1]
    _ < ε := by
      have := he2.2; rwa [lt_div_iff₀ (by linarith : 0 < Cy + 1), mul_comm] at this

lemma askingV2_tendsto (M : Market) {ρ : ℝ} (hρa : M.a ≤ ρ) (hρ1 : ρ < 1) :
    Tendsto (askingV2 M ρ) (𝓝[>] 0) (nhds ρ) := by
  have hqpos := qRho_pos M hρa hρ1
  have hm := M.m_pos_real
  obtain ⟨fmin, hfmin, hf_lo⟩ := M.exists_f_min
  obtain ⟨fmax, _, hf_hi⟩ := M.exists_f_max
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [Ioo_mem_nhdsGT hqpos, Ioo_mem_nhdsGT (div_pos (mul_pos hfmin hε) hm)] with e he1 he2
  have hc := asking_coords M hρa hρ1 he1.1 he1.2
  have hys := askingY_spec M hρa hρ1 he1.1 he1.2
  have hlip := (M.F_lipschitz_bounds ⟨hρa, hρ1.le⟩
    ⟨le_trans hρa (by linarith [hc.2.2.2.2.2.1, hc.2.2.2.2.2.2.1]), hc.2.2.2.2.2.2.2.1.le⟩
    (by linarith [hc.2.2.2.2.2.1, hc.2.2.2.2.2.2.1]) hf_lo hf_hi).1
  rw [hc.2.2.2.2.2.2.2.2.2.1] at hlip
  rw [Real.dist_eq, abs_of_pos (by linarith [hc.2.2.2.2.2.1, hc.2.2.2.2.2.2.1])]
  have hmy : (M.m : ℝ) * askingY M ρ e < (M.m : ℝ) * e := mul_lt_mul_of_pos_left hys.1.2 hm
  have he_b : (M.m : ℝ) * e < fmin * ε := by
    have := he2.2; rwa [lt_div_iff₀ hm, mul_comm] at this
  nlinarith

lemma F_slope_tendsto (M : Market) {ρ : ℝ} (hρa : M.a ≤ ρ) (hρ1 : ρ < 1) :
    Tendsto (fun v => (M.F v - M.F ρ) / (v - ρ)) (𝓝[>] ρ) (nhds (M.f ρ)) := by
  have hd' : HasDerivWithinAt M.F (M.f ρ) (Ioi ρ) ρ := by
    rw [hasDerivWithinAt_iff_tendsto_slope]
    have h1 := hasDerivWithinAt_iff_tendsto_slope.mp (M.hF_deriv_within ρ ⟨hρa, hρ1.le⟩)
    refine h1.mono_left fun s hs => ?_
    rw [mem_nhdsWithin] at hs ⊢
    obtain ⟨u, huo, hρu, hus⟩ := hs
    refine ⟨u ∩ Iio 1, huo.inter isOpen_Iio, ⟨hρu, hρ1⟩, fun x hx => ?_⟩
    exact hus ⟨hx.1.1, ⟨⟨le_trans hρa hx.2.1.le, hx.1.2.le⟩, hx.2.2⟩⟩
  have h1 := hasDerivWithinAt_iff_tendsto_slope.mp hd'
  have h2 : slope M.F ρ = fun v => (M.F v - M.F ρ) / (v - ρ) := by
    ext v; rw [slope_def_field]
  rw [h2] at h1
  exact h1.mono_left (nhdsWithin_mono ρ fun x hx => ⟨hx, ne_of_gt hx⟩)

lemma askingRatio_tendsto (M : Market) {ρ : ℝ} (hρa : M.a ≤ ρ) (hρ1 : ρ < 1) :
    Tendsto (fun e =>
      ((M.m : ℝ) - 1) *
        ((((1 - askingQ1 M ρ e) ^ M.n - (1 - askingQ0 M ρ e) ^ M.n) / (M.n : ℝ) -
            (1 - askingQ0 M ρ e) ^ (M.n - 1) * (askingQ0 M ρ e - askingQ1 M ρ e)) /
          (((1 - askingQ1 M ρ e) ^ (M.n - 1) - (1 - askingQ0 M ρ e) ^ (M.n - 1)) * e)))
      (𝓝[>] 0) (nhds (((M.m : ℝ) - 1) / 4)) := by
  have hqpos := qRho_pos M hρa hρ1
  have hqhalf := qRho_le_half M hρa hρ1.le
  have hm := M.m_pos_real
  have hm1 := M.m_sub_one_pos_real
  have hn1 := M.n_sub_one_pos_real
  have h_y_lim := askingY_div_e_tendsto M hρa hρ1
  set A := 1 - qRho M ρ
  have hApos : 0 < A := by linarith
  obtain ⟨C₁, hC₁, hpowA⟩ := pow_first_order_bound (M.n - 1) A
  obtain ⟨C₂, hC₂, hpoolA⟩ := poolAvg_first_order_bound M.n M.hn A
  have hΔ_lim : Tendsto (fun e => (askingQ0 M ρ e - askingQ1 M ρ e) / e) (𝓝[>] 0) (nhds (1 / 2)) := by
    have hEq : ∀ e ≠ 0, (askingQ0 M ρ e - askingQ1 M ρ e) / e =
        ((M.m : ℝ) * (askingY M ρ e / e) - 1) / ((M.m : ℝ) - 1) := by
      intro e he0; unfold askingQ0 askingQ1; field_simp [hm1.ne', he0]; ring
    have hlim : Tendsto (fun e => ((M.m : ℝ) * (askingY M ρ e / e) - 1) / ((M.m : ℝ) - 1))
        (𝓝[>] 0) (nhds (((M.m : ℝ) * (((M.m : ℝ) + 1) / (2 * (M.m : ℝ))) - 1) / ((M.m : ℝ) - 1))) :=
      ((h_y_lim.const_mul (M.m : ℝ)).sub tendsto_const_nhds).div_const ((M.m : ℝ) - 1)
    have hval : ((M.m : ℝ) * (((M.m : ℝ) + 1) / (2 * (M.m : ℝ))) - 1) / ((M.m : ℝ) - 1) = 1 / 2 := by
      field_simp [hm.ne', hm1.ne']; ring
    rw [hval] at hlim
    exact hlim.congr' (by filter_upwards [self_mem_nhdsWithin] with e he using (hEq e (ne_of_gt he)).symm)
  have hnum_lim : Tendsto (fun e =>
      (poolAvg M.n (1 - askingQ0 M ρ e) (1 - askingQ1 M ρ e) - (1 - askingQ0 M ρ e) ^ (M.n - 1)) / e)
      (𝓝[>] 0) (nhds (((M.n : ℝ) - 1) * A ^ (M.n - 2) * (1 / 4))) := by
    have hlin_lim : Tendsto (fun e => ((M.n : ℝ) - 1) * A ^ (M.n - 2) * ((askingQ0 M ρ e - askingQ1 M ρ e) / (2 * e)))
        (𝓝[>] 0) (nhds (((M.n : ℝ) - 1) * A ^ (M.n - 2) * (1 / 4))) := by
      have := (hΔ_lim.div_const 2).const_mul (((M.n : ℝ) - 1) * A ^ (M.n - 2))
      convert this using 1
      · ext e; ring
      · ring
    have hrem : Tendsto (fun e =>
        (poolAvg M.n (1 - askingQ0 M ρ e) (1 - askingQ1 M ρ e) - (1 - askingQ0 M ρ e) ^ (M.n - 1)) / e -
        ((M.n : ℝ) - 1) * A ^ (M.n - 2) * ((askingQ0 M ρ e - askingQ1 M ρ e) / (2 * e)))
        (𝓝[>] 0) (nhds 0) := by
      rw [Metric.tendsto_nhds]
      intro ε₂ hε₂
      let Ctot := 4 * C₂ + C₁
      filter_upwards [Ioo_mem_nhdsGT hqpos, Ioo_mem_nhdsGT (div_pos hε₂ (by linarith : 0 < Ctot + 1))] with e he1 he2
      rw [Real.dist_eq, sub_zero]
      have hys := askingY_spec M hρa hρ1 he1.1 he1.2
      have hy0 : 0 < askingY M ρ e := lt_trans (div_pos he1.1 hm) hys.1.1
      have he1_le : e ≤ 1 := by linarith [he1.2, hqhalf]
      let h₀ := (e - askingY M ρ e) / ((M.m : ℝ) - 1)
      have hh₀_le : |h₀| ≤ e := by
        dsimp [h₀]; rw [abs_div, abs_of_pos hm1, abs_of_pos (by linarith [hys.1.2])]
        have hm2 : (2 : ℝ) ≤ M.m := by exact_mod_cast M.hm
        exact le_trans (div_le_div_of_nonneg_right (by linarith : e - askingY M ρ e ≤ e) hm1.le)
          (div_le_self he1.1.le (by linarith))
      have hy_le : |askingY M ρ e| ≤ e := by rw [abs_of_pos hy0]; exact hys.1.2.le
      have hp1 := hpoolA h₀ (askingY M ρ e) (le_trans hh₀_le he1_le) (le_trans hy_le he1_le)
      have hp2 := hpowA h₀ (le_trans hh₀_le he1_le)
      have hA1 : A + h₀ = 1 - askingQ0 M ρ e := by dsimp [A, h₀]; unfold askingQ0; ring
      have hA2 : A + askingY M ρ e = 1 - askingQ1 M ρ e := by dsimp [A]; unfold askingQ1; ring
      have hcast : ((M.n - 1 : ℕ) : ℝ) = (M.n : ℝ) - 1 := by
        rw [Nat.cast_sub (by have := M.hn; omega), Nat.cast_one]
      have hsub : M.n - 1 - 1 = M.n - 2 := by omega
      rw [hA1, hA2] at hp1
      rw [hA1, hcast, hsub] at hp2
      set X₁ := poolAvg M.n (1 - askingQ0 M ρ e) (1 - askingQ1 M ρ e) - A ^ (M.n - 1) -
          ((M.n : ℝ) - 1) * A ^ (M.n - 2) * ((h₀ + askingY M ρ e) / 2)
      set X₂ := (1 - askingQ0 M ρ e) ^ (M.n - 1) - A ^ (M.n - 1) -
          ((M.n : ℝ) - 1) * A ^ (M.n - 2) * h₀
      have hdiv_id : (poolAvg M.n (1 - askingQ0 M ρ e) (1 - askingQ1 M ρ e) - (1 - askingQ0 M ρ e) ^ (M.n - 1)) / e -
          ((M.n : ℝ) - 1) * A ^ (M.n - 2) * ((askingQ0 M ρ e - askingQ1 M ρ e) / (2 * e)) = (X₁ - X₂) / e := by
        have hqd : askingQ0 M ρ e - askingQ1 M ρ e = askingY M ρ e - h₀ := by
          dsimp [h₀]; unfold askingQ0 askingQ1; ring
        rw [hqd]; dsimp [X₁, X₂]; field_simp [he1.1.ne']; ring
      rw [hdiv_id, abs_div, abs_of_pos he1.1]
      have htri : |X₁ - X₂| ≤ |X₁| + |X₂| := by simpa [sub_zero, zero_sub, abs_neg] using abs_sub_le X₁ 0 X₂
      have hsq1 : (|h₀| + |askingY M ρ e|) ^ 2 ≤ (2 * e) ^ 2 := by gcongr; linarith
      have hsq2 : h₀ ^ 2 ≤ e ^ 2 := by rw [← sq_abs]; gcongr
      have hnum_b : |X₁ - X₂| ≤ Ctot * e ^ 2 := by dsimp [Ctot]; nlinarith
      calc _ ≤ (Ctot * e ^ 2) / e := div_le_div_of_nonneg_right hnum_b he1.1.le
        _ = Ctot * e := by field_simp [he1.1.ne']
        _ ≤ (Ctot + 1) * e := by nlinarith [he1.1]
        _ < ε₂ := by have := he2.2; rwa [lt_div_iff₀ (by linarith : 0 < Ctot + 1), mul_comm] at this
    have hsum := hrem.add hlin_lim
    rw [zero_add] at hsum
    exact hsum.congr (fun e => by ring)
  have hden_lim : Tendsto (fun e =>
      ((1 - askingQ1 M ρ e) ^ (M.n - 1) - (1 - askingQ0 M ρ e) ^ (M.n - 1)) / e)
      (𝓝[>] 0) (nhds (((M.n : ℝ) - 1) * A ^ (M.n - 2) * (1 / 2))) := by
    have hlin_lim := hΔ_lim.const_mul (((M.n : ℝ) - 1) * A ^ (M.n - 2))
    have hrem : Tendsto (fun e =>
        ((1 - askingQ1 M ρ e) ^ (M.n - 1) - (1 - askingQ0 M ρ e) ^ (M.n - 1)) / e -
        ((M.n : ℝ) - 1) * A ^ (M.n - 2) * ((askingQ0 M ρ e - askingQ1 M ρ e) / e))
        (𝓝[>] 0) (nhds 0) := by
      rw [Metric.tendsto_nhds]
      intro ε₂ hε₂
      filter_upwards [Ioo_mem_nhdsGT hqpos, Ioo_mem_nhdsGT (div_pos hε₂ (by linarith : 0 < 2 * C₁ + 1))] with e he1 he2
      rw [Real.dist_eq, sub_zero]
      have hys := askingY_spec M hρa hρ1 he1.1 he1.2
      have hy0 : 0 < askingY M ρ e := lt_trans (div_pos he1.1 hm) hys.1.1
      have he1_le : e ≤ 1 := by linarith [he1.2, hqhalf]
      let h₀ := (e - askingY M ρ e) / ((M.m : ℝ) - 1)
      have hh₀_le : |h₀| ≤ e := by
        dsimp [h₀]; rw [abs_div, abs_of_pos hm1, abs_of_pos (by linarith [hys.1.2])]
        have hm2 : (2 : ℝ) ≤ M.m := by exact_mod_cast M.hm
        exact le_trans (div_le_div_of_nonneg_right (by linarith : e - askingY M ρ e ≤ e) hm1.le)
          (div_le_self he1.1.le (by linarith))
      have hy_le : |askingY M ρ e| ≤ e := by rw [abs_of_pos hy0]; exact hys.1.2.le
      have hp1 := hpowA (askingY M ρ e) (le_trans hy_le he1_le)
      have hp2 := hpowA h₀ (le_trans hh₀_le he1_le)
      have hA1 : A + askingY M ρ e = 1 - askingQ1 M ρ e := by dsimp [A]; unfold askingQ1; ring
      have hA2 : A + h₀ = 1 - askingQ0 M ρ e := by dsimp [A, h₀]; unfold askingQ0; ring
      have hcast : ((M.n - 1 : ℕ) : ℝ) = (M.n : ℝ) - 1 := by
        rw [Nat.cast_sub (by have := M.hn; omega), Nat.cast_one]
      have hsub : M.n - 1 - 1 = M.n - 2 := by omega
      rw [hA1, hcast, hsub] at hp1
      rw [hA2, hcast, hsub] at hp2
      set X₁ := (1 - askingQ1 M ρ e) ^ (M.n - 1) - A ^ (M.n - 1) - ((M.n : ℝ) - 1) * A ^ (M.n - 2) * askingY M ρ e
      set X₂ := (1 - askingQ0 M ρ e) ^ (M.n - 1) - A ^ (M.n - 1) - ((M.n : ℝ) - 1) * A ^ (M.n - 2) * h₀
      have hdiv_id : ((1 - askingQ1 M ρ e) ^ (M.n - 1) - (1 - askingQ0 M ρ e) ^ (M.n - 1)) / e -
          ((M.n : ℝ) - 1) * A ^ (M.n - 2) * ((askingQ0 M ρ e - askingQ1 M ρ e) / e) = (X₁ - X₂) / e := by
        have hqd : askingQ0 M ρ e - askingQ1 M ρ e = askingY M ρ e - h₀ := by
          dsimp [h₀]; unfold askingQ0 askingQ1; ring
        rw [hqd]; dsimp [X₁, X₂]; field_simp [he1.1.ne']; ring
      rw [hdiv_id, abs_div, abs_of_pos he1.1]
      have htri : |X₁ - X₂| ≤ |X₁| + |X₂| := by simpa [sub_zero, zero_sub, abs_neg] using abs_sub_le X₁ 0 X₂
      have hsq1 : askingY M ρ e ^ 2 ≤ e ^ 2 := by rw [← sq_abs]; gcongr
      have hsq2 : h₀ ^ 2 ≤ e ^ 2 := by rw [← sq_abs]; gcongr
      have hnum_b : |X₁ - X₂| ≤ 2 * C₁ * e ^ 2 := by nlinarith
      calc _ ≤ (2 * C₁ * e ^ 2) / e := div_le_div_of_nonneg_right hnum_b he1.1.le
        _ = 2 * C₁ * e := by field_simp [he1.1.ne']
        _ ≤ (2 * C₁ + 1) * e := by nlinarith [he1.1]
        _ < ε₂ := by have := he2.2; rwa [lt_div_iff₀ (by linarith : 0 < 2 * C₁ + 1), mul_comm] at this
    have hsum := hrem.add hlin_lim
    rw [zero_add] at hsum
    exact hsum.congr (fun e => by ring)
  have hden_ne : ((M.n : ℝ) - 1) * A ^ (M.n - 2) * (1 / 2) ≠ 0 := by positivity
  have hfrac_lim : Tendsto (fun e =>
      (poolAvg M.n (1 - askingQ0 M ρ e) (1 - askingQ1 M ρ e) - (1 - askingQ0 M ρ e) ^ (M.n - 1)) /
        ((1 - askingQ1 M ρ e) ^ (M.n - 1) - (1 - askingQ0 M ρ e) ^ (M.n - 1)))
      (𝓝[>] 0) (nhds (1 / 2)) := by
    have hq := hnum_lim.div hden_lim hden_ne
    have hval : (((M.n : ℝ) - 1) * A ^ (M.n - 2) * (1 / 4)) /
        (((M.n : ℝ) - 1) * A ^ (M.n - 2) * (1 / 2)) = 1 / 2 := by
      field_simp [hn1.ne', (pow_pos hApos (M.n - 2)).ne']; ring
    rw [hval] at hq
    refine hq.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with e he
    exact div_div_div_cancel_right₀ (ne_of_gt (mem_Ioi.mp he)) _ _
  have hprod := (hΔ_lim.mul hfrac_lim).const_mul ((M.m : ℝ) - 1)
  have hval : ((M.m : ℝ) - 1) * (1 / 2 * (1 / 2)) = ((M.m : ℝ) - 1) / 4 := by ring
  rw [hval] at hprod
  refine hprod.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hqpos] with e he
  have hc := asking_coords M hρa hρ1 he.1 he.2
  have hne : 1 - askingQ0 M ρ e ≠ 1 - askingQ1 M ρ e := by linarith [hc.2.1]
  unfold poolAvg
  simp only [hne, ↓reduceIte]
  have hsub : (1 - askingQ1 M ρ e) - (1 - askingQ0 M ρ e) = askingQ0 M ρ e - askingQ1 M ρ e := by ring
  rw [hsub]
  have hΔpos : 0 < askingQ0 M ρ e - askingQ1 M ρ e := by linarith [hc.2.1]
  have hnR : (M.n : ℝ) ≠ 0 := M.n_pos_real.ne'
  field_simp [hΔpos.ne', hnR, he.1.ne']

lemma askingV2_sub_beta_tendsto (M : Market) {ρ : ℝ} (hρa : M.a ≤ ρ) (hρ1 : ρ < 1) :
    Tendsto (fun e => (askingV2 M ρ e - askingBeta M ρ e) / e) (𝓝[>] 0)
      (nhds (((M.m : ℝ) - 1) / (4 * M.f ρ))) := by
  have hqpos := qRho_pos M hρa hρ1
  have hqhalf := qRho_le_half M hρa hρ1.le
  have hm1 := M.m_sub_one_pos_real
  have hfρ : 0 < M.f ρ := M.hf_pos ρ ⟨hρa, hρ1.le⟩
  have hv2_lim := askingV2_tendsto M hρa hρ1
  have hR_lim := askingRatio_tendsto M hρa hρ1
  let R : ℝ → ℝ := fun e =>
    ((M.m : ℝ) - 1) *
      ((((1 - askingQ1 M ρ e) ^ M.n - (1 - askingQ0 M ρ e) ^ M.n) / (M.n : ℝ) -
          (1 - askingQ0 M ρ e) ^ (M.n - 1) * (askingQ0 M ρ e - askingQ1 M ρ e)) /
        (((1 - askingQ1 M ρ e) ^ (M.n - 1) - (1 - askingQ0 M ρ e) ^ (M.n - 1)) * e))
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hfc := Metric.continuousWithinAt_iff.mp (M.hf_cont ρ ⟨hρa, hρ1.le⟩)
  let η := min (M.f ρ / 4) (ε * (M.f ρ) ^ 2 / (2 * (M.m : ℝ) + 4))
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  obtain ⟨δ, hδ, hfδ⟩ := hfc η hη
  have hR_near := Metric.tendsto_nhds.mp hR_lim (ε * (M.f ρ) / 4) (by positivity)
  filter_upwards [Ioo_mem_nhdsGT hqpos,
    hv2_lim.eventually (Metric.ball_mem_nhds ρ hδ), hR_near] with e he hv2b hRb
  have hc := asking_coords M hρa hρ1 he.1 he.2
  rcases hc with ⟨_, hq1_lt_q0, hq0_lt_qr, _, _, hρv1, hv1v2, hv21, _, _, _, hFriv1, hFriv2, _, _, _⟩
  set v₁ := askingV1 M ρ e
  set v₂ := askingV2 M ρ e
  set q₁ := askingQ1 M ρ e
  set q₀ := askingQ0 M ρ e
  set barx := askingBarX M ρ e
  have hf_on : ∀ u ∈ Icc v₁ v₂, M.f ρ - η ≤ M.f u ∧ M.f u ≤ M.f ρ + η := by
    intro u hu
    have hu_mem : u ∈ Icc M.a 1 := ⟨le_trans hρa (le_trans hρv1.le hu.1), le_trans hu.2 hv21.le⟩
    have hdist : dist u ρ < δ := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hu.1, hρv1])]
      have hv2d : v₂ - ρ < δ := by
        have h : dist (askingV2 M ρ e) ρ < δ := hv2b
        rw [Real.dist_eq, abs_of_pos (by linarith [hρv1, hv1v2] : 0 < askingV2 M ρ e - ρ)] at h
        exact h
      linarith [hu.2]
    have h := hfδ hu_mem hdist
    rw [Real.dist_eq, abs_lt] at h
    exact ⟨by linarith, by linarith⟩
  have hF_sub := M.F_continuousOn.mono (Icc_subset_Icc (le_trans hρa hρv1.le) hv21.le)
  have hf_sub := M.hf_cont.mono (Icc_subset_Icc (le_trans hρa hρv1.le) hv21.le)
  have hFriv_cont : ContinuousOn (askingFriv M ρ e) (Icc v₁ v₂) := by unfold askingFriv; fun_prop
  have hint_g0 : IntervalIntegrable (fun v => askingFriv M ρ e v ^ (M.n - 1) - barx) volume v₁ v₂ :=
    (((hFriv_cont.pow _).sub continuousOn_const).mono (by rw [uIcc_of_le hv1v2.le])).intervalIntegrable
  have hint_gf : IntervalIntegrable (fun v => (askingFriv M ρ e v ^ (M.n - 1) - barx) * M.f v) volume v₁ v₂ :=
    ((((hFriv_cont.pow _).sub continuousOn_const).mul hf_sub).mono (by rw [uIcc_of_le hv1v2.le])).intervalIntegrable
  have hFTC : ∫ v in v₁..v₂, (askingFriv M ρ e v ^ (M.n - 1) - barx) * M.f v =
      ((M.m : ℝ) - 1) * (((1 - q₁) ^ M.n - (1 - q₀) ^ M.n) / (M.n : ℝ) -
        (1 - q₀) ^ (M.n - 1) * (q₀ - q₁)) := by
    let G : ℝ → ℝ := fun v => ((M.m : ℝ) - 1) *
      (askingFriv M ρ e v ^ M.n / (M.n : ℝ) - barx * askingFriv M ρ e v)
    have hG_cont : ContinuousOn G (Icc v₁ v₂) :=
      continuousOn_const.mul (((hFriv_cont.pow _).div_const _).sub (continuousOn_const.mul hFriv_cont))
    have hG_deriv : ∀ v ∈ Ioo v₁ v₂, HasDerivAt G ((askingFriv M ρ e v ^ (M.n - 1) - barx) * M.f v) v := by
      intro v hv
      have hv_open : v ∈ Ioo M.a 1 := ⟨lt_of_le_of_lt hρa (lt_trans hρv1 hv.1), lt_trans hv.2 hv21⟩
      have hFriv_d : HasDerivAt (askingFriv M ρ e) (M.f v / ((M.m : ℝ) - 1)) v := by
        unfold askingFriv
        have h1 := ((hasDerivAt_const v (M.F v₂)).sub (M.hF_deriv_open v hv_open)).div_const ((M.m : ℝ) - 1)
        convert (hasDerivAt_const v (1 - q₁)).sub h1 using 1; ring
      have htot := (((hFriv_d.pow M.n).div_const (M.n : ℝ)).sub (hFriv_d.const_mul barx)).const_mul ((M.m : ℝ) - 1)
      convert htot using 1
      have hnR : (M.n : ℝ) ≠ 0 := M.n_pos_real.ne'
      field_simp [hnR, hm1.ne']
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hv1v2.le hG_cont hG_deriv hint_gf]
    dsimp [G]; rw [hFriv2, hFriv1]; dsimp [barx]; unfold askingBarX; ring
  have hnonneg : ∀ v ∈ Icc v₁ v₂, 0 ≤ askingFriv M ρ e v ^ (M.n - 1) - barx := by
    intro v hv
    have hv_mem : v ∈ Icc M.a 1 := ⟨le_trans hρa (le_trans hρv1.le hv.1), le_trans hv.2 hv21.le⟩
    have hv1_mem : v₁ ∈ Icc M.a 1 := ⟨le_trans hρa hρv1.le, le_trans hv1v2.le hv21.le⟩
    have hF1 := M.F_strictMonoOn.monotoneOn hv1_mem hv_mem hv.1
    have hlo : 1 - q₀ ≤ askingFriv M ρ e v := by
      rw [← hFriv1]; unfold askingFriv
      have := div_le_div_of_nonneg_right (by linarith : M.F v₂ - M.F v ≤ M.F v₂ - M.F v₁) hm1.le
      linarith
    dsimp [barx]; unfold askingBarX
    have := pow_le_pow_left₀ (by linarith : 0 ≤ 1 - q₀) hlo (M.n - 1)
    linarith
  have hsand_lo : (M.f ρ - η) * (∫ v in v₁..v₂, (askingFriv M ρ e v ^ (M.n - 1) - barx)) ≤
      ∫ v in v₁..v₂, (askingFriv M ρ e v ^ (M.n - 1) - barx) * M.f v := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on hv1v2.le (hint_g0.const_mul _) hint_gf
      (fun v hv => by rw [mul_comm]; exact mul_le_mul_of_nonneg_left (hf_on v hv).1 (hnonneg v hv))
  have hsand_hi : ∫ v in v₁..v₂, (askingFriv M ρ e v ^ (M.n - 1) - barx) * M.f v ≤
      (M.f ρ + η) * (∫ v in v₁..v₂, (askingFriv M ρ e v ^ (M.n - 1) - barx)) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on hv1v2.le hint_gf (hint_g0.const_mul _)
      (fun v hv => by rw [mul_comm (M.f ρ + η)]; exact mul_le_mul_of_nonneg_left (hf_on v hv).2 (hnonneg v hv))
  have hden_pos : 0 < ((1 - q₁) ^ (M.n - 1) - barx) * e := by
    apply mul_pos _ he.1
    dsimp [barx]; unfold askingBarX
    have := pow_lt_pow_left₀ (by linarith : 1 - q₀ < 1 - q₁) (by linarith) M.n_sub_one_ne_zero
    linarith
  have hv2β_eq : (v₂ - askingBeta M ρ e) / e =
      (∫ v in v₁..v₂, (askingFriv M ρ e v ^ (M.n - 1) - barx)) / (((1 - q₁) ^ (M.n - 1) - barx) * e) := by
    unfold askingBeta
    have h1 : v₂ - (v₂ - (∫ v in v₁..v₂, (askingFriv M ρ e v ^ (M.n - 1) - barx)) /
        ((1 - q₁) ^ (M.n - 1) - barx)) =
        (∫ v in v₁..v₂, (askingFriv M ρ e v ^ (M.n - 1) - barx)) / ((1 - q₁) ^ (M.n - 1) - barx) := by ring
    rw [h1, div_div]
  have hR_eq : R e = (∫ v in v₁..v₂, (askingFriv M ρ e v ^ (M.n - 1) - barx) * M.f v) /
      (((1 - q₁) ^ (M.n - 1) - barx) * e) := by
    rw [hFTC]; dsimp [R, barx]; unfold askingBarX; ring
  have hfη_pos : 0 < M.f ρ - η := by have : η ≤ M.f ρ / 4 := min_le_left _ _; linarith only [this, hfρ]
  have hlow : R e / (M.f ρ + η) ≤ (v₂ - askingBeta M ρ e) / e := by
    rw [hv2β_eq, hR_eq, div_le_iff₀ (by positivity), div_mul_eq_mul_div,
      div_le_div_iff_of_pos_right hden_pos]
    linarith only [hsand_hi]
  have hhigh : (v₂ - askingBeta M ρ e) / e ≤ R e / (M.f ρ - η) := by
    rw [hv2β_eq, hR_eq, le_div_iff₀ hfη_pos, div_mul_eq_mul_div,
      div_le_div_iff_of_pos_right hden_pos]
    linarith only [hsand_lo]
  rw [Real.dist_eq] at hRb ⊢
  have hη_le2 : η ≤ ε * (M.f ρ) ^ 2 / (2 * (M.m : ℝ) + 4) := min_le_right _ _
  have hR_up : R e ≤ ((M.m : ℝ) - 1) / 4 + ε * M.f ρ / 4 := by linarith only [(abs_lt.mp hRb).2]
  have hR_dn : ((M.m : ℝ) - 1) / 4 - ε * M.f ρ / 4 ≤ R e := by linarith only [(abs_lt.mp hRb).1]
  rw [abs_lt]
  constructor
  · have h1 : (((M.m : ℝ) - 1) / 4 - ε * M.f ρ / 4) / (M.f ρ + η) ≤ R e / (M.f ρ + η) :=
      div_le_div_of_nonneg_right hR_dn (by positivity)
    have h2 : ((M.m : ℝ) - 1) / (4 * M.f ρ) - ε < (((M.m : ℝ) - 1) / 4 - ε * M.f ρ / 4) / (M.f ρ + η) := by
      rw [lt_div_iff₀ (by positivity)]
      have hstep : (((M.m : ℝ) - 1) / (4 * M.f ρ) - ε) * (M.f ρ + η) =
          ((M.m : ℝ) - 1) / 4 - ε * M.f ρ + (((M.m : ℝ) - 1) / (4 * M.f ρ) - ε) * η := by
        field_simp [hfρ.ne']
      rw [hstep]
      have hterm : (((M.m : ℝ) - 1) / (4 * M.f ρ)) * η ≤ ε * M.f ρ / 2 := by
        have hmul : η * (2 * (M.m : ℝ) + 4) ≤ ε * (M.f ρ) ^ 2 :=
          (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (M.m : ℝ) + 4)).mp hη_le2
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith only [hmul, hη, hfρ, hm1]
      have hεη : 0 < ε * η := mul_pos hε hη
      nlinarith only [hterm, hεη, hε, hfρ]
    linarith only [hlow, h1, h2]
  · have h1 : R e / (M.f ρ - η) ≤ (((M.m : ℝ) - 1) / 4 + ε * M.f ρ / 4) / (M.f ρ - η) :=
      div_le_div_of_nonneg_right hR_up hfη_pos.le
    have h2 : (((M.m : ℝ) - 1) / 4 + ε * M.f ρ / 4) / (M.f ρ - η) < ((M.m : ℝ) - 1) / (4 * M.f ρ) + ε := by
      rw [div_lt_iff₀ hfη_pos]
      have hstep : (((M.m : ℝ) - 1) / (4 * M.f ρ) + ε) * (M.f ρ - η) =
          ((M.m : ℝ) - 1) / 4 + ε * M.f ρ - (((M.m : ℝ) - 1) / (4 * M.f ρ) + ε) * η := by
        field_simp [hfρ.ne']
      rw [hstep]
      have hterm1 : (((M.m : ℝ) - 1) / (4 * M.f ρ)) * η ≤ ε * M.f ρ / 4 := by
        have hmul : η * (2 * (M.m : ℝ) + 4) ≤ ε * (M.f ρ) ^ 2 :=
          (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (M.m : ℝ) + 4)).mp hη_le2
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith only [hmul, hη, hfρ, hm1]
      have hterm2 : ε * η ≤ ε * M.f ρ / 4 := by
        have hη4 : η ≤ M.f ρ / 4 := min_le_left _ _
        nlinarith only [hε, hη4]
      nlinarith only [hterm1, hterm2, hε, hfρ]
    linarith only [hhigh, h1, h2]

lemma askingBeta_asymptotic (M : Market) {ρ : ℝ} (hρa : M.a ≤ ρ) (hρ1 : ρ < 1) :
    Tendsto (fun e => (M.F (askingBeta M ρ e) - M.F ρ) / e) (𝓝[>] 0) (nhds (((M.m : ℝ) + 3) / 4)) ∧
    Tendsto (fun e => (askingBeta M ρ e - ρ) / e) (𝓝[>] 0) (nhds (((M.m : ℝ) + 3) / (4 * M.f ρ))) := by
  have hqpos := qRho_pos M hρa hρ1
  have hm := M.m_pos_real
  have hfρ : 0 < M.f ρ := M.hf_pos ρ ⟨hρa, hρ1.le⟩
  have h_y_lim := askingY_div_e_tendsto M hρa hρ1
  have hv2_lim := askingV2_tendsto M hρa hρ1
  have hv2_sub_β_lim := askingV2_sub_beta_tendsto M hρa hρ1
  have hslope := F_slope_tendsto M hρa hρ1
  have hv2_sub_ρ_lim : Tendsto (fun e => (askingV2 M ρ e - ρ) / e) (𝓝[>] 0)
      (nhds (((M.m : ℝ) + 1) / (2 * M.f ρ))) := by
    have hF2_lim : Tendsto (fun e => (M.F (askingV2 M ρ e) - M.F ρ) / e) (𝓝[>] 0)
        (nhds (((M.m : ℝ) + 1) / 2)) := by
      have h := h_y_lim.const_mul (M.m : ℝ)
      have hval : (M.m : ℝ) * (((M.m : ℝ) + 1) / (2 * (M.m : ℝ))) = ((M.m : ℝ) + 1) / 2 := by
        field_simp [hm.ne']
      rw [hval] at h
      refine h.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT hqpos] with e he
      have hc := asking_coords M hρa hρ1 he.1 he.2
      rw [hc.2.2.2.2.2.2.2.2.2.1]; ring
    have hv2_gt : Tendsto (askingV2 M ρ) (𝓝[>] 0) (𝓝[>] ρ) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨hv2_lim, ?_⟩
      filter_upwards [Ioo_mem_nhdsGT hqpos] with e he
      have hc := asking_coords M hρa hρ1 he.1 he.2
      exact lt_trans hc.2.2.2.2.2.1 hc.2.2.2.2.2.2.1
    have hdiv := hF2_lim.div (hslope.comp hv2_gt) hfρ.ne'
    have hval : (((M.m : ℝ) + 1) / 2) / M.f ρ = ((M.m : ℝ) + 1) / (2 * M.f ρ) := by ring
    rw [hval] at hdiv
    refine hdiv.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hqpos] with e he
    have hc := asking_coords M hρa hρ1 he.1 he.2
    have hne : M.F (askingV2 M ρ e) - M.F ρ ≠ 0 := by
      rw [hc.2.2.2.2.2.2.2.2.2.1]
      have hys := askingY_spec M hρa hρ1 he.1 he.2
      have : 0 < (M.m : ℝ) * askingY M ρ e := mul_pos hm (lt_trans (div_pos he.1 hm) hys.1.1)
      linarith
    have hne2 : askingV2 M ρ e - ρ ≠ 0 := by linarith [hc.2.2.2.2.2.1, hc.2.2.2.2.2.2.1]
    dsimp [Function.comp]
    field_simp [he.1.ne', hne, hne2]
  have hβ_sub_lim : Tendsto (fun e => (askingBeta M ρ e - ρ) / e) (𝓝[>] 0)
      (nhds (((M.m : ℝ) + 3) / (4 * M.f ρ))) := by
    have hdiff := hv2_sub_ρ_lim.sub hv2_sub_β_lim
    have hval : ((M.m : ℝ) + 1) / (2 * M.f ρ) - ((M.m : ℝ) - 1) / (4 * M.f ρ) =
        ((M.m : ℝ) + 3) / (4 * M.f ρ) := by
      field_simp [hfρ.ne']; ring
    rw [hval] at hdiff
    exact hdiff.congr (fun e => by ring)
  have hFβ_lim : Tendsto (fun e => (M.F (askingBeta M ρ e) - M.F ρ) / e) (𝓝[>] 0)
      (nhds (((M.m : ℝ) + 3) / 4)) := by
    have hβ_gt : Tendsto (askingBeta M ρ) (𝓝[>] 0) (𝓝[>] ρ) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have h0 : Tendsto (fun e => e * ((askingBeta M ρ e - ρ) / e) + ρ) (𝓝[>] 0)
            (nhds (0 * (((M.m : ℝ) + 3) / (4 * M.f ρ)) + ρ)) :=
          ((tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).mul hβ_sub_lim).add tendsto_const_nhds
        rw [zero_mul, zero_add] at h0
        refine h0.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with e he
        rw [mul_div_cancel₀ _ (ne_of_gt (mem_Ioi.mp he))]; ring
      · filter_upwards [Ioo_mem_nhdsGT hqpos] with e he
        have hc := asking_coords M hρa hρ1 he.1 he.2
        exact lt_trans hc.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hprod := (hslope.comp hβ_gt).mul hβ_sub_lim
    have hval : M.f ρ * (((M.m : ℝ) + 3) / (4 * M.f ρ)) = ((M.m : ℝ) + 3) / 4 := by
      field_simp [hfρ.ne']
    rw [hval] at hprod
    refine hprod.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hqpos] with e he
    have hc := asking_coords M hρa hρ1 he.1 he.2
    have hne : askingBeta M ρ e - ρ ≠ 0 := by
      linarith [hc.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
    dsimp [Function.comp]
    field_simp [hne, he.1.ne']
  exact ⟨hFβ_lim, hβ_sub_lim⟩

/-- Exact `v`-coordinate formula for the asking-price revenue gain `D(e)`. -/
lemma askingRevGain_eq (M : Market) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hρa : M.a ≤ ρ) {e : ℝ} (he0 : 0 < e) (heq : e < qRho M ρ)
    (hρβ : ρ < askingBeta M ρ e) (hβ1 : askingBeta M ρ e ≤ 1) :
    sellerRev M (askingMech ρ (askingBeta M ρ e) hρ0.le hρβ hβ1)
        (askingVisit M ρ e) (seller0 M) -
      sellerRev M (SPA ρ hρ0.le hρ1.le) (unifVisit M) (seller0 M) =
    (M.n : ℝ) * ρ * (askingT0 M ρ e * (1 - askingQ0 M ρ e) ^ (M.n - 1) -
        qRho M ρ * (1 - qRho M ρ) ^ (M.n - 1)) +
      (M.n : ℝ) * ((M.n : ℝ) - 1) * askingQ1 M ρ e *
        (∫ v in askingV1 M ρ e..askingV2 M ρ e,
          v * askingFriv M ρ e v ^ (M.n - 2) * (M.f v / ((M.m : ℝ) - 1))) -
      (M.n : ℝ) * ((M.n : ℝ) - 1) *
        (∫ v in ρ..askingV2 M ρ e,
          v * (1 - M.A v) * M.A v ^ (M.n - 2) * (M.f v / (M.m : ℝ))) := by
  have hc := asking_coords M hρa hρ1 he0 heq
  rcases hc with ⟨_, _, _, _, _, hρv1, hv1v2, hv21, hFv1, _, hAv2, hFriv1, hFriv2, hbarx, hv1β, hβv2⟩
  set β := askingBeta M ρ e
  set v₁ := askingV1 M ρ e
  set v₂ := askingV2 M ρ e
  set q₁ := askingQ1 M ρ e
  set q₀ := askingQ0 M ρ e
  set t₀ := askingT0 M ρ e
  set mech := askingMech ρ β hρ0.le hρβ hβ1
  set θ := askingVisit M ρ e
  set barx := askingBarX M ρ e
  set s_unif : ℝ → ℝ := fun v => ∫ u in ρ..v, M.A u ^ (M.n - 1)
  set s_dev_v2 : ℝ := (v₁ - ρ) * barx + ∫ u in v₁..v₂, askingFriv M ρ e u ^ (M.n - 1)
  have hbal := askingBeta_balance M hρa hρ1 he0 heq
  have hρv2 : ρ ≤ v₂ := by linarith
  have hcontA : ContinuousOn (fun u => M.A u ^ (M.n - 1)) (Icc M.a 1) := M.A_continuousOn.pow _
  have hcont_s_top : ContinuousOn (fun v => ∫ u in v₂..v, M.A u ^ (M.n - 1)) (Icc v₂ 1) :=
    continuousOn_primitive_Icc hv21.le (hcontA.mono (Icc_subset_Icc (le_trans hρa hρv2) le_rfl))
  have hcont_s_unif : ContinuousOn s_unif (Icc ρ 1) :=
    continuousOn_primitive_Icc hρ1.le (hcontA.mono (Icc_subset_Icc hρa le_rfl))
  let g_top : ℝ → ℝ := fun v => (v * M.A v ^ (M.n - 1) - ∫ u in v₂..v, M.A u ^ (M.n - 1)) * (1 / (M.m : ℝ)) * M.f v
  have hg_top_int : IntervalIntegrable g_top volume v₂ 1 := by
    have hcont : ContinuousOn g_top (Icc v₂ 1) :=
      (((continuousOn_id.mul (hcontA.mono (Icc_subset_Icc (le_trans hρa hρv2) le_rfl))).sub hcont_s_top).mul
        continuousOn_const).mul (M.hf_cont.mono (Icc_subset_Icc (le_trans hρa hρv2) le_rfl))
    exact (hcont.mono (by rw [uIcc_of_le hv21.le])).intervalIntegrable
  have hf_top_int : IntervalIntegrable (fun v => (1 / (M.m : ℝ)) * M.f v) volume v₂ 1 :=
    ((M.hf_cont.mono (by rw [uIcc_of_le hv21.le]; exact Icc_subset_Icc (le_trans hρa hρv2) le_rfl)).intervalIntegrable).const_mul _
  have hI_f_top : ∫ v in v₂..1, (1 / (M.m : ℝ)) * M.f v = q₁ := by
    rw [intervalIntegral.integral_const_mul, ← M.F_sub_eq_integral (le_trans hρa hρv2) hv21.le le_rfl, M.hF_1]
    have h1 : 1 - (1 - M.F v₂) / (M.m : ℝ) = 1 - q₁ := hAv2
    have h2 : 1 / (M.m : ℝ) * (1 - M.F v₂) = (1 - M.F v₂) / (M.m : ℝ) := by ring
    linarith
  have hF0_ρ : effDist M θ (seller0 M) ρ = 1 - t₀ := by
    dsimp [θ]
    rw [effDist_askingVisit_seller0 M hρa hρ1 he0 heq le_rfl hρ1.le]
    have hle : ρ ≤ askingV1 M ρ e := hρv1.le
    simp only [hle, ↓reduceIte]
    change 1 - askingQ1 M ρ e - (M.F v₁ - M.F ρ) = 1 - t₀
    rw [hFv1]; dsimp [t₀]; unfold askingT0; ring
  have hF0_β : effDist M θ (seller0 M) β = 1 - q₁ := by
    dsimp [θ]
    rw [effDist_askingVisit_seller0 M hρa hρ1 he0 heq hρβ.le hβ1]
    have h1 : ¬askingBeta M ρ e ≤ askingV1 M ρ e := not_le.mpr hv1β
    have h2 : askingBeta M ρ e ≤ askingV2 M ρ e := hβv2.le
    simp only [β, h1, h2, ↓reduceIte]; rfl
  have hR_dev : sellerRev M mech θ (seller0 M) =
      (M.n : ℝ) * (ρ * barx * e + (∫ v in v₂..1, g_top v) - s_dev_v2 * q₁) := by
    unfold sellerRev
    congr 1
    let fn : ℝ → ℝ := fun v => payment M mech (effDist M θ (seller0 M)) v * θ.θ (seller0 M) v * M.f v
    have h_aρ : ∀ v ∈ Ioo M.a ρ, fn v = 0 := by
      intro v hv; dsimp [fn]; unfold payment
      have hall : alloc M mech (effDist M θ (seller0 M)) v = 0 := by
        unfold alloc mech askingMech; dsimp; simp [hv.2]
      have hsurp : surplus M mech (effDist M θ (seller0 M)) v = 0 := by
        rw [surplus_askingVisit_seller0 M hρ0 hρ1 hρa he0 heq (le_trans M.ha0 hv.1.le) (le_trans hv.2.le hρ1.le) hρβ hβ1]
        simp [hv.2.le]
      rw [hall, hsurp]; ring
    have h_ρv1 : ∀ v ∈ Ioo ρ v₁, fn v = (ρ * barx) * M.f v := by
      intro v hv; dsimp [fn]; unfold payment
      have hall : alloc M mech (effDist M θ (seller0 M)) v = barx := by
        unfold alloc mech askingMech; dsimp
        simp only [not_lt.mpr hv.1.le, hv.1, lt_trans hv.2 hv1β, and_self, decide_true,
          List.find?_cons_of_pos, ↓reduceIte]
        rw [hF0_ρ, hF0_β]; exact hbarx.symm
      have hsurp : surplus M mech (effDist M θ (seller0 M)) v = (v - ρ) * barx := by
        rw [surplus_askingVisit_seller0 M hρ0 hρ1 hρa he0 heq (by linarith [hv.1])
          (le_trans hv.2.le (le_trans hv1v2.le hv21.le)) hρβ hβ1]
        have h1 : ¬v ≤ ρ := not_le.mpr hv.1
        have h2 : v ≤ askingBeta M ρ e := le_trans hv.2.le hv1β.le
        simp only [h1, h2, ↓reduceIte]; rfl
      have hθ1 : θ.θ (seller0 M) v = 1 := by
        dsimp [θ]; unfold askingVisit; dsimp
        have h1 : ρ ≤ v ∧ v ≤ askingV1 M ρ e := ⟨hv.1.le, hv.2.le⟩
        simp [h1]
      rw [hall, hsurp, hθ1]; ring
    have h_v1v2 : ∀ v ∈ Ioo v₁ v₂, fn v = 0 := by
      intro v hv; dsimp [fn]
      have hθ0 : θ.θ (seller0 M) v = 0 := by
        dsimp [θ]; unfold askingVisit; dsimp
        have h1 : ¬(ρ ≤ v ∧ v ≤ askingV1 M ρ e) := fun h => by linarith [h.2, hv.1]
        have h2 : askingV1 M ρ e < v ∧ v < askingV2 M ρ e := hv
        simp [h1, h2]
      rw [hθ0]; ring
    have h_v21 : ∀ v ∈ Ioo v₂ 1, fn v = g_top v - s_dev_v2 * ((1 / (M.m : ℝ)) * M.f v) := by
      intro v hv; dsimp [fn, g_top]; unfold payment
      have hv_gt_ρ : ρ < v := lt_of_le_of_lt hρv2 hv.1
      have hall : alloc M mech (effDist M θ (seller0 M)) v = M.A v ^ (M.n - 1) := by
        unfold alloc mech askingMech; dsimp
        have hnot : ¬(ρ < v ∧ v < β) := fun h => by linarith [h.2, hv.1, hβv2]
        simp only [not_lt.mpr hv_gt_ρ.le, hnot, decide_false,
          List.find?_cons_of_neg, List.find?_nil, Bool.false_eq_true, not_false_eq_true, ↓reduceIte]
        rw [effDist_askingVisit_seller0 M hρa hρ1 he0 heq hv_gt_ρ.le hv.2.le]
        have h1 : ¬v ≤ askingV1 M ρ e := not_le.mpr (lt_trans hv1v2 hv.1)
        have h2 : ¬v ≤ askingV2 M ρ e := not_le.mpr hv.1
        simp only [h1, h2, ↓reduceIte]
      have hsurp : surplus M mech (effDist M θ (seller0 M)) v =
          s_dev_v2 + ∫ u in v₂..v, M.A u ^ (M.n - 1) := by
        rw [surplus_askingVisit_seller0 M hρ0 hρ1 hρa he0 heq (le_trans hρ0.le hv_gt_ρ.le) hv.2.le hρβ hβ1]
        have h1 : ¬v ≤ ρ := not_le.mpr hv_gt_ρ
        have h2 : ¬v ≤ askingBeta M ρ e := not_le.mpr (lt_trans hβv2 hv.1)
        have h3 : ¬v ≤ askingV2 M ρ e := not_le.mpr hv.1
        simp only [h1, h2, h3, ↓reduceIte]
        dsimp [s_dev_v2]; linarith [hbal]
      have hθm : θ.θ (seller0 M) v = 1 / (M.m : ℝ) := by
        dsimp [θ]; unfold askingVisit; dsimp
        have h1 : ¬(ρ ≤ v ∧ v ≤ askingV1 M ρ e) := fun h => by linarith [h.2, hv.1, hv1v2]
        have h2 : ¬(askingV1 M ρ e < v ∧ v < askingV2 M ρ e) := fun h => by linarith [h.2, hv.1]
        simp [h1, h2]
      rw [hall, hsurp, hθm]; ring
    have hi_aρ : IntervalIntegrable fn volume M.a ρ :=
      (intervalIntegrable_congr_Ioo hρa h_aρ).mpr intervalIntegrable_const
    have hi_ρv1 : IntervalIntegrable fn volume ρ v₁ :=
      (intervalIntegrable_congr_Ioo hρv1.le h_ρv1).mpr
        (((M.hf_cont.mono (by rw [uIcc_of_le hρv1.le]; exact Icc_subset_Icc hρa (le_trans hv1v2.le hv21.le))).intervalIntegrable).const_mul _)
    have hi_v1v2 : IntervalIntegrable fn volume v₁ v₂ :=
      (intervalIntegrable_congr_Ioo hv1v2.le h_v1v2).mpr intervalIntegrable_const
    have hi_v21 : IntervalIntegrable fn volume v₂ 1 :=
      (intervalIntegrable_congr_Ioo hv21.le h_v21).mpr (hg_top_int.sub (hf_top_int.const_mul _))
    change ∫ v in M.a..1, fn v = _
    rw [← intervalIntegral.integral_add_adjacent_intervals hi_aρ ((hi_ρv1.trans hi_v1v2).trans hi_v21),
      ← intervalIntegral.integral_add_adjacent_intervals hi_ρv1 (hi_v1v2.trans hi_v21),
      ← intervalIntegral.integral_add_adjacent_intervals hi_v1v2 hi_v21]
    rw [intervalIntegral_congr_Ioo hρa h_aρ, intervalIntegral.integral_zero, zero_add]
    rw [intervalIntegral_congr_Ioo hv1v2.le h_v1v2, intervalIntegral.integral_zero, zero_add]
    rw [intervalIntegral_congr_Ioo hρv1.le h_ρv1, intervalIntegral.integral_const_mul,
      ← M.F_sub_eq_integral hρa hρv1.le (le_trans hv1v2.le hv21.le), hFv1]
    rw [intervalIntegral_congr_Ioo hv21.le h_v21, intervalIntegral.integral_sub hg_top_int (hf_top_int.const_mul _),
      intervalIntegral.integral_const_mul, hI_f_top]
    ring
  have hR_unif : sellerRev M (SPA ρ hρ0.le hρ1.le) (unifVisit M) (seller0 M) =
      (M.n : ℝ) * ((∫ v in ρ..v₂, (v * M.A v ^ (M.n - 1) - s_unif v) * (M.f v / (M.m : ℝ))) +
        (∫ v in v₂..1, g_top v) - s_unif v₂ * q₁) := by
    unfold sellerRev
    congr 1
    let fn : ℝ → ℝ := fun v => payment M (SPA ρ hρ0.le hρ1.le) (effDist M (unifVisit M) (seller0 M)) v *
      (unifVisit M).θ (seller0 M) v * M.f v
    have h_aρ : ∀ v ∈ Ioo M.a ρ, fn v = 0 := by
      intro v hv; dsimp [fn]; unfold payment
      rw [alloc_SPA_unif M hρ0.le hρ1.le hρa (seller0 M) (le_trans hv.2.le hρ1.le),
        surplus_SPA_unif M hρ0.le hρ1.le hρa (seller0 M) (le_trans M.ha0 hv.1.le) (le_trans hv.2.le hρ1.le)]
      simp [hv.2, hv.2.le]
    have h_ρv2 : ∀ v ∈ Ioo ρ v₂, fn v = (v * M.A v ^ (M.n - 1) - s_unif v) * (M.f v / (M.m : ℝ)) := by
      intro v hv; dsimp [fn]; unfold payment
      rw [alloc_SPA_unif M hρ0.le hρ1.le hρa (seller0 M) (le_trans hv.2.le hv21.le),
        surplus_SPA_unif M hρ0.le hρ1.le hρa (seller0 M) (by linarith [hv.1]) (le_trans hv.2.le hv21.le)]
      simp only [not_lt.mpr hv.1.le, not_le.mpr hv.1, ↓reduceIte]
      dsimp [unifVisit, s_unif]; ring
    have h_v21 : ∀ v ∈ Ioo v₂ 1, fn v = g_top v - s_unif v₂ * ((1 / (M.m : ℝ)) * M.f v) := by
      intro v hv; dsimp [fn, g_top]; unfold payment
      have hv_gt_ρ : ρ < v := lt_of_le_of_lt hρv2 hv.1
      rw [alloc_SPA_unif M hρ0.le hρ1.le hρa (seller0 M) hv.2.le,
        surplus_SPA_unif M hρ0.le hρ1.le hρa (seller0 M) (le_trans hρ0.le hv_gt_ρ.le) hv.2.le]
      simp only [not_lt.mpr hv_gt_ρ.le, not_le.mpr hv_gt_ρ, ↓reduceIte]
      have hsplit : ∫ u in ρ..v, M.A u ^ (M.n - 1) = s_unif v₂ + ∫ u in v₂..v, M.A u ^ (M.n - 1) := by
        dsimp [s_unif]
        exact (intervalIntegral.integral_add_adjacent_intervals
          ((hcontA.mono (by rw [uIcc_of_le hρv2]; exact Icc_subset_Icc hρa hv21.le)).intervalIntegrable)
          ((hcontA.mono (by rw [uIcc_of_le hv.1.le]; exact Icc_subset_Icc (le_trans hρa hρv2) hv.2.le)).intervalIntegrable)).symm
      rw [hsplit]; dsimp [unifVisit]; ring
    have hi_aρ : IntervalIntegrable fn volume M.a ρ :=
      (intervalIntegrable_congr_Ioo hρa h_aρ).mpr intervalIntegrable_const
    have hcont_mid : ContinuousOn (fun v => (v * M.A v ^ (M.n - 1) - s_unif v) * (M.f v / (M.m : ℝ))) (Icc ρ v₂) :=
      ((continuousOn_id.mul (hcontA.mono (Icc_subset_Icc hρa hv21.le))).sub
        (hcont_s_unif.mono (Icc_subset_Icc le_rfl hv21.le))).mul
        ((M.hf_cont.mono (Icc_subset_Icc hρa hv21.le)).div_const _)
    have hi_ρv2 : IntervalIntegrable fn volume ρ v₂ :=
      (intervalIntegrable_congr_Ioo hρv2 h_ρv2).mpr (hcont_mid.mono (by rw [uIcc_of_le hρv2])).intervalIntegrable
    have hi_v21 : IntervalIntegrable fn volume v₂ 1 :=
      (intervalIntegrable_congr_Ioo hv21.le h_v21).mpr (hg_top_int.sub (hf_top_int.const_mul _))
    change ∫ v in M.a..1, fn v = _
    rw [← intervalIntegral.integral_add_adjacent_intervals hi_aρ (hi_ρv2.trans hi_v21),
      ← intervalIntegral.integral_add_adjacent_intervals hi_ρv2 hi_v21]
    rw [intervalIntegral_congr_Ioo hρa h_aρ, intervalIntegral.integral_zero, zero_add]
    rw [intervalIntegral_congr_Ioo hρv2 h_ρv2]
    rw [intervalIntegral_congr_Ioo hv21.le h_v21, intervalIntegral.integral_sub hg_top_int (hf_top_int.const_mul _),
      intervalIntegral.integral_const_mul, hI_f_top]
    ring
  have hIBP_A : s_unif v₂ * q₁ + ∫ v in ρ..v₂, s_unif v * (M.f v / (M.m : ℝ)) =
      ∫ v in ρ..v₂, (1 - M.A v) * M.A v ^ (M.n - 1) := by
    have hs_deriv : ∀ v ∈ Ioo ρ v₂, HasDerivAt s_unif (M.A v ^ (M.n - 1)) v :=
      fun v hv => integral_hasDerivAt_right_of_continuousOn (hcontA.mono (Icc_subset_Icc hρa hv21.le)) hv
    have h1A_deriv : ∀ v ∈ Ioo ρ v₂, HasDerivAt (fun v => 1 - M.A v) (-(M.f v / (M.m : ℝ))) v := by
      intro v hv
      have := (hasDerivAt_const v (1 : ℝ)).sub (M.A_deriv_open ⟨lt_of_le_of_lt hρa hv.1, lt_trans hv.2 hv21⟩)
      convert this using 1; ring
    have h1A_cont : ContinuousOn (fun v => 1 - M.A v) (Icc ρ v₂) :=
      continuousOn_const.sub (M.A_continuousOn.mono (Icc_subset_Icc hρa hv21.le))
    have hibp := ibp_of_hasDerivAt_of_le hρv2 h1A_cont
      (hcont_s_unif.mono (Icc_subset_Icc le_rfl hv21.le))
      h1A_deriv hs_deriv
      ((((M.hf_cont.mono (Icc_subset_Icc hρa hv21.le)).div_const _).neg.mul
        (hcont_s_unif.mono (Icc_subset_Icc le_rfl hv21.le))).mono (by rw [uIcc_of_le hρv2])).intervalIntegrable
      ((h1A_cont.mul (hcontA.mono (Icc_subset_Icc hρa hv21.le))).mono (by rw [uIcc_of_le hρv2])).intervalIntegrable
    have hs_ρ : s_unif ρ = 0 := intervalIntegral.integral_same
    have h1A_v2 : 1 - M.A v₂ = q₁ := by linarith [hAv2]
    have hneg_int : ∫ x in ρ..v₂, -(M.f x / (M.m : ℝ)) * s_unif x =
        -(∫ x in ρ..v₂, s_unif x * (M.f x / (M.m : ℝ))) := by
      have heq : (fun x => -(M.f x / (M.m : ℝ)) * s_unif x) = fun x => -(s_unif x * (M.f x / (M.m : ℝ))) := by
        ext x; ring
      rw [heq, intervalIntegral.integral_neg]
    rw [hs_ρ, h1A_v2, mul_zero, sub_zero, hneg_int] at hibp
    linarith
  have hIBP_B : (∫ v in ρ..v₂, (1 - M.A v) * M.A v ^ (M.n - 1)) -
      (∫ v in ρ..v₂, v * M.A v ^ (M.n - 1) * (M.f v / (M.m : ℝ))) =
      v₂ * q₁ * (1 - q₁) ^ (M.n - 1) - ρ * qRho M ρ * (1 - qRho M ρ) ^ (M.n - 1) -
      ((M.n : ℝ) - 1) * ∫ v in ρ..v₂, v * (1 - M.A v) * M.A v ^ (M.n - 2) * (M.f v / (M.m : ℝ)) := by
    let u : ℝ → ℝ := fun v => v * (1 - M.A v)
    let w : ℝ → ℝ := fun v => M.A v ^ (M.n - 1)
    have hu_deriv : ∀ v ∈ Ioo ρ v₂, HasDerivAt u ((1 - M.A v) - v * (M.f v / (M.m : ℝ))) v := by
      intro v hv
      have h1 := (hasDerivAt_id v).mul ((hasDerivAt_const v (1 : ℝ)).sub
        (M.A_deriv_open ⟨lt_of_le_of_lt hρa hv.1, lt_trans hv.2 hv21⟩))
      convert h1 using 1
      · ext x; simp [u]
      · simp only [Pi.sub_apply, id_eq]; ring
    have hw_deriv : ∀ v ∈ Ioo ρ v₂, HasDerivAt w (((M.n : ℝ) - 1) * M.A v ^ (M.n - 2) * (M.f v / (M.m : ℝ))) v := by
      intro v hv
      have h1 := (M.A_deriv_open ⟨lt_of_le_of_lt hρa hv.1, lt_trans hv.2 hv21⟩).pow (M.n - 1)
      have hcast : ((M.n - 1 : ℕ) : ℝ) = (M.n : ℝ) - 1 := by
        rw [Nat.cast_sub (by have := M.hn; omega), Nat.cast_one]
      rw [hcast, show M.n - 1 - 1 = M.n - 2 by omega] at h1
      exact h1
    have hA_sub := M.A_continuousOn.mono (Icc_subset_Icc hρa hv21.le)
    have hf_sub := M.hf_cont.mono (Icc_subset_Icc hρa hv21.le)
    have hi1 : IntervalIntegrable (fun v => (1 - M.A v) * M.A v ^ (M.n - 1)) volume ρ v₂ :=
      (((continuousOn_const.sub hA_sub).mul (hA_sub.pow _)).mono (by rw [uIcc_of_le hρv2])).intervalIntegrable
    have hi2 : IntervalIntegrable (fun v => v * M.A v ^ (M.n - 1) * (M.f v / (M.m : ℝ))) volume ρ v₂ :=
      (((continuousOn_id.mul (hA_sub.pow _)).mul (hf_sub.div_const _)).mono (by rw [uIcc_of_le hρv2])).intervalIntegrable
    have hi3 : IntervalIntegrable (fun v => v * (1 - M.A v) * M.A v ^ (M.n - 2) * (M.f v / (M.m : ℝ))) volume ρ v₂ :=
      ((((continuousOn_id.mul (continuousOn_const.sub hA_sub)).mul (hA_sub.pow _)).mul (hf_sub.div_const _)).mono
        (by rw [uIcc_of_le hρv2])).intervalIntegrable
    have heq1 : (fun x => ((1 - M.A x) - x * (M.f x / (M.m : ℝ))) * w x) =
        fun x => (1 - M.A x) * M.A x ^ (M.n - 1) - x * M.A x ^ (M.n - 1) * (M.f x / (M.m : ℝ)) := by
      ext x; dsimp [w]; ring
    have heq2 : (fun x => u x * (((M.n : ℝ) - 1) * M.A x ^ (M.n - 2) * (M.f x / (M.m : ℝ)))) =
        fun x => ((M.n : ℝ) - 1) * (x * (1 - M.A x) * M.A x ^ (M.n - 2) * (M.f x / (M.m : ℝ))) := by
      ext x; dsimp [u]; ring
    have hu_cont : ContinuousOn u (Icc ρ v₂) := continuousOn_id.mul (continuousOn_const.sub hA_sub)
    have hw_cont : ContinuousOn w (Icc ρ v₂) := hA_sub.pow (M.n - 1)
    have hibp := ibp_of_hasDerivAt_of_le hρv2 hu_cont hw_cont
      hu_deriv hw_deriv (by rw [heq1]; exact hi1.sub hi2) (by rw [heq2]; exact hi3.const_mul _)
    rw [heq1, intervalIntegral.integral_sub hi1 hi2, heq2, intervalIntegral.integral_const_mul] at hibp
    dsimp [u, w] at hibp
    have h1A_v2 : 1 - M.A v₂ = q₁ := by linarith [hAv2]
    have h1A_ρ : 1 - M.A ρ = qRho M ρ := by unfold Market.A qRho; ring
    have hA_ρ : M.A ρ = 1 - qRho M ρ := rfl
    rw [h1A_v2, hAv2, h1A_ρ, hA_ρ] at hibp
    linarith
  have hIBP_C : s_dev_v2 = v₂ * (1 - q₁) ^ (M.n - 1) - ρ * (1 - q₀) ^ (M.n - 1) -
      ((M.n : ℝ) - 1) * ∫ v in v₁..v₂, v * askingFriv M ρ e v ^ (M.n - 2) * (M.f v / ((M.m : ℝ) - 1)) := by
    have hF_sub := M.F_continuousOn.mono (Icc_subset_Icc (le_trans hρa hρv1.le) hv21.le)
    have hf_sub := M.hf_cont.mono (Icc_subset_Icc (le_trans hρa hρv1.le) hv21.le)
    have hFriv_cont : ContinuousOn (askingFriv M ρ e) (Icc v₁ v₂) := by unfold askingFriv; fun_prop
    have hFriv_deriv : ∀ v ∈ Ioo v₁ v₂, HasDerivAt (fun v => askingFriv M ρ e v ^ (M.n - 1))
        (((M.n : ℝ) - 1) * askingFriv M ρ e v ^ (M.n - 2) * (M.f v / ((M.m : ℝ) - 1))) v := by
      intro v hv
      have h1 : HasDerivAt (askingFriv M ρ e) (M.f v / ((M.m : ℝ) - 1)) v := by
        unfold askingFriv
        have h := ((hasDerivAt_const v (M.F v₂)).sub
          (M.hF_deriv_open v ⟨lt_of_le_of_lt hρa (lt_trans hρv1 hv.1), lt_trans hv.2 hv21⟩)).div_const ((M.m : ℝ) - 1)
        convert (hasDerivAt_const v (1 - q₁)).sub h using 1; ring
      have h2 := h1.pow (M.n - 1)
      have hcast : ((M.n - 1 : ℕ) : ℝ) = (M.n : ℝ) - 1 := by
        rw [Nat.cast_sub (by have := M.hn; omega), Nat.cast_one]
      rw [hcast, show M.n - 1 - 1 = M.n - 2 by omega] at h2
      exact h2
    have hi1 : IntervalIntegrable (fun v => askingFriv M ρ e v ^ (M.n - 1)) volume v₁ v₂ :=
      ((hFriv_cont.pow _).mono (by rw [uIcc_of_le hv1v2.le])).intervalIntegrable
    have hi2 : IntervalIntegrable (fun v => v * askingFriv M ρ e v ^ (M.n - 2) * (M.f v / ((M.m : ℝ) - 1))) volume v₁ v₂ :=
      (((continuousOn_id.mul (hFriv_cont.pow _)).mul (hf_sub.div_const _)).mono (by rw [uIcc_of_le hv1v2.le])).intervalIntegrable
    have heq2 : (fun x => id x * (((M.n : ℝ) - 1) * askingFriv M ρ e x ^ (M.n - 2) * (M.f x / ((M.m : ℝ) - 1)))) =
        fun x => ((M.n : ℝ) - 1) * (x * askingFriv M ρ e x ^ (M.n - 2) * (M.f x / ((M.m : ℝ) - 1))) := by ext x; dsimp; ring
    have hFp_cont : ContinuousOn (fun v => askingFriv M ρ e v ^ (M.n - 1)) (Icc v₁ v₂) := hFriv_cont.pow _
    have hibp := ibp_of_hasDerivAt_of_le hv1v2.le continuousOn_id hFp_cont
      (fun v _ => hasDerivAt_id v) hFriv_deriv (by simpa using hi1) (by rw [heq2]; exact hi2.const_mul _)
    rw [heq2, intervalIntegral.integral_const_mul] at hibp
    simp only [one_mul, id_eq] at hibp
    rw [hFriv2, hFriv1] at hibp
    dsimp [s_dev_v2, barx]; unfold askingBarX; linarith
  have hsplit_unif : ∫ v in ρ..v₂, (v * M.A v ^ (M.n - 1) - s_unif v) * (M.f v / (M.m : ℝ)) =
      (∫ v in ρ..v₂, v * M.A v ^ (M.n - 1) * (M.f v / (M.m : ℝ))) -
      (∫ v in ρ..v₂, s_unif v * (M.f v / (M.m : ℝ))) := by
    have hA_sub := M.A_continuousOn.mono (Icc_subset_Icc hρa hv21.le)
    have hf_sub := M.hf_cont.mono (Icc_subset_Icc hρa hv21.le)
    have hs_sub := hcont_s_unif.mono (Icc_subset_Icc le_rfl hv21.le)
    have h1 : IntervalIntegrable (fun v => v * M.A v ^ (M.n - 1) * (M.f v / (M.m : ℝ))) volume ρ v₂ :=
      (((continuousOn_id.mul (hA_sub.pow _)).mul (hf_sub.div_const _)).mono (by rw [uIcc_of_le hρv2])).intervalIntegrable
    have h2 : IntervalIntegrable (fun v => s_unif v * (M.f v / (M.m : ℝ))) volume ρ v₂ :=
      ((hs_sub.mul (hf_sub.div_const _)).mono (by rw [uIcc_of_le hρv2])).intervalIntegrable
    have heq : (fun v => (v * M.A v ^ (M.n - 1) - s_unif v) * (M.f v / (M.m : ℝ))) =
        fun v => v * M.A v ^ (M.n - 1) * (M.f v / (M.m : ℝ)) - s_unif v * (M.f v / (M.m : ℝ)) := by ext v; ring
    rw [heq, intervalIntegral.integral_sub h1 h2]
  rw [hR_dev, hR_unif, hsplit_unif]
  have ht0_eq : q₁ + e = t₀ := rfl
  have hbarx_eq : barx = (1 - q₀) ^ (M.n - 1) := rfl
  rw [hbarx_eq]
  linear_combination (M.n : ℝ) * hIBP_A + (M.n : ℝ) * hIBP_B - (M.n : ℝ) * q₁ * hIBP_C +
    (M.n : ℝ) * ρ * (1 - q₀) ^ (M.n - 1) * ht0_eq

/-! #### Modular Sub-Lemmas for `askingRevGain_O_e2` -/

lemma askingRevGain_piece1 (M : Market) {ρ : ℝ} (hρa : M.a ≤ ρ) (hρ1 : ρ < 1) :
    ∃ K ≥ 0, ∀ e ∈ Ioo (0 : ℝ) (qRho M ρ),
      |askingT0 M ρ e * (1 - askingQ0 M ρ e) ^ (M.n - 1) - qRho M ρ * (1 - qRho M ρ) ^ (M.n - 1) -
        (((M.m : ℝ) - 1) / (2 * (M.m : ℝ)) * (1 - qRho M ρ) ^ (M.n - 1) +
          ((M.n : ℝ) - 1) / (2 * (M.m : ℝ)) * qRho M ρ * (1 - qRho M ρ) ^ (M.n - 2)) * e| ≤ K * e ^ 2 := by
  set q_ρ := qRho M ρ
  set A := 1 - q_ρ
  have hqhalf := qRho_le_half M hρa hρ1.le
  have hApos : 0 < A := by linarith
  have hm := M.m_pos_real
  have hm1 := M.m_sub_one_pos_real
  have hn1 := M.n_sub_one_pos_real
  obtain ⟨Cy, hCy, hy_asym⟩ := askingY_asymptotic M hρa hρ1
  obtain ⟨Cp1, hCp1, hpow1⟩ := pow_first_order_bound (M.n - 1) A
  refine ⟨Cy + Cp1 + ((M.n : ℝ) - 1) * (Cy / ((M.m : ℝ) - 1) + 1), by positivity, fun e he => ?_⟩
  have hc := asking_coords M hρa hρ1 he.1 he.2
  have hys := askingY_spec M hρa hρ1 he.1 he.2
  set y := askingY M ρ e
  set q₀ := askingQ0 M ρ e
  set t₀ := askingT0 M ρ e
  have hy0 : 0 < y := lt_trans (div_pos he.1 hm) hys.1.1
  have he1 : e ≤ 1 := by linarith [he.2, hqhalf]
  have hy_err := hy_asym e he
  have ht0_err : |t₀ - q_ρ - ((M.m : ℝ) - 1) / (2 * (M.m : ℝ)) * e| ≤ Cy * e ^ 2 := by
    have : t₀ - q_ρ - ((M.m : ℝ) - 1) / (2 * (M.m : ℝ)) * e =
        -(y - ((M.m : ℝ) + 1) / (2 * (M.m : ℝ)) * e) := by
      dsimp [t₀, q_ρ]; unfold askingT0 askingQ1; field_simp [hm.ne']; ring
    rw [this, abs_neg]; exact hy_err
  let δ₀ := q_ρ - q₀
  have hrq : |δ₀ - e / (2 * (M.m : ℝ))| ≤ (Cy / ((M.m : ℝ) - 1)) * e ^ 2 := by
    have : δ₀ - e / (2 * (M.m : ℝ)) = -(y - ((M.m : ℝ) + 1) / (2 * (M.m : ℝ)) * e) / ((M.m : ℝ) - 1) := by
      dsimp [δ₀, q₀, q_ρ]; unfold askingQ0; field_simp [hm.ne', hm1.ne']; ring
    rw [this, abs_div, abs_neg, abs_of_pos hm1, div_mul_eq_mul_div Cy]
    exact div_le_div_of_nonneg_right hy_err hm1.le
  have hδ₀_le : |δ₀| ≤ e := by
    rw [abs_of_pos (by linarith [hc.2.2.1])]
    dsimp [δ₀, q₀, q_ρ]; unfold askingQ0
    have hm2 : (2 : ℝ) ≤ M.m := by exact_mod_cast M.hm
    have h1 : (e - y) / ((M.m : ℝ) - 1) ≤ e := by
      calc (e - y) / ((M.m : ℝ) - 1) ≤ e / ((M.m : ℝ) - 1) := div_le_div_of_nonneg_right (by linarith) hm1.le
        _ ≤ e := div_le_self he.1.le (by linarith)
    have h2 : qRho M ρ - (qRho M ρ + (y - e) / ((M.m : ℝ) - 1)) = (e - y) / ((M.m : ℝ) - 1) := by ring
    linarith
  have hp := hpow1 δ₀ (le_trans hδ₀_le he1)
  have hAδ : A + δ₀ = 1 - q₀ := by dsimp [A, δ₀]; ring
  have hcast : ((M.n - 1 : ℕ) : ℝ) = (M.n : ℝ) - 1 := by
    rw [Nat.cast_sub (by have := M.hn; omega), Nat.cast_one]
  rw [hAδ, hcast, show M.n - 1 - 1 = M.n - 2 by omega] at hp
  set r_p := (1 - q₀) ^ (M.n - 1) - A ^ (M.n - 1) - ((M.n : ℝ) - 1) * A ^ (M.n - 2) * δ₀
  set r_t := t₀ - q_ρ - ((M.m : ℝ) - 1) / (2 * (M.m : ℝ)) * e
  set r_q := δ₀ - e / (2 * (M.m : ℝ))
  have hrp : |r_p| ≤ Cp1 * e ^ 2 := by
    have hsq : δ₀ ^ 2 ≤ e ^ 2 := by rw [← sq_abs]; gcongr
    exact le_trans hp (mul_le_mul_of_nonneg_left hsq hCp1)
  have hid : t₀ * (1 - q₀) ^ (M.n - 1) - q_ρ * A ^ (M.n - 1) -
      (((M.m : ℝ) - 1) / (2 * (M.m : ℝ)) * A ^ (M.n - 1) +
        ((M.n : ℝ) - 1) / (2 * (M.m : ℝ)) * q_ρ * A ^ (M.n - 2)) * e =
      r_t * A ^ (M.n - 1) + t₀ * r_p +
      ((M.n : ℝ) - 1) * A ^ (M.n - 2) * q_ρ * r_q +
      ((M.n : ℝ) - 1) * A ^ (M.n - 2) * (t₀ - q_ρ) * δ₀ := by
    have h1 : (1 - q₀) ^ (M.n - 1) = A ^ (M.n - 1) + ((M.n : ℝ) - 1) * A ^ (M.n - 2) * δ₀ + r_p := by dsimp [r_p]; ring
    rw [h1]; dsimp [r_t, r_q]; ring
  rw [hid]
  have hA_le1 : A ≤ 1 := by dsimp [A]; linarith [qRho_pos M hρa hρ1]
  have hAp1 : A ^ (M.n - 1) ≤ 1 := pow_le_one₀ hApos.le hA_le1
  have hAp2 : A ^ (M.n - 2) ≤ 1 := pow_le_one₀ hApos.le hA_le1
  have ht0_q : |t₀ - q_ρ| ≤ e := by
    rw [abs_of_pos (by linarith [hc.2.2.2.1])]; dsimp [t₀, q_ρ]; unfold askingT0 askingQ1; linarith
  have hb1 : |r_t * A ^ (M.n - 1)| ≤ Cy * e ^ 2 := by
    rw [abs_mul, abs_of_pos (pow_pos hApos _)]
    calc |r_t| * A ^ (M.n - 1) ≤ (Cy * e ^ 2) * 1 := by gcongr
      _ = Cy * e ^ 2 := mul_one _
  have hb2 : |t₀ * r_p| ≤ Cp1 * e ^ 2 := by
    rw [abs_mul, abs_of_pos (by linarith [qRho_pos M hρa hρ1, hc.2.2.2.1])]
    calc t₀ * |r_p| ≤ 1 * (Cp1 * e ^ 2) := by gcongr; exact hc.2.2.2.2.1.le
      _ = Cp1 * e ^ 2 := one_mul _
  have hb3 : |((M.n : ℝ) - 1) * A ^ (M.n - 2) * q_ρ * r_q| ≤
      ((M.n : ℝ) - 1) * (Cy / ((M.m : ℝ) - 1)) * e ^ 2 := by
    have hqρ0 : 0 ≤ q_ρ := (qRho_pos M hρa hρ1).le
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos hn1, abs_of_pos (pow_pos hApos _), abs_of_nonneg hqρ0]
    calc ((M.n : ℝ) - 1) * A ^ (M.n - 2) * q_ρ * |r_q|
        ≤ ((M.n : ℝ) - 1) * 1 * 1 * ((Cy / ((M.m : ℝ) - 1)) * e ^ 2) := by gcongr; linarith
      _ = ((M.n : ℝ) - 1) * (Cy / ((M.m : ℝ) - 1)) * e ^ 2 := by ring
  have hb4 : |((M.n : ℝ) - 1) * A ^ (M.n - 2) * (t₀ - q_ρ) * δ₀| ≤ ((M.n : ℝ) - 1) * e ^ 2 := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos hn1, abs_of_pos (pow_pos hApos _)]
    have h1 : ((M.n : ℝ) - 1) * A ^ (M.n - 2) * |t₀ - q_ρ| * |δ₀| ≤ ((M.n : ℝ) - 1) * 1 * e * e := by
      gcongr; exact mul_nonneg (mul_nonneg hn1.le zero_le_one) he.1.le
    linarith [show ((M.n : ℝ) - 1) * 1 * e * e = ((M.n : ℝ) - 1) * e ^ 2 by ring]
  have ht1 := abs_add_le (r_t * A ^ (M.n - 1) + t₀ * r_p + ((M.n : ℝ) - 1) * A ^ (M.n - 2) * q_ρ * r_q)
    (((M.n : ℝ) - 1) * A ^ (M.n - 2) * (t₀ - q_ρ) * δ₀)
  have ht2 := abs_add_le (r_t * A ^ (M.n - 1) + t₀ * r_p) (((M.n : ℝ) - 1) * A ^ (M.n - 2) * q_ρ * r_q)
  have ht3 := abs_add_le (r_t * A ^ (M.n - 1)) (t₀ * r_p)
  linarith only [ht1, ht2, ht3, hb1, hb2, hb3, hb4]

lemma askingRevGain_piece2 (M : Market) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hρa : M.a ≤ ρ) :
    ∃ K ≥ 0, ∀ e ∈ Ioo (0 : ℝ) (qRho M ρ),
      |askingQ1 M ρ e * (∫ v in askingV1 M ρ e..askingV2 M ρ e,
          v * askingFriv M ρ e v ^ (M.n - 2) * (M.f v / ((M.m : ℝ) - 1))) -
        qRho M ρ * ρ * (1 - qRho M ρ) ^ (M.n - 2) * (askingQ0 M ρ e - askingQ1 M ρ e)| ≤ K * e ^ 2 := by
  set q_ρ := qRho M ρ
  set A := 1 - q_ρ
  have hqhalf := qRho_le_half M hρa hρ1.le
  have hApos : 0 < A := by linarith
  have hm := M.m_pos_real
  have hm1 := M.m_sub_one_pos_real
  have hn2 : (0 : ℝ) ≤ (M.n : ℝ) - 2 := by
    have hnR : (2 : ℝ) ≤ (M.n : ℝ) := by exact_mod_cast M.hn
    linarith
  obtain ⟨Cp2, hCp2, hpow2⟩ := pow_first_order_bound (M.n - 2) A
  obtain ⟨fmin, hfmin, hf_lo⟩ := M.exists_f_min
  obtain ⟨fmax, _, hf_hi⟩ := M.exists_f_max
  let M_lip := (M.m : ℝ) / fmin + ((M.n : ℝ) - 2) + Cp2 + 2
  refine ⟨M_lip * ((M.m : ℝ) / ((M.m : ℝ) - 1) + 1), by positivity, fun e he => ?_⟩
  have hc := asking_coords M hρa hρ1 he.1 he.2
  rcases hc with ⟨hq1_pos, hq1_lt_q0, hq0_lt_qr, _, _, hρv1, hv1v2, hv21, hFv1, hFv2, _, hFriv1, hFriv2, _, _, _⟩
  have hys := askingY_spec M hρa hρ1 he.1 he.2
  set y := askingY M ρ e
  set q₁ := askingQ1 M ρ e
  set q₀ := askingQ0 M ρ e
  set v₁ := askingV1 M ρ e
  set v₂ := askingV2 M ρ e
  have hy0 : 0 < y := lt_trans (div_pos he.1 hm) hys.1.1
  have hye : y < e := hys.1.2
  have he1 : e ≤ 1 := by linarith [he.2, hqhalf]
  have hv2_ρ_b : v₂ - ρ ≤ ((M.m : ℝ) / fmin) * e := by
    have hlip := (M.F_lipschitz_bounds ⟨hρa, hρ1.le⟩ ⟨le_trans hρa (by linarith), hv21.le⟩
      (by linarith) hf_lo hf_hi).1
    rw [hFv2] at hlip
    rw [div_mul_eq_mul_div, le_div_iff₀ hfmin]; nlinarith
  have hmass : ∫ v in v₁..v₂, M.f v / ((M.m : ℝ) - 1) = q₀ - q₁ := by
    rw [intervalIntegral.integral_div, ← M.F_sub_eq_integral (le_trans hρa hρv1.le) hv1v2.le hv21.le, hFv2, hFv1]
    dsimp [q₀, q₁]; unfold askingQ0 askingQ1; field_simp [hm1.ne']; ring
  have hpw : ∀ v ∈ Icc v₁ v₂, |q₁ * (v * askingFriv M ρ e v ^ (M.n - 2)) - q_ρ * ρ * A ^ (M.n - 2)| ≤ M_lip * e := by
    intro v hv
    have hv_mem : v ∈ Icc M.a 1 := ⟨le_trans hρa (le_trans hρv1.le hv.1), le_trans hv.2 hv21.le⟩
    have hFriv_lo : 1 - q₀ ≤ askingFriv M ρ e v := by
      rw [← hFriv1]; unfold askingFriv
      have := div_le_div_of_nonneg_right
        (by linarith [M.F_strictMonoOn.monotoneOn ⟨le_trans hρa hρv1.le, le_trans hv1v2.le hv21.le⟩ hv_mem hv.1] :
          M.F v₂ - M.F v ≤ M.F v₂ - M.F v₁) hm1.le
      linarith
    have hFriv_hi : askingFriv M ρ e v ≤ 1 - q₁ := by
      unfold askingFriv
      have := div_nonneg (by linarith [M.F_strictMonoOn.monotoneOn hv_mem ⟨le_trans hρa (by linarith), hv21.le⟩ hv.2] :
          0 ≤ M.F v₂ - M.F v) hm1.le
      dsimp [q₁]; linarith
    have hF_d : |askingFriv M ρ e v - A| ≤ e := by
      have hq1e : q_ρ - q₁ = y := by dsimp [q₁, q_ρ]; unfold askingQ1; ring
      rw [abs_le]; constructor <;> (dsimp [A]; linarith only [hFriv_lo, hFriv_hi, hq0_lt_qr, hq1e, hye, he.1])
    have hp2 := hpow2 (askingFriv M ρ e v - A) (le_trans hF_d he1)
    have hcast2 : ((M.n - 2 : ℕ) : ℝ) = (M.n : ℝ) - 2 := by rw [Nat.cast_sub M.hn, Nat.cast_ofNat]
    have hA_le1 : A ≤ 1 := by dsimp [A]; linarith [qRho_pos M hρa hρ1]
    have hAp : A ^ (M.n - 2 - 1) ≤ 1 := pow_le_one₀ hApos.le hA_le1
    have hFp_d : |askingFriv M ρ e v ^ (M.n - 2) - A ^ (M.n - 2)| ≤ (((M.n : ℝ) - 2) + Cp2) * e := by
      rw [show A + (askingFriv M ρ e v - A) = askingFriv M ρ e v by ring, hcast2] at hp2
      have htri := abs_add_le (askingFriv M ρ e v ^ (M.n - 2) - A ^ (M.n - 2) -
        ((M.n : ℝ) - 2) * A ^ (M.n - 2 - 1) * (askingFriv M ρ e v - A))
        (((M.n : ℝ) - 2) * A ^ (M.n - 2 - 1) * (askingFriv M ρ e v - A))
      rw [show (askingFriv M ρ e v ^ (M.n - 2) - A ^ (M.n - 2) -
          ((M.n : ℝ) - 2) * A ^ (M.n - 2 - 1) * (askingFriv M ρ e v - A)) +
          ((M.n : ℝ) - 2) * A ^ (M.n - 2 - 1) * (askingFriv M ρ e v - A) =
          askingFriv M ρ e v ^ (M.n - 2) - A ^ (M.n - 2) by ring] at htri
      have hlin : |((M.n : ℝ) - 2) * A ^ (M.n - 2 - 1) * (askingFriv M ρ e v - A)| ≤ ((M.n : ℝ) - 2) * e := by
        rw [abs_mul, abs_mul, abs_of_nonneg hn2, abs_of_pos (pow_pos hApos _)]
        calc ((M.n : ℝ) - 2) * A ^ (M.n - 2 - 1) * |askingFriv M ρ e v - A|
            ≤ ((M.n : ℝ) - 2) * 1 * e := by gcongr
          _ = ((M.n : ℝ) - 2) * e := by ring
      have hsq : (askingFriv M ρ e v - A) ^ 2 ≤ e := by
        rw [← sq_abs]; calc |askingFriv M ρ e v - A| ^ 2 ≤ e ^ 2 := by gcongr
          _ ≤ e * 1 := by nlinarith only [he.1, he1]
          _ = e := mul_one e
      nlinarith only [htri, hp2, hlin, hsq, hCp2]
    have hv_d : |v - ρ| ≤ ((M.m : ℝ) / fmin) * e := by
      rw [abs_of_nonneg (by linarith [hv.1, hρv1])]; linarith [hv.2, hv2_ρ_b]
    have hq1_d : |q₁ - q_ρ| ≤ e := by
      have : q₁ - q_ρ = -y := by dsimp [q₁, q_ρ]; unfold askingQ1; ring
      rw [this, abs_neg, abs_of_pos hy0]; exact hye.le
    have hFriv_nn : 0 ≤ askingFriv M ρ e v := by linarith only [hFriv_lo, hq0_lt_qr, hqhalf]
    have hv_pos : 0 < v := by linarith only [hρ0, hρv1, hv.1]
    have hFriv_le1 : askingFriv M ρ e v ^ (M.n - 2) ≤ 1 :=
      pow_le_one₀ hFriv_nn (by linarith only [hFriv_hi, hq1_pos])
    have hid : q₁ * (v * askingFriv M ρ e v ^ (M.n - 2)) - q_ρ * ρ * A ^ (M.n - 2) =
        (q₁ - q_ρ) * v * askingFriv M ρ e v ^ (M.n - 2) +
        q_ρ * (v - ρ) * askingFriv M ρ e v ^ (M.n - 2) +
        q_ρ * ρ * (askingFriv M ρ e v ^ (M.n - 2) - A ^ (M.n - 2)) := by ring
    rw [hid]
    have hv_le1 : v ≤ 1 := by linarith only [hv.2, hv21]
    have hqρ_le1 : q_ρ ≤ 1 := by linarith only [hqhalf]
    have hb1 : |(q₁ - q_ρ) * v * askingFriv M ρ e v ^ (M.n - 2)| ≤ e := by
      rw [abs_mul, abs_mul, abs_of_pos hv_pos, abs_of_nonneg (pow_nonneg hFriv_nn _)]
      have h1 : |q₁ - q_ρ| * v ≤ e * 1 := mul_le_mul hq1_d hv_le1 hv_pos.le he.1.le
      have h2 := mul_le_mul h1 hFriv_le1 (pow_nonneg hFriv_nn _) (by linarith only [he.1])
      linarith only [h2]
    have hb2 : |q_ρ * (v - ρ) * askingFriv M ρ e v ^ (M.n - 2)| ≤ ((M.m : ℝ) / fmin) * e := by
      rw [abs_mul, abs_mul, abs_of_pos (qRho_pos M hρa hρ1), abs_of_nonneg (pow_nonneg hFriv_nn _)]
      have h1 : q_ρ * |v - ρ| ≤ 1 * (((M.m : ℝ) / fmin) * e) :=
        mul_le_mul hqρ_le1 hv_d (abs_nonneg _) zero_le_one
      have h2 := mul_le_mul h1 hFriv_le1 (pow_nonneg hFriv_nn _)
        (mul_nonneg zero_le_one (mul_nonneg (div_nonneg hm.le hfmin.le) he.1.le))
      linarith only [h2]
    have hb3 : |q_ρ * ρ * (askingFriv M ρ e v ^ (M.n - 2) - A ^ (M.n - 2))| ≤ (((M.n : ℝ) - 2) + Cp2) * e := by
      rw [abs_mul, abs_mul, abs_of_pos (qRho_pos M hρa hρ1), abs_of_pos hρ0]
      calc q_ρ * ρ * |askingFriv M ρ e v ^ (M.n - 2) - A ^ (M.n - 2)|
          ≤ 1 * 1 * ((((M.n : ℝ) - 2) + Cp2) * e) := by gcongr
        _ = (((M.n : ℝ) - 2) + Cp2) * e := by ring
    have ht1 := abs_add_le ((q₁ - q_ρ) * v * askingFriv M ρ e v ^ (M.n - 2) +
      q_ρ * (v - ρ) * askingFriv M ρ e v ^ (M.n - 2)) (q_ρ * ρ * (askingFriv M ρ e v ^ (M.n - 2) - A ^ (M.n - 2)))
    have ht2 := abs_add_le ((q₁ - q_ρ) * v * askingFriv M ρ e v ^ (M.n - 2))
      (q_ρ * (v - ρ) * askingFriv M ρ e v ^ (M.n - 2))
    dsimp [M_lip]; linarith only [ht1, ht2, hb1, hb2, hb3, he.1]
  have hF_sub := M.F_continuousOn.mono (Icc_subset_Icc (le_trans hρa hρv1.le) hv21.le)
  have hf_sub := M.hf_cont.mono (Icc_subset_Icc (le_trans hρa hρv1.le) hv21.le)
  have hFriv_cont : ContinuousOn (askingFriv M ρ e) (Icc v₁ v₂) := by unfold askingFriv; fun_prop
  have hdiff_int : q₁ * (∫ v in v₁..v₂, v * askingFriv M ρ e v ^ (M.n - 2) * (M.f v / ((M.m : ℝ) - 1))) -
      q_ρ * ρ * A ^ (M.n - 2) * (q₀ - q₁) =
      ∫ v in v₁..v₂, (q₁ * (v * askingFriv M ρ e v ^ (M.n - 2)) - q_ρ * ρ * A ^ (M.n - 2)) *
        (M.f v / ((M.m : ℝ) - 1)) := by
    have hi1 : IntervalIntegrable (fun v => q₁ * (v * askingFriv M ρ e v ^ (M.n - 2)) * (M.f v / ((M.m : ℝ) - 1))) volume v₁ v₂ :=
      (((continuousOn_const.mul (continuousOn_id.mul (hFriv_cont.pow _))).mul (hf_sub.div_const _)).mono
        (by rw [uIcc_of_le hv1v2.le])).intervalIntegrable
    have hi2 : IntervalIntegrable (fun v => (q_ρ * ρ * A ^ (M.n - 2)) * (M.f v / ((M.m : ℝ) - 1))) volume v₁ v₂ :=
      ((hf_sub.div_const _).mono (by rw [uIcc_of_le hv1v2.le])).intervalIntegrable.const_mul _
    have heq : (fun v => (q₁ * (v * askingFriv M ρ e v ^ (M.n - 2)) - q_ρ * ρ * A ^ (M.n - 2)) *
        (M.f v / ((M.m : ℝ) - 1))) =
        fun v => q₁ * (v * askingFriv M ρ e v ^ (M.n - 2)) * (M.f v / ((M.m : ℝ) - 1)) -
          (q_ρ * ρ * A ^ (M.n - 2)) * (M.f v / ((M.m : ℝ) - 1)) := by ext v; ring
    rw [heq, intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_const_mul, hmass]
    congr 1; rw [← intervalIntegral.integral_const_mul]; congr 1; ext v; ring
  rw [hdiff_int]
  have hnorm := intervalIntegral.abs_integral_le_integral_abs (μ := volume) hv1v2.le
    (f := fun v => (q₁ * (v * askingFriv M ρ e v ^ (M.n - 2)) - q_ρ * ρ * A ^ (M.n - 2)) * (M.f v / ((M.m : ℝ) - 1)))
  have hi_abs : IntervalIntegrable (fun v => |(q₁ * (v * askingFriv M ρ e v ^ (M.n - 2)) - q_ρ * ρ * A ^ (M.n - 2)) *
      (M.f v / ((M.m : ℝ) - 1))|) volume v₁ v₂ :=
    ((((((continuousOn_const.mul (continuousOn_id.mul (hFriv_cont.pow _))).sub continuousOn_const).mul
      (hf_sub.div_const _)).abs)).mono (by rw [uIcc_of_le hv1v2.le])).intervalIntegrable
  have hi_hi : IntervalIntegrable (fun v => (M_lip * e) * (M.f v / ((M.m : ℝ) - 1))) volume v₁ v₂ :=
    ((hf_sub.div_const _).mono (by rw [uIcc_of_le hv1v2.le])).intervalIntegrable.const_mul _
  have hmono := intervalIntegral.integral_mono_on hv1v2.le hi_abs hi_hi fun v hv => by
    rw [abs_mul, abs_of_pos (div_pos (M.hf_pos v ⟨le_trans hρa (le_trans hρv1.le hv.1), le_trans hv.2 hv21.le⟩) hm1)]
    exact mul_le_mul_of_nonneg_right (hpw v hv)
      (div_nonneg (M.hf_pos v ⟨le_trans hρa (le_trans hρv1.le hv.1), le_trans hv.2 hv21.le⟩).le hm1.le)
  rw [intervalIntegral.integral_const_mul, hmass] at hmono
  have hqdiff_le : q₀ - q₁ ≤ ((M.m : ℝ) / ((M.m : ℝ) - 1) + 1) * e := by
    have h1 : q₀ - q₁ = ((M.m : ℝ) * y - e) / ((M.m : ℝ) - 1) := by
      dsimp [q₀, q₁]; unfold askingQ0 askingQ1; field_simp [hm1.ne']; ring
    have h2 : ((M.m : ℝ) / ((M.m : ℝ) - 1) + 1) * e * ((M.m : ℝ) - 1) = (2 * (M.m : ℝ) - 1) * e := by
      field_simp [hm1.ne']; ring
    rw [h1, div_le_iff₀ hm1, h2]; nlinarith only [hm, hye, he.1]
  have hMlip_e : 0 ≤ M_lip * e := mul_nonneg (by positivity) he.1.le
  calc _ ≤ (M_lip * e) * (q₀ - q₁) := le_trans hnorm hmono
    _ ≤ (M_lip * e) * (((M.m : ℝ) / ((M.m : ℝ) - 1) + 1) * e) := mul_le_mul_of_nonneg_left hqdiff_le hMlip_e
    _ = M_lip * ((M.m : ℝ) / ((M.m : ℝ) - 1) + 1) * e ^ 2 := by ring

lemma askingRevGain_piece3 (M : Market) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hρa : M.a ≤ ρ) :
    ∃ K ≥ 0, ∀ e ∈ Ioo (0 : ℝ) (qRho M ρ),
      |(∫ v in ρ..askingV2 M ρ e, v * (1 - M.A v) * M.A v ^ (M.n - 2) * (M.f v / (M.m : ℝ))) -
        qRho M ρ * ρ * (1 - qRho M ρ) ^ (M.n - 2) * (qRho M ρ - askingQ1 M ρ e)| ≤ K * e ^ 2 := by
  set q_ρ := qRho M ρ
  set A := 1 - q_ρ
  have hqhalf := qRho_le_half M hρa hρ1.le
  have hApos : 0 < A := by linarith
  have hm := M.m_pos_real
  have hn2 : (0 : ℝ) ≤ (M.n : ℝ) - 2 := by
    have hnR : (2 : ℝ) ≤ (M.n : ℝ) := by exact_mod_cast M.hn
    linarith
  obtain ⟨Cp2, hCp2, hpow2⟩ := pow_first_order_bound (M.n - 2) A
  obtain ⟨fmin, hfmin, hf_lo⟩ := M.exists_f_min
  obtain ⟨fmax, _, hf_hi⟩ := M.exists_f_max
  let M_lip := (M.m : ℝ) / fmin + ((M.n : ℝ) - 2) + Cp2 + 2
  refine ⟨M_lip, by positivity, fun e he => ?_⟩
  have hc := asking_coords M hρa hρ1 he.1 he.2
  rcases hc with ⟨_, _, _, _, _, hρv1, hv1v2, hv21, _, hFv2, hAv2, _, _, _, _, _⟩
  have hys := askingY_spec M hρa hρ1 he.1 he.2
  set y := askingY M ρ e
  set q₁ := askingQ1 M ρ e
  set v₂ := askingV2 M ρ e
  have hρv2 : ρ ≤ v₂ := by linarith
  have hy0 : 0 < y := lt_trans (div_pos he.1 hm) hys.1.1
  have hye : y < e := hys.1.2
  have he1 : e ≤ 1 := by linarith [he.2, hqhalf]
  have hv2_ρ_b : v₂ - ρ ≤ ((M.m : ℝ) / fmin) * e := by
    have hlip := (M.F_lipschitz_bounds ⟨hρa, hρ1.le⟩ ⟨le_trans hρa hρv2, hv21.le⟩ hρv2 hf_lo hf_hi).1
    rw [hFv2] at hlip
    rw [div_mul_eq_mul_div, le_div_iff₀ hfmin]; nlinarith
  have hmass : ∫ v in ρ..v₂, M.f v / (M.m : ℝ) = q_ρ - q₁ := by
    rw [intervalIntegral.integral_div, ← M.F_sub_eq_integral hρa hρv2 hv21.le, hFv2]
    dsimp [q_ρ, q₁]; unfold askingQ1; field_simp [hm.ne']; ring
  have hpw : ∀ v ∈ Icc ρ v₂, |v * (1 - M.A v) * M.A v ^ (M.n - 2) - q_ρ * ρ * A ^ (M.n - 2)| ≤ M_lip * e := by
    intro v hv
    have hv_mem : v ∈ Icc M.a 1 := ⟨le_trans hρa hv.1, le_trans hv.2 hv21.le⟩
    have hAv_d : |M.A v - A| ≤ e := by
      have hlo : A ≤ M.A v := by
        unfold Market.A; dsimp [A, q_ρ]; unfold qRho
        have := M.F_strictMonoOn.monotoneOn ⟨hρa, hρ1.le⟩ hv_mem hv.1
        have := div_le_div_of_nonneg_right (by linarith : 1 - M.F v ≤ 1 - M.F ρ) hm.le
        linarith
      have hhi : M.A v ≤ 1 - q₁ := by
        rw [← hAv2]; unfold Market.A
        have := M.F_strictMonoOn.monotoneOn hv_mem ⟨le_trans hρa hρv2, hv21.le⟩ hv.2
        have := div_le_div_of_nonneg_right (by linarith : 1 - M.F v₂ ≤ 1 - M.F v) hm.le
        linarith
      rw [abs_of_nonneg (by linarith)]
      have hq1e : q_ρ - q₁ = y := by dsimp [q₁, q_ρ]; unfold askingQ1; ring
      dsimp [A]; linarith only [hhi, hq1e, hye]
    have hp2 := hpow2 (M.A v - A) (le_trans hAv_d he1)
    have hcast2 : ((M.n - 2 : ℕ) : ℝ) = (M.n : ℝ) - 2 := by rw [Nat.cast_sub M.hn, Nat.cast_ofNat]
    have hA_le1 : A ≤ 1 := by dsimp [A]; linarith [qRho_pos M hρa hρ1]
    have hAp : A ^ (M.n - 2 - 1) ≤ 1 := pow_le_one₀ hApos.le hA_le1
    have hAp_d : |M.A v ^ (M.n - 2) - A ^ (M.n - 2)| ≤ (((M.n : ℝ) - 2) + Cp2) * e := by
      rw [show A + (M.A v - A) = M.A v by ring, hcast2] at hp2
      have htri := abs_add_le (M.A v ^ (M.n - 2) - A ^ (M.n - 2) -
        ((M.n : ℝ) - 2) * A ^ (M.n - 2 - 1) * (M.A v - A))
        (((M.n : ℝ) - 2) * A ^ (M.n - 2 - 1) * (M.A v - A))
      rw [show (M.A v ^ (M.n - 2) - A ^ (M.n - 2) -
          ((M.n : ℝ) - 2) * A ^ (M.n - 2 - 1) * (M.A v - A)) +
          ((M.n : ℝ) - 2) * A ^ (M.n - 2 - 1) * (M.A v - A) =
          M.A v ^ (M.n - 2) - A ^ (M.n - 2) by ring] at htri
      have hlin : |((M.n : ℝ) - 2) * A ^ (M.n - 2 - 1) * (M.A v - A)| ≤ ((M.n : ℝ) - 2) * e := by
        rw [abs_mul, abs_mul, abs_of_nonneg hn2, abs_of_pos (pow_pos hApos _)]
        calc ((M.n : ℝ) - 2) * A ^ (M.n - 2 - 1) * |M.A v - A|
            ≤ ((M.n : ℝ) - 2) * 1 * e := by gcongr
          _ = ((M.n : ℝ) - 2) * e := by ring
      have hsq : (M.A v - A) ^ 2 ≤ e := by
        rw [← sq_abs]; calc |M.A v - A| ^ 2 ≤ e ^ 2 := by gcongr
          _ ≤ e * 1 := by nlinarith only [he.1, he1]
          _ = e := mul_one e
      nlinarith only [htri, hp2, hlin, hsq, hCp2]
    have hv_d : |v - ρ| ≤ ((M.m : ℝ) / fmin) * e := by
      rw [abs_of_nonneg (by linarith [hv.1])]; linarith [hv.2, hv2_ρ_b]
    have h1A_d : |(1 - M.A v) - q_ρ| ≤ e := by
      have : (1 - M.A v) - q_ρ = -(M.A v - A) := by dsimp [A]; ring
      rw [this, abs_neg]; exact hAv_d
    have hAv_p : M.A v ^ (M.n - 2) ≤ 1 := pow_le_one₀ (M.br_A_pos hv_mem).le (M.br_A_mem_Icc hv_mem).2
    have hid : v * (1 - M.A v) * M.A v ^ (M.n - 2) - q_ρ * ρ * A ^ (M.n - 2) =
        ((1 - M.A v) - q_ρ) * v * M.A v ^ (M.n - 2) +
        q_ρ * (v - ρ) * M.A v ^ (M.n - 2) +
        q_ρ * ρ * (M.A v ^ (M.n - 2) - A ^ (M.n - 2)) := by ring
    rw [hid]
    have hv_pos : 0 < v := by linarith only [hρ0, hv.1]
    have hv_le1 : v ≤ 1 := by linarith only [hv.2, hv21]
    have hqρ_le1 : q_ρ ≤ 1 := by linarith only [hqhalf]
    have hAp_le1 : M.A v ^ (M.n - 2) ≤ 1 := pow_le_one₀ (M.br_A_pos hv_mem).le (M.br_A_mem_Icc hv_mem).2
    have hb1 : |((1 - M.A v) - q_ρ) * v * M.A v ^ (M.n - 2)| ≤ e := by
      rw [abs_mul, abs_mul, abs_of_pos hv_pos, abs_of_pos (pow_pos (M.br_A_pos hv_mem) _)]
      have h1 : |(1 - M.A v) - q_ρ| * v ≤ e * 1 := mul_le_mul h1A_d hv_le1 hv_pos.le he.1.le
      have h2 := mul_le_mul h1 hAp_le1 (pow_pos (M.br_A_pos hv_mem) _).le (by linarith only [he.1])
      linarith only [h2]
    have hb2 : |q_ρ * (v - ρ) * M.A v ^ (M.n - 2)| ≤ ((M.m : ℝ) / fmin) * e := by
      rw [abs_mul, abs_mul, abs_of_pos (qRho_pos M hρa hρ1), abs_of_pos (pow_pos (M.br_A_pos hv_mem) _)]
      have h1 : q_ρ * |v - ρ| ≤ 1 * (((M.m : ℝ) / fmin) * e) :=
        mul_le_mul hqρ_le1 hv_d (abs_nonneg _) zero_le_one
      have h2 := mul_le_mul h1 hAp_le1 (pow_pos (M.br_A_pos hv_mem) _).le
        (mul_nonneg zero_le_one (mul_nonneg (div_nonneg hm.le hfmin.le) he.1.le))
      linarith only [h2]
    have hb3 : |q_ρ * ρ * (M.A v ^ (M.n - 2) - A ^ (M.n - 2))| ≤ (((M.n : ℝ) - 2) + Cp2) * e := by
      rw [abs_mul, abs_mul, abs_of_pos (qRho_pos M hρa hρ1), abs_of_pos hρ0]
      calc q_ρ * ρ * |M.A v ^ (M.n - 2) - A ^ (M.n - 2)|
          ≤ 1 * 1 * ((((M.n : ℝ) - 2) + Cp2) * e) := by gcongr
        _ = (((M.n : ℝ) - 2) + Cp2) * e := by ring
    have ht1 := abs_add_le (((1 - M.A v) - q_ρ) * v * M.A v ^ (M.n - 2) + q_ρ * (v - ρ) * M.A v ^ (M.n - 2))
      (q_ρ * ρ * (M.A v ^ (M.n - 2) - A ^ (M.n - 2)))
    have ht2 := abs_add_le (((1 - M.A v) - q_ρ) * v * M.A v ^ (M.n - 2)) (q_ρ * (v - ρ) * M.A v ^ (M.n - 2))
    dsimp [M_lip]; linarith only [ht1, ht2, hb1, hb2, hb3, he.1]
  have hA_sub := M.A_continuousOn.mono (Icc_subset_Icc hρa hv21.le)
  have hf_sub := M.hf_cont.mono (Icc_subset_Icc hρa hv21.le)
  have hdiff_int : (∫ v in ρ..v₂, v * (1 - M.A v) * M.A v ^ (M.n - 2) * (M.f v / (M.m : ℝ))) -
      q_ρ * ρ * A ^ (M.n - 2) * (q_ρ - q₁) =
      ∫ v in ρ..v₂, (v * (1 - M.A v) * M.A v ^ (M.n - 2) - q_ρ * ρ * A ^ (M.n - 2)) *
        (M.f v / (M.m : ℝ)) := by
    have hi1 : IntervalIntegrable (fun v => v * (1 - M.A v) * M.A v ^ (M.n - 2) * (M.f v / (M.m : ℝ))) volume ρ v₂ :=
      ((((continuousOn_id.mul (continuousOn_const.sub hA_sub)).mul (hA_sub.pow _)).mul (hf_sub.div_const _)).mono
        (by rw [uIcc_of_le hρv2])).intervalIntegrable
    have hi2 : IntervalIntegrable (fun v => (q_ρ * ρ * A ^ (M.n - 2)) * (M.f v / (M.m : ℝ))) volume ρ v₂ :=
      ((hf_sub.div_const _).mono (by rw [uIcc_of_le hρv2])).intervalIntegrable.const_mul _
    have heq : (fun v => (v * (1 - M.A v) * M.A v ^ (M.n - 2) - q_ρ * ρ * A ^ (M.n - 2)) *
        (M.f v / (M.m : ℝ))) =
        fun v => v * (1 - M.A v) * M.A v ^ (M.n - 2) * (M.f v / (M.m : ℝ)) -
          (q_ρ * ρ * A ^ (M.n - 2)) * (M.f v / (M.m : ℝ)) := by ext v; ring
    rw [heq, intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_const_mul, hmass]
  rw [hdiff_int]
  have hnorm := intervalIntegral.abs_integral_le_integral_abs (μ := volume) hρv2
    (f := fun v => (v * (1 - M.A v) * M.A v ^ (M.n - 2) - q_ρ * ρ * A ^ (M.n - 2)) * (M.f v / (M.m : ℝ)))
  have hi_abs : IntervalIntegrable (fun v => |(v * (1 - M.A v) * M.A v ^ (M.n - 2) - q_ρ * ρ * A ^ (M.n - 2)) *
      (M.f v / (M.m : ℝ))|) volume ρ v₂ :=
    ((((((continuousOn_id.mul (continuousOn_const.sub hA_sub)).mul (hA_sub.pow _)).sub continuousOn_const).mul
      (hf_sub.div_const _)).abs).mono (by rw [uIcc_of_le hρv2])).intervalIntegrable
  have hi_hi : IntervalIntegrable (fun v => (M_lip * e) * (M.f v / (M.m : ℝ))) volume ρ v₂ :=
    ((hf_sub.div_const _).mono (by rw [uIcc_of_le hρv2])).intervalIntegrable.const_mul _
  have hmono := intervalIntegral.integral_mono_on hρv2 hi_abs hi_hi fun v hv => by
    rw [abs_mul, abs_of_pos (div_pos (M.hf_pos v ⟨le_trans hρa hv.1, le_trans hv.2 hv21.le⟩) hm)]
    exact mul_le_mul_of_nonneg_right (hpw v hv)
      (div_nonneg (M.hf_pos v ⟨le_trans hρa hv.1, le_trans hv.2 hv21.le⟩).le hm.le)
  rw [intervalIntegral.integral_const_mul, hmass] at hmono
  have hqy : q_ρ - q₁ = y := by dsimp [q_ρ, q₁]; unfold askingQ1; ring
  rw [hqy] at hmono
  have hMlip_e : 0 ≤ M_lip * e := mul_nonneg (by positivity) he.1.le
  calc _ ≤ (M_lip * e) * y := le_trans hnorm hmono
    _ ≤ (M_lip * e) * e := mul_le_mul_of_nonneg_left hye.le hMlip_e
    _ = M_lip * e ^ 2 := by ring

/-- Leading-order revenue gain in `e` (`O(e^2)` remainder!). -/
lemma askingRevGain_O_e2 (M : Market) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hρa : M.a ≤ ρ) :
    ∃ C ≥ 0, ∀ (e : ℝ) (_ : 0 < e) (_ : e < qRho M ρ)
      (hρβ : ρ < askingBeta M ρ e) (hβ1 : askingBeta M ρ e ≤ 1),
      |(sellerRev M (askingMech ρ (askingBeta M ρ e) hρ0.le hρβ hβ1)
          (askingVisit M ρ e) (seller0 M) -
        sellerRev M (SPA ρ hρ0.le hρ1.le) (unifVisit M) (seller0 M)) -
        ((M.n : ℝ) * ((M.m : ℝ) - 1) / (2 * (M.m : ℝ))) * ρ * M.A ρ ^ (M.n - 1) * e| ≤ C * e ^ 2 := by
  set q_ρ := qRho M ρ
  set A := 1 - q_ρ
  have hqpos := qRho_pos M hρa hρ1
  have hApos : 0 < A := by have := qRho_le_half M hρa hρ1.le; linarith
  have hm := M.m_pos_real
  have hm1 := M.m_sub_one_pos_real
  have hn := M.n_pos_real
  have hn1 := M.n_sub_one_pos_real
  obtain ⟨K₁, hK₁, hP1⟩ := askingRevGain_piece1 M hρa hρ1
  obtain ⟨K₂, hK₂, hP2⟩ := askingRevGain_piece2 M hρ0 hρ1 hρa
  obtain ⟨K₃, hK₃, hP3⟩ := askingRevGain_piece3 M hρ0 hρ1 hρa
  obtain ⟨Cy, hCy, hy_asym⟩ := askingY_asymptotic M hρa hρ1
  let C := (M.n : ℝ) * ρ * K₁ + (M.n : ℝ) * ((M.n : ℝ) - 1) * K₂ + (M.n : ℝ) * ((M.n : ℝ) - 1) * K₃ +
    (M.n : ℝ) * ((M.n : ℝ) - 1) * q_ρ * ρ * A ^ (M.n - 2) * (Cy / ((M.m : ℝ) - 1))
  refine ⟨C, by positivity, fun e he0 heq hρβ hβ1 => ?_⟩
  rw [askingRevGain_eq M hρ0 hρ1 hρa he0 heq hρβ hβ1]
  have h1 := hP1 e ⟨he0, heq⟩
  have h2 := hP2 e ⟨he0, heq⟩
  have h3 := hP3 e ⟨he0, heq⟩
  have hq0_err : |askingQ0 M ρ e - q_ρ + e / (2 * (M.m : ℝ))| ≤ (Cy / ((M.m : ℝ) - 1)) * e ^ 2 := by
    have : askingQ0 M ρ e - q_ρ + e / (2 * (M.m : ℝ)) =
        (askingY M ρ e - ((M.m : ℝ) + 1) / (2 * (M.m : ℝ)) * e) / ((M.m : ℝ) - 1) := by
      dsimp [q_ρ]; unfold askingQ0; field_simp [hm.ne', hm1.ne']; ring
    rw [this, abs_div, abs_of_pos hm1, div_mul_eq_mul_div Cy]
    exact div_le_div_of_nonneg_right (hy_asym e ⟨he0, heq⟩) hm1.le
  set E₁ := askingT0 M ρ e * (1 - askingQ0 M ρ e) ^ (M.n - 1) - q_ρ * A ^ (M.n - 1) -
      (((M.m : ℝ) - 1) / (2 * (M.m : ℝ)) * A ^ (M.n - 1) +
        ((M.n : ℝ) - 1) / (2 * (M.m : ℝ)) * q_ρ * A ^ (M.n - 2)) * e
  set E₂ := askingQ1 M ρ e * (∫ v in askingV1 M ρ e..askingV2 M ρ e,
      v * askingFriv M ρ e v ^ (M.n - 2) * (M.f v / ((M.m : ℝ) - 1))) -
      q_ρ * ρ * A ^ (M.n - 2) * (askingQ0 M ρ e - askingQ1 M ρ e)
  set E₃ := (∫ v in ρ..askingV2 M ρ e, v * (1 - M.A v) * M.A v ^ (M.n - 2) * (M.f v / (M.m : ℝ))) -
      q_ρ * ρ * A ^ (M.n - 2) * (q_ρ - askingQ1 M ρ e)
  set E₄ := askingQ0 M ρ e - q_ρ + e / (2 * (M.m : ℝ))
  have hcomb : (M.n : ℝ) * ρ * (askingT0 M ρ e * (1 - askingQ0 M ρ e) ^ (M.n - 1) -
        q_ρ * (1 - q_ρ) ^ (M.n - 1)) +
      (M.n : ℝ) * ((M.n : ℝ) - 1) * askingQ1 M ρ e *
        (∫ v in askingV1 M ρ e..askingV2 M ρ e, v * askingFriv M ρ e v ^ (M.n - 2) * (M.f v / ((M.m : ℝ) - 1))) -
      (M.n : ℝ) * ((M.n : ℝ) - 1) *
        (∫ v in ρ..askingV2 M ρ e, v * (1 - M.A v) * M.A v ^ (M.n - 2) * (M.f v / (M.m : ℝ))) -
      ((M.n : ℝ) * ((M.m : ℝ) - 1) / (2 * (M.m : ℝ))) * ρ * M.A ρ ^ (M.n - 1) * e =
      (M.n : ℝ) * ρ * E₁ + (M.n : ℝ) * ((M.n : ℝ) - 1) * E₂ - (M.n : ℝ) * ((M.n : ℝ) - 1) * E₃ +
      (M.n : ℝ) * ((M.n : ℝ) - 1) * q_ρ * ρ * A ^ (M.n - 2) * E₄ := by
    have hA_eq : M.A ρ = A := rfl
    rw [hA_eq]; dsimp [E₁, E₂, E₃, E₄, A]; ring
  rw [hcomb]
  have hb1 : |(M.n : ℝ) * ρ * E₁| ≤ (M.n : ℝ) * ρ * K₁ * e ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_pos hn, abs_of_pos hρ0]
    have := mul_le_mul_of_nonneg_left h1 (mul_pos hn hρ0).le; linarith
  have hb2 : |(M.n : ℝ) * ((M.n : ℝ) - 1) * E₂| ≤ (M.n : ℝ) * ((M.n : ℝ) - 1) * K₂ * e ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_pos hn, abs_of_pos hn1]
    have := mul_le_mul_of_nonneg_left h2 (mul_pos hn hn1).le; linarith
  have hb3 : |(M.n : ℝ) * ((M.n : ℝ) - 1) * E₃| ≤ (M.n : ℝ) * ((M.n : ℝ) - 1) * K₃ * e ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_pos hn, abs_of_pos hn1]
    have := mul_le_mul_of_nonneg_left h3 (mul_pos hn hn1).le; linarith
  have hb4 : |(M.n : ℝ) * ((M.n : ℝ) - 1) * q_ρ * ρ * A ^ (M.n - 2) * E₄| ≤
      (M.n : ℝ) * ((M.n : ℝ) - 1) * q_ρ * ρ * A ^ (M.n - 2) * (Cy / ((M.m : ℝ) - 1)) * e ^ 2 := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < (M.n : ℝ) * ((M.n : ℝ) - 1) * q_ρ * ρ * A ^ (M.n - 2))]
    have := mul_le_mul_of_nonneg_left hq0_err (by positivity : 0 ≤ (M.n : ℝ) * ((M.n : ℝ) - 1) * q_ρ * ρ * A ^ (M.n - 2))
    linarith
  have ht1 := abs_add_le ((M.n : ℝ) * ρ * E₁ + (M.n : ℝ) * ((M.n : ℝ) - 1) * E₂ - (M.n : ℝ) * ((M.n : ℝ) - 1) * E₃)
    ((M.n : ℝ) * ((M.n : ℝ) - 1) * q_ρ * ρ * A ^ (M.n - 2) * E₄)
  have ht2 : |(M.n : ℝ) * ρ * E₁ + (M.n : ℝ) * ((M.n : ℝ) - 1) * E₂ - (M.n : ℝ) * ((M.n : ℝ) - 1) * E₃| ≤
      |(M.n : ℝ) * ρ * E₁ + (M.n : ℝ) * ((M.n : ℝ) - 1) * E₂| + |(M.n : ℝ) * ((M.n : ℝ) - 1) * E₃| := by
    simpa [sub_zero, zero_sub, abs_neg] using
      abs_sub_le ((M.n : ℝ) * ρ * E₁ + (M.n : ℝ) * ((M.n : ℝ) - 1) * E₂) 0 ((M.n : ℝ) * ((M.n : ℝ) - 1) * E₃)
  have ht3 := abs_add_le ((M.n : ℝ) * ρ * E₁) ((M.n : ℝ) * ((M.n : ℝ) - 1) * E₂)
  dsimp [C]; linarith

/-- **Theorem 3 (Part 2 — Asking-Price Revenue Gain Asymptotics)**:
For any `M : Market` and binding reserve `ρ ∈ (0, 1)` (`M.a ≤ ρ`), every `β` sufficiently
close to `ρ` from above (`β ∈ (ρ, β₀)`) is realized as `β = askingBeta M ρ e` for some
`e ∈ (0, q_ρ)` with SR continuation `askingVisit M ρ e`, and the resulting revenue gain `D(β)`
satisfies:
* `D(β) = (2 * n * (m - 1) / (m * (m + 3))) * ρ * A(ρ)^(n-1) * (F(β) - F(ρ)) + o(β - ρ)` as `β → ρ+`,
* `e(β) = (4 / (m + 3)) * (F(β) - F(ρ)) + o(β - ρ)` as `β → ρ+`,
* equivalently in `e`: `D_e(e) = (n * (m - 1) / (2 * m)) * ρ * A(ρ)^(n-1) * e + o(e)` as `e → 0+`,
* and `D(β) > 0` for all `β` sufficiently close to `ρ` from above. -/
theorem theorem3_asking_price_gain (M : Market) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hρa : M.a ≤ ρ) :
    ∃ β₀ ∈ Ioo ρ 1, ∃ eOfβ : ℝ → ℝ,
      (∀ β (hβ : β ∈ Ioo ρ β₀),
        eOfβ β ∈ Ioo (0 : ℝ) (qRho M ρ) ∧
          askingBeta M ρ (eOfβ β) = β ∧
          ∀ hβ1 : β ≤ 1, IsSR M (askingProfile M ρ β hρ0.le hβ.1 hβ1) (askingVisit M ρ (eOfβ β))) ∧
      (fun e =>
        (if h : 0 < e ∧ e < qRho M ρ then
          have hc := asking_coords M hρa hρ1 h.1 h.2
          sellerRev M (askingMech ρ (askingBeta M ρ e) hρ0.le
              (lt_trans hc.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
              (le_trans hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.le hc.2.2.2.2.2.2.2.1.le))
              (askingVisit M ρ e) (seller0 M) -
            sellerRev M (SPA ρ hρ0.le hρ1.le) (unifVisit M) (seller0 M)
        else 0) -
        ((M.n : ℝ) * ((M.m : ℝ) - 1) / (2 * (M.m : ℝ))) * ρ * M.A ρ ^ (M.n - 1) * e)
        =o[𝓝[>] 0] id ∧
      (fun β => eOfβ β - (4 / ((M.m : ℝ) + 3)) * (M.F β - M.F ρ)) =o[𝓝[>] ρ] (fun β => β - ρ) ∧
      (fun β =>
        (if h : ρ < β ∧ β ≤ 1 then
          sellerRev M (askingMech ρ β hρ0.le h.1 h.2) (askingVisit M ρ (eOfβ β)) (seller0 M) -
            sellerRev M (SPA ρ hρ0.le hρ1.le) (unifVisit M) (seller0 M)
        else 0) -
        (2 * (M.n : ℝ) * ((M.m : ℝ) - 1) / ((M.m : ℝ) * ((M.m : ℝ) + 3))) * ρ * M.A ρ ^ (M.n - 1) *
          (M.F β - M.F ρ))
        =o[𝓝[>] ρ] (fun β => β - ρ) ∧
      ∀ᶠ β in 𝓝[>] ρ,
        ∃ (hρβ : ρ < β) (hβ1 : β ≤ 1),
          0 < sellerRev M (askingMech ρ β hρ0.le hρβ hβ1) (askingVisit M ρ (eOfβ β)) (seller0 M) -
            sellerRev M (SPA ρ hρ0.le hρ1.le) (unifVisit M) (seller0 M) := by
  have hqpos := qRho_pos M hρa hρ1
  have hm := M.m_pos_real
  have hm1 := M.m_sub_one_pos_real
  have hn := M.n_pos_real
  have hfρ : 0 < M.f ρ := M.hf_pos ρ ⟨hρa, hρ1.le⟩
  obtain ⟨hFβ_lim, hβ_sub_lim⟩ := askingBeta_asymptotic M hρa hρ1
  obtain ⟨C_D, hCD, hD_O2⟩ := askingRevGain_O_e2 M hρ0 hρ1 hρa
  let e_hi := qRho M ρ / 2
  have he_hi : e_hi ∈ Ioo (0 : ℝ) (qRho M ρ) := ⟨by positivity, by dsimp [e_hi]; linarith⟩
  have hc_hi := asking_coords M hρa hρ1 he_hi.1 he_hi.2
  let β₀ := askingBeta M ρ e_hi
  have hβ₀_mem : β₀ ∈ Ioo ρ 1 :=
    ⟨lt_trans hc_hi.2.2.2.2.2.1 hc_hi.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
     lt_trans hc_hi.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 hc_hi.2.2.2.2.2.2.2.1⟩
  have hβ_lim0 : Tendsto (askingBeta M ρ) (𝓝[>] 0) (nhds ρ) := by
    have h0 : Tendsto (fun e => e * ((askingBeta M ρ e - ρ) / e) + ρ) (𝓝[>] 0)
        (nhds (0 * (((M.m : ℝ) + 3) / (4 * M.f ρ)) + ρ)) :=
      ((tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).mul hβ_sub_lim).add tendsto_const_nhds
    rw [zero_mul, zero_add] at h0
    refine h0.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with e he
    rw [mul_div_cancel₀ _ (ne_of_gt he)]; ring
  have hex_e : ∀ β ∈ Ioo ρ β₀, ∃ e ∈ Ioo (0 : ℝ) e_hi, askingBeta M ρ e = β := by
    intro β hβ
    have hnear := Metric.tendsto_nhds.mp hβ_lim0 (β - ρ) (by linarith [hβ.1])
    obtain ⟨δ, hδ, hδ_prop⟩ := Metric.mem_nhdsWithin_iff.mp hnear
    let e_lo := min (e_hi / 2) (δ / 2)
    have he_lo_pos : 0 < e_lo := lt_min (by positivity) (by positivity)
    have he_lo_lt : e_lo < e_hi := lt_of_le_of_lt (min_le_left _ _) (by linarith [he_hi.1])
    have hβ_lo : askingBeta M ρ e_lo < β := by
      have hmem : e_lo ∈ Metric.ball (0 : ℝ) δ ∩ Ioi 0 :=
        ⟨by rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos he_lo_pos]
            exact lt_of_le_of_lt (min_le_right _ _) (by linarith), he_lo_pos⟩
      have h : dist (askingBeta M ρ e_lo) ρ < β - ρ := hδ_prop hmem
      rw [Real.dist_eq] at h
      linarith [(abs_lt.mp h).2]
    have hcont : ContinuousOn (askingBeta M ρ) (Icc e_lo e_hi) :=
      (askingBeta_continuousOn M hρa hρ1).mono (Icc_subset_Ioo he_lo_pos he_hi.2)
    obtain ⟨e, he, hβe⟩ := intermediate_value_Icc he_lo_lt.le hcont ⟨hβ_lo.le, hβ.2.le⟩
    have he_open : e ∈ Ioo (0 : ℝ) e_hi := by
      refine ⟨lt_of_lt_of_le he_lo_pos he.1, lt_of_le_of_ne he.2 ?_⟩
      intro h; rw [h] at hβe; linarith [hβ.2]
    exact ⟨e, he_open, hβe⟩
  let eOfβ : ℝ → ℝ := fun β => if h : β ∈ Ioo ρ β₀ then (hex_e β h).choose else 0
  have heOfβ_spec : ∀ β (h : β ∈ Ioo ρ β₀),
      eOfβ β ∈ Ioo (0 : ℝ) (qRho M ρ) ∧ askingBeta M ρ (eOfβ β) = β := by
    intro β h
    dsimp [eOfβ]; simp only [h, ↓reduceDIte]
    have hs := (hex_e β h).choose_spec
    exact ⟨⟨hs.1.1, lt_trans hs.1.2 he_hi.2⟩, hs.2⟩
  have heOfβ_lim0 : Tendsto eOfβ (𝓝[>] ρ) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · rw [Metric.tendsto_nhds]
      intro ε hε
      have hFcont : ContinuousWithinAt M.F (Ioi ρ) ρ :=
        (M.F_continuousOn ρ ⟨hρa, hρ1.le⟩).mono_of_mem_nhdsWithin (by
          filter_upwards [Ioo_mem_nhdsGT hρ1] with v hv using ⟨le_trans hρa hv.1.le, hv.2.le⟩)
      obtain ⟨δ, hδ, hFδ⟩ := Metric.continuousWithinAt_iff.mp hFcont ε hε
      filter_upwards [Ioo_mem_nhdsGT hβ₀_mem.1, Ioo_mem_nhdsGT (lt_min hρ1 (by linarith : ρ < ρ + δ))] with β hβ1 hβ2
      have hsp := heOfβ_spec β hβ1
      have hc := asking_coords M hρa hρ1 hsp.1.1 hsp.1.2
      have hv1β : askingV1 M ρ (eOfβ β) < β := by
        calc askingV1 M ρ (eOfβ β) < askingBeta M ρ (eOfβ β) := hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          _ = β := hsp.2
      have hFlt : M.F (askingV1 M ρ (eOfβ β)) < M.F β :=
        M.F_strictMonoOn ⟨le_trans hρa hc.2.2.2.2.2.1.le, le_trans hc.2.2.2.2.2.2.1.le hc.2.2.2.2.2.2.2.1.le⟩
          ⟨le_trans hρa hβ1.1.le, le_trans hβ1.2.le hβ₀_mem.2.le⟩ hv1β
      have he_lt : eOfβ β < M.F β - M.F ρ := by linarith [hc.2.2.2.2.2.2.2.2.1]
      have hFd : |M.F β - M.F ρ| < ε := by
        have := hFδ hβ1.1 (by rw [Real.dist_eq, abs_of_pos (by linarith [hβ1.1])]; linarith [hβ2.2, min_le_right 1 (ρ + δ)])
        rwa [Real.dist_eq] at this
      rw [Real.dist_eq, sub_zero, abs_of_pos hsp.1.1]
      linarith [(abs_lt.mp hFd).2]
    · filter_upwards [Ioo_mem_nhdsGT hβ₀_mem.1] with β hβ using (heOfβ_spec β hβ).1.1
  have he_div_β : Tendsto (fun β => eOfβ β / (β - ρ)) (𝓝[>] ρ)
      (nhds (4 * M.f ρ / ((M.m : ℝ) + 3))) := by
    have hinv := (hβ_sub_lim.comp heOfβ_lim0).inv₀ (by positivity : (((M.m : ℝ) + 3) / (4 * M.f ρ)) ≠ 0)
    have hval : (((M.m : ℝ) + 3) / (4 * M.f ρ))⁻¹ = 4 * M.f ρ / ((M.m : ℝ) + 3) := by
      rw [inv_div]
    rw [hval] at hinv
    refine hinv.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hβ₀_mem.1] with β hβ
    have hsp := heOfβ_spec β hβ
    dsimp [Function.comp]
    rw [hsp.2, inv_div]
  have hF_slope := F_slope_tendsto M hρa hρ1
  have ho_e : (fun e =>
      (if h : 0 < e ∧ e < qRho M ρ then
        have hc := asking_coords M hρa hρ1 h.1 h.2
        sellerRev M (askingMech ρ (askingBeta M ρ e) hρ0.le
            (lt_trans hc.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
            (le_trans hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.le hc.2.2.2.2.2.2.2.1.le))
            (askingVisit M ρ e) (seller0 M) -
          sellerRev M (SPA ρ hρ0.le hρ1.le) (unifVisit M) (seller0 M)
      else 0) -
      ((M.n : ℝ) * ((M.m : ℝ) - 1) / (2 * (M.m : ℝ))) * ρ * M.A ρ ^ (M.n - 1) * e)
      =o[𝓝[>] 0] id := by
    rw [Asymptotics.isLittleO_iff]
    intro c hc_pos
    have hCD1 : 0 < C_D + 1 := by linarith only [hCD]
    filter_upwards [Ioo_mem_nhdsGT hqpos, Ioo_mem_nhdsGT (div_pos hc_pos hCD1)] with e he1 he2
    simp only [he1.1, he1.2, and_self, ↓reduceDIte, Real.norm_eq_abs, id_eq, abs_of_pos he1.1]
    have hc := asking_coords M hρa hρ1 he1.1 he1.2
    have h := hD_O2 e he1.1 he1.2 (lt_trans hc.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
      (le_trans hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.le hc.2.2.2.2.2.2.2.1.le)
    have hle : C_D * e ≤ c := by
      have : e < c / (C_D + 1) := he2.2
      rw [lt_div_iff₀ hCD1] at this
      nlinarith only [this, he1.1]
    calc _ ≤ C_D * e ^ 2 := h
      _ = (C_D * e) * e := by ring
      _ ≤ c * e := by gcongr; exact he1.1.le
  have ho_eOfβ : (fun β => eOfβ β - (4 / ((M.m : ℝ) + 3)) * (M.F β - M.F ρ))
      =o[𝓝[>] ρ] (fun β => β - ρ) := by
    have hlim0 : Tendsto (fun β => (eOfβ β - (4 / ((M.m : ℝ) + 3)) * (M.F β - M.F ρ)) / (β - ρ))
        (𝓝[>] ρ) (nhds 0) := by
      have h := he_div_β.sub (hF_slope.const_mul (4 / ((M.m : ℝ) + 3)))
      have h0 : 4 * M.f ρ / ((M.m : ℝ) + 3) - 4 / ((M.m : ℝ) + 3) * M.f ρ = 0 := by ring
      rw [h0] at h
      exact h.congr (fun β => by ring)
    rw [Asymptotics.isLittleO_iff]
    intro c hc_pos
    filter_upwards [self_mem_nhdsWithin, Metric.tendsto_nhds.mp hlim0 c hc_pos] with β hβ hdist
    have hβpos : 0 < β - ρ := sub_pos.mpr hβ
    rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hβpos, div_lt_iff₀ hβpos] at hdist
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hβpos]
    exact hdist.le
  have ho_D : (fun β =>
      (if h : ρ < β ∧ β ≤ 1 then
        sellerRev M (askingMech ρ β hρ0.le h.1 h.2) (askingVisit M ρ (eOfβ β)) (seller0 M) -
          sellerRev M (SPA ρ hρ0.le hρ1.le) (unifVisit M) (seller0 M)
      else 0) -
      (2 * (M.n : ℝ) * ((M.m : ℝ) - 1) / ((M.m : ℝ) * ((M.m : ℝ) + 3))) * ρ * M.A ρ ^ (M.n - 1) *
        (M.F β - M.F ρ))
      =o[𝓝[>] ρ] (fun β => β - ρ) := by
    have hD_div_e : Tendsto (fun e =>
        (if h : 0 < e ∧ e < qRho M ρ then
          have hc := asking_coords M hρa hρ1 h.1 h.2
          sellerRev M (askingMech ρ (askingBeta M ρ e) hρ0.le
              (lt_trans hc.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
              (le_trans hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.le hc.2.2.2.2.2.2.2.1.le))
              (askingVisit M ρ e) (seller0 M) -
            sellerRev M (SPA ρ hρ0.le hρ1.le) (unifVisit M) (seller0 M)
        else 0) / e)
        (𝓝[>] 0) (nhds (((M.n : ℝ) * ((M.m : ℝ) - 1) / (2 * (M.m : ℝ))) * ρ * M.A ρ ^ (M.n - 1))) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      have hCD1 : 0 < C_D + 1 := by linarith only [hCD]
      filter_upwards [Ioo_mem_nhdsGT hqpos, Ioo_mem_nhdsGT (div_pos hε hCD1)] with e he1 he2
      rw [Real.dist_eq]; simp only [he1.1, he1.2, and_self, ↓reduceDIte]
      have hc := asking_coords M hρa hρ1 he1.1 he1.2
      have h := hD_O2 e he1.1 he1.2 (lt_trans hc.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
        (le_trans hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.le hc.2.2.2.2.2.2.2.1.le)
      set Dval := sellerRev M (askingMech ρ (askingBeta M ρ e) hρ0.le
          (lt_trans hc.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
          (le_trans hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.le hc.2.2.2.2.2.2.2.1.le))
          (askingVisit M ρ e) (seller0 M) -
        sellerRev M (SPA ρ hρ0.le hρ1.le) (unifVisit M) (seller0 M)
      set c₀ := ((M.n : ℝ) * ((M.m : ℝ) - 1) / (2 * (M.m : ℝ))) * ρ * M.A ρ ^ (M.n - 1)
      have hid : Dval / e - c₀ = (Dval - c₀ * e) / e := by field_simp [he1.1.ne']
      rw [hid, abs_div, abs_of_pos he1.1]
      have hlt : (C_D + 1) * e < ε := by
        have hlt0 : e * (C_D + 1) < ε := (lt_div_iff₀ hCD1).mp he2.2
        linarith only [hlt0]
      calc _ ≤ (C_D * e ^ 2) / e := div_le_div_of_nonneg_right h he1.1.le
        _ = C_D * e := by field_simp [he1.1.ne']
        _ ≤ (C_D + 1) * e := by nlinarith only [he1.1]
        _ < ε := hlt
    have hD_div_β : Tendsto (fun β =>
        (if h : ρ < β ∧ β ≤ 1 then
          sellerRev M (askingMech ρ β hρ0.le h.1 h.2) (askingVisit M ρ (eOfβ β)) (seller0 M) -
            sellerRev M (SPA ρ hρ0.le hρ1.le) (unifVisit M) (seller0 M)
        else 0) / (β - ρ))
        (𝓝[>] ρ) (nhds ((2 * (M.n : ℝ) * ((M.m : ℝ) - 1) / ((M.m : ℝ) * ((M.m : ℝ) + 3))) *
          ρ * M.A ρ ^ (M.n - 1) * M.f ρ)) := by
      have hprod := (hD_div_e.comp heOfβ_lim0).mul he_div_β
      have hval : ((M.n : ℝ) * ((M.m : ℝ) - 1) / (2 * (M.m : ℝ))) * ρ * M.A ρ ^ (M.n - 1) *
          (4 * M.f ρ / ((M.m : ℝ) + 3)) =
          (2 * (M.n : ℝ) * ((M.m : ℝ) - 1) / ((M.m : ℝ) * ((M.m : ℝ) + 3))) *
          ρ * M.A ρ ^ (M.n - 1) * M.f ρ := by
        have hm3 : (M.m : ℝ) + 3 ≠ 0 := by positivity
        field_simp [hm.ne', hm3]; ring
      rw [hval] at hprod
      refine hprod.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT hβ₀_mem.1] with β hβ
      have hsp := heOfβ_spec β hβ
      have hβ1 : β ≤ 1 := le_trans hβ.2.le hβ₀_mem.2.le
      dsimp [Function.comp]
      simp only [hsp.1.1, hsp.1.2, hβ.1, hβ1, and_self, ↓reduceDIte]
      have hmech_eq : askingMech ρ (askingBeta M ρ (eOfβ β)) hρ0.le
          (lt_trans (asking_coords M hρa hρ1 hsp.1.1 hsp.1.2).2.2.2.2.2.1
            (asking_coords M hρa hρ1 hsp.1.1 hsp.1.2).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
          (le_trans (asking_coords M hρa hρ1 hsp.1.1 hsp.1.2).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.le
            (asking_coords M hρa hρ1 hsp.1.1 hsp.1.2).2.2.2.2.2.2.2.1.le) =
          askingMech ρ β hρ0.le hβ.1 hβ1 :=
        askingMech_eq_of_eq hsp.2 _ _ _ _ _
      rw [hmech_eq]
      field_simp [hsp.1.1.ne']
    have hlim0 : Tendsto (fun β =>
        ((if h : ρ < β ∧ β ≤ 1 then
          sellerRev M (askingMech ρ β hρ0.le h.1 h.2) (askingVisit M ρ (eOfβ β)) (seller0 M) -
            sellerRev M (SPA ρ hρ0.le hρ1.le) (unifVisit M) (seller0 M)
        else 0) -
        (2 * (M.n : ℝ) * ((M.m : ℝ) - 1) / ((M.m : ℝ) * ((M.m : ℝ) + 3))) * ρ * M.A ρ ^ (M.n - 1) *
          (M.F β - M.F ρ)) / (β - ρ))
        (𝓝[>] ρ) (nhds 0) := by
      have h := hD_div_β.sub (hF_slope.const_mul
        ((2 * (M.n : ℝ) * ((M.m : ℝ) - 1) / ((M.m : ℝ) * ((M.m : ℝ) + 3))) * ρ * M.A ρ ^ (M.n - 1)))
      rw [sub_self] at h
      exact h.congr (fun β => by ring)
    rw [Asymptotics.isLittleO_iff]
    intro c hc_pos
    filter_upwards [self_mem_nhdsWithin, Metric.tendsto_nhds.mp hlim0 c hc_pos] with β hβ hdist
    have hβpos : 0 < β - ρ := sub_pos.mpr hβ
    rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hβpos, div_lt_iff₀ hβpos] at hdist
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hβpos]
    exact hdist.le
  have hpos_ev : ∀ᶠ β in 𝓝[>] ρ,
      ∃ (hρβ : ρ < β) (hβ1 : β ≤ 1),
        0 < sellerRev M (askingMech ρ β hρ0.le hρβ hβ1) (askingVisit M ρ (eOfβ β)) (seller0 M) -
          sellerRev M (SPA ρ hρ0.le hρ1.le) (unifVisit M) (seller0 M) := by
    let c₀ := ((M.n : ℝ) * ((M.m : ℝ) - 1) / (2 * (M.m : ℝ))) * ρ * M.A ρ ^ (M.n - 1)
    have hc₀_pos : 0 < c₀ := by have := M.br_A_pos ⟨hρa, hρ1.le⟩; positivity
    have he_small : ∀ᶠ β in 𝓝[>] ρ, eOfβ β < c₀ / (C_D + 1) :=
      heOfβ_lim0.eventually (nhdsWithin_le_nhds (Iio_mem_nhds (by positivity : (0 : ℝ) < c₀ / (C_D + 1))))
    filter_upwards [Ioo_mem_nhdsGT hβ₀_mem.1, he_small] with β hβ he_lt
    have hsp := heOfβ_spec β hβ
    have hβ1 : β ≤ 1 := le_trans hβ.2.le hβ₀_mem.2.le
    refine ⟨hβ.1, hβ1, ?_⟩
    have hc := asking_coords M hρa hρ1 hsp.1.1 hsp.1.2
    have h := hD_O2 (eOfβ β) hsp.1.1 hsp.1.2 (lt_trans hc.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
      (le_trans hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.le hc.2.2.2.2.2.2.2.1.le)
    have hmech_eq : askingMech ρ (askingBeta M ρ (eOfβ β)) hρ0.le
        (lt_trans hc.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
        (le_trans hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.le hc.2.2.2.2.2.2.2.1.le) =
        askingMech ρ β hρ0.le hβ.1 hβ1 :=
      askingMech_eq_of_eq hsp.2 _ _ _ _ _
    rw [hmech_eq] at h
    have hlo : c₀ * eOfβ β - C_D * (eOfβ β) ^ 2 ≤
        sellerRev M (askingMech ρ β hρ0.le hβ.1 hβ1) (askingVisit M ρ (eOfβ β)) (seller0 M) -
          sellerRev M (SPA ρ hρ0.le hρ1.le) (unifVisit M) (seller0 M) := by linarith only [(abs_le.mp h).1]
    have hCD_lt : C_D * eOfβ β < c₀ := by
      have : eOfβ β * (C_D + 1) < c₀ := (lt_div_iff₀ (by linarith only [hCD] : 0 < C_D + 1)).mp he_lt
      nlinarith only [this, hsp.1.1]
    nlinarith only [hlo, hCD_lt, hsp.1.1]
  refine ⟨β₀, hβ₀_mem, eOfβ, ?_, ho_e, ho_eOfβ, ho_D, hpos_ev⟩
  intro β hβ
  have hsp := heOfβ_spec β hβ
  refine ⟨hsp.1, hsp.2, fun hβ1 => ?_⟩
  have hsr := theorem3_asking_price_sr M hρ0 hρ1 hρa hsp.1.1 hsp.1.2
    (by rw [hsp.2]; exact hβ.1) (by rw [hsp.2]; exact hβ1)
  have hprof_eq : askingProfile M ρ (askingBeta M ρ (eOfβ β)) hρ0.le
      (by rw [hsp.2]; exact hβ.1) (by rw [hsp.2]; exact hβ1) =
      askingProfile M ρ β hρ0.le hβ.1 hβ1 :=
    askingProfile_eq_of_eq M hsp.2 _ _ _ _ _
  rwa [hprof_eq] at hsr

/-! #### Theorem 3 Boundary Cases (`ρ = 1` and `a = ρ = 0`) -/

/-- Exclusive visit strategy sending every buyer to `seller0 M`. -/
def exclVisit (M : Market) : VisitStrategy M where
  θ := fun j _ => if j = seller0 M then 1 else 0
  hmeas := fun _ => measurable_const
  hnonneg := fun _ _ => by split_ifs <;> positivity
  hsum := fun _ _ => by
    rw [Finset.sum_ite_eq' Finset.univ (seller0 M) (fun _ => (1 : ℝ))]
    simp

/-- **Theorem 3 (Boundary Case `ρ = 1`)**:
At `ρ = 1`, symmetric `SPA(1)` yields zero revenue, and deviating to any lower reserve
`r₁ ∈ (a, 1)` induces the exclusive visit strategy as SR and strictly raises seller 0's revenue. -/
theorem theorem3_rho_one_fails (M : Market) {r₁ : ℝ} (hr1_a : M.a < r₁) (hr1_1 : r₁ < 1) :
    let hr1_0 : 0 ≤ r₁ := le_trans M.ha0 hr1_a.le
    let prof : Fin M.m → HierarchicalMech := fun j =>
      if j = seller0 M then SPA r₁ hr1_0 hr1_1.le else SPA 1 zero_le_one le_rfl
    sellerRev M (SPA 1 zero_le_one le_rfl) (unifVisit M) (seller0 M) = 0 ∧
    IsSR M prof (exclVisit M) ∧
    0 < sellerRev M (SPA r₁ hr1_0 hr1_1.le) (exclVisit M) (seller0 M) := by
  intro hr1_0 prof
  have hR1_zero : sellerRev M (SPA 1 zero_le_one le_rfl) (unifVisit M) (seller0 M) = 0 := by
    unfold sellerRev
    suffices ∫ v in M.a..1, payment M (SPA 1 zero_le_one le_rfl) (effDist M (unifVisit M) (seller0 M)) v *
        (unifVisit M).θ (seller0 M) v * M.f v = 0 by rw [this, mul_zero]
    rw [intervalIntegral_congr_Ioo M.ha1.le (g := fun _ => (0 : ℝ)) (fun v hv => by
      unfold payment
      rw [alloc_SPA_unif M zero_le_one le_rfl M.ha1.le (seller0 M) hv.2.le,
        surplus_SPA_unif M zero_le_one le_rfl M.ha1.le (seller0 M) (le_trans M.ha0 hv.1.le) hv.2.le]
      simp [hv.2, hv.2.le])]
    simp
  have hF0_excl : ∀ v ∈ Icc M.a 1, effDist M (exclVisit M) (seller0 M) v = M.F v := by
    intro v hv
    unfold effDist exclVisit; dsimp
    simp only [one_mul]
    rw [← M.F_sub_eq_integral hv.1 hv.2 le_rfl, M.hF_1]; ring
  have hs_riv_zero : ∀ (j : Fin M.m), j ≠ seller0 M → ∀ v ∈ Icc (0 : ℝ) 1,
      surplus M (SPA 1 zero_le_one le_rfl) (effDist M (exclVisit M) j) v = 0 := by
    intro j _ v hv
    unfold surplus
    rw [intervalIntegral_congr_Ioo hv.1 (g := fun _ => (0 : ℝ)) (fun u hu => by
      unfold alloc SPA; dsimp; simp [lt_of_lt_of_le hu.2 hv.2])]
    simp
  have hs_0_excl : ∀ v ∈ Icc (0 : ℝ) 1,
      surplus M (SPA r₁ hr1_0 hr1_1.le) (effDist M (exclVisit M) (seller0 M)) v =
        if v ≤ r₁ then 0 else ∫ u in r₁..v, M.F u ^ (M.n - 1) := by
    intro v hv
    unfold surplus
    have ha0 : ∀ u ∈ Ioo (0 : ℝ) r₁, alloc M (SPA r₁ hr1_0 hr1_1.le) (effDist M (exclVisit M) (seller0 M)) u = 0 := by
      intro u hu; unfold alloc SPA; dsimp; simp [hu.2]
    have ha1 : ∀ u ∈ Ioo r₁ 1, alloc M (SPA r₁ hr1_0 hr1_1.le) (effDist M (exclVisit M) (seller0 M)) u = M.F u ^ (M.n - 1) := by
      intro u hu; unfold alloc SPA; dsimp
      simp only [not_lt.mpr hu.1.le, ↓reduceIte]
      rw [hF0_excl u ⟨le_trans hr1_a.le hu.1.le, hu.2.le⟩]
    split_ifs with hvr
    · rw [intervalIntegral_congr_Ioo hv.1 (g := fun _ => (0 : ℝ)) (fun u hu => ha0 u ⟨hu.1, lt_of_lt_of_le hu.2 hvr⟩)]
      simp
    · push Not at hvr
      have hi0 : IntervalIntegrable (alloc M (SPA r₁ hr1_0 hr1_1.le) (effDist M (exclVisit M) (seller0 M))) volume 0 r₁ :=
        (intervalIntegrable_congr_Ioo hr1_0 ha0).mpr intervalIntegrable_const
      have hcontF : ContinuousOn (fun u => M.F u ^ (M.n - 1)) (Icc r₁ v) :=
        (M.F_continuousOn.mono (Icc_subset_Icc hr1_a.le hv.2)).pow _
      have hi1 : IntervalIntegrable (alloc M (SPA r₁ hr1_0 hr1_1.le) (effDist M (exclVisit M) (seller0 M))) volume r₁ v :=
        (intervalIntegrable_congr_Ioo hvr.le (fun u hu => ha1 u ⟨hu.1, lt_of_lt_of_le hu.2 hv.2⟩)).mpr
          (hcontF.mono (by rw [uIcc_of_le hvr.le])).intervalIntegrable
      rw [← intervalIntegral.integral_add_adjacent_intervals hi0 hi1,
        intervalIntegral_congr_Ioo hr1_0 ha0, intervalIntegral.integral_zero, zero_add]
      exact intervalIntegral_congr_Ioo hvr.le (fun u hu => ha1 u ⟨hu.1, lt_of_lt_of_le hu.2 hv.2⟩)
  have hSR : IsSR M prof (exclVisit M) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv j k hjpos
    have hj0 : j = seller0 M := by
      by_contra hne
      have : (exclVisit M).θ j v = 0 := by simp [exclVisit, hne]
      linarith
    subst hj0
    by_cases hk0 : k = seller0 M
    · subst hk0; exact le_rfl
    · have hp0 : prof (seller0 M) = SPA r₁ hr1_0 hr1_1.le := by simp [prof]
      have hpk : prof k = SPA 1 zero_le_one le_rfl := by simp [prof, hk0]
      rw [hp0, hpk, hs_riv_zero k hk0 v ⟨le_trans M.ha0 hv.1, hv.2⟩,
        hs_0_excl v ⟨le_trans M.ha0 hv.1, hv.2⟩]
      split_ifs with hvr
      · exact le_rfl
      · push Not at hvr
        apply intervalIntegral.integral_nonneg hvr.le
        intro u hu
        exact pow_nonneg (M.F_mem_Icc ⟨le_trans hr1_a.le hu.1, le_trans hu.2 hv.2⟩).1 _
  have hR0_pos : 0 < sellerRev M (SPA r₁ hr1_0 hr1_1.le) (exclVisit M) (seller0 M) := by
    unfold sellerRev
    apply mul_pos M.n_pos_real
    let fn : ℝ → ℝ := fun v => payment M (SPA r₁ hr1_0 hr1_1.le) (effDist M (exclVisit M) (seller0 M)) v *
      (exclVisit M).θ (seller0 M) v * M.f v
    have h_ar1 : ∀ v ∈ Ioo M.a r₁, fn v = 0 := by
      intro v hv; dsimp [fn]; unfold payment
      have ha : alloc M (SPA r₁ hr1_0 hr1_1.le) (effDist M (exclVisit M) (seller0 M)) v = 0 := by
        unfold alloc SPA; dsimp; simp [hv.2]
      rw [ha, hs_0_excl v ⟨le_trans M.ha0 hv.1.le, le_trans hv.2.le hr1_1.le⟩]
      simp [hv.2.le]
    have h_r11 : ∀ v ∈ Ioo r₁ 1, fn v = (v * M.F v ^ (M.n - 1) - ∫ u in r₁..v, M.F u ^ (M.n - 1)) * M.f v := by
      intro v hv; dsimp [fn]; unfold payment
      have ha : alloc M (SPA r₁ hr1_0 hr1_1.le) (effDist M (exclVisit M) (seller0 M)) v = M.F v ^ (M.n - 1) := by
        unfold alloc SPA; dsimp
        simp only [not_lt.mpr hv.1.le, ↓reduceIte]
        rw [hF0_excl v ⟨le_trans hr1_a.le hv.1.le, hv.2.le⟩]
      rw [ha, hs_0_excl v ⟨le_trans hr1_0 hv.1.le, hv.2.le⟩]
      dsimp [exclVisit]; simp [not_le.mpr hv.1]
    have hcontF : ContinuousOn (fun u => M.F u ^ (M.n - 1)) (Icc r₁ 1) :=
      (M.F_continuousOn.mono (Icc_subset_Icc hr1_a.le le_rfl)).pow _
    have hcont_int : ContinuousOn (fun v => ∫ u in r₁..v, M.F u ^ (M.n - 1)) (Icc r₁ 1) :=
      continuousOn_primitive_Icc hr1_1.le hcontF
    have hcont_g : ContinuousOn (fun v => (v * M.F v ^ (M.n - 1) - ∫ u in r₁..v, M.F u ^ (M.n - 1)) * M.f v) (Icc r₁ 1) :=
      ((continuousOn_id.mul hcontF).sub hcont_int).mul (M.hf_cont.mono (Icc_subset_Icc hr1_a.le le_rfl))
    have hi1 : IntervalIntegrable fn volume M.a r₁ :=
      (intervalIntegrable_congr_Ioo hr1_a.le h_ar1).mpr intervalIntegrable_const
    have hi2 : IntervalIntegrable fn volume r₁ 1 :=
      (intervalIntegrable_congr_Ioo hr1_1.le h_r11).mpr (hcont_g.mono (by rw [uIcc_of_le hr1_1.le])).intervalIntegrable
    change 0 < ∫ v in M.a..1, fn v
    rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2,
      intervalIntegral_congr_Ioo hr1_a.le h_ar1, intervalIntegral.integral_zero, zero_add,
      intervalIntegral_congr_Ioo hr1_1.le h_r11]
    have hge : ∀ v ∈ Icc r₁ 1, r₁ * M.F v ^ (M.n - 1) * M.f v ≤
        (v * M.F v ^ (M.n - 1) - ∫ u in r₁..v, M.F u ^ (M.n - 1)) * M.f v := by
      intro v hv
      have hle : ∫ u in r₁..v, M.F u ^ (M.n - 1) ≤ (v - r₁) * M.F v ^ (M.n - 1) := by
        have hc' : ∫ _ in r₁..v, M.F v ^ (M.n - 1) = (v - r₁) * M.F v ^ (M.n - 1) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
        rw [← hc']
        exact intervalIntegral.integral_mono_on hv.1
          ((hcontF.mono (by rw [uIcc_of_le hv.1]; exact Icc_subset_Icc le_rfl hv.2)).intervalIntegrable)
          intervalIntegrable_const fun u hu => pow_le_pow_left₀
            (M.F_mem_Icc ⟨le_trans hr1_a.le hu.1, le_trans hu.2 hv.2⟩).1
            (M.F_strictMonoOn.monotoneOn ⟨le_trans hr1_a.le hu.1, le_trans hu.2 hv.2⟩
              ⟨le_trans hr1_a.le hv.1, hv.2⟩ hu.2) _
      have hfv := (M.hf_pos v ⟨le_trans hr1_a.le hv.1, hv.2⟩).le
      nlinarith
    apply intervalIntegral.integral_pos hr1_1 hcont_g
    · intro v hv
      have h1 := hge v (Ioc_subset_Icc_self hv)
      have h2 : 0 ≤ r₁ * M.F v ^ (M.n - 1) * M.f v := by
        have hF0 := (M.F_mem_Icc ⟨le_trans hr1_a.le hv.1.le, hv.2⟩).1
        have hf0 := (M.hf_pos v ⟨le_trans hr1_a.le hv.1.le, hv.2⟩).le
        positivity
      linarith
    · let vm := (r₁ + 1) / 2
      have hvm_oc : vm ∈ Ioc r₁ 1 := ⟨by dsimp [vm]; linarith, by dsimp [vm]; linarith⟩
      have hFpos : 0 < M.F vm := by
        rw [← M.hF_a]
        exact M.F_strictMonoOn (left_mem_Icc.mpr M.ha1.le) ⟨le_trans hr1_a.le hvm_oc.1.le, hvm_oc.2⟩
          (by dsimp [vm]; linarith)
      have hr1_pos : 0 < r₁ := lt_of_le_of_lt M.ha0 hr1_a
      have hfpos := M.hf_pos vm ⟨le_trans hr1_a.le hvm_oc.1.le, hvm_oc.2⟩
      exact ⟨vm, Ioc_subset_Icc_self hvm_oc, lt_of_lt_of_le (by positivity) (hge vm (Ioc_subset_Icc_self hvm_oc))⟩
  exact ⟨hR1_zero, hSR, hR0_pos⟩

/-- Rival effective distribution below cutoff `w` for a reserve increase from `ρ = 0`:
`F_riv(v; w) = A(w) - (F(w) - F(v)) / (m - 1)`. -/
noncomputable def zeroResFriv (M : Market) (w v : ℝ) : ℝ :=
  M.A w - (M.F w - M.F v) / ((M.m : ℝ) - 1)

/-- Reserve price `r₁(w) ∈ (0, w)` inducing indifference cutoff `w ∈ (0, 1)` against `SPA(0)`. -/
noncomputable def zeroResR1 (M : Market) (w : ℝ) : ℝ :=
  w - (∫ v in (0 : ℝ)..w, zeroResFriv M w v ^ (M.n - 1)) / M.A w ^ (M.n - 1)

/-- Visit strategy for reserve increase `SPA(r₁(w))` against `SPA(0)`:
buyers below `w` split symmetrically among the `m - 1` rivals; buyers at/above `w` split uniformly. -/
noncomputable def zeroResVisit (M : Market) (w : ℝ) : VisitStrategy M where
  θ := fun j v =>
    if v < w then
      if j = seller0 M then 0 else 1 / ((M.m : ℝ) - 1)
    else
      1 / (M.m : ℝ)
  hmeas := fun _ => Measurable.ite measurableSet_Iio measurable_const measurable_const
  hnonneg := fun _ _ => by
    have := M.m_sub_one_pos_real; have := M.m_pos_real
    split_ifs <;> positivity
  hsum := fun v _ => by
    have hcard : (Finset.univ.erase (seller0 M)).card = M.m - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_fin]
    split_ifs with hlt
    · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (seller0 M))]
      simp only [↓reduceIte, zero_add]
      have hconst : ∑ j ∈ Finset.univ.erase (seller0 M),
          (if j = seller0 M then (0 : ℝ) else 1 / ((M.m : ℝ) - 1)) =
          ∑ _ ∈ Finset.univ.erase (seller0 M), (1 / ((M.m : ℝ) - 1)) :=
        Finset.sum_congr rfl fun j hj => by simp [Finset.ne_of_mem_erase hj]
      rw [hconst, Finset.sum_const, hcard, nsmul_eq_mul,
        Nat.cast_sub (by have := M.hm; omega), Nat.cast_one,
        mul_one_div_cancel M.m_sub_one_pos_real.ne']
    · rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_one_div_cancel M.m_pos_real.ne']

lemma zeroRes_sr_and_rev (M : Market) (ha : M.a = 0) {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    0 < zeroResR1 M w ∧ zeroResR1 M w < w ∧
    (∀ (hr0 : 0 ≤ zeroResR1 M w) (hr1 : zeroResR1 M w ≤ 1),
      IsSR M (fun j => if j = seller0 M then SPA (zeroResR1 M w) hr0 hr1 else SPA 0 le_rfl zero_le_one)
        (zeroResVisit M w) ∧
      sellerRev M (SPA (zeroResR1 M w) hr0 hr1) (zeroResVisit M w) (seller0 M) -
        sellerRev M (SPA 0 le_rfl zero_le_one) (unifVisit M) (seller0 M) =
      (M.n : ℝ) * (-(1 - M.A w) * (∫ v in (0 : ℝ)..w, zeroResFriv M w v ^ (M.n - 1)) +
        (∫ v in (0 : ℝ)..w, (1 - M.A v) * M.A v ^ (M.n - 1)) -
        (∫ v in (0 : ℝ)..w, v * M.A v ^ (M.n - 1) * (M.f v / (M.m : ℝ))))) := by
  have hm := M.m_pos_real
  have hm1 := M.m_sub_one_pos_real
  have hm2 : (2 : ℝ) ≤ M.m := by exact_mod_cast M.hm
  have hFw_lt1 : M.F w < 1 := by
    rw [← M.hF_1]; exact M.F_strictMonoOn ⟨by rw [ha]; exact hw.1.le, hw.2.le⟩ (right_mem_Icc.mpr M.ha1.le) hw.2
  have hFriv_pos : ∀ v ∈ Icc (0 : ℝ) w, 0 < zeroResFriv M w v := by
    intro v hv; unfold zeroResFriv Market.A
    have hFv0 : 0 ≤ M.F v := (M.F_mem_Icc ⟨by rw [ha]; exact hv.1, le_trans hv.2 hw.2.le⟩).1
    have h1 : 1 - (1 - M.F w) / (M.m : ℝ) - (M.F w - M.F v) / ((M.m : ℝ) - 1) =
        (((M.m : ℝ) - 1) ^ 2 - M.F w) / ((M.m : ℝ) * ((M.m : ℝ) - 1)) + M.F v / ((M.m : ℝ) - 1) := by
      field_simp [hm.ne', hm1.ne']; ring
    rw [h1]
    have hnum : 0 < ((M.m : ℝ) - 1) ^ 2 - M.F w := by nlinarith
    have h2 : 0 ≤ M.F v / ((M.m : ℝ) - 1) := div_nonneg hFv0 hm1.le
    linarith [div_pos hnum (mul_pos hm hm1)]
  have hFriv_le : ∀ v ∈ Icc (0 : ℝ) w, zeroResFriv M w v ≤ M.A w := by
    intro v hv; unfold zeroResFriv
    have hFle := M.F_strictMonoOn.monotoneOn ⟨by rw [ha]; exact hv.1, le_trans hv.2 hw.2.le⟩
      ⟨by rw [ha]; exact hw.1.le, hw.2.le⟩ hv.2
    have : 0 ≤ (M.F w - M.F v) / ((M.m : ℝ) - 1) := div_nonneg (by linarith) hm1.le
    linarith
  have hFriv_lt : ∀ v ∈ Ioo (0 : ℝ) w, zeroResFriv M w v < M.A w := by
    intro v hv; unfold zeroResFriv
    have hFlt := M.F_strictMonoOn ⟨by rw [ha]; exact hv.1.le, le_trans hv.2.le hw.2.le⟩
      ⟨by rw [ha]; exact hw.1.le, hw.2.le⟩ hv.2
    have : 0 < (M.F w - M.F v) / ((M.m : ℝ) - 1) := div_pos (by linarith) hm1
    linarith
  have hcontFriv : ContinuousOn (fun v => zeroResFriv M w v ^ (M.n - 1)) (Icc 0 w) := by
    have hF_sub := M.F_continuousOn.mono (Icc_subset_Icc (by rw [ha]) hw.2.le)
    unfold zeroResFriv; fun_prop
  have hAw_pos : 0 < M.A w := M.br_A_pos ⟨by rw [ha]; exact hw.1.le, hw.2.le⟩
  have hint_pos : 0 < ∫ v in (0 : ℝ)..w, zeroResFriv M w v ^ (M.n - 1) := by
    apply intervalIntegral.integral_pos hw.1 hcontFriv
    · intro v hv; exact pow_nonneg (hFriv_pos v (Ioc_subset_Icc_self hv)).le _
    · exact ⟨w / 2, ⟨by linarith [hw.1], by linarith [hw.1]⟩,
        pow_pos (hFriv_pos (w / 2) ⟨by linarith [hw.1], by linarith [hw.1]⟩) _⟩
  have hint_lt : ∫ v in (0 : ℝ)..w, zeroResFriv M w v ^ (M.n - 1) < w * M.A w ^ (M.n - 1) := by
    have hconst : ∫ _ in (0 : ℝ)..w, M.A w ^ (M.n - 1) = w * M.A w ^ (M.n - 1) := by
      rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    rw [← hconst, ← sub_pos, ← intervalIntegral.integral_sub intervalIntegrable_const
      (hcontFriv.mono (by rw [uIcc_of_le hw.1.le])).intervalIntegrable]
    apply intervalIntegral.integral_pos hw.1 (continuousOn_const.sub hcontFriv)
    · intro v hv
      exact sub_nonneg.mpr (pow_le_pow_left₀ (hFriv_pos v (Ioc_subset_Icc_self hv)).le
        (hFriv_le v (Ioc_subset_Icc_self hv)) _)
    · exact ⟨w / 2, ⟨by linarith [hw.1], by linarith [hw.1]⟩,
        sub_pos.mpr (pow_lt_pow_left₀ (hFriv_lt (w / 2) ⟨by linarith [hw.1], by linarith [hw.1]⟩)
          (hFriv_pos (w / 2) ⟨by linarith [hw.1], by linarith [hw.1]⟩).le M.n_sub_one_ne_zero)⟩
  have hr1_pos : 0 < zeroResR1 M w := by
    unfold zeroResR1
    have : (∫ v in (0 : ℝ)..w, zeroResFriv M w v ^ (M.n - 1)) / M.A w ^ (M.n - 1) < w :=
      (div_lt_iff₀ (pow_pos hAw_pos _)).mpr hint_lt
    linarith
  have hr1_lt_w : zeroResR1 M w < w := by
    unfold zeroResR1
    have : 0 < (∫ v in (0 : ℝ)..w, zeroResFriv M w v ^ (M.n - 1)) / M.A w ^ (M.n - 1) :=
      div_pos hint_pos (pow_pos hAw_pos _)
    linarith
  refine ⟨hr1_pos, hr1_lt_w, fun hr0 hr1 => ?_⟩
  set r₁ := zeroResR1 M w
  set θ := zeroResVisit M w
  have hf_int : ∀ x y, 0 ≤ x → x ≤ y → y ≤ 1 → IntervalIntegrable M.f volume x y :=
    fun x y hx hxy hy => (M.hf_cont.mono (by rw [uIcc_of_le hxy]; exact Icc_subset_Icc (by rw [ha]; exact hx) hy)).intervalIntegrable
  have hF0 : ∀ v ∈ Icc (0 : ℝ) 1, effDist M θ (seller0 M) v = if v ≤ w then M.A w else M.A v := by
    intro v hv; unfold effDist
    have htop : ∀ x, w ≤ x → x ≤ 1 →
        IntervalIntegrable (fun u => θ.θ (seller0 M) u * M.f u) volume x 1 ∧
        ∫ u in x..1, θ.θ (seller0 M) u * M.f u = (1 - M.F x) / (M.m : ℝ) := by
      intro x hwx hx1
      have hc : ∀ u ∈ Ioo x 1, θ.θ (seller0 M) u * M.f u = (1 / (M.m : ℝ)) * M.f u := by
        intro u hu; dsimp [θ]; unfold zeroResVisit; dsimp; simp [not_lt.mpr (le_trans hwx hu.1.le)]
      refine ⟨(intervalIntegrable_congr_Ioo hx1 hc).mpr ((hf_int x 1 (le_trans hw.1.le hwx) hx1 le_rfl).const_mul _), ?_⟩
      rw [intervalIntegral_congr_Ioo hx1 hc, intervalIntegral.integral_const_mul,
        ← M.F_sub_eq_integral (by rw [ha]; exact le_trans hw.1.le hwx) hx1 le_rfl, M.hF_1]; ring
    split_ifs with hvw
    · have hc : ∀ u ∈ Ioo v w, θ.θ (seller0 M) u * M.f u = 0 := by
        intro u hu; dsimp [θ]; unfold zeroResVisit; dsimp; simp [hu.2]
      have hi : IntervalIntegrable (fun u => θ.θ (seller0 M) u * M.f u) volume v w :=
        (intervalIntegrable_congr_Ioo hvw hc).mpr intervalIntegrable_const
      rw [← intervalIntegral.integral_add_adjacent_intervals hi (htop w le_rfl hw.2.le).1,
        intervalIntegral_congr_Ioo hvw hc, intervalIntegral.integral_zero, zero_add, (htop w le_rfl hw.2.le).2]
      rfl
    · push Not at hvw; rw [(htop v hvw.le hv.2).2]; rfl
  have hFj : ∀ (j : Fin M.m), j ≠ seller0 M → ∀ v ∈ Icc (0 : ℝ) 1,
      effDist M θ j v = if v ≤ w then zeroResFriv M w v else M.A v := by
    intro j hj v hv; unfold effDist
    have htop : ∀ x, w ≤ x → x ≤ 1 →
        IntervalIntegrable (fun u => θ.θ j u * M.f u) volume x 1 ∧
        ∫ u in x..1, θ.θ j u * M.f u = (1 - M.F x) / (M.m : ℝ) := by
      intro x hwx hx1
      have hc : ∀ u ∈ Ioo x 1, θ.θ j u * M.f u = (1 / (M.m : ℝ)) * M.f u := by
        intro u hu; dsimp [θ]; unfold zeroResVisit; dsimp; simp [not_lt.mpr (le_trans hwx hu.1.le)]
      refine ⟨(intervalIntegrable_congr_Ioo hx1 hc).mpr ((hf_int x 1 (le_trans hw.1.le hwx) hx1 le_rfl).const_mul _), ?_⟩
      rw [intervalIntegral_congr_Ioo hx1 hc, intervalIntegral.integral_const_mul,
        ← M.F_sub_eq_integral (by rw [ha]; exact le_trans hw.1.le hwx) hx1 le_rfl, M.hF_1]; ring
    split_ifs with hvw
    · have hc : ∀ u ∈ Ioo v w, θ.θ j u * M.f u = (1 / ((M.m : ℝ) - 1)) * M.f u := by
        intro u hu; dsimp [θ]; unfold zeroResVisit; dsimp; simp [hu.2, hj]
      have hi : IntervalIntegrable (fun u => θ.θ j u * M.f u) volume v w :=
        (intervalIntegrable_congr_Ioo hvw hc).mpr ((hf_int v w hv.1 hvw hw.2.le).const_mul _)
      rw [← intervalIntegral.integral_add_adjacent_intervals hi (htop w le_rfl hw.2.le).1,
        intervalIntegral_congr_Ioo hvw hc, intervalIntegral.integral_const_mul,
        ← M.F_sub_eq_integral (by rw [ha]; exact hv.1) hvw hw.2.le, (htop w le_rfl hw.2.le).2]
      unfold zeroResFriv Market.A; ring
    · push Not at hvw; rw [(htop v hvw.le hv.2).2]; rfl
  have hcontA : ContinuousOn (fun u => M.A u ^ (M.n - 1)) (Icc 0 1) :=
    (M.A_continuousOn.mono (by rw [ha])).pow _
  have hs0 : ∀ v ∈ Icc (0 : ℝ) 1,
      surplus M (SPA r₁ hr0 hr1) (effDist M θ (seller0 M)) v =
        if v ≤ r₁ then 0
        else if v ≤ w then (v - r₁) * M.A w ^ (M.n - 1)
        else (w - r₁) * M.A w ^ (M.n - 1) + ∫ u in w..v, M.A u ^ (M.n - 1) := by
    intro v hv; unfold surplus
    have ha0 : ∀ u ∈ Ioo (0 : ℝ) r₁, alloc M (SPA r₁ hr0 hr1) (effDist M θ (seller0 M)) u = 0 := by
      intro u hu; unfold alloc SPA; dsimp; simp [hu.2]
    have ha1 : ∀ u ∈ Ioo r₁ w, alloc M (SPA r₁ hr0 hr1) (effDist M θ (seller0 M)) u = M.A w ^ (M.n - 1) := by
      intro u hu; unfold alloc SPA; dsimp
      simp only [not_lt.mpr hu.1.le, ↓reduceIte]
      rw [hF0 u ⟨le_trans hr0 hu.1.le, le_trans hu.2.le hw.2.le⟩]; simp [hu.2.le]
    have ha2 : ∀ u ∈ Ioo w 1, alloc M (SPA r₁ hr0 hr1) (effDist M θ (seller0 M)) u = M.A u ^ (M.n - 1) := by
      intro u hu; unfold alloc SPA; dsimp
      simp only [not_lt.mpr (le_trans hr1_lt_w.le hu.1.le), ↓reduceIte]
      rw [hF0 u ⟨le_trans hw.1.le hu.1.le, hu.2.le⟩]; simp [not_le.mpr hu.1]
    have hi0 : IntervalIntegrable (alloc M (SPA r₁ hr0 hr1) (effDist M θ (seller0 M))) volume 0 r₁ :=
      (intervalIntegrable_congr_Ioo hr0 ha0).mpr intervalIntegrable_const
    split_ifs with hvr hvw
    · rw [intervalIntegral_congr_Ioo hv.1 (g := fun _ => (0 : ℝ)) (fun u hu => ha0 u ⟨hu.1, lt_of_lt_of_le hu.2 hvr⟩)]
      simp
    · push Not at hvr
      have hi1 : IntervalIntegrable (alloc M (SPA r₁ hr0 hr1) (effDist M θ (seller0 M))) volume r₁ v :=
        (intervalIntegrable_congr_Ioo hvr.le (fun u hu => ha1 u ⟨hu.1, lt_of_lt_of_le hu.2 hvw⟩)).mpr intervalIntegrable_const
      rw [← intervalIntegral.integral_add_adjacent_intervals hi0 hi1,
        intervalIntegral_congr_Ioo hr0 ha0, intervalIntegral.integral_zero, zero_add,
        intervalIntegral_congr_Ioo hvr.le (fun u hu => ha1 u ⟨hu.1, lt_of_lt_of_le hu.2 hvw⟩),
        intervalIntegral.integral_const, smul_eq_mul]
    · push Not at hvr hvw
      have hi1 : IntervalIntegrable (alloc M (SPA r₁ hr0 hr1) (effDist M θ (seller0 M))) volume r₁ w :=
        (intervalIntegrable_congr_Ioo hr1_lt_w.le ha1).mpr intervalIntegrable_const
      have hi2 : IntervalIntegrable (alloc M (SPA r₁ hr0 hr1) (effDist M θ (seller0 M))) volume w v :=
        (intervalIntegrable_congr_Ioo hvw.le (fun u hu => ha2 u ⟨hu.1, lt_of_lt_of_le hu.2 hv.2⟩)).mpr
          ((hcontA.mono (by rw [uIcc_of_le hvw.le]; exact Icc_subset_Icc hw.1.le hv.2)).intervalIntegrable)
      rw [← intervalIntegral.integral_add_adjacent_intervals (hi0.trans hi1) hi2,
        ← intervalIntegral.integral_add_adjacent_intervals hi0 hi1,
        intervalIntegral_congr_Ioo hr0 ha0, intervalIntegral.integral_zero, zero_add,
        intervalIntegral_congr_Ioo hr1_lt_w.le ha1, intervalIntegral.integral_const, smul_eq_mul,
        intervalIntegral_congr_Ioo hvw.le (fun u hu => ha2 u ⟨hu.1, lt_of_lt_of_le hu.2 hv.2⟩)]
  have hsj : ∀ (j : Fin M.m), j ≠ seller0 M → ∀ v ∈ Icc (0 : ℝ) 1,
      surplus M (SPA 0 le_rfl zero_le_one) (effDist M θ j) v =
        if v ≤ w then ∫ u in (0 : ℝ)..v, zeroResFriv M w u ^ (M.n - 1)
        else (∫ u in (0 : ℝ)..w, zeroResFriv M w u ^ (M.n - 1)) + ∫ u in w..v, M.A u ^ (M.n - 1) := by
    intro j hj v hv; unfold surplus
    have ha1 : ∀ u ∈ Ioo (0 : ℝ) w, alloc M (SPA 0 le_rfl zero_le_one) (effDist M θ j) u = zeroResFriv M w u ^ (M.n - 1) := by
      intro u hu; unfold alloc SPA; dsimp
      simp only [not_lt.mpr hu.1.le, ↓reduceIte]
      rw [hFj j hj u ⟨hu.1.le, le_trans hu.2.le hw.2.le⟩]; simp [hu.2.le]
    have ha2 : ∀ u ∈ Ioo w 1, alloc M (SPA 0 le_rfl zero_le_one) (effDist M θ j) u = M.A u ^ (M.n - 1) := by
      intro u hu; unfold alloc SPA; dsimp
      simp only [not_lt.mpr (le_trans hw.1.le hu.1.le), ↓reduceIte]
      rw [hFj j hj u ⟨le_trans hw.1.le hu.1.le, hu.2.le⟩]; simp [not_le.mpr hu.1]
    split_ifs with hvw
    · exact intervalIntegral_congr_Ioo hv.1 (fun u hu => ha1 u ⟨hu.1, lt_of_lt_of_le hu.2 hvw⟩)
    · push Not at hvw
      have hi1 : IntervalIntegrable (alloc M (SPA 0 le_rfl zero_le_one) (effDist M θ j)) volume 0 w :=
        (intervalIntegrable_congr_Ioo hw.1.le ha1).mpr (hcontFriv.mono (by rw [uIcc_of_le hw.1.le])).intervalIntegrable
      have hi2 : IntervalIntegrable (alloc M (SPA 0 le_rfl zero_le_one) (effDist M θ j)) volume w v :=
        (intervalIntegrable_congr_Ioo hvw.le (fun u hu => ha2 u ⟨hu.1, lt_of_lt_of_le hu.2 hv.2⟩)).mpr
          ((hcontA.mono (by rw [uIcc_of_le hvw.le]; exact Icc_subset_Icc hw.1.le hv.2)).intervalIntegrable)
      rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2,
        intervalIntegral_congr_Ioo hw.1.le ha1,
        intervalIntegral_congr_Ioo hvw.le (fun u hu => ha2 u ⟨hu.1, lt_of_lt_of_le hu.2 hv.2⟩)]
  have hbal : (w - r₁) * M.A w ^ (M.n - 1) = ∫ u in (0 : ℝ)..w, zeroResFriv M w u ^ (M.n - 1) := by
    dsimp [r₁]; unfold zeroResR1
    have h1 : w - (w - (∫ v in (0 : ℝ)..w, zeroResFriv M w v ^ (M.n - 1)) / M.A w ^ (M.n - 1)) =
        (∫ v in (0 : ℝ)..w, zeroResFriv M w v ^ (M.n - 1)) / M.A w ^ (M.n - 1) := by ring
    rw [h1, div_mul_cancel₀ _ (pow_pos hAw_pos _).ne']
  have hSR : IsSR M (fun j => if j = seller0 M then SPA r₁ hr0 hr1 else SPA 0 le_rfl zero_le_one) θ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv j k hjpos
    have hv01 : v ∈ Icc (0 : ℝ) 1 := by rwa [ha] at hv
    have hle_0j : ∀ j' : Fin M.m, j' ≠ seller0 M →
        surplus M (SPA r₁ hr0 hr1) (effDist M θ (seller0 M)) v ≤
          surplus M (SPA 0 le_rfl zero_le_one) (effDist M θ j') v := by
      intro j' hj'
      rw [hs0 v hv01, hsj j' hj' v hv01]
      split_ifs with hvr hvw1 hvw2
      · exact intervalIntegral.integral_nonneg hv01.1 (fun u hu => pow_nonneg (hFriv_pos u ⟨hu.1, le_trans hu.2 hvw1⟩).le _)
      · linarith [hvr, hr1_lt_w]
      · push Not at hvr
        have hi1 : IntervalIntegrable (fun u => zeroResFriv M w u ^ (M.n - 1)) volume 0 v :=
          (hcontFriv.mono (by rw [uIcc_of_le hv01.1]; exact Icc_subset_Icc le_rfl hvw2)).intervalIntegrable
        have hi2 : IntervalIntegrable (fun u => zeroResFriv M w u ^ (M.n - 1)) volume v w :=
          (hcontFriv.mono (by rw [uIcc_of_le hvw2]; exact Icc_subset_Icc hv01.1 le_rfl)).intervalIntegrable
        have hsp := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
        have hvw_le : ∫ u in v..w, zeroResFriv M w u ^ (M.n - 1) ≤ (w - v) * M.A w ^ (M.n - 1) := by
          have hc' : ∫ _ in v..w, M.A w ^ (M.n - 1) = (w - v) * M.A w ^ (M.n - 1) := by
            rw [intervalIntegral.integral_const, smul_eq_mul]
          rw [← hc']
          exact intervalIntegral.integral_mono_on hvw2 hi2 intervalIntegrable_const
            (fun u hu => pow_le_pow_left₀ (hFriv_pos u ⟨le_trans hv01.1 hu.1, hu.2⟩).le
              (hFriv_le u ⟨le_trans hv01.1 hu.1, hu.2⟩) _)
        linarith
      · push Not at hvr hvw2; linarith
    have heq_0j : ∀ j' : Fin M.m, j' ≠ seller0 M → w ≤ v →
        surplus M (SPA r₁ hr0 hr1) (effDist M θ (seller0 M)) v =
          surplus M (SPA 0 le_rfl zero_le_one) (effDist M θ j') v := by
      intro j' hj' hvw
      rw [hs0 v hv01, hsj j' hj' v hv01]
      by_cases hveq : v = w
      · subst hveq; simp [not_le.mpr hr1_lt_w, hbal]
      · have hgt : w < v := lt_of_le_of_ne hvw (Ne.symm hveq)
        simp only [not_le.mpr (lt_trans hr1_lt_w hgt), not_le.mpr hgt, ↓reduceIte]; linarith
    by_cases hj0 : j = seller0 M
    · subst hj0
      have hwv : w ≤ v := by
        by_contra hlt; push Not at hlt
        have : θ.θ (seller0 M) v = 0 := by dsimp [θ]; unfold zeroResVisit; dsimp; simp [hlt]
        linarith
      by_cases hk0 : k = seller0 M
      · subst hk0; exact le_rfl
      · simp only [↓reduceIte, hk0]; exact (heq_0j k hk0 hwv).symm.le
    · by_cases hk0 : k = seller0 M
      · subst hk0; simp only [↓reduceIte, hj0]; exact hle_0j j hj0
      · simp only [hj0, hk0, ↓reduceIte, hsj j hj0 v hv01, hsj k hk0 v hv01]; exact le_rfl
  have hrev_diff : sellerRev M (SPA r₁ hr0 hr1) θ (seller0 M) -
      sellerRev M (SPA 0 le_rfl zero_le_one) (unifVisit M) (seller0 M) =
      (M.n : ℝ) * (-(1 - M.A w) * (∫ v in (0 : ℝ)..w, zeroResFriv M w v ^ (M.n - 1)) +
        (∫ v in (0 : ℝ)..w, (1 - M.A v) * M.A v ^ (M.n - 1)) -
        (∫ v in (0 : ℝ)..w, v * M.A v ^ (M.n - 1) * (M.f v / (M.m : ℝ)))) := by
    set s_unif : ℝ → ℝ := fun v => ∫ u in (0 : ℝ)..v, M.A u ^ (M.n - 1)
    set s_w : ℝ := ∫ u in (0 : ℝ)..w, zeroResFriv M w u ^ (M.n - 1)
    set t₀ := 1 - M.A w
    have hcont_s_top : ContinuousOn (fun v => ∫ u in w..v, M.A u ^ (M.n - 1)) (Icc w 1) :=
      continuousOn_primitive_Icc hw.2.le (hcontA.mono (Icc_subset_Icc hw.1.le le_rfl))
    have hcont_s_unif : ContinuousOn s_unif (Icc 0 1) := continuousOn_primitive_Icc zero_le_one hcontA
    let g_top : ℝ → ℝ := fun v => (v * M.A v ^ (M.n - 1) - ∫ u in w..v, M.A u ^ (M.n - 1)) * (1 / (M.m : ℝ)) * M.f v
    have hg_top_int : IntervalIntegrable g_top volume w 1 := by
      have hcont : ContinuousOn g_top (Icc w 1) :=
        (((continuousOn_id.mul (hcontA.mono (Icc_subset_Icc hw.1.le le_rfl))).sub hcont_s_top).mul
          continuousOn_const).mul (M.hf_cont.mono (Icc_subset_Icc (by rw [ha]; exact hw.1.le) le_rfl))
      exact (hcont.mono (by rw [uIcc_of_le hw.2.le])).intervalIntegrable
    have hf_top_int : IntervalIntegrable (fun v => (1 / (M.m : ℝ)) * M.f v) volume w 1 :=
      (hf_int w 1 hw.1.le hw.2.le le_rfl).const_mul _
    have hI_top : ∫ v in w..1, (1 / (M.m : ℝ)) * M.f v = t₀ := by
      rw [intervalIntegral.integral_const_mul, ← M.F_sub_eq_integral (by rw [ha]; exact hw.1.le) hw.2.le le_rfl, M.hF_1]
      dsimp [t₀]; unfold Market.A; ring
    have hR_dev : sellerRev M (SPA r₁ hr0 hr1) θ (seller0 M) =
        (M.n : ℝ) * ((∫ v in w..1, g_top v) - s_w * t₀) := by
      unfold sellerRev; rw [ha]; congr 1
      let fn : ℝ → ℝ := fun v => payment M (SPA r₁ hr0 hr1) (effDist M θ (seller0 M)) v * θ.θ (seller0 M) v * M.f v
      have h_0w : ∀ v ∈ Ioo (0 : ℝ) w, fn v = 0 := by
        intro v hv; dsimp [fn, θ]; unfold zeroResVisit; dsimp; simp [hv.2]
      have h_w1 : ∀ v ∈ Ioo w 1, fn v = g_top v - s_w * ((1 / (M.m : ℝ)) * M.f v) := by
        intro v hv; dsimp [fn, g_top]; unfold payment
        have hθ1 : θ.θ (seller0 M) v = 1 / (M.m : ℝ) := by
          dsimp [θ]; unfold zeroResVisit; dsimp; simp [not_lt.mpr hv.1.le]
        have hall : alloc M (SPA r₁ hr0 hr1) (effDist M θ (seller0 M)) v = M.A v ^ (M.n - 1) := by
          unfold alloc SPA; dsimp
          simp only [not_lt.mpr (le_trans hr1_lt_w.le hv.1.le), ↓reduceIte]
          rw [hF0 v ⟨le_trans hw.1.le hv.1.le, hv.2.le⟩]; simp [not_le.mpr hv.1]
        rw [hθ1, hall, hs0 v ⟨le_trans hw.1.le hv.1.le, hv.2.le⟩]
        simp only [not_le.mpr (lt_trans hr1_lt_w hv.1), not_le.mpr hv.1, ↓reduceIte, hbal]; ring
      have hi1 : IntervalIntegrable fn volume 0 w := (intervalIntegrable_congr_Ioo hw.1.le h_0w).mpr intervalIntegrable_const
      have hi2 : IntervalIntegrable fn volume w 1 := (intervalIntegrable_congr_Ioo hw.2.le h_w1).mpr (hg_top_int.sub (hf_top_int.const_mul _))
      change ∫ v in (0 : ℝ)..1, fn v = _
      rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2,
        intervalIntegral_congr_Ioo hw.1.le h_0w, intervalIntegral.integral_zero, zero_add,
        intervalIntegral_congr_Ioo hw.2.le h_w1, intervalIntegral.integral_sub hg_top_int (hf_top_int.const_mul _),
        intervalIntegral.integral_const_mul, hI_top]
    have hR_unif : sellerRev M (SPA 0 le_rfl zero_le_one) (unifVisit M) (seller0 M) =
        (M.n : ℝ) * ((∫ v in (0 : ℝ)..w, (v * M.A v ^ (M.n - 1) - s_unif v) * (M.f v / (M.m : ℝ))) +
          (∫ v in w..1, g_top v) - s_unif w * t₀) := by
      unfold sellerRev; rw [ha]; congr 1
      let fn : ℝ → ℝ := fun v => payment M (SPA 0 le_rfl zero_le_one) (effDist M (unifVisit M) (seller0 M)) v *
        (unifVisit M).θ (seller0 M) v * M.f v
      have h_0w : ∀ v ∈ Ioo (0 : ℝ) w, fn v = (v * M.A v ^ (M.n - 1) - s_unif v) * (M.f v / (M.m : ℝ)) := by
        intro v hv; dsimp [fn]; unfold payment
        rw [alloc_SPA_unif M le_rfl zero_le_one (by rw [ha]) (seller0 M) (le_trans hv.2.le hw.2.le),
          surplus_SPA_unif M le_rfl zero_le_one (by rw [ha]) (seller0 M) hv.1.le (le_trans hv.2.le hw.2.le)]
        simp only [not_lt.mpr hv.1.le, not_le.mpr hv.1, ↓reduceIte]; dsimp [unifVisit, s_unif]; ring
      have h_w1 : ∀ v ∈ Ioo w 1, fn v = g_top v - s_unif w * ((1 / (M.m : ℝ)) * M.f v) := by
        intro v hv; dsimp [fn, g_top]; unfold payment
        rw [alloc_SPA_unif M le_rfl zero_le_one (by rw [ha]) (seller0 M) hv.2.le,
          surplus_SPA_unif M le_rfl zero_le_one (by rw [ha]) (seller0 M) (le_trans hw.1.le hv.1.le) hv.2.le]
        simp only [not_lt.mpr (le_trans hw.1.le hv.1.le), not_le.mpr (lt_trans hw.1 hv.1), ↓reduceIte]
        have hsp : ∫ u in (0 : ℝ)..v, M.A u ^ (M.n - 1) = s_unif w + ∫ u in w..v, M.A u ^ (M.n - 1) := by
          dsimp [s_unif]
          exact (intervalIntegral.integral_add_adjacent_intervals
            ((hcontA.mono (by rw [uIcc_of_le hw.1.le]; exact Icc_subset_Icc le_rfl hw.2.le)).intervalIntegrable)
            ((hcontA.mono (by rw [uIcc_of_le hv.1.le]; exact Icc_subset_Icc hw.1.le hv.2.le)).intervalIntegrable)).symm
        rw [hsp]; dsimp [unifVisit]; ring
      have hcont_mid : ContinuousOn (fun v => (v * M.A v ^ (M.n - 1) - s_unif v) * (M.f v / (M.m : ℝ))) (Icc 0 w) :=
        ((continuousOn_id.mul (hcontA.mono (Icc_subset_Icc le_rfl hw.2.le))).sub
          (hcont_s_unif.mono (Icc_subset_Icc le_rfl hw.2.le))).mul
          ((M.hf_cont.mono (Icc_subset_Icc (by rw [ha]) hw.2.le)).div_const _)
      have hi1 : IntervalIntegrable fn volume 0 w :=
        (intervalIntegrable_congr_Ioo hw.1.le h_0w).mpr (hcont_mid.mono (by rw [uIcc_of_le hw.1.le])).intervalIntegrable
      have hi2 : IntervalIntegrable fn volume w 1 :=
        (intervalIntegrable_congr_Ioo hw.2.le h_w1).mpr (hg_top_int.sub (hf_top_int.const_mul _))
      change ∫ v in (0 : ℝ)..1, fn v = _
      rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2,
        intervalIntegral_congr_Ioo hw.1.le h_0w,
        intervalIntegral_congr_Ioo hw.2.le h_w1, intervalIntegral.integral_sub hg_top_int (hf_top_int.const_mul _),
        intervalIntegral.integral_const_mul, hI_top]
      ring
    have hIBP : s_unif w * t₀ + ∫ v in (0 : ℝ)..w, s_unif v * (M.f v / (M.m : ℝ)) =
        ∫ v in (0 : ℝ)..w, (1 - M.A v) * M.A v ^ (M.n - 1) := by
      have hs_deriv : ∀ v ∈ Ioo (0 : ℝ) w, HasDerivAt s_unif (M.A v ^ (M.n - 1)) v :=
        fun v hv => integral_hasDerivAt_right_of_continuousOn (hcontA.mono (Icc_subset_Icc le_rfl hw.2.le)) hv
      have h1A_deriv : ∀ v ∈ Ioo (0 : ℝ) w, HasDerivAt (fun v => 1 - M.A v) (-(M.f v / (M.m : ℝ))) v := by
        intro v hv
        have := (hasDerivAt_const v (1 : ℝ)).sub (M.A_deriv_open ⟨by rw [ha]; exact hv.1, lt_trans hv.2 hw.2⟩)
        convert this using 1; ring
      have h1A_cont : ContinuousOn (fun v => 1 - M.A v) (Icc 0 w) :=
        continuousOn_const.sub (M.A_continuousOn.mono (Icc_subset_Icc (by rw [ha]) hw.2.le))
      have hibp := ibp_of_hasDerivAt_of_le hw.1.le h1A_cont
        (hcont_s_unif.mono (Icc_subset_Icc le_rfl hw.2.le))
        h1A_deriv hs_deriv
        ((((M.hf_cont.mono (Icc_subset_Icc (by rw [ha]) hw.2.le)).div_const _).neg.mul
          (hcont_s_unif.mono (Icc_subset_Icc le_rfl hw.2.le))).mono (by rw [uIcc_of_le hw.1.le])).intervalIntegrable
        ((h1A_cont.mul (hcontA.mono (Icc_subset_Icc le_rfl hw.2.le))).mono (by rw [uIcc_of_le hw.1.le])).intervalIntegrable
      have hs0' : s_unif 0 = 0 := intervalIntegral.integral_same
      have hneg : ∫ x in (0 : ℝ)..w, -(M.f x / (M.m : ℝ)) * s_unif x =
          -(∫ x in (0 : ℝ)..w, s_unif x * (M.f x / (M.m : ℝ))) := by
        have heq : (fun x => -(M.f x / (M.m : ℝ)) * s_unif x) = fun x => -(s_unif x * (M.f x / (M.m : ℝ))) := by
          ext x; ring
        rw [heq, intervalIntegral.integral_neg]
      rw [hs0', mul_zero, sub_zero, hneg] at hibp
      dsimp [t₀]; linarith only [hibp]
    have hsplit_u : ∫ v in (0 : ℝ)..w, (v * M.A v ^ (M.n - 1) - s_unif v) * (M.f v / (M.m : ℝ)) =
        (∫ v in (0 : ℝ)..w, v * M.A v ^ (M.n - 1) * (M.f v / (M.m : ℝ))) -
        (∫ v in (0 : ℝ)..w, s_unif v * (M.f v / (M.m : ℝ))) := by
      have hi1 : IntervalIntegrable (fun v => v * M.A v ^ (M.n - 1) * (M.f v / (M.m : ℝ))) volume 0 w :=
        (((continuousOn_id.mul (hcontA.mono (Icc_subset_Icc le_rfl hw.2.le))).mul
          ((M.hf_cont.mono (Icc_subset_Icc (by rw [ha]) hw.2.le)).div_const _)).mono (by rw [uIcc_of_le hw.1.le])).intervalIntegrable
      have hi2 : IntervalIntegrable (fun v => s_unif v * (M.f v / (M.m : ℝ))) volume 0 w :=
        (((hcont_s_unif.mono (Icc_subset_Icc le_rfl hw.2.le)).mul
          ((M.hf_cont.mono (Icc_subset_Icc (by rw [ha]) hw.2.le)).div_const _)).mono (by rw [uIcc_of_le hw.1.le])).intervalIntegrable
      have heq : (fun v => (v * M.A v ^ (M.n - 1) - s_unif v) * (M.f v / (M.m : ℝ))) =
          fun v => v * M.A v ^ (M.n - 1) * (M.f v / (M.m : ℝ)) - s_unif v * (M.f v / (M.m : ℝ)) := by ext v; ring
      rw [heq, intervalIntegral.integral_sub hi1 hi2]
    rw [hR_dev, hR_unif, hsplit_u]
    linear_combination (M.n : ℝ) * hIBP
  exact ⟨hSR, hrev_diff⟩

/-- Pointwise Taylor lower bound for the `a = ρ = 0` reserve-increase integrand. -/
lemma zeroRes_integrand_lower (M : Market) (ha : M.a = 0) {fmax Cp w : ℝ}
    (hfmax : 0 < fmax) (hf_hi : ∀ v ∈ Icc M.a 1, M.f v ≤ fmax)
    (hCp : 0 ≤ Cp)
    (hpow : ∀ h : ℝ, |h| ≤ 1 →
      |((1 - 1 / (M.m : ℝ)) + h) ^ (M.n - 1) - (1 - 1 / (M.m : ℝ)) ^ (M.n - 1) -
        ((M.n - 1 : ℕ) : ℝ) * (1 - 1 / (M.m : ℝ)) ^ (M.n - 1 - 1) * h| ≤ Cp * h ^ 2)
    (hw_pos : 0 < w) (hw_lt1 : w < 1) (hfw_le1 : fmax * w ≤ 1)
    (hF_le : ∀ v ∈ Icc (0 : ℝ) w, 0 ≤ M.F v ∧ M.F v ≤ fmax * w) :
    let A₀ := 1 - 1 / (M.m : ℝ)
    let C_err := Cp * fmax ^ 2 / ((M.m : ℝ) - 1) ^ 2 + Cp * fmax ^ 2 / (M.m : ℝ) ^ 2 +
      ((M.n : ℝ) - 1) * fmax ^ 2 / ((M.m : ℝ) * ((M.m : ℝ) - 1)) +
      2 * ((M.n : ℝ) - 1) * fmax ^ 2 / (M.m : ℝ) ^ 2 + Cp * fmax ^ 3 / (M.m : ℝ) ^ 3
    ∀ v ∈ Icc (0 : ℝ) w,
      ((M.n : ℝ) - 1) * A₀ ^ (M.n - 2) / ((M.m : ℝ) ^ 2 * ((M.m : ℝ) - 1)) * (M.F w - M.F v) - C_err * w ^ 2 ≤
      -(1 - M.A w) * (zeroResFriv M w v ^ (M.n - 1) - A₀ ^ (M.n - 1)) +
      (1 - M.A v) * (M.A v ^ (M.n - 1) - A₀ ^ (M.n - 1)) -
      v * (M.A v ^ (M.n - 1) - A₀ ^ (M.n - 1)) * (M.f v / (M.m : ℝ)) := by
  intro A₀ C_err v hv
  have hm := M.m_pos_real
  have hm1 := M.m_sub_one_pos_real
  have hm2 : (2 : ℝ) ≤ M.m := by exact_mod_cast M.hm
  have hn1 := M.n_sub_one_pos_real
  have hA₀_pos : 0 < A₀ := by
    have : 1 / (M.m : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hm2; linarith
  have hA₀_le1 : A₀ ≤ 1 := by dsimp [A₀]; linarith only [div_pos one_pos hm]
  have hcast : ((M.n - 1 : ℕ) : ℝ) = (M.n : ℝ) - 1 := by
    rw [Nat.cast_sub (by have := M.hn; omega), Nat.cast_one]
  have hsub : M.n - 1 - 1 = M.n - 2 := by omega
  have h1A_eq : ∀ u, 1 - M.A u = 1 / (M.m : ℝ) - M.F u / (M.m : ℝ) := fun u => by unfold Market.A; ring
  have hFriv_diff : zeroResFriv M w v - A₀ = (M.F v - M.F w / (M.m : ℝ)) / ((M.m : ℝ) - 1) := by
    unfold zeroResFriv Market.A; dsimp [A₀]; field_simp [hm.ne', hm1.ne']; ring
  have hA_diff : M.A v - A₀ = M.F v / (M.m : ℝ) := by unfold Market.A; dsimp [A₀]; ring
  have hFv := hF_le v hv
  have hFw := hF_le w (right_mem_Icc.mpr hw_pos.le)
  let δF := zeroResFriv M w v ^ (M.n - 1) - A₀ ^ (M.n - 1)
  let δA := M.A v ^ (M.n - 1) - A₀ ^ (M.n - 1)
  let hF := zeroResFriv M w v - A₀
  let hA := M.A v - A₀
  have hhF_le : |hF| ≤ fmax * w / ((M.m : ℝ) - 1) := by
    dsimp [hF]; rw [hFriv_diff, abs_div, abs_of_pos hm1]
    apply div_le_div_of_nonneg_right _ hm1.le
    rw [abs_le]
    have h1 : 0 ≤ M.F w / (M.m : ℝ) := div_nonneg hFw.1 hm.le
    have h2 : M.F w / (M.m : ℝ) ≤ M.F w := div_le_self hFw.1 (by linarith only [hm2])
    constructor <;> linarith only [hFv.1, hFv.2, hFw.1, hFw.2, h1, h2]
  have hhA_le : |hA| ≤ fmax * w / (M.m : ℝ) := by
    dsimp [hA]; rw [hA_diff, abs_div, abs_of_pos hm, abs_of_nonneg hFv.1]
    exact div_le_div_of_nonneg_right hFv.2 hm.le
  have hhF_1 : |hF| ≤ 1 := le_trans hhF_le (le_trans (div_le_self (by positivity) (by linarith only [hm2])) hfw_le1)
  have hhA_1 : |hA| ≤ 1 := le_trans hhA_le (le_trans (div_le_self (by positivity) (by linarith only [hm2])) hfw_le1)
  have hpF := hpow hF hhF_1
  have hpA := hpow hA hhA_1
  rw [show 1 - 1 / (M.m : ℝ) + hF = zeroResFriv M w v by dsimp [hF, A₀]; ring, hcast, hsub] at hpF
  rw [show 1 - 1 / (M.m : ℝ) + hA = M.A v by dsimp [hA, A₀]; ring, hcast, hsub] at hpA
  set rF := δF - ((M.n : ℝ) - 1) * A₀ ^ (M.n - 2) * hF
  set rA := δA - ((M.n : ℝ) - 1) * A₀ ^ (M.n - 2) * hA
  have hrF : |rF| ≤ Cp * (fmax * w / ((M.m : ℝ) - 1)) ^ 2 := by
    have hsq : hF ^ 2 ≤ (fmax * w / ((M.m : ℝ) - 1)) ^ 2 := by
      rw [← sq_abs hF]; exact pow_le_pow_left₀ (abs_nonneg _) hhF_le 2
    exact le_trans hpF (mul_le_mul_of_nonneg_left hsq hCp)
  have hrA : |rA| ≤ Cp * (fmax * w / (M.m : ℝ)) ^ 2 := by
    have hsq : hA ^ 2 ≤ (fmax * w / (M.m : ℝ)) ^ 2 := by
      rw [← sq_abs hA]; exact pow_le_pow_left₀ (abs_nonneg _) hhA_le 2
    exact le_trans hpA (mul_le_mul_of_nonneg_left hsq hCp)
  have hmain_id : -(1 / (M.m : ℝ)) * (((M.n : ℝ) - 1) * A₀ ^ (M.n - 2) * hF) +
      (1 / (M.m : ℝ)) * (((M.n : ℝ) - 1) * A₀ ^ (M.n - 2) * hA) =
      ((M.n : ℝ) - 1) * A₀ ^ (M.n - 2) / ((M.m : ℝ) ^ 2 * ((M.m : ℝ) - 1)) * (M.F w - M.F v) := by
    dsimp [hF, hA]; rw [hFriv_diff, hA_diff]; field_simp [hm.ne', hm1.ne']; ring
  have hdecomp : -(1 - M.A w) * δF + (1 - M.A v) * δA - v * δA * (M.f v / (M.m : ℝ)) -
      ((M.n : ℝ) - 1) * A₀ ^ (M.n - 2) / ((M.m : ℝ) ^ 2 * ((M.m : ℝ) - 1)) * (M.F w - M.F v) =
      -(1 - M.A w) * rF + (1 - M.A v) * rA +
      (M.F w / (M.m : ℝ)) * (((M.n : ℝ) - 1) * A₀ ^ (M.n - 2) * hF) -
      (M.F v / (M.m : ℝ)) * (((M.n : ℝ) - 1) * A₀ ^ (M.n - 2) * hA) -
      v * (((M.n : ℝ) - 1) * A₀ ^ (M.n - 2) * hA + rA) * (M.f v / (M.m : ℝ)) := by
    rw [← hmain_id, h1A_eq w, h1A_eq v]
    have h1 : δF = ((M.n : ℝ) - 1) * A₀ ^ (M.n - 2) * hF + rF := by dsimp [rF]; ring
    have h2 : δA = ((M.n : ℝ) - 1) * A₀ ^ (M.n - 2) * hA + rA := by dsimp [rA]; ring
    rw [h1, h2]; ring
  have hA₀_p : A₀ ^ (M.n - 2) ≤ 1 := pow_le_one₀ hA₀_pos.le hA₀_le1
  have h1Aw_b : 0 ≤ 1 - M.A w ∧ 1 - M.A w ≤ 1 := by
    have hmA := M.br_A_mem_Icc ⟨by rw [ha]; exact hw_pos.le, hw_lt1.le⟩
    exact ⟨by linarith only [hmA.2], by linarith only [M.br_A_pos ⟨by rw [ha]; exact hw_pos.le, hw_lt1.le⟩]⟩
  have h1Av_b : 0 ≤ 1 - M.A v ∧ 1 - M.A v ≤ 1 := by
    have hmA := M.br_A_mem_Icc ⟨by rw [ha]; exact hv.1, le_trans hv.2 hw_lt1.le⟩
    exact ⟨by linarith only [hmA.2], by linarith only [M.br_A_pos ⟨by rw [ha]; exact hv.1, le_trans hv.2 hw_lt1.le⟩]⟩
  have he1 : -(Cp * fmax ^ 2 / ((M.m : ℝ) - 1) ^ 2) * w ^ 2 ≤ -(1 - M.A w) * rF := by
    have h1 : (1 - M.A w) * rF ≤ 1 * (Cp * (fmax * w / ((M.m : ℝ) - 1)) ^ 2) :=
      le_trans (mul_le_mul_of_nonneg_left (abs_le.mp hrF).2 h1Aw_b.1)
        (mul_le_mul_of_nonneg_right h1Aw_b.2 (by positivity))
    have heq : 1 * (Cp * (fmax * w / ((M.m : ℝ) - 1)) ^ 2) = Cp * fmax ^ 2 / ((M.m : ℝ) - 1) ^ 2 * w ^ 2 := by
      field_simp [hm1.ne']
    linarith only [h1, heq]
  have he2 : -(Cp * fmax ^ 2 / (M.m : ℝ) ^ 2) * w ^ 2 ≤ (1 - M.A v) * rA := by
    have h := (abs_le.mp hrA).1
    have hsq0 : 0 ≤ Cp * (fmax * w / (M.m : ℝ)) ^ 2 := by positivity
    have hstep : -(Cp * (fmax * w / (M.m : ℝ)) ^ 2) ≤ (1 - M.A v) * (-(Cp * (fmax * w / (M.m : ℝ)) ^ 2)) := by
      nlinarith only [h1Av_b.2, hsq0]
    have h1 := le_trans hstep (mul_le_mul_of_nonneg_left h h1Av_b.1)
    have heq : Cp * (fmax * w / (M.m : ℝ)) ^ 2 = Cp * fmax ^ 2 / (M.m : ℝ) ^ 2 * w ^ 2 := by
      field_simp [hm.ne']
    linarith only [h1, heq]
  have he3 : -(((M.n : ℝ) - 1) * fmax ^ 2 / ((M.m : ℝ) * ((M.m : ℝ) - 1))) * w ^ 2 ≤
      (M.F w / (M.m : ℝ)) * (((M.n : ℝ) - 1) * A₀ ^ (M.n - 2) * hF) := by
    have h1 : (M.F w / (M.m : ℝ)) * (((M.n : ℝ) - 1) * A₀ ^ (M.n - 2) * (-(fmax * w / ((M.m : ℝ) - 1)))) ≤
        (M.F w / (M.m : ℝ)) * (((M.n : ℝ) - 1) * A₀ ^ (M.n - 2) * hF) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (abs_le.mp hhF_le).1 (by positivity))
        (div_nonneg hFw.1 hm.le)
    have hpos1 : (M.F w / (M.m : ℝ)) * (((M.n : ℝ) - 1) * A₀ ^ (M.n - 2) * (fmax * w / ((M.m : ℝ) - 1))) ≤
        (fmax * w / (M.m : ℝ)) * (((M.n : ℝ) - 1) * 1 * (fmax * w / ((M.m : ℝ) - 1))) := by
      gcongr; exact hFw.2
    have heq : (fmax * w / (M.m : ℝ)) * (((M.n : ℝ) - 1) * 1 * (fmax * w / ((M.m : ℝ) - 1))) =
        ((M.n : ℝ) - 1) * fmax ^ 2 / ((M.m : ℝ) * ((M.m : ℝ) - 1)) * w ^ 2 := by
      field_simp [hm.ne', hm1.ne']
    have hneg : (M.F w / (M.m : ℝ)) * (((M.n : ℝ) - 1) * A₀ ^ (M.n - 2) * (-(fmax * w / ((M.m : ℝ) - 1)))) =
        -((M.F w / (M.m : ℝ)) * (((M.n : ℝ) - 1) * A₀ ^ (M.n - 2) * (fmax * w / ((M.m : ℝ) - 1)))) := by ring
    linarith only [h1, hpos1, heq, hneg]
  have he4 : -(((M.n : ℝ) - 1) * fmax ^ 2 / (M.m : ℝ) ^ 2) * w ^ 2 ≤
      -(M.F v / (M.m : ℝ)) * (((M.n : ℝ) - 1) * A₀ ^ (M.n - 2) * hA) := by
    have hA_nn : 0 ≤ hA := by dsimp [hA]; rw [hA_diff]; exact div_nonneg hFv.1 hm.le
    have h1 : (M.F v / (M.m : ℝ)) * (((M.n : ℝ) - 1) * A₀ ^ (M.n - 2) * hA) ≤
        (fmax * w / (M.m : ℝ)) * (((M.n : ℝ) - 1) * 1 * (fmax * w / (M.m : ℝ))) := by
      gcongr
      · exact hFv.2
      · exact (abs_le.mp hhA_le).2
    have heq : (fmax * w / (M.m : ℝ)) * (((M.n : ℝ) - 1) * 1 * (fmax * w / (M.m : ℝ))) =
        ((M.n : ℝ) - 1) * fmax ^ 2 / (M.m : ℝ) ^ 2 * w ^ 2 := by
      field_simp [hm.ne']
    linarith only [h1, heq]
  have he5 : -(((M.n : ℝ) - 1) * fmax ^ 2 / (M.m : ℝ) ^ 2 + Cp * fmax ^ 3 / (M.m : ℝ) ^ 3) * w ^ 2 ≤
      -v * (((M.n : ℝ) - 1) * A₀ ^ (M.n - 2) * hA + rA) * (M.f v / (M.m : ℝ)) := by
    have hfv_hi := hf_hi v ⟨by rw [ha]; exact hv.1, le_trans hv.2 hw_lt1.le⟩
    have hfv_nn := (M.hf_pos v ⟨by rw [ha]; exact hv.1, le_trans hv.2 hw_lt1.le⟩).le
    have hA_nn : 0 ≤ hA := by dsimp [hA]; rw [hA_diff]; exact div_nonneg hFv.1 hm.le
    have hbr : ((M.n : ℝ) - 1) * A₀ ^ (M.n - 2) * hA + rA ≤
        ((M.n : ℝ) - 1) * (fmax * w / (M.m : ℝ)) + Cp * (fmax * w / (M.m : ℝ)) ^ 2 := by
      have h1 : ((M.n : ℝ) - 1) * A₀ ^ (M.n - 2) * hA ≤ ((M.n : ℝ) - 1) * 1 * (fmax * w / (M.m : ℝ)) := by
        gcongr; exact (abs_le.mp hhA_le).2
      linarith only [h1, (abs_le.mp hrA).2]
    have hprod : v * (((M.n : ℝ) - 1) * A₀ ^ (M.n - 2) * hA + rA) * (M.f v / (M.m : ℝ)) ≤
        w * (((M.n : ℝ) - 1) * (fmax * w / (M.m : ℝ)) + Cp * (fmax * w / (M.m : ℝ)) ^ 2) * (fmax / (M.m : ℝ)) := by
      have h1 : v * (((M.n : ℝ) - 1) * A₀ ^ (M.n - 2) * hA + rA) ≤
          w * (((M.n : ℝ) - 1) * (fmax * w / (M.m : ℝ)) + Cp * (fmax * w / (M.m : ℝ)) ^ 2) :=
        le_trans (mul_le_mul_of_nonneg_left hbr hv.1) (mul_le_mul_of_nonneg_right hv.2 (by positivity))
      exact le_trans (mul_le_mul_of_nonneg_right h1 (div_nonneg hfv_nn hm.le))
        (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hfv_hi hm.le) (by positivity))
    have hw3 : w ^ 3 ≤ w ^ 2 := by nlinarith only [hw_pos, hw_lt1]
    have heq : w * (((M.n : ℝ) - 1) * (fmax * w / (M.m : ℝ)) + Cp * (fmax * w / (M.m : ℝ)) ^ 2) * (fmax / (M.m : ℝ)) =
        ((M.n : ℝ) - 1) * fmax ^ 2 / (M.m : ℝ) ^ 2 * w ^ 2 + Cp * fmax ^ 3 / (M.m : ℝ) ^ 3 * w ^ 3 := by
      field_simp [hm.ne']
    have h32 : Cp * fmax ^ 3 / (M.m : ℝ) ^ 3 * w ^ 3 ≤ Cp * fmax ^ 3 / (M.m : ℝ) ^ 3 * w ^ 2 :=
      mul_le_mul_of_nonneg_left hw3 (by positivity)
    linarith only [hprod, heq, h32]
  have hsum : -C_err * w ^ 2 ≤
      -(1 - M.A w) * rF + (1 - M.A v) * rA +
      (M.F w / (M.m : ℝ)) * (((M.n : ℝ) - 1) * A₀ ^ (M.n - 2) * hF) -
      (M.F v / (M.m : ℝ)) * (((M.n : ℝ) - 1) * A₀ ^ (M.n - 2) * hA) -
      v * (((M.n : ℝ) - 1) * A₀ ^ (M.n - 2) * hA + rA) * (M.f v / (M.m : ℝ)) := by
    have hring : -C_err * w ^ 2 =
        -(Cp * fmax ^ 2 / ((M.m : ℝ) - 1) ^ 2) * w ^ 2 +
        -(Cp * fmax ^ 2 / (M.m : ℝ) ^ 2) * w ^ 2 +
        -(((M.n : ℝ) - 1) * fmax ^ 2 / ((M.m : ℝ) * ((M.m : ℝ) - 1))) * w ^ 2 +
        -(((M.n : ℝ) - 1) * fmax ^ 2 / (M.m : ℝ) ^ 2) * w ^ 2 +
        -(((M.n : ℝ) - 1) * fmax ^ 2 / (M.m : ℝ) ^ 2 + Cp * fmax ^ 3 / (M.m : ℝ) ^ 3) * w ^ 2 := by
      dsimp [C_err]; ring
    linarith only [hring, he1, he2, he3, he4, he5]
  linarith only [hdecomp, hsum]

/-- **Theorem 3 (Boundary Case `a = ρ = 0`)**:
When `M.a = 0` and rivals post `SPA(0)`, a small reserve increase `r₁ ∈ (0, 1)` induces an SR
continuation that strictly raises seller 0's revenue above `SPA(0)^m`. -/
theorem theorem3_zero_reserve_fails (M : Market) (ha : M.a = 0) :
    ∃ (r₁ : ℝ) (hr1_0 : 0 < r₁) (hr1_1 : r₁ < 1) (θ : VisitStrategy M),
      IsSR M (fun j => if j = seller0 M then SPA r₁ hr1_0.le hr1_1.le else SPA 0 le_rfl zero_le_one) θ ∧
      sellerRev M (SPA 0 le_rfl zero_le_one) (unifVisit M) (seller0 M) <
        sellerRev M (SPA r₁ hr1_0.le hr1_1.le) θ (seller0 M) := by
  have hm := M.m_pos_real
  have hm1 := M.m_sub_one_pos_real
  have hm2 : (2 : ℝ) ≤ M.m := by exact_mod_cast M.hm
  have hn := M.n_pos_real
  have hn1 := M.n_sub_one_pos_real
  obtain ⟨fmin, hfmin, hf_lo⟩ := M.exists_f_min
  obtain ⟨fmax, hfmax, hf_hi⟩ := M.exists_f_max
  set A₀ := 1 - 1 / (M.m : ℝ)
  have hA₀_pos : 0 < A₀ := by
    have : 1 / (M.m : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hm2; linarith
  obtain ⟨Cp, hCp, hpow⟩ := pow_first_order_bound (M.n - 1) A₀
  let c_pos := ((M.n : ℝ) - 1) * A₀ ^ (M.n - 2) * fmin / (2 * (M.m : ℝ) ^ 2 * ((M.m : ℝ) - 1))
  have hc_pos : 0 < c_pos := by positivity
  let C_err := Cp * fmax ^ 2 / ((M.m : ℝ) - 1) ^ 2 + Cp * fmax ^ 2 / (M.m : ℝ) ^ 2 +
    ((M.n : ℝ) - 1) * fmax ^ 2 / ((M.m : ℝ) * ((M.m : ℝ) - 1)) +
    2 * ((M.n : ℝ) - 1) * fmax ^ 2 / (M.m : ℝ) ^ 2 + Cp * fmax ^ 3 / (M.m : ℝ) ^ 3
  let w := min (1 / 2) (min (1 / (2 * fmax + 1)) (c_pos / (2 * C_err + 2)))
  have hw_pos : 0 < w := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hw_lt1 : w < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hst := zeroRes_sr_and_rev M ha ⟨hw_pos, hw_lt1⟩
  refine ⟨zeroResR1 M w, hst.1, lt_trans hst.2.1 hw_lt1, zeroResVisit M w,
    (hst.2.2 hst.1.le (lt_trans hst.2.1 hw_lt1).le).1, ?_⟩
  rw [← sub_pos, (hst.2.2 hst.1.le (lt_trans hst.2.1 hw_lt1).le).2]
  apply mul_pos hn
  have hF0_zero : M.F 0 = 0 := by simpa [ha] using M.hF_a
  have hF_le : ∀ v ∈ Icc (0 : ℝ) w, 0 ≤ M.F v ∧ M.F v ≤ fmax * w := by
    intro v hv
    have hlip := M.F_lipschitz_bounds (by rw [ha]; exact left_mem_Icc.mpr zero_le_one)
      ⟨by rw [ha]; exact hv.1, le_trans hv.2 hw_lt1.le⟩ hv.1 hf_lo hf_hi
    simp only [hF0_zero, sub_zero] at hlip
    exact ⟨(M.F_mem_Icc ⟨by rw [ha]; exact hv.1, le_trans hv.2 hw_lt1.le⟩).1,
      le_trans hlip.2 (mul_le_mul_of_nonneg_left hv.2 hfmax.le)⟩
  have hF_sub := M.F_continuousOn.mono (Icc_subset_Icc (by rw [ha]) hw_lt1.le)
  have hf_sub := M.hf_cont.mono (Icc_subset_Icc (by rw [ha]) hw_lt1.le)
  have hcontA : ContinuousOn (fun v => M.A v ^ (M.n - 1)) (Icc 0 w) :=
    (M.A_continuousOn.mono (Icc_subset_Icc (by rw [ha]) hw_lt1.le)).pow _
  have hcontFriv : ContinuousOn (fun v => zeroResFriv M w v ^ (M.n - 1)) (Icc 0 w) := by
    unfold zeroResFriv; fun_prop
  have hIBP_vF : ∫ v in (0 : ℝ)..w, (M.F v + v * M.f v) = w * M.F w := by
    have hcont : ContinuousOn (fun v => v * M.F v) (Icc 0 w) := continuousOn_id.mul hF_sub
    have hderiv : ∀ v ∈ Ioo (0 : ℝ) w, HasDerivAt (fun v => v * M.F v) (M.F v + v * M.f v) v := by
      intro v hv
      have h := (hasDerivAt_id v).mul (M.hF_deriv_open v ⟨by rw [ha]; exact hv.1, lt_trans hv.2 hw_lt1⟩)
      convert h using 1
      · ext x; simp
      · simp only [id_eq]; ring
    have hint : IntervalIntegrable (fun v => M.F v + v * M.f v) volume 0 w :=
      ((hF_sub.add (continuousOn_id.mul hf_sub)).mono (by rw [uIcc_of_le hw_pos.le])).intervalIntegrable
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hw_pos.le hcont hderiv hint]
    simp [hF0_zero]
  have h1A_eq : ∀ v, 1 - M.A v = 1 / (M.m : ℝ) - M.F v / (M.m : ℝ) := fun v => by unfold Market.A; ring
  have hA0_cancel : -(1 - M.A w) * (w * A₀ ^ (M.n - 1)) +
      (∫ v in (0 : ℝ)..w, (1 - M.A v) * A₀ ^ (M.n - 1)) -
      (∫ v in (0 : ℝ)..w, v * A₀ ^ (M.n - 1) * (M.f v / (M.m : ℝ))) = 0 := by
    have h1 : ∫ v in (0 : ℝ)..w, (1 - M.A v) * A₀ ^ (M.n - 1) =
        (A₀ ^ (M.n - 1) / (M.m : ℝ)) * (w - ∫ v in (0 : ℝ)..w, M.F v) := by
      have heq : (fun v => (1 - M.A v) * A₀ ^ (M.n - 1)) =
          fun v => (A₀ ^ (M.n - 1) / (M.m : ℝ)) * (1 - M.F v) := by ext v; rw [h1A_eq]; ring
      rw [heq, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub intervalIntegrable_const ((hF_sub.mono (by rw [uIcc_of_le hw_pos.le])).intervalIntegrable),
        intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero]
    have h2 : ∫ v in (0 : ℝ)..w, v * A₀ ^ (M.n - 1) * (M.f v / (M.m : ℝ)) =
        (A₀ ^ (M.n - 1) / (M.m : ℝ)) * (∫ v in (0 : ℝ)..w, v * M.f v) := by
      have heq : (fun v => v * A₀ ^ (M.n - 1) * (M.f v / (M.m : ℝ))) =
          fun v => (A₀ ^ (M.n - 1) / (M.m : ℝ)) * (v * M.f v) := by ext v; ring
      rw [heq, intervalIntegral.integral_const_mul]
    rw [h1, h2, h1A_eq w]
    have hadd : (∫ v in (0 : ℝ)..w, M.F v) + (∫ v in (0 : ℝ)..w, v * M.f v) = w * M.F w := by
      have hvf : IntervalIntegrable (fun v => v * M.f v) volume 0 w :=
        ((show ContinuousOn (fun v => v * M.f v) (Icc 0 w) from continuousOn_id.mul hf_sub).mono
          (by rw [uIcc_of_le hw_pos.le])).intervalIntegrable
      rw [← intervalIntegral.integral_add ((hF_sub.mono (by rw [uIcc_of_le hw_pos.le])).intervalIntegrable) hvf, hIBP_vF]
    linear_combination -(A₀ ^ (M.n - 1) / (M.m : ℝ)) * hadd
  have hfw_le1 : fmax * w ≤ 1 := by
    have : w ≤ 1 / (2 * fmax + 1) := le_trans (min_le_right _ _) (min_le_left _ _)
    rw [le_div_iff₀ (by positivity)] at this; nlinarith only [this, hw_pos]
  have hmain_int : ∫ v in (0 : ℝ)..w, (M.F w - M.F v) = ∫ v in (0 : ℝ)..w, v * M.f v := by
    have hiF : IntervalIntegrable M.F volume 0 w := (hF_sub.mono (by rw [uIcc_of_le hw_pos.le])).intervalIntegrable
    have hvf : IntervalIntegrable (fun v => v * M.f v) volume 0 w :=
      ((continuousOn_id.mul hf_sub).mono (by rw [uIcc_of_le hw_pos.le])).intervalIntegrable
    rw [intervalIntegral.integral_sub intervalIntegrable_const hiF,
      intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    have hadd := intervalIntegral.integral_add hiF hvf; rw [hIBP_vF] at hadd; linarith only [hadd]
  have hv_f_lower : fmin * w ^ 2 / 2 ≤ ∫ v in (0 : ℝ)..w, v * M.f v := by
    have h1 : ∫ v in (0 : ℝ)..w, fmin * v = fmin * w ^ 2 / 2 := by
      have hd : ∀ v ∈ uIcc (0 : ℝ) w, HasDerivAt (fun x => fmin * x ^ 2 / 2) (fmin * v) v := fun v _ => by
        have h := ((hasDerivAt_pow 2 v).const_mul fmin).div_const 2
        convert h using 1; ring
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
        ((continuousOn_const.mul continuousOn_id).mono (by rw [uIcc_of_le hw_pos.le])).intervalIntegrable]
      ring
    rw [← h1]
    exact intervalIntegral.integral_mono_on hw_pos.le
      ((continuousOn_const.mul continuousOn_id).mono (by rw [uIcc_of_le hw_pos.le])).intervalIntegrable
      ((continuousOn_id.mul hf_sub).mono (by rw [uIcc_of_le hw_pos.le])).intervalIntegrable
      (fun v hv => by rw [mul_comm]; exact mul_le_mul_of_nonneg_left (hf_lo v ⟨by rw [ha]; exact hv.1, le_trans hv.2 hw_lt1.le⟩) hv.1)
  set δF := fun v => zeroResFriv M w v ^ (M.n - 1) - A₀ ^ (M.n - 1)
  set δA := fun v => M.A v ^ (M.n - 1) - A₀ ^ (M.n - 1)
  have hrewrite : -(1 - M.A w) * (∫ v in (0 : ℝ)..w, zeroResFriv M w v ^ (M.n - 1)) +
      (∫ v in (0 : ℝ)..w, (1 - M.A v) * M.A v ^ (M.n - 1)) -
      (∫ v in (0 : ℝ)..w, v * M.A v ^ (M.n - 1) * (M.f v / (M.m : ℝ))) =
      ∫ v in (0 : ℝ)..w, (-(1 - M.A w) * δF v + (1 - M.A v) * δA v - v * δA v * (M.f v / (M.m : ℝ))) := by
    have hiF1 : IntervalIntegrable (fun v => zeroResFriv M w v ^ (M.n - 1)) volume 0 w :=
      (hcontFriv.mono (by rw [uIcc_of_le hw_pos.le])).intervalIntegrable
    have hiA1 : IntervalIntegrable (fun v => (1 - M.A v) * M.A v ^ (M.n - 1)) volume 0 w :=
      (((continuousOn_const.sub (M.A_continuousOn.mono (Icc_subset_Icc (by rw [ha]) hw_lt1.le))).mul hcontA).mono
        (by rw [uIcc_of_le hw_pos.le])).intervalIntegrable
    have hiA0 : IntervalIntegrable (fun v => (1 - M.A v) * A₀ ^ (M.n - 1)) volume 0 w :=
      (((continuousOn_const.sub (M.A_continuousOn.mono (Icc_subset_Icc (by rw [ha]) hw_lt1.le))).mul continuousOn_const).mono
        (by rw [uIcc_of_le hw_pos.le])).intervalIntegrable
    have hiV1 : IntervalIntegrable (fun v => v * M.A v ^ (M.n - 1) * (M.f v / (M.m : ℝ))) volume 0 w :=
      (((continuousOn_id.mul hcontA).mul (hf_sub.div_const _)).mono (by rw [uIcc_of_le hw_pos.le])).intervalIntegrable
    have hiV0 : IntervalIntegrable (fun v => v * A₀ ^ (M.n - 1) * (M.f v / (M.m : ℝ))) volume 0 w :=
      (((continuousOn_id.mul continuousOn_const).mul (hf_sub.div_const _)).mono (by rw [uIcc_of_le hw_pos.le])).intervalIntegrable
    have h1 : ∫ v in (0 : ℝ)..w, δF v = (∫ v in (0 : ℝ)..w, zeroResFriv M w v ^ (M.n - 1)) - w * A₀ ^ (M.n - 1) := by
      dsimp [δF]
      rw [intervalIntegral.integral_sub hiF1 intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    have h2 : ∫ v in (0 : ℝ)..w, (1 - M.A v) * δA v =
        (∫ v in (0 : ℝ)..w, (1 - M.A v) * M.A v ^ (M.n - 1)) - (∫ v in (0 : ℝ)..w, (1 - M.A v) * A₀ ^ (M.n - 1)) := by
      have heq : (fun v => (1 - M.A v) * δA v) = fun v => (1 - M.A v) * M.A v ^ (M.n - 1) - (1 - M.A v) * A₀ ^ (M.n - 1) := by
        ext v; dsimp [δA]; ring
      rw [heq, intervalIntegral.integral_sub hiA1 hiA0]
    have h3 : ∫ v in (0 : ℝ)..w, v * δA v * (M.f v / (M.m : ℝ)) =
        (∫ v in (0 : ℝ)..w, v * M.A v ^ (M.n - 1) * (M.f v / (M.m : ℝ))) -
        (∫ v in (0 : ℝ)..w, v * A₀ ^ (M.n - 1) * (M.f v / (M.m : ℝ))) := by
      have heq : (fun v => v * δA v * (M.f v / (M.m : ℝ))) =
          fun v => v * M.A v ^ (M.n - 1) * (M.f v / (M.m : ℝ)) - v * A₀ ^ (M.n - 1) * (M.f v / (M.m : ℝ)) := by
        ext v; dsimp [δA]; ring
      rw [heq, intervalIntegral.integral_sub hiV1 hiV0]
    have hi_dF : IntervalIntegrable (fun v => -(1 - M.A w) * δF v) volume 0 w :=
      (hiF1.sub intervalIntegrable_const).const_mul _
    have hi_dA : IntervalIntegrable (fun v => (1 - M.A v) * δA v) volume 0 w := by
      have heq : (fun v => (1 - M.A v) * δA v) = fun v => (1 - M.A v) * M.A v ^ (M.n - 1) - (1 - M.A v) * A₀ ^ (M.n - 1) := by
        ext v; dsimp [δA]; ring
      rw [heq]; exact hiA1.sub hiA0
    have hi_dV : IntervalIntegrable (fun v => v * δA v * (M.f v / (M.m : ℝ))) volume 0 w := by
      have heq : (fun v => v * δA v * (M.f v / (M.m : ℝ))) =
          fun v => v * M.A v ^ (M.n - 1) * (M.f v / (M.m : ℝ)) - v * A₀ ^ (M.n - 1) * (M.f v / (M.m : ℝ)) := by
        ext v; dsimp [δA]; ring
      rw [heq]; exact hiV1.sub hiV0
    rw [intervalIntegral.integral_sub (hi_dF.add hi_dA) hi_dV,
      intervalIntegral.integral_add hi_dF hi_dA, intervalIntegral.integral_const_mul, h1, h2, h3]
    linarith only [hA0_cancel]
  rw [hrewrite]
  have hpw_lo := zeroRes_integrand_lower M ha hfmax hf_hi hCp hpow hw_pos hw_lt1 hfw_le1 hF_le
  have hi_lo : IntervalIntegrable (fun v => ((M.n : ℝ) - 1) * A₀ ^ (M.n - 2) / ((M.m : ℝ) ^ 2 * ((M.m : ℝ) - 1)) *
      (M.F w - M.F v) - C_err * w ^ 2) volume 0 w :=
    (((continuousOn_const.mul (continuousOn_const.sub hF_sub)).sub continuousOn_const).mono
      (by rw [uIcc_of_le hw_pos.le])).intervalIntegrable
  have hi_hi : IntervalIntegrable (fun v => -(1 - M.A w) * δF v + (1 - M.A v) * δA v -
      v * δA v * (M.f v / (M.m : ℝ))) volume 0 w := by
    have hc1 : ContinuousOn (fun v => -(1 - M.A w) * δF v) (Icc 0 w) :=
      continuousOn_const.mul (hcontFriv.sub continuousOn_const)
    have hc2 : ContinuousOn (fun v => (1 - M.A v) * δA v) (Icc 0 w) :=
      (continuousOn_const.sub (M.A_continuousOn.mono (Icc_subset_Icc (by rw [ha]) hw_lt1.le))).mul
        (hcontA.sub continuousOn_const)
    have hc3 : ContinuousOn (fun v => v * δA v * (M.f v / (M.m : ℝ))) (Icc 0 w) :=
      (continuousOn_id.mul (hcontA.sub continuousOn_const)).mul (hf_sub.div_const _)
    exact (((hc1.add hc2).sub hc3).mono (by rw [uIcc_of_le hw_pos.le])).intervalIntegrable
  have hint_le := intervalIntegral.integral_mono_on hw_pos.le hi_lo hi_hi hpw_lo
  have hi_FmF : IntervalIntegrable (fun v => M.F w - M.F v) volume 0 w :=
    ((continuousOn_const.sub hF_sub).mono (by rw [uIcc_of_le hw_pos.le])).intervalIntegrable
  rw [intervalIntegral.integral_sub (hi_FmF.const_mul _) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, hmain_int, intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hint_le
  have hmain_pos : c_pos * w ^ 2 ≤
      ((M.n : ℝ) - 1) * A₀ ^ (M.n - 2) / ((M.m : ℝ) ^ 2 * ((M.m : ℝ) - 1)) * (∫ v in (0 : ℝ)..w, v * M.f v) := by
    have h1 := mul_le_mul_of_nonneg_left hv_f_lower
      (by positivity : (0 : ℝ) ≤ ((M.n : ℝ) - 1) * A₀ ^ (M.n - 2) / ((M.m : ℝ) ^ 2 * ((M.m : ℝ) - 1)))
    dsimp [c_pos]
    have heq : ((M.n : ℝ) - 1) * A₀ ^ (M.n - 2) / ((M.m : ℝ) ^ 2 * ((M.m : ℝ) - 1)) * (fmin * w ^ 2 / 2) =
        ((M.n : ℝ) - 1) * A₀ ^ (M.n - 2) * fmin / (2 * (M.m : ℝ) ^ 2 * ((M.m : ℝ) - 1)) * w ^ 2 := by
      field_simp [hm.ne', hm1.ne']
    linarith only [h1, heq]
  have hw_small : C_err * w < c_pos := by
    have hle : w ≤ c_pos / (2 * C_err + 2) := le_trans (min_le_right _ _) (min_le_right _ _)
    have hmul : w * (2 * C_err + 2) ≤ c_pos := (le_div_iff₀ (by positivity)).mp hle
    have hCnn : 0 ≤ C_err := by positivity
    nlinarith only [hmul, hw_pos, hCnn]
  have hstrict : 0 < c_pos * w ^ 2 - w * (C_err * w ^ 2) := by
    rw [show w * (C_err * w ^ 2) = (C_err * w) * w ^ 2 by ring]
    nlinarith only [hw_small, sq_pos_of_pos hw_pos]
  linarith only [hint_le, hmain_pos, hstrict]

end Theorem3

/-! ### Section 5 & Appendix B: Theorem 4 (Asymmetric Duopoly Failure for Large `n`) -/

section Theorem4

/-! ### Theorem 4: Asymmetric Duopoly Profiles (`m = 2`, `a = 0`) -/


/-! #### Generic helpers for Theorem 4 -/

/-- The market with `max n 2` buyers and the same `m, a, F, f`. -/
def Market.br_atN (M : Market) (n : ℕ) : Market := M.withBuyers (max n 2) (le_max_right _ _)

lemma Market.br_atN_n (M : Market) {n : ℕ} (hn : 2 ≤ n) : (M.br_atN n).n = n := max_eq_left hn

/-- Symmetric duopoly effective distribution `(1 + F v) / 2`. -/
noncomputable def br_Ah (M : Market) (v : ℝ) : ℝ := (1 + M.F v) / 2

lemma br_A_eq (M : Market) (hm : M.m = 2) (v : ℝ) : M.A v = br_Ah M v := by
  unfold Market.A br_Ah; rw [hm]; norm_num; ring

/-- Total version of `SPA`. -/
noncomputable def br_spa (r : ℝ) : HierarchicalMech :=
  if h : 0 ≤ r ∧ r ≤ 1 then SPA r h.1 h.2 else SPA 0 le_rfl zero_le_one

lemma br_spa_eq {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) : br_spa r = SPA r h0 h1 := by
  unfold br_spa; simp only [h0, h1, and_self, ↓reduceDIte]

/-- Total one-pool mechanism `(r, {(α, β)})`. -/
noncomputable def br_onePool (r α β : ℝ) : HierarchicalMech :=
  if h : 0 ≤ r ∧ r ≤ α ∧ α < β ∧ β ≤ 1 then
    { r := r
      hr0 := h.1
      hr1 := le_trans h.2.1 (le_trans h.2.2.1.le h.2.2.2)
      pools := [⟨α, β, h.2.2.1⟩]
      hpools_in := by
        intro I hI
        simp only [List.mem_singleton] at hI
        subst hI
        exact ⟨h.2.1, h.2.2.2⟩
      hpools_disj := List.pairwise_singleton _ _ }
  else SPA 0 le_rfl zero_le_one

lemma br_alloc_spa (M : Market) {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) (G : ℝ → ℝ) (v : ℝ) :
    alloc M (br_spa r) G v = if v < r then 0 else G v ^ (M.n - 1) := by
  rw [br_spa_eq h0 h1]
  unfold alloc SPA
  simp only [List.find?_nil]

lemma br_alloc_onePool (M : Market) {r α β : ℝ} (h : 0 ≤ r ∧ r ≤ α ∧ α < β ∧ β ≤ 1)
    (G : ℝ → ℝ) (v : ℝ) :
    alloc M (br_onePool r α β) G v =
      if v < r then 0 else if α < v ∧ v < β then poolAvg M.n (G α) (G β) else G v ^ (M.n - 1) := by
  unfold alloc br_onePool
  simp only [h.1, h.2.1, h.2.2.1, h.2.2.2, and_self, ↓reduceDIte]
  by_cases hv : v < r
  · simp only [hv, ↓reduceIte]
  · simp only [hv, ↓reduceIte]
    by_cases hp : α < v ∧ v < β
    · simp only [hp, decide_true, List.find?_cons_of_pos, ↓reduceIte, and_self]
    · simp only [hp, decide_false, List.find?_cons_of_neg, List.find?_nil, Bool.false_eq_true,
        not_false_eq_true, ↓reduceIte]

/-- Visit strategy giving weight `θ0 v` to seller `0` and sharing the rest among rivals. -/
noncomputable def br_visit (M : Market) (θ0 : ℝ → ℝ) (hmeas : Measurable θ0)
    (h0 : ∀ v, 0 ≤ θ0 v) (h1 : ∀ v, θ0 v ≤ 1) : VisitStrategy M where
  θ := fun j v => if j = seller0 M then θ0 v else (1 - θ0 v) / ((M.m : ℝ) - 1)
  hmeas := fun j => by
    by_cases hj : j = seller0 M
    · simp only [hj, ↓reduceIte]; exact hmeas
    · simp only [hj, ↓reduceIte]; exact (measurable_const.sub hmeas).div_const _
  hnonneg := fun j v => by
    have := M.m_sub_one_pos_real
    split_ifs
    · exact h0 v
    · exact div_nonneg (by linarith [h1 v]) this.le
  hsum := fun v _ => by
    have hcard : (Finset.univ.erase (seller0 M)).card = M.m - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_fin]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (seller0 M))]
    simp only [↓reduceIte]
    have hconst : ∑ j ∈ Finset.univ.erase (seller0 M),
        (if j = seller0 M then θ0 v else (1 - θ0 v) / ((M.m : ℝ) - 1)) =
        ∑ _j ∈ Finset.univ.erase (seller0 M), (1 - θ0 v) / ((M.m : ℝ) - 1) :=
      Finset.sum_congr rfl fun j hj => by simp [Finset.ne_of_mem_erase hj]
    rw [hconst, Finset.sum_const, hcard, nsmul_eq_mul,
      Nat.cast_sub (by have := M.hm; omega), Nat.cast_one]
    field_simp [M.m_sub_one_pos_real.ne']
    ring

lemma br_visit_seller0 (M : Market) (θ0 : ℝ → ℝ) (hmeas : Measurable θ0)
    (h0 : ∀ v, 0 ≤ θ0 v) (h1 : ∀ v, θ0 v ≤ 1) (v : ℝ) :
    (br_visit M θ0 hmeas h0 h1).θ (seller0 M) v = θ0 v := by
  simp [br_visit]

lemma br_visit_rival (M : Market) (hm : M.m = 2) (θ0 : ℝ → ℝ) (hmeas : Measurable θ0)
    (h0 : ∀ v, 0 ≤ θ0 v) (h1 : ∀ v, θ0 v ≤ 1) {j : Fin M.m} (hj : j ≠ seller0 M) (v : ℝ) :
    (br_visit M θ0 hmeas h0 h1).θ j v = 1 - θ0 v := by
  simp only [br_visit, hj, ↓reduceIte]
  rw [hm]; norm_num

lemma br_theta_f_intervalIntegrable (M : Market) (θ : VisitStrategy M) (j : Fin M.m)
    {x y : ℝ} (hx : M.a ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) :
    IntervalIntegrable (fun u => θ.θ j u * M.f u) volume x y := by
  obtain ⟨fmax, hfmax, hf_hi⟩ := M.exists_f_max
  have hθle : ∀ u ∈ Icc M.a 1, θ.θ j u ≤ 1 := by
    intro u hu
    have hs := θ.hsum u hu
    have := Finset.single_le_sum (fun k _ => θ.hnonneg k u) (Finset.mem_univ j)
    linarith
  have hfm : AEStronglyMeasurable M.f (volume.restrict (uIoc x y)) := by
    rw [uIoc_of_le hxy]
    exact ((M.hf_cont.mono (Icc_subset_Icc hx hy)).aestronglyMeasurable measurableSet_Icc).mono_measure
      (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)
  refine IntervalIntegrable.mono_fun' (g := fun _ => fmax) intervalIntegrable_const
    ((θ.hmeas j).aestronglyMeasurable.mul hfm) ?_
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with u hu
  rw [uIoc_of_le hxy] at hu
  have hu' : u ∈ Icc M.a 1 := ⟨le_trans hx hu.1.le, le_trans hu.2 hy⟩
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (θ.hnonneg j u), abs_of_nonneg (M.hf_pos u hu').le]
  calc θ.θ j u * M.f u ≤ 1 * fmax :=
        mul_le_mul (hθle u hu') (hf_hi u hu') (M.hf_pos u hu').le zero_le_one
    _ = fmax := one_mul _

lemma br_effDist_one (M : Market) (θ : VisitStrategy M) (j : Fin M.m) : effDist M θ j 1 = 1 := by
  unfold effDist; simp

lemma br_effDist_sub (M : Market) (θ : VisitStrategy M) (j : Fin M.m) {x y c : ℝ}
    (hx : M.a ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) (hc : ∀ u ∈ Ioo x y, θ.θ j u = c) :
    effDist M θ j x = effDist M θ j y - c * (M.F y - M.F x) := by
  unfold effDist
  have h1 := br_theta_f_intervalIntegrable M θ j hx hxy hy
  have h2 := br_theta_f_intervalIntegrable M θ j (le_trans hx hxy) hy le_rfl
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  have h3 : ∫ u in x..y, θ.θ j u * M.f u = c * (M.F y - M.F x) := by
    rw [intervalIntegral_congr_Ioo hxy (g := fun u => c * M.f u) (fun u hu => by rw [hc u hu]),
      intervalIntegral.integral_const_mul, ← M.F_sub_eq_integral hx hxy hy]
  rw [h3]; ring

lemma br_surplus_step (M : Market) (mech : HierarchicalMech) (G : ℝ → ℝ) {b v : ℝ}
    (hbv : b ≤ v) (hint : IntervalIntegrable (alloc M mech G) volume 0 b)
    {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Icc b v)) (heq : ∀ u ∈ Ioo b v, alloc M mech G u = φ u) :
    IntervalIntegrable (alloc M mech G) volume 0 v ∧
      surplus M mech G v = surplus M mech G b + ∫ u in b..v, φ u := by
  have h2 : IntervalIntegrable (alloc M mech G) volume b v :=
    (intervalIntegrable_congr_Ioo hbv heq).mpr (hφ.mono (by rw [uIcc_of_le hbv])).intervalIntegrable
  refine ⟨hint.trans h2, ?_⟩
  unfold surplus
  rw [← intervalIntegral.integral_add_adjacent_intervals hint h2, intervalIntegral_congr_Ioo hbv heq]

lemma br_surplus_zero (M : Market) (mech : HierarchicalMech) (G : ℝ → ℝ) :
    IntervalIntegrable (alloc M mech G) volume 0 0 ∧ surplus M mech G 0 = 0 := by
  refine ⟨IntervalIntegrable.refl, ?_⟩
  unfold surplus; simp

/-! #### Exact block identities -/

/-- Exclusive-block revenue identity (two integrations by parts). -/
lemma br_block_rev (n : ℕ) (hn : 1 ≤ n) {b0 b1 : ℝ} (hb : b0 ≤ b1) {G g : ℝ → ℝ}
    (hG : ContinuousOn G (Icc b0 b1)) (hg : ContinuousOn g (Icc b0 b1))
    (hd : ∀ v ∈ Ioo b0 b1, HasDerivAt G (g v) v) (S0 : ℝ) :
    (n : ℝ) * ∫ v in b0..b1, (v * G v ^ (n - 1) - (S0 + ∫ u in b0..v, G u ^ (n - 1))) * g v =
      b1 * G b1 ^ n - b0 * G b0 ^ n -
        (∫ v in b0..b1, ((n : ℝ) * (G b1 - G v) + G v) * G v ^ (n - 1)) -
        (n : ℝ) * S0 * (G b1 - G b0) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hnR : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  set s : ℝ → ℝ := fun v => S0 + ∫ u in b0..v, G u ^ k with hs_def
  have hGk : ContinuousOn (fun v => G v ^ k) (Icc b0 b1) := hG.pow _
  have hs_cont : ContinuousOn s (Icc b0 b1) :=
    continuousOn_const.add (continuousOn_primitive_Icc hb hGk)
  have hs_d : ∀ v ∈ Ioo b0 b1, HasDerivAt s (G v ^ k) v := fun v hv =>
    (integral_hasDerivAt_right_of_continuousOn hGk hv).const_add S0
  have hW_d : ∀ v ∈ Ioo b0 b1,
      HasDerivAt (fun v => G v ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) (G v ^ k * g v) v := by
    intro v hv
    have h := ((hd v hv).pow (k + 1)).div_const ((k + 1 : ℕ) : ℝ)
    convert h using 1
    simp only [Nat.add_sub_cancel]
    field_simp
  have hint : ∀ φ : ℝ → ℝ, ContinuousOn φ (Icc b0 b1) → IntervalIntegrable φ volume b0 b1 :=
    fun φ hφ => (hφ.mono (by rw [uIcc_of_le hb])).intervalIntegrable
  have hWc : ContinuousOn (fun v => G v ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) (Icc b0 b1) :=
    (hG.pow _).div_const _
  have I1 := ibp_of_hasDerivAt_of_le hb continuousOn_id hWc (fun v _ => hasDerivAt_id v) hW_d
    (hint _ (continuousOn_const.mul hWc)) (hint _ (continuousOn_id.mul (hGk.mul hg)))
  have I2 := ibp_of_hasDerivAt_of_le hb hs_cont hG hs_d hd
    (hint _ (hGk.mul hG)) (hint _ (hs_cont.mul hg))
  simp only [id_eq] at I1
  have hs_b0 : s b0 = S0 := by simp [hs_def]
  have hs_b1 : s b1 = S0 + ∫ u in b0..b1, G u ^ k := rfl
  rw [hs_b0, hs_b1] at I2
  -- normalize the integrals
  set J0 := ∫ u in b0..b1, G u ^ k
  set J1 := ∫ u in b0..b1, G u ^ (k + 1)
  have e1 : ∫ x in b0..b1, (1 : ℝ) * (G x ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) = J1 / ((k + 1 : ℕ) : ℝ) := by
    simp only [one_mul]; rw [intervalIntegral.integral_div]
  have e2 : ∫ x in b0..b1, G x ^ k * G x = J1 := by
    congr 1
  have e3 : ∫ v in b0..b1, (((k + 1 : ℕ) : ℝ) * (G b1 - G v) + G v) * G v ^ k =
      ((k + 1 : ℕ) : ℝ) * G b1 * J0 - (k : ℝ) * J1 := by
    have hfun : (fun v => (((k + 1 : ℕ) : ℝ) * (G b1 - G v) + G v) * G v ^ k) =
        fun v => (((k + 1 : ℕ) : ℝ) * G b1) * G v ^ k - (k : ℝ) * G v ^ (k + 1) := by
      ext v; push_cast; ring
    have hGk1 : ContinuousOn (fun v => G v ^ (k + 1)) (Icc b0 b1) := hG.pow (k + 1)
    rw [hfun, intervalIntegral.integral_sub
      (hint (fun v => (((k + 1 : ℕ) : ℝ) * G b1) * G v ^ k) (continuousOn_const.mul hGk))
      (hint (fun v => (k : ℝ) * G v ^ (k + 1)) (continuousOn_const.mul hGk1)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have e4 : ∫ v in b0..b1, (v * G v ^ k - s v) * g v =
      (∫ v in b0..b1, v * (G v ^ k * g v)) - ∫ v in b0..b1, s v * g v := by
    rw [← intervalIntegral.integral_sub
      (hint (fun v => v * (G v ^ k * g v)) (continuousOn_id.mul (hGk.mul hg)))
      (hint (fun v => s v * g v) (hs_cont.mul hg))]
    congr 1; ext v; ring
  rw [e4, I1, I2, e1, e2, e3]
  field_simp
  push_cast
  ring

/-- Bounds on the exclusive-block error integral. -/
lemma br_block_err_bounds (n : ℕ) (hn : 1 ≤ n) {b0 b1 : ℝ} (hb : b0 ≤ b1) {G g : ℝ → ℝ}
    (hG : ContinuousOn G (Icc b0 b1)) (hg : ContinuousOn g (Icc b0 b1))
    (hd : ∀ v ∈ Ioo b0 b1, HasDerivAt G (g v) v) {gmin : ℝ} (hgmin : 0 < gmin)
    (hglo : ∀ v ∈ Icc b0 b1, gmin ≤ g v) (hG0 : 0 ≤ G b0) :
    0 ≤ ∫ v in b0..b1, ((n : ℝ) * (G b1 - G v) + G v) * G v ^ (n - 1) ∧
    ∫ v in b0..b1, ((n : ℝ) * (G b1 - G v) + G v) * G v ^ (n - 1) ≤
      2 * G b1 ^ (n + 1) / (((n : ℝ) + 1) * gmin) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hmono : MonotoneOn G (Icc b0 b1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc b0 b1) hG
    · rw [interior_Icc]; exact fun v hv => (hd v hv).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]; intro v hv
      rw [(hd v hv).deriv]; exact le_trans hgmin.le (hglo v (Ioo_subset_Icc_self hv))
  have hGr : ∀ v ∈ Icc b0 b1, 0 ≤ G v ∧ G v ≤ G b1 := fun v hv =>
    ⟨le_trans hG0 (hmono (left_mem_Icc.mpr hb) hv hv.1), hmono hv (right_mem_Icc.mpr hb) hv.2⟩
  have hnR : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hint : ∀ φ : ℝ → ℝ, ContinuousOn φ (Icc b0 b1) → IntervalIntegrable φ volume b0 b1 :=
    fun φ hφ => (hφ.mono (by rw [uIcc_of_le hb])).intervalIntegrable
  have hcI : ContinuousOn (fun v => (((k + 1 : ℕ) : ℝ) * (G b1 - G v) + G v) * G v ^ k) (Icc b0 b1) :=
    ((continuousOn_const.mul (continuousOn_const.sub hG)).add hG).mul (hG.pow _)
  have hI_nn : ∀ v ∈ Icc b0 b1, 0 ≤ (((k + 1 : ℕ) : ℝ) * (G b1 - G v) + G v) * G v ^ k := by
    intro v hv
    have h := hGr v hv
    have : 0 ≤ G b1 - G v := by linarith [h.2]
    exact mul_nonneg (add_nonneg (mul_nonneg hnR.le this) h.1) (pow_nonneg h.1 _)
  refine ⟨intervalIntegral.integral_nonneg hb hI_nn, ?_⟩
  -- antiderivative Φ(y) = G1 y^(k+1) - k/(k+2) y^(k+2)
  set G1 := G b1
  set Φ : ℝ → ℝ := fun v => G1 * G v ^ (k + 1) - (k : ℝ) / ((k : ℝ) + 2) * G v ^ (k + 2) with hΦ_def
  set I : ℝ → ℝ := fun v => (((k + 1 : ℕ) : ℝ) * (G1 - G v) + G v) * G v ^ k with hI_def
  have hΦd : ∀ v ∈ Ioo b0 b1, HasDerivAt Φ (I v * g v) v := by
    intro v hv
    have h1 := ((hd v hv).pow (k + 1)).const_mul G1
    have h2 := ((hd v hv).pow (k + 2)).const_mul ((k : ℝ) / ((k : ℝ) + 2))
    have h := h1.sub h2
    convert h using 1
    simp only [hI_def, Nat.add_sub_cancel, show k + 2 - 1 = k + 1 by omega]
    have hk2 : (k : ℝ) + 2 ≠ 0 := by positivity
    field_simp
    push_cast
    ring
  have hGk1 : ContinuousOn (fun v => G v ^ (k + 1)) (Icc b0 b1) := hG.pow (k + 1)
  have hGk2 : ContinuousOn (fun v => G v ^ (k + 2)) (Icc b0 b1) := hG.pow (k + 2)
  have hΦc : ContinuousOn Φ (Icc b0 b1) :=
    (continuousOn_const.mul hGk1).sub (continuousOn_const.mul hGk2)
  have hIc : ContinuousOn I (Icc b0 b1) := hcI
  have hIg : ContinuousOn (fun v => I v * g v) (Icc b0 b1) := hIc.mul hg
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hb hΦc hΦd (hint _ hIg)
  have hΦ0 : 0 ≤ Φ b0 := by
    have h := hGr b0 (left_mem_Icc.mpr hb)
    simp only [hΦ_def]
    have hk : (k : ℝ) / ((k : ℝ) + 2) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    have hp : G b0 ^ (k + 2) ≤ G1 * G b0 ^ (k + 1) := by
      rw [pow_succ, mul_comm]; exact mul_le_mul_of_nonneg_right h.2 (pow_nonneg h.1 _)
    have hp0 : 0 ≤ G b0 ^ (k + 2) := pow_nonneg h.1 _
    have hk0 : 0 ≤ (k : ℝ) / ((k : ℝ) + 2) := by positivity
    nlinarith
  have hΦ1 : Φ b1 = 2 * G1 ^ (k + 2) / ((k : ℝ) + 2) := by
    simp only [hΦ_def]
    have hk2 : (k : ℝ) + 2 ≠ 0 := by positivity
    rw [show G1 * G1 ^ (k + 1) = G1 ^ (k + 2) by ring]
    field_simp; ring
  have hle : ∫ v in b0..b1, I v ≤ ∫ v in b0..b1, I v * g v / gmin := by
    apply intervalIntegral.integral_mono_on hb (hint _ hIc) (hint _ (hIg.div_const _))
    intro v hv
    have h0 : 0 ≤ I v := hI_nn v hv
    have : 1 ≤ g v / gmin := by rw [le_div_iff₀ hgmin]; linarith [hglo v hv]
    calc I v = I v * 1 := (mul_one _).symm
      _ ≤ I v * (g v / gmin) := mul_le_mul_of_nonneg_left this h0
      _ = I v * g v / gmin := by ring
  rw [intervalIntegral.integral_div, hFTC] at hle
  calc ∫ v in b0..b1, I v ≤ (Φ b1 - Φ b0) / gmin := hle
    _ ≤ Φ b1 / gmin := by
        apply div_le_div_of_nonneg_right _ hgmin.le; linarith
    _ = 2 * G b1 ^ (k + 1 + 1) / ((((k + 1 : ℕ) : ℝ) + 1) * gmin) := by
        rw [hΦ1]; push_cast
        have hk2 : (k : ℝ) + 2 ≠ 0 := by positivity
        field_simp; ring

/-! #### The localized power-integral lemma (P2) -/

/-- `F`-increment sandwich on a window where `|f - f0| ≤ ε`. -/
lemma br_F_diff_bound (M : Market) {x y f0 ε : ℝ} (hxa : M.a ≤ x) (hxy : x ≤ y) (hy1 : y ≤ 1)
    (hwin : ∀ t ∈ Icc x y, |M.f t - f0| ≤ ε) :
    (f0 - ε) * (y - x) ≤ M.F y - M.F x ∧ M.F y - M.F x ≤ (f0 + ε) * (y - x) := by
  rw [M.F_sub_eq_integral hxa hxy hy1]
  have hint : IntervalIntegrable M.f volume x y :=
    (M.hf_cont.mono (by rw [uIcc_of_le hxy]; exact Icc_subset_Icc hxa hy1)).intervalIntegrable
  constructor
  · have hc : ∫ _ in x..y, (f0 - ε) = (f0 - ε) * (y - x) := by
      rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
    rw [← hc]
    exact intervalIntegral.integral_mono_on hxy intervalIntegrable_const hint
      (fun t ht => by have := hwin t ht; rw [abs_le] at this; linarith [this.1])
  · have hc : ∫ _ in x..y, (f0 + ε) = (f0 + ε) * (y - x) := by
      rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
    rw [← hc]
    exact intervalIntegral.integral_mono_on hxy hint intervalIntegrable_const
      (fun t ht => by have := hwin t ht; rw [abs_le] at this; linarith [this.2])

/-- Deterministic form of the localized power-integral estimate. -/
lemma br_P2_det (M : Market) (n : ℕ) (hn : 1 ≤ n) {lam c α b f0 ε η fmin : ℝ}
    (hlam : 0 < lam) (hf0 : 0 < f0) (hε : 0 < ε) (hε2 : ε ≤ f0 / 2) (hη : 0 < η)
    (hf_lo : ∀ v ∈ Icc M.a 1, fmin ≤ M.f v)
    (hαa : M.a ≤ α) (hαb : α ≤ b) (hb1 : b ≤ 1) (hGα : 0 ≤ c + lam * M.F α)
    (hwin : ∀ t ∈ Icc (max α (b - η)) b, |M.f t - f0| ≤ ε) :
    |(n : ℝ) * (∫ v in α..b, (c + lam * M.F v) ^ (n - 1)) -
        ((c + lam * M.F b) ^ n - (c + lam * M.F α) ^ n) / (lam * f0)| ≤
      2 * ε * (c + lam * M.F b) ^ n / (lam * f0 ^ 2) +
        (n : ℝ) * (max 0 (c + lam * M.F b - lam * fmin * η)) ^ (n - 1) +
        (max 0 (c + lam * M.F b - lam * fmin * η)) ^ n / (lam * f0) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  set G : ℝ → ℝ := fun v => c + lam * M.F v with hG_def
  have hnR : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  set c' := max α (b - η) with hc'_def
  have hαc : α ≤ c' := le_max_left _ _
  have hcb : c' ≤ b := max_le hαb (by linarith)
  have ha0 := M.ha0
  have hGmono : ∀ x y, x ∈ Icc M.a 1 → y ∈ Icc M.a 1 → x ≤ y → G x ≤ G y := fun x y hx hy hxy => by
    have := M.F_strictMonoOn.monotoneOn hx hy hxy
    simp only [hG_def]; nlinarith
  have hmemI : ∀ v ∈ Icc α b, v ∈ Icc M.a 1 := fun v hv => ⟨le_trans hαa hv.1, le_trans hv.2 hb1⟩
  have hGnn : ∀ v ∈ Icc α b, 0 ≤ G v := fun v hv =>
    le_trans hGα (hGmono α v (hmemI α ⟨le_rfl, hαb⟩) (hmemI v hv) hv.1)
  have hFc : ContinuousOn M.F (Icc α b) := M.F_continuousOn.mono (Icc_subset_Icc hαa hb1)
  have hGc : ContinuousOn G (Icc α b) := continuousOn_const.add (continuousOn_const.mul hFc)
  have hGk : ContinuousOn (fun v => G v ^ k) (Icc α b) := hGc.pow _
  have hint1 : IntervalIntegrable (fun v => G v ^ k) volume α c' :=
    (hGk.mono (by rw [uIcc_of_le hαc]; exact Icc_subset_Icc le_rfl hcb)).intervalIntegrable
  have hint2 : IntervalIntegrable (fun v => G v ^ k) volume c' b :=
    (hGk.mono (by rw [uIcc_of_le hcb]; exact Icc_subset_Icc hαc le_rfl)).intervalIntegrable
  have hsplit : ∫ v in α..b, G v ^ k = (∫ v in α..c', G v ^ k) + ∫ v in c'..b, G v ^ k :=
    (intervalIntegral.integral_add_adjacent_intervals hint1 hint2).symm
  -- FTC on [c', b]
  have hfc : ContinuousOn M.f (Icc c' b) := M.hf_cont.mono (Icc_subset_Icc (le_trans hαa hαc) hb1)
  have hFTC : ∫ v in c'..b, G v ^ k * (lam * M.f v) = (G b ^ (k + 1) - G c' ^ (k + 1)) / ((k + 1 : ℕ) : ℝ) := by
    have hd : ∀ v ∈ Ioo c' b, HasDerivAt (fun v => G v ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) (G v ^ k * (lam * M.f v)) v := by
      intro v hv
      have hv' : v ∈ Ioo M.a 1 := ⟨lt_of_le_of_lt (le_trans hαa hαc) hv.1, lt_of_lt_of_le hv.2 hb1⟩
      have hGd : HasDerivAt G (lam * M.f v) v := ((M.hF_deriv_open v hv').const_mul lam).const_add c
      have h := (hGd.pow (k + 1)).div_const ((k + 1 : ℕ) : ℝ)
      convert h using 1
      simp only [Nat.add_sub_cancel]
      field_simp
    have hc2 : ContinuousOn (fun v => G v ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) (Icc c' b) :=
      ((hGc.mono (Icc_subset_Icc hαc le_rfl)).pow _).div_const _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hcb hc2 hd
      (((hGk.mono (Icc_subset_Icc hαc le_rfl)).mul (continuousOn_const.mul hfc)).mono
        (by rw [uIcc_of_le hcb])).intervalIntegrable]
    ring
  set I1 := ∫ v in c'..b, G v ^ k
  set X := G b ^ (k + 1) - G c' ^ (k + 1)
  have hGc'nn : 0 ≤ G c' := hGnn c' ⟨hαc, hcb⟩
  have hGc'b : G c' ≤ G b := hGmono c' b (hmemI c' ⟨hαc, hcb⟩) (hmemI b ⟨hαb, le_rfl⟩) hcb
  have hX0 : 0 ≤ X := by
    have := pow_le_pow_left₀ hGc'nn hGc'b (k + 1); simp only [X]; linarith
  have hXb : X ≤ G b ^ (k + 1) := by
    have := pow_nonneg hGc'nn (k + 1); simp only [X]; linarith
  have hlo : lam * (f0 - ε) * I1 ≤ X / ((k + 1 : ℕ) : ℝ) := by
    rw [← hFTC, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hcb
    · exact ((continuousOn_const.mul (hGk.mono (Icc_subset_Icc hαc le_rfl))).mono
        (by rw [uIcc_of_le hcb])).intervalIntegrable
    · exact (((hGk.mono (Icc_subset_Icc hαc le_rfl)).mul (continuousOn_const.mul hfc)).mono
        (by rw [uIcc_of_le hcb])).intervalIntegrable
    · intro t ht
      have h1 := hwin t ht
      rw [abs_le] at h1
      have hG0 : 0 ≤ G t ^ k := pow_nonneg (hGnn t ⟨le_trans hαc ht.1, ht.2⟩) _
      have : lam * (f0 - ε) ≤ lam * M.f t := mul_le_mul_of_nonneg_left (by linarith [h1.1]) hlam.le
      nlinarith
  have hhi : X / ((k + 1 : ℕ) : ℝ) ≤ lam * (f0 + ε) * I1 := by
    rw [← hFTC, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hcb
    · exact (((hGk.mono (Icc_subset_Icc hαc le_rfl)).mul (continuousOn_const.mul hfc)).mono
        (by rw [uIcc_of_le hcb])).intervalIntegrable
    · exact ((continuousOn_const.mul (hGk.mono (Icc_subset_Icc hαc le_rfl))).mono
        (by rw [uIcc_of_le hcb])).intervalIntegrable
    · intro t ht
      have h1 := hwin t ht
      rw [abs_le] at h1
      have hG0 : 0 ≤ G t ^ k := pow_nonneg (hGnn t ⟨le_trans hαc ht.1, ht.2⟩) _
      have : lam * M.f t ≤ lam * (f0 + ε) := mul_le_mul_of_nonneg_left (by linarith [h1.2]) hlam.le
      nlinarith
  have hfe : 0 < f0 - ε := by linarith
  -- error from I1
  have herr1 : |((k + 1 : ℕ) : ℝ) * I1 - X / (lam * f0)| ≤ 2 * ε * G b ^ (k + 1) / (lam * f0 ^ 2) := by
    have hup : ((k + 1 : ℕ) : ℝ) * I1 ≤ X / (lam * (f0 - ε)) := by
      rw [le_div_iff₀ (by positivity)]
      have := hlo; rw [le_div_iff₀ hnR] at this; nlinarith
    have hdn : X / (lam * (f0 + ε)) ≤ ((k + 1 : ℕ) : ℝ) * I1 := by
      rw [div_le_iff₀ (by positivity)]
      have := hhi; rw [div_le_iff₀ hnR] at this; nlinarith
    have hA1 : X / (lam * (f0 - ε)) - X / (lam * f0) ≤ 2 * ε * X / (lam * f0 ^ 2) := by
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      have hfac : (X * (lam * f0) - lam * (f0 - ε) * X) * (lam * f0 ^ 2) =
          X * ε * lam ^ 2 * f0 ^ 2 := by ring
      have hfac2 : 2 * ε * X * (lam * (f0 - ε) * (lam * f0)) =
          X * ε * lam ^ 2 * (2 * f0 * (f0 - ε)) := by ring
      rw [hfac, hfac2]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [hf0, hε2]
    have hA2 : X / (lam * f0) - X / (lam * (f0 + ε)) ≤ 2 * ε * X / (lam * f0 ^ 2) := by
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      have hfac : (X * (lam * (f0 + ε)) - lam * f0 * X) * (lam * f0 ^ 2) =
          X * ε * lam ^ 2 * f0 ^ 2 := by ring
      have hfac2 : 2 * ε * X * (lam * f0 * (lam * (f0 + ε))) =
          X * ε * lam ^ 2 * (2 * f0 * (f0 + ε)) := by ring
      rw [hfac, hfac2]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [hf0, hε]
    have hA3 : 2 * ε * X / (lam * f0 ^ 2) ≤ 2 * ε * G b ^ (k + 1) / (lam * f0 ^ 2) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hXb (by positivity)
    rw [abs_le]; constructor <;> linarith
  set K := max 0 (G b - lam * fmin * η)
  have hK0 : 0 ≤ K := le_max_left _ _
  have hfin : 0 ≤ 2 * ε * G b ^ (k + 1) / (lam * f0 ^ 2) := by
    have : 0 ≤ G b := hGnn b ⟨hαb, le_rfl⟩; positivity
  rw [hsplit]
  by_cases hcase : b - η ≤ α
  · have hc'α : c' = α := max_eq_left hcase
    have hI0 : ∫ v in α..c', G v ^ k = 0 := by rw [hc'α]; exact intervalIntegral.integral_same
    rw [hI0, zero_add]
    have hXα : X = G b ^ (k + 1) - G α ^ (k + 1) := by simp only [X, hc'α]
    rw [← hXα]
    have h1 : 0 ≤ ((k + 1 : ℕ) : ℝ) * K ^ k := by positivity
    have h2 : 0 ≤ K ^ (k + 1) / (lam * f0) := by positivity
    linarith
  · push Not at hcase
    have hc'b : c' = b - η := max_eq_right hcase.le
    have hbη_mem : b - η ∈ Icc M.a 1 := ⟨le_trans hαa hcase.le, by linarith⟩
    have hGc'K : G c' ≤ K := by
      obtain ⟨fmax, _, hf_hi⟩ := M.exists_f_max
      have hlip := (M.F_lipschitz_bounds hbη_mem (hmemI b ⟨hαb, le_rfl⟩) (by linarith) hf_lo hf_hi).1
      have : G c' ≤ G b - lam * fmin * η := by
        rw [hc'b]; simp only [hG_def]
        have := mul_le_mul_of_nonneg_left hlip hlam.le
        nlinarith
      exact le_trans this (le_max_right _ _)
    have hI0_nn : 0 ≤ ∫ v in α..c', G v ^ k :=
      intervalIntegral.integral_nonneg hαc (fun v hv => pow_nonneg (hGnn v ⟨hv.1, le_trans hv.2 hcb⟩) _)
    have hI0_le : ∫ v in α..c', G v ^ k ≤ K ^ k := by
      have hle : ∫ v in α..c', G v ^ k ≤ ∫ _ in α..c', G c' ^ k :=
        intervalIntegral.integral_mono_on hαc hint1 intervalIntegrable_const (fun v hv =>
          pow_le_pow_left₀ (hGnn v ⟨hv.1, le_trans hv.2 hcb⟩)
            (hGmono v c' (hmemI v ⟨hv.1, le_trans hv.2 hcb⟩) (hmemI c' ⟨hαc, hcb⟩) hv.2) _)
      rw [intervalIntegral.integral_const, smul_eq_mul] at hle
      have hlen : c' - α ≤ 1 := by linarith only [hb1, hcb, hαa, ha0]
      have hp : G c' ^ k ≤ K ^ k := pow_le_pow_left₀ hGc'nn hGc'K _
      have hp0 : 0 ≤ G c' ^ k := pow_nonneg hGc'nn _
      have hlen0 : 0 ≤ c' - α := by linarith only [hαc]
      nlinarith only [hle, hlen, hp, hp0, hlen0]
    have hGα_le : G α ≤ G c' := hGmono α c' (hmemI α ⟨le_rfl, hαb⟩) (hmemI c' ⟨hαc, hcb⟩) hαc
    have hpow1 : G α ^ (k + 1) ≤ G c' ^ (k + 1) := pow_le_pow_left₀ hGα hGα_le _
    have hpow2 : G c' ^ (k + 1) ≤ K ^ (k + 1) := pow_le_pow_left₀ hGc'nn hGc'K _
    have hpow3 : 0 ≤ G α ^ (k + 1) := pow_nonneg hGα _
    have hdiff : 0 ≤ (G c' ^ (k + 1) - G α ^ (k + 1)) / (lam * f0) ∧
        (G c' ^ (k + 1) - G α ^ (k + 1)) / (lam * f0) ≤ K ^ (k + 1) / (lam * f0) := by
      constructor
      · apply div_nonneg (by linarith) (by positivity)
      · apply div_le_div_of_nonneg_right (by linarith) (by positivity)
    have hid : ((k + 1 : ℕ) : ℝ) * ((∫ v in α..c', G v ^ k) + I1) -
        (G b ^ (k + 1) - G α ^ (k + 1)) / (lam * f0) =
        (((k + 1 : ℕ) : ℝ) * I1 - X / (lam * f0)) + ((k + 1 : ℕ) : ℝ) * (∫ v in α..c', G v ^ k) -
          (G c' ^ (k + 1) - G α ^ (k + 1)) / (lam * f0) := by
      simp only [X]; field_simp; ring
    rw [hid]
    have hI0n : ((k + 1 : ℕ) : ℝ) * (∫ v in α..c', G v ^ k) ≤ ((k + 1 : ℕ) : ℝ) * K ^ k :=
      mul_le_mul_of_nonneg_left hI0_le hnR.le
    have hI0n' : 0 ≤ ((k + 1 : ℕ) : ℝ) * (∫ v in α..c', G v ^ k) := mul_nonneg hnR.le hI0_nn
    rw [abs_le] at herr1 ⊢
    constructor <;> linarith only [herr1.1, herr1.2, hdiff.1, hdiff.2, hI0n, hI0n']

/-! #### Limit wrappers (`br_P2_limit`, `br_exp_pow_tendsto`) and small-`u` `sinh`/`log` Taylor bounds -/

/-- `(1 + x n / n)^n → exp L` and `(1 + x n / n)^(n - 1) → exp L` whenever `x n → L`. -/
lemma br_exp_pow_tendsto {x : ℕ → ℝ} {L : ℝ} (hx : Tendsto x atTop (nhds L)) :
    Tendsto (fun n : ℕ => (1 + x n / (n : ℝ)) ^ n) atTop (nhds (Real.exp L)) ∧
    Tendsto (fun n : ℕ => (1 + x n / (n : ℝ)) ^ (n - 1)) atTop (nhds (Real.exp L)) := by
  have hmain : Tendsto (fun n : ℕ => (1 + x n / (n : ℝ)) ^ n) atTop (nhds (Real.exp L)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hexp_c := Metric.continuousAt_iff.mp (Real.continuous_exp.continuousAt (x := L)) (ε / 2) (by linarith)
    obtain ⟨δ, hδ, hδp⟩ := hexp_c
    have hlo_t := Real.tendsto_one_add_div_pow_exp (L - δ / 2)
    have hhi_t := Real.tendsto_one_add_div_pow_exp (L + δ / 2)
    have hx_ev : ∀ᶠ n : ℕ in atTop, L - δ / 2 ≤ x n ∧ x n ≤ L + δ / 2 := by
      filter_upwards [Metric.tendsto_nhds.mp hx (δ / 2) (by linarith)] with n hn
      rw [Real.dist_eq, abs_lt] at hn
      exact ⟨by linarith, by linarith⟩
    have hpos_ev : ∀ᶠ n : ℕ in atTop, 0 ≤ 1 + (L - δ / 2) / (n : ℝ) := by
      have h0 : Tendsto (fun n : ℕ => 1 + (L - δ / 2) / (n : ℝ)) atTop (nhds (1 + 0)) :=
        tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
      rw [add_zero] at h0
      filter_upwards [h0.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))] with n hn using le_of_lt hn
    have hlo_ev := Metric.tendsto_nhds.mp hlo_t (ε / 2) (by linarith)
    have hhi_ev := Metric.tendsto_nhds.mp hhi_t (ε / 2) (by linarith)
    have hdl : |Real.exp (L - δ / 2) - Real.exp L| < ε / 2 := by
      have := hδp (by rw [Real.dist_eq, show (L - δ / 2) - L = -(δ / 2) by ring, abs_neg, abs_of_pos (by linarith)]; linarith)
      rwa [Real.dist_eq] at this
    have hdh : |Real.exp (L + δ / 2) - Real.exp L| < ε / 2 := by
      have := hδp (by rw [Real.dist_eq, show (L + δ / 2) - L = δ / 2 by ring, abs_of_pos (by linarith)]; linarith)
      rwa [Real.dist_eq] at this
    filter_upwards [hx_ev, hpos_ev, hlo_ev, hhi_ev] with n hxn hpos hlo hhi
    rw [Real.dist_eq] at hlo hhi ⊢
    have h1 : (1 + (L - δ / 2) / (n : ℝ)) ^ n ≤ (1 + x n / (n : ℝ)) ^ n :=
      pow_le_pow_left₀ hpos (by gcongr; exact hxn.1) n
    have h2 : (1 + x n / (n : ℝ)) ^ n ≤ (1 + (L + δ / 2) / (n : ℝ)) ^ n :=
      pow_le_pow_left₀ (le_trans hpos (by gcongr; exact hxn.1)) (by gcongr; exact hxn.2) n
    rw [abs_lt] at hlo hhi hdl hdh ⊢
    constructor <;> linarith
  refine ⟨hmain, ?_⟩
  have h1 : Tendsto (fun n : ℕ => 1 + x n / (n : ℝ)) atTop (nhds 1) := by
    have h := tendsto_const_nhds (x := (1 : ℝ)).add (hx.div_atTop tendsto_natCast_atTop_atTop)
    simpa using h
  have hdiv := hmain.div h1 one_ne_zero
  rw [div_one] at hdiv
  refine hdiv.congr' ?_
  filter_upwards [eventually_ge_atTop 1, h1.eventually (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))] with n hn hpos
  have hne : (1 + x n / (n : ℝ)) ≠ 0 := by linarith
  have hpow : (1 + x n / (n : ℝ)) ^ n = (1 + x n / (n : ℝ)) ^ (n - 1) * (1 + x n / (n : ℝ)) := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  simp only [Pi.div_apply]
  rw [hpow, mul_div_cancel_right₀ _ hne]

/-- Asymptotic limit of the localized power integral `n * (∫_{α_n}^{b_n} (c_n + lam * F v)^(n-1)) / (c_n + lam * F(b_n))^n`. -/
lemma br_P2_limit (M : Market) (ha : M.a = 0) {lam rH G_lim δ₀ : ℝ}
    (hlam : 0 < lam) (hrH0 : 0 < rH) (hrH1 : rH < 1) (hGlim : 0 < G_lim) (hδ₀ : 0 < δ₀)
    {α b c : ℕ → ℝ} (hb : Tendsto b atTop (nhds rH))
    (hGb : Tendsto (fun n => c n + lam * M.F (b n)) atTop (nhds G_lim))
    (hdom : ∀ᶠ n : ℕ in atTop, 0 ≤ α n ∧ α n ≤ b n ∧ b n ≤ 1 ∧ 0 ≤ c n + lam * M.F (α n))
    (hsep : ∀ᶠ n : ℕ in atTop, α n ≤ rH - δ₀) :
    Tendsto (fun n : ℕ =>
      ((n : ℝ) * ∫ v in α n..b n, (c n + lam * M.F v) ^ (n - 1)) /
        (c n + lam * M.F (b n)) ^ n) atTop (nhds (1 / (lam * M.f rH))) := by
  obtain ⟨fmin, hfmin, hf_lo⟩ := M.exists_f_min
  have hfH : 0 < M.f rH := M.hf_pos rH ⟨by linarith, hrH1.le⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  let ε₁ := min (M.f rH / 2) (ε * lam * M.f rH ^ 2 / 8)
  have hε₁ : 0 < ε₁ := lt_min (by positivity) (by positivity)
  have hε₁2 : ε₁ ≤ M.f rH / 2 := min_le_left _ _
  have hfc := Metric.continuousWithinAt_iff.mp (M.hf_cont rH ⟨by linarith, hrH1.le⟩) ε₁ hε₁
  obtain ⟨δ₁, hδ₁, hfδ⟩ := hfc
  let η := min (δ₁ / 3) (min (δ₀ / 2) (G_lim / (4 * lam * fmin)))
  have hη : 0 < η := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hη_le1 : η ≤ δ₁ / 3 := min_le_left _ _
  have hη_le2 : η ≤ δ₀ / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hη_le3 : η ≤ G_lim / (4 * lam * fmin) := le_trans (min_le_right _ _) (min_le_right _ _)
  let r_ratio := 1 - lam * fmin * η / (2 * G_lim)
  have hr_lt1 : r_ratio < 1 := by dsimp [r_ratio]; linarith [show 0 < lam * fmin * η / (2 * G_lim) by positivity]
  have hr_nn : 0 ≤ r_ratio := by
    dsimp [r_ratio]
    have hmul : η * (4 * lam * fmin) ≤ G_lim := (le_div_iff₀ (by positivity)).mp hη_le3
    have hdiv : lam * fmin * η / (2 * G_lim) ≤ 1 / 8 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    linarith
  have hpow0 : Tendsto (fun n : ℕ => r_ratio ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr_nn hr_lt1
  have hnpow0 : Tendsto (fun n : ℕ => (n : ℝ) * r_ratio ^ (n - 1)) atTop (nhds 0) := by
    have h := tendsto_self_mul_const_pow_of_lt_one hr_nn hr_lt1
    have hshift : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * r_ratio ^ n) atTop (nhds 0) := by
      have h2 := h.add hpow0
      rw [add_zero] at h2
      exact h2.congr (fun n => by push_cast; ring)
    have hsub := hshift.comp (tendsto_sub_atTop_nat 1)
    refine hsub.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp only [Function.comp_apply, Nat.sub_add_cancel hn]
  have hb_near : ∀ᶠ n : ℕ in atTop, |b n - rH| < min (δ₁ / 3) (δ₀ / 2) := by
    filter_upwards [Metric.tendsto_nhds.mp hb (min (δ₁ / 3) (δ₀ / 2)) (lt_min (by positivity) (by positivity))] with n hn
    rwa [Real.dist_eq] at hn
  have hGb_near : ∀ᶠ n : ℕ in atTop, G_lim / 2 ≤ c n + lam * M.F (b n) ∧ c n + lam * M.F (b n) ≤ 2 * G_lim := by
    filter_upwards [Metric.tendsto_nhds.mp hGb (G_lim / 2) (by positivity)] with n hn
    rw [Real.dist_eq, abs_lt] at hn
    exact ⟨by linarith, by linarith⟩
  have h_r_ev := Metric.tendsto_nhds.mp hpow0 (ε * lam * M.f rH / 8) (by positivity)
  have h_nr_ev := Metric.tendsto_nhds.mp hnpow0 (ε * G_lim / 8) (by positivity)
  filter_upwards [eventually_ge_atTop 1, hdom, hsep, hb_near, hGb_near, h_r_ev, h_nr_ev]
    with n hn hdn hsepn hbn hGbn hrn hnrn
  set Gb := c n + lam * M.F (b n)
  set Gα := c n + lam * M.F (α n)
  have hGb_pos : 0 < Gb := by linarith [hGbn.1]
  have hwin : ∀ t ∈ Icc (max (α n) (b n - η)) (b n), |M.f t - M.f rH| ≤ ε₁ := by
    intro t ht
    have htb : b n - η ≤ t := le_trans (le_max_right _ _) ht.1
    have hdist : dist t rH < δ₁ := by
      rw [Real.dist_eq]
      have h1 : |b n - rH| < δ₁ / 3 := lt_of_lt_of_le hbn (min_le_left _ _)
      rw [abs_lt] at h1 ⊢
      constructor <;> linarith [ht.2, htb, hη_le1]
    have htmem : t ∈ Icc M.a 1 := ⟨by rw [ha]; exact le_trans hdn.1 (le_trans (le_max_left _ _) ht.1), le_trans ht.2 hdn.2.2.1⟩
    exact (le_of_lt (by simpa [Real.dist_eq] using hfδ htmem hdist))
  have hdet := br_P2_det M n hn hlam hfH hε₁ hε₁2 hη hf_lo (by rw [ha]; exact hdn.1) hdn.2.1 hdn.2.2.1 hdn.2.2.2 hwin
  -- Also Gα ≤ max 0 (Gb - lam * fmin * η) ≤ r_ratio * Gb
  have hα_le : α n ≤ b n - η := by
    have h1 : |b n - rH| < δ₀ / 2 := lt_of_lt_of_le hbn (min_le_right _ _)
    rw [abs_lt] at h1; linarith [hsepn, hη_le2]
  have hGα_le : Gα ≤ Gb - lam * fmin * η := by
    obtain ⟨fmax, _, hf_hi⟩ := M.exists_f_max
    have hα_mem : α n ∈ Icc M.a 1 := ⟨by rw [ha]; exact hdn.1, le_trans hdn.2.1 hdn.2.2.1⟩
    have hb_mem : b n ∈ Icc M.a 1 := ⟨by rw [ha]; exact le_trans hdn.1 hdn.2.1, hdn.2.2.1⟩
    have hlip := (M.F_lipschitz_bounds hα_mem hb_mem hdn.2.1 hf_lo hf_hi).1
    have h1 : lam * fmin * η ≤ lam * (M.F (b n) - M.F (α n)) := by
      have : fmin * η ≤ M.F (b n) - M.F (α n) := le_trans (mul_le_mul_of_nonneg_left (by linarith) hfmin.le) hlip
      nlinarith
    dsimp [Gα, Gb]; linarith
  set K := max 0 (Gb - lam * fmin * η)
  have hK_nn : 0 ≤ K := le_max_left _ _
  have hGα_K : Gα ≤ K := le_trans hGα_le (le_max_right _ _)
  have hK_le : K ≤ r_ratio * Gb := by
    apply max_le (mul_nonneg hr_nn hGb_pos.le)
    dsimp [r_ratio]
    have h1 : lam * fmin * η / (2 * G_lim) * Gb ≤ lam * fmin * η := by
      have : Gb / (2 * G_lim) ≤ 1 := by rw [div_le_one (by positivity)]; exact hGbn.2
      calc lam * fmin * η / (2 * G_lim) * Gb = lam * fmin * η * (Gb / (2 * G_lim)) := by ring
        _ ≤ lam * fmin * η * 1 := mul_le_mul_of_nonneg_left this (by positivity)
        _ = lam * fmin * η := mul_one _
    linarith
  have hK_div : K / Gb ≤ r_ratio := (div_le_iff₀ hGb_pos).mpr hK_le
  have hK_div_nn : 0 ≤ K / Gb := div_nonneg hK_nn hGb_pos.le
  have hGbn_pos : 0 < Gb ^ n := pow_pos hGb_pos n
  have hdiv := div_le_div_of_nonneg_right hdet hGbn_pos.le
  have hLHS : |((n : ℝ) * ∫ v in α n..b n, (c n + lam * M.F v) ^ (n - 1)) -
      (Gb ^ n - Gα ^ n) / (lam * M.f rH)| / Gb ^ n =
      |((n : ℝ) * ∫ v in α n..b n, (c n + lam * M.F v) ^ (n - 1)) / Gb ^ n -
        1 / (lam * M.f rH) + (Gα / Gb) ^ n / (lam * M.f rH)| := by
    rw [show |((n : ℝ) * ∫ v in α n..b n, (c n + lam * M.F v) ^ (n - 1)) -
        (Gb ^ n - Gα ^ n) / (lam * M.f rH)| / Gb ^ n =
        |(((n : ℝ) * ∫ v in α n..b n, (c n + lam * M.F v) ^ (n - 1)) -
          (Gb ^ n - Gα ^ n) / (lam * M.f rH)) / Gb ^ n| by rw [abs_div, abs_of_pos hGbn_pos]]
    congr 1
    rw [div_pow]
    field_simp [hGbn_pos.ne', hlam.ne', hfH.ne']
    ring
  rw [hLHS] at hdiv
  have hGα_pow : (Gα / Gb) ^ n ≤ r_ratio ^ n :=
    pow_le_pow_left₀ (div_nonneg hdn.2.2.2 hGb_pos.le) (le_trans (div_le_div_of_nonneg_right hGα_K hGb_pos.le) hK_div) n
  have hK_pow_n : K ^ n / Gb ^ n ≤ r_ratio ^ n := by
    rw [← div_pow]; exact pow_le_pow_left₀ hK_div_nn hK_div n
  have hK_pow_n1 : (n : ℝ) * K ^ (n - 1) / Gb ^ n ≤ (2 / G_lim) * ((n : ℝ) * r_ratio ^ (n - 1)) := by
    have hGb_split : Gb ^ n = Gb ^ (n - 1) * Gb := by rw [← pow_succ, Nat.sub_add_cancel hn]
    rw [hGb_split]
    have h1 : K ^ (n - 1) / Gb ^ (n - 1) ≤ r_ratio ^ (n - 1) := by
      rw [← div_pow]; exact pow_le_pow_left₀ hK_div_nn hK_div (n - 1)
    have h2 : 1 / Gb ≤ 2 / G_lim := by
      rw [div_le_div_iff₀ hGb_pos hGlim]; linarith [hGbn.1]
    have hid : (n : ℝ) * K ^ (n - 1) / (Gb ^ (n - 1) * Gb) =
        (1 / Gb) * ((n : ℝ) * (K ^ (n - 1) / Gb ^ (n - 1))) := by field_simp [hGb_pos.ne']
    rw [hid]
    exact mul_le_mul h2 (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg n))
      (mul_nonneg (Nat.cast_nonneg n) (div_nonneg (pow_nonneg hK_nn _) (pow_pos hGb_pos _).le)) (by positivity)
  have hT1 : (2 * ε₁ * Gb ^ n / (lam * M.f rH ^ 2)) / Gb ^ n ≤ ε / 4 := by
    have heq : (2 * ε₁ * Gb ^ n / (lam * M.f rH ^ 2)) / Gb ^ n = 2 * ε₁ / (lam * M.f rH ^ 2) := by
      field_simp [hGbn_pos.ne', hlam.ne', hfH.ne']
    rw [heq, div_le_iff₀ (by positivity)]
    have hε₁_le : ε₁ ≤ ε * lam * M.f rH ^ 2 / 8 := min_le_right _ _
    nlinarith
  have hT2 : ((n : ℝ) * K ^ (n - 1)) / Gb ^ n < ε / 4 := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hnrn
    calc ((n : ℝ) * K ^ (n - 1)) / Gb ^ n ≤ (2 / G_lim) * ((n : ℝ) * r_ratio ^ (n - 1)) := hK_pow_n1
      _ < (2 / G_lim) * (ε * G_lim / 8) := mul_lt_mul_of_pos_left hnrn (by positivity)
      _ = ε / 4 := by field_simp [hGlim.ne']; ring
  have hT3 : (K ^ n / (lam * M.f rH)) / Gb ^ n < ε / 8 := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (pow_nonneg hr_nn n)] at hrn
    have heq : (K ^ n / (lam * M.f rH)) / Gb ^ n = (K ^ n / Gb ^ n) / (lam * M.f rH) := by ring
    rw [heq, div_lt_iff₀ (by positivity)]
    calc K ^ n / Gb ^ n ≤ r_ratio ^ n := hK_pow_n
      _ < ε * lam * M.f rH / 8 := hrn
      _ = ε / 8 * (lam * M.f rH) := by ring
  have hT4 : |(Gα / Gb) ^ n / (lam * M.f rH)| < ε / 8 := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (pow_nonneg hr_nn n)] at hrn
    rw [abs_of_nonneg (div_nonneg (pow_nonneg (div_nonneg hdn.2.2.2 hGb_pos.le) n) (by positivity)),
      div_lt_iff₀ (by positivity)]
    calc (Gα / Gb) ^ n ≤ r_ratio ^ n := hGα_pow
      _ < ε * lam * M.f rH / 8 := hrn
      _ = ε / 8 * (lam * M.f rH) := by ring
  rw [Real.dist_eq]
  have htri : |((n : ℝ) * ∫ v in α n..b n, (c n + lam * M.F v) ^ (n - 1)) / Gb ^ n - 1 / (lam * M.f rH)| ≤
      |((n : ℝ) * ∫ v in α n..b n, (c n + lam * M.F v) ^ (n - 1)) / Gb ^ n - 1 / (lam * M.f rH) +
        (Gα / Gb) ^ n / (lam * M.f rH)| + |(Gα / Gb) ^ n / (lam * M.f rH)| := by
    have h := abs_add_le
      (((n : ℝ) * ∫ v in α n..b n, (c n + lam * M.F v) ^ (n - 1)) / Gb ^ n - 1 / (lam * M.f rH) +
        (Gα / Gb) ^ n / (lam * M.f rH))
      (-((Gα / Gb) ^ n / (lam * M.f rH)))
    rw [add_neg_cancel_right, abs_neg] at h
    exact h
  have hRHS_eq : (2 * ε₁ * Gb ^ n / (lam * M.f rH ^ 2) + (n : ℝ) * K ^ (n - 1) + K ^ n / (lam * M.f rH)) / Gb ^ n =
      (2 * ε₁ * Gb ^ n / (lam * M.f rH ^ 2)) / Gb ^ n + ((n : ℝ) * K ^ (n - 1)) / Gb ^ n + (K ^ n / (lam * M.f rH)) / Gb ^ n := by ring
  rw [hRHS_eq] at hdiv
  linarith only [hdiv, htri, hT1, hT2, hT3, hT4, hε]

/-! #### Small-`u` Taylor bounds for `γ = -log(sinh u / u)` and eq. (22) -/

/-- `γ(u) = -log(sinh u / u)`, so `exp(-γ(u)) = sinh u / u`. -/
noncomputable def br_gamma (u : ℝ) : ℝ := -Real.log (Real.sinh u / u)

/-- First coefficient `(1 - u - γ) * exp(-γ) - exp(-u)` in eq. (22). -/
noncomputable def br_coeff1 (u : ℝ) : ℝ :=
  (1 - u - br_gamma u) * Real.exp (-br_gamma u) - Real.exp (-u)

/-- Second coefficient `(γ - u) * exp(-γ) + exp u - 1` in eq. (22). -/
noncomputable def br_coeff2 (u : ℝ) : ℝ :=
  (br_gamma u - u) * Real.exp (-br_gamma u) + Real.exp u - 1

/-- Rescaled revenue-gain limit from eq. (22) in Appendix B. -/
noncomputable def br_asymLimit (M : Market) (rH u : ℝ) : ℝ :=
  rH * br_coeff1 u + ((1 - M.F rH) / (2 * M.f rH)) * br_coeff2 u

lemma br_sinh_div_bounds {u : ℝ} (hu : 0 < u) :
    1 < Real.sinh u / u ∧ Real.sinh u / u < Real.exp u ∧
    Real.exp (-br_gamma u) = Real.sinh u / u ∧
    -u < br_gamma u ∧ br_gamma u < 0 := by
  have hsinh_gt : u < Real.sinh u := by
    have hd : ∀ t ∈ Ioo (0 : ℝ) u, HasDerivAt (fun x => Real.sinh x - x) (Real.cosh t - 1) t := by
      intro t _
      have hs : HasDerivAt Real.sinh (Real.cosh t) t := by
        have h1 : Real.sinh = fun x => (Real.exp x - Real.exp (-x)) / 2 := by ext x; exact Real.sinh_eq x
        rw [h1, Real.cosh_eq]
        have h := ((Real.hasDerivAt_exp t).sub ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t))).div_const 2
        convert h using 1
        · ext x; simp
        · ring
      exact hs.sub (hasDerivAt_id t)
    have hcont : ContinuousOn (fun x => Real.sinh x - x) (Icc 0 u) :=
      (Real.continuous_sinh.sub continuous_id).continuousOn
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (fun x => Real.sinh x - x)
      (fun t => Real.cosh t - 1) hu hcont hd
    have hcosh : 1 < Real.cosh c := by
      rw [Real.cosh_eq]
      have h1 : 1 < Real.exp c := Real.one_lt_exp_iff.mpr hc.1
      have h2 : Real.exp (-c) = (Real.exp c)⁻¹ := Real.exp_neg c
      rw [h2]
      have hpos : 0 < Real.exp c := Real.exp_pos c
      have : (Real.exp c - 1) ^ 2 > 0 := sq_pos_of_pos (by linarith)
      have hmul : (Real.exp c + (Real.exp c)⁻¹) * Real.exp c = Real.exp c ^ 2 + 1 := by
        field_simp [hpos.ne']
      nlinarith
    simp only [Real.sinh_zero, sub_zero] at hslope
    rw [eq_div_iff hu.ne'] at hslope
    nlinarith
  have h1 : 1 < Real.sinh u / u := (one_lt_div hu).mpr hsinh_gt
  have h2 : Real.sinh u / u < Real.exp u := by
    rw [div_lt_iff₀ hu, Real.sinh_eq]
    have hmul : 1 < 2 * u + Real.exp (-2 * u) := by
      have := Real.add_one_lt_exp (show (-2 * u : ℝ) ≠ 0 by linarith)
      linarith
    have hpos : 0 < Real.exp u := Real.exp_pos u
    have hprod : Real.exp u * Real.exp (-2 * u) = Real.exp (-u) := by
      rw [← Real.exp_add]; congr 1; ring
    have hstep := mul_lt_mul_of_pos_left hmul hpos
    rw [mul_one, mul_add, hprod] at hstep
    linarith
  have hexp : Real.exp (-br_gamma u) = Real.sinh u / u := by
    unfold br_gamma; rw [neg_neg, Real.exp_log (by linarith)]
  have hgt : -u < br_gamma u := by
    have : Real.exp (-br_gamma u) < Real.exp u := by rwa [hexp]
    linarith [Real.exp_lt_exp.mp this]
  have hlt : br_gamma u < 0 := by
    have : Real.exp 0 < Real.exp (-br_gamma u) := by rw [Real.exp_zero, hexp]; exact h1
    linarith [Real.exp_lt_exp.mp this]
  exact ⟨h1, h2, hexp, hgt, hlt⟩

lemma br_asymLimit_psi2_zero (M : Market) (hm : M.m = 2) {rH u : ℝ} (hu : 0 < u)
    (hpsi : M.psi rH = 0) :
    br_asymLimit M rH u = rH * (Real.sinh u / u - 1) := by
  have hrH_eq : (1 - M.F rH) / (2 * M.f rH) = rH := by
    unfold Market.psi at hpsi
    rw [hm] at hpsi; push_cast at hpsi; linarith
  have hb := br_sinh_div_bounds hu
  unfold br_asymLimit br_coeff1 br_coeff2
  rw [hrH_eq, hb.2.2.1]
  have hsinh : 2 * u * (Real.sinh u / u) = Real.exp u - Real.exp (-u) := by
    rw [Real.sinh_eq]; field_simp [hu.ne']
  linear_combination -rH * hsinh

lemma br_exp_taylor5 {x : ℝ} (hx : |x| ≤ 1) :
    |Real.exp x - (1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24)| ≤ |x| ^ 5 / 100 := by
  have hb := Real.exp_bound hx (n := 5) (by decide)
  have hsum : ∑ m ∈ Finset.range 5, x ^ m / (m.factorial : ℝ) =
      1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]; norm_num
  rw [hsum] at hb
  have hcoef : ((5 : ℕ).succ : ℝ) / (((5 : ℕ).factorial : ℝ) * (5 : ℕ)) = 1 / 100 := by
    norm_num [Nat.factorial]
  rw [hcoef] at hb
  linarith

lemma br_asymLimit_taylor (M : Market) (rH : ℝ) :
    ∃ C₁ ≥ 0, ∃ C₂ ≥ 0, ∀ u ∈ Ioc (0 : ℝ) (1 / 2),
      |br_coeff1 u - (-(u ^ 2 / 6))| ≤ C₁ * u ^ 4 ∧
      |br_coeff2 u - (u ^ 2 / 3)| ≤ C₂ * u ^ 4 ∧
      |br_asymLimit M rH u - (-(u ^ 2 / 6) * M.psi1 rH)| ≤
        (|rH| * C₁ + |(1 - M.F rH) / (2 * M.f rH)| * C₂) * u ^ 4 := by
  refine ⟨10, by norm_num, 10, by norm_num, fun u hu => ?_⟩
  have hu0 : 0 < u := hu.1
  have hu1 : u ≤ 1 / 2 := hu.2
  have hu_le1 : |u| ≤ 1 := by rw [abs_of_pos hu0]; linarith
  have hnu_le1 : |-u| ≤ 1 := by rw [abs_neg]; exact hu_le1
  have hep := br_exp_taylor5 hu_le1
  have hem := br_exp_taylor5 hnu_le1
  rw [abs_of_pos hu0] at hep
  rw [abs_neg, abs_of_pos hu0] at hem
  set S := Real.sinh u / u
  have hS_bound : |S - (1 + u ^ 2 / 6)| ≤ u ^ 4 / 100 := by
    have hdiff : S - (1 + u ^ 2 / 6) =
        ((Real.exp u - (1 + u + u ^ 2 / 2 + u ^ 3 / 6 + u ^ 4 / 24)) -
          (Real.exp (-u) - (1 + (-u) + (-u) ^ 2 / 2 + (-u) ^ 3 / 6 + (-u) ^ 4 / 24))) / (2 * u) := by
      dsimp [S]; rw [Real.sinh_eq]; field_simp [hu0.ne']; ring
    rw [hdiff, abs_div, abs_of_pos (by positivity : 0 < 2 * u), div_le_iff₀ (by positivity)]
    have htri := abs_sub_le
      (Real.exp u - (1 + u + u ^ 2 / 2 + u ^ 3 / 6 + u ^ 4 / 24)) 0
      (Real.exp (-u) - (1 + (-u) + (-u) ^ 2 / 2 + (-u) ^ 3 / 6 + (-u) ^ 4 / 24))
    simp only [sub_zero, zero_sub, abs_neg] at htri
    nlinarith only [htri, hep, hem, hu0]
  set x := 1 - S
  have hx_bound : |x| ≤ u ^ 2 / 4 := by
    have h1 : |S - 1| ≤ u ^ 2 / 6 + u ^ 4 / 100 := by
      have h := abs_add_le (S - (1 + u ^ 2 / 6)) (u ^ 2 / 6)
      rw [show S - (1 + u ^ 2 / 6) + u ^ 2 / 6 = S - 1 by ring, abs_of_pos (by positivity : 0 < u ^ 2 / 6)] at h
      linarith only [h, hS_bound]
    have hx_eq : |x| = |S - 1| := by dsimp [x]; rw [abs_sub_comm]
    rw [hx_eq]
    have hu4 : u ^ 4 ≤ u ^ 2 / 4 := by
      have : u ^ 2 ≤ 1 / 4 := by nlinarith only [hu0, hu1]
      nlinarith only [this, sq_nonneg u]
    linarith only [h1, hu4, sq_nonneg u]
  have hx_lt1 : |x| < 1 := by
    have : u ^ 2 ≤ 1 / 4 := by nlinarith only [hu0, hu1]
    linarith only [hx_bound, this]
  have hlog := Real.abs_log_sub_add_sum_range_le hx_lt1 1
  simp only [Finset.sum_range_one, zero_add, pow_one, Nat.cast_zero, div_one] at hlog
  have h1x : 1 - x = S := by dsimp [x]; ring
  rw [h1x] at hlog
  have hγ_eq : br_gamma u = -Real.log S := rfl
  have hlog_b : |x + Real.log S| ≤ u ^ 4 / 8 := by
    have hnum : |x| ^ 2 ≤ u ^ 4 / 16 := by
      calc |x| ^ 2 ≤ (u ^ 2 / 4) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hx_bound 2
        _ = u ^ 4 / 16 := by ring
    have hden : 1 / 2 ≤ 1 - |x| := by
      have : u ^ 2 ≤ 1 / 4 := by nlinarith only [hu0, hu1]
      linarith only [hx_bound, this]
    calc |x + Real.log S| ≤ |x| ^ 2 / (1 - |x|) := hlog
      _ ≤ (u ^ 4 / 16) / (1 / 2) := div_le_div₀ (by positivity) hnum (by positivity) hden
      _ = u ^ 4 / 8 := by ring
  have hγ_bound : |br_gamma u + u ^ 2 / 6| ≤ u ^ 4 / 4 := by
    have hid : br_gamma u + u ^ 2 / 6 = -(x + Real.log S) + -(S - (1 + u ^ 2 / 6)) := by
      rw [hγ_eq]; dsimp [x]; ring
    rw [hid]
    have htri := abs_add_le (-(x + Real.log S)) (-(S - (1 + u ^ 2 / 6)))
    rw [abs_neg, abs_neg] at htri
    linarith only [htri, hlog_b, hS_bound, pow_nonneg hu0.le 4]
  have hexp_γ : Real.exp (-br_gamma u) = S := (br_sinh_div_bounds hu0).2.2.1
  set eS := S - (1 + u ^ 2 / 6)
  set eγ := br_gamma u + u ^ 2 / 6
  set eM := Real.exp (-u) - (1 - u + u ^ 2 / 2 - u ^ 3 / 6 + u ^ 4 / 24)
  set eP := Real.exp u - (1 + u + u ^ 2 / 2 + u ^ 3 / 6 + u ^ 4 / 24)
  have heM : |eM| ≤ u ^ 5 / 100 := by
    have : eM = Real.exp (-u) - (1 + -u + (-u) ^ 2 / 2 + (-u) ^ 3 / 6 + (-u) ^ 4 / 24) := by dsimp [eM]; ring
    rw [this]; exact hem
  have heP : |eP| ≤ u ^ 5 / 100 := hep
  have hu2_le : u ^ 2 ≤ 1 / 4 := by nlinarith only [hu0, hu1]
  have hu4_le : u ^ 4 ≤ 1 / 16 := by nlinarith only [hu2_le, sq_nonneg u]
  have hu5 : u ^ 5 ≤ u ^ 4 := by nlinarith only [hu0, hu1, pow_nonneg hu0.le 4]
  have hu4_nn : 0 ≤ u ^ 4 := pow_nonneg hu0.le 4
  have ha2 : |1 + u ^ 2 / 6 + eS| ≤ 2 := by
    have hSb := abs_le.mp hS_bound
    rw [abs_le]; constructor <;> linarith only [hSb.1, hSb.2, hu2_le, hu4_le, sq_nonneg u, hu4_nn]
  have h1 : |br_coeff1 u - (-(u ^ 2 / 6))| ≤ 10 * u ^ 4 := by
    have hid : br_coeff1 u - (-(u ^ 2 / 6)) =
        (1 - u + u ^ 2 / 6) * eS + -(eγ * (1 + u ^ 2 / 6 + eS)) + -eM + -(u ^ 4 / 72) := by
      unfold br_coeff1; rw [hexp_γ]
      have hS_r : S = 1 + u ^ 2 / 6 + eS := by dsimp [eS]; ring
      have hγ_r : br_gamma u = -(u ^ 2 / 6) + eγ := by dsimp [eγ]; ring
      have hM_r : Real.exp (-u) = 1 - u + u ^ 2 / 2 - u ^ 3 / 6 + u ^ 4 / 24 + eM := by dsimp [eM]; ring
      rw [hS_r, hγ_r, hM_r]; ring
    rw [hid]
    have ha1 : |1 - u + u ^ 2 / 6| ≤ 2 := by rw [abs_le]; constructor <;> linarith only [hu0, hu1, hu2_le, sq_nonneg u]
    have hb1 : |(1 - u + u ^ 2 / 6) * eS| ≤ 2 * (u ^ 4 / 100) := by
      rw [abs_mul]; exact mul_le_mul ha1 hS_bound (abs_nonneg _) (by norm_num)
    have hb2 : |eγ * (1 + u ^ 2 / 6 + eS)| ≤ (u ^ 4 / 4) * 2 := by
      rw [abs_mul]; exact mul_le_mul hγ_bound ha2 (abs_nonneg _) (by positivity)
    have ht1 := abs_add_le ((1 - u + u ^ 2 / 6) * eS + -(eγ * (1 + u ^ 2 / 6 + eS)) + -eM) (-(u ^ 4 / 72))
    have ht2 := abs_add_le ((1 - u + u ^ 2 / 6) * eS + -(eγ * (1 + u ^ 2 / 6 + eS))) (-eM)
    have ht3 := abs_add_le ((1 - u + u ^ 2 / 6) * eS) (-(eγ * (1 + u ^ 2 / 6 + eS)))
    simp only [abs_neg] at ht1 ht2 ht3
    have h72 : |u ^ 4 / 72| = u ^ 4 / 72 := abs_of_pos (by positivity)
    linarith only [ht1, ht2, ht3, hb1, hb2, heM, hu5, h72, hu4_nn]
  have h2 : |br_coeff2 u - (u ^ 2 / 3)| ≤ 10 * u ^ 4 := by
    have hid : br_coeff2 u - (u ^ 2 / 3) =
        (-(u ^ 2 / 6) - u) * eS + eγ * (1 + u ^ 2 / 6 + eS) + eP + u ^ 4 / 72 := by
      unfold br_coeff2; rw [hexp_γ]
      have hS_r : S = 1 + u ^ 2 / 6 + eS := by dsimp [eS]; ring
      have hγ_r : br_gamma u = -(u ^ 2 / 6) + eγ := by dsimp [eγ]; ring
      have hP_r : Real.exp u = 1 + u + u ^ 2 / 2 + u ^ 3 / 6 + u ^ 4 / 24 + eP := by dsimp [eP]; ring
      rw [hS_r, hγ_r, hP_r]; ring
    rw [hid]
    have ha1 : |-(u ^ 2 / 6) - u| ≤ 2 := by rw [abs_le]; constructor <;> linarith only [hu0, hu1, hu2_le, sq_nonneg u]
    have hb1 : |(-(u ^ 2 / 6) - u) * eS| ≤ 2 * (u ^ 4 / 100) := by
      rw [abs_mul]; exact mul_le_mul ha1 hS_bound (abs_nonneg _) (by norm_num)
    have hb2 : |eγ * (1 + u ^ 2 / 6 + eS)| ≤ (u ^ 4 / 4) * 2 := by
      rw [abs_mul]; exact mul_le_mul hγ_bound ha2 (abs_nonneg _) (by positivity)
    have ht1 := abs_add_le ((-(u ^ 2 / 6) - u) * eS + eγ * (1 + u ^ 2 / 6 + eS) + eP) (u ^ 4 / 72)
    have ht2 := abs_add_le ((-(u ^ 2 / 6) - u) * eS + eγ * (1 + u ^ 2 / 6 + eS)) eP
    have ht3 := abs_add_le ((-(u ^ 2 / 6) - u) * eS) (eγ * (1 + u ^ 2 / 6 + eS))
    have h72 : |u ^ 4 / 72| = u ^ 4 / 72 := abs_of_pos (by positivity)
    linarith only [ht1, ht2, ht3, hb1, hb2, heP, hu5, h72, hu4_nn]
  refine ⟨h1, h2, ?_⟩
  have hcomb : br_asymLimit M rH u - (-(u ^ 2 / 6) * M.psi1 rH) =
      rH * (br_coeff1 u - (-(u ^ 2 / 6))) +
      ((1 - M.F rH) / (2 * M.f rH)) * (br_coeff2 u - (u ^ 2 / 3)) := by
    unfold br_asymLimit Market.psi1; ring
  rw [hcomb]
  have htri := abs_add_le (rH * (br_coeff1 u - (-(u ^ 2 / 6))))
    (((1 - M.F rH) / (2 * M.f rH)) * (br_coeff2 u - (u ^ 2 / 3)))
  rw [abs_mul, abs_mul] at htri
  have hm1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg rH)
  have hm2 := mul_le_mul_of_nonneg_left h2 (abs_nonneg ((1 - M.F rH) / (2 * M.f rH)))
  linarith only [htri, hm1, hm2]

lemma br_exists_good_u (M : Market) {rH : ℝ} (hpsi1 : M.psi1 rH < 0) :
    ∃ u > 0, u + br_gamma u < 1 ∧
      (1 - u - br_gamma u) * Real.exp (-br_gamma u) < Real.exp (-u) ∧
      0 < br_asymLimit M rH u := by
  obtain ⟨C₁, hC₁, C₂, hC₂, ht⟩ := br_asymLimit_taylor M rH
  let B := |rH| * C₁ + |(1 - M.F rH) / (2 * M.f rH)| * C₂
  have hB : 0 ≤ B := by positivity
  let u := min (1 / 2) (min (1 / (2 * Real.sqrt (6 * C₁ + 1))) (Real.sqrt ((-M.psi1 rH) / (12 * (B + 1)))))
  -- Even simpler: avoid sqrt completely! Pick u ≤ min(1/2, 1/(12*(C1+1)), (-psi1 rH)/(12*(B+1)))
  let u₀ := min (1 / 2) (min (1 / (12 * (C₁ + 1))) ((-M.psi1 rH) / (12 * (B + 1))))
  have hu₀_pos : 0 < u₀ := lt_min (by norm_num) (lt_min (by positivity) (div_pos (by linarith) (by positivity)))
  have hu₀_half : u₀ ≤ 1 / 2 := min_le_left _ _
  have hu₀_1 : u₀ ≤ 1 / (12 * (C₁ + 1)) := le_trans (min_le_right _ _) (min_le_left _ _)
  have hu₀_2 : u₀ ≤ (-M.psi1 rH) / (12 * (B + 1)) := le_trans (min_le_right _ _) (min_le_right _ _)
  have htb := ht u₀ ⟨hu₀_pos, hu₀_half⟩
  have hb := br_sinh_div_bounds hu₀_pos
  have huγ_lt1 : u₀ + br_gamma u₀ < 1 := by linarith [hb.2.2.2.2, hu₀_half]
  have hcoeff1_neg : (1 - u₀ - br_gamma u₀) * Real.exp (-br_gamma u₀) < Real.exp (-u₀) := by
    have hc1 := (abs_le.mp htb.1).2
    have hC1u : C₁ * u₀ ^ 4 < u₀ ^ 2 / 6 := by
      have hmul : u₀ * (12 * (C₁ + 1)) ≤ 1 := (le_div_iff₀ (by positivity)).mp hu₀_1
      have hsq : u₀ ^ 2 ≤ u₀ := by nlinarith [hu₀_pos, hu₀_half]
      have hstep : C₁ * u₀ ^ 2 < 1 / 6 := by nlinarith [hu₀_pos, hC₁, hmul, hsq]
      have : C₁ * u₀ ^ 4 = (C₁ * u₀ ^ 2) * u₀ ^ 2 := by ring
      rw [this]; nlinarith [sq_pos_of_pos hu₀_pos]
    unfold br_coeff1 at hc1; linarith
  have hlim_pos : 0 < br_asymLimit M rH u₀ := by
    have hL := (abs_le.mp htb.2.2).1
    have hBu : B * u₀ ^ 4 < (-(u₀ ^ 2 / 6) * M.psi1 rH) := by
      have hmul : u₀ * (12 * (B + 1)) ≤ -M.psi1 rH := (le_div_iff₀ (by positivity)).mp hu₀_2
      have hsq : u₀ ^ 2 ≤ u₀ := by nlinarith [hu₀_pos, hu₀_half]
      have hstep : B * u₀ ^ 2 < (-M.psi1 rH) / 6 := by nlinarith [hu₀_pos, hB, hmul, hsq]
      have : B * u₀ ^ 4 = (B * u₀ ^ 2) * u₀ ^ 2 := by ring
      rw [this]; nlinarith [sq_pos_of_pos hu₀_pos]
    linarith
  exact ⟨u₀, hu₀_pos, huγ_lt1, hcoeff1_neg, hlim_pos⟩

/-! #### Theorem 4, Part 1: Indifference Cutoff `w_n` and Asymptotics -/

/-- Indifference-cutoff equation for asymmetric duopoly `(SPA(rL), SPA(rH))` with `n` buyers:
`∫_{rL}^w ((1 - F w) / 2 + F v)^(n-1) dv - (w - rH) * ((1 + F w) / 2)^(n-1) = 0`. -/
noncomputable def br_cutoffPhi (M : Market) (rL rH : ℝ) (n : ℕ) (w : ℝ) : ℝ :=
  (∫ v in rL..w, ((1 - M.F w) / 2 + M.F v) ^ (n - 1)) - (w - rH) * (br_Ah M w) ^ (n - 1)

lemma br_cutoffPhi_strictAntiOn (M : Market) (ha : M.a = 0) {rL rH : ℝ} (n : ℕ) (hn : 2 ≤ n)
    (hrL0 : 0 ≤ rL) (hrLH : rL < rH) (hrH1 : rH < 1) :
    StrictAntiOn (br_cutoffPhi M rL rH n) (Icc rH 1) := by
  intro w₁ hw₁ w₂ hw₂ hw12
  have hn1 : 1 ≤ n - 1 := by omega
  have hmem : ∀ w ∈ Icc rH 1, w ∈ Icc M.a 1 := fun w hw => ⟨by rw [ha]; linarith [hrL0, hrLH, hw.1], hw.2⟩
  have hF12 : M.F w₁ < M.F w₂ := M.F_strictMonoOn (hmem w₁ hw₁) (hmem w₂ hw₂) hw12
  have hA12 : br_Ah M w₁ < br_Ah M w₂ := by unfold br_Ah; linarith
  have hA1_pos : 0 < br_Ah M w₁ := by
    unfold br_Ah; have := (M.F_mem_Icc (hmem w₁ hw₁)).1; linarith
  have hA2_pos : 0 < br_Ah M w₂ := lt_trans hA1_pos hA12
  set G₁ : ℝ → ℝ := fun v => (1 - M.F w₁) / 2 + M.F v
  set G₂ : ℝ → ℝ := fun v => (1 - M.F w₂) / 2 + M.F v
  have hG1c : ContinuousOn (fun v => G₁ v ^ (n - 1)) (Icc rL w₁) := by
    have hFc : ContinuousOn M.F (Icc rL w₁) := M.F_continuousOn.mono (Icc_subset_Icc (by rw [ha]; exact hrL0) hw₁.2)
    exact (continuousOn_const.add hFc).pow _
  have hG2c : ContinuousOn (fun v => G₂ v ^ (n - 1)) (Icc rL w₂) := by
    have hFc : ContinuousOn M.F (Icc rL w₂) := M.F_continuousOn.mono (Icc_subset_Icc (by rw [ha]; exact hrL0) hw₂.2)
    exact (continuousOn_const.add hFc).pow _
  have hG2_nn : ∀ v ∈ Icc rL w₂, 0 ≤ G₂ v := fun v hv => by
    have h1 := (M.F_mem_Icc ⟨by rw [ha]; linarith [hrL0, hv.1], le_trans hv.2 hw₂.2⟩).1
    have h2 := (M.F_mem_Icc (hmem w₂ hw₂)).2
    dsimp [G₂]; linarith
  have hrLw1 : rL ≤ w₁ := le_trans hrLH.le hw₁.1
  have hsplit : ∫ v in rL..w₂, G₂ v ^ (n - 1) =
      (∫ v in rL..w₁, G₂ v ^ (n - 1)) + ∫ v in w₁..w₂, G₂ v ^ (n - 1) :=
    (intervalIntegral.integral_add_adjacent_intervals
      ((hG2c.mono (by rw [uIcc_of_le hrLw1]; exact Icc_subset_Icc le_rfl hw12.le)).intervalIntegrable)
      ((hG2c.mono (by rw [uIcc_of_le hw12.le]; exact Icc_subset_Icc hrLw1 le_rfl)).intervalIntegrable)).symm
  have hI_le1 : ∫ v in rL..w₁, G₂ v ^ (n - 1) ≤ ∫ v in rL..w₁, G₁ v ^ (n - 1) := by
    apply intervalIntegral.integral_mono_on hrLw1
      ((hG2c.mono (by rw [uIcc_of_le hrLw1]; exact Icc_subset_Icc le_rfl hw12.le)).intervalIntegrable)
      ((hG1c.mono (by rw [uIcc_of_le hrLw1])).intervalIntegrable)
    intro v hv
    exact pow_le_pow_left₀ (hG2_nn v ⟨hv.1, le_trans hv.2 hw12.le⟩) (by dsimp [G₁, G₂]; linarith) _
  have hI_lt2 : ∫ v in w₁..w₂, G₂ v ^ (n - 1) < (w₂ - w₁) * br_Ah M w₂ ^ (n - 1) := by
    have hsub : 0 < ∫ v in w₁..w₂, (br_Ah M w₂ ^ (n - 1) - G₂ v ^ (n - 1)) := by
      apply intervalIntegral.integral_pos hw12
        (continuousOn_const.sub (hG2c.mono (Icc_subset_Icc hrLw1 le_rfl)))
      · intro v hv
        have hFv : M.F v ≤ M.F w₂ :=
          M.F_strictMonoOn.monotoneOn ⟨by rw [ha]; linarith [hrL0, hrLH, hw₁.1, hv.1.le], le_trans hv.2 hw₂.2⟩ (hmem w₂ hw₂) hv.2
        have hle : G₂ v ≤ br_Ah M w₂ := by unfold br_Ah; dsimp [G₂]; linarith
        simp only [Pi.sub_apply]
        linarith [pow_le_pow_left₀ (hG2_nn v ⟨by linarith [hrLw1, hv.1], hv.2⟩) hle (n - 1)]
      · let vm := (w₁ + w₂) / 2
        refine ⟨vm, ⟨by dsimp [vm]; linarith, by dsimp [vm]; linarith⟩, ?_⟩
        have hFlt : M.F vm < M.F w₂ :=
          M.F_strictMonoOn ⟨by rw [ha]; dsimp [vm]; linarith [hrL0, hrLH, hw₁.1, hw12], by dsimp [vm]; linarith [hw₂.2, hw12]⟩
            (hmem w₂ hw₂) (by dsimp [vm]; linarith)
        have hlt : G₂ vm < br_Ah M w₂ := by unfold br_Ah; dsimp [G₂]; linarith
        have hplt : G₂ vm ^ (n - 1) < br_Ah M w₂ ^ (n - 1) :=
          pow_lt_pow_left₀ hlt (hG2_nn vm ⟨by dsimp [vm]; linarith [hrLw1, hw12], by dsimp [vm]; linarith [hw12]⟩) (by omega)
        simp only [Pi.sub_apply]
        linarith
    rw [intervalIntegral.integral_sub intervalIntegrable_const
      ((hG2c.mono (by rw [uIcc_of_le hw12.le]; exact Icc_subset_Icc hrLw1 le_rfl)).intervalIntegrable),
      intervalIntegral.integral_const, smul_eq_mul] at hsub
    linarith
  have hR_le : (w₁ - rH) * br_Ah M w₁ ^ (n - 1) ≤ (w₁ - rH) * br_Ah M w₂ ^ (n - 1) :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hA1_pos.le hA12.le _) (by linarith [hw₁.1])
  unfold br_cutoffPhi
  change (∫ v in rL..w₂, G₂ v ^ (n - 1)) - (w₂ - rH) * br_Ah M w₂ ^ (n - 1) <
    (∫ v in rL..w₁, G₁ v ^ (n - 1)) - (w₁ - rH) * br_Ah M w₁ ^ (n - 1)
  rw [hsplit]
  linarith

lemma br_cutoffPhi_continuousOn (M : Market) (ha : M.a = 0) {rL rH : ℝ} (n : ℕ) (hn : 2 ≤ n)
    (hrL0 : 0 ≤ rL) (hrLH : rL < rH) (hrH1 : rH < 1) :
    ContinuousOn (br_cutoffPhi M rL rH n) (Icc rH 1) := by
  unfold br_cutoffPhi
  have hF_sub : ContinuousOn M.F (Icc rH 1) :=
    M.F_continuousOn.mono (Icc_subset_Icc (by rw [ha]; linarith) le_rfl)
  have hR : ContinuousOn (fun w => (w - rH) * br_Ah M w ^ (n - 1)) (Icc rH 1) :=
    (continuousOn_id.sub continuousOn_const).mul (((continuousOn_const.add hF_sub).div_const 2).pow _)
  refine ContinuousOn.sub ?_ hR
  have hcongr : EqOn (fun w => ∫ v in rL..w, ((1 - M.F w) / 2 + M.F v) ^ (n - 1))
      (fun w => ∑ k ∈ Finset.range n, ((n - 1).choose k : ℝ) * ((1 - M.F w) / 2) ^ (n - 1 - k) *
        (∫ v in rL..w, M.F v ^ k)) (Icc rH 1) := by
    intro w hw
    have hpow : ∀ v, ((1 - M.F w) / 2 + M.F v) ^ (n - 1) =
        ∑ k ∈ Finset.range n, ((n - 1).choose k : ℝ) * ((1 - M.F w) / 2) ^ (n - 1 - k) * M.F v ^ k := by
      intro v
      rw [add_comm, add_pow, show n - 1 + 1 = n by omega]
      refine Finset.sum_congr rfl fun k _ => by ring
    simp_rw [hpow]
    have hFc : ContinuousOn M.F (Icc rL w) :=
      M.F_continuousOn.mono (Icc_subset_Icc (by rw [ha]; exact hrL0) hw.2)
    have hsum_int := intervalIntegral_finset_sum_local (Finset.range n)
      (f := fun k v => ((n - 1).choose k : ℝ) * ((1 - M.F w) / 2) ^ (n - 1 - k) * M.F v ^ k)
      (a := rL) (b := w) (fun k _ => by
        have hFk : ContinuousOn (fun v => M.F v ^ k) (Icc rL w) := hFc.pow k
        exact ((continuousOn_const.mul hFk).mono (by rw [uIcc_of_le (by linarith [hrLH, hw.1])])).intervalIntegrable)
    rw [hsum_int]
    refine Finset.sum_congr rfl fun k _ => intervalIntegral.integral_const_mul _ _
  refine (continuousOn_finset_sum_local (Finset.range n)
    (f := fun k w => ((n - 1).choose k : ℝ) * ((1 - M.F w) / 2) ^ (n - 1 - k) * (∫ v in rL..w, M.F v ^ k))
    (fun k _ => ?_)).congr hcongr
  have hFc : ContinuousOn M.F (Icc rL 1) := M.F_continuousOn.mono (Icc_subset_Icc (by rw [ha]; exact hrL0) le_rfl)
  have hFk : ContinuousOn (fun v => M.F v ^ k) (Icc rL 1) := hFc.pow k
  have hprim : ContinuousOn (fun w => ∫ v in rL..w, M.F v ^ k) (Icc rH 1) :=
    (continuousOn_primitive_Icc (by linarith : rL ≤ 1) hFk).mono (Icc_subset_Icc hrLH.le le_rfl)
  have hpowF : ContinuousOn (fun w => ((1 - M.F w) / 2) ^ (n - 1 - k)) (Icc rH 1) :=
    ((continuousOn_const.sub hF_sub).div_const 2).pow _
  exact (continuousOn_const.mul hpowF).mul hprim

open scoped Classical in
/-- Indifference cutoff `w_n` for asymmetric duopoly `(SPA(r_L n), SPA(r_H n))`. -/
noncomputable def asymW (M : Market) (r_L r_H : ℕ → ℝ) (n : ℕ) : ℝ :=
  if h : ∃ w ∈ Ioo (r_H n) 1, br_cutoffPhi M (r_L n) (r_H n) n w = 0 then h.choose else r_H n

/-- **Theorem 4 (Part 1 — Indifference Cutoff Existence and Asymptotics)**:
For `m = 2`, `a = 0`, and sequences `r_L n → rL`, `r_H n → rH` with `0 ≤ rL < rH < 1`,
for all sufficiently large `n`, there exists a unique interior cutoff `w_n ∈ (r_H n, 1)` solving
`∫_{r_L n}^{w_n} ((1 - F w_n)/2 + F v)^(n-1) dv = (w_n - r_H n) * A(w_n)^(n-1)`,
with `w_n → rH` and `w_n - r_H n = (1 - q_{w_n}) / (n * f(rH)) + o(1/n)`. -/
theorem theorem4_cutoff_asymptotics (M : Market) (hm : M.m = 2) (ha : M.a = 0)
    {r_L r_H : ℕ → ℝ} {rL rH : ℝ} (hrL0 : 0 ≤ rL) (hrLH : rL < rH) (hrH1 : rH < 1)
    (hL_lim : Tendsto r_L atTop (nhds rL)) (hH_lim : Tendsto r_H atTop (nhds rH))
    (hL_nn : ∀ᶠ n in atTop, 0 ≤ r_L n) :
    (∀ᶠ n : ℕ in atTop,
      asymW M r_L r_H n ∈ Ioo (r_H n) 1 ∧
      (∀ w ∈ Ioo (r_H n) 1, br_cutoffPhi M (r_L n) (r_H n) n w = 0 → w = asymW M r_L r_H n) ∧
      ∫ v in r_L n..asymW M r_L r_H n, ((1 - M.F (asymW M r_L r_H n)) / 2 + M.F v) ^ (n - 1) =
        (asymW M r_L r_H n - r_H n) * M.A (asymW M r_L r_H n) ^ (n - 1)) ∧
    Tendsto (asymW M r_L r_H) atTop (nhds rH) ∧
    Tendsto (fun n : ℕ =>
      (n : ℝ) * ((asymW M r_L r_H n - r_H n) - (1 - (1 - M.F (asymW M r_L r_H n)) / 2) / ((n : ℝ) * M.f rH)))
      atTop (nhds 0) := by
  obtain ⟨fmin, hfmin, hf_lo⟩ := M.exists_f_min
  have hfH : 0 < M.f rH := M.hf_pos rH ⟨by rw [ha]; linarith, hrH1.le⟩
  have hord : ∀ᶠ n : ℕ in atTop, r_L n < r_H n ∧ r_H n < (rH + 1) / 2 ∧ r_L n ≤ (rL + rH) / 2 := by
    have d1 := Metric.tendsto_nhds.mp hL_lim ((rH - rL) / 4) (by linarith)
    have d2 := Metric.tendsto_nhds.mp hH_lim (min ((rH - rL) / 4) ((1 - rH) / 2)) (lt_min (by linarith) (by linarith))
    filter_upwards [d1, d2] with n h1 h2
    rw [Real.dist_eq, abs_lt] at h1 h2
    have h2a : |r_H n - rH| < (rH - rL) / 4 := by rw [abs_lt]; exact ⟨lt_of_le_of_lt (neg_le_neg (min_le_left _ _)) h2.1, lt_of_lt_of_le h2.2 (min_le_left _ _)⟩
    have h2b : |r_H n - rH| < (1 - rH) / 2 := by rw [abs_lt]; exact ⟨lt_of_le_of_lt (neg_le_neg (min_le_right _ _)) h2.1, lt_of_lt_of_le h2.2 (min_le_right _ _)⟩
    rw [abs_lt] at h2a h2b
    exact ⟨by linarith, by linarith, by linarith⟩
  have hlarge : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) * fmin) < (1 - rH) / 2 := by
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) * fmin)) atTop (nhds 0) := by
      have := tendsto_const_nhds (x := (1 : ℝ)).div_atTop
        (tendsto_natCast_atTop_atTop.atTop_mul_const hfmin)
      simpa using this
    exact h0.eventually (Iio_mem_nhds (by linarith))
  have hex_ev : ∀ᶠ n : ℕ in atTop,
      asymW M r_L r_H n ∈ Ioo (r_H n) 1 ∧
      (∀ w ∈ Ioo (r_H n) 1, br_cutoffPhi M (r_L n) (r_H n) n w = 0 → w = asymW M r_L r_H n) ∧
      br_cutoffPhi M (r_L n) (r_H n) n (asymW M r_L r_H n) = 0 ∧
      asymW M r_L r_H n - r_H n ≤ 1 / ((n : ℝ) * fmin) := by
    filter_upwards [eventually_ge_atTop 2, hL_nn, hord, hlarge] with n hn hLn ho hl
    have hrH1' : r_H n < 1 := by linarith [ho.2.1]
    have hPhi_pos : 0 < br_cutoffPhi M (r_L n) (r_H n) n (r_H n) := by
      unfold br_cutoffPhi; rw [sub_self, zero_mul, sub_zero]
      have hFc : ContinuousOn M.F (Icc (r_L n) (r_H n)) :=
        M.F_continuousOn.mono (Icc_subset_Icc (by rw [ha]; exact hLn) hrH1'.le)
      have hGcont : ContinuousOn (fun v => ((1 - M.F (r_H n)) / 2 + M.F v) ^ (n - 1)) (Icc (r_L n) (r_H n)) :=
        (continuousOn_const.add hFc).pow _
      apply intervalIntegral.integral_pos ho.1 hGcont
      · intro v hv
        have hF1 := (M.F_mem_Icc ⟨by rw [ha]; linarith [hLn, hv.1], le_trans hv.2 hrH1'.le⟩).1
        have hF2 := (M.F_mem_Icc ⟨by rw [ha]; linarith [hLn, ho.1], hrH1'.le⟩).2
        exact pow_nonneg (by linarith) _
      · let vm := (r_L n + r_H n) / 2
        refine ⟨vm, ⟨by dsimp [vm]; linarith [ho.1], by dsimp [vm]; linarith [ho.1]⟩, ?_⟩
        have hvm_mem : vm ∈ Icc M.a 1 := ⟨by rw [ha]; dsimp [vm]; linarith [hLn, ho.1], by dsimp [vm]; linarith [ho.1, hrH1']⟩
        have hF1 := (M.F_mem_Icc hvm_mem).1
        have hF2 : M.F (r_H n) < 1 := by
          rw [← M.hF_1]; exact M.F_strictMonoOn ⟨by rw [ha]; linarith [hLn, ho.1], hrH1'.le⟩ (right_mem_Icc.mpr M.ha1.le) hrH1'
        exact pow_pos (by linarith) _
    have hInt_bound : ∀ w ∈ Icc (r_H n) 1,
        ∫ v in r_L n..w, ((1 - M.F w) / 2 + M.F v) ^ (n - 1) ≤ br_Ah M w ^ n / ((n : ℝ) * fmin) := by
      intro w hw
      set G : ℝ → ℝ := fun v => (1 - M.F w) / 2 + M.F v
      have hFc : ContinuousOn M.F (Icc (r_L n) w) :=
        M.F_continuousOn.mono (Icc_subset_Icc (by rw [ha]; exact hLn) hw.2)
      have hfc : ContinuousOn M.f (Icc (r_L n) w) :=
        M.hf_cont.mono (Icc_subset_Icc (by rw [ha]; exact hLn) hw.2)
      have hGc : ContinuousOn G (Icc (r_L n) w) := continuousOn_const.add hFc
      have hGnn : ∀ v ∈ Icc (r_L n) w, 0 ≤ G v := fun v hv => by
        have h1 := (M.F_mem_Icc ⟨by rw [ha]; linarith [hLn, hv.1], le_trans hv.2 hw.2⟩).1
        have h2 := (M.F_mem_Icc ⟨by rw [ha]; linarith [hLn, ho.1, hw.1], hw.2⟩).2
        dsimp [G]; linarith
      have hnR : (0 : ℝ) < (n : ℝ) := by positivity
      have hFTC : ∫ v in r_L n..w, G v ^ (n - 1) * M.f v = (G w ^ n - G (r_L n) ^ n) / (n : ℝ) := by
        have hd : ∀ v ∈ Ioo (r_L n) w, HasDerivAt (fun v => G v ^ n / (n : ℝ)) (G v ^ (n - 1) * M.f v) v := by
          intro v hv
          have hv' : v ∈ Ioo M.a 1 := ⟨by rw [ha]; linarith [hLn, hv.1], lt_of_lt_of_le hv.2 hw.2⟩
          have hGd : HasDerivAt G (M.f v) v := (M.hF_deriv_open v hv').const_add _
          have h := (hGd.pow n).div_const (n : ℝ)
          convert h using 1; field_simp [hnR.ne']
        have hGn : ContinuousOn (fun v => G v ^ n / (n : ℝ)) (Icc (r_L n) w) := (hGc.pow n).div_const _
        have hGk : ContinuousOn (fun v => G v ^ (n - 1) * M.f v) (Icc (r_L n) w) := (hGc.pow (n - 1)).mul hfc
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by linarith [ho.1, hw.1]) hGn hd
          (hGk.mono (by rw [uIcc_of_le (by linarith [ho.1, hw.1])])).intervalIntegrable]
        ring
      have hGk : ContinuousOn (fun v => G v ^ (n - 1)) (Icc (r_L n) w) := hGc.pow (n - 1)
      have hle : ∫ v in r_L n..w, G v ^ (n - 1) ≤ ∫ v in r_L n..w, G v ^ (n - 1) * M.f v / fmin := by
        apply intervalIntegral.integral_mono_on (by linarith [ho.1, hw.1])
          ((hGk.mono (by rw [uIcc_of_le (by linarith [ho.1, hw.1])])).intervalIntegrable)
          (((hGk.mul hfc).div_const _).mono (by rw [uIcc_of_le (by linarith [ho.1, hw.1])])).intervalIntegrable
        intro v hv
        have h0 : 0 ≤ G v ^ (n - 1) := pow_nonneg (hGnn v hv) _
        have hfv : fmin ≤ M.f v := hf_lo v ⟨by rw [ha]; linarith [hLn, hv.1], le_trans hv.2 hw.2⟩
        have h1 : 1 ≤ M.f v / fmin := (one_le_div hfmin).mpr hfv
        calc G v ^ (n - 1) = G v ^ (n - 1) * 1 := (mul_one _).symm
          _ ≤ G v ^ (n - 1) * (M.f v / fmin) := mul_le_mul_of_nonneg_left h1 h0
          _ = G v ^ (n - 1) * M.f v / fmin := by ring
      rw [intervalIntegral.integral_div, hFTC] at hle
      have hGw : G w = br_Ah M w := by dsimp [G]; unfold br_Ah; ring
      have hGrL_nn : 0 ≤ G (r_L n) ^ n := pow_nonneg (hGnn (r_L n) ⟨le_rfl, by linarith [ho.1, hw.1]⟩) _
      rw [hGw] at hle
      calc _ ≤ (br_Ah M w ^ n - G (r_L n) ^ n) / (n : ℝ) / fmin := hle
        _ ≤ br_Ah M w ^ n / (n : ℝ) / fmin := by
            apply div_le_div_of_nonneg_right _ hfmin.le
            apply div_le_div_of_nonneg_right (by linarith) hnR.le
        _ = br_Ah M w ^ n / ((n : ℝ) * fmin) := by rw [div_div]
    have hPhi_neg : br_cutoffPhi M (r_L n) (r_H n) n 1 < 0 := by
      unfold br_cutoffPhi
      have h1 := hInt_bound 1 (right_mem_Icc.mpr hrH1'.le)
      have hA1 : br_Ah M 1 = 1 := by unfold br_Ah; rw [M.hF_1]; ring
      rw [hA1, one_pow] at h1
      rw [hA1, one_pow, mul_one]
      linarith [ho.2.1, hl]
    have hcont := br_cutoffPhi_continuousOn M ha n hn hLn ho.1 hrH1'
    obtain ⟨w, hw_cc, hw_zero⟩ := intermediate_value_Icc' hrH1'.le hcont ⟨hPhi_neg.le, hPhi_pos.le⟩
    have hw_oo : w ∈ Ioo (r_H n) 1 := by
      refine ⟨lt_of_le_of_ne hw_cc.1 ?_, lt_of_le_of_ne hw_cc.2 ?_⟩
      · intro h; rw [← h] at hw_zero; linarith
      · intro h; rw [h] at hw_zero; linarith
    have hex : ∃ w ∈ Ioo (r_H n) 1, br_cutoffPhi M (r_L n) (r_H n) n w = 0 := ⟨w, hw_oo, hw_zero⟩
    have hasym_mem : asymW M r_L r_H n ∈ Ioo (r_H n) 1 := by
      unfold asymW; simp only [hex, ↓reduceDIte]; exact hex.choose_spec.1
    have hasym_zero : br_cutoffPhi M (r_L n) (r_H n) n (asymW M r_L r_H n) = 0 := by
      unfold asymW; simp only [hex, ↓reduceDIte]; exact hex.choose_spec.2
    have hanti := br_cutoffPhi_strictAntiOn M ha n hn hLn ho.1 hrH1'
    have huniq : ∀ w' ∈ Ioo (r_H n) 1, br_cutoffPhi M (r_L n) (r_H n) n w' = 0 → w' = asymW M r_L r_H n :=
      fun w' hw' h0 => hanti.injOn (Ioo_subset_Icc_self hw') (Ioo_subset_Icc_self hasym_mem) (h0.trans hasym_zero.symm)
    have hgap : asymW M r_L r_H n - r_H n ≤ 1 / ((n : ℝ) * fmin) := by
      have hb := hInt_bound (asymW M r_L r_H n) (Ioo_subset_Icc_self hasym_mem)
      unfold br_cutoffPhi at hasym_zero
      have hAw_pos : 0 < br_Ah M (asymW M r_L r_H n) := by
        unfold br_Ah; have := (M.F_mem_Icc ⟨by rw [ha]; linarith [hLn, ho.1, hasym_mem.1], hasym_mem.2.le⟩).1; linarith
      have hAw_le1 : br_Ah M (asymW M r_L r_H n) ≤ 1 := by
        unfold br_Ah; have := (M.F_mem_Icc ⟨by rw [ha]; linarith [hLn, ho.1, hasym_mem.1], hasym_mem.2.le⟩).2; linarith
      have hpow : br_Ah M (asymW M r_L r_H n) ^ n =
          br_Ah M (asymW M r_L r_H n) ^ (n - 1) * br_Ah M (asymW M r_L r_H n) := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega)]
      have hle2 : (asymW M r_L r_H n - r_H n) * br_Ah M (asymW M r_L r_H n) ^ (n - 1) ≤
          br_Ah M (asymW M r_L r_H n) ^ (n - 1) * (1 / ((n : ℝ) * fmin)) := by
        calc _ = ∫ v in r_L n..asymW M r_L r_H n, ((1 - M.F (asymW M r_L r_H n)) / 2 + M.F v) ^ (n - 1) := by linarith
          _ ≤ br_Ah M (asymW M r_L r_H n) ^ n / ((n : ℝ) * fmin) := hb
          _ = br_Ah M (asymW M r_L r_H n) ^ (n - 1) * (br_Ah M (asymW M r_L r_H n) / ((n : ℝ) * fmin)) := by
              rw [hpow]; ring
          _ ≤ br_Ah M (asymW M r_L r_H n) ^ (n - 1) * (1 / ((n : ℝ) * fmin)) := by
              apply mul_le_mul_of_nonneg_left _ (pow_pos hAw_pos _).le
              exact div_le_div_of_nonneg_right hAw_le1 (by positivity)
      exact le_of_mul_le_mul_right (by linarith) (pow_pos hAw_pos (n - 1))
    exact ⟨hasym_mem, huniq, hasym_zero, hgap⟩
  have hw_lim : Tendsto (asymW M r_L r_H) atTop (nhds rH) := by
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) * fmin)) atTop (nhds 0) := by
      have := tendsto_const_nhds (x := (1 : ℝ)).div_atTop (tendsto_natCast_atTop_atTop.atTop_mul_const hfmin)
      simpa using this
    have hhi : Tendsto (fun n : ℕ => r_H n + 1 / ((n : ℝ) * fmin)) atTop (nhds rH) := by
      simpa using hH_lim.add h0
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hH_lim hhi ?_ ?_
    · filter_upwards [hex_ev] with n hn using hn.1.1.le
    · filter_upwards [hex_ev] with n hn using by linarith [hn.2.2.2]
  have hP2 : Tendsto (fun n : ℕ =>
      ((n : ℝ) * ∫ v in r_L n..asymW M r_L r_H n, ((1 - M.F (asymW M r_L r_H n)) / 2 + 1 * M.F v) ^ (n - 1)) /
        ((1 - M.F (asymW M r_L r_H n)) / 2 + 1 * M.F (asymW M r_L r_H n)) ^ n)
      atTop (nhds (1 / (1 * M.f rH))) := by
    have hAh_lim : Tendsto (fun n => (1 - M.F (asymW M r_L r_H n)) / 2 + 1 * M.F (asymW M r_L r_H n))
        atTop (nhds (br_Ah M rH)) := by
      have hFlim : Tendsto (fun n => M.F (asymW M r_L r_H n)) atTop (nhds (M.F rH)) := by
        have hFc : ContinuousAt M.F rH :=
          M.F_continuousOn.continuousAt (Icc_mem_nhds (by rw [ha]; linarith) hrH1)
        exact hFc.tendsto.comp hw_lim
      have h := ((tendsto_const_nhds (x := (1 : ℝ)).sub hFlim).div_const 2).add (hFlim.const_mul 1)
      convert h using 1; unfold br_Ah; ring
    have hAh_pos : 0 < br_Ah M rH := by
      unfold br_Ah; have := (M.F_mem_Icc ⟨by rw [ha]; linarith, hrH1.le⟩).1; linarith
    refine br_P2_limit M ha one_pos (by linarith) hrH1 hAh_pos (show 0 < (rH - rL) / 2 by linarith)
      hw_lim hAh_lim ?_ ?_
    · filter_upwards [hL_nn, hord, hex_ev] with n hLn ho he
      have h1 := (M.F_mem_Icc ⟨by rw [ha]; exact hLn, le_trans (le_trans ho.1.le he.1.1.le) he.1.2.le⟩).1
      have h2 := (M.F_mem_Icc ⟨by rw [ha]; linarith [hLn, ho.1, he.1.1], he.1.2.le⟩).2
      exact ⟨hLn, le_trans ho.1.le he.1.1.le, he.1.2.le, by linarith⟩
    · filter_upwards [hord] with n ho using by linarith [ho.2.2]
  have hAh_lim' : Tendsto (fun n => br_Ah M (asymW M r_L r_H n)) atTop (nhds (br_Ah M rH)) := by
    have hFc : ContinuousAt M.F rH :=
      M.F_continuousOn.continuousAt (Icc_mem_nhds (by rw [ha]; linarith) hrH1)
    have hFlim := hFc.tendsto.comp hw_lim
    exact (tendsto_const_nhds.add hFlim).div_const 2
  have ho_lim : Tendsto (fun n : ℕ =>
      (n : ℝ) * ((asymW M r_L r_H n - r_H n) - (1 - (1 - M.F (asymW M r_L r_H n)) / 2) / ((n : ℝ) * M.f rH)))
      atTop (nhds 0) := by
    have hsub := hP2.sub (tendsto_const_nhds (x := 1 / M.f rH))
    rw [one_mul, sub_self] at hsub
    have hmul := hAh_lim'.mul hsub
    rw [mul_zero] at hmul
    refine hmul.congr' ?_
    filter_upwards [eventually_ge_atTop 2, hL_nn, hord, hex_ev] with n hn hLn ho he
    have hnR : (n : ℝ) ≠ 0 := by positivity
    have hAw_pos : 0 < br_Ah M (asymW M r_L r_H n) := by
      unfold br_Ah; have := (M.F_mem_Icc ⟨by rw [ha]; linarith [hLn, ho.1, he.1.1], he.1.2.le⟩).1; linarith
    have heq_A : (1 - M.F (asymW M r_L r_H n)) / 2 + 1 * M.F (asymW M r_L r_H n) = br_Ah M (asymW M r_L r_H n) := by
      unfold br_Ah; ring
    have heq_1q : 1 - (1 - M.F (asymW M r_L r_H n)) / 2 = br_Ah M (asymW M r_L r_H n) := by
      unfold br_Ah; ring
    have hphi := he.2.2.1; unfold br_cutoffPhi at hphi
    have hint_eq : ∫ v in r_L n..asymW M r_L r_H n, ((1 - M.F (asymW M r_L r_H n)) / 2 + 1 * M.F v) ^ (n - 1) =
        (asymW M r_L r_H n - r_H n) * br_Ah M (asymW M r_L r_H n) ^ (n - 1) := by
      simp only [one_mul]; linarith
    rw [heq_A, heq_1q, hint_eq]
    have hpow : br_Ah M (asymW M r_L r_H n) ^ n =
        br_Ah M (asymW M r_L r_H n) ^ (n - 1) * br_Ah M (asymW M r_L r_H n) := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    rw [hpow]
    field_simp [hnR, hAw_pos.ne', hfH.ne']
  refine ⟨?_, hw_lim, ho_lim⟩
  filter_upwards [hex_ev] with n hn
  refine ⟨hn.1, hn.2.1, ?_⟩
  have hphi := hn.2.2.1; unfold br_cutoffPhi at hphi
  rw [br_A_eq M hm]; linarith

/-! #### Theorem 4, Part 2: Construction of Deviation and Sequential Rationality -/

/-- Baseline duopoly visit strategy for `(SPA(rL), SPA(rH))` with cutoff `w`:
`θ_L = 1` on `(-∞, w]` and `1/2` on `(w, ∞)`. -/
noncomputable def asymBaseVisit (M : Market) (w : ℝ) : VisitStrategy M :=
  br_visit M (fun v => if v ≤ w then 1 else 1 / 2)
    (Measurable.ite measurableSet_Iic measurable_const measurable_const)
    (fun v => by split_ifs <;> norm_num)
    (fun v => by split_ifs <;> norm_num)

/-- Deviation coordinates for Theorem 4 (parametrized by `u > 0` and buyer count `n`). -/
noncomputable def asymQw (M : Market) (r_L r_H : ℕ → ℝ) (n : ℕ) : ℝ :=
  (1 - M.F (asymW M r_L r_H n)) / 2

noncomputable def asymAn (M : Market) (r_L r_H : ℕ → ℝ) (n : ℕ) : ℝ :=
  1 - asymQw M r_L r_H n

noncomputable def asymDelta (M : Market) (r_L r_H : ℕ → ℝ) (n : ℕ) : ℝ :=
  asymAn M r_L r_H n / (n : ℝ)

noncomputable def asymQa (M : Market) (r_L r_H : ℕ → ℝ) (u : ℝ) (n : ℕ) : ℝ :=
  asymQw M r_L r_H n - u * asymDelta M r_L r_H n

noncomputable def asymThat (M : Market) (r_L r_H : ℕ → ℝ) (u : ℝ) (n : ℕ) : ℝ :=
  asymQw M r_L r_H n + u * asymDelta M r_L r_H n

noncomputable def asymBarX (M : Market) (r_L r_H : ℕ → ℝ) (u : ℝ) (n : ℕ) : ℝ :=
  poolAvg n (1 - asymThat M r_L r_H u n) (1 - asymQa M r_L r_H u n)

noncomputable def asymQ0 (M : Market) (r_L r_H : ℕ → ℝ) (u : ℝ) (n : ℕ) : ℝ :=
  1 - (asymBarX M r_L r_H u n) ^ (1 / ((n : ℝ) - 1))

noncomputable def asymGammaN (M : Market) (r_L r_H : ℕ → ℝ) (u : ℝ) (n : ℕ) : ℝ :=
  (asymQ0 M r_L r_H u n - asymQw M r_L r_H n) / asymDelta M r_L r_H n

noncomputable def asymVa (M : Market) (r_L r_H : ℕ → ℝ) (u : ℝ) (n : ℕ) : ℝ :=
  M.invF (1 - 2 * asymQa M r_L r_H u n)

noncomputable def asymV2 (M : Market) (r_L r_H : ℕ → ℝ) (u : ℝ) (n : ℕ) : ℝ :=
  M.invF (1 - (asymQa M r_L r_H u n + asymQ0 M r_L r_H u n))

noncomputable def asymVhat (M : Market) (r_L r_H : ℕ → ℝ) (u : ℝ) (n : ℕ) : ℝ :=
  M.invF (1 - (asymThat M r_L r_H u n + asymQ0 M r_L r_H u n))

open scoped Classical in
/-- Lower reserve `v_{0,n}` solving eq. (20):
`∫_{v_0}^{\hat v_n} (q_{0,n} + F v)^(n-1) dv = (\hat v_n - r_{H,n}) * (1 - q_{0,n})^(n-1)`. -/
noncomputable def asymV0 (M : Market) (r_L r_H : ℕ → ℝ) (u : ℝ) (n : ℕ) : ℝ :=
  if h : ∃ v0 ∈ Ioo (0 : ℝ) (asymVhat M r_L r_H u n),
      ∫ v in v0..asymVhat M r_L r_H u n, (asymQ0 M r_L r_H u n + M.F v) ^ (n - 1) =
        (asymVhat M r_L r_H u n - r_H n) * (1 - asymQ0 M r_L r_H u n) ^ (n - 1)
  then h.choose else 0

/-- Upper pool endpoint `β_n ∈ (v_{2,n}, v_{a,n})`. -/
noncomputable def asymBeta (M : Market) (r_L r_H : ℕ → ℝ) (u : ℝ) (n : ℕ) : ℝ :=
  asymVa M r_L r_H u n -
    (∫ v in asymV2 M r_L r_H u n..asymVa M r_L r_H u n,
        ((asymQa M r_L r_H u n + M.F v) ^ (n - 1) - asymBarX M r_L r_H u n)) /
      ((1 - asymQa M r_L r_H u n) ^ (n - 1) - asymBarX M r_L r_H u n)

/-- Deviation mechanism `(v_{0,n}, {(\hat v_n, β_n)})`. -/
noncomputable def asymDevMech (M : Market) (r_L r_H : ℕ → ℝ) (u : ℝ) (n : ℕ) : HierarchicalMech :=
  br_onePool (asymV0 M r_L r_H u n) (asymVhat M r_L r_H u n) (asymBeta M r_L r_H u n)

/-- Deviation visit strategy: `θ_L = 1` on `[0, v_{2,n}]`, `0` on `(v_{2,n}, v_{a,n})`, `1/2` above `v_{a,n}`. -/
noncomputable def asymDevVisit (M : Market) (r_L r_H : ℕ → ℝ) (u : ℝ) (n : ℕ) : VisitStrategy M :=
  br_visit M
    (fun v => if v ≤ asymV2 M r_L r_H u n then 1
              else if v < asymVa M r_L r_H u n then 0 else 1 / 2)
    (Measurable.ite measurableSet_Iic measurable_const
      (Measurable.ite measurableSet_Iio measurable_const measurable_const))
    (fun v => by split_ifs <;> norm_num)
    (fun v => by split_ifs <;> norm_num)

/-- Convergence `γ_n → γ = -log(sinh u / u)` and `q_{a,n} < q_{0,n} < \hat T_n`. -/
lemma br_gammaN_tendsto (M : Market) (hm : M.m = 2) (ha : M.a = 0)
    {r_L r_H : ℕ → ℝ} {rL rH u : ℝ} (hrL0 : 0 ≤ rL) (hrLH : rL < rH) (hrH1 : rH < 1)
    (hL_lim : Tendsto r_L atTop (nhds rL)) (hH_lim : Tendsto r_H atTop (nhds rH))
    (hL_nn : ∀ᶠ n in atTop, 0 ≤ r_L n) (hu : 0 < u) :
    (∀ᶠ n : ℕ in atTop,
      0 < asymQa M r_L r_H u n ∧ asymQa M r_L r_H u n < asymQ0 M r_L r_H u n ∧
      asymQ0 M r_L r_H u n < asymThat M r_L r_H u n ∧ asymThat M r_L r_H u n < 1 / 2 ∧
      (1 - asymQ0 M r_L r_H u n) ^ (n - 1) = asymBarX M r_L r_H u n ∧
      |asymGammaN M r_L r_H u n| < u) ∧
    Tendsto (asymGammaN M r_L r_H u) atTop (nhds (br_gamma u)) := by
  have hcut := theorem4_cutoff_asymptotics M hm ha hrL0 hrLH hrH1 hL_lim hH_lim hL_nn
  have hw_lim := hcut.2.1
  have hF_lim : Tendsto (fun n => M.F (asymW M r_L r_H n)) atTop (nhds (M.F rH)) :=
    (M.F_continuousOn.continuousAt (Icc_mem_nhds (by rw [ha]; linarith) hrH1)).tendsto.comp hw_lim
  have hFH_pos : 0 < M.F rH := by
    rw [← M.hF_a]; exact M.F_strictMonoOn (left_mem_Icc.mpr M.ha1.le) ⟨by rw [ha]; linarith, hrH1.le⟩ (by rw [ha]; linarith)
  have hFH_lt1 : M.F rH < 1 := by
    rw [← M.hF_1]; exact M.F_strictMonoOn ⟨by rw [ha]; linarith, hrH1.le⟩ (right_mem_Icc.mpr M.ha1.le) hrH1
  have hqw_lim : Tendsto (asymQw M r_L r_H) atTop (nhds ((1 - M.F rH) / 2)) :=
    (tendsto_const_nhds.sub hF_lim).div_const 2
  have hAn_lim : Tendsto (asymAn M r_L r_H) atTop (nhds (1 - (1 - M.F rH) / 2)) :=
    tendsto_const_nhds.sub hqw_lim
  have hδ_lim : Tendsto (asymDelta M r_L r_H) atTop (nhds 0) :=
    hAn_lim.div_atTop tendsto_natCast_atTop_atTop
  have hqw_pos : 0 < (1 - M.F rH) / 2 := by linarith
  have hqw_half : (1 - M.F rH) / 2 < 1 / 2 := by linarith
  have hqa_lim : Tendsto (asymQa M r_L r_H u) atTop (nhds ((1 - M.F rH) / 2)) := by
    unfold asymQa; have h := hqw_lim.sub (hδ_lim.const_mul u); simpa using h
  have hThat_lim : Tendsto (asymThat M r_L r_H u) atTop (nhds ((1 - M.F rH) / 2)) := by
    unfold asymThat; have h := hqw_lim.add (hδ_lim.const_mul u); simpa using h
  have hord : ∀ᶠ n : ℕ in atTop,
      0 < asymQa M r_L r_H u n ∧ asymQa M r_L r_H u n < asymQ0 M r_L r_H u n ∧
      asymQ0 M r_L r_H u n < asymThat M r_L r_H u n ∧ asymThat M r_L r_H u n < 1 / 2 ∧
      (1 - asymQ0 M r_L r_H u n) ^ (n - 1) = asymBarX M r_L r_H u n ∧
      |asymGammaN M r_L r_H u n| < u := by
    filter_upwards [eventually_ge_atTop 2, hqa_lim.eventually (Ioi_mem_nhds hqw_pos),
      hThat_lim.eventually (Iio_mem_nhds hqw_half),
      hAn_lim.eventually (Ioi_mem_nhds (show (1 / 2 : ℝ) < 1 - (1 - M.F rH) / 2 by linarith))] with n hn hqa0 hThat5 hAn5
    have hnR : (0 : ℝ) < (n : ℝ) := by positivity
    have hn1R : (0 : ℝ) < (n : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hδpos : 0 < asymDelta M r_L r_H n := div_pos (by linarith) hnR
    have hqa_lt_That : asymQa M r_L r_H u n < asymThat M r_L r_H u n := by
      unfold asymQa asymThat; linarith [mul_pos hu hδpos]
    have h1T_pos : 0 < 1 - asymThat M r_L r_H u n := by linarith
    have hpb := poolAvg_strict_bounds hn h1T_pos.le (show 1 - asymThat M r_L r_H u n < 1 - asymQa M r_L r_H u n by linarith)
    have hbarx_pos : 0 < asymBarX M r_L r_H u n := lt_trans (pow_pos h1T_pos _) hpb.1
    have hpow_eq : (1 - asymQ0 M r_L r_H u n) ^ (n - 1) = asymBarX M r_L r_H u n := by
      unfold asymQ0
      rw [sub_sub_cancel, ← Real.rpow_natCast, ← Real.rpow_mul hbarx_pos.le]
      have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
      rw [hcast, one_div_mul_cancel hn1R.ne', Real.rpow_one]
    have h1q0_pos : 0 < 1 - asymQ0 M r_L r_H u n := by
      unfold asymQ0; rw [sub_sub_cancel]; exact Real.rpow_pos_of_pos hbarx_pos _
    have hlt1 : 1 - asymThat M r_L r_H u n < 1 - asymQ0 M r_L r_H u n := by
      by_contra hle; push Not at hle
      have := pow_le_pow_left₀ h1q0_pos.le hle (n - 1)
      rw [hpow_eq] at this; unfold asymBarX at this; linarith [hpb.1]
    have hlt2 : 1 - asymQ0 M r_L r_H u n < 1 - asymQa M r_L r_H u n := by
      by_contra hle; push Not at hle
      have := pow_le_pow_left₀ (by linarith) hle (n - 1)
      rw [hpow_eq] at this; unfold asymBarX at this; linarith [hpb.2]
    have hγ_abs : |asymGammaN M r_L r_H u n| < u := by
      unfold asymGammaN
      rw [abs_div, abs_of_pos hδpos, div_lt_iff₀ hδpos, abs_lt]
      unfold asymThat at hlt1
      unfold asymQa at hlt2
      constructor <;> linarith
    exact ⟨hqa0, by linarith, by linarith, hThat5, hpow_eq, hγ_abs⟩
  refine ⟨hord, ?_⟩
  -- Ratio barx_n / A_n^(n-1) = ((1 + u/n)^n - (1 - u/n)^n) / (2u) → sinh u / u = exp(-γ)
  have hratio_lim : Tendsto (fun n => asymBarX M r_L r_H u n / asymAn M r_L r_H n ^ (n - 1))
      atTop (nhds (Real.exp (-br_gamma u))) := by
    have h1 := Real.tendsto_one_add_div_pow_exp u
    have h2 := Real.tendsto_one_add_div_pow_exp (-u)
    have hsub := (h1.sub h2).div_const (2 * u)
    have hval : (Real.exp u - Real.exp (-u)) / (2 * u) = Real.exp (-br_gamma u) := by
      rw [(br_sinh_div_bounds hu).2.2.1, Real.sinh_eq]; ring
    rw [hval] at hsub
    refine hsub.congr' ?_
    filter_upwards [eventually_ge_atTop 2, hord, hAn_lim.eventually (Ioi_mem_nhds (show (1 / 2 : ℝ) < 1 - (1 - M.F rH) / 2 by linarith))]
      with n hn ho hAn5
    have hnR : (0 : ℝ) < (n : ℝ) := by positivity
    have hAn_pos : 0 < asymAn M r_L r_H n := by linarith
    have hne : 1 - asymThat M r_L r_H u n ≠ 1 - asymQa M r_L r_H u n := by linarith [ho.2.1, ho.2.2.1]
    unfold asymBarX poolAvg
    simp only [hne, ↓reduceIte]
    have h1a : 1 - asymQa M r_L r_H u n = asymAn M r_L r_H n * (1 + u / (n : ℝ)) := by
      unfold asymQa asymDelta asymAn; field_simp [hnR.ne']; ring
    have h1T : 1 - asymThat M r_L r_H u n = asymAn M r_L r_H n * (1 + -u / (n : ℝ)) := by
      unfold asymThat asymDelta asymAn; field_simp [hnR.ne']; ring
    have hdiff : (1 - asymQa M r_L r_H u n) - (1 - asymThat M r_L r_H u n) = 2 * u * asymAn M r_L r_H n / (n : ℝ) := by
      unfold asymQa asymThat asymDelta; ring
    rw [hdiff, h1a, h1T, mul_pow, mul_pow]
    have hpow : asymAn M r_L r_H n ^ n = asymAn M r_L r_H n ^ (n - 1) * asymAn M r_L r_H n := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    rw [hpow]
    field_simp [hnR.ne', hAn_pos.ne', hu.ne']
  -- Take logs: ((n - 1) : ℝ) * log (1 - γ_n / n) → -γ
  have hlog_lim : Tendsto (fun n : ℕ => ((n : ℝ) - 1) * Real.log (1 - asymGammaN M r_L r_H u n / (n : ℝ)))
      atTop (nhds (-br_gamma u)) := by
    have hc : ContinuousAt Real.log (Real.exp (-br_gamma u)) :=
      Real.continuousAt_log (Real.exp_pos _).ne'
    have h := (hc.tendsto.comp hratio_lim)
    rw [Real.log_exp] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 2, hord, hAn_lim.eventually (Ioi_mem_nhds (show (1 / 2 : ℝ) < 1 - (1 - M.F rH) / 2 by linarith))]
      with n hn ho hAn5
    have hAn_pos : 0 < asymAn M r_L r_H n := by linarith
    have hnR : (0 : ℝ) < (n : ℝ) := by positivity
    have h1q : (1 - asymQ0 M r_L r_H u n) / asymAn M r_L r_H n = 1 - asymGammaN M r_L r_H u n / (n : ℝ) := by
      have hAn_def : asymAn M r_L r_H n = 1 - asymQw M r_L r_H n := rfl
      unfold asymGammaN asymDelta; field_simp [hAn_pos.ne', hnR.ne']; rw [hAn_def]; ring
    dsimp [Function.comp]
    rw [← ho.2.2.2.2.1, ← div_pow, h1q, Real.log_pow, Nat.cast_sub (by omega), Nat.cast_one]
  -- Remainder |((n-1)/n) * γ_n + (n-1) * log(1 - γ_n/n)| ≤ 2 u^2 / n → 0
  have hrem0 : Tendsto (fun n : ℕ =>
      (((n : ℝ) - 1) / (n : ℝ)) * asymGammaN M r_L r_H u n +
        ((n : ℝ) - 1) * Real.log (1 - asymGammaN M r_L r_H u n / (n : ℝ))) atTop (nhds 0) := by
    have hbound : Tendsto (fun n : ℕ => 2 * u ^ 2 / (n : ℝ)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hsmall : ∀ᶠ n : ℕ in atTop, u / (n : ℝ) ≤ 1 / 2 :=
      (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop).eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
    filter_upwards [eventually_ge_atTop 2, hord, hsmall, Metric.tendsto_nhds.mp hbound ε hε] with n hn ho hs hbn
    rw [Real.dist_eq, sub_zero] at hbn ⊢
    have hnR : (0 : ℝ) < (n : ℝ) := by positivity
    have hn1R : (0 : ℝ) < (n : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hx_le : |asymGammaN M r_L r_H u n / (n : ℝ)| ≤ u / (n : ℝ) := by
      rw [abs_div, abs_of_pos hnR]; exact div_le_div_of_nonneg_right ho.2.2.2.2.2.le hnR.le
    have hx_lt1 : |asymGammaN M r_L r_H u n / (n : ℝ)| < 1 := by linarith
    have hlb := Real.abs_log_sub_add_sum_range_le hx_lt1 1
    simp only [Finset.sum_range_one, zero_add, pow_one, Nat.cast_zero, div_one] at hlb
    have hstep : |asymGammaN M r_L r_H u n / (n : ℝ) + Real.log (1 - asymGammaN M r_L r_H u n / (n : ℝ))| ≤
        2 * u ^ 2 / (n : ℝ) ^ 2 := by
      have hnum : |asymGammaN M r_L r_H u n / (n : ℝ)| ^ 2 ≤ (u / (n : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hx_le 2
      have hden : 1 / 2 ≤ 1 - |asymGammaN M r_L r_H u n / (n : ℝ)| := by linarith
      calc _ ≤ |asymGammaN M r_L r_H u n / (n : ℝ)| ^ 2 / (1 - |asymGammaN M r_L r_H u n / (n : ℝ)|) := hlb
        _ ≤ (u / (n : ℝ)) ^ 2 / (1 / 2) := div_le_div₀ (by positivity) hnum (by positivity) hden
        _ = 2 * u ^ 2 / (n : ℝ) ^ 2 := by ring
    have hfac : (((n : ℝ) - 1) / (n : ℝ)) * asymGammaN M r_L r_H u n +
        ((n : ℝ) - 1) * Real.log (1 - asymGammaN M r_L r_H u n / (n : ℝ)) =
        ((n : ℝ) - 1) * (asymGammaN M r_L r_H u n / (n : ℝ) + Real.log (1 - asymGammaN M r_L r_H u n / (n : ℝ))) := by ring
    rw [hfac, abs_mul, abs_of_pos hn1R]
    rw [abs_of_pos (by positivity)] at hbn
    calc ((n : ℝ) - 1) * |asymGammaN M r_L r_H u n / (n : ℝ) + Real.log (1 - asymGammaN M r_L r_H u n / (n : ℝ))|
        ≤ ((n : ℝ) - 1) * (2 * u ^ 2 / (n : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hstep hn1R.le
      _ ≤ (n : ℝ) * (2 * u ^ 2 / (n : ℝ) ^ 2) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 2 * u ^ 2 / (n : ℝ) := by field_simp [hnR.ne']
      _ < ε := hbn
  have hscaled : Tendsto (fun n : ℕ => (((n : ℝ) - 1) / (n : ℝ)) * asymGammaN M r_L r_H u n)
      atTop (nhds (br_gamma u)) := by
    have h := hrem0.sub hlog_lim
    rw [zero_sub, neg_neg] at h
    exact h.congr (fun n => by ring)
  have hfrac : Tendsto (fun n : ℕ => ((n : ℝ) - 1) / (n : ℝ)) atTop (nhds 1) := by
    have h := tendsto_const_nhds (x := (1 : ℝ)).sub (tendsto_const_nhds (x := (1 : ℝ)).div_atTop tendsto_natCast_atTop_atTop)
    rw [sub_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (n : ℝ) ≠ 0 := by positivity
    field_simp [hnR]
  have hdiv := hscaled.div hfrac one_ne_zero
  rw [div_one] at hdiv
  refine hdiv.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hnR : (n : ℝ) ≠ 0 := by positivity
  have hn1' : (n : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  simp only [Pi.div_apply]
  field_simp [hn1', hnR]

/-- Helper (Part A1): ordering of `\hat v_n, w_n, v_{2,n}, β_n, v_{a,n}` and convergence to `rH`. -/
lemma br_dev_ord (M : Market) (hm : M.m = 2) (ha : M.a = 0)
    {r_L r_H : ℕ → ℝ} {rL rH u : ℝ} (hrL0 : 0 ≤ rL) (hrLH : rL < rH) (hrH1 : rH < 1)
    (hL_lim : Tendsto r_L atTop (nhds rL)) (hH_lim : Tendsto r_H atTop (nhds rH))
    (hL_nn : ∀ᶠ n in atTop, 0 ≤ r_L n) (hu : 0 < u) :
    (∀ᶠ n : ℕ in atTop,
      0 < asymVhat M r_L r_H u n ∧ asymVhat M r_L r_H u n < asymW M r_L r_H n ∧
      asymW M r_L r_H n < asymV2 M r_L r_H u n ∧ asymV2 M r_L r_H u n < asymVa M r_L r_H u n ∧
      asymVa M r_L r_H u n < 1 ∧
      M.F (asymVa M r_L r_H u n) = 1 - 2 * asymQa M r_L r_H u n ∧
      M.F (asymV2 M r_L r_H u n) = 1 - (asymQa M r_L r_H u n + asymQ0 M r_L r_H u n) ∧
      M.F (asymVhat M r_L r_H u n) = 1 - (asymThat M r_L r_H u n + asymQ0 M r_L r_H u n) ∧
      asymV2 M r_L r_H u n < asymBeta M r_L r_H u n ∧ asymBeta M r_L r_H u n < asymVa M r_L r_H u n) ∧
    Tendsto (asymVhat M r_L r_H u) atTop (nhds rH) ∧
    Tendsto (asymV2 M r_L r_H u) atTop (nhds rH) ∧
    Tendsto (asymVa M r_L r_H u) atTop (nhds rH) := by
  have hcut := theorem4_cutoff_asymptotics M hm ha hrL0 hrLH hrH1 hL_lim hH_lim hL_nn
  have hγ := br_gammaN_tendsto M hm ha hrL0 hrLH hrH1 hL_lim hH_lim hL_nn hu
  have hb := br_sinh_div_bounds hu
  have hw_lim := hcut.2.1
  have hF_lim : Tendsto (fun n => M.F (asymW M r_L r_H n)) atTop (nhds (M.F rH)) :=
    (M.F_continuousOn.continuousAt (Icc_mem_nhds (by rw [ha]; linarith) hrH1)).tendsto.comp hw_lim
  have hFH_pos : 0 < M.F rH := by
    rw [← M.hF_a]; exact M.F_strictMonoOn (left_mem_Icc.mpr M.ha1.le) ⟨by rw [ha]; linarith, hrH1.le⟩ (by rw [ha]; linarith)
  have hFH_lt1 : M.F rH < 1 := by
    rw [← M.hF_1]; exact M.F_strictMonoOn ⟨by rw [ha]; linarith, hrH1.le⟩ (right_mem_Icc.mpr M.ha1.le) hrH1
  have hfH : 0 < M.f rH := M.hf_pos rH ⟨by rw [ha]; linarith, hrH1.le⟩
  have hqw_lim : Tendsto (asymQw M r_L r_H) atTop (nhds ((1 - M.F rH) / 2)) :=
    (tendsto_const_nhds.sub hF_lim).div_const 2
  have hAn_lim : Tendsto (asymAn M r_L r_H) atTop (nhds (1 - (1 - M.F rH) / 2)) :=
    tendsto_const_nhds.sub hqw_lim
  have hAnH_pos : 0 < 1 - (1 - M.F rH) / 2 := by linarith
  have hδ_lim : Tendsto (asymDelta M r_L r_H) atTop (nhds 0) :=
    hAn_lim.div_atTop tendsto_natCast_atTop_atTop
  have hqa_lim : Tendsto (asymQa M r_L r_H u) atTop (nhds ((1 - M.F rH) / 2)) := by
    unfold asymQa; simpa using hqw_lim.sub (hδ_lim.const_mul u)
  have hThat_lim : Tendsto (asymThat M r_L r_H u) atTop (nhds ((1 - M.F rH) / 2)) := by
    unfold asymThat; simpa using hqw_lim.add (hδ_lim.const_mul u)
  have hq0_lim : Tendsto (asymQ0 M r_L r_H u) atTop (nhds ((1 - M.F rH) / 2)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hqa_lim hThat_lim ?_ ?_
    · filter_upwards [hγ.1] with n hn using hn.2.1.le
    · filter_upwards [hγ.1] with n hn using hn.2.2.1.le
  -- Convergence of invF arguments to M.F rH ∈ (0, 1)
  have harg_a : Tendsto (fun n => 1 - 2 * asymQa M r_L r_H u n) atTop (nhds (M.F rH)) := by
    have h := tendsto_const_nhds (x := (1 : ℝ)).sub (hqa_lim.const_mul 2)
    convert h using 1; ring
  have harg_2 : Tendsto (fun n => 1 - (asymQa M r_L r_H u n + asymQ0 M r_L r_H u n)) atTop (nhds (M.F rH)) := by
    have h := tendsto_const_nhds (x := (1 : ℝ)).sub (hqa_lim.add hq0_lim)
    convert h using 1; ring
  have harg_h : Tendsto (fun n => 1 - (asymThat M r_L r_H u n + asymQ0 M r_L r_H u n)) atTop (nhds (M.F rH)) := by
    have h := tendsto_const_nhds (x := (1 : ℝ)).sub (hThat_lim.add hq0_lim)
    convert h using 1; ring
  have hinv_c : ContinuousAt M.invF (M.F rH) :=
    M.invF_continuousOn.continuousAt (Icc_mem_nhds hFH_pos hFH_lt1)
  have hinv_rH : M.invF (M.F rH) = rH := M.invF_F ⟨by rw [ha]; linarith, hrH1.le⟩
  have hva_lim : Tendsto (asymVa M r_L r_H u) atTop (nhds rH) := by
    unfold asymVa; simpa [hinv_rH, Function.comp_def] using hinv_c.tendsto.comp harg_a
  have hv2_lim : Tendsto (asymV2 M r_L r_H u) atTop (nhds rH) := by
    unfold asymV2; simpa [hinv_rH, Function.comp_def] using hinv_c.tendsto.comp harg_2
  have hvhat_lim : Tendsto (asymVhat M r_L r_H u) atTop (nhds rH) := by
    unfold asymVhat; simpa [hinv_rH, Function.comp_def] using hinv_c.tendsto.comp harg_h
  -- Ordering 0 < v_hat < w_n < v_2 < v_a < 1 and F values
  have hord1 : ∀ᶠ n : ℕ in atTop,
      0 < asymVhat M r_L r_H u n ∧ asymVhat M r_L r_H u n < asymW M r_L r_H n ∧
      asymW M r_L r_H n < asymV2 M r_L r_H u n ∧ asymV2 M r_L r_H u n < asymVa M r_L r_H u n ∧
      asymVa M r_L r_H u n < 1 ∧
      M.F (asymVa M r_L r_H u n) = 1 - 2 * asymQa M r_L r_H u n ∧
      M.F (asymV2 M r_L r_H u n) = 1 - (asymQa M r_L r_H u n + asymQ0 M r_L r_H u n) ∧
      M.F (asymVhat M r_L r_H u n) = 1 - (asymThat M r_L r_H u n + asymQ0 M r_L r_H u n) ∧
      asymV2 M r_L r_H u n < asymBeta M r_L r_H u n ∧ asymBeta M r_L r_H u n < asymVa M r_L r_H u n := by
    have hγ_pos : ∀ᶠ n in atTop, 0 < u + asymGammaN M r_L r_H u n ∧ asymGammaN M r_L r_H u n < 0 := by
      filter_upwards [hγ.2.eventually (Ioo_mem_nhds hb.2.2.2.1 hb.2.2.2.2)] with n hn
      exact ⟨by linarith [hn.1], hn.2⟩
    filter_upwards [eventually_ge_atTop 2, hcut.1, hγ.1, hγ_pos,
      harg_a.eventually (Ioo_mem_nhds hFH_pos hFH_lt1),
      harg_2.eventually (Ioo_mem_nhds hFH_pos hFH_lt1),
      harg_h.eventually (Ioo_mem_nhds hFH_pos hFH_lt1),
      hAn_lim.eventually (Ioi_mem_nhds (show (1 / 2 : ℝ) < 1 - (1 - M.F rH) / 2 by linarith)),
      hH_lim.eventually (Ioi_mem_nhds (show (0 : ℝ) < rH by linarith))]
      with n hn hcn hγn hγp ha_in h2_in hh_in hAn5 hrHpos
    have hδpos : 0 < asymDelta M r_L r_H n := div_pos (by linarith) (by positivity)
    have hq0_eq : asymQ0 M r_L r_H u n = asymQw M r_L r_H n + asymGammaN M r_L r_H u n * asymDelta M r_L r_H n := by
      unfold asymGammaN; field_simp [hδpos.ne']; ring
    have hFva : M.F (asymVa M r_L r_H u n) = 1 - 2 * asymQa M r_L r_H u n := M.F_invF ha_in.1.le ha_in.2.le
    have hFv2 : M.F (asymV2 M r_L r_H u n) = 1 - (asymQa M r_L r_H u n + asymQ0 M r_L r_H u n) := M.F_invF h2_in.1.le h2_in.2.le
    have hFvh : M.F (asymVhat M r_L r_H u n) = 1 - (asymThat M r_L r_H u n + asymQ0 M r_L r_H u n) := M.F_invF hh_in.1.le hh_in.2.le
    have hFw_eq : M.F (asymW M r_L r_H n) = 1 - 2 * asymQw M r_L r_H n := by unfold asymQw; ring
    have h1 : 1 - (asymThat M r_L r_H u n + asymQ0 M r_L r_H u n) < M.F (asymW M r_L r_H n) := by
      rw [hFw_eq, hq0_eq]; unfold asymThat; nlinarith [hγp.1, hδpos]
    have h2 : M.F (asymW M r_L r_H n) < 1 - (asymQa M r_L r_H u n + asymQ0 M r_L r_H u n) := by
      rw [hFw_eq, hq0_eq]; unfold asymQa; nlinarith [hγp.2, hu, hδpos]
    have h3 : 1 - (asymQa M r_L r_H u n + asymQ0 M r_L r_H u n) < 1 - 2 * asymQa M r_L r_H u n := by
      linarith [hγn.2.1]
    have hvh_pos : 0 < asymVhat M r_L r_H u n := by
      rw [← ha, ← M.invF_F (left_mem_Icc.mpr M.ha1.le), M.hF_a]
      exact M.invF_strictMonoOn (left_mem_Icc.mpr zero_le_one) (Ioo_subset_Icc_self hh_in) hh_in.1
    have hw_mem : asymW M r_L r_H n ∈ Icc M.a 1 := ⟨by rw [ha]; linarith [hrHpos, hcn.1.1], hcn.1.2.le⟩
    have hvh_w : asymVhat M r_L r_H u n < asymW M r_L r_H n := by
      rw [← M.invF_F hw_mem]
      exact M.invF_strictMonoOn (Ioo_subset_Icc_self hh_in) (M.F_mem_Icc hw_mem) h1
    have hw_v2 : asymW M r_L r_H n < asymV2 M r_L r_H u n := by
      rw [← M.invF_F hw_mem]
      exact M.invF_strictMonoOn (M.F_mem_Icc hw_mem) (Ioo_subset_Icc_self h2_in) h2
    have hv2_va : asymV2 M r_L r_H u n < asymVa M r_L r_H u n :=
      M.invF_strictMonoOn (Ioo_subset_Icc_self h2_in) (Ioo_subset_Icc_self ha_in) h3
    have hva_lt1 : asymVa M r_L r_H u n < 1 := by
      rw [← M.invF_F (right_mem_Icc.mpr M.ha1.le), M.hF_1]
      exact M.invF_strictMonoOn (Ioo_subset_Icc_self ha_in) (right_mem_Icc.mpr zero_le_one) ha_in.2
    -- Show β_n ∈ (v_2, v_a)
    have hden : 0 < (1 - asymQa M r_L r_H u n) ^ (n - 1) - asymBarX M r_L r_H u n := by
      rw [← hγn.2.2.2.2.1]
      have : (1 - asymQ0 M r_L r_H u n) ^ (n - 1) < (1 - asymQa M r_L r_H u n) ^ (n - 1) :=
        pow_lt_pow_left₀ (by linarith [hγn.2.1]) (by linarith [hγn.2.2.1, hγn.2.2.2.1]) (by omega)
      linarith
    have hFc : ContinuousOn M.F (Icc (asymV2 M r_L r_H u n) (asymVa M r_L r_H u n)) :=
      M.F_continuousOn.mono (Icc_subset_Icc (by rw [ha]; linarith) hva_lt1.le)
    have hI_pos : 0 < ∫ v in asymV2 M r_L r_H u n..asymVa M r_L r_H u n,
        ((asymQa M r_L r_H u n + M.F v) ^ (n - 1) - asymBarX M r_L r_H u n) := by
      apply intervalIntegral.integral_pos hv2_va (((continuousOn_const.add hFc).pow _).sub continuousOn_const)
      · intro v hv
        simp only [Pi.sub_apply, Pi.pow_apply, Pi.add_apply]
        rw [← hγn.2.2.2.2.1]
        have hFv : M.F (asymV2 M r_L r_H u n) ≤ M.F v :=
          M.F_strictMonoOn.monotoneOn ⟨by rw [ha]; linarith, le_trans hv2_va.le hva_lt1.le⟩
            ⟨by rw [ha]; linarith [hv.1], le_trans hv.2 hva_lt1.le⟩ hv.1.le
        have hlo : 1 - asymQ0 M r_L r_H u n ≤ asymQa M r_L r_H u n + M.F v := by linarith [hFv2]
        linarith [pow_le_pow_left₀ (by linarith [hγn.2.2.1, hγn.2.2.2.1]) hlo (n - 1)]
      · let vm := (asymV2 M r_L r_H u n + asymVa M r_L r_H u n) / 2
        refine ⟨vm, ⟨by dsimp [vm]; linarith, by dsimp [vm]; linarith⟩, ?_⟩
        simp only [Pi.sub_apply, Pi.pow_apply, Pi.add_apply]
        rw [← hγn.2.2.2.2.1]
        have hFv : M.F (asymV2 M r_L r_H u n) < M.F vm :=
          M.F_strictMonoOn ⟨by rw [ha]; linarith, le_trans hv2_va.le hva_lt1.le⟩
            ⟨by rw [ha]; dsimp [vm]; linarith, by dsimp [vm]; linarith⟩ (by dsimp [vm]; linarith)
        have hlo : 1 - asymQ0 M r_L r_H u n < asymQa M r_L r_H u n + M.F vm := by linarith [hFv2]
        have hpow : (1 - asymQ0 M r_L r_H u n) ^ (n - 1) < (asymQa M r_L r_H u n + M.F vm) ^ (n - 1) :=
          pow_lt_pow_left₀ hlo (by linarith [hγn.2.2.1, hγn.2.2.2.1]) (by omega)
        linarith
    have hI_lt : ∫ v in asymV2 M r_L r_H u n..asymVa M r_L r_H u n,
        ((asymQa M r_L r_H u n + M.F v) ^ (n - 1) - asymBarX M r_L r_H u n) <
        (asymVa M r_L r_H u n - asymV2 M r_L r_H u n) * ((1 - asymQa M r_L r_H u n) ^ (n - 1) - asymBarX M r_L r_H u n) := by
      have hsub : 0 < ∫ v in asymV2 M r_L r_H u n..asymVa M r_L r_H u n,
          ((1 - asymQa M r_L r_H u n) ^ (n - 1) - (asymQa M r_L r_H u n + M.F v) ^ (n - 1)) := by
        apply intervalIntegral.integral_pos hv2_va (continuousOn_const.sub ((continuousOn_const.add hFc).pow _))
        · intro v hv
          simp only [Pi.sub_apply, Pi.pow_apply, Pi.add_apply]
          have hFv : M.F v ≤ M.F (asymVa M r_L r_H u n) :=
            M.F_strictMonoOn.monotoneOn ⟨by rw [ha]; linarith [hv.1], le_trans hv.2 hva_lt1.le⟩
              ⟨by rw [ha]; linarith, hva_lt1.le⟩ hv.2
          have hhi : asymQa M r_L r_H u n + M.F v ≤ 1 - asymQa M r_L r_H u n := by linarith [hFva]
          have hnn : 0 ≤ asymQa M r_L r_H u n + M.F v := by
            have := (M.F_mem_Icc ⟨by rw [ha]; linarith [hv.1], le_trans hv.2 hva_lt1.le⟩).1; linarith [hγn.1]
          linarith [pow_le_pow_left₀ hnn hhi (n - 1)]
        · let vm := (asymV2 M r_L r_H u n + asymVa M r_L r_H u n) / 2
          refine ⟨vm, ⟨by dsimp [vm]; linarith, by dsimp [vm]; linarith⟩, ?_⟩
          simp only [Pi.sub_apply, Pi.pow_apply, Pi.add_apply]
          have hFv : M.F vm < M.F (asymVa M r_L r_H u n) :=
            M.F_strictMonoOn ⟨by rw [ha]; dsimp [vm]; linarith, by dsimp [vm]; linarith⟩
              ⟨by rw [ha]; linarith, hva_lt1.le⟩ (by dsimp [vm]; linarith)
          have hhi : asymQa M r_L r_H u n + M.F vm < 1 - asymQa M r_L r_H u n := by linarith [hFva]
          have hvm_mem : vm ∈ Icc M.a 1 := ⟨by rw [ha]; dsimp [vm]; linarith, by dsimp [vm]; linarith⟩
          have hnn : 0 ≤ asymQa M r_L r_H u n + M.F vm := by
            have := (M.F_mem_Icc hvm_mem).1; linarith [hγn.1]
          have hpow : (asymQa M r_L r_H u n + M.F vm) ^ (n - 1) < (1 - asymQa M r_L r_H u n) ^ (n - 1) :=
            pow_lt_pow_left₀ hhi hnn (by omega)
          linarith
      have hsub_int : IntervalIntegrable (fun v => (asymQa M r_L r_H u n + M.F v) ^ (n - 1) - asymBarX M r_L r_H u n)
          volume (asymV2 M r_L r_H u n) (asymVa M r_L r_H u n) :=
        ((((continuousOn_const.add hFc).pow _).sub continuousOn_const).mono (by rw [uIcc_of_le hv2_va.le])).intervalIntegrable
      have heq : (fun v => ((1 - asymQa M r_L r_H u n) ^ (n - 1) - asymBarX M r_L r_H u n) -
          ((asymQa M r_L r_H u n + M.F v) ^ (n - 1) - asymBarX M r_L r_H u n)) =
          fun v => (1 - asymQa M r_L r_H u n) ^ (n - 1) - (asymQa M r_L r_H u n + M.F v) ^ (n - 1) := by ext v; ring
      rw [← heq, intervalIntegral.integral_sub intervalIntegrable_const hsub_int,
        intervalIntegral.integral_const, smul_eq_mul] at hsub
      linarith
    have hβ_lt : asymBeta M r_L r_H u n < asymVa M r_L r_H u n := by
      unfold asymBeta; linarith [div_pos hI_pos hden]
    have hβ_gt : asymV2 M r_L r_H u n < asymBeta M r_L r_H u n := by
      unfold asymBeta
      have : (∫ v in asymV2 M r_L r_H u n..asymVa M r_L r_H u n,
          ((asymQa M r_L r_H u n + M.F v) ^ (n - 1) - asymBarX M r_L r_H u n)) /
          ((1 - asymQa M r_L r_H u n) ^ (n - 1) - asymBarX M r_L r_H u n) <
          asymVa M r_L r_H u n - asymV2 M r_L r_H u n := (div_lt_iff₀ hden).mpr hI_lt
      linarith
    exact ⟨hvh_pos, hvh_w, hw_v2, hv2_va, hva_lt1, hFva, hFv2, hFvh, hβ_gt, hβ_lt⟩
  exact ⟨hord1, hvhat_lim, hv2_lim, hva_lim⟩

/-- Helper (Part A2): `(\hat v_n - r_H n) / δ_n → (1 - u - γ) / f(rH)`. -/
lemma br_dev_gap_hr (M : Market) (hm : M.m = 2) (ha : M.a = 0)
    {r_L r_H : ℕ → ℝ} {rL rH u : ℝ} (hrL0 : 0 ≤ rL) (hrLH : rL < rH) (hrH1 : rH < 1)
    (hL_lim : Tendsto r_L atTop (nhds rL)) (hH_lim : Tendsto r_H atTop (nhds rH))
    (hL_nn : ∀ᶠ n in atTop, 0 ≤ r_L n) (hu : 0 < u) :
    Tendsto (fun n : ℕ => (asymVhat M r_L r_H u n - r_H n) / asymDelta M r_L r_H n)
      atTop (nhds ((1 - u - br_gamma u) / M.f rH)) := by
  have hcut := theorem4_cutoff_asymptotics M hm ha hrL0 hrLH hrH1 hL_lim hH_lim hL_nn
  have hγ := br_gammaN_tendsto M hm ha hrL0 hrLH hrH1 hL_lim hH_lim hL_nn hu
  have hord := br_dev_ord M hm ha hrL0 hrLH hrH1 hL_lim hH_lim hL_nn hu
  have hord1 := hord.1
  have hvhat_lim := hord.2.1
  have hw_lim := hcut.2.1
  have hF_lim : Tendsto (fun n => M.F (asymW M r_L r_H n)) atTop (nhds (M.F rH)) :=
    (M.F_continuousOn.continuousAt (Icc_mem_nhds (by rw [ha]; linarith) hrH1)).tendsto.comp hw_lim
  have hFH_pos : 0 < M.F rH := by
    rw [← M.hF_a]; exact M.F_strictMonoOn (left_mem_Icc.mpr M.ha1.le) ⟨by rw [ha]; linarith, hrH1.le⟩ (by rw [ha]; linarith)
  have hfH : 0 < M.f rH := M.hf_pos rH ⟨by rw [ha]; linarith, hrH1.le⟩
  have hqw_lim : Tendsto (asymQw M r_L r_H) atTop (nhds ((1 - M.F rH) / 2)) :=
    (tendsto_const_nhds.sub hF_lim).div_const 2
  have hAn_lim : Tendsto (asymAn M r_L r_H) atTop (nhds (1 - (1 - M.F rH) / 2)) :=
    tendsto_const_nhds.sub hqw_lim
  have hAnH_pos : 0 < 1 - (1 - M.F rH) / 2 := by linarith
  have hgap_wh : Tendsto (fun n : ℕ => (asymW M r_L r_H n - asymVhat M r_L r_H u n) / asymDelta M r_L r_H n)
      atTop (nhds ((u + br_gamma u) / M.f rH)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    let ε₁ := min (M.f rH / 2) (ε * M.f rH ^ 2 / (8 * (u + 2)))
    have hε₁ : 0 < ε₁ := lt_min (by positivity) (by positivity)
    have hε₁2 : ε₁ ≤ M.f rH / 2 := min_le_left _ _
    obtain ⟨δ₁, hδ₁, hfδ⟩ := Metric.continuousWithinAt_iff.mp (M.hf_cont rH ⟨by rw [ha]; linarith, hrH1.le⟩) ε₁ hε₁
    have hγ_near := Metric.tendsto_nhds.mp hγ.2 (ε * M.f rH / 4) (by positivity)
    filter_upwards [eventually_ge_atTop 2, hord1, hγ.1, hγ_near,
      Metric.tendsto_nhds.mp hw_lim δ₁ hδ₁, Metric.tendsto_nhds.mp hvhat_lim δ₁ hδ₁,
      hAn_lim.eventually (Ioi_mem_nhds (show (1 / 2 : ℝ) < 1 - (1 - M.F rH) / 2 by linarith))]
      with n hn ho hγn hγb hwb hvhb hAn5
    have hδpos : 0 < asymDelta M r_L r_H n := div_pos (by linarith) (by positivity)
    have hw1 : asymW M r_L r_H n < 1 := lt_trans ho.2.2.1 (lt_trans ho.2.2.2.1 ho.2.2.2.2.1)
    have hwin : ∀ t ∈ Icc (asymVhat M r_L r_H u n) (asymW M r_L r_H n), |M.f t - M.f rH| ≤ ε₁ := by
      intro t ht
      have hdist : dist t rH < δ₁ := by
        rw [Real.dist_eq] at hwb hvhb ⊢; rw [abs_lt] at hwb hvhb ⊢
        constructor <;> linarith [ht.1, ht.2]
      exact le_of_lt (by simpa [Real.dist_eq] using hfδ ⟨by rw [ha]; linarith [ho.1, ht.1], le_trans ht.2 hw1.le⟩ hdist)
    have hFb := br_F_diff_bound M (by rw [ha]; exact ho.1.le) ho.2.1.le hw1.le hwin
    have hFdiff : M.F (asymW M r_L r_H n) - M.F (asymVhat M r_L r_H u n) =
        (u + asymGammaN M r_L r_H u n) * asymDelta M r_L r_H n := by
      rw [ho.2.2.2.2.2.2.2.1]
      have hFw : M.F (asymW M r_L r_H n) = 1 - 2 * asymQw M r_L r_H n := by unfold asymQw; ring
      have hq0 : asymQ0 M r_L r_H u n = asymQw M r_L r_H n + asymGammaN M r_L r_H u n * asymDelta M r_L r_H n := by
        unfold asymGammaN; field_simp [hδpos.ne']; ring
      rw [hFw, hq0]; unfold asymThat; ring
    rw [hFdiff] at hFb
    have hfe : 0 < M.f rH - ε₁ := by linarith only [hε₁2, hfH]
    have huγ_nn : 0 ≤ u + asymGammaN M r_L r_H u n := by linarith [(abs_lt.mp hγn.2.2.2.2.2).1]
    have huγ_le : u + asymGammaN M r_L r_H u n ≤ 2 * u := by linarith [(abs_lt.mp hγn.2.2.2.2.2).2]
    have hhi : (asymW M r_L r_H n - asymVhat M r_L r_H u n) / asymDelta M r_L r_H n ≤
        (u + asymGammaN M r_L r_H u n) / (M.f rH - ε₁) := by
      rw [div_le_div_iff₀ hδpos hfe]; linarith only [hFb.1]
    have hlo : (u + asymGammaN M r_L r_H u n) / (M.f rH + ε₁) ≤
        (asymW M r_L r_H n - asymVhat M r_L r_H u n) / asymDelta M r_L r_H n := by
      rw [div_le_div_iff₀ (by positivity) hδpos]; linarith only [hFb.2]
    have hε1_b : ε₁ * (8 * (u + 2)) ≤ ε * M.f rH ^ 2 :=
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    have h4 : (2 * u) * ε₁ ≤ ε / 4 * M.f rH ^ 2 := by nlinarith only [hε1_b, hε₁, hu]
    have he1 : (u + asymGammaN M r_L r_H u n) / (M.f rH - ε₁) - (u + asymGammaN M r_L r_H u n) / M.f rH ≤ ε / 2 := by
      rw [div_sub_div _ _ hfe.ne' hfH.ne', div_le_iff₀ (mul_pos hfe hfH)]
      have hfac : (u + asymGammaN M r_L r_H u n) * M.f rH - (M.f rH - ε₁) * (u + asymGammaN M r_L r_H u n) =
          (u + asymGammaN M r_L r_H u n) * ε₁ := by ring
      rw [hfac]
      have h1 : (u + asymGammaN M r_L r_H u n) * ε₁ ≤ (2 * u) * ε₁ := mul_le_mul_of_nonneg_right huγ_le hε₁.le
      have hm : M.f rH ^ 2 / 2 ≤ (M.f rH - ε₁) * M.f rH := by nlinarith only [hε₁2, hfH]
      have h2 : ε / 4 * M.f rH ^ 2 ≤ ε / 2 * ((M.f rH - ε₁) * M.f rH) := by nlinarith only [hm, hε]
      linarith only [h1, h2, h4]
    have he2 : (u + asymGammaN M r_L r_H u n) / M.f rH - (u + asymGammaN M r_L r_H u n) / (M.f rH + ε₁) ≤ ε / 2 := by
      rw [div_sub_div _ _ hfH.ne' (by positivity), div_le_iff₀ (by positivity)]
      have hfac : (u + asymGammaN M r_L r_H u n) * (M.f rH + ε₁) - M.f rH * (u + asymGammaN M r_L r_H u n) =
          (u + asymGammaN M r_L r_H u n) * ε₁ := by ring
      rw [hfac]
      have h1 : (u + asymGammaN M r_L r_H u n) * ε₁ ≤ (2 * u) * ε₁ := mul_le_mul_of_nonneg_right huγ_le hε₁.le
      have hm : M.f rH ^ 2 ≤ M.f rH * (M.f rH + ε₁) := by nlinarith only [hfH, hε₁]
      have h2 : ε / 4 * M.f rH ^ 2 ≤ ε / 2 * (M.f rH * (M.f rH + ε₁)) := by nlinarith only [hm, hε, sq_nonneg (M.f rH)]
      linarith only [h1, h2, h4]
    rw [Real.dist_eq] at hγb ⊢
    have hγd : |(u + asymGammaN M r_L r_H u n) / M.f rH - (u + br_gamma u) / M.f rH| < ε / 4 := by
      rw [← sub_div, abs_div, abs_of_pos hfH, div_lt_iff₀ hfH]
      have : (u + asymGammaN M r_L r_H u n) - (u + br_gamma u) = asymGammaN M r_L r_H u n - br_gamma u := by ring
      rw [this]; linarith only [hγb]
    rw [abs_lt] at hγd ⊢
    constructor <;> linarith only [hhi, hlo, he1, he2, hγd.1, hγd.2, hε]
  have hgap_hr : Tendsto (fun n : ℕ => (asymVhat M r_L r_H u n - r_H n) / asymDelta M r_L r_H n)
      atTop (nhds ((1 - u - br_gamma u) / M.f rH)) := by
    have hwr : Tendsto (fun n : ℕ => (asymW M r_L r_H n - r_H n) / asymDelta M r_L r_H n)
        atTop (nhds (1 / M.f rH)) := by
      have h := (hcut.2.2.div hAn_lim hAnH_pos.ne').add (tendsto_const_nhds (x := 1 / M.f rH))
      rw [zero_div, zero_add] at h
      refine h.congr' ?_
      filter_upwards [eventually_ge_atTop 2, hAn_lim.eventually (Ioi_mem_nhds (show (1 / 2 : ℝ) < 1 - (1 - M.F rH) / 2 by linarith))] with n hn hAn5
      have hnR : (n : ℝ) ≠ 0 := by positivity
      have hAn_pos : 0 < asymAn M r_L r_H n := by linarith
      have hAn_def : asymAn M r_L r_H n = 1 - asymQw M r_L r_H n := rfl
      simp only [Pi.div_apply]
      unfold asymDelta
      field_simp [hnR, hAn_pos.ne', hfH.ne']
      rw [hAn_def]; unfold asymQw; ring
    have h := hwr.sub hgap_wh
    have hval : 1 / M.f rH - (u + br_gamma u) / M.f rH = (1 - u - br_gamma u) / M.f rH := by ring
    rw [hval] at h
    exact h.congr (fun n => by ring)
  exact hgap_hr

/-- Asymptotics of `v_{a,n}`, `v_{2,n}`, `\hat v_n`, `v_{0,n}`, `β_n`, and eq. (21). -/
lemma br_dev_coords_asym (M : Market) (hm : M.m = 2) (ha : M.a = 0)
    {r_L r_H : ℕ → ℝ} {rL rH u : ℝ} (hrL0 : 0 ≤ rL) (hrLH : rL < rH) (hrH1 : rH < 1)
    (hL_lim : Tendsto r_L atTop (nhds rL)) (hH_lim : Tendsto r_H atTop (nhds rH))
    (hL_nn : ∀ᶠ n in atTop, 0 ≤ r_L n)
    (hu : 0 < u) (huγ : u + br_gamma u < 1)
    (hfeas : (1 - u - br_gamma u) * Real.exp (-br_gamma u) < Real.exp (-u)) :
    (∀ᶠ n : ℕ in atTop,
      0 < asymV0 M r_L r_H u n ∧ asymV0 M r_L r_H u n < r_H n ∧
      r_H n < asymVhat M r_L r_H u n ∧ asymVhat M r_L r_H u n < asymW M r_L r_H n ∧
      asymW M r_L r_H n < asymV2 M r_L r_H u n ∧ asymV2 M r_L r_H u n < asymBeta M r_L r_H u n ∧
      asymBeta M r_L r_H u n < asymVa M r_L r_H u n ∧ asymVa M r_L r_H u n < 1 ∧
      M.F (asymVa M r_L r_H u n) = 1 - 2 * asymQa M r_L r_H u n ∧
      M.F (asymV2 M r_L r_H u n) = 1 - (asymQa M r_L r_H u n + asymQ0 M r_L r_H u n) ∧
      M.F (asymVhat M r_L r_H u n) = 1 - (asymThat M r_L r_H u n + asymQ0 M r_L r_H u n) ∧
      ∫ v in asymV0 M r_L r_H u n..asymVhat M r_L r_H u n, (asymQ0 M r_L r_H u n + M.F v) ^ (n - 1) =
        (asymVhat M r_L r_H u n - r_H n) * (1 - asymQ0 M r_L r_H u n) ^ (n - 1)) ∧
    Tendsto (asymV0 M r_L r_H u) atTop (nhds rH) ∧
    Tendsto (asymVhat M r_L r_H u) atTop (nhds rH) ∧
    Tendsto (asymV2 M r_L r_H u) atTop (nhds rH) ∧
    Tendsto (asymVa M r_L r_H u) atTop (nhds rH) ∧
    Tendsto (fun n => ((1 - asymThat M r_L r_H u n) ^ n -
      (asymQ0 M r_L r_H u n + M.F (asymV0 M r_L r_H u n)) ^ n) / asymAn M r_L r_H n ^ n)
      atTop (nhds ((1 - u - br_gamma u) * Real.exp (-br_gamma u))) := by
  have hcut := theorem4_cutoff_asymptotics M hm ha hrL0 hrLH hrH1 hL_lim hH_lim hL_nn
  have hγ := br_gammaN_tendsto M hm ha hrL0 hrLH hrH1 hL_lim hH_lim hL_nn hu
  have hpartA := br_dev_ord M hm ha hrL0 hrLH hrH1 hL_lim hH_lim hL_nn hu
  have hord1 := hpartA.1
  have hvhat_lim := hpartA.2.1
  have hv2_lim := hpartA.2.2.1
  have hva_lim := hpartA.2.2.2
  have hgap_hr := br_dev_gap_hr M hm ha hrL0 hrLH hrH1 hL_lim hH_lim hL_nn hu
  have hw_lim := hcut.2.1
  have hF_lim : Tendsto (fun n => M.F (asymW M r_L r_H n)) atTop (nhds (M.F rH)) :=
    (M.F_continuousOn.continuousAt (Icc_mem_nhds (by rw [ha]; linarith) hrH1)).tendsto.comp hw_lim
  have hFH_pos : 0 < M.F rH := by
    rw [← M.hF_a]; exact M.F_strictMonoOn (left_mem_Icc.mpr M.ha1.le) ⟨by rw [ha]; linarith, hrH1.le⟩ (by rw [ha]; linarith)
  have hfH : 0 < M.f rH := M.hf_pos rH ⟨by rw [ha]; linarith, hrH1.le⟩
  have hqw_lim : Tendsto (asymQw M r_L r_H) atTop (nhds ((1 - M.F rH) / 2)) :=
    (tendsto_const_nhds.sub hF_lim).div_const 2
  have hAn_lim : Tendsto (asymAn M r_L r_H) atTop (nhds (1 - (1 - M.F rH) / 2)) :=
    tendsto_const_nhds.sub hqw_lim
  have hAnH_pos : 0 < 1 - (1 - M.F rH) / 2 := by linarith
  have hδ_lim : Tendsto (asymDelta M r_L r_H) atTop (nhds 0) :=
    hAn_lim.div_atTop tendsto_natCast_atTop_atTop
  have hThat_lim : Tendsto (asymThat M r_L r_H u) atTop (nhds ((1 - M.F rH) / 2)) := by
    unfold asymThat; simpa using hqw_lim.add (hδ_lim.const_mul u)
  -- Existence of v_{0,n} ∈ (0, v_hat n) and v_{0,n} < r_H n
  have hRHS_lim : Tendsto (fun n : ℕ =>
      ((n : ℝ) * (asymVhat M r_L r_H u n - r_H n) * (1 - asymQ0 M r_L r_H u n) ^ (n - 1)) /
        asymAn M r_L r_H n ^ n)
      atTop (nhds ((1 - u - br_gamma u) * Real.exp (-br_gamma u) / M.f rH)) := by
    have hexp_γ : Tendsto (fun n : ℕ => (1 + (-asymGammaN M r_L r_H u n) / (n : ℝ)) ^ (n - 1))
        atTop (nhds (Real.exp (-br_gamma u))) :=
      (br_exp_pow_tendsto hγ.2.neg).2
    have hprod := hgap_hr.mul hexp_γ
    have hval : (1 - u - br_gamma u) / M.f rH * Real.exp (-br_gamma u) =
        (1 - u - br_gamma u) * Real.exp (-br_gamma u) / M.f rH := by ring
    rw [hval] at hprod
    refine hprod.congr' ?_
    filter_upwards [eventually_ge_atTop 2, hAn_lim.eventually (Ioi_mem_nhds (show (1 / 2 : ℝ) < 1 - (1 - M.F rH) / 2 by linarith))] with n hn hAn5
    have hnR : (0 : ℝ) < (n : ℝ) := by positivity
    have hAn_pos : 0 < asymAn M r_L r_H n := by linarith
    have h1q : 1 + -asymGammaN M r_L r_H u n / (n : ℝ) = (1 - asymQ0 M r_L r_H u n) / asymAn M r_L r_H n := by
      have hAn_def : asymAn M r_L r_H n = 1 - asymQw M r_L r_H n := rfl
      unfold asymGammaN asymDelta; field_simp [hnR.ne', hAn_pos.ne']; rw [hAn_def]; ring
    have hpow : asymAn M r_L r_H n ^ n = asymAn M r_L r_H n ^ (n - 1) * asymAn M r_L r_H n := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    rw [h1q, div_pow, hpow]; unfold asymDelta
    field_simp [hnR.ne', hAn_pos.ne']
  -- Helper: for any fixed c ∈ [0, rH), (n * ∫_c^{v_hat n} (q_0 n + F v)^(n-1)) / A_n^n → exp(-u) / f(rH)
  have hLHS_lim : ∀ c₀ : ℝ, 0 ≤ c₀ → c₀ < rH →
      Tendsto (fun n : ℕ =>
        ((n : ℝ) * ∫ v in c₀..asymVhat M r_L r_H u n, (asymQ0 M r_L r_H u n + M.F v) ^ (n - 1)) /
          asymAn M r_L r_H n ^ n)
        atTop (nhds (Real.exp (-u) / M.f rH)) := by
    intro c₀ hc₀0 hc₀H
    have hG_lim : Tendsto (fun n => asymQ0 M r_L r_H u n + 1 * M.F (asymVhat M r_L r_H u n))
        atTop (nhds (1 - (1 - M.F rH) / 2)) := by
      have h1 := tendsto_const_nhds (x := (1 : ℝ)).sub hThat_lim
      refine h1.congr' ?_
      filter_upwards [hord1] with n ho
      rw [one_mul, ho.2.2.2.2.2.2.2.1]; ring
    have hP2 := br_P2_limit M ha one_pos (by linarith) hrH1 hAnH_pos (show 0 < rH - c₀ by linarith)
      hvhat_lim hG_lim
      (by
        filter_upwards [hord1, hγ.1, hvhat_lim.eventually (Ioi_mem_nhds hc₀H)] with n ho hγn hvhc
        have hc0_mem : c₀ ∈ Icc M.a 1 := ⟨by rw [ha]; exact hc₀0, by linarith⟩
        have hFc0 := (M.F_mem_Icc hc0_mem).1
        exact ⟨hc₀0, hvhc.le, by linarith [ho.2.1, ho.2.2.1, ho.2.2.2.1, ho.2.2.2.2.1], by linarith [hγn.1, hγn.2.1, hFc0]⟩)
      (by filter_upwards with n; linarith)
    have hexp_u : Tendsto (fun n : ℕ => (1 + (-u) / (n : ℝ)) ^ n) atTop (nhds (Real.exp (-u))) :=
      Real.tendsto_one_add_div_pow_exp (-u)
    have hprod := hP2.mul hexp_u
    have hval : 1 / (1 * M.f rH) * Real.exp (-u) = Real.exp (-u) / M.f rH := by ring
    rw [hval] at hprod
    refine hprod.congr' ?_
    filter_upwards [eventually_ge_atTop 2, hord1, hγ.1,
      hAn_lim.eventually (Ioi_mem_nhds (show (1 / 2 : ℝ) < 1 - (1 - M.F rH) / 2 by linarith))]
      with n hn ho hγn hAn5
    have hnR : (n : ℝ) ≠ 0 := by positivity
    have hAn_pos : 0 < asymAn M r_L r_H n := by linarith
    have hGb : asymQ0 M r_L r_H u n + 1 * M.F (asymVhat M r_L r_H u n) = 1 - asymThat M r_L r_H u n := by
      rw [one_mul, ho.2.2.2.2.2.2.2.1]; ring
    have h1T : 1 + -u / (n : ℝ) = (1 - asymThat M r_L r_H u n) / asymAn M r_L r_H n := by
      have hAn_def : asymAn M r_L r_H n = 1 - asymQw M r_L r_H n := rfl
      unfold asymThat asymDelta; field_simp [hnR, hAn_pos.ne']; rw [hAn_def]; ring
    have h1T_pos : 0 < 1 - asymThat M r_L r_H u n := by linarith [hγn.2.2.2.1]
    simp only [one_mul] at hGb ⊢
    rw [hGb, h1T, div_pow]
    field_simp [h1T_pos.ne', hAn_pos.ne']
  -- Now prove existence of v_{0,n} ∈ (0, r_H n) and v_{0,n} → rH
  have hgap_pos : ∀ᶠ n : ℕ in atTop, r_H n < asymVhat M r_L r_H u n := by
    have hlim_pos : 0 < (1 - u - br_gamma u) / M.f rH := div_pos (by linarith) hfH
    filter_upwards [eventually_ge_atTop 2, hgap_hr.eventually (Ioi_mem_nhds hlim_pos),
      hAn_lim.eventually (Ioi_mem_nhds (show (1 / 2 : ℝ) < 1 - (1 - M.F rH) / 2 by linarith))] with n hn hg hAn5
    have hδpos : 0 < asymDelta M r_L r_H n := div_pos (by linarith) (by positivity)
    have := (div_pos_iff_of_pos_right hδpos).mp hg
    linarith
  have hv0_below : ∀ c₀ : ℝ, 0 ≤ c₀ → c₀ < rH →
      ∀ᶠ n : ℕ in atTop,
        (asymVhat M r_L r_H u n - r_H n) * (1 - asymQ0 M r_L r_H u n) ^ (n - 1) <
          ∫ v in c₀..asymVhat M r_L r_H u n, (asymQ0 M r_L r_H u n + M.F v) ^ (n - 1) := by
    intro c₀ hc₀0 hc₀H
    have hdiff_lim := (hLHS_lim c₀ hc₀0 hc₀H).sub hRHS_lim
    have hpos : 0 < Real.exp (-u) / M.f rH - (1 - u - br_gamma u) * Real.exp (-br_gamma u) / M.f rH := by
      rw [← sub_div]; exact div_pos (by linarith) hfH
    filter_upwards [eventually_ge_atTop 2, hdiff_lim.eventually (Ioi_mem_nhds hpos),
      hAn_lim.eventually (Ioi_mem_nhds (show (1 / 2 : ℝ) < 1 - (1 - M.F rH) / 2 by linarith))] with n hn hgt hAn5
    have hAn_pos : 0 < asymAn M r_L r_H n := by linarith
    have hnR : (0 : ℝ) < (n : ℝ) := by positivity
    have h0 : 0 < ((n : ℝ) * ∫ v in c₀..asymVhat M r_L r_H u n, (asymQ0 M r_L r_H u n + M.F v) ^ (n - 1)) /
        asymAn M r_L r_H n ^ n -
        ((n : ℝ) * (asymVhat M r_L r_H u n - r_H n) * (1 - asymQ0 M r_L r_H u n) ^ (n - 1)) /
        asymAn M r_L r_H n ^ n := hgt
    rw [← sub_div, div_pos_iff_of_pos_right (pow_pos hAn_pos n)] at h0
    nlinarith
  have hv0_ev : ∀ᶠ n : ℕ in atTop,
      0 < asymV0 M r_L r_H u n ∧ asymV0 M r_L r_H u n < r_H n ∧
      ∫ v in asymV0 M r_L r_H u n..asymVhat M r_L r_H u n, (asymQ0 M r_L r_H u n + M.F v) ^ (n - 1) =
        (asymVhat M r_L r_H u n - r_H n) * (1 - asymQ0 M r_L r_H u n) ^ (n - 1) := by
    filter_upwards [eventually_ge_atTop 2, hord1, hγ.1, hgap_pos, hv0_below 0 le_rfl (by linarith),
      hH_lim.eventually (Ioi_mem_nhds (show (0 : ℝ) < rH by linarith))] with n hn ho hγn hgh hlt0 hrHpos
    set vh := asymVhat M r_L r_H u n
    set q0 := asymQ0 M r_L r_H u n
    set rhs := (vh - r_H n) * (1 - q0) ^ (n - 1)
    have hvh1 : vh < 1 := lt_trans ho.2.1 (lt_trans ho.2.2.1 (lt_trans ho.2.2.2.1 ho.2.2.2.2.1))
    have hFc : ContinuousOn M.F (Icc 0 vh) :=
      M.F_continuousOn.mono (Icc_subset_Icc (by rw [ha]) hvh1.le)
    have hGc : ContinuousOn (fun v => (q0 + M.F v) ^ (n - 1)) (Icc 0 vh) := (continuousOn_const.add hFc).pow _
    let ψ : ℝ → ℝ := fun x => (∫ v in 0..vh, (q0 + M.F v) ^ (n - 1)) - ∫ v in 0..x, (q0 + M.F v) ^ (n - 1)
    have hψ_eq : ∀ x ∈ Icc (0 : ℝ) vh, ψ x = ∫ v in x..vh, (q0 + M.F v) ^ (n - 1) := by
      intro x hx
      have hi1 : IntervalIntegrable (fun v => (q0 + M.F v) ^ (n - 1)) volume 0 x :=
        (hGc.mono (by rw [uIcc_of_le hx.1]; exact Icc_subset_Icc le_rfl hx.2)).intervalIntegrable
      have hi2 : IntervalIntegrable (fun v => (q0 + M.F v) ^ (n - 1)) volume x vh :=
        (hGc.mono (by rw [uIcc_of_le hx.2]; exact Icc_subset_Icc hx.1 le_rfl)).intervalIntegrable
      have hadd := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
      dsimp [ψ]; linarith
    have hψ_cont : ContinuousOn ψ (Icc 0 vh) :=
      continuousOn_const.sub (continuousOn_primitive_Icc ho.1.le hGc)
    have hψ_0 : rhs < ψ 0 := by rw [hψ_eq 0 (left_mem_Icc.mpr ho.1.le)]; exact hlt0
    have hψ_vh : ψ vh = 0 := by rw [hψ_eq vh (right_mem_Icc.mpr ho.1.le)]; exact intervalIntegral.integral_same
    have hrhs_pos : 0 < rhs := mul_pos (by linarith) (pow_pos (by linarith [hγn.2.2.1, hγn.2.2.2.1]) _)
    obtain ⟨v0, hv0_cc, hv0_eq⟩ := intermediate_value_Icc' ho.1.le hψ_cont ⟨by linarith, hψ_0.le⟩
    have hv0_oo : v0 ∈ Ioo (0 : ℝ) vh := by
      refine ⟨lt_of_le_of_ne hv0_cc.1 ?_, lt_of_le_of_ne hv0_cc.2 ?_⟩
      · intro h; rw [← h] at hv0_eq; linarith
      · intro h; rw [h, hψ_vh] at hv0_eq; linarith
    have hex : ∃ v0 ∈ Ioo (0 : ℝ) vh, ∫ v in v0..vh, (q0 + M.F v) ^ (n - 1) = rhs :=
      ⟨v0, hv0_oo, by rw [← hψ_eq v0 hv0_cc]; exact hv0_eq⟩
    have hv0_spec : asymV0 M r_L r_H u n ∈ Ioo (0 : ℝ) vh ∧
        ∫ v in asymV0 M r_L r_H u n..vh, (q0 + M.F v) ^ (n - 1) = rhs := by
      dsimp only [vh, q0, rhs] at hex ⊢
      unfold asymV0; rw [dite_eq_left hex]; exact hex.choose_spec
    -- Show asymV0 < r_H n because ∫_{r_H n}^{vh} (q0 + F v)^(n-1) < rhs
    have hrH_lt : ∫ v in r_H n..vh, (q0 + M.F v) ^ (n - 1) < rhs := by
      have hG_lt : ∀ v ∈ Icc (r_H n) vh, (q0 + M.F v) ^ (n - 1) < (1 - q0) ^ (n - 1) := by
        intro v hv
        have hFv : M.F v ≤ M.F vh :=
          M.F_strictMonoOn.monotoneOn ⟨by rw [ha]; linarith [hrHpos, hv.1], by linarith [hv.2, hvh1]⟩
            ⟨by rw [ha]; exact ho.1.le, hvh1.le⟩ hv.2
        have hle : q0 + M.F v ≤ 1 - asymThat M r_L r_H u n := by linarith [ho.2.2.2.2.2.2.2.1]
        have hlt : q0 + M.F v < 1 - q0 := by linarith [hγn.2.2.1]
        have hnn : 0 ≤ q0 + M.F v := by
          have hv_mem : v ∈ Icc M.a 1 := ⟨by rw [ha]; linarith [hrHpos, hv.1], by linarith [hv.2, hvh1]⟩
          have := (M.F_mem_Icc hv_mem).1
          linarith [hγn.1, hγn.2.1]
        exact pow_lt_pow_left₀ hlt hnn (by omega)
      have hsub : 0 < ∫ v in r_H n..vh, ((1 - q0) ^ (n - 1) - (q0 + M.F v) ^ (n - 1)) := by
        apply intervalIntegral.integral_pos hgh
          (continuousOn_const.sub (hGc.mono (Icc_subset_Icc hrHpos.le le_rfl)))
        · intro v hv; simp only [Pi.sub_apply]; linarith [hG_lt v (Ioc_subset_Icc_self hv)]
        · refine ⟨(r_H n + vh) / 2, ⟨by linarith, by linarith⟩, ?_⟩
          simp only [Pi.sub_apply]
          linarith [hG_lt ((r_H n + vh) / 2) ⟨by linarith, by linarith⟩]
      rw [intervalIntegral.integral_sub intervalIntegrable_const
        ((hGc.mono (by rw [uIcc_of_le hgh.le]; exact Icc_subset_Icc hrHpos.le le_rfl)).intervalIntegrable),
        intervalIntegral.integral_const, smul_eq_mul] at hsub
      dsimp [rhs]; linarith
    have hv0_lt_rH : asymV0 M r_L r_H u n < r_H n := by
      by_contra hge; push Not at hge
      have hi1 : IntervalIntegrable (fun v => (q0 + M.F v) ^ (n - 1)) volume (r_H n) (asymV0 M r_L r_H u n) :=
        (hGc.mono (by rw [uIcc_of_le hge]; exact Icc_subset_Icc hrHpos.le hv0_spec.1.2.le)).intervalIntegrable
      have hi2 : IntervalIntegrable (fun v => (q0 + M.F v) ^ (n - 1)) volume (asymV0 M r_L r_H u n) vh :=
        (hGc.mono (by rw [uIcc_of_le hv0_spec.1.2.le]; exact Icc_subset_Icc hv0_spec.1.1.le le_rfl)).intervalIntegrable
      have hsp := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
      have hnn : 0 ≤ ∫ v in r_H n..asymV0 M r_L r_H u n, (q0 + M.F v) ^ (n - 1) :=
        intervalIntegral.integral_nonneg hge fun v hv => pow_nonneg (by
          have hv_mem : v ∈ Icc M.a 1 := ⟨by rw [ha]; linarith [hrHpos, hv.1], by linarith [hv.2, hv0_spec.1.2, hvh1]⟩
          have := (M.F_mem_Icc hv_mem).1
          linarith [hγn.1, hγn.2.1]) _
      linarith [hv0_spec.2]
    exact ⟨hv0_spec.1.1, hv0_lt_rH, hv0_spec.2⟩
  -- Convergence v_{0,n} → rH
  have hv0_lim : Tendsto (asymV0 M r_L r_H u) atTop (nhds rH) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    let c₀ := max 0 (rH - ε / 2)
    have hc₀0 : 0 ≤ c₀ := le_max_left _ _
    have hc₀H : c₀ < rH := max_lt (by linarith) (by linarith)
    filter_upwards [eventually_ge_atTop 2, hord1, hγ.1, hgap_pos, hv0_ev, hv0_below c₀ hc₀0 hc₀H,
      hvhat_lim.eventually (Ioi_mem_nhds hc₀H), Metric.tendsto_nhds.mp hH_lim ε hε]
      with n hn ho hγn hgh hv0n hltc hvhc hHb
    have hgt : c₀ < asymV0 M r_L r_H u n := by
      by_contra hle; push Not at hle
      have hvh1 : asymVhat M r_L r_H u n < 1 := lt_trans ho.2.1 (lt_trans ho.2.2.1 (lt_trans ho.2.2.2.1 ho.2.2.2.2.1))
      have hv0_lt_vh : asymV0 M r_L r_H u n < asymVhat M r_L r_H u n := lt_trans hv0n.2.1 hgh
      have hFc : ContinuousOn M.F (Icc 0 (asymVhat M r_L r_H u n)) :=
        M.F_continuousOn.mono (Icc_subset_Icc (by rw [ha]) hvh1.le)
      have hGc : ContinuousOn (fun v => (asymQ0 M r_L r_H u n + M.F v) ^ (n - 1)) (Icc 0 (asymVhat M r_L r_H u n)) :=
        (continuousOn_const.add hFc).pow _
      have hi1 : IntervalIntegrable (fun v => (asymQ0 M r_L r_H u n + M.F v) ^ (n - 1)) volume (asymV0 M r_L r_H u n) c₀ :=
        (hGc.mono (by rw [uIcc_of_le hle]; exact Icc_subset_Icc hv0n.1.le hvhc.le)).intervalIntegrable
      have hi2 : IntervalIntegrable (fun v => (asymQ0 M r_L r_H u n + M.F v) ^ (n - 1)) volume c₀ (asymVhat M r_L r_H u n) :=
        (hGc.mono (by rw [uIcc_of_le hvhc.le]; exact Icc_subset_Icc hc₀0 le_rfl)).intervalIntegrable
      have hsp := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
      have hnn : 0 ≤ ∫ v in asymV0 M r_L r_H u n..c₀, (asymQ0 M r_L r_H u n + M.F v) ^ (n - 1) :=
        intervalIntegral.integral_nonneg hle fun v hv => pow_nonneg (by
          have hv_mem : v ∈ Icc M.a 1 := ⟨by rw [ha]; linarith [hv0n.1, hv.1], by linarith [hv.2, hvhc, hvh1]⟩
          have := (M.F_mem_Icc hv_mem).1
          linarith [hγn.1, hγn.2.1]) _
      linarith [hv0n.2.2]
    rw [Real.dist_eq] at hHb ⊢
    rw [abs_lt] at hHb ⊢
    have : rH - ε / 2 ≤ c₀ := le_max_right _ _
    constructor <;> linarith [hv0n.2.1]
  -- Eq. (21): ((1 - T_hat n)^n - (q_0 n + F(v_0 n))^n) / A_n^n → (1 - u - γ) * exp(-γ)
  have heq21 : Tendsto (fun n => ((1 - asymThat M r_L r_H u n) ^ n -
      (asymQ0 M r_L r_H u n + M.F (asymV0 M r_L r_H u n)) ^ n) / asymAn M r_L r_H n ^ n)
      atTop (nhds ((1 - u - br_gamma u) * Real.exp (-br_gamma u))) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    let L := (1 - u - br_gamma u) * Real.exp (-br_gamma u)
    have hL_pos : 0 < L := mul_pos (by linarith) (Real.exp_pos _)
    let ε₁ := min (M.f rH / 2) (ε * M.f rH / (4 * (L + 1)))
    have hε₁ : 0 < ε₁ := lt_min (by positivity) (by positivity)
    obtain ⟨δ₁, hδ₁, hfδ⟩ := Metric.continuousWithinAt_iff.mp (M.hf_cont rH ⟨by rw [ha]; linarith, hrH1.le⟩) ε₁ hε₁
    have hRHS_near := Metric.tendsto_nhds.mp hRHS_lim (min (L / (2 * M.f rH)) (ε / (4 * M.f rH)))
      (lt_min (by positivity) (by positivity))
    filter_upwards [eventually_ge_atTop 2, hord1, hγ.1, hgap_pos, hv0_ev,
      Metric.tendsto_nhds.mp hv0_lim δ₁ hδ₁, Metric.tendsto_nhds.mp hvhat_lim δ₁ hδ₁,
      hRHS_near, hAn_lim.eventually (Ioi_mem_nhds (show (1 / 2 : ℝ) < 1 - (1 - M.F rH) / 2 by linarith))]
      with n hn ho hγn hgh hv0n hv0d hvhd hRb hAn5
    set v0 := asymV0 M r_L r_H u n
    set vh := asymVhat M r_L r_H u n
    set q0 := asymQ0 M r_L r_H u n
    set An := asymAn M r_L r_H n
    have hv0_vh : v0 < vh := lt_trans hv0n.2.1 hgh
    have hvh1 : vh < 1 := lt_trans ho.2.1 (lt_trans ho.2.2.1 (lt_trans ho.2.2.2.1 ho.2.2.2.2.1))
    have hAn_pos : 0 < An := by linarith
    have hnR : (0 : ℝ) < (n : ℝ) := by positivity
    have hFc : ContinuousOn M.F (Icc v0 vh) := M.F_continuousOn.mono (Icc_subset_Icc (by rw [ha]; exact hv0n.1.le) hvh1.le)
    have hfc : ContinuousOn M.f (Icc v0 vh) := M.hf_cont.mono (Icc_subset_Icc (by rw [ha]; exact hv0n.1.le) hvh1.le)
    have hGc : ContinuousOn (fun v => q0 + M.F v) (Icc v0 vh) := continuousOn_const.add hFc
    have hFTC : (1 - asymThat M r_L r_H u n) ^ n - (q0 + M.F v0) ^ n =
        (n : ℝ) * ∫ v in v0..vh, (q0 + M.F v) ^ (n - 1) * M.f v := by
      have hd : ∀ v ∈ Ioo v0 vh, HasDerivAt (fun v => (q0 + M.F v) ^ n) ((n : ℝ) * ((q0 + M.F v) ^ (n - 1) * M.f v)) v := by
        intro v hv
        have hv' : v ∈ Ioo M.a 1 := ⟨by rw [ha]; linarith [hv0n.1, hv.1], by linarith [hv.2, hvh1]⟩
        have h := ((M.hF_deriv_open v hv').const_add q0).pow n
        convert h using 1; ring
      have hGn : ContinuousOn (fun v => (q0 + M.F v) ^ n) (Icc v0 vh) := hGc.pow n
      have hGk : ContinuousOn (fun v => (q0 + M.F v) ^ (n - 1) * M.f v) (Icc v0 vh) := (hGc.pow (n - 1)).mul hfc
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hv0_vh.le hGn hd
        ((continuousOn_const.mul hGk).mono (by rw [uIcc_of_le hv0_vh.le])).intervalIntegrable
      rw [intervalIntegral.integral_const_mul] at h
      have hGvh : q0 + M.F vh = 1 - asymThat M r_L r_H u n := by rw [ho.2.2.2.2.2.2.2.1]; ring
      rw [hGvh] at h; exact h.symm
    have hwin : ∀ v ∈ Icc v0 vh, M.f rH - ε₁ ≤ M.f v ∧ M.f v ≤ M.f rH + ε₁ := by
      intro v hv
      have hdist : dist v rH < δ₁ := by
        rw [Real.dist_eq] at hv0d hvhd ⊢; rw [abs_lt] at hv0d hvhd ⊢
        constructor <;> linarith [hv.1, hv.2]
      have h := hfδ ⟨by rw [ha]; linarith [hv0n.1, hv.1], by linarith [hv.2, hvh1]⟩ hdist
      rw [Real.dist_eq, abs_lt] at h
      exact ⟨by linarith, by linarith⟩
    have hGk : ContinuousOn (fun v => (q0 + M.F v) ^ (n - 1)) (Icc v0 vh) := hGc.pow (n - 1)
    have hGnn : ∀ v ∈ Icc v0 vh, 0 ≤ (q0 + M.F v) ^ (n - 1) := fun v hv => pow_nonneg (by
      have hv_mem : v ∈ Icc M.a 1 := ⟨by rw [ha]; linarith [hv0n.1, hv.1], by linarith [hv.2, hvh1]⟩
      have := (M.F_mem_Icc hv_mem).1
      linarith [hγn.1, hγn.2.1]) _
    have hlo : (M.f rH - ε₁) * (∫ v in v0..vh, (q0 + M.F v) ^ (n - 1)) ≤
        ∫ v in v0..vh, (q0 + M.F v) ^ (n - 1) * M.f v := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_mono_on hv0_vh.le
        ((continuousOn_const.mul hGk).mono (by rw [uIcc_of_le hv0_vh.le])).intervalIntegrable
        ((hGk.mul hfc).mono (by rw [uIcc_of_le hv0_vh.le])).intervalIntegrable
        (fun v hv => by rw [mul_comm]; exact mul_le_mul_of_nonneg_left (hwin v hv).1 (hGnn v hv))
    have hhi : ∫ v in v0..vh, (q0 + M.F v) ^ (n - 1) * M.f v ≤
        (M.f rH + ε₁) * (∫ v in v0..vh, (q0 + M.F v) ^ (n - 1)) := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_mono_on hv0_vh.le
        ((hGk.mul hfc).mono (by rw [uIcc_of_le hv0_vh.le])).intervalIntegrable
        ((continuousOn_const.mul hGk).mono (by rw [uIcc_of_le hv0_vh.le])).intervalIntegrable
        (fun v hv => by rw [mul_comm (M.f rH + ε₁)]; exact mul_le_mul_of_nonneg_left (hwin v hv).2 (hGnn v hv))
    set R := ((n : ℝ) * (vh - r_H n) * (1 - q0) ^ (n - 1)) / An ^ n
    have hscale_lo : (M.f rH - ε₁) * R ≤ ((1 - asymThat M r_L r_H u n) ^ n - (q0 + M.F v0) ^ n) / An ^ n := by
      rw [hFTC]; dsimp [R]
      rw [show (M.f rH - ε₁) * ((n : ℝ) * (vh - r_H n) * (1 - q0) ^ (n - 1) / An ^ n) =
        ((n : ℝ) * ((M.f rH - ε₁) * ((vh - r_H n) * (1 - q0) ^ (n - 1)))) / An ^ n by ring]
      rw [← hv0n.2.2]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlo hnR.le) (pow_pos hAn_pos n).le
    have hscale_hi : ((1 - asymThat M r_L r_H u n) ^ n - (q0 + M.F v0) ^ n) / An ^ n ≤ (M.f rH + ε₁) * R := by
      rw [hFTC]; dsimp [R]
      rw [show (M.f rH + ε₁) * ((n : ℝ) * (vh - r_H n) * (1 - q0) ^ (n - 1) / An ^ n) =
        ((n : ℝ) * ((M.f rH + ε₁) * ((vh - r_H n) * (1 - q0) ^ (n - 1)))) / An ^ n by ring]
      rw [← hv0n.2.2]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hhi hnR.le) (pow_pos hAn_pos n).le
    rw [Real.dist_eq] at hRb ⊢
    have hR1 : |R - L / M.f rH| < L / (2 * M.f rH) := lt_of_lt_of_le hRb (min_le_left _ _)
    have hR2 : |R - L / M.f rH| < ε / (4 * M.f rH) := lt_of_lt_of_le hRb (min_le_right _ _)
    have hhalf : L / (2 * M.f rH) = (L / M.f rH) / 2 := by ring
    have hLdiv : 0 < L / M.f rH := div_pos hL_pos hfH
    have hR_le : R ≤ 2 * (L / M.f rH) := by linarith only [(abs_lt.mp hR1).2, hhalf, hLdiv]
    have hR_nn : 0 ≤ R := by linarith only [(abs_lt.mp hR1).1, hhalf, hLdiv]
    have hε1_R : ε₁ * R ≤ ε / 2 := by
      have h1 : ε₁ ≤ ε * M.f rH / (4 * (L + 1)) := min_le_right _ _
      have hmul : ε₁ * (4 * (L + 1)) ≤ ε * M.f rH := (le_div_iff₀ (by positivity)).mp h1
      have h2 : ε₁ * (2 * L / M.f rH) ≤ ε / 2 := by
        rw [show ε₁ * (2 * L / M.f rH) = (2 * L * ε₁) / M.f rH by ring, div_le_iff₀ hfH]
        nlinarith only [hmul, hε₁, hL_pos]
      calc ε₁ * R ≤ ε₁ * (2 * (L / M.f rH)) := mul_le_mul_of_nonneg_left hR_le hε₁.le
        _ = ε₁ * (2 * L / M.f rH) := by ring
        _ ≤ ε / 2 := h2
    have hfR : |M.f rH * R - L| < ε / 4 := by
      have hid : M.f rH * R - L = M.f rH * (R - L / M.f rH) := by field_simp [hfH.ne']
      rw [hid, abs_mul, abs_of_pos hfH]
      have h := mul_lt_mul_of_pos_left hR2 hfH
      have hval : M.f rH * (ε / (4 * M.f rH)) = ε / 4 := by field_simp [hfH.ne']
      linarith only [h, hval]
    rw [abs_lt] at hfR ⊢
    constructor <;> linarith only [hscale_lo, hscale_hi, hε1_R, hfR.1, hfR.2, hε]
  refine ⟨?_, hv0_lim, hvhat_lim, hv2_lim, hva_lim, heq21⟩
  filter_upwards [hord1, hgap_pos, hv0_ev] with n ho hgh hv0n
  exact ⟨hv0n.1, hv0n.2.1, hgh, ho.2.1, ho.2.2.1, ho.2.2.2.2.2.2.2.2.1,
    ho.2.2.2.2.2.2.2.2.2, ho.2.2.2.2.1, ho.2.2.2.2.2.1, ho.2.2.2.2.2.2.1,
    ho.2.2.2.2.2.2.2.1, hv0n.2.2⟩

/-! #### Theorem 4, Part 2 (cont.): Verification of Sequential Rationality (`theorem4_deviation_sr`) -/

/-- Exact `effDist` for `asymBaseVisit M w` in a duopoly (`M.m = 2`, `M.a = 0`). -/
lemma br_effDist_asymBase (M : Market) (hm : M.m = 2) (ha : M.a = 0) {w : ℝ}
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    effDist M (asymBaseVisit M w) (seller0 M) v =
      (if v ≤ w then (1 - M.F w) / 2 + M.F v else br_Ah M v) ∧
    ∀ j : Fin M.m, j ≠ seller0 M →
      effDist M (asymBaseVisit M w) j v =
        (if v ≤ w then br_Ah M w else br_Ah M v) := by
  have htop : ∀ x ∈ Icc w 1,
      effDist M (asymBaseVisit M w) (seller0 M) x = br_Ah M x ∧
      ∀ j : Fin M.m, j ≠ seller0 M → effDist M (asymBaseVisit M w) j x = br_Ah M x := by
    intro x hx
    refine ⟨?_, fun j hj => ?_⟩
    · rw [br_effDist_sub M _ (seller0 M) (by rw [ha]; linarith [hw0, hx.1]) hx.2 le_rfl (c := 1 / 2)
        (fun u hu => by unfold asymBaseVisit; rw [br_visit_seller0]; simp [not_le.mpr (lt_of_le_of_lt hx.1 hu.1)]),
        br_effDist_one, M.hF_1]; unfold br_Ah; ring
    · rw [br_effDist_sub M _ j (by rw [ha]; linarith [hw0, hx.1]) hx.2 le_rfl (c := 1 / 2)
        (fun u hu => by unfold asymBaseVisit; rw [br_visit_rival M hm _ _ _ _ hj]; simp [not_le.mpr (lt_of_le_of_lt hx.1 hu.1)]; ring),
        br_effDist_one, M.hF_1]; unfold br_Ah; ring
  refine ⟨?_, fun j hj => ?_⟩
  · split_ifs with hvw
    · rw [br_effDist_sub M _ (seller0 M) (by rw [ha]; exact hv0) hvw hw1 (c := 1)
        (fun u hu => by unfold asymBaseVisit; rw [br_visit_seller0]; simp [hu.2.le]),
        (htop w (left_mem_Icc.mpr hw1)).1]; unfold br_Ah; ring
    · push Not at hvw; exact (htop v ⟨hvw.le, hv1⟩).1
  · split_ifs with hvw
    · rw [br_effDist_sub M _ j (by rw [ha]; exact hv0) hvw hw1 (c := 0)
        (fun u hu => by unfold asymBaseVisit; rw [br_visit_rival M hm _ _ _ _ hj]; simp [hu.2.le]),
        (htop w (left_mem_Icc.mpr hw1)).2 j hj]; ring
    · push Not at hvw; exact (htop v ⟨hvw.le, hv1⟩).2 j hj

/-- Exact `surplus` for `asymBaseVisit M w` under `(SPA rL, SPA rH)` in a duopoly. -/
lemma br_surplus_asymBase (M : Market) (hm : M.m = 2) (ha : M.a = 0) {rL rH w : ℝ}
    (hrL0 : 0 ≤ rL) (hrLH : rL < rH) (hrHw : rH < w) (hw1 : w ≤ 1)
    {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    surplus M (br_spa rL) (effDist M (asymBaseVisit M w) (seller0 M)) v =
      (if v ≤ rL then 0
       else if v ≤ w then ∫ u in rL..v, ((1 - M.F w) / 2 + M.F u) ^ (M.n - 1)
       else (∫ u in rL..w, ((1 - M.F w) / 2 + M.F u) ^ (M.n - 1)) + ∫ u in w..v, br_Ah M u ^ (M.n - 1)) ∧
    ∀ j : Fin M.m, j ≠ seller0 M →
      surplus M (br_spa rH) (effDist M (asymBaseVisit M w) j) v =
        (if v ≤ rH then 0
         else if v ≤ w then (v - rH) * br_Ah M w ^ (M.n - 1)
         else (w - rH) * br_Ah M w ^ (M.n - 1) + ∫ u in w..v, br_Ah M u ^ (M.n - 1)) := by
  have hw0 : 0 ≤ w := by linarith
  have hrH0 : 0 ≤ rH := by linarith
  have hrL1 : rL ≤ 1 := by linarith
  have hrH1 : rH ≤ 1 := by linarith
  have hFc : ContinuousOn M.F (Icc 0 1) := by rw [← ha]; exact M.F_continuousOn
  have hFLc : ContinuousOn (fun u => ((1 - M.F w) / 2 + M.F u) ^ (M.n - 1)) (Icc 0 1) :=
    (continuousOn_const.add hFc).pow _
  have hAc : ContinuousOn (fun u => br_Ah M u ^ (M.n - 1)) (Icc 0 1) := by
    unfold br_Ah; exact ((continuousOn_const.add hFc).div_const 2).pow _
  have hL0 : IntervalIntegrable (alloc M (br_spa rL) (effDist M (asymBaseVisit M w) (seller0 M))) volume 0 rL ∧
      surplus M (br_spa rL) (effDist M (asymBaseVisit M w) (seller0 M)) rL = 0 := by
    have h := br_surplus_step M (br_spa rL) (effDist M (asymBaseVisit M w) (seller0 M)) hrL0
      (br_surplus_zero _ _ _).1 (φ := fun _ => 0) continuousOn_const
      (fun u hu => by rw [br_alloc_spa M hrL0 hrL1]; simp [hu.2])
    rw [(br_surplus_zero _ _ _).2, intervalIntegral.integral_zero, add_zero] at h; exact h
  have hLw : IntervalIntegrable (alloc M (br_spa rL) (effDist M (asymBaseVisit M w) (seller0 M))) volume 0 w ∧
      surplus M (br_spa rL) (effDist M (asymBaseVisit M w) (seller0 M)) w =
        ∫ u in rL..w, ((1 - M.F w) / 2 + M.F u) ^ (M.n - 1) := by
    have h := br_surplus_step M (br_spa rL) (effDist M (asymBaseVisit M w) (seller0 M)) (by linarith : rL ≤ w)
      hL0.1 (hFLc.mono (Icc_subset_Icc hrL0 hw1))
      (fun u hu => by
        rw [br_alloc_spa M hrL0 hrL1, ite_eq_right (not_lt.mpr hu.1.le),
          (br_effDist_asymBase M hm ha hw0 hw1 (by linarith [hu.1]) (by linarith [hu.2])).1, ite_eq_left hu.2.le])
    rw [hL0.2, zero_add] at h; exact h
  refine ⟨?_, fun j hj => ?_⟩
  · split_ifs with h1 h2
    · have h := br_surplus_step M (br_spa rL) (effDist M (asymBaseVisit M w) (seller0 M)) hv0
        (br_surplus_zero _ _ _).1 (φ := fun _ => 0) continuousOn_const
        (fun u hu => by rw [br_alloc_spa M hrL0 hrL1]; simp [lt_of_lt_of_le hu.2 h1])
      rw [(br_surplus_zero _ _ _).2, intervalIntegral.integral_zero, add_zero] at h; exact h.2
    · push Not at h1
      have h := br_surplus_step M (br_spa rL) (effDist M (asymBaseVisit M w) (seller0 M)) h1.le
        hL0.1 (hFLc.mono (Icc_subset_Icc hrL0 hv1))
        (fun u hu => by
          rw [br_alloc_spa M hrL0 hrL1, ite_eq_right (not_lt.mpr hu.1.le),
            (br_effDist_asymBase M hm ha hw0 hw1 (by linarith [hu.1]) (by linarith [hu.2])).1,
            ite_eq_left (le_trans hu.2.le h2)])
      rw [hL0.2, zero_add] at h; exact h.2
    · push Not at h1 h2
      have h := br_surplus_step M (br_spa rL) (effDist M (asymBaseVisit M w) (seller0 M)) h2.le
        hLw.1 (hAc.mono (Icc_subset_Icc hw0 hv1))
        (fun u hu => by
          rw [br_alloc_spa M hrL0 hrL1, ite_eq_right (not_lt.mpr (by linarith [hu.1])),
            (br_effDist_asymBase M hm ha hw0 hw1 (by linarith [hu.1]) (by linarith [hu.2])).1,
            ite_eq_right (not_le.mpr hu.1)])
      rw [hLw.2] at h; exact h.2
  · have hH0 : IntervalIntegrable (alloc M (br_spa rH) (effDist M (asymBaseVisit M w) j)) volume 0 rH ∧
        surplus M (br_spa rH) (effDist M (asymBaseVisit M w) j) rH = 0 := by
      have h := br_surplus_step M (br_spa rH) (effDist M (asymBaseVisit M w) j) hrH0
        (br_surplus_zero _ _ _).1 (φ := fun _ => 0) continuousOn_const
        (fun u hu => by rw [br_alloc_spa M hrH0 hrH1]; simp [hu.2])
      rw [(br_surplus_zero _ _ _).2, intervalIntegral.integral_zero, add_zero] at h; exact h
    have hHw : IntervalIntegrable (alloc M (br_spa rH) (effDist M (asymBaseVisit M w) j)) volume 0 w ∧
        surplus M (br_spa rH) (effDist M (asymBaseVisit M w) j) w = (w - rH) * br_Ah M w ^ (M.n - 1) := by
      have h := br_surplus_step M (br_spa rH) (effDist M (asymBaseVisit M w) j) hrHw.le
        hH0.1 (φ := fun _ => br_Ah M w ^ (M.n - 1)) continuousOn_const
        (fun u hu => by
          rw [br_alloc_spa M hrH0 hrH1, ite_eq_right (not_lt.mpr hu.1.le),
            (br_effDist_asymBase M hm ha hw0 hw1 (by linarith [hu.1]) (by linarith [hu.2])).2 j hj,
            ite_eq_left hu.2.le])
      rw [hH0.2, zero_add, intervalIntegral.integral_const, smul_eq_mul] at h; exact h
    split_ifs with h1 h2
    · have h := br_surplus_step M (br_spa rH) (effDist M (asymBaseVisit M w) j) hv0
        (br_surplus_zero _ _ _).1 (φ := fun _ => 0) continuousOn_const
        (fun u hu => by rw [br_alloc_spa M hrH0 hrH1]; simp [lt_of_lt_of_le hu.2 h1])
      rw [(br_surplus_zero _ _ _).2, intervalIntegral.integral_zero, add_zero] at h; exact h.2
    · push Not at h1
      have h := br_surplus_step M (br_spa rH) (effDist M (asymBaseVisit M w) j) h1.le
        hH0.1 (φ := fun _ => br_Ah M w ^ (M.n - 1)) continuousOn_const
        (fun u hu => by
          rw [br_alloc_spa M hrH0 hrH1, ite_eq_right (not_lt.mpr hu.1.le),
            (br_effDist_asymBase M hm ha hw0 hw1 (by linarith [hu.1]) (by linarith [hu.2])).2 j hj,
            ite_eq_left (le_trans hu.2.le h2)])
      rw [hH0.2, zero_add, intervalIntegral.integral_const, smul_eq_mul] at h; exact h.2
    · push Not at h1 h2
      have h := br_surplus_step M (br_spa rH) (effDist M (asymBaseVisit M w) j) h2.le
        hHw.1 (hAc.mono (Icc_subset_Icc hw0 hv1))
        (fun u hu => by
          rw [br_alloc_spa M hrH0 hrH1, ite_eq_right (not_lt.mpr (by linarith [hu.1])),
            (br_effDist_asymBase M hm ha hw0 hw1 (by linarith [hu.1]) (by linarith [hu.2])).2 j hj,
            ite_eq_right (not_le.mpr hu.1)])
      rw [hHw.2] at h; exact h.2

/-- Exact `effDist` for `asymDevVisit` in `M.br_atN n`. -/
lemma br_effDist_asymDev (M : Market) (hm : M.m = 2) (ha : M.a = 0)
    {r_L r_H : ℕ → ℝ} {u : ℝ} {n : ℕ}
    (hv2_0 : 0 ≤ asymV2 M r_L r_H u n) (hv2_va : asymV2 M r_L r_H u n < asymVa M r_L r_H u n)
    (hva_1 : asymVa M r_L r_H u n ≤ 1)
    (hFva : M.F (asymVa M r_L r_H u n) = 1 - 2 * asymQa M r_L r_H u n)
    (hFv2 : M.F (asymV2 M r_L r_H u n) = 1 - (asymQa M r_L r_H u n + asymQ0 M r_L r_H u n))
    {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    let Mn := M.br_atN n
    let θ := asymDevVisit Mn r_L r_H u n
    effDist Mn θ (seller0 Mn) v =
      (if v ≤ asymV2 M r_L r_H u n then asymQ0 M r_L r_H u n + M.F v
       else if v ≤ asymVa M r_L r_H u n then 1 - asymQa M r_L r_H u n
       else br_Ah M v) ∧
    ∀ j : Fin Mn.m, j ≠ seller0 Mn →
      effDist Mn θ j v =
        (if v ≤ asymV2 M r_L r_H u n then 1 - asymQ0 M r_L r_H u n
         else if v ≤ asymVa M r_L r_H u n then asymQa M r_L r_H u n + M.F v
         else br_Ah M v) := by
  intro Mn θ
  have hMn_a : Mn.a = 0 := ha
  have hMn_m : Mn.m = 2 := hm
  have hMn_F : Mn.F = M.F := rfl
  have hMn_f : Mn.f = M.f := rfl
  set v2 := asymV2 M r_L r_H u n
  set va := asymVa M r_L r_H u n
  set qa := asymQa M r_L r_H u n
  set q0 := asymQ0 M r_L r_H u n
  have hA_va : br_Ah M va = 1 - qa := by unfold br_Ah; rw [hFva]; ring
  have hθ_eq : ∀ x, θ.θ (seller0 Mn) x = if x ≤ v2 then 1 else if x < va then 0 else 1 / 2 := by
    intro x; dsimp [θ]; unfold asymDevVisit; rw [br_visit_seller0]; rfl
  have hθj_eq : ∀ j : Fin Mn.m, j ≠ seller0 Mn → ∀ x,
      θ.θ j x = 1 - (if x ≤ v2 then 1 else if x < va then 0 else 1 / 2) := by
    intro j hj x; dsimp [θ]; unfold asymDevVisit; rw [br_visit_rival Mn hMn_m _ _ _ _ hj]; rfl
  have htop : ∀ x ∈ Icc va 1,
      effDist Mn θ (seller0 Mn) x = br_Ah M x ∧
      ∀ j : Fin Mn.m, j ≠ seller0 Mn → effDist Mn θ j x = br_Ah M x := by
    intro x hx
    refine ⟨?_, fun j hj => ?_⟩
    · rw [br_effDist_sub Mn θ (seller0 Mn) (by rw [hMn_a]; linarith [hv2_0, hv2_va, hx.1]) hx.2 le_rfl (c := 1 / 2)
        (fun t ht => by rw [hθ_eq]; simp [not_le.mpr (by linarith [hv2_va, hx.1, ht.1] : v2 < t), not_lt.mpr (le_trans hx.1 ht.1.le)]),
        br_effDist_one, Mn.hF_1]; unfold br_Ah; rw [hMn_F]; ring
    · rw [br_effDist_sub Mn θ j (by rw [hMn_a]; linarith [hv2_0, hv2_va, hx.1]) hx.2 le_rfl (c := 1 / 2)
        (fun t ht => by rw [hθj_eq j hj]; simp [not_le.mpr (by linarith [hv2_va, hx.1, ht.1] : v2 < t), not_lt.mpr (le_trans hx.1 ht.1.le)]; ring),
        br_effDist_one, Mn.hF_1]; unfold br_Ah; rw [hMn_F]; ring
  have hmid : ∀ x ∈ Icc v2 va,
      effDist Mn θ (seller0 Mn) x = 1 - qa ∧
      ∀ j : Fin Mn.m, j ≠ seller0 Mn → effDist Mn θ j x = qa + M.F x := by
    intro x hx
    refine ⟨?_, fun j hj => ?_⟩
    · rw [br_effDist_sub Mn θ (seller0 Mn) (by rw [hMn_a]; linarith [hv2_0, hx.1]) hx.2 hva_1 (c := 0)
        (fun t ht => by rw [hθ_eq]; simp [not_le.mpr (lt_of_le_of_lt hx.1 ht.1), ht.2]),
        (htop va (left_mem_Icc.mpr hva_1)).1, hA_va]; ring
    · rw [br_effDist_sub Mn θ j (by rw [hMn_a]; linarith [hv2_0, hx.1]) hx.2 hva_1 (c := 1)
        (fun t ht => by rw [hθj_eq j hj]; simp [not_le.mpr (lt_of_le_of_lt hx.1 ht.1), ht.2]),
        (htop va (left_mem_Icc.mpr hva_1)).2 j hj, hA_va, hMn_F, hFva]; ring
  refine ⟨?_, fun j hj => ?_⟩
  · split_ifs with h1 h2
    · rw [br_effDist_sub Mn θ (seller0 Mn) (by rw [hMn_a]; exact hv0) h1 (le_trans hv2_va.le hva_1) (c := 1)
        (fun t ht => by rw [hθ_eq]; simp [ht.2.le]),
        (hmid v2 (left_mem_Icc.mpr hv2_va.le)).1, hMn_F, hFv2]; ring
    · push Not at h1; exact (hmid v ⟨h1.le, h2⟩).1
    · push Not at h1 h2; exact (htop v ⟨h2.le, hv1⟩).1
  · split_ifs with h1 h2
    · rw [br_effDist_sub Mn θ j (by rw [hMn_a]; exact hv0) h1 (le_trans hv2_va.le hva_1) (c := 0)
        (fun t ht => by rw [hθj_eq j hj]; simp [ht.2.le]),
        (hmid v2 (left_mem_Icc.mpr hv2_va.le)).2 j hj, hFv2]; ring
    · push Not at h1; exact (hmid v ⟨h1.le, h2⟩).2 j hj
    · push Not at h1 h2; exact (htop v ⟨h2.le, hv1⟩).2 j hj

/-- Exact `surplus` for `asymDevVisit` under `(asymDevMech, SPA (r_H n))` in `M.br_atN n`. -/
lemma br_surplus_asymDev (M : Market) (hm : M.m = 2) (ha : M.a = 0)
    {r_L r_H : ℕ → ℝ} {u : ℝ} {n : ℕ} (hn : 2 ≤ n)
    (hv0_0 : 0 < asymV0 M r_L r_H u n) (hv0_rH : asymV0 M r_L r_H u n < r_H n)
    (hrH_vh : r_H n < asymVhat M r_L r_H u n) (hvh_v2 : asymVhat M r_L r_H u n < asymV2 M r_L r_H u n)
    (hv2_β : asymV2 M r_L r_H u n < asymBeta M r_L r_H u n)
    (hβ_va : asymBeta M r_L r_H u n < asymVa M r_L r_H u n)
    (hva_1 : asymVa M r_L r_H u n < 1)
    (hFva : M.F (asymVa M r_L r_H u n) = 1 - 2 * asymQa M r_L r_H u n)
    (hFv2 : M.F (asymV2 M r_L r_H u n) = 1 - (asymQa M r_L r_H u n + asymQ0 M r_L r_H u n))
    (hFvh : M.F (asymVhat M r_L r_H u n) = 1 - (asymThat M r_L r_H u n + asymQ0 M r_L r_H u n))
    (hbarx : (1 - asymQ0 M r_L r_H u n) ^ (n - 1) = asymBarX M r_L r_H u n)
    (heq20 : ∫ v in asymV0 M r_L r_H u n..asymVhat M r_L r_H u n, (asymQ0 M r_L r_H u n + M.F v) ^ (n - 1) =
      (asymVhat M r_L r_H u n - r_H n) * (1 - asymQ0 M r_L r_H u n) ^ (n - 1))
    {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    let Mn := M.br_atN n
    let θ := asymDevVisit Mn r_L r_H u n
    let mech := asymDevMech M r_L r_H u n
    let v0 := asymV0 M r_L r_H u n
    let vh := asymVhat M r_L r_H u n
    let v2 := asymV2 M r_L r_H u n
    let β := asymBeta M r_L r_H u n
    let va := asymVa M r_L r_H u n
    let qa := asymQa M r_L r_H u n
    let q0 := asymQ0 M r_L r_H u n
    let barx := asymBarX M r_L r_H u n
    surplus Mn mech (effDist Mn θ (seller0 Mn)) v =
      (if v ≤ v0 then 0
       else if v ≤ vh then ∫ t in v0..v, (q0 + M.F t) ^ (n - 1)
       else if v ≤ β then (v - r_H n) * barx
       else if v ≤ va then (β - r_H n) * barx + (v - β) * (1 - qa) ^ (n - 1)
       else (β - r_H n) * barx + (va - β) * (1 - qa) ^ (n - 1) + ∫ t in va..v, br_Ah M t ^ (n - 1)) ∧
    ∀ j : Fin Mn.m, j ≠ seller0 Mn →
      surplus Mn (br_spa (r_H n)) (effDist Mn θ j) v =
        (if v ≤ r_H n then 0
         else if v ≤ v2 then (v - r_H n) * barx
         else if v ≤ va then (v2 - r_H n) * barx + ∫ t in v2..v, (qa + M.F t) ^ (n - 1)
         else (v2 - r_H n) * barx + (∫ t in v2..va, (qa + M.F t) ^ (n - 1)) + ∫ t in va..v, br_Ah M t ^ (n - 1)) := by
  intro Mn θ mech v0 vh v2 β va qa q0 barx
  have hMn_n : Mn.n = n := M.br_atN_n hn
  have hpool : 0 ≤ v0 ∧ v0 ≤ vh ∧ vh < β ∧ β ≤ 1 :=
    ⟨hv0_0.le, by linarith, lt_trans hvh_v2 hv2_β, le_trans hβ_va.le hva_1.le⟩
  have hF0_vh : effDist Mn θ (seller0 Mn) vh = 1 - asymThat M r_L r_H u n := by
    rw [(br_effDist_asymDev M hm ha (by linarith) (lt_trans hv2_β hβ_va) hva_1.le hFva hFv2
      (by linarith) (by linarith)).1, ite_eq_left hvh_v2.le, hFvh]; ring
  have hF0_β : effDist Mn θ (seller0 Mn) β = 1 - qa := by
    rw [(br_effDist_asymDev M hm ha (by linarith) (lt_trans hv2_β hβ_va) hva_1.le hFva hFv2
      (by linarith) (by linarith)).1, ite_eq_right (not_le.mpr hv2_β), ite_eq_left hβ_va.le]
  have hpool_val : poolAvg Mn.n (effDist Mn θ (seller0 Mn) vh) (effDist Mn θ (seller0 Mn) β) = barx := by
    rw [hMn_n, hF0_vh, hF0_β]; rfl
  have hFc : ContinuousOn M.F (Icc 0 1) := by rw [← ha]; exact M.F_continuousOn
  have hFLc : ContinuousOn (fun t => (q0 + M.F t) ^ (n - 1)) (Icc 0 1) := (continuousOn_const.add hFc).pow _
  have hFHc : ContinuousOn (fun t => (qa + M.F t) ^ (n - 1)) (Icc 0 1) := (continuousOn_const.add hFc).pow _
  have hAc : ContinuousOn (fun t => br_Ah M t ^ (n - 1)) (Icc 0 1) := by
    unfold br_Ah; exact ((continuousOn_const.add hFc).div_const 2).pow _
  have hallL : ∀ t ∈ Icc (0 : ℝ) 1, alloc Mn mech (effDist Mn θ (seller0 Mn)) t =
      if t < v0 then 0
      else if vh < t ∧ t < β then barx
      else (effDist Mn θ (seller0 Mn) t) ^ (n - 1) := fun t _ => by
    dsimp [mech]; unfold asymDevMech
    rw [br_alloc_onePool Mn hpool, hpool_val, hMn_n]
  -- Step by step for seller 0
  have h0_v0 : IntervalIntegrable (alloc Mn mech (effDist Mn θ (seller0 Mn))) volume 0 v0 ∧
      surplus Mn mech (effDist Mn θ (seller0 Mn)) v0 = 0 := by
    have h := br_surplus_step Mn mech (effDist Mn θ (seller0 Mn)) hv0_0.le (br_surplus_zero _ _ _).1
      (φ := fun _ => 0) continuousOn_const
      (fun t ht => by rw [hallL t ⟨ht.1.le, by linarith [ht.2]⟩, ite_eq_left ht.2])
    rw [(br_surplus_zero _ _ _).2, intervalIntegral.integral_zero, add_zero] at h; exact h
  have h0_vh : IntervalIntegrable (alloc Mn mech (effDist Mn θ (seller0 Mn))) volume 0 vh ∧
      surplus Mn mech (effDist Mn θ (seller0 Mn)) vh = (vh - r_H n) * barx := by
    have h := br_surplus_step Mn mech (effDist Mn θ (seller0 Mn)) (by linarith : v0 ≤ vh) h0_v0.1
      (hFLc.mono (Icc_subset_Icc hv0_0.le (by linarith)))
      (fun t ht => by
        rw [hallL t ⟨by linarith [ht.1], by linarith [ht.2]⟩, ite_eq_right (not_lt.mpr ht.1.le),
          ite_eq_right (fun h' => by linarith [h'.1, ht.2]),
          (br_effDist_asymDev M hm ha (by linarith) (lt_trans hv2_β hβ_va) hva_1.le hFva hFv2
            (by linarith [ht.1]) (by linarith [ht.2])).1, ite_eq_left (by linarith [ht.2])])
    rw [h0_v0.2, zero_add, heq20, hbarx] at h; exact h
  have h0_β : IntervalIntegrable (alloc Mn mech (effDist Mn θ (seller0 Mn))) volume 0 β ∧
      surplus Mn mech (effDist Mn θ (seller0 Mn)) β = (β - r_H n) * barx := by
    have h := br_surplus_step Mn mech (effDist Mn θ (seller0 Mn)) (lt_trans hvh_v2 hv2_β).le h0_vh.1
      (φ := fun _ => barx) continuousOn_const
      (fun t ht => by
        rw [hallL t ⟨by linarith [ht.1], by linarith [ht.2]⟩,
          ite_eq_right (not_lt.mpr (by linarith [ht.1])), ite_eq_left ⟨ht.1, ht.2⟩])
    rw [h0_vh.2, intervalIntegral.integral_const, smul_eq_mul] at h
    exact ⟨h.1, by linarith [h.2]⟩
  have h0_va : IntervalIntegrable (alloc Mn mech (effDist Mn θ (seller0 Mn))) volume 0 va ∧
      surplus Mn mech (effDist Mn θ (seller0 Mn)) va = (β - r_H n) * barx + (va - β) * (1 - qa) ^ (n - 1) := by
    have h := br_surplus_step Mn mech (effDist Mn θ (seller0 Mn)) hβ_va.le h0_β.1
      (φ := fun _ => (1 - qa) ^ (n - 1)) continuousOn_const
      (fun t ht => by
        rw [hallL t ⟨by linarith [ht.1], by linarith [ht.2]⟩,
          ite_eq_right (not_lt.mpr (by linarith [ht.1])), ite_eq_right (fun h' => by linarith [h'.2, ht.1]),
          (br_effDist_asymDev M hm ha (by linarith) (lt_trans hv2_β hβ_va) hva_1.le hFva hFv2
            (by linarith [ht.1]) (by linarith [ht.2])).1,
          ite_eq_right (not_le.mpr (lt_trans hv2_β ht.1)), ite_eq_left ht.2.le])
    rw [h0_β.2, intervalIntegral.integral_const, smul_eq_mul] at h; exact h
  refine ⟨?_, fun j hj => ?_⟩
  · split_ifs with h1 h2 h3 h4
    · have h := br_surplus_step Mn mech (effDist Mn θ (seller0 Mn)) hv0 (br_surplus_zero _ _ _).1
        (φ := fun _ => 0) continuousOn_const
        (fun t ht => by rw [hallL t ⟨ht.1.le, by linarith [ht.2]⟩]; simp [lt_of_lt_of_le ht.2 h1])
      rw [(br_surplus_zero _ _ _).2, intervalIntegral.integral_zero, add_zero] at h; exact h.2
    · push Not at h1
      have h := br_surplus_step Mn mech (effDist Mn θ (seller0 Mn)) h1.le h0_v0.1
        (hFLc.mono (Icc_subset_Icc hv0_0.le hv1))
        (fun t ht => by
          rw [hallL t ⟨by linarith [ht.1], by linarith [ht.2]⟩, ite_eq_right (not_lt.mpr ht.1.le),
            ite_eq_right (fun h' => by linarith [h'.1, ht.2, h2]),
            (br_effDist_asymDev M hm ha (by linarith) (lt_trans hv2_β hβ_va) hva_1.le hFva hFv2
              (by linarith [ht.1]) (by linarith [ht.2])).1, ite_eq_left (by linarith [ht.2, h2])])
      rw [h0_v0.2, zero_add] at h; exact h.2
    · push Not at h1 h2
      have h := br_surplus_step Mn mech (effDist Mn θ (seller0 Mn)) h2.le h0_vh.1
        (φ := fun _ => barx) continuousOn_const
        (fun t ht => by
          rw [hallL t ⟨by linarith [ht.1], by linarith [ht.2]⟩,
            ite_eq_right (not_lt.mpr (by linarith [ht.1])), ite_eq_left ⟨ht.1, lt_of_lt_of_le ht.2 h3⟩])
      rw [h0_vh.2, intervalIntegral.integral_const, smul_eq_mul] at h; linarith [h.2]
    · push Not at h1 h2 h3
      have h := br_surplus_step Mn mech (effDist Mn θ (seller0 Mn)) h3.le h0_β.1
        (φ := fun _ => (1 - qa) ^ (n - 1)) continuousOn_const
        (fun t ht => by
          rw [hallL t ⟨by linarith [ht.1], by linarith [ht.2]⟩,
            ite_eq_right (not_lt.mpr (by linarith [ht.1])), ite_eq_right (fun h' => by linarith [h'.2, ht.1]),
            (br_effDist_asymDev M hm ha (by linarith) (lt_trans hv2_β hβ_va) hva_1.le hFva hFv2
              (by linarith [ht.1]) (by linarith [ht.2])).1,
            ite_eq_right (not_le.mpr (lt_trans hv2_β ht.1)), ite_eq_left (le_trans ht.2.le h4)])
      rw [h0_β.2, intervalIntegral.integral_const, smul_eq_mul] at h; exact h.2
    · push Not at h1 h2 h3 h4
      have h := br_surplus_step Mn mech (effDist Mn θ (seller0 Mn)) h4.le h0_va.1
        (hAc.mono (Icc_subset_Icc (by linarith) hv1))
        (fun t ht => by
          rw [hallL t ⟨by linarith [ht.1], by linarith [ht.2]⟩,
            ite_eq_right (not_lt.mpr (by linarith [ht.1])), ite_eq_right (fun h' => by linarith [h'.2, ht.1]),
            (br_effDist_asymDev M hm ha (by linarith) (lt_trans hv2_β hβ_va) hva_1.le hFva hFv2
              (by linarith [ht.1]) (by linarith [ht.2])).1,
            ite_eq_right (not_le.mpr (by linarith [ht.1])), ite_eq_right (not_le.mpr ht.1)])
      rw [h0_va.2] at h; exact h.2
  · have hrH0 : 0 ≤ r_H n := by linarith
    have hrH1 : r_H n ≤ 1 := by linarith
    have hH_rH : IntervalIntegrable (alloc Mn (br_spa (r_H n)) (effDist Mn θ j)) volume 0 (r_H n) ∧
        surplus Mn (br_spa (r_H n)) (effDist Mn θ j) (r_H n) = 0 := by
      have h := br_surplus_step Mn (br_spa (r_H n)) (effDist Mn θ j) hrH0 (br_surplus_zero _ _ _).1
        (φ := fun _ => 0) continuousOn_const
        (fun t ht => by rw [br_alloc_spa Mn hrH0 hrH1]; simp [ht.2])
      rw [(br_surplus_zero _ _ _).2, intervalIntegral.integral_zero, add_zero] at h; exact h
    have hH_v2 : IntervalIntegrable (alloc Mn (br_spa (r_H n)) (effDist Mn θ j)) volume 0 v2 ∧
        surplus Mn (br_spa (r_H n)) (effDist Mn θ j) v2 = (v2 - r_H n) * barx := by
      have h := br_surplus_step Mn (br_spa (r_H n)) (effDist Mn θ j) (lt_trans hrH_vh hvh_v2).le hH_rH.1
        (φ := fun _ => barx) continuousOn_const
        (fun t ht => by
          rw [br_alloc_spa Mn hrH0 hrH1, ite_eq_right (not_lt.mpr ht.1.le), hMn_n,
            (br_effDist_asymDev M hm ha (by linarith) (lt_trans hv2_β hβ_va) hva_1.le hFva hFv2
              (by linarith [ht.1]) (by linarith [ht.2])).2 j hj, ite_eq_left ht.2.le, hbarx])
      rw [hH_rH.2, zero_add, intervalIntegral.integral_const, smul_eq_mul] at h; exact h
    have hH_va : IntervalIntegrable (alloc Mn (br_spa (r_H n)) (effDist Mn θ j)) volume 0 va ∧
        surplus Mn (br_spa (r_H n)) (effDist Mn θ j) va =
          (v2 - r_H n) * barx + ∫ t in v2..va, (qa + M.F t) ^ (n - 1) := by
      have h := br_surplus_step Mn (br_spa (r_H n)) (effDist Mn θ j) (lt_trans hv2_β hβ_va).le hH_v2.1
        (hFHc.mono (Icc_subset_Icc (by linarith) hva_1.le))
        (fun t ht => by
          rw [br_alloc_spa Mn hrH0 hrH1, ite_eq_right (not_lt.mpr (by linarith [ht.1])), hMn_n,
            (br_effDist_asymDev M hm ha (by linarith) (lt_trans hv2_β hβ_va) hva_1.le hFva hFv2
              (by linarith [ht.1]) (by linarith [ht.2])).2 j hj,
            ite_eq_right (not_le.mpr ht.1), ite_eq_left ht.2.le])
      rw [hH_v2.2] at h; exact h
    split_ifs with h1 h2 h3
    · have h := br_surplus_step Mn (br_spa (r_H n)) (effDist Mn θ j) hv0 (br_surplus_zero _ _ _).1
        (φ := fun _ => 0) continuousOn_const
        (fun t ht => by rw [br_alloc_spa Mn hrH0 hrH1]; simp [lt_of_lt_of_le ht.2 h1])
      rw [(br_surplus_zero _ _ _).2, intervalIntegral.integral_zero, add_zero] at h; exact h.2
    · push Not at h1
      have h := br_surplus_step Mn (br_spa (r_H n)) (effDist Mn θ j) h1.le hH_rH.1
        (φ := fun _ => barx) continuousOn_const
        (fun t ht => by
          rw [br_alloc_spa Mn hrH0 hrH1, ite_eq_right (not_lt.mpr ht.1.le), hMn_n,
            (br_effDist_asymDev M hm ha (by linarith) (lt_trans hv2_β hβ_va) hva_1.le hFva hFv2
              (by linarith [ht.1]) (by linarith [ht.2])).2 j hj,
            ite_eq_left (le_trans ht.2.le h2), hbarx])
      rw [hH_rH.2, zero_add, intervalIntegral.integral_const, smul_eq_mul] at h; exact h.2
    · push Not at h1 h2
      have h := br_surplus_step Mn (br_spa (r_H n)) (effDist Mn θ j) h2.le hH_v2.1
        (hFHc.mono (Icc_subset_Icc (by linarith) hv1))
        (fun t ht => by
          rw [br_alloc_spa Mn hrH0 hrH1, ite_eq_right (not_lt.mpr (by linarith [ht.1])), hMn_n,
            (br_effDist_asymDev M hm ha (by linarith) (lt_trans hv2_β hβ_va) hva_1.le hFva hFv2
              (by linarith [ht.1]) (by linarith [ht.2])).2 j hj,
            ite_eq_right (not_le.mpr ht.1), ite_eq_left (le_trans ht.2.le h3)])
      rw [hH_v2.2] at h; exact h.2
    · push Not at h1 h2 h3
      have h := br_surplus_step Mn (br_spa (r_H n)) (effDist Mn θ j) h3.le hH_va.1
        (hAc.mono (Icc_subset_Icc (by linarith) hv1))
        (fun t ht => by
          rw [br_alloc_spa Mn hrH0 hrH1, ite_eq_right (not_lt.mpr (by linarith [ht.1])), hMn_n,
            (br_effDist_asymDev M hm ha (by linarith) (lt_trans hv2_β hβ_va) hva_1.le hFva hFv2
              (by linarith [ht.1]) (by linarith [ht.2])).2 j hj,
            ite_eq_right (not_le.mpr (by linarith [ht.1])), ite_eq_right (not_le.mpr ht.1)])
      rw [hH_va.2] at h; exact h.2

/-- **Theorem 4 (Part 2 — Sequential Rationality of Baseline and Deviation)**:
For `m = 2`, `a = 0`, `r_L n → rL < rH ← r_H n`, and any feasible `u > 0`
(`u + γ < 1` and `(1 - u - γ) e^{-γ} < e^{-u}`), for all sufficiently large `n`:
1. The baseline visit strategy `asymBaseVisit` is SR for `(SPA(r_L n), SPA(r_H n))`.
2. The deviation visit strategy `asymDevVisit` is SR for `(asymDevMech, SPA(r_H n))`. -/
theorem theorem4_deviation_sr (M : Market) (hm : M.m = 2) (ha : M.a = 0)
    {r_L r_H : ℕ → ℝ} {rL rH u : ℝ} (hrL0 : 0 ≤ rL) (hrLH : rL < rH) (hrH1 : rH < 1)
    (hL_lim : Tendsto r_L atTop (nhds rL)) (hH_lim : Tendsto r_H atTop (nhds rH))
    (hL_nn : ∀ᶠ n in atTop, 0 ≤ r_L n)
    (hu : 0 < u) (huγ : u + br_gamma u < 1)
    (hfeas : (1 - u - br_gamma u) * Real.exp (-br_gamma u) < Real.exp (-u)) :
    ∀ᶠ n : ℕ in atTop,
      let Mn := M.br_atN n
      IsSR Mn (fun j => if j = seller0 Mn then br_spa (r_L n) else br_spa (r_H n))
        (asymBaseVisit Mn (asymW M r_L r_H n)) ∧
      IsSR Mn (fun j => if j = seller0 Mn then asymDevMech M r_L r_H u n else br_spa (r_H n))
        (asymDevVisit Mn r_L r_H u n) := by
  have hcut := theorem4_cutoff_asymptotics M hm ha hrL0 hrLH hrH1 hL_lim hH_lim hL_nn
  have hγ := br_gammaN_tendsto M hm ha hrL0 hrLH hrH1 hL_lim hH_lim hL_nn hu
  have hdev := br_dev_coords_asym M hm ha hrL0 hrLH hrH1 hL_lim hH_lim hL_nn hu huγ hfeas
  have hord_r : ∀ᶠ n : ℕ in atTop, r_L n < r_H n := by
    have hd := (hH_lim.sub hL_lim).eventually (Ioi_mem_nhds (sub_pos.mpr hrLH))
    filter_upwards [hd] with n hn; linarith
  filter_upwards [eventually_ge_atTop 2, hL_nn, hord_r, hcut.1, hγ.1, hdev.1]
    with n hn hLn hrLHn hcn hγn hdn
  intro Mn
  have hMn_m : Mn.m = 2 := hm
  have hMn_a : Mn.a = 0 := ha
  have hMn_n : Mn.n = n := M.br_atN_n hn
  have hFc : ContinuousOn M.F (Icc 0 1) := by rw [← ha]; exact M.F_continuousOn
  have hriv_eq : ∀ j k : Fin Mn.m, j ≠ seller0 Mn → k ≠ seller0 Mn → j = k := by
    intro j k hj hk
    have hj0 : j.1 ≠ 0 := fun h => hj (Fin.ext h)
    have hk0 : k.1 ≠ 0 := fun h => hk (Fin.ext h)
    have hjm : j.1 < 2 := by rw [← hMn_m]; exact j.2
    have hkm : k.1 < 2 := by rw [← hMn_m]; exact k.2
    exact Fin.ext (by omega)
  constructor
  · -- Part 1: Baseline SR
    set w := asymW M r_L r_H n
    set θb := asymBaseVisit Mn w
    have hFLc : ContinuousOn (fun t => ((1 - M.F w) / 2 + M.F t) ^ (n - 1)) (Icc 0 1) :=
      (continuousOn_const.add hFc).pow _
    have hbal_w : ∫ t in r_L n..w, ((1 - M.F w) / 2 + M.F t) ^ (n - 1) = (w - r_H n) * br_Ah M w ^ (n - 1) := by
      have := hcn.2.2; rw [br_A_eq M hm] at this; exact this
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv j k hjpos
    have hv01 : 0 ≤ v ∧ v ≤ 1 := by rw [hMn_a] at hv; exact hv
    have hs := br_surplus_asymBase Mn hMn_m hMn_a hLn hrLHn hcn.1.1 hcn.1.2.le hv01.1 hv01.2
    have hMn_F : Mn.F = M.F := rfl
    have hMn_Ah : br_Ah Mn = br_Ah M := rfl
    have hFL_nn : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ (1 - M.F w) / 2 + M.F t := fun t ht => by
      have h1 := (M.F_mem_Icc (by rw [ha]; exact ht)).1
      have h2 := (M.F_mem_Icc ⟨by rw [ha]; linarith [hLn, hrLHn, hcn.1.1], hcn.1.2.le⟩).2
      linarith
    have hFL_le : ∀ t ∈ Icc (0 : ℝ) w, (1 - M.F w) / 2 + M.F t ≤ br_Ah M w := fun t ht => by
      have h1 := M.F_strictMonoOn.monotoneOn ⟨by rw [ha]; exact ht.1, le_trans ht.2 hcn.1.2.le⟩
        ⟨by rw [ha]; linarith [hLn, hrLHn, hcn.1.1], hcn.1.2.le⟩ ht.2
      unfold br_Ah; linarith
    by_cases hj0 : j = seller0 Mn
    · subst hj0
      by_cases hk0 : k = seller0 Mn
      · subst hk0; exact le_rfl
      · simp only [↓reduceIte, hk0]
        rw [hs.1, hs.2 k hk0, hMn_n, hMn_F, hMn_Ah]
        by_cases h1 : v ≤ r_L n
        · simp only [h1, show v ≤ r_H n by linarith, ↓reduceIte]; exact le_rfl
        · push Not at h1
          by_cases h2 : v ≤ w
          · by_cases hr : v ≤ r_H n
            · simp only [not_le.mpr h1, h2, hr, ↓reduceIte]
              exact intervalIntegral.integral_nonneg h1.le fun t ht =>
                pow_nonneg (hFL_nn t ⟨by linarith [ht.1], by linarith [ht.2]⟩) _
            · push Not at hr
              simp only [not_le.mpr h1, h2, not_le.mpr hr, ↓reduceIte]
              have hi1 : IntervalIntegrable (fun t => ((1 - M.F w) / 2 + M.F t) ^ (n - 1)) volume (r_L n) v :=
                (hFLc.mono (by rw [uIcc_of_le h1.le]; exact Icc_subset_Icc hLn hv01.2)).intervalIntegrable
              have hi2 : IntervalIntegrable (fun t => ((1 - M.F w) / 2 + M.F t) ^ (n - 1)) volume v w :=
                (hFLc.mono (by rw [uIcc_of_le h2]; exact Icc_subset_Icc hv01.1 hcn.1.2.le)).intervalIntegrable
              have hsp := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
              have hle : ∫ t in v..w, ((1 - M.F w) / 2 + M.F t) ^ (n - 1) ≤ (w - v) * br_Ah M w ^ (n - 1) := by
                have hc' : ∫ _ in v..w, br_Ah M w ^ (n - 1) = (w - v) * br_Ah M w ^ (n - 1) := by
                  rw [intervalIntegral.integral_const, smul_eq_mul]
                rw [← hc']
                exact intervalIntegral.integral_mono_on h2 hi2 intervalIntegrable_const fun t ht =>
                  pow_le_pow_left₀ (hFL_nn t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
                    (hFL_le t ⟨by linarith [ht.1], ht.2⟩) _
              linarith only [hsp, hbal_w, hle]
          · push Not at h2
            simp only [not_le.mpr h1, not_le.mpr h2, not_le.mpr (lt_trans hcn.1.1 h2), ↓reduceIte]
            linarith only [hbal_w]
    · by_cases hk0 : k = seller0 Mn
      · subst hk0
        simp only [↓reduceIte, hj0]
        have hvw : w < v := by
          by_contra hle; push Not at hle
          have h0 : θb.θ j v = 0 := by
            dsimp [θb]; unfold asymBaseVisit; rw [br_visit_rival Mn hMn_m _ _ _ _ hj0]; simp [hle]
          linarith
        rw [hs.1, hs.2 j hj0, hMn_n, hMn_F, hMn_Ah]
        simp only [not_le.mpr (by linarith : r_L n < v), not_le.mpr (by linarith : r_H n < v),
          not_le.mpr hvw, ↓reduceIte]
        linarith only [hbal_w]
      · rw [hriv_eq j k hj0 hk0]
  · -- Part 2: Deviation SR
    set v0 := asymV0 M r_L r_H u n
    set vh := asymVhat M r_L r_H u n
    set v2 := asymV2 M r_L r_H u n
    set β := asymBeta M r_L r_H u n
    set va := asymVa M r_L r_H u n
    set qa := asymQa M r_L r_H u n
    set q0 := asymQ0 M r_L r_H u n
    set barx := asymBarX M r_L r_H u n
    set θd := asymDevVisit Mn r_L r_H u n
    have hFLc : ContinuousOn (fun t => (q0 + M.F t) ^ (n - 1)) (Icc 0 1) := (continuousOn_const.add hFc).pow _
    have hFHc : ContinuousOn (fun t => (qa + M.F t) ^ (n - 1)) (Icc 0 1) := (continuousOn_const.add hFc).pow _
    have hvh_v2 : vh < v2 := lt_trans hdn.2.2.2.1 hdn.2.2.2.2.1
    have hv2_va : v2 < va := lt_trans hdn.2.2.2.2.2.1 hdn.2.2.2.2.2.2.1
    have hbal_β : (β - r_H n) * barx + (va - β) * (1 - qa) ^ (n - 1) =
        (v2 - r_H n) * barx + ∫ t in v2..va, (qa + M.F t) ^ (n - 1) := by
      have hden : (1 - qa) ^ (n - 1) - barx ≠ 0 := by
        rw [← hγn.2.2.2.2.1]
        have := pow_lt_pow_left₀ (show 1 - q0 < 1 - qa by linarith [hγn.2.1]) (by linarith [hγn.2.2.1, hγn.2.2.2.1]) (by omega : n - 1 ≠ 0)
        linarith
      have h1 : (va - β) * ((1 - qa) ^ (n - 1) - barx) =
          ∫ t in v2..va, ((qa + M.F t) ^ (n - 1) - barx) := by
        have hβd : va - β = (∫ t in v2..va, ((qa + M.F t) ^ (n - 1) - barx)) / ((1 - qa) ^ (n - 1) - barx) := by
          dsimp [β, va, v2, qa, barx]; unfold asymBeta; ring
        rw [hβd, div_mul_cancel₀ _ hden]
      rw [intervalIntegral.integral_sub
        ((hFHc.mono (by rw [uIcc_of_le hv2_va.le]; exact Icc_subset_Icc (by linarith [hdn.1, hdn.2.1, hdn.2.2.1, hvh_v2]) hdn.2.2.2.2.2.2.2.1.le)).intervalIntegrable)
        intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul] at h1
      linarith only [h1]
    have hFL_nn : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ q0 + M.F t := fun t ht => by
      have := (M.F_mem_Icc (by rw [ha]; exact ht)).1; linarith [hγn.1, hγn.2.1]
    have hFL_le : ∀ t ∈ Icc (0 : ℝ) vh, (q0 + M.F t) ^ (n - 1) ≤ barx := fun t ht => by
      rw [← hγn.2.2.2.2.1]
      have hFt := M.F_strictMonoOn.monotoneOn ⟨by rw [ha]; exact ht.1, by linarith [ht.2, hvh_v2, hv2_va, hdn.2.2.2.2.2.2.2.1]⟩
        ⟨by rw [ha]; linarith [hdn.1, hdn.2.1, hdn.2.2.1], by linarith [hvh_v2, hv2_va, hdn.2.2.2.2.2.2.2.1]⟩ ht.2
      have hle : q0 + M.F t ≤ 1 - q0 := by linarith [hdn.2.2.2.2.2.2.2.2.2.2.1, hγn.2.2.1]
      exact pow_le_pow_left₀ (hFL_nn t ⟨ht.1, by linarith [ht.2, hvh_v2, hv2_va, hdn.2.2.2.2.2.2.2.1]⟩) hle _
    have hFH_range : ∀ t ∈ Icc v2 va, barx ≤ (qa + M.F t) ^ (n - 1) ∧ (qa + M.F t) ^ (n - 1) ≤ (1 - qa) ^ (n - 1) := by
      intro t ht
      have ht_mem : t ∈ Icc M.a 1 := ⟨by rw [ha]; linarith [hdn.1, hdn.2.1, hdn.2.2.1, hvh_v2, ht.1], le_trans ht.2 hdn.2.2.2.2.2.2.2.1.le⟩
      have h1 := M.F_strictMonoOn.monotoneOn ⟨by rw [ha]; linarith [hdn.1, hdn.2.1, hdn.2.2.1, hvh_v2], le_trans hv2_va.le hdn.2.2.2.2.2.2.2.1.le⟩ ht_mem ht.1
      have h2 := M.F_strictMonoOn.monotoneOn ht_mem ⟨by rw [ha]; linarith [hdn.1, hdn.2.1, hdn.2.2.1, hvh_v2, hv2_va], hdn.2.2.2.2.2.2.2.1.le⟩ ht.2
      have hlo : 1 - q0 ≤ qa + M.F t := by linarith [hdn.2.2.2.2.2.2.2.2.2.1]
      have hhi : qa + M.F t ≤ 1 - qa := by linarith [hdn.2.2.2.2.2.2.2.2.1]
      rw [← hγn.2.2.2.2.1]
      exact ⟨pow_le_pow_left₀ (by linarith [hγn.2.2.1, hγn.2.2.2.1]) hlo _,
             pow_le_pow_left₀ (by linarith [hγn.2.2.1, hγn.2.2.2.1]) hhi _⟩
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv j k hjpos
    have hv01 : 0 ≤ v ∧ v ≤ 1 := by rw [hMn_a] at hv; exact hv
    have hs := br_surplus_asymDev M hm ha hn hdn.1 hdn.2.1 hdn.2.2.1 hvh_v2 hdn.2.2.2.2.2.1
      hdn.2.2.2.2.2.2.1 hdn.2.2.2.2.2.2.2.1 hdn.2.2.2.2.2.2.2.2.1 hdn.2.2.2.2.2.2.2.2.2.1
      hdn.2.2.2.2.2.2.2.2.2.2.1 hγn.2.2.2.2.1 hdn.2.2.2.2.2.2.2.2.2.2.2 hv01.1 hv01.2
    -- Fold `asym*` in `hs` to `v0, vh, v2, β, va, qa, q0, barx`
    have hs1 : surplus Mn (asymDevMech M r_L r_H u n) (effDist Mn θd (seller0 Mn)) v =
        (if v ≤ v0 then 0
         else if v ≤ vh then ∫ t in v0..v, (q0 + M.F t) ^ (n - 1)
         else if v ≤ β then (v - r_H n) * barx
         else if v ≤ va then (β - r_H n) * barx + (v - β) * (1 - qa) ^ (n - 1)
         else (β - r_H n) * barx + (va - β) * (1 - qa) ^ (n - 1) + ∫ t in va..v, br_Ah M t ^ (n - 1)) := hs.1
    have hs2 : ∀ j' : Fin Mn.m, j' ≠ seller0 Mn →
        surplus Mn (br_spa (r_H n)) (effDist Mn θd j') v =
          (if v ≤ r_H n then 0
           else if v ≤ v2 then (v - r_H n) * barx
           else if v ≤ va then (v2 - r_H n) * barx + ∫ t in v2..v, (qa + M.F t) ^ (n - 1)
           else (v2 - r_H n) * barx + (∫ t in v2..va, (qa + M.F t) ^ (n - 1)) + ∫ t in va..v, br_Ah M t ^ (n - 1)) := hs.2
    -- Prove s_H(v) ≤ s_L(v) when v ≤ v2 or va ≤ v, and s_L(v) ≤ s_H(v) when v2 < v < va (and equality at v ≥ va)
    have hcomp_L_ge_H : v ≤ v2 ∨ va ≤ v → ∀ j' : Fin Mn.m, j' ≠ seller0 Mn →
        surplus Mn (br_spa (r_H n)) (effDist Mn θd j') v ≤
          surplus Mn (asymDevMech M r_L r_H u n) (effDist Mn θd (seller0 Mn)) v := by
      intro hcase j' hj'
      rw [hs1, hs2 j' hj']
      rcases hcase with hv2 | hva
      · by_cases h1 : v ≤ v0
        · simp only [h1, show v ≤ r_H n by linarith [hdn.2.1], ↓reduceIte]; exact le_rfl
        · push Not at h1
          by_cases h2 : v ≤ vh
          · by_cases hr : v ≤ r_H n
            · simp only [not_le.mpr h1, h2, hr, ↓reduceIte]
              exact intervalIntegral.integral_nonneg h1.le fun t ht =>
                pow_nonneg (hFL_nn t ⟨by linarith [ht.1], by linarith [ht.2]⟩) _
            · push Not at hr
              simp only [not_le.mpr h1, h2, not_le.mpr hr, hv2, ↓reduceIte]
              have hi1 : IntervalIntegrable (fun t => (q0 + M.F t) ^ (n - 1)) volume v0 v :=
                (hFLc.mono (by rw [uIcc_of_le h1.le]; exact Icc_subset_Icc hdn.1.le hv01.2)).intervalIntegrable
              have hi2 : IntervalIntegrable (fun t => (q0 + M.F t) ^ (n - 1)) volume v vh :=
                (hFLc.mono (by rw [uIcc_of_le h2]; exact Icc_subset_Icc hv01.1 (by linarith [hvh_v2, hv2_va, hdn.2.2.2.2.2.2.2.1]))).intervalIntegrable
              have hsp := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
              have hle : ∫ t in v..vh, (q0 + M.F t) ^ (n - 1) ≤ (vh - v) * barx := by
                have hc' : ∫ _ in v..vh, barx = (vh - v) * barx := by rw [intervalIntegral.integral_const, smul_eq_mul]
                rw [← hc']
                exact intervalIntegral.integral_mono_on h2 hi2 intervalIntegrable_const fun t ht =>
                  hFL_le t ⟨by linarith [ht.1], ht.2⟩
              have he20' : ∫ t in v0..vh, (q0 + M.F t) ^ (n - 1) = (vh - r_H n) * barx := by
                rw [← hγn.2.2.2.2.1]; exact hdn.2.2.2.2.2.2.2.2.2.2.2
              linarith only [hsp, he20', hle]
          · push Not at h2
            simp only [not_le.mpr h1, not_le.mpr h2, show v ≤ β by linarith [hdn.2.2.2.2.2.1],
              not_le.mpr (lt_trans hdn.2.2.1 h2), hv2, ↓reduceIte]
            exact le_rfl
      · by_cases hveq : v = va
        · subst hveq
          simp only [not_le.mpr (by linarith [hdn.2.1, hdn.2.2.1, hvh_v2, hv2_va] : v0 < va),
            not_le.mpr (lt_trans hvh_v2 hv2_va), not_le.mpr hdn.2.2.2.2.2.2.1, le_rfl,
            not_le.mpr (by linarith [hdn.2.2.1, hvh_v2, hv2_va] : r_H n < va),
            not_le.mpr hv2_va, ↓reduceIte]
          linarith only [hbal_β]
        · have hvgt : va < v := lt_of_le_of_ne hva (Ne.symm hveq)
          simp only [not_le.mpr (by linarith [hdn.2.1, hdn.2.2.1, hvh_v2, hv2_va] : v0 < v),
            not_le.mpr (by linarith [hvh_v2, hv2_va] : vh < v),
            not_le.mpr (lt_trans hdn.2.2.2.2.2.2.1 hvgt), not_le.mpr hvgt,
            not_le.mpr (by linarith [hdn.2.2.1, hvh_v2, hv2_va] : r_H n < v),
            not_le.mpr (lt_trans hv2_va hvgt), ↓reduceIte]
          linarith only [hbal_β]
    have hcomp_H_ge_L : v2 < v → ∀ j' : Fin Mn.m, j' ≠ seller0 Mn →
        surplus Mn (asymDevMech M r_L r_H u n) (effDist Mn θd (seller0 Mn)) v ≤
          surplus Mn (br_spa (r_H n)) (effDist Mn θd j') v := by
      intro hv2 j' hj'
      rw [hs1, hs2 j' hj']
      by_cases hva : v ≤ va
      · simp only [not_le.mpr (by linarith [hdn.2.1, hdn.2.2.1, hvh_v2] : v0 < v),
          not_le.mpr (lt_trans hvh_v2 hv2), hva,
          not_le.mpr (by linarith [hdn.2.2.1, hvh_v2] : r_H n < v), not_le.mpr hv2, ↓reduceIte]
        by_cases hβ : v ≤ β
        · simp only [hβ, ↓reduceIte]
          have hi : IntervalIntegrable (fun t => (qa + M.F t) ^ (n - 1)) volume v2 v :=
            (hFHc.mono (by rw [uIcc_of_le hv2.le]; exact Icc_subset_Icc (by linarith [hdn.1, hdn.2.1, hdn.2.2.1, hvh_v2]) hv01.2)).intervalIntegrable
          have hle : (v - v2) * barx ≤ ∫ t in v2..v, (qa + M.F t) ^ (n - 1) := by
            have hc' : ∫ _ in v2..v, barx = (v - v2) * barx := by rw [intervalIntegral.integral_const, smul_eq_mul]
            rw [← hc']
            exact intervalIntegral.integral_mono_on hv2.le intervalIntegrable_const hi fun t ht =>
              (hFH_range t ⟨ht.1, le_trans ht.2 hva⟩).1
          linarith only [hle]
        · push Not at hβ
          simp only [not_le.mpr hβ, ↓reduceIte]
          have hi1 : IntervalIntegrable (fun t => (qa + M.F t) ^ (n - 1)) volume v2 v :=
            (hFHc.mono (by rw [uIcc_of_le hv2.le]; exact Icc_subset_Icc (by linarith [hdn.1, hdn.2.1, hdn.2.2.1, hvh_v2]) hv01.2)).intervalIntegrable
          have hi2 : IntervalIntegrable (fun t => (qa + M.F t) ^ (n - 1)) volume v va :=
            (hFHc.mono (by rw [uIcc_of_le hva]; exact Icc_subset_Icc hv01.1 hdn.2.2.2.2.2.2.2.1.le)).intervalIntegrable
          have hsp := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
          have hle : ∫ t in v..va, (qa + M.F t) ^ (n - 1) ≤ (va - v) * (1 - qa) ^ (n - 1) := by
            have hc' : ∫ _ in v..va, (1 - qa) ^ (n - 1) = (va - v) * (1 - qa) ^ (n - 1) := by
              rw [intervalIntegral.integral_const, smul_eq_mul]
            rw [← hc']
            exact intervalIntegral.integral_mono_on hva hi2 intervalIntegrable_const fun t ht =>
              (hFH_range t ⟨le_trans hv2.le ht.1, ht.2⟩).2
          linarith only [hsp, hbal_β, hle]
      · push Not at hva
        simp only [not_le.mpr (by linarith [hdn.2.1, hdn.2.2.1, hvh_v2] : v0 < v),
          not_le.mpr (lt_trans hvh_v2 hv2), not_le.mpr (lt_trans hdn.2.2.2.2.2.2.1 hva),
          not_le.mpr hva, not_le.mpr (by linarith [hdn.2.2.1, hvh_v2] : r_H n < v),
          not_le.mpr hv2, ↓reduceIte]
        linarith only [hbal_β]
    by_cases hj0 : j = seller0 Mn
    · subst hj0
      by_cases hk0 : k = seller0 Mn
      · subst hk0; exact le_rfl
      · simp only [↓reduceIte, hk0]
        have hcase : v ≤ v2 ∨ va ≤ v := by
          by_contra hnot; push Not at hnot
          have h0 : θd.θ (seller0 Mn) v = 0 := by
            dsimp [θd]; unfold asymDevVisit; rw [br_visit_seller0]
            rw [show asymV2 Mn r_L r_H u n = v2 from rfl, show asymVa Mn r_L r_H u n = va from rfl]
            simp [not_le.mpr hnot.1, hnot.2]
          linarith
        exact hcomp_L_ge_H hcase k hk0
    · by_cases hk0 : k = seller0 Mn
      · subst hk0; simp only [↓reduceIte, hj0]
        have hv2 : v2 < v := by
          by_contra hle; push Not at hle
          have h0 : θd.θ j v = 0 := by
            dsimp [θd]; unfold asymDevVisit; rw [br_visit_rival Mn hMn_m _ _ _ _ hj0]
            rw [show asymV2 Mn r_L r_H u n = v2 from rfl]
            simp [hle]
          linarith
        exact hcomp_H_ge_L hv2 j hj0
      · rw [hriv_eq j k hj0 hk0]

/-! #### Theorem 4, Part 3: Rescaled Revenue Gain Limit (eq. (22)) and Main Theorem -/

/-- Elementary FTC limit for `n * (∫_{a_n}^{b_n} (c_n + lam * F v)^(n-1) dv) / A_n^n`
when both endpoints `a_n, b_n → rH ∈ (0, 1)`. -/
lemma br_pow_int_tendsto (M : Market) (ha : M.a = 0) {lam rH A_lim L : ℝ}
    (hlam : 0 < lam) (hrH0 : 0 < rH) (hrH1 : rH < 1) (hAlim : 0 < A_lim)
    {a_seq b_seq c_seq A_seq : ℕ → ℝ}
    (ha_lim : Tendsto a_seq atTop (nhds rH)) (hb_lim : Tendsto b_seq atTop (nhds rH))
    (hA_lim : Tendsto A_seq atTop (nhds A_lim))
    (hdom : ∀ᶠ n : ℕ in atTop, 0 < a_seq n ∧ a_seq n ≤ b_seq n ∧ b_seq n < 1 ∧
      0 ≤ c_seq n + lam * M.F (a_seq n))
    (hR_lim : Tendsto (fun n : ℕ =>
      ((c_seq n + lam * M.F (b_seq n)) ^ n - (c_seq n + lam * M.F (a_seq n)) ^ n) / A_seq n ^ n)
      atTop (nhds L)) :
    Tendsto (fun n : ℕ =>
      ((n : ℝ) * ∫ v in a_seq n..b_seq n, (c_seq n + lam * M.F v) ^ (n - 1)) / A_seq n ^ n)
      atTop (nhds (L / (lam * M.f rH))) := by
  have hfH : 0 < M.f rH := M.hf_pos rH ⟨by rw [ha]; linarith, hrH1.le⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  let M_L := |L| + 1
  have hML : 0 < M_L := by positivity
  let ε₁ := min (M.f rH / 2) (ε * lam * M.f rH ^ 2 / (8 * M_L))
  have hε₁ : 0 < ε₁ := lt_min (by positivity) (by positivity)
  have hε₁2 : ε₁ ≤ M.f rH / 2 := min_le_left _ _
  have hε₁_mul : ε₁ * (8 * M_L) ≤ ε * lam * M.f rH ^ 2 :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  obtain ⟨δ₁, hδ₁, hfδ⟩ :=
    Metric.continuousWithinAt_iff.mp (M.hf_cont rH ⟨by rw [ha]; linarith, hrH1.le⟩) ε₁ hε₁
  have hR_near := Metric.tendsto_nhds.mp hR_lim (min (1 / 2) (ε * lam * M.f rH / 4))
    (lt_min (by norm_num) (by positivity))
  filter_upwards [eventually_ge_atTop 1, hdom,
    Metric.tendsto_nhds.mp ha_lim δ₁ hδ₁, Metric.tendsto_nhds.mp hb_lim δ₁ hδ₁,
    hA_lim.eventually (Ioi_mem_nhds (show 0 < A_lim by exact hAlim)), hR_near]
    with n hn hd hab hbb hApos hRb
  set an := a_seq n
  set bn := b_seq n
  set cn := c_seq n
  set An := A_seq n
  have hnR : (0 : ℝ) < (n : ℝ) := by positivity
  have hAn_pos : 0 < An ^ n := pow_pos hApos n
  have hFc : ContinuousOn M.F (Icc an bn) :=
    M.F_continuousOn.mono (Icc_subset_Icc (by rw [ha]; exact hd.1.le) hd.2.2.1.le)
  have hfc : ContinuousOn M.f (Icc an bn) :=
    M.hf_cont.mono (Icc_subset_Icc (by rw [ha]; exact hd.1.le) hd.2.2.1.le)
  have hGc : ContinuousOn (fun v => cn + lam * M.F v) (Icc an bn) :=
    continuousOn_const.add (continuousOn_const.mul hFc)
  have hGk : ContinuousOn (fun v => (cn + lam * M.F v) ^ (n - 1)) (Icc an bn) := hGc.pow (n - 1)
  have hGnn : ∀ v ∈ Icc an bn, 0 ≤ (cn + lam * M.F v) ^ (n - 1) := fun v hv => by
    have hFv : M.F an ≤ M.F v :=
      M.F_strictMonoOn.monotoneOn ⟨by rw [ha]; exact hd.1.le, le_trans hd.2.1 hd.2.2.1.le⟩
        ⟨by rw [ha]; linarith [hd.1, hv.1], le_trans hv.2 hd.2.2.1.le⟩ hv.1
    exact pow_nonneg (by nlinarith [hd.2.2.2]) _
  have hwin : ∀ v ∈ Icc an bn, M.f rH - ε₁ ≤ M.f v ∧ M.f v ≤ M.f rH + ε₁ := by
    intro v hv
    have hdist : dist v rH < δ₁ := by
      rw [Real.dist_eq] at hab hbb ⊢; rw [abs_lt] at hab hbb ⊢
      constructor <;> linarith [hv.1, hv.2]
    have h := hfδ ⟨by rw [ha]; linarith [hd.1, hv.1], le_trans hv.2 hd.2.2.1.le⟩ hdist
    rw [Real.dist_eq, abs_lt] at h; exact ⟨by linarith, by linarith⟩
  have hFTC : (cn + lam * M.F bn) ^ n - (cn + lam * M.F an) ^ n =
      (n : ℝ) * (lam * ∫ v in an..bn, (cn + lam * M.F v) ^ (n - 1) * M.f v) := by
    have hderiv : ∀ v ∈ Ioo an bn,
        HasDerivAt (fun v => (cn + lam * M.F v) ^ n)
          ((n : ℝ) * lam * ((cn + lam * M.F v) ^ (n - 1) * M.f v)) v := by
      intro v hv
      have hv' : v ∈ Ioo M.a 1 := ⟨by rw [ha]; linarith [hd.1, hv.1], lt_of_lt_of_le hv.2 hd.2.2.1.le⟩
      have h := (((M.hF_deriv_open v hv').const_mul lam).const_add cn).pow n
      convert h using 1; ring
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hd.2.1 (hGc.pow n) hderiv
      ((continuousOn_const.mul (hGk.mul hfc)).mono (by rw [uIcc_of_le hd.2.1])).intervalIntegrable
    simp only [Pi.pow_apply] at h
    rw [intervalIntegral.integral_const_mul] at h
    linarith
  have hint_lo : (M.f rH - ε₁) * (∫ v in an..bn, (cn + lam * M.F v) ^ (n - 1)) ≤
      ∫ v in an..bn, (cn + lam * M.F v) ^ (n - 1) * M.f v := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on hd.2.1
      ((continuousOn_const.mul hGk).mono (by rw [uIcc_of_le hd.2.1])).intervalIntegrable
      ((hGk.mul hfc).mono (by rw [uIcc_of_le hd.2.1])).intervalIntegrable
      (fun v hv => by rw [mul_comm]; exact mul_le_mul_of_nonneg_left (hwin v hv).1 (hGnn v hv))
  have hint_hi : ∫ v in an..bn, (cn + lam * M.F v) ^ (n - 1) * M.f v ≤
      (M.f rH + ε₁) * (∫ v in an..bn, (cn + lam * M.F v) ^ (n - 1)) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on hd.2.1
      ((hGk.mul hfc).mono (by rw [uIcc_of_le hd.2.1])).intervalIntegrable
      ((continuousOn_const.mul hGk).mono (by rw [uIcc_of_le hd.2.1])).intervalIntegrable
      (fun v hv => by rw [mul_comm (M.f rH + ε₁)]; exact mul_le_mul_of_nonneg_left (hwin v hv).2 (hGnn v hv))
  set I := ((n : ℝ) * ∫ v in an..bn, (cn + lam * M.F v) ^ (n - 1)) / An ^ n
  set R := ((cn + lam * M.F bn) ^ n - (cn + lam * M.F an) ^ n) / An ^ n
  have hI_nn : 0 ≤ I := div_nonneg (mul_nonneg hnR.le (intervalIntegral.integral_nonneg hd.2.1 hGnn)) hAn_pos.le
  have hR_lo : lam * (M.f rH - ε₁) * I ≤ R := by
    dsimp [R, I]; rw [hFTC]
    have heq : lam * (M.f rH - ε₁) * ((n : ℝ) * (∫ v in an..bn, (cn + lam * M.F v) ^ (n - 1)) / An ^ n) =
        ((n : ℝ) * (lam * ((M.f rH - ε₁) * ∫ v in an..bn, (cn + lam * M.F v) ^ (n - 1)))) / An ^ n := by ring
    rw [heq]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hint_lo hlam.le) hnR.le) hAn_pos.le
  have hR_hi : R ≤ lam * (M.f rH + ε₁) * I := by
    dsimp [R, I]; rw [hFTC]
    have heq : lam * (M.f rH + ε₁) * ((n : ℝ) * (∫ v in an..bn, (cn + lam * M.F v) ^ (n - 1)) / An ^ n) =
        ((n : ℝ) * (lam * ((M.f rH + ε₁) * ∫ v in an..bn, (cn + lam * M.F v) ^ (n - 1)))) / An ^ n := by ring
    rw [heq]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hint_hi hlam.le) hnR.le) hAn_pos.le
  have hR_nn : 0 ≤ R := le_trans (mul_nonneg (mul_nonneg hlam.le (by linarith)) hI_nn) hR_lo
  have hfe : 0 < M.f rH - ε₁ := by linarith
  have hI_le : I ≤ R / (lam * (M.f rH - ε₁)) := (le_div_iff₀ (mul_pos hlam hfe)).mpr (by linarith)
  have hI_ge : R / (lam * (M.f rH + ε₁)) ≤ I := (div_le_iff₀ (mul_pos hlam (by linarith))).mpr (by linarith)
  rw [Real.dist_eq] at hRb ⊢
  have hR1 : |R - L| < 1 / 2 := lt_of_lt_of_le hRb (min_le_left _ _)
  have hR2 : |R - L| < ε * lam * M.f rH / 4 := lt_of_lt_of_le hRb (min_le_right _ _)
  have hR_le_ML : R ≤ M_L := by
    have := (abs_lt.mp hR1).2
    have hL_le : L ≤ |L| := le_abs_self L
    dsimp [M_L]; linarith
  have he1 : R / (lam * (M.f rH - ε₁)) - R / (lam * M.f rH) ≤ ε / 2 := by
    rw [div_sub_div _ _ (mul_pos hlam hfe).ne' (mul_pos hlam hfH).ne',
      div_le_iff₀ (mul_pos (mul_pos hlam hfe) (mul_pos hlam hfH))]
    have hfac : R * (lam * M.f rH) - lam * (M.f rH - ε₁) * R = R * lam * ε₁ := by ring
    rw [hfac]
    have h1 : R * lam * ε₁ ≤ M_L * lam * ε₁ := by
      have := mul_le_mul_of_nonneg_right hR_le_ML (mul_nonneg hlam.le hε₁.le)
      linarith only [this]
    have h2 : M.f rH / 2 ≤ M.f rH - ε₁ := by linarith only [hε₁2]
    have h3 : ε / 4 * (lam ^ 2 * M.f rH ^ 2) ≤ ε / 2 * (lam * (M.f rH - ε₁) * (lam * M.f rH)) := by
      have hm : M.f rH ^ 2 / 2 ≤ (M.f rH - ε₁) * M.f rH := by nlinarith only [h2, hfH]
      have : lam ^ 2 * M.f rH ^ 2 / 2 ≤ lam * (M.f rH - ε₁) * (lam * M.f rH) := by
        calc lam ^ 2 * M.f rH ^ 2 / 2 = lam ^ 2 * (M.f rH ^ 2 / 2) := by ring
          _ ≤ lam ^ 2 * ((M.f rH - ε₁) * M.f rH) := mul_le_mul_of_nonneg_left hm (sq_nonneg lam)
          _ = lam * (M.f rH - ε₁) * (lam * M.f rH) := by ring
      nlinarith only [this, hε]
    have h4 : M_L * lam * ε₁ ≤ ε / 8 * (lam ^ 2 * M.f rH ^ 2) := by
      nlinarith only [hε₁_mul, hlam]
    have hpos : 0 ≤ ε * (lam ^ 2 * M.f rH ^ 2) := by positivity
    linarith only [h1, h3, h4, hpos]
  have he2 : R / (lam * M.f rH) - R / (lam * (M.f rH + ε₁)) ≤ ε / 2 := by
    rw [div_sub_div _ _ (mul_pos hlam hfH).ne' (mul_pos hlam (by linarith)).ne',
      div_le_iff₀ (mul_pos (mul_pos hlam hfH) (mul_pos hlam (by linarith)))]
    have hfac : R * (lam * (M.f rH + ε₁)) - lam * M.f rH * R = R * lam * ε₁ := by ring
    rw [hfac]
    have h1 : R * lam * ε₁ ≤ M_L * lam * ε₁ := by
      have := mul_le_mul_of_nonneg_right hR_le_ML (mul_nonneg hlam.le hε₁.le)
      linarith only [this]
    have h3 : ε / 4 * (lam ^ 2 * M.f rH ^ 2) ≤ ε / 2 * (lam * M.f rH * (lam * (M.f rH + ε₁))) := by
      have hm : M.f rH ^ 2 ≤ M.f rH * (M.f rH + ε₁) := by nlinarith only [hfH, hε₁]
      have : lam ^ 2 * M.f rH ^ 2 ≤ lam * M.f rH * (lam * (M.f rH + ε₁)) := by
        calc lam ^ 2 * M.f rH ^ 2 = lam ^ 2 * M.f rH ^ 2 := rfl
          _ ≤ lam ^ 2 * (M.f rH * (M.f rH + ε₁)) := mul_le_mul_of_nonneg_left hm (sq_nonneg lam)
          _ = lam * M.f rH * (lam * (M.f rH + ε₁)) := by ring
      have hnn : 0 ≤ lam ^ 2 * M.f rH ^ 2 := by positivity
      nlinarith only [this, hε, hnn]
    have h4 : M_L * lam * ε₁ ≤ ε / 8 * (lam ^ 2 * M.f rH ^ 2) := by
      nlinarith only [hε₁_mul, hlam]
    have hpos : 0 ≤ ε * (lam ^ 2 * M.f rH ^ 2) := by positivity
    linarith only [h1, h3, h4, hpos]
  have hRL : |R / (lam * M.f rH) - L / (lam * M.f rH)| < ε / 4 := by
    rw [← sub_div, abs_div, abs_of_pos (mul_pos hlam hfH), div_lt_iff₀ (mul_pos hlam hfH)]
    linarith only [hR2]
  rw [abs_lt] at hRL ⊢
  constructor <;> linarith only [hI_le, hI_ge, he1, he2, hRL.1, hRL.2, hε]

/-- Elementary MVT gap limit: if `a_n, b_n → rH` and `(F b_n - F a_n) / δ_n → L`,
then `(b_n - a_n) / δ_n → L / f(rH)`. -/
lemma br_F_gap_tendsto (M : Market) (ha : M.a = 0) {rH L : ℝ} (hrH0 : 0 < rH) (hrH1 : rH < 1)
    {a_seq b_seq δ_seq : ℕ → ℝ}
    (ha_lim : Tendsto a_seq atTop (nhds rH)) (hb_lim : Tendsto b_seq atTop (nhds rH))
    (hdom : ∀ᶠ n : ℕ in atTop, 0 < a_seq n ∧ a_seq n ≤ b_seq n ∧ b_seq n < 1 ∧ 0 < δ_seq n)
    (hF_lim : Tendsto (fun n : ℕ => (M.F (b_seq n) - M.F (a_seq n)) / δ_seq n) atTop (nhds L)) :
    Tendsto (fun n : ℕ => (b_seq n - a_seq n) / δ_seq n) atTop (nhds (L / M.f rH)) := by
  have hfH : 0 < M.f rH := M.hf_pos rH ⟨by rw [ha]; linarith, hrH1.le⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  let M_L := |L| + 1
  have hML : 0 < M_L := by positivity
  let ε₁ := min (M.f rH / 2) (ε * M.f rH ^ 2 / (8 * M_L))
  have hε₁ : 0 < ε₁ := lt_min (by positivity) (by positivity)
  have hε₁2 : ε₁ ≤ M.f rH / 2 := min_le_left _ _
  have hε₁_mul : ε₁ * (8 * M_L) ≤ ε * M.f rH ^ 2 := (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  obtain ⟨δ₁, hδ₁, hfδ⟩ :=
    Metric.continuousWithinAt_iff.mp (M.hf_cont rH ⟨by rw [ha]; linarith, hrH1.le⟩) ε₁ hε₁
  have hF_near := Metric.tendsto_nhds.mp hF_lim (min (1 / 2) (ε * M.f rH / 4))
    (lt_min (by norm_num) (by positivity))
  filter_upwards [hdom, Metric.tendsto_nhds.mp ha_lim δ₁ hδ₁, Metric.tendsto_nhds.mp hb_lim δ₁ hδ₁,
    hF_near] with n hd hab hbb hFb
  have hwin : ∀ t ∈ Icc (a_seq n) (b_seq n), |M.f t - M.f rH| ≤ ε₁ := by
    intro t ht
    have hdist : dist t rH < δ₁ := by
      rw [Real.dist_eq] at hab hbb ⊢; rw [abs_lt] at hab hbb ⊢
      constructor <;> linarith [ht.1, ht.2]
    exact le_of_lt (by simpa [Real.dist_eq] using hfδ ⟨by rw [ha]; linarith [hd.1, ht.1], le_trans ht.2 hd.2.2.1.le⟩ hdist)
  have hbd := br_F_diff_bound M (by rw [ha]; exact hd.1.le) hd.2.1 hd.2.2.1.le hwin
  set R := (M.F (b_seq n) - M.F (a_seq n)) / δ_seq n
  set I := (b_seq n - a_seq n) / δ_seq n
  have hδp : 0 < δ_seq n := hd.2.2.2
  have hI_nn : 0 ≤ I := div_nonneg (by linarith [hd.2.1]) hδp.le
  have hfe : 0 < M.f rH - ε₁ := by linarith
  have hI_le : I ≤ R / (M.f rH - ε₁) := by
    rw [le_div_iff₀ hfe]; dsimp [I, R]
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hδp]; linarith [hbd.1]
  have hI_ge : R / (M.f rH + ε₁) ≤ I := by
    rw [div_le_iff₀ (by linarith)]; dsimp [I, R]
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hδp]; linarith [hbd.2]
  have hR_nn : 0 ≤ R := by linarith [mul_nonneg hfe.le hI_nn, show I * (M.f rH - ε₁) ≤ R from (le_div_iff₀ hfe).mp hI_le]
  rw [Real.dist_eq] at hFb ⊢
  have hR1 : |R - L| < 1 / 2 := lt_of_lt_of_le hFb (min_le_left _ _)
  have hR2 : |R - L| < ε * M.f rH / 4 := lt_of_lt_of_le hFb (min_le_right _ _)
  have hR_le_ML : R ≤ M_L := by
    have := (abs_lt.mp hR1).2; have := le_abs_self L; dsimp [M_L]; linarith
  have he1 : R / (M.f rH - ε₁) - R / M.f rH ≤ ε / 2 := by
    rw [div_sub_div _ _ hfe.ne' hfH.ne', div_le_iff₀ (mul_pos hfe hfH)]
    have hfac : R * M.f rH - (M.f rH - ε₁) * R = R * ε₁ := by ring
    rw [hfac]
    have h1 : R * ε₁ ≤ M_L * ε₁ := mul_le_mul_of_nonneg_right hR_le_ML hε₁.le
    have h2 : M.f rH / 2 ≤ M.f rH - ε₁ := by linarith only [hε₁2]
    have hm2 : M.f rH ^ 2 / 2 ≤ (M.f rH - ε₁) * M.f rH := by nlinarith only [h2, hfH]
    have h3 : ε / 4 * M.f rH ^ 2 ≤ ε / 2 * ((M.f rH - ε₁) * M.f rH) := by nlinarith only [hm2, hε]
    have h4 : M_L * ε₁ ≤ ε / 8 * M.f rH ^ 2 := by linarith only [hε₁_mul]
    have hpos : 0 ≤ ε * M.f rH ^ 2 := by positivity
    linarith only [h1, h3, h4, hpos]
  have he2 : R / M.f rH - R / (M.f rH + ε₁) ≤ ε / 2 := by
    rw [div_sub_div _ _ hfH.ne' (by linarith), div_le_iff₀ (mul_pos hfH (by linarith))]
    have hfac : R * (M.f rH + ε₁) - M.f rH * R = R * ε₁ := by ring
    rw [hfac]
    have h1 : R * ε₁ ≤ M_L * ε₁ := mul_le_mul_of_nonneg_right hR_le_ML hε₁.le
    have hm2 : M.f rH ^ 2 ≤ M.f rH * (M.f rH + ε₁) := by nlinarith only [hfH, hε₁]
    have h3 : ε / 4 * M.f rH ^ 2 ≤ ε / 2 * (M.f rH * (M.f rH + ε₁)) := by nlinarith only [hm2, hε, sq_nonneg (M.f rH)]
    have h4 : M_L * ε₁ ≤ ε / 8 * M.f rH ^ 2 := by linarith only [hε₁_mul]
    have hpos : 0 ≤ ε * M.f rH ^ 2 := by positivity
    linarith only [h1, h3, h4, hpos]
  have hRL : |R / M.f rH - L / M.f rH| < ε / 4 := by
    rw [← sub_div, abs_div, abs_of_pos hfH, div_lt_iff₀ hfH]; linarith only [hR2]
  rw [abs_lt] at hRL ⊢
  constructor <;> linarith only [hI_le, hI_ge, he1, he2, hRL.1, hRL.2, hε]

/-- Exact `v`-coordinate decomposition of the deviation revenue gain `R_dev - R_base` in `M.br_atN n`. -/
lemma br_asymRevGain_eq (M : Market) (hm : M.m = 2) (ha : M.a = 0)
    {r_L r_H : ℕ → ℝ} {u : ℝ} {n : ℕ} (hn : 2 ≤ n)
    (hLn : 0 ≤ r_L n) (hrLHn : r_L n < r_H n)
    (hv0_0 : 0 < asymV0 M r_L r_H u n) (hv0_rH : asymV0 M r_L r_H u n < r_H n)
    (hrH_vh : r_H n < asymVhat M r_L r_H u n) (hvh_w : asymVhat M r_L r_H u n < asymW M r_L r_H n)
    (hw_v2 : asymW M r_L r_H n < asymV2 M r_L r_H u n)
    (hv2_β : asymV2 M r_L r_H u n < asymBeta M r_L r_H u n)
    (hβ_va : asymBeta M r_L r_H u n < asymVa M r_L r_H u n)
    (hva_1 : asymVa M r_L r_H u n < 1)
    (hqa_lt_That : asymQa M r_L r_H u n < asymThat M r_L r_H u n)
    (hFva : M.F (asymVa M r_L r_H u n) = 1 - 2 * asymQa M r_L r_H u n)
    (hFv2 : M.F (asymV2 M r_L r_H u n) = 1 - (asymQa M r_L r_H u n + asymQ0 M r_L r_H u n))
    (hFvh : M.F (asymVhat M r_L r_H u n) = 1 - (asymThat M r_L r_H u n + asymQ0 M r_L r_H u n))
    (hbarx : (1 - asymQ0 M r_L r_H u n) ^ (n - 1) = asymBarX M r_L r_H u n)
    (hbal_w : ∫ v in r_L n..asymW M r_L r_H n, ((1 - M.F (asymW M r_L r_H n)) / 2 + M.F v) ^ (n - 1) =
      (asymW M r_L r_H n - r_H n) * br_Ah M (asymW M r_L r_H n) ^ (n - 1))
    (heq20 : ∫ v in asymV0 M r_L r_H u n..asymVhat M r_L r_H u n, (asymQ0 M r_L r_H u n + M.F v) ^ (n - 1) =
      (asymVhat M r_L r_H u n - r_H n) * (1 - asymQ0 M r_L r_H u n) ^ (n - 1))
    (hbal_β : (asymBeta M r_L r_H u n - r_H n) * asymBarX M r_L r_H u n +
      (asymVa M r_L r_H u n - asymBeta M r_L r_H u n) * (1 - asymQa M r_L r_H u n) ^ (n - 1) =
      (asymV2 M r_L r_H u n - r_H n) * asymBarX M r_L r_H u n +
        ∫ t in asymV2 M r_L r_H u n..asymVa M r_L r_H u n, (asymQa M r_L r_H u n + M.F t) ^ (n - 1)) :
    let Mn := M.br_atN n
    let w := asymW M r_L r_H n
    let v0 := asymV0 M r_L r_H u n
    let vh := asymVhat M r_L r_H u n
    let v2 := asymV2 M r_L r_H u n
    let va := asymVa M r_L r_H u n
    let qa := asymQa M r_L r_H u n
    let q0 := asymQ0 M r_L r_H u n
    let That := asymThat M r_L r_H u n
    let An := asymAn M r_L r_H n
    let barx := asymBarX M r_L r_H u n
    sellerRev Mn (asymDevMech M r_L r_H u n) (asymDevVisit Mn r_L r_H u n) (seller0 Mn) -
    sellerRev Mn (br_spa (r_L n)) (asymBaseVisit Mn w) (seller0 Mn) =
      (vh - r_H n) * (1 - That) ^ n +
      (r_H n - va) * (1 - qa) ^ n -
      v0 * (1 - That) ^ n +
      v0 * ((1 - That) ^ n - (q0 + M.F v0) ^ n) +
      r_L n * ((1 - M.F w) / 2 + M.F (r_L n)) ^ n +
      (∫ v in r_L n..w, ((n : ℝ) * (An - ((1 - M.F w) / 2 + M.F v)) + ((1 - M.F w) / 2 + M.F v)) *
        ((1 - M.F w) / 2 + M.F v) ^ (n - 1)) -
      (∫ v in v0..vh, ((n : ℝ) * ((1 - That) - (q0 + M.F v)) + (q0 + M.F v)) * (q0 + M.F v) ^ (n - 1)) +
      (∫ v in w..va, ((n : ℝ) * ((1 - qa) - br_Ah M v) + br_Ah M v) * br_Ah M v ^ (n - 1)) +
      (n : ℝ) * (w - r_H n) * An ^ (n - 1) * ((1 - qa) - An) -
      (n : ℝ) * qa * (v2 - r_H n) * barx +
      (n : ℝ) * qa * (w - r_H n) * An ^ (n - 1) -
      (n : ℝ) * qa * (∫ t in v2..va, (qa + M.F t) ^ (n - 1)) +
      (n : ℝ) * qa * (∫ t in w..va, br_Ah M t ^ (n - 1)) := by
  intro Mn w v0 vh v2 va qa q0 That An barx
  have hMn_n : Mn.n = n := M.br_atN_n hn
  have hMn_a : Mn.a = 0 := ha
  have hMn_m : Mn.m = 2 := hm
  have hMn_F : Mn.F = M.F := rfl
  have hMn_Ah : br_Ah Mn = br_Ah M := rfl
  have hvh_v2 : vh < v2 := lt_trans hvh_w hw_v2
  have hv2_va : v2 < va := lt_trans hv2_β hβ_va
  have hw_va : w < va := lt_trans hw_v2 hv2_va
  have hrH_w : r_H n < w := lt_trans hrH_vh hvh_w
  have hrL_w : r_L n < w := lt_trans hrLHn hrH_w
  have hw0 : 0 ≤ w := by linarith
  have hw1 : w ≤ 1 := by linarith
  have hv0_1 : v0 ≤ 1 := by linarith
  have hvh_0 : 0 ≤ vh := by linarith
  have hvh_1 : vh ≤ 1 := by linarith
  have hv2_0 : 0 ≤ v2 := by linarith
  have hv2_1 : v2 ≤ 1 := by linarith
  have hva_0 : 0 ≤ va := by linarith
  have hAn_eq : An = br_Ah M w := by dsimp [An]; unfold asymAn asymQw br_Ah; ring
  have hA_va : br_Ah M va = 1 - qa := by unfold br_Ah; rw [hFva]; ring
  have hFc : ContinuousOn M.F (Icc 0 1) := by rw [← ha]; exact M.F_continuousOn
  have hfc : ContinuousOn M.f (Icc 0 1) := by rw [← ha]; exact M.hf_cont
  have hAc : ContinuousOn (fun v => br_Ah M v) (Icc 0 1) := by
    unfold br_Ah; exact (continuousOn_const.add hFc).div_const 2
  have hAk : ContinuousOn (fun v => br_Ah M v ^ (n - 1)) (Icc 0 1) := hAc.pow (n - 1)
  have hint_c : ∀ {a b : ℝ} {φ : ℝ → ℝ}, 0 ≤ a → a ≤ b → b ≤ 1 → ContinuousOn φ (Icc a b) →
      IntervalIntegrable φ volume a b :=
    fun _ hab _ hφ => (hφ.mono (by rw [uIcc_of_le hab])).intervalIntegrable
  -- Helper: split integral by replacing integrand on open interval (a, b)
  have hcongr_oo : ∀ {a b : ℝ} {f g : ℝ → ℝ}, a ≤ b → (∀ v ∈ Ioo a b, f v = g v) →
      IntervalIntegrable g volume a b →
      IntervalIntegrable f volume a b ∧ ∫ v in a..b, f v = ∫ v in a..b, g v := by
    intro a b f g hab heq hg
    have hae : ∀ᵐ v ∂volume, v ∈ uIoc a b → f v = g v := by
      rw [uIoc_of_le hab]
      have hne : ∀ᵐ v ∂volume, v ≠ b := by
        rw [ae_iff]; simp only [not_not]; exact measure_singleton b
      filter_upwards [hne] with v hvb hv
      exact heq v ⟨hv.1, lt_of_le_of_ne hv.2 hvb⟩
    have hae_eq : g =ᵐ[volume.restrict (uIoc a b)] f :=
      (ae_restrict_iff' measurableSet_uIoc).mpr (by filter_upwards [hae] with v hv h; exact (hv h).symm)
    exact ⟨hg.congr_ae hae_eq, intervalIntegral.integral_congr_ae hae⟩
  set θd := asymDevVisit Mn r_L r_H u n
  set θb := asymBaseVisit Mn w
  set mech := asymDevMech M r_L r_H u n
  set φd : ℝ → ℝ := fun v => payment Mn mech (effDist Mn θd (seller0 Mn)) v * θd.θ (seller0 Mn) v * M.f v
  set φb : ℝ → ℝ := fun v => payment Mn (br_spa (r_L n)) (effDist Mn θb (seller0 Mn)) v * θb.θ (seller0 Mn) v * M.f v
  have hRd_def : sellerRev Mn mech θd (seller0 Mn) = (n : ℝ) * ∫ v in (0 : ℝ)..1, φd v := by
    unfold sellerRev; rw [hMn_n, hMn_a]; rfl
  have hRb_def : sellerRev Mn (br_spa (r_L n)) θb (seller0 Mn) = (n : ℝ) * ∫ v in (0 : ℝ)..1, φb v := by
    unfold sellerRev; rw [hMn_n, hMn_a]; rfl
  -- Shared top integral on [va, 1]
  set ψtop : ℝ → ℝ := fun v => (v * br_Ah M v ^ (n - 1) - ∫ t in va..v, br_Ah M t ^ (n - 1)) * (M.f v / 2)
  have hψtop_c : ContinuousOn ψtop (Icc va 1) := by
    have hprim := continuousOn_primitive_Icc hva_1.le (hAk.mono (Icc_subset_Icc (by linarith) le_rfl))
    exact ((continuousOn_id.mul (hAk.mono (Icc_subset_Icc (by linarith) le_rfl))).sub hprim).mul
      ((hfc.mono (Icc_subset_Icc (by linarith) le_rfl)).div_const 2)
  have hft_int : ∫ v in va..1, M.f v / 2 = qa := by
    rw [intervalIntegral.integral_div]
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hva_1.le
      (hFc.mono (Icc_subset_Icc (by linarith) le_rfl))
      (fun v hv => M.hF_deriv_open v ⟨by rw [ha]; linarith [hv.1], hv.2⟩)
      (hint_c (by linarith) hva_1.le le_rfl (hfc.mono (Icc_subset_Icc (by linarith) le_rfl)))
    rw [hFTC, M.hF_1, hFva]; ring
  set sd_va := (v2 - r_H n) * barx + ∫ t in v2..va, (qa + M.F t) ^ (n - 1)
  set sb_va := (w - r_H n) * An ^ (n - 1) + ∫ t in w..va, br_Ah M t ^ (n - 1)
  -- ====== DEVIATION PIECES ======
  have hpool : 0 ≤ v0 ∧ v0 ≤ vh ∧ vh < asymBeta M r_L r_H u n ∧ asymBeta M r_L r_H u n ≤ 1 :=
    ⟨hv0_0.le, by linarith, lt_trans hvh_v2 hv2_β, le_trans hβ_va.le hva_1.le⟩
  have hF0_vh : effDist Mn θd (seller0 Mn) vh = 1 - That := by
    rw [(br_effDist_asymDev M hm ha (by linarith) hv2_va hva_1.le hFva hFv2 (by linarith) (by linarith)).1,
      ite_eq_left hvh_v2.le, hFvh]; ring
  have hF0_β : effDist Mn θd (seller0 Mn) (asymBeta M r_L r_H u n) = 1 - qa := by
    rw [(br_effDist_asymDev M hm ha (by linarith) hv2_va hva_1.le hFva hFv2 (by linarith) (by linarith)).1,
      ite_eq_right (not_le.mpr hv2_β), ite_eq_left hβ_va.le]
  have hpool_val : poolAvg Mn.n (effDist Mn θd (seller0 Mn) vh) (effDist Mn θd (seller0 Mn) (asymBeta M r_L r_H u n)) = barx := by
    rw [hMn_n, hF0_vh, hF0_β]; rfl
  have hallL : ∀ v, alloc Mn mech (effDist Mn θd (seller0 Mn)) v =
      if v < v0 then 0 else if vh < v ∧ v < asymBeta M r_L r_H u n then barx else (effDist Mn θd (seller0 Mn) v) ^ (n - 1) := by
    intro v; dsimp [mech]; unfold asymDevMech; rw [br_alloc_onePool Mn hpool, hpool_val, hMn_n]
  have hθd0 : ∀ v, θd.θ (seller0 Mn) v = if v ≤ v2 then 1 else if v < va then 0 else 1 / 2 := by
    intro v; dsimp [θd]; unfold asymDevVisit; rw [br_visit_seller0]; rfl
  -- Dev piece 1: [0, v0]
  have hd1 : IntervalIntegrable φd volume 0 v0 ∧ ∫ v in (0 : ℝ)..v0, φd v = 0 := by
    have h := hcongr_oo hv0_0.le (f := φd) (g := fun _ => 0) (fun v hv => by
      dsimp [φd]; unfold payment
      have hs := (br_surplus_asymDev M hm ha hn hv0_0 hv0_rH hrH_vh hvh_v2 hv2_β hβ_va hva_1 hFva hFv2 hFvh hbarx heq20
        hv.1.le (by linarith [hv.2])).1
      rw [hallL, ite_eq_left hv.2, hs, ite_eq_left hv.2.le]; ring) intervalIntegrable_const
    rw [intervalIntegral.integral_zero] at h; exact h
  -- Dev piece 2: [v0, vh]
  have hd2 : IntervalIntegrable φd volume v0 vh ∧
      (n : ℝ) * ∫ v in v0..vh, φd v =
        vh * (1 - That) ^ n - v0 * (q0 + M.F v0) ^ n -
          ∫ v in v0..vh, ((n : ℝ) * ((1 - That) - (q0 + M.F v)) + (q0 + M.F v)) * (q0 + M.F v) ^ (n - 1) := by
    set Gd : ℝ → ℝ := fun v => q0 + M.F v
    have hGdc : ContinuousOn Gd (Icc v0 vh) := continuousOn_const.add (hFc.mono (Icc_subset_Icc hv0_0.le (by linarith)))
    have hGdk : ContinuousOn (fun v => Gd v ^ (n - 1)) (Icc v0 vh) := hGdc.pow (n - 1)
    have hprim := continuousOn_primitive_Icc (by linarith : v0 ≤ vh) hGdk
    have hgc : ContinuousOn (fun v => (v * Gd v ^ (n - 1) - (0 + ∫ t in v0..v, Gd t ^ (n - 1))) * M.f v) (Icc v0 vh) :=
      ((continuousOn_id.mul hGdk).sub (continuousOn_const.add hprim)).mul (hfc.mono (Icc_subset_Icc hv0_0.le (by linarith)))
    have h := hcongr_oo (by linarith : v0 ≤ vh) (f := φd)
      (g := fun v => (v * Gd v ^ (n - 1) - (0 + ∫ t in v0..v, Gd t ^ (n - 1))) * M.f v)
      (fun v hv => by
        dsimp [φd]; unfold payment
        have hs := (br_surplus_asymDev M hm ha hn hv0_0 hv0_rH hrH_vh hvh_v2 hv2_β hβ_va hva_1 hFva hFv2 hFvh hbarx heq20
          (v := v) (by linarith [hv.1, hv0_0]) (by linarith [hv.2, hvh_1])).1
        have he := (br_effDist_asymDev M hm ha hv2_0 hv2_va hva_1.le hFva hFv2
          (v := v) (by linarith [hv.1, hv0_0]) (by linarith [hv.2, hvh_1])).1
        rw [hallL, ite_eq_right (not_lt.mpr hv.1.le), ite_eq_right (fun h' => by linarith [h'.1, hv.2]), he,
          ite_eq_left (by linarith [hv.2]), hs, ite_eq_right (not_le.mpr hv.1), ite_eq_left hv.2.le, hθd0,
          ite_eq_left (by linarith [hv.2])]
        dsimp [Gd]; ring)
      (hint_c hv0_0.le (by linarith) (by linarith) hgc)
    have hbr := br_block_rev n (by omega) (by linarith : v0 ≤ vh) hGdc
      (hfc.mono (Icc_subset_Icc hv0_0.le hvh_1))
      (fun v hv => (M.hF_deriv_open v ⟨by rw [ha]; linarith [hv.1, hv0_0], by linarith [hv.2, hvh_1]⟩).const_add q0) 0
    have hGvh : Gd vh = 1 - That := by dsimp [Gd]; rw [hFvh]; ring
    rw [hGvh, mul_zero, zero_mul, sub_zero] at hbr
    refine ⟨h.1, ?_⟩; rw [h.2]; exact hbr
  -- Dev piece 3: [vh, v2]
  have hd3 : IntervalIntegrable φd volume vh v2 ∧
      (n : ℝ) * ∫ v in vh..v2, φd v = r_H n * ((1 - qa) ^ n - (1 - That) ^ n) := by
    have h := hcongr_oo hvh_v2.le (f := φd) (g := fun v => (r_H n * barx) * M.f v)
      (fun v hv => by
        dsimp [φd]; unfold payment
        have hs := (br_surplus_asymDev M hm ha hn hv0_0 hv0_rH hrH_vh hvh_v2 hv2_β hβ_va hva_1 hFva hFv2 hFvh hbarx heq20
          (v := v) (by linarith [hv.1, hvh_0]) (by linarith [hv.2, hv2_1])).1
        rw [hallL, ite_eq_right (not_lt.mpr (by linarith [hv.1, hv0_rH, hrH_vh])), ite_eq_left ⟨hv.1, lt_trans hv.2 hv2_β⟩,
          hs, ite_eq_right (not_le.mpr (by linarith [hv.1, hv0_rH, hrH_vh])), ite_eq_right (not_le.mpr hv.1),
          ite_eq_left (lt_trans hv.2 hv2_β).le, hθd0, ite_eq_left hv.2.le]
        ring)
      (hint_c hvh_0 hvh_v2.le hv2_1 (continuousOn_const.mul (hfc.mono (Icc_subset_Icc hvh_0 hv2_1))))
    refine ⟨h.1, ?_⟩
    rw [h.2, intervalIntegral.integral_const_mul]
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hvh_v2.le
      (hFc.mono (Icc_subset_Icc hvh_0 hv2_1))
      (fun v hv => M.hF_deriv_open v ⟨by rw [ha]; linarith [hv.1, hvh_0], by linarith [hv.2, hv2_1]⟩)
      (hint_c hvh_0 hvh_v2.le hv2_1 (hfc.mono (Icc_subset_Icc hvh_0 hv2_1)))
    rw [hFTC, hFv2, hFvh]
    have hne : asymThat M r_L r_H u n ≠ asymQa M r_L r_H u n := by linarith
    have hbarx_def : barx = ((1 - qa) ^ n - (1 - That) ^ n) / ((n : ℝ) * ((1 - qa) - (1 - That))) := by
      dsimp [barx, That, qa]; unfold asymBarX poolAvg; simp [hne]
    have hnR : (n : ℝ) ≠ 0 := by positivity
    have hdiff_ne : (1 - qa) - (1 - That) ≠ 0 := by linarith
    have hFdiff : (1 - (qa + q0)) - (1 - (That + q0)) = (1 - qa) - (1 - That) := by ring
    rw [hFdiff, hbarx_def]; field_simp [hnR, hdiff_ne]
  -- Dev piece 4: [v2, va]
  have hd4 : IntervalIntegrable φd volume v2 va ∧ ∫ v in v2..va, φd v = 0 := by
    have h := hcongr_oo hv2_va.le (f := φd) (g := fun _ => 0) (fun v hv => by
      dsimp [φd]; rw [hθd0, ite_eq_right (not_le.mpr hv.1), ite_eq_left hv.2]; ring) intervalIntegrable_const
    rw [intervalIntegral.integral_zero] at h; exact h
  -- Dev piece 5: [va, 1]
  have hd5 : IntervalIntegrable φd volume va 1 ∧
      (n : ℝ) * ∫ v in va..1, φd v = (n : ℝ) * (∫ v in va..1, ψtop v) - (n : ℝ) * qa * sd_va := by
    have hsd_int : IntervalIntegrable (fun v => sd_va * (M.f v / 2)) volume va 1 :=
      hint_c hva_0 hva_1.le le_rfl (continuousOn_const.mul ((hfc.mono (Icc_subset_Icc hva_0 le_rfl)).div_const 2))
    have h := hcongr_oo hva_1.le (f := φd) (g := fun v => ψtop v - sd_va * (M.f v / 2))
      (fun v hv => by
        dsimp [φd, ψtop]; unfold payment
        have hs := (br_surplus_asymDev M hm ha hn hv0_0 hv0_rH hrH_vh hvh_v2 hv2_β hβ_va hva_1 hFva hFv2 hFvh hbarx heq20
          (by linarith [hv.1, hva_0]) hv.2.le).1
        have he := (br_effDist_asymDev M hm ha hv2_0 hv2_va hva_1.le hFva hFv2 (by linarith [hv.1, hva_0]) hv.2.le).1
        rw [hallL, ite_eq_right (not_lt.mpr (by linarith [hv.1, hv0_rH, hrH_vh, hvh_v2, hv2_va])),
          ite_eq_right (fun h' => by linarith [h'.2, hv.1, hβ_va]),
          he, ite_eq_right (not_le.mpr (by linarith [hv.1, hv2_va])), ite_eq_right (not_le.mpr hv.1),
          hs, ite_eq_right (not_le.mpr (by linarith [hv.1, hv0_rH, hrH_vh, hvh_v2, hv2_va])),
          ite_eq_right (not_le.mpr (by linarith [hv.1, hvh_v2, hv2_va])),
          ite_eq_right (not_le.mpr (by linarith [hv.1, hβ_va])), ite_eq_right (not_le.mpr hv.1),
          hθd0, ite_eq_right (not_le.mpr (by linarith [hv.1, hv2_va])), ite_eq_right (not_lt.mpr hv.1.le), hbal_β]
        dsimp [sd_va]; ring)
      ((hint_c hva_0 hva_1.le le_rfl hψtop_c).sub hsd_int)
    refine ⟨h.1, ?_⟩
    rw [h.2, intervalIntegral.integral_sub (hint_c hva_0 hva_1.le le_rfl hψtop_c) hsd_int,
      intervalIntegral.integral_const_mul, hft_int]
    ring
  -- Sum Dev pieces
  have hRd_sum : sellerRev Mn mech θd (seller0 Mn) =
      (n : ℝ) * (∫ v in v0..vh, φd v) + (n : ℝ) * (∫ v in vh..v2, φd v) + (n : ℝ) * (∫ v in va..1, φd v) := by
    rw [hRd_def]
    have i0vh := hd1.1.trans hd2.1
    have i0v2 := i0vh.trans hd3.1
    have i0va := i0v2.trans hd4.1
    rw [← intervalIntegral.integral_add_adjacent_intervals i0va hd5.1,
      ← intervalIntegral.integral_add_adjacent_intervals i0v2 hd4.1,
      ← intervalIntegral.integral_add_adjacent_intervals i0vh hd3.1,
      ← intervalIntegral.integral_add_adjacent_intervals hd1.1 hd2.1,
      hd1.2, hd4.2]
    ring
  -- ====== BASELINE PIECES ======
  have hθb0 : ∀ v, θb.θ (seller0 Mn) v = if v ≤ w then 1 else 1 / 2 := by
    intro v; dsimp [θb]; unfold asymBaseVisit; rw [br_visit_seller0]
  have hrL1 : r_L n ≤ 1 := by linarith
  -- Base piece 1: [0, r_L n]
  have hb1 : IntervalIntegrable φb volume 0 (r_L n) ∧ ∫ v in (0 : ℝ)..r_L n, φb v = 0 := by
    have h := hcongr_oo hLn (f := φb) (g := fun _ => 0) (fun v hv => by
      dsimp [φb]; unfold payment
      have hs := (br_surplus_asymBase Mn hMn_m hMn_a hLn hrLHn hrH_w hw1 (v := v) hv.1.le (by linarith [hv.2, hrL1])).1
      rw [br_alloc_spa Mn hLn hrL1, ite_eq_left hv.2, hs, ite_eq_left hv.2.le]; ring) intervalIntegrable_const
    rw [intervalIntegral.integral_zero] at h; exact h
  -- Base piece 2: [r_L n, w]
  have hb2 : IntervalIntegrable φb volume (r_L n) w ∧
      (n : ℝ) * ∫ v in r_L n..w, φb v =
        w * An ^ n - r_L n * ((1 - M.F w) / 2 + M.F (r_L n)) ^ n -
          ∫ v in r_L n..w, ((n : ℝ) * (An - ((1 - M.F w) / 2 + M.F v)) + ((1 - M.F w) / 2 + M.F v)) *
            ((1 - M.F w) / 2 + M.F v) ^ (n - 1) := by
    set Gb : ℝ → ℝ := fun v => (1 - M.F w) / 2 + M.F v
    have hGbc : ContinuousOn Gb (Icc (r_L n) w) := continuousOn_const.add (hFc.mono (Icc_subset_Icc hLn hw1))
    have hGbk : ContinuousOn (fun v => Gb v ^ (n - 1)) (Icc (r_L n) w) := hGbc.pow (n - 1)
    have hprim := continuousOn_primitive_Icc hrL_w.le hGbk
    have hgc : ContinuousOn (fun v => (v * Gb v ^ (n - 1) - (0 + ∫ t in r_L n..v, Gb t ^ (n - 1))) * M.f v) (Icc (r_L n) w) :=
      ((continuousOn_id.mul hGbk).sub (continuousOn_const.add hprim)).mul (hfc.mono (Icc_subset_Icc hLn hw1))
    have h := hcongr_oo hrL_w.le (f := φb)
      (g := fun v => (v * Gb v ^ (n - 1) - (0 + ∫ t in r_L n..v, Gb t ^ (n - 1))) * M.f v)
      (fun v hv => by
        dsimp [φb]; unfold payment
        have hs := (br_surplus_asymBase Mn hMn_m hMn_a hLn hrLHn hrH_w hw1 (v := v) (by linarith [hv.1, hLn]) (by linarith [hv.2, hw1])).1
        have he := (br_effDist_asymBase Mn hMn_m hMn_a hw0 hw1 (v := v) (by linarith [hv.1, hLn]) (by linarith [hv.2, hw1])).1
        rw [br_alloc_spa Mn hLn hrL1, ite_eq_right (not_lt.mpr hv.1.le), he, ite_eq_left hv.2.le,
          hs, ite_eq_right (not_le.mpr hv.1), ite_eq_left hv.2.le, hθb0, ite_eq_left hv.2.le, hMn_n, hMn_F]
        dsimp [Gb]; ring)
      (hint_c hLn hrL_w.le hw1 hgc)
    have hbr := br_block_rev n (by omega) hrL_w.le hGbc (hfc.mono (Icc_subset_Icc hLn hw1))
      (fun v hv => (M.hF_deriv_open v ⟨by rw [ha]; linarith [hv.1, hLn], by linarith [hv.2, hw1]⟩).const_add _) 0
    have hGw : Gb w = An := by dsimp [Gb, An]; unfold asymAn asymQw; ring
    rw [hGw, mul_zero, zero_mul, sub_zero] at hbr
    refine ⟨h.1, ?_⟩; rw [h.2]; exact hbr
  -- Base piece 3: [w, va]
  have hb3 : IntervalIntegrable φb volume w va ∧
      (n : ℝ) * ∫ v in w..va, φb v =
        va * (1 - qa) ^ n - w * An ^ n -
          (∫ v in w..va, ((n : ℝ) * ((1 - qa) - br_Ah M v) + br_Ah M v) * br_Ah M v ^ (n - 1)) -
          (n : ℝ) * ((w - r_H n) * An ^ (n - 1)) * ((1 - qa) - An) := by
    set S0 := (w - r_H n) * An ^ (n - 1)
    have hprim := continuousOn_primitive_Icc hw_va.le (hAk.mono (Icc_subset_Icc hw0 hva_1.le))
    have hgc : ContinuousOn (fun v => (v * br_Ah M v ^ (n - 1) - (S0 + ∫ t in w..v, br_Ah M t ^ (n - 1))) * (M.f v / 2)) (Icc w va) :=
      ((continuousOn_id.mul (hAk.mono (Icc_subset_Icc hw0 hva_1.le))).sub (continuousOn_const.add hprim)).mul
        ((hfc.mono (Icc_subset_Icc hw0 hva_1.le)).div_const 2)
    have h := hcongr_oo hw_va.le (f := φb)
      (g := fun v => (v * br_Ah M v ^ (n - 1) - (S0 + ∫ t in w..v, br_Ah M t ^ (n - 1))) * (M.f v / 2))
      (fun v hv => by
        dsimp [φb]; unfold payment
        have hs := (br_surplus_asymBase Mn hMn_m hMn_a hLn hrLHn hrH_w hw1 (v := v) (by linarith [hv.1, hw0]) (by linarith [hv.2, hva_1])).1
        have he := (br_effDist_asymBase Mn hMn_m hMn_a hw0 hw1 (v := v) (by linarith [hv.1, hw0]) (by linarith [hv.2, hva_1])).1
        rw [br_alloc_spa Mn hLn hrL1, ite_eq_right (not_lt.mpr (by linarith [hv.1, hrL_w])), he, ite_eq_right (not_le.mpr hv.1),
          hs, ite_eq_right (not_le.mpr (by linarith [hv.1, hrL_w])), ite_eq_right (not_le.mpr hv.1),
          hθb0, ite_eq_right (not_le.mpr hv.1), hMn_n, hMn_F, hMn_Ah, hbal_w, ← hAn_eq]
        dsimp [S0]; ring)
      (hint_c hw0 hw_va.le hva_1.le hgc)
    have hbr := br_block_rev n (by omega) hw_va.le
      (hAc.mono (Icc_subset_Icc hw0 hva_1.le))
      ((hfc.mono (Icc_subset_Icc hw0 hva_1.le)).div_const 2)
      (fun v hv => by
        unfold br_Ah
        exact ((M.hF_deriv_open v ⟨by rw [ha]; linarith [hv.1, hw0], by linarith [hv.2, hva_1]⟩).const_add 1).div_const 2)
      S0
    rw [hA_va, ← hAn_eq] at hbr
    refine ⟨h.1, ?_⟩; rw [h.2]; exact hbr
  -- Base piece 4: [va, 1]
  have hb4 : IntervalIntegrable φb volume va 1 ∧
      (n : ℝ) * ∫ v in va..1, φb v = (n : ℝ) * (∫ v in va..1, ψtop v) - (n : ℝ) * qa * sb_va := by
    have hsb_int : IntervalIntegrable (fun v => sb_va * (M.f v / 2)) volume va 1 :=
      hint_c hva_0 hva_1.le le_rfl (continuousOn_const.mul ((hfc.mono (Icc_subset_Icc hva_0 le_rfl)).div_const 2))
    have h := hcongr_oo hva_1.le (f := φb) (g := fun v => ψtop v - sb_va * (M.f v / 2))
      (fun v hv => by
        dsimp [φb, ψtop]; unfold payment
        have hs := (br_surplus_asymBase Mn hMn_m hMn_a hLn hrLHn hrH_w hw1 (by linarith [hv.1, hva_0]) hv.2.le).1
        have he := (br_effDist_asymBase Mn hMn_m hMn_a hw0 hw1 (by linarith [hv.1, hva_0]) hv.2.le).1
        have hsp : ∫ t in w..v, br_Ah M t ^ (n - 1) =
            (∫ t in w..va, br_Ah M t ^ (n - 1)) + ∫ t in va..v, br_Ah M t ^ (n - 1) :=
          (intervalIntegral.integral_add_adjacent_intervals
            (hint_c hw0 hw_va.le hva_1.le (hAk.mono (Icc_subset_Icc hw0 hva_1.le)))
            (hint_c hva_0 hv.1.le hv.2.le (hAk.mono (Icc_subset_Icc hva_0 hv.2.le)))).symm
        rw [br_alloc_spa Mn hLn hrL1, ite_eq_right (not_lt.mpr (by linarith [hv.1, hrL_w, hw_va])), he,
          ite_eq_right (not_le.mpr (by linarith [hv.1, hw_va])),
          hs, ite_eq_right (not_le.mpr (by linarith [hv.1, hrL_w, hw_va])), ite_eq_right (not_le.mpr (by linarith [hv.1, hw_va])),
          hθb0, ite_eq_right (not_le.mpr (by linarith [hv.1, hw_va])), hMn_n, hMn_F, hMn_Ah, hbal_w, ← hAn_eq, hsp]
        dsimp [sb_va]; ring)
      ((hint_c hva_0 hva_1.le le_rfl hψtop_c).sub hsb_int)
    refine ⟨h.1, ?_⟩
    rw [h.2, intervalIntegral.integral_sub (hint_c hva_0 hva_1.le le_rfl hψtop_c) hsb_int,
      intervalIntegral.integral_const_mul, hft_int]
    ring
  -- Sum Base pieces
  have hRb_sum : sellerRev Mn (br_spa (r_L n)) θb (seller0 Mn) =
      (n : ℝ) * (∫ v in r_L n..w, φb v) + (n : ℝ) * (∫ v in w..va, φb v) + (n : ℝ) * (∫ v in va..1, φb v) := by
    rw [hRb_def]
    have i0w := hb1.1.trans hb2.1
    have i0va := i0w.trans hb3.1
    rw [← intervalIntegral.integral_add_adjacent_intervals i0va hb4.1,
      ← intervalIntegral.integral_add_adjacent_intervals i0w hb3.1,
      ← intervalIntegral.integral_add_adjacent_intervals hb1.1 hb2.1, hb1.2]
    ring
  rw [hRd_sum, hRb_sum, hd2.2, hd3.2, hd5.2, hb2.2, hb3.2, hb4.2]
  dsimp [sd_va, sb_va]
  ring

/-- **Theorem 4 (Part 3 — Exact Rescaled Revenue Limit, eq. (22))**:
Under the hypotheses of Theorem 4 and any feasible `u > 0`,
`D_n / (1 - q_{w_n})^n → rH * ((1 - u - γ) e^{-γ} - e^{-u}) + ((1 - F rH) / (2 f rH)) * ((γ - u) e^{-γ} + e^u - 1)`. -/
theorem theorem4_revenue_limit (M : Market) (hm : M.m = 2) (ha : M.a = 0)
    {r_L r_H : ℕ → ℝ} {rL rH u : ℝ} (hrL0 : 0 ≤ rL) (hrLH : rL < rH) (hrH1 : rH < 1)
    (hL_lim : Tendsto r_L atTop (nhds rL)) (hH_lim : Tendsto r_H atTop (nhds rH))
    (hL_nn : ∀ᶠ n in atTop, 0 ≤ r_L n)
    (hu : 0 < u) (huγ : u + br_gamma u < 1)
    (hfeas : (1 - u - br_gamma u) * Real.exp (-br_gamma u) < Real.exp (-u)) :
    Tendsto (fun n : ℕ =>
      let Mn := M.br_atN n
      (sellerRev Mn (asymDevMech M r_L r_H u n) (asymDevVisit Mn r_L r_H u n) (seller0 Mn) -
       sellerRev Mn (br_spa (r_L n)) (asymBaseVisit Mn (asymW M r_L r_H n)) (seller0 Mn)) /
        (1 - asymQw M r_L r_H n) ^ n)
      atTop (nhds (rH * ((1 - u - br_gamma u) * Real.exp (-br_gamma u) - Real.exp (-u)) +
        ((1 - M.F rH) / (2 * M.f rH)) * ((br_gamma u - u) * Real.exp (-br_gamma u) + Real.exp u - 1))) := by
  have hcut := theorem4_cutoff_asymptotics M hm ha hrL0 hrLH hrH1 hL_lim hH_lim hL_nn
  have hγ := br_gammaN_tendsto M hm ha hrL0 hrLH hrH1 hL_lim hH_lim hL_nn hu
  have hdev := br_dev_coords_asym M hm ha hrL0 hrLH hrH1 hL_lim hH_lim hL_nn hu huγ hfeas
  obtain ⟨fmin, hfmin, hf_lo⟩ := M.exists_f_min
  have hfH : 0 < M.f rH := M.hf_pos rH ⟨by rw [ha]; linarith, hrH1.le⟩
  have hFH_pos : 0 < M.F rH := by
    rw [← M.hF_a]; exact M.F_strictMonoOn (left_mem_Icc.mpr M.ha1.le) ⟨by rw [ha]; linarith, hrH1.le⟩ (by rw [ha]; linarith)
  have hFH_lt1 : M.F rH < 1 := by
    rw [← M.hF_1]; exact M.F_strictMonoOn ⟨by rw [ha]; linarith, hrH1.le⟩ (right_mem_Icc.mpr M.ha1.le) hrH1
  have hw_lim := hcut.2.1
  have hv0_lim := hdev.2.1
  have hvh_lim := hdev.2.2.1
  have hv2_lim := hdev.2.2.2.1
  have hva_lim := hdev.2.2.2.2.1
  have heq21 := hdev.2.2.2.2.2
  have hF_w : Tendsto (fun n => M.F (asymW M r_L r_H n)) atTop (nhds (M.F rH)) :=
    (M.F_continuousOn.continuousAt (Icc_mem_nhds (by rw [ha]; linarith) hrH1)).tendsto.comp hw_lim
  have hqw_lim : Tendsto (asymQw M r_L r_H) atTop (nhds ((1 - M.F rH) / 2)) :=
    (tendsto_const_nhds.sub hF_w).div_const 2
  have hAn_lim : Tendsto (asymAn M r_L r_H) atTop (nhds (1 - (1 - M.F rH) / 2)) :=
    tendsto_const_nhds.sub hqw_lim
  have hAnH_pos : 0 < 1 - (1 - M.F rH) / 2 := by linarith
  have hAn_half : ∀ᶠ n : ℕ in atTop, (1 / 2 : ℝ) < asymAn M r_L r_H n :=
    hAn_lim.eventually (Ioi_mem_nhds (show (1 / 2 : ℝ) < 1 - (1 - M.F rH) / 2 by linarith))
  have hδ_lim : Tendsto (asymDelta M r_L r_H) atTop (nhds 0) :=
    hAn_lim.div_atTop tendsto_natCast_atTop_atTop
  have hqa_lim : Tendsto (asymQa M r_L r_H u) atTop (nhds ((1 - M.F rH) / 2)) := by
    unfold asymQa; simpa using hqw_lim.sub (hδ_lim.const_mul u)
  have hord_r : ∀ᶠ n : ℕ in atTop, r_L n < r_H n := by
    filter_upwards [(hH_lim.sub hL_lim).eventually (Ioi_mem_nhds (sub_pos.mpr hrLH))] with n h; linarith
  -- Key exponential power limits
  have h1T_pow : Tendsto (fun n : ℕ => (1 - asymThat M r_L r_H u n) ^ n / asymAn M r_L r_H n ^ n)
      atTop (nhds (Real.exp (-u))) := by
    refine (Real.tendsto_one_add_div_pow_exp (-u)).congr' ?_
    filter_upwards [eventually_ge_atTop 1, hAn_half] with n hn hAn5
    have hnR : (n : ℝ) ≠ 0 := by positivity
    have hAn_pos : 0 < asymAn M r_L r_H n := by linarith
    have hAn_def : asymAn M r_L r_H n = 1 - asymQw M r_L r_H n := rfl
    rw [← div_pow]; congr 1
    unfold asymThat asymDelta; field_simp [hnR, hAn_pos.ne']; rw [hAn_def]; ring
  have h1a_pow : Tendsto (fun n : ℕ => (1 - asymQa M r_L r_H u n) ^ n / asymAn M r_L r_H n ^ n)
      atTop (nhds (Real.exp u)) := by
    refine (Real.tendsto_one_add_div_pow_exp u).congr' ?_
    filter_upwards [eventually_ge_atTop 1, hAn_half] with n hn hAn5
    have hnR : (n : ℝ) ≠ 0 := by positivity
    have hAn_pos : 0 < asymAn M r_L r_H n := by linarith
    have hAn_def : asymAn M r_L r_H n = 1 - asymQw M r_L r_H n := rfl
    rw [← div_pow]; congr 1
    unfold asymQa asymDelta; field_simp [hnR, hAn_pos.ne']; rw [hAn_def]; ring
  have h1q0_pow : Tendsto (fun n : ℕ => (1 - asymQ0 M r_L r_H u n) ^ n / asymAn M r_L r_H n ^ n)
      atTop (nhds (Real.exp (-br_gamma u))) := by
    refine (br_exp_pow_tendsto hγ.2.neg).1.congr' ?_
    filter_upwards [eventually_ge_atTop 1, hAn_half] with n hn hAn5
    have hnR : (n : ℝ) ≠ 0 := by positivity
    have hAn_pos : 0 < asymAn M r_L r_H n := by linarith
    have hAn_def : asymAn M r_L r_H n = 1 - asymQw M r_L r_H n := rfl
    rw [← div_pow]; congr 1
    unfold asymGammaN asymDelta; field_simp [hnR, hAn_pos.ne']; rw [hAn_def]; ring
  have hbarx_lim : Tendsto (fun n : ℕ => asymBarX M r_L r_H u n / asymAn M r_L r_H n ^ (n - 1))
      atTop (nhds (Real.exp (-br_gamma u))) := by
    refine (br_exp_pow_tendsto hγ.2.neg).2.congr' ?_
    filter_upwards [eventually_ge_atTop 2, hγ.1, hAn_half] with n hn hγn hAn5
    have hnR : (n : ℝ) ≠ 0 := by positivity
    have hAn_pos : 0 < asymAn M r_L r_H n := by linarith
    have hAn_def : asymAn M r_L r_H n = 1 - asymQw M r_L r_H n := rfl
    rw [← hγn.2.2.2.2.1, ← div_pow]; congr 1
    unfold asymGammaN asymDelta; field_simp [hnR, hAn_pos.ne']; rw [hAn_def]; ring
  -- Gap limits: (w - r_H) / δ → 1 / f(rH), (v2 - r_H) / δ → (1 + u - γ) / f(rH)
  have hwr_lim : Tendsto (fun n : ℕ => (asymW M r_L r_H n - r_H n) / asymDelta M r_L r_H n)
      atTop (nhds (1 / M.f rH)) := by
    have h := (hcut.2.2.div hAn_lim hAnH_pos.ne').add (tendsto_const_nhds (x := 1 / M.f rH))
    rw [zero_div, zero_add] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1, hAn_half] with n hn hAn5
    have hnR : (n : ℝ) ≠ 0 := by positivity
    have hAn_pos : 0 < asymAn M r_L r_H n := by linarith
    have hAn_def : asymAn M r_L r_H n = 1 - asymQw M r_L r_H n := rfl
    simp only [Pi.div_apply]
    unfold asymDelta; field_simp [hnR, hAn_pos.ne', hfH.ne']; rw [hAn_def]; unfold asymQw; ring
  have hv2w_lim : Tendsto (fun n : ℕ => (asymV2 M r_L r_H u n - asymW M r_L r_H n) / asymDelta M r_L r_H n)
      atTop (nhds ((u - br_gamma u) / M.f rH)) := by
    refine br_F_gap_tendsto M ha (by linarith) hrH1 hw_lim hv2_lim ?_ ?_
    · filter_upwards [eventually_ge_atTop 2, hdev.1, hAn_half] with n hn hdn hAn5
      exact ⟨by linarith [hdn.1, hdn.2.1, hdn.2.2.1, hdn.2.2.2.1], hdn.2.2.2.2.1.le,
        by linarith [hdn.2.2.2.2.2.1, hdn.2.2.2.2.2.2.1, hdn.2.2.2.2.2.2.2.1],
        div_pos (by linarith) (by positivity)⟩
    · refine (tendsto_const_nhds (x := u).sub hγ.2).congr' ?_
      filter_upwards [eventually_ge_atTop 2, hdev.1, hAn_half] with n hn hdn hAn5
      have hδpos : 0 < asymDelta M r_L r_H n := div_pos (by linarith) (by positivity)
      rw [hdn.2.2.2.2.2.2.2.2.2.1]
      have hFw : M.F (asymW M r_L r_H n) = 1 - 2 * asymQw M r_L r_H n := by unfold asymQw; ring
      have hq0 : asymQ0 M r_L r_H u n = asymQw M r_L r_H n + asymGammaN M r_L r_H u n * asymDelta M r_L r_H n := by
        unfold asymGammaN; field_simp [hδpos.ne']; ring
      rw [hFw, hq0]; unfold asymQa; field_simp [hδpos.ne']; ring
  have hv2r_lim : Tendsto (fun n : ℕ => (asymV2 M r_L r_H u n - r_H n) / asymDelta M r_L r_H n)
      atTop (nhds ((1 + u - br_gamma u) / M.f rH)) := by
    have h := hwr_lim.add hv2w_lim
    rw [show 1 / M.f rH + (u - br_gamma u) / M.f rH = (1 + u - br_gamma u) / M.f rH by ring] at h
    exact h.congr (fun n => by ring)
  -- Now limit of each of the 13 summands in br_asymRevGain_eq divided by An^n!
  have hL1 : Tendsto (fun n : ℕ => (asymVhat M r_L r_H u n - r_H n) * (1 - asymThat M r_L r_H u n) ^ n / asymAn M r_L r_H n ^ n)
      atTop (nhds 0) := by
    have h := (hvh_lim.sub hH_lim).mul h1T_pow
    rw [sub_self, zero_mul] at h
    exact h.congr (fun n => by ring)
  have hL2 : Tendsto (fun n : ℕ => (r_H n - asymVa M r_L r_H u n) * (1 - asymQa M r_L r_H u n) ^ n / asymAn M r_L r_H n ^ n)
      atTop (nhds 0) := by
    have h := (hH_lim.sub hva_lim).mul h1a_pow
    rw [sub_self, zero_mul] at h
    exact h.congr (fun n => by ring)
  have hL3 : Tendsto (fun n : ℕ => asymV0 M r_L r_H u n * (1 - asymThat M r_L r_H u n) ^ n / asymAn M r_L r_H n ^ n)
      atTop (nhds (rH * Real.exp (-u))) := by
    exact (hv0_lim.mul h1T_pow).congr (fun n => by ring)
  have hL4 : Tendsto (fun n : ℕ =>
      asymV0 M r_L r_H u n * ((1 - asymThat M r_L r_H u n) ^ n - (asymQ0 M r_L r_H u n + M.F (asymV0 M r_L r_H u n)) ^ n) /
        asymAn M r_L r_H n ^ n)
      atTop (nhds (rH * ((1 - u - br_gamma u) * Real.exp (-br_gamma u)))) := by
    exact (hv0_lim.mul heq21).congr (fun n => by ring)
  have hL5 : Tendsto (fun n : ℕ =>
      r_L n * ((1 - M.F (asymW M r_L r_H n)) / 2 + M.F (r_L n)) ^ n / asymAn M r_L r_H n ^ n)
      atTop (nhds 0) := by
    have hF_rL : Tendsto (fun n => M.F (r_L n)) atTop (nhds (M.F rL)) :=
      (M.F_continuousOn.continuousWithinAt ⟨by rw [ha]; exact hrL0, by linarith⟩).tendsto.comp
        (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hL_lim (by
          filter_upwards [hL_nn, hH_lim.eventually (Iio_mem_nhds hrH1), (hH_lim.sub hL_lim).eventually (Ioi_mem_nhds (sub_pos.mpr hrLH))]
            with n h1 h2 h3; exact ⟨by rw [ha]; exact h1, by linarith⟩))
    have hFL_lt : M.F rL < M.F rH :=
      M.F_strictMonoOn ⟨by rw [ha]; exact hrL0, by linarith⟩ ⟨by rw [ha]; linarith, hrH1.le⟩ hrLH
    have hrat_lim : Tendsto (fun n => ((1 - M.F (asymW M r_L r_H n)) / 2 + M.F (r_L n)) / asymAn M r_L r_H n)
        atTop (nhds (((1 - M.F rH) / 2 + M.F rL) / (1 - (1 - M.F rH) / 2))) :=
      (hqw_lim.add hF_rL).div hAn_lim hAnH_pos.ne'
    let ρ := (((1 - M.F rH) / 2 + M.F rL) / (1 - (1 - M.F rH) / 2) + 1) / 2
    have hrat_lt1 : ((1 - M.F rH) / 2 + M.F rL) / (1 - (1 - M.F rH) / 2) < 1 := by
      rw [div_lt_one hAnH_pos]; linarith
    have hρ_lt1 : ρ < 1 := by dsimp [ρ]; linarith
    have hρ_nn : 0 ≤ ρ := by
      have hrL_mem : rL ∈ Icc M.a 1 := ⟨by rw [ha]; exact hrL0, by linarith⟩
      have hrH_mem : rH ∈ Icc M.a 1 := ⟨by rw [ha]; linarith, hrH1.le⟩
      have h1 := (M.F_mem_Icc hrL_mem).1
      have h2 := (M.F_mem_Icc hrH_mem).2
      dsimp [ρ]; have : 0 ≤ ((1 - M.F rH) / 2 + M.F rL) / (1 - (1 - M.F rH) / 2) := div_nonneg (by linarith) hAnH_pos.le
      linarith
    have hpow0 : Tendsto (fun n : ℕ => ρ ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hρ_nn hρ_lt1
    have hbase_pow0 : Tendsto (fun n : ℕ => (((1 - M.F (asymW M r_L r_H n)) / 2 + M.F (r_L n)) / asymAn M r_L r_H n) ^ n)
        atTop (nhds 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hpow0 ?_ ?_
      · filter_upwards [hL_nn, hord_r, hcut.1, hAn_half] with n hLn hrLHn hcn hAn5
        have hrL_mem : r_L n ∈ Icc M.a 1 := ⟨by rw [ha]; exact hLn, by linarith [hrLHn, hcn.1.1, hcn.1.2]⟩
        have hw_mem : asymW M r_L r_H n ∈ Icc M.a 1 := ⟨by rw [ha]; linarith [hLn, hrLHn, hcn.1.1], hcn.1.2.le⟩
        have h1 := (M.F_mem_Icc hrL_mem).1
        have h2 := (M.F_mem_Icc hw_mem).2
        exact pow_nonneg (div_nonneg (by linarith) (by linarith)) n
      · filter_upwards [hL_nn, hord_r, hcut.1, hAn_half, hrat_lim.eventually (Iio_mem_nhds (show ((1 - M.F rH) / 2 + M.F rL) / (1 - (1 - M.F rH) / 2) < ρ by dsimp [ρ]; linarith))]
          with n hLn hrLHn hcn hAn5 hlt
        have hrL_mem : r_L n ∈ Icc M.a 1 := ⟨by rw [ha]; exact hLn, by linarith [hrLHn, hcn.1.1, hcn.1.2]⟩
        have hw_mem : asymW M r_L r_H n ∈ Icc M.a 1 := ⟨by rw [ha]; linarith [hLn, hrLHn, hcn.1.1], hcn.1.2.le⟩
        have h1 := (M.F_mem_Icc hrL_mem).1
        have h2 := (M.F_mem_Icc hw_mem).2
        exact pow_le_pow_left₀ (div_nonneg (by linarith) (by linarith)) hlt.le n
    have h := hL_lim.mul hbase_pow0
    rw [mul_zero] at h
    exact h.congr (fun n => by rw [div_pow]; ring)
  -- Block errors E_base / An^n → 0, E_dev / An^n → 0, E_mid / An^n → 0
  have hinv_n : Tendsto (fun n : ℕ => 2 / (((n : ℝ) + 1) * fmin)) atTop (nhds 0) := by
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * fmin) atTop atTop :=
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).atTop_mul_const hfmin
    exact tendsto_const_nhds.div_atTop h1
  have hL6 : Tendsto (fun n : ℕ =>
      (∫ v in r_L n..asymW M r_L r_H n,
        ((n : ℝ) * (asymAn M r_L r_H n - ((1 - M.F (asymW M r_L r_H n)) / 2 + M.F v)) +
          ((1 - M.F (asymW M r_L r_H n)) / 2 + M.F v)) *
        ((1 - M.F (asymW M r_L r_H n)) / 2 + M.F v) ^ (n - 1)) / asymAn M r_L r_H n ^ n)
      atTop (nhds 0) := by
    have hhi : Tendsto (fun n : ℕ => 2 * asymAn M r_L r_H n / (((n : ℝ) + 1) * fmin)) atTop (nhds 0) := by
      have h := hAn_lim.mul hinv_n; rw [mul_zero] at h; exact h.congr (fun n => by ring)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hhi ?_ ?_
    · filter_upwards [eventually_ge_atTop 2, hL_nn, hord_r, hcut.1, hAn_half] with n hn hLn hrLHn hcn hAn5
      set w := asymW M r_L r_H n
      have hbd := br_block_err_bounds n (by omega) (le_trans hrLHn.le hcn.1.1.le)
        (G := fun v => (1 - M.F w) / 2 + M.F v) (g := M.f)
        (continuousOn_const.add (M.F_continuousOn.mono (Icc_subset_Icc (by rw [ha]; exact hLn) hcn.1.2.le)))
        (M.hf_cont.mono (Icc_subset_Icc (by rw [ha]; exact hLn) hcn.1.2.le))
        (fun v hv => (M.hF_deriv_open v ⟨by rw [ha]; linarith [hLn, hv.1], lt_of_lt_of_le hv.2 hcn.1.2.le⟩).const_add _)
        hfmin (fun v hv => hf_lo v ⟨by rw [ha]; linarith [hLn, hv.1], le_trans hv.2 hcn.1.2.le⟩)
        (by
          have hrL_mem : r_L n ∈ Icc M.a 1 := ⟨by rw [ha]; exact hLn, by linarith [hrLHn, hcn.1.1, hcn.1.2]⟩
          have hw_mem : w ∈ Icc M.a 1 := ⟨by rw [ha]; linarith [hLn, hrLHn, hcn.1.1], hcn.1.2.le⟩
          have h1 := (M.F_mem_Icc hrL_mem).1
          have h2 := (M.F_mem_Icc hw_mem).2
          linarith)
      have hGw : (1 - M.F w) / 2 + M.F w = asymAn M r_L r_H n := by unfold asymAn asymQw; ring
      rw [hGw] at hbd
      exact div_nonneg hbd.1 (pow_pos (by linarith) n).le
    · filter_upwards [eventually_ge_atTop 2, hL_nn, hord_r, hcut.1, hAn_half] with n hn hLn hrLHn hcn hAn5
      set w := asymW M r_L r_H n
      have hAn_pos : 0 < asymAn M r_L r_H n := by linarith
      have hbd := br_block_err_bounds n (by omega) (le_trans hrLHn.le hcn.1.1.le)
        (G := fun v => (1 - M.F w) / 2 + M.F v) (g := M.f)
        (continuousOn_const.add (M.F_continuousOn.mono (Icc_subset_Icc (by rw [ha]; exact hLn) hcn.1.2.le)))
        (M.hf_cont.mono (Icc_subset_Icc (by rw [ha]; exact hLn) hcn.1.2.le))
        (fun v hv => (M.hF_deriv_open v ⟨by rw [ha]; linarith [hLn, hv.1], lt_of_lt_of_le hv.2 hcn.1.2.le⟩).const_add _)
        hfmin (fun v hv => hf_lo v ⟨by rw [ha]; linarith [hLn, hv.1], le_trans hv.2 hcn.1.2.le⟩)
        (by
          have hrL_mem : r_L n ∈ Icc M.a 1 := ⟨by rw [ha]; exact hLn, by linarith [hrLHn, hcn.1.1, hcn.1.2]⟩
          have hw_mem : w ∈ Icc M.a 1 := ⟨by rw [ha]; linarith [hLn, hrLHn, hcn.1.1], hcn.1.2.le⟩
          have h1 := (M.F_mem_Icc hrL_mem).1
          have h2 := (M.F_mem_Icc hw_mem).2
          linarith)
      have hGw : (1 - M.F w) / 2 + M.F w = asymAn M r_L r_H n := by unfold asymAn asymQw; ring
      rw [hGw] at hbd
      have hstep := div_le_div_of_nonneg_right hbd.2 (pow_pos hAn_pos n).le
      have hsimp : 2 * asymAn M r_L r_H n ^ (n + 1) / (((n : ℝ) + 1) * fmin) / asymAn M r_L r_H n ^ n =
          2 * asymAn M r_L r_H n / (((n : ℝ) + 1) * fmin) := by
        rw [pow_succ]; field_simp [(pow_pos hAn_pos n).ne', (show (0 : ℝ) < ((n : ℝ) + 1) * fmin by positivity).ne']
      linarith
  have hL7 : Tendsto (fun n : ℕ =>
      (∫ v in asymV0 M r_L r_H u n..asymVhat M r_L r_H u n,
        ((n : ℝ) * ((1 - asymThat M r_L r_H u n) - (asymQ0 M r_L r_H u n + M.F v)) +
          (asymQ0 M r_L r_H u n + M.F v)) *
        (asymQ0 M r_L r_H u n + M.F v) ^ (n - 1)) / asymAn M r_L r_H n ^ n)
      atTop (nhds 0) := by
    have hhi : Tendsto (fun n : ℕ =>
        (2 / (((n : ℝ) + 1) * fmin)) * ((1 - asymThat M r_L r_H u n) ^ n / asymAn M r_L r_H n ^ n))
        atTop (nhds 0) := by
      have h := hinv_n.mul h1T_pow; rwa [zero_mul] at h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hhi ?_ ?_
    · filter_upwards [eventually_ge_atTop 2, hγ.1, hdev.1, hAn_half] with n hn hγn hdn hAn5
      have hv0_vh : asymV0 M r_L r_H u n < asymVhat M r_L r_H u n := lt_trans hdn.2.1 hdn.2.2.1
      have hvh1 : asymVhat M r_L r_H u n < 1 := by
        linarith [hdn.2.2.2.1, hdn.2.2.2.2.1, hdn.2.2.2.2.2.1, hdn.2.2.2.2.2.2.1, hdn.2.2.2.2.2.2.2.1]
      have hbd := br_block_err_bounds n (by omega) hv0_vh.le
        (G := fun v => asymQ0 M r_L r_H u n + M.F v) (g := M.f)
        (continuousOn_const.add (M.F_continuousOn.mono (Icc_subset_Icc (by rw [ha]; exact hdn.1.le) hvh1.le)))
        (M.hf_cont.mono (Icc_subset_Icc (by rw [ha]; exact hdn.1.le) hvh1.le))
        (fun v hv => (M.hF_deriv_open v ⟨by rw [ha]; linarith [hdn.1, hv.1], by linarith [hv.2, hvh1]⟩).const_add _)
        hfmin (fun v hv => hf_lo v ⟨by rw [ha]; linarith [hdn.1, hv.1], by linarith [hv.2, hvh1]⟩)
        (by
          have hv0_mem : asymV0 M r_L r_H u n ∈ Icc M.a 1 := ⟨by rw [ha]; exact hdn.1.le, by linarith [hv0_vh, hvh1]⟩
          have := (M.F_mem_Icc hv0_mem).1
          linarith [hγn.1, hγn.2.1])
      have hGvh : asymQ0 M r_L r_H u n + M.F (asymVhat M r_L r_H u n) = 1 - asymThat M r_L r_H u n := by
        rw [hdn.2.2.2.2.2.2.2.2.2.2.1]; ring
      rw [hGvh] at hbd
      exact div_nonneg hbd.1 (pow_pos (by linarith) n).le
    · filter_upwards [eventually_ge_atTop 2, hγ.1, hdev.1, hAn_half] with n hn hγn hdn hAn5
      have hv0_vh : asymV0 M r_L r_H u n < asymVhat M r_L r_H u n := lt_trans hdn.2.1 hdn.2.2.1
      have hvh1 : asymVhat M r_L r_H u n < 1 := by
        linarith [hdn.2.2.2.1, hdn.2.2.2.2.1, hdn.2.2.2.2.2.1, hdn.2.2.2.2.2.2.1, hdn.2.2.2.2.2.2.2.1]
      have hAn_pos : 0 < asymAn M r_L r_H n := by linarith
      have hbd := br_block_err_bounds n (by omega) hv0_vh.le
        (G := fun v => asymQ0 M r_L r_H u n + M.F v) (g := M.f)
        (continuousOn_const.add (M.F_continuousOn.mono (Icc_subset_Icc (by rw [ha]; exact hdn.1.le) hvh1.le)))
        (M.hf_cont.mono (Icc_subset_Icc (by rw [ha]; exact hdn.1.le) hvh1.le))
        (fun v hv => (M.hF_deriv_open v ⟨by rw [ha]; linarith [hdn.1, hv.1], by linarith [hv.2, hvh1]⟩).const_add _)
        hfmin (fun v hv => hf_lo v ⟨by rw [ha]; linarith [hdn.1, hv.1], by linarith [hv.2, hvh1]⟩)
        (by
          have hv0_mem : asymV0 M r_L r_H u n ∈ Icc M.a 1 := ⟨by rw [ha]; exact hdn.1.le, by linarith [hv0_vh, hvh1]⟩
          have := (M.F_mem_Icc hv0_mem).1
          linarith [hγn.1, hγn.2.1])
      have hGvh : asymQ0 M r_L r_H u n + M.F (asymVhat M r_L r_H u n) = 1 - asymThat M r_L r_H u n := by
        rw [hdn.2.2.2.2.2.2.2.2.2.2.1]; ring
      rw [hGvh] at hbd
      have hstep := div_le_div_of_nonneg_right hbd.2 (pow_pos hAn_pos n).le
      have h1T_le1 : 1 - asymThat M r_L r_H u n ≤ 1 := by linarith [hγn.1, hγn.2.1, hγn.2.2.1]
      have hpow_le : (1 - asymThat M r_L r_H u n) ^ (n + 1) ≤ (1 - asymThat M r_L r_H u n) ^ n := by
        rw [pow_succ]
        exact mul_le_of_le_one_right (pow_nonneg (by linarith [hγn.2.2.2.1]) n) h1T_le1
      have hsimp : 2 * (1 - asymThat M r_L r_H u n) ^ (n + 1) / (((n : ℝ) + 1) * fmin) / asymAn M r_L r_H n ^ n ≤
          2 / (((n : ℝ) + 1) * fmin) * ((1 - asymThat M r_L r_H u n) ^ n / asymAn M r_L r_H n ^ n) := by
        have hpos : 0 < ((n : ℝ) + 1) * fmin := by positivity
        have heq : 2 / (((n : ℝ) + 1) * fmin) * ((1 - asymThat M r_L r_H u n) ^ n / asymAn M r_L r_H n ^ n) =
            2 * (1 - asymThat M r_L r_H u n) ^ n / (((n : ℝ) + 1) * fmin) / asymAn M r_L r_H n ^ n := by ring
        rw [heq]
        exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_right (by linarith) hpos.le) (pow_pos hAn_pos n).le
      linarith
  have hL8 : Tendsto (fun n : ℕ =>
      (∫ v in asymW M r_L r_H n..asymVa M r_L r_H u n,
        ((n : ℝ) * ((1 - asymQa M r_L r_H u n) - br_Ah M v) + br_Ah M v) * br_Ah M v ^ (n - 1)) /
        asymAn M r_L r_H n ^ n)
      atTop (nhds 0) := by
    have hhi : Tendsto (fun n : ℕ =>
        (2 / (((n : ℝ) + 1) * (fmin / 2))) * ((1 - asymQa M r_L r_H u n) ^ n / asymAn M r_L r_H n ^ n))
        atTop (nhds 0) := by
      have h1 : Tendsto (fun n : ℕ => 2 / (((n : ℝ) + 1) * (fmin / 2))) atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop ((tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).atTop_mul_const (by positivity))
      have h := h1.mul h1a_pow; rwa [zero_mul] at h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hhi ?_ ?_
    · filter_upwards [eventually_ge_atTop 2, hγ.1, hdev.1, hAn_half] with n hn hγn hdn hAn5
      have hw_va : asymW M r_L r_H n < asymVa M r_L r_H u n :=
        lt_trans hdn.2.2.2.2.1 (lt_trans hdn.2.2.2.2.2.1 hdn.2.2.2.2.2.2.1)
      have hw0 : 0 < asymW M r_L r_H n := by linarith [hdn.1, hdn.2.1, hdn.2.2.1, hdn.2.2.2.1]
      have hva1 : asymVa M r_L r_H u n < 1 := hdn.2.2.2.2.2.2.2.1
      have hbd := br_block_err_bounds n (by omega) hw_va.le
        (G := br_Ah M) (g := fun v => M.f v / 2)
        ((continuousOn_const.add (M.F_continuousOn.mono (Icc_subset_Icc (by rw [ha]; exact hw0.le) hva1.le))).div_const 2)
        ((M.hf_cont.mono (Icc_subset_Icc (by rw [ha]; exact hw0.le) hva1.le)).div_const 2)
        (fun v hv => ((M.hF_deriv_open v ⟨by rw [ha]; linarith [hw0, hv.1], by linarith [hv.2, hva1]⟩).const_add 1).div_const 2)
        (by positivity : 0 < fmin / 2)
        (fun v hv => by linarith [hf_lo v ⟨by rw [ha]; linarith [hw0, hv.1], by linarith [hv.2, hva1]⟩])
        (by
          have hw_mem : asymW M r_L r_H n ∈ Icc M.a 1 := ⟨by rw [ha]; exact hw0.le, by linarith [hw_va, hva1]⟩
          have := (M.F_mem_Icc hw_mem).1; unfold br_Ah; linarith)
      have hAva : br_Ah M (asymVa M r_L r_H u n) = 1 - asymQa M r_L r_H u n := by
        unfold br_Ah; rw [hdn.2.2.2.2.2.2.2.2.1]; ring
      rw [hAva] at hbd
      exact div_nonneg hbd.1 (pow_pos (by linarith) n).le
    · filter_upwards [eventually_ge_atTop 2, hγ.1, hdev.1, hAn_half] with n hn hγn hdn hAn5
      have hw_va : asymW M r_L r_H n < asymVa M r_L r_H u n :=
        lt_trans hdn.2.2.2.2.1 (lt_trans hdn.2.2.2.2.2.1 hdn.2.2.2.2.2.2.1)
      have hw0 : 0 < asymW M r_L r_H n := by linarith [hdn.1, hdn.2.1, hdn.2.2.1, hdn.2.2.2.1]
      have hva1 : asymVa M r_L r_H u n < 1 := hdn.2.2.2.2.2.2.2.1
      have hAn_pos : 0 < asymAn M r_L r_H n := by linarith
      have hbd := br_block_err_bounds n (by omega) hw_va.le
        (G := br_Ah M) (g := fun v => M.f v / 2)
        ((continuousOn_const.add (M.F_continuousOn.mono (Icc_subset_Icc (by rw [ha]; exact hw0.le) hva1.le))).div_const 2)
        ((M.hf_cont.mono (Icc_subset_Icc (by rw [ha]; exact hw0.le) hva1.le)).div_const 2)
        (fun v hv => ((M.hF_deriv_open v ⟨by rw [ha]; linarith [hw0, hv.1], by linarith [hv.2, hva1]⟩).const_add 1).div_const 2)
        (by positivity : 0 < fmin / 2)
        (fun v hv => by linarith [hf_lo v ⟨by rw [ha]; linarith [hw0, hv.1], by linarith [hv.2, hva1]⟩])
        (by
          have hw_mem : asymW M r_L r_H n ∈ Icc M.a 1 := ⟨by rw [ha]; exact hw0.le, by linarith [hw_va, hva1]⟩
          have := (M.F_mem_Icc hw_mem).1; unfold br_Ah; linarith)
      have hAva : br_Ah M (asymVa M r_L r_H u n) = 1 - asymQa M r_L r_H u n := by
        unfold br_Ah; rw [hdn.2.2.2.2.2.2.2.2.1]; ring
      rw [hAva] at hbd
      have hstep := div_le_div_of_nonneg_right hbd.2 (pow_pos hAn_pos n).le
      have h1a_le1 : 1 - asymQa M r_L r_H u n ≤ 1 := by linarith [hγn.1]
      have hpow_le : (1 - asymQa M r_L r_H u n) ^ (n + 1) ≤ (1 - asymQa M r_L r_H u n) ^ n := by
        rw [pow_succ]
        exact mul_le_of_le_one_right (pow_nonneg (by linarith [hγn.2.1, hγn.2.2.1, hγn.2.2.2.1]) n) h1a_le1
      have hpos : 0 < ((n : ℝ) + 1) * (fmin / 2) := by positivity
      have heq : 2 / (((n : ℝ) + 1) * (fmin / 2)) * ((1 - asymQa M r_L r_H u n) ^ n / asymAn M r_L r_H n ^ n) =
          2 * (1 - asymQa M r_L r_H u n) ^ n / (((n : ℝ) + 1) * (fmin / 2)) / asymAn M r_L r_H n ^ n := by ring
      have hsimp : 2 * (1 - asymQa M r_L r_H u n) ^ (n + 1) / (((n : ℝ) + 1) * (fmin / 2)) / asymAn M r_L r_H n ^ n ≤
          2 / (((n : ℝ) + 1) * (fmin / 2)) * ((1 - asymQa M r_L r_H u n) ^ n / asymAn M r_L r_H n ^ n) := by
        rw [heq]
        exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_right (by linarith) hpos.le) (pow_pos hAn_pos n).le
      linarith
  have hL9 : Tendsto (fun n : ℕ =>
      (n : ℝ) * (asymW M r_L r_H n - r_H n) * asymAn M r_L r_H n ^ (n - 1) *
        ((1 - asymQa M r_L r_H u n) - asymAn M r_L r_H n) / asymAn M r_L r_H n ^ n)
      atTop (nhds 0) := by
    have h := (hw_lim.sub hH_lim).const_mul u
    rw [sub_self, mul_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 2, hAn_half] with n hn hAn5
    have hnR : (n : ℝ) ≠ 0 := by positivity
    have hAn_pos : 0 < asymAn M r_L r_H n := by linarith
    have hAn_def : asymAn M r_L r_H n = 1 - asymQw M r_L r_H n := rfl
    have hpow : asymAn M r_L r_H n ^ n = asymAn M r_L r_H n ^ (n - 1) * asymAn M r_L r_H n := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    have hdiff : (1 - asymQa M r_L r_H u n) - asymAn M r_L r_H n = u * asymAn M r_L r_H n / (n : ℝ) := by
      unfold asymQa asymDelta; rw [hAn_def]; ring
    rw [hpow, hdiff]; field_simp [hnR, hAn_pos.ne']
  have hL10 : Tendsto (fun n : ℕ =>
      (n : ℝ) * asymQa M r_L r_H u n * (asymV2 M r_L r_H u n - r_H n) * asymBarX M r_L r_H u n /
        asymAn M r_L r_H n ^ n)
      atTop (nhds (((1 - M.F rH) / (2 * M.f rH)) * ((1 + u - br_gamma u) * Real.exp (-br_gamma u)))) := by
    have h := (hqa_lim.mul hv2r_lim).mul hbarx_lim
    rw [show (1 - M.F rH) / 2 * ((1 + u - br_gamma u) / M.f rH) * Real.exp (-br_gamma u) =
      ((1 - M.F rH) / (2 * M.f rH)) * ((1 + u - br_gamma u) * Real.exp (-br_gamma u)) by ring] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 2, hAn_half] with n hn hAn5
    have hnR : (n : ℝ) ≠ 0 := by positivity
    have hAn_pos : 0 < asymAn M r_L r_H n := by linarith
    have hpow : asymAn M r_L r_H n ^ n = asymAn M r_L r_H n ^ (n - 1) * asymAn M r_L r_H n := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    rw [hpow]; unfold asymDelta; field_simp [hnR, hAn_pos.ne']
  have hL11 : Tendsto (fun n : ℕ =>
      (n : ℝ) * asymQa M r_L r_H u n * (asymW M r_L r_H n - r_H n) * asymAn M r_L r_H n ^ (n - 1) /
        asymAn M r_L r_H n ^ n)
      atTop (nhds ((1 - M.F rH) / (2 * M.f rH))) := by
    have h := hqa_lim.mul hwr_lim
    rw [show (1 - M.F rH) / 2 * (1 / M.f rH) = (1 - M.F rH) / (2 * M.f rH) by ring] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 2, hAn_half] with n hn hAn5
    have hnR : (n : ℝ) ≠ 0 := by positivity
    have hAn_pos : 0 < asymAn M r_L r_H n := by linarith
    have hpow : asymAn M r_L r_H n ^ n = asymAn M r_L r_H n ^ (n - 1) * asymAn M r_L r_H n := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    rw [hpow]; unfold asymDelta; field_simp [hnR, hAn_pos.ne']
  have hL12 : Tendsto (fun n : ℕ =>
      (n : ℝ) * asymQa M r_L r_H u n *
        (∫ t in asymV2 M r_L r_H u n..asymVa M r_L r_H u n, (asymQa M r_L r_H u n + M.F t) ^ (n - 1)) /
        asymAn M r_L r_H n ^ n)
      atTop (nhds (((1 - M.F rH) / (2 * M.f rH)) * (Real.exp u - Real.exp (-br_gamma u)))) := by
    have hI := br_pow_int_tendsto M ha one_pos (by linarith) hrH1 hAnH_pos hv2_lim hva_lim hAn_lim
      (c_seq := asymQa M r_L r_H u)
      (by
        filter_upwards [hγ.1, hdev.1] with n hγn hdn
        have hv2_0 : 0 < asymV2 M r_L r_H u n := by linarith [hdn.1, hdn.2.1, hdn.2.2.1, hdn.2.2.2.1, hdn.2.2.2.2.1]
        have hv2_va : asymV2 M r_L r_H u n < asymVa M r_L r_H u n := lt_trans hdn.2.2.2.2.2.1 hdn.2.2.2.2.2.2.1
        have hv2_mem : asymV2 M r_L r_H u n ∈ Icc M.a 1 := ⟨by rw [ha]; exact hv2_0.le, le_trans hv2_va.le hdn.2.2.2.2.2.2.2.1.le⟩
        have hFnn := (M.F_mem_Icc hv2_mem).1
        exact ⟨hv2_0, hv2_va.le, hdn.2.2.2.2.2.2.2.1, by linarith [hγn.1, hFnn]⟩)
      (by
        refine (h1a_pow.sub h1q0_pow).congr' ?_
        filter_upwards [hdev.1] with n hdn
        simp only [one_mul, hdn.2.2.2.2.2.2.2.2.1, hdn.2.2.2.2.2.2.2.2.2.1]
        rw [← sub_div]; congr 1; ring)
    have h := hqa_lim.mul hI
    rw [one_mul, show (1 - M.F rH) / 2 * ((Real.exp u - Real.exp (-br_gamma u)) / M.f rH) =
      ((1 - M.F rH) / (2 * M.f rH)) * (Real.exp u - Real.exp (-br_gamma u)) by ring] at h
    exact h.congr (fun n => by simp only [one_mul]; ring)
  have hL13 : Tendsto (fun n : ℕ =>
      (n : ℝ) * asymQa M r_L r_H u n *
        (∫ t in asymW M r_L r_H n..asymVa M r_L r_H u n, br_Ah M t ^ (n - 1)) /
        asymAn M r_L r_H n ^ n)
      atTop (nhds (((1 - M.F rH) / (2 * M.f rH)) * (2 * (Real.exp u - 1)))) := by
    have hI := br_pow_int_tendsto M ha (by norm_num : (0 : ℝ) < 1 / 2) (by linarith) hrH1 hAnH_pos
      hw_lim hva_lim hAn_lim
      (c_seq := fun _ => (1 / 2 : ℝ))
      (by
        filter_upwards [hdev.1] with n hdn
        have hw0 : 0 < asymW M r_L r_H n := by linarith [hdn.1, hdn.2.1, hdn.2.2.1, hdn.2.2.2.1]
        have hw_va : asymW M r_L r_H n < asymVa M r_L r_H u n :=
          lt_trans hdn.2.2.2.2.1 (lt_trans hdn.2.2.2.2.2.1 hdn.2.2.2.2.2.2.1)
        have hw_mem : asymW M r_L r_H n ∈ Icc M.a 1 := ⟨by rw [ha]; exact hw0.le, le_trans hw_va.le hdn.2.2.2.2.2.2.2.1.le⟩
        have hFnn := (M.F_mem_Icc hw_mem).1
        exact ⟨hw0, hw_va.le, hdn.2.2.2.2.2.2.2.1, by linarith⟩)
      (by
        refine (h1a_pow.sub (tendsto_const_nhds (x := (1 : ℝ)))).congr' ?_
        filter_upwards [hdev.1, hAn_half] with n hdn hAn5
        have hAn_pos : 0 < asymAn M r_L r_H n := by linarith
        have h1 : (1 / 2 : ℝ) + 1 / 2 * M.F (asymVa M r_L r_H u n) = 1 - asymQa M r_L r_H u n := by
          rw [hdn.2.2.2.2.2.2.2.2.1]; ring
        have h2 : (1 / 2 : ℝ) + 1 / 2 * M.F (asymW M r_L r_H n) = asymAn M r_L r_H n := by
          unfold asymAn asymQw; ring
        rw [h1, h2, sub_div, div_self (pow_pos hAn_pos n).ne'])
    have h := hqa_lim.mul hI
    rw [show (1 - M.F rH) / 2 * ((Real.exp u - 1) / (1 / 2 * M.f rH)) =
      ((1 - M.F rH) / (2 * M.f rH)) * (2 * (Real.exp u - 1)) by ring] at h
    exact h.congr (fun n => by
      have hint_eq : (∫ t in asymW M r_L r_H n..asymVa M r_L r_H u n, ((1 / 2 : ℝ) + 1 / 2 * M.F t) ^ (n - 1)) =
          ∫ t in asymW M r_L r_H n..asymVa M r_L r_H u n, br_Ah M t ^ (n - 1) := by
        congr 1; ext t; unfold br_Ah; ring
      rw [hint_eq]; ring)
  -- Combine all 13 limits!
  have hcomb := (((((((((((hL1.add hL2).sub hL3).add hL4).add hL5).add hL6).sub hL7).add hL8).add hL9).sub hL10).add hL11).sub hL12).add hL13
  have hval :
      0 + 0 - rH * Real.exp (-u) + rH * ((1 - u - br_gamma u) * Real.exp (-br_gamma u)) + 0 + 0 - 0 + 0 + 0 -
        ((1 - M.F rH) / (2 * M.f rH)) * ((1 + u - br_gamma u) * Real.exp (-br_gamma u)) +
        (1 - M.F rH) / (2 * M.f rH) -
        ((1 - M.F rH) / (2 * M.f rH)) * (Real.exp u - Real.exp (-br_gamma u)) +
        ((1 - M.F rH) / (2 * M.f rH)) * (2 * (Real.exp u - 1)) =
      rH * ((1 - u - br_gamma u) * Real.exp (-br_gamma u) - Real.exp (-u)) +
        ((1 - M.F rH) / (2 * M.f rH)) * ((br_gamma u - u) * Real.exp (-br_gamma u) + Real.exp u - 1) := by ring
  rw [hval] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [eventually_ge_atTop 2, hL_nn, hord_r, hcut.1, hγ.1, hdev.1] with n hn hLn hrLHn hcn hγn hdn
  have hbal_w : ∫ v in r_L n..asymW M r_L r_H n, ((1 - M.F (asymW M r_L r_H n)) / 2 + M.F v) ^ (n - 1) =
      (asymW M r_L r_H n - r_H n) * br_Ah M (asymW M r_L r_H n) ^ (n - 1) := by
    have := hcn.2.2; rw [br_A_eq M hm] at this; exact this
  have hbal_β : (asymBeta M r_L r_H u n - r_H n) * asymBarX M r_L r_H u n +
      (asymVa M r_L r_H u n - asymBeta M r_L r_H u n) * (1 - asymQa M r_L r_H u n) ^ (n - 1) =
      (asymV2 M r_L r_H u n - r_H n) * asymBarX M r_L r_H u n +
        ∫ t in asymV2 M r_L r_H u n..asymVa M r_L r_H u n, (asymQa M r_L r_H u n + M.F t) ^ (n - 1) := by
    have hv2_va : asymV2 M r_L r_H u n < asymVa M r_L r_H u n := lt_trans hdn.2.2.2.2.2.1 hdn.2.2.2.2.2.2.1
    have hden : (1 - asymQa M r_L r_H u n) ^ (n - 1) - asymBarX M r_L r_H u n ≠ 0 := by
      rw [← hγn.2.2.2.2.1]
      have := pow_lt_pow_left₀ (show 1 - asymQ0 M r_L r_H u n < 1 - asymQa M r_L r_H u n by linarith [hγn.2.1])
        (by linarith [hγn.2.2.1, hγn.2.2.2.1]) (by omega : n - 1 ≠ 0)
      linarith
    have h1 : (asymVa M r_L r_H u n - asymBeta M r_L r_H u n) * ((1 - asymQa M r_L r_H u n) ^ (n - 1) - asymBarX M r_L r_H u n) =
        ∫ t in asymV2 M r_L r_H u n..asymVa M r_L r_H u n, ((asymQa M r_L r_H u n + M.F t) ^ (n - 1) - asymBarX M r_L r_H u n) := by
      have hβd : asymVa M r_L r_H u n - asymBeta M r_L r_H u n =
          (∫ t in asymV2 M r_L r_H u n..asymVa M r_L r_H u n, ((asymQa M r_L r_H u n + M.F t) ^ (n - 1) - asymBarX M r_L r_H u n)) /
            ((1 - asymQa M r_L r_H u n) ^ (n - 1) - asymBarX M r_L r_H u n) := by unfold asymBeta; ring
      rw [hβd, div_mul_cancel₀ _ hden]
    have hFc : ContinuousOn M.F (Icc (asymV2 M r_L r_H u n) (asymVa M r_L r_H u n)) :=
      M.F_continuousOn.mono (Icc_subset_Icc (by rw [ha]; linarith [hdn.1, hdn.2.1, hdn.2.2.1, hdn.2.2.2.1, hdn.2.2.2.2.1]) hdn.2.2.2.2.2.2.2.1.le)
    have hint_FH : IntervalIntegrable (fun t => (asymQa M r_L r_H u n + M.F t) ^ (n - 1)) volume
        (asymV2 M r_L r_H u n) (asymVa M r_L r_H u n) :=
      (((continuousOn_const.add hFc).pow _).mono (by rw [uIcc_of_le hv2_va.le])).intervalIntegrable
    rw [intervalIntegral.integral_sub hint_FH intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul] at h1
    linarith only [h1]
  have hgain := br_asymRevGain_eq M hm ha hn hLn hrLHn hdn.1 hdn.2.1 hdn.2.2.1 hdn.2.2.2.1
    hdn.2.2.2.2.1 hdn.2.2.2.2.2.1 hdn.2.2.2.2.2.2.1 hdn.2.2.2.2.2.2.2.1
    (lt_trans hγn.2.1 hγn.2.2.1) hdn.2.2.2.2.2.2.2.2.1 hdn.2.2.2.2.2.2.2.2.2.1
    hdn.2.2.2.2.2.2.2.2.2.2.1 hγn.2.2.2.2.1 hbal_w hdn.2.2.2.2.2.2.2.2.2.2.2 hbal_β
  dsimp only
  rw [hgain]
  have hAn_def : 1 - asymQw M r_L r_H n = asymAn M r_L r_H n := rfl
  rw [hAn_def]
  ring

/-- **Theorem 4 (Failure of Asymmetric Duopoly Pure-Reserve Equilibrium for Large `n`)**:
Fix `m = 2`, `a = 0`, and sequences `r_L n → rL`, `r_H n → rH` with `0 ≤ rL < rH < 1` and
`M.psi1 rH < 0`. Then:
1. Small-`u` Taylor expansion of the eq. (22) limit:
   `br_asymLimit M rH u = -(u^2 / 6) * M.psi1 rH + O(u^4)` (and when `M.psi rH = 0`,
   `br_asymLimit M rH u = rH * (sinh u / u - 1)` for all `u > 0`).
2. There exists a feasible `u > 0` such that for all sufficiently large `n`:
   - `asymBaseVisit` is SR for `(SPA(r_L n), SPA(r_H n))`,
   - `asymDevVisit` is SR for `(asymDevMech, SPA(r_H n))`, and
   - seller `0` strictly gains revenue by deviating from `SPA(r_L n)` to `asymDevMech`. -/
theorem theorem4_asymmetric_duopoly_fails (M : Market) (hm : M.m = 2) (ha : M.a = 0)
    {r_L r_H : ℕ → ℝ} {rL rH : ℝ} (hrL0 : 0 ≤ rL) (hrLH : rL < rH) (hrH1 : rH < 1)
    (hL_lim : Tendsto r_L atTop (nhds rL)) (hH_lim : Tendsto r_H atTop (nhds rH))
    (hL_nn : ∀ᶠ n in atTop, 0 ≤ r_L n) (hpsi1 : M.psi1 rH < 0) :
    (∃ C ≥ 0, ∀ u ∈ Ioc (0 : ℝ) (1 / 2),
      |br_asymLimit M rH u - (-(u ^ 2 / 6) * M.psi1 rH)| ≤ C * u ^ 4) ∧
    (M.psi rH = 0 → ∀ u > 0, br_asymLimit M rH u = rH * (Real.sinh u / u - 1)) ∧
    ∃ u > 0, ∀ᶠ n : ℕ in atTop,
      let Mn := M.br_atN n
      IsSR Mn (fun j => if j = seller0 Mn then br_spa (r_L n) else br_spa (r_H n))
        (asymBaseVisit Mn (asymW M r_L r_H n)) ∧
      IsSR Mn (fun j => if j = seller0 Mn then asymDevMech M r_L r_H u n else br_spa (r_H n))
        (asymDevVisit Mn r_L r_H u n) ∧
      sellerRev Mn (br_spa (r_L n)) (asymBaseVisit Mn (asymW M r_L r_H n)) (seller0 Mn) <
        sellerRev Mn (asymDevMech M r_L r_H u n) (asymDevVisit Mn r_L r_H u n) (seller0 Mn) := by
  obtain ⟨C₁, hC₁, C₂, hC₂, htay⟩ := br_asymLimit_taylor M rH
  refine ⟨⟨|rH| * C₁ + |(1 - M.F rH) / (2 * M.f rH)| * C₂, by positivity, fun u hu => (htay u hu).2.2⟩,
    fun hpsi u hu => br_asymLimit_psi2_zero M hm hu hpsi, ?_⟩
  obtain ⟨u, hu, huγ, hfeas, hlim_pos⟩ := br_exists_good_u M hpsi1
  have hsr := theorem4_deviation_sr M hm ha hrL0 hrLH hrH1 hL_lim hH_lim hL_nn hu huγ hfeas
  have hrev := theorem4_revenue_limit M hm ha hrL0 hrLH hrH1 hL_lim hH_lim hL_nn hu huγ hfeas
  have hcut := theorem4_cutoff_asymptotics M hm ha hrL0 hrLH hrH1 hL_lim hH_lim hL_nn
  have hAn_pos_ev : ∀ᶠ n : ℕ in atTop, 0 < 1 - asymQw M r_L r_H n := by
    have hF_w : Tendsto (fun n => M.F (asymW M r_L r_H n)) atTop (nhds (M.F rH)) :=
      (M.F_continuousOn.continuousAt (Icc_mem_nhds (by rw [ha]; linarith) hrH1)).tendsto.comp hcut.2.1
    have hAn_lim : Tendsto (fun n => 1 - asymQw M r_L r_H n) atTop (nhds (1 - (1 - M.F rH) / 2)) :=
      tendsto_const_nhds.sub ((tendsto_const_nhds.sub hF_w).div_const 2)
    have hFH_pos : 0 < M.F rH := by
      rw [← M.hF_a]; exact M.F_strictMonoOn (left_mem_Icc.mpr M.ha1.le) ⟨by rw [ha]; linarith, hrH1.le⟩ (by rw [ha]; linarith)
    exact hAn_lim.eventually (Ioi_mem_nhds (by linarith : (0 : ℝ) < 1 - (1 - M.F rH) / 2))
  refine ⟨u, hu, ?_⟩
  filter_upwards [hsr, hrev.eventually (Ioi_mem_nhds hlim_pos), hAn_pos_ev] with n hsrn hgt hAnpos
  refine ⟨hsrn.1, hsrn.2, ?_⟩
  have hpos_pow : 0 < (1 - asymQw M r_L r_H n) ^ n := pow_pos hAnpos n
  have hdiff := (div_pos_iff_of_pos_right hpos_pow).mp hgt
  linarith

end Theorem4

end AuctionCompetition
