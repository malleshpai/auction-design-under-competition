import AuctionCompetition.Defs
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Topology.Order.IntermediateValue

/-!
# Auction Design under Competition: The Visit Stage (Section 3 & Appendix A)

Formalizes Section 3 and Appendix A of Mallesh M. Pai,
*Auction Design under Competition* (`paper/auction-design-under-competition.tex`):

1. **Proposition 1 (`prop1_*`)**: Standard auctions `SPA(r_j)` form a potential game
   with concave potential `Φ(θ) = ∑_j ∫_{r_j}^1 (1 - F_j(v)^n) dv`, directional derivative
   `n ∑_j ∫_a^1 (θ'_j - θ_j) s_j f dv`, characterization `IsSR ↔ maximizes Φ`, uniqueness of
   effective distributions on `[r_j, 1]`, symmetric split `F_j = A` under common reserve `ρ`,
   and existence, uniqueness, continuity, and monotonicity of the cutoff `w(r₁)` for
   `r₁ > ρ` (eq. (12)) and `r₁ < ρ` (eq. (13)).

2. **Proposition 2(i)–(iii) & Lemma A.4 (`prop2_*`)**: Against rivals at `SPA(ρ)` and seller 1
   at any hierarchical mechanism `(r₁, P)`:
   - (i) Rival symmetry (`F_riv` coincides across all rivals on `[ρ, 1]`).
   - (ii) Uniqueness of `(F₁, F_riv)` via 1D sign propagation of `(ΔF, Δσ)` across gaps and pools.
   - (iii) Localization: uniform split outside finitely many intervals where `θ₁ ∈ {0, 1}` a.e.,
     and strict preference `σ > 0` on at most one initial interval starting at `max (min r₁ ρ) a`
     (only possible when `r₁ < ρ`).
   *(Note: General existence of SR visit strategies for arbitrary mechanism profiles relies on
   Glicksberg's infinite-dimensional fixed-point theorem, which is not yet in Mathlib and is
   therefore omitted; all main theorems either hold for every SR continuation or explicitly
   construct SR splits without invoking Glicksberg.)*

3. **Lemma 1 & Lemma A.5 (`lemma1_*`)**: Single interior pool band structure
   (`v₁ < α < v₂ < v₃ < β < v₄`, served mass `(F(v₄) - F(v₁)) / m`, rival quantile `q*`
   satisfying eq. (5), pool endpoint formulas eq. (15), `n = 2` exact midpoint formula,
   top-reaching bands `v₄ = 1`, and bijection between interior pools and interior bands).
-/

open MeasureTheory Set Filter Topology
open scoped Classical

namespace AuctionCompetition

instance (M : Market) : NeZero M.m := ⟨by have := M.hm; omega⟩

/-! ### Part 0: Foundational Properties of Markets, Effective Distributions, and Allocations -/

section Foundation

variable (M : Market)

lemma Market.F_continuousOn_Iic : ContinuousOn M.F (Iic 1) := by
  intro v hv
  by_cases hva : v < M.a
  · have hnhds : Iio M.a ∈ 𝓝[Iic 1] v :=
      nhdsWithin_le_nhds (isOpen_Iio.mem_nhds hva)
    exact (continuousWithinAt_const (b := (0 : ℝ))).congr_of_eventuallyEq
      (Filter.eventually_of_mem hnhds fun x hx => M.hF_below x (le_of_lt hx))
      (M.hF_below v (le_of_lt hva))
  · push Not at hva
    by_cases hveq : v = M.a
    · subst hveq
      have hleft : ContinuousWithinAt M.F (Iic M.a) M.a :=
        (continuousWithinAt_const (b := (0 : ℝ))).congr
          (fun x hx => M.hF_below x hx) M.hF_a
      have hright : ContinuousWithinAt M.F (Icc M.a 1) M.a :=
        M.F_continuousOn M.a (left_mem_Icc.mpr M.ha1.le)
      have hunion : Iic (1 : ℝ) = Iic M.a ∪ Icc M.a 1 := by
        ext x; simp only [mem_Iic, mem_union, mem_Icc]
        constructor
        · intro hx; rcases le_total x M.a with h | h; exact Or.inl h; exact Or.inr ⟨h, hx⟩
        · rintro (h | ⟨_, h⟩); exact h.trans M.ha1.le; exact h
      rw [hunion]
      exact hleft.union hright
    · have hlt : M.a < v := lt_of_le_of_ne hva (Ne.symm hveq)
      have hsub : Icc M.a 1 ∈ 𝓝[Iic 1] v := by
        rw [mem_nhdsWithin]
        refine ⟨Ioi M.a, isOpen_Ioi, hlt, ?_⟩
        intro x ⟨hx1, hx2⟩
        exact ⟨le_of_lt hx1, hx2⟩
      exact (M.F_continuousOn v ⟨hva, hv⟩).mono_of_mem_nhdsWithin hsub

lemma Market.F_monotoneOn_Iic : MonotoneOn M.F (Iic 1) := by
  intro x hx y hy hxy
  by_cases hxa : x ≤ M.a
  · rw [M.hF_below x hxa]
    by_cases hya : y ≤ M.a
    · rw [M.hF_below y hya]
    · exact (M.F_mem_Icc ⟨le_of_not_ge hya, hy⟩).1
  · push Not at hxa
    exact M.F_strictMonoOn.monotoneOn ⟨hxa.le, hx⟩ ⟨hxa.le.trans hxy, hy⟩ hxy

lemma Market.F_mem_Icc_Iic {v : ℝ} (hv : v ≤ 1) : M.F v ∈ Icc (0 : ℝ) 1 := by
  by_cases hva : v ≤ M.a
  · rw [M.hF_below v hva]; exact ⟨le_refl 0, zero_le_one⟩
  · exact M.F_mem_Icc ⟨le_of_not_ge hva, hv⟩

lemma Market.f_nonneg_Iic {v : ℝ} (hv : v ≤ 1) : 0 ≤ M.f v := by
  by_cases hva : v < M.a
  · rw [M.hf_below v hva]
  · exact (M.hf_pos v ⟨le_of_not_gt hva, hv⟩).le

lemma Market.f_bddAbove : ∃ B : ℝ, 0 < B ∧ ∀ v ≤ 1, M.f v ≤ B := by
  obtain ⟨B₀, hB₀⟩ := isCompact_Icc.bddAbove_image M.hf_cont
  refine ⟨max B₀ 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun v hv => ?_⟩
  by_cases hva : v < M.a
  · rw [M.hf_below v hva]; exact le_trans zero_le_one (le_max_right _ _)
  · exact le_trans (hB₀ ⟨v, ⟨le_of_not_gt hva, hv⟩, rfl⟩) (le_max_left _ _)

lemma Market.f_intervalIntegrable {u v : ℝ} (hu : u ≤ 1) (hv : v ≤ 1) :
    IntervalIntegrable M.f volume u v := by
  suffices h : ∀ x y : ℝ, x ≤ y → y ≤ 1 → IntervalIntegrable M.f volume x y by
    rcases le_total u v with hle | hle
    · exact h u v hle hv
    · exact (h v u hle hu).symm
  intro x y hxy hy1
  by_cases hya : y ≤ M.a
  · exact (intervalIntegrable_const (c := (0 : ℝ))).congr_ae
      (by
        change ∀ᵐ t ∂(volume.restrict (uIoc x y)), (0 : ℝ) = M.f t
        rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
        have hne : ∀ᵐ t ∂volume, t ≠ y := by simp [ae_iff, measure_singleton]
        filter_upwards [hne] with t ht hmem
        rw [uIoc_of_le hxy] at hmem
        exact (M.hf_below t (lt_of_lt_of_le (lt_of_le_of_ne hmem.2 ht) hya)).symm)
  · push Not at hya
    by_cases hxa : M.a ≤ x
    · exact (M.hf_cont.mono (by
        rw [uIcc_of_le hxy]; exact Icc_subset_Icc hxa hy1)).intervalIntegrable
    · push Not at hxa
      have h1 : IntervalIntegrable M.f volume x M.a :=
        (intervalIntegrable_const (c := (0 : ℝ))).congr_ae
          (by
            change ∀ᵐ t ∂(volume.restrict (uIoc x M.a)), (0 : ℝ) = M.f t
            rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
            have hne : ∀ᵐ t ∂volume, t ≠ M.a := by simp [ae_iff, measure_singleton]
            filter_upwards [hne] with t ht hmem
            rw [uIoc_of_le hxa.le] at hmem
            exact (M.hf_below t (lt_of_le_of_ne hmem.2 ht)).symm)
      have h2 : IntervalIntegrable M.f volume M.a y :=
        (M.hf_cont.mono (by
          rw [uIcc_of_le hya.le]; exact Icc_subset_Icc le_rfl hy1)).intervalIntegrable
      exact h1.trans h2

lemma Market.integral_f {u v : ℝ} (hu : u ≤ 1) (hv : v ≤ 1) :
    ∫ t in u..v, M.f t = M.F v - M.F u := by
  suffices h : ∀ x y : ℝ, x ≤ y → y ≤ 1 → ∫ t in x..y, M.f t = M.F y - M.F x by
    rcases le_total u v with hle | hle
    · exact h u v hle hv
    · rw [intervalIntegral.integral_symm, h v u hle hu]; ring
  intro x y hxy hy1
  by_cases hya : y ≤ M.a
  · rw [M.hF_below y hya, M.hF_below x (hxy.trans hya), sub_self]
    have hcongr : ∫ t in x..y, M.f t = ∫ _ in x..y, (0 : ℝ) := by
      apply intervalIntegral.integral_congr_ae
      have hne : ∀ᵐ t ∂volume, t ≠ y := by simp [ae_iff, measure_singleton]
      filter_upwards [hne] with t ht hmem
      rw [uIoc_of_le hxy] at hmem
      exact M.hf_below t (lt_of_lt_of_le (lt_of_le_of_ne hmem.2 ht) hya)
    rw [hcongr]; simp
  · push Not at hya
    by_cases hxa : M.a ≤ x
    · exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hxy
        (M.F_continuousOn.mono (Icc_subset_Icc hxa hy1))
        (fun t ht => M.hF_deriv_open t ⟨lt_of_le_of_lt hxa ht.1, lt_of_lt_of_le ht.2 hy1⟩)
        (M.f_intervalIntegrable (hxy.trans hy1) hy1)
    · push Not at hxa
      have h1 : ∫ t in x..M.a, M.f t = 0 := by
        have hcongr : ∫ t in x..M.a, M.f t = ∫ _ in x..M.a, (0 : ℝ) := by
          apply intervalIntegral.integral_congr_ae
          have hne : ∀ᵐ t ∂volume, t ≠ M.a := by simp [ae_iff, measure_singleton]
          filter_upwards [hne] with t ht hmem
          rw [uIoc_of_le hxa.le] at hmem
          exact M.hf_below t (lt_of_le_of_ne hmem.2 ht)
        rw [hcongr]; simp
      have h2 : ∫ t in M.a..y, M.f t = M.F y - M.F M.a :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hya.le
          (M.F_continuousOn.mono (Icc_subset_Icc le_rfl hy1))
          (fun t ht => M.hF_deriv_open t ⟨ht.1, lt_of_lt_of_le ht.2 hy1⟩)
          (M.f_intervalIntegrable M.ha1.le hy1)
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (M.f_intervalIntegrable (hxy.trans hy1) M.ha1.le)
        (M.f_intervalIntegrable M.ha1.le hy1), h1, h2, zero_add, M.hF_a, M.hF_below x hxa.le]

lemma Market.A_mem_Icc {v : ℝ} (hv : v ≤ 1) : M.A v ∈ Icc (0 : ℝ) 1 := by
  unfold Market.A
  have hF := M.F_mem_Icc_Iic hv
  have hm : (2 : ℝ) ≤ M.m := by exact_mod_cast M.hm
  have hmpos : (0 : ℝ) < M.m := by linarith
  constructor
  · have : (1 - M.F v) / M.m ≤ 1 := by
      rw [div_le_one hmpos]; linarith [hF.1]
    linarith
  · have : 0 ≤ (1 - M.F v) / M.m := div_nonneg (by linarith [hF.2]) hmpos.le
    linarith

lemma Market.A_pos {v : ℝ} (hv : v ≤ 1) : 0 < M.A v := by
  unfold Market.A
  have hF := M.F_mem_Icc_Iic hv
  have hm : (2 : ℝ) ≤ M.m := by exact_mod_cast M.hm
  have hmpos : (0 : ℝ) < M.m := by linarith
  have : (1 - M.F v) / M.m < 1 := by
    rw [div_lt_one hmpos]; linarith [hF.1]
  linarith

lemma Market.A_one : M.A 1 = 1 := by
  simp [Market.A, M.hF_1]

lemma Market.A_continuousOn_Iic : ContinuousOn M.A (Iic 1) := by
  unfold Market.A
  exact continuousOn_const.sub ((continuousOn_const.sub M.F_continuousOn_Iic).div_const _)

lemma Market.A_strictMonoOn : StrictMonoOn M.A (Icc M.a 1) := by
  intro x hx y hy hxy
  unfold Market.A
  have hF := M.F_strictMonoOn hx hy hxy
  have hmpos : (0 : ℝ) < M.m := M.m_pos_real
  have : (1 - M.F y) / M.m < (1 - M.F x) / M.m := div_lt_div_of_pos_right (by linarith) hmpos
  linarith

lemma Market.A_hasDerivAt_open {v : ℝ} (hv : v ∈ Ioo M.a 1) :
    HasDerivAt M.A (M.f v / M.m) v := by
  have h1 : HasDerivAt (fun x => 1 - (1 - M.F x) / M.m) (0 - (0 - M.f v) / M.m) v :=
    (hasDerivAt_const v (1 : ℝ)).sub
      (((hasDerivAt_const v (1 : ℝ)).sub (M.hF_deriv_open v hv)).div_const _)
  have heq : (0 : ℝ) - (0 - M.f v) / M.m = M.f v / M.m := by ring
  rw [heq] at h1
  exact h1

lemma VisitStrategy.le_one {M : Market} (θ : VisitStrategy M) (j : Fin M.m)
    {v : ℝ} (hv : v ∈ Icc M.a 1) : θ.θ j v ≤ 1 := by
  have hsum := θ.hsum v hv
  have hle : θ.θ j v ≤ ∑ k : Fin M.m, θ.θ k v :=
    Finset.single_le_sum (fun k _ => θ.hnonneg k v) (Finset.mem_univ j)
  linarith

lemma VisitStrategy.mul_f_intervalIntegrable {M : Market} (θ : VisitStrategy M) (j : Fin M.m)
    {u v : ℝ} (hu : u ≤ 1) (hv : v ≤ 1) :
    IntervalIntegrable (fun t => θ.θ j t * M.f t) volume u v := by
  suffices h : ∀ x y : ℝ, x ≤ y → y ≤ 1 →
      IntegrableOn (fun t => θ.θ j t * M.f t) (Ioc x y) volume by
    constructor
    · rcases le_total u v with hle | hle
      · exact h u v hle hv
      · rw [Ioc_eq_empty (not_lt.mpr hle)]; exact integrableOn_empty
    · rcases le_total v u with hle | hle
      · exact h v u hle hu
      · rw [Ioc_eq_empty (not_lt.mpr hle)]; exact integrableOn_empty
  intro x y hxy hy1
  have hf_int : IntegrableOn M.f (Ioc x y) volume := (M.f_intervalIntegrable (hxy.trans hy1) hy1).1
  have hmeas : AEStronglyMeasurable (fun t => θ.θ j t * M.f t) (volume.restrict (Ioc x y)) :=
    (θ.hmeas j).aestronglyMeasurable.mul hf_int.aestronglyMeasurable
  refine Integrable.mono' hf_int hmeas ?_
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
  refine Filter.Eventually.of_forall fun t ht => ?_
  have ht1 : t ≤ 1 := ht.2.trans hy1
  by_cases hta : t < M.a
  · rw [M.hf_below t hta, mul_zero, norm_zero]
  · have hmem : t ∈ Icc M.a 1 := ⟨le_of_not_gt hta, ht1⟩
    have h1 : 0 ≤ θ.θ j t * M.f t := mul_nonneg (θ.hnonneg j t) (M.f_nonneg_Iic ht1)
    rw [Real.norm_of_nonneg h1]
    exact mul_le_of_le_one_left (M.f_nonneg_Iic ht1) (θ.le_one j hmem)

lemma vs_effDist_one {M : Market} (θ : VisitStrategy M) (j : Fin M.m) :
    effDist M θ j 1 = 1 := by
  simp [effDist]

lemma effDist_sub {M : Market} (θ : VisitStrategy M) (j : Fin M.m)
    {u v : ℝ} (hu : u ≤ 1) (hv : v ≤ 1) :
    effDist M θ j v - effDist M θ j u = ∫ t in u..v, θ.θ j t * M.f t := by
  unfold effDist
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (θ.mul_f_intervalIntegrable j hu hv) (θ.mul_f_intervalIntegrable j hv le_rfl)
  linarith

lemma effDist_le_F_diff {M : Market} (θ : VisitStrategy M) (j : Fin M.m)
    {u v : ℝ} (huv : u ≤ v) (hv : v ≤ 1) :
    0 ≤ effDist M θ j v - effDist M θ j u ∧ effDist M θ j v - effDist M θ j u ≤ M.F v - M.F u := by
  rw [effDist_sub θ j (huv.trans hv) hv, ← M.integral_f (huv.trans hv) hv]
  constructor
  · apply intervalIntegral.integral_nonneg huv
    intro t ht
    exact mul_nonneg (θ.hnonneg j t) (M.f_nonneg_Iic (ht.2.trans hv))
  · apply intervalIntegral.integral_mono_on huv
      (θ.mul_f_intervalIntegrable j (huv.trans hv) hv) (M.f_intervalIntegrable (huv.trans hv) hv)
    intro t ht
    by_cases hta : t < M.a
    · rw [M.hf_below t hta, mul_zero]
    · exact mul_le_of_le_one_left (M.f_nonneg_Iic (ht.2.trans hv))
        (θ.le_one j ⟨le_of_not_gt hta, ht.2.trans hv⟩)

lemma vs_effDist_monotoneOn {M : Market} (θ : VisitStrategy M) (j : Fin M.m) :
    MonotoneOn (effDist M θ j) (Iic 1) := by
  intro u _ v hv huv
  linarith [(effDist_le_F_diff θ j huv hv).1]

lemma effDist_const_below_a {M : Market} (θ : VisitStrategy M) (j : Fin M.m)
    {v : ℝ} (hv : v ≤ M.a) : effDist M θ j v = effDist M θ j M.a := by
  have h := effDist_le_F_diff θ j hv M.ha1.le
  rw [M.hF_a, M.hF_below v hv, sub_self] at h
  linarith

lemma vs_effDist_mem_Icc {M : Market} (θ : VisitStrategy M) (j : Fin M.m)
    {v : ℝ} (hv : v ≤ 1) : effDist M θ j v ∈ Icc (M.F v) 1 := by
  have h := effDist_le_F_diff θ j hv le_rfl
  rw [vs_effDist_one, M.hF_1] at h
  constructor <;> linarith

lemma effDist_nonneg {M : Market} (θ : VisitStrategy M) (j : Fin M.m)
    {v : ℝ} (hv : v ≤ 1) : 0 ≤ effDist M θ j v :=
  le_trans (M.F_mem_Icc_Iic hv).1 (vs_effDist_mem_Icc θ j hv).1

lemma effDist_le_one {M : Market} (θ : VisitStrategy M) (j : Fin M.m)
    {v : ℝ} (hv : v ≤ 1) : effDist M θ j v ≤ 1 :=
  (vs_effDist_mem_Icc θ j hv).2

lemma effDist_continuousOn {M : Market} (θ : VisitStrategy M) (j : Fin M.m) :
    ContinuousOn (effDist M θ j) (Iic 1) := by
  obtain ⟨B, hBpos, hB⟩ := M.f_bddAbove
  intro v hv
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  refine ⟨ε / B, div_pos hε hBpos, fun x hx hdist => ?_⟩
  rw [Real.dist_eq] at hdist ⊢
  have hlip : |effDist M θ j x - effDist M θ j v| ≤ B * |x - v| := by
    rcases le_total x v with hle | hle
    · have h1 := effDist_le_F_diff θ j hle hv
      have h2 : M.F v - M.F x ≤ B * (v - x) := by
        rw [← M.integral_f hx hv]
        calc ∫ t in x..v, M.f t
            ≤ ∫ _ in x..v, B := intervalIntegral.integral_mono_on hle
              (M.f_intervalIntegrable hx hv) intervalIntegrable_const
              (fun t ht => hB t (ht.2.trans hv))
          _ = B * (v - x) := by simp [mul_comm]
      rw [abs_of_nonpos (by linarith [h1.1]), abs_of_nonpos (by linarith)]
      linarith [h1.2]
    · have h1 := effDist_le_F_diff θ j hle hx
      have h2 : M.F x - M.F v ≤ B * (x - v) := by
        rw [← M.integral_f hv hx]
        calc ∫ t in v..x, M.f t
            ≤ ∫ _ in v..x, B := intervalIntegral.integral_mono_on hle
              (M.f_intervalIntegrable hv hx) intervalIntegrable_const
              (fun t ht => hB t (ht.2.trans hx))
          _ = B * (x - v) := by simp [mul_comm]
      rw [abs_of_nonneg h1.1, abs_of_nonneg (by linarith)]
      linarith [h1.2]
  calc |effDist M θ j x - effDist M θ j v|
      ≤ B * |x - v| := hlip
    _ < B * (ε / B) := mul_lt_mul_of_pos_left hdist hBpos
    _ = ε := mul_div_cancel₀ ε hBpos.ne'

lemma effDist_sum_one_sub {M : Market} (θ : VisitStrategy M) {v : ℝ} (hv : v ≤ 1) :
    ∑ j : Fin M.m, (1 - effDist M θ j v) = 1 - M.F v := by
  have h1 : ∀ j : Fin M.m, 1 - effDist M θ j v = ∫ t in v..1, θ.θ j t * M.f t := by
    intro j; unfold effDist; ring
  simp_rw [h1]
  rw [← intervalIntegral.integral_finsetSum (fun j _ => θ.mul_f_intervalIntegrable j hv le_rfl)]
  have heq : ∫ t in v..1, (∑ j : Fin M.m, θ.θ j t * M.f t) = ∫ t in v..1, M.f t := by
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [uIcc_of_le hv] at ht
    rw [← Finset.sum_mul]
    by_cases hta : t < M.a
    · rw [M.hf_below t hta, mul_zero]
    · rw [θ.hsum t ⟨le_of_not_gt hta, ht.2⟩, one_mul]
  rw [heq, M.integral_f hv le_rfl, M.hF_1]

/-- Convex combination of two visit strategies. -/
noncomputable def VisitStrategy.mix {M : Market} (θ θ' : VisitStrategy M)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : VisitStrategy M where
  θ j v := (1 - t) * θ.θ j v + t * θ'.θ j v
  hmeas j := (measurable_const.mul (θ.hmeas j)).add (measurable_const.mul (θ'.hmeas j))
  hnonneg j v := add_nonneg (mul_nonneg (by linarith) (θ.hnonneg j v))
    (mul_nonneg ht0 (θ'.hnonneg j v))
  hsum v hv := by
    simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum, θ.hsum v hv, θ'.hsum v hv]
    ring

lemma effDist_mix {M : Market} (θ θ' : VisitStrategy M) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (j : Fin M.m) {v : ℝ} (hv : v ≤ 1) :
    effDist M (θ.mix θ' t ht0 ht1) j v =
      (1 - t) * effDist M θ j v + t * effDist M θ' j v := by
  unfold effDist VisitStrategy.mix
  simp only
  have h1 : (fun u => ((1 - t) * θ.θ j u + t * θ'.θ j u) * M.f u) =
      (fun u => (1 - t) * (θ.θ j u * M.f u) + t * (θ'.θ j u * M.f u)) := by
    ext u; ring
  rw [h1, intervalIntegral.integral_add
    ((θ.mul_f_intervalIntegrable j hv le_rfl).const_mul (1 - t))
    ((θ'.mul_f_intervalIntegrable j hv le_rfl).const_mul t),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  ring

/-- Uniform visit strategy `θ_j ≡ 1 / m`. -/
noncomputable def uniformVisit (M : Market) : VisitStrategy M where
  θ _ _ := 1 / (M.m : ℝ)
  hmeas _ := measurable_const
  hnonneg _ _ := div_nonneg zero_le_one M.m_pos_real.le
  hsum _ _ := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_one_div_cancel M.m_pos_real.ne'

lemma effDist_uniformVisit (M : Market) (j : Fin M.m) {v : ℝ} (hv : v ≤ 1) :
    effDist M (uniformVisit M) j v = M.A v := by
  unfold effDist uniformVisit Market.A
  simp only [one_div]
  rw [intervalIntegral.integral_const_mul, M.integral_f hv le_rfl, M.hF_1]
  ring

/-! #### Properties of `poolAvg`, `alloc`, and `surplus` -/

lemma poolAvg_strictMono_left {n : ℕ} (hn : 2 ≤ n) {x₁ x₂ y : ℝ}
    (hx₁ : 0 ≤ x₁) (hy : 0 ≤ y) (hlt : x₁ < x₂) :
    poolAvg n x₁ y < poolAvg n x₂ y := by
  rw [poolAvg_eq_sum n (by omega), poolAvg_eq_sum n (by omega)]
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  apply div_lt_div_of_pos_right _ hnR
  apply Finset.sum_lt_sum
  · intro k _
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx₁ hlt.le k) (pow_nonneg hy _)
  · refine ⟨n - 1, Finset.mem_range.mpr (by omega), ?_⟩
    simp only [Nat.sub_self, pow_zero, mul_one]
    exact pow_lt_pow_left₀ hlt hx₁ (by omega)

lemma poolAvg_strictMono_right {n : ℕ} (hn : 2 ≤ n) {x y₁ y₂ : ℝ}
    (hx : 0 ≤ x) (hy₁ : 0 ≤ y₁) (hlt : y₁ < y₂) :
    poolAvg n x y₁ < poolAvg n x y₂ := by
  rw [poolAvg_eq_sum n (by omega), poolAvg_eq_sum n (by omega)]
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  apply div_lt_div_of_pos_right _ hnR
  apply Finset.sum_lt_sum
  · intro k _
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy₁ hlt.le _) (pow_nonneg hx _)
  · refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
    simp only [pow_zero, one_mul, Nat.sub_zero]
    exact pow_lt_pow_left₀ hlt hy₁ (by omega)

lemma vs_poolAvg_self (n : ℕ) (x : ℝ) : poolAvg n x x = x ^ (n - 1) := by
  simp [poolAvg]

lemma vs_poolAvg_bounds {n : ℕ} (hn : 2 ≤ n) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    x ^ (n - 1) ≤ poolAvg n x y ∧ poolAvg n x y ≤ y ^ (n - 1) := by
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · simp [vs_poolAvg_self]
  · constructor
    · rw [← vs_poolAvg_self n x]
      exact (poolAvg_strictMono_right hn hx hx hlt).le
    · rw [← vs_poolAvg_self n y]
      exact (poolAvg_strictMono_left hn hx (hx.trans hlt.le) hlt).le

lemma vs_poolAvg_strict_bounds {n : ℕ} (hn : 2 ≤ n) {x y : ℝ} (hx : 0 ≤ x) (hlt : x < y) :
    x ^ (n - 1) < poolAvg n x y ∧ poolAvg n x y < y ^ (n - 1) := by
  constructor
  · rw [← vs_poolAvg_self n x]
    exact poolAvg_strictMono_right hn hx hx hlt
  · rw [← vs_poolAvg_self n y]
    exact poolAvg_strictMono_left hn hx (hx.trans hlt.le) hlt

lemma poolAvg_nonneg {n : ℕ} (hn : 2 ≤ n) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ poolAvg n x y := by
  rw [poolAvg_eq_sum n (by omega)]
  apply div_nonneg
  · exact Finset.sum_nonneg fun k _ => mul_nonneg (pow_nonneg hx _) (pow_nonneg hy _)
  · positivity

lemma poolAvg_le_one {n : ℕ} (hn : 2 ≤ n) {x y : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    poolAvg n x y ≤ 1 := by
  rw [poolAvg_eq_sum n (by omega)]
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  rw [div_le_one hnR]
  calc ∑ k ∈ Finset.range n, x ^ k * y ^ (n - 1 - k)
      ≤ ∑ _k ∈ Finset.range n, (1 : ℝ) := by
        apply Finset.sum_le_sum; intro k _
        calc x ^ k * y ^ (n - 1 - k)
            ≤ 1 * 1 := mul_le_mul (pow_le_one₀ hx0 hx1) (pow_le_one₀ hy0 hy1)
              (pow_nonneg hy0 _) zero_le_one
          _ = 1 := one_mul 1
    _ = n := by simp

lemma poolAvg_diff_pos {n : ℕ} (hn : 2 ≤ n) {x₁ x₂ y₁ y₂ : ℝ}
    (hx₁ : 0 ≤ x₁) (hy₁ : 0 ≤ y₁) (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂)
    (hstrict : x₁ < x₂ ∨ y₁ < y₂) :
    poolAvg n x₁ y₁ < poolAvg n x₂ y₂ := by
  rcases hstrict with hlt | hlt
  · exact lt_of_lt_of_le (poolAvg_strictMono_left hn hx₁ hy₁ hlt)
      (by rcases eq_or_lt_of_le hy with rfl | hylt
          · exact le_rfl
          · exact (poolAvg_strictMono_right hn (hx₁.trans hlt.le) hy₁ hylt).le)
  · exact lt_of_le_of_lt
      (by rcases eq_or_lt_of_le hx with rfl | hxlt
          · exact le_rfl
          · exact (poolAvg_strictMono_left hn hx₁ hy₁ hxlt).le)
      (poolAvg_strictMono_right hn (hx₁.trans hx) hy₁ hlt)

lemma alloc_SPA (M : Market) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (Fj : ℝ → ℝ) (v : ℝ) :
    alloc M (SPA r hr0 hr1) Fj v = if v < r then 0 else (Fj v) ^ (M.n - 1) := by
  simp [alloc, SPA]

lemma alloc_below_r (M : Market) (mech : HierarchicalMech) (Fj : ℝ → ℝ) {v : ℝ} (hv : v < mech.r) :
    alloc M mech Fj v = 0 := by
  simp [alloc, hv]

lemma alloc_in_pool (M : Market) (mech : HierarchicalMech) (Fj : ℝ → ℝ)
    {I : Pool} (hI : I ∈ mech.pools) {v : ℝ} (hv : v ∈ Ioo I.α I.β) :
    alloc M mech Fj v = poolAvg M.n (Fj I.α) (Fj I.β) := by
  have hvr : ¬ v < mech.r := not_lt.mpr ((mech.hpools_in I hI).1.trans hv.1.le)
  unfold alloc
  rw [ite_eq_right_iff.mpr (fun h => absurd h hvr)]
  cases hfind : mech.pools.find? (fun J => decide (J.α < v ∧ v < J.β)) with
  | none =>
    have hfalse := List.find?_eq_none.mp hfind I hI
    simp [hv.1, hv.2] at hfalse
  | some J =>
    have hJmem := List.mem_of_find?_eq_some hfind
    have hJpred := List.find?_some hfind
    simp only [decide_eq_true_eq] at hJpred
    have hIJ : J = I := by
      by_contra hne
      have hdisj : J.β ≤ I.α ∨ I.β ≤ J.α := by
        have hp := mech.hpools_disj
        rw [List.pairwise_iff_getElem] at hp
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hI
        obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hJmem
        rcases lt_trichotomy j i with hlt | heq | hgt
        · exact hp j i hj hi hlt
        · subst heq; exact absurd rfl hne
        · exact (hp i j hi hj hgt).symm
      rcases hdisj with h | h <;> linarith [hv.1, hv.2, hJpred.1, hJpred.2]
    subst hIJ; rfl

lemma alloc_off_pools (M : Market) (mech : HierarchicalMech) (Fj : ℝ → ℝ)
    {v : ℝ} (hvr : mech.r ≤ v) (hoff : ∀ I ∈ mech.pools, ¬ (I.α < v ∧ v < I.β)) :
    alloc M mech Fj v = (Fj v) ^ (M.n - 1) := by
  unfold alloc
  rw [ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr hvr))]
  have hnone : mech.pools.find? (fun I => decide (I.α < v ∧ v < I.β)) = none := by
    rw [List.find?_eq_none]
    intro I hI
    simp [hoff I hI]
  rw [hnone]

lemma vs_alloc_monotoneOn (M : Market) (mech : HierarchicalMech) (Fj : ℝ → ℝ)
    (hmono : MonotoneOn Fj (Iic 1)) (hnonneg : ∀ v ≤ 1, 0 ≤ Fj v) :
    MonotoneOn (alloc M mech Fj) (Iic 1) := by
  intro x hx y hy hxy
  by_cases hxr : x < mech.r
  · rw [alloc_below_r M mech Fj hxr]
    by_cases hyr : y < mech.r
    · rw [alloc_below_r M mech Fj hyr]
    · unfold alloc
      rw [ite_eq_right_iff.mpr (fun h => absurd h hyr)]
      cases hfind : mech.pools.find? (fun I => decide (I.α < y ∧ y < I.β)) with
      | none => exact pow_nonneg (hnonneg y hy) _
      | some I =>
        have hI := List.mem_of_find?_eq_some hfind
        exact poolAvg_nonneg M.hn
          (hnonneg I.α (I.hαβ.le.trans (mech.hpools_in I hI).2))
          (hnonneg I.β (mech.hpools_in I hI).2)
  · push Not at hxr
    have hyr : mech.r ≤ y := hxr.trans hxy
    by_cases hxpool : ∃ I ∈ mech.pools, I.α < x ∧ x < I.β
    · obtain ⟨I, hI, hx1, hx2⟩ := hxpool
      rw [alloc_in_pool M mech Fj hI ⟨hx1, hx2⟩]
      by_cases hypool : ∃ J ∈ mech.pools, J.α < y ∧ y < J.β
      · obtain ⟨J, hJ, hy1, hy2⟩ := hypool
        rw [alloc_in_pool M mech Fj hJ ⟨hy1, hy2⟩]
        by_cases hIJ : I = J
        · subst hIJ; exact le_rfl
        · have hdisj : I.β ≤ J.α ∨ J.β ≤ I.α := by
            have hp := mech.hpools_disj
            rw [List.pairwise_iff_getElem] at hp
            obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hI
            obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hJ
            rcases lt_trichotomy i j with hlt | heq | hgt
            · exact hp i j hi hj hlt
            · subst heq; exact absurd rfl hIJ
            · exact (hp j i hj hi hgt).symm
          have hIβJα : I.β ≤ J.α := by
            rcases hdisj with h | h; exact h; linarith
          have hIβ1 : I.β ≤ 1 := (mech.hpools_in I hI).2
          have hJβ1 : J.β ≤ 1 := (mech.hpools_in J hJ).2
          calc poolAvg M.n (Fj I.α) (Fj I.β)
              ≤ (Fj I.β) ^ (M.n - 1) := (vs_poolAvg_bounds M.hn
                (hnonneg I.α (I.hαβ.le.trans hIβ1))
                (hmono (I.hαβ.le.trans hIβ1) hIβ1 I.hαβ.le)).2
            _ ≤ (Fj J.α) ^ (M.n - 1) := pow_le_pow_left₀ (hnonneg I.β hIβ1)
                (hmono hIβ1 (J.hαβ.le.trans hJβ1) hIβJα) _
            _ ≤ poolAvg M.n (Fj J.α) (Fj J.β) := (vs_poolAvg_bounds M.hn
                (hnonneg J.α (J.hαβ.le.trans hJβ1))
                (hmono (J.hαβ.le.trans hJβ1) hJβ1 J.hαβ.le)).1
      · push Not at hypool
        rw [alloc_off_pools M mech Fj hyr (fun J hJ h => not_le.mpr h.2 (hypool J hJ h.1))]
        have hIβy : I.β ≤ y := hypool I hI (lt_of_lt_of_le hx1 hxy)
        have hIβ1 : I.β ≤ 1 := (mech.hpools_in I hI).2
        calc poolAvg M.n (Fj I.α) (Fj I.β)
            ≤ (Fj I.β) ^ (M.n - 1) := (vs_poolAvg_bounds M.hn
              (hnonneg I.α (I.hαβ.le.trans hIβ1))
              (hmono (I.hαβ.le.trans hIβ1) hIβ1 I.hαβ.le)).2
          _ ≤ (Fj y) ^ (M.n - 1) := pow_le_pow_left₀ (hnonneg I.β hIβ1) (hmono hIβ1 hy hIβy) _
    · push Not at hxpool
      rw [alloc_off_pools M mech Fj hxr (fun I hI h => not_le.mpr h.2 (hxpool I hI h.1))]
      by_cases hypool : ∃ J ∈ mech.pools, J.α < y ∧ y < J.β
      · obtain ⟨J, hJ, hy1, hy2⟩ := hypool
        rw [alloc_in_pool M mech Fj hJ ⟨hy1, hy2⟩]
        have hxJα : x ≤ J.α := by
          by_contra hlt; push Not at hlt
          have := hxpool J hJ hlt
          linarith
        have hJβ1 : J.β ≤ 1 := (mech.hpools_in J hJ).2
        calc (Fj x) ^ (M.n - 1)
            ≤ (Fj J.α) ^ (M.n - 1) := pow_le_pow_left₀ (hnonneg x hx)
              (hmono hx (J.hαβ.le.trans hJβ1) hxJα) _
          _ ≤ poolAvg M.n (Fj J.α) (Fj J.β) := (vs_poolAvg_bounds M.hn
              (hnonneg J.α (J.hαβ.le.trans hJβ1))
              (hmono (J.hαβ.le.trans hJβ1) hJβ1 J.hαβ.le)).1
      · push Not at hypool
        rw [alloc_off_pools M mech Fj hyr (fun J hJ h => not_le.mpr h.2 (hypool J hJ h.1))]
        exact pow_le_pow_left₀ (hnonneg x hx) (hmono hx hy hxy) _

lemma alloc_nonneg (M : Market) (mech : HierarchicalMech) (Fj : ℝ → ℝ)
    (hnonneg : ∀ v ≤ 1, 0 ≤ Fj v) {v : ℝ} (hv : v ≤ 1) :
    0 ≤ alloc M mech Fj v := by
  unfold alloc
  split_ifs
  · exact le_rfl
  · cases hfind : mech.pools.find? (fun I => decide (I.α < v ∧ v < I.β)) with
    | none => exact pow_nonneg (hnonneg v hv) _
    | some I =>
      have hI := List.mem_of_find?_eq_some hfind
      exact poolAvg_nonneg M.hn
        (hnonneg I.α (I.hαβ.le.trans (mech.hpools_in I hI).2))
        (hnonneg I.β (mech.hpools_in I hI).2)

lemma alloc_le_one (M : Market) (mech : HierarchicalMech) (Fj : ℝ → ℝ)
    (hnonneg : ∀ v ≤ 1, 0 ≤ Fj v) (hle1 : ∀ v ≤ 1, Fj v ≤ 1) {v : ℝ} (hv : v ≤ 1) :
    alloc M mech Fj v ≤ 1 := by
  unfold alloc
  split_ifs
  · exact zero_le_one
  · cases hfind : mech.pools.find? (fun I => decide (I.α < v ∧ v < I.β)) with
    | none => exact pow_le_one₀ (hnonneg v hv) (hle1 v hv)
    | some I =>
      have hI := List.mem_of_find?_eq_some hfind
      have hIβ1 := (mech.hpools_in I hI).2
      exact poolAvg_le_one M.hn
        (hnonneg I.α (I.hαβ.le.trans hIβ1)) (hle1 I.α (I.hαβ.le.trans hIβ1))
        (hnonneg I.β hIβ1) (hle1 I.β hIβ1)

lemma alloc_intervalIntegrable (M : Market) (mech : HierarchicalMech) (Fj : ℝ → ℝ)
    (hmono : MonotoneOn Fj (Iic 1)) (hnonneg : ∀ v ≤ 1, 0 ≤ Fj v)
    {u v : ℝ} (hu : u ≤ 1) (hv : v ≤ 1) :
    IntervalIntegrable (alloc M mech Fj) volume u v := by
  have hma := vs_alloc_monotoneOn M mech Fj hmono hnonneg
  have hsub : uIcc u v ⊆ Iic 1 := by
    intro t ht; rcases le_total u v with hle | hle
    · rw [uIcc_of_le hle] at ht; exact ht.2.trans hv
    · rw [uIcc_comm, uIcc_of_le hle] at ht; exact ht.2.trans hu
  exact (hma.mono hsub).intervalIntegrable

lemma surplus_sub (M : Market) (mech : HierarchicalMech) (Fj : ℝ → ℝ)
    (hmono : MonotoneOn Fj (Iic 1)) (hnonneg : ∀ v ≤ 1, 0 ≤ Fj v)
    {u v : ℝ} (hu : u ≤ 1) (hv : v ≤ 1) :
    surplus M mech Fj v - surplus M mech Fj u = ∫ t in u..v, alloc M mech Fj t := by
  unfold surplus
  have h1 := alloc_intervalIntegrable M mech Fj hmono hnonneg (by linarith : (0 : ℝ) ≤ 1) hu
  have h2 := alloc_intervalIntegrable M mech Fj hmono hnonneg hu hv
  have hadd := intervalIntegral.integral_add_adjacent_intervals h1 h2
  linarith

lemma surplus_zero_of_le_r (M : Market) (mech : HierarchicalMech) (Fj : ℝ → ℝ)
    {v : ℝ} (hv0 : 0 ≤ v) (hvr : v ≤ mech.r) :
    surplus M mech Fj v = 0 := by
  unfold surplus
  have hcongr : ∫ u in (0 : ℝ)..v, alloc M mech Fj u = ∫ _ in (0 : ℝ)..v, (0 : ℝ) := by
    apply intervalIntegral.integral_congr_ae
    have hne : ∀ᵐ t ∂volume, t ≠ v := by simp [ae_iff, measure_singleton]
    filter_upwards [hne] with t ht hmem
    rw [uIoc_of_le hv0] at hmem
    exact alloc_below_r M mech Fj (lt_of_lt_of_le (lt_of_le_of_ne hmem.2 ht) hvr)
  rw [hcongr]; simp

lemma surplus_SPA_eq (M : Market) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (Fj : ℝ → ℝ)
    (hmono : MonotoneOn Fj (Iic 1)) (hnonneg : ∀ v ≤ 1, 0 ≤ Fj v)
    {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    surplus M (SPA r hr0 hr1) Fj v = ∫ t in r..(max v r), (Fj t) ^ (M.n - 1) := by
  by_cases hvr : v ≤ r
  · rw [surplus_zero_of_le_r M (SPA r hr0 hr1) Fj hv0 hvr, max_eq_right hvr,
      intervalIntegral.integral_same]
  · push Not at hvr
    rw [max_eq_left hvr.le]
    have h0 := surplus_zero_of_le_r M (SPA r hr0 hr1) Fj hr0 le_rfl
    have hsub := surplus_sub M (SPA r hr0 hr1) Fj hmono hnonneg hr1 hv1
    rw [h0, sub_zero] at hsub
    rw [hsub]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hvr.le] at ht
    rw [alloc_SPA, ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr ht.1))]

lemma surplus_continuousOn (M : Market) (mech : HierarchicalMech) (Fj : ℝ → ℝ)
    (hmono : MonotoneOn Fj (Iic 1)) (hnonneg : ∀ v ≤ 1, 0 ≤ Fj v) (hle1 : ∀ v ≤ 1, Fj v ≤ 1) :
    ContinuousOn (surplus M mech Fj) (Iic 1) := by
  intro v hv
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  refine ⟨ε, hε, fun x hx hdist => ?_⟩
  rw [Real.dist_eq] at hdist ⊢
  have hlip : |surplus M mech Fj x - surplus M mech Fj v| ≤ |x - v| := by
    rcases le_total x v with hle | hle
    · rw [surplus_sub M mech Fj hmono hnonneg hv hx, intervalIntegral.integral_symm,
        abs_neg]
      have hnn : 0 ≤ ∫ t in x..v, alloc M mech Fj t :=
        intervalIntegral.integral_nonneg hle fun t ht =>
          alloc_nonneg M mech Fj hnonneg (ht.2.trans hv)
      rw [abs_of_nonneg hnn, abs_of_nonpos (sub_nonpos.mpr hle)]
      calc ∫ t in x..v, alloc M mech Fj t
          ≤ ∫ _ in x..v, (1 : ℝ) := intervalIntegral.integral_mono_on hle
            (alloc_intervalIntegrable M mech Fj hmono hnonneg hx hv) intervalIntegrable_const
            (fun t ht => alloc_le_one M mech Fj hnonneg hle1 (ht.2.trans hv))
        _ = -(x - v) := by simp
    · rw [surplus_sub M mech Fj hmono hnonneg hv hx]
      have hnn : 0 ≤ ∫ t in v..x, alloc M mech Fj t :=
        intervalIntegral.integral_nonneg hle fun t ht =>
          alloc_nonneg M mech Fj hnonneg (ht.2.trans hx)
      rw [abs_of_nonneg hnn, abs_of_nonneg (sub_nonneg.mpr hle)]
      calc ∫ t in v..x, alloc M mech Fj t
          ≤ ∫ _ in v..x, (1 : ℝ) := intervalIntegral.integral_mono_on hle
            (alloc_intervalIntegrable M mech Fj hmono hnonneg hv hx) intervalIntegrable_const
            (fun t ht => alloc_le_one M mech Fj hnonneg hle1 (ht.2.trans hx))
        _ = x - v := by simp
  exact lt_of_le_of_lt hlip hdist

/-- Helper: if `g` is interval integrable on `[c, d]` and `∫_c^x g = 0` for all `x ∈ [c, d]`,
then `g = 0` a.e. on `[c, d]`. -/
lemma ae_eq_zero_of_forall_integral_eq_zero {g : ℝ → ℝ} {c d : ℝ} (hcd : c ≤ d)
    (hg : IntervalIntegrable g volume c d)
    (hzero : ∀ x ∈ Icc c d, ∫ t in c..x, g t = 0) :
    ∀ᵐ x ∂(volume.restrict (Icc c d)), g x = 0 := by
  have hld := hg.ae_hasDerivAt_integral
  have hne_c : ∀ᵐ x ∂volume, x ≠ c := by simp [ae_iff, measure_singleton]
  have hne_d : ∀ᵐ x ∂volume, x ≠ d := by simp [ae_iff, measure_singleton]
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  filter_upwards [hld, hne_c, hne_d] with x hx hxc hxd hmem
  have hx_open : x ∈ Ioo c d := ⟨lt_of_le_of_ne hmem.1 (Ne.symm hxc), lt_of_le_of_ne hmem.2 hxd⟩
  have hderiv := hx (by rwa [uIcc_of_le hcd]) c (by rw [uIcc_of_le hcd]; exact left_mem_Icc.mpr hcd)
  have hconst : HasDerivAt (fun y => ∫ t in c..y, g t) 0 x := by
    refine (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds hx_open] with y hy
    exact hzero y (Ioo_subset_Icc_self hy)
  exact hderiv.unique hconst

/-- Reusable Fubini identity: for `r ∈ [0, 1]`, integrable `g` on `[min a r, 1]` vanishing
below `a`, and continuous `φ` on `[r, 1]`,
`∫ v in r..1, φ v * (∫ u in v..1, g u) = ∫ u in a..1, g u * (∫ v in r..(max u r), φ v)`. -/
lemma fubini_tail_integral {a r : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    {φ g : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc r 1))
    (hg_int : IntervalIntegrable g volume (min a r) 1)
    (hg_below : ∀ u < a, g u = 0) :
    ∫ v in r..1, φ v * (∫ u in v..1, g u) =
      ∫ u in a..1, g u * (∫ v in r..(max u r), φ v) := by
  let F : ℝ → ℝ → ℝ := fun v u => if v ≤ u then φ v * g u else 0
  have hφ_int : IntegrableOn φ (Ioc r 1) volume :=
    hφ.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hg_int_a1 : IntegrableOn g (Ioc a 1) volume := by
    have hsub : Ioc a 1 ⊆ Ioc (min a r) 1 := Ioc_subset_Ioc_left (min_le_left _ _)
    exact hg_int.1.mono_set hsub
  have hprod_int : Integrable (fun p : ℝ × ℝ => φ p.1 * g p.2)
      ((volume.restrict (Ioc r 1)).prod (volume.restrict (Ioc a 1))) :=
    hφ_int.mul_prod hg_int_a1
  have hF_meas : MeasurableSet {p : ℝ × ℝ | p.1 ≤ p.2} :=
    isClosed_le continuous_fst continuous_snd |>.measurableSet
  have hF_int : Integrable (Function.uncurry F)
      ((volume.restrict (Ioc r 1)).prod (volume.restrict (Ioc a 1))) := by
    have : Function.uncurry F = Set.indicator {p : ℝ × ℝ | p.1 ≤ p.2} (fun p => φ p.1 * g p.2) := by
      ext p; simp [F, Function.uncurry, Set.indicator]
    rw [this]
    exact hprod_int.indicator hF_meas
  have hswap := MeasureTheory.integral_integral_swap hF_int
  have hLHS : ∫ v in Ioc r 1, (∫ u in Ioc a 1, F v u) =
      ∫ v in r..1, φ v * (∫ u in v..1, g u) := by
    rw [intervalIntegral.integral_of_le hr1]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro v hv
    dsimp only
    have hv1 : v ≤ 1 := hv.2
    have hinner : ∫ u in Ioc a 1, F v u = φ v * ∫ u in Ioc (max v a) 1, g u := by
      have h1 : ∀ u, F v u = φ v * (if v ≤ u then g u else 0) := by
        intro u; simp only [F]; split_ifs <;> ring
      simp_rw [h1, MeasureTheory.integral_const_mul]
      congr 1
      have h2 : ∫ u in Ioc a 1, (if v ≤ u then g u else 0) =
          ∫ u in Ioc a 1 ∩ Ici v, g u := by
        rw [← MeasureTheory.setIntegral_indicator measurableSet_Ici]
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
        intro u _; simp [Set.indicator]
      rw [h2]
      apply MeasureTheory.setIntegral_congr_set
      have hne : volume ({v} : Set ℝ) = 0 := measure_singleton v
      rw [MeasureTheory.ae_eq_set]
      constructor
      · refine measure_mono_null (fun u hu => ?_) hne
        simp only [Set.mem_sdiff, mem_inter_iff, mem_Ioc, mem_Ici, max_lt_iff, not_and,
          not_le, mem_singleton_iff] at hu ⊢
        by_contra hne_v
        have hvlt : v < u := lt_of_le_of_ne hu.1.2 (Ne.symm hne_v)
        exact absurd hu.1.1.2 (not_le.mpr (hu.2 ⟨hvlt, hu.1.1.1⟩))
      · refine measure_mono_null (fun u hu => ?_) hne
        simp only [Set.mem_sdiff, mem_inter_iff, mem_Ioc, mem_Ici, max_lt_iff, not_and,
          not_le, mem_singleton_iff] at hu ⊢
        exfalso
        exact lt_asymm hu.1.1.1 (hu.2 ⟨hu.1.1.2, hu.1.2⟩)
    rw [hinner]
    congr 1
    rw [intervalIntegral.integral_of_le hv1]
    by_cases hva : v ≤ a
    · rw [max_eq_right hva]
      symm
      calc ∫ u in Ioc v 1, g u
          = ∫ u in Ioc v a ∪ Ioc a 1, g u := by rw [Ioc_union_Ioc_eq_Ioc hva ha1.le]
        _ = (∫ u in Ioc v a, g u) + ∫ u in Ioc a 1, g u := by
            rw [MeasureTheory.setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
              (hg_int.1.mono_set (Ioc_subset_Ioc (min_le_of_right_le hv.1.le) ha1.le))
              hg_int_a1]
        _ = 0 + ∫ u in Ioc a 1, g u := by
            congr 1
            have : ∀ᵐ u ∂(volume.restrict (Ioc v a)), g u = 0 := by
              rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
              have hne : ∀ᵐ u ∂volume, u ≠ a := by simp [ae_iff, measure_singleton]
              filter_upwards [hne] with u hu hmem
              exact hg_below u (lt_of_le_of_ne hmem.2 hu)
            rw [MeasureTheory.integral_congr_ae this, MeasureTheory.integral_zero]
        _ = ∫ u in Ioc a 1, g u := zero_add _
    · push Not at hva; rw [max_eq_left hva.le]
  have hRHS : ∫ u in Ioc a 1, (∫ v in Ioc r 1, F v u) =
      ∫ u in a..1, g u * (∫ v in r..(max u r), φ v) := by
    rw [intervalIntegral.integral_of_le ha1.le]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro u hu
    dsimp only
    have h1 : ∀ v, F v u = g u * (if v ≤ u then φ v else 0) := by
      intro v; simp only [F]; split_ifs <;> ring
    simp_rw [h1, MeasureTheory.integral_const_mul]
    congr 1
    have h2 : ∫ v in Ioc r 1, (if v ≤ u then φ v else 0) =
        ∫ v in Ioc r 1 ∩ Iic u, φ v := by
      rw [← MeasureTheory.setIntegral_indicator measurableSet_Iic]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      intro v _; simp only [Set.indicator_apply, mem_Iic]
    rw [h2, intervalIntegral.integral_of_le (le_max_right u r)]
    congr 2
    ext v; simp only [mem_inter_iff, mem_Ioc, mem_Iic]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, le_max_of_le_left h3⟩
    · rintro ⟨h1, h2⟩
      by_cases hur : u ≤ r
      · rw [max_eq_right hur] at h2; linarith
      · push Not at hur; rw [max_eq_left hur.le] at h2
        exact ⟨⟨h1, h2.trans hu.2⟩, h2⟩
  linarith [hswap, hLHS, hRHS]

end Foundation

/-! ### Part 1: Proposition 1 — Standard Auctions Form a Potential Game -/

section Proposition1

variable (M : Market)

/-- The welfare potential `Φ(θ) = ∑_j ∫_{r_j}^1 (1 - F_j(v)^n) dv` (equation (4)). -/
noncomputable def potential (r : Fin M.m → ℝ) (θ : VisitStrategy M) : ℝ :=
  ∑ j : Fin M.m, ∫ v in (r j)..1, (1 - (effDist M θ j v) ^ M.n)

lemma potential_integrand_continuousOn (r : Fin M.m → ℝ)
    (θ : VisitStrategy M) (j : Fin M.m) :
    ContinuousOn (fun v => 1 - (effDist M θ j v) ^ M.n) (Icc (r j) 1) := by
  exact continuousOn_const.sub
    (((effDist_continuousOn θ j).mono (Icc_subset_Iic_self)).pow M.n)

/-- **Proposition 1 (Concavity)**: The potential functional `Φ` is concave in `θ`. -/
theorem prop1_potential_concave (r : Fin M.m → ℝ) (hr1 : ∀ j, r j ≤ 1)
    (θ θ' : VisitStrategy M) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * potential M r θ + t * potential M r θ' ≤
      potential M r (θ.mix θ' t ht0 ht1) := by
  unfold potential
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  have hconv := (strictConvexOn_pow M.hn).convexOn
  have hint1 : IntervalIntegrable (fun v => 1 - (effDist M θ j v) ^ M.n) volume (r j) 1 :=
    (potential_integrand_continuousOn M r θ j).intervalIntegrable_of_Icc (hr1 j)
  have hint2 : IntervalIntegrable (fun v => 1 - (effDist M θ' j v) ^ M.n) volume (r j) 1 :=
    (potential_integrand_continuousOn M r θ' j).intervalIntegrable_of_Icc (hr1 j)
  have hintm : IntervalIntegrable (fun v => 1 - (effDist M (θ.mix θ' t ht0 ht1) j v) ^ M.n)
      volume (r j) 1 :=
    (potential_integrand_continuousOn M r (θ.mix θ' t ht0 ht1) j).intervalIntegrable_of_Icc (hr1 j)
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add (hint1.const_mul _) (hint2.const_mul _)]
  apply intervalIntegral.integral_mono_on (hr1 j)
    ((hint1.const_mul _).add (hint2.const_mul _)) hintm
  intro v hv
  rw [effDist_mix θ θ' ht0 ht1 j hv.2]
  have hpow := hconv.2 (effDist_nonneg θ j hv.2) (effDist_nonneg θ' j hv.2)
    (sub_nonneg.mpr ht1) ht0 (by ring)
  simp only [smul_eq_mul] at hpow
  linarith

/-- **Proposition 1 (Strict midpoint concavity)**: If `θ` and `θ'` induce distinct effective
distributions at some `v ∈ (r_j, 1)`, then their midpoint strictly increases `Φ`. -/
theorem prop1_potential_strict_midpoint (r : Fin M.m → ℝ) (hr1 : ∀ j, r j ≤ 1)
    (θ θ' : VisitStrategy M)
    (hdiff : ∃ j : Fin M.m, ∃ v ∈ Ioo (r j) 1, effDist M θ j v ≠ effDist M θ' j v) :
    (1 / 2 : ℝ) * potential M r θ + (1 / 2 : ℝ) * potential M r θ' <
      potential M r (θ.mix θ' (1 / 2) (by norm_num) (by norm_num)) := by
  obtain ⟨j₀, v₀, hv₀, hne⟩ := hdiff
  let θm := θ.mix θ' (1 / 2) (by norm_num) (by norm_num)
  unfold potential
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  have hsc := strictConvexOn_pow M.hn
  apply Finset.sum_lt_sum
  · intro j _
    have hconv := hsc.convexOn
    have hint1 : IntervalIntegrable (fun v => 1 - (effDist M θ j v) ^ M.n) volume (r j) 1 :=
      (potential_integrand_continuousOn M r θ j).intervalIntegrable_of_Icc (hr1 j)
    have hint2 : IntervalIntegrable (fun v => 1 - (effDist M θ' j v) ^ M.n) volume (r j) 1 :=
      (potential_integrand_continuousOn M r θ' j).intervalIntegrable_of_Icc (hr1 j)
    have hintm : IntervalIntegrable (fun v => 1 - (effDist M θm j v) ^ M.n) volume (r j) 1 :=
      (potential_integrand_continuousOn M r θm j).intervalIntegrable_of_Icc (hr1 j)
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (hint1.const_mul _) (hint2.const_mul _)]
    apply intervalIntegral.integral_mono_on (hr1 j)
      ((hint1.const_mul _).add (hint2.const_mul _)) hintm
    intro v hv
    have hmix : effDist M θm j v =
        (1 - (1 / 2 : ℝ)) * effDist M θ j v + (1 / 2 : ℝ) * effDist M θ' j v :=
      effDist_mix θ θ' (by norm_num) (by norm_num) j hv.2
    rw [hmix]
    have hpow := hconv.2 (effDist_nonneg θ j hv.2) (effDist_nonneg θ' j hv.2)
      (by norm_num : (0 : ℝ) ≤ 1 - 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by ring)
    simp only [smul_eq_mul] at hpow
    linarith
  · refine ⟨j₀, Finset.mem_univ j₀, ?_⟩
    let g : ℝ → ℝ := fun v =>
      (1 - (effDist M θm j₀ v) ^ M.n) -
      ((1 / 2 : ℝ) * (1 - (effDist M θ j₀ v) ^ M.n) +
       (1 / 2 : ℝ) * (1 - (effDist M θ' j₀ v) ^ M.n))
    have hg_cont : ContinuousOn g (Icc (r j₀) 1) :=
      (potential_integrand_continuousOn M r θm j₀).sub
        (((potential_integrand_continuousOn M r θ j₀).const_mul _).add
         ((potential_integrand_continuousOn M r θ' j₀).const_mul _))
    have hg_nn : ∀ v ∈ Ioc (r j₀) 1, 0 ≤ g v := by
      intro v hv
      have hmix : effDist M θm j₀ v =
          (1 - (1 / 2 : ℝ)) * effDist M θ j₀ v + (1 / 2 : ℝ) * effDist M θ' j₀ v :=
        effDist_mix θ θ' (by norm_num) (by norm_num) j₀ hv.2
      simp only [g, hmix]
      have hpow := hsc.convexOn.2 (effDist_nonneg θ j₀ hv.2) (effDist_nonneg θ' j₀ hv.2)
        (by norm_num : (0 : ℝ) ≤ 1 - 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by ring)
      simp only [smul_eq_mul] at hpow; linarith
    have hg_pos : 0 < g v₀ := by
      have hmix : effDist M θm j₀ v₀ =
          (1 - (1 / 2 : ℝ)) * effDist M θ j₀ v₀ + (1 / 2 : ℝ) * effDist M θ' j₀ v₀ :=
        effDist_mix θ θ' (by norm_num) (by norm_num) j₀ hv₀.2.le
      simp only [g, hmix]
      have hpow := hsc.2 (effDist_nonneg θ j₀ hv₀.2.le) (effDist_nonneg θ' j₀ hv₀.2.le) hne
        (by norm_num : (0 : ℝ) < 1 - 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by ring)
      simp only [smul_eq_mul] at hpow; linarith
    have hint_pos : 0 < ∫ v in (r j₀)..1, g v :=
      intervalIntegral.integral_pos (lt_trans hv₀.1 hv₀.2) hg_cont hg_nn
        ⟨v₀, Ioo_subset_Icc_self hv₀, hg_pos⟩
    have hint1 : IntervalIntegrable (fun v => 1 - (effDist M θ j₀ v) ^ M.n) volume (r j₀) 1 :=
      (potential_integrand_continuousOn M r θ j₀).intervalIntegrable_of_Icc (hr1 j₀)
    have hint2 : IntervalIntegrable (fun v => 1 - (effDist M θ' j₀ v) ^ M.n) volume (r j₀) 1 :=
      (potential_integrand_continuousOn M r θ' j₀).intervalIntegrable_of_Icc (hr1 j₀)
    have hintm : IntervalIntegrable (fun v => 1 - (effDist M θm j₀ v) ^ M.n) volume (r j₀) 1 :=
      (potential_integrand_continuousOn M r θm j₀).intervalIntegrable_of_Icc (hr1 j₀)
    have hsplit : ∫ v in (r j₀)..1, g v =
        (∫ v in (r j₀)..1, (1 - (effDist M θm j₀ v) ^ M.n)) -
        ((1 / 2 : ℝ) * (∫ v in (r j₀)..1, (1 - (effDist M θ j₀ v) ^ M.n)) +
         (1 / 2 : ℝ) * (∫ v in (r j₀)..1, (1 - (effDist M θ' j₀ v) ^ M.n))) := by
      simp only [g]
      rw [intervalIntegral.integral_sub hintm ((hint1.const_mul _).add (hint2.const_mul _)),
        intervalIntegral.integral_add (hint1.const_mul _) (hint2.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    linarith

/-- Helper: algebraic second-order Taylor remainder for `(x + ε * d)^n`. -/
private lemma pow_taylor_bound {n : ℕ} (hn : 2 ≤ n) {x d ε : ℝ}
    (hx : |x| ≤ 1) (hd : |d| ≤ 2) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    |(x + ε * d) ^ n - x ^ n - (n : ℝ) * x ^ (n - 1) * (ε * d)| ≤
      (n : ℝ) * (n : ℝ) * 3 ^ n * ε ^ 2 := by
  have hC : ∀ t ∈ Icc (0 : ℝ) ε, |(x + t * d) ^ (n - 1) - x ^ (n - 1)| ≤ (n : ℝ) * 3 ^ n * t := by
    intro t ht
    have ht1 : t ≤ 1 := ht.2.trans hε1
    have hxt : |x + t * d| ≤ 3 := by
      calc |x + t * d| ≤ |x| + |t * d| := abs_add_le _ _
        _ = |x| + t * |d| := by rw [abs_mul, abs_of_nonneg ht.1]
        _ ≤ 1 + 1 * 2 := add_le_add hx (mul_le_mul ht1 hd (abs_nonneg d) zero_le_one)
        _ = 3 := by norm_num
    have hgeom : (x + t * d) ^ (n - 1) - x ^ (n - 1) =
        (t * d) * ∑ k ∈ Finset.range (n - 1), (x + t * d) ^ k * x ^ (n - 1 - 1 - k) := by
      have h := geom_sum₂_mul (x + t * d) x (n - 1)
      have hsub : x + t * d - x = t * d := by ring
      rw [hsub] at h
      rw [← h, mul_comm]
    rw [hgeom, abs_mul, abs_mul, abs_of_nonneg ht.1]
    have hsum_le : |∑ k ∈ Finset.range (n - 1), (x + t * d) ^ k * x ^ (n - 1 - 1 - k)| ≤
        ((n - 1 : ℕ) : ℝ) * 3 ^ (n - 1) := by
      calc |∑ k ∈ Finset.range (n - 1), (x + t * d) ^ k * x ^ (n - 1 - 1 - k)|
          ≤ ∑ k ∈ Finset.range (n - 1), |(x + t * d) ^ k * x ^ (n - 1 - 1 - k)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k ∈ Finset.range (n - 1), (3 : ℝ) ^ (n - 1) := by
            apply Finset.sum_le_sum; intro k hk
            rw [Finset.mem_range] at hk
            rw [abs_mul, abs_pow, abs_pow]
            calc |x + t * d| ^ k * |x| ^ (n - 1 - 1 - k)
                ≤ 3 ^ k * 1 ^ (n - 1 - 1 - k) :=
                  mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hxt k)
                    (pow_le_pow_left₀ (abs_nonneg _) hx _) (pow_nonneg (abs_nonneg _) _) (by positivity)
              _ = 3 ^ k := by simp
              _ ≤ 3 ^ (n - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
        _ = ((n - 1 : ℕ) : ℝ) * 3 ^ (n - 1) := by simp
    have hnm1 : ((n - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
    have h3 : (3 : ℝ) ^ (n - 1) * 2 ≤ 3 ^ n := by
      have : (3 : ℝ) ^ n = 3 ^ (n - 1) * 3 := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega)]
      linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) (n - 1)]
    have ht0 : 0 ≤ t := ht.1
    calc t * |d| * |∑ k ∈ Finset.range (n - 1), (x + t * d) ^ k * x ^ (n - 1 - 1 - k)|
        ≤ t * 2 * (((n - 1 : ℕ) : ℝ) * 3 ^ (n - 1)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hd ht0) hsum_le (abs_nonneg _) (by positivity)
      _ = ((n - 1 : ℕ) : ℝ) * (3 ^ (n - 1) * 2) * t := by ring
      _ ≤ (n : ℝ) * 3 ^ n * t :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hnm1 h3 (by positivity) (Nat.cast_nonneg n)) ht0
  have hFTC : (x + ε * d) ^ n - x ^ n - (n : ℝ) * x ^ (n - 1) * (ε * d) =
      ∫ t in (0 : ℝ)..ε, (n : ℝ) * d * ((x + t * d) ^ (n - 1) - x ^ (n - 1)) := by
    have hderiv : ∀ t, HasDerivAt (fun s => (x + s * d) ^ n - (n : ℝ) * x ^ (n - 1) * (s * d))
        ((n : ℝ) * d * ((x + t * d) ^ (n - 1) - x ^ (n - 1))) t := by
      intro t
      have h1 : HasDerivAt (fun s => x + s * d) d t := by
        have h := ((hasDerivAt_id t).mul_const d).const_add x
        simpa [one_mul] using h
      have h2 := h1.pow n
      have h3 : HasDerivAt (fun s => (n : ℝ) * x ^ (n - 1) * (s * d))
          ((n : ℝ) * x ^ (n - 1) * d) t := by
        have h := ((hasDerivAt_id t).mul_const d).const_mul ((n : ℝ) * x ^ (n - 1))
        simpa [one_mul] using h
      convert h2.sub h3 using 1; ring
    have hcont_f : Continuous (fun t : ℝ => (n : ℝ) * d * ((x + t * d) ^ (n - 1) - x ^ (n - 1))) :=
      continuous_const.mul
        (((continuous_const.add (continuous_id.mul continuous_const)).pow (n - 1)).sub continuous_const)
    have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hderiv t) (hcont_f.intervalIntegrable 0 ε)
    simp only [zero_mul, add_zero, mul_zero, sub_zero] at heq
    linarith
  rw [hFTC]
  have hcont_abs : Continuous (fun t : ℝ => |(n : ℝ) * d * ((x + t * d) ^ (n - 1) - x ^ (n - 1))|) :=
    (continuous_const.mul
      (((continuous_const.add (continuous_id.mul continuous_const)).pow (n - 1)).sub
        continuous_const)).abs
  have hcont_lin : Continuous (fun t : ℝ => (n : ℝ) * 2 * ((n : ℝ) * 3 ^ n * t)) :=
    continuous_const.mul (continuous_const.mul continuous_id)
  calc |∫ t in (0 : ℝ)..ε, (n : ℝ) * d * ((x + t * d) ^ (n - 1) - x ^ (n - 1))|
      ≤ ∫ t in (0 : ℝ)..ε, |(n : ℝ) * d * ((x + t * d) ^ (n - 1) - x ^ (n - 1))| :=
        intervalIntegral.abs_integral_le_integral_abs hε0
    _ ≤ ∫ t in (0 : ℝ)..ε, (n : ℝ) * 2 * ((n : ℝ) * 3 ^ n * t) := by
        apply intervalIntegral.integral_mono_on hε0
          (hcont_abs.intervalIntegrable 0 ε) (hcont_lin.intervalIntegrable 0 ε)
        intro t ht
        rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
        exact mul_le_mul (mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg n))
          (hC t ht) (abs_nonneg _) (by positivity)
    _ = (n : ℝ) * (n : ℝ) * 3 ^ n * ε ^ 2 := by
        have hconst : (fun t => (n : ℝ) * 2 * ((n : ℝ) * 3 ^ n * t)) =
            (fun t => ((n : ℝ) * (n : ℝ) * 3 ^ n * 2) * t) := by ext t; ring
        have hid : ∫ t in (0 : ℝ)..ε, t = ε ^ 2 / 2 := by
          have hd : ∀ t : ℝ, HasDerivAt (fun s : ℝ => s ^ 2 / 2) t t := fun t => by
            convert ((hasDerivAt_pow 2 t).div_const (2 : ℝ)) using 1; ring
          have := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
            (continuous_id.intervalIntegrable 0 ε)
          simpa using this
        rw [hconst, intervalIntegral.integral_const_mul, hid]
        ring

/-- **Proposition 1 (Directional derivative, Lemma A.3)**:
The right directional derivative of `Φ` along `θ' - θ` at `θ` equals
`n * ∑_j ∫_a^1 (θ'_j(v) - θ_j(v)) s_j(v) f(v) dv`. -/
theorem prop1_potential_deriv (r : Fin M.m → ℝ) (hr0 : ∀ j, 0 ≤ r j) (hr1 : ∀ j, r j ≤ 1)
    (θ θ' : VisitStrategy M) :
    HasDerivWithinAt
      (fun ε => ∑ j : Fin M.m, ∫ v in (r j)..1,
        (1 - (effDist M θ j v + ε * (effDist M θ' j v - effDist M θ j v)) ^ M.n))
      ((M.n : ℝ) * ∑ j : Fin M.m, ∫ v in M.a..1,
        (θ'.θ j v - θ.θ j v) * surplus M (SPA (r j) (hr0 j) (hr1 j)) (effDist M θ j) v * M.f v)
      (Icc 0 1) 0 := by
  have hFub : ∀ j : Fin M.m,
      ∫ v in M.a..1,
        (θ'.θ j v - θ.θ j v) * surplus M (SPA (r j) (hr0 j) (hr1 j)) (effDist M θ j) v * M.f v =
      ∫ v in (r j)..1, (effDist M θ j v) ^ (M.n - 1) * (effDist M θ j v - effDist M θ' j v) := by
    intro j
    have hg_int : IntervalIntegrable (fun u => (θ'.θ j u - θ.θ j u) * M.f u)
        volume (min M.a (r j)) 1 := by
      have hmin1 : min M.a (r j) ≤ 1 := min_le_of_left_le M.ha1.le
      have h1 := θ'.mul_f_intervalIntegrable j hmin1 le_rfl
      have h2 := θ.mul_f_intervalIntegrable j hmin1 le_rfl
      have hsub := h1.sub h2
      have hfun : (fun u => θ'.θ j u * M.f u - θ.θ j u * M.f u) =
          (fun u => (θ'.θ j u - θ.θ j u) * M.f u) := by ext u; ring
      rwa [hfun] at hsub
    have hswap := fubini_tail_integral M.ha0 M.ha1 (hr0 j) (hr1 j)
      (φ := fun v => (effDist M θ j v) ^ (M.n - 1))
      (g := fun u => (θ'.θ j u - θ.θ j u) * M.f u)
      (((effDist_continuousOn θ j).mono Icc_subset_Iic_self).pow (M.n - 1))
      hg_int
      (fun u hu => by rw [M.hf_below u hu, mul_zero])
    have hL : ∫ v in (r j)..1, (effDist M θ j v) ^ (M.n - 1) *
          (∫ u in v..1, (θ'.θ j u - θ.θ j u) * M.f u) =
        ∫ v in (r j)..1, (effDist M θ j v) ^ (M.n - 1) * (effDist M θ j v - effDist M θ' j v) := by
      apply intervalIntegral.integral_congr
      intro v hv
      dsimp only
      rw [uIcc_of_le (hr1 j)] at hv
      have hsub : ∫ u in v..1, (θ'.θ j u - θ.θ j u) * M.f u =
          effDist M θ j v - effDist M θ' j v := by
        simp_rw [sub_mul]
        rw [intervalIntegral.integral_sub (θ'.mul_f_intervalIntegrable j hv.2 le_rfl)
          (θ.mul_f_intervalIntegrable j hv.2 le_rfl)]
        unfold effDist; ring
      rw [hsub]
    have hR : ∫ u in M.a..1, (θ'.θ j u - θ.θ j u) * M.f u *
          (∫ v in (r j)..(max u (r j)), (effDist M θ j v) ^ (M.n - 1)) =
        ∫ u in M.a..1,
          (θ'.θ j u - θ.θ j u) * surplus M (SPA (r j) (hr0 j) (hr1 j)) (effDist M θ j) u * M.f u := by
      apply intervalIntegral.integral_congr
      intro u hu
      dsimp only
      rw [uIcc_of_le M.ha1.le] at hu
      rw [surplus_SPA_eq M (r j) (hr0 j) (hr1 j) (effDist M θ j)
        (vs_effDist_monotoneOn θ j) (fun x hx => effDist_nonneg θ j hx) (M.ha0.trans hu.1) hu.2]
      ring
    linarith [hswap, hL, hR]
  simp_rw [hFub, Finset.mul_sum]
  apply HasDerivWithinAt.fun_sum
  intro j _
  rw [hasDerivWithinAt_iff_tendsto_slope]
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro η hη
  let C : ℝ := (M.n : ℝ) * (M.n : ℝ) * 3 ^ M.n * (1 - r j) + 1
  have hCpos : 0 < C := by
    have : 0 ≤ (M.n : ℝ) * (M.n : ℝ) * 3 ^ M.n * (1 - r j) := by
      have : 0 ≤ 1 - r j := sub_nonneg.mpr (hr1 j)
      positivity
    linarith
  refine ⟨η / C, div_pos hη hCpos, fun ε hεmem hεdist => ?_⟩
  simp only [Set.mem_sdiff, mem_Icc, mem_singleton_iff] at hεmem
  have hεpos : 0 < ε := lt_of_le_of_ne hεmem.1.1 (Ne.symm hεmem.2)
  have hε1 : ε ≤ 1 := hεmem.1.2
  rw [Real.dist_eq, sub_zero, abs_of_pos hεpos] at hεdist
  rw [Real.dist_eq, slope_def_field]
  simp only [zero_mul, add_zero, sub_zero]
  have hFθ : ContinuousOn (effDist M θ j) (Icc (r j) 1) :=
    (effDist_continuousOn θ j).mono Icc_subset_Iic_self
  have hFθ' : ContinuousOn (effDist M θ' j) (Icc (r j) 1) :=
    (effDist_continuousOn θ' j).mono Icc_subset_Iic_self
  have hcont0 : ContinuousOn (fun v => 1 - (effDist M θ j v) ^ M.n) (Icc (r j) 1) :=
    potential_integrand_continuousOn M r θ j
  have hcontε : ContinuousOn
      (fun v => 1 - (effDist M θ j v + ε * (effDist M θ' j v - effDist M θ j v)) ^ M.n)
      (Icc (r j) 1) :=
    continuousOn_const.sub ((hFθ.add (continuousOn_const.mul (hFθ'.sub hFθ))).pow M.n)
  have hcontD : ContinuousOn
      (fun v => (effDist M θ j v) ^ (M.n - 1) * (effDist M θ j v - effDist M θ' j v))
      (Icc (r j) 1) :=
    (hFθ.pow (M.n - 1)).mul (hFθ.sub hFθ')
  let rem : ℝ → ℝ := fun v =>
    (effDist M θ j v + ε * (effDist M θ' j v - effDist M θ j v)) ^ M.n -
    (effDist M θ j v) ^ M.n -
    (M.n : ℝ) * (effDist M θ j v) ^ (M.n - 1) * (ε * (effDist M θ' j v - effDist M θ j v))
  have hnum : (∫ v in (r j)..1,
        (1 - (effDist M θ j v + ε * (effDist M θ' j v - effDist M θ j v)) ^ M.n)) -
      (∫ v in (r j)..1, (1 - (effDist M θ j v) ^ M.n)) -
      ε * ((M.n : ℝ) * ∫ v in (r j)..1,
        (effDist M θ j v) ^ (M.n - 1) * (effDist M θ j v - effDist M θ' j v)) =
      - ∫ v in (r j)..1, rem v := by
    have h1 := hcontε.intervalIntegrable_of_Icc (μ := volume) (hr1 j)
    have h2 := hcont0.intervalIntegrable_of_Icc (μ := volume) (hr1 j)
    have h3 := hcontD.intervalIntegrable_of_Icc (μ := volume) (hr1 j)
    rw [← intervalIntegral.integral_sub h1 h2, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (h1.sub h2) ((h3.const_mul _).const_mul _),
      ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro v _; simp only [rem]; ring
  have hdiv : ((∫ v in (r j)..1,
        (1 - (effDist M θ j v + ε * (effDist M θ' j v - effDist M θ j v)) ^ M.n)) -
      (∫ v in (r j)..1, (1 - (effDist M θ j v) ^ M.n))) / ε -
      (M.n : ℝ) * ∫ v in (r j)..1,
        (effDist M θ j v) ^ (M.n - 1) * (effDist M θ j v - effDist M θ' j v) =
      (- ∫ v in (r j)..1, rem v) / ε := by
    rw [← hnum]; field_simp [hεpos.ne']
  rw [hdiv, abs_div, abs_neg, abs_of_pos hεpos]
  have hrem_cont : ContinuousOn rem (Icc (r j) 1) :=
    (((hFθ.add (continuousOn_const.mul (hFθ'.sub hFθ))).pow M.n).sub (hFθ.pow M.n)).sub
      ((continuousOn_const.mul (hFθ.pow (M.n - 1))).mul (continuousOn_const.mul (hFθ'.sub hFθ)))
  have hbound_int : |∫ v in (r j)..1, rem v| ≤
      (M.n : ℝ) * (M.n : ℝ) * 3 ^ M.n * ε ^ 2 * (1 - r j) := by
    calc |∫ v in (r j)..1, rem v|
        ≤ ∫ v in (r j)..1, |rem v| := intervalIntegral.abs_integral_le_integral_abs (hr1 j)
      _ ≤ ∫ _ in (r j)..1, ((M.n : ℝ) * (M.n : ℝ) * 3 ^ M.n * ε ^ 2) := by
          apply intervalIntegral.integral_mono_on (hr1 j)
            (hrem_cont.abs.intervalIntegrable_of_Icc (hr1 j)) intervalIntegrable_const
          intro v hv
          have h1 : |effDist M θ j v| ≤ 1 := by
            rw [abs_of_nonneg (effDist_nonneg θ j hv.2)]; exact effDist_le_one θ j hv.2
          have h2 : |effDist M θ' j v - effDist M θ j v| ≤ 2 := by
            calc |effDist M θ' j v - effDist M θ j v|
                ≤ |effDist M θ' j v| + |effDist M θ j v| := abs_sub _ _
              _ ≤ 1 + 1 := by
                  rw [abs_of_nonneg (effDist_nonneg θ' j hv.2), abs_of_nonneg (effDist_nonneg θ j hv.2)]
                  linarith [effDist_le_one θ' j hv.2, effDist_le_one θ j hv.2]
              _ = 2 := by norm_num
          exact pow_taylor_bound M.hn h1 h2 hεpos.le hε1
      _ = (M.n : ℝ) * (M.n : ℝ) * 3 ^ M.n * ε ^ 2 * (1 - r j) := by
          simp [mul_comm, mul_assoc, mul_left_comm]
  calc |∫ v in (r j)..1, rem v| / ε
      ≤ ((M.n : ℝ) * (M.n : ℝ) * 3 ^ M.n * ε ^ 2 * (1 - r j)) / ε :=
        div_le_div_of_nonneg_right hbound_int hεpos.le
    _ = (M.n : ℝ) * (M.n : ℝ) * 3 ^ M.n * (1 - r j) * ε := by
        field_simp [hεpos.ne']
    _ ≤ C * ε := by
        apply mul_le_mul_of_nonneg_right _ hεpos.le
        simp only [C]; linarith
    _ < C * (η / C) := mul_lt_mul_of_pos_left hεdist hCpos
    _ = η := mul_div_cancel₀ η hCpos.ne'

/-- Helper: constructing a measurable best-response visit strategy that puts mass `1` on the
smallest index `k : Fin M.m` maximizing `s k v`. -/
noncomputable def argmaxVisit (M : Market) (s : Fin M.m → ℝ → ℝ)
    (hs_meas : ∀ j, Measurable (s j)) : VisitStrategy M where
  θ j v := if (∀ k : Fin M.m, s k v ≤ s j v) ∧ (∀ k : Fin M.m, k < j → s k v < s j v)
    then 1 else 0
  hmeas j := by
    have hset : MeasurableSet
        {v : ℝ | (∀ k : Fin M.m, s k v ≤ s j v) ∧ (∀ k : Fin M.m, k < j → s k v < s j v)} := by
      have h1 : MeasurableSet {v : ℝ | ∀ k : Fin M.m, s k v ≤ s j v} := by
        rw [show {v : ℝ | ∀ k : Fin M.m, s k v ≤ s j v} = ⋂ k : Fin M.m, {v | s k v ≤ s j v} by
          ext v; simp]
        exact MeasurableSet.iInter fun k => measurableSet_le (hs_meas k) (hs_meas j)
      have h2 : MeasurableSet {v : ℝ | ∀ k : Fin M.m, k < j → s k v < s j v} := by
        rw [show {v : ℝ | ∀ k : Fin M.m, k < j → s k v < s j v} =
          ⋂ k : Fin M.m, ⋂ (_ : k < j), {v | s k v < s j v} by ext v; simp]
        exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
          measurableSet_lt (hs_meas k) (hs_meas j)
      exact h1.inter h2
    exact measurable_const.ite hset measurable_const
  hnonneg j v := by split_ifs <;> norm_num
  hsum v _ := by
    have hm0 : 0 < M.m := lt_of_lt_of_le (by decide : 0 < 2) M.hm
    have hne : (Finset.univ : Finset (Fin M.m)).Nonempty := ⟨⟨0, hm0⟩, Finset.mem_univ _⟩
    obtain ⟨jmax, _, hjmax⟩ := Finset.exists_max_image Finset.univ (fun k => s k v) hne
    let S : Finset (Fin M.m) := Finset.univ.filter (fun k => ∀ l : Fin M.m, s l v ≤ s k v)
    have hSne : S.Nonempty := ⟨jmax, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, fun l => hjmax l (Finset.mem_univ l)⟩⟩
    let j0 := S.min' hSne
    have hj0_mem : j0 ∈ S := Finset.min'_mem S hSne
    have hj0_max : ∀ l : Fin M.m, s l v ≤ s j0 v := (Finset.mem_filter.mp hj0_mem).2
    have hj0_lt : ∀ k : Fin M.m, k < j0 → s k v < s j0 v := by
      intro k hk
      refine lt_of_le_of_ne (hj0_max k) ?_
      intro heq
      have hkS : k ∈ S := Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, fun l => by rw [heq]; exact hj0_max l⟩
      exact not_le.mpr hk (Finset.min'_le S k hkS)
    rw [Finset.sum_eq_single j0]
    · rw [ite_eq_left_iff.mpr (fun h => absurd ⟨hj0_max, hj0_lt⟩ h)]
    · intro j _ hne_j
      rw [ite_eq_right_iff]
      rintro ⟨hmax, hlt⟩
      exfalso
      rcases lt_or_gt_of_ne hne_j with h | h
      · exact not_lt.mpr (hmax j0) (hj0_lt j h)
      · exact not_lt.mpr (hj0_max j) (hlt j0 h)
    · intro h; exact absurd (Finset.mem_univ j0) h

lemma argmaxVisit_sum_eq_max (M : Market) (s : Fin M.m → ℝ → ℝ)
    (hs_meas : ∀ j, Measurable (s j)) {v : ℝ} (hv : v ∈ Icc M.a 1) :
    ∀ k : Fin M.m, s k v ≤ ∑ j : Fin M.m, (argmaxVisit M s hs_meas).θ j v * s j v := by
  intro k
  have hsum1 := (argmaxVisit M s hs_meas).hsum v hv
  have hle : ∑ j : Fin M.m, (argmaxVisit M s hs_meas).θ j v * s k v ≤
      ∑ j : Fin M.m, (argmaxVisit M s hs_meas).θ j v * s j v := by
    apply Finset.sum_le_sum
    intro j _
    unfold argmaxVisit; simp only
    split_ifs with h
    · linarith [h.1 k]
    · simp
  rw [← Finset.sum_mul, hsum1, one_mul] at hle
  exact hle

/-- **Proposition 1 (SR iff maximizes Φ)**: Under `SPA(r_j)`, a visit strategy `θ` is
sequentially rational if and only if it maximizes the potential `Φ`. -/
theorem prop1_sr_iff_max_potential (r : Fin M.m → ℝ) (hr0 : ∀ j, 0 ≤ r j) (hr1 : ∀ j, r j ≤ 1)
    (θ : VisitStrategy M) :
    IsSR M (fun j => SPA (r j) (hr0 j) (hr1 j)) θ ↔
      ∀ θ' : VisitStrategy M, potential M r θ' ≤ potential M r θ := by
  let s : Fin M.m → ℝ → ℝ := fun j v => surplus M (SPA (r j) (hr0 j) (hr1 j)) (effDist M θ j) v
  have hs_cont : ∀ j, ContinuousOn (s j) (Iic 1) := fun j =>
    surplus_continuousOn M _ _ (vs_effDist_monotoneOn θ j)
      (fun v hv => effDist_nonneg θ j hv) (fun v hv => effDist_le_one θ j hv)
  have hm0 : 0 < M.m := lt_of_lt_of_le (by decide : 0 < 2) M.hm
  have hneBot : NeBot (𝓝[Ioc (0 : ℝ) 1] 0) := left_nhdsWithin_Ioc_neBot zero_lt_one
  constructor
  · -- Necessity: SR ⇒ maximizes Φ
    intro hSR θ'
    have hderiv := prop1_potential_deriv M r hr0 hr1 θ θ'
    have hD_le : (M.n : ℝ) * ∑ j : Fin M.m, ∫ v in M.a..1, (θ'.θ j v - θ.θ j v) * s j v * M.f v ≤ 0 := by
      have hint : ∀ j : Fin M.m,
          IntervalIntegrable (fun v => (θ'.θ j v - θ.θ j v) * s j v * M.f v) volume M.a 1 := by
        intro j
        have h1 : IntervalIntegrable (fun v => (θ'.θ j v - θ.θ j v) * M.f v) volume M.a 1 := by
          have hsub := (θ'.mul_f_intervalIntegrable j M.ha1.le le_rfl).sub
            (θ.mul_f_intervalIntegrable j M.ha1.le le_rfl)
          have hfun : (fun v => θ'.θ j v * M.f v - θ.θ j v * M.f v) =
              (fun v => (θ'.θ j v - θ.θ j v) * M.f v) := by ext v; ring
          rwa [hfun] at hsub
        have hs_c : ContinuousOn (s j) (uIcc M.a 1) := by
          rw [uIcc_of_le M.ha1.le]; exact (hs_cont j).mono Icc_subset_Iic_self
        have := h1.mul_continuousOn hs_c
        simpa [mul_assoc, mul_comm, mul_left_comm] using this
      rw [← intervalIntegral.integral_finsetSum (fun j _ => hint j)]
      apply mul_nonpos_of_nonneg_of_nonpos M.n_pos_real.le
      rw [intervalIntegral.integral_of_le M.ha1.le]
      apply MeasureTheory.integral_nonpos_of_ae
      have hSR_Ioc : ∀ᵐ v ∂(volume.restrict (Ioc M.a 1)),
          ∀ j k : Fin M.m, 0 < θ.θ j v → s k v ≤ s j v :=
        MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono Ioc_subset_Icc_self le_rfl) hSR
      filter_upwards [hSR_Ioc, MeasureTheory.ae_restrict_mem measurableSet_Ioc] with v hv hmem
      have hmemIcc : v ∈ Icc M.a 1 := Ioc_subset_Icc_self hmem
      have hne : (Finset.univ : Finset (Fin M.m)).Nonempty := ⟨⟨0, hm0⟩, Finset.mem_univ _⟩
      obtain ⟨jmax, _, hjmax⟩ := Finset.exists_max_image Finset.univ (fun k => s k v) hne
      have hsum_θ : ∑ j : Fin M.m, θ.θ j v * s j v = s jmax v := by
        have hterm : ∀ j : Fin M.m, θ.θ j v * s j v = θ.θ j v * s jmax v := by
          intro j
          rcases eq_or_lt_of_le (θ.hnonneg j v) with h0 | hpos
          · rw [← h0, zero_mul, zero_mul]
          · congr 1; exact le_antisymm (hjmax j (Finset.mem_univ j)) (hv j jmax hpos)
        simp_rw [hterm, ← Finset.sum_mul, θ.hsum v hmemIcc, one_mul]
      have hsum_θ' : ∑ j : Fin M.m, θ'.θ j v * s j v ≤ s jmax v := by
        calc ∑ j : Fin M.m, θ'.θ j v * s j v
            ≤ ∑ j : Fin M.m, θ'.θ j v * s jmax v := by
              apply Finset.sum_le_sum; intro j _
              exact mul_le_mul_of_nonneg_left (hjmax j (Finset.mem_univ j)) (θ'.hnonneg j v)
          _ = s jmax v := by rw [← Finset.sum_mul, θ'.hsum v hmemIcc, one_mul]
      have hdiff : ∑ j : Fin M.m, (θ'.θ j v - θ.θ j v) * s j v * M.f v =
          (∑ j : Fin M.m, θ'.θ j v * s j v - ∑ j : Fin M.m, θ.θ j v * s j v) * M.f v := by
        rw [← Finset.sum_mul, ← Finset.sum_sub_distrib]
        congr 1; apply Finset.sum_congr rfl; intro j _; ring
      rw [hdiff]
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (M.f_nonneg_Iic hmemIcc.2)
    let g : ℝ → ℝ := fun ε => ∑ j : Fin M.m, ∫ v in (r j)..1,
      (1 - (effDist M θ j v + ε * (effDist M θ' j v - effDist M θ j v)) ^ M.n)
    have hg0 : g 0 = potential M r θ := by simp [g, potential]
    have hslope_ge : ∀ ε ∈ Ioc (0 : ℝ) 1, potential M r θ' - potential M r θ ≤ slope g 0 ε := by
      intro ε hε
      have hconc := prop1_potential_concave M r hr1 θ θ' hε.1.le hε.2
      have hgeq : potential M r (θ.mix θ' ε hε.1.le hε.2) = g ε := by
        unfold potential g
        apply Finset.sum_congr rfl; intro j _
        apply intervalIntegral.integral_congr; intro v hv
        dsimp only
        rw [uIcc_of_le (hr1 j)] at hv
        rw [effDist_mix θ θ' hε.1.le hε.2 j hv.2]; ring
      rw [hgeq] at hconc
      rw [slope_def_field, sub_zero, hg0, le_div_iff₀ hε.1]
      linarith
    have htend := (hasDerivWithinAt_iff_tendsto_slope.mp hderiv).mono_left
      (nhdsWithin_mono 0 (show Ioc (0 : ℝ) 1 ⊆ Icc 0 1 \ {0} by
        intro x hx; exact ⟨⟨hx.1.le, hx.2⟩, hx.1.ne'⟩))
    have hle_lim : potential M r θ' - potential M r θ ≤
        (M.n : ℝ) * ∑ j : Fin M.m, ∫ v in M.a..1, (θ'.θ j v - θ.θ j v) * s j v * M.f v :=
      ge_of_tendsto htend (eventually_nhdsWithin_of_forall fun ε hε => hslope_ge ε hε)
    linarith
  · -- Sufficiency: maximizes Φ ⇒ SR
    intro hmax
    let st : Fin M.m → ℝ → ℝ := fun j v => if v ∈ Icc M.a 1 then s j v else 0
    have hst_meas : ∀ j, Measurable (st j) := fun j =>
      ((hs_cont j).mono Icc_subset_Iic_self).measurable_piecewise continuousOn_const measurableSet_Icc
    let θ' := argmaxVisit M st hst_meas
    have hderiv := prop1_potential_deriv M r hr0 hr1 θ θ'
    let g : ℝ → ℝ := fun ε => ∑ j : Fin M.m, ∫ v in (r j)..1,
      (1 - (effDist M θ j v + ε * (effDist M θ' j v - effDist M θ j v)) ^ M.n)
    have hslope_le : ∀ ε ∈ Ioc (0 : ℝ) 1, slope g 0 ε ≤ 0 := by
      intro ε hε
      have hm := hmax (θ.mix θ' ε hε.1.le hε.2)
      have hgeq : potential M r (θ.mix θ' ε hε.1.le hε.2) = g ε := by
        unfold potential g
        apply Finset.sum_congr rfl; intro j _
        apply intervalIntegral.integral_congr; intro v hv
        dsimp only
        rw [uIcc_of_le (hr1 j)] at hv
        rw [effDist_mix θ θ' hε.1.le hε.2 j hv.2]; ring
      rw [slope_def_field, sub_zero, show g 0 = potential M r θ by simp [g, potential]]
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) hε.1.le
    have htend := (hasDerivWithinAt_iff_tendsto_slope.mp hderiv).mono_left
      (nhdsWithin_mono 0 (show Ioc (0 : ℝ) 1 ⊆ Icc 0 1 \ {0} by
        intro x hx; exact ⟨⟨hx.1.le, hx.2⟩, hx.1.ne'⟩))
    have hD_le : (M.n : ℝ) * ∑ j : Fin M.m,
        ∫ v in M.a..1, (θ'.θ j v - θ.θ j v) * s j v * M.f v ≤ 0 :=
      le_of_tendsto htend (eventually_nhdsWithin_of_forall fun ε hε => hslope_le ε hε)
    have hint : ∀ j : Fin M.m,
        IntervalIntegrable (fun v => (θ'.θ j v - θ.θ j v) * s j v * M.f v) volume M.a 1 := by
      intro j
      have h1 : IntervalIntegrable (fun v => (θ'.θ j v - θ.θ j v) * M.f v) volume M.a 1 := by
        have hsub := (θ'.mul_f_intervalIntegrable j M.ha1.le le_rfl).sub
          (θ.mul_f_intervalIntegrable j M.ha1.le le_rfl)
        have hfun : (fun v => θ'.θ j v * M.f v - θ.θ j v * M.f v) =
            (fun v => (θ'.θ j v - θ.θ j v) * M.f v) := by ext v; ring
        rwa [hfun] at hsub
      have hs_c : ContinuousOn (s j) (uIcc M.a 1) := by
        rw [uIcc_of_le M.ha1.le]; exact (hs_cont j).mono Icc_subset_Iic_self
      have := h1.mul_continuousOn hs_c
      simpa [mul_assoc, mul_comm, mul_left_comm] using this
    rw [← intervalIntegral.integral_finsetSum (fun j _ => hint j)] at hD_le
    have hint_le : ∫ v in M.a..1, ∑ j : Fin M.m, (θ'.θ j v - θ.θ j v) * s j v * M.f v ≤ 0 :=
      nonpos_of_mul_nonpos_right hD_le M.n_pos_real
    have hnn : ∀ v ∈ Icc M.a 1, 0 ≤ ∑ j : Fin M.m, (θ'.θ j v - θ.θ j v) * s j v * M.f v := by
      intro v hv
      have harg : ∀ k, s k v ≤ ∑ j : Fin M.m, θ'.θ j v * s j v := by
        intro k
        have h1 := argmaxVisit_sum_eq_max M st hst_meas hv k
        have hst_eq : ∀ l, st l v = s l v := fun l => if_pos hv
        simpa only [θ', hst_eq] using h1
      have hle : ∑ j : Fin M.m, θ.θ j v * s j v ≤ ∑ j : Fin M.m, θ'.θ j v * s j v := by
        calc ∑ j : Fin M.m, θ.θ j v * s j v
            ≤ ∑ j : Fin M.m, θ.θ j v * (∑ l : Fin M.m, θ'.θ l v * s l v) := by
              apply Finset.sum_le_sum; intro j _
              exact mul_le_mul_of_nonneg_left (harg j) (θ.hnonneg j v)
          _ = ∑ l : Fin M.m, θ'.θ l v * s l v := by rw [← Finset.sum_mul, θ.hsum v hv, one_mul]
      have hrew : ∑ j : Fin M.m, (θ'.θ j v - θ.θ j v) * s j v * M.f v =
          (∑ j : Fin M.m, θ'.θ j v * s j v - ∑ j : Fin M.m, θ.θ j v * s j v) * M.f v := by
        rw [← Finset.sum_mul, ← Finset.sum_sub_distrib]
        congr 1; apply Finset.sum_congr rfl; intro j _; ring
      rw [hrew]
      exact mul_nonneg (by linarith) (M.hf_pos v hv).le
    have hint_eq0 : ∫ v in Icc M.a 1, ∑ j : Fin M.m, (θ'.θ j v - θ.θ j v) * s j v * M.f v = 0 := by
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le M.ha1.le]
      exact le_antisymm hint_le (intervalIntegral.integral_nonneg M.ha1.le hnn)
    have hsum_int : IntegrableOn (fun v => ∑ j : Fin M.m, (θ'.θ j v - θ.θ j v) * s j v * M.f v)
        (Icc M.a 1) volume := by
      rw [integrableOn_Icc_iff_integrableOn_Ioc]
      have h := (IntervalIntegrable.sum Finset.univ (fun j _ => hint j)).1
      have heq : (∑ i : Fin M.m, fun v => (θ'.θ i v - θ.θ i v) * s i v * M.f v) =
          (fun v => ∑ j : Fin M.m, (θ'.θ j v - θ.θ j v) * s j v * M.f v) := by
        ext v; simp [Finset.sum_apply]
      rwa [heq] at h
    have hae0 : (fun v => ∑ j : Fin M.m, (θ'.θ j v - θ.θ j v) * s j v * M.f v) =ᵐ[volume.restrict (Icc M.a 1)] 0 :=
      (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae
        (by change ∀ᵐ v ∂(volume.restrict (Icc M.a 1)),
              (0 : ℝ) ≤ ∑ j : Fin M.m, (θ'.θ j v - θ.θ j v) * s j v * M.f v
            rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
            exact Filter.Eventually.of_forall hnn)
        hsum_int).mp hint_eq0
    filter_upwards [hae0, MeasureTheory.ae_restrict_mem measurableSet_Icc] with v hv0 hmem
    intro j k hjpos
    have harg : ∀ l, s l v ≤ ∑ l' : Fin M.m, θ'.θ l' v * s l' v := by
      intro l
      have h1 := argmaxVisit_sum_eq_max M st hst_meas hmem l
      have hst_eq : ∀ l', st l' v = s l' v := fun l' => if_pos hmem
      simpa only [θ', hst_eq] using h1
    let Mv := ∑ l' : Fin M.m, θ'.θ l' v * s l' v
    have hrew : ∑ l : Fin M.m, (θ'.θ l v - θ.θ l v) * s l v * M.f v =
        (∑ l : Fin M.m, θ.θ l v * (Mv - s l v)) * M.f v := by
      have h1 : ∑ l : Fin M.m, θ.θ l v * (Mv - s l v) =
          Mv - ∑ l : Fin M.m, θ.θ l v * s l v := by
        simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, θ.hsum v hmem, one_mul]
      rw [h1]
      simp only [Mv]; rw [← Finset.sum_mul, ← Finset.sum_sub_distrib]
      congr 1; apply Finset.sum_congr rfl; intro l _; ring
    change ∑ l : Fin M.m, (θ'.θ l v - θ.θ l v) * s l v * M.f v = 0 at hv0
    rw [hrew] at hv0
    have hsum0 : ∑ l : Fin M.m, θ.θ l v * (Mv - s l v) = 0 :=
      (mul_eq_zero.mp hv0).resolve_right (M.hf_pos v hmem).ne'
    have hterm0 : θ.θ j v * (Mv - s j v) = 0 := by
      have hterm_nn : ∀ l ∈ (Finset.univ : Finset (Fin M.m)), 0 ≤ θ.θ l v * (Mv - s l v) :=
        fun l _ => mul_nonneg (θ.hnonneg l v) (sub_nonneg.mpr (harg l))
      exact (Finset.sum_eq_zero_iff_of_nonneg hterm_nn).mp hsum0 j (Finset.mem_univ j)
    have hsj_eq : s j v = Mv := by
      have := (mul_eq_zero.mp hterm0).resolve_left hjpos.ne'
      linarith
    change s k v ≤ s j v
    rw [hsj_eq]
    exact harg k

/-- **Proposition 1 (Uniqueness of effective distributions)**: Any two SR strategies under
`SPA(r_j)` induce the same effective distribution on `[r_j, 1]` for every seller `j`. -/
theorem prop1_effDist_unique (r : Fin M.m → ℝ) (hr0 : ∀ j, 0 ≤ r j) (hr1 : ∀ j, r j ≤ 1)
    {θ θ' : VisitStrategy M}
    (hθ : IsSR M (fun j => SPA (r j) (hr0 j) (hr1 j)) θ)
    (hθ' : IsSR M (fun j => SPA (r j) (hr0 j) (hr1 j)) θ') :
    ∀ j : Fin M.m, ∀ v ∈ Icc (r j) 1, effDist M θ j v = effDist M θ' j v := by
  have hmax := (prop1_sr_iff_max_potential M r hr0 hr1 θ).mp hθ
  have hmax' := (prop1_sr_iff_max_potential M r hr0 hr1 θ').mp hθ'
  have hno_diff : ∀ j : Fin M.m, ∀ v ∈ Ioo (r j) 1, effDist M θ j v = effDist M θ' j v := by
    by_contra h
    push Not at h
    have hstrict := prop1_potential_strict_midpoint M r hr1 θ θ' h
    have hle1 := hmax (θ.mix θ' (1 / 2) (by norm_num) (by norm_num))
    have hle2 := hmax' (θ.mix θ' (1 / 2) (by norm_num) (by norm_num))
    linarith
  intro j v hv
  rcases eq_or_lt_of_le (hr1 j) with heq | hlt
  · have : v = 1 := le_antisymm hv.2 (heq ▸ hv.1)
    rw [this, vs_effDist_one, vs_effDist_one]
  · rcases eq_or_lt_of_le hv.1 with rfl | hv1
    · have hcont : ContinuousOn (fun x => effDist M θ j x - effDist M θ' j x) (Icc (r j) 1) :=
        ((effDist_continuousOn θ j).mono Icc_subset_Iic_self).sub
          ((effDist_continuousOn θ' j).mono Icc_subset_Iic_self)
      have h0 : effDist M θ j (r j) - effDist M θ' j (r j) = 0 := by
        have htend : Tendsto (fun x => effDist M θ j x - effDist M θ' j x)
            (𝓝[Ioo (r j) 1] (r j)) (𝓝 (effDist M θ j (r j) - effDist M θ' j (r j))) :=
          (hcont (r j) (left_mem_Icc.mpr hlt.le)).mono_left (nhdsWithin_mono _ Ioo_subset_Icc_self)
        have hzero : Tendsto (fun x => effDist M θ j x - effDist M θ' j x)
            (𝓝[Ioo (r j) 1] (r j)) (𝓝 0) :=
          tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun x hx => by
            dsimp only; rw [hno_diff j x hx, sub_self])
        have : NeBot (𝓝[Ioo (r j) 1] (r j)) := left_nhdsWithin_Ioo_neBot hlt
        exact tendsto_nhds_unique htend hzero
      linarith
    · rcases eq_or_lt_of_le hv.2 with rfl | hv2
      · rw [vs_effDist_one, vs_effDist_one]
      · exact hno_diff j v ⟨hv1, hv2⟩

/-- **Proposition 1(i)**: Under a common reserve `ρ`, the uniform split is SR and every SR
continuation induces `F_j = A` on `[ρ, 1]`. -/
theorem prop1_symmetric (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    IsSR M (fun _ => SPA ρ hρ0 hρ1) (uniformVisit M) ∧
    ∀ θ : VisitStrategy M, IsSR M (fun _ => SPA ρ hρ0 hρ1) θ →
      ∀ j : Fin M.m, ∀ v ∈ Icc ρ 1, effDist M θ j v = M.A v := by
  have hunif : IsSR M (fun _ => SPA ρ hρ0 hρ1) (uniformVisit M) := by
    rw [IsSR, MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    refine Filter.Eventually.of_forall fun v hv j k _ => ?_
    have heq : surplus M (SPA ρ hρ0 hρ1) (effDist M (uniformVisit M) k) v =
        surplus M (SPA ρ hρ0 hρ1) (effDist M (uniformVisit M) j) v := by
      rw [surplus_SPA_eq M ρ hρ0 hρ1 _ (vs_effDist_monotoneOn _ _) (fun x hx => effDist_nonneg _ _ hx)
            (M.ha0.trans hv.1) hv.2,
          surplus_SPA_eq M ρ hρ0 hρ1 _ (vs_effDist_monotoneOn _ _) (fun x hx => effDist_nonneg _ _ hx)
            (M.ha0.trans hv.1) hv.2]
      apply intervalIntegral.integral_congr; intro t ht
      dsimp only
      have ht1 : t ≤ 1 := by
        rw [uIcc_of_le (le_max_right v ρ)] at ht
        exact ht.2.trans (max_le hv.2 hρ1)
      rw [effDist_uniformVisit M k ht1, effDist_uniformVisit M j ht1]
    exact le_of_eq heq
  refine ⟨hunif, fun θ hθ j v hv => ?_⟩
  rw [prop1_effDist_unique M (fun _ => ρ) (fun _ => hρ0) (fun _ => hρ1) hθ hunif j v hv,
    effDist_uniformVisit M j hv.2]

/-! #### Proposition 1(ii): Cutoffs `w` for `r₁ > ρ` (eq. (12)) and `r₁ < ρ` (eq. (13)) -/

/-- Helper: Lipschitz bound `|x^(n-1) - y^(n-1)| ≤ (n - 1) * |x - y|` on `[0, 1]`. -/
lemma pow_sub_one_lipschitz {n : ℕ} (hn : 2 ≤ n) {x y : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    |x ^ (n - 1) - y ^ (n - 1)| ≤ ((n : ℝ) - 1) * |x - y| := by
  have hgeom : x ^ (n - 1) - y ^ (n - 1) =
      (x - y) * ∑ k ∈ Finset.range (n - 1), x ^ k * y ^ (n - 1 - 1 - k) := by
    rw [mul_comm, geom_sum₂_mul]
  rw [hgeom, abs_mul]
  have hsum : |∑ k ∈ Finset.range (n - 1), x ^ k * y ^ (n - 1 - 1 - k)| ≤ ((n - 1 : ℕ) : ℝ) := by
    calc |∑ k ∈ Finset.range (n - 1), x ^ k * y ^ (n - 1 - 1 - k)|
        ≤ ∑ k ∈ Finset.range (n - 1), |x ^ k * y ^ (n - 1 - 1 - k)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k ∈ Finset.range (n - 1), (1 : ℝ) := by
          apply Finset.sum_le_sum; intro k _
          rw [abs_of_nonneg (mul_nonneg (pow_nonneg hx0 _) (pow_nonneg hy0 _))]
          calc x ^ k * y ^ (n - 1 - 1 - k)
              ≤ 1 * 1 := mul_le_mul (pow_le_one₀ hx0 hx1) (pow_le_one₀ hy0 hy1)
                (pow_nonneg hy0 _) zero_le_one
            _ = 1 := one_mul 1
      _ = ((n - 1 : ℕ) : ℝ) := by simp
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]; simp
  rw [hcast] at hsum
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right hsum (abs_nonneg _)

/-- Rival effective distribution below cutoff `w` when `r₁ > ρ` (eq. (12)). -/
noncomputable def FrivGt (w v : ℝ) : ℝ :=
  M.A w - (M.F w - M.F v) / ((M.m : ℝ) - 1)

/-- Indifference function `h(w)` for `r₁ > ρ` (eq. (12)). -/
noncomputable def hGt (ρ r₁ w : ℝ) : ℝ :=
  (w - r₁) * (M.A w) ^ (M.n - 1) - ∫ v in ρ..w, (FrivGt M w v) ^ (M.n - 1)

lemma FrivGt_eq (w v : ℝ) :
    FrivGt M w v = 1 - 1 / (M.m : ℝ) - M.F w / ((M.m : ℝ) * ((M.m : ℝ) - 1)) +
      M.F v / ((M.m : ℝ) - 1) := by
  unfold FrivGt Market.A
  have hm : (M.m : ℝ) ≠ 0 := M.m_pos_real.ne'
  have hm1 : (M.m : ℝ) - 1 ≠ 0 := M.m_sub_one_pos_real.ne'
  field_simp [hm, hm1]; ring

lemma FrivGt_self (w : ℝ) : FrivGt M w w = M.A w := by
  simp [FrivGt]

lemma FrivGt_mem_Icc {w v : ℝ} (hvw : v ≤ w) (hw : w ≤ 1) :
    FrivGt M w v ∈ Icc (0 : ℝ) 1 := by
  have hm : (2 : ℝ) ≤ M.m := by exact_mod_cast M.hm
  have hmpos : (0 : ℝ) < M.m := M.m_pos_real
  have hm1 : (0 : ℝ) < (M.m : ℝ) - 1 := M.m_sub_one_pos_real
  have hFw := M.F_mem_Icc_Iic hw
  have hFv := M.F_mem_Icc_Iic (hvw.trans hw)
  have hFmono : M.F v ≤ M.F w := M.F_monotoneOn_Iic (hvw.trans hw) hw hvw
  constructor
  · rw [FrivGt_eq]
    have h1 : M.F w / ((M.m : ℝ) * ((M.m : ℝ) - 1)) ≤ 1 / ((M.m : ℝ) * ((M.m : ℝ) - 1)) :=
      div_le_div_of_nonneg_right hFw.2 (by positivity)
    have h2 : 0 ≤ M.F v / ((M.m : ℝ) - 1) := div_nonneg hFv.1 hm1.le
    have h3 : 1 - 1 / (M.m : ℝ) - 1 / ((M.m : ℝ) * ((M.m : ℝ) - 1)) =
        ((M.m : ℝ) - 2) / ((M.m : ℝ) - 1) := by
      field_simp [hmpos.ne', hm1.ne']; ring
    have h4 : 0 ≤ ((M.m : ℝ) - 2) / ((M.m : ℝ) - 1) := div_nonneg (by linarith) hm1.le
    linarith
  · unfold FrivGt
    have hAw := (M.A_mem_Icc hw).2
    have hnn : 0 ≤ (M.F w - M.F v) / ((M.m : ℝ) - 1) := div_nonneg (by linarith) hm1.le
    linarith

lemma FrivGt_strictMono_v {w v₁ v₂ : ℝ} (hv₁ : v₁ ∈ Icc M.a 1) (hv₂ : v₂ ∈ Icc M.a 1)
    (hlt : v₁ < v₂) : FrivGt M w v₁ < FrivGt M w v₂ := by
  rw [FrivGt_eq, FrivGt_eq]
  have hF := M.F_strictMonoOn hv₁ hv₂ hlt
  have := div_lt_div_of_pos_right hF M.m_sub_one_pos_real
  linarith

lemma FrivGt_strictAnti_w {w₁ w₂ v : ℝ} (hw₁ : w₁ ∈ Icc M.a 1) (hw₂ : w₂ ∈ Icc M.a 1)
    (hlt : w₁ < w₂) : FrivGt M w₂ v < FrivGt M w₁ v := by
  rw [FrivGt_eq, FrivGt_eq]
  have hF := M.F_strictMonoOn hw₁ hw₂ hlt
  have hden : 0 < (M.m : ℝ) * ((M.m : ℝ) - 1) := mul_pos M.m_pos_real M.m_sub_one_pos_real
  have := div_lt_div_of_pos_right hF hden
  linarith

lemma FrivGt_continuousOn_v (w : ℝ) : ContinuousOn (FrivGt M w) (Iic 1) := by
  unfold FrivGt
  exact continuousOn_const.sub ((continuousOn_const.sub M.F_continuousOn_Iic).div_const _)

lemma hGt_continuousOn_w (ρ r₁ : ℝ) (hρ1 : ρ ≤ 1) :
    ContinuousOn (hGt M ρ r₁) (Icc ρ 1) := by
  have hfirst : ContinuousOn (fun w => (w - r₁) * (M.A w) ^ (M.n - 1)) (Icc ρ 1) :=
    (continuousOn_id.sub continuousOn_const).mul
      ((M.A_continuousOn_Iic.mono Icc_subset_Iic_self).pow (M.n - 1))
  refine hfirst.sub ?_
  intro w hw
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  -- Continuity of F at w on Iic 1
  have hFcont := Metric.continuousWithinAt_iff.mp (M.F_continuousOn_Iic w hw.2)
  have hCpos : 0 < ((M.n : ℝ) - 1) / ((M.m : ℝ) * ((M.m : ℝ) - 1)) + 1 := by
    have : 0 ≤ ((M.n : ℝ) - 1) / ((M.m : ℝ) * ((M.m : ℝ) - 1)) :=
      div_nonneg M.n_sub_one_pos_real.le (mul_nonneg M.m_pos_real.le M.m_sub_one_pos_real.le)
    linarith
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := hFcont
    (ε / (2 * (((M.n : ℝ) - 1) / ((M.m : ℝ) * ((M.m : ℝ) - 1)) * (1 - ρ) + 1)))
    (by
      have hden : 0 < 2 * (((M.n : ℝ) - 1) / ((M.m : ℝ) * ((M.m : ℝ) - 1)) * (1 - ρ) + 1) := by
        have : 0 ≤ ((M.n : ℝ) - 1) / ((M.m : ℝ) * ((M.m : ℝ) - 1)) * (1 - ρ) :=
          mul_nonneg (div_nonneg M.n_sub_one_pos_real.le
            (mul_nonneg M.m_pos_real.le M.m_sub_one_pos_real.le)) (sub_nonneg.mpr hρ1)
        linarith
      exact div_pos hε hden)
  refine ⟨min δ₁ (ε / 2), lt_min hδ₁pos (half_pos hε), fun x hx hdist => ?_⟩
  rw [Real.dist_eq] at hdist ⊢
  have hFdist : |M.F x - M.F w| <
      ε / (2 * (((M.n : ℝ) - 1) / ((M.m : ℝ) * ((M.m : ℝ) - 1)) * (1 - ρ) + 1)) := by
    have := hδ₁ hx.2 (lt_of_lt_of_le hdist (min_le_left _ _))
    rwa [Real.dist_eq] at this
  have hxd : |x - w| < ε / 2 := lt_of_lt_of_le hdist (min_le_right _ _)
  have hint_x : ∀ a b, a ≤ 1 → b ≤ 1 →
      IntervalIntegrable (fun v => (FrivGt M x v) ^ (M.n - 1)) volume a b := by
    intro a b ha hb
    exact ((FrivGt_continuousOn_v M x).pow (M.n - 1) |>.mono (by
      intro t ht; rcases le_total a b with hle | hle
      · rw [uIcc_of_le hle] at ht; exact ht.2.trans hb
      · rw [uIcc_comm, uIcc_of_le hle] at ht; exact ht.2.trans ha)).intervalIntegrable
  have hint_w : ∀ a b, a ≤ 1 → b ≤ 1 →
      IntervalIntegrable (fun v => (FrivGt M w v) ^ (M.n - 1)) volume a b := by
    intro a b ha hb
    exact ((FrivGt_continuousOn_v M w).pow (M.n - 1) |>.mono (by
      intro t ht; rcases le_total a b with hle | hle
      · rw [uIcc_of_le hle] at ht; exact ht.2.trans hb
      · rw [uIcc_comm, uIcc_of_le hle] at ht; exact ht.2.trans ha)).intervalIntegrable
  -- Split ∫_ρ^x f(x) - ∫_ρ^w f(w) at min x w
  let m0 := min x w
  have hm0_ρ : ρ ≤ m0 := le_min hx.1 hw.1
  have hm0_1 : m0 ≤ 1 := le_trans (min_le_left _ _) hx.2
  have hdiff_split : (∫ v in ρ..x, (FrivGt M x v) ^ (M.n - 1)) -
      (∫ v in ρ..w, (FrivGt M w v) ^ (M.n - 1)) =
      (∫ v in ρ..m0, ((FrivGt M x v) ^ (M.n - 1) - (FrivGt M w v) ^ (M.n - 1))) +
      ((∫ v in m0..x, (FrivGt M x v) ^ (M.n - 1)) -
       (∫ v in m0..w, (FrivGt M w v) ^ (M.n - 1))) := by
    have hx_sp := intervalIntegral.integral_add_adjacent_intervals
      (hint_x ρ m0 hρ1 hm0_1) (hint_x m0 x hm0_1 hx.2)
    have hw_sp := intervalIntegral.integral_add_adjacent_intervals
      (hint_w ρ m0 hρ1 hm0_1) (hint_w m0 w hm0_1 hw.2)
    rw [intervalIntegral.integral_sub (hint_x ρ m0 hρ1 hm0_1) (hint_w ρ m0 hρ1 hm0_1)]
    linarith
  rw [hdiff_split]
  have hterm1 : |∫ v in ρ..m0, ((FrivGt M x v) ^ (M.n - 1) - (FrivGt M w v) ^ (M.n - 1))| < ε / 2 := by
    have hK : ((M.n : ℝ) - 1) / ((M.m : ℝ) * ((M.m : ℝ) - 1)) * |M.F x - M.F w| * (m0 - ρ) < ε / 2 := by
      have hm0_le : m0 - ρ ≤ 1 - ρ := by linarith
      have hcoeff_nn : 0 ≤ ((M.n : ℝ) - 1) / ((M.m : ℝ) * ((M.m : ℝ) - 1)) :=
        div_nonneg M.n_sub_one_pos_real.le (mul_nonneg M.m_pos_real.le M.m_sub_one_pos_real.le)
      have hden_pos : 0 < ((M.n : ℝ) - 1) / ((M.m : ℝ) * ((M.m : ℝ) - 1)) * (1 - ρ) + 1 := by
        have : 0 ≤ ((M.n : ℝ) - 1) / ((M.m : ℝ) * ((M.m : ℝ) - 1)) * (1 - ρ) :=
          mul_nonneg hcoeff_nn (sub_nonneg.mpr hρ1)
        linarith
      calc ((M.n : ℝ) - 1) / ((M.m : ℝ) * ((M.m : ℝ) - 1)) * |M.F x - M.F w| * (m0 - ρ)
          ≤ ((M.n : ℝ) - 1) / ((M.m : ℝ) * ((M.m : ℝ) - 1)) * (1 - ρ) * |M.F x - M.F w| := by
            have := mul_le_mul_of_nonneg_left hm0_le (mul_nonneg hcoeff_nn (abs_nonneg (M.F x - M.F w)))
            linarith
        _ ≤ (((M.n : ℝ) - 1) / ((M.m : ℝ) * ((M.m : ℝ) - 1)) * (1 - ρ) + 1) * |M.F x - M.F w| := by
            nlinarith [abs_nonneg (M.F x - M.F w)]
        _ < (((M.n : ℝ) - 1) / ((M.m : ℝ) * ((M.m : ℝ) - 1)) * (1 - ρ) + 1) *
              (ε / (2 * (((M.n : ℝ) - 1) / ((M.m : ℝ) * ((M.m : ℝ) - 1)) * (1 - ρ) + 1))) :=
            mul_lt_mul_of_pos_left hFdist hden_pos
        _ = ε / 2 := by
            rw [mul_comm (2 : ℝ), mul_div_assoc', mul_div_mul_left _ _ hden_pos.ne']
    calc |∫ v in ρ..m0, ((FrivGt M x v) ^ (M.n - 1) - (FrivGt M w v) ^ (M.n - 1))|
        ≤ ∫ v in ρ..m0, |(FrivGt M x v) ^ (M.n - 1) - (FrivGt M w v) ^ (M.n - 1)| :=
          intervalIntegral.abs_integral_le_integral_abs hm0_ρ
      _ ≤ ∫ _ in ρ..m0, (((M.n : ℝ) - 1) / ((M.m : ℝ) * ((M.m : ℝ) - 1)) * |M.F x - M.F w|) := by
          apply intervalIntegral.integral_mono_on hm0_ρ
            ((((FrivGt_continuousOn_v M x).pow (M.n - 1)).sub
              ((FrivGt_continuousOn_v M w).pow (M.n - 1))).abs.mono
              (fun t (ht : t ∈ Icc ρ m0) => ht.2.trans hm0_1) |>.intervalIntegrable_of_Icc hm0_ρ)
            intervalIntegrable_const
          intro v hv
          have hvx := FrivGt_mem_Icc M (hv.2.trans (min_le_left _ _)) hx.2
          have hvw := FrivGt_mem_Icc M (hv.2.trans (min_le_right _ _)) hw.2
          have hlip := pow_sub_one_lipschitz M.hn hvx.1 hvx.2 hvw.1 hvw.2
          have hFd : |FrivGt M x v - FrivGt M w v| =
              |M.F x - M.F w| / ((M.m : ℝ) * ((M.m : ℝ) - 1)) := by
            rw [FrivGt_eq, FrivGt_eq]
            have h1 : (1 - 1 / (M.m : ℝ) - M.F x / ((M.m : ℝ) * ((M.m : ℝ) - 1)) +
                M.F v / ((M.m : ℝ) - 1)) -
              (1 - 1 / (M.m : ℝ) - M.F w / ((M.m : ℝ) * ((M.m : ℝ) - 1)) +
                M.F v / ((M.m : ℝ) - 1)) =
              -(M.F x - M.F w) / ((M.m : ℝ) * ((M.m : ℝ) - 1)) := by ring
            rw [h1, abs_div, abs_neg,
              abs_of_pos (mul_pos M.m_pos_real M.m_sub_one_pos_real)]
          rw [hFd] at hlip
          change |(FrivGt M x v) ^ (M.n - 1) - (FrivGt M w v) ^ (M.n - 1)| ≤ _
          linarith [show ((M.n : ℝ) - 1) * (|M.F x - M.F w| / ((M.m : ℝ) * ((M.m : ℝ) - 1))) =
            ((M.n : ℝ) - 1) / ((M.m : ℝ) * ((M.m : ℝ) - 1)) * |M.F x - M.F w| by ring]
      _ = ((M.n : ℝ) - 1) / ((M.m : ℝ) * ((M.m : ℝ) - 1)) * |M.F x - M.F w| * (m0 - ρ) := by
          simp [mul_comm, mul_left_comm]
      _ < ε / 2 := hK
  have hterm2 : |(∫ v in m0..x, (FrivGt M x v) ^ (M.n - 1)) -
      (∫ v in m0..w, (FrivGt M w v) ^ (M.n - 1))| < ε / 2 := by
    rcases le_total x w with hle | hle
    · have hm0_eq : m0 = x := min_eq_left hle
      rw [hm0_eq, intervalIntegral.integral_same, zero_sub, abs_neg]
      have hnn : 0 ≤ ∫ v in x..w, (FrivGt M w v) ^ (M.n - 1) :=
        intervalIntegral.integral_nonneg hle fun v hv =>
          pow_nonneg (FrivGt_mem_Icc M hv.2 hw.2).1 _
      rw [abs_of_nonneg hnn]
      calc ∫ v in x..w, (FrivGt M w v) ^ (M.n - 1)
          ≤ ∫ _ in x..w, (1 : ℝ) := intervalIntegral.integral_mono_on hle
            (hint_w x w hx.2 hw.2) intervalIntegrable_const
            (fun v hv => pow_le_one₀ (FrivGt_mem_Icc M hv.2 hw.2).1 (FrivGt_mem_Icc M hv.2 hw.2).2)
        _ = w - x := by simp
        _ = |x - w| := by rw [abs_of_nonpos (sub_nonpos.mpr hle)]; ring
        _ < ε / 2 := hxd
    · have hm0_eq : m0 = w := min_eq_right hle
      rw [hm0_eq, intervalIntegral.integral_same, sub_zero]
      have hnn : 0 ≤ ∫ v in w..x, (FrivGt M x v) ^ (M.n - 1) :=
        intervalIntegral.integral_nonneg hle fun v hv =>
          pow_nonneg (FrivGt_mem_Icc M hv.2 hx.2).1 _
      rw [abs_of_nonneg hnn]
      calc ∫ v in w..x, (FrivGt M x v) ^ (M.n - 1)
          ≤ ∫ _ in w..x, (1 : ℝ) := intervalIntegral.integral_mono_on hle
            (hint_x w x hw.2 hx.2) intervalIntegrable_const
            (fun v hv => pow_le_one₀ (FrivGt_mem_Icc M hv.2 hx.2).1 (FrivGt_mem_Icc M hv.2 hx.2).2)
        _ = x - w := by simp
        _ = |x - w| := by rw [abs_of_nonneg (sub_nonneg.mpr hle)]
        _ < ε / 2 := hxd
  calc |(_ + _)| ≤ |_| + |_| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hterm1 hterm2
    _ = ε := add_halves ε

lemma hGt_strictMonoOn_w (ρ r₁ : ℝ) (hρr : ρ < r₁) (hr1 : r₁ ≤ 1) :
    StrictMonoOn (hGt M ρ r₁) (Icc (max r₁ M.a) 1) := by
  intro w₁ hw₁ w₂ hw₂ hlt
  have hρw₁ : ρ ≤ w₁ := hρr.le.trans (le_trans (le_max_left _ _) hw₁.1)
  have hρw₂ : ρ ≤ w₂ := hρw₁.trans hlt.le
  have hint1 : IntervalIntegrable (fun v => (FrivGt M w₁ v) ^ (M.n - 1)) volume ρ w₁ :=
    (((FrivGt_continuousOn_v M w₁).pow (M.n - 1)).mono
      (fun t (ht : t ∈ Icc ρ w₁) => ht.2.trans hw₁.2)).intervalIntegrable_of_Icc hρw₁
  have hint2a : IntervalIntegrable (fun v => (FrivGt M w₂ v) ^ (M.n - 1)) volume ρ w₁ :=
    (((FrivGt_continuousOn_v M w₂).pow (M.n - 1)).mono
      (fun t (ht : t ∈ Icc ρ w₁) => ht.2.trans hw₁.2)).intervalIntegrable_of_Icc hρw₁
  have hint2b : IntervalIntegrable (fun v => (FrivGt M w₂ v) ^ (M.n - 1)) volume w₁ w₂ :=
    (((FrivGt_continuousOn_v M w₂).pow (M.n - 1)).mono
      (fun t (ht : t ∈ Icc w₁ w₂) => ht.2.trans hw₂.2)).intervalIntegrable_of_Icc hlt.le
  have hsplit : hGt M ρ r₁ w₂ - hGt M ρ r₁ w₁ =
      (w₁ - r₁) * ((M.A w₂) ^ (M.n - 1) - (M.A w₁) ^ (M.n - 1)) +
      (∫ v in w₁..w₂, ((M.A w₂) ^ (M.n - 1) - (FrivGt M w₂ v) ^ (M.n - 1))) +
      (∫ v in ρ..w₁, ((FrivGt M w₁ v) ^ (M.n - 1) - (FrivGt M w₂ v) ^ (M.n - 1))) := by
    unfold hGt
    rw [← intervalIntegral.integral_add_adjacent_intervals hint2a hint2b,
      intervalIntegral.integral_sub intervalIntegrable_const hint2b,
      intervalIntegral.integral_sub hint1 hint2a]
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hT1 : 0 ≤ (w₁ - r₁) * ((M.A w₂) ^ (M.n - 1) - (M.A w₁) ^ (M.n - 1)) := by
    apply mul_nonneg (sub_nonneg.mpr (le_trans (le_max_left _ _) hw₁.1))
    have hA := M.A_strictMonoOn ⟨le_trans (le_max_right _ _) hw₁.1, hw₁.2⟩
      ⟨le_trans (le_max_right _ _) hw₂.1, hw₂.2⟩ hlt
    exact sub_nonneg.mpr (pow_le_pow_left₀ (M.A_pos hw₁.2).le hA.le _)
  have hT2 : 0 < ∫ v in w₁..w₂, ((M.A w₂) ^ (M.n - 1) - (FrivGt M w₂ v) ^ (M.n - 1)) := by
    apply intervalIntegral.integral_pos hlt
    · exact continuousOn_const.sub
        (((FrivGt_continuousOn_v M w₂).pow (M.n - 1)).mono (fun t ht => ht.2.trans hw₂.2))
    · intro v hv
      have hle : FrivGt M w₂ v ≤ M.A w₂ := by
        have hF := M.F_monotoneOn_Iic (hv.2.trans hw₂.2) hw₂.2 hv.2
        unfold FrivGt
        have : 0 ≤ (M.F w₂ - M.F v) / ((M.m : ℝ) - 1) := div_nonneg (by linarith) M.m_sub_one_pos_real.le
        linarith
      exact sub_nonneg.mpr (pow_le_pow_left₀ (FrivGt_mem_Icc M hv.2 hw₂.2).1 hle _)
    · refine ⟨(w₁ + w₂) / 2, ⟨by linarith, by linarith⟩, ?_⟩
      have hmid_a : M.a ≤ (w₁ + w₂) / 2 := by linarith [le_trans (le_max_right r₁ M.a) hw₁.1]
      have hmid_lt : (w₁ + w₂) / 2 < w₂ := by linarith
      have hFlt : FrivGt M w₂ ((w₁ + w₂) / 2) < M.A w₂ := by
        rw [← FrivGt_self M w₂]
        exact FrivGt_strictMono_v M ⟨hmid_a, hmid_lt.le.trans hw₂.2⟩
          ⟨le_trans (le_max_right _ _) hw₂.1, hw₂.2⟩ hmid_lt
      have hn1 : M.n - 1 ≠ 0 := by have := M.hn; omega
      exact sub_pos.mpr (pow_lt_pow_left₀ hFlt (FrivGt_mem_Icc M hmid_lt.le hw₂.2).1 hn1)
  have hT3 : 0 ≤ ∫ v in ρ..w₁, ((FrivGt M w₁ v) ^ (M.n - 1) - (FrivGt M w₂ v) ^ (M.n - 1)) := by
    apply intervalIntegral.integral_nonneg hρw₁
    intro v hv
    have hFlt := FrivGt_strictAnti_w M ⟨le_trans (le_max_right _ _) hw₁.1, hw₁.2⟩
      ⟨le_trans (le_max_right _ _) hw₂.1, hw₂.2⟩ (v := v) hlt
    exact sub_nonneg.mpr (pow_le_pow_left₀ (FrivGt_mem_Icc M (hv.2.trans hlt.le) hw₂.2).1 hFlt.le _)
  linarith

lemma hGt_neg_at_bot (ρ r₁ : ℝ) (hρr : ρ < r₁) (hr1 : r₁ ≤ 1) :
    hGt M ρ r₁ (max r₁ M.a) < 0 := by
  by_cases hra : r₁ ≤ M.a
  · rw [max_eq_right hra]
    unfold hGt
    have hcongr : ∫ v in ρ..M.a, (FrivGt M M.a v) ^ (M.n - 1) =
        (M.a - ρ) * (M.A M.a) ^ (M.n - 1) := by
      have : ∫ v in ρ..M.a, (FrivGt M M.a v) ^ (M.n - 1) =
          ∫ _ in ρ..M.a, (M.A M.a) ^ (M.n - 1) := by
        apply intervalIntegral.integral_congr
        intro v hv
        dsimp only
        rw [uIcc_of_le (hρr.le.trans hra)] at hv
        unfold FrivGt
        rw [M.hF_a, M.hF_below v hv.2, sub_self, zero_div, sub_zero]
      rw [this, intervalIntegral.integral_const, smul_eq_mul]
    rw [hcongr]
    have hpos : 0 < (M.A M.a) ^ (M.n - 1) := pow_pos (M.A_pos M.ha1.le) _
    nlinarith
  · push Not at hra
    rw [max_eq_left hra.le]
    unfold hGt
    rw [sub_self, zero_mul, zero_sub, neg_lt_zero]
    apply intervalIntegral.integral_pos hρr
    · exact ((FrivGt_continuousOn_v M r₁).pow (M.n - 1)).mono (fun t ht => ht.2.trans hr1)
    · intro v hv
      exact pow_nonneg (FrivGt_mem_Icc M hv.2 hr1).1 _
    · refine ⟨r₁, right_mem_Icc.mpr hρr.le, ?_⟩
      rw [FrivGt_self]
      exact pow_pos (M.A_pos hr1) _

/-- Cutoff `w(r₁) ∈ (max r₁ a, 1]` for `r₁ > ρ` (Proposition 1(ii), eq. (12)). -/
noncomputable def cutoffGt (ρ r₁ : ℝ) : ℝ :=
  if h : ∃ w ∈ Icc (max r₁ M.a) 1, hGt M ρ r₁ w = 0 then Classical.choose h else 1

lemma cutoffGt_spec (ρ r₁ : ℝ) (hρr : ρ < r₁) (hr1 : r₁ ≤ 1) :
    let w := cutoffGt M ρ r₁
    w ∈ Icc (max r₁ M.a) 1 ∧
    (r₁ < 1 → max r₁ M.a < w) ∧
    ((0 ≤ hGt M ρ r₁ 1 ∧ hGt M ρ r₁ w = 0) ∨ (hGt M ρ r₁ 1 < 0 ∧ w = 1)) := by
  have hbot := hGt_neg_at_bot M ρ r₁ hρr hr1
  have hmono := hGt_strictMonoOn_w M ρ r₁ hρr hr1
  have hmax1 : max r₁ M.a ≤ 1 := max_le hr1 M.ha1.le
  by_cases htop : 0 ≤ hGt M ρ r₁ 1
  · have hex : ∃ w ∈ Icc (max r₁ M.a) 1, hGt M ρ r₁ w = 0 := by
      have hcont : ContinuousOn (hGt M ρ r₁) (Icc (max r₁ M.a) 1) :=
        (hGt_continuousOn_w M ρ r₁ (hρr.le.trans hr1)).mono
          (Icc_subset_Icc_left (hρr.le.trans (le_max_left _ _)))
      exact intermediate_value_Icc hmax1 hcont ⟨hbot.le, htop⟩
    have hw_spec := Classical.choose_spec hex
    have hw_eq : cutoffGt M ρ r₁ = Classical.choose hex := dif_pos hex
    rw [hw_eq]
    have hgt : max r₁ M.a < Classical.choose hex := by
      refine lt_of_le_of_ne hw_spec.1.1 ?_
      intro heq; rw [← heq] at hw_spec; linarith
    exact ⟨hw_spec.1, fun _ => hgt, Or.inl ⟨htop, hw_spec.2⟩⟩
  · push Not at htop
    have hno : ¬ ∃ w ∈ Icc (max r₁ M.a) 1, hGt M ρ r₁ w = 0 := by
      rintro ⟨w, hw, hw0⟩
      rcases eq_or_lt_of_le hw.2 with rfl | hlt
      · linarith
      · have := hmono hw (right_mem_Icc.mpr hmax1) hlt
        linarith
    have hw_eq : cutoffGt M ρ r₁ = 1 := dif_neg hno
    rw [hw_eq]
    exact ⟨right_mem_Icc.mpr hmax1, fun hr1lt => max_lt hr1lt M.ha1, Or.inr ⟨htop, rfl⟩⟩

lemma cutoffGt_unique (ρ r₁ : ℝ) (hρr : ρ < r₁) (hr1 : r₁ ≤ 1) {w : ℝ}
    (hw : w ∈ Icc (max r₁ M.a) 1) (hw0 : hGt M ρ r₁ w = 0) :
    w = cutoffGt M ρ r₁ := by
  have hspec := cutoffGt_spec M ρ r₁ hρr hr1
  have hmono := hGt_strictMonoOn_w M ρ r₁ hρr hr1
  rcases hspec.2.2 with ⟨_, hc0⟩ | ⟨htop, _⟩
  · by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := hmono hw hspec.1 hlt; linarith
    · have := hmono hspec.1 hw hgt; linarith
  · rcases eq_or_lt_of_le hw.2 with rfl | hlt
    · linarith
    · have := hmono hw (right_mem_Icc.mpr (max_le hr1 M.ha1.le)) hlt; linarith

lemma cutoffGt_hGt_nonpos (ρ r₁ : ℝ) (hρr : ρ < r₁) (hr1 : r₁ ≤ 1) :
    hGt M ρ r₁ (cutoffGt M ρ r₁) ≤ 0 := by
  rcases (cutoffGt_spec M ρ r₁ hρr hr1).2.2 with ⟨_, h0⟩ | ⟨htop, hw1⟩
  · exact h0.le
  · rw [hw1]; exact htop.le

lemma hGt_sub_r (ρ r₁ r₂ w : ℝ) :
    hGt M ρ r₂ w - hGt M ρ r₁ w = (r₁ - r₂) * (M.A w) ^ (M.n - 1) := by
  unfold hGt; ring

/-- **Proposition 1(ii) (`r₁ > ρ`, monotonicity)**: `r₁ ↦ cutoffGt M ρ r₁` is nondecreasing
on `(ρ, 1]`. -/
theorem prop1_cutoffGt_monotone (ρ : ℝ) (hρ1 : ρ < 1) :
    MonotoneOn (cutoffGt M ρ) (Ioc ρ 1) := by
  intro r₁ hr₁ r₂ hr₂ hle
  have hs1 := cutoffGt_spec M ρ r₁ hr₁.1 hr₁.2
  have hs2 := cutoffGt_spec M ρ r₂ hr₂.1 hr₂.2
  rcases hs2.2.2 with ⟨_, h0_2⟩ | ⟨_, hw2_1⟩
  · by_contra hlt; push Not at hlt
    have hmem2_in_1 : cutoffGt M ρ r₂ ∈ Icc (max r₁ M.a) 1 :=
      ⟨le_trans (max_le_max_right M.a hle) hs2.1.1, hs2.1.2⟩
    have hgt := hGt_strictMonoOn_w M ρ r₁ hr₁.1 hr₁.2 hmem2_in_1 hs1.1 hlt
    have hsub := hGt_sub_r M ρ r₁ r₂ (cutoffGt M ρ r₂)
    have hge : 0 ≤ hGt M ρ r₁ (cutoffGt M ρ r₂) := by
      have hnn : 0 ≤ (r₂ - r₁) * (M.A (cutoffGt M ρ r₂)) ^ (M.n - 1) :=
        mul_nonneg (sub_nonneg.mpr hle) (pow_nonneg (M.A_pos hs2.1.2).le _)
      linarith
    have hle1 := cutoffGt_hGt_nonpos M ρ r₁ hr₁.1 hr₁.2
    linarith
  · rw [hw2_1]; exact hs1.1.2

/-- **Proposition 1(ii) (`r₁ > ρ`, continuity)**: `r₁ ↦ cutoffGt M ρ r₁` is continuous
on `(ρ, 1]`. -/
theorem prop1_cutoffGt_continuous (ρ : ℝ) (hρ1 : ρ < 1) :
    ContinuousOn (cutoffGt M ρ) (Ioc ρ 1) := by
  intro r₁ hr₁
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hs1 := cutoffGt_spec M ρ r₁ hr₁.1 hr₁.2
  set w := cutoffGt M ρ r₁
  by_cases hr1eq : r₁ = 1
  · subst hr1eq
    have hw1 : w = 1 := le_antisymm hs1.1.2 (le_trans (le_max_left 1 M.a) hs1.1.1)
    refine ⟨min ε (1 - ρ), lt_min hε (sub_pos.mpr hρ1), fun r hr hdist => ?_⟩
    rw [Real.dist_eq] at hdist ⊢
    have hsr := cutoffGt_spec M ρ r hr.1 hr.2
    have hle : r ≤ cutoffGt M ρ r := le_trans (le_max_left r M.a) hsr.1.1
    rw [hw1, abs_of_nonpos (sub_nonpos.mpr hsr.1.2)]
    have h1 : 1 - r < ε := by
      have := lt_of_lt_of_le hdist (min_le_left _ _)
      rwa [abs_of_nonpos (sub_nonpos.mpr hr.2), neg_sub] at this
    linarith
  · have hr1lt : r₁ < 1 := lt_of_le_of_ne hr₁.2 hr1eq
    have hbot_lt : max r₁ M.a < w := hs1.2.1 hr1lt
    set ε' := min (ε / 2) ((w - max r₁ M.a) / 2)
    have hε'pos : 0 < ε' := lt_min (half_pos hε) (half_pos (sub_pos.mpr hbot_lt))
    set wlo := w - ε'
    have hwlo_gt : max r₁ M.a < wlo := by
      have : ε' ≤ (w - max r₁ M.a) / 2 := min_le_right _ _
      linarith
    have hwlo_lt : wlo < w := by linarith
    have hwlo_mem : wlo ∈ Icc (max r₁ M.a) 1 := ⟨hwlo_gt.le, hwlo_lt.le.trans hs1.1.2⟩
    have hneg_lo : hGt M ρ r₁ wlo < 0 := by
      have hlt := hGt_strictMonoOn_w M ρ r₁ hr₁.1 hr₁.2 hwlo_mem hs1.1 hwlo_lt
      linarith [cutoffGt_hGt_nonpos M ρ r₁ hr₁.1 hr₁.2]
    have hδ_lo_pos : 0 < (-hGt M ρ r₁ wlo) / (M.A wlo) ^ (M.n - 1) :=
      div_pos (neg_pos.mpr hneg_lo) (pow_pos (M.A_pos hwlo_mem.2) _)
    -- Upper bound δ
    by_cases hw_lt1 : w < 1
    · set whi := min (w + ε') 1
      have hwhi_gt : w < whi := lt_min (by linarith) hw_lt1
      have hwhi_mem : whi ∈ Icc (max r₁ M.a) 1 :=
        ⟨hs1.1.1.trans hwhi_gt.le, min_le_right _ _⟩
      have h0_w : hGt M ρ r₁ w = 0 := by
        rcases hs1.2.2 with ⟨_, h0⟩ | ⟨_, hw1⟩
        · exact h0
        · exfalso; linarith
      have hpos_hi : 0 < hGt M ρ r₁ whi := by
        have := hGt_strictMonoOn_w M ρ r₁ hr₁.1 hr₁.2 hs1.1 hwhi_mem hwhi_gt
        linarith
      have hδ_hi_pos : 0 < hGt M ρ r₁ whi / (M.A whi) ^ (M.n - 1) :=
        div_pos hpos_hi (pow_pos (M.A_pos hwhi_mem.2) _)
      refine ⟨min (min (wlo - max r₁ M.a) ((-hGt M ρ r₁ wlo) / (M.A wlo) ^ (M.n - 1)))
          (hGt M ρ r₁ whi / (M.A whi) ^ (M.n - 1)),
        lt_min (lt_min (sub_pos.mpr hwlo_gt) hδ_lo_pos) hδ_hi_pos,
        fun r hr hdist => ?_⟩
      rw [Real.dist_eq] at hdist ⊢
      have hsr := cutoffGt_spec M ρ r hr.1 hr.2
      have hr_lo : max r M.a ≤ wlo := by
        have h1 : |r - r₁| < wlo - max r₁ M.a :=
          lt_of_lt_of_le hdist (le_trans (min_le_left _ _) (min_le_left _ _))
        have h2 : r - r₁ < wlo - max r₁ M.a := lt_of_le_of_lt (le_abs_self _) h1
        exact max_le (by linarith [le_max_left r₁ M.a]) (le_trans (le_max_right r₁ M.a) hwlo_gt.le)
      have hneg_r_lo : hGt M ρ r wlo < 0 := by
        have hsub := hGt_sub_r M ρ r₁ r wlo
        have h1 : |r - r₁| < (-hGt M ρ r₁ wlo) / (M.A wlo) ^ (M.n - 1) :=
          lt_of_lt_of_le hdist (le_trans (min_le_left _ _) (min_le_right _ _))
        have hApos : 0 < (M.A wlo) ^ (M.n - 1) := pow_pos (M.A_pos hwlo_mem.2) _
        have h2 : (r₁ - r) * (M.A wlo) ^ (M.n - 1) < -hGt M ρ r₁ wlo := by
          have : r₁ - r < (-hGt M ρ r₁ wlo) / (M.A wlo) ^ (M.n - 1) := by
            have := lt_of_le_of_lt (neg_le_abs (r - r₁)) h1; linarith
          rwa [lt_div_iff₀ hApos] at this
        linarith
      have hpos_r_hi : 0 < hGt M ρ r whi := by
        have hsub := hGt_sub_r M ρ r₁ r whi
        have h1 : |r - r₁| < hGt M ρ r₁ whi / (M.A whi) ^ (M.n - 1) :=
          lt_of_lt_of_le hdist (min_le_right _ _)
        have hApos : 0 < (M.A whi) ^ (M.n - 1) := pow_pos (M.A_pos hwhi_mem.2) _
        have h2 : (r - r₁) * (M.A whi) ^ (M.n - 1) < hGt M ρ r₁ whi := by
          have : r - r₁ < hGt M ρ r₁ whi / (M.A whi) ^ (M.n - 1) :=
            lt_of_le_of_lt (le_abs_self _) h1
          rwa [lt_div_iff₀ hApos] at this
        linarith
      have hw_gt_lo : wlo < cutoffGt M ρ r := by
        by_contra hle; push Not at hle
        rcases hsr.2.2 with ⟨_, h0⟩ | ⟨_, hw1⟩
        · rcases eq_or_lt_of_le hle with heq | hlt
          · rw [heq] at h0; linarith
          · have := hGt_strictMonoOn_w M ρ r hr.1 hr.2 hsr.1 ⟨hr_lo, hwlo_mem.2⟩ hlt; linarith
        · linarith [hwlo_lt, hs1.1.2]
      have hw_lt_hi : cutoffGt M ρ r < whi := by
        by_contra hge; push Not at hge
        have hle0 := cutoffGt_hGt_nonpos M ρ r hr.1 hr.2
        rcases eq_or_lt_of_le hge with heq | hlt
        · rw [← heq] at hle0; linarith
        · have := hGt_strictMonoOn_w M ρ r hr.1 hr.2
            ⟨hr_lo.trans (hwlo_lt.le.trans hwhi_gt.le), hwhi_mem.2⟩ hsr.1 hlt
          linarith
      rw [abs_lt]
      have hε'le : ε' ≤ ε / 2 := min_le_left _ _
      constructor <;> linarith [min_le_left (w + ε') 1]
    · -- w = 1
      have hw1 : w = 1 := le_antisymm hs1.1.2 (le_of_not_gt hw_lt1)
      refine ⟨min (wlo - max r₁ M.a) ((-hGt M ρ r₁ wlo) / (M.A wlo) ^ (M.n - 1)),
        lt_min (sub_pos.mpr hwlo_gt) hδ_lo_pos, fun r hr hdist => ?_⟩
      rw [Real.dist_eq] at hdist ⊢
      have hsr := cutoffGt_spec M ρ r hr.1 hr.2
      have hr_lo : max r M.a ≤ wlo := by
        have h1 : |r - r₁| < wlo - max r₁ M.a := lt_of_lt_of_le hdist (min_le_left _ _)
        have h2 : r - r₁ < wlo - max r₁ M.a := lt_of_le_of_lt (le_abs_self _) h1
        exact max_le (by linarith [le_max_left r₁ M.a]) (le_trans (le_max_right r₁ M.a) hwlo_gt.le)
      have hneg_r_lo : hGt M ρ r wlo < 0 := by
        have hsub := hGt_sub_r M ρ r₁ r wlo
        have h1 : |r - r₁| < (-hGt M ρ r₁ wlo) / (M.A wlo) ^ (M.n - 1) :=
          lt_of_lt_of_le hdist (min_le_right _ _)
        have hApos : 0 < (M.A wlo) ^ (M.n - 1) := pow_pos (M.A_pos hwlo_mem.2) _
        have h2 : (r₁ - r) * (M.A wlo) ^ (M.n - 1) < -hGt M ρ r₁ wlo := by
          have : r₁ - r < (-hGt M ρ r₁ wlo) / (M.A wlo) ^ (M.n - 1) := by
            have := lt_of_le_of_lt (neg_le_abs (r - r₁)) h1; linarith
          rwa [lt_div_iff₀ hApos] at this
        linarith
      have hw_gt_lo : wlo < cutoffGt M ρ r := by
        by_contra hle; push Not at hle
        rcases hsr.2.2 with ⟨_, h0⟩ | ⟨_, h1⟩
        · rcases eq_or_lt_of_le hle with heq | hlt
          · rw [heq] at h0; linarith
          · have := hGt_strictMonoOn_w M ρ r hr.1 hr.2 hsr.1 ⟨hr_lo, hwlo_mem.2⟩ hlt; linarith
        · linarith [hwlo_lt, hs1.1.2]
      rw [abs_lt]
      have hε'le : ε' ≤ ε / 2 := min_le_left _ _
      constructor <;> linarith [hsr.1.2]

/-- Explicit cutoff visit strategy for `r₁ > ρ`: types `< w` visit rivals symmetrically,
types `≥ w` split uniformly across all `m` sellers. -/
noncomputable def cutoffGtVisit (w : ℝ) : VisitStrategy M where
  θ j v := if v < w then (if j = 0 then 0 else 1 / ((M.m : ℝ) - 1)) else 1 / (M.m : ℝ)
  hmeas j := by
    have h1 : Measurable (fun _ : ℝ => if j = 0 then (0 : ℝ) else 1 / ((M.m : ℝ) - 1)) :=
      measurable_const
    exact h1.ite measurableSet_Iio measurable_const
  hnonneg j v := by
    split_ifs
    · exact le_rfl
    · exact div_nonneg zero_le_one M.m_sub_one_pos_real.le
    · exact div_nonneg zero_le_one M.m_pos_real.le
  hsum v _ := by
    by_cases hvw : v < w
    · simp only [if_pos hvw]
      have h0 : (0 : Fin M.m) ∈ (Finset.univ : Finset (Fin M.m)) := Finset.mem_univ _
      rw [← Finset.add_sum_erase _ _ h0]
      simp only [ite_true, zero_add]
      have hcongr : ∑ j ∈ Finset.univ.erase (0 : Fin M.m),
          (if j = 0 then (0 : ℝ) else 1 / ((M.m : ℝ) - 1)) =
          ∑ _j ∈ Finset.univ.erase (0 : Fin M.m), (1 / ((M.m : ℝ) - 1)) := by
        apply Finset.sum_congr rfl; intro j hj
        rw [ite_eq_right_iff]; intro heq; exact absurd heq (Finset.ne_of_mem_erase hj)
      rw [hcongr, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub (by have := M.hm; omega : 1 ≤ M.m)]
      simp only [Nat.cast_one]
      exact mul_one_div_cancel M.m_sub_one_pos_real.ne'
    · simp only [if_neg hvw, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact mul_one_div_cancel M.m_pos_real.ne'

lemma effDist_cutoffGtVisit_zero {w v : ℝ} (hw1 : w ≤ 1) (hv1 : v ≤ 1) :
    effDist M (cutoffGtVisit M w) 0 v = M.A (max v w) := by
  unfold effDist cutoffGtVisit Market.A
  simp only [ite_true]
  by_cases hvw : v ≤ w
  · rw [max_eq_right hvw]
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      ((cutoffGtVisit M w).mul_f_intervalIntegrable 0 hv1 hw1)
      ((cutoffGtVisit M w).mul_f_intervalIntegrable 0 hw1 le_rfl)
    have h1 : ∫ u in v..w, (if u < w then (0 : ℝ) else 1 / (M.m : ℝ)) * M.f u = 0 := by
      have hcongr : ∫ u in v..w, (if u < w then (0 : ℝ) else 1 / (M.m : ℝ)) * M.f u =
          ∫ _ in v..w, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_ae
        have hne : ∀ᵐ u ∂volume, u ≠ w := by simp [ae_iff, measure_singleton]
        filter_upwards [hne] with u hu hmem
        rw [uIoc_of_le hvw] at hmem
        simp [lt_of_le_of_ne hmem.2 hu]
      rw [hcongr]; simp
    have h2 : ∫ u in w..1, (if u < w then (0 : ℝ) else 1 / (M.m : ℝ)) * M.f u =
        (1 - M.F w) / (M.m : ℝ) := by
      have hcongr : ∫ u in w..1, (if u < w then (0 : ℝ) else 1 / (M.m : ℝ)) * M.f u =
          ∫ u in w..1, (1 / (M.m : ℝ)) * M.f u := by
        apply intervalIntegral.integral_congr
        intro u hu; dsimp only; rw [uIcc_of_le hw1] at hu
        rw [ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr hu.1))]
      rw [hcongr, intervalIntegral.integral_const_mul, M.integral_f hw1 le_rfl, M.hF_1]; ring
    have htot : ∫ u in v..1, (if u < w then (0 : ℝ) else 1 / (M.m : ℝ)) * M.f u =
        (1 - M.F w) / (M.m : ℝ) := by
      have hsp : (∫ u in v..w, (if u < w then (0 : ℝ) else 1 / (M.m : ℝ)) * M.f u) +
          (∫ u in w..1, (if u < w then (0 : ℝ) else 1 / (M.m : ℝ)) * M.f u) =
          ∫ u in v..1, (if u < w then (0 : ℝ) else 1 / (M.m : ℝ)) * M.f u := by
        simpa only [cutoffGtVisit, ite_true] using hsplit
      rw [← hsp, h1, h2, zero_add]
    rw [htot]
  · push Not at hvw
    rw [max_eq_left hvw.le]
    have hcongr : ∫ u in v..1, (if u < w then (0 : ℝ) else 1 / (M.m : ℝ)) * M.f u =
        ∫ u in v..1, (1 / (M.m : ℝ)) * M.f u := by
      apply intervalIntegral.integral_congr
      intro u hu; dsimp only; rw [uIcc_of_le hv1] at hu
      rw [ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr (hvw.le.trans hu.1)))]
    rw [hcongr, intervalIntegral.integral_const_mul, M.integral_f hv1 le_rfl, M.hF_1]; ring

lemma effDist_cutoffGtVisit_rival {w v : ℝ} (hw1 : w ≤ 1) (hv1 : v ≤ 1)
    {j : Fin M.m} (hj : j ≠ 0) :
    effDist M (cutoffGtVisit M w) j v = if v ≤ w then FrivGt M w v else M.A v := by
  unfold effDist cutoffGtVisit
  simp only [ite_eq_right_iff.mpr (fun h => absurd h hj)]
  by_cases hvw : v ≤ w
  · rw [if_pos hvw]
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      ((cutoffGtVisit M w).mul_f_intervalIntegrable j hv1 hw1)
      ((cutoffGtVisit M w).mul_f_intervalIntegrable j hw1 le_rfl)
    have h1 : ∫ u in v..w, (if u < w then 1 / ((M.m : ℝ) - 1) else 1 / (M.m : ℝ)) * M.f u =
        (M.F w - M.F v) / ((M.m : ℝ) - 1) := by
      have hcongr : ∫ u in v..w, (if u < w then 1 / ((M.m : ℝ) - 1) else 1 / (M.m : ℝ)) * M.f u =
          ∫ u in v..w, (1 / ((M.m : ℝ) - 1)) * M.f u := by
        apply intervalIntegral.integral_congr_ae
        have hne : ∀ᵐ u ∂volume, u ≠ w := by simp [ae_iff, measure_singleton]
        filter_upwards [hne] with u hu hmem
        rw [uIoc_of_le hvw] at hmem
        simp [lt_of_le_of_ne hmem.2 hu]
      rw [hcongr, intervalIntegral.integral_const_mul, M.integral_f hv1 hw1]; ring
    have h2 : ∫ u in w..1, (if u < w then 1 / ((M.m : ℝ) - 1) else 1 / (M.m : ℝ)) * M.f u =
        (1 - M.F w) / (M.m : ℝ) := by
      have hcongr : ∫ u in w..1, (if u < w then 1 / ((M.m : ℝ) - 1) else 1 / (M.m : ℝ)) * M.f u =
          ∫ u in w..1, (1 / (M.m : ℝ)) * M.f u := by
        apply intervalIntegral.integral_congr
        intro u hu; dsimp only; rw [uIcc_of_le hw1] at hu
        rw [ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr hu.1))]
      rw [hcongr, intervalIntegral.integral_const_mul, M.integral_f hw1 le_rfl, M.hF_1]; ring
    have htot : ∫ u in v..1, (if u < w then 1 / ((M.m : ℝ) - 1) else 1 / (M.m : ℝ)) * M.f u =
        (M.F w - M.F v) / ((M.m : ℝ) - 1) + (1 - M.F w) / (M.m : ℝ) := by
      have hsp : (∫ u in v..w, (if u < w then 1 / ((M.m : ℝ) - 1) else 1 / (M.m : ℝ)) * M.f u) +
          (∫ u in w..1, (if u < w then 1 / ((M.m : ℝ) - 1) else 1 / (M.m : ℝ)) * M.f u) =
          ∫ u in v..1, (if u < w then 1 / ((M.m : ℝ) - 1) else 1 / (M.m : ℝ)) * M.f u := by
        simpa only [cutoffGtVisit, ite_eq_right_iff.mpr (fun h => absurd h hj)] using hsplit
      rw [← hsp, h1, h2]
    rw [htot]; unfold FrivGt Market.A; ring
  · rw [if_neg hvw]
    push Not at hvw
    have hcongr : ∫ u in v..1, (if u < w then 1 / ((M.m : ℝ) - 1) else 1 / (M.m : ℝ)) * M.f u =
        ∫ u in v..1, (1 / (M.m : ℝ)) * M.f u := by
      apply intervalIntegral.integral_congr
      intro u hu; dsimp only; rw [uIcc_of_le hv1] at hu
      rw [ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr (hvw.le.trans hu.1)))]
    rw [hcongr, intervalIntegral.integral_const_mul, M.integral_f hv1 le_rfl, M.hF_1]
    unfold Market.A; ring

/-- **Proposition 1(ii) (`r₁ > ρ`, SR verification)**: With seller 1 at `SPA(r₁)` and rivals
at `SPA(ρ)` (`r₁ > ρ`), `cutoffGtVisit M (cutoffGt M ρ r₁)` is sequentially rational. -/
theorem prop1_cutoffGt_isSR (ρ r₁ : ℝ) (hρ0 : 0 ≤ ρ) (hρr : ρ < r₁) (hr1 : r₁ ≤ 1) :
    let w := cutoffGt M ρ r₁
    let mechs : Fin M.m → HierarchicalMech :=
      fun j => if j = 0 then SPA r₁ (hρ0.trans hρr.le) hr1 else SPA ρ hρ0 (hρr.le.trans hr1)
    IsSR M mechs (cutoffGtVisit M w) := by
  intro w mechs
  have hspec := cutoffGt_spec M ρ r₁ hρr hr1
  have hr10 : 0 ≤ r₁ := hρ0.trans hρr.le
  have hρ1 : ρ ≤ 1 := hρr.le.trans hr1
  have hr1w : r₁ ≤ w := le_trans (le_max_left _ _) hspec.1.1
  have hρw : ρ ≤ w := hρr.le.trans hr1w
  have hw1 : w ≤ 1 := hspec.1.2
  -- Compute surpluses s₀(v) and s_j(v) for rival j ≠ 0
  have hs_riv_eq : ∀ j k : Fin M.m, j ≠ 0 → k ≠ 0 → ∀ v ∈ Icc M.a 1,
      surplus M (mechs j) (effDist M (cutoffGtVisit M w) j) v =
      surplus M (mechs k) (effDist M (cutoffGtVisit M w) k) v := by
    intro j k hj hk v hv
    simp only [mechs, if_neg hj, if_neg hk]
    rw [surplus_SPA_eq M ρ hρ0 hρ1 _ (vs_effDist_monotoneOn _ _) (fun x hx => effDist_nonneg _ _ hx)
          (M.ha0.trans hv.1) hv.2,
        surplus_SPA_eq M ρ hρ0 hρ1 _ (vs_effDist_monotoneOn _ _) (fun x hx => effDist_nonneg _ _ hx)
          (M.ha0.trans hv.1) hv.2]
    apply intervalIntegral.integral_congr; intro t ht; dsimp only
    rw [uIcc_of_le (le_max_right v ρ)] at ht
    have ht1 : t ≤ 1 := ht.2.trans (max_le hv.2 hρ1)
    rw [effDist_cutoffGtVisit_rival M hw1 ht1 hj, effDist_cutoffGtVisit_rival M hw1 ht1 hk]
  have hs0_at_w : surplus M (mechs 0) (effDist M (cutoffGtVisit M w) 0) w =
      (w - r₁) * (M.A w) ^ (M.n - 1) := by
    simp only [mechs, ite_true]
    rw [surplus_SPA_eq M r₁ hr10 hr1 _ (vs_effDist_monotoneOn _ _) (fun x hx => effDist_nonneg _ _ hx)
          (hr10.trans hr1w) hw1, max_eq_left hr1w]
    have hcongr : ∫ t in r₁..w, (effDist M (cutoffGtVisit M w) 0 t) ^ (M.n - 1) =
        ∫ _ in r₁..w, (M.A w) ^ (M.n - 1) := by
      apply intervalIntegral.integral_congr; intro t ht; dsimp only
      rw [uIcc_of_le hr1w] at ht
      rw [effDist_cutoffGtVisit_zero M hw1 (ht.2.trans hw1), max_eq_right ht.2]
    rw [hcongr, intervalIntegral.integral_const, smul_eq_mul]
  have hsriv_at_w : ∀ j : Fin M.m, j ≠ 0 →
      surplus M (mechs j) (effDist M (cutoffGtVisit M w) j) w =
      ∫ t in ρ..w, (FrivGt M w t) ^ (M.n - 1) := by
    intro j hj
    simp only [mechs, if_neg hj]
    rw [surplus_SPA_eq M ρ hρ0 hρ1 _ (vs_effDist_monotoneOn _ _) (fun x hx => effDist_nonneg _ _ hx)
          (hρ0.trans hρw) hw1, max_eq_left hρw]
    apply intervalIntegral.integral_congr; intro t ht; dsimp only
    rw [uIcc_of_le hρw] at ht
    rw [effDist_cutoffGtVisit_rival M hw1 (ht.2.trans hw1) hj, if_pos ht.2]
  have hs_le_below : ∀ j : Fin M.m, j ≠ 0 → ∀ v ∈ Icc M.a 1, v ≤ w →
      surplus M (mechs 0) (effDist M (cutoffGtVisit M w) 0) v ≤
      surplus M (mechs j) (effDist M (cutoffGtVisit M w) j) v := by
    intro j hj v hv hvw
    by_cases hvr : v ≤ r₁
    · simp only [mechs, ite_true, if_neg hj]
      rw [surplus_zero_of_le_r M (SPA r₁ hr10 hr1) _ (M.ha0.trans hv.1) hvr]
      rw [surplus_SPA_eq M ρ hρ0 hρ1 _ (vs_effDist_monotoneOn _ _) (fun x hx => effDist_nonneg _ _ hx)
            (M.ha0.trans hv.1) hv.2]
      exact intervalIntegral.integral_nonneg (le_max_right v ρ) fun t ht =>
        pow_nonneg (effDist_nonneg _ _ (ht.2.trans (max_le hv.2 hρ1))) _
    · push Not at hvr
      have hdiff_0 : surplus M (mechs 0) (effDist M (cutoffGtVisit M w) 0) w -
          surplus M (mechs 0) (effDist M (cutoffGtVisit M w) 0) v =
          (w - v) * (M.A w) ^ (M.n - 1) := by
        simp only [mechs, ite_true]
        rw [surplus_sub M (SPA r₁ hr10 hr1) _ (vs_effDist_monotoneOn _ _)
              (fun x hx => effDist_nonneg _ _ hx) hv.2 hw1]
        have hcongr : ∫ t in v..w, alloc M (SPA r₁ hr10 hr1) (effDist M (cutoffGtVisit M w) 0) t =
            ∫ _ in v..w, (M.A w) ^ (M.n - 1) := by
          apply intervalIntegral.integral_congr; intro t ht; dsimp only
          rw [uIcc_of_le hvw] at ht
          rw [alloc_SPA, ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr (hvr.le.trans ht.1))),
            effDist_cutoffGtVisit_zero M hw1 (ht.2.trans hw1), max_eq_right ht.2]
        rw [hcongr, intervalIntegral.integral_const, smul_eq_mul]
      have hdiff_j : surplus M (mechs j) (effDist M (cutoffGtVisit M w) j) w -
          surplus M (mechs j) (effDist M (cutoffGtVisit M w) j) v ≤
          (w - v) * (M.A w) ^ (M.n - 1) := by
        simp only [mechs, if_neg hj]
        rw [surplus_sub M (SPA ρ hρ0 hρ1) _ (vs_effDist_monotoneOn _ _)
              (fun x hx => effDist_nonneg _ _ hx) hv.2 hw1]
        have hle_int : ∫ t in v..w, alloc M (SPA ρ hρ0 hρ1) (effDist M (cutoffGtVisit M w) j) t ≤
            ∫ _ in v..w, (M.A w) ^ (M.n - 1) := by
          apply intervalIntegral.integral_mono_on hvw
            (alloc_intervalIntegrable M _ _ (vs_effDist_monotoneOn _ _)
              (fun x hx => effDist_nonneg _ _ hx) hv.2 hw1)
            intervalIntegrable_const
          intro t ht
          rw [alloc_SPA, ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr (hρr.le.trans (hvr.le.trans ht.1)))),
            effDist_cutoffGtVisit_rival M hw1 (ht.2.trans hw1) hj, if_pos ht.2]
          have hFle : FrivGt M w t ≤ M.A w := by
            unfold FrivGt
            have hF := M.F_monotoneOn_Iic (ht.2.trans hw1) hw1 ht.2
            have : 0 ≤ (M.F w - M.F t) / ((M.m : ℝ) - 1) := div_nonneg (by linarith) M.m_sub_one_pos_real.le
            linarith
          exact pow_le_pow_left₀ (FrivGt_mem_Icc M ht.2 hw1).1 hFle _
        simpa [intervalIntegral.integral_const, smul_eq_mul] using hle_int
      have hw_le : surplus M (mechs 0) (effDist M (cutoffGtVisit M w) 0) w ≤
          surplus M (mechs j) (effDist M (cutoffGtVisit M w) j) w := by
        rw [hs0_at_w, hsriv_at_w j hj]
        have := cutoffGt_hGt_nonpos M ρ r₁ hρr hr1
        unfold hGt at this; linarith
      linarith
  have hs_eq_above : ∀ j : Fin M.m, j ≠ 0 → ∀ v ∈ Icc M.a 1, w ≤ v →
      hGt M ρ r₁ w = 0 →
      surplus M (mechs 0) (effDist M (cutoffGtVisit M w) 0) v =
      surplus M (mechs j) (effDist M (cutoffGtVisit M w) j) v := by
    intro j hj v hv hwv h0
    have hat_w : surplus M (mechs 0) (effDist M (cutoffGtVisit M w) 0) w =
        surplus M (mechs j) (effDist M (cutoffGtVisit M w) j) w := by
      rw [hs0_at_w, hsriv_at_w j hj]; unfold hGt at h0; linarith
    have hd0 : surplus M (mechs 0) (effDist M (cutoffGtVisit M w) 0) v -
        surplus M (mechs 0) (effDist M (cutoffGtVisit M w) 0) w =
        ∫ t in w..v, (M.A t) ^ (M.n - 1) := by
      simp only [mechs, ite_true]
      rw [surplus_sub M (SPA r₁ hr10 hr1) _ (vs_effDist_monotoneOn _ _)
            (fun x hx => effDist_nonneg _ _ hx) hw1 hv.2]
      apply intervalIntegral.integral_congr; intro t ht; dsimp only
      rw [uIcc_of_le hwv] at ht
      rw [alloc_SPA, ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr (hr1w.trans ht.1))),
        effDist_cutoffGtVisit_zero M hw1 (ht.2.trans hv.2), max_eq_left ht.1]
    have hdj : surplus M (mechs j) (effDist M (cutoffGtVisit M w) j) v -
        surplus M (mechs j) (effDist M (cutoffGtVisit M w) j) w =
        ∫ t in w..v, (M.A t) ^ (M.n - 1) := by
      simp only [mechs, if_neg hj]
      rw [surplus_sub M (SPA ρ hρ0 hρ1) _ (vs_effDist_monotoneOn _ _)
            (fun x hx => effDist_nonneg _ _ hx) hw1 hv.2]
      apply intervalIntegral.integral_congr_ae
      have hne : ∀ᵐ t ∂volume, t ≠ w := by simp [ae_iff, measure_singleton]
      filter_upwards [hne] with t ht hmem
      rw [uIoc_of_le hwv] at hmem
      have hwt : w < t := hmem.1
      rw [alloc_SPA, ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr (hρw.trans hwt.le))),
        effDist_cutoffGtVisit_rival M hw1 (hmem.2.trans hv.2) hj, if_neg (not_le.mpr hwt)]
    linarith
  -- Conclude IsSR
  rw [IsSR, MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  have hne_w : ∀ᵐ v ∂volume, v ≠ w := by simp [ae_iff, measure_singleton]
  filter_upwards [hne_w] with v hvw_ne hv j k hjpos
  by_cases hvw : v < w
  · -- Below w: θ_0 = 0, so j ≠ 0
    have hj0 : j ≠ 0 := by
      intro heq; subst heq; simp [cutoffGtVisit, hvw] at hjpos
    by_cases hk0 : k = 0
    · subst hk0; exact hs_le_below j hj0 v hv hvw.le
    · exact le_of_eq (hs_riv_eq k j hk0 hj0 v hv)
  · push Not at hvw
    have hwv_lt : w < v := lt_of_le_of_ne hvw (Ne.symm hvw_ne)
    have h0 : hGt M ρ r₁ w = 0 := by
      rcases hspec.2.2 with ⟨_, h0⟩ | ⟨_, hw1'⟩
      · exact h0
      · exfalso; linarith [hv.2]
    by_cases hj0 : j = 0
    · subst hj0
      by_cases hk0 : k = 0
      · subst hk0; exact le_rfl
      · exact le_of_eq (hs_eq_above k hk0 v hv hvw h0).symm
    · by_cases hk0 : k = 0
      · subst hk0; exact le_of_eq (hs_eq_above j hj0 v hv hvw h0)
      · exact le_of_eq (hs_riv_eq k j hk0 hj0 v hv)

/-! #### Symmetric cutoff `w` for `r₁ < ρ` (eq. (13)) -/

/-- Seller 1 effective distribution below cutoff `w` when `r₁ < ρ` (eq. (13)). -/
noncomputable def F1Lt (w v : ℝ) : ℝ :=
  M.A w - (M.F w - M.F v)

/-- Indifference function `h̃(w)` for `r₁ < ρ` (eq. (13)). -/
noncomputable def hLt (ρ r₁ w : ℝ) : ℝ :=
  (w - ρ) * (M.A w) ^ (M.n - 1) - ∫ v in r₁..w, (F1Lt M w v) ^ (M.n - 1)

lemma F1Lt_eq (w v : ℝ) :
    F1Lt M w v = (1 - 1 / (M.m : ℝ)) * (1 - M.F w) + M.F v := by
  unfold F1Lt Market.A; ring

lemma F1Lt_self (w : ℝ) : F1Lt M w w = M.A w := by
  simp [F1Lt]

lemma F1Lt_mem_Icc {w v : ℝ} (hvw : v ≤ w) (hw : w ≤ 1) :
    F1Lt M w v ∈ Icc (0 : ℝ) 1 := by
  have hm : (2 : ℝ) ≤ M.m := by exact_mod_cast M.hm
  have hmpos : (0 : ℝ) < M.m := M.m_pos_real
  have hFw := M.F_mem_Icc_Iic hw
  have hFv := M.F_mem_Icc_Iic (hvw.trans hw)
  have hFmono : M.F v ≤ M.F w := M.F_monotoneOn_Iic (hvw.trans hw) hw hvw
  constructor
  · rw [F1Lt_eq]
    have h1 : 0 ≤ 1 - 1 / (M.m : ℝ) := by
      have : 1 / (M.m : ℝ) ≤ 1 := by rw [div_le_one hmpos]; linarith
      linarith
    exact add_nonneg (mul_nonneg h1 (by linarith [hFw.2])) hFv.1
  · unfold F1Lt
    linarith [(M.A_mem_Icc hw).2]

lemma F1Lt_strictMono_v {w v₁ v₂ : ℝ} (hv₁ : v₁ ∈ Icc M.a 1) (hv₂ : v₂ ∈ Icc M.a 1)
    (hlt : v₁ < v₂) : F1Lt M w v₁ < F1Lt M w v₂ := by
  rw [F1Lt_eq, F1Lt_eq]; linarith [M.F_strictMonoOn hv₁ hv₂ hlt]

lemma F1Lt_strictAnti_w {w₁ w₂ v : ℝ} (hw₁ : w₁ ∈ Icc M.a 1) (hw₂ : w₂ ∈ Icc M.a 1)
    (hlt : w₁ < w₂) : F1Lt M w₂ v < F1Lt M w₁ v := by
  rw [F1Lt_eq, F1Lt_eq]
  have hpos : 0 < 1 - 1 / (M.m : ℝ) := by
    have hm : (2 : ℝ) ≤ M.m := by exact_mod_cast M.hm
    have : 1 / (M.m : ℝ) < 1 := by rw [div_lt_one M.m_pos_real]; linarith
    linarith
  have hF := M.F_strictMonoOn hw₁ hw₂ hlt
  nlinarith

lemma F1Lt_continuousOn_v (w : ℝ) : ContinuousOn (F1Lt M w) (Iic 1) := by
  unfold F1Lt
  exact continuousOn_const.sub (continuousOn_const.sub M.F_continuousOn_Iic)

lemma hLt_continuousOn_w (ρ r₁ : ℝ) (hr1 : r₁ ≤ 1) :
    ContinuousOn (hLt M ρ r₁) (Icc r₁ 1) := by
  have hfirst : ContinuousOn (fun w => (w - ρ) * (M.A w) ^ (M.n - 1)) (Icc r₁ 1) :=
    (continuousOn_id.sub continuousOn_const).mul
      ((M.A_continuousOn_Iic.mono Icc_subset_Iic_self).pow (M.n - 1))
  refine hfirst.sub ?_
  intro w hw
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hFcont := Metric.continuousWithinAt_iff.mp (M.F_continuousOn_Iic w hw.2)
  have hden_pos : 0 < ((M.n : ℝ) - 1) * (1 - r₁) + 1 := by
    have : 0 ≤ ((M.n : ℝ) - 1) * (1 - r₁) := mul_nonneg M.n_sub_one_pos_real.le (sub_nonneg.mpr hr1)
    linarith
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := hFcont (ε / (2 * (((M.n : ℝ) - 1) * (1 - r₁) + 1)))
    (div_pos hε (by linarith))
  refine ⟨min δ₁ (ε / 2), lt_min hδ₁pos (half_pos hε), fun x hx hdist => ?_⟩
  rw [Real.dist_eq] at hdist ⊢
  have hFdist : |M.F x - M.F w| < ε / (2 * (((M.n : ℝ) - 1) * (1 - r₁) + 1)) := by
    have := hδ₁ hx.2 (lt_of_lt_of_le hdist (min_le_left _ _))
    rwa [Real.dist_eq] at this
  have hxd : |x - w| < ε / 2 := lt_of_lt_of_le hdist (min_le_right _ _)
  have hint_x : ∀ a b, a ≤ 1 → b ≤ 1 →
      IntervalIntegrable (fun v => (F1Lt M x v) ^ (M.n - 1)) volume a b := by
    intro a b ha hb
    exact ((F1Lt_continuousOn_v M x).pow (M.n - 1) |>.mono (by
      intro t ht; rcases le_total a b with hle | hle
      · rw [uIcc_of_le hle] at ht; exact ht.2.trans hb
      · rw [uIcc_comm, uIcc_of_le hle] at ht; exact ht.2.trans ha)).intervalIntegrable
  have hint_w : ∀ a b, a ≤ 1 → b ≤ 1 →
      IntervalIntegrable (fun v => (F1Lt M w v) ^ (M.n - 1)) volume a b := by
    intro a b ha hb
    exact ((F1Lt_continuousOn_v M w).pow (M.n - 1) |>.mono (by
      intro t ht; rcases le_total a b with hle | hle
      · rw [uIcc_of_le hle] at ht; exact ht.2.trans hb
      · rw [uIcc_comm, uIcc_of_le hle] at ht; exact ht.2.trans ha)).intervalIntegrable
  let m0 := min x w
  have hm0_r : r₁ ≤ m0 := le_min hx.1 hw.1
  have hm0_1 : m0 ≤ 1 := le_trans (min_le_left _ _) hx.2
  have hdiff_split : (∫ v in r₁..x, (F1Lt M x v) ^ (M.n - 1)) -
      (∫ v in r₁..w, (F1Lt M w v) ^ (M.n - 1)) =
      (∫ v in r₁..m0, ((F1Lt M x v) ^ (M.n - 1) - (F1Lt M w v) ^ (M.n - 1))) +
      ((∫ v in m0..x, (F1Lt M x v) ^ (M.n - 1)) -
       (∫ v in m0..w, (F1Lt M w v) ^ (M.n - 1))) := by
    have hx_sp := intervalIntegral.integral_add_adjacent_intervals
      (hint_x r₁ m0 hr1 hm0_1) (hint_x m0 x hm0_1 hx.2)
    have hw_sp := intervalIntegral.integral_add_adjacent_intervals
      (hint_w r₁ m0 hr1 hm0_1) (hint_w m0 w hm0_1 hw.2)
    rw [intervalIntegral.integral_sub (hint_x r₁ m0 hr1 hm0_1) (hint_w r₁ m0 hr1 hm0_1)]
    linarith
  rw [hdiff_split]
  have hterm1 : |∫ v in r₁..m0, ((F1Lt M x v) ^ (M.n - 1) - (F1Lt M w v) ^ (M.n - 1))| < ε / 2 := by
    have hK : ((M.n : ℝ) - 1) * |M.F x - M.F w| * (m0 - r₁) < ε / 2 := by
      have hm0_le : m0 - r₁ ≤ 1 - r₁ := by linarith
      calc ((M.n : ℝ) - 1) * |M.F x - M.F w| * (m0 - r₁)
          ≤ ((M.n : ℝ) - 1) * (1 - r₁) * |M.F x - M.F w| := by
            have := mul_le_mul_of_nonneg_left hm0_le (mul_nonneg M.n_sub_one_pos_real.le (abs_nonneg (M.F x - M.F w)))
            linarith
        _ ≤ (((M.n : ℝ) - 1) * (1 - r₁) + 1) * |M.F x - M.F w| := by
            nlinarith [abs_nonneg (M.F x - M.F w)]
        _ < (((M.n : ℝ) - 1) * (1 - r₁) + 1) * (ε / (2 * (((M.n : ℝ) - 1) * (1 - r₁) + 1))) :=
            mul_lt_mul_of_pos_left hFdist hden_pos
        _ = ε / 2 := by
            rw [mul_comm (2 : ℝ), mul_div_assoc', mul_div_mul_left _ _ hden_pos.ne']
    calc |∫ v in r₁..m0, ((F1Lt M x v) ^ (M.n - 1) - (F1Lt M w v) ^ (M.n - 1))|
        ≤ ∫ v in r₁..m0, |(F1Lt M x v) ^ (M.n - 1) - (F1Lt M w v) ^ (M.n - 1)| :=
          intervalIntegral.abs_integral_le_integral_abs hm0_r
      _ ≤ ∫ _ in r₁..m0, (((M.n : ℝ) - 1) * |M.F x - M.F w|) := by
          apply intervalIntegral.integral_mono_on hm0_r
            ((((F1Lt_continuousOn_v M x).pow (M.n - 1)).sub
              ((F1Lt_continuousOn_v M w).pow (M.n - 1))).abs.mono
              (fun t (ht : t ∈ Icc r₁ m0) => ht.2.trans hm0_1) |>.intervalIntegrable_of_Icc hm0_r)
            intervalIntegrable_const
          intro v hv
          have hvx := F1Lt_mem_Icc M (hv.2.trans (min_le_left _ _)) hx.2
          have hvw := F1Lt_mem_Icc M (hv.2.trans (min_le_right _ _)) hw.2
          have hlip := pow_sub_one_lipschitz M.hn hvx.1 hvx.2 hvw.1 hvw.2
          have hFd : |F1Lt M x v - F1Lt M w v| ≤ |M.F x - M.F w| := by
            rw [F1Lt_eq, F1Lt_eq]
            have h1 : ((1 - 1 / (M.m : ℝ)) * (1 - M.F x) + M.F v) -
                ((1 - 1 / (M.m : ℝ)) * (1 - M.F w) + M.F v) =
                -(1 - 1 / (M.m : ℝ)) * (M.F x - M.F w) := by ring
            rw [h1, abs_mul, abs_neg]
            have hcoeff : 0 ≤ 1 - 1 / (M.m : ℝ) ∧ 1 - 1 / (M.m : ℝ) ≤ 1 := by
              have hm : (2 : ℝ) ≤ M.m := by exact_mod_cast M.hm
              have : 0 ≤ 1 / (M.m : ℝ) := div_nonneg zero_le_one M.m_pos_real.le
              have : 1 / (M.m : ℝ) ≤ 1 := by rw [div_le_one M.m_pos_real]; linarith
              constructor <;> linarith
            rw [abs_of_nonneg hcoeff.1]
            exact mul_le_of_le_one_left (abs_nonneg _) hcoeff.2
          change |(F1Lt M x v) ^ (M.n - 1) - (F1Lt M w v) ^ (M.n - 1)| ≤ _
          exact le_trans hlip (mul_le_mul_of_nonneg_left hFd M.n_sub_one_pos_real.le)
      _ = ((M.n : ℝ) - 1) * |M.F x - M.F w| * (m0 - r₁) := by
          simp [mul_comm, mul_left_comm]
      _ < ε / 2 := hK
  have hterm2 : |(∫ v in m0..x, (F1Lt M x v) ^ (M.n - 1)) -
      (∫ v in m0..w, (F1Lt M w v) ^ (M.n - 1))| < ε / 2 := by
    rcases le_total x w with hle | hle
    · have hm0_eq : m0 = x := min_eq_left hle
      rw [hm0_eq, intervalIntegral.integral_same, zero_sub, abs_neg]
      have hnn : 0 ≤ ∫ v in x..w, (F1Lt M w v) ^ (M.n - 1) :=
        intervalIntegral.integral_nonneg hle fun v hv =>
          pow_nonneg (F1Lt_mem_Icc M hv.2 hw.2).1 _
      rw [abs_of_nonneg hnn]
      calc ∫ v in x..w, (F1Lt M w v) ^ (M.n - 1)
          ≤ ∫ _ in x..w, (1 : ℝ) := intervalIntegral.integral_mono_on hle
            (hint_w x w hx.2 hw.2) intervalIntegrable_const
            (fun v hv => pow_le_one₀ (F1Lt_mem_Icc M hv.2 hw.2).1 (F1Lt_mem_Icc M hv.2 hw.2).2)
        _ = w - x := by simp
        _ = |x - w| := by rw [abs_of_nonpos (sub_nonpos.mpr hle)]; ring
        _ < ε / 2 := hxd
    · have hm0_eq : m0 = w := min_eq_right hle
      rw [hm0_eq, intervalIntegral.integral_same, sub_zero]
      have hnn : 0 ≤ ∫ v in w..x, (F1Lt M x v) ^ (M.n - 1) :=
        intervalIntegral.integral_nonneg hle fun v hv =>
          pow_nonneg (F1Lt_mem_Icc M hv.2 hx.2).1 _
      rw [abs_of_nonneg hnn]
      calc ∫ v in w..x, (F1Lt M x v) ^ (M.n - 1)
          ≤ ∫ _ in w..x, (1 : ℝ) := intervalIntegral.integral_mono_on hle
            (hint_x w x hw.2 hx.2) intervalIntegrable_const
            (fun v hv => pow_le_one₀ (F1Lt_mem_Icc M hv.2 hx.2).1 (F1Lt_mem_Icc M hv.2 hx.2).2)
        _ = x - w := by simp
        _ = |x - w| := by rw [abs_of_nonneg (sub_nonneg.mpr hle)]
        _ < ε / 2 := hxd
  calc |(_ + _)| ≤ |_| + |_| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hterm1 hterm2
    _ = ε := add_halves ε

lemma hLt_strictMonoOn_w (ρ r₁ : ℝ) (hrρ : r₁ < ρ) (hρ1 : ρ ≤ 1) :
    StrictMonoOn (hLt M ρ r₁) (Icc (max ρ M.a) 1) := by
  intro w₁ hw₁ w₂ hw₂ hlt
  have hrw₁ : r₁ ≤ w₁ := hrρ.le.trans (le_trans (le_max_left _ _) hw₁.1)
  have hint1 : IntervalIntegrable (fun v => (F1Lt M w₁ v) ^ (M.n - 1)) volume r₁ w₁ :=
    (((F1Lt_continuousOn_v M w₁).pow (M.n - 1)).mono
      (fun t (ht : t ∈ Icc r₁ w₁) => ht.2.trans hw₁.2)).intervalIntegrable_of_Icc hrw₁
  have hint2a : IntervalIntegrable (fun v => (F1Lt M w₂ v) ^ (M.n - 1)) volume r₁ w₁ :=
    (((F1Lt_continuousOn_v M w₂).pow (M.n - 1)).mono
      (fun t (ht : t ∈ Icc r₁ w₁) => ht.2.trans hw₁.2)).intervalIntegrable_of_Icc hrw₁
  have hint2b : IntervalIntegrable (fun v => (F1Lt M w₂ v) ^ (M.n - 1)) volume w₁ w₂ :=
    (((F1Lt_continuousOn_v M w₂).pow (M.n - 1)).mono
      (fun t (ht : t ∈ Icc w₁ w₂) => ht.2.trans hw₂.2)).intervalIntegrable_of_Icc hlt.le
  have hsplit : hLt M ρ r₁ w₂ - hLt M ρ r₁ w₁ =
      (w₁ - ρ) * ((M.A w₂) ^ (M.n - 1) - (M.A w₁) ^ (M.n - 1)) +
      (∫ v in w₁..w₂, ((M.A w₂) ^ (M.n - 1) - (F1Lt M w₂ v) ^ (M.n - 1))) +
      (∫ v in r₁..w₁, ((F1Lt M w₁ v) ^ (M.n - 1) - (F1Lt M w₂ v) ^ (M.n - 1))) := by
    unfold hLt
    rw [← intervalIntegral.integral_add_adjacent_intervals hint2a hint2b,
      intervalIntegral.integral_sub intervalIntegrable_const hint2b,
      intervalIntegral.integral_sub hint1 hint2a]
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hT1 : 0 ≤ (w₁ - ρ) * ((M.A w₂) ^ (M.n - 1) - (M.A w₁) ^ (M.n - 1)) := by
    apply mul_nonneg (sub_nonneg.mpr (le_trans (le_max_left _ _) hw₁.1))
    have hA := M.A_strictMonoOn ⟨le_trans (le_max_right _ _) hw₁.1, hw₁.2⟩
      ⟨le_trans (le_max_right _ _) hw₂.1, hw₂.2⟩ hlt
    exact sub_nonneg.mpr (pow_le_pow_left₀ (M.A_pos hw₁.2).le hA.le _)
  have hT2 : 0 < ∫ v in w₁..w₂, ((M.A w₂) ^ (M.n - 1) - (F1Lt M w₂ v) ^ (M.n - 1)) := by
    apply intervalIntegral.integral_pos hlt
    · exact continuousOn_const.sub
        (((F1Lt_continuousOn_v M w₂).pow (M.n - 1)).mono (fun t ht => ht.2.trans hw₂.2))
    · intro v hv
      have hle : F1Lt M w₂ v ≤ M.A w₂ := by
        unfold F1Lt; linarith [M.F_monotoneOn_Iic (hv.2.trans hw₂.2) hw₂.2 hv.2]
      exact sub_nonneg.mpr (pow_le_pow_left₀ (F1Lt_mem_Icc M hv.2 hw₂.2).1 hle _)
    · refine ⟨(w₁ + w₂) / 2, ⟨by linarith, by linarith⟩, ?_⟩
      have hmid_a : M.a ≤ (w₁ + w₂) / 2 := by linarith [le_trans (le_max_right ρ M.a) hw₁.1]
      have hmid_lt : (w₁ + w₂) / 2 < w₂ := by linarith
      have hFlt : F1Lt M w₂ ((w₁ + w₂) / 2) < M.A w₂ := by
        rw [← F1Lt_self M w₂]
        exact F1Lt_strictMono_v M ⟨hmid_a, hmid_lt.le.trans hw₂.2⟩
          ⟨le_trans (le_max_right _ _) hw₂.1, hw₂.2⟩ hmid_lt
      have hn1 : M.n - 1 ≠ 0 := by have := M.hn; omega
      exact sub_pos.mpr (pow_lt_pow_left₀ hFlt (F1Lt_mem_Icc M hmid_lt.le hw₂.2).1 hn1)
  have hT3 : 0 ≤ ∫ v in r₁..w₁, ((F1Lt M w₁ v) ^ (M.n - 1) - (F1Lt M w₂ v) ^ (M.n - 1)) := by
    apply intervalIntegral.integral_nonneg hrw₁
    intro v hv
    have hFlt := F1Lt_strictAnti_w M ⟨le_trans (le_max_right _ _) hw₁.1, hw₁.2⟩
      ⟨le_trans (le_max_right _ _) hw₂.1, hw₂.2⟩ (v := v) hlt
    exact sub_nonneg.mpr (pow_le_pow_left₀ (F1Lt_mem_Icc M (hv.2.trans hlt.le) hw₂.2).1 hFlt.le _)
  linarith

lemma hLt_neg_at_bot (ρ r₁ : ℝ) (hrρ : r₁ < ρ) (hρ1 : ρ ≤ 1) :
    hLt M ρ r₁ (max ρ M.a) < 0 := by
  by_cases hρa : ρ ≤ M.a
  · rw [max_eq_right hρa]
    unfold hLt
    have hcongr : ∫ v in r₁..M.a, (F1Lt M M.a v) ^ (M.n - 1) =
        (M.a - r₁) * (M.A M.a) ^ (M.n - 1) := by
      have : ∫ v in r₁..M.a, (F1Lt M M.a v) ^ (M.n - 1) =
          ∫ _ in r₁..M.a, (M.A M.a) ^ (M.n - 1) := by
        apply intervalIntegral.integral_congr; intro v hv; dsimp only
        rw [uIcc_of_le (hrρ.le.trans hρa)] at hv
        unfold F1Lt; rw [M.hF_a, M.hF_below v hv.2, sub_self, sub_zero]
      rw [this, intervalIntegral.integral_const, smul_eq_mul]
    rw [hcongr]
    have hpos : 0 < (M.A M.a) ^ (M.n - 1) := pow_pos (M.A_pos M.ha1.le) _
    nlinarith
  · push Not at hρa
    rw [max_eq_left hρa.le]
    unfold hLt
    rw [sub_self, zero_mul, zero_sub, neg_lt_zero]
    apply intervalIntegral.integral_pos hrρ
    · exact ((F1Lt_continuousOn_v M ρ).pow (M.n - 1)).mono (fun t ht => ht.2.trans hρ1)
    · intro v hv; exact pow_nonneg (F1Lt_mem_Icc M hv.2 hρ1).1 _
    · refine ⟨ρ, right_mem_Icc.mpr hrρ.le, ?_⟩
      rw [F1Lt_self]; exact pow_pos (M.A_pos hρ1) _

/-- Cutoff `w(r₁) ∈ [max ρ a, 1]` for `r₁ < ρ` (Proposition 1(ii), eq. (13)). -/
noncomputable def cutoffLt (ρ r₁ : ℝ) : ℝ :=
  if h : ∃ w ∈ Icc (max ρ M.a) 1, hLt M ρ r₁ w = 0 then Classical.choose h else 1

lemma cutoffLt_spec (ρ r₁ : ℝ) (hrρ : r₁ < ρ) (hρ1 : ρ ≤ 1) :
    let w := cutoffLt M ρ r₁
    w ∈ Icc (max ρ M.a) 1 ∧
    (ρ < 1 → max ρ M.a < w) ∧
    ((0 ≤ hLt M ρ r₁ 1 ∧ hLt M ρ r₁ w = 0) ∨ (hLt M ρ r₁ 1 < 0 ∧ w = 1)) := by
  have hbot := hLt_neg_at_bot M ρ r₁ hrρ hρ1
  have hmono := hLt_strictMonoOn_w M ρ r₁ hrρ hρ1
  have hmax1 : max ρ M.a ≤ 1 := max_le hρ1 M.ha1.le
  by_cases htop : 0 ≤ hLt M ρ r₁ 1
  · have hex : ∃ w ∈ Icc (max ρ M.a) 1, hLt M ρ r₁ w = 0 := by
      have hcont : ContinuousOn (hLt M ρ r₁) (Icc (max ρ M.a) 1) :=
        (hLt_continuousOn_w M ρ r₁ (hrρ.le.trans hρ1)).mono
          (Icc_subset_Icc_left (hrρ.le.trans (le_max_left _ _)))
      exact intermediate_value_Icc hmax1 hcont ⟨hbot.le, htop⟩
    have hw_spec := Classical.choose_spec hex
    have hw_eq : cutoffLt M ρ r₁ = Classical.choose hex := dif_pos hex
    rw [hw_eq]
    have hgt : max ρ M.a < Classical.choose hex := by
      refine lt_of_le_of_ne hw_spec.1.1 ?_
      intro heq; rw [← heq] at hw_spec; linarith
    exact ⟨hw_spec.1, fun _ => hgt, Or.inl ⟨htop, hw_spec.2⟩⟩
  · push Not at htop
    have hno : ¬ ∃ w ∈ Icc (max ρ M.a) 1, hLt M ρ r₁ w = 0 := by
      rintro ⟨w, hw, hw0⟩
      rcases eq_or_lt_of_le hw.2 with rfl | hlt
      · linarith
      · have := hmono hw (right_mem_Icc.mpr hmax1) hlt; linarith
    have hw_eq : cutoffLt M ρ r₁ = 1 := dif_neg hno
    rw [hw_eq]
    exact ⟨right_mem_Icc.mpr hmax1, fun hρlt => max_lt hρlt M.ha1, Or.inr ⟨htop, rfl⟩⟩

lemma cutoffLt_unique (ρ r₁ : ℝ) (hrρ : r₁ < ρ) (hρ1 : ρ ≤ 1) {w : ℝ}
    (hw : w ∈ Icc (max ρ M.a) 1) (hw0 : hLt M ρ r₁ w = 0) :
    w = cutoffLt M ρ r₁ := by
  have hspec := cutoffLt_spec M ρ r₁ hrρ hρ1
  have hmono := hLt_strictMonoOn_w M ρ r₁ hrρ hρ1
  rcases hspec.2.2 with ⟨_, hc0⟩ | ⟨htop, _⟩
  · by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := hmono hw hspec.1 hlt; linarith
    · have := hmono hspec.1 hw hgt; linarith
  · rcases eq_or_lt_of_le hw.2 with rfl | hlt
    · linarith
    · have := hmono hw (right_mem_Icc.mpr (max_le hρ1 M.ha1.le)) hlt; linarith

lemma cutoffLt_hLt_nonpos (ρ r₁ : ℝ) (hrρ : r₁ < ρ) (hρ1 : ρ ≤ 1) :
    hLt M ρ r₁ (cutoffLt M ρ r₁) ≤ 0 := by
  rcases (cutoffLt_spec M ρ r₁ hrρ hρ1).2.2 with ⟨_, h0⟩ | ⟨htop, hw1⟩
  · exact h0.le
  · rw [hw1]; exact htop.le

lemma hLt_sub_r (ρ r₁ r₂ w : ℝ) (hr1 : r₁ ≤ 1) (hr2 : r₂ ≤ 1) (hw1 : w ≤ 1) :
    hLt M ρ r₂ w - hLt M ρ r₁ w = ∫ v in r₁..r₂, (F1Lt M w v) ^ (M.n - 1) := by
  unfold hLt
  have hint : ∀ a b, a ≤ 1 → b ≤ 1 →
      IntervalIntegrable (fun v => (F1Lt M w v) ^ (M.n - 1)) volume a b := by
    intro a b ha hb
    exact ((F1Lt_continuousOn_v M w).pow (M.n - 1) |>.mono (by
      intro t ht; rcases le_total a b with hle | hle
      · rw [uIcc_of_le hle] at ht; exact ht.2.trans hb
      · rw [uIcc_comm, uIcc_of_le hle] at ht; exact ht.2.trans ha)).intervalIntegrable
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hint r₁ r₂ hr1 hr2) (hint r₂ w hr2 hw1)
  linarith

/-- **Proposition 1(ii) (`r₁ < ρ`, antitonicity)**: `r₁ ↦ cutoffLt M ρ r₁` is nonincreasing
on `[0, ρ)`. -/
theorem prop1_cutoffLt_antitone (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) :
    AntitoneOn (cutoffLt M ρ) (Ico 0 ρ) := by
  intro r₁ hr₁ r₂ hr₂ hle
  have hs1 := cutoffLt_spec M ρ r₁ hr₁.2 hρ1
  have hs2 := cutoffLt_spec M ρ r₂ hr₂.2 hρ1
  rcases hs1.2.2 with ⟨_, h0_1⟩ | ⟨_, hw1_1⟩
  · by_contra hlt; push Not at hlt
    have hgt := hLt_strictMonoOn_w M ρ r₂ hr₂.2 hρ1 hs1.1 hs2.1 hlt
    have hsub := hLt_sub_r M ρ r₁ r₂ (cutoffLt M ρ r₁) (hr₁.2.le.trans hρ1)
      (hr₂.2.le.trans hρ1) hs1.1.2
    have hnn : 0 ≤ ∫ v in r₁..r₂, (F1Lt M (cutoffLt M ρ r₁) v) ^ (M.n - 1) :=
      intervalIntegral.integral_nonneg hle fun v hv =>
        pow_nonneg (F1Lt_mem_Icc M (hv.2.trans (hr₂.2.le.trans (le_trans (le_max_left _ _) hs1.1.1))) hs1.1.2).1 _
    have hle2 := cutoffLt_hLt_nonpos M ρ r₂ hr₂.2 hρ1
    linarith
  · rw [hw1_1]; exact hs2.1.2

/-- **Proposition 1(ii) (`r₁ < ρ`, continuity)**: `r₁ ↦ cutoffLt M ρ r₁` is continuous
on `[0, ρ)`. -/
theorem prop1_cutoffLt_continuous (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ContinuousOn (cutoffLt M ρ) (Ico 0 ρ) := by
  intro r₁ hr₁
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  by_cases hρeq : ρ = 1
  · subst hρeq
    refine ⟨ε, hε, fun r hr _ => ?_⟩
    have h1 := (cutoffLt_spec M 1 r₁ hr₁.2 le_rfl).1
    have h2 := (cutoffLt_spec M 1 r hr.2 le_rfl).1
    have hw1 : cutoffLt M 1 r₁ = 1 := le_antisymm h1.2 (le_trans (le_max_left 1 M.a) h1.1)
    have hwr : cutoffLt M 1 r = 1 := le_antisymm h2.2 (le_trans (le_max_left 1 M.a) h2.1)
    rw [hw1, hwr, dist_self]; exact hε
  · have hρlt : ρ < 1 := lt_of_le_of_ne hρ1 hρeq
    have hs1 := cutoffLt_spec M ρ r₁ hr₁.2 hρ1
    set w := cutoffLt M ρ r₁
    have hbot_lt : max ρ M.a < w := hs1.2.1 hρlt
    set ε' := min (ε / 2) ((w - max ρ M.a) / 2)
    have hε'pos : 0 < ε' := lt_min (half_pos hε) (half_pos (sub_pos.mpr hbot_lt))
    set wlo := w - ε'
    have hwlo_gt : max ρ M.a < wlo := by
      have : ε' ≤ (w - max ρ M.a) / 2 := min_le_right _ _; linarith
    have hwlo_lt : wlo < w := by linarith
    have hwlo_mem : wlo ∈ Icc (max ρ M.a) 1 := ⟨hwlo_gt.le, hwlo_lt.le.trans hs1.1.2⟩
    have hneg_lo : hLt M ρ r₁ wlo < 0 := by
      have := hLt_strictMonoOn_w M ρ r₁ hr₁.2 hρ1 hwlo_mem hs1.1 hwlo_lt
      linarith [cutoffLt_hLt_nonpos M ρ r₁ hr₁.2 hρ1]
    have hbound_r : ∀ r ∈ Ico (0 : ℝ) ρ, ∀ u ∈ Icc (max ρ M.a) 1,
        |hLt M ρ r u - hLt M ρ r₁ u| ≤ |r - r₁| := by
      intro r hr u hu
      rw [hLt_sub_r M ρ r₁ r u (hr₁.2.le.trans hρ1) (hr.2.le.trans hρ1) hu.2]
      rcases le_total r₁ r with hle | hle
      · have hnn : 0 ≤ ∫ v in r₁..r, (F1Lt M u v) ^ (M.n - 1) :=
          intervalIntegral.integral_nonneg hle fun v hv =>
            pow_nonneg (F1Lt_mem_Icc M (hv.2.trans (hr.2.le.trans (le_trans (le_max_left _ _) hu.1))) hu.2).1 _
        rw [abs_of_nonneg hnn, abs_of_nonneg (sub_nonneg.mpr hle)]
        calc ∫ v in r₁..r, (F1Lt M u v) ^ (M.n - 1)
            ≤ ∫ _ in r₁..r, (1 : ℝ) := intervalIntegral.integral_mono_on hle
              ((((F1Lt_continuousOn_v M u).pow (M.n - 1)).mono
                (fun t (ht : t ∈ Icc r₁ r) => ht.2.trans (hr.2.le.trans hρ1))).intervalIntegrable_of_Icc hle)
              intervalIntegrable_const
              (fun v hv => by
                have hmem := F1Lt_mem_Icc M
                  (hv.2.trans (hr.2.le.trans (le_trans (le_max_left _ _) hu.1))) hu.2
                exact pow_le_one₀ hmem.1 hmem.2)
          _ = r - r₁ := by simp
      · rw [intervalIntegral.integral_symm, abs_neg, abs_of_nonpos (sub_nonpos.mpr hle)]
        have hnn : 0 ≤ ∫ v in r..r₁, (F1Lt M u v) ^ (M.n - 1) :=
          intervalIntegral.integral_nonneg hle fun v hv =>
            pow_nonneg (F1Lt_mem_Icc M (hv.2.trans (hr₁.2.le.trans (le_trans (le_max_left _ _) hu.1))) hu.2).1 _
        rw [abs_of_nonneg hnn]
        calc ∫ v in r..r₁, (F1Lt M u v) ^ (M.n - 1)
            ≤ ∫ _ in r..r₁, (1 : ℝ) := intervalIntegral.integral_mono_on hle
              ((((F1Lt_continuousOn_v M u).pow (M.n - 1)).mono
                (fun t (ht : t ∈ Icc r r₁) => ht.2.trans (hr₁.2.le.trans hρ1))).intervalIntegrable_of_Icc hle)
              intervalIntegrable_const
              (fun v hv => by
                have hmem := F1Lt_mem_Icc M
                  (hv.2.trans (hr₁.2.le.trans (le_trans (le_max_left _ _) hu.1))) hu.2
                exact pow_le_one₀ hmem.1 hmem.2)
          _ = -(r - r₁) := by simp
    by_cases hw_lt1 : w < 1
    · set whi := min (w + ε') 1
      have hwhi_gt : w < whi := lt_min (by linarith) hw_lt1
      have hwhi_mem : whi ∈ Icc (max ρ M.a) 1 := ⟨hs1.1.1.trans hwhi_gt.le, min_le_right _ _⟩
      have h0_w : hLt M ρ r₁ w = 0 := by
        rcases hs1.2.2 with ⟨_, h0⟩ | ⟨_, hw1⟩; exact h0; exfalso; linarith
      have hpos_hi : 0 < hLt M ρ r₁ whi := by
        have := hLt_strictMonoOn_w M ρ r₁ hr₁.2 hρ1 hs1.1 hwhi_mem hwhi_gt; linarith
      refine ⟨min (-hLt M ρ r₁ wlo) (hLt M ρ r₁ whi), lt_min (neg_pos.mpr hneg_lo) hpos_hi,
        fun r hr hdist => ?_⟩
      rw [Real.dist_eq] at hdist ⊢
      have hsr := cutoffLt_spec M ρ r hr.2 hρ1
      have hneg_r_lo : hLt M ρ r wlo < 0 := by
        have hb := hbound_r r hr wlo hwlo_mem
        have h1 : |r - r₁| < -hLt M ρ r₁ wlo := lt_of_lt_of_le hdist (min_le_left _ _)
        linarith [(abs_lt.mp (lt_of_le_of_lt hb h1)).2]
      have hpos_r_hi : 0 < hLt M ρ r whi := by
        have hb := hbound_r r hr whi hwhi_mem
        have h1 : |r - r₁| < hLt M ρ r₁ whi := lt_of_lt_of_le hdist (min_le_right _ _)
        linarith [(abs_lt.mp (lt_of_le_of_lt hb h1)).1]
      have hw_gt_lo : wlo < cutoffLt M ρ r := by
        by_contra hle; push Not at hle
        rcases hsr.2.2 with ⟨_, h0⟩ | ⟨_, h1⟩
        · rcases eq_or_lt_of_le hle with heq | hlt
          · rw [heq] at h0; linarith
          · have := hLt_strictMonoOn_w M ρ r hr.2 hρ1 hsr.1 hwlo_mem hlt; linarith
        · linarith [hwlo_lt, hs1.1.2]
      have hw_lt_hi : cutoffLt M ρ r < whi := by
        by_contra hge; push Not at hge
        have hle0 := cutoffLt_hLt_nonpos M ρ r hr.2 hρ1
        rcases eq_or_lt_of_le hge with heq | hlt
        · rw [← heq] at hle0; linarith
        · have := hLt_strictMonoOn_w M ρ r hr.2 hρ1 hwhi_mem hsr.1 hlt; linarith
      rw [abs_lt]
      have hε'le : ε' ≤ ε / 2 := min_le_left _ _
      constructor <;> linarith [min_le_left (w + ε') 1]
    · have hw1 : w = 1 := le_antisymm hs1.1.2 (le_of_not_gt hw_lt1)
      refine ⟨-hLt M ρ r₁ wlo, neg_pos.mpr hneg_lo, fun r hr hdist => ?_⟩
      rw [Real.dist_eq] at hdist ⊢
      have hsr := cutoffLt_spec M ρ r hr.2 hρ1
      have hneg_r_lo : hLt M ρ r wlo < 0 := by
        have hb := hbound_r r hr wlo hwlo_mem
        linarith [(abs_lt.mp (lt_of_le_of_lt hb hdist)).2]
      have hw_gt_lo : wlo < cutoffLt M ρ r := by
        by_contra hle; push Not at hle
        rcases hsr.2.2 with ⟨_, h0⟩ | ⟨_, h1⟩
        · rcases eq_or_lt_of_le hle with heq | hlt
          · rw [heq] at h0; linarith
          · have := hLt_strictMonoOn_w M ρ r hr.2 hρ1 hsr.1 hwlo_mem hlt; linarith
        · linarith [hwlo_lt, hs1.1.2]
      rw [abs_lt]
      have hε'le : ε' ≤ ε / 2 := min_le_left _ _
      constructor <;> linarith [hsr.1.2]

/-- Explicit cutoff visit strategy for `r₁ < ρ`: types `< w` visit seller 1 exclusively,
types `≥ w` split uniformly across all `m` sellers. -/
noncomputable def cutoffLtVisit (w : ℝ) : VisitStrategy M where
  θ j v := if v < w then (if j = 0 then 1 else 0) else 1 / (M.m : ℝ)
  hmeas j := by
    have h1 : Measurable (fun _ : ℝ => if j = 0 then (1 : ℝ) else 0) := measurable_const
    exact h1.ite measurableSet_Iio measurable_const
  hnonneg j v := by
    split_ifs
    · exact zero_le_one
    · exact le_rfl
    · exact div_nonneg zero_le_one M.m_pos_real.le
  hsum v _ := by
    by_cases hvw : v < w
    · simp only [if_pos hvw]
      rw [Finset.sum_eq_single (0 : Fin M.m)]
      · simp
      · intro j _ hj; simp [hj]
      · intro h; exact absurd (Finset.mem_univ _) h
    · simp only [if_neg hvw, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact mul_one_div_cancel M.m_pos_real.ne'

lemma effDist_cutoffLtVisit_zero {w v : ℝ} (hw1 : w ≤ 1) (hv1 : v ≤ 1) :
    effDist M (cutoffLtVisit M w) 0 v = if v ≤ w then F1Lt M w v else M.A v := by
  unfold effDist cutoffLtVisit
  simp only [ite_true]
  by_cases hvw : v ≤ w
  · rw [if_pos hvw]
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      ((cutoffLtVisit M w).mul_f_intervalIntegrable 0 hv1 hw1)
      ((cutoffLtVisit M w).mul_f_intervalIntegrable 0 hw1 le_rfl)
    have h1 : ∫ u in v..w, (if u < w then (1 : ℝ) else 1 / (M.m : ℝ)) * M.f u =
        M.F w - M.F v := by
      have hcongr : ∫ u in v..w, (if u < w then (1 : ℝ) else 1 / (M.m : ℝ)) * M.f u =
          ∫ u in v..w, M.f u := by
        apply intervalIntegral.integral_congr_ae
        have hne : ∀ᵐ u ∂volume, u ≠ w := by simp [ae_iff, measure_singleton]
        filter_upwards [hne] with u hu hmem
        rw [uIoc_of_le hvw] at hmem
        simp [lt_of_le_of_ne hmem.2 hu]
      rw [hcongr, M.integral_f hv1 hw1]
    have h2 : ∫ u in w..1, (if u < w then (1 : ℝ) else 1 / (M.m : ℝ)) * M.f u =
        (1 - M.F w) / (M.m : ℝ) := by
      have hcongr : ∫ u in w..1, (if u < w then (1 : ℝ) else 1 / (M.m : ℝ)) * M.f u =
          ∫ u in w..1, (1 / (M.m : ℝ)) * M.f u := by
        apply intervalIntegral.integral_congr; intro u hu; dsimp only
        rw [uIcc_of_le hw1] at hu
        rw [ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr hu.1))]
      rw [hcongr, intervalIntegral.integral_const_mul, M.integral_f hw1 le_rfl, M.hF_1]; ring
    have htot : ∫ u in v..1, (if u < w then (1 : ℝ) else 1 / (M.m : ℝ)) * M.f u =
        (M.F w - M.F v) + (1 - M.F w) / (M.m : ℝ) := by
      have hsp : (∫ u in v..w, (if u < w then (1 : ℝ) else 1 / (M.m : ℝ)) * M.f u) +
          (∫ u in w..1, (if u < w then (1 : ℝ) else 1 / (M.m : ℝ)) * M.f u) =
          ∫ u in v..1, (if u < w then (1 : ℝ) else 1 / (M.m : ℝ)) * M.f u := by
        simpa only [cutoffLtVisit, ite_true] using hsplit
      rw [← hsp, h1, h2]
    rw [htot]; unfold F1Lt Market.A; ring
  · rw [if_neg hvw]; push Not at hvw
    have hcongr : ∫ u in v..1, (if u < w then (1 : ℝ) else 1 / (M.m : ℝ)) * M.f u =
        ∫ u in v..1, (1 / (M.m : ℝ)) * M.f u := by
      apply intervalIntegral.integral_congr; intro u hu; dsimp only
      rw [uIcc_of_le hv1] at hu
      rw [ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr (hvw.le.trans hu.1)))]
    rw [hcongr, intervalIntegral.integral_const_mul, M.integral_f hv1 le_rfl, M.hF_1]
    unfold Market.A; ring

lemma effDist_cutoffLtVisit_rival {w v : ℝ} (hw1 : w ≤ 1) (hv1 : v ≤ 1)
    {j : Fin M.m} (hj : j ≠ 0) :
    effDist M (cutoffLtVisit M w) j v = M.A (max v w) := by
  unfold effDist cutoffLtVisit Market.A
  simp only [ite_eq_right_iff.mpr (fun h => absurd h hj)]
  by_cases hvw : v ≤ w
  · rw [max_eq_right hvw]
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      ((cutoffLtVisit M w).mul_f_intervalIntegrable j hv1 hw1)
      ((cutoffLtVisit M w).mul_f_intervalIntegrable j hw1 le_rfl)
    have h1 : ∫ u in v..w, (if u < w then (0 : ℝ) else 1 / (M.m : ℝ)) * M.f u = 0 := by
      have hcongr : ∫ u in v..w, (if u < w then (0 : ℝ) else 1 / (M.m : ℝ)) * M.f u =
          ∫ _ in v..w, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_ae
        have hne : ∀ᵐ u ∂volume, u ≠ w := by simp [ae_iff, measure_singleton]
        filter_upwards [hne] with u hu hmem
        rw [uIoc_of_le hvw] at hmem
        simp [lt_of_le_of_ne hmem.2 hu]
      rw [hcongr]; simp
    have h2 : ∫ u in w..1, (if u < w then (0 : ℝ) else 1 / (M.m : ℝ)) * M.f u =
        (1 - M.F w) / (M.m : ℝ) := by
      have hcongr : ∫ u in w..1, (if u < w then (0 : ℝ) else 1 / (M.m : ℝ)) * M.f u =
          ∫ u in w..1, (1 / (M.m : ℝ)) * M.f u := by
        apply intervalIntegral.integral_congr; intro u hu; dsimp only
        rw [uIcc_of_le hw1] at hu
        rw [ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr hu.1))]
      rw [hcongr, intervalIntegral.integral_const_mul, M.integral_f hw1 le_rfl, M.hF_1]; ring
    have htot : ∫ u in v..1, (if u < w then (0 : ℝ) else 1 / (M.m : ℝ)) * M.f u =
        (1 - M.F w) / (M.m : ℝ) := by
      have hsp : (∫ u in v..w, (if u < w then (0 : ℝ) else 1 / (M.m : ℝ)) * M.f u) +
          (∫ u in w..1, (if u < w then (0 : ℝ) else 1 / (M.m : ℝ)) * M.f u) =
          ∫ u in v..1, (if u < w then (0 : ℝ) else 1 / (M.m : ℝ)) * M.f u := by
        simpa only [cutoffLtVisit, ite_eq_right_iff.mpr (fun h => absurd h hj)] using hsplit
      rw [← hsp, h1, h2, zero_add]
    rw [htot]
  · push Not at hvw
    rw [max_eq_left hvw.le]
    have hcongr : ∫ u in v..1, (if u < w then (0 : ℝ) else 1 / (M.m : ℝ)) * M.f u =
        ∫ u in v..1, (1 / (M.m : ℝ)) * M.f u := by
      apply intervalIntegral.integral_congr; intro u hu; dsimp only
      rw [uIcc_of_le hv1] at hu
      rw [ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr (hvw.le.trans hu.1)))]
    rw [hcongr, intervalIntegral.integral_const_mul, M.integral_f hv1 le_rfl, M.hF_1]; ring

/-- **Proposition 1(ii) (`r₁ < ρ`, SR verification)**: With seller 1 at `SPA(r₁)` and rivals
at `SPA(ρ)` (`r₁ < ρ`), `cutoffLtVisit M (cutoffLt M ρ r₁)` is sequentially rational. -/
theorem prop1_cutoffLt_isSR (ρ r₁ : ℝ) (hr0 : 0 ≤ r₁) (hrρ : r₁ < ρ) (hρ1 : ρ ≤ 1) :
    let w := cutoffLt M ρ r₁
    let mechs : Fin M.m → HierarchicalMech :=
      fun j => if j = 0 then SPA r₁ hr0 (hrρ.le.trans hρ1) else SPA ρ (hr0.trans hrρ.le) hρ1
    IsSR M mechs (cutoffLtVisit M w) := by
  intro w mechs
  have hspec := cutoffLt_spec M ρ r₁ hrρ hρ1
  have hr11 : r₁ ≤ 1 := hrρ.le.trans hρ1
  have hρ0 : 0 ≤ ρ := hr0.trans hrρ.le
  have hρw : ρ ≤ w := le_trans (le_max_left _ _) hspec.1.1
  have hrw : r₁ ≤ w := hrρ.le.trans hρw
  have hw1 : w ≤ 1 := hspec.1.2
  have hs_riv_eq : ∀ j k : Fin M.m, j ≠ 0 → k ≠ 0 → ∀ v ∈ Icc M.a 1,
      surplus M (mechs j) (effDist M (cutoffLtVisit M w) j) v =
      surplus M (mechs k) (effDist M (cutoffLtVisit M w) k) v := by
    intro j k hj hk v hv
    simp only [mechs, if_neg hj, if_neg hk]
    rw [surplus_SPA_eq M ρ hρ0 hρ1 _ (vs_effDist_monotoneOn _ _) (fun x hx => effDist_nonneg _ _ hx)
          (M.ha0.trans hv.1) hv.2,
        surplus_SPA_eq M ρ hρ0 hρ1 _ (vs_effDist_monotoneOn _ _) (fun x hx => effDist_nonneg _ _ hx)
          (M.ha0.trans hv.1) hv.2]
    apply intervalIntegral.integral_congr; intro t ht; dsimp only
    rw [uIcc_of_le (le_max_right v ρ)] at ht
    have ht1 : t ≤ 1 := ht.2.trans (max_le hv.2 hρ1)
    rw [effDist_cutoffLtVisit_rival M hw1 ht1 hj, effDist_cutoffLtVisit_rival M hw1 ht1 hk]
  have hs0_at_w : surplus M (mechs 0) (effDist M (cutoffLtVisit M w) 0) w =
      ∫ t in r₁..w, (F1Lt M w t) ^ (M.n - 1) := by
    simp only [mechs, ite_true]
    rw [surplus_SPA_eq M r₁ hr0 hr11 _ (vs_effDist_monotoneOn _ _) (fun x hx => effDist_nonneg _ _ hx)
          (hr0.trans hrw) hw1, max_eq_left hrw]
    apply intervalIntegral.integral_congr; intro t ht; dsimp only
    rw [uIcc_of_le hrw] at ht
    rw [effDist_cutoffLtVisit_zero M hw1 (ht.2.trans hw1), if_pos ht.2]
  have hsriv_at_w : ∀ j : Fin M.m, j ≠ 0 →
      surplus M (mechs j) (effDist M (cutoffLtVisit M w) j) w =
      (w - ρ) * (M.A w) ^ (M.n - 1) := by
    intro j hj
    simp only [mechs, if_neg hj]
    rw [surplus_SPA_eq M ρ hρ0 hρ1 _ (vs_effDist_monotoneOn _ _) (fun x hx => effDist_nonneg _ _ hx)
          (hρ0.trans hρw) hw1, max_eq_left hρw]
    have hcongr : ∫ t in ρ..w, (effDist M (cutoffLtVisit M w) j t) ^ (M.n - 1) =
        ∫ _ in ρ..w, (M.A w) ^ (M.n - 1) := by
      apply intervalIntegral.integral_congr; intro t ht; dsimp only
      rw [uIcc_of_le hρw] at ht
      rw [effDist_cutoffLtVisit_rival M hw1 (ht.2.trans hw1) hj, max_eq_right ht.2]
    rw [hcongr, intervalIntegral.integral_const, smul_eq_mul]
  have hs_ge_below : ∀ j : Fin M.m, j ≠ 0 → ∀ v ∈ Icc M.a 1, v ≤ w →
      surplus M (mechs j) (effDist M (cutoffLtVisit M w) j) v ≤
      surplus M (mechs 0) (effDist M (cutoffLtVisit M w) 0) v := by
    intro j hj v hv hvw
    by_cases hvρ : v ≤ ρ
    · simp only [mechs, ite_true, if_neg hj]
      rw [surplus_zero_of_le_r M (SPA ρ hρ0 hρ1) _ (M.ha0.trans hv.1) hvρ]
      rw [surplus_SPA_eq M r₁ hr0 hr11 _ (vs_effDist_monotoneOn _ _) (fun x hx => effDist_nonneg _ _ hx)
            (M.ha0.trans hv.1) hv.2]
      exact intervalIntegral.integral_nonneg (le_max_right v r₁) fun t ht =>
        pow_nonneg (effDist_nonneg _ _ (ht.2.trans (max_le hv.2 hr11))) _
    · push Not at hvρ
      have hdiff_j : surplus M (mechs j) (effDist M (cutoffLtVisit M w) j) w -
          surplus M (mechs j) (effDist M (cutoffLtVisit M w) j) v =
          (w - v) * (M.A w) ^ (M.n - 1) := by
        simp only [mechs, if_neg hj]
        rw [surplus_sub M (SPA ρ hρ0 hρ1) _ (vs_effDist_monotoneOn _ _)
              (fun x hx => effDist_nonneg _ _ hx) hv.2 hw1]
        have hcongr : ∫ t in v..w, alloc M (SPA ρ hρ0 hρ1) (effDist M (cutoffLtVisit M w) j) t =
            ∫ _ in v..w, (M.A w) ^ (M.n - 1) := by
          apply intervalIntegral.integral_congr; intro t ht; dsimp only
          rw [uIcc_of_le hvw] at ht
          rw [alloc_SPA, ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr (hvρ.le.trans ht.1))),
            effDist_cutoffLtVisit_rival M hw1 (ht.2.trans hw1) hj, max_eq_right ht.2]
        rw [hcongr, intervalIntegral.integral_const, smul_eq_mul]
      have hdiff_0 : surplus M (mechs 0) (effDist M (cutoffLtVisit M w) 0) w -
          surplus M (mechs 0) (effDist M (cutoffLtVisit M w) 0) v ≤
          (w - v) * (M.A w) ^ (M.n - 1) := by
        simp only [mechs, ite_true]
        rw [surplus_sub M (SPA r₁ hr0 hr11) _ (vs_effDist_monotoneOn _ _)
              (fun x hx => effDist_nonneg _ _ hx) hv.2 hw1]
        have hle_int : ∫ t in v..w, alloc M (SPA r₁ hr0 hr11) (effDist M (cutoffLtVisit M w) 0) t ≤
            ∫ _ in v..w, (M.A w) ^ (M.n - 1) := by
          apply intervalIntegral.integral_mono_on hvw
            (alloc_intervalIntegrable M _ _ (vs_effDist_monotoneOn _ _)
              (fun x hx => effDist_nonneg _ _ hx) hv.2 hw1)
            intervalIntegrable_const
          intro t ht
          rw [alloc_SPA, ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr (hrρ.le.trans (hvρ.le.trans ht.1)))),
            effDist_cutoffLtVisit_zero M hw1 (ht.2.trans hw1), if_pos ht.2]
          have hFle : F1Lt M w t ≤ M.A w := by
            unfold F1Lt; linarith [M.F_monotoneOn_Iic (ht.2.trans hw1) hw1 ht.2]
          exact pow_le_pow_left₀ (F1Lt_mem_Icc M ht.2 hw1).1 hFle _
        simpa [intervalIntegral.integral_const, smul_eq_mul] using hle_int
      have hw_ge : surplus M (mechs j) (effDist M (cutoffLtVisit M w) j) w ≤
          surplus M (mechs 0) (effDist M (cutoffLtVisit M w) 0) w := by
        rw [hs0_at_w, hsriv_at_w j hj]
        have := cutoffLt_hLt_nonpos M ρ r₁ hrρ hρ1
        unfold hLt at this; linarith
      linarith
  have hs_eq_above : ∀ j : Fin M.m, j ≠ 0 → ∀ v ∈ Icc M.a 1, w ≤ v →
      hLt M ρ r₁ w = 0 →
      surplus M (mechs 0) (effDist M (cutoffLtVisit M w) 0) v =
      surplus M (mechs j) (effDist M (cutoffLtVisit M w) j) v := by
    intro j hj v hv hwv h0
    have hat_w : surplus M (mechs 0) (effDist M (cutoffLtVisit M w) 0) w =
        surplus M (mechs j) (effDist M (cutoffLtVisit M w) j) w := by
      rw [hs0_at_w, hsriv_at_w j hj]; unfold hLt at h0; linarith
    have hd0 : surplus M (mechs 0) (effDist M (cutoffLtVisit M w) 0) v -
        surplus M (mechs 0) (effDist M (cutoffLtVisit M w) 0) w =
        ∫ t in w..v, (M.A t) ^ (M.n - 1) := by
      simp only [mechs, ite_true]
      rw [surplus_sub M (SPA r₁ hr0 hr11) _ (vs_effDist_monotoneOn _ _)
            (fun x hx => effDist_nonneg _ _ hx) hw1 hv.2]
      apply intervalIntegral.integral_congr_ae
      have hne : ∀ᵐ t ∂volume, t ≠ w := by simp [ae_iff, measure_singleton]
      filter_upwards [hne] with t ht hmem
      rw [uIoc_of_le hwv] at hmem
      have hwt : w < t := hmem.1
      rw [alloc_SPA, ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr (hrw.trans hwt.le))),
        effDist_cutoffLtVisit_zero M hw1 (hmem.2.trans hv.2), if_neg (not_le.mpr hwt)]
    have hdj : surplus M (mechs j) (effDist M (cutoffLtVisit M w) j) v -
        surplus M (mechs j) (effDist M (cutoffLtVisit M w) j) w =
        ∫ t in w..v, (M.A t) ^ (M.n - 1) := by
      simp only [mechs, if_neg hj]
      rw [surplus_sub M (SPA ρ hρ0 hρ1) _ (vs_effDist_monotoneOn _ _)
            (fun x hx => effDist_nonneg _ _ hx) hw1 hv.2]
      apply intervalIntegral.integral_congr; intro t ht; dsimp only
      rw [uIcc_of_le hwv] at ht
      rw [alloc_SPA, ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr (hρw.trans ht.1))),
        effDist_cutoffLtVisit_rival M hw1 (ht.2.trans hv.2) hj, max_eq_left ht.1]
    linarith
  rw [IsSR, MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  have hne_w : ∀ᵐ v ∂volume, v ≠ w := by simp [ae_iff, measure_singleton]
  filter_upwards [hne_w] with v hvw_ne hv j k hjpos
  by_cases hvw : v < w
  · have hj0 : j = 0 := by
      by_contra hne; simp [cutoffLtVisit, hvw, hne] at hjpos
    subst hj0
    by_cases hk0 : k = 0
    · subst hk0; exact le_rfl
    · exact hs_ge_below k hk0 v hv hvw.le
  · push Not at hvw
    have hwv_lt : w < v := lt_of_le_of_ne hvw (Ne.symm hvw_ne)
    have h0 : hLt M ρ r₁ w = 0 := by
      rcases hspec.2.2 with ⟨_, h0⟩ | ⟨_, hw1'⟩
      · exact h0
      · exfalso; linarith [hv.2]
    by_cases hj0 : j = 0
    · subst hj0
      by_cases hk0 : k = 0
      · subst hk0; exact le_rfl
      · exact le_of_eq (hs_eq_above k hk0 v hv hvw h0).symm
    · by_cases hk0 : k = 0
      · subst hk0; exact le_of_eq (hs_eq_above j hj0 v hv hvw h0)
      · exact le_of_eq (hs_riv_eq k j hk0 hj0 v hv)

end Proposition1

/-! ### Part 2: Proposition 2(i)–(ii) — Rival Symmetry and Uniqueness after Any Unilateral Deviation -/

section Proposition2

variable (M : Market)

/-- Mechanism profile where seller `0` posts `m1` and all `m - 1` rivals post `SPA(ρ)`. -/
def unilateralProfile (m1 : HierarchicalMech) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    Fin M.m → HierarchicalMech :=
  fun j => if j = 0 then m1 else SPA ρ hρ0 hρ1

/-- Canonical rival index `1 : Fin M.m` (exists since `2 ≤ M.m`). -/
def rivalIdx : Fin M.m := ⟨1, lt_of_lt_of_le (by decide : 1 < 2) M.hm⟩

lemma rivalIdx_ne_zero : rivalIdx M ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  simp [rivalIdx] at this

/-- Rival effective distribution implied by market clearing given seller 1's `F₁`:
`F_riv(v) = 1 - (F₁(v) - F(v)) / (m - 1)`. -/
noncomputable def FrivOf (F1 : ℝ → ℝ) (v : ℝ) : ℝ :=
  1 - (F1 v - M.F v) / ((M.m : ℝ) - 1)

/-- Rival surplus implied by `F₁` under `SPA(ρ)`. -/
noncomputable def srivOf (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (F1 : ℝ → ℝ) (v : ℝ) : ℝ :=
  surplus M (SPA ρ hρ0 hρ1) (FrivOf M F1) v

/-- Seller 1's surplus advantage `σ(v) = s₁(v) - s_riv(v)` in a continuation `θ`. -/
noncomputable def sigma (m1 : HierarchicalMech) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (θ : VisitStrategy M) (v : ℝ) : ℝ :=
  surplus M m1 (effDist M θ 0) v - srivOf M ρ hρ0 hρ1 (effDist M θ 0) v

/-- **Proposition 2(i) (Rival symmetry)**: In every SR continuation against rivals at `SPA(ρ)`,
all rivals induce the same effective distribution `F_riv(v) = 1 - (F₁(v) - F(v)) / (m - 1)` on `[ρ, 1]`. -/
theorem prop2_rival_symmetry (m1 : HierarchicalMech) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    {θ : VisitStrategy M} (hSR : IsSR M (unilateralProfile M m1 ρ hρ0 hρ1) θ) :
    (∀ j k : Fin M.m, j ≠ 0 → k ≠ 0 →
      ∀ v ∈ Icc ρ 1, effDist M θ j v = effDist M θ k v) ∧
    (∀ j : Fin M.m, j ≠ 0 →
      ∀ v ∈ Icc ρ 1, effDist M θ j v = FrivOf M (effDist M θ 0) v) := by
  have hsym : ∀ j k : Fin M.m, j ≠ 0 → k ≠ 0 →
      ∀ v ∈ Icc ρ 1, effDist M θ j v = effDist M θ k v := by
    intro j k hj hk
    let φ : ℝ → ℝ := fun v => (effDist M θ j v) ^ (M.n - 1) - (effDist M θ k v) ^ (M.n - 1)
    let g : ℝ → ℝ := fun u => (θ.θ j u - θ.θ k u) * M.f u
    have hφ_cont : ContinuousOn φ (Icc ρ 1) :=
      (((effDist_continuousOn θ j).mono Icc_subset_Iic_self).pow (M.n - 1)).sub
        (((effDist_continuousOn θ k).mono Icc_subset_Iic_self).pow (M.n - 1))
    have hg_int : IntervalIntegrable g volume (min M.a ρ) 1 := by
      have hmin1 : min M.a ρ ≤ 1 := min_le_of_left_le M.ha1.le
      have h1 := θ.mul_f_intervalIntegrable j hmin1 le_rfl
      have h2 := θ.mul_f_intervalIntegrable k hmin1 le_rfl
      have hsub := h1.sub h2
      have hfun : (fun u => θ.θ j u * M.f u - θ.θ k u * M.f u) = g := by ext u; simp [g]; ring
      rwa [hfun] at hsub
    have hswap := fubini_tail_integral M.ha0 M.ha1 hρ0 hρ1 hφ_cont hg_int
      (fun u hu => by simp [g, M.hf_below u hu])
    -- LHS = -∫_ρ^1 (F_j^(n-1) - F_k^(n-1)) (F_j - F_k)
    have hLHS : ∫ v in ρ..1, φ v * (∫ u in v..1, g u) =
        - ∫ v in ρ..1, ((effDist M θ j v) ^ (M.n - 1) - (effDist M θ k v) ^ (M.n - 1)) *
          (effDist M θ j v - effDist M θ k v) := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro v hv; dsimp only
      rw [uIcc_of_le hρ1] at hv
      have hsub : ∫ u in v..1, g u = effDist M θ k v - effDist M θ j v := by
        have hfun : g = fun u => θ.θ j u * M.f u - θ.θ k u * M.f u := by ext u; simp [g]; ring
        rw [hfun, intervalIntegral.integral_sub (θ.mul_f_intervalIntegrable j hv.2 le_rfl)
          (θ.mul_f_intervalIntegrable k hv.2 le_rfl)]
        unfold effDist; ring
      rw [hsub]; simp only [φ]; ring
    -- RHS = ∫_a^1 (θ_j - θ_k) * (s_j - s_k) * f ≥ 0
    have hRHS_nonneg : 0 ≤ ∫ u in M.a..1, g u * (∫ v in ρ..(max u ρ), φ v) := by
      rw [intervalIntegral.integral_of_le M.ha1.le]
      apply MeasureTheory.integral_nonneg_of_ae
      have hSR_Ioc := MeasureTheory.ae_mono
        (MeasureTheory.Measure.restrict_mono Ioc_subset_Icc_self le_rfl) hSR
      filter_upwards [hSR_Ioc, MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu hmem
      have hu0 : 0 ≤ u := M.ha0.trans hmem.1.le
      have hu1 : u ≤ 1 := hmem.2
      have hs_diff : ∫ v in ρ..(max u ρ), φ v =
          surplus M (SPA ρ hρ0 hρ1) (effDist M θ j) u -
          surplus M (SPA ρ hρ0 hρ1) (effDist M θ k) u := by
        rw [surplus_SPA_eq M ρ hρ0 hρ1 _ (vs_effDist_monotoneOn θ j) (fun x hx => effDist_nonneg θ j hx) hu0 hu1,
            surplus_SPA_eq M ρ hρ0 hρ1 _ (vs_effDist_monotoneOn θ k) (fun x hx => effDist_nonneg θ k hx) hu0 hu1]
        have hintj : IntervalIntegrable (fun v => (effDist M θ j v) ^ (M.n - 1)) volume ρ (max u ρ) :=
          (((effDist_continuousOn θ j).mono (fun t (ht : t ∈ Icc ρ (max u ρ)) =>
            ht.2.trans (max_le hu1 hρ1))).pow (M.n - 1)).intervalIntegrable_of_Icc (le_max_right u ρ)
        have hintk : IntervalIntegrable (fun v => (effDist M θ k v) ^ (M.n - 1)) volume ρ (max u ρ) :=
          (((effDist_continuousOn θ k).mono (fun t (ht : t ∈ Icc ρ (max u ρ)) =>
            ht.2.trans (max_le hu1 hρ1))).pow (M.n - 1)).intervalIntegrable_of_Icc (le_max_right u ρ)
        exact intervalIntegral.integral_sub hintj hintk
      change 0 ≤ g u * ∫ v in ρ..(max u ρ), φ v
      rw [hs_diff]; simp only [g]
      have hfj : 0 ≤ M.f u := M.f_nonneg_Iic hu1
      have hprod : 0 ≤ (θ.θ j u - θ.θ k u) *
          (surplus M (SPA ρ hρ0 hρ1) (effDist M θ j) u -
           surplus M (SPA ρ hρ0 hρ1) (effDist M θ k) u) := by
        rcases lt_trichotomy (θ.θ j u) (θ.θ k u) with hlt | heq | hgt
        · have hkpos : 0 < θ.θ k u := lt_of_le_of_lt (θ.hnonneg j u) hlt
          have hsle := hu k j hkpos
          simp only [unilateralProfile, ite_eq_right_iff.mpr (fun h => absurd h hj),
            ite_eq_right_iff.mpr (fun h => absurd h hk)] at hsle
          exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
        · rw [heq, sub_self, zero_mul]
        · have hjpos : 0 < θ.θ j u := lt_of_le_of_lt (θ.hnonneg k u) hgt
          have hsle := hu j k hjpos
          simp only [unilateralProfile, ite_eq_right_iff.mpr (fun h => absurd h hj),
            ite_eq_right_iff.mpr (fun h => absurd h hk)] at hsle
          exact mul_nonneg (by linarith) (by linarith)
      have : (θ.θ j u - θ.θ k u) * M.f u *
          (surplus M (SPA ρ hρ0 hρ1) (effDist M θ j) u -
           surplus M (SPA ρ hρ0 hρ1) (effDist M θ k) u) =
          (θ.θ j u - θ.θ k u) *
          (surplus M (SPA ρ hρ0 hρ1) (effDist M θ j) u -
           surplus M (SPA ρ hρ0 hρ1) (effDist M θ k) u) * M.f u := by ring
      rw [this]
      exact mul_nonneg hprod hfj
    -- Combine: ∫_ρ^1 (F_j^(n-1) - F_k^(n-1)) (F_j - F_k) ≤ 0, while integrand ≥ 0 and continuous!
    let ψ : ℝ → ℝ := fun v =>
      ((effDist M θ j v) ^ (M.n - 1) - (effDist M θ k v) ^ (M.n - 1)) *
      (effDist M θ j v - effDist M θ k v)
    have hψ_cont : ContinuousOn ψ (Icc ρ 1) :=
      hφ_cont.mul (((effDist_continuousOn θ j).mono Icc_subset_Iic_self).sub
        ((effDist_continuousOn θ k).mono Icc_subset_Iic_self))
    have hψ_nn : ∀ v ∈ Icc ρ 1, 0 ≤ ψ v := by
      intro v hv
      rcases le_total (effDist M θ j v) (effDist M θ k v) with hle | hle
      · exact mul_nonneg_of_nonpos_of_nonpos
          (sub_nonpos.mpr (pow_le_pow_left₀ (effDist_nonneg θ j hv.2) hle _))
          (sub_nonpos.mpr hle)
      · exact mul_nonneg
          (sub_nonneg.mpr (pow_le_pow_left₀ (effDist_nonneg θ k hv.2) hle _))
          (sub_nonneg.mpr hle)
    have hint_le0 : ∫ v in ρ..1, ψ v ≤ 0 := by linarith [hswap, hLHS, hRHS_nonneg]
    intro v hv
    by_contra hne
    have hψ_pos : 0 < ψ v := by
      have hn1 : M.n - 1 ≠ 0 := by have := M.hn; omega
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact mul_pos_of_neg_of_neg
          (sub_neg.mpr (pow_lt_pow_left₀ hlt (effDist_nonneg θ j hv.2) hn1))
          (sub_neg.mpr hlt)
      · exact mul_pos
          (sub_pos.mpr (pow_lt_pow_left₀ hgt (effDist_nonneg θ k hv.2) hn1))
          (sub_pos.mpr hgt)
    have hρlt : ρ < 1 := by
      refine lt_of_le_of_ne hρ1 ?_
      intro heq; subst heq
      have hv1 : v = 1 := le_antisymm hv.2 hv.1
      rw [hv1, vs_effDist_one, vs_effDist_one] at hne; exact hne rfl
    have hint_pos : 0 < ∫ t in ρ..1, ψ t :=
      intervalIntegral.integral_pos hρlt hψ_cont (fun t ht => hψ_nn t (Ioc_subset_Icc_self ht))
        ⟨v, hv, hψ_pos⟩
    linarith
  refine ⟨hsym, fun j hj v hv => ?_⟩
  have hsum := effDist_sum_one_sub θ hv.2
  have h0mem : (0 : Fin M.m) ∈ (Finset.univ : Finset (Fin M.m)) := Finset.mem_univ _
  rw [← Finset.add_sum_erase _ _ h0mem] at hsum
  have hcongr : ∑ k ∈ Finset.univ.erase (0 : Fin M.m), (1 - effDist M θ k v) =
      ((M.m : ℝ) - 1) * (1 - effDist M θ j v) := by
    have h1 : ∀ k ∈ Finset.univ.erase (0 : Fin M.m), 1 - effDist M θ k v = 1 - effDist M θ j v := by
      intro k hk; rw [hsym k j (Finset.ne_of_mem_erase hk) hj v hv]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_erase_of_mem h0mem,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_sub (by have := M.hm; omega : 1 ≤ M.m), Nat.cast_one]
  rw [hcongr] at hsum
  unfold FrivOf
  have hm1 : (M.m : ℝ) - 1 ≠ 0 := M.m_sub_one_pos_real.ne'
  field_simp [hm1]
  linarith

lemma prop2_rival_surplus_eq (m1 : HierarchicalMech) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    {θ : VisitStrategy M} (hSR : IsSR M (unilateralProfile M m1 ρ hρ0 hρ1) θ)
    {j : Fin M.m} (hj : j ≠ 0) {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    surplus M (SPA ρ hρ0 hρ1) (effDist M θ j) v = srivOf M ρ hρ0 hρ1 (effDist M θ 0) v := by
  have hsym := (prop2_rival_symmetry M m1 ρ hρ0 hρ1 hSR).2 j hj
  have hFriv_mono : MonotoneOn (FrivOf M (effDist M θ 0)) (Icc ρ 1) := by
    intro x hx y hy hxy
    rw [← hsym x hx, ← hsym y hy]
    exact vs_effDist_monotoneOn θ j hx.2 hy.2 hxy
  unfold srivOf
  have h1 := surplus_SPA_eq M ρ hρ0 hρ1 (effDist M θ j) (vs_effDist_monotoneOn θ j)
    (fun x hx => effDist_nonneg θ j hx) hv0 hv1
  -- Direct integral comparison on 0..v
  unfold surplus
  apply intervalIntegral.integral_congr_ae
  have hne : ∀ᵐ t ∂volume, t ≠ ρ := by simp [ae_iff, measure_singleton]
  filter_upwards [hne] with t ht hmem
  rw [uIoc_of_le hv0] at hmem
  by_cases htρ : t < ρ
  · rw [alloc_SPA, alloc_SPA, ite_eq_left_iff.mpr (fun h => absurd htρ h),
      ite_eq_left_iff.mpr (fun h => absurd htρ h)]
  · push Not at htρ
    rw [alloc_SPA, alloc_SPA, ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr htρ)),
      ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr htρ)),
      hsym t ⟨htρ, hmem.2.trans hv1⟩]

lemma srivOf_eq_integral (m1 : HierarchicalMech) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    {θ : VisitStrategy M} (hSR : IsSR M (unilateralProfile M m1 ρ hρ0 hρ1) θ)
    {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    srivOf M ρ hρ0 hρ1 (effDist M θ 0) v =
      ∫ t in ρ..(max v ρ), (FrivOf M (effDist M θ 0) t) ^ (M.n - 1) := by
  rw [← prop2_rival_surplus_eq M m1 ρ hρ0 hρ1 hSR (rivalIdx_ne_zero M) hv0 hv1,
    surplus_SPA_eq M ρ hρ0 hρ1 _ (vs_effDist_monotoneOn θ _) (fun x hx => effDist_nonneg θ _ hx) hv0 hv1]
  apply intervalIntegral.integral_congr; intro t ht; dsimp only
  rw [uIcc_of_le (le_max_right v ρ)] at ht
  rw [(prop2_rival_symmetry M m1 ρ hρ0 hρ1 hSR).2 (rivalIdx M) (rivalIdx_ne_zero M) t
    ⟨ht.1, ht.2.trans (max_le hv1 hρ1)⟩]

lemma sigma_continuousOn (m1 : HierarchicalMech) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    {θ : VisitStrategy M} (hSR : IsSR M (unilateralProfile M m1 ρ hρ0 hρ1) θ) :
    ContinuousOn (sigma M m1 ρ hρ0 hρ1 θ) (Icc 0 1) := by
  have h1 : ContinuousOn (surplus M m1 (effDist M θ 0)) (Icc 0 1) :=
    (surplus_continuousOn M m1 _ (vs_effDist_monotoneOn θ 0)
      (fun x hx => effDist_nonneg θ 0 hx) (fun x hx => effDist_le_one θ 0 hx)).mono Icc_subset_Iic_self
  have h2 : ContinuousOn (surplus M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M))) (Icc 0 1) :=
    (surplus_continuousOn M (SPA ρ hρ0 hρ1) _ (vs_effDist_monotoneOn θ _)
      (fun x hx => effDist_nonneg θ _ hx) (fun x hx => effDist_le_one θ _ hx)).mono Icc_subset_Iic_self
  have heq : EqOn (sigma M m1 ρ hρ0 hρ1 θ)
      (fun v => surplus M m1 (effDist M θ 0) v -
        surplus M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) v) (Icc 0 1) := by
    intro v hv; dsimp only [sigma]
    rw [prop2_rival_surplus_eq M m1 ρ hρ0 hρ1 hSR (rivalIdx_ne_zero M) hv.1 hv.2]
  exact (h1.sub h2).congr heq

lemma sigma_zero_at_rmin (m1 : HierarchicalMech) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    {θ : VisitStrategy M} (hSR : IsSR M (unilateralProfile M m1 ρ hρ0 hρ1) θ) :
    sigma M m1 ρ hρ0 hρ1 θ (min m1.r ρ) = 0 := by
  have hmin0 : 0 ≤ min m1.r ρ := le_min m1.hr0 hρ0
  have hmin1 : min m1.r ρ ≤ 1 := min_le_of_left_le m1.hr1
  unfold sigma
  rw [← prop2_rival_surplus_eq M m1 ρ hρ0 hρ1 hSR (rivalIdx_ne_zero M) hmin0 hmin1,
    surplus_zero_of_le_r M m1 _ hmin0 (min_le_left _ _),
    surplus_zero_of_le_r M (SPA ρ hρ0 hρ1) _ hmin0 (min_le_right _ _), sub_self]

lemma sigma_sub (m1 : HierarchicalMech) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    {θ : VisitStrategy M} (hSR : IsSR M (unilateralProfile M m1 ρ hρ0 hρ1) θ)
    {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    sigma M m1 ρ hρ0 hρ1 θ v - sigma M m1 ρ hρ0 hρ1 θ u =
      ∫ t in u..v, (alloc M m1 (effDist M θ 0) t -
        alloc M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) t) := by
  unfold sigma
  rw [← prop2_rival_surplus_eq M m1 ρ hρ0 hρ1 hSR (rivalIdx_ne_zero M) hv0 hv1,
      ← prop2_rival_surplus_eq M m1 ρ hρ0 hρ1 hSR (rivalIdx_ne_zero M) hu0 hu1]
  have h1 := surplus_sub M m1 (effDist M θ 0) (vs_effDist_monotoneOn θ 0)
    (fun x hx => effDist_nonneg θ 0 hx) hu1 hv1
  have h2 := surplus_sub M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M))
    (vs_effDist_monotoneOn θ _) (fun x hx => effDist_nonneg θ _ hx) hu1 hv1
  have hi1 := alloc_intervalIntegrable M m1 (effDist M θ 0) (vs_effDist_monotoneOn θ 0)
    (fun x hx => effDist_nonneg θ 0 hx) hu1 hv1
  have hi2 := alloc_intervalIntegrable M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M))
    (vs_effDist_monotoneOn θ _) (fun x hx => effDist_nonneg θ _ hx) hu1 hv1
  rw [intervalIntegral.integral_sub hi1 hi2]
  linarith

/-- Below `ρ` (when `r₁ < ρ`), seller 1 has strictly positive surplus on `(max r₁ a, ρ)` and
captures all buyers there a.e. -/
lemma prop2_below_rho_seller1_captures (m1 : HierarchicalMech) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    {θ : VisitStrategy M} (hSR : IsSR M (unilateralProfile M m1 ρ hρ0 hρ1) θ)
    (hrlt : m1.r < ρ) :
    (∀ v ∈ Ioo (max m1.r M.a) ρ, 0 < sigma M m1 ρ hρ0 hρ1 θ v) ∧
    (∀ u ∈ Icc (min m1.r ρ) ρ, ∀ v ∈ Icc (min m1.r ρ) ρ,
      effDist M θ 0 v - effDist M θ 0 u = M.F v - M.F u) := by
  have hpos_alloc : ∀ t ∈ Ioo (max m1.r M.a) ρ, 0 < alloc M m1 (effDist M θ 0) t := by
    intro t ht
    have hta : M.a < t := lt_of_le_of_lt (le_max_right _ _) ht.1
    have htr : m1.r < t := lt_of_le_of_lt (le_max_left _ _) ht.1
    have ht1 : t ≤ 1 := ht.2.le.trans hρ1
    have hFt_pos : 0 < M.F t := by
      rw [← M.hF_a]; exact M.F_strictMonoOn (left_mem_Icc.mpr M.ha1.le) ⟨hta.le, ht1⟩ hta
    have hF1_pos : 0 < effDist M θ 0 t := lt_of_lt_of_le hFt_pos (vs_effDist_mem_Icc θ 0 ht1).1
    by_cases hpool : ∃ I ∈ m1.pools, I.α < t ∧ t < I.β
    · obtain ⟨I, hI, h1, h2⟩ := hpool
      rw [alloc_in_pool M m1 _ hI ⟨h1, h2⟩]
      have hIβ1 : I.β ≤ 1 := (m1.hpools_in I hI).2
      have hFβ_pos : 0 < effDist M θ 0 I.β :=
        lt_of_lt_of_le hF1_pos (vs_effDist_monotoneOn θ 0 ht1 hIβ1 h2.le)
      have hFα_nn : 0 ≤ effDist M θ 0 I.α := effDist_nonneg θ 0 (I.hαβ.le.trans hIβ1)
      have hpa := poolAvg_strictMono_right M.hn hFα_nn le_rfl hFβ_pos
      have hpa0 : 0 ≤ poolAvg M.n (effDist M θ 0 I.α) 0 := poolAvg_nonneg M.hn hFα_nn le_rfl
      linarith
    · push Not at hpool
      rw [alloc_off_pools M m1 _ htr.le (fun I hI h => not_le.mpr h.2 (hpool I hI h.1))]
      exact pow_pos hF1_pos _
  have hsigma_pos : ∀ v ∈ Ioo (max m1.r M.a) ρ, 0 < sigma M m1 ρ hρ0 hρ1 θ v := by
    intro v hv
    have hv0 : 0 ≤ v := le_trans (le_max_of_le_right M.ha0) hv.1.le
    have hv1 : v ≤ 1 := hv.2.le.trans hρ1
    unfold sigma
    rw [← prop2_rival_surplus_eq M m1 ρ hρ0 hρ1 hSR (rivalIdx_ne_zero M) hv0 hv1,
      surplus_zero_of_le_r M (SPA ρ hρ0 hρ1) _ hv0 hv.2.le, sub_zero]
    set m0 := (max m1.r M.a + v) / 2
    have hm0_gt : max m1.r M.a < m0 := by dsimp only [m0]; linarith [hv.1]
    have hm0_lt : m0 < v := by dsimp only [m0]; linarith [hv.1]
    have hm0_pos : 0 < alloc M m1 (effDist M θ 0) m0 :=
      hpos_alloc m0 ⟨hm0_gt, hm0_lt.trans hv.2⟩
    have hm0_0 : 0 ≤ m0 := le_trans (le_max_of_le_right M.ha0) hm0_gt.le
    have hsplit : surplus M m1 (effDist M θ 0) v =
        surplus M m1 (effDist M θ 0) m0 + ∫ t in m0..v, alloc M m1 (effDist M θ 0) t := by
      have := surplus_sub M m1 (effDist M θ 0) (vs_effDist_monotoneOn θ 0)
        (fun x hx => effDist_nonneg θ 0 hx) (hm0_lt.le.trans hv1) hv1
      linarith
    have hs_m0_nn : 0 ≤ surplus M m1 (effDist M θ 0) m0 := by
      unfold surplus
      exact intervalIntegral.integral_nonneg hm0_0 fun t ht =>
        alloc_nonneg M m1 _ (fun x hx => effDist_nonneg θ 0 hx) (ht.2.trans (hm0_lt.le.trans hv1))
    have hint_ge : (v - m0) * alloc M m1 (effDist M θ 0) m0 ≤
        ∫ t in m0..v, alloc M m1 (effDist M θ 0) t := by
      have hmono := vs_alloc_monotoneOn M m1 (effDist M θ 0) (vs_effDist_monotoneOn θ 0)
        (fun x hx => effDist_nonneg θ 0 hx)
      have := intervalIntegral.integral_mono_on hm0_lt.le intervalIntegrable_const
        (alloc_intervalIntegrable M m1 _ (vs_effDist_monotoneOn θ 0)
          (fun x hx => effDist_nonneg θ 0 hx) (hm0_lt.le.trans hv1) hv1)
        (fun t ht => hmono (hm0_lt.le.trans hv1) (ht.2.trans hv1) ht.1)
      simpa [intervalIntegral.integral_const, smul_eq_mul] using this
    have hprod_pos : 0 < (v - m0) * alloc M m1 (effDist M θ 0) m0 :=
      mul_pos (sub_pos.mpr hm0_lt) hm0_pos
    linarith
  refine ⟨hsigma_pos, ?_⟩
  -- Now show θ_0 = 1 a.e. on (max m1.r a, ρ) and hence effDist diff = F diff on [r_min, ρ]
  have hae_one : ∀ᵐ t ∂(volume.restrict (Ioo (max m1.r M.a) ρ)), θ.θ 0 t = 1 := by
    have hsub : Ioo (max m1.r M.a) ρ ⊆ Icc M.a 1 := fun t ht =>
      ⟨le_trans (le_max_right _ _) ht.1.le, ht.2.le.trans hρ1⟩
    have hSR' := MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono hsub le_rfl) hSR
    filter_upwards [hSR', MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht hmem
    have hsig := hsigma_pos t hmem
    have hmemIcc : t ∈ Icc M.a 1 := hsub hmem
    have hsum := θ.hsum t hmemIcc
    have h0mem : (0 : Fin M.m) ∈ (Finset.univ : Finset (Fin M.m)) := Finset.mem_univ _
    rw [← Finset.add_sum_erase _ _ h0mem] at hsum
    have hriv0 : ∀ j ∈ Finset.univ.erase (0 : Fin M.m), θ.θ j t = 0 := by
      intro j hj
      have hjne : j ≠ 0 := Finset.ne_of_mem_erase hj
      by_contra hne0
      have hjpos : 0 < θ.θ j t := lt_of_le_of_ne (θ.hnonneg j t) (Ne.symm hne0)
      have hle := ht j 0 hjpos
      simp only [unilateralProfile, ite_true, ite_eq_right_iff.mpr (fun h => absurd h hjne)] at hle
      rw [prop2_rival_surplus_eq M m1 ρ hρ0 hρ1 hSR hjne (M.ha0.trans hmemIcc.1) hmemIcc.2] at hle
      unfold sigma at hsig; linarith
    rw [Finset.sum_eq_zero hriv0, add_zero] at hsum
    exact hsum
  intro u hu v hv
  have hu1 : u ≤ 1 := hu.2.trans hρ1
  have hv1 : v ≤ 1 := hv.2.trans hρ1
  rw [effDist_sub θ 0 hu1 hv1, ← M.integral_f hu1 hv1]
  suffices h : ∀ x y : ℝ, m1.r ≤ x → x ≤ y → y ≤ ρ →
      ∫ t in x..y, θ.θ 0 t * M.f t = ∫ t in x..y, M.f t by
    have hmin_eq : min m1.r ρ = m1.r := min_eq_left hrlt.le
    rw [hmin_eq] at hu hv
    rcases le_total u v with hle | hle
    · exact h u v hu.1 hle hv.2
    · rw [intervalIntegral.integral_symm (f := fun t => θ.θ 0 t * M.f t) v u,
          intervalIntegral.integral_symm (f := M.f) v u, h v u hv.1 hle hu.2]
  intro x y hxr hxy hyρ
  rw [intervalIntegral.integral_of_le hxy, intervalIntegral.integral_of_le hxy]
  apply MeasureTheory.setIntegral_congr_ae measurableSet_Ioc
  have hae_univ : ∀ᵐ t ∂volume, t ∈ Ioo (max m1.r M.a) ρ → θ.θ 0 t = 1 :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mp hae_one
  have hne_a : ∀ᵐ t ∂volume, t ≠ M.a := by simp [ae_iff, measure_singleton]
  have hne_ρ : ∀ᵐ t ∂volume, t ≠ ρ := by simp [ae_iff, measure_singleton]
  filter_upwards [hae_univ, hne_a, hne_ρ] with t ht hta htρ hmem
  by_cases hlt_a : t < M.a
  · rw [M.hf_below t hlt_a, mul_zero]
  · push Not at hlt_a
    have hgt_a : M.a < t := lt_of_le_of_ne hlt_a (Ne.symm hta)
    have hgt_r : m1.r < t := lt_of_le_of_lt hxr hmem.1
    have hlt_ρ : t < ρ := lt_of_le_of_ne (hmem.2.trans hyρ) htρ
    rw [ht ⟨max_lt hgt_r hgt_a, hlt_ρ⟩, one_mul]

/-! #### 1D Sign Propagation for Proposition 2(ii) (Uniqueness) -/

section SignPropagation

variable (m1 : HierarchicalMech) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
variable {θ θ' : VisitStrategy M}
variable (hSR : IsSR M (unilateralProfile M m1 ρ hρ0 hρ1) θ)
variable (hSR' : IsSR M (unilateralProfile M m1 ρ hρ0 hρ1) θ')

include m1 ρ hρ0 hρ1 hSR hSR'

/-- Property (a): `ΔF` is constant on `[min r₁ ρ, ρ]`. -/
private lemma prop2_prop_a {u v : ℝ}
    (hu : u ∈ Icc (min m1.r ρ) ρ) (hv : v ∈ Icc (min m1.r ρ) ρ) :
    (effDist M θ' 0 v - effDist M θ 0 v) = (effDist M θ' 0 u - effDist M θ 0 u) := by
  by_cases hrlt : m1.r < ρ
  · have h1 := (prop2_below_rho_seller1_captures M m1 ρ hρ0 hρ1 hSR hrlt).2 u hu v hv
    have h2 := (prop2_below_rho_seller1_captures M m1 ρ hρ0 hρ1 hSR' hrlt).2 u hu v hv
    linarith
  · push Not at hrlt
    have hmin : min m1.r ρ = ρ := min_eq_right hrlt
    rw [hmin] at hu hv
    have huρ : u = ρ := le_antisymm hu.2 hu.1
    have hvρ : v = ρ := le_antisymm hv.2 hv.1
    rw [huρ, hvρ]

/-- Property (b): `Δσ > 0` on `(x, y)` implies `ΔF` is nondecreasing on `[x, y]`. -/
private lemma prop2_prop_b_pos {x y : ℝ} (hxy : x ≤ y) (hy1 : y ≤ 1)
    (hpos : ∀ t ∈ Ioo x y,
      0 < sigma M m1 ρ hρ0 hρ1 θ' t - sigma M m1 ρ hρ0 hρ1 θ t) :
    effDist M θ' 0 x - effDist M θ 0 x ≤ effDist M θ' 0 y - effDist M θ 0 y := by
  have hx1 : x ≤ 1 := hxy.trans hy1
  have hsub : (effDist M θ' 0 y - effDist M θ 0 y) - (effDist M θ' 0 x - effDist M θ 0 x) =
      ∫ t in x..y, (θ'.θ 0 t - θ.θ 0 t) * M.f t := by
    have h1 := effDist_sub θ' 0 hx1 hy1
    have h2 := effDist_sub θ 0 hx1 hy1
    have hfun : (fun t => (θ'.θ 0 t - θ.θ 0 t) * M.f t) =
        (fun t => θ'.θ 0 t * M.f t - θ.θ 0 t * M.f t) := by ext t; ring
    rw [hfun, intervalIntegral.integral_sub (θ'.mul_f_intervalIntegrable 0 hx1 hy1)
      (θ.mul_f_intervalIntegrable 0 hx1 hy1)]
    linarith
  suffices hnn : 0 ≤ ∫ t in x..y, (θ'.θ 0 t - θ.θ 0 t) * M.f t by linarith
  rw [intervalIntegral.integral_of_le hxy]
  apply MeasureTheory.integral_nonneg_of_ae
  have hSR_ae : ∀ᵐ t ∂volume, t ∈ Icc M.a 1 →
      ∀ j k : Fin M.m, 0 < θ.θ j t →
        surplus M (unilateralProfile M m1 ρ hρ0 hρ1 k) (effDist M θ k) t ≤
        surplus M (unilateralProfile M m1 ρ hρ0 hρ1 j) (effDist M θ j) t :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mp hSR
  have hSR'_ae : ∀ᵐ t ∂volume, t ∈ Icc M.a 1 →
      ∀ j k : Fin M.m, 0 < θ'.θ j t →
        surplus M (unilateralProfile M m1 ρ hρ0 hρ1 k) (effDist M θ' k) t ≤
        surplus M (unilateralProfile M m1 ρ hρ0 hρ1 j) (effDist M θ' j) t :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mp hSR'
  have hne_y : ∀ᵐ t ∂volume, t ≠ y := by simp [ae_iff, measure_singleton]
  change ∀ᵐ t ∂(volume.restrict (Ioc x y)), (0 : ℝ) ≤ (θ'.θ 0 t - θ.θ 0 t) * M.f t
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [hSR_ae, hSR'_ae, hne_y] with t hSRt hSR't hty hmem
  by_cases hta : t < M.a
  · rw [M.hf_below t hta, mul_zero]
  · push Not at hta
    have ht1 : t ≤ 1 := hmem.2.trans hy1
    have hmemIcc : t ∈ Icc M.a 1 := ⟨hta, ht1⟩
    have hopen : t ∈ Ioo x y := ⟨hmem.1, lt_of_le_of_ne hmem.2 hty⟩
    have hsig_pos := hpos t hopen
    have hle : θ.θ 0 t ≤ θ'.θ 0 t := by
      by_contra hlt; push Not at hlt
      have hθ0_pos : 0 < θ.θ 0 t := lt_of_le_of_lt (θ'.hnonneg 0 t) hlt
      have hθ'0_lt1 : θ'.θ 0 t < 1 := lt_of_lt_of_le hlt (θ.le_one 0 hmemIcc)
      -- From θ.θ 0 t > 0: σ t ≥ 0
      have hσ_nn : 0 ≤ sigma M m1 ρ hρ0 hρ1 θ t := by
        have h1 := hSRt hmemIcc 0 (rivalIdx M) hθ0_pos
        simp only [unilateralProfile, ite_true,
          ite_eq_right_iff.mpr (fun h => absurd h (rivalIdx_ne_zero M))] at h1
        rw [prop2_rival_surplus_eq M m1 ρ hρ0 hρ1 hSR (rivalIdx_ne_zero M)
          (M.ha0.trans hta) ht1] at h1
        unfold sigma; linarith
      -- From θ'.θ 0 t < 1: ∃ rival j ≠ 0 with θ'.θ j t > 0, so σ' t ≤ 0
      have hex_riv : ∃ j : Fin M.m, j ≠ 0 ∧ 0 < θ'.θ j t := by
        by_contra hnone; push Not at hnone
        have hsum := θ'.hsum t hmemIcc
        have h0mem : (0 : Fin M.m) ∈ (Finset.univ : Finset (Fin M.m)) := Finset.mem_univ _
        rw [← Finset.add_sum_erase _ _ h0mem] at hsum
        have hzero : ∑ j ∈ Finset.univ.erase (0 : Fin M.m), θ'.θ j t = 0 :=
          Finset.sum_eq_zero fun j hj =>
            le_antisymm (hnone j (Finset.ne_of_mem_erase hj)) (θ'.hnonneg j t)
        rw [hzero, add_zero] at hsum; linarith
      obtain ⟨j, hj, hjpos⟩ := hex_riv
      have hσ'_np : sigma M m1 ρ hρ0 hρ1 θ' t ≤ 0 := by
        have h1 := hSR't hmemIcc j 0 hjpos
        simp only [unilateralProfile, ite_true,
          ite_eq_right_iff.mpr (fun h => absurd h hj)] at h1
        rw [prop2_rival_surplus_eq M m1 ρ hρ0 hρ1 hSR' hj (M.ha0.trans hta) ht1] at h1
        unfold sigma; linarith
      linarith
    exact mul_nonneg (sub_nonneg.mpr hle) (M.f_nonneg_Iic ht1)

/-- Property (b), mirror image: `Δσ < 0` on `(x, y)` implies `ΔF` is nonincreasing on `[x, y]`. -/
private lemma prop2_prop_b_neg {x y : ℝ} (hxy : x ≤ y) (hy1 : y ≤ 1)
    (hneg : ∀ t ∈ Ioo x y,
      sigma M m1 ρ hρ0 hρ1 θ' t - sigma M m1 ρ hρ0 hρ1 θ t < 0) :
    effDist M θ' 0 y - effDist M θ 0 y ≤ effDist M θ' 0 x - effDist M θ 0 x := by
  have := prop2_prop_b_pos M m1 ρ hρ0 hρ1 hSR' hSR hxy hy1 (fun t ht => by linarith [hneg t ht])
  linarith

/-- Rival allocation difference `φ(t) = x_riv(t) - x'_riv(t)` satisfies sign & Lipschitz properties (d). -/
private lemma prop2_phi_props {t : ℝ} (ht1 : t ≤ 1) :
    let φ := alloc M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) t -
      alloc M (SPA ρ hρ0 hρ1) (effDist M θ' (rivalIdx M)) t
    let dF := effDist M θ' 0 t - effDist M θ 0 t
    (t < ρ → φ = 0) ∧
    (ρ ≤ t → (0 < dF → 0 < φ) ∧ (0 ≤ dF → 0 ≤ φ) ∧ (dF ≤ 0 → φ ≤ 0) ∧ (dF < 0 → φ < 0)) ∧
    |φ| ≤ (((M.n : ℝ) - 1) / ((M.m : ℝ) - 1)) * |dF| := by
  intro φ dF
  have hbelow : t < ρ → φ = 0 := fun htρ => by
    simp only [φ, alloc_SPA, ite_eq_left_iff.mpr (fun h => absurd htρ h), sub_self]
  have habove : ρ ≤ t →
      effDist M θ (rivalIdx M) t - effDist M θ' (rivalIdx M) t = dF / ((M.m : ℝ) - 1) := by
    intro hρt
    rw [(prop2_rival_symmetry M m1 ρ hρ0 hρ1 hSR).2 (rivalIdx M) (rivalIdx_ne_zero M) t ⟨hρt, ht1⟩,
        (prop2_rival_symmetry M m1 ρ hρ0 hρ1 hSR').2 (rivalIdx M) (rivalIdx_ne_zero M) t ⟨hρt, ht1⟩]
    unfold FrivOf; simp only [dF]; ring
  have hn1 : M.n - 1 ≠ 0 := by have := M.hn; omega
  refine ⟨hbelow, fun hρt => ?_, ?_⟩
  · have hφeq : φ = (effDist M θ (rivalIdx M) t) ^ (M.n - 1) -
        (effDist M θ' (rivalIdx M) t) ^ (M.n - 1) := by
      simp only [φ, alloc_SPA, ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr hρt))]
    have hdiff := habove hρt
    have hm1 := M.m_sub_one_pos_real
    have hnn1 := effDist_nonneg θ (rivalIdx M) ht1
    have hnn2 := effDist_nonneg θ' (rivalIdx M) ht1
    rw [hφeq]
    refine ⟨fun hd => ?_, fun hd => ?_, fun hd => ?_, fun hd => ?_⟩
    · have hgt : effDist M θ' (rivalIdx M) t < effDist M θ (rivalIdx M) t := by
        have := div_pos hd hm1; linarith
      exact sub_pos.mpr (pow_lt_pow_left₀ hgt hnn2 hn1)
    · have hge : effDist M θ' (rivalIdx M) t ≤ effDist M θ (rivalIdx M) t := by
        have := div_nonneg hd hm1.le; linarith
      exact sub_nonneg.mpr (pow_le_pow_left₀ hnn2 hge _)
    · have hle : effDist M θ (rivalIdx M) t ≤ effDist M θ' (rivalIdx M) t := by
        have := div_nonpos_of_nonpos_of_nonneg hd hm1.le; linarith
      exact sub_nonpos.mpr (pow_le_pow_left₀ hnn1 hle _)
    · have hlt : effDist M θ (rivalIdx M) t < effDist M θ' (rivalIdx M) t := by
        have := div_neg_of_neg_of_pos hd hm1; linarith
      exact sub_neg.mpr (pow_lt_pow_left₀ hlt hnn1 hn1)
  · by_cases htρ : t < ρ
    · rw [hbelow htρ, abs_zero]
      exact mul_nonneg (div_nonneg M.n_sub_one_pos_real.le M.m_sub_one_pos_real.le) (abs_nonneg _)
    · push Not at htρ
      have hφeq : φ = (effDist M θ (rivalIdx M) t) ^ (M.n - 1) -
          (effDist M θ' (rivalIdx M) t) ^ (M.n - 1) := by
        simp only [φ, alloc_SPA, ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr htρ))]
      rw [hφeq]
      have hlip := pow_sub_one_lipschitz M.hn
        (effDist_nonneg θ (rivalIdx M) ht1) (effDist_le_one θ (rivalIdx M) ht1)
        (effDist_nonneg θ' (rivalIdx M) ht1) (effDist_le_one θ' (rivalIdx M) ht1)
      rw [habove htρ, abs_div, abs_of_pos M.m_sub_one_pos_real] at hlip
      linarith [show ((M.n : ℝ) - 1) * (|dF| / ((M.m : ℝ) - 1)) =
        (((M.n : ℝ) - 1) / ((M.m : ℝ) - 1)) * |dF| by ring]

/-- Property (c): On a gap `[u₁, u₂] ⊆ [min r₁ ρ, 1]` avoiding all pools, if `ΔF > 0` on `(u₁, u₂)`
then `Δσ(u₁) < Δσ(u₂)` (and if `ΔF = 0` on `(u₁, u₂)` then `Δσ(u₁) = Δσ(u₂)`). -/
private lemma prop2_prop_c_pos {u₁ u₂ : ℝ} (hmin : min m1.r ρ ≤ u₁) (hlt : u₁ < u₂) (hu2 : u₂ ≤ 1)
    (hgap : ∀ I ∈ m1.pools, ∀ t ∈ Ioo u₁ u₂, ¬ (I.α < t ∧ t < I.β))
    (hFpos : ∀ t ∈ Ioo u₁ u₂, 0 < effDist M θ' 0 t - effDist M θ 0 t) :
    sigma M m1 ρ hρ0 hρ1 θ' u₁ - sigma M m1 ρ hρ0 hρ1 θ u₁ <
    sigma M m1 ρ hρ0 hρ1 θ' u₂ - sigma M m1 ρ hρ0 hρ1 θ u₂ := by
  have hu1_0 : 0 ≤ u₁ := (le_min m1.hr0 hρ0).trans hmin
  have hu2_0 : 0 ≤ u₂ := hu1_0.trans hlt.le
  have hu1_1 : u₁ ≤ 1 := hlt.le.trans hu2
  have hdiff : (sigma M m1 ρ hρ0 hρ1 θ' u₂ - sigma M m1 ρ hρ0 hρ1 θ u₂) -
      (sigma M m1 ρ hρ0 hρ1 θ' u₁ - sigma M m1 ρ hρ0 hρ1 θ u₁) =
      ∫ t in u₁..u₂,
        ((alloc M m1 (effDist M θ' 0) t - alloc M m1 (effDist M θ 0) t) +
         (alloc M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) t -
          alloc M (SPA ρ hρ0 hρ1) (effDist M θ' (rivalIdx M)) t)) := by
    have h1 := sigma_sub M m1 ρ hρ0 hρ1 hSR' hu1_0 hu1_1 hu2_0 hu2
    have h2 := sigma_sub M m1 ρ hρ0 hρ1 hSR hu1_0 hu1_1 hu2_0 hu2
    have hi1 := (alloc_intervalIntegrable M m1 _ (vs_effDist_monotoneOn θ' 0)
      (fun x hx => effDist_nonneg θ' 0 hx) hu1_1 hu2).sub
      (alloc_intervalIntegrable M (SPA ρ hρ0 hρ1) _ (vs_effDist_monotoneOn θ' (rivalIdx M))
      (fun x hx => effDist_nonneg θ' (rivalIdx M) hx) hu1_1 hu2)
    have hi2 := (alloc_intervalIntegrable M m1 _ (vs_effDist_monotoneOn θ 0)
      (fun x hx => effDist_nonneg θ 0 hx) hu1_1 hu2).sub
      (alloc_intervalIntegrable M (SPA ρ hρ0 hρ1) _ (vs_effDist_monotoneOn θ (rivalIdx M))
      (fun x hx => effDist_nonneg θ (rivalIdx M) hx) hu1_1 hu2)
    have hsub := intervalIntegral.integral_sub hi1 hi2
    have hfun : (fun t =>
        (alloc M m1 (effDist M θ' 0) t - alloc M (SPA ρ hρ0 hρ1) (effDist M θ' (rivalIdx M)) t) -
        (alloc M m1 (effDist M θ 0) t - alloc M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) t)) =
      (fun t =>
        (alloc M m1 (effDist M θ' 0) t - alloc M m1 (effDist M θ 0) t) +
        (alloc M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) t -
         alloc M (SPA ρ hρ0 hρ1) (effDist M θ' (rivalIdx M)) t)) := by ext t; ring
    rw [hfun] at hsub
    linarith
  suffices hpos_int : 0 < ∫ t in u₁..u₂,
      ((alloc M m1 (effDist M θ' 0) t - alloc M m1 (effDist M θ 0) t) +
       (alloc M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) t -
        alloc M (SPA ρ hρ0 hρ1) (effDist M θ' (rivalIdx M)) t)) by linarith
  let ψ : ℝ → ℝ := fun t =>
    (alloc M m1 (effDist M θ' 0) t - alloc M m1 (effDist M θ 0) t) +
    (alloc M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) t -
     alloc M (SPA ρ hρ0 hρ1) (effDist M θ' (rivalIdx M)) t)
  have hψ_int : ∀ x y, u₁ ≤ x → x ≤ y → y ≤ u₂ → IntervalIntegrable ψ volume x y := by
    intro x y _ _ hy
    have hx1 : x ≤ 1 := by linarith
    have hy1 : y ≤ 1 := hy.trans hu2
    exact ((alloc_intervalIntegrable M m1 _ (vs_effDist_monotoneOn θ' 0)
      (fun z hz => effDist_nonneg θ' 0 hz) hx1 hy1).sub
      (alloc_intervalIntegrable M m1 _ (vs_effDist_monotoneOn θ 0)
      (fun z hz => effDist_nonneg θ 0 hz) hx1 hy1)).add
      ((alloc_intervalIntegrable M (SPA ρ hρ0 hρ1) _ (vs_effDist_monotoneOn θ _)
      (fun z hz => effDist_nonneg θ _ hz) hx1 hy1).sub
      (alloc_intervalIntegrable M (SPA ρ hρ0 hρ1) _ (vs_effDist_monotoneOn θ' _)
      (fun z hz => effDist_nonneg θ' _ hz) hx1 hy1))
  have hn1 : M.n - 1 ≠ 0 := by have := M.hn; omega
  have hψ_nn : ∀ t ∈ Ioo u₁ u₂, 0 < ψ t := by
    intro t ht
    have ht1 : t ≤ 1 := ht.2.le.trans hu2
    have hdF : 0 < effDist M θ' 0 t - effDist M θ 0 t := hFpos t ht
    have hφ := prop2_phi_props M m1 ρ hρ0 hρ1 hSR hSR' ht1
    have h1_nn : 0 ≤ alloc M m1 (effDist M θ' 0) t - alloc M m1 (effDist M θ 0) t := by
      by_cases htr : t < m1.r
      · rw [alloc_below_r M m1 _ htr, alloc_below_r M m1 _ htr, sub_self]
      · push Not at htr
        rw [alloc_off_pools M m1 _ htr (fun I hI => hgap I hI t ht),
            alloc_off_pools M m1 _ htr (fun I hI => hgap I hI t ht)]
        exact sub_nonneg.mpr (pow_le_pow_left₀ (effDist_nonneg θ 0 ht1) (by linarith) _)
    have h2_nn : 0 ≤ alloc M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) t -
        alloc M (SPA ρ hρ0 hρ1) (effDist M θ' (rivalIdx M)) t := by
      by_cases htρ : t < ρ
      · rw [hφ.1 htρ]
      · push Not at htρ; exact (hφ.2.1 htρ).2.1 hdF.le
    have htgt : min m1.r ρ < t := lt_of_le_of_lt hmin ht.1
    rcases lt_or_ge (min m1.r ρ) t with _ | _
    · rcases lt_or_ge m1.r t with htr | htr
      · have h1_pos : 0 < alloc M m1 (effDist M θ' 0) t - alloc M m1 (effDist M θ 0) t := by
          rw [alloc_off_pools M m1 _ htr.le (fun I hI => hgap I hI t ht),
              alloc_off_pools M m1 _ htr.le (fun I hI => hgap I hI t ht)]
          exact sub_pos.mpr (pow_lt_pow_left₀ (by linarith) (effDist_nonneg θ 0 ht1) hn1)
        linarith
      · have htρ : ρ < t := by
          rcases min_cases m1.r ρ with ⟨h, _⟩ | ⟨h, _⟩
          · linarith
          · linarith
        have h2_pos := (hφ.2.1 htρ.le).1 hdF
        linarith
    · exfalso; linarith
  -- Pick a closed subinterval [c, d] ⊆ Ioo u₁ u₂ avoiding max m1.r ρ so ψ is continuous on [c, d]
  have hex_sub : ∃ c d : ℝ, u₁ < c ∧ c < d ∧ d < u₂ ∧ max m1.r ρ ∉ Icc c d := by
    by_cases hm : max m1.r ρ ≤ (u₁ + u₂) / 2
    · refine ⟨((u₁ + u₂) / 2 + u₂) / 2, ((u₁ + u₂) / 2 + 3 * u₂) / 4, by linarith, by linarith, by linarith, ?_⟩
      intro hmem; linarith [hmem.1]
    · push Not at hm
      refine ⟨(3 * u₁ + (u₁ + u₂) / 2) / 4, (u₁ + (u₁ + u₂) / 2) / 2, by linarith, by linarith, by linarith, ?_⟩
      intro hmem; linarith [hmem.2]
  obtain ⟨c, d, huc, hcd, hdu, havoid⟩ := hex_sub
  -- On [c, d], ψ is continuous and strictly positive
  have hψ_cont_cd : ContinuousOn ψ (Icc c d) := by
    have hsub_oo : Icc c d ⊆ Ioo u₁ u₂ := fun t ht => ⟨lt_of_lt_of_le huc ht.1, lt_of_le_of_lt ht.2 hdu⟩
    have hconst_r : (∀ t ∈ Icc c d, t < m1.r) ∨ (∀ t ∈ Icc c d, m1.r ≤ t) := by
      by_cases h1 : d < m1.r
      · exact Or.inl fun t ht => lt_of_le_of_lt ht.2 h1
      · push Not at h1
        right; intro t ht
        by_contra hlt; push Not at hlt
        have hlt_max : c < max m1.r ρ := lt_of_le_of_lt ht.1 (lt_of_lt_of_le hlt (le_max_left _ _))
        -- Wait: max m1.r ρ ≥ m1.r > t ≥ c, while either m1.r ≤ d (so m1.r ∈ [c, d]) or...
        -- Actually if m1.r ≤ d and c < m1.r: could ρ > d? Then max m1.r ρ = ρ > d, so m1.r < ρ!
        -- Wait: if m1.r < ρ, then min m1.r ρ = m1.r ≤ u₁ < c ≤ t, contradicting t < m1.r!
        have hmin_lt : min m1.r ρ < t := lt_of_le_of_lt hmin (hsub_oo ht).1
        rcases le_total m1.r ρ with hle | hle
        · rw [min_eq_left hle] at hmin_lt; linarith
        · rw [max_eq_left hle] at havoid
          exact havoid ⟨hlt.le.trans' ht.1, h1⟩
    have hconst_ρ : (∀ t ∈ Icc c d, t < ρ) ∨ (∀ t ∈ Icc c d, ρ ≤ t) := by
      by_cases h1 : d < ρ
      · exact Or.inl fun t ht => lt_of_le_of_lt ht.2 h1
      · push Not at h1
        right; intro t ht
        by_contra hlt; push Not at hlt
        have hmin_lt : min m1.r ρ < t := lt_of_le_of_lt hmin (hsub_oo ht).1
        rcases le_total ρ m1.r with hle | hle
        · rw [min_eq_right hle] at hmin_lt; linarith
        · rw [max_eq_right hle] at havoid
          exact havoid ⟨ht.1.trans hlt.le, h1⟩
    have hcont1 : ContinuousOn (fun t => alloc M m1 (effDist M θ' 0) t - alloc M m1 (effDist M θ 0) t) (Icc c d) := by
      rcases hconst_r with hlt_r | hge_r
      · exact continuousOn_const.congr fun t ht => by
          rw [alloc_below_r M m1 _ (hlt_r t ht), alloc_below_r M m1 _ (hlt_r t ht), sub_self]
      · exact ((((effDist_continuousOn θ' 0).mono (fun t (ht : t ∈ Icc c d) => ht.2.trans (hdu.le.trans hu2))).pow (M.n - 1)).sub
          (((effDist_continuousOn θ 0).mono (fun t (ht : t ∈ Icc c d) => ht.2.trans (hdu.le.trans hu2))).pow (M.n - 1))).congr
          fun t ht => by
            dsimp only [Pi.sub_apply, Pi.pow_apply]
            rw [alloc_off_pools M m1 _ (hge_r t ht) (fun I hI => hgap I hI t (hsub_oo ht)),
                alloc_off_pools M m1 _ (hge_r t ht) (fun I hI => hgap I hI t (hsub_oo ht))]
    have hcont2 : ContinuousOn (fun t =>
        alloc M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) t -
        alloc M (SPA ρ hρ0 hρ1) (effDist M θ' (rivalIdx M)) t) (Icc c d) := by
      rcases hconst_ρ with hlt_ρ | hge_ρ
      · exact continuousOn_const.congr fun t ht => by
          rw [alloc_SPA, alloc_SPA, ite_eq_left_iff.mpr (fun h => absurd (hlt_ρ t ht) h),
            ite_eq_left_iff.mpr (fun h => absurd (hlt_ρ t ht) h), sub_self]
      · exact ((((effDist_continuousOn θ (rivalIdx M)).mono (fun t (ht : t ∈ Icc c d) => ht.2.trans (hdu.le.trans hu2))).pow (M.n - 1)).sub
          (((effDist_continuousOn θ' (rivalIdx M)).mono (fun t (ht : t ∈ Icc c d) => ht.2.trans (hdu.le.trans hu2))).pow (M.n - 1))).congr
          fun t ht => by
            dsimp only [Pi.sub_apply, Pi.pow_apply]
            rw [alloc_SPA, alloc_SPA, ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr (hge_ρ t ht))),
              ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr (hge_ρ t ht)))]
    exact hcont1.add hcont2
  have hcd_pos : 0 < ∫ t in c..d, ψ t :=
    intervalIntegral.integral_pos hcd hψ_cont_cd
      (fun t ht => (hψ_nn t ⟨lt_of_lt_of_le huc ht.1.le, lt_of_le_of_lt ht.2 hdu⟩).le)
      ⟨(c + d) / 2, ⟨by linarith, by linarith⟩, hψ_nn _ ⟨by linarith, by linarith⟩⟩
  have h1_nn : 0 ≤ ∫ t in u₁..c, ψ t := by
    rw [intervalIntegral.integral_of_le huc.le]
    apply MeasureTheory.integral_nonneg_of_ae
    change ∀ᵐ t ∂(volume.restrict (Ioc u₁ c)), (0 : ℝ) ≤ ψ t
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with t ht
    exact (hψ_nn t ⟨ht.1, lt_of_le_of_lt ht.2 (hcd.trans hdu)⟩).le
  have h3_nn : 0 ≤ ∫ t in d..u₂, ψ t := by
    rw [intervalIntegral.integral_of_le hdu.le]
    apply MeasureTheory.integral_nonneg_of_ae
    have hne_u2 : ∀ᵐ t ∂volume, t ≠ u₂ := by simp [ae_iff, measure_singleton]
    change ∀ᵐ t ∂(volume.restrict (Ioc d u₂)), (0 : ℝ) ≤ ψ t
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hne_u2] with t htu2 ht
    exact (hψ_nn t ⟨huc.trans (hcd.trans ht.1), lt_of_le_of_ne ht.2 htu2⟩).le
  have hsp1 := intervalIntegral.integral_add_adjacent_intervals
    (hψ_int u₁ c le_rfl huc.le (hcd.le.trans hdu.le))
    (hψ_int c u₂ huc.le (hcd.le.trans hdu.le) le_rfl)
  have hsp2 := intervalIntegral.integral_add_adjacent_intervals
    (hψ_int c d huc.le hcd.le hdu.le)
    (hψ_int d u₂ (huc.le.trans hcd.le) hdu.le le_rfl)
  change 0 < ∫ t in u₁..u₂, ψ t
  linarith

/-- Step 1 (gaps preserve sign): if `[u₁, u₂]` meets no pool and `(ΔF, Δσ)` is positive at `u₁`,
then it remains positive at `u₂` (strictly positive if `u₁ < u₂`). -/
private lemma prop2_step1_gap_pos {u₁ u₂ : ℝ} (hmin : min m1.r ρ ≤ u₁) (hle : u₁ ≤ u₂) (hu2 : u₂ ≤ 1)
    (hgap : ∀ I ∈ m1.pools, ∀ t ∈ Ioo u₁ u₂, ¬ (I.α < t ∧ t < I.β))
    (hF1 : 0 < effDist M θ' 0 u₁ - effDist M θ 0 u₁)
    (hσ1 : 0 ≤ sigma M m1 ρ hρ0 hρ1 θ' u₁ - sigma M m1 ρ hρ0 hρ1 θ u₁) :
    0 < effDist M θ' 0 u₂ - effDist M θ 0 u₂ ∧
    (u₁ < u₂ → 0 < sigma M m1 ρ hρ0 hρ1 θ' u₂ - sigma M m1 ρ hρ0 hρ1 θ u₂) ∧
    0 ≤ sigma M m1 ρ hρ0 hρ1 θ' u₂ - sigma M m1 ρ hρ0 hρ1 θ u₂ := by
  let dF : ℝ → ℝ := fun v => effDist M θ' 0 v - effDist M θ 0 v
  let dσ : ℝ → ℝ := fun v => sigma M m1 ρ hρ0 hρ1 θ' v - sigma M m1 ρ hρ0 hρ1 θ v
  rcases eq_or_lt_of_le hle with rfl | hlt
  · exact ⟨hF1, fun h => absurd h (lt_irrefl _), hσ1⟩
  let S : Set ℝ := {v ∈ Icc u₁ u₂ | ∀ x ∈ Icc u₁ v, 0 < dF x}
  have hS_ne : S.Nonempty := ⟨u₁, left_mem_Icc.mpr hlt.le, fun x hx => by
    have : x = u₁ := le_antisymm hx.2 hx.1; rw [this]; exact hF1⟩
  have hS_bdd : BddAbove S := ⟨u₂, fun v hv => hv.1.2⟩
  let c := sSup S
  have hc_ge : u₁ ≤ c := le_csSup hS_bdd ⟨left_mem_Icc.mpr hlt.le, fun x hx => by
    have : x = u₁ := le_antisymm hx.2 hx.1; rw [this]; exact hF1⟩
  have hc_le : c ≤ u₂ := csSup_le hS_ne (fun v hv => hv.1.2)
  have hdF_pos_lt : ∀ x ∈ Ico u₁ c, 0 < dF x := by
    intro x hx
    obtain ⟨v, hvS, hxv⟩ := exists_lt_of_lt_csSup hS_ne hx.2
    exact hvS.2 x ⟨hx.1, hxv.le⟩
  have hdσ_pos_c : ∀ x ∈ Ioo u₁ c, 0 < dσ x := by
    intro x hx
    have hlt_σ := prop2_prop_c_pos M m1 ρ hρ0 hρ1 hSR hSR' hmin hx.1 (hx.2.le.trans (hc_le.trans hu2))
      (fun I hI t ht => hgap I hI t ⟨ht.1, ht.2.trans (hx.2.trans_le hc_le)⟩)
      (fun t ht => hdF_pos_lt t ⟨ht.1.le, ht.2.trans hx.2⟩)
    linarith
  have hdF_c : dF u₁ ≤ dF c := by
    rcases eq_or_lt_of_le hc_ge with heq | huc
    · rw [← heq]
    · exact prop2_prop_b_pos M m1 ρ hρ0 hρ1 hSR hSR' huc.le (hc_le.trans hu2) hdσ_pos_c
  have hc_eq : c = u₂ := by
    by_contra hne
    have hclt : c < u₂ := lt_of_le_of_ne hc_le hne
    have hcont : ContinuousOn dF (Icc u₁ u₂) :=
      ((effDist_continuousOn θ' 0).mono (fun t (ht : t ∈ Icc u₁ u₂) => ht.2.trans hu2)).sub
        ((effDist_continuousOn θ 0).mono (fun t (ht : t ∈ Icc u₁ u₂) => ht.2.trans hu2))
    have hc_pos : 0 < dF c := lt_of_lt_of_le hF1 hdF_c
    obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousWithinAt_iff.mp (hcont c ⟨hc_ge, hc_le⟩) (dF c / 2) (half_pos hc_pos)
    let c' := min u₂ (c + δ / 2)
    have hc'_gt : c < c' := lt_min hclt (by linarith)
    have hc'_mem : c' ∈ S := by
      refine ⟨⟨hc_ge.trans hc'_gt.le, min_le_left _ _⟩, fun x hx => ?_⟩
      by_cases hxc : x < c
      · exact hdF_pos_lt x ⟨hx.1, hxc⟩
      · push Not at hxc
        have hdist : dist x c < δ := by
          rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hxc)]
          have : x ≤ c + δ / 2 := hx.2.trans (min_le_right _ _)
          linarith
        have h1 := hδ ⟨hx.1, hx.2.trans (min_le_left _ _)⟩ hdist
        rw [Real.dist_eq] at h1
        linarith [(abs_lt.mp h1).1]
    exact not_lt.mpr (le_csSup hS_bdd hc'_mem) hc'_gt
  have hdσ_u2 : dσ u₁ < dσ u₂ :=
    prop2_prop_c_pos M m1 ρ hρ0 hρ1 hSR hSR' hmin hlt hu2 hgap
      (fun t ht => hdF_pos_lt t ⟨ht.1.le, hc_eq.symm ▸ ht.2⟩)
  exact ⟨lt_of_lt_of_le hF1 (hc_eq ▸ hdF_c), fun _ => by linarith, by linarith⟩

/-- Pool increment formula for `Δσ` (Property (d)). -/
private lemma prop2_pool_delta_sigma_sub {I : Pool} (hI : I ∈ m1.pools)
    {x y : ℝ} (hx : x ∈ Icc I.α I.β) (hy : y ∈ Icc I.α I.β) (hxy : x ≤ y) :
    (sigma M m1 ρ hρ0 hρ1 θ' y - sigma M m1 ρ hρ0 hρ1 θ y) -
    (sigma M m1 ρ hρ0 hρ1 θ' x - sigma M m1 ρ hρ0 hρ1 θ x) =
      (y - x) * (poolAvg M.n (effDist M θ' 0 I.α) (effDist M θ' 0 I.β) -
                 poolAvg M.n (effDist M θ 0 I.α) (effDist M θ 0 I.β)) +
      ∫ t in x..y, (alloc M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) t -
                    alloc M (SPA ρ hρ0 hρ1) (effDist M θ' (rivalIdx M)) t) := by
  have hIin := m1.hpools_in I hI
  have hx0 : 0 ≤ x := m1.hr0.trans (hIin.1.trans hx.1)
  have hx1 : x ≤ 1 := hx.2.trans hIin.2
  have hy0 : 0 ≤ y := hx0.trans hxy
  have hy1 : y ≤ 1 := hy.2.trans hIin.2
  have h1 := sigma_sub M m1 ρ hρ0 hρ1 hSR' hx0 hx1 hy0 hy1
  have h2 := sigma_sub M m1 ρ hρ0 hρ1 hSR hx0 hx1 hy0 hy1
  have hi1' := alloc_intervalIntegrable M m1 _ (vs_effDist_monotoneOn θ' 0)
    (fun z hz => effDist_nonneg θ' 0 hz) hx1 hy1
  have hi1 := alloc_intervalIntegrable M m1 _ (vs_effDist_monotoneOn θ 0)
    (fun z hz => effDist_nonneg θ 0 hz) hx1 hy1
  have hir := alloc_intervalIntegrable M (SPA ρ hρ0 hρ1) _ (vs_effDist_monotoneOn θ (rivalIdx M))
    (fun z hz => effDist_nonneg θ (rivalIdx M) hz) hx1 hy1
  have hir' := alloc_intervalIntegrable M (SPA ρ hρ0 hρ1) _ (vs_effDist_monotoneOn θ' (rivalIdx M))
    (fun z hz => effDist_nonneg θ' (rivalIdx M) hz) hx1 hy1
  have hpool_eq : ∫ t in x..y, (alloc M m1 (effDist M θ' 0) t - alloc M m1 (effDist M θ 0) t) =
      (y - x) * (poolAvg M.n (effDist M θ' 0 I.α) (effDist M θ' 0 I.β) -
                 poolAvg M.n (effDist M θ 0 I.α) (effDist M θ 0 I.β)) := by
    have hcongr : ∫ t in x..y, (alloc M m1 (effDist M θ' 0) t - alloc M m1 (effDist M θ 0) t) =
        ∫ _ in x..y, (poolAvg M.n (effDist M θ' 0 I.α) (effDist M θ' 0 I.β) -
                      poolAvg M.n (effDist M θ 0 I.α) (effDist M θ 0 I.β)) := by
      apply intervalIntegral.integral_congr_ae
      have hne_y : ∀ᵐ t ∂volume, t ≠ y := by simp [ae_iff, measure_singleton]
      filter_upwards [hne_y] with t hty hmem
      rw [uIoc_of_le hxy] at hmem
      have htI : t ∈ Ioo I.α I.β := ⟨lt_of_le_of_lt hx.1 hmem.1, lt_of_lt_of_le (lt_of_le_of_ne hmem.2 hty) hy.2⟩
      rw [alloc_in_pool M m1 _ hI htI, alloc_in_pool M m1 _ hI htI]
    rw [hcongr, intervalIntegral.integral_const, smul_eq_mul]
  rw [intervalIntegral.integral_sub hi1' hir'] at h1
  rw [intervalIntegral.integral_sub hi1 hir] at h2
  rw [intervalIntegral.integral_sub hi1' hi1] at hpool_eq
  rw [intervalIntegral.integral_sub hir hir']
  linarith

/-- Helper: strict positivity of `∫_x^y φ` when `ρ ≤ x < y ≤ 1` and `ΔF > 0` on `(x, y)`. -/
private lemma prop2_phi_integral_pos {x y : ℝ} (hρx : ρ ≤ x) (hlt : x < y) (hy1 : y ≤ 1)
    (hFpos : ∀ t ∈ Ioo x y, 0 < effDist M θ' 0 t - effDist M θ 0 t) :
    0 < ∫ t in x..y, (alloc M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) t -
                      alloc M (SPA ρ hρ0 hρ1) (effDist M θ' (rivalIdx M)) t) := by
  let φ : ℝ → ℝ := fun t =>
    alloc M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) t -
    alloc M (SPA ρ hρ0 hρ1) (effDist M θ' (rivalIdx M)) t
  have hcont : ContinuousOn φ (Icc x y) := by
    have h1 := ((effDist_continuousOn θ (rivalIdx M)).mono
      (fun t (ht : t ∈ Icc x y) => ht.2.trans hy1)).pow (M.n - 1)
    have h2 := ((effDist_continuousOn θ' (rivalIdx M)).mono
      (fun t (ht : t ∈ Icc x y) => ht.2.trans hy1)).pow (M.n - 1)
    exact (h1.sub h2).congr fun t ht => by
      dsimp only [φ, Pi.sub_apply, Pi.pow_apply]
      rw [alloc_SPA, alloc_SPA, ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr (hρx.trans ht.1))),
        ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr (hρx.trans ht.1)))]
  have hnn : ∀ t ∈ Ioc x y, 0 ≤ φ t := by
    intro t ht
    have hprops := prop2_phi_props M m1 ρ hρ0 hρ1 hSR hSR' (ht.2.trans hy1)
    by_cases hty : t = y
    · rw [hty]
      have hdF_cont : ContinuousOn (fun z => effDist M θ' 0 z - effDist M θ 0 z) (Icc x y) :=
        ((effDist_continuousOn θ' 0).mono (fun z (hz : z ∈ Icc x y) => hz.2.trans hy1)).sub
          ((effDist_continuousOn θ 0).mono (fun z (hz : z ∈ Icc x y) => hz.2.trans hy1))
      have hdFy : 0 ≤ effDist M θ' 0 y - effDist M θ 0 y := by
        have htend := (hdF_cont y (right_mem_Icc.mpr hlt.le)).mono_left
          (nhdsWithin_mono _ Ioo_subset_Icc_self)
        have : NeBot (𝓝[Ioo x y] y) := right_nhdsWithin_Ioo_neBot hlt
        exact ge_of_tendsto htend (eventually_nhdsWithin_of_forall fun z hz => (hFpos z hz).le)
      exact ((prop2_phi_props M m1 ρ hρ0 hρ1 hSR hSR' hy1).2.1 (hρx.trans hlt.le)).2.1 hdFy
    · exact (hprops.2.1 (hρx.trans ht.1.le)).2.1 (hFpos t ⟨ht.1, lt_of_le_of_ne ht.2 hty⟩).le
  have hmid : 0 < φ ((x + y) / 2) :=
    ((prop2_phi_props M m1 ρ hρ0 hρ1 hSR hSR' (by linarith)).2.1 (by linarith)).1
      (hFpos ((x + y) / 2) ⟨by linarith, by linarith⟩)
  exact intervalIntegral.integral_pos hlt hcont hnn ⟨(x + y) / 2, ⟨by linarith, by linarith⟩, hmid⟩

/-- Step 2 (pools cannot bring a signed pair to rest): if `(ΔF, Δσ)` is positive at `I.α`,
then at `I.β` it is either strictly positive or strictly negative. -/
private lemma prop2_step2_pool_pos {I : Pool} (hI : I ∈ m1.pools)
    (hFα : 0 < effDist M θ' 0 I.α - effDist M θ 0 I.α)
    (hσα : 0 ≤ sigma M m1 ρ hρ0 hρ1 θ' I.α - sigma M m1 ρ hρ0 hρ1 θ I.α) :
    (0 < effDist M θ' 0 I.β - effDist M θ 0 I.β ∧
     0 < sigma M m1 ρ hρ0 hρ1 θ' I.β - sigma M m1 ρ hρ0 hρ1 θ I.β) ∨
    (effDist M θ' 0 I.β - effDist M θ 0 I.β < 0 ∧
     sigma M m1 ρ hρ0 hρ1 θ' I.β - sigma M m1 ρ hρ0 hρ1 θ I.β < 0) := by
  let dF : ℝ → ℝ := fun v => effDist M θ' 0 v - effDist M θ 0 v
  let dσ : ℝ → ℝ := fun v => sigma M m1 ρ hρ0 hρ1 θ' v - sigma M m1 ρ hρ0 hρ1 θ v
  let dxbar := poolAvg M.n (effDist M θ' 0 I.α) (effDist M θ' 0 I.β) -
               poolAvg M.n (effDist M θ 0 I.α) (effDist M θ 0 I.β)
  have hIin := m1.hpools_in I hI
  have hIα1 : I.α ≤ 1 := I.hαβ.le.trans hIin.2
  have hmin_α : min m1.r ρ ≤ I.α := min_le_of_left_le hIin.1
  by_cases hdx : 0 ≤ dxbar
  · left
    let S : Set ℝ := {v ∈ Icc I.α I.β | ∀ x ∈ Icc I.α v, 0 < dF x}
    have hS_ne : S.Nonempty := ⟨I.α, left_mem_Icc.mpr I.hαβ.le, fun x hx => by
      have : x = I.α := le_antisymm hx.2 hx.1; rw [this]; exact hFα⟩
    have hS_bdd : BddAbove S := ⟨I.β, fun v hv => hv.1.2⟩
    let c := sSup S
    have hc_ge : I.α ≤ c := le_csSup hS_bdd ⟨left_mem_Icc.mpr I.hαβ.le, fun x hx => by
      have : x = I.α := le_antisymm hx.2 hx.1; rw [this]; exact hFα⟩
    have hc_le : c ≤ I.β := csSup_le hS_ne (fun v hv => hv.1.2)
    have hdF_pos_lt : ∀ x ∈ Ico I.α c, 0 < dF x := by
      intro x hx
      obtain ⟨v, hvS, hxv⟩ := exists_lt_of_lt_csSup hS_ne hx.2
      exact hvS.2 x ⟨hx.1, hxv.le⟩
    have hdF_c : dF I.α ≤ dF c := by
      by_cases hcρ : c ≤ ρ
      · have hconst := prop2_prop_a M m1 ρ hρ0 hρ1 hSR hSR'
          ⟨hmin_α, hc_ge.trans hcρ⟩ ⟨hmin_α.trans hc_ge, hcρ⟩
        linarith
      · push Not at hcρ
        let b := max I.α ρ
        have hb_mem : b ∈ Icc I.α c := ⟨le_max_left _ _, max_le hc_ge hcρ.le⟩
        have hdF_b : dF b = dF I.α := by
          by_cases hαρ : I.α ≤ ρ
          · have hbeq : b = ρ := max_eq_right hαρ
            rw [hbeq]
            exact prop2_prop_a M m1 ρ hρ0 hρ1 hSR hSR' ⟨hmin_α, hαρ⟩ ⟨hmin_α.trans hαρ, le_rfl⟩
          · push Not at hαρ; dsimp only [b]; rw [max_eq_left hαρ.le]
        have hdσ_b : dσ I.α ≤ dσ b := by
          have hsub := prop2_pool_delta_sigma_sub M m1 ρ hρ0 hρ1 hSR hSR' hI
            (left_mem_Icc.mpr I.hαβ.le) ⟨hb_mem.1, hb_mem.2.trans hc_le⟩ hb_mem.1
          have hphi_nn : 0 ≤ ∫ t in I.α..b,
              (alloc M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) t -
               alloc M (SPA ρ hρ0 hρ1) (effDist M θ' (rivalIdx M)) t) := by
            rw [intervalIntegral.integral_of_le hb_mem.1]
            apply MeasureTheory.integral_nonneg_of_ae
            have hne_b : ∀ᵐ t ∂volume, t ≠ b := by simp [ae_iff, measure_singleton]
            change ∀ᵐ t ∂(volume.restrict (Ioc I.α b)), (0 : ℝ) ≤ _
            rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
            filter_upwards [hne_b] with t htb ht
            have ht1 : t ≤ 1 := (ht.2.trans (hb_mem.2.trans hc_le)).trans hIin.2
            have hp := prop2_phi_props M m1 ρ hρ0 hρ1 hSR hSR' ht1
            by_cases htρ : t < ρ
            · rw [hp.1 htρ]
            · push Not at htρ
              exact (hp.2.1 htρ).2.1 (hdF_pos_lt t ⟨ht.1.le, lt_of_le_of_ne ht.2 htb |>.trans_le hb_mem.2⟩).le
          have h1 : 0 ≤ (b - I.α) * dxbar := mul_nonneg (sub_nonneg.mpr hb_mem.1) hdx
          linarith
        have hdσ_pos_bc : ∀ x ∈ Ioo b c, 0 < dσ x := by
          intro x hx
          have hsub := prop2_pool_delta_sigma_sub M m1 ρ hρ0 hρ1 hSR hSR' hI
            ⟨hb_mem.1, hb_mem.2.trans hc_le⟩ ⟨hb_mem.1.trans hx.1.le, hx.2.le.trans hc_le⟩ hx.1.le
          have hphi_pos := prop2_phi_integral_pos M m1 ρ hρ0 hρ1 hSR hSR'
            (le_max_right I.α ρ) hx.1 ((hx.2.le.trans hc_le).trans hIin.2)
            (fun t ht => hdF_pos_lt t ⟨hb_mem.1.trans ht.1.le, ht.2.trans hx.2⟩)
          have h1 : 0 ≤ (x - b) * dxbar := mul_nonneg (sub_nonneg.mpr hx.1.le) hdx
          linarith
        have hdF_bc := prop2_prop_b_pos M m1 ρ hρ0 hρ1 hSR hSR' hb_mem.2 (hc_le.trans hIin.2) hdσ_pos_bc
        linarith
    have hc_eq : c = I.β := by
      by_contra hne
      have hclt : c < I.β := lt_of_le_of_ne hc_le hne
      have hcont : ContinuousOn dF (Icc I.α I.β) :=
        ((effDist_continuousOn θ' 0).mono (fun t (ht : t ∈ Icc I.α I.β) => ht.2.trans hIin.2)).sub
          ((effDist_continuousOn θ 0).mono (fun t (ht : t ∈ Icc I.α I.β) => ht.2.trans hIin.2))
      have hc_pos : 0 < dF c := lt_of_lt_of_le hFα hdF_c
      obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousWithinAt_iff.mp (hcont c ⟨hc_ge, hc_le⟩) (dF c / 2) (half_pos hc_pos)
      let c' := min I.β (c + δ / 2)
      have hc'_gt : c < c' := lt_min hclt (by linarith)
      have hc'_mem : c' ∈ S := by
        refine ⟨⟨hc_ge.trans hc'_gt.le, min_le_left _ _⟩, fun x hx => ?_⟩
        by_cases hxc : x < c
        · exact hdF_pos_lt x ⟨hx.1, hxc⟩
        · push Not at hxc
          have hdist : dist x c < δ := by
            rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hxc)]
            have : x ≤ c + δ / 2 := hx.2.trans (min_le_right _ _)
            linarith
          have h1 := hδ ⟨hx.1, hx.2.trans (min_le_left _ _)⟩ hdist
          rw [Real.dist_eq] at h1; linarith [(abs_lt.mp h1).1]
      exact not_lt.mpr (le_csSup hS_bdd hc'_mem) hc'_gt
    have hdFβ : 0 < dF I.β := lt_of_lt_of_le hFα (hc_eq ▸ hdF_c)
    have hdx_pos : 0 < dxbar := sub_pos.mpr (poolAvg_diff_pos M.hn
      (effDist_nonneg θ 0 hIα1) (effDist_nonneg θ 0 hIin.2)
      (by linarith) (by linarith) (Or.inl (by linarith)))
    have hsub := prop2_pool_delta_sigma_sub M m1 ρ hρ0 hρ1 hSR hSR' hI
      (left_mem_Icc.mpr I.hαβ.le) (right_mem_Icc.mpr I.hαβ.le) I.hαβ.le
    have hphi_nn : 0 ≤ ∫ t in I.α..I.β,
        (alloc M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) t -
         alloc M (SPA ρ hρ0 hρ1) (effDist M θ' (rivalIdx M)) t) := by
      rw [intervalIntegral.integral_of_le I.hαβ.le]
      apply MeasureTheory.integral_nonneg_of_ae
      have hne_β : ∀ᵐ t ∂volume, t ≠ I.β := by simp [ae_iff, measure_singleton]
      change ∀ᵐ t ∂(volume.restrict (Ioc I.α I.β)), (0 : ℝ) ≤ _
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
      filter_upwards [hne_β] with t htβ ht
      have hp := prop2_phi_props M m1 ρ hρ0 hρ1 hSR hSR' (ht.2.trans hIin.2)
      by_cases htρ : t < ρ
      · rw [hp.1 htρ]
      · push Not at htρ
        exact (hp.2.1 htρ).2.1 (hdF_pos_lt t ⟨ht.1.le, hc_eq.symm ▸ lt_of_le_of_ne ht.2 htβ⟩).le
    have hprod_pos : 0 < (I.β - I.α) * dxbar := mul_pos (sub_pos.mpr I.hαβ) hdx_pos
    exact ⟨hdFβ, by linarith⟩
  · push Not at hdx
    right
    have hdFβ : dF I.β < 0 := by
      by_contra hge; push Not at hge
      dsimp only [dF] at hge
      have hpos : 0 < dxbar := sub_pos.mpr (poolAvg_diff_pos M.hn
        (effDist_nonneg θ 0 hIα1) (effDist_nonneg θ 0 hIin.2)
        (by linarith) (by linarith) (Or.inl (by linarith)))
      linarith
    have hcont : ContinuousOn dF (Icc I.α I.β) :=
      ((effDist_continuousOn θ' 0).mono (fun t (ht : t ∈ Icc I.α I.β) => ht.2.trans hIin.2)).sub
        ((effDist_continuousOn θ 0).mono (fun t (ht : t ∈ Icc I.α I.β) => ht.2.trans hIin.2))
    let Z : Set ℝ := {v ∈ Icc I.α I.β | dF v = 0}
    have hZ_ne : Z.Nonempty := by
      have h0 : (0 : ℝ) ∈ Icc (dF I.β) (dF I.α) := ⟨hdFβ.le, hFα.le⟩
      exact intermediate_value_Icc' I.hαβ.le hcont h0
    have hZ_bdd : BddAbove Z := ⟨I.β, fun v hv => hv.1.2⟩
    let z0 := sSup Z
    have hz0_mem : z0 ∈ Icc I.α I.β := ⟨le_trans hZ_ne.choose_spec.1.1 (le_csSup hZ_bdd hZ_ne.choose_spec),
      csSup_le hZ_ne (fun v hv => hv.1.2)⟩
    have hz0_zero : dF z0 = 0 := by
      have hcl : z0 ∈ closure Z := csSup_mem_closure hZ_ne hZ_bdd
      have hZ_closed : IsClosed Z := by
        have h1 : Z = Icc I.α I.β ∩ dF ⁻¹' {0} := by ext v; simp [Z]
        rw [h1]
        exact hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
      rw [hZ_closed.closure_eq] at hcl; exact hcl.2
    have hz0_lt : z0 < I.β := lt_of_le_of_ne hz0_mem.2 (fun h => by rw [h] at hz0_zero; linarith)
    have hdF_neg : ∀ x ∈ Ioc z0 I.β, dF x < 0 := by
      intro x hx
      by_contra hge; push Not at hge
      rcases eq_or_lt_of_le hge with h0 | hpos
      · have hxZ : x ∈ Z := ⟨⟨hz0_mem.1.trans hx.1.le, hx.2⟩, h0.symm⟩
        exact not_le.mpr hx.1 (le_csSup hZ_bdd hxZ)
      · obtain ⟨z, hz, hz0'⟩ := intermediate_value_Icc' hx.2
          (hcont.mono (Icc_subset_Icc (hz0_mem.1.trans hx.1.le) le_rfl)) ⟨hdFβ.le, hpos.le⟩
        have hzZ : z ∈ Z := ⟨⟨hz0_mem.1.trans (hx.1.le.trans hz.1), hz.2⟩, hz0'⟩
        exact not_lt.mpr (le_csSup hZ_bdd hzZ) (lt_of_lt_of_le hx.1 hz.1)
    have hdσ_anti : ∀ x ∈ Ico z0 I.β, dσ I.β < dσ x := by
      intro x hx
      have hsub := prop2_pool_delta_sigma_sub M m1 ρ hρ0 hρ1 hSR hSR' hI
        ⟨hz0_mem.1.trans hx.1, hx.2.le⟩ (right_mem_Icc.mpr I.hαβ.le) hx.2.le
      have hphi_np : ∫ t in x..I.β,
          (alloc M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) t -
           alloc M (SPA ρ hρ0 hρ1) (effDist M θ' (rivalIdx M)) t) ≤ 0 := by
        rw [intervalIntegral.integral_of_le hx.2.le]
        apply MeasureTheory.integral_nonpos_of_ae
        change ∀ᵐ t ∂(volume.restrict (Ioc x I.β)), _ ≤ (0 : ℝ)
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
        filter_upwards with t ht
        have hp := prop2_phi_props M m1 ρ hρ0 hρ1 hSR hSR' (ht.2.trans hIin.2)
        by_cases htρ : t < ρ
        · rw [hp.1 htρ]
        · push Not at htρ
          exact (hp.2.1 htρ).2.2.1 (hdF_neg t ⟨lt_of_le_of_lt hx.1 ht.1, ht.2⟩).le
      have hprod_neg : (I.β - x) * dxbar < 0 := mul_neg_of_pos_of_neg (sub_pos.mpr hx.2) hdx
      linarith
    have hdσβ : dσ I.β < 0 := by
      by_contra hge; push Not at hge
      have hdσ_pos : ∀ x ∈ Ioo z0 I.β, 0 < dσ x := fun x hx =>
        lt_of_le_of_lt hge (hdσ_anti x ⟨hx.1.le, hx.2⟩)
      have hmono := prop2_prop_b_pos M m1 ρ hρ0 hρ1 hSR hSR' hz0_lt.le hIin.2 hdσ_pos
      linarith
    exact ⟨hdFβ, hdσβ⟩

/-- Step 3 (from rest across a gap): if `[u₁, u₂]` meets no pool and `(ΔF, Δσ)` is at rest at `u₁`,
then either `ΔF = 0 ∧ Δσ = 0` everywhere on `[u₁, u₂]`, or `(ΔF, Δσ)` is strictly signed at `u₂`. -/
private lemma prop2_step3_gap_rest {u₁ u₂ : ℝ} (hmin : min m1.r ρ ≤ u₁) (hle : u₁ ≤ u₂) (hu2 : u₂ ≤ 1)
    (hgap : ∀ I ∈ m1.pools, ∀ t ∈ Ioo u₁ u₂, ¬ (I.α < t ∧ t < I.β))
    (hF1 : effDist M θ' 0 u₁ - effDist M θ 0 u₁ = 0)
    (hσ1 : sigma M m1 ρ hρ0 hρ1 θ' u₁ - sigma M m1 ρ hρ0 hρ1 θ u₁ = 0) :
    (∀ v ∈ Icc u₁ u₂, effDist M θ' 0 v - effDist M θ 0 v = 0 ∧
      sigma M m1 ρ hρ0 hρ1 θ' v - sigma M m1 ρ hρ0 hρ1 θ v = 0) ∨
    (0 < effDist M θ' 0 u₂ - effDist M θ 0 u₂ ∧
     0 < sigma M m1 ρ hρ0 hρ1 θ' u₂ - sigma M m1 ρ hρ0 hρ1 θ u₂) ∨
    (effDist M θ' 0 u₂ - effDist M θ 0 u₂ < 0 ∧
     sigma M m1 ρ hρ0 hρ1 θ' u₂ - sigma M m1 ρ hρ0 hρ1 θ u₂ < 0) := by
  let dF : ℝ → ℝ := fun v => effDist M θ' 0 v - effDist M θ 0 v
  let dσ : ℝ → ℝ := fun v => sigma M m1 ρ hρ0 hρ1 θ' v - sigma M m1 ρ hρ0 hρ1 θ v
  by_cases hall : ∀ v ∈ Icc u₁ u₂, dF v = 0
  · left
    intro v hv
    refine ⟨hall v hv, ?_⟩
    have hu1_0 : 0 ≤ u₁ := (le_min m1.hr0 hρ0).trans hmin
    have hv0 : 0 ≤ v := hu1_0.trans hv.1
    have hu1_1 : u₁ ≤ 1 := hle.trans hu2
    have hv1 : v ≤ 1 := hv.2.trans hu2
    have h1 := sigma_sub M m1 ρ hρ0 hρ1 hSR' hu1_0 hu1_1 hv0 hv1
    have h2 := sigma_sub M m1 ρ hρ0 hρ1 hSR hu1_0 hu1_1 hv0 hv1
    have hcongr : ∫ t in u₁..v, (alloc M m1 (effDist M θ' 0) t - alloc M (SPA ρ hρ0 hρ1) (effDist M θ' (rivalIdx M)) t) =
        ∫ t in u₁..v, (alloc M m1 (effDist M θ 0) t - alloc M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) t) := by
      apply intervalIntegral.integral_congr_ae
      have hne_v : ∀ᵐ t ∂volume, t ≠ v := by simp [ae_iff, measure_singleton]
      filter_upwards [hne_v] with t htv ht
      rw [uIoc_of_le hv.1] at ht
      have ht_oo : t ∈ Ioo u₁ u₂ := ⟨ht.1, lt_of_lt_of_le (lt_of_le_of_ne ht.2 htv) hv.2⟩
      have hdFt : dF t = 0 := hall t ⟨ht.1.le, ht.2.trans hv.2⟩
      have hFeq : effDist M θ' 0 t = effDist M θ 0 t := sub_eq_zero.mp hdFt
      have ha1 : alloc M m1 (effDist M θ' 0) t = alloc M m1 (effDist M θ 0) t := by
        by_cases htr : t < m1.r
        · rw [alloc_below_r M m1 _ htr, alloc_below_r M m1 _ htr]
        · push Not at htr
          rw [alloc_off_pools M m1 _ htr (fun I hI => hgap I hI t ht_oo),
              alloc_off_pools M m1 _ htr (fun I hI => hgap I hI t ht_oo), hFeq]
      have ha2 : alloc M (SPA ρ hρ0 hρ1) (effDist M θ' (rivalIdx M)) t =
          alloc M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) t := by
        have hp := prop2_phi_props M m1 ρ hρ0 hρ1 hSR hSR' (ht.2.trans hv1)
        by_cases htρ : t < ρ
        · linarith [hp.1 htρ]
        · push Not at htρ
          have h1' := (hp.2.1 htρ).2.1 hdFt.ge
          have h2' := (hp.2.1 htρ).2.2.1 hdFt.le
          linarith
      rw [ha1, ha2]
    linarith
  · push Not at hall
    obtain ⟨v0, hv0, hne0⟩ := hall
    -- Helper: if dF v0 > 0, then dσ v0 > 0, and Step 1 gives strictly positive at u₂
    have hpos_case : ∀ (θ₁ θ₂ : VisitStrategy M),
        IsSR M (unilateralProfile M m1 ρ hρ0 hρ1) θ₁ →
        IsSR M (unilateralProfile M m1 ρ hρ0 hρ1) θ₂ →
        effDist M θ₂ 0 u₁ - effDist M θ₁ 0 u₁ = 0 →
        0 < effDist M θ₂ 0 v0 - effDist M θ₁ 0 v0 →
        0 < effDist M θ₂ 0 u₂ - effDist M θ₁ 0 u₂ ∧
        0 < sigma M m1 ρ hρ0 hρ1 θ₂ u₂ - sigma M m1 ρ hρ0 hρ1 θ₁ u₂ := by
      intro θ₁ θ₂ h₁ h₂ h0 hv0_pos
      let dF' : ℝ → ℝ := fun v => effDist M θ₂ 0 v - effDist M θ₁ 0 v
      let dσ' : ℝ → ℝ := fun v => sigma M m1 ρ hρ0 hρ1 θ₂ v - sigma M m1 ρ hρ0 hρ1 θ₁ v
      have hv0_gt : u₁ < v0 := lt_of_le_of_ne hv0.1 (fun h => by rw [← h] at hv0_pos; linarith)
      let Z : Set ℝ := {v ∈ Icc u₁ v0 | dF' v = 0}
      have hZ_ne : Z.Nonempty := ⟨u₁, left_mem_Icc.mpr hv0_gt.le, h0⟩
      have hZ_bdd : BddAbove Z := ⟨v0, fun v hv => hv.1.2⟩
      let y1 := sSup Z
      have hy1_mem : y1 ∈ Icc u₁ v0 := ⟨le_csSup hZ_bdd ⟨left_mem_Icc.mpr hv0_gt.le, h0⟩,
        csSup_le hZ_ne (fun v hv => hv.1.2)⟩
      have hcont : ContinuousOn dF' (Icc u₁ v0) :=
        ((effDist_continuousOn θ₂ 0).mono (fun t (ht : t ∈ Icc u₁ v0) => ht.2.trans (hv0.2.trans hu2))).sub
          ((effDist_continuousOn θ₁ 0).mono (fun t (ht : t ∈ Icc u₁ v0) => ht.2.trans (hv0.2.trans hu2)))
      have hy1_zero : dF' y1 = 0 := by
        have hcl : y1 ∈ closure Z := csSup_mem_closure hZ_ne hZ_bdd
        have hZ_closed : IsClosed Z := by
          have : Z = Icc u₁ v0 ∩ dF' ⁻¹' {0} := by ext v; simp [Z]
          rw [this]; exact hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
        rw [hZ_closed.closure_eq] at hcl; exact hcl.2
      have hy1_lt : y1 < v0 := lt_of_le_of_ne hy1_mem.2 (fun h => by rw [h] at hy1_zero; linarith)
      have hdF'_pos : ∀ x ∈ Ioc y1 v0, 0 < dF' x := by
        intro x hx
        by_contra hle'; push Not at hle'
        rcases eq_or_lt_of_le hle' with h0' | hneg'
        · exact not_le.mpr hx.1 (le_csSup hZ_bdd ⟨⟨hy1_mem.1.trans hx.1.le, hx.2⟩, h0'⟩)
        · obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc hx.2
            (hcont.mono (Icc_subset_Icc (hy1_mem.1.trans hx.1.le) le_rfl)) ⟨hneg'.le, hv0_pos.le⟩
          exact not_lt.mpr (le_csSup hZ_bdd ⟨⟨hy1_mem.1.trans (hx.1.le.trans hz.1), hz.2⟩, hz0⟩)
            (lt_of_lt_of_le hx.1 hz.1)
      have hdσ'_v0 : 0 < dσ' v0 := by
        by_contra hle'; push Not at hle'
        have hdσ'_neg : ∀ x ∈ Ioo y1 v0, dσ' x < 0 := by
          intro x hx
          have hinc := prop2_prop_c_pos M m1 ρ hρ0 hρ1 h₁ h₂
            (hmin.trans (hy1_mem.1.trans hx.1.le)) hx.2 (hv0.2.trans hu2)
            (fun I hI t ht => hgap I hI t ⟨lt_of_le_of_lt (hy1_mem.1.trans hx.1.le) ht.1,
              lt_of_lt_of_le ht.2 hv0.2⟩)
            (fun t ht => hdF'_pos t ⟨hx.1.trans ht.1, ht.2.le⟩)
          linarith
        have hanti := prop2_prop_b_neg M m1 ρ hρ0 hρ1 h₁ h₂ hy1_lt.le (hv0.2.trans hu2) hdσ'_neg
        linarith
      have hstep1 := prop2_step1_gap_pos M m1 ρ hρ0 hρ1 h₁ h₂
        (hmin.trans hv0.1) hv0.2 hu2
        (fun I hI t ht => hgap I hI t ⟨lt_of_le_of_lt hv0.1 ht.1, ht.2⟩)
        hv0_pos hdσ'_v0.le
      rcases eq_or_lt_of_le hv0.2 with rfl | hv0_lt
      · exact ⟨hv0_pos, hdσ'_v0⟩
      · exact ⟨hstep1.1, hstep1.2.1 hv0_lt⟩
    rcases lt_or_gt_of_ne hne0 with hneg | hpos
    · right; right
      have := hpos_case θ' θ hSR' hSR (by linarith) (by linarith)
      exact ⟨by linarith, by linarith⟩
    · right; left
      exact hpos_case θ θ' hSR hSR' hF1 hpos

/-- Step 4 (from rest across a pool): if `(ΔF, Δσ)` is at rest at `I.α`, then either
`ΔF = 0 ∧ Δσ = 0` everywhere on `[I.α, I.β]`, or `(ΔF, Δσ)` is strictly signed at `I.β`. -/
private lemma prop2_step4_pool_rest {I : Pool} (hI : I ∈ m1.pools)
    (hFα : effDist M θ' 0 I.α - effDist M θ 0 I.α = 0)
    (hσα : sigma M m1 ρ hρ0 hρ1 θ' I.α - sigma M m1 ρ hρ0 hρ1 θ I.α = 0) :
    (∀ v ∈ Icc I.α I.β, effDist M θ' 0 v - effDist M θ 0 v = 0 ∧
      sigma M m1 ρ hρ0 hρ1 θ' v - sigma M m1 ρ hρ0 hρ1 θ v = 0) ∨
    (0 < effDist M θ' 0 I.β - effDist M θ 0 I.β ∧
     0 < sigma M m1 ρ hρ0 hρ1 θ' I.β - sigma M m1 ρ hρ0 hρ1 θ I.β) ∨
    (effDist M θ' 0 I.β - effDist M θ 0 I.β < 0 ∧
     sigma M m1 ρ hρ0 hρ1 θ' I.β - sigma M m1 ρ hρ0 hρ1 θ I.β < 0) := by
  have hIin := m1.hpools_in I hI
  have hIα1 : I.α ≤ 1 := I.hαβ.le.trans hIin.2
  have hmin_α : min m1.r ρ ≤ I.α := min_le_of_left_le hIin.1
  -- Helper for Case 4a: ΔF(I.β) > 0 ⇒ strictly positive at I.β
  have hpos_end : ∀ (θ₁ θ₂ : VisitStrategy M),
      IsSR M (unilateralProfile M m1 ρ hρ0 hρ1) θ₁ →
      IsSR M (unilateralProfile M m1 ρ hρ0 hρ1) θ₂ →
      effDist M θ₂ 0 I.α - effDist M θ₁ 0 I.α = 0 →
      sigma M m1 ρ hρ0 hρ1 θ₂ I.α - sigma M m1 ρ hρ0 hρ1 θ₁ I.α = 0 →
      0 < effDist M θ₂ 0 I.β - effDist M θ₁ 0 I.β →
      0 < sigma M m1 ρ hρ0 hρ1 θ₂ I.β - sigma M m1 ρ hρ0 hρ1 θ₁ I.β := by
    intro θ₁ θ₂ h₁ h₂ hFα' hσα' hFβ'
    let dF' : ℝ → ℝ := fun v => effDist M θ₂ 0 v - effDist M θ₁ 0 v
    let dσ' : ℝ → ℝ := fun v => sigma M m1 ρ hρ0 hρ1 θ₂ v - sigma M m1 ρ hρ0 hρ1 θ₁ v
    let dxbar' := poolAvg M.n (effDist M θ₂ 0 I.α) (effDist M θ₂ 0 I.β) -
                  poolAvg M.n (effDist M θ₁ 0 I.α) (effDist M θ₁ 0 I.β)
    have hdx' : 0 < dxbar' := sub_pos.mpr (poolAvg_diff_pos M.hn
      (effDist_nonneg θ₁ 0 hIα1) (effDist_nonneg θ₁ 0 hIin.2)
      (by linarith) (by linarith) (Or.inr (by linarith)))
    have hnn_all : ∀ v ∈ Icc I.α I.β, 0 ≤ dF' v := by
      by_contra hneg_ex; push Not at hneg_ex
      let N : Set ℝ := {v ∈ Ioo I.α I.β | dF' v < 0}
      have hN_ne : N.Nonempty := by
        obtain ⟨v, hv, hlt⟩ := hneg_ex
        have hv_gt : I.α < v := lt_of_le_of_ne hv.1 (fun h => by rw [← h] at hlt; linarith)
        have hv_lt : v < I.β := lt_of_le_of_ne hv.2 (fun h => by rw [h] at hlt; linarith)
        exact ⟨v, ⟨hv_gt, hv_lt⟩, hlt⟩
      have hN_bdd : BddBelow N := ⟨I.α, fun v hv => hv.1.1.le⟩
      let p0 := sInf N
      have hp0_ge : I.α ≤ p0 := le_csInf hN_ne (fun v hv => hv.1.1.le)
      have hp0_lt : p0 < I.β := lt_of_le_of_lt (csInf_le hN_bdd hN_ne.choose_spec) hN_ne.choose_spec.1.2
      have hnn_left : ∀ x ∈ Ico I.α p0, 0 ≤ dF' x := by
        intro x hx
        by_contra hlt; push Not at hlt
        rcases eq_or_lt_of_le hx.1 with rfl | hαx
        · linarith
        · exact not_lt.mpr (csInf_le hN_bdd ⟨⟨hαx, hx.2.trans hp0_lt⟩, hlt⟩) hx.2
      have hcont : ContinuousOn dF' (Icc I.α I.β) :=
        ((effDist_continuousOn θ₂ 0).mono (fun t (ht : t ∈ Icc I.α I.β) => ht.2.trans hIin.2)).sub
          ((effDist_continuousOn θ₁ 0).mono (fun t (ht : t ∈ Icc I.α I.β) => ht.2.trans hIin.2))
      have hp0_zero : dF' p0 = 0 := by
        have hle0 : dF' p0 ≤ 0 := by
          have hcl : p0 ∈ closure N := csInf_mem_closure hN_ne hN_bdd
          have hsub : N ⊆ Icc I.α I.β ∩ dF' ⁻¹' Iic 0 := fun v hv => ⟨Ioo_subset_Icc_self hv.1, hv.2.le⟩
          have hclosed : IsClosed (Icc I.α I.β ∩ dF' ⁻¹' Iic 0) :=
            hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
          exact (closure_minimal hsub hclosed hcl).2
        have hge0 : 0 ≤ dF' p0 := by
          rcases eq_or_lt_of_le hp0_ge with heq | hαp0
          · rw [← heq]; dsimp only [dF']; linarith
          · have htend := (hcont p0 ⟨hp0_ge, hp0_lt.le⟩).mono_left
              (nhdsWithin_mono _ (Ico_subset_Icc_self.trans (Icc_subset_Icc_right hp0_lt.le)))
            have : NeBot (𝓝[Ico I.α p0] p0) := right_nhdsWithin_Ico_neBot hαp0
            exact ge_of_tendsto htend (eventually_nhdsWithin_of_forall hnn_left)
        linarith
      -- dσ' p0 ≥ 0
      have hdσ'_p0 : 0 ≤ dσ' p0 := by
        have hsub := prop2_pool_delta_sigma_sub M m1 ρ hρ0 hρ1 h₁ h₂ hI
          (left_mem_Icc.mpr I.hαβ.le) ⟨hp0_ge, hp0_lt.le⟩ hp0_ge
        have hphi_nn : 0 ≤ ∫ t in I.α..p0,
            (alloc M (SPA ρ hρ0 hρ1) (effDist M θ₁ (rivalIdx M)) t -
             alloc M (SPA ρ hρ0 hρ1) (effDist M θ₂ (rivalIdx M)) t) := by
          rw [intervalIntegral.integral_of_le hp0_ge]
          apply MeasureTheory.integral_nonneg_of_ae
          have hne_p0 : ∀ᵐ t ∂volume, t ≠ p0 := by simp [ae_iff, measure_singleton]
          change ∀ᵐ t ∂(volume.restrict (Ioc I.α p0)), (0 : ℝ) ≤ _
          rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
          filter_upwards [hne_p0] with t htp0 ht
          have hp := prop2_phi_props M m1 ρ hρ0 hρ1 h₁ h₂ ((ht.2.trans hp0_lt.le).trans hIin.2)
          by_cases htρ : t < ρ
          · rw [hp.1 htρ]
          · push Not at htρ
            exact (hp.2.1 htρ).2.1 (hnn_left t ⟨ht.1.le, lt_of_le_of_ne ht.2 htp0⟩)
        have h1' : 0 ≤ (p0 - I.α) * dxbar' := mul_nonneg (sub_nonneg.mpr hp0_ge) hdx'.le
        linarith
      -- Near p0, |φ| ≤ dxbar' / 2, so dσ' strictly increases and dF' ≥ 0 on [p0, p0 + ε]
      have hη_pos : 0 < ((M.m : ℝ) - 1) / (2 * ((M.n : ℝ) - 1)) * dxbar' :=
        mul_pos (div_pos M.m_sub_one_pos_real (by linarith [M.n_sub_one_pos_real])) hdx'
      obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousWithinAt_iff.mp (hcont p0 ⟨hp0_ge, hp0_lt.le⟩) _ hη_pos
      let p1 := min I.β (p0 + δ / 2)
      have hp1_gt : p0 < p1 := lt_min hp0_lt (by linarith)
      have hdσ'_pos_near : ∀ x ∈ Ioo p0 p1, 0 < dσ' x := by
        intro x hx
        have hsub := prop2_pool_delta_sigma_sub M m1 ρ hρ0 hρ1 h₁ h₂ hI
          ⟨hp0_ge, hp0_lt.le⟩ ⟨hp0_ge.trans hx.1.le, hx.2.le.trans (min_le_left _ _)⟩ hx.1.le
        have hphi_lb : -((x - p0) * (dxbar' / 2)) ≤ ∫ t in p0..x,
            (alloc M (SPA ρ hρ0 hρ1) (effDist M θ₁ (rivalIdx M)) t -
             alloc M (SPA ρ hρ0 hρ1) (effDist M θ₂ (rivalIdx M)) t) := by
          have hle_int : ∫ _ in p0..x, (-(dxbar' / 2)) ≤ ∫ t in p0..x,
              (alloc M (SPA ρ hρ0 hρ1) (effDist M θ₁ (rivalIdx M)) t -
               alloc M (SPA ρ hρ0 hρ1) (effDist M θ₂ (rivalIdx M)) t) := by
            apply intervalIntegral.integral_mono_on hx.1.le intervalIntegrable_const
              ((alloc_intervalIntegrable M (SPA ρ hρ0 hρ1) _ (vs_effDist_monotoneOn θ₁ _)
                (fun z hz => effDist_nonneg θ₁ _ hz) (hp0_lt.le.trans hIin.2)
                ((hx.2.le.trans (min_le_left _ _)).trans hIin.2)).sub
               (alloc_intervalIntegrable M (SPA ρ hρ0 hρ1) _ (vs_effDist_monotoneOn θ₂ _)
                (fun z hz => effDist_nonneg θ₂ _ hz) (hp0_lt.le.trans hIin.2)
                ((hx.2.le.trans (min_le_left _ _)).trans hIin.2)))
            intro t ht
            have ht_mem : t ∈ Icc I.α I.β := ⟨hp0_ge.trans ht.1, ht.2.trans (hx.2.le.trans (min_le_left _ _))⟩
            have hdist : dist t p0 < δ := by
              rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)]
              have : t ≤ p0 + δ / 2 := ht.2.trans (hx.2.le.trans (min_le_right _ _))
              linarith
            have hFd := hδ ht_mem hdist
            rw [Real.dist_eq, hp0_zero, sub_zero] at hFd
            have hφb := (prop2_phi_props M m1 ρ hρ0 hρ1 h₁ h₂ (ht_mem.2.trans hIin.2)).2.2
            have hbound : (((M.n : ℝ) - 1) / ((M.m : ℝ) - 1)) * |dF' t| ≤ dxbar' / 2 := by
              have h1 := mul_le_mul_of_nonneg_left hFd.le
                (div_nonneg M.n_sub_one_pos_real.le M.m_sub_one_pos_real.le)
              have hcancel : (((M.n : ℝ) - 1) / ((M.m : ℝ) - 1)) *
                  (((M.m : ℝ) - 1) / (2 * ((M.n : ℝ) - 1)) * dxbar') = dxbar' / 2 := by
                have hm1 := M.m_sub_one_pos_real.ne'
                have hn1 := M.n_sub_one_pos_real.ne'
                field_simp [hm1, hn1]
              linarith
            have habs_le := le_trans hφb hbound
            exact (abs_le.mp habs_le).1
          rw [intervalIntegral.integral_const, smul_eq_mul] at hle_int
          linarith
        have hpos_half : 0 < (x - p0) * (dxbar' / 2) := mul_pos (sub_pos.mpr hx.1) (half_pos hdx')
        linarith
      -- Therefore dF' is nondecreasing on [p0, p1], contradicting p0 = sInf N
      obtain ⟨v, hvN, hvp1⟩ := exists_lt_of_csInf_lt hN_ne hp1_gt
      have hp0v : p0 ≤ v := csInf_le hN_bdd hvN
      have hmono := prop2_prop_b_pos M m1 ρ hρ0 hρ1 h₁ h₂ hp0v (hvN.1.2.le.trans hIin.2)
        (fun x hx => hdσ'_pos_near x ⟨hx.1, hx.2.trans hvp1⟩)
      have hv_neg : dF' v < 0 := hvN.2
      linarith
    -- Now dF' ≥ 0 on [I.α, I.β], so dσ' I.β > 0
    have hsub := prop2_pool_delta_sigma_sub M m1 ρ hρ0 hρ1 h₁ h₂ hI
      (left_mem_Icc.mpr I.hαβ.le) (right_mem_Icc.mpr I.hαβ.le) I.hαβ.le
    have hphi_nn : 0 ≤ ∫ t in I.α..I.β,
        (alloc M (SPA ρ hρ0 hρ1) (effDist M θ₁ (rivalIdx M)) t -
         alloc M (SPA ρ hρ0 hρ1) (effDist M θ₂ (rivalIdx M)) t) := by
      rw [intervalIntegral.integral_of_le I.hαβ.le]
      apply MeasureTheory.integral_nonneg_of_ae
      change ∀ᵐ t ∂(volume.restrict (Ioc I.α I.β)), (0 : ℝ) ≤ _
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
      filter_upwards with t ht
      have hp := prop2_phi_props M m1 ρ hρ0 hρ1 h₁ h₂ (ht.2.trans hIin.2)
      by_cases htρ : t < ρ
      · rw [hp.1 htρ]
      · push Not at htρ
        exact (hp.2.1 htρ).2.1 (hnn_all t ⟨ht.1.le, ht.2⟩)
    have hprod_pos : 0 < (I.β - I.α) * dxbar' := mul_pos (sub_pos.mpr I.hαβ) hdx'
    linarith
  -- Split by sign of ΔF(I.β)
  rcases lt_trichotomy (effDist M θ' 0 I.β - effDist M θ 0 I.β) 0 with hneg | hzero | hpos
  · right; right
    have := hpos_end θ' θ hSR' hSR (by linarith) (by linarith) (by linarith)
    exact ⟨hneg, by linarith⟩
  · -- Case 4c: ΔF(I.β) = 0 ⇒ Δxbar = 0 ⇒ ΔF = 0 and Δσ = 0 on [I.α, I.β]
    left
    have hdx0 : poolAvg M.n (effDist M θ' 0 I.α) (effDist M θ' 0 I.β) -
        poolAvg M.n (effDist M θ 0 I.α) (effDist M θ 0 I.β) = 0 := by
      have h1 : effDist M θ' 0 I.α = effDist M θ 0 I.α := sub_eq_zero.mp hFα
      have h2 : effDist M θ' 0 I.β = effDist M θ 0 I.β := sub_eq_zero.mp hzero
      rw [h1, h2, sub_self]
    have hall_F : ∀ v ∈ Icc I.α I.β, effDist M θ' 0 v - effDist M θ 0 v = 0 := by
      -- Prove neither > 0 nor < 0 can occur inside (I.α, I.β)
      have hno_pos : ∀ (θ₁ θ₂ : VisitStrategy M),
          IsSR M (unilateralProfile M m1 ρ hρ0 hρ1) θ₁ →
          IsSR M (unilateralProfile M m1 ρ hρ0 hρ1) θ₂ →
          effDist M θ₂ 0 I.α - effDist M θ₁ 0 I.α = 0 →
          effDist M θ₂ 0 I.β - effDist M θ₁ 0 I.β = 0 →
          ∀ v0 ∈ Icc I.α I.β, effDist M θ₂ 0 v0 - effDist M θ₁ 0 v0 ≤ 0 := by
        intro θ₁ θ₂ h₁ h₂ hα0 hβ0 v0 hv0
        by_contra hlt; push Not at hlt
        let dF' : ℝ → ℝ := fun v => effDist M θ₂ 0 v - effDist M θ₁ 0 v
        let dσ' : ℝ → ℝ := fun v => sigma M m1 ρ hρ0 hρ1 θ₂ v - sigma M m1 ρ hρ0 hρ1 θ₁ v
        have hdx0' : poolAvg M.n (effDist M θ₂ 0 I.α) (effDist M θ₂ 0 I.β) -
            poolAvg M.n (effDist M θ₁ 0 I.α) (effDist M θ₁ 0 I.β) = 0 := by
          rw [sub_eq_zero.mp hα0, sub_eq_zero.mp hβ0, sub_self]
        have hv0_gt_ρ : ρ < v0 := by
          by_contra hle; push Not at hle
          have hc := prop2_prop_a M m1 ρ hρ0 hρ1 h₁ h₂
            ⟨hmin_α, hv0.1.trans hle⟩ ⟨hmin_α.trans hv0.1, hle⟩
          linarith
        have hv0_gt_α : I.α < v0 := lt_of_le_of_ne hv0.1 (fun h => by rw [← h] at hlt; linarith)
        have hcont : ContinuousOn dF' (Icc I.α I.β) :=
          ((effDist_continuousOn θ₂ 0).mono (fun t (ht : t ∈ Icc I.α I.β) => ht.2.trans hIin.2)).sub
            ((effDist_continuousOn θ₁ 0).mono (fun t (ht : t ∈ Icc I.α I.β) => ht.2.trans hIin.2))
        let Z : Set ℝ := {v ∈ Icc I.α v0 | dF' v = 0}
        have hZ_ne : Z.Nonempty := ⟨I.α, left_mem_Icc.mpr hv0_gt_α.le, hα0⟩
        have hZ_bdd : BddAbove Z := ⟨v0, fun v hv => hv.1.2⟩
        let y1 := sSup Z
        have hy1_mem : y1 ∈ Icc I.α v0 := ⟨le_csSup hZ_bdd ⟨left_mem_Icc.mpr hv0_gt_α.le, hα0⟩,
          csSup_le hZ_ne (fun v hv => hv.1.2)⟩
        have hy1_ge_ρ : ρ ≤ y1 := by
          by_cases hαρ : I.α ≤ ρ
          · have hρ_zero : dF' ρ = 0 := by
              have hc := prop2_prop_a M m1 ρ hρ0 hρ1 h₁ h₂ ⟨hmin_α, hαρ⟩ ⟨hmin_α.trans hαρ, le_rfl⟩
              linarith
            exact le_csSup hZ_bdd ⟨⟨hαρ, hv0_gt_ρ.le⟩, hρ_zero⟩
          · push Not at hαρ; exact hαρ.le.trans hy1_mem.1
        have hy1_zero : dF' y1 = 0 := by
          have hcl : y1 ∈ closure Z := csSup_mem_closure hZ_ne hZ_bdd
          have hZ_closed : IsClosed Z := by
            have : Z = Icc I.α v0 ∩ dF' ⁻¹' {0} := by ext v; simp [Z]
            rw [this]
            exact (hcont.mono (Icc_subset_Icc_right hv0.2)).preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
          rw [hZ_closed.closure_eq] at hcl; exact hcl.2
        have hy1_lt : y1 < v0 := lt_of_le_of_ne hy1_mem.2 (fun h => by rw [h] at hy1_zero; linarith)
        have hdF'_pos : ∀ x ∈ Ioc y1 v0, 0 < dF' x := by
          intro x hx
          by_contra hle'; push Not at hle'
          rcases eq_or_lt_of_le hle' with h0' | hneg'
          · exact not_le.mpr hx.1 (le_csSup hZ_bdd ⟨⟨hy1_mem.1.trans hx.1.le, hx.2⟩, h0'⟩)
          · obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc hx.2
              (hcont.mono (Icc_subset_Icc (hy1_mem.1.trans hx.1.le) hv0.2)) ⟨hneg'.le, hlt.le⟩
            exact not_lt.mpr (le_csSup hZ_bdd ⟨⟨hy1_mem.1.trans (hx.1.le.trans hz.1), hz.2⟩, hz0⟩)
              (lt_of_lt_of_le hx.1 hz.1)
        have hdσ'_v0 : 0 < dσ' v0 := by
          by_contra hle'; push Not at hle'
          have hdσ'_neg : ∀ x ∈ Ioo y1 v0, dσ' x < 0 := by
            intro x hx
            have hsub := prop2_pool_delta_sigma_sub M m1 ρ hρ0 hρ1 h₁ h₂ hI
              ⟨hy1_mem.1.trans hx.1.le, hx.2.le.trans hv0.2⟩ hv0 hx.2.le
            have hphi_pos := prop2_phi_integral_pos M m1 ρ hρ0 hρ1 h₁ h₂
              (hy1_ge_ρ.trans hx.1.le) hx.2 (hv0.2.trans hIin.2)
              (fun t ht => hdF'_pos t ⟨hx.1.trans ht.1, ht.2.le⟩)
            rw [hdx0', mul_zero, zero_add] at hsub
            linarith
          have hanti := prop2_prop_b_neg M m1 ρ hρ0 hρ1 h₁ h₂ hy1_lt.le (hv0.2.trans hIin.2) hdσ'_neg
          linarith
        -- Now push forward from v0 to I.β using S = {v ∈ [v0, I.β] | dF' > 0 on [v0, v]}
        let S : Set ℝ := {v ∈ Icc v0 I.β | ∀ x ∈ Icc v0 v, 0 < dF' x}
        have hS_ne : S.Nonempty := ⟨v0, left_mem_Icc.mpr hv0.2, fun x hx => by
          have : x = v0 := le_antisymm hx.2 hx.1; rw [this]; exact hlt⟩
        have hS_bdd : BddAbove S := ⟨I.β, fun v hv => hv.1.2⟩
        let c := sSup S
        have hc_ge : v0 ≤ c := le_csSup hS_bdd ⟨left_mem_Icc.mpr hv0.2, fun x hx => by
          have : x = v0 := le_antisymm hx.2 hx.1; rw [this]; exact hlt⟩
        have hc_le : c ≤ I.β := csSup_le hS_ne (fun v hv => hv.1.2)
        have hdF'_pos_c : ∀ x ∈ Ico v0 c, 0 < dF' x := by
          intro x hx
          obtain ⟨v, hvS, hxv⟩ := exists_lt_of_lt_csSup hS_ne hx.2
          exact hvS.2 x ⟨hx.1, hxv.le⟩
        have hdσ'_pos_c : ∀ x ∈ Ioo v0 c, 0 < dσ' x := by
          intro x hx
          have hsub := prop2_pool_delta_sigma_sub M m1 ρ hρ0 hρ1 h₁ h₂ hI
            hv0 ⟨hv0.1.trans hx.1.le, hx.2.le.trans hc_le⟩ hx.1.le
          have hphi_pos := prop2_phi_integral_pos M m1 ρ hρ0 hρ1 h₁ h₂
            hv0_gt_ρ.le hx.1 ((hx.2.le.trans hc_le).trans hIin.2)
            (fun t ht => hdF'_pos_c t ⟨ht.1.le, ht.2.trans hx.2⟩)
          rw [hdx0', mul_zero, zero_add] at hsub
          linarith
        have hdF'_c : dF' v0 ≤ dF' c := by
          rcases eq_or_lt_of_le hc_ge with heq | hlt_c
          · rw [← heq]
          · exact prop2_prop_b_pos M m1 ρ hρ0 hρ1 h₁ h₂ hlt_c.le (hc_le.trans hIin.2) hdσ'_pos_c
        have hc_eq : c = I.β := by
          by_contra hne
          have hclt : c < I.β := lt_of_le_of_ne hc_le hne
          have hc_pos : 0 < dF' c := lt_of_lt_of_le hlt hdF'_c
          obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousWithinAt_iff.mp
            (hcont c ⟨hv0.1.trans hc_ge, hc_le⟩) (dF' c / 2) (half_pos hc_pos)
          let c' := min I.β (c + δ / 2)
          have hc'_gt : c < c' := lt_min hclt (by linarith)
          have hc'_mem : c' ∈ S := by
            refine ⟨⟨hc_ge.trans hc'_gt.le, min_le_left _ _⟩, fun x hx => ?_⟩
            by_cases hxc : x < c
            · exact hdF'_pos_c x ⟨hx.1, hxc⟩
            · push Not at hxc
              have hdist : dist x c < δ := by
                rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hxc)]
                have : x ≤ c + δ / 2 := hx.2.trans (min_le_right _ _)
                linarith
              have h1' := hδ ⟨hv0.1.trans hx.1, hx.2.trans (min_le_left _ _)⟩ hdist
              rw [Real.dist_eq] at h1'; linarith [(abs_lt.mp h1').1]
          exact not_lt.mpr (le_csSup hS_bdd hc'_mem) hc'_gt
        rw [hc_eq] at hdF'_c; linarith
      intro v hv
      have h1 := hno_pos θ θ' hSR hSR' hFα hzero v hv
      have h2 := hno_pos θ' θ hSR' hSR (by linarith) (by linarith) v hv
      linarith
    intro v hv
    refine ⟨hall_F v hv, ?_⟩
    have hsub := prop2_pool_delta_sigma_sub M m1 ρ hρ0 hρ1 hSR hSR' hI
      (left_mem_Icc.mpr I.hαβ.le) hv hv.1
    have hphi0 : ∫ t in I.α..v,
        (alloc M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) t -
         alloc M (SPA ρ hρ0 hρ1) (effDist M θ' (rivalIdx M)) t) = 0 := by
      have hcongr : ∫ t in I.α..v,
          (alloc M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) t -
           alloc M (SPA ρ hρ0 hρ1) (effDist M θ' (rivalIdx M)) t) =
          ∫ _ in I.α..v, (0 : ℝ) := by
        apply intervalIntegral.integral_congr; intro t ht; dsimp only
        rw [uIcc_of_le hv.1] at ht
        have hp := prop2_phi_props M m1 ρ hρ0 hρ1 hSR hSR' ((ht.2.trans hv.2).trans hIin.2)
        have hF0 := hall_F t ⟨ht.1, ht.2.trans hv.2⟩
        by_cases htρ : t < ρ
        · exact hp.1 htρ
        · push Not at htρ
          exact le_antisymm ((hp.2.1 htρ).2.2.1 hF0.le) ((hp.2.1 htρ).2.1 hF0.ge)
      rw [hcongr]; simp
    rw [hdx0, mul_zero, zero_add, hphi0] at hsub
    linarith
  · right; left
    exact ⟨hpos, hpos_end θ θ' hSR hSR' hFα hσα hpos⟩

/-- Step 5a: induction along sorted disjoint pools showing a signed pair at `u` stays signed at `1`,
contradicting `ΔF(1) = 0`. -/
private lemma prop2_signed_contradiction (ps : List Pool) :
    ∀ u : ℝ, min m1.r ρ ≤ u → u ≤ 1 →
      (∀ I ∈ ps, I ∈ m1.pools ∧ u ≤ I.α) →
      ps.Pairwise (fun I J => I.β ≤ J.α) →
      (∀ I ∈ m1.pools, ∀ t ∈ Ioo u 1, (I.α < t ∧ t < I.β) → I ∈ ps) →
      ((0 < effDist M θ' 0 u - effDist M θ 0 u ∧
        0 ≤ sigma M m1 ρ hρ0 hρ1 θ' u - sigma M m1 ρ hρ0 hρ1 θ u) ∨
       (effDist M θ' 0 u - effDist M θ 0 u < 0 ∧
        sigma M m1 ρ hρ0 hρ1 θ' u - sigma M m1 ρ hρ0 hρ1 θ u ≤ 0)) →
      False := by
  induction ps with
  | nil =>
    intro u hmin hu1 _ _ hcover hsign
    have hgap : ∀ I ∈ m1.pools, ∀ t ∈ Ioo u 1, ¬ (I.α < t ∧ t < I.β) :=
      fun I hI t ht h => by simpa using hcover I hI t ht h
    have h1 : effDist M θ' 0 1 - effDist M θ 0 1 = 0 := by rw [vs_effDist_one, vs_effDist_one, sub_self]
    rcases hsign with ⟨hF, hσ⟩ | ⟨hF, hσ⟩
    · have := (prop2_step1_gap_pos M m1 ρ hρ0 hρ1 hSR hSR' hmin hu1 le_rfl hgap hF hσ).1
      linarith
    · have := (prop2_step1_gap_pos M m1 ρ hρ0 hρ1 hSR' hSR hmin hu1 le_rfl hgap
        (by linarith) (by linarith)).1
      linarith
  | cons I rest ih =>
    intro u hmin hu1 hps_in hpair hcover hsign
    have hI_in : I ∈ m1.pools := (hps_in I (List.mem_cons_self ..)).1
    have hu_Iα : u ≤ I.α := (hps_in I (List.mem_cons_self ..)).2
    have hI_bounds := m1.hpools_in I hI_in
    have hIα1 : I.α ≤ 1 := I.hαβ.le.trans hI_bounds.2
    have hpair_cons := List.pairwise_cons.mp hpair
    -- No pool meets (u, I.α)
    have hgap : ∀ J ∈ m1.pools, ∀ t ∈ Ioo u I.α, ¬ (J.α < t ∧ t < J.β) := by
      intro J hJ t ht hJt
      have hJmem := hcover J hJ t ⟨ht.1, ht.2.trans_le hIα1⟩ hJt
      rcases List.mem_cons.mp hJmem with rfl | hJrest
      · linarith [ht.2, hJt.1]
      · have := hpair_cons.1 J hJrest
        linarith [I.hαβ, ht.2, hJt.1]
    -- Propagate sign from u to I.α, then across I to I.β
    have hsign_α :
        (0 < effDist M θ' 0 I.α - effDist M θ 0 I.α ∧
         0 ≤ sigma M m1 ρ hρ0 hρ1 θ' I.α - sigma M m1 ρ hρ0 hρ1 θ I.α) ∨
        (effDist M θ' 0 I.α - effDist M θ 0 I.α < 0 ∧
         sigma M m1 ρ hρ0 hρ1 θ' I.α - sigma M m1 ρ hρ0 hρ1 θ I.α ≤ 0) := by
      rcases hsign with ⟨hF, hσ⟩ | ⟨hF, hσ⟩
      · have h1 := prop2_step1_gap_pos M m1 ρ hρ0 hρ1 hSR hSR' hmin hu_Iα hIα1 hgap hF hσ
        exact Or.inl ⟨h1.1, h1.2.2⟩
      · have h1 := prop2_step1_gap_pos M m1 ρ hρ0 hρ1 hSR' hSR hmin hu_Iα hIα1 hgap
          (by linarith) (by linarith)
        exact Or.inr ⟨by linarith [h1.1], by linarith [h1.2.2]⟩
    have hsign_β :
        (0 < effDist M θ' 0 I.β - effDist M θ 0 I.β ∧
         0 ≤ sigma M m1 ρ hρ0 hρ1 θ' I.β - sigma M m1 ρ hρ0 hρ1 θ I.β) ∨
        (effDist M θ' 0 I.β - effDist M θ 0 I.β < 0 ∧
         sigma M m1 ρ hρ0 hρ1 θ' I.β - sigma M m1 ρ hρ0 hρ1 θ I.β ≤ 0) := by
      rcases hsign_α with ⟨hF, hσ⟩ | ⟨hF, hσ⟩
      · rcases prop2_step2_pool_pos M m1 ρ hρ0 hρ1 hSR hSR' hI_in hF hσ with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1, h2.le⟩
        · exact Or.inr ⟨h1, h2.le⟩
      · rcases prop2_step2_pool_pos M m1 ρ hρ0 hρ1 hSR' hSR hI_in (by linarith) (by linarith) with
            ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inr ⟨by linarith, by linarith⟩
        · exact Or.inl ⟨by linarith, by linarith⟩
    refine ih I.β (hmin.trans (hu_Iα.trans I.hαβ.le)) hI_bounds.2 ?_ hpair_cons.2 ?_ hsign_β
    · intro J hJ
      exact ⟨(hps_in J (List.mem_cons_of_mem _ hJ)).1, hpair_cons.1 J hJ⟩
    · intro J hJ t ht hJt
      have hJmem := hcover J hJ t ⟨(hu_Iα.trans I.hαβ.le).trans_lt ht.1, ht.2⟩ hJt
      rcases List.mem_cons.mp hJmem with rfl | hJrest
      · linarith [ht.1, hJt.2]
      · exact hJrest

/-- Step 5b: induction along sorted disjoint pools showing a pair at rest stays at rest on `[u, 1]`. -/
private lemma prop2_rest_everywhere (ps : List Pool) :
    ∀ u : ℝ, min m1.r ρ ≤ u → u ≤ 1 →
      (∀ I ∈ ps, I ∈ m1.pools ∧ u ≤ I.α) →
      ps.Pairwise (fun I J => I.β ≤ J.α) →
      (∀ I ∈ m1.pools, ∀ t ∈ Ioo u 1, (I.α < t ∧ t < I.β) → I ∈ ps) →
      effDist M θ' 0 u - effDist M θ 0 u = 0 →
      sigma M m1 ρ hρ0 hρ1 θ' u - sigma M m1 ρ hρ0 hρ1 θ u = 0 →
      ∀ v ∈ Icc u 1, effDist M θ' 0 v - effDist M θ 0 v = 0 ∧
        sigma M m1 ρ hρ0 hρ1 θ' v - sigma M m1 ρ hρ0 hρ1 θ v = 0 := by
  induction ps with
  | nil =>
    intro u hmin hu1 _ _ hcover hFu hσu
    have hgap : ∀ I ∈ m1.pools, ∀ t ∈ Ioo u 1, ¬ (I.α < t ∧ t < I.β) :=
      fun I hI t ht h => by simpa using hcover I hI t ht h
    have h1 : effDist M θ' 0 1 - effDist M θ 0 1 = 0 := by rw [vs_effDist_one, vs_effDist_one, sub_self]
    rcases prop2_step3_gap_rest M m1 ρ hρ0 hρ1 hSR hSR' hmin hu1 le_rfl hgap hFu hσu with
        hall | ⟨hF, _⟩ | ⟨hF, _⟩
    · exact hall
    · exfalso; linarith
    · exfalso; linarith
  | cons I rest ih =>
    intro u hmin hu1 hps_in hpair hcover hFu hσu
    have hI_in : I ∈ m1.pools := (hps_in I (List.mem_cons_self ..)).1
    have hu_Iα : u ≤ I.α := (hps_in I (List.mem_cons_self ..)).2
    have hI_bounds := m1.hpools_in I hI_in
    have hIα1 : I.α ≤ 1 := I.hαβ.le.trans hI_bounds.2
    have hpair_cons := List.pairwise_cons.mp hpair
    have hgap : ∀ J ∈ m1.pools, ∀ t ∈ Ioo u I.α, ¬ (J.α < t ∧ t < J.β) := by
      intro J hJ t ht hJt
      have hJmem := hcover J hJ t ⟨ht.1, ht.2.trans_le hIα1⟩ hJt
      rcases List.mem_cons.mp hJmem with rfl | hJrest
      · linarith [ht.2, hJt.1]
      · have := hpair_cons.1 J hJrest; linarith [I.hαβ, ht.2, hJt.1]
    have hrest_gap : ∀ v ∈ Icc u I.α, effDist M θ' 0 v - effDist M θ 0 v = 0 ∧
        sigma M m1 ρ hρ0 hρ1 θ' v - sigma M m1 ρ hρ0 hρ1 θ v = 0 := by
      rcases prop2_step3_gap_rest M m1 ρ hρ0 hρ1 hSR hSR' hmin hu_Iα hIα1 hgap hFu hσu with
          hall | ⟨hF, hσ⟩ | ⟨hF, hσ⟩
      · exact hall
      · exfalso
        exact prop2_signed_contradiction M m1 ρ hρ0 hρ1 hSR hSR' (I :: rest) I.α
          (hmin.trans hu_Iα) hIα1
          (fun J hJ => by
            rcases List.mem_cons.mp hJ with rfl | hJr
            · exact ⟨hI_in, le_rfl⟩
            · exact ⟨(hps_in J (List.mem_cons_of_mem _ hJr)).1, I.hαβ.le.trans (hpair_cons.1 J hJr)⟩)
          hpair
          (fun J hJ t ht hJt => hcover J hJ t ⟨hu_Iα.trans_lt ht.1, ht.2⟩ hJt)
          (Or.inl ⟨hF, hσ.le⟩)
      · exfalso
        exact prop2_signed_contradiction M m1 ρ hρ0 hρ1 hSR hSR' (I :: rest) I.α
          (hmin.trans hu_Iα) hIα1
          (fun J hJ => by
            rcases List.mem_cons.mp hJ with rfl | hJr
            · exact ⟨hI_in, le_rfl⟩
            · exact ⟨(hps_in J (List.mem_cons_of_mem _ hJr)).1, I.hαβ.le.trans (hpair_cons.1 J hJr)⟩)
          hpair
          (fun J hJ t ht hJt => hcover J hJ t ⟨hu_Iα.trans_lt ht.1, ht.2⟩ hJt)
          (Or.inr ⟨hF, hσ.le⟩)
    have hα_rest := hrest_gap I.α (right_mem_Icc.mpr hu_Iα)
    have hrest_in : ∀ J ∈ rest, J ∈ m1.pools ∧ I.β ≤ J.α := fun J hJ =>
      ⟨(hps_in J (List.mem_cons_of_mem _ hJ)).1, hpair_cons.1 J hJ⟩
    have hrest_cover : ∀ J ∈ m1.pools, ∀ t ∈ Ioo I.β 1, (J.α < t ∧ t < J.β) → J ∈ rest := by
      intro J hJ t ht hJt
      have hJmem := hcover J hJ t ⟨(hu_Iα.trans I.hαβ.le).trans_lt ht.1, ht.2⟩ hJt
      rcases List.mem_cons.mp hJmem with rfl | hJr
      · linarith [ht.1, hJt.2]
      · exact hJr
    have hrest_pool : ∀ v ∈ Icc I.α I.β, effDist M θ' 0 v - effDist M θ 0 v = 0 ∧
        sigma M m1 ρ hρ0 hρ1 θ' v - sigma M m1 ρ hρ0 hρ1 θ v = 0 := by
      rcases prop2_step4_pool_rest M m1 ρ hρ0 hρ1 hSR hSR' hI_in hα_rest.1 hα_rest.2 with
          hall | ⟨hF, hσ⟩ | ⟨hF, hσ⟩
      · exact hall
      · exfalso
        exact prop2_signed_contradiction M m1 ρ hρ0 hρ1 hSR hSR' rest I.β
          (hmin.trans (hu_Iα.trans I.hαβ.le)) hI_bounds.2 hrest_in hpair_cons.2 hrest_cover
          (Or.inl ⟨hF, hσ.le⟩)
      · exfalso
        exact prop2_signed_contradiction M m1 ρ hρ0 hρ1 hSR hSR' rest I.β
          (hmin.trans (hu_Iα.trans I.hαβ.le)) hI_bounds.2 hrest_in hpair_cons.2 hrest_cover
          (Or.inr ⟨hF, hσ.le⟩)
    have hβ_rest := hrest_pool I.β (right_mem_Icc.mpr I.hαβ.le)
    have hrest_tail := ih I.β (hmin.trans (hu_Iα.trans I.hαβ.le)) hI_bounds.2
      hrest_in hpair_cons.2 hrest_cover hβ_rest.1 hβ_rest.2
    intro v hv
    by_cases hv1 : v ≤ I.α
    · exact hrest_gap v ⟨hv.1, hv1⟩
    · push Not at hv1
      by_cases hv2 : v ≤ I.β
      · exact hrest_pool v ⟨hv1.le, hv2⟩
      · push Not at hv2
        exact hrest_tail v ⟨hv2.le, hv.2⟩

end SignPropagation

/-- Helper: sort `m1.pools` in ascending order of `α` while preserving disjointness `I.β ≤ J.α`. -/
lemma sorted_pools_props (m1 : HierarchicalMech) :
    ∃ ps : List Pool,
      (∀ I, I ∈ ps ↔ I ∈ m1.pools) ∧
      ps.Pairwise (fun I J => I.β ≤ J.α) := by
  let le_α : Pool → Pool → Bool := fun I J => decide (I.α ≤ J.α)
  let ps := m1.pools.mergeSort le_α
  have hperm : ps.Perm m1.pools := List.mergeSort_perm m1.pools le_α
  have hmem : ∀ I, I ∈ ps ↔ I ∈ m1.pools := fun I => hperm.mem_iff
  have hsorted : ps.Pairwise (fun I J => le_α I J = true) := by
    refine List.pairwise_mergeSort (le := le_α) ?_ ?_ m1.pools
    · intro a b c hab hbc
      simp only [le_α, decide_eq_true_eq] at hab hbc ⊢; exact hab.trans hbc
    · intro a b
      simp only [le_α, Bool.or_eq_true, decide_eq_true_eq]; exact le_total a.α b.α
  have hdisj : ps.Pairwise (fun I J => I.β ≤ J.α ∨ J.β ≤ I.α) :=
    (hperm.pairwise_iff (fun {a b} h => Or.symm h)).mpr m1.hpools_disj
  have hpair : ps.Pairwise (fun I J => I.β ≤ J.α) := by
    refine (hsorted.and hdisj).imp fun {I J} ⟨hle, hd⟩ => ?_
    simp only [le_α, decide_eq_true_eq] at hle
    rcases hd with h | h
    · exact h
    · exfalso; linarith [I.hαβ, J.hαβ]
  exact ⟨ps, hmem, hpair⟩

/-- **Proposition 2(ii) (Uniqueness)**: Against rivals at `SPA(ρ)` and seller 1 at any
`m1 ∈ M`, every SR continuation induces the same `F₁` on `[min r₁ ρ, 1]`, the same `F_riv`
on `[ρ, 1]`, the same surpluses on `[0, 1]`, and the same visit probabilities a.e. above
`max (min r₁ ρ) a`. -/
theorem prop2_uniqueness (m1 : HierarchicalMech) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    {θ θ' : VisitStrategy M}
    (hSR : IsSR M (unilateralProfile M m1 ρ hρ0 hρ1) θ)
    (hSR' : IsSR M (unilateralProfile M m1 ρ hρ0 hρ1) θ') :
    (∀ v ∈ Icc (min m1.r ρ) 1, effDist M θ' 0 v = effDist M θ 0 v) ∧
    (∀ j : Fin M.m, j ≠ 0 → ∀ v ∈ Icc ρ 1, effDist M θ' j v = effDist M θ j v) ∧
    (∀ j : Fin M.m, ∀ᵐ v ∂(volume.restrict (Icc (max (min m1.r ρ) M.a) 1)),
      θ'.θ j v = θ.θ j v) := by
  obtain ⟨ps, hps_mem, hps_pair⟩ := sorted_pools_props m1
  let rmin := min m1.r ρ
  have hrmin1 : rmin ≤ 1 := min_le_of_left_le m1.hr1
  have hps_in : ∀ I ∈ ps, I ∈ m1.pools ∧ rmin ≤ I.α := fun I hI =>
    ⟨(hps_mem I).mp hI, min_le_of_left_le (m1.hpools_in I ((hps_mem I).mp hI)).1⟩
  have hps_cover : ∀ I ∈ m1.pools, ∀ t ∈ Ioo rmin 1, (I.α < t ∧ t < I.β) → I ∈ ps :=
    fun I hI _ _ _ => (hps_mem I).mpr hI
  have hσ_min : sigma M m1 ρ hρ0 hρ1 θ' rmin - sigma M m1 ρ hρ0 hρ1 θ rmin = 0 := by
    rw [sigma_zero_at_rmin M m1 ρ hρ0 hρ1 hSR', sigma_zero_at_rmin M m1 ρ hρ0 hρ1 hSR, sub_self]
  have hF_min : effDist M θ' 0 rmin - effDist M θ 0 rmin = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · exact prop2_signed_contradiction M m1 ρ hρ0 hρ1 hSR hSR' ps rmin le_rfl hrmin1
        hps_in hps_pair hps_cover (Or.inr ⟨hneg, hσ_min.le⟩)
    · exact prop2_signed_contradiction M m1 ρ hρ0 hρ1 hSR hSR' ps rmin le_rfl hrmin1
        hps_in hps_pair hps_cover (Or.inl ⟨hpos, hσ_min.ge⟩)
  have hall := prop2_rest_everywhere M m1 ρ hρ0 hρ1 hSR hSR' ps rmin le_rfl hrmin1
    hps_in hps_pair hps_cover hF_min hσ_min
  have hF1_eq : ∀ v ∈ Icc rmin 1, effDist M θ' 0 v = effDist M θ 0 v := fun v hv =>
    sub_eq_zero.mp (hall v hv).1
  have hFriv_eq : ∀ j : Fin M.m, j ≠ 0 → ∀ v ∈ Icc ρ 1, effDist M θ' j v = effDist M θ j v := by
    intro j hj v hv
    rw [(prop2_rival_symmetry M m1 ρ hρ0 hρ1 hSR').2 j hj v hv,
        (prop2_rival_symmetry M m1 ρ hρ0 hρ1 hSR).2 j hj v hv]
    unfold FrivOf
    rw [hF1_eq v ⟨(min_le_right _ _).trans hv.1, hv.2⟩]
  refine ⟨hF1_eq, hFriv_eq, fun j => ?_⟩
  -- Deduce θ'_j = θ_j a.e. on [max rmin a, 1] via Lebesgue differentiation
  let c := max rmin M.a
  have hc1 : c ≤ 1 := max_le hrmin1 M.ha1.le
  have hdiff_int : IntervalIntegrable (fun t => (θ'.θ j t - θ.θ j t) * M.f t) volume c 1 := by
    have hsub := (θ'.mul_f_intervalIntegrable j hc1 le_rfl).sub (θ.mul_f_intervalIntegrable j hc1 le_rfl)
    have hfun : (fun t => θ'.θ j t * M.f t - θ.θ j t * M.f t) =
        (fun t => (θ'.θ j t - θ.θ j t) * M.f t) := by ext t; ring
    rwa [hfun] at hsub
  have hzero_int : ∀ x ∈ Icc c 1, ∫ t in c..x, (θ'.θ j t - θ.θ j t) * M.f t = 0 := by
    intro x hx
    have hfun : (fun t => (θ'.θ j t - θ.θ j t) * M.f t) =
        (fun t => θ'.θ j t * M.f t - θ.θ j t * M.f t) := by ext t; ring
    rw [hfun, intervalIntegral.integral_sub (θ'.mul_f_intervalIntegrable j hc1 hx.2)
      (θ.mul_f_intervalIntegrable j hc1 hx.2),
      ← effDist_sub θ' j hc1 hx.2, ← effDist_sub θ j hc1 hx.2]
    by_cases hj0 : j = 0
    · subst hj0
      rw [hF1_eq x ⟨(le_max_left _ _).trans hx.1, hx.2⟩,
          hF1_eq c ⟨le_max_left _ _, hc1⟩]
      ring
    · -- For rival j ≠ 0: above ρ we have hFriv_eq; below ρ (when r₁ < ρ), both θ_j and θ'_j are 0 a.e.!
      -- Even simpler: prove effDist M θ' j v = effDist M θ j v for all v ∈ [rmin, 1]!
      have hFj_eq : ∀ v ∈ Icc rmin 1, effDist M θ' j v = effDist M θ j v := by
        intro v hv
        by_cases hvρ : ρ ≤ v
        · exact hFriv_eq j hj0 v ⟨hvρ, hv.2⟩
        · push Not at hvρ
          have hrlt : m1.r < ρ := by
            rcases min_cases m1.r ρ with ⟨h, _⟩ | ⟨h, _⟩
            · linarith [hv.1]
            · linarith [hv.1]
          -- On [v, ρ], θ_0 = 1 a.e. so θ_j = 0 a.e., hence effDist j v = effDist j ρ!
          have hconst : ∀ (θ₀ : VisitStrategy M),
              IsSR M (unilateralProfile M m1 ρ hρ0 hρ1) θ₀ →
              effDist M θ₀ j v = effDist M θ₀ j ρ := by
            intro θ₀ hSR₀
            have h1 := (prop2_below_rho_seller1_captures M m1 ρ hρ0 hρ1 hSR₀ hrlt).2
              v ⟨hv.1, hvρ.le⟩ ρ ⟨min_le_right _ _, le_rfl⟩
            have hsum_v := effDist_sum_one_sub θ₀ (hvρ.le.trans hρ1)
            have hsum_ρ := effDist_sum_one_sub θ₀ hρ1
            have hdiff_sum : ∑ k : Fin M.m, (effDist M θ₀ k ρ - effDist M θ₀ k v) =
                M.F ρ - M.F v := by
              rw [Finset.sum_sub_distrib] at hsum_v hsum_ρ ⊢
              linarith
            have h0mem : (0 : Fin M.m) ∈ (Finset.univ : Finset (Fin M.m)) := Finset.mem_univ _
            rw [← Finset.add_sum_erase _ _ h0mem, h1] at hdiff_sum
            have hrem0 : ∑ k ∈ Finset.univ.erase (0 : Fin M.m),
                (effDist M θ₀ k ρ - effDist M θ₀ k v) = 0 := by linarith
            have hterm_nn : ∀ k ∈ Finset.univ.erase (0 : Fin M.m),
                0 ≤ effDist M θ₀ k ρ - effDist M θ₀ k v := fun k _ =>
              sub_nonneg.mpr (vs_effDist_monotoneOn θ₀ k (hvρ.le.trans hρ1) hρ1 hvρ.le)
            have hjmem : j ∈ Finset.univ.erase (0 : Fin M.m) := Finset.mem_erase.mpr ⟨hj0, Finset.mem_univ j⟩
            have hj0' := (Finset.sum_eq_zero_iff_of_nonneg hterm_nn).mp hrem0 j hjmem
            linarith
          rw [hconst θ' hSR', hconst θ hSR, hFriv_eq j hj0 ρ (left_mem_Icc.mpr hρ1)]
      rw [hFj_eq x ⟨(le_max_left _ _).trans hx.1, hx.2⟩,
          hFj_eq c ⟨le_max_left _ _, hc1⟩]
      ring
  have hae := ae_eq_zero_of_forall_integral_eq_zero hc1 hdiff_int hzero_int
  filter_upwards [hae, MeasureTheory.ae_restrict_mem measurableSet_Icc] with v hv hmem
  have hfpos : 0 < M.f v := M.hf_pos v ⟨(le_max_right _ _).trans hmem.1, hmem.2⟩
  have h0 := (mul_eq_zero.mp hv).resolve_right hfpos.ne'
  linarith

/-! #### Proposition 2(iii) and Lemma A.4: Localization and Sub-Interval Structure -/

/-- If `σ > 0` on `(x, y)`, then `θ_0 = 1` a.e. on `[max x a, y]` and every rival's `effDist`
is constant on `[x, y]`. -/
lemma prop2_sigma_pos_on_Ioo (m1 : HierarchicalMech) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    {θ : VisitStrategy M} (hSR : IsSR M (unilateralProfile M m1 ρ hρ0 hρ1) θ)
    {x y : ℝ} (hxy : x ≤ y) (hy1 : y ≤ 1)
    (hpos : ∀ t ∈ Ioo x y, 0 < sigma M m1 ρ hρ0 hρ1 θ t) :
    (∀ᵐ t ∂(volume.restrict (Icc (max x M.a) y)), θ.θ 0 t = 1) ∧
    (∀ j : Fin M.m, j ≠ 0 → ∀ u ∈ Icc x y, ∀ v ∈ Icc x y, effDist M θ j u = effDist M θ j v) := by
  have hae_one : ∀ᵐ t ∂(volume.restrict (Icc (max x M.a) y)), θ.θ 0 t = 1 := by
    have hSR_ae := (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mp hSR
    have hne_x : ∀ᵐ t ∂volume, t ≠ x := by simp [ae_iff, measure_singleton]
    have hne_y : ∀ᵐ t ∂volume, t ≠ y := by simp [ae_iff, measure_singleton]
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hSR_ae, hne_x, hne_y] with t ht htx hty hmem
    have hmemIcc : t ∈ Icc M.a 1 := ⟨(le_max_right _ _).trans hmem.1, hmem.2.trans hy1⟩
    have ht_oo : t ∈ Ioo x y := ⟨lt_of_le_of_ne ((le_max_left _ _).trans hmem.1) (Ne.symm htx),
      lt_of_le_of_ne hmem.2 hty⟩
    have hsig := hpos t ht_oo
    have hsum := θ.hsum t hmemIcc
    have h0mem : (0 : Fin M.m) ∈ (Finset.univ : Finset (Fin M.m)) := Finset.mem_univ _
    rw [← Finset.add_sum_erase _ _ h0mem] at hsum
    have hriv0 : ∀ j ∈ Finset.univ.erase (0 : Fin M.m), θ.θ j t = 0 := by
      intro j hj
      have hjne : j ≠ 0 := Finset.ne_of_mem_erase hj
      by_contra hne0
      have hjpos : 0 < θ.θ j t := lt_of_le_of_ne (θ.hnonneg j t) (Ne.symm hne0)
      have hle := ht hmemIcc j 0 hjpos
      simp only [unilateralProfile, ite_true, ite_eq_right_iff.mpr (fun h => absurd h hjne)] at hle
      rw [prop2_rival_surplus_eq M m1 ρ hρ0 hρ1 hSR hjne (M.ha0.trans hmemIcc.1) hmemIcc.2] at hle
      unfold sigma at hsig; linarith
    rw [Finset.sum_eq_zero hriv0, add_zero] at hsum
    exact hsum
  refine ⟨hae_one, fun j hj u hu v hv => ?_⟩
  have hconst_x : ∀ z ∈ Icc x y, effDist M θ j z = effDist M θ j x := by
    intro z hz
    have hsub := effDist_sub θ j (hxy.trans hy1) (hz.2.trans hy1)
    suffices h0 : ∫ t in x..z, θ.θ j t * M.f t = 0 by linarith
    have hcongr : ∫ t in x..z, θ.θ j t * M.f t = ∫ _ in x..z, (0 : ℝ) := by
      apply intervalIntegral.integral_congr_ae
      have hae_univ := (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mp hae_one
      filter_upwards [hae_univ] with t ht hmem
      rw [uIoc_of_le hz.1] at hmem
      by_cases hta : t < M.a
      · rw [M.hf_below t hta, mul_zero]
      · push Not at hta
        have hθ0 : θ.θ 0 t = 1 := ht ⟨max_le hmem.1.le hta, hmem.2.trans hz.2⟩
        have hsum := θ.hsum t ⟨hta, (hmem.2.trans hz.2).trans hy1⟩
        have h0mem : (0 : Fin M.m) ∈ (Finset.univ : Finset (Fin M.m)) := Finset.mem_univ _
        rw [← Finset.add_sum_erase _ _ h0mem, hθ0] at hsum
        have hrem0 : ∑ k ∈ Finset.univ.erase (0 : Fin M.m), θ.θ k t = 0 := by linarith
        have hj0 : θ.θ j t = 0 := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => θ.hnonneg k t)).mp
          hrem0 j (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
        rw [hj0, zero_mul]
    rw [hcongr]; simp
  rw [hconst_x u hu, hconst_x v hv]

/-- If `σ < 0` on `(x, y)`, then `θ_0 = 0` a.e. on `[max x a, y]` and `effDist M θ 0` is constant
on `[x, y]`. -/
lemma prop2_sigma_neg_on_Ioo (m1 : HierarchicalMech) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    {θ : VisitStrategy M} (hSR : IsSR M (unilateralProfile M m1 ρ hρ0 hρ1) θ)
    {x y : ℝ} (hxy : x ≤ y) (hy1 : y ≤ 1)
    (hneg : ∀ t ∈ Ioo x y, sigma M m1 ρ hρ0 hρ1 θ t < 0) :
    (∀ᵐ t ∂(volume.restrict (Icc (max x M.a) y)), θ.θ 0 t = 0) ∧
    (∀ u ∈ Icc x y, ∀ v ∈ Icc x y, effDist M θ 0 u = effDist M θ 0 v) := by
  have hae_zero : ∀ᵐ t ∂(volume.restrict (Icc (max x M.a) y)), θ.θ 0 t = 0 := by
    have hSR_ae := (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mp hSR
    have hne_x : ∀ᵐ t ∂volume, t ≠ x := by simp [ae_iff, measure_singleton]
    have hne_y : ∀ᵐ t ∂volume, t ≠ y := by simp [ae_iff, measure_singleton]
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hSR_ae, hne_x, hne_y] with t ht htx hty hmem
    have hmemIcc : t ∈ Icc M.a 1 := ⟨(le_max_right _ _).trans hmem.1, hmem.2.trans hy1⟩
    have ht_oo : t ∈ Ioo x y := ⟨lt_of_le_of_ne ((le_max_left _ _).trans hmem.1) (Ne.symm htx),
      lt_of_le_of_ne hmem.2 hty⟩
    have hsig := hneg t ht_oo
    by_contra hne0
    have hpos0 : 0 < θ.θ 0 t := lt_of_le_of_ne (θ.hnonneg 0 t) (Ne.symm hne0)
    have hle := ht hmemIcc 0 (rivalIdx M) hpos0
    simp only [unilateralProfile, ite_true,
      ite_eq_right_iff.mpr (fun h => absurd h (rivalIdx_ne_zero M))] at hle
    rw [prop2_rival_surplus_eq M m1 ρ hρ0 hρ1 hSR (rivalIdx_ne_zero M)
      (M.ha0.trans hmemIcc.1) hmemIcc.2] at hle
    unfold sigma at hsig; linarith
  refine ⟨hae_zero, fun u hu v hv => ?_⟩
  have hconst_x : ∀ z ∈ Icc x y, effDist M θ 0 z = effDist M θ 0 x := by
    intro z hz
    have hsub := effDist_sub θ 0 (hxy.trans hy1) (hz.2.trans hy1)
    suffices h0 : ∫ t in x..z, θ.θ 0 t * M.f t = 0 by linarith
    have hcongr : ∫ t in x..z, θ.θ 0 t * M.f t = ∫ _ in x..z, (0 : ℝ) := by
      apply intervalIntegral.integral_congr_ae
      have hae_univ := (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mp hae_zero
      filter_upwards [hae_univ] with t ht hmem
      rw [uIoc_of_le hz.1] at hmem
      by_cases hta : t < M.a
      · rw [M.hf_below t hta, mul_zero]
      · push Not at hta
        rw [ht ⟨max_le hmem.1.le hta, hmem.2.trans hz.2⟩, zero_mul]
    rw [hcongr]; simp
  rw [hconst_x u hu, hconst_x v hv]

/-- **Proposition 2(iii), part 1 (Initial `σ > 0` interval)**:
Seller 1's customers strictly prefer him (`σ > 0`) on at most one initial interval
`(max (min r₁ ρ) a, v_hat)`, which can be nonempty only if `r₁ < ρ`. In particular,
when `ρ ≤ r₁`, `σ ≤ 0` everywhere on `[min r₁ ρ, 1]`. -/
theorem prop2_sigma_pos_initial (m1 : HierarchicalMech) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    {θ : VisitStrategy M} (hSR : IsSR M (unilateralProfile M m1 ρ hρ0 hρ1) θ) :
    (ρ ≤ m1.r → ∀ v ∈ Icc (min m1.r ρ) 1, sigma M m1 ρ hρ0 hρ1 θ v ≤ 0) ∧
    ∃ v_hat ∈ Icc (max (min m1.r ρ) M.a) 1,
      (∀ v ∈ Ioo (max (min m1.r ρ) M.a) v_hat, 0 < sigma M m1 ρ hρ0 hρ1 θ v) ∧
      (∀ v ∈ Ioc v_hat 1, sigma M m1 ρ hρ0 hρ1 θ v ≤ 0) ∧
      (v_hat < 1 → sigma M m1 ρ hρ0 hρ1 θ v_hat ≤ 0) ∧
      (max (min m1.r ρ) M.a < v_hat → m1.r < ρ) ∧
      (∀ᵐ v ∂(volume.restrict (Icc (max (min m1.r ρ) M.a) v_hat)), θ.θ 0 v = 1) := by
  let σ := sigma M m1 ρ hρ0 hρ1 θ
  have hσ_cont : ContinuousOn σ (Icc 0 1) := sigma_continuousOn M m1 ρ hρ0 hρ1 hSR
  have hrmin0 : 0 ≤ min m1.r ρ := le_min m1.hr0 hρ0
  have hrmax0 : 0 ≤ max m1.r ρ := le_max_of_le_left m1.hr0
  have hrmax1 : max m1.r ρ ≤ 1 := max_le m1.hr1 hρ1
  -- Key convexity obstruction: no open interval (y₁, y₂) ⊆ (max r₁ ρ, 1) with σ y₁ = 0 and σ > 0 inside
  have hno_pos_above : ∀ y₁ y₂ : ℝ, max m1.r ρ ≤ y₁ → y₁ < y₂ → y₂ ≤ 1 →
      σ y₁ = 0 → (∀ t ∈ Ioo y₁ y₂, 0 < σ t) → (y₂ = 1 ∨ σ y₂ = 0) → False := by
    intro y₁ y₂ hy1_ge hy12 hy21 hσy1 hpos hend
    have hFriv_const := (prop2_sigma_pos_on_Ioo M m1 ρ hρ0 hρ1 hSR hy12.le hy21 hpos).2
      (rivalIdx M) (rivalIdx_ne_zero M)
    have hρy1 : ρ ≤ y₁ := (le_max_right _ _).trans hy1_ge
    have hy1_0 : 0 ≤ y₁ := hrmax0.trans hy1_ge
    have hy2_0 : 0 ≤ y₂ := hy1_0.trans hy12.le
    rcases hend with rfl | hσy2
    · -- y₂ = 1 ⇒ F_riv ≡ 1 on [y₁, 1] ⇒ σ' = alloc₁ - 1 ≤ 0 ⇒ σ ≤ σ y₁ = 0
      let mid := (y₁ + 1) / 2
      have hmid_mem : mid ∈ Ioo y₁ 1 := ⟨by dsimp only [mid]; linarith, by dsimp only [mid]; linarith⟩
      have hsub := sigma_sub M m1 ρ hρ0 hρ1 hSR hy1_0 (hy12.le) (hy1_0.trans hmid_mem.1.le) hmid_mem.2.le
      have hint_np : ∫ t in y₁..mid, (alloc M m1 (effDist M θ 0) t -
          alloc M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) t) ≤ 0 := by
        rw [intervalIntegral.integral_of_le hmid_mem.1.le]
        apply MeasureTheory.integral_nonpos_of_ae
        change ∀ᵐ t ∂(volume.restrict (Ioc y₁ mid)), _ ≤ (0 : ℝ)
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
        filter_upwards with t ht
        have ht1 : t ≤ 1 := ht.2.trans hmid_mem.2.le
        have hF1 : effDist M θ (rivalIdx M) t = 1 := by
          rw [hFriv_const t ⟨ht.1.le, ht1⟩ 1 (right_mem_Icc.mpr hy12.le), vs_effDist_one]
        rw [alloc_SPA, ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr (hρy1.trans ht.1.le))),
          hF1, one_pow]
        have hle1 := alloc_le_one M m1 (effDist M θ 0) (fun z hz => effDist_nonneg θ 0 hz)
          (fun z hz => effDist_le_one θ 0 hz) ht1
        linarith
      have hmid_pos := hpos mid hmid_mem
      change σ mid - σ y₁ = _ at hsub
      linarith
    · -- σ y₁ = 0 and σ y₂ = 0: monotonicity of alloc₁ contradicts σ mid > 0
      let mid := (y₁ + y₂) / 2
      have hmid_gt : y₁ < mid := by dsimp only [mid]; linarith
      have hmid_lt : mid < y₂ := by dsimp only [mid]; linarith
      have hmid_mem : mid ∈ Ioo y₁ y₂ := ⟨hmid_gt, hmid_lt⟩
      have hmid_0 : 0 ≤ mid := hy1_0.trans hmid_gt.le
      have hmid_1 : mid ≤ 1 := hmid_lt.le.trans hy21
      let c := (effDist M θ (rivalIdx M) y₁) ^ (M.n - 1)
      have hmono_a := vs_alloc_monotoneOn M m1 (effDist M θ 0) (vs_effDist_monotoneOn θ 0)
        (fun z hz => effDist_nonneg θ 0 hz)
      have hleft_le : σ mid - σ y₁ ≤ (mid - y₁) * (alloc M m1 (effDist M θ 0) mid - c) := by
        have hsub := sigma_sub M m1 ρ hρ0 hρ1 hSR hy1_0 (hy12.le.trans hy21) hmid_0 hmid_1
        have hle : ∫ t in y₁..mid, (alloc M m1 (effDist M θ 0) t -
            alloc M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) t) ≤
            ∫ _ in y₁..mid, (alloc M m1 (effDist M θ 0) mid - c) := by
          apply intervalIntegral.integral_mono_on hmid_gt.le
            ((alloc_intervalIntegrable M m1 _ (vs_effDist_monotoneOn θ 0)
              (fun z hz => effDist_nonneg θ 0 hz) (hy12.le.trans hy21) hmid_1).sub
             (alloc_intervalIntegrable M (SPA ρ hρ0 hρ1) _ (vs_effDist_monotoneOn θ (rivalIdx M))
              (fun z hz => effDist_nonneg θ (rivalIdx M) hz) (hy12.le.trans hy21) hmid_1))
            intervalIntegrable_const
          intro t ht
          have ht_le : alloc M m1 (effDist M θ 0) t ≤ alloc M m1 (effDist M θ 0) mid :=
            hmono_a (ht.2.trans hmid_1) hmid_1 ht.2
          have hriv_eq : alloc M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) t = c := by
            rw [alloc_SPA, ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr (hρy1.trans ht.1))),
              hFriv_const t ⟨ht.1, ht.2.trans hmid_lt.le⟩ y₁ (left_mem_Icc.mpr hy12.le)]
          linarith
        rw [intervalIntegral.integral_const, smul_eq_mul] at hle
        change σ mid - σ y₁ = _ at hsub; linarith
      have hright_ge : (y₂ - mid) * (alloc M m1 (effDist M θ 0) mid - c) ≤ σ y₂ - σ mid := by
        have hsub := sigma_sub M m1 ρ hρ0 hρ1 hSR hmid_0 hmid_1 hy2_0 hy21
        have hge : ∫ _ in mid..y₂, (alloc M m1 (effDist M θ 0) mid - c) ≤
            ∫ t in mid..y₂, (alloc M m1 (effDist M θ 0) t -
              alloc M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) t) := by
          apply intervalIntegral.integral_mono_on hmid_lt.le intervalIntegrable_const
            ((alloc_intervalIntegrable M m1 _ (vs_effDist_monotoneOn θ 0)
              (fun z hz => effDist_nonneg θ 0 hz) hmid_1 hy21).sub
             (alloc_intervalIntegrable M (SPA ρ hρ0 hρ1) _ (vs_effDist_monotoneOn θ (rivalIdx M))
              (fun z hz => effDist_nonneg θ (rivalIdx M) hz) hmid_1 hy21))
          intro t ht
          have ht_ge : alloc M m1 (effDist M θ 0) mid ≤ alloc M m1 (effDist M θ 0) t :=
            hmono_a hmid_1 (ht.2.trans hy21) ht.1
          have hriv_eq : alloc M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) t = c := by
            rw [alloc_SPA, ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr (hρy1.trans (hmid_gt.le.trans ht.1)))),
              hFriv_const t ⟨hmid_gt.le.trans ht.1, ht.2⟩ y₁ (left_mem_Icc.mpr hy12.le)]
          linarith
        rw [intervalIntegral.integral_const, smul_eq_mul] at hge
        change σ y₂ - σ mid = _ at hsub; linarith
      have hmid_pos : 0 < σ mid := hpos mid hmid_mem
      have hlen : mid - y₁ = y₂ - mid := by dsimp only [mid]; ring
      have hlen_pos : 0 < mid - y₁ := sub_pos.mpr hmid_gt
      have h1 : 0 < alloc M m1 (effDist M θ 0) mid - c := by nlinarith
      have h2 : alloc M m1 (effDist M θ 0) mid - c < 0 := by nlinarith
      linarith
  -- Consequence: if σ(v₂) > 0 for some v₂ ∈ (min r₁ ρ, 1], then m1.r < ρ and σ > 0 on (max (min r₁ ρ) a, v₂]
  have hpos_imp : ∀ v₂ ∈ Ioc (min m1.r ρ) 1, 0 < σ v₂ →
      m1.r < ρ ∧ ∀ v ∈ Ioc (max (min m1.r ρ) M.a) v₂, 0 < σ v := by
    intro v₂ hv₂ hσv2
    -- Find largest zero/nonpos point y₁ ≤ v₂ in [min m1.r ρ, v₂]
    let Z : Set ℝ := {v ∈ Icc (min m1.r ρ) v₂ | σ v ≤ 0}
    have hZ_ne : Z.Nonempty := ⟨min m1.r ρ, left_mem_Icc.mpr hv₂.1.le,
      by change sigma M m1 ρ hρ0 hρ1 θ (min m1.r ρ) ≤ 0; rw [sigma_zero_at_rmin M m1 ρ hρ0 hρ1 hSR]⟩
    have hZ_bdd : BddAbove Z := ⟨v₂, fun v hv => hv.1.2⟩
    let y₁ := sSup Z
    have hy1_mem : y₁ ∈ Icc (min m1.r ρ) v₂ := ⟨le_csSup hZ_bdd ⟨left_mem_Icc.mpr hv₂.1.le,
      by change sigma M m1 ρ hρ0 hρ1 θ (min m1.r ρ) ≤ 0; rw [sigma_zero_at_rmin M m1 ρ hρ0 hρ1 hSR]⟩,
      csSup_le hZ_ne (fun v hv => hv.1.2)⟩
    have hcont_seg : ContinuousOn σ (Icc (min m1.r ρ) v₂) :=
      hσ_cont.mono (Icc_subset_Icc hrmin0 hv₂.2)
    have hy1_le0 : σ y₁ ≤ 0 := by
      have hcl : y₁ ∈ closure Z := csSup_mem_closure hZ_ne hZ_bdd
      have hZ_closed : IsClosed Z := by
        have : Z = Icc (min m1.r ρ) v₂ ∩ σ ⁻¹' Iic 0 := by ext v; simp [Z]
        rw [this]; exact hcont_seg.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
      rw [hZ_closed.closure_eq] at hcl; exact hcl.2
    have hy1_lt : y₁ < v₂ := lt_of_le_of_ne hy1_mem.2 (fun h => by rw [h] at hy1_le0; linarith)
    have hpos_right : ∀ t ∈ Ioc y₁ v₂, 0 < σ t := by
      intro t ht
      by_contra hle; push Not at hle
      exact not_lt.mpr (le_csSup hZ_bdd ⟨⟨hy1_mem.1.trans ht.1.le, ht.2⟩, hle⟩) ht.1
    have hy1_zero : σ y₁ = 0 := by
      refine le_antisymm hy1_le0 ?_
      have htend := (hcont_seg y₁ hy1_mem).mono_left
        (nhdsWithin_mono _ (Ioc_subset_Icc_self.trans (Icc_subset_Icc_left hy1_mem.1)))
      have : NeBot (𝓝[Ioc y₁ v₂] y₁) := left_nhdsWithin_Ioc_neBot hy1_lt
      exact ge_of_tendsto htend (eventually_nhdsWithin_of_forall fun t ht => (hpos_right t ht).le)
    -- Find right endpoint y₂ of the maximal positive component containing (y₁, v₂]
    let Rset : Set ℝ := {v ∈ Icc v₂ 1 | ∀ t ∈ Icc v₂ v, 0 < σ t}
    have hR_ne : Rset.Nonempty := ⟨v₂, left_mem_Icc.mpr hv₂.2, fun t ht => by
      have : t = v₂ := le_antisymm ht.2 ht.1; rw [this]; exact hσv2⟩
    have hR_bdd : BddAbove Rset := ⟨1, fun v hv => hv.1.2⟩
    let y₂ := sSup Rset
    have hy2_mem : y₂ ∈ Icc v₂ 1 := ⟨le_csSup hR_bdd ⟨left_mem_Icc.mpr hv₂.2, fun t ht => by
      have : t = v₂ := le_antisymm ht.2 ht.1; rw [this]; exact hσv2⟩,
      csSup_le hR_ne (fun v hv => hv.1.2)⟩
    have hpos_all : ∀ t ∈ Ioo y₁ y₂, 0 < σ t := by
      intro t ht
      by_cases htv2 : t ≤ v₂
      · exact hpos_right t ⟨ht.1, htv2⟩
      · push Not at htv2
        obtain ⟨w, hwR, htw⟩ := exists_lt_of_lt_csSup hR_ne ht.2
        exact hwR.2 t ⟨htv2.le, htw.le⟩
    have hend : y₂ = 1 ∨ σ y₂ = 0 := by
      by_cases hy2eq : y₂ = 1
      · exact Or.inl hy2eq
      · right
        have hy2lt : y₂ < 1 := lt_of_le_of_ne hy2_mem.2 hy2eq
        have hcont_1 : ContinuousOn σ (Icc y₁ 1) :=
          hσ_cont.mono (Icc_subset_Icc (hrmin0.trans hy1_mem.1) le_rfl)
        have hge0 : 0 ≤ σ y₂ := by
          have htend := (hcont_1 y₂ ⟨hy1_lt.le.trans hy2_mem.1, hy2_mem.2⟩).mono_left
            (nhdsWithin_mono _ (Ioo_subset_Icc_self.trans (Icc_subset_Icc_right hy2_mem.2)))
          have : NeBot (𝓝[Ioo y₁ y₂] y₂) := right_nhdsWithin_Ioo_neBot (hy1_lt.trans_le hy2_mem.1)
          exact ge_of_tendsto htend (eventually_nhdsWithin_of_forall fun t ht => (hpos_all t ht).le)
        refine le_antisymm ?_ hge0
        by_contra hpos2; push Not at hpos2
        obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousWithinAt_iff.mp
          (hcont_1 y₂ ⟨hy1_lt.le.trans hy2_mem.1, hy2_mem.2⟩) (σ y₂ / 2) (half_pos hpos2)
        let y₂' := min 1 (y₂ + δ / 2)
        have hy2'_gt : y₂ < y₂' := lt_min hy2lt (by linarith)
        have hy2'_mem : y₂' ∈ Rset := by
          refine ⟨⟨hy2_mem.1.trans hy2'_gt.le, min_le_left _ _⟩, fun t ht => ?_⟩
          by_cases hty2 : t < y₂
          · exact hpos_all t ⟨hy1_lt.trans_le ht.1, hty2⟩
          · push Not at hty2
            have hdist : dist t y₂ < δ := by
              rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hty2)]
              have : t ≤ y₂ + δ / 2 := ht.2.trans (min_le_right _ _)
              linarith
            have h1 := hδ ⟨hy1_lt.le.trans ht.1, ht.2.trans (min_le_left _ _)⟩ hdist
            rw [Real.dist_eq] at h1; linarith [(abs_lt.mp h1).1]
        exact not_lt.mpr (le_csSup hR_bdd hy2'_mem) hy2'_gt
    -- Therefore y₁ < max m1.r ρ!
    have hy1_lt_rmax : y₁ < max m1.r ρ := by
      by_contra hge; push Not at hge
      exact hno_pos_above y₁ y₂ hge (hy1_lt.trans_le hy2_mem.1) hy2_mem.2 hy1_zero hpos_all hend
    -- If ρ ≤ m1.r, then on [ρ, m1.r] we have s₁ = 0 so σ = -s_riv ≤ 0, contradicting y₁ < m1.r!
    have hrlt : m1.r < ρ := by
      by_contra hge; push Not at hge
      have hrmax_eq : max m1.r ρ = m1.r := max_eq_left hge
      rw [hrmax_eq] at hy1_lt_rmax
      -- Pick a point t ∈ (y₁, min m1.r v₂) where σ(t) > 0, yet t ≤ m1.r so s₁(t) = 0 and σ(t) ≤ 0!
      let t0 := (y₁ + min m1.r v₂) / 2
      have ht0_gt : y₁ < t0 := by dsimp only [t0]; linarith [lt_min hy1_lt_rmax hy1_lt]
      have ht0_le_v2 : t0 ≤ v₂ := by dsimp only [t0]; linarith [min_le_right m1.r v₂, lt_min hy1_lt_rmax hy1_lt]
      have ht0_le_r : t0 ≤ m1.r := by dsimp only [t0]; linarith [min_le_left m1.r v₂, lt_min hy1_lt_rmax hy1_lt]
      have ht0_0 : 0 ≤ t0 := (hrmin0.trans hy1_mem.1).trans ht0_gt.le
      have ht0_1 : t0 ≤ 1 := ht0_le_r.trans m1.hr1
      have ht0_pos : 0 < σ t0 := hpos_right t0 ⟨ht0_gt, ht0_le_v2⟩
      have hs1_0 : surplus M m1 (effDist M θ 0) t0 = 0 := surplus_zero_of_le_r M m1 _ ht0_0 ht0_le_r
      have hsriv_nn : 0 ≤ srivOf M ρ hρ0 hρ1 (effDist M θ 0) t0 := by
        rw [srivOf_eq_integral M m1 ρ hρ0 hρ1 hSR ht0_0 ht0_1]
        exact intervalIntegral.integral_nonneg (le_max_right t0 ρ) fun z hz => by
          rw [← (prop2_rival_symmetry M m1 ρ hρ0 hρ1 hSR).2 (rivalIdx M) (rivalIdx_ne_zero M) z
            ⟨hz.1, hz.2.trans (max_le ht0_1 hρ1)⟩]
          exact pow_nonneg (effDist_nonneg θ _ (hz.2.trans (max_le ht0_1 hρ1))) _
      have : σ t0 = surplus M m1 (effDist M θ 0) t0 - srivOf M ρ hρ0 hρ1 (effDist M θ 0) t0 := rfl
      linarith
    -- Now m1.r < ρ, so max m1.r ρ = ρ and y₁ < ρ; also σ > 0 on (max m1.r a, ρ) forces y₁ ≤ max m1.r a!
    have hy1_le_bot : y₁ ≤ max (min m1.r ρ) M.a := by
      rw [min_eq_left hrlt.le]
      rw [max_eq_right hrlt.le] at hy1_lt_rmax
      by_contra hgt; push Not at hgt
      have h1 := (prop2_below_rho_seller1_captures M m1 ρ hρ0 hρ1 hSR hrlt).1 y₁ ⟨hgt, hy1_lt_rmax⟩
      change 0 < σ y₁ at h1; linarith
    refine ⟨hrlt, fun v hv => hpos_right v ⟨lt_of_le_of_lt hy1_le_bot hv.1, hv.2⟩⟩
  -- Part 1: ρ ≤ m1.r ⇒ σ ≤ 0 on [min m1.r ρ, 1]
  have hpart1 : ρ ≤ m1.r → ∀ v ∈ Icc (min m1.r ρ) 1, σ v ≤ 0 := by
    intro hle v hv
    rcases eq_or_lt_of_le hv.1 with rfl | hgt
    · rw [show σ (min m1.r ρ) = 0 from sigma_zero_at_rmin M m1 ρ hρ0 hρ1 hSR]
    · by_contra hpos; push Not at hpos
      have := (hpos_imp v ⟨hgt, hv.2⟩ hpos).1
      linarith
  refine ⟨hpart1, ?_⟩
  -- Part 2: construct v_hat
  let bot := max (min m1.r ρ) M.a
  have hbot1 : bot ≤ 1 := max_le (min_le_of_left_le m1.hr1) M.ha1.le
  by_cases hex : ∃ v ∈ Ioc bot 1, 0 < σ v
  · let P : Set ℝ := {v ∈ Ioc bot 1 | 0 < σ v}
    have hP_bdd : BddAbove P := ⟨1, fun v hv => hv.1.2⟩
    let v_hat := sSup P
    have hvhat_gt : bot < v_hat := lt_of_lt_of_le hex.choose_spec.1.1 (le_csSup hP_bdd hex.choose_spec)
    have hvhat_le : v_hat ≤ 1 := csSup_le hex (fun v hv => hv.1.2)
    have hpos_oo : ∀ v ∈ Ioo bot v_hat, 0 < σ v := by
      intro v hv
      obtain ⟨v₂, hv₂P, hvv₂⟩ := exists_lt_of_lt_csSup (show P.Nonempty from hex) hv.2
      exact (hpos_imp v₂ ⟨(le_max_left _ _).trans_lt hv₂P.1.1, hv₂P.1.2⟩ hv₂P.2).2 v ⟨hv.1, hvv₂.le⟩
    have hle_above : ∀ v ∈ Ioc v_hat 1, σ v ≤ 0 := by
      intro v hv
      by_contra hpos; push Not at hpos
      exact not_lt.mpr (le_csSup hP_bdd ⟨⟨hvhat_gt.trans hv.1, hv.2⟩, hpos⟩) hv.1
    have hle_at_vhat : v_hat < 1 → σ v_hat ≤ 0 := by
      intro hvhat_lt
      have htend := (hσ_cont.mono (Icc_subset_Icc ((le_max_of_le_left hrmin0).trans hvhat_gt.le) le_rfl)
        v_hat (left_mem_Icc.mpr hvhat_lt.le)).mono_left (nhdsWithin_mono _ Ioc_subset_Icc_self)
      have : NeBot (𝓝[Ioc v_hat 1] v_hat) := left_nhdsWithin_Ioc_neBot hvhat_lt
      exact le_of_tendsto htend (eventually_nhdsWithin_of_forall hle_above)
    have hrlt : m1.r < ρ :=
      (hpos_imp hex.choose ⟨(le_max_left _ _).trans_lt hex.choose_spec.1.1, hex.choose_spec.1.2⟩ hex.choose_spec.2).1
    have hae1 : ∀ᵐ v ∂(volume.restrict (Icc bot v_hat)), θ.θ 0 v = 1 := by
      have h1 := (prop2_sigma_pos_on_Ioo M m1 ρ hρ0 hρ1 hSR hvhat_gt.le hvhat_le hpos_oo).1
      rwa [show max bot M.a = bot from max_eq_left (le_max_right _ _)] at h1
    exact ⟨v_hat, ⟨hvhat_gt.le, hvhat_le⟩, hpos_oo, hle_above, hle_at_vhat, fun _ => hrlt, hae1⟩
  · push Not at hex
    refine ⟨bot, left_mem_Icc.mpr hbot1, fun v hv => absurd (hv.1.trans hv.2) (lt_irrefl _),
      fun v hv => hex v hv, ?_, fun h => absurd h (lt_irrefl _), ?_⟩
    · intro hbotlt
      have htend := (hσ_cont.mono (Icc_subset_Icc (le_max_of_le_left hrmin0) le_rfl) bot
        (left_mem_Icc.mpr hbotlt.le)).mono_left (nhdsWithin_mono _ Ioc_subset_Icc_self)
      have : NeBot (𝓝[Ioc bot 1] bot) := left_nhdsWithin_Ioc_neBot hbotlt
      exact le_of_tendsto htend (eventually_nhdsWithin_of_forall fun t ht => hex t ht)
    · rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
      have hne : ∀ᵐ v ∂volume, v ≠ bot := by simp [ae_iff, measure_singleton]
      filter_upwards [hne] with v hv hmem
      exact absurd (le_antisymm hmem.2 hmem.1) hv

/-- If `σ = 0` on a gap `[x, y] ⊆ [max (max r₁ ρ) a, 1]` avoiding all pools, then `F₁ = A`
identically on `[x, y]` and `θ_0 = 1 / m` a.e. on `[x, y]`. -/
lemma prop2_sigma_zero_off_pools (m1 : HierarchicalMech) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    {θ : VisitStrategy M} (hSR : IsSR M (unilateralProfile M m1 ρ hρ0 hρ1) θ)
    {x y : ℝ} (hx_ge : max (max m1.r ρ) M.a ≤ x) (hlt : x < y) (hy1 : y ≤ 1)
    (hgap : ∀ I ∈ m1.pools, ∀ t ∈ Ioo x y, ¬ (I.α < t ∧ t < I.β))
    (hzero : ∀ t ∈ Icc x y, sigma M m1 ρ hρ0 hρ1 θ t = 0) :
    (∀ t ∈ Icc x y, effDist M θ 0 t = M.A t) ∧
    (∀ᵐ t ∂(volume.restrict (Icc x y)), θ.θ 0 t = 1 / (M.m : ℝ)) := by
  have hx_r : m1.r ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hx_ge)
  have hx_ρ : ρ ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx_ge)
  have hx_a : M.a ≤ x := (le_max_right _ _).trans hx_ge
  have hx0 : 0 ≤ x := M.ha0.trans hx_a
  have hF_eq_riv : ∀ t ∈ Icc x y, effDist M θ 0 t = effDist M θ (rivalIdx M) t := by
    let ψ : ℝ → ℝ := fun t => (effDist M θ 0 t) ^ (M.n - 1) - (effDist M θ (rivalIdx M) t) ^ (M.n - 1)
    have hψ_cont : ContinuousOn ψ (Icc x y) :=
      (((effDist_continuousOn θ 0).mono (fun t (ht : t ∈ Icc x y) => ht.2.trans hy1)).pow (M.n - 1)).sub
        (((effDist_continuousOn θ (rivalIdx M)).mono (fun t (ht : t ∈ Icc x y) => ht.2.trans hy1)).pow (M.n - 1))
    have hψ_int0 : ∀ c d : ℝ, c ∈ Icc x y → d ∈ Icc x y → c ≤ d → ∫ t in c..d, ψ t = 0 := by
      intro c d hc hd hcd
      have hsub := sigma_sub M m1 ρ hρ0 hρ1 hSR (hx0.trans hc.1) (hc.2.trans hy1)
        (hx0.trans hd.1) (hd.2.trans hy1)
      rw [hzero d hd, hzero c hc, sub_self] at hsub
      have hcongr : ∫ t in c..d, ψ t =
          ∫ t in c..d, (alloc M m1 (effDist M θ 0) t -
            alloc M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) t) := by
        apply intervalIntegral.integral_congr_ae
        have hne_d : ∀ᵐ t ∂volume, t ≠ d := by simp [ae_iff, measure_singleton]
        filter_upwards [hne_d] with t htd hmem
        rw [uIoc_of_le hcd] at hmem
        have ht_oo : t ∈ Ioo x y := ⟨lt_of_le_of_lt hc.1 hmem.1, lt_of_lt_of_le (lt_of_le_of_ne hmem.2 htd) hd.2⟩
        simp only [ψ]
        rw [alloc_off_pools M m1 _ (hx_r.trans ht_oo.1.le) (fun I hI => hgap I hI t ht_oo),
            alloc_SPA, ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr (hx_ρ.trans ht_oo.1.le)))]
      linarith
    have hψ_zero : ∀ t ∈ Icc x y, ψ t = 0 := by
      intro t ht
      by_contra hne
      have hpos_or_neg : 0 < |ψ t| := abs_pos.mpr hne
      obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousWithinAt_iff.mp (hψ_cont t ht) (|ψ t| / 2) (half_pos hpos_or_neg)
      let c := max x (t - δ / 2)
      let d := min y (t + δ / 2)
      have hcd : c < d := by
        have h1 : x < y := hlt
        have h2 : x < t + δ / 2 := by linarith [ht.1]
        have h3 : t - δ / 2 < y := by linarith [ht.2]
        have h4 : t - δ / 2 < t + δ / 2 := by linarith
        exact max_lt (lt_min h1 h2) (lt_min h3 h4)
      have hc_mem : c ∈ Icc x y := ⟨le_max_left _ _, max_le hlt.le (by linarith [ht.2])⟩
      have hd_mem : d ∈ Icc x y := ⟨le_min hlt.le (by linarith [ht.1]), min_le_left _ _⟩
      have hnear : ∀ u ∈ Icc c d, |ψ u - ψ t| < |ψ t| / 2 := by
        intro u hu
        have hu_mem : u ∈ Icc x y := ⟨hc_mem.1.trans hu.1, hu.2.trans hd_mem.2⟩
        have hdist : dist u t < δ := by
          rw [Real.dist_eq, abs_lt]
          have h1 : t - δ / 2 ≤ u := (le_max_right x _).trans hu.1
          have h2 : u ≤ t + δ / 2 := hu.2.trans (min_le_right y _)
          constructor <;> linarith
        have := hδ hu_mem hdist; rwa [Real.dist_eq] at this
      have hint0 := hψ_int0 c d hc_mem hd_mem hcd.le
      rcases lt_or_gt_of_ne hne with hneg | hpos
      · have hint_neg : ∫ u in c..d, ψ u < 0 := by
          have hlt_int : ∫ u in c..d, ψ u ≤ ∫ _ in c..d, (ψ t / 2) := by
            apply intervalIntegral.integral_mono_on hcd.le
              ((hψ_cont.mono (Icc_subset_Icc hc_mem.1 hd_mem.2)).intervalIntegrable_of_Icc hcd.le)
              intervalIntegrable_const
            intro u hu
            have := (abs_lt.mp (hnear u hu)).2
            rw [abs_of_neg hneg] at this; linarith
          rw [intervalIntegral.integral_const, smul_eq_mul] at hlt_int
          have : (d - c) * (ψ t / 2) < 0 := mul_neg_of_pos_of_neg (sub_pos.mpr hcd) (by linarith)
          linarith
        linarith
      · have hint_pos : 0 < ∫ u in c..d, ψ u := by
          have hgt_int : ∫ _ in c..d, (ψ t / 2) ≤ ∫ u in c..d, ψ u := by
            apply intervalIntegral.integral_mono_on hcd.le intervalIntegrable_const
              ((hψ_cont.mono (Icc_subset_Icc hc_mem.1 hd_mem.2)).intervalIntegrable_of_Icc hcd.le)
            intro u hu
            have := (abs_lt.mp (hnear u hu)).1
            rw [abs_of_pos hpos] at this; linarith
          rw [intervalIntegral.integral_const, smul_eq_mul] at hgt_int
          have : 0 < (d - c) * (ψ t / 2) := mul_pos (sub_pos.mpr hcd) (half_pos hpos)
          linarith
        linarith
    intro t ht
    have h0 := hψ_zero t ht
    have hpow_eq : (effDist M θ 0 t) ^ (M.n - 1) = (effDist M θ (rivalIdx M) t) ^ (M.n - 1) :=
      sub_eq_zero.mp h0
    have hn1 : M.n - 1 ≠ 0 := by have := M.hn; omega
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt' | hgt'
    · exact absurd hpow_eq (ne_of_lt (pow_lt_pow_left₀ hlt' (effDist_nonneg θ 0 (ht.2.trans hy1)) hn1))
    · exact absurd hpow_eq (ne_of_gt (pow_lt_pow_left₀ hgt' (effDist_nonneg θ (rivalIdx M) (ht.2.trans hy1)) hn1))
  have hF1_eq_A : ∀ t ∈ Icc x y, effDist M θ 0 t = M.A t := by
    intro t ht
    have hsym := (prop2_rival_symmetry M m1 ρ hρ0 hρ1 hSR).2 (rivalIdx M) (rivalIdx_ne_zero M) t
      ⟨hx_ρ.trans ht.1, ht.2.trans hy1⟩
    have heq := hF_eq_riv t ht
    rw [hsym] at heq
    unfold FrivOf at heq
    unfold Market.A
    have hm1 : (M.m : ℝ) - 1 ≠ 0 := M.m_sub_one_pos_real.ne'
    have hm : (M.m : ℝ) ≠ 0 := M.m_pos_real.ne'
    field_simp [hm1, hm] at heq ⊢
    linarith
  refine ⟨hF1_eq_A, ?_⟩
  have hg_int : IntervalIntegrable (fun t => (θ.θ 0 t - 1 / (M.m : ℝ)) * M.f t) volume x y := by
    have h1 := θ.mul_f_intervalIntegrable 0 (hlt.le.trans hy1) hy1
    have h2 := (M.f_intervalIntegrable (hlt.le.trans hy1) hy1).const_mul (1 / (M.m : ℝ))
    have hsub := h1.sub h2
    have hfun : (fun t => θ.θ 0 t * M.f t - 1 / (M.m : ℝ) * M.f t) =
        (fun t => (θ.θ 0 t - 1 / (M.m : ℝ)) * M.f t) := by ext t; ring
    rwa [hfun] at hsub
  have hzero_int : ∀ z ∈ Icc x y, ∫ t in x..z, (θ.θ 0 t - 1 / (M.m : ℝ)) * M.f t = 0 := by
    intro z hz
    have hfun : (fun t => (θ.θ 0 t - 1 / (M.m : ℝ)) * M.f t) =
        (fun t => θ.θ 0 t * M.f t - 1 / (M.m : ℝ) * M.f t) := by ext t; ring
    rw [hfun, intervalIntegral.integral_sub (θ.mul_f_intervalIntegrable 0 (hlt.le.trans hy1) (hz.2.trans hy1))
      ((M.f_intervalIntegrable (hlt.le.trans hy1) (hz.2.trans hy1)).const_mul _),
      ← effDist_sub θ 0 (hlt.le.trans hy1) (hz.2.trans hy1),
      intervalIntegral.integral_const_mul, M.integral_f (hlt.le.trans hy1) (hz.2.trans hy1),
      hF1_eq_A z hz, hF1_eq_A x (left_mem_Icc.mpr hlt.le)]
    unfold Market.A; ring
  have hae := ae_eq_zero_of_forall_integral_eq_zero hlt.le hg_int hzero_int
  filter_upwards [hae, MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht hmem
  have hfpos := M.hf_pos t ⟨hx_a.trans hmem.1, hmem.2.trans hy1⟩
  have h0 := (mul_eq_zero.mp ht).resolve_right hfpos.ne'
  linarith

/-- Inside a pool `I ∈ m1.pools`, if `σ = 0` on `[x, y] ⊆ [max I.α u₀, I.β]` (`x < y`), then
`F_riv` is constant with `F_riv^{n-1} = poolAvg(F₁(I.α), F₁(I.β))` and `θ_0 = 1` a.e. on `[x, y]`. -/
lemma prop2_sigma_zero_in_pool (m1 : HierarchicalMech) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    {θ : VisitStrategy M} (hSR : IsSR M (unilateralProfile M m1 ρ hρ0 hρ1) θ)
    {I : Pool} (hI : I ∈ m1.pools) {x y : ℝ}
    (hx_ge : max (max m1.r ρ) M.a ≤ x) (hx_α : I.α ≤ x) (hlt : x < y) (hy_β : y ≤ I.β)
    (hzero : ∀ t ∈ Icc x y, sigma M m1 ρ hρ0 hρ1 θ t = 0) :
    (∀ t ∈ Icc x y,
      (effDist M θ (rivalIdx M) t) ^ (M.n - 1) =
        poolAvg M.n (effDist M θ 0 I.α) (effDist M θ 0 I.β)) ∧
    (∀ᵐ t ∂(volume.restrict (Icc x y)), θ.θ 0 t = 1) := by
  have hIin := m1.hpools_in I hI
  have hy1 : y ≤ 1 := hy_β.trans hIin.2
  have hx_ρ : ρ ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx_ge)
  have hx_a : M.a ≤ x := (le_max_right _ _).trans hx_ge
  have hx0 : 0 ≤ x := M.ha0.trans hx_a
  let xbar := poolAvg M.n (effDist M θ 0 I.α) (effDist M θ 0 I.β)
  let ψ : ℝ → ℝ := fun t => xbar - (effDist M θ (rivalIdx M) t) ^ (M.n - 1)
  have hψ_cont : ContinuousOn ψ (Icc x y) :=
    continuousOn_const.sub
      (((effDist_continuousOn θ (rivalIdx M)).mono (fun t (ht : t ∈ Icc x y) => ht.2.trans hy1)).pow (M.n - 1))
  have hψ_int0 : ∀ c d : ℝ, c ∈ Icc x y → d ∈ Icc x y → c ≤ d → ∫ t in c..d, ψ t = 0 := by
    intro c d hc hd hcd
    have hsub := sigma_sub M m1 ρ hρ0 hρ1 hSR (hx0.trans hc.1) (hc.2.trans hy1)
      (hx0.trans hd.1) (hd.2.trans hy1)
    rw [hzero d hd, hzero c hc, sub_self] at hsub
    have hcongr : ∫ t in c..d, ψ t =
        ∫ t in c..d, (alloc M m1 (effDist M θ 0) t -
          alloc M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) t) := by
      apply intervalIntegral.integral_congr_ae
      have hne_d : ∀ᵐ t ∂volume, t ≠ d := by simp [ae_iff, measure_singleton]
      filter_upwards [hne_d] with t htd hmem
      rw [uIoc_of_le hcd] at hmem
      have ht_oo : t ∈ Ioo I.α I.β := ⟨lt_of_le_of_lt (hx_α.trans hc.1) hmem.1,
        lt_of_lt_of_le (lt_of_le_of_ne hmem.2 htd) (hd.2.trans hy_β)⟩
      simp only [ψ, xbar]
      rw [alloc_in_pool M m1 _ hI ht_oo,
          alloc_SPA, ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr (hx_ρ.trans (hc.1.trans hmem.1.le))))]
    linarith
  have hψ_zero : ∀ t ∈ Icc x y, ψ t = 0 := by
    intro t ht
    by_contra hne
    have hpos_or_neg : 0 < |ψ t| := abs_pos.mpr hne
    obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousWithinAt_iff.mp (hψ_cont t ht) (|ψ t| / 2) (half_pos hpos_or_neg)
    let c := max x (t - δ / 2)
    let d := min y (t + δ / 2)
    have hcd : c < d := max_lt (lt_min hlt (by linarith [ht.1])) (lt_min (by linarith [ht.2]) (by linarith))
    have hc_mem : c ∈ Icc x y := ⟨le_max_left _ _, max_le hlt.le (by linarith [ht.2])⟩
    have hd_mem : d ∈ Icc x y := ⟨le_min hlt.le (by linarith [ht.1]), min_le_left _ _⟩
    have hnear : ∀ u ∈ Icc c d, |ψ u - ψ t| < |ψ t| / 2 := by
      intro u hu
      have hdist : dist u t < δ := by
        rw [Real.dist_eq, abs_lt]
        have h1 : t - δ / 2 ≤ u := (le_max_right x _).trans hu.1
        have h2 : u ≤ t + δ / 2 := hu.2.trans (min_le_right y _)
        constructor <;> linarith
      have := hδ ⟨hc_mem.1.trans hu.1, hu.2.trans hd_mem.2⟩ hdist; rwa [Real.dist_eq] at this
    have hint0 := hψ_int0 c d hc_mem hd_mem hcd.le
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have hlt_int : ∫ u in c..d, ψ u ≤ ∫ _ in c..d, (ψ t / 2) := by
        apply intervalIntegral.integral_mono_on hcd.le
          ((hψ_cont.mono (Icc_subset_Icc hc_mem.1 hd_mem.2)).intervalIntegrable_of_Icc hcd.le)
          intervalIntegrable_const
        intro u hu; have := (abs_lt.mp (hnear u hu)).2; rw [abs_of_neg hneg] at this; linarith
      rw [intervalIntegral.integral_const, smul_eq_mul] at hlt_int
      have : (d - c) * (ψ t / 2) < 0 := mul_neg_of_pos_of_neg (sub_pos.mpr hcd) (by linarith)
      linarith
    · have hgt_int : ∫ _ in c..d, (ψ t / 2) ≤ ∫ u in c..d, ψ u := by
        apply intervalIntegral.integral_mono_on hcd.le intervalIntegrable_const
          ((hψ_cont.mono (Icc_subset_Icc hc_mem.1 hd_mem.2)).intervalIntegrable_of_Icc hcd.le)
        intro u hu; have := (abs_lt.mp (hnear u hu)).1; rw [abs_of_pos hpos] at this; linarith
      rw [intervalIntegral.integral_const, smul_eq_mul] at hgt_int
      have : 0 < (d - c) * (ψ t / 2) := mul_pos (sub_pos.mpr hcd) (half_pos hpos)
      linarith
  have hriv_pow : ∀ t ∈ Icc x y, (effDist M θ (rivalIdx M) t) ^ (M.n - 1) = xbar := fun t ht =>
    (sub_eq_zero.mp (hψ_zero t ht)).symm
  have hriv_const : ∀ t ∈ Icc x y, effDist M θ (rivalIdx M) t = effDist M θ (rivalIdx M) x := by
    intro t ht
    have hpow : (effDist M θ (rivalIdx M) t) ^ (M.n - 1) = (effDist M θ (rivalIdx M) x) ^ (M.n - 1) := by
      rw [hriv_pow t ht, hriv_pow x (left_mem_Icc.mpr hlt.le)]
    have hn1 : M.n - 1 ≠ 0 := by have := M.hn; omega
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt' | hgt'
    · exact absurd hpow (ne_of_lt (pow_lt_pow_left₀ hlt' (effDist_nonneg θ _ (ht.2.trans hy1)) hn1))
    · exact absurd hpow (ne_of_gt (pow_lt_pow_left₀ hgt' (effDist_nonneg θ _ (hlt.le.trans hy1)) hn1))
  refine ⟨hriv_pow, ?_⟩
  have hg_int : IntervalIntegrable (fun t => (1 - θ.θ 0 t) * M.f t) volume x y := by
    have hsub := (M.f_intervalIntegrable (hlt.le.trans hy1) hy1).sub
      (θ.mul_f_intervalIntegrable 0 (hlt.le.trans hy1) hy1)
    have hfun : (fun t => M.f t - θ.θ 0 t * M.f t) = (fun t => (1 - θ.θ 0 t) * M.f t) := by ext t; ring
    rwa [hfun] at hsub
  have hzero_int : ∀ z ∈ Icc x y, ∫ t in x..z, (1 - θ.θ 0 t) * M.f t = 0 := by
    intro z hz
    have hfun : (fun t => (1 - θ.θ 0 t) * M.f t) = (fun t => M.f t - θ.θ 0 t * M.f t) := by ext t; ring
    rw [hfun, intervalIntegral.integral_sub (M.f_intervalIntegrable (hlt.le.trans hy1) (hz.2.trans hy1))
      (θ.mul_f_intervalIntegrable 0 (hlt.le.trans hy1) (hz.2.trans hy1)),
      M.integral_f (hlt.le.trans hy1) (hz.2.trans hy1),
      ← effDist_sub θ 0 (hlt.le.trans hy1) (hz.2.trans hy1)]
    have hsym_z := (prop2_rival_symmetry M m1 ρ hρ0 hρ1 hSR).2 (rivalIdx M) (rivalIdx_ne_zero M) z
      ⟨hx_ρ.trans hz.1, hz.2.trans hy1⟩
    have hsym_x := (prop2_rival_symmetry M m1 ρ hρ0 hρ1 hSR).2 (rivalIdx M) (rivalIdx_ne_zero M) x
      ⟨hx_ρ, hlt.le.trans hy1⟩
    have hc := hriv_const z hz
    rw [hsym_z, hsym_x] at hc
    unfold FrivOf at hc
    have hm1 : (M.m : ℝ) - 1 ≠ 0 := M.m_sub_one_pos_real.ne'
    have hF1_diff : effDist M θ 0 z - effDist M θ 0 x = M.F z - M.F x := by
      field_simp [hm1] at hc; linarith
    linarith
  have hae := ae_eq_zero_of_forall_integral_eq_zero hlt.le hg_int hzero_int
  filter_upwards [hae, MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht hmem
  have hfpos := M.hf_pos t ⟨hx_a.trans hmem.1, hmem.2.trans hy1⟩
  have h0 := (mul_eq_zero.mp ht).resolve_right hfpos.ne'
  linarith

/-- Strict concavity obstruction for negative `σ` dips: no open interval `(y₁, y₂) ⊆ (u₀, 1)`
avoiding all pool endpoints can have `σ(y₁) = σ(y₂) = 0` and `σ < 0` on `(y₁, y₂)`. -/
lemma prop2_no_dip_without_endpoint (m1 : HierarchicalMech) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    {θ : VisitStrategy M} (hSR : IsSR M (unilateralProfile M m1 ρ hρ0 hρ1) θ)
    {y₁ y₂ : ℝ} (hy1_ge : max (max m1.r ρ) M.a ≤ y₁) (hlt : y₁ < y₂) (hy2_le : y₂ ≤ 1)
    (hσ1 : sigma M m1 ρ hρ0 hρ1 θ y₁ = 0) (hσ2 : sigma M m1 ρ hρ0 hρ1 θ y₂ = 0)
    (hneg : ∀ t ∈ Ioo y₁ y₂, sigma M m1 ρ hρ0 hρ1 θ t < 0)
    (hno_end : ∀ I ∈ m1.pools, I.α ∉ Ioo y₁ y₂ ∧ I.β ∉ Ioo y₁ y₂) : False := by
  have hy1_r : m1.r ≤ y₁ := (le_max_left _ _).trans ((le_max_left _ _).trans hy1_ge)
  have hy1_ρ : ρ ≤ y₁ := (le_max_right _ _).trans ((le_max_left _ _).trans hy1_ge)
  have hy1_a : M.a ≤ y₁ := (le_max_right _ _).trans hy1_ge
  have hy1_0 : 0 ≤ y₁ := M.ha0.trans hy1_a
  have hy2_0 : 0 ≤ y₂ := hy1_0.trans hlt.le
  -- On (y₁, y₂), F₁ is constant, hence F_riv is strictly increasing!
  have hF1_const := (prop2_sigma_neg_on_Ioo M m1 ρ hρ0 hρ1 hSR hlt.le hy2_le hneg).2
  have hFriv_strict : StrictMonoOn (effDist M θ (rivalIdx M)) (Icc y₁ y₂) := by
    intro u hu v hv huv
    rw [(prop2_rival_symmetry M m1 ρ hρ0 hρ1 hSR).2 (rivalIdx M) (rivalIdx_ne_zero M) u
          ⟨hy1_ρ.trans hu.1, hu.2.trans hy2_le⟩,
        (prop2_rival_symmetry M m1 ρ hρ0 hρ1 hSR).2 (rivalIdx M) (rivalIdx_ne_zero M) v
          ⟨hy1_ρ.trans hv.1, hv.2.trans hy2_le⟩]
    unfold FrivOf
    rw [hF1_const u hu v hv]
    have hF := M.F_strictMonoOn ⟨hy1_a.trans hu.1, hu.2.trans hy2_le⟩
      ⟨hy1_a.trans hv.1, hv.2.trans hy2_le⟩ huv
    have := div_lt_div_of_pos_right (sub_lt_sub_left hF (effDist M θ 0 v)) M.m_sub_one_pos_real
    linarith
  -- Also alloc₁ is constant on (y₁, y₂): either inside one pool I, or off all pools (so = F₁(y₁)^{n-1})
  have halloc1_const : ∃ C : ℝ, ∀ t ∈ Ioo y₁ y₂, alloc M m1 (effDist M θ 0) t = C := by
    by_cases hex : ∃ I ∈ m1.pools, ∃ t ∈ Ioo y₁ y₂, I.α < t ∧ t < I.β
    · obtain ⟨I, hI, t0, ht0, ht0_1, ht0_2⟩ := hex
      have hα_le : I.α ≤ y₁ := by
        by_contra hgt; push Not at hgt
        exact (hno_end I hI).1 ⟨hgt, ht0_1.trans ht0.2⟩
      have hβ_ge : y₂ ≤ I.β := by
        by_contra hlt'; push Not at hlt'
        exact (hno_end I hI).2 ⟨ht0.1.trans ht0_2, hlt'⟩
      refine ⟨poolAvg M.n (effDist M θ 0 I.α) (effDist M θ 0 I.β), fun t ht => ?_⟩
      exact alloc_in_pool M m1 _ hI ⟨lt_of_le_of_lt hα_le ht.1, lt_of_lt_of_le ht.2 hβ_ge⟩
    · push Not at hex
      refine ⟨(effDist M θ 0 y₁) ^ (M.n - 1), fun t ht => ?_⟩
      rw [alloc_off_pools M m1 _ (hy1_r.trans ht.1.le) (fun I hI h => not_le.mpr h.2 (hex I hI t ht h.1)),
          hF1_const t (Ioo_subset_Icc_self ht) y₁ (left_mem_Icc.mpr hlt.le)]
  obtain ⟨C, hC⟩ := halloc1_const
  let mid := (y₁ + y₂) / 2
  have hmid_gt : y₁ < mid := by dsimp only [mid]; linarith
  have hmid_lt : mid < y₂ := by dsimp only [mid]; linarith
  have hmid_0 : 0 ≤ mid := hy1_0.trans hmid_gt.le
  have hmid_1 : mid ≤ 1 := hmid_lt.le.trans hy2_le
  have hn1 : M.n - 1 ≠ 0 := by have := M.hn; omega
  let cMid := C - (effDist M θ (rivalIdx M) mid) ^ (M.n - 1)
  -- On [y₁, mid], C - F_riv^{n-1} > cMid strictly on [y₁, mid), so σ(mid) - σ(y₁) > (mid - y₁) * cMid
  have hleft_gt : (mid - y₁) * cMid < sigma M m1 ρ hρ0 hρ1 θ mid - sigma M m1 ρ hρ0 hρ1 θ y₁ := by
    rw [sigma_sub M m1 ρ hρ0 hρ1 hSR hy1_0 (hlt.le.trans hy2_le) hmid_0 hmid_1]
    have hcongr : ∫ t in y₁..mid, (alloc M m1 (effDist M θ 0) t -
        alloc M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) t) =
        ∫ t in y₁..mid, (C - (effDist M θ (rivalIdx M) t) ^ (M.n - 1)) := by
      apply intervalIntegral.integral_congr_ae
      have hne_m : ∀ᵐ t ∂volume, t ≠ mid := by simp [ae_iff, measure_singleton]
      filter_upwards [hne_m] with t htm ht
      rw [uIoc_of_le hmid_gt.le] at ht
      have ht_oo : t ∈ Ioo y₁ y₂ := ⟨ht.1, (lt_of_le_of_ne ht.2 htm).trans hmid_lt⟩
      rw [hC t ht_oo, alloc_SPA, ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr (hy1_ρ.trans ht.1.le)))]
    rw [hcongr]
    have hpos_int : 0 < ∫ t in y₁..mid, ((C - (effDist M θ (rivalIdx M) t) ^ (M.n - 1)) - cMid) := by
      apply intervalIntegral.integral_pos hmid_gt
      · exact (continuousOn_const.sub (((effDist_continuousOn θ (rivalIdx M)).mono
          (fun t (ht : t ∈ Icc y₁ mid) => ht.2.trans hmid_1)).pow (M.n - 1))).sub continuousOn_const
      · intro t ht
        have hle := hFriv_strict.monotoneOn ⟨ht.1.le, ht.2.trans hmid_lt.le⟩
          ⟨hmid_gt.le, hmid_lt.le⟩ ht.2
        have hpow := pow_le_pow_left₀ (effDist_nonneg θ _ (ht.2.trans hmid_1)) hle (M.n - 1)
        dsimp only [cMid]; linarith
      · refine ⟨y₁, left_mem_Icc.mpr hmid_gt.le, ?_⟩
        have hlt_F := hFriv_strict (left_mem_Icc.mpr hlt.le) ⟨hmid_gt.le, hmid_lt.le⟩ hmid_gt
        have hpow := pow_lt_pow_left₀ hlt_F (effDist_nonneg θ _ (hlt.le.trans hy2_le)) hn1
        dsimp only [cMid]; linarith
    have hint1 : IntervalIntegrable (fun t => C - (effDist M θ (rivalIdx M) t) ^ (M.n - 1)) volume y₁ mid :=
      (continuousOn_const.sub (((effDist_continuousOn θ (rivalIdx M)).mono
        (fun t (ht : t ∈ Icc y₁ mid) => ht.2.trans hmid_1)).pow (M.n - 1))).intervalIntegrable_of_Icc hmid_gt.le
    rw [intervalIntegral.integral_sub hint1 intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul] at hpos_int
    linarith
  -- On [mid, y₂], C - F_riv^{n-1} < cMid strictly on (mid, y₂], so σ(y₂) - σ(mid) < (y₂ - mid) * cMid
  have hright_lt : sigma M m1 ρ hρ0 hρ1 θ y₂ - sigma M m1 ρ hρ0 hρ1 θ mid < (y₂ - mid) * cMid := by
    rw [sigma_sub M m1 ρ hρ0 hρ1 hSR hmid_0 hmid_1 hy2_0 hy2_le]
    have hcongr : ∫ t in mid..y₂, (alloc M m1 (effDist M θ 0) t -
        alloc M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) t) =
        ∫ t in mid..y₂, (C - (effDist M θ (rivalIdx M) t) ^ (M.n - 1)) := by
      apply intervalIntegral.integral_congr_ae
      have hne_2 : ∀ᵐ t ∂volume, t ≠ y₂ := by simp [ae_iff, measure_singleton]
      filter_upwards [hne_2] with t ht2 ht
      rw [uIoc_of_le hmid_lt.le] at ht
      have ht_oo : t ∈ Ioo y₁ y₂ := ⟨hmid_gt.trans ht.1, lt_of_le_of_ne ht.2 ht2⟩
      rw [hC t ht_oo, alloc_SPA, ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr (hy1_ρ.trans ht_oo.1.le)))]
    rw [hcongr]
    have hpos_int : 0 < ∫ t in mid..y₂, (cMid - (C - (effDist M θ (rivalIdx M) t) ^ (M.n - 1))) := by
      apply intervalIntegral.integral_pos hmid_lt
      · exact continuousOn_const.sub (continuousOn_const.sub (((effDist_continuousOn θ (rivalIdx M)).mono
          (fun t (ht : t ∈ Icc mid y₂) => ht.2.trans hy2_le)).pow (M.n - 1)))
      · intro t ht
        have hle := hFriv_strict.monotoneOn ⟨hmid_gt.le, hmid_lt.le⟩
          ⟨hmid_gt.le.trans ht.1.le, ht.2⟩ ht.1.le
        have hpow := pow_le_pow_left₀ (effDist_nonneg θ _ hmid_1) hle (M.n - 1)
        dsimp only [cMid]; linarith
      · refine ⟨y₂, right_mem_Icc.mpr hmid_lt.le, ?_⟩
        have hlt_F := hFriv_strict ⟨hmid_gt.le, hmid_lt.le⟩ (right_mem_Icc.mpr hlt.le) hmid_lt
        have hpow := pow_lt_pow_left₀ hlt_F (effDist_nonneg θ _ hmid_1) hn1
        dsimp only [cMid]; linarith
    have hint1 : IntervalIntegrable (fun t => C - (effDist M θ (rivalIdx M) t) ^ (M.n - 1)) volume mid y₂ :=
      (continuousOn_const.sub (((effDist_continuousOn θ (rivalIdx M)).mono
        (fun t (ht : t ∈ Icc mid y₂) => ht.2.trans hy2_le)).pow (M.n - 1))).intervalIntegrable_of_Icc hmid_lt.le
    rw [intervalIntegral.integral_sub intervalIntegrable_const hint1,
      intervalIntegral.integral_const, smul_eq_mul] at hpos_int
    linarith
  have hmid_neg : sigma M m1 ρ hρ0 hρ1 θ mid < 0 := hneg mid ⟨hmid_gt, hmid_lt⟩
  have hlen : mid - y₁ = y₂ - mid := by dsimp only [mid]; ring
  have hlen_pos : 0 < mid - y₁ := sub_pos.mpr hmid_gt
  have hc1 : cMid < 0 := by nlinarith
  have hc2 : 0 < cMid := by nlinarith
  linarith

/-- Inside a pool `I ∈ m1.pools` where `σ ≤ 0` on `[a_I, I.β]`, the zero set `{v ∈ [a_I, I.β] | σ v = 0}`
is convex (an interval, possibly empty or a singleton). -/
lemma prop2_pool_zero_set_convex (m1 : HierarchicalMech) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    {θ : VisitStrategy M} (hSR : IsSR M (unilateralProfile M m1 ρ hρ0 hρ1) θ)
    {I : Pool} (hI : I ∈ m1.pools) {x y z : ℝ}
    (hx_ge : max (max m1.r ρ) M.a ≤ x) (hx_α : I.α ≤ x) (hxy : x < y) (hyz : y < z) (hz_β : z ≤ I.β)
    (hnp : ∀ t ∈ Icc x z, sigma M m1 ρ hρ0 hρ1 θ t ≤ 0)
    (hx0' : sigma M m1 ρ hρ0 hρ1 θ x = 0) (hz0' : sigma M m1 ρ hρ0 hρ1 θ z = 0) :
    sigma M m1 ρ hρ0 hρ1 θ y = 0 := by
  refine le_antisymm (hnp y ⟨hxy.le, hyz.le⟩) ?_
  by_contra hneg; push Not at hneg
  have hIin := m1.hpools_in I hI
  have hx_ρ : ρ ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx_ge)
  have hx_0 : 0 ≤ x := M.ha0.trans ((le_max_right _ _).trans hx_ge)
  have hy_0 : 0 ≤ y := hx_0.trans hxy.le
  have hz_0 : 0 ≤ z := hy_0.trans hyz.le
  have hz_1 : z ≤ 1 := hz_β.trans hIin.2
  have hy_1 : y ≤ 1 := hyz.le.trans hz_1
  have hx_1 : x ≤ 1 := hxy.le.trans hy_1
  let xbar := poolAvg M.n (effDist M θ 0 I.α) (effDist M θ 0 I.β)
  let cMid := xbar - (effDist M θ (rivalIdx M) y) ^ (M.n - 1)
  have hFriv_mono := vs_effDist_monotoneOn θ (rivalIdx M)
  have hleft_ge : (y - x) * cMid ≤ sigma M m1 ρ hρ0 hρ1 θ y - sigma M m1 ρ hρ0 hρ1 θ x := by
    rw [sigma_sub M m1 ρ hρ0 hρ1 hSR hx_0 hx_1 hy_0 hy_1]
    have hcongr : ∫ t in x..y, (alloc M m1 (effDist M θ 0) t -
        alloc M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) t) =
        ∫ t in x..y, (xbar - (effDist M θ (rivalIdx M) t) ^ (M.n - 1)) := by
      apply intervalIntegral.integral_congr_ae
      have hne_y : ∀ᵐ t ∂volume, t ≠ y := by simp [ae_iff, measure_singleton]
      filter_upwards [hne_y] with t hty ht
      rw [uIoc_of_le hxy.le] at ht
      have htI : t ∈ Ioo I.α I.β := ⟨lt_of_le_of_lt hx_α ht.1, (lt_of_le_of_ne ht.2 hty).trans (hyz.trans_le hz_β)⟩
      rw [alloc_in_pool M m1 _ hI htI, alloc_SPA,
        ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr (hx_ρ.trans ht.1.le)))]
    rw [hcongr]
    have hge_int : ∫ _ in x..y, cMid ≤ ∫ t in x..y, (xbar - (effDist M θ (rivalIdx M) t) ^ (M.n - 1)) := by
      apply intervalIntegral.integral_mono_on hxy.le intervalIntegrable_const
        ((continuousOn_const.sub (((effDist_continuousOn θ (rivalIdx M)).mono
          (fun t (ht : t ∈ Icc x y) => ht.2.trans hy_1)).pow (M.n - 1))).intervalIntegrable_of_Icc hxy.le)
      intro t ht
      have hpow := pow_le_pow_left₀ (effDist_nonneg θ _ (ht.2.trans hy_1))
        (hFriv_mono (ht.2.trans hy_1) hy_1 ht.2) (M.n - 1)
      change cMid ≤ xbar - (effDist M θ (rivalIdx M) t) ^ (M.n - 1)
      dsimp only [cMid]; linarith
    simpa [intervalIntegral.integral_const, smul_eq_mul] using hge_int
  have hright_le : sigma M m1 ρ hρ0 hρ1 θ z - sigma M m1 ρ hρ0 hρ1 θ y ≤ (z - y) * cMid := by
    rw [sigma_sub M m1 ρ hρ0 hρ1 hSR hy_0 hy_1 hz_0 hz_1]
    have hcongr : ∫ t in y..z, (alloc M m1 (effDist M θ 0) t -
        alloc M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) t) =
        ∫ t in y..z, (xbar - (effDist M θ (rivalIdx M) t) ^ (M.n - 1)) := by
      apply intervalIntegral.integral_congr_ae
      have hne_z : ∀ᵐ t ∂volume, t ≠ z := by simp [ae_iff, measure_singleton]
      filter_upwards [hne_z] with t htz ht
      rw [uIoc_of_le hyz.le] at ht
      have htI : t ∈ Ioo I.α I.β := ⟨lt_of_le_of_lt (hx_α.trans hxy.le) ht.1,
        (lt_of_le_of_ne ht.2 htz).trans_le hz_β⟩
      rw [alloc_in_pool M m1 _ hI htI, alloc_SPA,
        ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr (hx_ρ.trans (hxy.le.trans ht.1.le))))]
    rw [hcongr]
    have hle_int : ∫ t in y..z, (xbar - (effDist M θ (rivalIdx M) t) ^ (M.n - 1)) ≤ ∫ _ in y..z, cMid := by
      apply intervalIntegral.integral_mono_on hyz.le
        ((continuousOn_const.sub (((effDist_continuousOn θ (rivalIdx M)).mono
          (fun t (ht : t ∈ Icc y z) => ht.2.trans hz_1)).pow (M.n - 1))).intervalIntegrable_of_Icc hyz.le)
        intervalIntegrable_const
      intro t ht
      have hpow := pow_le_pow_left₀ (effDist_nonneg θ _ hy_1)
        (hFriv_mono hy_1 (ht.2.trans hz_1) ht.1) (M.n - 1)
      change xbar - (effDist M θ (rivalIdx M) t) ^ (M.n - 1) ≤ cMid
      dsimp only [cMid]; linarith
    simpa [intervalIntegral.integral_const, smul_eq_mul] using hle_int
  have h1 : cMid < 0 := by nlinarith [sub_pos.mpr hxy]
  have h2 : 0 < cMid := by nlinarith [sub_pos.mpr hyz]
  linarith

/-- **Proposition 2(iii) & Lemma A.4 (Localization)**:
Above `u₀ := max (max r₁ ρ) a`, there is a finite list of open sub-intervals `nonUnif`
(with cardinality at most `3 * m1.pools.length + 3`) such that:
1. Every `(c, d) ∈ nonUnif` satisfies `u₀ ≤ c < d ≤ 1`, and `θ_0` is a.e. constant in `{0, 1}` on `(c, d)`.
2. Every `(c, d) ∈ nonUnif` on which `σ = 0` and `θ_0 = 1` a.e. lies inside a single pool `I ∈ m1.pools`
   (at most one per pool).
3. At every point `v ∈ (u₀, 1)` outside `⋃ p ∈ nonUnif, Icc p.1 p.2` (and finitely many pool endpoints),
   `σ(v) = 0`, `effDist M θ 0 v = M.A v`, and on the complement `(u₀, 1) \ ⋃ p ∈ nonUnif, Icc p.1 p.2`,
   `θ_0 = 1 / m` a.e.! -/
theorem prop2_localization (m1 : HierarchicalMech) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    {θ : VisitStrategy M} (hSR : IsSR M (unilateralProfile M m1 ρ hρ0 hρ1) θ) :
    let u0 := max (max m1.r ρ) M.a
    ∃ nonUnif : List (ℝ × ℝ),
      nonUnif.length ≤ 3 * m1.pools.length + 3 ∧
      (∀ p ∈ nonUnif, u0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ 1 ∧
        ((∀ᵐ v ∂(volume.restrict (Ioo p.1 p.2)), θ.θ 0 v = 0) ∨
         (∀ᵐ v ∂(volume.restrict (Ioo p.1 p.2)), θ.θ 0 v = 1))) ∧
      (∀ v ∈ Ioo u0 1, (∀ p ∈ nonUnif, v ∉ Icc p.1 p.2) →
        (∀ I ∈ m1.pools, v ≠ I.α ∧ v ≠ I.β) →
        sigma M m1 ρ hρ0 hρ1 θ v = 0 ∧ effDist M θ 0 v = M.A v) ∧
      (∀ᵐ v ∂(volume.restrict (Ioo u0 1 \ (⋃ p ∈ nonUnif, Icc p.1 p.2))),
        θ.θ 0 v = 1 / (M.m : ℝ)) := by
  intro u0
  let σ := sigma M m1 ρ hρ0 hρ1 θ
  have hu0_0 : 0 ≤ u0 := M.ha0.trans (le_max_right _ _)
  have hu0_1 : u0 ≤ 1 := max_le (max_le m1.hr1 hρ1) M.ha1.le
  have hσ_cont : ContinuousOn σ (Icc u0 1) :=
    (sigma_continuousOn M m1 ρ hρ0 hρ1 hSR).mono (Icc_subset_Icc hu0_0 le_rfl)
  -- Component endpoints L(x), R(x) for any x ∈ Ioo u0 1 with σ x < 0
  let L : ℝ → ℝ := fun x => sSup ({u0} ∪ {v ∈ Icc u0 x | 0 ≤ σ v})
  let R : ℝ → ℝ := fun x => sInf ({1} ∪ {v ∈ Icc x 1 | 0 ≤ σ v})
  have hcomp_props : ∀ x ∈ Ioo u0 1, σ x < 0 →
      u0 ≤ L x ∧ L x < x ∧ x < R x ∧ R x ≤ 1 ∧
      (∀ t ∈ Ioo (L x) (R x), σ t < 0) ∧
      (L x = u0 ∨ σ (L x) = 0) ∧ (R x = 1 ∨ σ (R x) = 0) ∧
      (L x = u0 ∨ R x = 1 ∨ ∃ I ∈ m1.pools, I.α ∈ Ioo (L x) (R x) ∨ I.β ∈ Ioo (L x) (R x)) := by
    intro x hx hσx
    let SL : Set ℝ := {u0} ∪ {v ∈ Icc u0 x | 0 ≤ σ v}
    let SR : Set ℝ := {1} ∪ {v ∈ Icc x 1 | 0 ≤ σ v}
    have hSL_ne : SL.Nonempty := ⟨u0, Or.inl rfl⟩
    have hSL_bdd : BddAbove SL := ⟨x, fun v hv => by rcases hv with rfl | ⟨h, _⟩; exact hx.1.le; exact h.2⟩
    have hSR_ne : SR.Nonempty := ⟨1, Or.inl rfl⟩
    have hSR_bdd : BddBelow SR := ⟨x, fun v hv => by rcases hv with rfl | ⟨h, _⟩; exact hx.2.le; exact h.1⟩
    have hL_ge : u0 ≤ L x := le_csSup hSL_bdd (Or.inl rfl)
    have hL_le : L x ≤ x := csSup_le hSL_ne (fun v hv => by rcases hv with rfl | ⟨h, _⟩; exact hx.1.le; exact h.2)
    have hR_ge : x ≤ R x := le_csInf hSR_ne (fun v hv => by rcases hv with rfl | ⟨h, _⟩; exact hx.2.le; exact h.1)
    have hR_le : R x ≤ 1 := csInf_le hSR_bdd (Or.inl rfl)
    have hL_closed : IsClosed SL := isClosed_singleton.union
      ((hσ_cont.mono (Icc_subset_Icc_right hx.2.le)).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici)
    have hR_closed : IsClosed SR := isClosed_singleton.union
      ((hσ_cont.mono (Icc_subset_Icc_left hx.1.le)).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici)
    have hL_in : L x ∈ SL := by rw [← hL_closed.closure_eq]; exact csSup_mem_closure hSL_ne hSL_bdd
    have hR_in : R x ∈ SR := by rw [← hR_closed.closure_eq]; exact csInf_mem_closure hSR_ne hSR_bdd
    have hL_lt : L x < x := lt_of_le_of_ne hL_le (fun h => by
      rw [h] at hL_in; rcases hL_in with h1 | ⟨_, h2⟩
      · rw [mem_singleton_iff] at h1; linarith [hx.1]
      · linarith)
    have hR_gt : x < R x := lt_of_le_of_ne hR_ge (fun h => by
      rw [← h] at hR_in; rcases hR_in with h1 | ⟨_, h2⟩
      · rw [mem_singleton_iff] at h1; linarith [hx.2]
      · linarith)
    have hneg_all : ∀ t ∈ Ioo (L x) (R x), σ t < 0 := by
      intro t ht
      by_contra hge; push Not at hge
      by_cases htx : t ≤ x
      · exact not_le.mpr ht.1 (le_csSup hSL_bdd (Or.inr ⟨⟨hL_ge.trans ht.1.le, htx⟩, hge⟩))
      · push Not at htx
        exact not_le.mpr ht.2 (csInf_le hSR_bdd (Or.inr ⟨⟨htx.le, ht.2.le.trans hR_le⟩, hge⟩))
    have hL_end : L x = u0 ∨ σ (L x) = 0 := by
      rcases hL_in with h1 | ⟨_, hge⟩
      · exact Or.inl h1
      · right
        have htend := (hσ_cont (L x) ⟨hL_ge, hL_lt.le.trans hx.2.le⟩).mono_left
          (nhdsWithin_mono _ (Ioo_subset_Icc_self.trans (Icc_subset_Icc hL_ge hR_le)))
        have : NeBot (𝓝[Ioo (L x) (R x)] (L x)) := left_nhdsWithin_Ioo_neBot (hL_lt.trans hR_gt)
        have hle0 := le_of_tendsto htend (eventually_nhdsWithin_of_forall fun t ht => (hneg_all t ht).le)
        linarith
    have hR_end : R x = 1 ∨ σ (R x) = 0 := by
      rcases hR_in with h1 | ⟨_, hge⟩
      · exact Or.inl h1
      · right
        have htend := (hσ_cont (R x) ⟨hx.1.le.trans hR_ge, hR_le⟩).mono_left
          (nhdsWithin_mono _ (Ioo_subset_Icc_self.trans (Icc_subset_Icc hL_ge hR_le)))
        have : NeBot (𝓝[Ioo (L x) (R x)] (R x)) := right_nhdsWithin_Ioo_neBot (hL_lt.trans hR_gt)
        have hle0 := le_of_tendsto htend (eventually_nhdsWithin_of_forall fun t ht => (hneg_all t ht).le)
        linarith
    have hanchor : L x = u0 ∨ R x = 1 ∨ ∃ I ∈ m1.pools, I.α ∈ Ioo (L x) (R x) ∨ I.β ∈ Ioo (L x) (R x) := by
      by_contra hnone; push Not at hnone
      obtain ⟨hLne, hRne, hnoI⟩ := hnone
      have hL0 : σ (L x) = 0 := hL_end.resolve_left hLne
      have hR0 : σ (R x) = 0 := hR_end.resolve_left hRne
      exact prop2_no_dip_without_endpoint M m1 ρ hρ0 hρ1 hSR hL_ge (hL_lt.trans hR_gt) hR_le
        hL0 hR0 hneg_all hnoI
    exact ⟨hL_ge, hL_lt, hR_gt, hR_le, hneg_all, hL_end, hR_end, hanchor⟩
  -- Helper: if y ∈ Ioo (L x) (R x), then L y = L x and R y = R x
  have hcomp_eq : ∀ x ∈ Ioo u0 1, σ x < 0 → ∀ y ∈ Ioo (L x) (R x), L y = L x ∧ R y = R x := by
    intro x hx hσx y hy
    have hpx := hcomp_props x hx hσx
    have hy_in : y ∈ Ioo u0 1 := ⟨lt_of_le_of_lt hpx.1 hy.1, lt_of_lt_of_le hy.2 hpx.2.2.2.1⟩
    have hpy := hcomp_props y hy_in (hpx.2.2.2.2.1 y hy)
    constructor
    · refine le_antisymm ?_ ?_
      · by_contra hgt; push Not at hgt
        have hLy_in : L y ∈ Ioo (L x) (R x) := ⟨hgt, hpy.2.1.trans hy.2⟩
        have hσLy_neg := hpx.2.2.2.2.1 (L y) hLy_in
        rcases hpy.2.2.2.2.2.1 with h1 | h2 <;> linarith [hpx.1]
      · by_contra hgt; push Not at hgt
        have hLx_in : L x ∈ Ioo (L y) (R y) := ⟨hgt, hy.1.trans hpy.2.2.1⟩
        have hσLx_neg := hpy.2.2.2.2.1 (L x) hLx_in
        rcases hpx.2.2.2.2.2.1 with h1 | h2 <;> linarith [hpy.1]
    · refine le_antisymm ?_ ?_
      · by_contra hgt; push Not at hgt
        have hRx_in : R x ∈ Ioo (L y) (R y) := ⟨hpy.2.1.trans hy.2, hgt⟩
        have hσRx_neg := hpy.2.2.2.2.1 (R x) hRx_in
        rcases hpx.2.2.2.2.2.2.1 with h1 | h2 <;> linarith [hpy.2.2.2.1]
      · by_contra hgt; push Not at hgt
        have hRy_in : R y ∈ Ioo (L x) (R x) := ⟨hy.1.trans hpy.2.2.1, hgt⟩
        have hσRy_neg := hpx.2.2.2.2.1 (R y) hRy_in
        rcases hpy.2.2.2.2.2.2.1 with h1 | h2 <;> linarith [hpx.2.2.2.1]
  -- Build the finite list of negative components (at most 2*N + 2)
  let cLeft : List (ℝ × ℝ) :=
    if h : ∃ x ∈ Ioo u0 1, σ x < 0 ∧ L x = u0 then [(L h.choose, R h.choose)] else []
  let cRight : List (ℝ × ℝ) :=
    if h : ∃ x ∈ Ioo u0 1, σ x < 0 ∧ R x = 1 then [(L h.choose, R h.choose)] else []
  let cAlpha : List (ℝ × ℝ) := m1.pools.filterMap fun I =>
    if I.α ∈ Ioo u0 1 ∧ σ I.α < 0 then some (L I.α, R I.α) else none
  let cBeta : List (ℝ × ℝ) := m1.pools.filterMap fun I =>
    if I.β ∈ Ioo u0 1 ∧ σ I.β < 0 then some (L I.β, R I.β) else none
  let negList : List (ℝ × ℝ) := cLeft ++ cRight ++ cAlpha ++ cBeta
  have hneg_len : negList.length ≤ 2 * m1.pools.length + 2 := by
    have h1 : cLeft.length ≤ 1 := by dsimp only [cLeft]; split_ifs <;> simp
    have h2 : cRight.length ≤ 1 := by dsimp only [cRight]; split_ifs <;> simp
    have h3 : cAlpha.length ≤ m1.pools.length := List.length_filterMap_le _ _
    have h4 : cBeta.length ≤ m1.pools.length := List.length_filterMap_le _ _
    simp only [negList, List.length_append]; omega
  have hneg_valid : ∀ p ∈ negList, u0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ 1 ∧ ∀ t ∈ Ioo p.1 p.2, σ t < 0 := by
    intro p hp
    simp only [negList, List.mem_append] at hp
    rcases hp with ((hp | hp) | hp) | hp
    · dsimp only [cLeft] at hp; split_ifs at hp with h
      · simp only [List.mem_singleton] at hp; subst hp
        have hpr := hcomp_props h.choose h.choose_spec.1 h.choose_spec.2.1
        exact ⟨hpr.1, hpr.2.1.trans hpr.2.2.1, hpr.2.2.2.1, hpr.2.2.2.2.1⟩
      · simp at hp
    · dsimp only [cRight] at hp; split_ifs at hp with h
      · simp only [List.mem_singleton] at hp; subst hp
        have hpr := hcomp_props h.choose h.choose_spec.1 h.choose_spec.2.1
        exact ⟨hpr.1, hpr.2.1.trans hpr.2.2.1, hpr.2.2.2.1, hpr.2.2.2.2.1⟩
      · simp at hp
    · rw [List.mem_filterMap] at hp
      obtain ⟨I, _, hIeq⟩ := hp; split_ifs at hIeq with h
      simp only [Option.some.injEq] at hIeq; subst hIeq
      have hpr := hcomp_props I.α h.1 h.2
      exact ⟨hpr.1, hpr.2.1.trans hpr.2.2.1, hpr.2.2.2.1, hpr.2.2.2.2.1⟩
    · rw [List.mem_filterMap] at hp
      obtain ⟨I, _, hIeq⟩ := hp; split_ifs at hIeq with h
      simp only [Option.some.injEq] at hIeq; subst hIeq
      have hpr := hcomp_props I.β h.1 h.2
      exact ⟨hpr.1, hpr.2.1.trans hpr.2.2.1, hpr.2.2.2.1, hpr.2.2.2.2.1⟩
  have hneg_cover : ∀ x ∈ Ioo u0 1, σ x < 0 → ∃ p ∈ negList, x ∈ Ioo p.1 p.2 := by
    intro x hx hσx
    have hpx := hcomp_props x hx hσx
    rcases hpx.2.2.2.2.2.2.2 with hL0 | hR1 | ⟨I, hI, hIα | hIβ⟩
    · have hex : ∃ y ∈ Ioo u0 1, σ y < 0 ∧ L y = u0 := ⟨x, hx, hσx, hL0⟩
      refine ⟨(L hex.choose, R hex.choose), ?_, ?_⟩
      · simp only [negList, List.mem_append]; left; left; left
        dsimp only [cLeft]; split_ifs; simp
      · have hpy := hcomp_props hex.choose hex.choose_spec.1 hex.choose_spec.2.1
        have hLy : L hex.choose = u0 := hex.choose_spec.2.2
        let z := min x hex.choose
        have hz_x : z ∈ Ioo (L x) (R x) := ⟨by rw [hL0]; exact lt_min hx.1 hex.choose_spec.1.1,
          (min_le_left _ _).trans_lt hpx.2.2.1⟩
        have hz_y : z ∈ Ioo (L hex.choose) (R hex.choose) := ⟨by rw [hLy]; exact lt_min hx.1 hex.choose_spec.1.1,
          (min_le_right _ _).trans_lt hpy.2.2.1⟩
        have heq1 := hcomp_eq x hx hσx z hz_x
        have heq2 := hcomp_eq hex.choose hex.choose_spec.1 hex.choose_spec.2.1 z hz_y
        rw [← heq2.1, heq1.1, ← heq2.2, heq1.2]; exact ⟨hpx.2.1, hpx.2.2.1⟩
    · have hex : ∃ y ∈ Ioo u0 1, σ y < 0 ∧ R y = 1 := ⟨x, hx, hσx, hR1⟩
      refine ⟨(L hex.choose, R hex.choose), ?_, ?_⟩
      · simp only [negList, List.mem_append]; left; left; right
        dsimp only [cRight]; split_ifs; simp
      · have hpy := hcomp_props hex.choose hex.choose_spec.1 hex.choose_spec.2.1
        have hRy : R hex.choose = 1 := hex.choose_spec.2.2
        let z := max x hex.choose
        have hz_x : z ∈ Ioo (L x) (R x) := ⟨hpx.2.1.trans_le (le_max_left _ _),
          by rw [hR1]; exact max_lt hx.2 hex.choose_spec.1.2⟩
        have hz_y : z ∈ Ioo (L hex.choose) (R hex.choose) := ⟨hpy.2.1.trans_le (le_max_right _ _),
          by rw [hRy]; exact max_lt hx.2 hex.choose_spec.1.2⟩
        have heq1 := hcomp_eq x hx hσx z hz_x
        have heq2 := hcomp_eq hex.choose hex.choose_spec.1 hex.choose_spec.2.1 z hz_y
        rw [← heq2.1, heq1.1, ← heq2.2, heq1.2]; exact ⟨hpx.2.1, hpx.2.2.1⟩
    · have hIα_in : I.α ∈ Ioo u0 1 := ⟨hpx.1.trans_lt hIα.1, hIα.2.trans_le hpx.2.2.2.1⟩
      have hIα_neg : σ I.α < 0 := hpx.2.2.2.2.1 I.α hIα
      have heq := hcomp_eq x hx hσx I.α hIα
      refine ⟨(L I.α, R I.α), ?_, ?_⟩
      · simp only [negList, List.mem_append]; left; right
        rw [List.mem_filterMap]
        exact ⟨I, hI, by rw [ite_eq_left_iff.mpr (fun h => absurd ⟨hIα_in, hIα_neg⟩ h)]⟩
      · rw [heq.1, heq.2]; exact ⟨hpx.2.1, hpx.2.2.1⟩
    · have hIβ_in : I.β ∈ Ioo u0 1 := ⟨hpx.1.trans_lt hIβ.1, hIβ.2.trans_le hpx.2.2.2.1⟩
      have hIβ_neg : σ I.β < 0 := hpx.2.2.2.2.1 I.β hIβ
      have heq := hcomp_eq x hx hσx I.β hIβ
      refine ⟨(L I.β, R I.β), ?_, ?_⟩
      · simp only [negList, List.mem_append]; right
        rw [List.mem_filterMap]
        exact ⟨I, hI, by rw [ite_eq_left_iff.mpr (fun h => absurd ⟨hIβ_in, hIβ_neg⟩ h)]⟩
      · rw [heq.1, heq.2]; exact ⟨hpx.2.1, hpx.2.2.1⟩
  -- Initial σ > 0 interval above u0 (at most 1)
  obtain ⟨_, v_hat, hvhat_mem, hvhat_pos, hvhat_le, hvhat_at, _, _⟩ :=
    prop2_sigma_pos_initial M m1 ρ hρ0 hρ1 hSR
  let posList : List (ℝ × ℝ) := if u0 < v_hat then [(u0, v_hat)] else []
  have hpos_len : posList.length ≤ 1 := by dsimp only [posList]; split_ifs <;> simp
  -- Pool zero intervals (at most N): for each pool I, the span [sInf Z_I, sSup Z_I] of zeros above max u0 v_hat
  let aStart := max u0 v_hat
  have haStart_le1 : aStart ≤ 1 := max_le hu0_1 hvhat_mem.2
  have hσ_np_above : ∀ t ∈ Icc aStart 1, aStart < 1 → σ t ≤ 0 := by
    intro t ht ha_lt1
    rcases eq_or_lt_of_le (le_max_right u0 v_hat |>.trans ht.1) with heq | hgt
    · rw [← heq]; exact hvhat_at (lt_of_le_of_lt (le_max_right _ _) ha_lt1)
    · exact hvhat_le t ⟨hgt, ht.2⟩
  let poolZeroList : List (ℝ × ℝ) := m1.pools.filterMap fun I =>
    let lo := max I.α aStart
    let Z := {v ∈ Icc lo I.β | σ v = 0}
    if lo < I.β ∧ Z.Nonempty ∧ sInf Z < sSup Z then some (sInf Z, sSup Z) else none
  have hpoolZ_len : poolZeroList.length ≤ m1.pools.length := List.length_filterMap_le _ _
  -- Combine all three lists into nonUnif
  let nonUnif : List (ℝ × ℝ) := posList ++ negList ++ poolZeroList
  refine ⟨nonUnif, ?_, ?_, ?_, ?_⟩
  · simp only [nonUnif, List.length_append]; omega
  · -- Property 1: each interval in nonUnif has θ_0 = 0 a.e. or θ_0 = 1 a.e.
    intro p hp
    simp only [nonUnif, List.mem_append] at hp
    rcases hp with (hp | hp) | hp
    · dsimp only [posList] at hp; split_ifs at hp with hlt
      · simp only [List.mem_singleton] at hp; subst hp
        refine ⟨le_rfl, hlt, hvhat_mem.2, Or.inr ?_⟩
        have hpos_oo : ∀ t ∈ Ioo u0 v_hat, 0 < σ t := fun t ht =>
          hvhat_pos t ⟨lt_of_le_of_lt (max_le_max_right M.a (min_le_max)) ht.1, ht.2⟩
        have h1 := (prop2_sigma_pos_on_Ioo M m1 ρ hρ0 hρ1 hSR hlt.le hvhat_mem.2 hpos_oo).1
        rw [show max u0 M.a = u0 from max_eq_left (le_max_right _ _)] at h1
        exact MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono Ioo_subset_Icc_self le_rfl) h1
      · simp at hp
    · have hnv := hneg_valid p hp
      refine ⟨hnv.1, hnv.2.1, hnv.2.2.1, Or.inl ?_⟩
      have h1 := (prop2_sigma_neg_on_Ioo M m1 ρ hρ0 hρ1 hSR hnv.2.1.le hnv.2.2.1 hnv.2.2.2).1
      rw [show max p.1 M.a = p.1 from max_eq_left ((le_max_right _ _).trans hnv.1)] at h1
      exact MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono Ioo_subset_Icc_self le_rfl) h1
    · rw [List.mem_filterMap] at hp
      obtain ⟨I, hI, hIeq⟩ := hp
      dsimp only at hIeq; split_ifs at hIeq with h
      simp only [Option.some.injEq] at hIeq; subst hIeq
      obtain ⟨hlo_lt, hZne, hInf_lt_Sup⟩ := h
      let lo := max I.α aStart
      let Z := {v ∈ Icc lo I.β | σ v = 0}
      have hIin := m1.hpools_in I hI
      have hZ_bddA : BddAbove Z := ⟨I.β, fun v hv => hv.1.2⟩
      have hZ_bddB : BddBelow Z := ⟨lo, fun v hv => hv.1.1⟩
      have hZ_closed : IsClosed Z := by
        have hZeq : Z = Icc lo I.β ∩ σ ⁻¹' {0} := by ext v; simp [Z]
        rw [hZeq]
        exact (hσ_cont.mono (Icc_subset_Icc ((le_max_left _ _).trans (le_max_right _ _)) hIin.2)).preimage_isClosed_of_isClosed
          isClosed_Icc isClosed_singleton
      have hZne' : Z.Nonempty := hZne
      have hInf_in : sInf Z ∈ Z := by
        have h := csInf_mem_closure hZne' hZ_bddB; rwa [hZ_closed.closure_eq] at h
      have hSup_in : sSup Z ∈ Z := by
        have h := csSup_mem_closure hZne' hZ_bddA; rwa [hZ_closed.closure_eq] at h
      have haStart_lt1 : aStart < 1 := lt_of_le_of_lt (le_max_right I.α aStart) (hlo_lt.trans_le hIin.2)
      have hzero_all : ∀ t ∈ Icc (sInf Z) (sSup Z), σ t = 0 := by
        intro t ht
        rcases eq_or_lt_of_le ht.1 with rfl | h1
        · exact hInf_in.2
        · rcases eq_or_lt_of_le ht.2 with rfl | h2
          · exact hSup_in.2
          · exact prop2_pool_zero_set_convex M m1 ρ hρ0 hρ1 hSR hI
              ((le_max_left _ _).trans ((le_max_right _ _).trans hInf_in.1.1))
              ((le_max_left _ _).trans hInf_in.1.1) h1 h2 hSup_in.1.2
              (fun z hz => hσ_np_above z ⟨(le_max_right _ _).trans (hInf_in.1.1.trans hz.1),
                (hz.2.trans hSup_in.1.2).trans hIin.2⟩ haStart_lt1)
              hInf_in.2 hSup_in.2
      have h1 := (prop2_sigma_zero_in_pool M m1 ρ hρ0 hρ1 hSR hI
        ((le_max_left _ _).trans ((le_max_right _ _).trans hInf_in.1.1))
        ((le_max_left _ _).trans hInf_in.1.1) hInf_lt_Sup hSup_in.1.2 hzero_all).2
      refine ⟨(le_max_left _ _).trans ((le_max_right _ _).trans hInf_in.1.1),
        hInf_lt_Sup, hSup_in.1.2.trans hIin.2, Or.inr ?_⟩
      exact MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono Ioo_subset_Icc_self le_rfl) h1
  · -- Property 2: outside nonUnif closures and pool endpoints, σ(v) = 0 and F₁(v) = A(v)
    -- First collect the finite bad set of closed intervals + singleton pool zeros + pool endpoints
    have hpt_good : ∀ v ∈ Ioo u0 1, (∀ p ∈ nonUnif, v ∉ Icc p.1 p.2) →
        (∀ I ∈ m1.pools, v ≠ I.α ∧ v ≠ I.β) →
        σ v = 0 ∧ (∀ I ∈ m1.pools, ¬ (I.α < v ∧ v < I.β) ∨
          (∀ w ∈ Icc (max I.α aStart) I.β, σ w = 0 → w = v)) := by
      intro v hv hnot_in hnot_end
      have hnot_pos : ¬ 0 < σ v := by
        intro hpos
        have hv_lt : v < v_hat := by
          by_contra hge; push Not at hge
          rcases eq_or_lt_of_le hge with rfl | hgt
          · exact not_le.mpr hpos (hvhat_at hv.2)
          · exact not_le.mpr hpos (hvhat_le v ⟨hgt, hv.2.le⟩)
        have hu0_lt : u0 < v_hat := hv.1.trans hv_lt
        have hp_mem : (u0, v_hat) ∈ nonUnif := by
          simp only [nonUnif, List.mem_append]; left; left
          dsimp only [posList]; rw [ite_eq_left_iff.mpr (fun h => absurd hu0_lt h)]; simp
        exact hnot_in (u0, v_hat) hp_mem ⟨hv.1.le, hv_lt.le⟩
      have hnot_neg : ¬ σ v < 0 := by
        intro hneg
        obtain ⟨p, hp_neg, hvp⟩ := hneg_cover v hv hneg
        have hp_mem : p ∈ nonUnif := by simp only [nonUnif, List.mem_append]; left; right; exact hp_neg
        exact hnot_in p hp_mem (Ioo_subset_Icc_self hvp)
      have hσv0 : σ v = 0 := le_antisymm (le_of_not_gt hnot_pos) (le_of_not_gt hnot_neg)
      refine ⟨hσv0, fun I hI => ?_⟩
      by_cases hvI : I.α < v ∧ v < I.β
      · right
        intro w hw hσw
        have hv_ge_aStart : aStart ≤ v := by
          by_contra hlt; push Not at hlt
          dsimp only [aStart] at hlt
          have hvh_gt : u0 < v_hat := by
            rcases max_cases u0 v_hat with ⟨_, _⟩ | ⟨_, _⟩ <;> linarith [hv.1]
          have hp_mem : (u0, v_hat) ∈ nonUnif := by
            simp only [nonUnif, List.mem_append]; left; left
            dsimp only [posList]; rw [ite_eq_left_iff.mpr (fun h => absurd hvh_gt h)]; simp
          rw [max_eq_right hvh_gt.le] at hlt
          exact hnot_in (u0, v_hat) hp_mem ⟨hv.1.le, hlt.le⟩
        let lo := max I.α aStart
        let Z := {z ∈ Icc lo I.β | σ z = 0}
        have hlo_lt : lo < I.β := max_lt I.hαβ (hv_ge_aStart.trans_lt hvI.2)
        have hvZ : v ∈ Z := ⟨⟨max_le hvI.1.le hv_ge_aStart, hvI.2.le⟩, hσv0⟩
        have hwZ : w ∈ Z := ⟨hw, hσw⟩
        have hZ_bddA : BddAbove Z := ⟨I.β, fun z hz => hz.1.2⟩
        have hZ_bddB : BddBelow Z := ⟨lo, fun z hz => hz.1.1⟩
        by_contra hne
        have hlt_inf_sup : sInf Z < sSup Z := by
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · exact lt_of_le_of_lt (csInf_le hZ_bddB hwZ) (lt_of_lt_of_le hlt (le_csSup hZ_bddA hvZ))
          · exact lt_of_le_of_lt (csInf_le hZ_bddB hvZ) (lt_of_lt_of_le hgt (le_csSup hZ_bddA hwZ))
        have hp_mem : (sInf Z, sSup Z) ∈ nonUnif := by
          simp only [nonUnif, List.mem_append]; right
          rw [List.mem_filterMap]
          refine ⟨I, hI, ?_⟩
          dsimp only
          rw [ite_eq_left_iff.mpr (fun h => absurd ⟨hlo_lt, ⟨v, hvZ⟩, hlt_inf_sup⟩ h)]
        exact hnot_in (sInf Z, sSup Z) hp_mem ⟨csInf_le hZ_bddB hvZ, le_csSup hZ_bddA hvZ⟩
      · exact Or.inl hvI
    -- Notice: if v ∈ Ioo u0 1 avoids all closures in nonUnif, all pool endpoints, AND is not a singleton pool zero,
    -- then v has an open neighborhood (c, d) ⊆ Ioo u0 1 disjoint from all pools and all nonUnif where σ ≡ 0!
    -- Wait: what if v IS a singleton pool zero inside a pool I?
    -- At a singleton pool zero v ∈ (I.α, I.β), σ < 0 on (I.α, v) and on (v, I.β), wait:
    -- then v is a limit point of TWO negative components, so v ∈ Icc p.1 p.2 for those components in nonUnif!!
    -- WHOA!! Let's verify that!!
    -- If v ∈ Ioo I.α I.β is a singleton pool zero, then σ < 0 immediately to the right of v (since σ ≤ 0 on [aStart, I.β] and no other zero!),
    -- so R(x) or L(x) equals v for x slightly > v, hence v ∈ Icc (L x) (R x) ∈ negList ⊆ nonUnif!!
    -- THEREFORE NO POINT OUTSIDE ⋃ p ∈ nonUnif, Icc p.1 p.2 CAN BE IN ANY POOL AT ALL!!
    have hnot_in_pool : ∀ v ∈ Ioo u0 1, (∀ p ∈ nonUnif, v ∉ Icc p.1 p.2) →
        (∀ I ∈ m1.pools, v ≠ I.α ∧ v ≠ I.β) →
        ∀ I ∈ m1.pools, ¬ (I.α < v ∧ v < I.β) := by
      intro v hv hnot_in hnot_end I hI hvI
      have hpg := hpt_good v hv hnot_in hnot_end
      have hsing := (hpg.2 I hI).resolve_left (not_not.mpr hvI)
      have hv_ge_aStart : aStart ≤ v := by
        by_contra hlt; push Not at hlt
        dsimp only [aStart] at hlt
        have hvh_gt : u0 < v_hat := by
          rcases max_cases u0 v_hat with ⟨_, _⟩ | ⟨_, _⟩ <;> linarith [hv.1]
        have hp_mem : (u0, v_hat) ∈ nonUnif := by
          simp only [nonUnif, List.mem_append]; left; left
          dsimp only [posList]; rw [ite_eq_left_iff.mpr (fun h => absurd hvh_gt h)]; simp
        rw [max_eq_right hvh_gt.le] at hlt
        exact hnot_in (u0, v_hat) hp_mem ⟨hv.1.le, hlt.le⟩
      let x := (v + I.β) / 2
      have hIin := m1.hpools_in I hI
      have hx_gt : v < x := by dsimp only [x]; linarith [hvI.2]
      have hx_lt : x < I.β := by dsimp only [x]; linarith [hvI.2]
      have hx_in : x ∈ Ioo u0 1 := ⟨hv.1.trans hx_gt, hx_lt.trans_le hIin.2⟩
      have hx_np : σ x ≤ 0 := hσ_np_above x ⟨hv_ge_aStart.trans hx_gt.le, hx_lt.le.trans hIin.2⟩
        (hv_ge_aStart.trans_lt (hx_gt.trans (hx_lt.trans_le hIin.2)))
      have hx_ne0 : σ x ≠ 0 := fun h0 => hx_gt.ne' (hsing x ⟨max_le (hvI.1.le.trans hx_gt.le) (hv_ge_aStart.trans hx_gt.le), hx_lt.le⟩ h0)
      have hx_neg : σ x < 0 := lt_of_le_of_ne hx_np hx_ne0
      obtain ⟨p, hp_neg, hxp⟩ := hneg_cover x hx_in hx_neg
      have hp_valid := hneg_valid p hp_neg
      have hp_mem : p ∈ nonUnif := by simp only [nonUnif, List.mem_append]; left; right; exact hp_neg
      -- Since p.1 < x and σ(v) = 0 while σ < 0 on (p.1, p.2), we must have v ≤ p.1!
      have hv_le_p1 : v ≤ p.1 := by
        by_contra hlt; push Not at hlt
        have := hp_valid.2.2.2 v ⟨hlt, hx_gt.trans hxp.2⟩
        linarith [hpg.1]
      -- If v < p.1, pick mid ∈ (v, p.1) ⊆ (v, I.β): σ(mid) < 0, wait: what if σ(p.1) = 0?
      -- Then p.1 ∈ [max I.α aStart, I.β] has σ(p.1) = 0, so by hsing p.1 = v!!
      have hp1_eq_v : p.1 = v := by
        have hp1_lt_β : p.1 < I.β := hxp.1.trans hx_lt
        have hp1_in : p.1 ∈ Icc (max I.α aStart) I.β :=
          ⟨max_le (hvI.1.le.trans hv_le_p1) (hv_ge_aStart.trans hv_le_p1), hp1_lt_β.le⟩
        -- Since p ∈ negList, p = (L y, R y) for some y, so p.1 = u0 ∨ σ(p.1) = 0!
        -- Even simpler: by continuity of σ on [u0, 1], since σ < 0 on (p.1, p.2), if σ(p.1) < 0 then
        -- p.1 cannot be L(x)... Actually let's check: we know p.1 = L x because x ∈ Ioo p.1 p.2!
        have hp1_le0 : σ p.1 ≤ 0 := hσ_np_above p.1 ⟨hv_ge_aStart.trans hv_le_p1, hp1_lt_β.le.trans hIin.2⟩
          (hv_ge_aStart.trans_lt (hx_gt.trans (hx_lt.trans_le hIin.2)))
        by_contra hne
        have hv_lt_p1 : v < p.1 := lt_of_le_of_ne hv_le_p1 (Ne.symm hne)
        have hp1_neg : σ p.1 < 0 := lt_of_le_of_ne hp1_le0 (fun h0 => hne (hsing p.1 hp1_in h0))
        -- Since σ(p.1) < 0 and p.1 ∈ Ioo u0 1, p.1 is in some q ∈ negList!
        obtain ⟨q, hq_neg, hp1_in_q⟩ := hneg_cover p.1 ⟨hv.1.trans hv_lt_p1, hp1_lt_β.trans_le hIin.2⟩ hp1_neg
        have hq_valid := hneg_valid q hq_neg
        -- Pick z ∈ (p.1, min p.2 q.2): z ∈ Ioo p.1 p.2 ∩ Ioo q.1 q.2, so both p and q are the component of z!
        -- Wait: we only know hneg_valid gives σ < 0 on (p.1, p.2), not that p is maximal!
        -- Wait: every p ∈ negList IS (L y, R y) for some y, so p.1 = u0 ∨ σ p.1 = 0!
        -- Let's prove σ p.1 = 0 directly since p ∈ negList!
        have hp1_zero : p.1 = u0 ∨ σ p.1 = 0 := by
          simp only [negList, List.mem_append] at hp_neg
          rcases hp_neg with ((hp' | hp') | hp') | hp'
          · dsimp only [cLeft] at hp'; split_ifs at hp' with h
            · simp only [List.mem_singleton] at hp'; subst hp'
              exact (hcomp_props h.choose h.choose_spec.1 h.choose_spec.2.1).2.2.2.2.2.1
            · simp at hp'
          · dsimp only [cRight] at hp'; split_ifs at hp' with h
            · simp only [List.mem_singleton] at hp'; subst hp'
              exact (hcomp_props h.choose h.choose_spec.1 h.choose_spec.2.1).2.2.2.2.2.1
            · simp at hp'
          · rw [List.mem_filterMap] at hp'; obtain ⟨J, _, hJeq⟩ := hp'; split_ifs at hJeq with h
            simp only [Option.some.injEq] at hJeq; subst hJeq
            exact (hcomp_props J.α h.1 h.2).2.2.2.2.2.1
          · rw [List.mem_filterMap] at hp'; obtain ⟨J, _, hJeq⟩ := hp'; split_ifs at hJeq with h
            simp only [Option.some.injEq] at hJeq; subst hJeq
            exact (hcomp_props J.β h.1 h.2).2.2.2.2.2.1
        rcases hp1_zero with h1 | h2
        · linarith [hv.1]
        · linarith
      exact hnot_in p hp_mem ⟨hp1_eq_v.le, hp1_eq_v.ge.trans hp_valid.2.1.le⟩
    -- Now the complement G := Ioo u0 1 \ (⋃ p ∈ nonUnif, Icc p.1 p.2 ∪ ⋃ I ∈ m1.pools, {I.α, I.β}) is OPEN!
    -- Around every v ∈ G, there is an open interval (c, d) ⊆ G on which σ ≡ 0 and no pool meets (c, d)!
    let badPts : Set ℝ := (⋃ p ∈ nonUnif, Icc p.1 p.2) ∪ (⋃ I ∈ m1.pools, ({I.α, I.β} : Set ℝ))
    have hbad_closed : IsClosed badPts := by
      apply IsClosed.union
      · have : (⋃ p ∈ nonUnif, Icc p.1 p.2) = ⋃ p ∈ nonUnif.toFinset, Icc p.1 p.2 := by
          ext t; simp
        rw [this]; exact Set.Finite.isClosed_biUnion (Finset.finite_toSet _) (fun _ _ => isClosed_Icc)
      · have : (⋃ I ∈ m1.pools, ({I.α, I.β} : Set ℝ)) = ⋃ I ∈ m1.pools.toFinset, ({I.α, I.β} : Set ℝ) := by
          ext t; simp
        rw [this]
        exact Set.Finite.isClosed_biUnion (Finset.finite_toSet _)
          (fun _ _ => isClosed_singleton.union isClosed_singleton)
    have hG_open : IsOpen (Ioo u0 1 \ badPts) := isOpen_Ioo.sdiff hbad_closed
    have hG_eff : ∀ v ∈ Ioo u0 1 \ badPts, σ v = 0 ∧ effDist M θ 0 v = M.A v := by
      intro v hv
      have hnot_in : ∀ p ∈ nonUnif, v ∉ Icc p.1 p.2 := fun p hp hvp =>
        hv.2 (Or.inl (Set.mem_iUnion₂.mpr ⟨p, hp, hvp⟩))
      have hnot_end : ∀ I ∈ m1.pools, v ≠ I.α ∧ v ≠ I.β := fun I hI =>
        ⟨fun h => hv.2 (Or.inr (Set.mem_iUnion₂.mpr ⟨I, hI, Or.inl h⟩)),
         fun h => hv.2 (Or.inr (Set.mem_iUnion₂.mpr ⟨I, hI, Or.inr h⟩))⟩
      obtain ⟨δ, hδpos, hδ⟩ := Metric.isOpen_iff.mp hG_open v hv
      let c := v - δ / 2
      let d := v + δ / 2
      have hcd_sub : Icc c d ⊆ Ioo u0 1 \ badPts := fun t ht => by
        dsimp only [c, d] at ht
        apply hδ; rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith [ht.1, ht.2]
      have hgap : ∀ I ∈ m1.pools, ∀ t ∈ Ioo c d, ¬ (I.α < t ∧ t < I.β) := by
        intro I hI t ht
        have htG := hcd_sub (Ioo_subset_Icc_self ht)
        exact hnot_in_pool t htG.1 (fun p hp htp => htG.2 (Or.inl (Set.mem_iUnion₂.mpr ⟨p, hp, htp⟩)))
          (fun J hJ => ⟨fun h => htG.2 (Or.inr (Set.mem_iUnion₂.mpr ⟨J, hJ, Or.inl h⟩)),
                        fun h => htG.2 (Or.inr (Set.mem_iUnion₂.mpr ⟨J, hJ, Or.inr h⟩))⟩) I hI
      have hzero : ∀ t ∈ Icc c d, σ t = 0 := by
        intro t ht
        have htG := hcd_sub ht
        exact (hpt_good t htG.1 (fun p hp htp => htG.2 (Or.inl (Set.mem_iUnion₂.mpr ⟨p, hp, htp⟩)))
          (fun J hJ => ⟨fun h => htG.2 (Or.inr (Set.mem_iUnion₂.mpr ⟨J, hJ, Or.inl h⟩)),
                        fun h => htG.2 (Or.inr (Set.mem_iUnion₂.mpr ⟨J, hJ, Or.inr h⟩))⟩)).1
      have hcv : c < v := by dsimp only [c]; linarith
      have hvd : v < d := by dsimp only [d]; linarith
      have hcd : c < d := hcv.trans hvd
      have hF1 := (prop2_sigma_zero_off_pools M m1 ρ hρ0 hρ1 hSR
        (hcd_sub (left_mem_Icc.mpr hcd.le)).1.1.le hcd
        (hcd_sub (right_mem_Icc.mpr hcd.le)).1.2.le hgap hzero).1
      exact ⟨hzero v ⟨hcv.le, hvd.le⟩, hF1 v ⟨hcv.le, hvd.le⟩⟩
    intro v hv hnot_in hnot_end
    refine hG_eff v ⟨hv, ?_⟩
    rintro (h1 | h2)
    · simp only [Set.mem_iUnion] at h1; obtain ⟨p, hp, hvp⟩ := h1; exact hnot_in p hp hvp
    · simp only [Set.mem_iUnion] at h2; obtain ⟨I, hI, h1 | h2⟩ := h2
      · exact (hnot_end I hI).1 h1
      · exact (hnot_end I hI).2 h2
  · -- Property 3: θ_0 = 1 / m a.e. on Ioo u0 1 \ ⋃ p ∈ nonUnif, Icc p.1 p.2
    -- Use rational intervals [q₁, q₂] ⊆ Ioo u0 1 \ badPts (countably many!)
    let badPts : Set ℝ := (⋃ p ∈ nonUnif, Icc p.1 p.2) ∪ (⋃ I ∈ m1.pools, ({I.α, I.β} : Set ℝ))
    have hbad_closed : IsClosed badPts := by
      apply IsClosed.union
      · have : (⋃ p ∈ nonUnif, Icc p.1 p.2) = ⋃ p ∈ nonUnif.toFinset, Icc p.1 p.2 := by ext t; simp
        rw [this]; exact Set.Finite.isClosed_biUnion (Finset.finite_toSet _) (fun _ _ => isClosed_Icc)
      · have : (⋃ I ∈ m1.pools, ({I.α, I.β} : Set ℝ)) = ⋃ I ∈ m1.pools.toFinset, ({I.α, I.β} : Set ℝ) := by ext t; simp
        rw [this]
        exact Set.Finite.isClosed_biUnion (Finset.finite_toSet _)
          (fun _ _ => isClosed_singleton.union isClosed_singleton)
    have hG_open : IsOpen (Ioo u0 1 \ badPts) := isOpen_Ioo.sdiff hbad_closed
    have hfinite_ends_null : volume (⋃ I ∈ m1.pools, ({I.α, I.β} : Set ℝ)) = 0 := by
      have : (⋃ I ∈ m1.pools, ({I.α, I.β} : Set ℝ)) = ⋃ I ∈ m1.pools.toFinset, ({I.α, I.β} : Set ℝ) := by ext t; simp
      rw [this]
      refine Set.Finite.measure_zero (Set.Finite.biUnion (Finset.finite_toSet _) (fun _ _ => ?_)) volume
      exact (Set.finite_singleton _).union (Set.finite_singleton _)
    -- For every pair of rationals (q₁, q₂) with Icc q₁ q₂ ⊆ G and q₁ < q₂, θ_0 = 1/m a.e. on Icc q₁ q₂
    have hrat_ae : ∀ q : ℚ × ℚ, ∀ᵐ v ∂volume,
        (↑q.1 < (↑q.2 : ℝ) ∧ Icc (↑q.1 : ℝ) ↑q.2 ⊆ Ioo u0 1 \ badPts) →
        v ∈ Icc (↑q.1 : ℝ) ↑q.2 → θ.θ 0 v = 1 / (M.m : ℝ) := by
      intro q
      by_cases hsub : (↑q.1 : ℝ) < ↑q.2 ∧ Icc (↑q.1 : ℝ) ↑q.2 ⊆ Ioo u0 1 \ badPts
      · have hnot_in_all : ∀ t ∈ Icc (↑q.1 : ℝ) ↑q.2, ∀ p ∈ nonUnif, t ∉ Icc p.1 p.2 :=
          fun t ht p hp htp => (hsub.2 ht).2 (Or.inl (Set.mem_iUnion₂.mpr ⟨p, hp, htp⟩))
        have hnot_end_all : ∀ t ∈ Icc (↑q.1 : ℝ) ↑q.2, ∀ I ∈ m1.pools, t ≠ I.α ∧ t ≠ I.β :=
          fun t ht I hI => ⟨fun h => (hsub.2 ht).2 (Or.inr (Set.mem_iUnion₂.mpr ⟨I, hI, Or.inl h⟩)),
            fun h => (hsub.2 ht).2 (Or.inr (Set.mem_iUnion₂.mpr ⟨I, hI, Or.inr h⟩))⟩
        have hgap : ∀ I ∈ m1.pools, ∀ t ∈ Ioo (↑q.1 : ℝ) ↑q.2, ¬ (I.α < t ∧ t < I.β) := by
          intro I hI t ht
          have htG := hsub.2 (Ioo_subset_Icc_self ht)
          -- use same logic: t is not in any pool because if it were, either it's in pos/neg/poolZ or singleton zero
          -- Wait: we already proved hnot_in_pool above! Let's re-invoke prop2_sigma_zero_off_pools via a helper?
          -- Actually we didn't save hnot_in_pool outside the branch, so let's check:
          -- Wait: if v ∈ G, then for any I ∈ m1.pools, can v ∈ Ioo I.α I.β?
          -- Look: if I.α < t ∧ t < I.β, and Icc q₁ q₂ ⊆ G, then Icc q₁ q₂ ∩ Ioo I.α I.β is a non-empty open interval
          -- containing t, so pick another point t' ≠ t in Ioo q₁ q₂ ∩ Ioo I.α I.β: both t and t' have σ = 0!
          -- That IMMEDIATELY contradicts singleton-ness of Z_I, without even needing hnot_in_pool!
          intro htI
          have hσ0 : ∀ z ∈ Icc (↑q.1 : ℝ) ↑q.2, σ z = 0 := by
            intro z hz
            have hzG := hsub.2 hz
            have hnp : ¬ 0 < σ z := by
              intro hpos
              have hz_lt : z < v_hat := by
                by_contra hge; push Not at hge
                rcases eq_or_lt_of_le hge with rfl | hgt
                · exact not_le.mpr hpos (hvhat_at hzG.1.2)
                · exact not_le.mpr hpos (hvhat_le z ⟨hgt, hzG.1.2.le⟩)
              have hu0_lt : u0 < v_hat := hzG.1.1.trans hz_lt
              have hp_mem : (u0, v_hat) ∈ nonUnif := by
                simp only [nonUnif, List.mem_append]; left; left
                dsimp only [posList]; rw [ite_eq_left_iff.mpr (fun h => absurd hu0_lt h)]; simp
              exact hnot_in_all z hz (u0, v_hat) hp_mem ⟨hzG.1.1.le, hz_lt.le⟩
            have hnn : ¬ σ z < 0 := by
              intro hneg
              obtain ⟨p, hp_neg, hzp⟩ := hneg_cover z hzG.1 hneg
              exact hnot_in_all z hz p (by simp only [nonUnif, List.mem_append]; left; right; exact hp_neg)
                (Ioo_subset_Icc_self hzp)
            exact le_antisymm (le_of_not_gt hnp) (le_of_not_gt hnn)
          have hge_aStart : aStart ≤ t := by
            by_contra hlt'; push Not at hlt'
            have hvh_gt : u0 < v_hat := by rcases max_cases u0 v_hat with ⟨_, _⟩ | ⟨_, _⟩ <;> linarith [(hsub.2 (Ioo_subset_Icc_self ht)).1.1]
            have hp_mem : (u0, v_hat) ∈ nonUnif := by
              simp only [nonUnif, List.mem_append]; left; left
              dsimp only [posList]; rw [ite_eq_left_iff.mpr (fun h => absurd hvh_gt h)]; simp
            exact hnot_in_all t (Ioo_subset_Icc_self ht) (u0, v_hat) hp_mem
              ⟨(hsub.2 (Ioo_subset_Icc_self ht)).1.1.le, by have : aStart = v_hat := max_eq_right hvh_gt.le; linarith⟩
          let t' := (t + min (↑q.2 : ℝ) I.β) / 2
          have ht'_gt : t < t' := by dsimp only [t']; linarith [lt_min ht.2 htI.2]
          have ht'_le_q2 : t' ≤ ↑q.2 := by dsimp only [t']; linarith [min_le_left (↑q.2 : ℝ) I.β, lt_min ht.2 htI.2]
          have ht'_lt_β : t' < I.β := by dsimp only [t']; linarith [min_le_right (↑q.2 : ℝ) I.β, lt_min ht.2 htI.2]
          let lo := max I.α aStart
          let Z := {z ∈ Icc lo I.β | σ z = 0}
          have htZ : t ∈ Z := ⟨⟨max_le htI.1.le hge_aStart, htI.2.le⟩, hσ0 t (Ioo_subset_Icc_self ht)⟩
          have ht'Z : t' ∈ Z := ⟨⟨max_le (htI.1.le.trans ht'_gt.le) (hge_aStart.trans ht'_gt.le), ht'_lt_β.le⟩,
            hσ0 t' ⟨ht.1.le.trans ht'_gt.le, ht'_le_q2⟩⟩
          have hZ_bddA : BddAbove Z := ⟨I.β, fun z hz => hz.1.2⟩
          have hZ_bddB : BddBelow Z := ⟨lo, fun z hz => hz.1.1⟩
          have hlo_lt : lo < I.β := max_lt (htI.1.trans htI.2) (hge_aStart.trans_lt htI.2)
          have hInf_lt_Sup : sInf Z < sSup Z :=
            lt_of_le_of_lt (csInf_le hZ_bddB htZ) (lt_of_lt_of_le ht'_gt (le_csSup hZ_bddA ht'Z))
          have hp_mem : (sInf Z, sSup Z) ∈ nonUnif := by
            simp only [nonUnif, List.mem_append]; right
            rw [List.mem_filterMap]
            exact ⟨I, hI, by dsimp only; rw [ite_eq_left_iff.mpr (fun h => absurd ⟨hlo_lt, ⟨t, htZ⟩, hInf_lt_Sup⟩ h)]⟩
          exact hnot_in_all t (Ioo_subset_Icc_self ht) (sInf Z, sSup Z) hp_mem
            ⟨csInf_le hZ_bddB htZ, le_csSup hZ_bddA htZ⟩
        have hzero : ∀ z ∈ Icc (↑q.1 : ℝ) ↑q.2, σ z = 0 := by
          intro z hz
          have hzG := hsub.2 hz
          have hnp : ¬ 0 < σ z := by
            intro hpos
            have hz_lt : z < v_hat := by
              by_contra hge; push Not at hge
              rcases eq_or_lt_of_le hge with rfl | hgt
              · exact not_le.mpr hpos (hvhat_at hzG.1.2)
              · exact not_le.mpr hpos (hvhat_le z ⟨hgt, hzG.1.2.le⟩)
            have hu0_lt : u0 < v_hat := hzG.1.1.trans hz_lt
            have hp_mem : (u0, v_hat) ∈ nonUnif := by
              simp only [nonUnif, List.mem_append]; left; left
              dsimp only [posList]; rw [ite_eq_left_iff.mpr (fun h => absurd hu0_lt h)]; simp
            exact hnot_in_all z hz (u0, v_hat) hp_mem ⟨hzG.1.1.le, hz_lt.le⟩
          have hnn : ¬ σ z < 0 := by
            intro hneg
            obtain ⟨p, hp_neg, hzp⟩ := hneg_cover z hzG.1 hneg
            exact hnot_in_all z hz p (by simp only [nonUnif, List.mem_append]; left; right; exact hp_neg)
              (Ioo_subset_Icc_self hzp)
          exact le_antisymm (le_of_not_gt hnp) (le_of_not_gt hnn)
        have hae := (prop2_sigma_zero_off_pools M m1 ρ hρ0 hρ1 hSR
          (hsub.2 (left_mem_Icc.mpr hsub.1.le)).1.1.le hsub.1
          (hsub.2 (right_mem_Icc.mpr hsub.1.le)).1.2.le hgap hzero).2
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc] at hae
        filter_upwards [hae] with v hv _ hmem
        exact hv hmem
      · exact Filter.Eventually.of_forall fun _ h => absurd h hsub
    have hall_rat := ae_all_iff.mpr hrat_ae
    have hnot_ends : ∀ᵐ v ∂volume, v ∉ ⋃ I ∈ m1.pools, ({I.α, I.β} : Set ℝ) :=
      compl_mem_ae_iff.mpr hfinite_ends_null
    have hmeas_set : MeasurableSet (Ioo u0 1 \ ⋃ p ∈ nonUnif, Icc p.1 p.2) := by
      refine measurableSet_Ioo.diff ?_
      have hcnt : ({p : ℝ × ℝ | p ∈ nonUnif}).Countable := by
        have hfin : ({p : ℝ × ℝ | p ∈ nonUnif}).Finite := by
          have : {p : ℝ × ℝ | p ∈ nonUnif} = (nonUnif.toFinset : Set (ℝ × ℝ)) := by ext p; simp
          rw [this]; exact Finset.finite_toSet _
        exact hfin.countable
      exact MeasurableSet.biUnion hcnt (fun _ _ => measurableSet_Icc)
    rw [MeasureTheory.ae_restrict_iff' hmeas_set]
    filter_upwards [hall_rat, hnot_ends] with v hv_rat hv_noend hv_mem
    have hvG : v ∈ Ioo u0 1 \ badPts := ⟨hv_mem.1, by rintro (h1 | h2); exact hv_mem.2 h1; exact hv_noend h2⟩
    obtain ⟨δ, hδpos, hδ⟩ := Metric.isOpen_iff.mp hG_open v hvG
    obtain ⟨q1, hq1_gt, hq1_lt⟩ := exists_rat_btwn (show v - δ / 2 < v by linarith)
    obtain ⟨q2, hq2_gt, hq2_lt⟩ := exists_rat_btwn (show v < v + δ / 2 by linarith)
    have hsub : Icc (↑q1 : ℝ) ↑q2 ⊆ Ioo u0 1 \ badPts := fun t ht => by
      apply hδ; rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [ht.1, ht.2]
    exact hv_rat (q1, q2) ⟨hq1_lt.trans hq2_gt, hsub⟩ ⟨hq1_lt.le, hq2_gt.le⟩

end Proposition2

/-! ### Part 4: Lemma 1 & Lemma A.5 — Anatomy of a Single Interior Pool -/

section Lemma1

variable (M : Market)

/-- Single-pool hierarchical mechanism `(ρ, {(α, β)})` with reserve `ρ` and one pooling interval
`(α, β) ⊆ [ρ, 1]`. -/
def singlePoolMech (ρ α β : ℝ) (hρ0 : 0 ≤ ρ) (hρα : ρ ≤ α) (hαβ : α < β) (hβ1 : β ≤ 1) :
    HierarchicalMech where
  r := ρ
  hr0 := hρ0
  hr1 := hρα.trans (hαβ.le.trans hβ1)
  pools := [⟨α, β, hαβ⟩]
  hpools_in := fun I hI => by
    simp only [List.mem_singleton] at hI; subst hI; exact ⟨hρα, hβ1⟩
  hpools_disj := by simp

/-- An interior band `[v₁, v₄]` for the single-pool deviation `(ρ, {(α, β)})`: strictly inside
`(max ρ a, 1)`, containing `(α, β)`, uniform (`F₁ = A`) outside `(v₁, v₄)`, and tight (minimal)
at both `v₁` and `v₄`. -/
def IsInteriorBand (ρ α β : ℝ) (θ : VisitStrategy M) (v₁ v₄ : ℝ) : Prop :=
  max ρ M.a < v₁ ∧ v₁ < v₄ ∧ v₄ < 1 ∧
  v₁ ≤ α ∧ β ≤ v₄ ∧
  (∀ v ∈ Icc (max ρ M.a) v₁ ∪ Icc v₄ 1, effDist M θ 0 v = M.A v) ∧
  (∀ ε > 0, ∃ u ∈ Ioo v₁ (min (v₁ + ε) v₄), effDist M θ 0 u ≠ M.A u) ∧
  (∀ ε > 0, ∃ u ∈ Ioo (max v₁ (v₄ - ε)) v₄, effDist M θ 0 u ≠ M.A u)

/-- A top-reaching band `[v₁, 1]` for `(ρ, {(α, β)})` (Lemma A.5(iii)): starts strictly above
`max ρ a`, uniform below `v₁`, tight at both `v₁` and `1`. -/
def IsTopReachingBand (ρ α β : ℝ) (θ : VisitStrategy M) (v₁ : ℝ) : Prop :=
  max ρ M.a < v₁ ∧ v₁ < 1 ∧
  v₁ ≤ α ∧ β ≤ 1 ∧
  (∀ v ∈ Icc (max ρ M.a) v₁, effDist M θ 0 v = M.A v) ∧
  (∀ ε > 0, ∃ u ∈ Ioo v₁ (min (v₁ + ε) 1), effDist M θ 0 u ≠ M.A u) ∧
  (∀ ε > 0, ∃ u ∈ Ioo (max v₁ (1 - ε)) 1, effDist M θ 0 u ≠ M.A u)

/-- The rival quantile `q*` on the served segment `(v₂, v₃)` solving equation (5):
`(1 - q*)^(n - 1) = poolAvg n (A v₁) (A v₄)`. -/
noncomputable def bandQStar (v₁ v₄ : ℝ) : ℝ :=
  1 - (poolAvg M.n (M.A v₁) (M.A v₄)) ^ ((1 : ℝ) / ((M.n : ℝ) - 1))

/-- Helper: integration by parts for `g(x)^(n - 1)` where `g(x) = c₀ + (F(x) - F(c)) / (m - 1)`
on `[c, d] ⊆ [a, 1]`. -/
private lemma ibp_riv_pow {c d : ℝ} (hc : M.a ≤ c) (hcd : c < d) (hd : d ≤ 1) (c₀ : ℝ) :
    let g : ℝ → ℝ := fun x => c₀ + (M.F x - M.F c) / ((M.m : ℝ) - 1)
    let gp : ℝ → ℝ := fun x => ((M.n : ℝ) - 1) * (g x) ^ (M.n - 2) * (M.f x / ((M.m : ℝ) - 1))
    (∫ x in c..d, gp x = (g d) ^ (M.n - 1) - (g c) ^ (M.n - 1)) ∧
    (∫ x in c..d, x * gp x =
      d * (g d) ^ (M.n - 1) - c * (g c) ^ (M.n - 1) - ∫ x in c..d, (g x) ^ (M.n - 1)) := by
  intro g gp
  have hsubIcc : Icc c d ⊆ Icc M.a 1 := Icc_subset_Icc hc hd
  have hg_cont : ContinuousOn g (Icc c d) :=
    continuousOn_const.add (((M.F_continuousOn.mono hsubIcc).sub continuousOn_const).div_const _)
  have hgpow_cont : ContinuousOn (fun x => (g x) ^ (M.n - 1)) (Icc c d) := hg_cont.pow (M.n - 1)
  have hgp_cont : ContinuousOn gp (Icc c d) :=
    (continuousOn_const.mul (hg_cont.pow (M.n - 2))).mul ((M.hf_cont.mono hsubIcc).div_const _)
  have hgp_int : IntervalIntegrable gp volume c d := hgp_cont.intervalIntegrable_of_Icc hcd.le
  have hderiv : ∀ x ∈ Ioo c d, HasDerivAt (fun t => (g t) ^ (M.n - 1)) (gp x) x := by
    intro x hx
    have hx_oo : x ∈ Ioo M.a 1 := ⟨lt_of_le_of_lt hc hx.1, lt_of_lt_of_le hx.2 hd⟩
    have hg_d : HasDerivAt g (M.f x / ((M.m : ℝ) - 1)) x := by
      have h1 : HasDerivAt (fun t => (M.F t - M.F c) / ((M.m : ℝ) - 1)) (M.f x / ((M.m : ℝ) - 1)) x :=
        ((M.hF_deriv_open x hx_oo).sub_const (M.F c)).div_const ((M.m : ℝ) - 1)
      simpa [g] using h1.const_add c₀
    have hp := hg_d.pow (M.n - 1)
    have hcast : ((M.n - 1 : ℕ) : ℝ) = (M.n : ℝ) - 1 := by
      rw [Nat.cast_sub (by have := M.hn; omega), Nat.cast_one]
    have hsub2 : M.n - 1 - 1 = M.n - 2 := by omega
    rw [hcast, hsub2] at hp
    exact hp
  constructor
  · exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hcd.le hgpow_cont hderiv hgp_int
  · have h1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      (u := fun x => x) (u' := fun _ => (1 : ℝ))
      (v := fun x => (g x) ^ (M.n - 1)) (v' := gp)
      (a := c) (b := d)
      (by rw [uIcc_of_le hcd.le]; exact continuousOn_id)
      (by rw [uIcc_of_le hcd.le]; exact hgpow_cont)
      (fun x _ => hasDerivAt_id x)
      (fun x hx => by rw [min_eq_left hcd.le, max_eq_right hcd.le] at hx; exact hderiv x hx)
      intervalIntegrable_const hgp_int
    simpa only [one_mul] using h1

lemma bandQStar_pow {v₁ v₄ : ℝ} (hv1 : M.a ≤ v₁) (hlt : v₁ < v₄) (hv4 : v₄ ≤ 1) :
    (1 - bandQStar M v₁ v₄) ^ (M.n - 1) = poolAvg M.n (M.A v₁) (M.A v₄) ∧
    (1 - bandQStar M v₁ v₄) ^ (M.n - 1) =
      ((1 - (1 - M.F v₄) / (M.m : ℝ)) ^ M.n - (1 - (1 - M.F v₁) / (M.m : ℝ)) ^ M.n) /
        ((M.n : ℝ) * ((1 - M.F v₁) / (M.m : ℝ) - (1 - M.F v₄) / (M.m : ℝ))) := by
  have hA1_nn : 0 ≤ M.A v₁ := (M.A_mem_Icc (hlt.le.trans hv4)).1
  have hA4_nn : 0 ≤ M.A v₄ := (M.A_mem_Icc hv4).1
  have hA_lt : M.A v₁ < M.A v₄ := by
    unfold Market.A
    have hFlt := M.F_strictMonoOn ⟨hv1, hlt.le.trans hv4⟩ ⟨hv1.trans hlt.le, hv4⟩ hlt
    have := div_lt_div_of_pos_right (sub_lt_sub_left hFlt 1) M.m_pos_real
    linarith
  have hp_nn : 0 ≤ poolAvg M.n (M.A v₁) (M.A v₄) := poolAvg_nonneg M.hn hA1_nn hA4_nn
  have h1sub : 1 - bandQStar M v₁ v₄ =
      (poolAvg M.n (M.A v₁) (M.A v₄)) ^ ((1 : ℝ) / ((M.n : ℝ) - 1)) := by
    unfold bandQStar; ring
  have hpow : (1 - bandQStar M v₁ v₄) ^ (M.n - 1) = poolAvg M.n (M.A v₁) (M.A v₄) := by
    rw [h1sub, ← Real.rpow_natCast, ← Real.rpow_mul hp_nn]
    have hcast : ((M.n - 1 : ℕ) : ℝ) = (M.n : ℝ) - 1 := by
      rw [Nat.cast_sub (by have := M.hn; omega), Nat.cast_one]
    rw [hcast, one_div_mul_cancel M.n_sub_one_pos_real.ne', Real.rpow_one]
  refine ⟨hpow, ?_⟩
  rw [hpow]
  unfold poolAvg
  rw [ite_eq_right_iff.mpr (fun h => absurd h hA_lt.ne)]
  unfold Market.A
  congr 1; ring

lemma bandQStar_bounds {v₁ v₄ : ℝ} (hv1 : M.a ≤ v₁) (hlt : v₁ < v₄) (hv4 : v₄ ≤ 1) :
    M.A v₁ < 1 - bandQStar M v₁ v₄ ∧ 1 - bandQStar M v₁ v₄ < M.A v₄ ∧
    (1 - M.F v₄) / (M.m : ℝ) < bandQStar M v₁ v₄ ∧
    bandQStar M v₁ v₄ < (1 - M.F v₁) / (M.m : ℝ) := by
  have hA1_nn : 0 ≤ M.A v₁ := (M.A_mem_Icc (hlt.le.trans hv4)).1
  have hA4_nn : 0 ≤ M.A v₄ := (M.A_mem_Icc hv4).1
  have hA_lt : M.A v₁ < M.A v₄ := by
    unfold Market.A
    have hFlt := M.F_strictMonoOn ⟨hv1, hlt.le.trans hv4⟩ ⟨hv1.trans hlt.le, hv4⟩ hlt
    have := div_lt_div_of_pos_right (sub_lt_sub_left hFlt 1) M.m_pos_real
    linarith
  have hp_bds := vs_poolAvg_strict_bounds M.hn hA1_nn hA_lt
  have hpow := (bandQStar_pow M hv1 hlt hv4).1
  have hr_nn : 0 ≤ 1 - bandQStar M v₁ v₄ := by
    have : 1 - bandQStar M v₁ v₄ =
        (poolAvg M.n (M.A v₁) (M.A v₄)) ^ ((1 : ℝ) / ((M.n : ℝ) - 1)) := by
      unfold bandQStar; ring
    rw [this]; exact Real.rpow_nonneg (poolAvg_nonneg M.hn hA1_nn hA4_nn) _
  have hn1 : M.n - 1 ≠ 0 := by have := M.hn; omega
  have hlt1 : M.A v₁ < 1 - bandQStar M v₁ v₄ := by
    by_contra hle; push Not at hle
    have := pow_le_pow_left₀ hr_nn hle (M.n - 1)
    linarith [hp_bds.1]
  have hlt2 : 1 - bandQStar M v₁ v₄ < M.A v₄ := by
    by_contra hle; push Not at hle
    have := pow_le_pow_left₀ hA4_nn hle (M.n - 1)
    linarith [hp_bds.2]
  refine ⟨hlt1, hlt2, ?_, ?_⟩
  · unfold Market.A at hlt2; linarith
  · unfold Market.A at hlt1; linarith

/-- **Lemma A.5(i) exact `n = 2` case**: When `n = 2`, `q* = (q_lo + q_hi) / 2` and both outer
segments carry equal quantile mass `(m - 1)(F(v₄) - F(v₁)) / (2m)`. -/
theorem lemma1_n_eq_two (hn2 : M.n = 2) {v₁ v₄ : ℝ} (hv1 : M.a ≤ v₁) (hlt : v₁ < v₄) (hv4 : v₄ ≤ 1) :
    let q_lo := (1 - M.F v₄) / (M.m : ℝ)
    let q_hi := (1 - M.F v₁) / (M.m : ℝ)
    bandQStar M v₁ v₄ = (q_lo + q_hi) / 2 ∧
    ((M.m : ℝ) - 1) * (q_hi - bandQStar M v₁ v₄) =
      ((M.m : ℝ) - 1) * (M.F v₄ - M.F v₁) / (2 * (M.m : ℝ)) ∧
    ((M.m : ℝ) - 1) * (bandQStar M v₁ v₄ - q_lo) =
      ((M.m : ℝ) - 1) * (M.F v₄ - M.F v₁) / (2 * (M.m : ℝ)) := by
  intro q_lo q_hi
  have hpow := (bandQStar_pow M hv1 hlt hv4).1
  rw [hn2] at hpow
  simp only [Nat.reduceSub, pow_one] at hpow
  have hA_lt : M.A v₁ < M.A v₄ := by
    unfold Market.A
    have hFlt := M.F_strictMonoOn ⟨hv1, hlt.le.trans hv4⟩ ⟨hv1.trans hlt.le, hv4⟩ hlt
    have := div_lt_div_of_pos_right (sub_lt_sub_left hFlt 1) M.m_pos_real
    linarith
  have hp2 : poolAvg 2 (M.A v₁) (M.A v₄) = (M.A v₁ + M.A v₄) / 2 := by
    unfold poolAvg
    rw [ite_eq_right_iff.mpr (fun h => absurd h hA_lt.ne)]
    have hne : M.A v₄ - M.A v₁ ≠ 0 := sub_ne_zero.mpr hA_lt.ne'
    push_cast; field_simp [hne]; ring
  rw [hp2] at hpow
  have hq : bandQStar M v₁ v₄ = (q_lo + q_hi) / 2 := by
    dsimp only [q_lo, q_hi]; unfold Market.A at hpow; linarith
  refine ⟨hq, ?_, ?_⟩
  · rw [hq]; dsimp only [q_lo, q_hi]; ring
  · rw [hq]; dsimp only [q_lo, q_hi]; ring

/-- Helper: for `g(v) = c₀ + (F(v) - F(c)) / (m - 1)` on `[c, d] ⊆ [a, 1]` with `c < d` and
`0 ≤ c₀`, the weighted-average endpoint `x* := (d * g(d)^(n-1) - c * c₀^(n-1) - ∫ g^(n-1)) /
(g(d)^(n-1) - c₀^(n-1))` lies strictly in `(c, d)`, and equals the Stieltjes ratio eq. (15). -/
private lemma outer_endpoint_strict_bounds {c d : ℝ} (hc : M.a ≤ c) (hcd : c < d) (hd : d ≤ 1)
    {c₀ c₁ : ℝ} (hc0 : 0 ≤ c₀) (hc1 : c₁ = c₀ + (M.F d - M.F c) / ((M.m : ℝ) - 1)) :
    let g : ℝ → ℝ := fun v => c₀ + (M.F v - M.F c) / ((M.m : ℝ) - 1)
    let xStar : ℝ := (d * c₁ ^ (M.n - 1) - c * c₀ ^ (M.n - 1) - ∫ v in c..d, (g v) ^ (M.n - 1)) /
      (c₁ ^ (M.n - 1) - c₀ ^ (M.n - 1))
    0 < c₁ ^ (M.n - 1) - c₀ ^ (M.n - 1) ∧
    c < xStar ∧ xStar < d ∧
    xStar = (∫ v in c..d, v * (((M.n : ℝ) - 1) * (g v) ^ (M.n - 2) * (M.f v / ((M.m : ℝ) - 1)))) /
      (∫ v in c..d, ((M.n : ℝ) - 1) * (g v) ^ (M.n - 2) * (M.f v / ((M.m : ℝ) - 1))) := by
  intro g xStar
  have hsubIcc : Icc c d ⊆ Icc M.a 1 := Icc_subset_Icc hc hd
  have hg_cont : ContinuousOn g (Icc c d) :=
    continuousOn_const.add (((M.F_continuousOn.mono hsubIcc).sub continuousOn_const).div_const _)
  have hg_c : g c = c₀ := by dsimp only [g]; simp
  have hg_d : g d = c₁ := hc1.symm
  have hg_strict : StrictMonoOn g (Icc c d) := fun x hx y hy hxy => by
    dsimp only [g]
    have hFlt := M.F_strictMonoOn (hsubIcc hx) (hsubIcc hy) hxy
    linarith [div_lt_div_of_pos_right (sub_lt_sub_right hFlt (M.F c)) M.m_sub_one_pos_real]
  have hc0_lt_c1 : c₀ < c₁ := by
    have := hg_strict (left_mem_Icc.mpr hcd.le) (right_mem_Icc.mpr hcd.le) hcd
    rwa [hg_c, hg_d] at this
  have hn1 : M.n - 1 ≠ 0 := by have := M.hn; omega
  have hden_pos : 0 < c₁ ^ (M.n - 1) - c₀ ^ (M.n - 1) :=
    sub_pos.mpr (pow_lt_pow_left₀ hc0_lt_c1 hc0 hn1)
  have hcont1 : ContinuousOn (fun v => c₁ ^ (M.n - 1) - (g v) ^ (M.n - 1)) (Icc c d) :=
    continuousOn_const.sub (hg_cont.pow (M.n - 1))
  have hcont2 : ContinuousOn (fun v => (g v) ^ (M.n - 1) - c₀ ^ (M.n - 1)) (Icc c d) :=
    (hg_cont.pow (M.n - 1)).sub continuousOn_const
  have h1 : 0 < ∫ v in c..d, (c₁ ^ (M.n - 1) - (g v) ^ (M.n - 1)) := by
    apply intervalIntegral.integral_pos hcd hcont1
    · intro v hv
      have hle := hg_strict.monotoneOn ⟨hv.1.le, hv.2⟩ (right_mem_Icc.mpr hcd.le) hv.2
      rw [hg_d] at hle
      have hnn : 0 ≤ g v := by
        have := hg_strict.monotoneOn (left_mem_Icc.mpr hcd.le) ⟨hv.1.le, hv.2⟩ hv.1.le
        rw [hg_c] at this; exact hc0.trans this
      linarith [pow_le_pow_left₀ hnn hle (M.n - 1)]
    · refine ⟨c, left_mem_Icc.mpr hcd.le, ?_⟩
      rw [hg_c]; linarith
  have h2 : 0 < ∫ v in c..d, ((g v) ^ (M.n - 1) - c₀ ^ (M.n - 1)) := by
    apply intervalIntegral.integral_pos hcd hcont2
    · intro v hv
      have hle := hg_strict.monotoneOn (left_mem_Icc.mpr hcd.le) ⟨hv.1.le, hv.2⟩ hv.1.le
      rw [hg_c] at hle
      linarith [pow_le_pow_left₀ hc0 hle (M.n - 1)]
    · refine ⟨d, right_mem_Icc.mpr hcd.le, ?_⟩
      rw [hg_d]; linarith
  have hint_g : IntervalIntegrable (fun v => (g v) ^ (M.n - 1)) volume c d :=
    (hg_cont.pow (M.n - 1)).intervalIntegrable_of_Icc hcd.le
  rw [intervalIntegral.integral_sub intervalIntegrable_const hint_g,
    intervalIntegral.integral_const, smul_eq_mul] at h1
  rw [intervalIntegral.integral_sub hint_g intervalIntegrable_const,
    intervalIntegral.integral_const, smul_eq_mul] at h2
  have hx_mul : xStar * (c₁ ^ (M.n - 1) - c₀ ^ (M.n - 1)) =
      d * c₁ ^ (M.n - 1) - c * c₀ ^ (M.n - 1) - ∫ v in c..d, (g v) ^ (M.n - 1) :=
    div_mul_cancel₀ _ hden_pos.ne'
  have hibp := ibp_riv_pow M hc hcd hd c₀
  refine ⟨hden_pos, by nlinarith, by nlinarith, ?_⟩
  dsimp only [xStar, g]
  rw [hibp.1, hibp.2]
  dsimp only
  rw [← hc1]
  simp

/-- Helper: under `singlePoolMech ρ α β`, if `F₁ = A` on `[max ρ a, v₁]` with `max ρ a < v₁ ≤ α`,
then `σ(v₁) = 0`, and if `v₁ < α` and `v₁` is tight then `σ < 0` on `(v₁, α]`. -/
private lemma singlePool_left_neg {ρ α β : ℝ} (hρ0 : 0 ≤ ρ) (hρα : ρ ≤ α) (hαβ : α < β) (hβ1 : β ≤ 1)
    {θ : VisitStrategy M}
    (hSR : IsSR M (unilateralProfile M (singlePoolMech ρ α β hρ0 hρα hαβ hβ1) ρ hρ0
      (hρα.trans (hαβ.le.trans hβ1))) θ)
    {v₁ v₄ : ℝ} (hu0_lt : max ρ M.a < v₁) (hv1α : v₁ ≤ α) (hβv4 : β ≤ v₄) (hv4_1 : v₄ ≤ 1)
    (hunif_lo : ∀ v ∈ Icc (max ρ M.a) v₁, effDist M θ 0 v = M.A v)
    (htight1 : ∀ ε > 0, ∃ u ∈ Ioo v₁ (min (v₁ + ε) v₄), effDist M θ 0 u ≠ M.A u)
    (hσ_end : v₄ = 1 ∨ sigma M (singlePoolMech ρ α β hρ0 hρα hαβ hβ1) ρ hρ0
      (hρα.trans (hαβ.le.trans hβ1)) θ v₄ = 0) :
    let m1 := singlePoolMech ρ α β hρ0 hρα hαβ hβ1
    let hρ1 := hρα.trans (hαβ.le.trans hβ1)
    (∀ v ∈ Icc ρ 1, sigma M m1 ρ hρ0 hρ1 θ v ≤ 0) ∧
    sigma M m1 ρ hρ0 hρ1 θ v₁ = 0 ∧
    (v₁ < α → ∀ t ∈ Ioc v₁ α, sigma M m1 ρ hρ0 hρ1 θ t < 0) := by
  intro m1 hρ1
  let σ := sigma M m1 ρ hρ0 hρ1 θ
  have hρ_lt_v1 : ρ < v₁ := (le_max_left ρ M.a).trans_lt hu0_lt
  have ha_lt_v1 : M.a < v₁ := (le_max_right ρ M.a).trans_lt hu0_lt
  have hv1_0 : 0 ≤ v₁ := M.ha0.trans ha_lt_v1.le
  have hv1_1 : v₁ ≤ 1 := hv1α.trans (hαβ.le.trans hβ1)
  have hmin : min m1.r ρ = ρ := min_self ρ
  have hσ_np : ∀ v ∈ Icc ρ 1, σ v ≤ 0 := by
    have h1 := (prop2_sigma_pos_initial M m1 ρ hρ0 hρ1 hSR).1 (le_refl ρ)
    rwa [hmin] at h1
  have hσ_cont : ContinuousOn σ (Icc 0 1) := sigma_continuousOn M m1 ρ hρ0 hρ1 hSR
  have hFriv_A : ∀ v, effDist M θ 0 v = M.A v → FrivOf M (effDist M θ 0) v = M.A v := by
    intro v hF1v
    unfold FrivOf Market.A at *; rw [hF1v]
    have hm1 := M.m_sub_one_pos_real.ne'; have hm := M.m_pos_real.ne'
    field_simp [hm1, hm]; ring
  have hσ_v1 : σ v₁ = 0 := by
    have h0 : σ ρ = 0 := by
      have h := sigma_zero_at_rmin M m1 ρ hρ0 hρ1 hSR
      rwa [hmin] at h
    have hsub := sigma_sub M m1 ρ hρ0 hρ1 hSR hρ0 hρ1 hv1_0 hv1_1
    have hzero_int : ∫ t in ρ..v₁, (alloc M m1 (effDist M θ 0) t -
        alloc M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) t) = 0 := by
      have hcongr : ∫ t in ρ..v₁, (alloc M m1 (effDist M θ 0) t -
          alloc M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) t) = ∫ _ in ρ..v₁, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_ae
        have hne : ∀ᵐ t ∂volume, t ≠ v₁ := by simp [ae_iff, measure_singleton]
        filter_upwards [hne] with t htv1 ht
        rw [uIoc_of_le hρ_lt_v1.le] at ht
        have ht_lt_v1 : t < v₁ := lt_of_le_of_ne ht.2 htv1
        have hF1t : effDist M θ 0 t = M.A t := by
          by_cases hta : t ≤ M.a
          · rw [effDist_const_below_a θ 0 hta]
            have hA_eq : M.A t = M.A M.a := by unfold Market.A; rw [M.hF_below t hta, M.hF_a]
            rw [hA_eq]
            have hρ_le_a : ρ ≤ M.a := ht.1.le.trans hta
            rw [← hunif_lo M.a ⟨max_le hρ_le_a (le_refl _), ha_lt_v1.le⟩]
          · push Not at hta
            exact hunif_lo t ⟨max_le ht.1.le hta.le, ht_lt_v1.le⟩
        have hFrivt : effDist M θ (rivalIdx M) t = M.A t := by
          rw [(prop2_rival_symmetry M m1 ρ hρ0 hρ1 hSR).2 (rivalIdx M) (rivalIdx_ne_zero M) t
            ⟨ht.1.le, ht_lt_v1.le.trans hv1_1⟩]
          exact hFriv_A t hF1t
        rw [alloc_off_pools M m1 _ ht.1.le (fun I hI => by
          simp only [m1, singlePoolMech, List.mem_singleton] at hI; subst hI
          intro h; linarith [h.1]), alloc_SPA,
          ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr ht.1.le)), hF1t, hFrivt, sub_self]
      rw [hcongr]; simp
    dsimp only [σ] at h0 ⊢; linarith
  refine ⟨hσ_np, hσ_v1, ?_⟩
  intro hv1_lt_α t ht
  have hex_neg : ∃ x ∈ Ioo v₁ t, σ x < 0 := by
    by_contra hall; push Not at hall
    have hzero : ∀ u ∈ Icc v₁ t, σ u = 0 := fun u hu => by
      rcases eq_or_lt_of_le hu.1 with rfl | h1
      · exact hσ_v1
      · rcases eq_or_lt_of_le hu.2 with hu_eq | h2
        · rw [hu_eq]
          have hlim : Tendsto σ (𝓝[Ioo v₁ t] t) (𝓝 (σ t)) :=
            (hσ_cont t ⟨hv1_0.trans ht.1.le, ht.2.trans (hαβ.le.trans hβ1)⟩).mono_left
              (nhdsWithin_mono t (fun z hz => ⟨hv1_0.trans hz.1.le, hz.2.le.trans (ht.2.trans (hαβ.le.trans hβ1))⟩))
          have h0' : Tendsto σ (𝓝[Ioo v₁ t] t) (𝓝 0) :=
            tendsto_const_nhds.congr' (Filter.eventually_of_mem self_mem_nhdsWithin fun z hz =>
              (le_antisymm (hσ_np z ⟨hρ_lt_v1.le.trans hz.1.le, hz.2.le.trans (ht.2.trans (hαβ.le.trans hβ1))⟩)
                (hall z hz)).symm)
          have : (𝓝[Ioo v₁ t] t).NeBot := right_nhdsWithin_Ioo_neBot ht.1
          exact tendsto_nhds_unique hlim h0'
        · exact le_antisymm (hσ_np u ⟨hρ_lt_v1.le.trans h1.le, hu.2.trans (ht.2.trans (hαβ.le.trans hβ1))⟩) (hall u ⟨h1, h2⟩)
    have hF1_eq := (prop2_sigma_zero_off_pools M m1 ρ hρ0 hρ1 hSR
      (by have : max (max m1.r ρ) M.a = max ρ M.a := by simp [m1, singlePoolMech]
          rw [this]; exact hu0_lt.le) ht.1 (ht.2.trans (hαβ.le.trans hβ1))
      (fun I hI u hu => by
        simp only [m1, singlePoolMech, List.mem_singleton] at hI; subst hI
        intro h; linarith [h.1, hu.2, ht.2])
      hzero).1
    obtain ⟨u, hu, hne⟩ := htight1 (t - v₁) (sub_pos.mpr ht.1)
    exact hne (hF1_eq u ⟨hu.1.le, (hu.2.le.trans (min_le_left _ _)).trans (by linarith)⟩)
  obtain ⟨x, hx, hσx⟩ := hex_neg
  let SL := {u ∈ Icc v₁ x | σ u = 0}
  let SR := {v₄} ∪ {u ∈ Icc x v₄ | σ u = 0}
  have hx_lt_v4 : x < v₄ := hx.2.trans_le (ht.2.trans (hαβ.le.trans hβv4))
  have hSL_ne : SL.Nonempty := ⟨v₁, ⟨le_refl _, hx.1.le⟩, hσ_v1⟩
  have hSR_ne : SR.Nonempty := ⟨v₄, Or.inl rfl⟩
  have hSL_bdd : BddAbove SL := ⟨x, fun u hu => hu.1.2⟩
  have hSR_bdd : BddBelow SR := ⟨x, fun u hu => by
    rcases hu with h1 | hu
    · rw [Set.mem_singleton_iff.mp h1]; exact hx_lt_v4.le
    · exact hu.1.1⟩
  let y₁ := sSup SL
  let y₂ := sInf SR
  have hSL_cl : IsClosed SL := by
    have : SL = Icc v₁ x ∩ σ ⁻¹' {0} := by ext u; simp [SL]
    rw [this]
    exact (hσ_cont.mono (Icc_subset_Icc hv1_0 (hx_lt_v4.le.trans hv4_1))).preimage_isClosed_of_isClosed
      isClosed_Icc isClosed_singleton
  have hSR_cl : IsClosed SR := by
    have : SR = {v₄} ∪ (Icc x v₄ ∩ σ ⁻¹' {0}) := by ext u; simp [SR]
    rw [this]
    exact isClosed_singleton.union ((hσ_cont.mono (Icc_subset_Icc (hv1_0.trans hx.1.le) hv4_1)).preimage_isClosed_of_isClosed
      isClosed_Icc isClosed_singleton)
  have hy1_in : y₁ ∈ SL := by
    have h := csSup_mem_closure hSL_ne hSL_bdd; rwa [hSL_cl.closure_eq] at h
  have hy2_in : y₂ ∈ SR := by
    have h := csInf_mem_closure hSR_ne hSR_bdd; rwa [hSR_cl.closure_eq] at h
  have hy1_lt_x : y₁ < x := lt_of_le_of_ne hy1_in.1.2 (fun h => by rw [h] at hy1_in; linarith [hy1_in.2])
  have hx_lt_y2 : x < y₂ := by
    rcases hy2_in with h1 | hy2
    · rw [Set.mem_singleton_iff.mp h1]; exact hx_lt_v4
    · exact lt_of_le_of_ne hy2.1.1 (fun h => by rw [← h] at hy2; linarith [hy2.2])
  have hy2_le_v4 : y₂ ≤ v₄ := by
    rcases hy2_in with h1 | hy2
    · rw [Set.mem_singleton_iff.mp h1]
    · exact hy2.1.2
  have hneg_comp : ∀ u ∈ Ioo y₁ y₂, σ u < 0 := fun u hu => by
    refine lt_of_le_of_ne (hσ_np u ⟨hρ_lt_v1.le.trans (hy1_in.1.1.trans hu.1.le), hu.2.le.trans (hy2_le_v4.trans hv4_1)⟩) ?_
    intro h0
    rcases le_total u x with hux | hxu
    · exact not_lt.mpr (le_csSup hSL_bdd ⟨⟨hy1_in.1.1.trans hu.1.le, hux⟩, h0⟩) hu.1
    · exact not_lt.mpr (csInf_le hSR_bdd (Or.inr ⟨⟨hxu, hu.2.le.trans hy2_le_v4⟩, h0⟩)) hu.2
  have hα_lt_y2 : α < y₂ := by
    rcases hy2_in with h1 | hy2
    · rw [Set.mem_singleton_iff.mp h1]; exact hαβ.trans_le hβv4
    · by_contra hle; push Not at hle
      exact prop2_no_dip_without_endpoint M m1 ρ hρ0 hρ1 hSR
        (by have : max (max m1.r ρ) M.a = max ρ M.a := by simp [m1, singlePoolMech]
            rw [this]; exact hu0_lt.le.trans hy1_in.1.1)
        (hy1_lt_x.trans hx_lt_y2) (hy2.1.2.trans hv4_1) hy1_in.2 hy2.2 hneg_comp (fun I hI => by
          simp only [m1, singlePoolMech, List.mem_singleton] at hI; subst hI
          exact ⟨fun h => not_le.mpr h.2 hle, fun h => not_le.mpr h.2 (hle.trans hαβ.le)⟩)
  exact hneg_comp t ⟨hy1_lt_x.trans hx.2, ht.2.trans_lt hα_lt_y2⟩

/-- **Lemma 1(i)–(ii) & Lemma A.5(i)–(ii) (Interior Band Structure & Pool Endpoints)**:
For a single-pool deviation `(ρ, {(α, β)})` inducing an interior band `[v₁, v₄]`:
- `F₁ = F_riv = A` at `v₁` and `v₄`;
- there exist `v₁ < α < v₂ < v₃ < β < v₄` with `θ_0 = 0` a.e. on `(v₁, v₂) ∪ (v₃, v₄)` and
  `θ_0 = 1` a.e. on `(v₂, v₃)`;
- served mass `F(v₃) - F(v₂) = (F(v₄) - F(v₁)) / m`;
- on `[v₂, v₃]`, `F_riv = 1 - q*` where `q* = bandQStar M v₁ v₄` solves eq. (5), and
  `F(v₂) - F(v₁) = (m - 1)(q_hi - q*)`, `F(v₄) - F(v₃) = (m - 1)(q* - q_lo)`;
- the pool endpoints `(α, β)` satisfy the exact Stieltjes ratio formulas eq. (15) (and their
  integrated-by-parts closed forms). -/
theorem lemma1_band_structure {ρ α β : ℝ} (hρ0 : 0 ≤ ρ) (hρα : ρ ≤ α) (hαβ : α < β) (hβ1 : β ≤ 1)
    {θ : VisitStrategy M}
    (hSR : IsSR M (unilateralProfile M (singlePoolMech ρ α β hρ0 hρα hαβ hβ1) ρ hρ0
      (hρα.trans (hαβ.le.trans hβ1))) θ)
    {v₁ v₄ : ℝ} (hband : IsInteriorBand M ρ α β θ v₁ v₄) :
    let q_lo := (1 - M.F v₄) / (M.m : ℝ)
    let q_hi := (1 - M.F v₁) / (M.m : ℝ)
    let qStar := bandQStar M v₁ v₄
    effDist M θ 0 v₁ = M.A v₁ ∧ effDist M θ 0 v₄ = M.A v₄ ∧
    FrivOf M (effDist M θ 0) v₁ = M.A v₁ ∧ FrivOf M (effDist M θ 0) v₄ = M.A v₄ ∧
    ∃ v₂ v₃ : ℝ,
      v₁ < α ∧ α < v₂ ∧ v₂ < v₃ ∧ v₃ < β ∧ β < v₄ ∧
      (∀ᵐ v ∂(volume.restrict (Icc v₁ v₂)), θ.θ 0 v = 0) ∧
      (∀ᵐ v ∂(volume.restrict (Icc v₂ v₃)), θ.θ 0 v = 1) ∧
      (∀ᵐ v ∂(volume.restrict (Icc v₃ v₄)), θ.θ 0 v = 0) ∧
      M.F v₃ - M.F v₂ = (M.F v₄ - M.F v₁) / (M.m : ℝ) ∧
      (∀ v ∈ Icc v₂ v₃, effDist M θ (rivalIdx M) v = 1 - qStar) ∧
      (1 - qStar) ^ (M.n - 1) =
        ((1 - q_lo) ^ M.n - (1 - q_hi) ^ M.n) / ((M.n : ℝ) * (q_hi - q_lo)) ∧
      M.F v₂ - M.F v₁ = ((M.m : ℝ) - 1) * (q_hi - qStar) ∧
      M.F v₄ - M.F v₃ = ((M.m : ℝ) - 1) * (qStar - q_lo) ∧
      α = (∫ v in v₁..v₂, v * (((M.n : ℝ) - 1) * (effDist M θ (rivalIdx M) v) ^ (M.n - 2) *
              (M.f v / ((M.m : ℝ) - 1)))) /
            (∫ v in v₁..v₂, ((M.n : ℝ) - 1) * (effDist M θ (rivalIdx M) v) ^ (M.n - 2) *
              (M.f v / ((M.m : ℝ) - 1))) ∧
      β = (∫ v in v₃..v₄, v * (((M.n : ℝ) - 1) * (effDist M θ (rivalIdx M) v) ^ (M.n - 2) *
              (M.f v / ((M.m : ℝ) - 1)))) /
            (∫ v in v₃..v₄, ((M.n : ℝ) - 1) * (effDist M θ (rivalIdx M) v) ^ (M.n - 2) *
              (M.f v / ((M.m : ℝ) - 1))) ∧
      α = (v₂ * (1 - qStar) ^ (M.n - 1) - v₁ * (M.A v₁) ^ (M.n - 1) -
            ∫ v in v₁..v₂, (M.A v₁ + (M.F v - M.F v₁) / ((M.m : ℝ) - 1)) ^ (M.n - 1)) /
          ((1 - qStar) ^ (M.n - 1) - (M.A v₁) ^ (M.n - 1)) ∧
      β = (v₄ * (M.A v₄) ^ (M.n - 1) - v₃ * (1 - qStar) ^ (M.n - 1) -
            ∫ v in v₃..v₄, (1 - qStar + (M.F v - M.F v₃) / ((M.m : ℝ) - 1)) ^ (M.n - 1)) /
          ((M.A v₄) ^ (M.n - 1) - (1 - qStar) ^ (M.n - 1)) := by
  intro q_lo q_hi qStar
  have hρ1 : ρ ≤ 1 := hρα.trans (hαβ.le.trans hβ1)
  let m1 := singlePoolMech ρ α β hρ0 hρα hαβ hβ1
  let I0 : Pool := ⟨α, β, hαβ⟩
  have hI0 : I0 ∈ m1.pools := by simp [m1, singlePoolMech, I0]
  let σ := sigma M m1 ρ hρ0 hρ1 θ
  obtain ⟨hu0_lt_v1, hv14, hv4_lt1, hv1α, hβv4, hunif, htight1, htight4⟩ := hband
  have hρ_lt_v1 : ρ < v₁ := (le_max_left ρ M.a).trans_lt hu0_lt_v1
  have ha_lt_v1 : M.a < v₁ := (le_max_right ρ M.a).trans_lt hu0_lt_v1
  have hv1_0 : 0 ≤ v₁ := M.ha0.trans ha_lt_v1.le
  have hv4_0 : 0 ≤ v₄ := hv1_0.trans hv14.le
  have hv1_1 : v₁ ≤ 1 := (hv14.trans hv4_lt1).le
  have hF1_v1 : effDist M θ 0 v₁ = M.A v₁ := hunif v₁ (Or.inl ⟨hu0_lt_v1.le, le_refl v₁⟩)
  have hF1_v4 : effDist M θ 0 v₄ = M.A v₄ := hunif v₄ (Or.inr ⟨le_refl v₄, hv4_lt1.le⟩)
  have hFriv_A_of_F1 : ∀ v, effDist M θ 0 v = M.A v → FrivOf M (effDist M θ 0) v = M.A v := by
    intro v hF1v
    unfold FrivOf Market.A at *; rw [hF1v]
    have hm1 := M.m_sub_one_pos_real.ne'; have hm := M.m_pos_real.ne'
    field_simp [hm1, hm]; ring
  have hFriv_v1 : FrivOf M (effDist M θ 0) v₁ = M.A v₁ := hFriv_A_of_F1 v₁ hF1_v1
  have hFriv_v4 : FrivOf M (effDist M θ 0) v₄ = M.A v₄ := hFriv_A_of_F1 v₄ hF1_v4
  refine ⟨hF1_v1, hF1_v4, hFriv_v1, hFriv_v4, ?_⟩
  have hσ_cont : ContinuousOn σ (Icc 0 1) := sigma_continuousOn M m1 ρ hρ0 hρ1 hSR
  have hσ_np : ∀ v ∈ Icc ρ 1, σ v ≤ 0 := by
    have h1 := (prop2_sigma_pos_initial M m1 ρ hρ0 hρ1 hSR).1 (le_refl ρ)
    have hmin : min m1.r ρ = ρ := min_self ρ
    rwa [hmin] at h1
  -- σ(v₄) = 0 since F₁ = A on [v₄, 1]
  have hσ_v4 : σ v₄ = 0 := by
    have hconst_σ : ∀ t ∈ Icc v₄ 1, σ t = σ v₄ := fun t ht => by
      have hsub := sigma_sub M m1 ρ hρ0 hρ1 hSR hv4_0 hv4_lt1.le (hv4_0.trans ht.1) ht.2
      have h0 : ∫ u in v₄..t, (alloc M m1 (effDist M θ 0) u -
          alloc M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) u) = 0 := by
        have hcongr : ∫ u in v₄..t, (alloc M m1 (effDist M θ 0) u -
            alloc M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) u) = ∫ _ in v₄..t, (0 : ℝ) := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards with u hu
          rw [uIoc_of_le ht.1] at hu
          have hu_mem : u ∈ Icc v₄ 1 := ⟨hu.1.le, hu.2.trans ht.2⟩
          have hF1u : effDist M θ 0 u = M.A u := hunif u (Or.inr hu_mem)
          have hFrivu : effDist M θ (rivalIdx M) u = M.A u := by
            rw [(prop2_rival_symmetry M m1 ρ hρ0 hρ1 hSR).2 (rivalIdx M) (rivalIdx_ne_zero M) u
              ⟨(hρ_lt_v1.le.trans hv14.le).trans hu.1.le, hu_mem.2⟩]
            exact hFriv_A_of_F1 u hF1u
          rw [alloc_off_pools M m1 _ ((hρ_lt_v1.le.trans hv14.le).trans hu.1.le) (fun I hI => by
            simp only [m1, singlePoolMech, List.mem_singleton] at hI; subst hI
            intro h; linarith [h.2, hu.1, hβv4]), alloc_SPA,
            ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr ((hρ_lt_v1.le.trans hv14.le).trans hu.1.le))),
            hF1u, hFrivu, sub_self]
        rw [hcongr]; simp
      dsimp only [σ]; linarith
    by_contra hne
    have hneg : σ v₄ < 0 := lt_of_le_of_ne (hσ_np v₄ ⟨hρ_lt_v1.le.trans hv14.le, hv4_lt1.le⟩) hne
    have hneg_all : ∀ t ∈ Ioo v₄ 1, σ t < 0 := fun t ht => by
      rw [hconst_σ t (Ioo_subset_Icc_self ht)]; exact hneg
    have h1 := (prop2_sigma_neg_on_Ioo M m1 ρ hρ0 hρ1 hSR hv4_lt1.le (le_refl 1) hneg_all).2
      v₄ (left_mem_Icc.mpr hv4_lt1.le) 1 (right_mem_Icc.mpr hv4_lt1.le)
    rw [hF1_v4, vs_effDist_one] at h1
    have hA_lt1 : M.A v₄ < 1 := by
      unfold Market.A
      have hFlt := M.F_strictMonoOn ⟨(ha_lt_v1.trans hv14).le, hv4_lt1.le⟩ (right_mem_Icc.mpr M.ha1.le) hv4_lt1
      rw [M.hF_1] at hFlt; linarith [div_pos (sub_pos.mpr hFlt) M.m_pos_real]
    linarith
  have hleft := singlePool_left_neg M hρ0 hρα hαβ hβ1 hSR hu0_lt_v1 hv1α hβv4 hv4_lt1.le
    (fun v hv => hunif v (Or.inl hv)) htight1 (Or.inr hσ_v4)
  have hσ_v1 : σ v₁ = 0 := hleft.2.1
  have hneg_left : v₁ < α → ∀ t ∈ Ioc v₁ α, σ t < 0 := hleft.2.2
  have hneg_right : β < v₄ → ∀ t ∈ Ico β v₄, σ t < 0 := by
    intro hβ_lt_v4 t ht
    have hex_neg : ∃ x ∈ Ioo t v₄, σ x < 0 := by
      by_contra hall; push Not at hall
      have hzero : ∀ u ∈ Icc t v₄, σ u = 0 := fun u hu => by
        rcases eq_or_lt_of_le hu.2 with rfl | h2
        · exact hσ_v4
        · rcases eq_or_lt_of_le hu.1 with rfl | h1
          · have hlim : Tendsto σ (𝓝[Ioo t v₄] t) (𝓝 (σ t)) :=
              (hσ_cont t ⟨hv1_0.trans (hv1α.trans (hαβ.le.trans ht.1)), ht.2.le.trans hv4_lt1.le⟩).mono_left
                (nhdsWithin_mono t (fun z hz => ⟨hv1_0.trans (hv1α.trans (hαβ.le.trans (ht.1.trans hz.1.le))), hz.2.le.trans hv4_lt1.le⟩))
            have h0' : Tendsto σ (𝓝[Ioo t v₄] t) (𝓝 0) :=
              tendsto_const_nhds.congr' (Filter.eventually_of_mem self_mem_nhdsWithin fun z hz =>
                (le_antisymm (hσ_np z ⟨hρ_lt_v1.le.trans (hv1α.trans (hαβ.le.trans (ht.1.trans hz.1.le))), hz.2.le.trans hv4_lt1.le⟩)
                  (hall z hz)).symm)
            haveI : (𝓝[Ioo t v₄] t).NeBot := left_nhdsWithin_Ioo_neBot ht.2
            exact tendsto_nhds_unique hlim h0'
          · exact le_antisymm (hσ_np u ⟨hρ_lt_v1.le.trans (hv1α.trans (hαβ.le.trans (ht.1.trans hu.1))), h2.le.trans hv4_lt1.le⟩) (hall u ⟨h1, h2⟩)
      have hF1_eq := (prop2_sigma_zero_off_pools M m1 ρ hρ0 hρ1 hSR
        (by have : max (max m1.r ρ) M.a = max ρ M.a := by simp [m1, singlePoolMech]
            rw [this]; exact hu0_lt_v1.le.trans (hv1α.trans (hαβ.le.trans ht.1))) ht.2 hv4_lt1.le
        (fun I hI u hu => by
          simp only [m1, singlePoolMech, List.mem_singleton] at hI; subst hI
          intro h; linarith [h.2, hu.1, ht.1])
        hzero).1
      obtain ⟨u, hu, hne⟩ := htight4 (v₄ - t) (sub_pos.mpr ht.2)
      exact hne (hF1_eq u ⟨(by linarith : t ≤ v₄ - (v₄ - t)).trans ((le_max_right _ _).trans hu.1.le), hu.2.le⟩)
    obtain ⟨x, hx, hσx⟩ := hex_neg
    let SL := {u ∈ Icc v₁ x | σ u = 0}
    let SR := {u ∈ Icc x v₄ | σ u = 0}
    have hSL_ne : SL.Nonempty := ⟨v₁, ⟨le_refl _, hv1α.trans (hαβ.le.trans (ht.1.trans hx.1.le))⟩, hσ_v1⟩
    have hSR_ne : SR.Nonempty := ⟨v₄, ⟨hx.2.le, le_refl _⟩, hσ_v4⟩
    have hSL_bdd : BddAbove SL := ⟨x, fun u hu => hu.1.2⟩
    have hSR_bdd : BddBelow SR := ⟨x, fun u hu => hu.1.1⟩
    let y₁ := sSup SL
    let y₂ := sInf SR
    have hSL_cl : IsClosed SL := by
      have : SL = Icc v₁ x ∩ σ ⁻¹' {0} := by ext u; simp [SL]
      rw [this]
      exact (hσ_cont.mono (Icc_subset_Icc hv1_0 (hx.2.le.trans hv4_lt1.le))).preimage_isClosed_of_isClosed
        isClosed_Icc isClosed_singleton
    have hSR_cl : IsClosed SR := by
      have : SR = Icc x v₄ ∩ σ ⁻¹' {0} := by ext u; simp [SR]
      rw [this]
      exact (hσ_cont.mono (Icc_subset_Icc (hv1_0.trans (hv1α.trans (hαβ.le.trans (ht.1.trans hx.1.le)))) hv4_lt1.le)).preimage_isClosed_of_isClosed
        isClosed_Icc isClosed_singleton
    have hy1_in : y₁ ∈ SL := by have h := csSup_mem_closure hSL_ne hSL_bdd; rwa [hSL_cl.closure_eq] at h
    have hy2_in : y₂ ∈ SR := by have h := csInf_mem_closure hSR_ne hSR_bdd; rwa [hSR_cl.closure_eq] at h
    have hy1_lt_x : y₁ < x := lt_of_le_of_ne hy1_in.1.2 (fun h => by rw [h] at hy1_in; linarith [hy1_in.2])
    have hx_lt_y2 : x < y₂ := lt_of_le_of_ne hy2_in.1.1 (fun h => by rw [← h] at hy2_in; linarith [hy2_in.2])
    have hneg_comp : ∀ u ∈ Ioo y₁ y₂, σ u < 0 := fun u hu => by
      refine lt_of_le_of_ne (hσ_np u ⟨hρ_lt_v1.le.trans (hy1_in.1.1.trans hu.1.le), (hu.2.le.trans hy2_in.1.2).trans hv4_lt1.le⟩) ?_
      intro h0
      rcases le_total u x with hux | hxu
      · exact not_lt.mpr (le_csSup hSL_bdd ⟨⟨hy1_in.1.1.trans hu.1.le, hux⟩, h0⟩) hu.1
      · exact not_lt.mpr (csInf_le hSR_bdd ⟨⟨hxu, hu.2.le.trans hy2_in.1.2⟩, h0⟩) hu.2
    have hy1_lt_β : y₁ < β := by
      by_contra hge; push Not at hge
      exact prop2_no_dip_without_endpoint M m1 ρ hρ0 hρ1 hSR
        (by have : max (max m1.r ρ) M.a = max ρ M.a := by simp [m1, singlePoolMech]
            rw [this]; exact hu0_lt_v1.le.trans hy1_in.1.1)
        (hy1_lt_x.trans hx_lt_y2) (hy2_in.1.2.trans hv4_lt1.le) hy1_in.2 hy2_in.2 hneg_comp (fun I hI => by
          simp only [m1, singlePoolMech, List.mem_singleton] at hI; subst hI
          exact ⟨fun h => not_le.mpr h.1 (hαβ.le.trans hge), fun h => not_le.mpr h.1 hge⟩)
    exact hneg_comp t ⟨hy1_lt_β.trans_le ht.1, hx.1.trans hx_lt_y2⟩
  -- Step 3: Z := {v ∈ Icc α β | σ v = 0} is nonempty and equals Icc v₂ v₃
  let Z := {v ∈ Icc α β | σ v = 0}
  have hA_lt : M.A v₁ < M.A v₄ := by
    unfold Market.A
    have hFlt := M.F_strictMonoOn ⟨ha_lt_v1.le, hv1_1⟩ ⟨(ha_lt_v1.trans hv14).le, hv4_lt1.le⟩ hv14
    linarith [div_lt_div_of_pos_right (sub_lt_sub_left hFlt 1) M.m_pos_real]
  have hZ_ne : Z.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have hneg_pool : ∀ t ∈ Icc α β, σ t < 0 := fun t ht =>
      lt_of_le_of_ne (hσ_np t ⟨hρα.trans ht.1, ht.2.trans hβ1⟩)
        (fun h0 => by have : t ∈ Z := ⟨ht, h0⟩; rw [hemp] at this; exact this)
    have hneg_all : ∀ t ∈ Ioo v₁ v₄, σ t < 0 := fun t ht => by
      by_cases h1 : t ≤ α
      · exact hneg_left (lt_of_lt_of_le ht.1 h1) t ⟨ht.1, h1⟩
      · push Not at h1
        by_cases h2 : t ≤ β
        · exact hneg_pool t ⟨h1.le, h2⟩
        · push Not at h2
          exact hneg_right (h2.trans ht.2) t ⟨h2.le, ht.2⟩
    have hF1_eq := (prop2_sigma_neg_on_Ioo M m1 ρ hρ0 hρ1 hSR hv14.le hv4_lt1.le hneg_all).2
      v₁ (left_mem_Icc.mpr hv14.le) v₄ (right_mem_Icc.mpr hv14.le)
    rw [hF1_v1, hF1_v4] at hF1_eq; linarith
  have hZ_bddA : BddAbove Z := ⟨β, fun v hv => hv.1.2⟩
  have hZ_bddB : BddBelow Z := ⟨α, fun v hv => hv.1.1⟩
  have hZ_cl : IsClosed Z := by
    have : Z = Icc α β ∩ σ ⁻¹' {0} := by ext v; simp [Z]
    rw [this]
    exact (hσ_cont.mono (Icc_subset_Icc (hρ0.trans hρα) hβ1)).preimage_isClosed_of_isClosed
      isClosed_Icc isClosed_singleton
  let v₂ := sInf Z
  let v₃ := sSup Z
  have hv2_in : v₂ ∈ Z := by have h := csInf_mem_closure hZ_ne hZ_bddB; rwa [hZ_cl.closure_eq] at h
  have hv3_in : v₃ ∈ Z := by have h := csSup_mem_closure hZ_ne hZ_bddA; rwa [hZ_cl.closure_eq] at h
  have hv23 : v₂ ≤ v₃ := le_trans (csInf_le hZ_bddB hZ_ne.some_mem) (le_csSup hZ_bddA hZ_ne.some_mem)
  have hZ_eq : ∀ t ∈ Icc v₂ v₃, σ t = 0 := fun t ht => by
    rcases eq_or_lt_of_le ht.1 with rfl | h1
    · exact hv2_in.2
    · rcases eq_or_lt_of_le ht.2 with rfl | h2
      · exact hv3_in.2
      · exact prop2_pool_zero_set_convex M m1 ρ hρ0 hρ1 hSR hI0
          (by have : max (max m1.r ρ) M.a = max ρ M.a := by simp [m1, singlePoolMech]
              rw [this]; exact hu0_lt_v1.le.trans (hv1α.trans hv2_in.1.1))
          hv2_in.1.1 h1 h2 hv3_in.1.2
          (fun u hu => hσ_np u ⟨hρα.trans (hv2_in.1.1.trans hu.1), (hu.2.trans hv3_in.1.2).trans hβ1⟩)
          hv2_in.2 hv3_in.2
  -- Step 4: σ < 0 on (v₁, v₂) and (v₃, v₄)
  have hneg_12 : ∀ t ∈ Ioo v₁ v₂, σ t < 0 := fun t ht => by
    by_cases h1 : t ≤ α
    · exact hneg_left (lt_of_lt_of_le ht.1 h1) t ⟨ht.1, h1⟩
    · push Not at h1
      refine lt_of_le_of_ne (hσ_np t ⟨hρα.trans h1.le, (ht.2.le.trans hv2_in.1.2).trans hβ1⟩) ?_
      intro h0; exact not_lt.mpr (csInf_le hZ_bddB ⟨⟨h1.le, ht.2.le.trans hv2_in.1.2⟩, h0⟩) ht.2
  have hneg_34 : ∀ t ∈ Ioo v₃ v₄, σ t < 0 := fun t ht => by
    by_cases h1 : β ≤ t
    · exact hneg_right (lt_of_le_of_lt h1 ht.2) t ⟨h1, ht.2⟩
    · push Not at h1
      refine lt_of_le_of_ne (hσ_np t ⟨hρα.trans (hv3_in.1.1.trans ht.1.le), h1.le.trans hβ1⟩) ?_
      intro h0; exact not_lt.mpr (le_csSup hZ_bddA ⟨⟨hv3_in.1.1.trans ht.1.le, h1.le⟩, h0⟩) ht.1
  have hv12_le : v₁ ≤ v₂ := hv1α.trans hv2_in.1.1
  have hv34_le : v₃ ≤ v₄ := hv3_in.1.2.trans hβv4
  have hv2_1 : v₂ ≤ 1 := hv2_in.1.2.trans (hβv4.trans hv4_lt1.le)
  have hv3_1 : v₃ ≤ 1 := hv34_le.trans hv4_lt1.le
  have h12_res := prop2_sigma_neg_on_Ioo M m1 ρ hρ0 hρ1 hSR hv12_le hv2_1 hneg_12
  have h34_res := prop2_sigma_neg_on_Ioo M m1 ρ hρ0 hρ1 hSR hv34_le hv4_lt1.le hneg_34
  have hae_12 : ∀ᵐ v ∂(volume.restrict (Icc v₁ v₂)), θ.θ 0 v = 0 := by
    have := h12_res.1; rwa [max_eq_left ha_lt_v1.le] at this
  have hae_34 : ∀ᵐ v ∂(volume.restrict (Icc v₃ v₄)), θ.θ 0 v = 0 := by
    have := h34_res.1; rwa [max_eq_left (ha_lt_v1.le.trans (hv12_le.trans hv23))] at this
  have hF1_v2 : effDist M θ 0 v₂ = M.A v₁ := by
    rw [h12_res.2 v₂ (right_mem_Icc.mpr hv12_le) v₁ (left_mem_Icc.mpr hv12_le), hF1_v1]
  have hF1_α : effDist M θ 0 α = M.A v₁ := by
    rw [h12_res.2 α ⟨hv1α, hv2_in.1.1⟩ v₁ (left_mem_Icc.mpr hv12_le), hF1_v1]
  have hF1_v3 : effDist M θ 0 v₃ = M.A v₄ := by
    rw [h34_res.2 v₃ (left_mem_Icc.mpr hv34_le) v₄ (right_mem_Icc.mpr hv34_le), hF1_v4]
  have hF1_β : effDist M θ 0 β = M.A v₄ := by
    rw [h34_res.2 β ⟨hv3_in.1.2, hβv4⟩ v₄ (right_mem_Icc.mpr hv34_le), hF1_v4]
  have hv2_lt_v3 : v₂ < v₃ := by
    rcases eq_or_lt_of_le hv23 with heq | hlt
    · exfalso; rw [heq] at hF1_v2; linarith
    · exact hlt
  have h23_res := prop2_sigma_zero_in_pool M m1 ρ hρ0 hρ1 hSR hI0
    (by have : max (max m1.r ρ) M.a = max ρ M.a := by simp [m1, singlePoolMech]
        rw [this]; exact hu0_lt_v1.le.trans hv12_le) hv2_in.1.1 hv2_lt_v3 hv3_in.1.2 hZ_eq
  have hqStar_pow := bandQStar_pow M ha_lt_v1.le hv14 hv4_lt1.le
  have hqStar_bds := bandQStar_bounds M ha_lt_v1.le hv14 hv4_lt1.le
  have hFriv_23 : ∀ v ∈ Icc v₂ v₃, effDist M θ (rivalIdx M) v = 1 - qStar := fun v hv => by
    have hp := h23_res.1 v hv
    dsimp only [I0] at hp
    rw [hF1_α, hF1_β, ← hqStar_pow.1] at hp
    have hr_nn : 0 ≤ 1 - qStar := (M.A_mem_Icc hv1_1).1.trans hqStar_bds.1.le
    have hFv_nn : 0 ≤ effDist M θ (rivalIdx M) v := effDist_nonneg θ _ (hv.2.trans hv3_1)
    have hn1 : M.n - 1 ≠ 0 := by have := M.hn; omega
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact absurd hp (ne_of_lt (pow_lt_pow_left₀ hlt hFv_nn hn1))
    · exact absurd hp (ne_of_gt (pow_lt_pow_left₀ hgt hr_nn hn1))
  have hserved : M.F v₃ - M.F v₂ = (M.F v₄ - M.F v₁) / (M.m : ℝ) := by
    have hsub := effDist_sub θ 0 hv2_1 hv3_1
    have hcongr : ∫ u in v₂..v₃, θ.θ 0 u * M.f u = ∫ u in v₂..v₃, M.f u := by
      apply intervalIntegral.integral_congr_ae
      have hae := (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mp h23_res.2
      filter_upwards [hae] with u hu hmem
      rw [uIoc_of_le hv2_lt_v3.le] at hmem; rw [hu ⟨hmem.1.le, hmem.2⟩, one_mul]
    rw [hcongr, M.integral_f hv2_1 hv3_1, hF1_v3, hF1_v2] at hsub
    unfold Market.A at hsub
    have hm := M.m_pos_real.ne'; field_simp [hm] at hsub ⊢; linarith
  have hFriv_formula_12 : ∀ v ∈ Icc v₁ v₂,
      effDist M θ (rivalIdx M) v = M.A v₁ + (M.F v - M.F v₁) / ((M.m : ℝ) - 1) := fun v hv => by
    rw [(prop2_rival_symmetry M m1 ρ hρ0 hρ1 hSR).2 (rivalIdx M) (rivalIdx_ne_zero M) v
      ⟨hρ_lt_v1.le.trans hv.1, hv.2.trans hv2_1⟩]
    unfold FrivOf
    rw [h12_res.2 v hv v₁ (left_mem_Icc.mpr hv12_le), hF1_v1]; unfold Market.A
    have hm1 := M.m_sub_one_pos_real.ne'; have hm := M.m_pos_real.ne'
    field_simp [hm1, hm]; ring
  have hFriv_formula_34 : ∀ v ∈ Icc v₃ v₄,
      effDist M θ (rivalIdx M) v = (1 - qStar) + (M.F v - M.F v₃) / ((M.m : ℝ) - 1) := fun v hv => by
    have hv3_eq : effDist M θ (rivalIdx M) v₃ = 1 - qStar := hFriv_23 v₃ (right_mem_Icc.mpr hv2_lt_v3.le)
    rw [(prop2_rival_symmetry M m1 ρ hρ0 hρ1 hSR).2 (rivalIdx M) (rivalIdx_ne_zero M) v
      ⟨(hρ_lt_v1.le.trans (hv12_le.trans hv23)).trans hv.1, hv.2.trans hv4_lt1.le⟩]
    rw [(prop2_rival_symmetry M m1 ρ hρ0 hρ1 hSR).2 (rivalIdx M) (rivalIdx_ne_zero M) v₃
      ⟨hρ_lt_v1.le.trans (hv12_le.trans hv23), hv3_1⟩] at hv3_eq
    unfold FrivOf at hv3_eq ⊢
    rw [h34_res.2 v hv v₃ (left_mem_Icc.mpr hv34_le)]
    have hm1 := M.m_sub_one_pos_real.ne'; field_simp [hm1] at hv3_eq ⊢; linarith
  have hmass_12 : M.F v₂ - M.F v₁ = ((M.m : ℝ) - 1) * (q_hi - qStar) := by
    have h1 := hFriv_formula_12 v₂ (right_mem_Icc.mpr hv12_le)
    rw [hFriv_23 v₂ (left_mem_Icc.mpr hv2_lt_v3.le)] at h1
    have hm1 := M.m_sub_one_pos_real.ne'; dsimp only [q_hi]; unfold Market.A at h1
    field_simp [hm1] at h1 ⊢; linarith
  have hmass_34 : M.F v₄ - M.F v₃ = ((M.m : ℝ) - 1) * (qStar - q_lo) := by
    have h1 := hFriv_formula_34 v₄ (right_mem_Icc.mpr hv34_le)
    rw [(prop2_rival_symmetry M m1 ρ hρ0 hρ1 hSR).2 (rivalIdx M) (rivalIdx_ne_zero M) v₄
      ⟨hρ_lt_v1.le.trans hv14.le, hv4_lt1.le⟩, hFriv_v4] at h1
    have hm1 := M.m_sub_one_pos_real.ne'; dsimp only [q_lo]; unfold Market.A at h1
    field_simp [hm1] at h1 ⊢; linarith
  have hv1_lt_v2 : v₁ < v₂ := by
    rcases eq_or_lt_of_le hv12_le with heq | hlt
    · exfalso; rw [heq, sub_self] at hmass_12
      linarith [mul_pos M.m_sub_one_pos_real (sub_pos.mpr hqStar_bds.2.2.2)]
    · exact hlt
  have hv3_lt_v4 : v₃ < v₄ := by
    rcases eq_or_lt_of_le hv34_le with heq | hlt
    · exfalso; rw [heq, sub_self] at hmass_34
      linarith [mul_pos M.m_sub_one_pos_real (sub_pos.mpr hqStar_bds.2.2.1)]
    · exact hlt
  -- Step 7: α via outer_endpoint_strict_bounds + σ(v₂) - σ(v₁) = 0
  have hσ_diff_12 :
      (α - v₁) * (M.A v₁) ^ (M.n - 1) + (v₂ - α) * (1 - qStar) ^ (M.n - 1) -
        ∫ v in v₁..v₂, (M.A v₁ + (M.F v - M.F v₁) / ((M.m : ℝ) - 1)) ^ (M.n - 1) = 0 := by
    have hsub := sigma_sub M m1 ρ hρ0 hρ1 hSR hv1_0 hv1_1 (hv1_0.trans hv12_le) hv2_1
    have h20 : sigma M m1 ρ hρ0 hρ1 θ v₂ = 0 := hv2_in.2
    have h10 : sigma M m1 ρ hρ0 hρ1 θ v₁ = 0 := hσ_v1
    rw [h20, h10, sub_self] at hsub
    have hi1 := alloc_intervalIntegrable M m1 (effDist M θ 0) (vs_effDist_monotoneOn θ 0) (fun _ h => effDist_nonneg θ 0 h) hv1_1 hv2_1
    have hiR := alloc_intervalIntegrable M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M))
      (vs_effDist_monotoneOn θ (rivalIdx M)) (fun _ h => effDist_nonneg θ (rivalIdx M) h) hv1_1 hv2_1
    rw [intervalIntegral.integral_sub hi1 hiR] at hsub
    have hsplit : ∫ t in v₁..v₂, alloc M m1 (effDist M θ 0) t =
        (∫ t in v₁..α, alloc M m1 (effDist M θ 0) t) + (∫ t in α..v₂, alloc M m1 (effDist M θ 0) t) :=
      (intervalIntegral.integral_add_adjacent_intervals
        (alloc_intervalIntegrable M m1 _ (vs_effDist_monotoneOn θ 0) (fun _ h => effDist_nonneg θ 0 h) hv1_1 (hαβ.le.trans hβ1))
        (alloc_intervalIntegrable M m1 _ (vs_effDist_monotoneOn θ 0) (fun _ h => effDist_nonneg θ 0 h) (hαβ.le.trans hβ1) hv2_1)).symm
    have hL : ∫ t in v₁..α, alloc M m1 (effDist M θ 0) t = (α - v₁) * (M.A v₁) ^ (M.n - 1) := by
      have hc : ∫ t in v₁..α, alloc M m1 (effDist M θ 0) t = ∫ _ in v₁..α, (M.A v₁) ^ (M.n - 1) := by
        apply intervalIntegral.integral_congr_ae
        have hne : ∀ᵐ t ∂volume, t ≠ α := by simp [ae_iff, measure_singleton]
        filter_upwards [hne] with t htα ht
        rw [uIoc_of_le hv1α] at ht
        rw [alloc_off_pools M m1 _ (hρ_lt_v1.le.trans ht.1.le) (fun I hI => by
          simp only [m1, singlePoolMech, List.mem_singleton] at hI; subst hI
          intro h; linarith [h.1, lt_of_le_of_ne ht.2 htα]),
          h12_res.2 t ⟨ht.1.le, ht.2.trans hv2_in.1.1⟩ v₁ (left_mem_Icc.mpr hv12_le), hF1_v1]
      rw [hc, intervalIntegral.integral_const, smul_eq_mul]
    have hR : ∫ t in α..v₂, alloc M m1 (effDist M θ 0) t = (v₂ - α) * (1 - qStar) ^ (M.n - 1) := by
      have hc : ∫ t in α..v₂, alloc M m1 (effDist M θ 0) t = ∫ _ in α..v₂, (1 - qStar) ^ (M.n - 1) := by
        apply intervalIntegral.integral_congr_ae
        have hne : ∀ᵐ t ∂volume, t ≠ v₂ := by simp [ae_iff, measure_singleton]
        filter_upwards [hne] with t htv2 ht
        rw [uIoc_of_le hv2_in.1.1] at ht
        rw [alloc_in_pool M m1 _ hI0 ⟨ht.1, (lt_of_le_of_ne ht.2 htv2).trans_le hv2_in.1.2⟩]
        dsimp only [I0]; rw [hF1_α, hF1_β, ← hqStar_pow.1]
      rw [hc, intervalIntegral.integral_const, smul_eq_mul]
    have hRiv : ∫ t in v₁..v₂, alloc M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) t =
        ∫ v in v₁..v₂, (M.A v₁ + (M.F v - M.F v₁) / ((M.m : ℝ) - 1)) ^ (M.n - 1) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with t ht
      rw [uIoc_of_le hv12_le] at ht
      rw [alloc_SPA, ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr (hρ_lt_v1.le.trans ht.1.le))),
        hFriv_formula_12 t ⟨ht.1.le, ht.2⟩]
    linarith
  have hc1_12 : 1 - qStar = M.A v₁ + (M.F v₂ - M.F v₁) / ((M.m : ℝ) - 1) := by
    have := hFriv_formula_12 v₂ (right_mem_Icc.mpr hv12_le)
    rwa [hFriv_23 v₂ (left_mem_Icc.mpr hv2_lt_v3.le)] at this
  have hα_out := outer_endpoint_strict_bounds M ha_lt_v1.le hv1_lt_v2 hv2_1 (M.A_mem_Icc hv1_1).1 hc1_12
  have hα_ibp_eq :
      α = (v₂ * (1 - qStar) ^ (M.n - 1) - v₁ * (M.A v₁) ^ (M.n - 1) -
            ∫ v in v₁..v₂, (M.A v₁ + (M.F v - M.F v₁) / ((M.m : ℝ) - 1)) ^ (M.n - 1)) /
          ((1 - qStar) ^ (M.n - 1) - (M.A v₁) ^ (M.n - 1)) := by
    rw [eq_div_iff hα_out.1.ne']; linarith
  have hα_stieltjes :
      α = (∫ v in v₁..v₂, v * (((M.n : ℝ) - 1) * (effDist M θ (rivalIdx M) v) ^ (M.n - 2) *
              (M.f v / ((M.m : ℝ) - 1)))) /
            (∫ v in v₁..v₂, ((M.n : ℝ) - 1) * (effDist M θ (rivalIdx M) v) ^ (M.n - 2) *
              (M.f v / ((M.m : ℝ) - 1))) := by
    rw [hα_ibp_eq, hα_out.2.2.2]
    congr 1
    · exact intervalIntegral.integral_congr (fun v hv => by rw [uIcc_of_le hv12_le] at hv; rw [hFriv_formula_12 v hv])
    · exact intervalIntegral.integral_congr (fun v hv => by rw [uIcc_of_le hv12_le] at hv; rw [hFriv_formula_12 v hv])
  -- Step 8: β via outer_endpoint_strict_bounds + σ(v₄) - σ(v₃) = 0
  have hσ_diff_34 :
      (β - v₃) * (1 - qStar) ^ (M.n - 1) + (v₄ - β) * (M.A v₄) ^ (M.n - 1) -
        ∫ v in v₃..v₄, (1 - qStar + (M.F v - M.F v₃) / ((M.m : ℝ) - 1)) ^ (M.n - 1) = 0 := by
    have hsub := sigma_sub M m1 ρ hρ0 hρ1 hSR (hv1_0.trans (hv12_le.trans hv23)) hv3_1 hv4_0 hv4_lt1.le
    have h40 : sigma M m1 ρ hρ0 hρ1 θ v₄ = 0 := hσ_v4
    have h30 : sigma M m1 ρ hρ0 hρ1 θ v₃ = 0 := hv3_in.2
    rw [h40, h30, sub_self] at hsub
    have hi1 := alloc_intervalIntegrable M m1 (effDist M θ 0) (vs_effDist_monotoneOn θ 0) (fun _ h => effDist_nonneg θ 0 h) hv3_1 hv4_lt1.le
    have hiR := alloc_intervalIntegrable M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M))
      (vs_effDist_monotoneOn θ (rivalIdx M)) (fun _ h => effDist_nonneg θ (rivalIdx M) h) hv3_1 hv4_lt1.le
    rw [intervalIntegral.integral_sub hi1 hiR] at hsub
    have hsplit : ∫ t in v₃..v₄, alloc M m1 (effDist M θ 0) t =
        (∫ t in v₃..β, alloc M m1 (effDist M θ 0) t) + (∫ t in β..v₄, alloc M m1 (effDist M θ 0) t) :=
      (intervalIntegral.integral_add_adjacent_intervals
        (alloc_intervalIntegrable M m1 _ (vs_effDist_monotoneOn θ 0) (fun _ h => effDist_nonneg θ 0 h) hv3_1 hβ1)
        (alloc_intervalIntegrable M m1 _ (vs_effDist_monotoneOn θ 0) (fun _ h => effDist_nonneg θ 0 h) hβ1 hv4_lt1.le)).symm
    have hL : ∫ t in v₃..β, alloc M m1 (effDist M θ 0) t = (β - v₃) * (1 - qStar) ^ (M.n - 1) := by
      have hc : ∫ t in v₃..β, alloc M m1 (effDist M θ 0) t = ∫ _ in v₃..β, (1 - qStar) ^ (M.n - 1) := by
        apply intervalIntegral.integral_congr_ae
        have hne : ∀ᵐ t ∂volume, t ≠ β := by simp [ae_iff, measure_singleton]
        filter_upwards [hne] with t htβ ht
        rw [uIoc_of_le hv3_in.1.2] at ht
        rw [alloc_in_pool M m1 _ hI0 ⟨hv3_in.1.1.trans_lt ht.1, lt_of_le_of_ne ht.2 htβ⟩]
        dsimp only [I0]; rw [hF1_α, hF1_β, ← hqStar_pow.1]
      rw [hc, intervalIntegral.integral_const, smul_eq_mul]
    have hR : ∫ t in β..v₄, alloc M m1 (effDist M θ 0) t = (v₄ - β) * (M.A v₄) ^ (M.n - 1) := by
      have hc : ∫ t in β..v₄, alloc M m1 (effDist M θ 0) t = ∫ _ in β..v₄, (M.A v₄) ^ (M.n - 1) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards with t ht
        rw [uIoc_of_le hβv4] at ht
        rw [alloc_off_pools M m1 _ (hρα.trans (hαβ.le.trans ht.1.le)) (fun I hI => by
          simp only [m1, singlePoolMech, List.mem_singleton] at hI; subst hI
          intro h; linarith [h.2, ht.1]),
          h34_res.2 t ⟨hv3_in.1.2.trans ht.1.le, ht.2⟩ v₄ (right_mem_Icc.mpr hv34_le), hF1_v4]
      rw [hc, intervalIntegral.integral_const, smul_eq_mul]
    have hRiv : ∫ t in v₃..v₄, alloc M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) t =
        ∫ v in v₃..v₄, (1 - qStar + (M.F v - M.F v₃) / ((M.m : ℝ) - 1)) ^ (M.n - 1) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with t ht
      rw [uIoc_of_le hv34_le] at ht
      rw [alloc_SPA, ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr ((hρ_lt_v1.le.trans (hv12_le.trans hv23)).trans ht.1.le))),
        hFriv_formula_34 t ⟨ht.1.le, ht.2⟩]
    linarith
  have hc1_34 : M.A v₄ = 1 - qStar + (M.F v₄ - M.F v₃) / ((M.m : ℝ) - 1) := by
    have := hFriv_formula_34 v₄ (right_mem_Icc.mpr hv34_le)
    rw [(prop2_rival_symmetry M m1 ρ hρ0 hρ1 hSR).2 (rivalIdx M) (rivalIdx_ne_zero M) v₄
      ⟨hρ_lt_v1.le.trans hv14.le, hv4_lt1.le⟩, hFriv_v4] at this; exact this
  have hβ_out := outer_endpoint_strict_bounds M (ha_lt_v1.le.trans (hv12_le.trans hv23)) hv3_lt_v4 hv4_lt1.le
    ((M.A_mem_Icc hv1_1).1.trans hqStar_bds.1.le) hc1_34
  have hβ_ibp_eq :
      β = (v₄ * (M.A v₄) ^ (M.n - 1) - v₃ * (1 - qStar) ^ (M.n - 1) -
            ∫ v in v₃..v₄, (1 - qStar + (M.F v - M.F v₃) / ((M.m : ℝ) - 1)) ^ (M.n - 1)) /
          ((M.A v₄) ^ (M.n - 1) - (1 - qStar) ^ (M.n - 1)) := by
    rw [eq_div_iff hβ_out.1.ne']; linarith
  have hβ_stieltjes :
      β = (∫ v in v₃..v₄, v * (((M.n : ℝ) - 1) * (effDist M θ (rivalIdx M) v) ^ (M.n - 2) *
              (M.f v / ((M.m : ℝ) - 1)))) /
            (∫ v in v₃..v₄, ((M.n : ℝ) - 1) * (effDist M θ (rivalIdx M) v) ^ (M.n - 2) *
              (M.f v / ((M.m : ℝ) - 1))) := by
    rw [hβ_ibp_eq, hβ_out.2.2.2]
    congr 1
    · exact intervalIntegral.integral_congr (fun v hv => by rw [uIcc_of_le hv34_le] at hv; rw [hFriv_formula_34 v hv])
    · exact intervalIntegral.integral_congr (fun v hv => by rw [uIcc_of_le hv34_le] at hv; rw [hFriv_formula_34 v hv])
  exact ⟨v₂, v₃, hα_ibp_eq ▸ hα_out.2.1, hα_ibp_eq ▸ hα_out.2.2.1, hv2_lt_v3,
    hβ_ibp_eq ▸ hβ_out.2.1, hβ_ibp_eq ▸ hβ_out.2.2.1,
    hae_12, h23_res.2, hae_34, hserved, hFriv_23, hqStar_pow.2, hmass_12, hmass_34,
    hα_stieltjes, hβ_stieltjes, hα_ibp_eq, hβ_ibp_eq⟩

/-- **Explicit band visit strategy** for `(v₁, v₂, v₃, v₄)`: seller 1 gets `1` on `(v₂, v₃)`,
`0` on `(v₁, v₄) \ (v₂, v₃)`, and `1 / m` outside `(v₁, v₄)`; rivals split the remainder equally. -/
noncomputable def bandVisit (v₁ v₂ v₃ v₄ : ℝ) : VisitStrategy M where
  θ j v :=
    if j = 0 then
      if v ∈ Ioo v₂ v₃ then 1
      else if v ∈ Ioo v₁ v₄ then 0
      else 1 / (M.m : ℝ)
    else
      if v ∈ Ioo v₂ v₃ then 0
      else if v ∈ Ioo v₁ v₄ then 1 / ((M.m : ℝ) - 1)
      else 1 / (M.m : ℝ)
  hmeas j := by
    by_cases hj : j = 0
    · simp only [hj, ite_true]
      exact Measurable.ite measurableSet_Ioo measurable_const
        (Measurable.ite measurableSet_Ioo measurable_const measurable_const)
    · simp only [hj, ite_false]
      exact Measurable.ite measurableSet_Ioo measurable_const
        (Measurable.ite measurableSet_Ioo measurable_const measurable_const)
  hnonneg j v := by
    have hm := M.m_pos_real
    have hm1 := M.m_sub_one_pos_real
    split_ifs <;> positivity
  hsum v _ := by
    have hm : (M.m : ℝ) ≠ 0 := M.m_pos_real.ne'
    have hm1 : (M.m : ℝ) - 1 ≠ 0 := M.m_sub_one_pos_real.ne'
    have hsplit : ∑ j : Fin M.m, (if j = 0 then
        (if v ∈ Ioo v₂ v₃ then (1 : ℝ) else if v ∈ Ioo v₁ v₄ then 0 else 1 / (M.m : ℝ))
      else
        (if v ∈ Ioo v₂ v₃ then (0 : ℝ) else if v ∈ Ioo v₁ v₄ then 1 / ((M.m : ℝ) - 1) else 1 / (M.m : ℝ))) =
        (if v ∈ Ioo v₂ v₃ then (1 : ℝ) else if v ∈ Ioo v₁ v₄ then 0 else 1 / (M.m : ℝ)) +
        ∑ j ∈ Finset.univ.erase (0 : Fin M.m),
          (if v ∈ Ioo v₂ v₃ then (0 : ℝ) else if v ∈ Ioo v₁ v₄ then 1 / ((M.m : ℝ) - 1) else 1 / (M.m : ℝ)) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin M.m))]
      simp only [ite_true]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [ite_eq_right_iff.mpr (fun h => absurd h (Finset.ne_of_mem_erase hj))]
    rw [hsplit, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_sub (by have := M.hm; omega), Nat.cast_one]
    by_cases h23 : v ∈ Ioo v₂ v₃
    · simp [h23]
    · by_cases h14 : v ∈ Ioo v₁ v₄
      · simp [h23, h14, hm1]
      · simp [h23, h14]; field_simp [hm]; ring

/-- Given `(v₁, v₄)` with `M.a ≤ v₁ < v₄ ≤ 1`, uniquely determines `(v₂, v₃)` via eq. (5)
and intermediate value theorem on `M.F`. -/
lemma band_coords_exist {v₁ v₄ : ℝ} (hv1 : M.a ≤ v₁) (hlt : v₁ < v₄) (hv4 : v₄ ≤ 1) :
    let qStar := bandQStar M v₁ v₄
    let q_lo := (1 - M.F v₄) / (M.m : ℝ)
    let q_hi := (1 - M.F v₁) / (M.m : ℝ)
    ∃ v₂ v₃ : ℝ,
      v₁ < v₂ ∧ v₂ < v₃ ∧ v₃ < v₄ ∧
      M.F v₂ = M.F v₁ + ((M.m : ℝ) - 1) * (q_hi - qStar) ∧
      M.F v₃ = M.F v₄ - ((M.m : ℝ) - 1) * (qStar - q_lo) := by
  intro qStar q_lo q_hi
  have hbds := bandQStar_bounds M hv1 hlt hv4
  let G₂ := M.F v₁ + ((M.m : ℝ) - 1) * (q_hi - qStar)
  let G₃ := M.F v₄ - ((M.m : ℝ) - 1) * (qStar - q_lo)
  have hG12 : M.F v₁ < G₂ := by
    dsimp only [G₂]; linarith [mul_pos M.m_sub_one_pos_real (sub_pos.mpr hbds.2.2.2)]
  have hG34 : G₃ < M.F v₄ := by
    dsimp only [G₃]; linarith [mul_pos M.m_sub_one_pos_real (sub_pos.mpr hbds.2.2.1)]
  have hG23 : G₂ < G₃ := by
    have hdiff : G₃ - G₂ = (M.F v₄ - M.F v₁) / (M.m : ℝ) := by
      dsimp only [G₂, G₃, q_lo, q_hi]
      have hm : (M.m : ℝ) ≠ 0 := M.m_pos_real.ne'
      field_simp [hm]; ring
    have hFlt := M.F_strictMonoOn ⟨hv1, hlt.le.trans hv4⟩ ⟨hv1.trans hlt.le, hv4⟩ hlt
    linarith [div_pos (sub_pos.mpr hFlt) M.m_pos_real]
  have hF_cont : ContinuousOn M.F (Icc v₁ v₄) := M.F_continuousOn.mono (Icc_subset_Icc hv1 hv4)
  obtain ⟨v₂, hv2_mem, hv2_eq⟩ := intermediate_value_Icc hlt.le hF_cont ⟨hG12.le, (hG23.trans hG34).le⟩
  obtain ⟨v₃, hv3_mem, hv3_eq⟩ := intermediate_value_Icc hlt.le hF_cont ⟨(hG12.trans hG23).le, hG34.le⟩
  have hstrict := M.F_strictMonoOn.mono (Icc_subset_Icc hv1 hv4)
  have hv12 : v₁ < v₂ := by
    rcases eq_or_lt_of_le hv2_mem.1 with rfl | h
    · linarith
    · exact h
  have hv23 : v₂ < v₃ := by
    by_contra hge; push Not at hge
    have := hstrict.monotoneOn hv3_mem hv2_mem hge; linarith
  have hv34 : v₃ < v₄ := by
    rcases eq_or_lt_of_le hv3_mem.2 with rfl | h
    · linarith
    · exact h
  exact ⟨v₂, v₃, hv12, hv23, hv34, hv2_eq, hv3_eq⟩

/-- Explicit map `bandToPool M (v₁, v₄) = (α, β)` assigning to every candidate band `(v₁, v₄)`
the unique pool endpoints `(α, β)` given by equation (15). -/
noncomputable def bandToPool (p : ℝ × ℝ) : ℝ × ℝ :=
  if h : M.a ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ 1 then
    let v₁ := p.1
    let v₄ := p.2
    let qStar := bandQStar M v₁ v₄
    let v₂ := (band_coords_exist M h.1 h.2.1 h.2.2).choose
    let v₃ := (band_coords_exist M h.1 h.2.1 h.2.2).choose_spec.choose
    let α := (v₂ * (1 - qStar) ^ (M.n - 1) - v₁ * (M.A v₁) ^ (M.n - 1) -
                ∫ v in v₁..v₂, (M.A v₁ + (M.F v - M.F v₁) / ((M.m : ℝ) - 1)) ^ (M.n - 1)) /
              ((1 - qStar) ^ (M.n - 1) - (M.A v₁) ^ (M.n - 1))
    let β := (v₄ * (M.A v₄) ^ (M.n - 1) - v₃ * (1 - qStar) ^ (M.n - 1) -
                ∫ v in v₃..v₄, (1 - qStar + (M.F v - M.F v₃) / ((M.m : ℝ) - 1)) ^ (M.n - 1)) /
              ((M.A v₄) ^ (M.n - 1) - (1 - qStar) ^ (M.n - 1))
    (α, β)
  else (0, 0)

/-- **Reverse construction for Lemma 1(iii)**: For any interior band `(v₁, v₄)` with
`max ρ a < v₁ < v₄ < 1`, the pool `(α, β) = bandToPool M (v₁, v₄)` satisfies
`v₁ < α < v₂ < v₃ < β < v₄`, and `bandVisit M v₁ v₂ v₃ v₄` is an SR continuation for
`singlePoolMech ρ α β` with interior band `[v₁, v₄]`. -/
theorem lemma1_band_to_pool_sr {ρ v₁ v₄ : ℝ} (hρ0 : 0 ≤ ρ)
    (hu0_lt : max ρ M.a < v₁) (hv14 : v₁ < v₄) (hv4_lt1 : v₄ < 1) :
    let α := (bandToPool M (v₁, v₄)).1
    let β := (bandToPool M (v₁, v₄)).2
    ∃ (hρα : ρ ≤ α) (hαβ : α < β) (hβ1 : β ≤ 1) (θ : VisitStrategy M),
      v₁ < α ∧ β < v₄ ∧
      IsSR M (unilateralProfile M (singlePoolMech ρ α β hρ0 hρα hαβ hβ1) ρ hρ0
        (hρα.trans (hαβ.le.trans hβ1))) θ ∧
      IsInteriorBand M ρ α β θ v₁ v₄ := by
  have ha_lt_v1 : M.a < v₁ := (le_max_right ρ M.a).trans_lt hu0_lt
  have hρ_lt_v1 : ρ < v₁ := (le_max_left ρ M.a).trans_lt hu0_lt
  have hcond : M.a ≤ v₁ ∧ v₁ < v₄ ∧ v₄ ≤ 1 := ⟨ha_lt_v1.le, hv14, hv4_lt1.le⟩
  let hex := band_coords_exist M hcond.1 hcond.2.1 hcond.2.2
  let v₂ := hex.choose
  let v₃ := hex.choose_spec.choose
  obtain ⟨hv12, hv23, hv34, hFv2, hFv3⟩ := hex.choose_spec.choose_spec
  let qStar := bandQStar M v₁ v₄
  have hqStar_pow := bandQStar_pow M ha_lt_v1.le hv14 hv4_lt1.le
  have hqStar_bds := bandQStar_bounds M ha_lt_v1.le hv14 hv4_lt1.le
  have hv1_1 : v₁ ≤ 1 := (hv14.trans hv4_lt1).le
  have hv2_1 : v₂ ≤ 1 := ((hv23.trans hv34).trans hv4_lt1).le
  have hv3_1 : v₃ ≤ 1 := (hv34.trans hv4_lt1).le
  let g1 : ℝ → ℝ := fun v => M.A v₁ + (M.F v - M.F v₁) / ((M.m : ℝ) - 1)
  let g2 : ℝ → ℝ := fun v => 1 - qStar + (M.F v - M.F v₃) / ((M.m : ℝ) - 1)
  have hg1_v1 : g1 v₁ = M.A v₁ := by dsimp only [g1]; simp
  have hg1_v2 : g1 v₂ = 1 - qStar := by
    dsimp only [g1]; rw [hFv2]; unfold Market.A
    have hm1 := M.m_sub_one_pos_real.ne'; field_simp [hm1]; ring
  have hg2_v3 : g2 v₃ = 1 - qStar := by dsimp only [g2]; simp
  have hg2_v4 : g2 v₄ = M.A v₄ := by
    dsimp only [g2]; rw [hFv3]; unfold Market.A
    have hm1 := M.m_sub_one_pos_real.ne'; field_simp [hm1]; ring
  let α := (v₂ * (1 - qStar) ^ (M.n - 1) - v₁ * (M.A v₁) ^ (M.n - 1) -
      ∫ v in v₁..v₂, (g1 v) ^ (M.n - 1)) / ((1 - qStar) ^ (M.n - 1) - (M.A v₁) ^ (M.n - 1))
  let β := (v₄ * (M.A v₄) ^ (M.n - 1) - v₃ * (1 - qStar) ^ (M.n - 1) -
      ∫ v in v₃..v₄, (g2 v) ^ (M.n - 1)) / ((M.A v₄) ^ (M.n - 1) - (1 - qStar) ^ (M.n - 1))
  have hbtp : bandToPool M (v₁, v₄) = (α, β) := by
    unfold bandToPool; simp only [hcond]; rfl
  rw [hbtp]; dsimp only
  have hr_nn : 0 ≤ 1 - qStar := (M.A_mem_Icc hv1_1).1.trans hqStar_bds.1.le
  have hα_out := outer_endpoint_strict_bounds M ha_lt_v1.le hv12 hv2_1 (M.A_mem_Icc hv1_1).1 hg1_v2.symm
  have hβ_out := outer_endpoint_strict_bounds M (ha_lt_v1.le.trans (hv12.le.trans hv23.le)) hv34 hv4_lt1.le hr_nn hg2_v4.symm
  have hα_bds : v₁ < α ∧ α < v₂ := ⟨hα_out.2.1, hα_out.2.2.1⟩
  have hβ_bds : v₃ < β ∧ β < v₄ := ⟨hβ_out.2.1, hβ_out.2.2.1⟩
  have hρα : ρ ≤ α := hρ_lt_v1.le.trans hα_bds.1.le
  have hαβ : α < β := hα_bds.2.trans (hv23.trans hβ_bds.1)
  have hβ1 : β ≤ 1 := hβ_bds.2.le.trans hv4_lt1.le
  have hρ1 : ρ ≤ 1 := hρα.trans (hαβ.le.trans hβ1)
  let m1 := singlePoolMech ρ α β hρ0 hρα hαβ hβ1
  let I0 : Pool := ⟨α, β, hαβ⟩
  have hI0 : I0 ∈ m1.pools := by simp [m1, singlePoolMech, I0]
  let θ := bandVisit M v₁ v₂ v₃ v₄
  have hmass_23 : M.F v₃ - M.F v₂ = (M.F v₄ - M.F v₁) / (M.m : ℝ) := by
    rw [hFv2, hFv3]; have hm := M.m_pos_real.ne'; field_simp [hm]; ring
  have hF1_41 : ∀ v ∈ Icc v₄ 1, effDist M θ 0 v = M.A v := fun v hv => by
    unfold effDist Market.A
    have hcongr : ∫ u in v..1, θ.θ 0 u * M.f u = ∫ u in v..1, (1 / (M.m : ℝ)) * M.f u := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with u hu
      rw [uIoc_of_le hv.2] at hu
      have hnot14 : u ∉ Ioo v₁ v₄ := fun h => not_lt.mpr (hv.1.trans hu.1.le) h.2
      have hnot23 : u ∉ Ioo v₂ v₃ := fun h => not_lt.mpr (hv34.le.trans (hv.1.trans hu.1.le)) h.2
      dsimp only [θ, bandVisit]; simp only [ite_true, hnot23, hnot14, ite_false]
    rw [hcongr, intervalIntegral.integral_const_mul, M.integral_f hv.2 (le_refl 1), M.hF_1]; ring
  have hF1_34 : ∀ v ∈ Icc v₃ v₄, effDist M θ 0 v = M.A v₄ := fun v hv => by
    have hsub := effDist_sub θ 0 (hv.2.trans hv4_lt1.le) hv4_lt1.le
    have h0 : ∫ u in v..v₄, θ.θ 0 u * M.f u = 0 := by
      have hcongr : ∫ u in v..v₄, θ.θ 0 u * M.f u = ∫ _ in v..v₄, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_ae
        have hne : ∀ᵐ u ∂volume, u ≠ v₄ := by simp [ae_iff, measure_singleton]
        filter_upwards [hne] with u huv4 hu
        rw [uIoc_of_le hv.2] at hu
        have h14 : u ∈ Ioo v₁ v₄ := ⟨(hv12.trans hv23).trans_le (hv.1.trans hu.1.le), lt_of_le_of_ne hu.2 huv4⟩
        have hnot23 : u ∉ Ioo v₂ v₃ := fun h => not_lt.mpr (hv.1.trans hu.1.le) h.2
        dsimp only [θ, bandVisit]; simp only [ite_true, hnot23, h14, ite_false, zero_mul]
      rw [hcongr]; simp
    rw [hF1_41 v₄ (left_mem_Icc.mpr hv4_lt1.le)] at hsub; linarith
  have hF1_23 : ∀ v ∈ Icc v₂ v₃, effDist M θ 0 v = M.A v₁ + (M.F v - M.F v₂) := fun v hv => by
    have hsub := effDist_sub θ 0 (hv.2.trans hv3_1) hv3_1
    have h1 : ∫ u in v..v₃, θ.θ 0 u * M.f u = M.F v₃ - M.F v := by
      have hcongr : ∫ u in v..v₃, θ.θ 0 u * M.f u = ∫ u in v..v₃, M.f u := by
        apply intervalIntegral.integral_congr_ae
        have hne : ∀ᵐ u ∂volume, u ≠ v₃ := by simp [ae_iff, measure_singleton]
        filter_upwards [hne] with u huv3 hu
        rw [uIoc_of_le hv.2] at hu
        have h23 : u ∈ Ioo v₂ v₃ := ⟨hv.1.trans_lt hu.1, lt_of_le_of_ne hu.2 huv3⟩
        dsimp only [θ, bandVisit]; simp only [ite_true, h23, one_mul]
      rw [hcongr, M.integral_f (hv.2.trans hv3_1) hv3_1]
    rw [hF1_34 v₃ (left_mem_Icc.mpr hv34.le)] at hsub
    have hAdiff : M.A v₄ - M.A v₁ = (M.F v₄ - M.F v₁) / (M.m : ℝ) := by unfold Market.A; ring
    linarith
  have hF1_12 : ∀ v ∈ Icc v₁ v₂, effDist M θ 0 v = M.A v₁ := fun v hv => by
    have hsub := effDist_sub θ 0 (hv.2.trans hv2_1) hv2_1
    have h0 : ∫ u in v..v₂, θ.θ 0 u * M.f u = 0 := by
      have hcongr : ∫ u in v..v₂, θ.θ 0 u * M.f u = ∫ _ in v..v₂, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards with u hu
        rw [uIoc_of_le hv.2] at hu
        have h14 : u ∈ Ioo v₁ v₄ := ⟨hv.1.trans_lt hu.1, hu.2.trans_lt (hv23.trans hv34)⟩
        have hnot23 : u ∉ Ioo v₂ v₃ := fun h => not_lt.mpr hu.2 h.1
        dsimp only [θ, bandVisit]; simp only [ite_true, hnot23, h14, ite_false, zero_mul]
      rw [hcongr]; simp
    have hv2_eq := hF1_23 v₂ (left_mem_Icc.mpr hv23.le)
    simp only [sub_self, add_zero] at hv2_eq; linarith
  have hF1_01 : ∀ v ≤ v₁, effDist M θ 0 v = M.A v := fun v hv => by
    have hsub := effDist_sub θ 0 (hv.trans hv1_1) hv1_1
    have h1 : ∫ u in v..v₁, θ.θ 0 u * M.f u = (M.F v₁ - M.F v) / (M.m : ℝ) := by
      have hcongr : ∫ u in v..v₁, θ.θ 0 u * M.f u = ∫ u in v..v₁, (1 / (M.m : ℝ)) * M.f u := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards with u hu
        rw [uIoc_of_le hv] at hu
        have hnot14 : u ∉ Ioo v₁ v₄ := fun h => not_lt.mpr hu.2 h.1
        have hnot23 : u ∉ Ioo v₂ v₃ := fun h => not_lt.mpr (hu.2.trans hv12.le) h.1
        dsimp only [θ, bandVisit]; simp only [ite_true, hnot23, hnot14, ite_false]
      rw [hcongr, intervalIntegral.integral_const_mul, M.integral_f (hv.trans hv1_1) hv1_1]; ring
    rw [h1, hF1_12 v₁ (left_mem_Icc.mpr hv12.le)] at hsub
    unfold Market.A at hsub ⊢; have hm := M.m_pos_real.ne'; field_simp [hm] at hsub ⊢; linarith
  have hFriv_sym : ∀ j : Fin M.m, j ≠ 0 → ∀ v ≤ 1, effDist M θ j v = FrivOf M (effDist M θ 0) v := by
    intro j hj v hv1'
    have hall : ∀ k : Fin M.m, k ≠ 0 → effDist M θ k v = effDist M θ j v := fun k hk => by
      unfold effDist; congr 1
      apply intervalIntegral.integral_congr
      intro u _; simp [θ, bandVisit, hk, hj]
    have hsum := effDist_sum_one_sub θ hv1'
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin M.m))] at hsum
    have hrest : ∑ k ∈ Finset.univ.erase (0 : Fin M.m), (1 - effDist M θ k v) =
        ((M.m : ℝ) - 1) * (1 - effDist M θ j v) := by
      rw [Finset.sum_congr rfl (fun k hk => by rw [hall k (Finset.ne_of_mem_erase hk)]),
        Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_sub (by have := M.hm; omega), Nat.cast_one]
    rw [hrest] at hsum; unfold FrivOf
    have hm1 := M.m_sub_one_pos_real.ne'; field_simp [hm1] at hsum ⊢; linarith
  have hFriv_41 : ∀ v ∈ Icc v₄ 1, FrivOf M (effDist M θ 0) v = M.A v := fun v hv => by
    unfold FrivOf; rw [hF1_41 v hv]; unfold Market.A
    have hm1 := M.m_sub_one_pos_real.ne'; have hm := M.m_pos_real.ne'; field_simp [hm1, hm]; ring
  have hFriv_34 : ∀ v ∈ Icc v₃ v₄, FrivOf M (effDist M θ 0) v = g2 v := fun v hv => by
    unfold FrivOf; rw [hF1_34 v hv]; dsimp only [g2]; rw [hFv3]; unfold Market.A
    have hm1 := M.m_sub_one_pos_real.ne'; have hm := M.m_pos_real.ne'; field_simp [hm1, hm]; ring
  have hFriv_23 : ∀ v ∈ Icc v₂ v₃, FrivOf M (effDist M θ 0) v = 1 - qStar := fun v hv => by
    unfold FrivOf; rw [hF1_23 v hv, hFv2]; unfold Market.A
    have hm1 := M.m_sub_one_pos_real.ne'; have hm := M.m_pos_real.ne'; field_simp [hm1, hm]; ring
  have hFriv_12 : ∀ v ∈ Icc v₁ v₂, FrivOf M (effDist M θ 0) v = g1 v := fun v hv => by
    unfold FrivOf; rw [hF1_12 v hv]; dsimp only [g1]; unfold Market.A
    have hm1 := M.m_sub_one_pos_real.ne'; have hm := M.m_pos_real.ne'; field_simp [hm1, hm]; ring
  have hFriv_01 : ∀ v ≤ v₁, FrivOf M (effDist M θ 0) v = M.A v := fun v hv => by
    unfold FrivOf; rw [hF1_01 v hv]; unfold Market.A
    have hm1 := M.m_sub_one_pos_real.ne'; have hm := M.m_pos_real.ne'; field_simp [hm1, hm]; ring
  have hF1_α : effDist M θ 0 α = M.A v₁ := hF1_12 α ⟨hα_bds.1.le, hα_bds.2.le⟩
  have hF1_β : effDist M θ 0 β = M.A v₄ := hF1_34 β ⟨hβ_bds.1.le, hβ_bds.2.le⟩
  let δ : ℝ → ℝ := fun v => surplus M m1 (effDist M θ 0) v -
      surplus M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) v
  have hδ_sub : ∀ x y, x ≤ 1 → y ≤ 1 →
      δ y - δ x = ∫ t in x..y, (alloc M m1 (effDist M θ 0) t -
        alloc M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) t) := fun x y hx1 hy1 => by
    dsimp only [δ]
    have h1 := surplus_sub M m1 (effDist M θ 0) (vs_effDist_monotoneOn θ 0) (fun _ h => effDist_nonneg θ 0 h) hx1 hy1
    have h2 := surplus_sub M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M))
      (vs_effDist_monotoneOn θ (rivalIdx M)) (fun _ h => effDist_nonneg θ (rivalIdx M) h) hx1 hy1
    have hi1 := alloc_intervalIntegrable M m1 (effDist M θ 0) (vs_effDist_monotoneOn θ 0) (fun _ h => effDist_nonneg θ 0 h) hx1 hy1
    have hi2 := alloc_intervalIntegrable M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M))
      (vs_effDist_monotoneOn θ (rivalIdx M)) (fun _ h => effDist_nonneg θ (rivalIdx M) h) hx1 hy1
    rw [intervalIntegral.integral_sub hi1 hi2]; linarith
  have hδ_01 : ∀ v ∈ Icc 0 v₁, δ v = 0 := fun v hv => by
    by_cases hvρ : v ≤ ρ
    · dsimp only [δ]
      rw [surplus_zero_of_le_r M m1 _ hv.1 hvρ,
          surplus_zero_of_le_r M (SPA ρ hρ0 hρ1) _ hv.1 hvρ, sub_self]
    · push Not at hvρ
      have h0 : δ ρ = 0 := by
        dsimp only [δ]
        rw [surplus_zero_of_le_r M m1 _ hρ0 (le_refl ρ),
            surplus_zero_of_le_r M (SPA ρ hρ0 hρ1) _ hρ0 (le_refl ρ), sub_self]
      have hsub := hδ_sub ρ v hρ1 (hv.2.trans hv1_1)
      have hint0 : ∫ t in ρ..v, (alloc M m1 (effDist M θ 0) t -
          alloc M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) t) = 0 := by
        have hcongr : ∫ t in ρ..v, (alloc M m1 (effDist M θ 0) t -
            alloc M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) t) = ∫ _ in ρ..v, (0 : ℝ) := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards with t ht
          rw [uIoc_of_le hvρ.le] at ht
          have ht_le_v1 : t ≤ v₁ := ht.2.trans hv.2
          rw [alloc_off_pools M m1 _ ht.1.le (fun I hI => by
            simp only [m1, singlePoolMech, List.mem_singleton] at hI; subst hI
            intro h; linarith [h.1, hα_bds.1]),
            alloc_SPA, ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr ht.1.le)),
            hF1_01 t ht_le_v1, hFriv_sym (rivalIdx M) (rivalIdx_ne_zero M) t (ht_le_v1.trans hv1_1),
            hFriv_01 t ht_le_v1, sub_self]
        rw [hcongr]; simp
      linarith
  have hv1_0 : 0 ≤ v₁ := M.ha0.trans ha_lt_v1.le
  have hδ_v2 : δ v₂ = 0 := by
    have hsub := hδ_sub v₁ v₂ hv1_1 hv2_1
    rw [hδ_01 v₁ ⟨hv1_0, le_refl _⟩, sub_zero] at hsub
    have hint1 := alloc_intervalIntegrable M m1 _ (vs_effDist_monotoneOn θ 0) (fun _ h => effDist_nonneg θ 0 h) hv1_1 hv2_1
    have hintR := alloc_intervalIntegrable M (SPA ρ hρ0 hρ1) _ (vs_effDist_monotoneOn θ (rivalIdx M))
      (fun _ h => effDist_nonneg θ (rivalIdx M) h) hv1_1 hv2_1
    rw [intervalIntegral.integral_sub hint1 hintR] at hsub
    have hsplit : ∫ t in v₁..v₂, alloc M m1 (effDist M θ 0) t =
        (∫ t in v₁..α, alloc M m1 (effDist M θ 0) t) + (∫ t in α..v₂, alloc M m1 (effDist M θ 0) t) :=
      (intervalIntegral.integral_add_adjacent_intervals
        (alloc_intervalIntegrable M m1 _ (vs_effDist_monotoneOn θ 0) (fun _ h => effDist_nonneg θ 0 h) hv1_1 (hα_bds.2.le.trans hv2_1))
        (alloc_intervalIntegrable M m1 _ (vs_effDist_monotoneOn θ 0) (fun _ h => effDist_nonneg θ 0 h) (hα_bds.2.le.trans hv2_1) hv2_1)).symm
    have hL : ∫ t in v₁..α, alloc M m1 (effDist M θ 0) t = (α - v₁) * (M.A v₁) ^ (M.n - 1) := by
      have hc : ∫ t in v₁..α, alloc M m1 (effDist M θ 0) t = ∫ _ in v₁..α, (M.A v₁) ^ (M.n - 1) := by
        apply intervalIntegral.integral_congr_ae
        have hne : ∀ᵐ t ∂volume, t ≠ α := by simp [ae_iff, measure_singleton]
        filter_upwards [hne] with t htα ht
        rw [uIoc_of_le hα_bds.1.le] at ht
        rw [alloc_off_pools M m1 _ (hρ_lt_v1.le.trans ht.1.le) (fun I hI => by
          simp only [m1, singlePoolMech, List.mem_singleton] at hI; subst hI
          intro h; linarith [h.1, lt_of_le_of_ne ht.2 htα]),
          hF1_12 t ⟨ht.1.le, ht.2.trans hα_bds.2.le⟩]
      rw [hc, intervalIntegral.integral_const, smul_eq_mul]
    have hR : ∫ t in α..v₂, alloc M m1 (effDist M θ 0) t = (v₂ - α) * (1 - qStar) ^ (M.n - 1) := by
      have hc : ∫ t in α..v₂, alloc M m1 (effDist M θ 0) t = ∫ _ in α..v₂, (1 - qStar) ^ (M.n - 1) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards with t ht
        rw [uIoc_of_le hα_bds.2.le] at ht
        rw [alloc_in_pool M m1 _ hI0 ⟨ht.1, ht.2.trans_lt (hv23.trans hβ_bds.1)⟩]
        dsimp only [I0]; rw [hF1_α, hF1_β, ← hqStar_pow.1]
      rw [hc, intervalIntegral.integral_const, smul_eq_mul]
    have hRiv : ∫ t in v₁..v₂, alloc M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) t =
        ∫ v in v₁..v₂, (g1 v) ^ (M.n - 1) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with t ht
      rw [uIoc_of_le hv12.le] at ht
      rw [alloc_SPA, ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr (hρ_lt_v1.le.trans ht.1.le))),
        hFriv_sym (rivalIdx M) (rivalIdx_ne_zero M) t (ht.2.trans hv2_1), hFriv_12 t ⟨ht.1.le, ht.2⟩]
    have hα_mul : α * ((1 - qStar) ^ (M.n - 1) - (M.A v₁) ^ (M.n - 1)) =
        v₂ * (1 - qStar) ^ (M.n - 1) - v₁ * (M.A v₁) ^ (M.n - 1) - ∫ v in v₁..v₂, (g1 v) ^ (M.n - 1) :=
      div_mul_cancel₀ _ hα_out.1.ne'
    linarith
  have hδ_23 : ∀ v ∈ Icc v₂ v₃, δ v = 0 := fun v hv => by
    have hsub := hδ_sub v₂ v hv2_1 (hv.2.trans hv3_1)
    have h0 : ∫ t in v₂..v, (alloc M m1 (effDist M θ 0) t -
        alloc M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) t) = 0 := by
      have hc : ∫ t in v₂..v, (alloc M m1 (effDist M θ 0) t -
          alloc M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) t) = ∫ _ in v₂..v, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards with t ht
        rw [uIoc_of_le hv.1] at ht
        rw [alloc_in_pool M m1 _ hI0 ⟨hα_bds.2.trans ht.1, (ht.2.trans hv.2).trans_lt hβ_bds.1⟩]
        dsimp only [I0]
        rw [hF1_α, hF1_β, ← hqStar_pow.1,
          alloc_SPA, ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr ((hρ_lt_v1.le.trans hv12.le).trans ht.1.le))),
          hFriv_sym (rivalIdx M) (rivalIdx_ne_zero M) t ((ht.2.trans hv.2).trans hv3_1),
          hFriv_23 t ⟨ht.1.le, ht.2.trans hv.2⟩, sub_self]
      rw [hc]; simp
    linarith
  have hδ_v4 : δ v₄ = 0 := by
    have hsub := hδ_sub v₃ v₄ hv3_1 hv4_lt1.le
    rw [hδ_23 v₃ (right_mem_Icc.mpr hv23.le), sub_zero] at hsub
    have hint1 := alloc_intervalIntegrable M m1 _ (vs_effDist_monotoneOn θ 0) (fun _ h => effDist_nonneg θ 0 h) hv3_1 hv4_lt1.le
    have hintR := alloc_intervalIntegrable M (SPA ρ hρ0 hρ1) _ (vs_effDist_monotoneOn θ (rivalIdx M))
      (fun _ h => effDist_nonneg θ (rivalIdx M) h) hv3_1 hv4_lt1.le
    rw [intervalIntegral.integral_sub hint1 hintR] at hsub
    have hsplit : ∫ t in v₃..v₄, alloc M m1 (effDist M θ 0) t =
        (∫ t in v₃..β, alloc M m1 (effDist M θ 0) t) + (∫ t in β..v₄, alloc M m1 (effDist M θ 0) t) :=
      (intervalIntegral.integral_add_adjacent_intervals
        (alloc_intervalIntegrable M m1 _ (vs_effDist_monotoneOn θ 0) (fun _ h => effDist_nonneg θ 0 h) hv3_1 hβ1)
        (alloc_intervalIntegrable M m1 _ (vs_effDist_monotoneOn θ 0) (fun _ h => effDist_nonneg θ 0 h) hβ1 hv4_lt1.le)).symm
    have hL : ∫ t in v₃..β, alloc M m1 (effDist M θ 0) t = (β - v₃) * (1 - qStar) ^ (M.n - 1) := by
      have hc : ∫ t in v₃..β, alloc M m1 (effDist M θ 0) t = ∫ _ in v₃..β, (1 - qStar) ^ (M.n - 1) := by
        apply intervalIntegral.integral_congr_ae
        have hne : ∀ᵐ t ∂volume, t ≠ β := by simp [ae_iff, measure_singleton]
        filter_upwards [hne] with t htβ ht
        rw [uIoc_of_le hβ_bds.1.le] at ht
        rw [alloc_in_pool M m1 _ hI0 ⟨(hα_bds.2.trans hv23).trans ht.1, lt_of_le_of_ne ht.2 htβ⟩]
        dsimp only [I0]; rw [hF1_α, hF1_β, ← hqStar_pow.1]
      rw [hc, intervalIntegral.integral_const, smul_eq_mul]
    have hR : ∫ t in β..v₄, alloc M m1 (effDist M θ 0) t = (v₄ - β) * (M.A v₄) ^ (M.n - 1) := by
      have hc : ∫ t in β..v₄, alloc M m1 (effDist M θ 0) t = ∫ _ in β..v₄, (M.A v₄) ^ (M.n - 1) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards with t ht
        rw [uIoc_of_le hβ_bds.2.le] at ht
        rw [alloc_off_pools M m1 _ (hρα.trans (hαβ.le.trans ht.1.le)) (fun I hI => by
          simp only [m1, singlePoolMech, List.mem_singleton] at hI; subst hI
          intro h; linarith [h.2, ht.1]),
          hF1_34 t ⟨hβ_bds.1.le.trans ht.1.le, ht.2⟩]
      rw [hc, intervalIntegral.integral_const, smul_eq_mul]
    have hRiv : ∫ t in v₃..v₄, alloc M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) t =
        ∫ v in v₃..v₄, (g2 v) ^ (M.n - 1) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with t ht
      rw [uIoc_of_le hv34.le] at ht
      rw [alloc_SPA, ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr ((hρ_lt_v1.le.trans (hv12.le.trans hv23.le)).trans ht.1.le))),
        hFriv_sym (rivalIdx M) (rivalIdx_ne_zero M) t (ht.2.trans hv4_lt1.le), hFriv_34 t ⟨ht.1.le, ht.2⟩]
    have hβ_mul : β * ((M.A v₄) ^ (M.n - 1) - (1 - qStar) ^ (M.n - 1)) =
        v₄ * (M.A v₄) ^ (M.n - 1) - v₃ * (1 - qStar) ^ (M.n - 1) - ∫ v in v₃..v₄, (g2 v) ^ (M.n - 1) :=
      div_mul_cancel₀ _ hβ_out.1.ne'
    linarith
  have hδ_41 : ∀ v ∈ Icc v₄ 1, δ v = 0 := fun v hv => by
    have hsub := hδ_sub v₄ v hv4_lt1.le hv.2
    have h0 : ∫ t in v₄..v, (alloc M m1 (effDist M θ 0) t -
        alloc M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) t) = 0 := by
      have hc : ∫ t in v₄..v, (alloc M m1 (effDist M θ 0) t -
          alloc M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) t) = ∫ _ in v₄..v, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards with t ht
        rw [uIoc_of_le hv.1] at ht
        rw [alloc_off_pools M m1 _ ((hρ_lt_v1.le.trans hv14.le).trans ht.1.le) (fun I hI => by
          simp only [m1, singlePoolMech, List.mem_singleton] at hI; subst hI
          intro h; linarith [h.2, hβ_bds.2, ht.1]),
          alloc_SPA, ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr ((hρ_lt_v1.le.trans hv14.le).trans ht.1.le))),
          hF1_41 t ⟨ht.1.le, ht.2.trans hv.2⟩,
          hFriv_sym (rivalIdx M) (rivalIdx_ne_zero M) t (ht.2.trans hv.2),
          hFriv_41 t ⟨ht.1.le, ht.2.trans hv.2⟩, sub_self]
      rw [hc]; simp
    linarith
  have hg1_cont : ContinuousOn g1 (Icc v₁ v₂) :=
    continuousOn_const.add (((M.F_continuousOn.mono (Icc_subset_Icc ha_lt_v1.le hv2_1)).sub continuousOn_const).div_const _)
  have hg2_cont : ContinuousOn g2 (Icc v₃ v₄) :=
    continuousOn_const.add (((M.F_continuousOn.mono (Icc_subset_Icc (ha_lt_v1.le.trans (hv12.le.trans hv23.le)) hv4_lt1.le)).sub continuousOn_const).div_const _)
  have hg1_mono : MonotoneOn g1 (Icc v₁ v₂) := fun x hx y hy hxy => by
    dsimp only [g1]
    have hF := M.F_strictMonoOn.monotoneOn ⟨ha_lt_v1.le.trans hx.1, hx.2.trans hv2_1⟩
      ⟨ha_lt_v1.le.trans hy.1, hy.2.trans hv2_1⟩ hxy
    linarith [div_le_div_of_nonneg_right (sub_le_sub_right hF (M.F v₁)) M.m_sub_one_pos_real.le]
  have hg2_mono : MonotoneOn g2 (Icc v₃ v₄) := fun x hx y hy hxy => by
    dsimp only [g2]
    have hF := M.F_strictMonoOn.monotoneOn ⟨(ha_lt_v1.le.trans (hv12.le.trans hv23.le)).trans hx.1, hx.2.trans hv4_lt1.le⟩
      ⟨(ha_lt_v1.le.trans (hv12.le.trans hv23.le)).trans hy.1, hy.2.trans hv4_lt1.le⟩ hxy
    linarith [div_le_div_of_nonneg_right (sub_le_sub_right hF (M.F v₃)) M.m_sub_one_pos_real.le]
  have hδ_np : ∀ v ∈ Icc (0 : ℝ) 1, δ v ≤ 0 := fun v hv => by
    by_cases h1 : v ≤ v₁
    · rw [hδ_01 v ⟨hv.1, h1⟩]
    · push Not at h1
      by_cases h2 : v ≤ α
      · have hsub := hδ_sub v₁ v hv1_1 hv.2
        rw [hδ_01 v₁ ⟨hv1_0, le_refl _⟩, sub_zero] at hsub
        have hc : ∫ t in v₁..v, (alloc M m1 (effDist M θ 0) t -
            alloc M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) t) =
            ∫ t in v₁..v, ((M.A v₁) ^ (M.n - 1) - (g1 t) ^ (M.n - 1)) := by
          apply intervalIntegral.integral_congr_ae
          have hne : ∀ᵐ t ∂volume, t ≠ α := by simp [ae_iff, measure_singleton]
          filter_upwards [hne] with t htα ht
          rw [uIoc_of_le h1.le] at ht
          have ht_lt_α : t < α := lt_of_le_of_ne (ht.2.trans h2) htα
          rw [alloc_off_pools M m1 _ (hρ_lt_v1.le.trans ht.1.le) (fun I hI => by
            simp only [m1, singlePoolMech, List.mem_singleton] at hI; subst hI
            intro h; linarith [h.1]),
            hF1_12 t ⟨ht.1.le, ht_lt_α.le.trans hα_bds.2.le⟩,
            alloc_SPA, ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr (hρ_lt_v1.le.trans ht.1.le))),
            hFriv_sym (rivalIdx M) (rivalIdx_ne_zero M) t (ht.2.trans hv.2),
            hFriv_12 t ⟨ht.1.le, ht_lt_α.le.trans hα_bds.2.le⟩]
        have hcont : ContinuousOn (fun t => (M.A v₁) ^ (M.n - 1) - (g1 t) ^ (M.n - 1)) (Icc v₁ v) :=
          continuousOn_const.sub ((hg1_cont.mono (Icc_subset_Icc (le_refl _) (h2.trans hα_bds.2.le))).pow (M.n - 1))
        have h0 : ∫ t in v₁..v, ((M.A v₁) ^ (M.n - 1) - (g1 t) ^ (M.n - 1)) ≤ ∫ _ in v₁..v, (0 : ℝ) := by
          apply intervalIntegral.integral_mono_on h1.le (hcont.intervalIntegrable_of_Icc h1.le) intervalIntegrable_const
          intro t ht
          have hgle := hg1_mono (left_mem_Icc.mpr hv12.le) ⟨ht.1, ht.2.trans (h2.trans hα_bds.2.le)⟩ ht.1
          rw [hg1_v1] at hgle; linarith [pow_le_pow_left₀ (M.A_mem_Icc hv1_1).1 hgle (M.n - 1)]
        simp only [intervalIntegral.integral_zero] at h0; linarith
      · push Not at h2
        by_cases h3 : v ≤ v₂
        · have hsub := hδ_sub v v₂ hv.2 hv2_1
          rw [hδ_v2, zero_sub] at hsub
          have hc : ∫ t in v..v₂, (alloc M m1 (effDist M θ 0) t -
              alloc M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) t) =
              ∫ t in v..v₂, ((1 - qStar) ^ (M.n - 1) - (g1 t) ^ (M.n - 1)) := by
            apply intervalIntegral.integral_congr_ae
            filter_upwards with t ht
            rw [uIoc_of_le h3] at ht
            rw [alloc_in_pool M m1 _ hI0 ⟨h2.trans ht.1, ht.2.trans_lt (hv23.trans hβ_bds.1)⟩]
            dsimp only [I0]
            rw [hF1_α, hF1_β, ← hqStar_pow.1,
              alloc_SPA, ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr ((hρ_lt_v1.le.trans h1.le).trans ht.1.le))),
              hFriv_sym (rivalIdx M) (rivalIdx_ne_zero M) t (ht.2.trans hv2_1),
              hFriv_12 t ⟨h1.le.trans ht.1.le, ht.2⟩]
          have hcont : ContinuousOn (fun t => (1 - qStar) ^ (M.n - 1) - (g1 t) ^ (M.n - 1)) (Icc v v₂) :=
            continuousOn_const.sub ((hg1_cont.mono (Icc_subset_Icc h1.le (le_refl _))).pow (M.n - 1))
          have h0 : ∫ _ in v..v₂, (0 : ℝ) ≤ ∫ t in v..v₂, ((1 - qStar) ^ (M.n - 1) - (g1 t) ^ (M.n - 1)) := by
            apply intervalIntegral.integral_mono_on h3 intervalIntegrable_const (hcont.intervalIntegrable_of_Icc h3)
            intro t ht
            have hgle := hg1_mono ⟨h1.le.trans ht.1, ht.2⟩ (right_mem_Icc.mpr hv12.le) ht.2
            rw [hg1_v2] at hgle
            have hnn : 0 ≤ g1 t := by
              have := hg1_mono (left_mem_Icc.mpr hv12.le) ⟨h1.le.trans ht.1, ht.2⟩ (h1.le.trans ht.1)
              rw [hg1_v1] at this; exact (M.A_mem_Icc hv1_1).1.trans this
            linarith [pow_le_pow_left₀ hnn hgle (M.n - 1)]
          simp only [intervalIntegral.integral_zero] at h0; linarith
        · push Not at h3
          by_cases h4 : v ≤ v₃
          · rw [hδ_23 v ⟨h3.le, h4⟩]
          · push Not at h4
            by_cases h5 : v ≤ β
            · have hsub := hδ_sub v₃ v hv3_1 hv.2
              rw [hδ_23 v₃ (right_mem_Icc.mpr hv23.le), sub_zero] at hsub
              have hc : ∫ t in v₃..v, (alloc M m1 (effDist M θ 0) t -
                  alloc M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) t) =
                  ∫ t in v₃..v, ((1 - qStar) ^ (M.n - 1) - (g2 t) ^ (M.n - 1)) := by
                apply intervalIntegral.integral_congr_ae
                have hne : ∀ᵐ t ∂volume, t ≠ β := by simp [ae_iff, measure_singleton]
                filter_upwards [hne] with t htβ ht
                rw [uIoc_of_le h4.le] at ht
                rw [alloc_in_pool M m1 _ hI0 ⟨(hα_bds.2.trans hv23).trans ht.1, lt_of_le_of_ne (ht.2.trans h5) htβ⟩]
                dsimp only [I0]
                rw [hF1_α, hF1_β, ← hqStar_pow.1,
                  alloc_SPA, ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr ((hρ_lt_v1.le.trans (hv12.le.trans hv23.le)).trans ht.1.le))),
                  hFriv_sym (rivalIdx M) (rivalIdx_ne_zero M) t (ht.2.trans hv.2),
                  hFriv_34 t ⟨ht.1.le, (ht.2.trans h5).trans hβ_bds.2.le⟩]
              have hcont : ContinuousOn (fun t => (1 - qStar) ^ (M.n - 1) - (g2 t) ^ (M.n - 1)) (Icc v₃ v) :=
                continuousOn_const.sub ((hg2_cont.mono (Icc_subset_Icc (le_refl _) (h5.trans hβ_bds.2.le))).pow (M.n - 1))
              have h0 : ∫ t in v₃..v, ((1 - qStar) ^ (M.n - 1) - (g2 t) ^ (M.n - 1)) ≤ ∫ _ in v₃..v, (0 : ℝ) := by
                apply intervalIntegral.integral_mono_on h4.le (hcont.intervalIntegrable_of_Icc h4.le) intervalIntegrable_const
                intro t ht
                have hgle := hg2_mono (left_mem_Icc.mpr hv34.le) ⟨ht.1, ht.2.trans (h5.trans hβ_bds.2.le)⟩ ht.1
                rw [hg2_v3] at hgle; linarith [pow_le_pow_left₀ hr_nn hgle (M.n - 1)]
              simp only [intervalIntegral.integral_zero] at h0; linarith
            · push Not at h5
              by_cases h6 : v ≤ v₄
              · have hsub := hδ_sub v v₄ hv.2 hv4_lt1.le
                rw [hδ_v4, zero_sub] at hsub
                have hc : ∫ t in v..v₄, (alloc M m1 (effDist M θ 0) t -
                    alloc M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) t) =
                    ∫ t in v..v₄, ((M.A v₄) ^ (M.n - 1) - (g2 t) ^ (M.n - 1)) := by
                  apply intervalIntegral.integral_congr_ae
                  filter_upwards with t ht
                  rw [uIoc_of_le h6] at ht
                  rw [alloc_off_pools M m1 _ (hρα.trans (hαβ.le.trans (h5.le.trans ht.1.le))) (fun I hI => by
                    simp only [m1, singlePoolMech, List.mem_singleton] at hI; subst hI
                    intro h; linarith [h.2, h5, ht.1]),
                    hF1_34 t ⟨h4.le.trans ht.1.le, ht.2⟩,
                    alloc_SPA, ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr (hρα.trans (hαβ.le.trans (h5.le.trans ht.1.le))))),
                    hFriv_sym (rivalIdx M) (rivalIdx_ne_zero M) t (ht.2.trans hv4_lt1.le),
                    hFriv_34 t ⟨h4.le.trans ht.1.le, ht.2⟩]
                have hcont : ContinuousOn (fun t => (M.A v₄) ^ (M.n - 1) - (g2 t) ^ (M.n - 1)) (Icc v v₄) :=
                  continuousOn_const.sub ((hg2_cont.mono (Icc_subset_Icc h4.le (le_refl _))).pow (M.n - 1))
                have h0 : ∫ _ in v..v₄, (0 : ℝ) ≤ ∫ t in v..v₄, ((M.A v₄) ^ (M.n - 1) - (g2 t) ^ (M.n - 1)) := by
                  apply intervalIntegral.integral_mono_on h6 intervalIntegrable_const (hcont.intervalIntegrable_of_Icc h6)
                  intro t ht
                  have hgle := hg2_mono ⟨h4.le.trans ht.1, ht.2⟩ (right_mem_Icc.mpr hv34.le) ht.2
                  rw [hg2_v4] at hgle
                  have hnn : 0 ≤ g2 t := by
                    have := hg2_mono (left_mem_Icc.mpr hv34.le) ⟨h4.le.trans ht.1, ht.2⟩ (h4.le.trans ht.1)
                    rw [hg2_v3] at this; exact hr_nn.trans this
                  linarith [pow_le_pow_left₀ hnn hgle (M.n - 1)]
                simp only [intervalIntegral.integral_zero] at h0; linarith
              · push Not at h6; rw [hδ_41 v ⟨h6.le, hv.2⟩]
  refine ⟨hρα, hαβ, hβ1, θ, hα_bds.1, hβ_bds.2, ?_, ?_⟩
  -- Verify IsSR pointwise everywhere on Icc M.a 1
  · unfold IsSR
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards with v hv j k hjpos
    have hv01 : v ∈ Icc (0 : ℝ) 1 := ⟨M.ha0.trans hv.1, hv.2⟩
    have hriv_eq : ∀ i : Fin M.m, i ≠ 0 →
        surplus M (unilateralProfile M m1 ρ hρ0 hρ1 i) (effDist M θ i) v =
          surplus M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) v := fun i hi => by
      simp only [unilateralProfile, ite_eq_right_iff.mpr (fun h => absurd h hi)]
      unfold surplus
      apply intervalIntegral.integral_congr
      intro u hu; rw [uIcc_of_le hv01.1] at hu
      rw [alloc_SPA, alloc_SPA,
        hFriv_sym i hi u (hu.2.trans hv.2), hFriv_sym (rivalIdx M) (rivalIdx_ne_zero M) u (hu.2.trans hv.2)]
    by_cases hj0 : j = 0
    · subst hj0
      have hδv0 : δ v = 0 := by
        by_cases h23 : v ∈ Ioo v₂ v₃
        · exact hδ_23 v (Ioo_subset_Icc_self h23)
        · by_cases h14 : v ∈ Ioo v₁ v₄
          · exfalso; dsimp only [θ, bandVisit] at hjpos
            simp only [ite_true, h23, h14, ite_false, lt_self_iff_false] at hjpos
          · by_cases hle : v ≤ v₁
            · exact hδ_01 v ⟨hv01.1, hle⟩
            · push Not at hle
              have hv4_le : v₄ ≤ v := by by_contra hlt; push Not at hlt; exact h14 ⟨hle, hlt⟩
              exact hδ_41 v ⟨hv4_le, hv.2⟩
      by_cases hk0 : k = 0
      · subst hk0; exact le_refl _
      · rw [hriv_eq k hk0]; simp only [unilateralProfile, ite_true]; dsimp only [δ] at hδv0; linarith
    · rw [hriv_eq j hj0]
      by_cases hk0 : k = 0
      · subst hk0; simp only [unilateralProfile, ite_true]
        have := hδ_np v hv01; dsimp only [δ] at this; linarith
      · rw [hriv_eq k hk0]
  -- Verify IsInteriorBand M ρ α β θ v₁ v₄
  · refine ⟨hu0_lt, hv14, hv4_lt1, hα_bds.1.le, hβ_bds.2.le, ?_, ?_, ?_⟩
    · rintro v (hv | hv)
      · exact hF1_01 v hv.2
      · exact hF1_41 v hv
    · intro ε hε
      let u := (v₁ + min (min (v₁ + ε) v₄) v₂) / 2
      have hmin_gt : v₁ < min (min (v₁ + ε) v₄) v₂ := lt_min (lt_min (by linarith : v₁ < v₁ + ε) hv14) hv12
      have hu_gt : v₁ < u := by dsimp only [u]; linarith
      have hu_lt_min : u < min (v₁ + ε) v₄ := by dsimp only [u]; linarith [min_le_left (min (v₁ + ε) v₄) v₂]
      have hu_lt_v2 : u < v₂ := by dsimp only [u]; linarith [min_le_right (min (v₁ + ε) v₄) v₂]
      refine ⟨u, ⟨hu_gt, hu_lt_min⟩, ?_⟩
      rw [hF1_12 u ⟨hu_gt.le, hu_lt_v2.le⟩]
      have hFlt := M.F_strictMonoOn ⟨ha_lt_v1.le, hv1_1⟩ ⟨ha_lt_v1.le.trans hu_gt.le, hu_lt_v2.le.trans hv2_1⟩ hu_gt
      unfold Market.A; linarith [div_lt_div_of_pos_right (sub_lt_sub_left hFlt 1) M.m_pos_real]
    · intro ε hε
      let u := (max (max v₁ (v₄ - ε)) v₃ + v₄) / 2
      have hmax_lt : max (max v₁ (v₄ - ε)) v₃ < v₄ := max_lt (max_lt hv14 (by linarith : v₄ - ε < v₄)) hv34
      have hu_lt : u < v₄ := by dsimp only [u]; linarith
      have hu_gt_max : max v₁ (v₄ - ε) < u := by dsimp only [u]; linarith [le_max_left (max v₁ (v₄ - ε)) v₃]
      have hu_gt_v3 : v₃ < u := by dsimp only [u]; linarith [le_max_right (max v₁ (v₄ - ε)) v₃]
      refine ⟨u, ⟨hu_gt_max, hu_lt⟩, ?_⟩
      rw [hF1_34 u ⟨hu_gt_v3.le, hu_lt.le⟩]
      have hFlt := M.F_strictMonoOn ⟨(ha_lt_v1.le.trans (hv12.le.trans hv23.le)).trans hu_gt_v3.le, hu_lt.le.trans hv4_lt1.le⟩
        ⟨(ha_lt_v1.trans hv14).le, hv4_lt1.le⟩ hu_lt
      unfold Market.A; linarith [div_lt_div_of_pos_right (sub_lt_sub_left hFlt 1) M.m_pos_real]

/-- Set of interior bands `{(v₁, v₄) | max ρ a < v₁ < v₄ < 1}`. -/
def InteriorBands (ρ : ℝ) : Set (ℝ × ℝ) :=
  {p | max ρ M.a < p.1 ∧ p.1 < p.2 ∧ p.2 < 1}

/-- Set of pools `(α, β)` whose unique SR continuation under `singlePoolMech ρ α β` induces
some interior band. -/
def InteriorPools (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) : Set (ℝ × ℝ) :=
  {p | ∃ (hρα : ρ ≤ p.1) (hαβ : p.1 < p.2) (hβ1 : p.2 ≤ 1) (θ : VisitStrategy M) (v₁ v₄ : ℝ),
    IsSR M (unilateralProfile M (singlePoolMech ρ p.1 p.2 hρ0 hρα hαβ hβ1) ρ hρ0 hρ1) θ ∧
    IsInteriorBand M ρ p.1 p.2 θ v₁ v₄}

/-- **Lemma 1(iii) (Pool–Band Bijection)**: The map `bandToPool` is a bijection between
interior bands `{(v₁, v₄) | max ρ a < v₁ < v₄ < 1}` and pools `(α, β)` inducing an interior band. -/
theorem lemma1_pool_band_bijection {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    Set.BijOn (bandToPool M) (InteriorBands M ρ) (InteriorPools M ρ hρ0 hρ1) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨v₁, v₄⟩ ⟨hu0, hv14, hv4⟩
    obtain ⟨hρα, hαβ, hβ1, θ, _, _, hSR, hband⟩ := lemma1_band_to_pool_sr M hρ0 hu0 hv14 hv4
    exact ⟨hρα, hαβ, hβ1, θ, v₁, v₄, hSR, hband⟩
  · rintro ⟨v₁, v₄⟩ ⟨hu0, hv14, hv4⟩ ⟨v₁', v₄'⟩ ⟨hu0', hv14', hv4'⟩ heq
    obtain ⟨hρα, hαβ, hβ1, θ, _, _, hSR, hband⟩ := lemma1_band_to_pool_sr M hρ0 hu0 hv14 hv4
    obtain ⟨hρα', hαβ', hβ1', θ', _, _, hSR', hband'⟩ := lemma1_band_to_pool_sr M hρ0 hu0' hv14' hv4'
    have hα_eq : (bandToPool M (v₁, v₄)).1 = (bandToPool M (v₁', v₄')).1 := congrArg Prod.fst heq
    have hβ_eq : (bandToPool M (v₁, v₄)).2 = (bandToPool M (v₁', v₄')).2 := congrArg Prod.snd heq
    have hmech_eq : singlePoolMech ρ (bandToPool M (v₁, v₄)).1 (bandToPool M (v₁, v₄)).2 hρ0 hρα hαβ hβ1 =
        singlePoolMech ρ (bandToPool M (v₁', v₄')).1 (bandToPool M (v₁', v₄')).2 hρ0 hρα' hαβ' hβ1' := by
      unfold singlePoolMech; simp [hα_eq, hβ_eq]
    rw [← hmech_eq] at hSR'
    have hF1_eq := (prop2_uniqueness M _ ρ hρ0 hρ1 hSR hSR').1
    have hF1_eq_all : ∀ u ∈ Icc ρ 1, effDist M θ 0 u = effDist M θ' 0 u := fun u hu =>
      (hF1_eq u (by simpa [singlePoolMech] using hu)).symm
    have hv1_eq : v₁ = v₁' := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · obtain ⟨u, hu, hneA⟩ := hband.2.2.2.2.2.2.1 (v₁' - v₁) (sub_pos.mpr hlt)
        have hu_le : u ≤ v₁' := (hu.2.le.trans (min_le_left _ _)).trans (by linarith)
        have hu_ρ : ρ ≤ u := (le_max_left ρ M.a).trans (hu0.le.trans hu.1.le)
        have hu_1 : u ≤ 1 := hu.2.le.trans ((min_le_right _ _).trans hv4.le)
        rw [hF1_eq_all u ⟨hu_ρ, hu_1⟩] at hneA
        exact hneA (hband'.2.2.2.2.2.1 u (Or.inl ⟨hu0.le.trans hu.1.le, hu_le⟩))
      · obtain ⟨u, hu, hneA⟩ := hband'.2.2.2.2.2.2.1 (v₁ - v₁') (sub_pos.mpr hgt)
        have hu_le : u ≤ v₁ := (hu.2.le.trans (min_le_left _ _)).trans (by linarith)
        have hu_ρ : ρ ≤ u := (le_max_left ρ M.a).trans (hu0'.le.trans hu.1.le)
        have hu_1 : u ≤ 1 := hu.2.le.trans ((min_le_right _ _).trans hv4'.le)
        rw [← hF1_eq_all u ⟨hu_ρ, hu_1⟩] at hneA
        exact hneA (hband.2.2.2.2.2.1 u (Or.inl ⟨hu0'.le.trans hu.1.le, hu_le⟩))
    have hv4_eq : v₄ = v₄' := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · obtain ⟨u, hu, hneA⟩ := hband'.2.2.2.2.2.2.2 (v₄' - v₄) (sub_pos.mpr hlt)
        have hu_ge : v₄ ≤ u := (by linarith : v₄ ≤ v₄' - (v₄' - v₄)).trans ((le_max_right _ _).trans hu.1.le)
        have hu_ρ : ρ ≤ u := (le_max_left ρ M.a).trans (hu0.le.trans (hv14.le.trans hu_ge))
        have hu_1 : u ≤ 1 := hu.2.le.trans hv4'.le
        rw [← hF1_eq_all u ⟨hu_ρ, hu_1⟩] at hneA
        exact hneA (hband.2.2.2.2.2.1 u (Or.inr ⟨hu_ge, hu_1⟩))
      · obtain ⟨u, hu, hneA⟩ := hband.2.2.2.2.2.2.2 (v₄ - v₄') (sub_pos.mpr hgt)
        have hu_ge : v₄' ≤ u := (by linarith : v₄' ≤ v₄ - (v₄ - v₄')).trans ((le_max_right _ _).trans hu.1.le)
        have hu_ρ : ρ ≤ u := (le_max_left ρ M.a).trans (hu0'.le.trans (hv14'.le.trans hu_ge))
        have hu_1 : u ≤ 1 := hu.2.le.trans hv4.le
        rw [hF1_eq_all u ⟨hu_ρ, hu_1⟩] at hneA
        exact hneA (hband'.2.2.2.2.2.1 u (Or.inr ⟨hu_ge, hu_1⟩))
    exact Prod.ext hv1_eq hv4_eq
  · rintro ⟨α, β⟩ ⟨hρα, hαβ, hβ1, θ, v₁, v₄, hSR, hband⟩
    refine ⟨(v₁, v₄), ⟨hband.1, hband.2.1, hband.2.2.1⟩, ?_⟩
    have hstruct := lemma1_band_structure M hρ0 hρα hαβ hβ1 hSR hband
    obtain ⟨_, _, _, _, v₂, v₃, hv1α, hαv2, hv23, hv3β, hβv4, _, _, _, _, _, _, hmass12, hmass34, _, _, hα_eq, hβ_eq⟩ := hstruct
    have ha_lt_v1 : M.a < v₁ := (le_max_right ρ M.a).trans_lt hband.1
    have hcond : M.a ≤ v₁ ∧ v₁ < v₄ ∧ v₄ ≤ 1 := ⟨ha_lt_v1.le, hband.2.1, hband.2.2.1.le⟩
    let hex := band_coords_exist M hcond.1 hcond.2.1 hcond.2.2
    let v₂' := hex.choose
    let v₃' := hex.choose_spec.choose
    obtain ⟨hv12', hv23', hv34', hFv2', hFv3'⟩ := hex.choose_spec.choose_spec
    have hv2_eq : v₂' = v₂ := M.F_strictMonoOn.injOn
      ⟨ha_lt_v1.le.trans hv12'.le, ((hv23'.trans hv34').trans hband.2.2.1).le⟩
      ⟨ha_lt_v1.le.trans (hv1α.trans hαv2).le, ((hv23.trans (hv3β.trans hβv4)).trans hband.2.2.1).le⟩
      (by linarith)
    have hv3_eq : v₃' = v₃ := M.F_strictMonoOn.injOn
      ⟨ha_lt_v1.le.trans (hv12'.trans hv23').le, (hv34'.trans hband.2.2.1).le⟩
      ⟨ha_lt_v1.le.trans ((hv1α.trans hαv2).trans hv23).le, ((hv3β.trans hβv4).trans hband.2.2.1).le⟩
      (by linarith)
    have hbtp : bandToPool M (v₁, v₄) =
        ((v₂' * (1 - bandQStar M v₁ v₄) ^ (M.n - 1) - v₁ * (M.A v₁) ^ (M.n - 1) -
            ∫ v in v₁..v₂', (M.A v₁ + (M.F v - M.F v₁) / ((M.m : ℝ) - 1)) ^ (M.n - 1)) /
          ((1 - bandQStar M v₁ v₄) ^ (M.n - 1) - (M.A v₁) ^ (M.n - 1)),
         (v₄ * (M.A v₄) ^ (M.n - 1) - v₃' * (1 - bandQStar M v₁ v₄) ^ (M.n - 1) -
            ∫ v in v₃'..v₄, (1 - bandQStar M v₁ v₄ + (M.F v - M.F v₃') / ((M.m : ℝ) - 1)) ^ (M.n - 1)) /
          ((M.A v₄) ^ (M.n - 1) - (1 - bandQStar M v₁ v₄) ^ (M.n - 1))) := by
      unfold bandToPool; simp only [hcond]; rfl
    rw [hbtp]
    apply Prod.ext
    · dsimp only; rw [hv2_eq]; exact hα_eq.symm
    · dsimp only; rw [hv3_eq]; exact hβ_eq.symm

/-- **Lemma A.5(iii) (Top-Reaching Band `v₄ = 1`)**: When a single-pool band reaches the top of
the support (`v₄ = 1`), the same split holds with `q_lo = 0`, `σ(1) ≤ 0`, `v₁ < α < v₂ < v₃ < β ≤ 1`,
served mass `(1 - F(v₁)) / m`, `q*` solving eq. (5) with `q_lo = 0`, `α` given by eq. (15), and
`β ≥ β₀` (the eq. (15) right-hand value). -/
theorem lemma1_top_reaching_band {ρ α β : ℝ} (hρ0 : 0 ≤ ρ) (hρα : ρ ≤ α) (hαβ : α < β) (hβ1 : β ≤ 1)
    {θ : VisitStrategy M}
    (hSR : IsSR M (unilateralProfile M (singlePoolMech ρ α β hρ0 hρα hαβ hβ1) ρ hρ0
      (hρα.trans (hαβ.le.trans hβ1))) θ)
    {v₁ : ℝ} (hband : IsTopReachingBand M ρ α β θ v₁) :
    let q_hi := (1 - M.F v₁) / (M.m : ℝ)
    let qStar := bandQStar M v₁ 1
    sigma M (singlePoolMech ρ α β hρ0 hρα hαβ hβ1) ρ hρ0 (hρα.trans (hαβ.le.trans hβ1)) θ 1 ≤ 0 ∧
    ∃ v₂ v₃ : ℝ,
      v₁ < α ∧ α < v₂ ∧ v₂ < v₃ ∧ v₃ < β ∧ β ≤ 1 ∧
      (∀ᵐ v ∂(volume.restrict (Icc v₁ v₂)), θ.θ 0 v = 0) ∧
      (∀ᵐ v ∂(volume.restrict (Icc v₂ v₃)), θ.θ 0 v = 1) ∧
      (∀ᵐ v ∂(volume.restrict (Icc v₃ 1)), θ.θ 0 v = 0) ∧
      M.F v₃ - M.F v₂ = (1 - M.F v₁) / (M.m : ℝ) ∧
      (∀ v ∈ Icc v₂ v₃, effDist M θ (rivalIdx M) v = 1 - qStar) ∧
      (1 - qStar) ^ (M.n - 1) = (1 - (1 - q_hi) ^ M.n) / ((M.n : ℝ) * q_hi) ∧
      M.F v₂ - M.F v₁ = ((M.m : ℝ) - 1) * (q_hi - qStar) ∧
      1 - M.F v₃ = ((M.m : ℝ) - 1) * qStar ∧
      α = (∫ v in v₁..v₂, v * (((M.n : ℝ) - 1) * (effDist M θ (rivalIdx M) v) ^ (M.n - 2) *
              (M.f v / ((M.m : ℝ) - 1)))) /
            (∫ v in v₁..v₂, ((M.n : ℝ) - 1) * (effDist M θ (rivalIdx M) v) ^ (M.n - 2) *
              (M.f v / ((M.m : ℝ) - 1))) ∧
      (∫ v in v₃..1, v * (((M.n : ℝ) - 1) * (effDist M θ (rivalIdx M) v) ^ (M.n - 2) *
            (M.f v / ((M.m : ℝ) - 1)))) /
          (∫ v in v₃..1, ((M.n : ℝ) - 1) * (effDist M θ (rivalIdx M) v) ^ (M.n - 2) *
            (M.f v / ((M.m : ℝ) - 1))) ≤ β := by
  intro q_hi qStar
  have hρ1 : ρ ≤ 1 := hρα.trans (hαβ.le.trans hβ1)
  let m1 := singlePoolMech ρ α β hρ0 hρα hαβ hβ1
  let I0 : Pool := ⟨α, β, hαβ⟩
  have hI0 : I0 ∈ m1.pools := by simp [m1, singlePoolMech, I0]
  let σ := sigma M m1 ρ hρ0 hρ1 θ
  obtain ⟨hu0_lt_v1, hv1_lt1, hv1α, hβ1', hunif, htight1, htight4⟩ := hband
  have hρ_lt_v1 : ρ < v₁ := (le_max_left ρ M.a).trans_lt hu0_lt_v1
  have ha_lt_v1 : M.a < v₁ := (le_max_right ρ M.a).trans_lt hu0_lt_v1
  have hv1_0 : 0 ≤ v₁ := M.ha0.trans ha_lt_v1.le
  have hleft := singlePool_left_neg M hρ0 hρα hαβ hβ1 hSR hu0_lt_v1 hv1α hβ1 (le_refl 1) hunif htight1 (Or.inl rfl)
  have hσ_np : ∀ v ∈ Icc ρ 1, σ v ≤ 0 := hleft.1
  have hσ_v1 : σ v₁ = 0 := hleft.2.1
  have hneg_left : v₁ < α → ∀ t ∈ Ioc v₁ α, σ t < 0 := hleft.2.2
  have hσ_cont : ContinuousOn σ (Icc 0 1) := sigma_continuousOn M m1 ρ hρ0 hρ1 hSR
  refine ⟨hσ_np 1 ⟨hρ1, le_refl 1⟩, ?_⟩
  have hF1_v1 : effDist M θ 0 v₁ = M.A v₁ := hunif v₁ ⟨hu0_lt_v1.le, le_refl v₁⟩
  -- Step 2: σ < 0 on [β, 1) (whenever β < 1)
  have hno_neg_to_one_above_β : ∀ y₁ : ℝ, β ≤ y₁ → y₁ < 1 → σ y₁ = 0 →
      (∀ z ∈ Ioo y₁ 1, σ z < 0) → False := by
    intro y₁ hy1_β hy1_1 hσy1 hneg_all
    have hF1_const := (prop2_sigma_neg_on_Ioo M m1 ρ hρ0 hρ1 hSR hy1_1.le (le_refl 1) hneg_all).2
    have hF1_eq1 : ∀ z ∈ Icc y₁ 1, effDist M θ 0 z = 1 := fun z hz => by
      rw [hF1_const z hz 1 (right_mem_Icc.mpr hy1_1.le), vs_effDist_one]
    have hsub := sigma_sub M m1 ρ hρ0 hρ1 hSR (hρ0.trans (hρα.trans (hαβ.le.trans hy1_β))) hy1_1.le zero_le_one (le_refl 1)
    have hy1_0 : sigma M m1 ρ hρ0 hρ1 θ y₁ = 0 := hσy1
    rw [hy1_0, sub_zero] at hsub
    have hcont : ContinuousOn (fun z => 1 - (effDist M θ (rivalIdx M) z) ^ (M.n - 1)) (Icc y₁ 1) :=
      continuousOn_const.sub (((effDist_continuousOn θ (rivalIdx M)).mono (fun z (hz : z ∈ Icc y₁ 1) => hz.2)).pow (M.n - 1))
    have hpos_int : 0 < ∫ z in y₁..1, (1 - (effDist M θ (rivalIdx M) z) ^ (M.n - 1)) := by
      apply intervalIntegral.integral_pos hy1_1 hcont
      · intro z hz
        linarith [pow_le_one₀ (effDist_nonneg θ (rivalIdx M) hz.2) (effDist_le_one θ (rivalIdx M) hz.2) (n := M.n - 1)]
      · refine ⟨y₁, left_mem_Icc.mpr hy1_1.le, ?_⟩
        rw [(prop2_rival_symmetry M m1 ρ hρ0 hρ1 hSR).2 (rivalIdx M) (rivalIdx_ne_zero M) y₁
          ⟨hρα.trans (hαβ.le.trans hy1_β), hy1_1.le⟩]
        unfold FrivOf; rw [hF1_eq1 y₁ (left_mem_Icc.mpr hy1_1.le)]
        have hFlt1 : M.F y₁ < 1 := by
          rw [← M.hF_1]
          exact M.F_strictMonoOn ⟨ha_lt_v1.le.trans (hv1α.trans (hαβ.le.trans hy1_β)), hy1_1.le⟩
            (right_mem_Icc.mpr M.ha1.le) hy1_1
        have hFriv_lt1 : 1 - (1 - M.F y₁) / ((M.m : ℝ) - 1) < 1 := by
          linarith [div_pos (sub_pos.mpr hFlt1) M.m_sub_one_pos_real]
        have hFriv_nn : 0 ≤ 1 - (1 - M.F y₁) / ((M.m : ℝ) - 1) := by
          have := effDist_nonneg θ (rivalIdx M) hy1_1.le
          rw [(prop2_rival_symmetry M m1 ρ hρ0 hρ1 hSR).2 (rivalIdx M) (rivalIdx_ne_zero M) y₁
            ⟨hρα.trans (hαβ.le.trans hy1_β), hy1_1.le⟩] at this
          unfold FrivOf at this; rwa [hF1_eq1 y₁ (left_mem_Icc.mpr hy1_1.le)] at this
        have hn1 : M.n - 1 ≠ 0 := by have := M.hn; omega
        have hpow_lt1 : (1 - (1 - M.F y₁) / ((M.m : ℝ) - 1)) ^ (M.n - 1) < 1 := by
          simpa only [one_pow] using pow_lt_pow_left₀ hFriv_lt1 hFriv_nn hn1
        linarith
    have hcongr : ∫ z in y₁..1, (alloc M m1 (effDist M θ 0) z -
        alloc M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) z) =
        ∫ z in y₁..1, (1 - (effDist M θ (rivalIdx M) z) ^ (M.n - 1)) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with z hz
      rw [uIoc_of_le hy1_1.le] at hz
      rw [alloc_off_pools M m1 _ (hρα.trans (hαβ.le.trans (hy1_β.trans hz.1.le))) (fun I hI => by
        simp only [m1, singlePoolMech, List.mem_singleton] at hI; subst hI
        intro h; linarith [h.2, hy1_β, hz.1]),
        hF1_eq1 z ⟨hz.1.le, hz.2⟩, one_pow,
        alloc_SPA, ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr (hρα.trans (hαβ.le.trans (hy1_β.trans hz.1.le)))))]
    have hσ1_pos : 0 < σ 1 := by dsimp only [σ]; linarith
    linarith [hσ_np 1 ⟨hρ1, le_refl 1⟩]
  have hneg_above_β : ∀ t ∈ Ico β 1, σ t < 0 := by
    intro t ht
    refine lt_of_le_of_ne (hσ_np t ⟨hρα.trans (hαβ.le.trans ht.1), ht.2.le⟩) ?_
    intro hσt0
    have hzero_oo : ∀ u ∈ Ioo t 1, σ u = 0 := fun u hu => by
      refine le_antisymm (hσ_np u ⟨hρα.trans (hαβ.le.trans (ht.1.trans hu.1.le)), hu.2.le⟩) ?_
      by_contra hneg; push Not at hneg
      let SL := {z ∈ Icc t u | σ z = 0}
      let SR := {1} ∪ {z ∈ Icc u 1 | σ z = 0}
      have hSL_ne : SL.Nonempty := ⟨t, ⟨le_refl _, hu.1.le⟩, hσt0⟩
      have hSR_ne : SR.Nonempty := ⟨1, Or.inl rfl⟩
      have hSL_bdd : BddAbove SL := ⟨u, fun z hz => hz.1.2⟩
      have hSR_bdd : BddBelow SR := ⟨u, fun z hz => by
        rcases hz with h1 | hz
        · rw [Set.mem_singleton_iff.mp h1]; exact hu.2.le
        · exact hz.1.1⟩
      let y₁ := sSup SL
      let y₂ := sInf SR
      have hSL_cl : IsClosed SL := by
        have : SL = Icc t u ∩ σ ⁻¹' {0} := by ext z; simp [SL]
        rw [this]
        exact (hσ_cont.mono (Icc_subset_Icc (hρ0.trans (hρα.trans (hαβ.le.trans ht.1))) hu.2.le)).preimage_isClosed_of_isClosed
          isClosed_Icc isClosed_singleton
      have hSR_cl : IsClosed SR := by
        have : SR = {1} ∪ (Icc u 1 ∩ σ ⁻¹' {0}) := by ext z; simp [SR]
        rw [this]
        exact isClosed_singleton.union ((hσ_cont.mono (Icc_subset_Icc (hρ0.trans (hρα.trans (hαβ.le.trans (ht.1.trans hu.1.le)))) (le_refl 1))).preimage_isClosed_of_isClosed
          isClosed_Icc isClosed_singleton)
      have hy1_in : y₁ ∈ SL := by have h := csSup_mem_closure hSL_ne hSL_bdd; rwa [hSL_cl.closure_eq] at h
      have hy2_in : y₂ ∈ SR := by have h := csInf_mem_closure hSR_ne hSR_bdd; rwa [hSR_cl.closure_eq] at h
      have hy1_lt_u : y₁ < u := lt_of_le_of_ne hy1_in.1.2 (fun h => by rw [h] at hy1_in; linarith [hy1_in.2])
      have hu_lt_y2 : u < y₂ := by
        rcases hy2_in with h1 | hy2
        · rw [Set.mem_singleton_iff.mp h1]; exact hu.2
        · exact lt_of_le_of_ne hy2.1.1 (fun h => by rw [← h] at hy2; linarith [hy2.2])
      have hy2_le1 : y₂ ≤ 1 := by
        rcases hy2_in with h1 | hy2
        · rw [Set.mem_singleton_iff.mp h1]
        · exact hy2.1.2
      have hneg_comp : ∀ z ∈ Ioo y₁ y₂, σ z < 0 := fun z hz => by
        refine lt_of_le_of_ne (hσ_np z ⟨hρα.trans (hαβ.le.trans (ht.1.trans (hy1_in.1.1.trans hz.1.le))), hz.2.le.trans hy2_le1⟩) ?_
        intro h0
        rcases le_total z u with hzu | huz
        · exact not_lt.mpr (le_csSup hSL_bdd ⟨⟨hy1_in.1.1.trans hz.1.le, hzu⟩, h0⟩) hz.1
        · exact not_lt.mpr (csInf_le hSR_bdd (Or.inr ⟨⟨huz, hz.2.le.trans hy2_le1⟩, h0⟩)) hz.2
      rcases hy2_in with h1 | hy2
      · rw [Set.mem_singleton_iff.mp h1] at hneg_comp
        exact hno_neg_to_one_above_β y₁ (ht.1.trans hy1_in.1.1) (hy1_lt_u.trans hu.2) hy1_in.2 hneg_comp
      · exact prop2_no_dip_without_endpoint M m1 ρ hρ0 hρ1 hSR
          (by have : max (max m1.r ρ) M.a = max ρ M.a := by simp [m1, singlePoolMech]
              rw [this]; exact hu0_lt_v1.le.trans (hv1α.trans (hαβ.le.trans (ht.1.trans hy1_in.1.1))))
          (hy1_lt_u.trans hu_lt_y2) hy2.1.2 hy1_in.2 hy2.2 hneg_comp (fun I hI => by
            simp only [m1, singlePoolMech, List.mem_singleton] at hI; subst hI
            exact ⟨fun h => by linarith [h.1, ht.1, hy1_in.1.1, hαβ], fun h => by linarith [h.1, ht.1, hy1_in.1.1]⟩)
    have hzero_Icc : ∀ u ∈ Icc t 1, σ u = 0 := fun u hu => by
      rcases eq_or_lt_of_le hu.1 with rfl | h1
      · exact hσt0
      · rcases eq_or_lt_of_le hu.2 with rfl | h2
        · have hlim : Tendsto σ (𝓝[Ioo t 1] 1) (𝓝 (σ 1)) :=
            (hσ_cont 1 ⟨zero_le_one, le_refl 1⟩).mono_left
              (nhdsWithin_mono 1 (fun z hz => ⟨(hρ0.trans (hρα.trans (hαβ.le.trans ht.1))).trans hz.1.le, hz.2.le⟩))
          have h0' : Tendsto σ (𝓝[Ioo t 1] 1) (𝓝 0) :=
            tendsto_const_nhds.congr' (Filter.eventually_of_mem self_mem_nhdsWithin fun z hz => (hzero_oo z hz).symm)
          haveI : (𝓝[Ioo t 1] (1 : ℝ)).NeBot := right_nhdsWithin_Ioo_neBot ht.2
          exact tendsto_nhds_unique hlim h0'
        · exact hzero_oo u ⟨h1, h2⟩
    have hF1_eq := (prop2_sigma_zero_off_pools M m1 ρ hρ0 hρ1 hSR
      (by have : max (max m1.r ρ) M.a = max ρ M.a := by simp [m1, singlePoolMech]
          rw [this]; exact hu0_lt_v1.le.trans (hv1α.trans (hαβ.le.trans ht.1))) ht.2 (le_refl 1)
      (fun I hI z hz => by
        simp only [m1, singlePoolMech, List.mem_singleton] at hI; subst hI
        intro h; linarith [h.2, ht.1, hz.1])
      hzero_Icc).1
    obtain ⟨u, hu, hne⟩ := htight4 (1 - t) (sub_pos.mpr ht.2)
    exact hne (hF1_eq u ⟨(by linarith : t ≤ 1 - (1 - t)).trans ((le_max_right _ _).trans hu.1.le), hu.2.le⟩)
  -- Step 3: Z := {v ∈ Icc α β | σ v = 0} is nonempty and equals Icc v₂ v₃
  let Z := {v ∈ Icc α β | σ v = 0}
  have hA1_eq1 : M.A 1 = 1 := by unfold Market.A; rw [M.hF_1]; simp
  have hA_lt : M.A v₁ < 1 := by
    unfold Market.A
    have hFlt := M.F_strictMonoOn ⟨ha_lt_v1.le, hv1_lt1.le⟩ (right_mem_Icc.mpr M.ha1.le) hv1_lt1
    rw [M.hF_1] at hFlt; linarith [div_pos (sub_pos.mpr hFlt) M.m_pos_real]
  have hZ_ne : Z.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have hneg_pool : ∀ t ∈ Icc α β, σ t < 0 := fun t ht =>
      lt_of_le_of_ne (hσ_np t ⟨hρα.trans ht.1, ht.2.trans hβ1⟩)
        (fun h0 => by have : t ∈ Z := ⟨ht, h0⟩; rw [hemp] at this; exact this)
    have hneg_all : ∀ t ∈ Ioo v₁ 1, σ t < 0 := fun t ht => by
      by_cases h1 : t ≤ α
      · exact hneg_left (lt_of_lt_of_le ht.1 h1) t ⟨ht.1, h1⟩
      · push Not at h1
        by_cases h2 : t ≤ β
        · exact hneg_pool t ⟨h1.le, h2⟩
        · push Not at h2
          exact hneg_above_β t ⟨h2.le, ht.2⟩
    have hF1_eq := (prop2_sigma_neg_on_Ioo M m1 ρ hρ0 hρ1 hSR hv1_lt1.le (le_refl 1) hneg_all).2
      v₁ (left_mem_Icc.mpr hv1_lt1.le) 1 (right_mem_Icc.mpr hv1_lt1.le)
    rw [hF1_v1, vs_effDist_one] at hF1_eq; linarith
  have hZ_bddA : BddAbove Z := ⟨β, fun v hv => hv.1.2⟩
  have hZ_bddB : BddBelow Z := ⟨α, fun v hv => hv.1.1⟩
  have hZ_cl : IsClosed Z := by
    have : Z = Icc α β ∩ σ ⁻¹' {0} := by ext v; simp [Z]
    rw [this]
    exact (hσ_cont.mono (Icc_subset_Icc (hρ0.trans hρα) hβ1)).preimage_isClosed_of_isClosed
      isClosed_Icc isClosed_singleton
  let v₂ := sInf Z
  let v₃ := sSup Z
  have hv2_in : v₂ ∈ Z := by have h := csInf_mem_closure hZ_ne hZ_bddB; rwa [hZ_cl.closure_eq] at h
  have hv3_in : v₃ ∈ Z := by have h := csSup_mem_closure hZ_ne hZ_bddA; rwa [hZ_cl.closure_eq] at h
  have hv23 : v₂ ≤ v₃ := le_trans (csInf_le hZ_bddB hZ_ne.some_mem) (le_csSup hZ_bddA hZ_ne.some_mem)
  have hZ_eq : ∀ t ∈ Icc v₂ v₃, σ t = 0 := fun t ht => by
    rcases eq_or_lt_of_le ht.1 with rfl | h1
    · exact hv2_in.2
    · rcases eq_or_lt_of_le ht.2 with rfl | h2
      · exact hv3_in.2
      · exact prop2_pool_zero_set_convex M m1 ρ hρ0 hρ1 hSR hI0
          (by have : max (max m1.r ρ) M.a = max ρ M.a := by simp [m1, singlePoolMech]
              rw [this]; exact hu0_lt_v1.le.trans (hv1α.trans hv2_in.1.1))
          hv2_in.1.1 h1 h2 hv3_in.1.2
          (fun u hu => hσ_np u ⟨hρα.trans (hv2_in.1.1.trans hu.1), (hu.2.trans hv3_in.1.2).trans hβ1⟩)
          hv2_in.2 hv3_in.2
  have hneg_12 : ∀ t ∈ Ioo v₁ v₂, σ t < 0 := fun t ht => by
    by_cases h1 : t ≤ α
    · exact hneg_left (lt_of_lt_of_le ht.1 h1) t ⟨ht.1, h1⟩
    · push Not at h1
      refine lt_of_le_of_ne (hσ_np t ⟨hρα.trans h1.le, (ht.2.le.trans hv2_in.1.2).trans hβ1⟩) ?_
      intro h0; exact not_lt.mpr (csInf_le hZ_bddB ⟨⟨h1.le, ht.2.le.trans hv2_in.1.2⟩, h0⟩) ht.2
  have hneg_31 : ∀ t ∈ Ioo v₃ 1, σ t < 0 := fun t ht => by
    by_cases h1 : β ≤ t
    · exact hneg_above_β t ⟨h1, ht.2⟩
    · push Not at h1
      refine lt_of_le_of_ne (hσ_np t ⟨hρα.trans (hv3_in.1.1.trans ht.1.le), h1.le.trans hβ1⟩) ?_
      intro h0; exact not_lt.mpr (le_csSup hZ_bddA ⟨⟨hv3_in.1.1.trans ht.1.le, h1.le⟩, h0⟩) ht.1
  have hv12_le : v₁ ≤ v₂ := hv1α.trans hv2_in.1.1
  have hv31_le : v₃ ≤ 1 := hv3_in.1.2.trans hβ1
  have hv2_1 : v₂ ≤ 1 := hv2_in.1.2.trans hβ1
  have h12_res := prop2_sigma_neg_on_Ioo M m1 ρ hρ0 hρ1 hSR hv12_le hv2_1 hneg_12
  have h31_res := prop2_sigma_neg_on_Ioo M m1 ρ hρ0 hρ1 hSR hv31_le (le_refl 1) hneg_31
  have hae_12 : ∀ᵐ v ∂(volume.restrict (Icc v₁ v₂)), θ.θ 0 v = 0 := by
    have := h12_res.1; rwa [max_eq_left ha_lt_v1.le] at this
  have hae_31 : ∀ᵐ v ∂(volume.restrict (Icc v₃ 1)), θ.θ 0 v = 0 := by
    have := h31_res.1; rwa [max_eq_left (ha_lt_v1.le.trans (hv12_le.trans hv23))] at this
  have hF1_v2 : effDist M θ 0 v₂ = M.A v₁ := by
    rw [h12_res.2 v₂ (right_mem_Icc.mpr hv12_le) v₁ (left_mem_Icc.mpr hv12_le), hF1_v1]
  have hF1_α : effDist M θ 0 α = M.A v₁ := by
    rw [h12_res.2 α ⟨hv1α, hv2_in.1.1⟩ v₁ (left_mem_Icc.mpr hv12_le), hF1_v1]
  have hF1_v3 : effDist M θ 0 v₃ = 1 := by
    rw [h31_res.2 v₃ (left_mem_Icc.mpr hv31_le) 1 (right_mem_Icc.mpr hv31_le), vs_effDist_one]
  have hF1_β : effDist M θ 0 β = 1 := by
    rw [h31_res.2 β ⟨hv3_in.1.2, hβ1⟩ 1 (right_mem_Icc.mpr hv31_le), vs_effDist_one]
  have hv2_lt_v3 : v₂ < v₃ := by
    rcases eq_or_lt_of_le hv23 with heq | hlt
    · exfalso; rw [heq] at hF1_v2; linarith
    · exact hlt
  have h23_res := prop2_sigma_zero_in_pool M m1 ρ hρ0 hρ1 hSR hI0
    (by have : max (max m1.r ρ) M.a = max ρ M.a := by simp [m1, singlePoolMech]
        rw [this]; exact hu0_lt_v1.le.trans hv12_le) hv2_in.1.1 hv2_lt_v3 hv3_in.1.2 hZ_eq
  have hqStar_pow := bandQStar_pow M ha_lt_v1.le hv1_lt1 (le_refl 1)
  have hqStar_bds := bandQStar_bounds M ha_lt_v1.le hv1_lt1 (le_refl 1)
  have hFriv_23 : ∀ v ∈ Icc v₂ v₃, effDist M θ (rivalIdx M) v = 1 - qStar := fun v hv => by
    have hp := h23_res.1 v hv; dsimp only [I0] at hp
    rw [hF1_α, hF1_β, ← hA1_eq1, ← hqStar_pow.1] at hp
    have hr_nn : 0 ≤ 1 - qStar := (M.A_mem_Icc hv1_lt1.le).1.trans hqStar_bds.1.le
    have hFv_nn : 0 ≤ effDist M θ (rivalIdx M) v := effDist_nonneg θ _ (hv.2.trans hv31_le)
    have hn1 : M.n - 1 ≠ 0 := by have := M.hn; omega
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact absurd hp (ne_of_lt (pow_lt_pow_left₀ hlt hFv_nn hn1))
    · exact absurd hp (ne_of_gt (pow_lt_pow_left₀ hgt hr_nn hn1))
  have hserved : M.F v₃ - M.F v₂ = (1 - M.F v₁) / (M.m : ℝ) := by
    have hsub := effDist_sub θ 0 hv2_1 hv31_le
    have hcongr : ∫ u in v₂..v₃, θ.θ 0 u * M.f u = ∫ u in v₂..v₃, M.f u := by
      apply intervalIntegral.integral_congr_ae
      have hae := (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mp h23_res.2
      filter_upwards [hae] with u hu hmem
      rw [uIoc_of_le hv2_lt_v3.le] at hmem; rw [hu ⟨hmem.1.le, hmem.2⟩, one_mul]
    rw [hcongr, M.integral_f hv2_1 hv31_le, hF1_v3, hF1_v2] at hsub
    unfold Market.A at hsub; have hm := M.m_pos_real.ne'; field_simp [hm] at hsub ⊢; linarith
  have hFriv_formula_12 : ∀ v ∈ Icc v₁ v₂,
      effDist M θ (rivalIdx M) v = M.A v₁ + (M.F v - M.F v₁) / ((M.m : ℝ) - 1) := fun v hv => by
    rw [(prop2_rival_symmetry M m1 ρ hρ0 hρ1 hSR).2 (rivalIdx M) (rivalIdx_ne_zero M) v
      ⟨hρ_lt_v1.le.trans hv.1, hv.2.trans hv2_1⟩]
    unfold FrivOf; rw [h12_res.2 v hv v₁ (left_mem_Icc.mpr hv12_le), hF1_v1]; unfold Market.A
    have hm1 := M.m_sub_one_pos_real.ne'; have hm := M.m_pos_real.ne'; field_simp [hm1, hm]; ring
  have hFriv_formula_31 : ∀ v ∈ Icc v₃ 1,
      effDist M θ (rivalIdx M) v = (1 - qStar) + (M.F v - M.F v₃) / ((M.m : ℝ) - 1) := fun v hv => by
    have hv3_eq : effDist M θ (rivalIdx M) v₃ = 1 - qStar := hFriv_23 v₃ (right_mem_Icc.mpr hv2_lt_v3.le)
    rw [(prop2_rival_symmetry M m1 ρ hρ0 hρ1 hSR).2 (rivalIdx M) (rivalIdx_ne_zero M) v
      ⟨(hρ_lt_v1.le.trans (hv12_le.trans hv23)).trans hv.1, hv.2⟩]
    rw [(prop2_rival_symmetry M m1 ρ hρ0 hρ1 hSR).2 (rivalIdx M) (rivalIdx_ne_zero M) v₃
      ⟨hρ_lt_v1.le.trans (hv12_le.trans hv23), hv31_le⟩] at hv3_eq
    unfold FrivOf at hv3_eq ⊢; rw [h31_res.2 v hv v₃ (left_mem_Icc.mpr hv31_le)]
    have hm1 := M.m_sub_one_pos_real.ne'; field_simp [hm1] at hv3_eq ⊢; linarith
  have hmass_12 : M.F v₂ - M.F v₁ = ((M.m : ℝ) - 1) * (q_hi - qStar) := by
    have h1 := hFriv_formula_12 v₂ (right_mem_Icc.mpr hv12_le)
    rw [hFriv_23 v₂ (left_mem_Icc.mpr hv2_lt_v3.le)] at h1
    have hm1 := M.m_sub_one_pos_real.ne'; dsimp only [q_hi]; unfold Market.A at h1
    field_simp [hm1] at h1 ⊢; linarith
  have hmass_31 : 1 - M.F v₃ = ((M.m : ℝ) - 1) * qStar := by
    have h1 := hFriv_formula_31 1 (right_mem_Icc.mpr hv31_le)
    rw [vs_effDist_one, M.hF_1] at h1
    have hm1 := M.m_sub_one_pos_real.ne'; field_simp [hm1] at h1 ⊢; linarith
  have hqStar_pos : 0 < qStar := by
    have := hqStar_bds.2.2.1; rw [M.hF_1] at this; simpa using this
  have hv1_lt_v2 : v₁ < v₂ := by
    rcases eq_or_lt_of_le hv12_le with heq | hlt
    · exfalso; rw [heq, sub_self] at hmass_12
      linarith [mul_pos M.m_sub_one_pos_real (sub_pos.mpr hqStar_bds.2.2.2)]
    · exact hlt
  have hv3_lt_1 : v₃ < 1 := by
    rcases eq_or_lt_of_le hv31_le with heq | hlt
    · exfalso; rw [heq, M.hF_1, sub_self] at hmass_31
      linarith [mul_pos M.m_sub_one_pos_real hqStar_pos]
    · exact hlt
  have hv3_lt_β : v₃ < β := by
    rcases eq_or_lt_of_le hv3_in.1.2 with heq | hlt
    · exfalso
      rcases eq_or_lt_of_le hβ1 with hβeq1 | hβlt1
      · linarith
      · have := hneg_above_β β ⟨le_refl _, hβlt1⟩; rw [← heq] at this; linarith [hv3_in.2]
    · exact hlt
  -- α strict bounds + eq. (15) via outer_endpoint_strict_bounds
  have hσ_diff_12 :
      (α - v₁) * (M.A v₁) ^ (M.n - 1) + (v₂ - α) * (1 - qStar) ^ (M.n - 1) -
        ∫ v in v₁..v₂, (M.A v₁ + (M.F v - M.F v₁) / ((M.m : ℝ) - 1)) ^ (M.n - 1) = 0 := by
    have hsub := sigma_sub M m1 ρ hρ0 hρ1 hSR hv1_0 hv1_lt1.le (hv1_0.trans hv12_le) hv2_1
    have h20 : sigma M m1 ρ hρ0 hρ1 θ v₂ = 0 := hv2_in.2
    have h10 : sigma M m1 ρ hρ0 hρ1 θ v₁ = 0 := hσ_v1
    rw [h20, h10, sub_self] at hsub
    have hi1 := alloc_intervalIntegrable M m1 _ (vs_effDist_monotoneOn θ 0) (fun _ h => effDist_nonneg θ 0 h) hv1_lt1.le hv2_1
    have hiR := alloc_intervalIntegrable M (SPA ρ hρ0 hρ1) _ (vs_effDist_monotoneOn θ (rivalIdx M))
      (fun _ h => effDist_nonneg θ (rivalIdx M) h) hv1_lt1.le hv2_1
    rw [intervalIntegral.integral_sub hi1 hiR] at hsub
    have hsplit : ∫ t in v₁..v₂, alloc M m1 (effDist M θ 0) t =
        (∫ t in v₁..α, alloc M m1 (effDist M θ 0) t) + (∫ t in α..v₂, alloc M m1 (effDist M θ 0) t) :=
      (intervalIntegral.integral_add_adjacent_intervals
        (alloc_intervalIntegrable M m1 _ (vs_effDist_monotoneOn θ 0) (fun _ h => effDist_nonneg θ 0 h) hv1_lt1.le (hαβ.le.trans hβ1))
        (alloc_intervalIntegrable M m1 _ (vs_effDist_monotoneOn θ 0) (fun _ h => effDist_nonneg θ 0 h) (hαβ.le.trans hβ1) hv2_1)).symm
    have hL : ∫ t in v₁..α, alloc M m1 (effDist M θ 0) t = (α - v₁) * (M.A v₁) ^ (M.n - 1) := by
      have hc : ∫ t in v₁..α, alloc M m1 (effDist M θ 0) t = ∫ _ in v₁..α, (M.A v₁) ^ (M.n - 1) := by
        apply intervalIntegral.integral_congr_ae
        have hne : ∀ᵐ t ∂volume, t ≠ α := by simp [ae_iff, measure_singleton]
        filter_upwards [hne] with t htα ht
        rw [uIoc_of_le hv1α] at ht
        rw [alloc_off_pools M m1 _ (hρ_lt_v1.le.trans ht.1.le) (fun I hI => by
          simp only [m1, singlePoolMech, List.mem_singleton] at hI; subst hI
          intro h; linarith [h.1, lt_of_le_of_ne ht.2 htα]),
          h12_res.2 t ⟨ht.1.le, ht.2.trans hv2_in.1.1⟩ v₁ (left_mem_Icc.mpr hv12_le), hF1_v1]
      rw [hc, intervalIntegral.integral_const, smul_eq_mul]
    have hpool_eq : poolAvg M.n (M.A v₁) 1 = (1 - qStar) ^ (M.n - 1) := by
      have := hqStar_pow.1; rw [hA1_eq1] at this; exact this.symm
    have hR : ∫ t in α..v₂, alloc M m1 (effDist M θ 0) t = (v₂ - α) * (1 - qStar) ^ (M.n - 1) := by
      have hc : ∫ t in α..v₂, alloc M m1 (effDist M θ 0) t = ∫ _ in α..v₂, (1 - qStar) ^ (M.n - 1) := by
        apply intervalIntegral.integral_congr_ae
        have hne : ∀ᵐ t ∂volume, t ≠ v₂ := by simp [ae_iff, measure_singleton]
        filter_upwards [hne] with t htv2 ht
        rw [uIoc_of_le hv2_in.1.1] at ht
        rw [alloc_in_pool M m1 _ hI0 ⟨ht.1, (lt_of_le_of_ne ht.2 htv2).trans_le hv2_in.1.2⟩]
        dsimp only [I0]; rw [hF1_α, hF1_β, hpool_eq]
      rw [hc, intervalIntegral.integral_const, smul_eq_mul]
    have hRiv : ∫ t in v₁..v₂, alloc M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) t =
        ∫ v in v₁..v₂, (M.A v₁ + (M.F v - M.F v₁) / ((M.m : ℝ) - 1)) ^ (M.n - 1) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with t ht
      rw [uIoc_of_le hv12_le] at ht
      rw [alloc_SPA, ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr (hρ_lt_v1.le.trans ht.1.le))),
        hFriv_formula_12 t ⟨ht.1.le, ht.2⟩]
    linarith
  have hc1_12 : 1 - qStar = M.A v₁ + (M.F v₂ - M.F v₁) / ((M.m : ℝ) - 1) := by
    have := hFriv_formula_12 v₂ (right_mem_Icc.mpr hv12_le)
    rwa [hFriv_23 v₂ (left_mem_Icc.mpr hv2_lt_v3.le)] at this
  have hα_out := outer_endpoint_strict_bounds M ha_lt_v1.le hv1_lt_v2 hv2_1 (M.A_mem_Icc hv1_lt1.le).1 hc1_12
  have hα_ibp_eq :
      α = (v₂ * (1 - qStar) ^ (M.n - 1) - v₁ * (M.A v₁) ^ (M.n - 1) -
            ∫ v in v₁..v₂, (M.A v₁ + (M.F v - M.F v₁) / ((M.m : ℝ) - 1)) ^ (M.n - 1)) /
          ((1 - qStar) ^ (M.n - 1) - (M.A v₁) ^ (M.n - 1)) := by
    rw [eq_div_iff hα_out.1.ne']; linarith
  have hα_stieltjes :
      α = (∫ v in v₁..v₂, v * (((M.n : ℝ) - 1) * (effDist M θ (rivalIdx M) v) ^ (M.n - 2) *
              (M.f v / ((M.m : ℝ) - 1)))) /
            (∫ v in v₁..v₂, ((M.n : ℝ) - 1) * (effDist M θ (rivalIdx M) v) ^ (M.n - 2) *
              (M.f v / ((M.m : ℝ) - 1))) := by
    rw [hα_ibp_eq, hα_out.2.2.2]
    congr 1
    · exact intervalIntegral.integral_congr (fun v hv => by rw [uIcc_of_le hv12_le] at hv; rw [hFriv_formula_12 v hv])
    · exact intervalIntegral.integral_congr (fun v hv => by rw [uIcc_of_le hv12_le] at hv; rw [hFriv_formula_12 v hv])
  -- β ≥ β₀ from σ(1) - σ(v₃) ≤ 0
  have hβ_ge :
      (∫ v in v₃..1, v * (((M.n : ℝ) - 1) * (effDist M θ (rivalIdx M) v) ^ (M.n - 2) *
            (M.f v / ((M.m : ℝ) - 1)))) /
          (∫ v in v₃..1, ((M.n : ℝ) - 1) * (effDist M θ (rivalIdx M) v) ^ (M.n - 2) *
            (M.f v / ((M.m : ℝ) - 1))) ≤ β := by
    have hsub := sigma_sub M m1 ρ hρ0 hρ1 hSR (hv1_0.trans (hv12_le.trans hv23)) hv31_le zero_le_one (le_refl 1)
    have h30 : sigma M m1 ρ hρ0 hρ1 θ v₃ = 0 := hv3_in.2
    have hσ1_le : sigma M m1 ρ hρ0 hρ1 θ 1 ≤ 0 := hσ_np 1 ⟨hρ1, le_refl 1⟩
    rw [h30, sub_zero] at hsub
    have hi1 := alloc_intervalIntegrable M m1 _ (vs_effDist_monotoneOn θ 0) (fun _ h => effDist_nonneg θ 0 h) hv31_le (le_refl 1)
    have hiR := alloc_intervalIntegrable M (SPA ρ hρ0 hρ1) _ (vs_effDist_monotoneOn θ (rivalIdx M))
      (fun _ h => effDist_nonneg θ (rivalIdx M) h) hv31_le (le_refl 1)
    rw [intervalIntegral.integral_sub hi1 hiR] at hsub
    have hsplit : ∫ t in v₃..1, alloc M m1 (effDist M θ 0) t =
        (∫ t in v₃..β, alloc M m1 (effDist M θ 0) t) + (∫ t in β..1, alloc M m1 (effDist M θ 0) t) :=
      (intervalIntegral.integral_add_adjacent_intervals
        (alloc_intervalIntegrable M m1 _ (vs_effDist_monotoneOn θ 0) (fun _ h => effDist_nonneg θ 0 h) hv31_le hβ1)
        (alloc_intervalIntegrable M m1 _ (vs_effDist_monotoneOn θ 0) (fun _ h => effDist_nonneg θ 0 h) hβ1 (le_refl 1))).symm
    have hpool_eq : poolAvg M.n (M.A v₁) 1 = (1 - qStar) ^ (M.n - 1) := by
      have := hqStar_pow.1; rw [hA1_eq1] at this; exact this.symm
    have hL : ∫ t in v₃..β, alloc M m1 (effDist M θ 0) t = (β - v₃) * (1 - qStar) ^ (M.n - 1) := by
      have hc : ∫ t in v₃..β, alloc M m1 (effDist M θ 0) t = ∫ _ in v₃..β, (1 - qStar) ^ (M.n - 1) := by
        apply intervalIntegral.integral_congr_ae
        have hne : ∀ᵐ t ∂volume, t ≠ β := by simp [ae_iff, measure_singleton]
        filter_upwards [hne] with t htβ ht
        rw [uIoc_of_le hv3_in.1.2] at ht
        rw [alloc_in_pool M m1 _ hI0 ⟨hv3_in.1.1.trans_lt ht.1, lt_of_le_of_ne ht.2 htβ⟩]
        dsimp only [I0]; rw [hF1_α, hF1_β, hpool_eq]
      rw [hc, intervalIntegral.integral_const, smul_eq_mul]
    have hR : ∫ t in β..1, alloc M m1 (effDist M θ 0) t = (1 - β) * (1 : ℝ) ^ (M.n - 1) := by
      have hc : ∫ t in β..1, alloc M m1 (effDist M θ 0) t = ∫ _ in β..1, (1 : ℝ) ^ (M.n - 1) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards with t ht
        rw [uIoc_of_le hβ1] at ht
        rw [alloc_off_pools M m1 _ (hρα.trans (hαβ.le.trans ht.1.le)) (fun I hI => by
          simp only [m1, singlePoolMech, List.mem_singleton] at hI; subst hI
          intro h; linarith [h.2, ht.1]),
          h31_res.2 t ⟨hv3_in.1.2.trans ht.1.le, ht.2⟩ 1 (right_mem_Icc.mpr hv31_le), vs_effDist_one]
      rw [hc, intervalIntegral.integral_const, smul_eq_mul]
    have hRiv : ∫ t in v₃..1, alloc M (SPA ρ hρ0 hρ1) (effDist M θ (rivalIdx M)) t =
        ∫ v in v₃..1, (1 - qStar + (M.F v - M.F v₃) / ((M.m : ℝ) - 1)) ^ (M.n - 1) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with t ht
      rw [uIoc_of_le hv31_le] at ht
      rw [alloc_SPA, ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr ((hρ_lt_v1.le.trans (hv12_le.trans hv23)).trans ht.1.le))),
        hFriv_formula_31 t ⟨ht.1.le, ht.2⟩]
    have hibp := ibp_riv_pow M (ha_lt_v1.le.trans (hv12_le.trans hv23)) hv3_lt_1 (le_refl 1) (1 - qStar)
    have hnum_eq : ∫ v in v₃..1, v * (((M.n : ℝ) - 1) * (effDist M θ (rivalIdx M) v) ^ (M.n - 2) *
          (M.f v / ((M.m : ℝ) - 1))) =
        ∫ v in v₃..1, v * (((M.n : ℝ) - 1) * (1 - qStar + (M.F v - M.F v₃) / ((M.m : ℝ) - 1)) ^ (M.n - 2) *
          (M.f v / ((M.m : ℝ) - 1))) :=
      intervalIntegral.integral_congr (fun v hv => by rw [uIcc_of_le hv31_le] at hv; rw [hFriv_formula_31 v hv])
    have hden_eq : ∫ v in v₃..1, ((M.n : ℝ) - 1) * (effDist M θ (rivalIdx M) v) ^ (M.n - 2) *
          (M.f v / ((M.m : ℝ) - 1)) =
        ∫ v in v₃..1, ((M.n : ℝ) - 1) * (1 - qStar + (M.F v - M.F v₃) / ((M.m : ℝ) - 1)) ^ (M.n - 2) *
          (M.f v / ((M.m : ℝ) - 1)) :=
      intervalIntegral.integral_congr (fun v hv => by rw [uIcc_of_le hv31_le] at hv; rw [hFriv_formula_31 v hv])
    have hg_1 : 1 - qStar + (M.F 1 - M.F v₃) / ((M.m : ℝ) - 1) = 1 := by
      have := hFriv_formula_31 1 (right_mem_Icc.mpr hv31_le); rw [vs_effDist_one] at this; exact this.symm
    have hg_v3 : 1 - qStar + (M.F v₃ - M.F v₃) / ((M.m : ℝ) - 1) = 1 - qStar := by simp
    have hn1 : M.n - 1 ≠ 0 := by have := M.hn; omega
    have hden_pos : 0 < (1 : ℝ) ^ (M.n - 1) - (1 - qStar) ^ (M.n - 1) := by
      have h1lt : 1 - qStar < 1 := by linarith
      have hr_nn : 0 ≤ 1 - qStar := (M.A_mem_Icc hv1_lt1.le).1.trans hqStar_bds.1.le
      exact sub_pos.mpr (pow_lt_pow_left₀ h1lt hr_nn hn1)
    rw [hnum_eq, hden_eq, hibp.1, hibp.2]
    dsimp only
    rw [hg_1, hg_v3, div_le_iff₀ hden_pos]
    simp only [one_pow, one_mul] at hR hden_pos ⊢; linarith
  have hqStar_eq5 : (1 - qStar) ^ (M.n - 1) = (1 - (1 - q_hi) ^ M.n) / ((M.n : ℝ) * q_hi) := by
    have h := hqStar_pow.2; rw [M.hF_1] at h; simpa [q_hi] using h
  exact ⟨v₂, v₃, hα_ibp_eq ▸ hα_out.2.1, hα_ibp_eq ▸ hα_out.2.2.1, hv2_lt_v3, hv3_lt_β, hβ1,
    hae_12, h23_res.2, hae_31, hserved, hFriv_23, hqStar_eq5, hmass_12, hmass_31,
    hα_stieltjes, hβ_ge⟩

end Lemma1

end AuctionCompetition
