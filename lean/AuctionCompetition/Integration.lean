import AuctionCompetition.Defs
import AuctionCompetition.VisitStage
import AuctionCompetition.Cournot
import AuctionCompetition.CoveredMarkets
import AuctionCompetition.Sharpness
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# End-to-End Integration: Mechanism / `IsSR` / `sellerRev` Bridges

This file closes the cross-module bridges between:
- `VisitStage.lean` (`IsSR`, Proposition 1, Proposition 2, Lemma 1, `bandToPool`, `lemma1_band_to_pool_sr`),
- `Cournot.lean` (`UnilateralContinuation`, Proposition 3, Lemma B.1, `Market.inverseDemand`),
- `CoveredMarkets.lean` (Theorem 2, Example 1), and
- `Sharpness.lean` (Proposition C.2, Theorem 5(ii)).

Main results proved here (100% complete, zero `sorry`/`admit`/`axiom`):
1. `unilateralContinuation_of_isSR`: constructs `UnilateralContinuation` directly from any
   `IsSR` continuation against rivals at `SPA(ρ)`.
2. `end_to_end_theorem2_covered_markets`: full mechanism-level Theorem 2 (`sellerRev` of any
   hierarchical deviation and any SR continuation is at most symmetric `SPA(ρ*)^m` revenue).
3. `end_to_end_example1`: full mechanism-level instantiation on Example 1 (alongside
   `example1_monopolist_irons` and `example1_rhoStar`).
4. `end_to_end_theorem5_many_buyers`: full mechanism-level Theorem 5(ii) constructing explicit
   interior-pool mechanisms `(ρ*(n), {(α_n, β_n)})` and explicit SR continuations `θ_n` with
   strictly higher `sellerRev` than symmetric `SPA(ρ*(n))^m` for all sufficiently large `n`.
-/

open MeasureTheory Set Filter Topology

namespace AuctionCompetition

/-! ### Part 1: Constructing `UnilateralContinuation` from `IsSR` -/

section IsSRToContinuation

/-- For any market `M`, the Virág candidate reserve `M.rhoStar` satisfies `M.rhoStar < 1`. -/
lemma int_rhoStar_lt_one (M : Market) : M.rhoStar < 1 := by
  rcases eq_or_lt_of_le M.ha0 with ha0 | hapos
  · unfold Market.rhoStar; rw [← ha0, mul_zero, zero_div]; exact zero_lt_one
  · exact (M.rhoStar_lt_a hapos).trans M.ha1

/-- Open-neighborhood continuity of `alloc M mech F1` away from
`{mech.r} ∪ ⋃ I ∈ mech.pools, {I.α, I.β}` when `F1` is continuous on `Iic 1`. -/
private lemma int_alloc_continuousOn_nhds {M : Market} (mech : HierarchicalMech) {F1 : ℝ → ℝ}
    (hF1_cont : ContinuousOn F1 (Iic 1)) {v : ℝ} (hv_lt1 : v < 1)
    (hvr : v ≠ mech.r) (hvp : ∀ I ∈ mech.pools, v ≠ I.α ∧ v ≠ I.β) :
    ∃ U : Set ℝ, IsOpen U ∧ v ∈ U ∧ ContinuousOn (alloc M mech F1) U := by
  by_cases hlt : v < mech.r
  · refine ⟨Iio mech.r, isOpen_Iio, hlt, ?_⟩
    exact continuousOn_const.congr (fun u hu => alloc_below_r M mech F1 hu)
  · have hgt : mech.r < v := lt_of_le_of_ne (not_lt.mp hlt) hvr.symm
    by_cases hpool : ∃ I ∈ mech.pools, I.α < v ∧ v < I.β
    · obtain ⟨I, hI, h1, h2⟩ := hpool
      refine ⟨Ioo I.α I.β, isOpen_Ioo, ⟨h1, h2⟩, ?_⟩
      exact continuousOn_const.congr (fun u hu => alloc_in_pool M mech F1 hI hu)
    · push Not at hpool
      have hsep : ∀ I ∈ mech.pools, ∀ᶠ u in 𝓝 v, ¬ (I.α < u ∧ u < I.β) := by
        intro I hI
        rcases lt_or_gt_of_ne (hvp I hI).1 with hlt_α | hgt_α
        · filter_upwards [Iio_mem_nhds hlt_α] with u hu h
          rw [mem_Iio] at hu; linarith [h.1]
        · have hge_β : I.β ≤ v := hpool I hI hgt_α
          have hgt_β : I.β < v := lt_of_le_of_ne hge_β (hvp I hI).2.symm
          filter_upwards [Ioi_mem_nhds hgt_β] with u hu h
          rw [mem_Ioi] at hu; linarith [h.2]
      have hall : ∀ᶠ u in 𝓝 v, ∀ I ∈ mech.pools, ¬ (I.α < u ∧ u < I.β) := by
        have hfin : ∀ L : List Pool, (∀ I ∈ L, ∀ᶠ u in 𝓝 v, ¬ (I.α < u ∧ u < I.β)) →
            ∀ᶠ u in 𝓝 v, ∀ I ∈ L, ¬ (I.α < u ∧ u < I.β) := by
          intro L
          induction L with
          | nil => intro _; exact Eventually.of_forall (fun _ _ h => nomatch h)
          | cons I L ih =>
            intro h
            have h1 := h I List.mem_cons_self
            have h2 := ih (fun J hJ => h J (List.mem_cons_of_mem I hJ))
            filter_upwards [h1, h2] with u hu1 hu2 J hJ
            rcases List.mem_cons.mp hJ with rfl | hJL
            · exact hu1
            · exact hu2 J hJL
        exact hfin mech.pools hsep
      have hmem : {u : ℝ | mech.r < u ∧ u < 1 ∧ ∀ I ∈ mech.pools, ¬ (I.α < u ∧ u < I.β)} ∈ 𝓝 v := by
        filter_upwards [Ioi_mem_nhds hgt, Iio_mem_nhds hv_lt1, hall] with u hu1 hu2 hu3
        exact ⟨hu1, hu2, hu3⟩
      obtain ⟨U, hU_sub, hU_open, hvU⟩ := mem_nhds_iff.mp hmem
      refine ⟨U, hU_open, hvU, ?_⟩
      have hF1_U : ContinuousOn (fun u => (F1 u) ^ (M.n - 1)) U :=
        (hF1_cont.mono (fun u hu => (hU_sub hu).2.1.le)).pow (M.n - 1)
      exact hF1_U.congr (fun u hu => alloc_off_pools M mech F1 (hU_sub hu).1.le (hU_sub hu).2.2)

/-- Open-neighborhood continuity of `alloc M (SPA ρ) F_riv` on `Ioo ρ 1`. -/
private lemma int_alloc_SPA_continuousOn {M : Market} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    {F_riv : ℝ → ℝ} (hFriv_cont : ContinuousOn F_riv (Icc ρ 1)) :
    ContinuousOn (alloc M (SPA ρ hρ0 hρ1) F_riv) (Ioo ρ 1) := by
  have hpow : ContinuousOn (fun u => (F_riv u) ^ (M.n - 1)) (Ioo ρ 1) :=
    (hFriv_cont.mono Ioo_subset_Icc_self).pow (M.n - 1)
  refine hpow.congr (fun u hu => ?_)
  rw [alloc_SPA, ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr hu.1.le))]

/-- The finite set of potential discontinuity points of `alloc M mech F1` has Lebesgue measure zero. -/
private lemma int_ae_not_mech_endpoints (mech : HierarchicalMech) :
    ∀ᵐ v ∂volume, v ≠ mech.r ∧ ∀ I ∈ mech.pools, v ≠ I.α ∧ v ≠ I.β := by
  have hne_r : ∀ᵐ v ∂volume, v ≠ mech.r := by simp [ae_iff, measure_singleton]
  have hpools : ∀ L : List Pool, ∀ᵐ v ∂volume, ∀ I ∈ L, v ≠ I.α ∧ v ≠ I.β := by
    intro L
    induction L with
    | nil => exact Eventually.of_forall (fun _ _ h => nomatch h)
    | cons I L ih =>
      have hα : ∀ᵐ v ∂volume, v ≠ I.α := by simp [ae_iff, measure_singleton]
      have hβ : ∀ᵐ v ∂volume, v ≠ I.β := by simp [ae_iff, measure_singleton]
      filter_upwards [hα, hβ, ih] with v hvα hvβ hvL J hJ
      rcases List.mem_cons.mp hJ with rfl | hJL
      · exact ⟨hvα, hvβ⟩
      · exact hvL J hJL
  filter_upwards [hne_r, hpools mech.pools] with v h1 h2
  exact ⟨h1, h2⟩

/-- **Bridge Theorem 1 (`IsSR` → `UnilateralContinuation`)**:
Given any market `M`, rival reserve `ρ ∈ [0, 1)`, unilateral deviation `mech : HierarchicalMech`
by seller `0`, and sequentially rational visit strategy `θ`, construct the
`UnilateralContinuation` object consumed by Proposition 3 and Lemma B.1 in `Cournot.lean`,
using Proposition 2(i) (`prop2_rival_symmetry`) and Proposition 2(iii) (`prop2_sigma_pos_initial`). -/
noncomputable def unilateralContinuation_of_isSR (M : Market) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (mech : HierarchicalMech) (θ : VisitStrategy M)
    (hSR : IsSR M (unilateralProfile M mech ρ hρ0 hρ1.le) θ) :
    UnilateralContinuation M ρ hρ0 hρ1 mech := by
  have hsym := (prop2_rival_symmetry M mech ρ hρ0 hρ1.le hSR).2
  have hinit := (prop2_sigma_pos_initial M mech ρ hρ0 hρ1.le hSR).2
  let v_hat := hinit.choose
  have hv_hat_mem : v_hat ∈ Icc (max (min mech.r ρ) M.a) 1 := hinit.choose_spec.1
  have hpos_oo : ∀ v ∈ Ioo (max (min mech.r ρ) M.a) v_hat,
      0 < sigma M mech ρ hρ0 hρ1.le θ v := hinit.choose_spec.2.1
  have hle_above : ∀ v ∈ Ioc v_hat 1, sigma M mech ρ hρ0 hρ1.le θ v ≤ 0 :=
    hinit.choose_spec.2.2.1
  have hle_at_vhat : v_hat < 1 → sigma M mech ρ hρ0 hρ1.le θ v_hat ≤ 0 :=
    hinit.choose_spec.2.2.2.1
  have hae_below_vhat :
      ∀ᵐ v ∂(volume.restrict (Icc (max (min mech.r ρ) M.a) v_hat)), θ.θ 0 v = 1 :=
    hinit.choose_spec.2.2.2.2.2
  -- 1. `ρ ≤ v_hat`
  have hρ_le_vhat : ρ ≤ v_hat := by
    by_contra hlt
    push Not at hlt
    have hbot_lt_ρ : max (min mech.r ρ) M.a < ρ := lt_of_le_of_lt hv_hat_mem.1 hlt
    have hmin_lt_ρ : min mech.r ρ < ρ := lt_of_le_of_lt (le_max_left _ _) hbot_lt_ρ
    have hr_lt_ρ : mech.r < ρ := by
      by_contra hge; push Not at hge
      rw [min_eq_right hge] at hmin_lt_ρ; exact lt_irrefl _ hmin_lt_ρ
    have hmax_lt_vhat : max mech.r M.a ≤ v_hat := by
      have h := hv_hat_mem.1
      rwa [min_eq_left hr_lt_ρ.le] at h
    let u := (v_hat + ρ) / 2
    have hu_gt_vhat : v_hat < u := by dsimp [u]; linarith
    have hu_lt_ρ : u < ρ := by dsimp [u]; linarith
    have hpos_u : 0 < sigma M mech ρ hρ0 hρ1.le θ u :=
      (prop2_below_rho_seller1_captures M mech ρ hρ0 hρ1.le hSR hr_lt_ρ).1 u
        ⟨lt_of_le_of_lt hmax_lt_vhat hu_gt_vhat, hu_lt_ρ⟩
    have hle_u : sigma M mech ρ hρ0 hρ1.le θ u ≤ 0 :=
      hle_above u ⟨hu_gt_vhat, hu_lt_ρ.le.trans hρ1.le⟩
    linarith
  -- 2. `hθ_below_r`
  have hθ_below_r :
      ∀ᵐ v ∂(volume.restrict (Icc (max (min mech.r ρ) M.a) mech.r)), θ.θ 0 v = 0 := by
    by_cases hlt : max (min mech.r ρ) M.a < mech.r
    · have hmin_lt_r : min mech.r ρ < mech.r := lt_of_le_of_lt (le_max_left _ _) hlt
      have hρ_lt_r : ρ < mech.r := by
        by_contra hge; push Not at hge
        rw [min_eq_left hge] at hmin_lt_r; exact lt_irrefl _ hmin_lt_r
      have hSR_ae := (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mp hSR
      have hne_bot : ∀ᵐ v ∂volume, v ≠ max (min mech.r ρ) M.a := by simp [ae_iff, measure_singleton]
      have hne_r : ∀ᵐ v ∂volume, v ≠ mech.r := by simp [ae_iff, measure_singleton]
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
      filter_upwards [hSR_ae, hne_bot, hne_r] with v hvSR hvbot hvr hmem
      have hv_gt_bot : max (min mech.r ρ) M.a < v := lt_of_le_of_ne hmem.1 (Ne.symm hvbot)
      have hv_lt_r : v < mech.r := lt_of_le_of_ne hmem.2 hvr
      have hv_gt_a : M.a < v := lt_of_le_of_lt (le_max_right _ _) hv_gt_bot
      have hv_gt_ρ : ρ < v := by
        have : ρ ≤ max (min mech.r ρ) M.a :=
          le_trans (by rw [min_eq_right hρ_lt_r.le]) (le_max_left _ _)
        exact lt_of_le_of_lt this hv_gt_bot
      have hv_Icc : v ∈ Icc M.a 1 := ⟨hv_gt_a.le, hv_lt_r.le.trans mech.hr1⟩
      have hv0 : 0 ≤ v := M.ha0.trans hv_gt_a.le
      have hs1_zero : surplus M mech (effDist M θ 0) v = 0 :=
        surplus_zero_of_le_r M mech (effDist M θ 0) hv0 hv_lt_r.le
      have hsriv_pos : 0 < surplus M (SPA ρ hρ0 hρ1.le) (effDist M θ (rivalIdx M)) v := by
        rw [surplus_SPA_eq M ρ hρ0 hρ1.le _ (vs_effDist_monotoneOn θ _)
          (fun x hx => effDist_nonneg θ _ hx) hv0 hv_Icc.2, max_eq_left hv_gt_ρ.le]
        let m0 := (max ρ M.a + v) / 2
        have hm0_gt_a : M.a < m0 := by dsimp [m0]; linarith [le_max_right ρ M.a, max_lt hv_gt_ρ hv_gt_a]
        have hm0_gt_ρ : ρ < m0 := by dsimp [m0]; linarith [le_max_left ρ M.a, max_lt hv_gt_ρ hv_gt_a]
        have hm0_lt_v : m0 < v := by dsimp [m0]; linarith [max_lt hv_gt_ρ hv_gt_a]
        have hF_pos : 0 < M.F m0 := by
          rw [← M.hF_a]
          exact M.F_strictMonoOn (left_mem_Icc.mpr M.ha1.le)
            ⟨hm0_gt_a.le, hm0_lt_v.le.trans hv_Icc.2⟩ hm0_gt_a
        have hFriv_m0_pos : 0 < effDist M θ (rivalIdx M) m0 :=
          lt_of_lt_of_le hF_pos (vs_effDist_mem_Icc θ (rivalIdx M) (hm0_lt_v.le.trans hv_Icc.2)).1
        have hcont : ContinuousOn (fun t => (effDist M θ (rivalIdx M) t) ^ (M.n - 1)) (Icc ρ v) :=
          ((effDist_continuousOn θ (rivalIdx M)).mono (fun t (ht : t ∈ Icc ρ v) => ht.2.trans hv_Icc.2)).pow (M.n - 1)
        exact intervalIntegral.integral_pos hv_gt_ρ hcont
          (fun t (ht : t ∈ Ioc ρ v) => pow_nonneg (effDist_nonneg θ _ (ht.2.trans hv_Icc.2)) _)
          ⟨m0, ⟨hm0_gt_ρ.le, hm0_lt_v.le⟩, pow_pos hFriv_m0_pos _⟩
      by_contra hne0
      have hpos0 : 0 < θ.θ 0 v := lt_of_le_of_ne (θ.hnonneg 0 v) (Ne.symm hne0)
      have hle := hvSR hv_Icc 0 (rivalIdx M) hpos0
      simp only [unilateralProfile, ite_true,
        ite_eq_right_iff.mpr (fun h => absurd h (rivalIdx_ne_zero M))] at hle
      linarith
    · push Not at hlt
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
      have hne : ∀ᵐ v ∂volume, v ≠ mech.r := by simp [ae_iff, measure_singleton]
      filter_upwards [hne] with v hv hmem
      have : v = mech.r := le_antisymm hmem.2 (hlt.trans hmem.1)
      exact absurd this hv
  -- 3. `hs_below`
  have hs_below : max (min mech.r ρ) M.a < v_hat →
      ∀ v ∈ Icc (max (min mech.r ρ) M.a) v_hat,
        surplus M (SPA ρ hρ0 hρ1.le) (FrivOf M (effDist M θ 0)) v ≤
          surplus M mech (effDist M θ 0) v := by
    intro hlt v hv
    have hbot0 : 0 ≤ max (min mech.r ρ) M.a := le_max_of_le_right M.ha0
    have hcont : ContinuousOn (sigma M mech ρ hρ0 hρ1.le θ)
        (Icc (max (min mech.r ρ) M.a) v_hat) :=
      (sigma_continuousOn M mech ρ hρ0 hρ1.le hSR).mono (Icc_subset_Icc hbot0 hv_hat_mem.2)
    have hσ_nn : 0 ≤ sigma M mech ρ hρ0 hρ1.le θ v := by
      have hcl : v ∈ closure (Ioo (max (min mech.r ρ) M.a) v_hat) := by
        rw [closure_Ioo hlt.ne]; exact hv
      have hsub : Ioo (max (min mech.r ρ) M.a) v_hat ⊆ Icc (max (min mech.r ρ) M.a) v_hat :=
        Ioo_subset_Icc_self
      have hnhds : NeBot (𝓝[Ioo (max (min mech.r ρ) M.a) v_hat] v) :=
        mem_closure_iff_nhdsWithin_neBot.mp hcl
      have htend : Tendsto (sigma M mech ρ hρ0 hρ1.le θ)
          (𝓝[Ioo (max (min mech.r ρ) M.a) v_hat] v)
          (𝓝 (sigma M mech ρ hρ0 hρ1.le θ v)) :=
        (hcont v hv).mono_left (nhdsWithin_mono v hsub)
      exact ge_of_tendsto htend
        (eventually_nhdsWithin_of_forall fun u hu => (hpos_oo u hu).le)
    unfold sigma srivOf at hσ_nn
    linarith
  -- 4. `hs_vhat_eq`
  have hs_vhat_eq : max (min mech.r ρ) M.a < v_hat → v_hat < 1 →
      surplus M mech (effDist M θ 0) v_hat =
        surplus M (SPA ρ hρ0 hρ1.le) (FrivOf M (effDist M θ 0)) v_hat := by
    intro hlt hvhat_lt1
    have hge := hs_below hlt v_hat (right_mem_Icc.mpr hlt.le)
    have hle := hle_at_vhat hvhat_lt1
    unfold sigma srivOf at hle
    linarith
  -- 5. `hs_above`
  have hs_above : ∀ᵐ v ∂(volume.restrict (Icc v_hat 1)),
      0 < θ.θ 0 v →
        surplus M mech (effDist M θ 0) v =
          surplus M (SPA ρ hρ0 hρ1.le) (FrivOf M (effDist M θ 0)) v := by
    have hSR_ae := (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mp hSR
    have hne_vh : ∀ᵐ v ∂volume, v ≠ v_hat := by simp [ae_iff, measure_singleton]
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hSR_ae, hne_vh] with v hvSR hvvh hmem hpos0
    have hv_a : M.a ≤ v := (le_max_right _ _).trans (hv_hat_mem.1.trans hmem.1)
    have hv_Icc : v ∈ Icc M.a 1 := ⟨hv_a, hmem.2⟩
    have hv_gt_vh : v_hat < v := lt_of_le_of_ne hmem.1 (Ne.symm hvvh)
    have hle_σ : sigma M mech ρ hρ0 hρ1.le θ v ≤ 0 := hle_above v ⟨hv_gt_vh, hmem.2⟩
    have hge_sr := hvSR hv_Icc 0 (rivalIdx M) hpos0
    simp only [unilateralProfile, ite_true,
      ite_eq_right_iff.mpr (fun h => absurd h (rivalIdx_ne_zero M))] at hge_sr
    rw [prop2_rival_surplus_eq M mech ρ hρ0 hρ1.le hSR (rivalIdx_ne_zero M)
      (M.ha0.trans hv_a) hmem.2] at hge_sr
    unfold sigma srivOf at hle_σ
    unfold srivOf at hge_sr
    linarith
  -- 6. `hx_above`
  have hx_above : ∀ᵐ v ∂(volume.restrict (Icc v_hat 1)),
      0 < θ.θ 0 v → alloc M mech (effDist M θ 0) v = (FrivOf M (effDist M θ 0) v) ^ (M.n - 1) := by
    have hhs_ae := (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mp hs_above
    have hne_vh : ∀ᵐ (v : ℝ) ∂volume, v ≠ v_hat := by simp [ae_iff, measure_singleton]
    have hne_1 : ∀ᵐ (v : ℝ) ∂volume, v ≠ (1 : ℝ) := by simp [ae_iff, measure_singleton]
    have hnot_disc := int_ae_not_mech_endpoints mech
    have hFriv_cont : ContinuousOn (FrivOf M (effDist M θ 0)) (Icc ρ 1) := by
      refine ((effDist_continuousOn θ (rivalIdx M)).mono Icc_subset_Iic_self).congr ?_
      intro u hu
      exact (hsym (rivalIdx M) (rivalIdx_ne_zero M) u hu).symm
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hhs_ae, hne_vh, hne_1, hnot_disc] with v hv_eq hvvh hv1 hvdisc hmem hpos0
    have hv_gt_vh : v_hat < v := lt_of_le_of_ne hmem.1 (Ne.symm hvvh)
    have hv_lt_1 : v < 1 := lt_of_le_of_ne hmem.2 hv1
    have hv_gt_ρ : ρ < v := lt_of_le_of_lt hρ_le_vhat hv_gt_vh
    have hσ_v : sigma M mech ρ hρ0 hρ1.le θ v = 0 := by
      unfold sigma srivOf; linarith [hv_eq hmem hpos0]
    have hmax : IsLocalMax (sigma M mech ρ hρ0 hρ1.le θ) v := by
      rw [IsLocalMax, IsMaxFilter]
      filter_upwards [Ioo_mem_nhds hv_gt_vh hv_lt_1] with u hu
      rw [hσ_v]
      exact hle_above u ⟨hu.1, hu.2.le⟩
    obtain ⟨U, hU_open, hvU, hU_cont⟩ :=
      int_alloc_continuousOn_nhds mech (effDist_continuousOn θ 0) hv_lt_1 hvdisc.1 hvdisc.2
    have hx1_int : IntervalIntegrable (alloc M mech (effDist M θ 0)) volume 0 v := by
      have hmono := vs_alloc_monotoneOn M mech (effDist M θ 0)
        (vs_effDist_monotoneOn θ 0) (fun x hx => effDist_nonneg θ 0 hx)
      have hv0 : 0 ≤ v := hρ0.trans hv_gt_ρ.le
      exact (hmono.mono (by rw [uIcc_of_le hv0]; intro u hu; exact hu.2.trans hv_lt_1.le)).intervalIntegrable
    have hderiv1 : HasDerivAt (surplus M mech (effDist M θ 0))
        (alloc M mech (effDist M θ 0) v) v := by
      unfold surplus
      exact intervalIntegral.integral_hasDerivAt_right hx1_int
        (hU_cont.stronglyMeasurableAtFilter hU_open v hvU)
        (hU_cont.continuousAt (hU_open.mem_nhds hvU))
    have hxr_contOn : ContinuousOn (alloc M (SPA ρ hρ0 hρ1.le) (FrivOf M (effDist M θ 0))) (Ioo ρ 1) :=
      int_alloc_SPA_continuousOn hρ0 hρ1.le hFriv_cont
    have hxr_int : IntervalIntegrable (alloc M (SPA ρ hρ0 hρ1.le) (FrivOf M (effDist M θ 0))) volume 0 v := by
      have hFriv_mono : MonotoneOn (effDist M θ (rivalIdx M)) (Iic 1) :=
        vs_effDist_monotoneOn θ (rivalIdx M)
      have hmono := vs_alloc_monotoneOn M (SPA ρ hρ0 hρ1.le) (effDist M θ (rivalIdx M))
        hFriv_mono (fun x hx => effDist_nonneg θ (rivalIdx M) hx)
      have hv0 : 0 ≤ v := hρ0.trans hv_gt_ρ.le
      have hint_j : IntervalIntegrable (alloc M (SPA ρ hρ0 hρ1.le) (effDist M θ (rivalIdx M))) volume 0 v :=
        (hmono.mono (by rw [uIcc_of_le hv0]; intro u hu; exact hu.2.trans hv_lt_1.le)).intervalIntegrable
      refine hint_j.congr_ae ?_
      change ∀ᵐ t ∂(volume.restrict (uIoc 0 v)),
        alloc M (SPA ρ hρ0 hρ1.le) (effDist M θ (rivalIdx M)) t =
          alloc M (SPA ρ hρ0 hρ1.le) (FrivOf M (effDist M θ 0)) t
      rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
      have hne_ρ : ∀ᵐ (t : ℝ) ∂volume, t ≠ ρ := by simp [ae_iff, measure_singleton]
      filter_upwards [hne_ρ] with t htρ ht
      rw [uIoc_of_le hv0] at ht
      by_cases ht_lt : t < ρ
      · rw [alloc_SPA, alloc_SPA, ite_eq_left_iff.mpr (fun h => absurd ht_lt h),
            ite_eq_left_iff.mpr (fun h => absurd ht_lt h)]
      · push Not at ht_lt
        rw [alloc_SPA, alloc_SPA, ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr ht_lt)),
            ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr ht_lt)),
            hsym (rivalIdx M) (rivalIdx_ne_zero M) t ⟨ht_lt, ht.2.trans hv_lt_1.le⟩]
    have hderiv_riv : HasDerivAt (srivOf M ρ hρ0 hρ1.le (effDist M θ 0))
        ((FrivOf M (effDist M θ 0) v) ^ (M.n - 1)) v := by
      have h1 : HasDerivAt (srivOf M ρ hρ0 hρ1.le (effDist M θ 0))
          (alloc M (SPA ρ hρ0 hρ1.le) (FrivOf M (effDist M θ 0)) v) v := by
        unfold srivOf surplus
        exact intervalIntegral.integral_hasDerivAt_right hxr_int
          (hxr_contOn.stronglyMeasurableAtFilter isOpen_Ioo v ⟨hv_gt_ρ, hv_lt_1⟩)
          (hxr_contOn.continuousAt (Ioo_mem_nhds hv_gt_ρ hv_lt_1))
      rwa [alloc_SPA, ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr hv_gt_ρ.le))] at h1
    have hderiv_σ : HasDerivAt (sigma M mech ρ hρ0 hρ1.le θ)
        (alloc M mech (effDist M θ 0) v - (FrivOf M (effDist M θ 0) v) ^ (M.n - 1)) v :=
      hderiv1.sub hderiv_riv
    have hzero := hmax.hasDerivAt_eq_zero hderiv_σ
    linarith
  exact
    { j0 := 0
      θ := θ
      F_riv := FrivOf M (effDist M θ 0)
      hriv_symm := hsym
      v_hat := v_hat
      hv_hat_mem := hv_hat_mem
      hρ_le_vhat := hρ_le_vhat
      hθ_below_vhat := hae_below_vhat
      hθ_below_r := hθ_below_r
      hs_below := hs_below
      hs_vhat_eq := hs_vhat_eq
      hs_above := hs_above
      hx_above := hx_above }

/-- Helper: when `ρ ≤ mech.r`, the continuation produced by `unilateralContinuation_of_isSR`
has `v_hat = v_bar` (empty initial strict-preference segment). -/
lemma int_v_hat_eq_v_bar_of_rho_le_r (M : Market) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (mech : HierarchicalMech) (θ : VisitStrategy M)
    (hSR : IsSR M (unilateralProfile M mech ρ hρ0 hρ1.le) θ)
    (hρr : ρ ≤ mech.r) :
    (unilateralContinuation_of_isSR M ρ hρ0 hρ1 mech θ hSR).v_hat =
      (unilateralContinuation_of_isSR M ρ hρ0 hρ1 mech θ hSR).v_bar := by
  let C := unilateralContinuation_of_isSR M ρ hρ0 hρ1 mech θ hSR
  have hle : C.v_bar ≤ C.v_hat := C.v_bar_le_v_hat
  by_contra hne
  have hlt : C.v_bar < C.v_hat := lt_of_le_of_ne hle (Ne.symm hne)
  have hinit := (prop2_sigma_pos_initial M mech ρ hρ0 hρ1.le hSR).2
  have hrlt : mech.r < ρ := hinit.choose_spec.2.2.2.2.1 hlt
  linarith

/-- Helper: symmetric `SPA(ρ)^m` revenue under `uniformVisit M` equals
`pathRev M P.P ρ q_ρ q_ρ 0 id`, where `q_ρ = (1 - M.F (max ρ M.a)) / M.m`. -/
lemma int_sellerRev_symmetric_SPA (M : Market) (P : M.InverseDemand)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    let q_ρ := (1 - M.F (max ρ M.a)) / (M.m : ℝ)
    sellerRev M (SPA ρ hρ0 hρ1.le) (uniformVisit M) 0 =
      pathRev M P.P ρ q_ρ q_ρ 0 id := by
  intro q_ρ
  have hprof : unilateralProfile M (SPA ρ hρ0 hρ1.le) ρ hρ0 hρ1.le =
      fun _ => SPA ρ hρ0 hρ1.le := by
    ext j; simp [unilateralProfile]
  have hSR : IsSR M (unilateralProfile M (SPA ρ hρ0 hρ1.le) ρ hρ0 hρ1.le) (uniformVisit M) := by
    rw [hprof]; exact (prop1_symmetric M ρ hρ0 hρ1.le).1
  let C := unilateralContinuation_of_isSR M ρ hρ0 hρ1 (SPA ρ hρ0 hρ1.le) (uniformVisit M) hSR
  have hvh : C.v_hat = C.v_bar :=
    int_v_hat_eq_v_bar_of_rho_le_r M ρ hρ0 hρ1 (SPA ρ hρ0 hρ1.le) (uniformVisit M) hSR le_rfl
  have hvbar : C.v_bar = max ρ M.a := by
    show max (min ρ ρ) M.a = max ρ M.a
    rw [min_self]
  have hmax_le1 : max ρ M.a ≤ 1 := max_le hρ1.le M.ha1.le
  have hF1 : ∀ v ≤ 1, C.F1 v = M.A v := fun v hv =>
    effDist_uniformVisit M 0 hv
  have hT : ∀ v ≤ 1, C.T v = (1 - M.F v) / (M.m : ℝ) := fun v hv => by
    show 1 - C.F1 v = (1 - M.F v) / (M.m : ℝ)
    rw [hF1 v hv]; unfold Market.A; ring
  have hq : ∀ v ∈ Icc ρ 1, C.q v = (1 - M.F v) / (M.m : ℝ) := fun v hv => by
    have hsym := C.hriv_symm (rivalIdx M) (rivalIdx_ne_zero M) v hv
    have heq : C.F_riv v = effDist M (uniformVisit M) (rivalIdx M) v := hsym.symm
    show 1 - C.F_riv v = (1 - M.F v) / (M.m : ℝ)
    rw [heq, effDist_uniformVisit M (rivalIdx M) hv.2]; unfold Market.A; ring
  have ht0_eq : C.t0 = q_ρ := by
    show C.T C.v_bar = q_ρ
    rw [hvbar, hT (max ρ M.a) hmax_le1]
  have hq0_eq : C.q0 = q_ρ := by
    show C.q C.v_hat = q_ρ
    rw [hvh, hvbar, hq (max ρ M.a) ⟨le_max_left _ _, hmax_le1⟩]
  have hell_eq : C.ell = 0 := (lemmaB1_indifferent C hvh).1
  have ht_id : ∀ qval ∈ Icc (0 : ℝ) C.q0, C.t qval = qval := by
    intro qval hqv
    have hspec := C.vOfQ_spec hqv
    have hv_ρ : ρ ≤ C.vOfQ qval := C.hρ_le_vhat.trans hspec.1.1
    show C.T (C.vOfQ qval) = qval
    rw [hT _ hspec.1.2, ← hq _ ⟨hv_ρ, hspec.1.2⟩, hspec.2]
  have hrev := (prop3_quantity_path_rev C P).1
  change sellerRev M (SPA ρ hρ0 hρ1.le) (uniformVisit M) 0 =
    pathRev M P.P ρ C.q0 C.t0 C.ell C.t at hrev
  rw [hrev]
  unfold pathRev
  rw [hq0_eq, ht0_eq, hell_eq]
  congr 1; congr 1
  apply intervalIntegral.integral_congr
  intro qval hqv
  have hq_nn : 0 ≤ q_ρ := div_nonneg (sub_nonneg.mpr (M.F_mem_Icc_Iic hmax_le1).2) M.m_pos_real.le
  rw [uIcc_of_le hq_nn] at hqv
  have hqv' : qval ∈ Icc (0 : ℝ) C.q0 := by rwa [hq0_eq]
  dsimp only
  rw [ht_id qval hqv', id_eq]

/-- In a covered market (`0 < M.a`), symmetric `SPA(ρ*)^m` revenue under `uniformVisit M`
equals `baselineRev M P.P`. -/
lemma int_sellerRev_symmetric_rhoStar (M : Market) (ha : 0 < M.a) (P : M.InverseDemand) :
    sellerRev M (SPA M.rhoStar M.rhoStar_nonneg (int_rhoStar_lt_one M).le) (uniformVisit M) 0 =
      baselineRev M P.P := by
  have hρa : M.rhoStar < M.a := M.rhoStar_lt_a ha
  have h := int_sellerRev_symmetric_SPA M P M.rhoStar M.rhoStar_nonneg (int_rhoStar_lt_one M)
  have hq : (1 - M.F (max M.rhoStar M.a)) / (M.m : ℝ) = 1 / (M.m : ℝ) := by
    rw [max_eq_right hρa.le, M.hF_a, sub_zero]
  simpa only [hq, baselineRev] using h

end IsSRToContinuation

/-! ### Part 2: End-to-End Theorem 2 (Covered Markets) -/

section EndToEndTheorem2

/-- `Cournot.convexityGap` and `CoveredMarkets.cm_convexityGap` are identical. -/
lemma int_convexityGap_eq (n : ℕ) (q0 t0 : ℝ) :
    convexityGap n q0 t0 = cm_convexityGap n q0 t0 := rfl

/-- **End-to-End Theorem 2 (Covered Markets)**:
In any covered market (`0 < M.a`) with nondecreasing Cournot marginal revenue `M.psi` on
`[M.a, 1]` and `0 ≤ M.psi M.a`, for EVERY hierarchical mechanism deviation `mech : HierarchicalMech`
and EVERY sequentially rational continuation `θ : VisitStrategy M` against rivals at `SPA(ρ*)`,
seller `0`'s expected revenue `sellerRev` is at most the symmetric equilibrium revenue under
`SPA(ρ*)^m` and `uniformVisit M`. -/
theorem end_to_end_theorem2_covered_markets (M : Market) (ha : 0 < M.a)
    (hpsi_mono : MonotoneOn M.psi (Icc M.a 1))
    (hpsi_a : 0 ≤ M.psi M.a)
    (mech : HierarchicalMech) (θ : VisitStrategy M)
    (hSR : IsSR M (unilateralProfile M mech M.rhoStar M.rhoStar_nonneg (int_rhoStar_lt_one M).le) θ) :
    sellerRev M mech θ 0 ≤
      sellerRev M (SPA M.rhoStar M.rhoStar_nonneg (int_rhoStar_lt_one M).le) (uniformVisit M) 0 := by
  obtain ⟨P⟩ := M.exists_inverseDemand
  have hρ0 : 0 ≤ M.rhoStar := M.rhoStar_nonneg
  have hρa : M.rhoStar < M.a := M.rhoStar_lt_a ha
  have hρ1 : M.rhoStar < 1 := int_rhoStar_lt_one M
  let C := unilateralContinuation_of_isSR M M.rhoStar hρ0 hρ1 mech θ hSR
  have hrev := prop3_quantity_path_rev C P
  have hbase := int_sellerRev_symmetric_rhoStar M ha P
  change sellerRev M mech θ 0 = pathRev M P.P M.rhoStar C.q0 C.t0 C.ell C.t ∧ 0 ≤ C.ell at hrev
  rw [hrev.1, hbase]
  -- Market clearing at the bottom type `v_bar = M.a`: `t0 + (m - 1) * q0 = 1`
  have hvbar_a : C.v_bar = M.a := by
    show max (min mech.r M.rhoStar) M.a = M.a
    exact max_eq_right ((min_le_right _ _).trans hρa.le)
  have hqa_eq : C.q M.a = C.q0 := by
    have hFriv_a := C.F_riv_const_on_rho_vhat ⟨hρa.le, hvbar_a ▸ C.v_bar_le_v_hat⟩
    show 1 - C.F_riv M.a = C.q0
    rw [hFriv_a]; ring
  have hmass : C.t0 + ((M.m : ℝ) - 1) * C.q0 = 1 := by
    have hm := C.mass_conservation (left_mem_Icc.mpr M.ha1.le) hρa.le
    rw [M.hF_a, sub_zero, hqa_eq] at hm
    have ht0_eq : C.t0 = C.T M.a := by show C.T C.v_bar = C.T M.a; rw [hvbar_a]
    linarith
  have hB1 := lemmaB1_rent_lower_bound C hρa
  rw [int_convexityGap_eq] at hB1
  exact theorem2_covered_markets M ha P hpsi_mono hpsi_a
    C.t0_mem_Icc.1 C.t0_mem_Icc.2 hmass hrev.2
    C.t_monotoneOn (fun q hq => C.t_mem_Icc hq) (prop3_border_q C) hB1.2 hB1.1

end EndToEndTheorem2

/-! ### Part 3: End-to-End Example 1 (Non-Regular Duopoly Equilibrium) -/

section EndToEndExample1

/-- **End-to-End Example 1**:
In the non-regular truncated Pareto duopoly (`m = 2`, `a = 1/2`, `example1_pareto_market n hn`),
for every `n ≥ 2`:
1. A monopolist strictly irons (`ψ_1` is strictly decreasing on `[1/2, 1/2 + 91/1782]` while
   `ψ_1(1/2) > 0`).
2. Virág's candidate reserve is `ρ* = (n - 1) / (2n)`.
3. For EVERY hierarchical mechanism `mech` and EVERY sequentially rational continuation `θ`
   against the rival at `SPA(ρ*)`, seller `0`'s expected revenue `sellerRev` is at most the
   symmetric `SPA(ρ*)^2` equilibrium revenue under `uniformVisit`. -/
theorem end_to_end_example1 (n : ℕ) (hn : 2 ≤ n) :
    let M := (example1_pareto_market n hn).toMarket
    StrictAntiOn M.psi1 (Icc (1 / 2 : ℝ) (1 / 2 + 91 / 1782)) ∧
    0 < M.psi1 (1 / 2) ∧
    M.rhoStar = ((n : ℝ) - 1) / (2 * (n : ℝ)) ∧
    (∀ (mech : HierarchicalMech) (θ : VisitStrategy M),
      IsSR M (unilateralProfile M mech M.rhoStar M.rhoStar_nonneg (int_rhoStar_lt_one M).le) θ →
      sellerRev M mech θ 0 ≤
        sellerRev M (SPA M.rhoStar M.rhoStar_nonneg (int_rhoStar_lt_one M).le) (uniformVisit M) 0) := by
  intro M
  have hduo := example1_duopoly_cournot n hn
  have ha : 0 < M.a := by show (0 : ℝ) < 1 / 2; norm_num
  have hpsi_mono : MonotoneOn M.psi (Icc M.a 1) := hduo.1.monotoneOn
  have hpsi_a : 0 ≤ M.psi M.a := hduo.2.2.1.le
  refine ⟨example1_monopolist_irons n hn, (example1_psi1_pos_at_half n hn).2,
    example1_rhoStar n hn, ?_⟩
  intro mech θ hSR
  exact end_to_end_theorem2_covered_markets M ha hpsi_mono hpsi_a mech θ hSR

end EndToEndExample1

/-! ### Part 4: End-to-End Theorem 5(ii) (Many-Buyers Sharpness of `m + 1`) -/

section EndToEndTheorem5

/-- Helper: `bandQStar` from `VisitStage.lean` equals `qStar` from `Sharpness.lean`
at the corresponding band quantities `q_lo = (1 - F v₄) / m`, `q_hi = (1 - F v₁) / m`. -/
lemma int_bandQStar_eq_qStar (M : Market) (v₁ v₄ : ℝ) :
    bandQStar M v₁ v₄ =
      qStar M.n ((1 - M.F v₄) / (M.m : ℝ)) ((1 - M.F v₁) / (M.m : ℝ)) := by
  unfold bandQStar qStar Market.A
  rfl

/-- Helper: `q ↦ M.cournotRev P.P c q * M.W q` is `IntervalIntegrable` on `[a, b] ⊆ [0, 1/m]`
whenever `c ∈ [0, 1/m]`. -/
private lemma int_cournotRev_const_intervalIntegrable (M : Market) (P : M.InverseDemand)
    {c a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1 / (M.m : ℝ))
    (hc0 : 0 ≤ c) (hc : c ≤ 1 / (M.m : ℝ)) :
    IntervalIntegrable (fun q => M.cournotRev P.P c q * M.W q) volume a b := by
  have hm_pos : (0 : ℝ) < M.m := M.m_pos_real
  have hm1_nn : (0 : ℝ) ≤ (M.m : ℝ) - 1 := M.m_sub_one_pos_real.le
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le hab]
  apply ContinuousOn.mul
  · show ContinuousOn (fun q => c * P.P (c + ((M.m : ℝ) - 1) * q)) (Icc a b)
    apply ContinuousOn.mul continuousOn_const
    refine P.hP_cont.comp (continuousOn_const.add (continuousOn_const.mul continuousOn_id)) ?_
    intro q hq
    have hq_nn : 0 ≤ q := ha0.trans hq.1
    have hq_le : q ≤ 1 / (M.m : ℝ) := hq.2.trans hb
    have h1 : (M.m : ℝ) * (1 / (M.m : ℝ)) = 1 := by field_simp [hm_pos.ne']
    exact ⟨add_nonneg hc0 (mul_nonneg hm1_nn hq_nn),
      calc c + ((M.m : ℝ) - 1) * q
          ≤ 1 / (M.m : ℝ) + ((M.m : ℝ) - 1) * (1 / (M.m : ℝ)) :=
            add_le_add hc (mul_le_mul_of_nonneg_left hq_le hm1_nn)
        _ = (M.m : ℝ) * (1 / (M.m : ℝ)) := by ring
        _ = 1 := h1⟩
  · show ContinuousOn (fun q => (M.n : ℝ) * ((M.n : ℝ) - 1) * (1 - q) ^ (M.n - 2)) (Icc a b)
    exact (continuous_const.mul ((continuous_const.sub continuous_id).pow _)).continuousOn

/-- Helper: `q ↦ M.cournotRev P.P q q * M.W q` is `IntervalIntegrable` on `[a, b] ⊆ [0, 1/m]`. -/
private lemma int_cournotRev_diag_intervalIntegrable (M : Market) (P : M.InverseDemand)
    {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1 / (M.m : ℝ)) :
    IntervalIntegrable (fun q => M.cournotRev P.P q q * M.W q) volume a b := by
  have hm_pos : (0 : ℝ) < M.m := M.m_pos_real
  have hm1_nn : (0 : ℝ) ≤ (M.m : ℝ) - 1 := M.m_sub_one_pos_real.le
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le hab]
  apply ContinuousOn.mul
  · show ContinuousOn (fun q => q * P.P (q + ((M.m : ℝ) - 1) * q)) (Icc a b)
    apply ContinuousOn.mul continuousOn_id
    refine P.hP_cont.comp (continuousOn_id.add (continuousOn_const.mul continuousOn_id)) ?_
    intro q hq
    have hq_nn : 0 ≤ q := ha0.trans hq.1
    have hq_le : q ≤ 1 / (M.m : ℝ) := hq.2.trans hb
    have h1 : (M.m : ℝ) * (1 / (M.m : ℝ)) = 1 := by field_simp [hm_pos.ne']
    exact ⟨add_nonneg hq_nn (mul_nonneg hm1_nn hq_nn),
      calc q + ((M.m : ℝ) - 1) * q
          = (M.m : ℝ) * q := by ring
        _ ≤ (M.m : ℝ) * (1 / (M.m : ℝ)) := mul_le_mul_of_nonneg_left hq_le hm_pos.le
        _ = 1 := h1⟩
  · show ContinuousOn (fun q => (M.n : ℝ) * ((M.n : ℝ) - 1) * (1 - q) ^ (M.n - 2)) (Icc a b)
    exact (continuous_const.mul ((continuous_const.sub continuous_id).pow _)).continuousOn

/-- **Exact Single-Band Revenue Bridge (`sellerRev` difference = `singleBandGain`)**:
For any interior band `[v₁, v₄] ⊂ (max ρ a, 1)` induced by a single-pool deviation
`singlePoolMech ρ α β` and an SR continuation `θ`, seller `0`'s exact revenue gain over
symmetric `SPA(ρ)^m` equals `singleBandGain M P.P q_lo q_hi`. -/
theorem int_sellerRev_single_band_eq_singleBandGain (M : Market) (P : M.InverseDemand)
    {ρ α β v₁ v₄ : ℝ} (hρ0 : 0 ≤ ρ) (hρα : ρ ≤ α) (hαβ : α < β) (hβ1 : β ≤ 1)
    {θ : VisitStrategy M}
    (hSR : IsSR M (unilateralProfile M (singlePoolMech ρ α β hρ0 hρα hαβ hβ1) ρ hρ0
      (hρα.trans (hαβ.le.trans hβ1))) θ)
    (hband : IsInteriorBand M ρ α β θ v₁ v₄) :
    let hρ1 : ρ ≤ 1 := hρα.trans (hαβ.le.trans hβ1)
    sellerRev M (singlePoolMech ρ α β hρ0 hρα hαβ hβ1) θ 0 -
      sellerRev M (SPA ρ hρ0 hρ1) (uniformVisit M) 0 =
        singleBandGain M P.P ((1 - M.F v₄) / (M.m : ℝ)) ((1 - M.F v₁) / (M.m : ℝ)) := by
  intro hρ1
  set mech := singlePoolMech ρ α β hρ0 hρα hαβ hβ1
  set q_lo := (1 - M.F v₄) / (M.m : ℝ)
  set q_hi := (1 - M.F v₁) / (M.m : ℝ)
  set q_ρ := (1 - M.F (max ρ M.a)) / (M.m : ℝ)
  set q_s := bandQStar M v₁ v₄
  have hmax_lt_v1 : max ρ M.a < v₁ := hband.1
  have hv14 : v₁ < v₄ := hband.2.1
  have hv4_lt1 : v₄ < 1 := hband.2.2.1
  have hρ_lt1 : ρ < 1 := lt_of_le_of_lt (le_max_left ρ M.a) (hmax_lt_v1.trans (hv14.trans hv4_lt1))
  have ha_lt_v1 : M.a < v₁ := lt_of_le_of_lt (le_max_right ρ M.a) hmax_lt_v1
  have hmax_le1 : max ρ M.a ≤ 1 := max_le hρ_lt1.le M.ha1.le
  -- Construct `UnilateralContinuation` and show `v_hat = v_bar = max ρ a`, `ell = 0`, `t0 = q0 = q_ρ`
  let C := unilateralContinuation_of_isSR M ρ hρ0 hρ_lt1 mech θ hSR
  have hvh : C.v_hat = C.v_bar :=
    int_v_hat_eq_v_bar_of_rho_le_r M ρ hρ0 hρ_lt1 mech θ hSR le_rfl
  have hvbar : C.v_bar = max ρ M.a := by
    show max (min ρ ρ) M.a = max ρ M.a; rw [min_self]
  have hell : C.ell = 0 := (lemmaB1_indifferent C hvh).1
  have hF1_off : ∀ v ∈ Icc (max ρ M.a) v₁ ∪ Icc v₄ 1, C.F1 v = M.A v := hband.2.2.2.2.2.1
  have hFriv_of_A : ∀ v, C.F1 v = M.A v → C.F_riv v = M.A v := by
    intro v hv
    show FrivOf M (effDist M θ 0) v = M.A v
    change effDist M θ 0 v = M.A v at hv
    unfold FrivOf Market.A
    unfold Market.A at hv
    rw [hv]
    have hm : (M.m : ℝ) ≠ 0 := M.m_pos_real.ne'
    have hm1 : (M.m : ℝ) - 1 ≠ 0 := M.m_sub_one_pos_real.ne'
    field_simp [hm, hm1]; ring
  have hF1_max : C.F1 (max ρ M.a) = M.A (max ρ M.a) :=
    hF1_off (max ρ M.a) (Or.inl (left_mem_Icc.mpr hmax_lt_v1.le))
  have ht0_eq : C.t0 = q_ρ := by
    show 1 - C.F1 C.v_bar = q_ρ
    rw [hvbar, hF1_max]; unfold Market.A; ring
  have hq0_eq : C.q0 = q_ρ := by
    show 1 - C.F_riv C.v_hat = q_ρ
    rw [hvh, hvbar, hFriv_of_A _ hF1_max]; unfold Market.A; ring
  -- Extract band coordinates `(v₂, v₃)` from `lemma1_band_structure`
  have hstruct := lemma1_band_structure M hρ0 hρα hαβ hβ1 hSR hband
  obtain ⟨hF1_v1, hF1_v4, _, _, v₂, v₃, hv1α, hαv2, hv23, hv3β, hβv4,
    hθ12, _, hθ34, _, hFriv23, _, _, _, _, _, _, _⟩ := hstruct
  have hv12 : v₁ < v₂ := hv1α.trans hαv2
  have hv34 : v₃ < v₄ := hv3β.trans hβv4
  have hq_bds := bandQStar_bounds M ha_lt_v1.le hv14 hv4_lt1.le
  have hq_lo_pos : 0 < q_lo := by
    have hFlt : M.F v₄ < 1 := by
      rw [← M.hF_1]; exact M.F_strictMonoOn ⟨(ha_lt_v1.trans hv14).le, hv4_lt1.le⟩ (right_mem_Icc.mpr M.ha1.le) hv4_lt1
    exact div_pos (sub_pos.mpr hFlt) M.m_pos_real
  have hq_lo_lt_qs : q_lo < q_s := hq_bds.2.2.1
  have hq_s_lt_hi : q_s < q_hi := hq_bds.2.2.2
  have hq_hi_lt_qρ : q_hi < q_ρ := by
    have hFlt : M.F (max ρ M.a) < M.F v₁ :=
      M.F_strictMonoOn ⟨le_max_right _ _, hmax_le1⟩ ⟨ha_lt_v1.le, (hv14.trans hv4_lt1).le⟩ hmax_lt_v1
    exact div_lt_div_of_pos_right (sub_lt_sub_left hFlt 1) M.m_pos_real
  have hq_ρ_le_inv_m : q_ρ ≤ 1 / (M.m : ℝ) := by
    have hFnn : 0 ≤ M.F (max ρ M.a) := (M.F_mem_Icc_Iic hmax_le1).1
    exact div_le_div_of_nonneg_right (by linarith) M.m_pos_real.le
  -- Compute `C.T` and `C.q` on the subintervals
  have hT_off : ∀ v ∈ Icc (max ρ M.a) v₁ ∪ Icc v₄ 1, C.T v = (1 - M.F v) / (M.m : ℝ) := by
    intro v hv; show 1 - C.F1 v = _; rw [hF1_off v hv]; unfold Market.A; ring
  have hq_off : ∀ v ∈ Icc (max ρ M.a) v₁ ∪ Icc v₄ 1, C.q v = (1 - M.F v) / (M.m : ℝ) := by
    intro v hv; show 1 - C.F_riv v = _; rw [hFriv_of_A v (hF1_off v hv)]; unfold Market.A; ring
  have hF1_const_on : ∀ x y : ℝ, x ≤ y → y ≤ 1 →
      (∀ᵐ u ∂(volume.restrict (Icc x y)), θ.θ 0 u = 0) →
      ∀ v ∈ Icc x y, effDist M θ 0 v = effDist M θ 0 x := by
    intro x y hxy hy1 hae v hv
    have hsub := effDist_sub θ 0 (hxy.trans hy1) (hv.2.trans hy1)
    have hzero : ∫ u in x..v, θ.θ 0 u * M.f u = 0 := by
      have hae_u := (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mp hae
      have hcongr : ∫ u in x..v, θ.θ 0 u * M.f u = ∫ _ in x..v, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hae_u] with u hu hmem
        rw [uIoc_of_le hv.1] at hmem
        rw [hu ⟨hmem.1.le, hmem.2.trans hv.2⟩, zero_mul]
      rw [hcongr]; simp
    linarith
  have hT_12 : ∀ v ∈ Icc v₁ v₂, C.T v = q_hi := by
    intro v hv
    have h1 := hF1_const_on v₁ v₂ hv12.le ((hv23.trans hv34).trans hv4_lt1).le hθ12 v hv
    show 1 - effDist M θ 0 v = q_hi
    rw [h1, hF1_v1]; unfold Market.A; ring
  have hT_34 : ∀ v ∈ Icc v₃ v₄, C.T v = q_lo := by
    intro v hv
    have h1 := hF1_const_on v₃ v₄ hv34.le hv4_lt1.le hθ34 v hv
    have h2 := hF1_const_on v₃ v₄ hv34.le hv4_lt1.le hθ34 v₄ (right_mem_Icc.mpr hv34.le)
    show 1 - effDist M θ 0 v = q_lo
    rw [h1, ← h2, hF1_v4]; unfold Market.A; ring
  have hq_v4 : C.q v₄ = q_lo := hq_off v₄ (Or.inr (left_mem_Icc.mpr hv4_lt1.le))
  have hq_v1 : C.q v₁ = q_hi := hq_off v₁ (Or.inl (right_mem_Icc.mpr hmax_lt_v1.le))
  have hq_v2 : C.q v₂ = q_s := by
    have hρv2 : ρ ≤ v₂ := (le_max_left ρ M.a).trans (hmax_lt_v1.le.trans hv12.le)
    have hv2_le1 : v₂ ≤ 1 := ((hv23.trans hv34).trans hv4_lt1).le
    have hsym := C.hriv_symm (rivalIdx M) (rivalIdx_ne_zero M) v₂ ⟨hρv2, hv2_le1⟩
    have heq : C.F_riv v₂ = effDist M θ (rivalIdx M) v₂ := hsym.symm
    show 1 - C.F_riv v₂ = q_s
    rw [heq, hFriv23 v₂ (left_mem_Icc.mpr hv23.le)]; ring
  have hq_v3 : C.q v₃ = q_s := by
    have hρv3 : ρ ≤ v₃ := (le_max_left ρ M.a).trans (hmax_lt_v1.le.trans (hv12.le.trans hv23.le))
    have hv3_le1 : v₃ ≤ 1 := (hv34.trans hv4_lt1).le
    have hsym := C.hriv_symm (rivalIdx M) (rivalIdx_ne_zero M) v₃ ⟨hρv3, hv3_le1⟩
    have heq : C.F_riv v₃ = effDist M θ (rivalIdx M) v₃ := hsym.symm
    show 1 - C.F_riv v₃ = q_s
    rw [heq, hFriv23 v₃ (right_mem_Icc.mpr hv23.le)]; ring
  -- Helper memberships in `Icc C.v_hat 1`
  have hv1_mem : v₁ ∈ Icc C.v_hat 1 := ⟨by rw [hvh, hvbar]; exact hmax_lt_v1.le, (hv14.trans hv4_lt1).le⟩
  have hv2_mem : v₂ ∈ Icc C.v_hat 1 := ⟨hv1_mem.1.trans hv12.le, ((hv23.trans hv34).trans hv4_lt1).le⟩
  have hv3_mem : v₃ ∈ Icc C.v_hat 1 := ⟨hv2_mem.1.trans hv23.le, (hv34.trans hv4_lt1).le⟩
  have hv4_mem : v₄ ∈ Icc C.v_hat 1 := ⟨hv3_mem.1.trans hv34.le, hv4_lt1.le⟩
  -- Compute `C.t q` on each of the 4 open intervals
  have ht_seg1 : ∀ q ∈ Ioo (0 : ℝ) q_lo, C.t q = q := by
    intro q hq
    have hq_icc : q ∈ Icc (0 : ℝ) C.q0 := ⟨hq.1.le, by rw [hq0_eq]; linarith [hq.2]⟩
    have hspec := C.vOfQ_spec hq_icc
    have hv_ge : v₄ ≤ C.vOfQ q := by
      by_contra hlt; push Not at hlt
      have hge := C.q_antitoneOn_vhat hspec.1 hv4_mem hlt.le
      rw [hspec.2, hq_v4] at hge; linarith [hq.2]
    show C.T (C.vOfQ q) = q
    rw [hT_off _ (Or.inr ⟨hv_ge, hspec.1.2⟩), ← hq_off _ (Or.inr ⟨hv_ge, hspec.1.2⟩), hspec.2]
  have ht_seg2 : ∀ q ∈ Ioo q_lo q_s, C.t q = q_lo := by
    intro q hq
    have hq_icc : q ∈ Icc (0 : ℝ) C.q0 := ⟨hq_lo_pos.le.trans hq.1.le, by rw [hq0_eq]; linarith [hq.2]⟩
    have hspec := C.vOfQ_spec hq_icc
    have hv_ge : v₃ ≤ C.vOfQ q := by
      by_contra hlt; push Not at hlt
      have hge := C.q_antitoneOn_vhat hspec.1 hv3_mem hlt.le
      rw [hspec.2, hq_v3] at hge; linarith [hq.2]
    have hv_le : C.vOfQ q ≤ v₄ := by
      by_contra hgt; push Not at hgt
      have hle := C.q_antitoneOn_vhat hv4_mem hspec.1 hgt.le
      rw [hspec.2, hq_v4] at hle; linarith [hq.1]
    exact hT_34 (C.vOfQ q) ⟨hv_ge, hv_le⟩
  have ht_seg3 : ∀ q ∈ Ioo q_s q_hi, C.t q = q_hi := by
    intro q hq
    have hq_icc : q ∈ Icc (0 : ℝ) C.q0 :=
      ⟨(hq_lo_pos.trans hq_lo_lt_qs).le.trans hq.1.le, by rw [hq0_eq]; linarith [hq.2]⟩
    have hspec := C.vOfQ_spec hq_icc
    have hv_ge : v₁ ≤ C.vOfQ q := by
      by_contra hlt; push Not at hlt
      have hge := C.q_antitoneOn_vhat hspec.1 hv1_mem hlt.le
      rw [hspec.2, hq_v1] at hge; linarith [hq.2]
    have hv_le : C.vOfQ q ≤ v₂ := by
      by_contra hgt; push Not at hgt
      have hle := C.q_antitoneOn_vhat hv2_mem hspec.1 hgt.le
      rw [hspec.2, hq_v2] at hle; linarith [hq.1]
    exact hT_12 (C.vOfQ q) ⟨hv_ge, hv_le⟩
  have ht_seg4 : ∀ q ∈ Ioo q_hi q_ρ, C.t q = q := by
    intro q hq
    have hq_icc : q ∈ Icc (0 : ℝ) C.q0 :=
      ⟨(hq_lo_pos.trans (hq_lo_lt_qs.trans hq_s_lt_hi)).le.trans hq.1.le, by rw [hq0_eq]; exact hq.2.le⟩
    have hspec := C.vOfQ_spec hq_icc
    have hv_le : C.vOfQ q ≤ v₁ := by
      by_contra hgt; push Not at hgt
      have hle := C.q_antitoneOn_vhat hv1_mem hspec.1 hgt.le
      rw [hspec.2, hq_v1] at hle; linarith [hq.1]
    have hv_ge : max ρ M.a ≤ C.vOfQ q := by rw [← hvbar, ← hvh]; exact hspec.1.1
    show C.T (C.vOfQ q) = q
    rw [hT_off _ (Or.inl ⟨hv_ge, hv_le⟩), ← hq_off _ (Or.inl ⟨hv_ge, hv_le⟩), hspec.2]
  -- Continuity/integrability of the piecewise Cournot integrands
  have hcont_const : ∀ c : ℝ, ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 / (M.m : ℝ) →
      0 ≤ c → c ≤ 1 / (M.m : ℝ) →
      IntervalIntegrable (fun q => M.cournotRev P.P c q * M.W q) volume a b :=
    fun _ _ _ ha0 hab hb hc0 hc => int_cournotRev_const_intervalIntegrable M P ha0 hab hb hc0 hc
  have hcont_diag : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 / (M.m : ℝ) →
      IntervalIntegrable (fun q => M.cournotRev P.P q q * M.W q) volume a b :=
    fun _ _ ha0 hab hb => int_cournotRev_diag_intervalIntegrable M P ha0 hab hb
  -- Helper: `IntervalIntegrable` and `integral` equality from agreement on `Ioo a b`
  have hcongr_Ioo : ∀ (f g : ℝ → ℝ) (a b : ℝ), a ≤ b →
      (∀ q ∈ Ioo a b, f q = g q) → IntervalIntegrable g volume a b →
      IntervalIntegrable f volume a b ∧ ∫ q in a..b, f q = ∫ q in a..b, g q := by
    intro f g a b hab heq hg
    have hae : ∀ᵐ q ∂volume, q ∈ uIoc a b → g q = f q := by
      have hne_b : ∀ᵐ (q : ℝ) ∂volume, q ≠ b := by simp [ae_iff, measure_singleton]
      filter_upwards [hne_b] with q hqb hmem
      rw [uIoc_of_le hab] at hmem
      exact (heq q ⟨hmem.1, lt_of_le_of_ne hmem.2 hqb⟩).symm
    have hf : IntervalIntegrable f volume a b := hg.congr_ae (ae_restrict_iff' measurableSet_uIoc |>.mpr hae)
    have hint : ∫ q in a..b, f q = ∫ q in a..b, g q :=
      intervalIntegral.integral_congr_ae (by filter_upwards [hae] with q hq hm; exact (hq hm).symm)
    exact ⟨hf, hint⟩
  set f_t : ℝ → ℝ := fun q => M.cournotRev P.P (C.t q) q * M.W q
  set f_id : ℝ → ℝ := fun q => M.cournotRev P.P q q * M.W q
  have h1 := hcongr_Ioo f_t f_id 0 q_lo hq_lo_pos.le
    (fun q hq => by dsimp [f_t, f_id]; rw [ht_seg1 q hq])
    (hcont_diag 0 q_lo le_rfl hq_lo_pos.le (by linarith))
  have h2 := hcongr_Ioo f_t (fun q => M.cournotRev P.P q_lo q * M.W q) q_lo q_s hq_lo_lt_qs.le
    (fun q hq => by dsimp [f_t]; rw [ht_seg2 q hq])
    (hcont_const q_lo q_lo q_s hq_lo_pos.le hq_lo_lt_qs.le (by linarith) hq_lo_pos.le (by linarith))
  have h3 := hcongr_Ioo f_t (fun q => M.cournotRev P.P q_hi q * M.W q) q_s q_hi hq_s_lt_hi.le
    (fun q hq => by dsimp [f_t]; rw [ht_seg3 q hq])
    (hcont_const q_hi q_s q_hi (by linarith) hq_s_lt_hi.le (by linarith) (by linarith) (by linarith))
  have h4 := hcongr_Ioo f_t f_id q_hi q_ρ hq_hi_lt_qρ.le
    (fun q hq => by dsimp [f_t, f_id]; rw [ht_seg4 q hq])
    (hcont_diag q_hi q_ρ (by linarith) hq_hi_lt_qρ.le hq_ρ_le_inv_m)
  have hf_t_int : IntervalIntegrable f_t volume 0 q_ρ :=
    ((h1.1.trans h2.1).trans h3.1).trans h4.1
  have hf_id_int : IntervalIntegrable f_id volume 0 q_ρ :=
    hcont_diag 0 q_ρ le_rfl (by linarith) hq_ρ_le_inv_m
  -- Rewrite `sellerRev` difference via `prop3_quantity_path_rev` + `int_sellerRev_symmetric_SPA`
  have hrev_dev := (prop3_quantity_path_rev C P).1
  change sellerRev M mech θ 0 = pathRev M P.P ρ C.q0 C.t0 C.ell C.t at hrev_dev
  have hrev_sym := int_sellerRev_symmetric_SPA M P ρ hρ0 hρ_lt1
  dsimp only at hrev_sym
  rw [hrev_dev, hrev_sym, hq0_eq, ht0_eq, hell]
  rw [theorem1_part_i_exact_diff M P ρ q_ρ hf_t_int hf_id_int]
  -- Split the difference integral across `0 < q_lo < q_s < q_hi < q_ρ`
  have hdiff_split :
      ∫ q in (0 : ℝ)..q_ρ, (M.cournotRev P.P (C.t q) q - M.cournotRev P.P q q) * M.W q =
        (∫ q in (0 : ℝ)..q_ρ, f_t q) - (∫ q in (0 : ℝ)..q_ρ, f_id q) := by
    rw [← intervalIntegral.integral_sub hf_t_int hf_id_int]
    apply intervalIntegral.integral_congr; intro q _; dsimp [f_t, f_id]; ring
  rw [hdiff_split]
  have hsplit_t : ∫ q in (0 : ℝ)..q_ρ, f_t q =
      (∫ q in (0 : ℝ)..q_lo, f_t q) + (∫ q in q_lo..q_s, f_t q) +
      (∫ q in q_s..q_hi, f_t q) + (∫ q in q_hi..q_ρ, f_t q) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals ((h1.1.trans h2.1).trans h3.1) h4.1,
        ← intervalIntegral.integral_add_adjacent_intervals (h1.1.trans h2.1) h3.1,
        ← intervalIntegral.integral_add_adjacent_intervals h1.1 h2.1]
  have hid1 := hcont_diag 0 q_lo le_rfl hq_lo_pos.le (by linarith)
  have hid2 := hcont_diag q_lo q_s hq_lo_pos.le hq_lo_lt_qs.le (by linarith)
  have hid3 := hcont_diag q_s q_hi (by linarith) hq_s_lt_hi.le (by linarith)
  have hid4 := hcont_diag q_hi q_ρ (by linarith) hq_hi_lt_qρ.le hq_ρ_le_inv_m
  have hsplit_id : ∫ q in (0 : ℝ)..q_ρ, f_id q =
      (∫ q in (0 : ℝ)..q_lo, f_id q) + (∫ q in q_lo..q_s, f_id q) +
      (∫ q in q_s..q_hi, f_id q) + (∫ q in q_hi..q_ρ, f_id q) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals ((hid1.trans hid2).trans hid3) hid4,
        ← intervalIntegral.integral_add_adjacent_intervals (hid1.trans hid2) hid3,
        ← intervalIntegral.integral_add_adjacent_intervals hid1 hid2]
  rw [hsplit_t, hsplit_id, h1.2, h2.2, h3.2, h4.2]
  have hsub2 :
      (∫ q in q_lo..q_s, M.cournotRev P.P q_lo q * M.W q) - (∫ q in q_lo..q_s, f_id q) =
        ∫ q in q_lo..q_s, (cournotRevOf M.m P.P q_lo q - cournotRevOf M.m P.P q q) * W_of M.n q := by
    rw [← intervalIntegral.integral_sub
      (hcont_const q_lo q_lo q_s hq_lo_pos.le hq_lo_lt_qs.le (by linarith) hq_lo_pos.le (by linarith)) hid2]
    apply intervalIntegral.integral_congr; intro q _
    dsimp [f_id, Market.cournotRev, cournotRevOf, Market.W, W_of]; ring
  have hsub3 :
      (∫ q in q_s..q_hi, M.cournotRev P.P q_hi q * M.W q) - (∫ q in q_s..q_hi, f_id q) =
        ∫ q in q_s..q_hi, (cournotRevOf M.m P.P q_hi q - cournotRevOf M.m P.P q q) * W_of M.n q := by
    rw [← intervalIntegral.integral_sub
      (hcont_const q_hi q_s q_hi (by linarith) hq_s_lt_hi.le (by linarith) (by linarith) (by linarith)) hid3]
    apply intervalIntegral.integral_congr; intro q _
    dsimp [f_id, Market.cournotRev, cournotRevOf, Market.W, W_of]; ring
  have hqs_eq : q_s = qStar M.n q_lo q_hi := int_bandQStar_eq_qStar M v₁ v₄
  unfold singleBandGain singleBandGainOf
  dsimp only
  rw [← hqs_eq, ← hsub2, ← hsub3]
  ring

/-- **End-to-End Theorem 5(ii) (Many-Buyers Sharpness of `m + 1`)**:
For every `m ≥ 2` and every `X > m + 1`, there exists a `C¹` covered-market distribution
`M₀ : SmoothMarket` (with `M₀.m = m`, `0 < M₀.a`, `0 < ψ_m(a)`, and `E(v) ∈ [0, X]` everywhere
on `[a, 1]`) and a threshold `N : ℕ` such that for EVERY `n ≥ max N 2`, in the `n`-buyer market
`M_n`, there exist an explicit interior pool `(α, β) ⊂ (a, 1)` (hence `ρ*(n) < α < β < 1`) and
an explicit sequentially rational continuation `θ` for `singlePoolMech ρ*(n) α β` against rivals
at `SPA(ρ*(n))` that strictly raises seller `0`'s expected revenue `sellerRev` above symmetric
`SPA(ρ*(n))^m`! -/
theorem end_to_end_theorem5_many_buyers (m : ℕ) (hm : 2 ≤ m) {X : ℝ} (hX : (m : ℝ) + 1 < X) :
    ∃ (M₀ : SmoothMarket),
      M₀.m = m ∧ 0 < M₀.a ∧ 0 < M₀.toMarket.psi M₀.a ∧
      (∀ v ∈ Icc M₀.a 1, curvatureE M₀ v ∈ Icc 0 X) ∧
      ∃ N : ℕ, ∀ (n : ℕ) (hn : 2 ≤ n), N ≤ n →
        let M : Market := { M₀.toMarket with n := n, hn := hn }
        let hρ0 : 0 ≤ M.rhoStar := M.rhoStar_nonneg
        let hρ1 : M.rhoStar ≤ 1 := (int_rhoStar_lt_one M).le
        ∃ (α β : ℝ) (hρα : M.rhoStar ≤ α) (hαβ : α < β) (hβ1 : β ≤ 1) (θ : VisitStrategy M),
          M.a < α ∧ β < 1 ∧
          IsSR M (unilateralProfile M (singlePoolMech M.rhoStar α β hρ0 hρα hαβ hβ1)
            M.rhoStar hρ0 hρ1) θ ∧
          sellerRev M (SPA M.rhoStar hρ0 hρ1) (uniformVisit M) 0 <
            sellerRev M (singlePoolMech M.rhoStar α β hρ0 hρα hαβ hβ1) θ 0 := by
  obtain ⟨M₀, inv, q_lo, q_hi, hMm, hMa, hpsi, hE, hq_lo_pos, hq_lt, hmq_hi, N, hN⟩ :=
    theorem5_many_buyers m hm hX
  refine ⟨M₀, hMm, hMa, hpsi, hE, N, ?_⟩
  intro n hn hnN M hρ0 hρ1
  -- Transfer `inv : M₀.toMarket.InverseDemand` to `inv_n : M.InverseDemand` (same `P`)
  let inv_n : M.InverseDemand :=
    { P := inv.P
      hP_mem := inv.hP_mem
      hP_right := inv.hP_right
      hP_left := inv.hP_left
      hP_zero := inv.hP_zero
      hP_one := inv.hP_one
      hP_cont := inv.hP_cont
      hP_strictAnti := inv.hP_strictAnti
      hP_deriv_open := inv.hP_deriv_open
      hP_deriv_within := inv.hP_deriv_within }
  -- Define band endpoints `v₁ = P(m q_hi)` and `v₄ = P(m q_lo)` in `(a, 1)`
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hm)
  have hmq_lo_pos : 0 < (m : ℝ) * q_lo := mul_pos hm_pos hq_lo_pos
  have hmq_lt : (m : ℝ) * q_lo < (m : ℝ) * q_hi := mul_lt_mul_of_pos_left hq_lt hm_pos
  set v₁ := inv.P ((m : ℝ) * q_hi)
  set v₄ := inv.P ((m : ℝ) * q_lo)
  have ha_lt_v1 : M.a < v₁ := by
    change M₀.a < inv.P ((m : ℝ) * q_hi)
    rw [← inv.hP_one]
    exact inv.hP_strictAnti ⟨(hmq_lo_pos.trans hmq_lt).le, hmq_hi.le⟩ (right_mem_Icc.mpr zero_le_one) hmq_hi
  have hv14 : v₁ < v₄ :=
    inv.hP_strictAnti ⟨hmq_lo_pos.le, (hmq_lt.trans hmq_hi).le⟩
      ⟨(hmq_lo_pos.trans hmq_lt).le, hmq_hi.le⟩ hmq_lt
  have hv4_lt1 : v₄ < 1 := by
    rw [← inv.hP_zero]
    exact inv.hP_strictAnti (left_mem_Icc.mpr zero_le_one)
      ⟨hmq_lo_pos.le, (hmq_lt.trans hmq_hi).le⟩ hmq_lo_pos
  have hρa : M.rhoStar < M.a := M.rhoStar_lt_a hMa
  have hu0_lt : max M.rhoStar M.a < v₁ := by rw [max_eq_right hρa.le]; exact ha_lt_v1
  -- Construct explicit interior pool `(α, β) = bandToPool M (v₁, v₄)` and SR strategy `θ`
  obtain ⟨hρα, hαβ, hβ1, θ, hv1_lt_α, hβ_lt_v4, hSR, hband⟩ :=
    lemma1_band_to_pool_sr M hρ0 hu0_lt hv14 hv4_lt1
  set α := (bandToPool M (v₁, v₄)).1
  set β := (bandToPool M (v₁, v₄)).2
  have hrev_diff := int_sellerRev_single_band_eq_singleBandGain M inv_n hρ0 hρα hαβ hβ1 hSR hband
  have hq_lo_eq : (1 - M.F v₄) / (M.m : ℝ) = q_lo := by
    have hF4 : M.F v₄ = 1 - (m : ℝ) * q_lo :=
      inv.hP_right ((m : ℝ) * q_lo) ⟨hmq_lo_pos.le, (hmq_lt.trans hmq_hi).le⟩
    rw [hF4]; change (1 - (1 - (m : ℝ) * q_lo)) / (M₀.m : ℝ) = q_lo
    rw [hMm]; field_simp [hm_pos.ne']; ring
  have hq_hi_eq : (1 - M.F v₁) / (M.m : ℝ) = q_hi := by
    have hF1 : M.F v₁ = 1 - (m : ℝ) * q_hi :=
      inv.hP_right ((m : ℝ) * q_hi) ⟨(hmq_lo_pos.trans hmq_lt).le, hmq_hi.le⟩
    rw [hF1]; change (1 - (1 - (m : ℝ) * q_hi)) / (M₀.m : ℝ) = q_hi
    rw [hMm]; field_simp [hm_pos.ne']; ring
  have hgain_pos : 0 < singleBandGain M inv_n.P ((1 - M.F v₄) / (M.m : ℝ)) ((1 - M.F v₁) / (M.m : ℝ)) := by
    rw [hq_lo_eq, hq_hi_eq]
    unfold singleBandGain
    change 0 < singleBandGainOf M₀.m n inv.P q_lo q_hi
    rw [hMm]
    exact hN n hnN
  refine ⟨α, β, hρα, hαβ, hβ1, θ, ha_lt_v1.trans hv1_lt_α, hβ_lt_v4.trans hv4_lt1, hSR, ?_⟩
  linarith [hrev_diff]

end EndToEndTheorem5

end AuctionCompetition
