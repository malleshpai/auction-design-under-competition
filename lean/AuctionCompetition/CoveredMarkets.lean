import AuctionCompetition.Defs
import Mathlib.Analysis.Convex.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Data.Nat.Choose.Sum

/-!
# Covered Markets: Theorem 2 and Example 1

Formalizes Section 4.3 (Theorem 2 and Example 1) and their full proofs in
Appendix B of Mallesh M. Pai, *Auction Design under Competition*
(`paper/auction-design-under-competition.tex`).

## Main Results

1. **Theorem 2 (`theorem2_covered_markets`)**: In a covered market (`0 < M.a`),
   if Cournot marginal revenue `M.psi` is nondecreasing on `[M.a, 1]` and
   `M.psi M.a ≥ 0` (equivalently `M.a * M.f M.a ≥ 1 / M.m`), then every
   Border-feasible quantity-path deviation with Lemma B.1's rent lower bound
   earns at most the symmetric candidate revenue `R*` at `ρ*`.
   - `theorem2_case1_lose_traffic`: Case 1 (`t0 ≤ 1 / m`), via generalized
     tangent bound, Border integration by parts, and `d/dt0 (reserveIncreaseRev) ≥ 0`.
   - `theorem2_case2_gain_traffic`: Case 2 (`t0 ≥ 1 / m`), via diagonal tangent
     bound, Lemma B.1's covered-market rent bound, and Jensen's inequality
     (`theorem2_jensen_ineq`).
   - `theorem2_virag_reserve_game`: `M.psi ≥ 0` on `[M.a, 1]` alone suffices
     against all reserve increases and reserve cuts (reserve cuts need only `P ≥ a`).
2. **Example 1 (`example1_pareto_market`, `example1_duopoly_cournot`,
   `example1_monopolist_irons`, `example1_psi1_pos_at_half`)**: Explicit smooth
   truncated Pareto market on `[1/2, 1]` with `m = 2` for every `n ≥ 2` where
   `psi1(1/2) > 0` and `psi1` strictly decreases near `1/2` (so a monopolist
   irons), yet `E < 3` everywhere and `psi2` is strictly increasing and positive,
   so Theorem 2 yields equilibrium at `ρ* = (n - 1) / (2 * n)`.
-/

open MeasureTheory Set Filter Finset

namespace AuctionCompetition

section CoveredPrelims

variable (M : Market)

/-- Equivalence in Theorem 2: `ψ_m(a) ≥ 0 ↔ a f(a) ≥ 1 / m`. -/
theorem psi_a_nonneg_iff :
    0 ≤ M.psi M.a ↔ 1 / (M.m : ℝ) ≤ M.a * M.f M.a := by
  unfold Market.psi
  rw [M.hF_a, sub_zero]
  have hm : (0 : ℝ) < M.m := M.m_pos_real
  have hfa : 0 < M.f M.a := M.hf_pos M.a ⟨le_rfl, M.ha1.le⟩
  have hmfa : 0 < (M.m : ℝ) * M.f M.a := mul_pos hm hfa
  constructor
  · intro h
    have h1 : 1 / ((M.m : ℝ) * M.f M.a) ≤ M.a := by linarith
    rw [div_le_iff₀ hmfa] at h1
    rw [div_le_iff₀ hm]
    nlinarith
  · intro h
    rw [div_le_iff₀ hm] at h
    have h1 : 1 / ((M.m : ℝ) * M.f M.a) ≤ M.a := by
      rw [div_le_iff₀ hmfa]
      nlinarith
    linarith

/-- Baseline symmetric candidate revenue `R*` at `ρ*` with uniform split `q0 = t0 = 1 / m`. -/
noncomputable def baselineRev (P : ℝ → ℝ) : ℝ :=
  pathRev M P M.rhoStar (1 / (M.m : ℝ)) (1 / (M.m : ℝ)) 0 id

/-- Cournot marginal revenue in quantity coordinates: `MR(z) = ψ_m(P(z))`. -/
noncomputable def MR (P : M.InverseDemand) (z : ℝ) : ℝ :=
  M.psi (P.P z)

/-- Probability scale `h_n(u) = (1 - (1 - u)^n) / n` from Appendix B. -/
noncomputable def probScale (n : ℕ) (u : ℝ) : ℝ :=
  (1 - (1 - u) ^ n) / (n : ℝ)

/-- Convexity gap `η = h_n(q0) - h_n(t0) + (1 - q0)^(n - 1) * (t0 - q0)` from Appendix B. -/
noncomputable def cm_convexityGap (n : ℕ) (q0 t0 : ℝ) : ℝ :=
  probScale n q0 - probScale n t0 + (1 - q0) ^ (n - 1) * (t0 - q0)

lemma inv_m_pos : (0 : ℝ) < 1 / (M.m : ℝ) :=
  div_pos one_pos M.m_pos_real

lemma inv_m_le_one : 1 / (M.m : ℝ) ≤ 1 := by
  have hm : (2 : ℝ) ≤ M.m := by exact_mod_cast M.hm
  rw [div_le_one M.m_pos_real]
  linarith

lemma cm_psi_continuousOn : ContinuousOn M.psi (Icc M.a 1) := by
  unfold Market.psi
  apply continuousOn_id.sub
  apply (continuousOn_const.sub M.F_continuousOn).div
  · exact continuousOn_const.mul M.hf_cont
  · intro v hv
    exact ne_of_gt (mul_pos M.m_pos_real (M.hf_pos v hv))

lemma MR_eq (P : M.InverseDemand) {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    MR M P z = P.P z - z / ((M.m : ℝ) * M.f (P.P z)) := by
  unfold MR Market.psi
  rw [P.hP_right z hz]
  ring

lemma MR_continuousOn (P : M.InverseDemand) : ContinuousOn (MR M P) (Icc 0 1) :=
  (cm_psi_continuousOn M).comp P.hP_cont (fun z hz => P.hP_mem z hz)

lemma MR_antitoneOn (P : M.InverseDemand) (hpsi : MonotoneOn M.psi (Icc M.a 1)) :
    AntitoneOn (MR M P) (Icc 0 1) := by
  intro x hx y hy hxy
  exact hpsi (P.hP_mem y hy) (P.hP_mem x hx) (P.hP_strictAnti.antitoneOn hx hy hxy)

lemma MR_nonneg (P : M.InverseDemand) (hpsi_mono : MonotoneOn M.psi (Icc M.a 1))
    (hpsi_a : 0 ≤ M.psi M.a) {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    0 ≤ MR M P z := by
  have h1 : M.psi M.a = MR M P 1 := by unfold MR; rw [P.hP_one]
  rw [h1] at hpsi_a
  exact hpsi_a.trans (MR_antitoneOn M P hpsi_mono hz ⟨zero_le_one, le_rfl⟩ hz.2)

lemma cm_W_nonneg {q : ℝ} (hq : q ≤ 1) : 0 ≤ M.W q := by
  unfold Market.W
  have hn : (0 : ℝ) ≤ M.n := M.n_pos_real.le
  have hn1 : (0 : ℝ) ≤ (M.n : ℝ) - 1 := M.n_sub_one_pos_real.le
  have h1q : 0 ≤ 1 - q := by linarith
  positivity

lemma cm_W_continuous : Continuous M.W := by
  unfold Market.W
  exact continuous_const.mul ((continuous_const.sub continuous_id).pow (M.n - 2))

/-- Generalized tangent bound (eq. (17) in Appendix B):
under monotone `ψ_m`, `Π(t, q) - Π(t', q) ≤ MR(t' + (m - 1)q) * (t - t')`
whenever `t' = q` or `t ≤ t' ≤ q`. -/
lemma cm_tangent_bound_general (P : M.InverseDemand)
    (hpsi : MonotoneOn M.psi (Icc M.a 1))
    {q t t' : ℝ}
    (htz : t + ((M.m : ℝ) - 1) * q ∈ Icc (0 : ℝ) 1)
    (ht'z : t' + ((M.m : ℝ) - 1) * q ∈ Icc (0 : ℝ) 1)
    (hcase : t' = q ∨ (t ≤ t' ∧ t' ≤ q)) :
    M.cournotRev P.P t q - M.cournotRev P.P t' q ≤
      MR M P (t' + ((M.m : ℝ) - 1) * q) * (t - t') := by
  let g : ℝ → ℝ := fun s => M.cournotRev P.P s q
  let shift : ℝ → ℝ := fun s => s + ((M.m : ℝ) - 1) * q
  have hshift_deriv : ∀ s, HasDerivAt shift 1 s := fun s =>
    (hasDerivAt_id' s).add_const (((M.m : ℝ) - 1) * q)
  have hg_deriv_open : ∀ s, shift s ∈ Ioo (0 : ℝ) 1 →
      HasDerivAt g (P.P (shift s) + s * (-1 / M.f (P.P (shift s)))) s := by
    intro s hs
    have hP : HasDerivAt (fun x => P.P (shift x)) (-1 / M.f (P.P (shift s))) s := by
      have hcomp := (P.hP_deriv_open (shift s) hs).comp s (hshift_deriv s)
      simpa only [Function.comp_def, mul_one] using hcomp
    have hmul := (hasDerivAt_id' s).fun_mul hP
    show HasDerivAt (fun x => x * P.P (shift x)) _ s
    convert hmul using 1
    ring
  have hg_cont : ∀ a b, a ≤ b → shift a ∈ Icc (0 : ℝ) 1 → shift b ∈ Icc (0 : ℝ) 1 →
      ContinuousOn g (Icc a b) := by
    intro a b _ ha hb
    apply continuousOn_id.mul
    apply P.hP_cont.comp (continuousOn_id.add continuousOn_const)
    intro x hx
    exact ⟨by change x + ((M.m : ℝ) - 1) * q ≥ 0; linarith [ha.1, hx.1],
           by change x + ((M.m : ℝ) - 1) * q ≤ 1; linarith [hb.2, hx.2]⟩
  have hderiv_rel : ∀ s, shift s ∈ Icc (0 : ℝ) 1 →
      P.P (shift s) + s * (-1 / M.f (P.P (shift s))) =
        MR M P (shift s) - (((M.m : ℝ) - 1) / (M.m : ℝ)) * (s - q) / M.f (P.P (shift s)) := by
    intro s hs
    rw [MR_eq M P hs]
    have hm : (M.m : ℝ) ≠ 0 := M.m_pos_real.ne'
    have hf : M.f (P.P (shift s)) ≠ 0 := (M.hf_pos _ (P.hP_mem _ hs)).ne'
    dsimp [shift]
    field_simp
    ring
  rcases lt_trichotomy t t' with hlt | rfl | hgt
  · -- Case t < t': then t' ≤ q in both branches of hcase
    have ht'q : t' ≤ q := by rcases hcase with rfl | ⟨_, h⟩ <;> linarith
    have hcont : ContinuousOn g (Icc t t') := hg_cont t t' hlt.le htz ht'z
    have hdiff : DifferentiableOn ℝ g (Ioo t t') := by
      intro c hc
      have hsc : shift c ∈ Ioo (0 : ℝ) 1 :=
        ⟨by dsimp [shift]; linarith [htz.1, hc.1], by dsimp [shift]; linarith [ht'z.2, hc.2]⟩
      exact (hg_deriv_open c hsc).differentiableAt.differentiableWithinAt
    obtain ⟨c, hc, hslope⟩ := exists_deriv_eq_slope g hlt hcont hdiff
    have hsc_open : shift c ∈ Ioo (0 : ℝ) 1 :=
      ⟨by dsimp [shift]; linarith [htz.1, hc.1], by dsimp [shift]; linarith [ht'z.2, hc.2]⟩
    have hsc_icc : shift c ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hsc_open
    have hderiv_c : deriv g c = P.P (shift c) + c * (-1 / M.f (P.P (shift c))) :=
      (hg_deriv_open c hsc_open).deriv
    have hMR_ge : MR M P (shift t') ≤ MR M P (shift c) :=
      MR_antitoneOn M P hpsi hsc_icc ht'z (by dsimp [shift]; linarith [hc.2])
    have hterm_le : (((M.m : ℝ) - 1) / (M.m : ℝ)) * (c - q) / M.f (P.P (shift c)) ≤ 0 := by
      have hm1 : 0 < ((M.m : ℝ) - 1) / (M.m : ℝ) :=
        div_pos M.m_sub_one_pos_real M.m_pos_real
      have hfc : 0 < M.f (P.P (shift c)) := M.hf_pos _ (P.hP_mem _ hsc_icc)
      have hcq : c - q ≤ 0 := by linarith [hc.2]
      exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hm1.le hcq) hfc.le
    have hslope_ge : MR M P (shift t') ≤ (g t' - g t) / (t' - t) := by
      rw [← hslope, hderiv_c, hderiv_rel c hsc_icc]
      linarith
    rw [le_div_iff₀ (sub_pos.mpr hlt)] at hslope_ge
    change g t - g t' ≤ MR M P (shift t') * (t - t')
    linarith
  · -- Case t = t'
    simp
  · -- Case t > t': must be t' = q
    have ht'q : t' = q := by
      rcases hcase with rfl | ⟨hle, _⟩
      · rfl
      · linarith
    subst ht'q
    have hcont : ContinuousOn g (Icc t' t) := hg_cont t' t hgt.le ht'z htz
    have hdiff : DifferentiableOn ℝ g (Ioo t' t) := by
      intro c hc
      have hsc : shift c ∈ Ioo (0 : ℝ) 1 :=
        ⟨by dsimp [shift]; linarith [ht'z.1, hc.1], by dsimp [shift]; linarith [htz.2, hc.2]⟩
      exact (hg_deriv_open c hsc).differentiableAt.differentiableWithinAt
    obtain ⟨c, hc, hslope⟩ := exists_deriv_eq_slope g hgt hcont hdiff
    have hsc_open : shift c ∈ Ioo (0 : ℝ) 1 :=
      ⟨by dsimp [shift]; linarith [ht'z.1, hc.1], by dsimp [shift]; linarith [htz.2, hc.2]⟩
    have hsc_icc : shift c ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hsc_open
    have hderiv_c : deriv g c = P.P (shift c) + c * (-1 / M.f (P.P (shift c))) :=
      (hg_deriv_open c hsc_open).deriv
    have hMR_le : MR M P (shift c) ≤ MR M P (shift t') :=
      MR_antitoneOn M P hpsi ht'z hsc_icc (by dsimp [shift]; linarith [hc.1])
    have hterm_ge : 0 ≤ (((M.m : ℝ) - 1) / (M.m : ℝ)) * (c - t') / M.f (P.P (shift c)) := by
      have hm1 : 0 < ((M.m : ℝ) - 1) / (M.m : ℝ) :=
        div_pos M.m_sub_one_pos_real M.m_pos_real
      have hfc : 0 < M.f (P.P (shift c)) := M.hf_pos _ (P.hP_mem _ hsc_icc)
      have hcq : 0 ≤ c - t' := by linarith [hc.1]
      exact div_nonneg (mul_nonneg hm1.le hcq) hfc.le
    have hslope_le : (g t - g t') / (t - t') ≤ MR M P (shift t') := by
      rw [← hslope, hderiv_c, hderiv_rel c hsc_icc]
      linarith
    rw [div_le_iff₀ (sub_pos.mpr hgt)] at hslope_le
    exact hslope_le

/-- Diagonal tangent bound (eq. (9)): `Π(t, q) - Π(q, q) ≤ ψ_m(P(mq)) * (t - q)`. -/
lemma cm_tangent_bound_diag (P : M.InverseDemand)
    (hpsi : MonotoneOn M.psi (Icc M.a 1))
    {q t : ℝ}
    (htz : t + ((M.m : ℝ) - 1) * q ∈ Icc (0 : ℝ) 1)
    (hqz : (M.m : ℝ) * q ∈ Icc (0 : ℝ) 1) :
    M.cournotRev P.P t q - M.cournotRev P.P q q ≤ MR M P ((M.m : ℝ) * q) * (t - q) := by
  have hshift : q + ((M.m : ℝ) - 1) * q = (M.m : ℝ) * q := by ring
  rw [← hshift]
  exact cm_tangent_bound_general M P hpsi htz (by rwa [hshift]) (Or.inl rfl)

/-- Stieltjes-free integration by parts for a continuous antitone weight `ϱ` against an
integrable function `h` whose prefix integrals are nonpositive:
`∫_a^b ϱ(q) h(q) dq ≤ ϱ(b) ∫_a^b h(q) dq`. -/
lemma cm_integral_antitone_mul_le {a b : ℝ} (hab : a ≤ b)
    {ϱ h : ℝ → ℝ}
    (hϱ_cont : ContinuousOn ϱ (Icc a b))
    (hϱ_anti : AntitoneOn ϱ (Icc a b))
    (hh_int : IntervalIntegrable h volume a b)
    (hH_le : ∀ q ∈ Icc a b, ∫ u in a..q, h u ≤ 0) :
    (∫ q in a..b, ϱ q * h q) ≤ ϱ b * ∫ q in a..b, h q := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simp
  have hϱh_int : IntervalIntegrable (fun q => ϱ q * h q) volume a b := by
    have hcont : ContinuousOn ϱ (uIcc a b) := by rwa [uIcc_of_le hab]
    exact hh_int.continuousOn_mul hcont
  have h_abs_int : IntervalIntegrable (fun q => |h q|) volume a b := hh_int.abs
  set M_abs : ℝ := ∫ q in a..b, |h q|
  have hM_nonneg : 0 ≤ M_abs :=
    intervalIntegral.integral_nonneg hab (fun _ _ => abs_nonneg _)
  -- Prove by showing LHS ≤ RHS + ε for all ε > 0
  apply le_of_forall_pos_le_add
  intro ε hε
  set η : ℝ := ε / (M_abs + 1)
  have hη : 0 < η := div_pos hε (by linarith)
  have hunif : UniformContinuousOn ϱ (Icc a b) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hϱ_cont
  rw [Metric.uniformContinuousOn_iff] at hunif
  obtain ⟨δ, hδ, hδ_spec⟩ := hunif η hη
  -- Pick k ≥ 1 with (b - a) / k < δ
  obtain ⟨k, hk⟩ := exists_nat_gt ((b - a) / δ)
  have hk_pos : 0 < k := by
    by_contra hk0
    push Not at hk0
    have hk0' : k = 0 := Nat.le_zero.mp hk0
    subst hk0'
    have : 0 < (b - a) / δ := div_pos (sub_pos.mpr hlt) hδ
    simp at hk
    linarith
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk_pos
  have hstep_lt : (b - a) / (k : ℝ) < δ := by
    rw [div_lt_iff₀ hkR]
    have := (div_lt_iff₀ hδ).mp hk
    linarith
  -- Uniform grid x i = a + i * (b - a) / k
  let x : ℕ → ℝ := fun i => a + (i : ℝ) * (b - a) / (k : ℝ)
  have hx0 : x 0 = a := by simp [x]
  have hxk : x k = b := by
    simp only [x]
    field_simp [hkR.ne']
    ring
  have hx_mono : ∀ i j, i ≤ j → x i ≤ x j := by
    intro i j hij
    dsimp [x]
    have hijR : (i : ℝ) ≤ j := by exact_mod_cast hij
    have hba : 0 ≤ b - a := sub_nonneg.mpr hab
    have : (i : ℝ) * (b - a) / (k : ℝ) ≤ (j : ℝ) * (b - a) / (k : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hijR hba) hkR.le
    linarith
  have hx_mem : ∀ i, i ≤ k → x i ∈ Icc a b := by
    intro i hi
    exact ⟨by rw [← hx0]; exact hx_mono 0 i (Nat.zero_le i),
           by rw [← hxk]; exact hx_mono i k hi⟩
  have hx_diff : ∀ i, x (i + 1) - x i = (b - a) / (k : ℝ) := by
    intro i
    dsimp [x]
    push_cast
    ring
  let H : ℝ → ℝ := fun q => ∫ u in a..q, h u
  -- Abel summation induction: ∑_{i < m} ϱ(x_{i+1}) * (H(x_{i+1}) - H(x_i)) ≤ ϱ(x_m) * H(x_m)
  have habel : ∀ m ≤ k,
      ∑ i ∈ Finset.range m, ϱ (x (i + 1)) * (H (x (i + 1)) - H (x i)) ≤ ϱ (x m) * H (x m) := by
    intro m hm
    induction m with
    | zero =>
      simp [H, hx0]
    | succ m ih =>
      rw [Finset.sum_range_succ]
      have hm_le : m ≤ k := Nat.le_of_succ_le hm
      have hih := ih hm_le
      have hϱ_le : ϱ (x (m + 1)) ≤ ϱ (x m) :=
        hϱ_anti (hx_mem m hm_le) (hx_mem (m + 1) hm) (hx_mono m (m + 1) (Nat.le_succ m))
      have hHm : H (x m) ≤ 0 := hH_le (x m) (hx_mem m hm_le)
      have hterm : (ϱ (x m) - ϱ (x (m + 1))) * H (x m) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hϱ_le) hHm
      linarith
  -- Relate H(x_{i+1}) - H(x_i) to ∫_{x_i}^{x_{i+1}} h
  have hH_sub : ∀ i < k, H (x (i + 1)) - H (x i) = ∫ q in x i..x (i + 1), h q := by
    intro i hi
    have h1 := hh_int.mono_set (uIcc_subset_uIcc_left (by
      rw [uIcc_of_le hab]; exact hx_mem i hi.le))
    have h2 : IntervalIntegrable h volume (x i) (x (i + 1)) :=
      hh_int.mono_set (by
        rw [uIcc_of_le (hx_mono i (i + 1) (Nat.le_succ i)), uIcc_of_le hab]
        exact Icc_subset_Icc (hx_mem i hi.le).1 (hx_mem (i + 1) hi).2)
    have hadd := intervalIntegral.integral_add_adjacent_intervals h1 h2
    dsimp [H]
    linarith
  -- Split ∫_a^b (ϱ * h) and ∫_a^b |h| across the k intervals
  have hsplit_main : (∫ q in a..b, ϱ q * h q) =
      ∑ i ∈ Finset.range k, ∫ q in x i..x (i + 1), ϱ q * h q := by
    rw [← hx0, ← hxk]
    symm
    apply intervalIntegral.sum_integral_adjacent_intervals
    intro i hi
    exact hϱh_int.mono_set (by
      rw [uIcc_of_le (hx_mono i (i + 1) (Nat.le_succ i)), uIcc_of_le hab]
      exact Icc_subset_Icc (hx_mem i hi.le).1 (hx_mem (i + 1) hi).2)
  have hsplit_abs : M_abs = ∑ i ∈ Finset.range k, ∫ q in x i..x (i + 1), |h q| := by
    dsimp [M_abs]
    rw [← hx0, ← hxk]
    symm
    apply intervalIntegral.sum_integral_adjacent_intervals
    intro i hi
    exact h_abs_int.mono_set (by
      rw [uIcc_of_le (hx_mono i (i + 1) (Nat.le_succ i)), uIcc_of_le hab]
      exact Icc_subset_Icc (hx_mem i hi.le).1 (hx_mem (i + 1) hi).2)
  -- Bound each subinterval error by η * ∫_{x_i}^{x_{i+1}} |h|
  have hsub_err : ∀ i ∈ Finset.range k,
      (∫ q in x i..x (i + 1), ϱ q * h q) - ϱ (x (i + 1)) * (H (x (i + 1)) - H (x i)) ≤
        η * ∫ q in x i..x (i + 1), |h q| := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [hH_sub i hi, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    have hxi_le : x i ≤ x (i + 1) := hx_mono i (i + 1) (Nat.le_succ i)
    have hsub_icc : Icc (x i) (x (i + 1)) ⊆ Icc a b :=
      Icc_subset_Icc (hx_mem i hi.le).1 (hx_mem (i + 1) hi).2
    have hi1 : IntervalIntegrable (fun q => ϱ q * h q) volume (x i) (x (i + 1)) :=
      hϱh_int.mono_set (by rw [uIcc_of_le hxi_le, uIcc_of_le hab]; exact hsub_icc)
    have hi2 : IntervalIntegrable (fun q => ϱ (x (i + 1)) * h q) volume (x i) (x (i + 1)) :=
      (hh_int.mono_set (by rw [uIcc_of_le hxi_le, uIcc_of_le hab]; exact hsub_icc)).const_mul _
    have hi3 : IntervalIntegrable (fun q => η * |h q|) volume (x i) (x (i + 1)) :=
      (h_abs_int.mono_set (by rw [uIcc_of_le hxi_le, uIcc_of_le hab]; exact hsub_icc)).const_mul _
    rw [← intervalIntegral.integral_sub hi1 hi2]
    apply intervalIntegral.integral_mono_on hxi_le (hi1.sub hi2) hi3
    intro q hq
    have hq_mem : q ∈ Icc a b := hsub_icc hq
    have hx1_mem : x (i + 1) ∈ Icc a b := hx_mem (i + 1) hi
    have hdist : dist q (x (i + 1)) < δ := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hq.2)]
      have : x (i + 1) - q ≤ x (i + 1) - x i := by linarith [hq.1]
      rw [hx_diff i] at this
      linarith
    have hϱ_dist : |ϱ q - ϱ (x (i + 1))| < η := by
      simpa [Real.dist_eq] using hδ_spec q hq_mem (x (i + 1)) hx1_mem hdist
    calc
      ϱ q * h q - ϱ (x (i + 1)) * h q = (ϱ q - ϱ (x (i + 1))) * h q := by ring
      _ ≤ |(ϱ q - ϱ (x (i + 1))) * h q| := le_abs_self _
      _ = |ϱ q - ϱ (x (i + 1))| * |h q| := abs_mul _ _
      _ ≤ η * |h q| := mul_le_mul_of_nonneg_right hϱ_dist.le (abs_nonneg _)
  -- Sum over i ∈ range k
  have hsum_err :
      (∫ q in a..b, ϱ q * h q) -
        ∑ i ∈ Finset.range k, ϱ (x (i + 1)) * (H (x (i + 1)) - H (x i)) ≤ η * M_abs := by
    rw [hsplit_main, hsplit_abs, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum hsub_err
  have habel_k := habel k le_rfl
  rw [hxk] at habel_k
  have hηM : η * M_abs ≤ ε := by
    dsimp [η]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith
  dsimp [H] at habel_k
  linarith

/-- Helper: a monotone function on `[a, b]` composed with `cournotRev` and `W` is
interval-integrable. -/
lemma monotoneOn_cournot_integrable {a b : ℝ} (hab : a ≤ b)
    (P : M.InverseDemand) {t : ℝ → ℝ}
    (ht_mono : MonotoneOn t (Icc a b))
    (ht_dom : ∀ q ∈ Icc a b, t q + ((M.m : ℝ) - 1) * q ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun q => M.cournotRev P.P (t q) q * M.W q) volume a b := by
  have ht_int : IntervalIntegrable t volume a b :=
    (ht_mono.mono (by rw [uIcc_of_le hab])).intervalIntegrable
  have hP_anti : AntitoneOn (fun q => P.P (t q + ((M.m : ℝ) - 1) * q)) (Icc a b) := by
    intro x hx y hy hxy
    have harg : t x + ((M.m : ℝ) - 1) * x ≤ t y + ((M.m : ℝ) - 1) * y := by
      have htx : t x ≤ t y := ht_mono hx hy hxy
      have hm1 : 0 ≤ (M.m : ℝ) - 1 := M.m_sub_one_pos_real.le
      nlinarith
    exact P.hP_strictAnti.antitoneOn (ht_dom x hx) (ht_dom y hy) harg
  have hP_int : IntervalIntegrable (fun q => P.P (t q + ((M.m : ℝ) - 1) * q)) volume a b :=
    (hP_anti.mono (by rw [uIcc_of_le hab])).intervalIntegrable
  -- Boundedness of t and P(t + (m-1)q) on Ioc a b
  have ht_meas : AEStronglyMeasurable t (volume.restrict (Ioc a b)) := ht_int.1.aestronglyMeasurable
  have hP_meas : AEStronglyMeasurable (fun q => P.P (t q + ((M.m : ℝ) - 1) * q))
      (volume.restrict (Ioc a b)) := hP_int.1.aestronglyMeasurable
  have hW_meas : AEStronglyMeasurable M.W (volume.restrict (Ioc a b)) :=
    (cm_W_continuous M).aestronglyMeasurable
  have h_meas : AEStronglyMeasurable (fun q => M.cournotRev P.P (t q) q * M.W q)
      (volume.restrict (Ioc a b)) := by
    unfold Market.cournotRev
    exact (ht_meas.mul hP_meas).mul hW_meas
  -- Bound the integrand by a constant on Icc a b
  have hC : ∃ C : ℝ, ∀ q ∈ Icc a b, ‖M.cournotRev P.P (t q) q * M.W q‖ ≤ C := by
    obtain ⟨Cw, hCw⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (s := Icc a b) (cm_W_continuous M).continuousOn
    refine ⟨max (|t a|) (|t b|) * 1 * Cw, fun q hq => ?_⟩
    have hta : t a ≤ t q := ht_mono (left_mem_Icc.mpr hab) hq hq.1
    have htb : t q ≤ t b := ht_mono hq (right_mem_Icc.mpr hab) hq.2
    have ht_bd : ‖t q‖ ≤ max (|t a|) (|t b|) := by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [neg_abs_le (t a), le_max_left (|t a|) (|t b|)],
                        by linarith [le_abs_self (t b), le_max_right (|t a|) (|t b|)]⟩
    have hP_mem := P.hP_mem _ (ht_dom q hq)
    have hP_bd : ‖P.P (t q + ((M.m : ℝ) - 1) * q)‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (M.ha0.trans hP_mem.1)]
      exact hP_mem.2
    have hW_bd : ‖M.W q‖ ≤ Cw := hCw q hq
    have h0 : 0 ≤ max (|t a|) (|t b|) := le_trans (abs_nonneg _) (le_max_left _ _)
    unfold Market.cournotRev
    calc
      ‖t q * P.P (t q + ((M.m : ℝ) - 1) * q) * M.W q‖
          = ‖t q‖ * ‖P.P (t q + ((M.m : ℝ) - 1) * q)‖ * ‖M.W q‖ := by
            rw [norm_mul, norm_mul]
      _ ≤ max (|t a|) (|t b|) * 1 * Cw := by
            apply mul_le_mul
            · exact mul_le_mul ht_bd hP_bd (norm_nonneg _) h0
            · exact hW_bd
            · exact norm_nonneg _
            · positivity
  obtain ⟨C, hC⟩ := hC
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine Integrable.mono' (integrableOn_const (hs := measure_Ioc_lt_top.ne) (C := C)) h_meas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with q hq
  exact hC q (Ioc_subset_Icc_self hq)

end CoveredPrelims

/-- Jensen's inequality in Theorem 2 (Case 2):
`((m - 1)/m) (1 - q0)^n + (1/m) ((m - 1) q0)^n ≥ ((m - 1)/m)^n`
for all `m, n ≥ 2` and `q0 ∈ [0, 1/m]`. -/
theorem theorem2_jensen_ineq {m n : ℕ} (hm : 2 ≤ m) (_hn : 2 ≤ n) {q0 : ℝ}
    (hq0 : 0 ≤ q0) (hq0_le : q0 ≤ 1 / (m : ℝ)) :
    (((m : ℝ) - 1) / (m : ℝ)) ^ n ≤
      (((m : ℝ) - 1) / (m : ℝ)) * (1 - q0) ^ n +
        (1 / (m : ℝ)) * (((m : ℝ) - 1) * q0) ^ n := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hm1 : (0 : ℝ) ≤ (m : ℝ) - 1 := by linarith
  have hw1 : 0 ≤ ((m : ℝ) - 1) / (m : ℝ) := div_nonneg hm1 hmpos.le
  have hw2 : 0 ≤ (1 : ℝ) / (m : ℝ) := div_nonneg zero_le_one hmpos.le
  have hwsum : ((m : ℝ) - 1) / (m : ℝ) + 1 / (m : ℝ) = 1 := by
    field_simp [hmpos.ne']
    ring
  have hx1 : (1 - q0) ∈ Ici (0 : ℝ) := by
    have : 1 / (m : ℝ) ≤ 1 := by rw [div_le_one hmpos]; linarith
    show 0 ≤ 1 - q0
    linarith
  have hx2 : (((m : ℝ) - 1) * q0) ∈ Ici (0 : ℝ) := mul_nonneg hm1 hq0
  have hconv := (convexOn_pow (𝕜 := ℝ) n).2 hx1 hx2 hw1 hw2 hwsum
  have hcomb : ((m : ℝ) - 1) / (m : ℝ) * (1 - q0) + 1 / (m : ℝ) * (((m : ℝ) - 1) * q0) =
      ((m : ℝ) - 1) / (m : ℝ) := by
    field_simp [hmpos.ne']
    ring
  simpa only [smul_eq_mul, hcomb] using hconv

/-! ### Case 1: Deviations Losing Traffic (`t0 ≤ 1 / m`) -/

section Case1

variable (M : Market)

/-- Binomial derivative identity obtained by differentiating `(x + y)^d`. -/
private lemma sum_choose_deriv (d : ℕ) (x y : ℝ) :
    ∑ k ∈ Finset.range (d + 1), ((k : ℝ) * x ^ (k - 1)) * y ^ (d - k) * (d.choose k : ℝ) =
      (d : ℝ) * (x + y) ^ (d - 1) := by
  have h1 : HasDerivAt (fun s : ℝ => (s + y) ^ d) ((d : ℝ) * (x + y) ^ (d - 1)) x := by
    have := ((hasDerivAt_id' x).add_const y).fun_pow d
    simpa only [mul_one] using this
  have h2 : HasDerivAt
      (fun s : ℝ => ∑ k ∈ Finset.range (d + 1), s ^ k * y ^ (d - k) * (d.choose k : ℝ))
      (∑ k ∈ Finset.range (d + 1), ((k : ℝ) * x ^ (k - 1)) * y ^ (d - k) * (d.choose k : ℝ)) x := by
    apply HasDerivAt.fun_sum
    intro k _
    have hk := (hasDerivAt_pow k x).mul_const (y ^ (d - k))
    exact hk.mul_const (d.choose k : ℝ)
  have heq : (fun s : ℝ => (s + y) ^ d) =
      (fun s : ℝ => ∑ k ∈ Finset.range (d + 1), s ^ k * y ^ (d - k) * (d.choose k : ℝ)) := by
    ext s; exact add_pow s y d
  rw [heq] at h1
  exact h2.unique h1

/-- Case 1, Step 1: Under monotone `ψ_m` and `ψ_m(a) ≥ 0`, any Border-feasible path with
`t0 ≤ 1 / m` and `ℓ ≥ 0` earns at most the reserve-increase revenue `R^S(t0)`. -/
theorem case1_le_reserveIncreaseRev (P : M.InverseDemand)
    (hpsi_mono : MonotoneOn M.psi (Icc M.a 1))
    (hpsi_a : 0 ≤ M.psi M.a)
    {q0 t0 ℓ : ℝ} {t : ℝ → ℝ}
    (ht0_nonneg : 0 ≤ t0) (ht0_le : t0 ≤ 1 / (M.m : ℝ))
    (hq0_eq : t0 + ((M.m : ℝ) - 1) * q0 = 1)
    (hℓ : 0 ≤ ℓ)
    (ht_mono : MonotoneOn t (Icc 0 q0))
    (ht_bounds : ∀ q ∈ Icc (0 : ℝ) q0, 0 ≤ t q ∧ t q ≤ t0)
    (hborder : BorderFeasible M q0 t) :
    pathRev M P.P M.rhoStar q0 t0 ℓ t ≤ reserveIncreaseRev M P.P M.rhoStar t0 := by
  have hm : (0 : ℝ) < M.m := M.m_pos_real
  have hm1 : (0 : ℝ) < (M.m : ℝ) - 1 := M.m_sub_one_pos_real
  have hmR : (2 : ℝ) ≤ M.m := by exact_mod_cast M.hm
  have hn : (0 : ℝ) < M.n := M.n_pos_real
  have hn1 : (0 : ℝ) < (M.n : ℝ) - 1 := M.n_sub_one_pos_real
  have hq0_val : q0 = (1 - t0) / ((M.m : ℝ) - 1) := by
    rw [eq_div_iff hm1.ne']; linarith
  have ht0_le_q0 : t0 ≤ q0 := by
    rw [hq0_val, le_div_iff₀ hm1]
    have : (M.m : ℝ) * t0 ≤ 1 := by rwa [le_div_iff₀ hm, mul_comm] at ht0_le
    linarith
  have hq0_nonneg : 0 ≤ q0 := ht0_nonneg.trans ht0_le_q0
  have hq0_le_one : q0 ≤ 1 := by
    rw [hq0_val, div_le_one hm1]
    linarith
  -- Unfold reserveIncreaseRev and cancel the boundary term
  unfold reserveIncreaseRev
  simp only [← hq0_val]
  unfold pathRev
  -- Both integrals are integrable
  have ht_dom : ∀ q ∈ Icc (0 : ℝ) q0, t q + ((M.m : ℝ) - 1) * q ∈ Icc (0 : ℝ) 1 := by
    intro q hq
    refine ⟨?_, ?_⟩
    · have := (ht_bounds q hq).1; nlinarith [hq.1]
    · have := (ht_bounds q hq).2; nlinarith [hq.2]
  have htS_mono : MonotoneOn (reserveIncreasePath t0) (Icc 0 q0) := by
    intro x _ y _ hxy
    exact min_le_min_right t0 hxy
  have htS_dom : ∀ q ∈ Icc (0 : ℝ) q0,
      reserveIncreasePath t0 q + ((M.m : ℝ) - 1) * q ∈ Icc (0 : ℝ) 1 := by
    intro q hq
    refine ⟨?_, ?_⟩
    · have : 0 ≤ min q t0 := le_min hq.1 ht0_nonneg
      unfold reserveIncreasePath; nlinarith [hq.1]
    · have : min q t0 ≤ t0 := min_le_right q t0
      unfold reserveIncreasePath; nlinarith [hq.2]
  have hint_t : IntervalIntegrable (fun q => M.cournotRev P.P (t q) q * M.W q) volume 0 q0 :=
    monotoneOn_cournot_integrable M hq0_nonneg P ht_mono ht_dom
  have hint_tS : IntervalIntegrable
      (fun q => M.cournotRev P.P (reserveIncreasePath t0 q) q * M.W q) volume 0 q0 :=
    monotoneOn_cournot_integrable M hq0_nonneg P htS_mono htS_dom
  -- Define ϱ(q) = MR(t^S(q) + (m - 1)q) and h(q) = (n - 1)(t(q) - t^S(q))(1 - q)^(n - 2)
  let ϱ : ℝ → ℝ := fun q => MR M P (reserveIncreasePath t0 q + ((M.m : ℝ) - 1) * q)
  let h : ℝ → ℝ := fun q => ((M.n : ℝ) - 1) * (t q - reserveIncreasePath t0 q) * (1 - q) ^ (M.n - 2)
  have hϱ_cont : ContinuousOn ϱ (Icc 0 q0) := by
    have harg_cont : ContinuousOn (fun q => reserveIncreasePath t0 q + ((M.m : ℝ) - 1) * q)
        (Icc 0 q0) :=
      ((continuous_id.min continuous_const).add (continuous_const.mul continuous_id)).continuousOn
    exact (MR_continuousOn M P).comp harg_cont htS_dom
  have hϱ_anti : AntitoneOn ϱ (Icc 0 q0) := by
    intro x hx y hy hxy
    have harg : reserveIncreasePath t0 x + ((M.m : ℝ) - 1) * x ≤
        reserveIncreasePath t0 y + ((M.m : ℝ) - 1) * y := by
      have hmin := htS_mono hx hy hxy
      nlinarith
    exact MR_antitoneOn M P hpsi_mono (htS_dom x hx) (htS_dom y hy) harg
  have hh_int : IntervalIntegrable h volume 0 q0 := by
    have hdiff_int : IntervalIntegrable (fun q => t q - reserveIncreasePath t0 q) volume 0 q0 :=
      (ht_mono.mono (by rw [uIcc_of_le hq0_nonneg])).intervalIntegrable.sub
        (htS_mono.mono (by rw [uIcc_of_le hq0_nonneg])).intervalIntegrable
    have hwt_cont : ContinuousOn (fun q => ((M.n : ℝ) - 1) * (1 - q) ^ (M.n - 2)) (uIcc 0 q0) :=
      (continuous_const.mul ((continuous_const.sub continuous_id).pow (M.n - 2))).continuousOn
    have hmul := hdiff_int.continuousOn_mul hwt_cont
    convert hmul using 1
    ext q; dsimp [h]; ring
  have hϱh_int : IntervalIntegrable (fun q => (M.n : ℝ) * (ϱ q * h q)) volume 0 q0 := by
    have hcont : ContinuousOn ϱ (uIcc 0 q0) := by rwa [uIcc_of_le hq0_nonneg]
    exact (hh_int.continuousOn_mul hcont).const_mul (M.n : ℝ)
  -- Prefix integrals of h are nonpositive on [0, q0]
  have hH_le : ∀ q ∈ Icc (0 : ℝ) q0, ∫ u in (0 : ℝ)..q, h u ≤ 0 := by
    intro q hq
    by_cases hqt : q ≤ t0
    · have hcongr : EqOn h (fun u => ((M.n : ℝ) - 1) * ((t u - u) * (1 - u) ^ (M.n - 2)))
          (uIcc 0 q) := by
        intro u hu
        rw [uIcc_of_le hq.1] at hu
        dsimp [h, reserveIncreasePath]
        rw [min_eq_left (hu.2.trans hqt)]
        ring
      rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const_mul]
      exact mul_nonpos_of_nonneg_of_nonpos hn1.le (hborder q hq)
    · push Not at hqt
      have h1 : IntervalIntegrable h volume 0 t0 :=
        hh_int.mono_set (by
          rw [uIcc_of_le ht0_nonneg, uIcc_of_le hq0_nonneg]
          exact Icc_subset_Icc_right ht0_le_q0)
      have h2 : IntervalIntegrable h volume t0 q :=
        hh_int.mono_set (by
          rw [uIcc_of_le hqt.le, uIcc_of_le hq0_nonneg]
          exact Icc_subset_Icc ht0_nonneg hq.2)
      rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
      have hpart1 : ∫ u in (0 : ℝ)..t0, h u ≤ 0 := by
        have hcongr : EqOn h (fun u => ((M.n : ℝ) - 1) * ((t u - u) * (1 - u) ^ (M.n - 2)))
            (uIcc 0 t0) := by
          intro u hu
          rw [uIcc_of_le ht0_nonneg] at hu
          dsimp [h, reserveIncreasePath]
          rw [min_eq_left hu.2]
          ring
        rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const_mul]
        exact mul_nonpos_of_nonneg_of_nonpos hn1.le (hborder t0 ⟨ht0_nonneg, ht0_le_q0⟩)
      have hpart2 : ∫ u in t0..q, h u ≤ 0 := by
        have hle := intervalIntegral.integral_mono_on hqt.le h2 intervalIntegrable_const
          (fun u hu => by
            dsimp [h, reserveIncreasePath]
            rw [min_eq_right hu.1]
            have hu_mem : u ∈ Icc (0 : ℝ) q0 := ⟨ht0_nonneg.trans hu.1, hu.2.trans hq.2⟩
            have htu : t u - t0 ≤ 0 := sub_nonpos.mpr (ht_bounds u hu_mem).2
            have h1u : 0 ≤ (1 - u) ^ (M.n - 2) :=
              pow_nonneg (by linarith [hu_mem.2, hq0_le_one]) _
            exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hn1.le htu) h1u)
        simpa using hle
      linarith
  -- Pointwise tangent bound on [0, q0]
  have hpt : ∀ q ∈ Icc (0 : ℝ) q0,
      M.cournotRev P.P (t q) q * M.W q -
        M.cournotRev P.P (reserveIncreasePath t0 q) q * M.W q ≤
      (M.n : ℝ) * (ϱ q * h q) := by
    intro q hq
    have hcase : reserveIncreasePath t0 q = q ∨
        (t q ≤ reserveIncreasePath t0 q ∧ reserveIncreasePath t0 q ≤ q) := by
      unfold reserveIncreasePath
      by_cases hqt : q ≤ t0
      · exact Or.inl (min_eq_left hqt)
      · push Not at hqt
        rw [min_eq_right hqt.le]
        exact Or.inr ⟨(ht_bounds q hq).2, hqt.le⟩
    have htan := cm_tangent_bound_general M P hpsi_mono (ht_dom q hq) (htS_dom q hq) hcase
    have hW : 0 ≤ M.W q := cm_W_nonneg M (hq.2.trans hq0_le_one)
    calc
      M.cournotRev P.P (t q) q * M.W q -
          M.cournotRev P.P (reserveIncreasePath t0 q) q * M.W q
          = (M.cournotRev P.P (t q) q - M.cournotRev P.P (reserveIncreasePath t0 q) q) * M.W q := by
            ring
      _ ≤ (ϱ q * (t q - reserveIncreasePath t0 q)) * M.W q :=
            mul_le_mul_of_nonneg_right htan hW
      _ = (M.n : ℝ) * (ϱ q * h q) := by
            dsimp [h, Market.W]; ring
  have hint_le :
      (∫ q in (0 : ℝ)..q0, M.cournotRev P.P (t q) q * M.W q) -
        (∫ q in (0 : ℝ)..q0, M.cournotRev P.P (reserveIncreasePath t0 q) q * M.W q) ≤
      (M.n : ℝ) * (ϱ q0 * ∫ q in (0 : ℝ)..q0, h q) := by
    rw [← intervalIntegral.integral_sub hint_t hint_tS]
    calc
      (∫ q in (0 : ℝ)..q0,
          M.cournotRev P.P (t q) q * M.W q -
            M.cournotRev P.P (reserveIncreasePath t0 q) q * M.W q)
          ≤ ∫ q in (0 : ℝ)..q0, (M.n : ℝ) * (ϱ q * h q) :=
            intervalIntegral.integral_mono_on hq0_nonneg (hint_t.sub hint_tS) hϱh_int hpt
      _ = (M.n : ℝ) * ∫ q in (0 : ℝ)..q0, ϱ q * h q :=
            intervalIntegral.integral_const_mul _ _
      _ ≤ (M.n : ℝ) * (ϱ q0 * ∫ q in (0 : ℝ)..q0, h q) :=
            mul_le_mul_of_nonneg_left
              (cm_integral_antitone_mul_le hq0_nonneg hϱ_cont hϱ_anti hh_int hH_le) hn.le
  have hϱ_q0_nonneg : 0 ≤ ϱ q0 := by
    have harg1 : reserveIncreasePath t0 q0 + ((M.m : ℝ) - 1) * q0 = 1 := by
      unfold reserveIncreasePath
      rw [min_eq_right ht0_le_q0]
      exact hq0_eq
    dsimp [ϱ]
    rw [harg1]
    exact MR_nonneg M P hpsi_mono hpsi_a ⟨zero_le_one, le_rfl⟩
  have hH_q0 : ∫ q in (0 : ℝ)..q0, h q ≤ 0 := hH_le q0 ⟨hq0_nonneg, le_rfl⟩
  have hprod : (M.n : ℝ) * (ϱ q0 * ∫ q in (0 : ℝ)..q0, h q) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hn.le (mul_nonpos_of_nonneg_of_nonpos hϱ_q0_nonneg hH_q0)
  linarith

/-- Decomposition of `reserveIncreaseRev` via `z = t0 + (m - 1)q` and binomial expansion,
valid on all of `[0, 1 / m]`. -/
private lemma reserveIncreaseRev_eq_decomp (P : M.InverseDemand)
    {t0 : ℝ} (ht0 : t0 ∈ Icc (0 : ℝ) (1 / (M.m : ℝ))) :
    let q0 := (1 - t0) / ((M.m : ℝ) - 1)
    let Am : ℝ → ℝ := fun z => ((M.m : ℝ) - 1 - z) / ((M.m : ℝ) - 1)
    let cm : ℝ := 1 / ((M.m : ℝ) - 1)
    reserveIncreaseRev M P.P M.rhoStar t0 =
      (M.n : ℝ) * M.rhoStar * t0 * (1 - q0) ^ (M.n - 1) +
        (∫ q in (0 : ℝ)..t0, M.cournotRev P.P q q * M.W q) +
        (M.n : ℝ) * ((M.n : ℝ) - 1) * cm * t0 *
          ∑ k ∈ Finset.range (M.n - 1),
            (((M.n - 2).choose k : ℝ) * (cm * t0) ^ k *
              ∫ z in ((M.m : ℝ) * t0)..1, P.P z * (Am z) ^ (M.n - 2 - k)) := by
  intro q0 Am cm
  have hm : (0 : ℝ) < M.m := M.m_pos_real
  have hm1 : (0 : ℝ) < (M.m : ℝ) - 1 := M.m_sub_one_pos_real
  have hmR : (2 : ℝ) ≤ M.m := by exact_mod_cast M.hm
  have ht0_le_q0 : t0 ≤ q0 := by
    dsimp [q0]
    rw [le_div_iff₀ hm1]
    have hmt0 : (M.m : ℝ) * t0 ≤ 1 := by
      have h1 := ht0.2; rwa [le_div_iff₀ hm, mul_comm] at h1
    linarith
  have hq0_nonneg : 0 ≤ q0 := ht0.1.trans ht0_le_q0
  have hq0_le_one : q0 ≤ 1 := by
    dsimp [q0]; rw [div_le_one hm1]; linarith [ht0.1]
  have htS_mono : MonotoneOn (reserveIncreasePath t0) (Icc 0 q0) :=
    fun _ _ _ _ hxy => min_le_min_right t0 hxy
  have htS_dom : ∀ q ∈ Icc (0 : ℝ) q0,
      reserveIncreasePath t0 q + ((M.m : ℝ) - 1) * q ∈ Icc (0 : ℝ) 1 := by
    intro q hq
    refine ⟨?_, ?_⟩
    · have : 0 ≤ min q t0 := le_min hq.1 ht0.1
      unfold reserveIncreasePath; nlinarith [hq.1]
    · have : min q t0 ≤ t0 := min_le_right q t0
      have hqeq : t0 + ((M.m : ℝ) - 1) * q0 = 1 := by
        dsimp [q0]; field_simp [hm1.ne']; ring
      unfold reserveIncreasePath; nlinarith [hq.2]
  have hint_full : IntervalIntegrable
      (fun q => M.cournotRev P.P (reserveIncreasePath t0 q) q * M.W q) volume 0 q0 :=
    monotoneOn_cournot_integrable M hq0_nonneg P htS_mono htS_dom
  have hint1 := hint_full.mono_set (by
    rw [uIcc_of_le ht0.1, uIcc_of_le hq0_nonneg]
    exact Icc_subset_Icc_right ht0_le_q0)
  have hint2 := hint_full.mono_set (by
    rw [uIcc_of_le ht0_le_q0, uIcc_of_le hq0_nonneg]
    exact Icc_subset_Icc ht0.1 le_rfl)
  unfold reserveIncreaseRev pathRev
  simp only [sub_zero]
  change (M.n : ℝ) * M.rhoStar * t0 * (1 - q0) ^ (M.n - 1) +
      (∫ q in (0 : ℝ)..q0, M.cournotRev P.P (reserveIncreasePath t0 q) q * M.W q) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
  -- Simplify first integral on [0, t0]
  have h1 : (∫ q in (0 : ℝ)..t0, M.cournotRev P.P (reserveIncreasePath t0 q) q * M.W q) =
      ∫ q in (0 : ℝ)..t0, M.cournotRev P.P q q * M.W q := by
    apply intervalIntegral.integral_congr
    intro q hq
    rw [uIcc_of_le ht0.1] at hq
    simp [reserveIncreasePath, min_eq_left hq.2]
  -- Simplify second integral on [t0, q0] via substitution z = (m - 1)q + t0
  have h2 : (∫ q in t0..q0, M.cournotRev P.P (reserveIncreasePath t0 q) q * M.W q) =
      (M.n : ℝ) * ((M.n : ℝ) - 1) * cm * t0 *
        ∑ k ∈ Finset.range (M.n - 1),
          (((M.n - 2).choose k : ℝ) * (cm * t0) ^ k *
            ∫ z in ((M.m : ℝ) * t0)..1, P.P z * (Am z) ^ (M.n - 2 - k)) := by
    have hcongr2 : (∫ q in t0..q0, M.cournotRev P.P (reserveIncreasePath t0 q) q * M.W q) =
        ∫ q in t0..q0, (M.n : ℝ) * ((M.n : ℝ) - 1) * t0 *
          (P.P (((M.m : ℝ) - 1) * q + t0) *
            (Am (((M.m : ℝ) - 1) * q + t0) + cm * t0) ^ (M.n - 2)) := by
      apply intervalIntegral.integral_congr
      intro q hq
      rw [uIcc_of_le ht0_le_q0] at hq
      dsimp only [Market.cournotRev, Market.W, reserveIncreasePath]
      rw [min_eq_right hq.1]
      have harg : t0 + ((M.m : ℝ) - 1) * q = ((M.m : ℝ) - 1) * q + t0 := by ring
      have h1q : 1 - q = Am (((M.m : ℝ) - 1) * q + t0) + cm * t0 := by
        dsimp [Am, cm]; field_simp [hm1.ne']; ring
      rw [harg, h1q]
      ring
    rw [hcongr2, intervalIntegral.integral_const_mul]
    have hsub := intervalIntegral.integral_comp_mul_add
      (f := fun z => P.P z * (Am z + cm * t0) ^ (M.n - 2))
      (a := t0) (b := q0) hm1.ne' t0
    have ha_end : ((M.m : ℝ) - 1) * t0 + t0 = (M.m : ℝ) * t0 := by ring
    have hb_end : ((M.m : ℝ) - 1) * q0 + t0 = 1 := by
      dsimp [q0]; field_simp [hm1.ne']; ring
    rw [ha_end, hb_end] at hsub
    rw [hsub]
    -- Expand (Am z + cm * t0)^(n - 2) using add_pow
    have hmt0_le : (M.m : ℝ) * t0 ≤ 1 := by
      have h1 := ht0.2; rwa [le_div_iff₀ hm, mul_comm] at h1
    have hmt0_nonneg : 0 ≤ (M.m : ℝ) * t0 := mul_nonneg hm.le ht0.1
    have hbin : (∫ z in ((M.m : ℝ) * t0)..1, P.P z * (Am z + cm * t0) ^ (M.n - 2)) =
        ∑ k ∈ Finset.range (M.n - 1),
          (((M.n - 2).choose k : ℝ) * (cm * t0) ^ k *
            ∫ z in ((M.m : ℝ) * t0)..1, P.P z * (Am z) ^ (M.n - 2 - k)) := by
      have hcongr_bin :
          (∫ z in ((M.m : ℝ) * t0)..1, P.P z * (Am z + cm * t0) ^ (M.n - 2)) =
          ∫ z in ((M.m : ℝ) * t0)..1,
            ∑ k ∈ Finset.range (M.n - 1),
              (((M.n - 2).choose k : ℝ) * (cm * t0) ^ k) * (P.P z * (Am z) ^ (M.n - 2 - k)) := by
        apply intervalIntegral.integral_congr
        intro z _
        dsimp only
        have hsucc : M.n - 1 = (M.n - 2) + 1 := by have := M.hn; omega
        rw [hsucc, add_comm (Am z) (cm * t0), add_pow, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      rw [hcongr_bin, intervalIntegral.integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro k _
        rw [intervalIntegral.integral_const_mul]
      · intro k _
        have hcont : ContinuousOn
            (fun z => (((M.n - 2).choose k : ℝ) * (cm * t0) ^ k) *
              (P.P z * (Am z) ^ (M.n - 2 - k))) (uIcc ((M.m : ℝ) * t0) 1) := by
          rw [uIcc_of_le hmt0_le]
          apply continuousOn_const.mul
          apply (P.hP_cont.mono (Icc_subset_Icc_left hmt0_nonneg)).mul
          exact (((continuous_const.sub continuous_id).div_const _).pow _).continuousOn
        exact hcont.intervalIntegrable
    rw [hbin, smul_eq_mul]
    dsimp [cm]
    ring
  rw [h1, h2]
  ring

/-- Continuity of `reserveIncreaseRev` on `[0, 1 / m]`. -/
lemma reserveIncreaseRev_continuousOn (P : M.InverseDemand) :
    ContinuousOn (fun t0 => reserveIncreaseRev M P.P M.rhoStar t0) (Icc 0 (1 / (M.m : ℝ))) := by
  let q0 : ℝ → ℝ := fun t0 => (1 - t0) / ((M.m : ℝ) - 1)
  let Am : ℝ → ℝ := fun z => ((M.m : ℝ) - 1 - z) / ((M.m : ℝ) - 1)
  let cm : ℝ := 1 / ((M.m : ℝ) - 1)
  let G : ℝ → ℝ := fun t0 =>
    (M.n : ℝ) * M.rhoStar * t0 * (1 - q0 t0) ^ (M.n - 1) +
      (∫ q in (0 : ℝ)..t0, M.cournotRev P.P q q * M.W q) +
      (M.n : ℝ) * ((M.n : ℝ) - 1) * cm * t0 *
        ∑ k ∈ Finset.range (M.n - 1),
          (((M.n - 2).choose k : ℝ) * (cm * t0) ^ k *
            ∫ z in ((M.m : ℝ) * t0)..1, P.P z * (Am z) ^ (M.n - 2 - k))
  have hcongr : EqOn (fun t0 => reserveIncreaseRev M P.P M.rhoStar t0) G (Icc 0 (1 / (M.m : ℝ))) :=
    fun t0 ht0 => reserveIncreaseRev_eq_decomp M P ht0
  rw [continuousOn_congr hcongr]
  have hm : (0 : ℝ) < M.m := M.m_pos_real
  -- Piece 1: boundary term
  have hc1 : ContinuousOn
      (fun t0 => (M.n : ℝ) * M.rhoStar * t0 * (1 - q0 t0) ^ (M.n - 1))
      (Icc 0 (1 / (M.m : ℝ))) :=
    (((continuous_const.mul continuous_id).mul
      ((continuous_const.sub ((continuous_const.sub continuous_id).div_const _)).pow _))).continuousOn
  -- Piece 2: ∫_0^{t0} Π(q, q) W(q) dq
  have hc2 : ContinuousOn
      (fun t0 => ∫ q in (0 : ℝ)..t0, M.cournotRev P.P q q * M.W q)
      (Icc 0 (1 / (M.m : ℝ))) := by
    have hcont_int : ContinuousOn (fun q => M.cournotRev P.P q q * M.W q)
        (Icc 0 (1 / (M.m : ℝ))) := by
      unfold Market.cournotRev
      apply (continuousOn_id.mul ?_).mul (cm_W_continuous M).continuousOn
      apply P.hP_cont.comp ((continuous_id.add (continuous_const.mul continuous_id)).continuousOn)
      intro q hq
      change q + ((M.m : ℝ) - 1) * q ∈ Icc (0 : ℝ) 1
      have hq_arg : q + ((M.m : ℝ) - 1) * q = (M.m : ℝ) * q := by ring
      rw [hq_arg]
      exact ⟨mul_nonneg hm.le hq.1, by have h1 := hq.2; rwa [le_div_iff₀ hm, mul_comm] at h1⟩
    rw [← uIcc_of_le (inv_m_pos M).le]
    apply intervalIntegral.continuousOn_primitive_interval
    rw [uIcc_of_le (inv_m_pos M).le]
    exact hcont_int.integrableOn_Icc
  -- Piece 3: sum over k of ∫_{m t0}^1 P(z) * Am(z)^(n - 2 - k) dz
  have hc3 : ContinuousOn
      (fun t0 => (M.n : ℝ) * ((M.n : ℝ) - 1) * cm * t0 *
        ∑ k ∈ Finset.range (M.n - 1),
          (((M.n - 2).choose k : ℝ) * (cm * t0) ^ k *
            ∫ z in ((M.m : ℝ) * t0)..1, P.P z * (Am z) ^ (M.n - 2 - k)))
      (Icc 0 (1 / (M.m : ℝ))) := by
    apply (continuous_const.mul continuous_id).continuousOn.mul
    have hterm : ∀ k ∈ Finset.range (M.n - 1), ContinuousOn
        (fun t0 => ((M.n - 2).choose k : ℝ) * (cm * t0) ^ k *
          ∫ z in ((M.m : ℝ) * t0)..1, P.P z * (Am z) ^ (M.n - 2 - k))
        (Icc 0 (1 / (M.m : ℝ))) := by
      intro k _
      apply (continuous_const.mul ((continuous_const.mul continuous_id).pow k)).continuousOn.mul
      have hφ_cont : ContinuousOn (fun z => P.P z * (Am z) ^ (M.n - 2 - k)) (Icc 0 1) :=
        P.hP_cont.mul ((((continuous_const.sub continuous_id).div_const _).pow _).continuousOn)
      have hprim : ContinuousOn
          (fun x => ∫ z in x..1, P.P z * (Am z) ^ (M.n - 2 - k)) (Icc 0 1) := by
        have hneg : ContinuousOn
            (fun x => -(∫ z in (1 : ℝ)..x, P.P z * (Am z) ^ (M.n - 2 - k))) (Icc 0 1) := by
          apply ContinuousOn.neg
          rw [← Set.uIcc_of_ge zero_le_one]
          apply intervalIntegral.continuousOn_primitive_interval
          rw [Set.uIcc_of_ge zero_le_one]
          exact hφ_cont.integrableOn_Icc
        refine hneg.congr (fun x _ => ?_)
        rw [intervalIntegral.integral_symm 1 x]
      apply hprim.comp (continuous_const.mul continuous_id).continuousOn
      intro t0 ht0
      exact ⟨mul_nonneg hm.le ht0.1, by have h1 := ht0.2; rwa [le_div_iff₀ hm, mul_comm] at h1⟩
    clear hc1 hc2 hcongr
    suffices ∀ (S : Finset ℕ),
        (∀ k ∈ S, ContinuousOn
          (fun t0 => ((M.n - 2).choose k : ℝ) * (cm * t0) ^ k *
            ∫ z in ((M.m : ℝ) * t0)..1, P.P z * (Am z) ^ (M.n - 2 - k))
          (Icc 0 (1 / (M.m : ℝ)))) →
        ContinuousOn
          (fun t0 => ∑ k ∈ S, ((M.n - 2).choose k : ℝ) * (cm * t0) ^ k *
            ∫ z in ((M.m : ℝ) * t0)..1, P.P z * (Am z) ^ (M.n - 2 - k))
          (Icc 0 (1 / (M.m : ℝ))) from this _ hterm
    intro S hS
    induction S using Finset.induction_on with
    | empty => simpa using continuousOn_const
    | @insert k s hks ih =>
      have hcongr_sum : EqOn
          (fun t0 => ∑ j ∈ insert k s, ((M.n - 2).choose j : ℝ) * (cm * t0) ^ j *
            ∫ z in ((M.m : ℝ) * t0)..1, P.P z * (Am z) ^ (M.n - 2 - j))
          (fun t0 => (((M.n - 2).choose k : ℝ) * (cm * t0) ^ k *
            ∫ z in ((M.m : ℝ) * t0)..1, P.P z * (Am z) ^ (M.n - 2 - k)) +
            ∑ j ∈ s, ((M.n - 2).choose j : ℝ) * (cm * t0) ^ j *
              ∫ z in ((M.m : ℝ) * t0)..1, P.P z * (Am z) ^ (M.n - 2 - j))
          (Icc 0 (1 / (M.m : ℝ))) := fun t0 _ => Finset.sum_insert hks
      rw [continuousOn_congr hcongr_sum]
      exact (hS k (Finset.mem_insert_self k s)).add
        (ih (fun j hj => hS j (Finset.mem_insert_of_mem hj)))
  exact (hc1.add hc2).add hc3

/-- Exact derivative of `reserveIncreaseRev` on `(0, 1 / m)` (Appendix B, eq. (839)-(844)). -/
theorem reserveIncreaseRev_hasDerivAt (P : M.InverseDemand)
    {t0 : ℝ} (ht0 : t0 ∈ Ioo (0 : ℝ) (1 / (M.m : ℝ))) :
    let q0 := (1 - t0) / ((M.m : ℝ) - 1)
    HasDerivAt (fun s => reserveIncreaseRev M P.P M.rhoStar s)
      ((M.n : ℝ) * (M.rhoStar * ((M.m : ℝ) - 2) * (q0 - t0) * (1 - q0) ^ (M.n - 2)) +
        ((M.n : ℝ) * ((M.n : ℝ) - 1) / ((M.m : ℝ) - 1)) *
          ∫ z in ((M.m : ℝ) * t0)..1,
            (P.P z + t0 * (-1 / M.f (P.P z))) *
              (1 - (z - t0) / ((M.m : ℝ) - 1)) ^ (M.n - 2))
      t0 := by
  intro q0
  have hm : (0 : ℝ) < M.m := M.m_pos_real
  have hm1 : (0 : ℝ) < (M.m : ℝ) - 1 := M.m_sub_one_pos_real
  have hmR : (2 : ℝ) ≤ M.m := by exact_mod_cast M.hm
  have hn : (0 : ℝ) < M.n := M.n_pos_real
  have hn1 : (0 : ℝ) < (M.n : ℝ) - 1 := M.n_sub_one_pos_real
  have hmt0_pos : 0 < (M.m : ℝ) * t0 := mul_pos hm ht0.1
  have hmt0_lt1 : (M.m : ℝ) * t0 < 1 := by
    have := ht0.2; rwa [lt_div_iff₀ hm, mul_comm] at this
  let Am : ℝ → ℝ := fun z => ((M.m : ℝ) - 1 - z) / ((M.m : ℝ) - 1)
  let cm : ℝ := 1 / ((M.m : ℝ) - 1)
  let qf : ℝ → ℝ := fun s => (1 - s) / ((M.m : ℝ) - 1)
  let G : ℝ → ℝ := fun s =>
    (M.n : ℝ) * M.rhoStar * s * (1 - qf s) ^ (M.n - 1) +
      (∫ q in (0 : ℝ)..s, M.cournotRev P.P q q * M.W q) +
      (M.n : ℝ) * ((M.n : ℝ) - 1) * cm * s *
        ∑ k ∈ Finset.range (M.n - 1),
          (((M.n - 2).choose k : ℝ) * (cm * s) ^ k *
            ∫ z in ((M.m : ℝ) * s)..1, P.P z * (Am z) ^ (M.n - 2 - k))
  -- G agrees with reserveIncreaseRev on a neighborhood of t0
  have heq_nhds : (fun s => reserveIncreaseRev M P.P M.rhoStar s) =ᶠ[nhds t0] G := by
    filter_upwards [Ioo_mem_nhds ht0.1 ht0.2] with s hs
    exact reserveIncreaseRev_eq_decomp M P (Ioo_subset_Icc_self hs)
  suffices hG : HasDerivAt G
      ((M.n : ℝ) * (M.rhoStar * ((M.m : ℝ) - 2) * (q0 - t0) * (1 - q0) ^ (M.n - 2)) +
        ((M.n : ℝ) * ((M.n : ℝ) - 1) / ((M.m : ℝ) - 1)) *
          ∫ z in ((M.m : ℝ) * t0)..1,
            (P.P z + t0 * (-1 / M.f (P.P z))) *
              (1 - (z - t0) / ((M.m : ℝ) - 1)) ^ (M.n - 2))
      t0 from hG.congr_of_eventuallyEq heq_nhds
  -- Derivative of piece 1: n * ρ* * s * (1 - qf s)^(n - 1)
  have hd1 : HasDerivAt
      (fun s => (M.n : ℝ) * M.rhoStar * s * (1 - qf s) ^ (M.n - 1))
      ((M.n : ℝ) * M.rhoStar * (1 - q0) ^ (M.n - 1) +
        (M.n : ℝ) * M.rhoStar * t0 * (((M.n : ℝ) - 1) * (1 - q0) ^ (M.n - 2) * cm)) t0 := by
    have hqf : HasDerivAt (fun s => 1 - qf s) cm t0 := by
      have h1 : HasDerivAt (fun s => 1 - s) (-1) t0 := by
        simpa using (hasDerivAt_const t0 (1 : ℝ)).fun_sub (hasDerivAt_id' t0)
      have h2 : HasDerivAt qf (-1 / ((M.m : ℝ) - 1)) t0 := h1.div_const _
      have h3 := (hasDerivAt_const t0 (1 : ℝ)).fun_sub h2
      convert h3 using 1
      dsimp [cm]; ring
    have hpow := hqf.fun_pow (M.n - 1)
    have hlin : HasDerivAt (fun s => (M.n : ℝ) * M.rhoStar * s) ((M.n : ℝ) * M.rhoStar) t0 := by
      simpa using (hasDerivAt_id' t0).const_mul ((M.n : ℝ) * M.rhoStar)
    have hmul := hlin.fun_mul hpow
    have hn_cast : ((M.n - 1 : ℕ) : ℝ) = (M.n : ℝ) - 1 := by
      rw [Nat.cast_sub (by have := M.hn; omega), Nat.cast_one]
    have hn_sub : M.n - 1 - 1 = M.n - 2 := by omega
    convert hmul using 1
    rw [hn_cast, hn_sub]
  -- Derivative of piece 2: ∫_0^s Π(q, q) W(q) dq
  have hd2 : HasDerivAt
      (fun s => ∫ q in (0 : ℝ)..s, M.cournotRev P.P q q * M.W q)
      (M.cournotRev P.P t0 t0 * M.W t0) t0 := by
    have hcont_int : ContinuousOn (fun q => M.cournotRev P.P q q * M.W q)
        (Icc 0 (1 / (M.m : ℝ))) := by
      unfold Market.cournotRev
      apply (continuousOn_id.mul ?_).mul (cm_W_continuous M).continuousOn
      apply P.hP_cont.comp ((continuous_id.add (continuous_const.mul continuous_id)).continuousOn)
      intro q hq
      change q + ((M.m : ℝ) - 1) * q ∈ Icc (0 : ℝ) 1
      have hq_arg : q + ((M.m : ℝ) - 1) * q = (M.m : ℝ) * q := by ring
      rw [hq_arg]
      exact ⟨mul_nonneg hm.le hq.1, by have h1 := hq.2; rwa [le_div_iff₀ hm, mul_comm] at h1⟩
    have hmeas : StronglyMeasurableAtFilter
        (fun q => M.cournotRev P.P q q * M.W q) (nhds t0) volume :=
      (hcont_int.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo t0 ht0
    have hint_t0 : IntervalIntegrable (fun q => M.cournotRev P.P q q * M.W q) volume 0 t0 :=
      (hcont_int.mono (by rw [uIcc_of_le ht0.1.le]; exact Icc_subset_Icc_right ht0.2.le)).intervalIntegrable
    have hca : ContinuousAt (fun q => M.cournotRev P.P q q * M.W q) t0 :=
      hcont_int.continuousAt (Icc_mem_nhds ht0.1 ht0.2)
    exact intervalIntegral.integral_hasDerivAt_right hint_t0 hmeas hca
  -- Derivative of piece 3: S(s) = ∑ k, choose * (cm * s)^k * ∫_{m s}^1 P(z) Am(z)^(n - 2 - k) dz
  let S : ℝ → ℝ := fun s =>
    ∑ k ∈ Finset.range (M.n - 1),
      (((M.n - 2).choose k : ℝ) * (cm * s) ^ k *
        ∫ z in ((M.m : ℝ) * s)..1, P.P z * (Am z) ^ (M.n - 2 - k))
  let S' : ℝ :=
    ∑ k ∈ Finset.range (M.n - 1),
      ((((M.n - 2).choose k : ℝ) * ((k : ℝ) * (cm * t0) ^ (k - 1) * cm)) *
          (∫ z in ((M.m : ℝ) * t0)..1, P.P z * (Am z) ^ (M.n - 2 - k)) +
        (((M.n - 2).choose k : ℝ) * (cm * t0) ^ k) *
          (-(M.m : ℝ) * (P.P ((M.m : ℝ) * t0) * (Am ((M.m : ℝ) * t0)) ^ (M.n - 2 - k))))
  have hdS : HasDerivAt S S' t0 := by
    apply HasDerivAt.fun_sum
    intro k _
    have hφ_cont : ContinuousOn (fun z => P.P z * (Am z) ^ (M.n - 2 - k)) (Icc 0 1) :=
      P.hP_cont.mul ((((continuous_const.sub continuous_id).div_const _).pow _).continuousOn)
    have hint_k : IntervalIntegrable (fun z => P.P z * (Am z) ^ (M.n - 2 - k)) volume
        ((M.m : ℝ) * t0) 1 :=
      (hφ_cont.mono (by
        rw [uIcc_of_le hmt0_lt1.le]
        exact Icc_subset_Icc_left hmt0_pos.le)).intervalIntegrable
    have hca_k : ContinuousAt (fun z => P.P z * (Am z) ^ (M.n - 2 - k)) ((M.m : ℝ) * t0) :=
      hφ_cont.continuousAt (Icc_mem_nhds hmt0_pos hmt0_lt1)
    have hmeas_k : StronglyMeasurableAtFilter
        (fun z => P.P z * (Am z) ^ (M.n - 2 - k)) (nhds ((M.m : ℝ) * t0)) volume :=
      (hφ_cont.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo
        ((M.m : ℝ) * t0) ⟨hmt0_pos, hmt0_lt1⟩
    have hleft : HasDerivAt (fun x => ∫ z in x..1, P.P z * (Am z) ^ (M.n - 2 - k))
        (-(P.P ((M.m : ℝ) * t0) * (Am ((M.m : ℝ) * t0)) ^ (M.n - 2 - k))) ((M.m : ℝ) * t0) :=
      intervalIntegral.integral_hasDerivAt_left hint_k hmeas_k hca_k
    have hcomp_k : HasDerivAt
        (fun s => ∫ z in ((M.m : ℝ) * s)..1, P.P z * (Am z) ^ (M.n - 2 - k))
        (-(M.m : ℝ) * (P.P ((M.m : ℝ) * t0) * (Am ((M.m : ℝ) * t0)) ^ (M.n - 2 - k))) t0 := by
      have hm_lin : HasDerivAt (fun s => (M.m : ℝ) * s) (M.m : ℝ) t0 := by
        simpa using (hasDerivAt_id' t0).const_mul (M.m : ℝ)
      have hc := hleft.comp t0 hm_lin
      have hceq : HasDerivAt (fun s => ∫ z in ((M.m : ℝ) * s)..1, P.P z * (Am z) ^ (M.n - 2 - k))
          (-(P.P ((M.m : ℝ) * t0) * (Am ((M.m : ℝ) * t0)) ^ (M.n - 2 - k)) * (M.m : ℝ)) t0 := hc
      convert hceq using 1
      ring
    have hpow_k : HasDerivAt
        (fun s => ((M.n - 2).choose k : ℝ) * (cm * s) ^ k)
        (((M.n - 2).choose k : ℝ) * ((k : ℝ) * (cm * t0) ^ (k - 1) * cm)) t0 := by
      have hcm_lin : HasDerivAt (fun s => cm * s) cm t0 := by
        simpa using (hasDerivAt_id' t0).const_mul cm
      exact (hcm_lin.fun_pow k).const_mul _
    exact hpow_k.fun_mul hcomp_k
  -- Combine piece 3 with outer factor n*(n-1)*cm*s
  have hd3 : HasDerivAt
      (fun s => (M.n : ℝ) * ((M.n : ℝ) - 1) * cm * s * S s)
      ((M.n : ℝ) * ((M.n : ℝ) - 1) * cm * S t0 +
        (M.n : ℝ) * ((M.n : ℝ) - 1) * cm * t0 * S') t0 := by
    have hlin : HasDerivAt (fun s => (M.n : ℝ) * ((M.n : ℝ) - 1) * cm * s)
        ((M.n : ℝ) * ((M.n : ℝ) - 1) * cm) t0 := by
      simpa using (hasDerivAt_id' t0).const_mul ((M.n : ℝ) * ((M.n : ℝ) - 1) * cm)
    exact hlin.fun_mul hdS
  -- Simplify S t0 and S' back into integrals!
  have hAm_eq : ∀ z, Am z + cm * t0 = 1 - (z - t0) / ((M.m : ℝ) - 1) := by
    intro z; dsimp [Am, cm]; field_simp [hm1.ne']; ring
  have hS_val : S t0 = ∫ z in ((M.m : ℝ) * t0)..1,
      P.P z * (1 - (z - t0) / ((M.m : ℝ) - 1)) ^ (M.n - 2) := by
    dsimp [S]
    have hcongr : (∫ z in ((M.m : ℝ) * t0)..1,
        P.P z * (1 - (z - t0) / ((M.m : ℝ) - 1)) ^ (M.n - 2)) =
        ∫ z in ((M.m : ℝ) * t0)..1,
          ∑ k ∈ Finset.range (M.n - 1),
            (((M.n - 2).choose k : ℝ) * (cm * t0) ^ k) * (P.P z * (Am z) ^ (M.n - 2 - k)) := by
      apply intervalIntegral.integral_congr
      intro z _
      dsimp only
      rw [← hAm_eq z]
      have hsucc : M.n - 1 = (M.n - 2) + 1 := by have := M.hn; omega
      rw [hsucc, add_comm (Am z) (cm * t0), add_pow, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k _; ring
    rw [hcongr, intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro k _
      rw [intervalIntegral.integral_const_mul]
    · intro k _
      have hcont : ContinuousOn
          (fun z => (((M.n - 2).choose k : ℝ) * (cm * t0) ^ k) *
            (P.P z * (Am z) ^ (M.n - 2 - k))) (uIcc ((M.m : ℝ) * t0) 1) := by
        rw [uIcc_of_le hmt0_lt1.le]
        apply continuousOn_const.mul
        apply (P.hP_cont.mono (Icc_subset_Icc_left hmt0_pos.le)).mul
        exact (((continuous_const.sub continuous_id).div_const _).pow _).continuousOn
      exact hcont.intervalIntegrable
  have hS'_val : S' =
      cm * (∫ z in ((M.m : ℝ) * t0)..1,
        P.P z * (((M.n - 2 : ℕ) : ℝ) * (1 - (z - t0) / ((M.m : ℝ) - 1)) ^ (M.n - 3))) -
      (M.m : ℝ) * P.P ((M.m : ℝ) * t0) * (1 - t0) ^ (M.n - 2) := by
    dsimp [S']
    rw [Finset.sum_add_distrib]
    have hpart1 :
        ∑ k ∈ Finset.range (M.n - 1),
          ((M.n - 2).choose k : ℝ) * ((k : ℝ) * (cm * t0) ^ (k - 1) * cm) *
            (∫ z in ((M.m : ℝ) * t0)..1, P.P z * (Am z) ^ (M.n - 2 - k)) =
        cm * (∫ z in ((M.m : ℝ) * t0)..1,
          P.P z * (((M.n - 2 : ℕ) : ℝ) * (1 - (z - t0) / ((M.m : ℝ) - 1)) ^ (M.n - 3))) := by
      have hpull :
          ∑ k ∈ Finset.range (M.n - 1),
            ((M.n - 2).choose k : ℝ) * ((k : ℝ) * (cm * t0) ^ (k - 1) * cm) *
              (∫ z in ((M.m : ℝ) * t0)..1, P.P z * (Am z) ^ (M.n - 2 - k)) =
          ∫ z in ((M.m : ℝ) * t0)..1,
            ∑ k ∈ Finset.range (M.n - 1),
              (((M.n - 2).choose k : ℝ) * ((k : ℝ) * (cm * t0) ^ (k - 1) * cm)) *
                (P.P z * (Am z) ^ (M.n - 2 - k)) := by
        rw [intervalIntegral.integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro k _
          rw [intervalIntegral.integral_const_mul]
        · intro k _
          have hcont : ContinuousOn
              (fun z => (((M.n - 2).choose k : ℝ) * ((k : ℝ) * (cm * t0) ^ (k - 1) * cm)) *
                (P.P z * (Am z) ^ (M.n - 2 - k))) (uIcc ((M.m : ℝ) * t0) 1) := by
            rw [uIcc_of_le hmt0_lt1.le]
            apply continuousOn_const.mul
            apply (P.hP_cont.mono (Icc_subset_Icc_left hmt0_pos.le)).mul
            exact (((continuous_const.sub continuous_id).div_const _).pow _).continuousOn
          exact hcont.intervalIntegrable
      rw [hpull, ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro z _
      have hsucc : M.n - 1 = (M.n - 2) + 1 := by have := M.hn; omega
      have hsub3 : M.n - 2 - 1 = M.n - 3 := by omega
      have hsum_id := sum_choose_deriv (M.n - 2) (cm * t0) (Am z)
      rw [hsub3, add_comm (cm * t0) (Am z), hAm_eq z] at hsum_id
      rw [hsucc]
      calc
        ∑ k ∈ Finset.range ((M.n - 2) + 1),
            ((M.n - 2).choose k : ℝ) * ((k : ℝ) * (cm * t0) ^ (k - 1) * cm) *
              (P.P z * (Am z) ^ (M.n - 2 - k))
            = cm * P.P z *
                ∑ k ∈ Finset.range ((M.n - 2) + 1),
                  ((k : ℝ) * (cm * t0) ^ (k - 1)) * (Am z) ^ (M.n - 2 - k) *
                    ((M.n - 2).choose k : ℝ) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl; intro k _; ring
        _ = cm * (P.P z * (((M.n - 2 : ℕ) : ℝ) * (1 - (z - t0) / ((M.m : ℝ) - 1)) ^ (M.n - 3))) := by
              rw [hsum_id]; ring
    have hpart2 :
        ∑ k ∈ Finset.range (M.n - 1),
          ((M.n - 2).choose k : ℝ) * (cm * t0) ^ k *
            (-(M.m : ℝ) * (P.P ((M.m : ℝ) * t0) * (Am ((M.m : ℝ) * t0)) ^ (M.n - 2 - k))) =
        -((M.m : ℝ) * P.P ((M.m : ℝ) * t0) * (1 - t0) ^ (M.n - 2)) := by
      have hsucc : M.n - 1 = (M.n - 2) + 1 := by have := M.hn; omega
      have hbase : Am ((M.m : ℝ) * t0) + cm * t0 = 1 - t0 := by
        rw [hAm_eq ((M.m : ℝ) * t0)]
        field_simp [hm1.ne']
      rw [hsucc]
      calc
        ∑ k ∈ Finset.range ((M.n - 2) + 1),
            ((M.n - 2).choose k : ℝ) * (cm * t0) ^ k *
              (-(M.m : ℝ) * (P.P ((M.m : ℝ) * t0) * (Am ((M.m : ℝ) * t0)) ^ (M.n - 2 - k)))
            = -(M.m : ℝ) * P.P ((M.m : ℝ) * t0) *
                ∑ k ∈ Finset.range ((M.n - 2) + 1),
                  (cm * t0) ^ k * (Am ((M.m : ℝ) * t0)) ^ (M.n - 2 - k) *
                    ((M.n - 2).choose k : ℝ) := by
              rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
        _ = -(M.m : ℝ) * P.P ((M.m : ℝ) * t0) * (cm * t0 + Am ((M.m : ℝ) * t0)) ^ (M.n - 2) := by
              rw [← add_pow]
        _ = -((M.m : ℝ) * P.P ((M.m : ℝ) * t0) * (1 - t0) ^ (M.n - 2)) := by
              rw [add_comm, hbase]; ring
    rw [hpart1, hpart2]; ring
  -- Integration by parts on [m * t0, 1] for ∫ P(z) * d/dz (-(1 - (z - t0)/(m - 1))^(n - 2)) dz
  have hibp :
      cm * (∫ z in ((M.m : ℝ) * t0)..1,
        P.P z * (((M.n - 2 : ℕ) : ℝ) * (1 - (z - t0) / ((M.m : ℝ) - 1)) ^ (M.n - 3))) =
      P.P ((M.m : ℝ) * t0) * (1 - t0) ^ (M.n - 2) - M.a * (1 - q0) ^ (M.n - 2) +
        ∫ z in ((M.m : ℝ) * t0)..1,
          (-1 / M.f (P.P z)) * (1 - (z - t0) / ((M.m : ℝ) - 1)) ^ (M.n - 2) := by
    let v : ℝ → ℝ := fun z => (1 - (z - t0) / ((M.m : ℝ) - 1)) ^ (M.n - 2)
    let v' : ℝ → ℝ := fun z =>
      -cm * (((M.n - 2 : ℕ) : ℝ) * (1 - (z - t0) / ((M.m : ℝ) - 1)) ^ (M.n - 3))
    have hu_cont : ContinuousOn P.P (uIcc ((M.m : ℝ) * t0) 1) := by
      rw [uIcc_of_le hmt0_lt1.le]
      exact P.hP_cont.mono (Icc_subset_Icc_left hmt0_pos.le)
    have hv_cont : ContinuousOn v (uIcc ((M.m : ℝ) * t0) 1) :=
      (((continuous_const.sub ((continuous_id.sub continuous_const).div_const _)).pow _)).continuousOn
    have hu_deriv : ∀ z ∈ Ioo (min ((M.m : ℝ) * t0) 1) (max ((M.m : ℝ) * t0) 1),
        HasDerivAt P.P (-1 / M.f (P.P z)) z := by
      intro z hz
      rw [min_eq_left hmt0_lt1.le, max_eq_right hmt0_lt1.le] at hz
      exact P.hP_deriv_open z ⟨hmt0_pos.trans hz.1, hz.2⟩
    have hv_deriv : ∀ z ∈ Ioo (min ((M.m : ℝ) * t0) 1) (max ((M.m : ℝ) * t0) 1),
        HasDerivAt v (v' z) z := by
      intro z _
      have hlin : HasDerivAt (fun x => 1 - (x - t0) / ((M.m : ℝ) - 1)) (-cm) z := by
        have h1 : HasDerivAt (fun x => (x - t0) / ((M.m : ℝ) - 1)) cm z := by
          have := ((hasDerivAt_id' z).sub_const t0).div_const ((M.m : ℝ) - 1)
          simpa only [cm] using this
        have h2 := (hasDerivAt_const z (1 : ℝ)).fun_sub h1
        simpa using h2
      have hp := hlin.fun_pow (M.n - 2)
      have hsub3 : M.n - 2 - 1 = M.n - 3 := by omega
      rw [hsub3] at hp
      convert hp using 1
      dsimp [v']; ring
    have hu'_int : IntervalIntegrable (fun z => -1 / M.f (P.P z)) volume ((M.m : ℝ) * t0) 1 := by
      have hcont : ContinuousOn (fun z => -1 / M.f (P.P z)) (uIcc ((M.m : ℝ) * t0) 1) := by
        rw [uIcc_of_le hmt0_lt1.le]
        apply continuousOn_const.div
        · exact M.hf_cont.comp (P.hP_cont.mono (Icc_subset_Icc_left hmt0_pos.le))
            (fun z hz => P.hP_mem z ⟨hmt0_pos.le.trans hz.1, hz.2⟩)
        · intro z hz
          exact (M.hf_pos _ (P.hP_mem z ⟨hmt0_pos.le.trans hz.1, hz.2⟩)).ne'
      exact hcont.intervalIntegrable
    have hv'_int : IntervalIntegrable v' volume ((M.m : ℝ) * t0) 1 := by
      have hcont : ContinuousOn v' (uIcc ((M.m : ℝ) * t0) 1) :=
        (continuous_const.mul (continuous_const.mul
          (((continuous_const.sub ((continuous_id.sub continuous_const).div_const _)).pow _)))).continuousOn
      exact hcont.intervalIntegrable
    have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      hu_cont hv_cont hu_deriv hv_deriv hu'_int hv'_int
    have hv1 : v 1 = (1 - q0) ^ (M.n - 2) := by
      dsimp [v, q0]
    have hv0 : v ((M.m : ℝ) * t0) = (1 - t0) ^ (M.n - 2) := by
      dsimp [v]
      have : ((M.m : ℝ) * t0 - t0) / ((M.m : ℝ) - 1) = t0 := by
        field_simp [hm1.ne']
      rw [this]
    have hneg : (∫ z in ((M.m : ℝ) * t0)..1, P.P z * v' z) =
        -(cm * ∫ z in ((M.m : ℝ) * t0)..1,
          P.P z * (((M.n - 2 : ℕ) : ℝ) * (1 - (z - t0) / ((M.m : ℝ) - 1)) ^ (M.n - 3))) := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro z _; dsimp [v']; ring
    rw [hneg, hv1, hv0, P.hP_one] at hparts
    dsimp [v] at hparts
    linarith
  -- Now combine hd1, hd2, hd3 and simplify algebraically!
  have htot := (hd1.fun_add hd2).fun_add hd3
  convert htot using 1
  rw [hS_val, hS'_val, hibp]
  -- Combine the two integrals on [m * t0, 1]
  have hintA : IntervalIntegrable
      (fun z => P.P z * (1 - (z - t0) / ((M.m : ℝ) - 1)) ^ (M.n - 2))
      volume ((M.m : ℝ) * t0) 1 := by
    have hcont : ContinuousOn
        (fun z => P.P z * (1 - (z - t0) / ((M.m : ℝ) - 1)) ^ (M.n - 2))
        (uIcc ((M.m : ℝ) * t0) 1) := by
      rw [uIcc_of_le hmt0_lt1.le]
      exact (P.hP_cont.mono (Icc_subset_Icc_left hmt0_pos.le)).mul
        (((continuous_const.sub ((continuous_id.sub continuous_const).div_const _)).pow _)).continuousOn
    exact hcont.intervalIntegrable
  have hintB : IntervalIntegrable
      (fun z => (-1 / M.f (P.P z)) * (1 - (z - t0) / ((M.m : ℝ) - 1)) ^ (M.n - 2))
      volume ((M.m : ℝ) * t0) 1 := by
    have hcont : ContinuousOn
        (fun z => (-1 / M.f (P.P z)) * (1 - (z - t0) / ((M.m : ℝ) - 1)) ^ (M.n - 2))
        (uIcc ((M.m : ℝ) * t0) 1) := by
      rw [uIcc_of_le hmt0_lt1.le]
      apply (continuousOn_const.div _ _).mul
      · exact (((continuous_const.sub ((continuous_id.sub continuous_const).div_const _)).pow _)).continuousOn
      · exact M.hf_cont.comp (P.hP_cont.mono (Icc_subset_Icc_left hmt0_pos.le))
          (fun z hz => P.hP_mem z ⟨hmt0_pos.le.trans hz.1, hz.2⟩)
      · intro z hz
        exact (M.hf_pos _ (P.hP_mem z ⟨hmt0_pos.le.trans hz.1, hz.2⟩)).ne'
    exact hcont.intervalIntegrable
  have hcomb :
      (∫ z in ((M.m : ℝ) * t0)..1,
        (P.P z + t0 * (-1 / M.f (P.P z))) * (1 - (z - t0) / ((M.m : ℝ) - 1)) ^ (M.n - 2)) =
      (∫ z in ((M.m : ℝ) * t0)..1,
        P.P z * (1 - (z - t0) / ((M.m : ℝ) - 1)) ^ (M.n - 2)) +
      t0 * (∫ z in ((M.m : ℝ) * t0)..1,
        (-1 / M.f (P.P z)) * (1 - (z - t0) / ((M.m : ℝ) - 1)) ^ (M.n - 2)) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hintA (hintB.const_mul t0)]
    apply intervalIntegral.integral_congr; intro z _; ring
  rw [hcomb]
  -- Use ρ* identity: a - ρ* = ((m - 1)^2 / (n - 1)) * ρ*, and 1 = t0 + (m - 1) q0
  have hrho_id : M.a - M.rhoStar = (((M.m : ℝ) - 1) ^ 2 / ((M.n : ℝ) - 1)) * M.rhoStar := by
    unfold Market.rhoStar
    have hden : ((M.m : ℝ) - 1) ^ 2 + ((M.n : ℝ) - 1) ≠ 0 := by positivity
    field_simp [hn1.ne', hden]
    ring
  have hpow_split : (1 - q0) ^ (M.n - 1) = (1 - q0) * (1 - q0) ^ (M.n - 2) := by
    have hne : M.n - 1 = (M.n - 2) + 1 := by have := M.hn; omega
    rw [hne, pow_succ']
  have hq0_rel : 1 - q0 - ((M.m : ℝ) - 1) * t0 = ((M.m : ℝ) - 2) * (q0 - t0) := by
    dsimp [q0]; field_simp [hm1.ne']; ring
  have harg_t0 : t0 + ((M.m : ℝ) - 1) * t0 = (M.m : ℝ) * t0 := by ring
  unfold Market.cournotRev Market.W
  rw [harg_t0, hpow_split]
  dsimp [cm]
  have ha_sub : M.a = M.rhoStar + (((M.m : ℝ) - 1) ^ 2 / ((M.n : ℝ) - 1)) * M.rhoStar := by
    linarith
  rw [ha_sub]
  field_simp [hm1.ne', hn1.ne']
  have h1q : 1 - q0 = ((M.m : ℝ) - 1) * t0 + ((M.m : ℝ) - 2) * (q0 - t0) := by linarith
  rw [h1q]
  ring

/-- `reserveIncreaseRev` is nondecreasing on `[0, 1 / m]` whenever `ψ_m ≥ 0` on `[a, 1]`
(no monotonicity of `ψ_m` is needed here — used for both Theorem 2 and Virág's reserve game). -/
theorem reserveIncreaseRev_le_baseline (P : M.InverseDemand)
    (hpsi_nonneg : ∀ v ∈ Icc M.a 1, 0 ≤ M.psi v)
    {t0 : ℝ} (ht0 : t0 ∈ Icc (0 : ℝ) (1 / (M.m : ℝ))) :
    reserveIncreaseRev M P.P M.rhoStar t0 ≤ baselineRev M P.P := by
  have hm : (0 : ℝ) < M.m := M.m_pos_real
  have hm1 : (0 : ℝ) < (M.m : ℝ) - 1 := M.m_sub_one_pos_real
  have hmR : (2 : ℝ) ≤ M.m := by exact_mod_cast M.hm
  have hn : (0 : ℝ) < M.n := M.n_pos_real
  have hn1 : (0 : ℝ) < (M.n : ℝ) - 1 := M.n_sub_one_pos_real
  -- First check reserveIncreaseRev at 1/m equals baselineRev
  have hat_end : reserveIncreaseRev M P.P M.rhoStar (1 / (M.m : ℝ)) = baselineRev M P.P := by
    unfold reserveIncreaseRev baselineRev pathRev
    have hq_end : (1 - 1 / (M.m : ℝ)) / ((M.m : ℝ) - 1) = 1 / (M.m : ℝ) := by
      field_simp [hm.ne', hm1.ne']
    simp only [hq_end]
    have hint_eq :
        (∫ q in (0 : ℝ)..(1 / (M.m : ℝ)),
          M.cournotRev P.P (reserveIncreasePath (1 / (M.m : ℝ)) q) q * M.W q) =
        ∫ q in (0 : ℝ)..(1 / (M.m : ℝ)), M.cournotRev P.P (id q) q * M.W q := by
      apply intervalIntegral.integral_congr
      intro q hq
      rw [uIcc_of_le (inv_m_pos M).le] at hq
      dsimp only [reserveIncreasePath, id]
      rw [min_eq_left hq.2]
    rw [hint_eq]
  rw [← hat_end]
  -- Show reserveIncreaseRev is monotone on [0, 1/m] via nonnegative derivative on (0, 1/m)
  have hmono : MonotoneOn (fun s => reserveIncreaseRev M P.P M.rhoStar s)
      (Icc 0 (1 / (M.m : ℝ))) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 (1 / (M.m : ℝ)))
    · exact reserveIncreaseRev_continuousOn M P
    · intro s hs
      rw [interior_Icc] at hs
      exact (reserveIncreaseRev_hasDerivAt M P hs).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      rw [(reserveIncreaseRev_hasDerivAt M P hs).deriv]
      set q0 := (1 - s) / ((M.m : ℝ) - 1)
      have hms_le : (M.m : ℝ) * s ≤ 1 := by
        have := hs.2.le; rwa [le_div_iff₀ hm, mul_comm] at this
      have hms_pos : 0 ≤ (M.m : ℝ) * s := mul_nonneg hm.le hs.1.le
      have hs_le_q0 : s ≤ q0 := by
        dsimp [q0]; rw [le_div_iff₀ hm1]; linarith
      have hq0_le_one : q0 ≤ 1 := by
        dsimp [q0]; rw [div_le_one hm1]; linarith [hs.1]
      have hterm1 : 0 ≤ (M.n : ℝ) *
          (M.rhoStar * ((M.m : ℝ) - 2) * (q0 - s) * (1 - q0) ^ (M.n - 2)) := by
        have hrho : 0 ≤ M.rhoStar := M.rhoStar_nonneg
        have hm2 : 0 ≤ (M.m : ℝ) - 2 := by linarith
        have hqs : 0 ≤ q0 - s := sub_nonneg.mpr hs_le_q0
        have h1q : 0 ≤ (1 - q0) ^ (M.n - 2) := pow_nonneg (by linarith) _
        positivity
      have hterm2 : 0 ≤ ((M.n : ℝ) * ((M.n : ℝ) - 1) / ((M.m : ℝ) - 1)) *
          ∫ z in ((M.m : ℝ) * s)..1,
            (P.P z + s * (-1 / M.f (P.P z))) *
              (1 - (z - s) / ((M.m : ℝ) - 1)) ^ (M.n - 2) := by
        apply mul_nonneg (by positivity)
        apply intervalIntegral.integral_nonneg hms_le
        intro z hz
        have hz_icc : z ∈ Icc (0 : ℝ) 1 := ⟨hms_pos.trans hz.1, hz.2⟩
        have hfz : 0 < M.f (P.P z) := M.hf_pos _ (P.hP_mem z hz_icc)
        have hsz : s ≤ z / (M.m : ℝ) := by
          rw [le_div_iff₀ hm, mul_comm]; exact hz.1
        have hbr : 0 ≤ P.P z + s * (-1 / M.f (P.P z)) := by
          have hpsi_z : 0 ≤ MR M P z := hpsi_nonneg (P.P z) (P.hP_mem z hz_icc)
          rw [MR_eq M P hz_icc] at hpsi_z
          have hcmp : s / M.f (P.P z) ≤ z / ((M.m : ℝ) * M.f (P.P z)) := by
            rw [div_le_div_iff₀ hfz (mul_pos hm hfz)]
            have : s * (M.m : ℝ) ≤ z := by linarith [hz.1]
            nlinarith
          have hrew : P.P z + s * (-1 / M.f (P.P z)) = P.P z - s / M.f (P.P z) := by ring
          rw [hrew]; linarith
        have hpow_nonneg : 0 ≤ (1 - (z - s) / ((M.m : ℝ) - 1)) ^ (M.n - 2) := by
          apply pow_nonneg
          rw [sub_nonneg, div_le_one hm1]
          linarith [hz.2, hs.1]
        exact mul_nonneg hbr hpow_nonneg
      linarith
  exact hmono ht0 ⟨(inv_m_pos M).le, le_rfl⟩ ht0.2

/-- Theorem 2, Case 1 (`t0 ≤ 1 / m`): every deviation losing traffic earns at most `R*`. -/
theorem theorem2_case1_lose_traffic (P : M.InverseDemand)
    (hpsi_mono : MonotoneOn M.psi (Icc M.a 1))
    (hpsi_a : 0 ≤ M.psi M.a)
    {q0 t0 ℓ : ℝ} {t : ℝ → ℝ}
    (ht0_nonneg : 0 ≤ t0) (ht0_le : t0 ≤ 1 / (M.m : ℝ))
    (hq0_eq : t0 + ((M.m : ℝ) - 1) * q0 = 1)
    (hℓ : 0 ≤ ℓ)
    (ht_mono : MonotoneOn t (Icc 0 q0))
    (ht_bounds : ∀ q ∈ Icc (0 : ℝ) q0, 0 ≤ t q ∧ t q ≤ t0)
    (hborder : BorderFeasible M q0 t) :
    pathRev M P.P M.rhoStar q0 t0 ℓ t ≤ baselineRev M P.P := by
  have h1 := case1_le_reserveIncreaseRev M P hpsi_mono hpsi_a
    ht0_nonneg ht0_le hq0_eq hℓ ht_mono ht_bounds hborder
  have hpsi_nonneg : ∀ v ∈ Icc M.a 1, 0 ≤ M.psi v := fun v hv =>
    hpsi_a.trans (hpsi_mono ⟨le_rfl, M.ha1.le⟩ hv hv.1)
  have h2 := reserveIncreaseRev_le_baseline M P hpsi_nonneg ⟨ht0_nonneg, ht0_le⟩
  exact h1.trans h2

end Case1

/-! ### Case 2: Deviations Gaining Traffic (`t0 ≥ 1 / m`, `q0 ≤ 1 / m`) -/

section Case2

variable (M : Market)

/-- Integral `J0 = ∫_{q0}^{1/m} (1 - q)^(n - 2) * (1/m - q) dq` from Appendix B. -/
noncomputable def J0 (q0 : ℝ) : ℝ :=
  ∫ q in q0..(1 / (M.m : ℝ)), (1 - q) ^ (M.n - 2) * (1 / (M.m : ℝ) - q)

/-- Diagonal-plus-boundary functional `V(q)` from Appendix B. -/
noncomputable def Vfun (P : ℝ → ℝ) (q : ℝ) : ℝ :=
  (M.n : ℝ) * M.rhoStar * (1 - ((M.m : ℝ) - 1) * q) * (1 - q) ^ (M.n - 1) +
    ∫ u in (0 : ℝ)..q, M.cournotRev P u u * M.W u

/-- Derivative factor `Y(q)` with `V'(q) = n (1 - q)^(n - 2) Y(q)`. -/
noncomputable def Yfun (P : ℝ → ℝ) (q : ℝ) : ℝ :=
  ((M.n : ℝ) - 1) * q * P ((M.m : ℝ) * q) -
    M.rhoStar * (((M.m : ℝ) - 1) * (1 - q) + ((M.n : ℝ) - 1) * (1 - ((M.m : ℝ) - 1) * q))

lemma J0_nonneg {q0 : ℝ} (hq0 : q0 ≤ 1 / (M.m : ℝ)) : 0 ≤ J0 M q0 := by
  unfold J0
  apply intervalIntegral.integral_nonneg hq0
  intro q hq
  have h1q : 0 ≤ 1 - q := by linarith [hq.2, inv_m_le_one M]
  exact mul_nonneg (pow_nonneg h1q _) (sub_nonneg.mpr hq.2)

/-- Exact identity relating `η` and `m(n - 1) J0` to the Jensen gap (Appendix B, eq. (860)). -/
lemma convexityGap_sub_J0_eq {q0 t0 : ℝ} (hq0_eq : t0 + ((M.m : ℝ) - 1) * q0 = 1) :
    cm_convexityGap M.n q0 t0 - (M.m : ℝ) * ((M.n : ℝ) - 1) * J0 M q0 =
      ((M.m : ℝ) / (M.n : ℝ)) *
        ((((M.m : ℝ) - 1) / (M.m : ℝ)) * (1 - q0) ^ M.n +
          (1 / (M.m : ℝ)) * (((M.m : ℝ) - 1) * q0) ^ M.n -
          (((M.m : ℝ) - 1) / (M.m : ℝ)) ^ M.n) := by
  have hm : (0 : ℝ) < M.m := M.m_pos_real
  have hn : (0 : ℝ) < M.n := M.n_pos_real
  have hn1 : (0 : ℝ) < (M.n : ℝ) - 1 := M.n_sub_one_pos_real
  have hn_cast1 : ((M.n - 1 : ℕ) : ℝ) = (M.n : ℝ) - 1 := by
    rw [Nat.cast_sub (by have := M.hn; omega), Nat.cast_one]
  have hn_sub1 : M.n - 1 - 1 = M.n - 2 := by omega
  have hpow_n : ∀ x : ℝ, x ^ M.n = x * x ^ (M.n - 1) := by
    intro x
    have h : (M.n - 1) + 1 = M.n := by have := M.hn; omega
    conv_lhs => rw [← h]
    rw [pow_succ']
  have hpow_n1 : ∀ x : ℝ, x ^ (M.n - 1) = x * x ^ (M.n - 2) := by
    intro x
    have h : (M.n - 2) + 1 = M.n - 1 := by have := M.hn; omega
    conv_lhs => rw [← h]
    rw [pow_succ']
  -- Evaluate J0 explicitly via FTC
  let FJ : ℝ → ℝ := fun q =>
    -(1 - q) ^ M.n / (M.n : ℝ) +
      (((M.m : ℝ) - 1) / (M.m : ℝ)) * ((1 - q) ^ (M.n - 1) / ((M.n : ℝ) - 1))
  have hFJ_deriv : ∀ q, HasDerivAt FJ ((1 - q) ^ (M.n - 2) * (1 / (M.m : ℝ) - q)) q := by
    intro q
    have h1q : HasDerivAt (fun x : ℝ => 1 - x) (-1) q := by
      simpa using (hasDerivAt_const q (1 : ℝ)).fun_sub (hasDerivAt_id' q)
    have hdA : HasDerivAt (fun x : ℝ => -(1 - x) ^ M.n / (M.n : ℝ)) ((1 - q) ^ (M.n - 1)) q := by
      have h := (((h1q.fun_pow M.n).fun_neg).div_const (M.n : ℝ))
      convert h using 1
      field_simp [hn.ne']
    have hdB : HasDerivAt
        (fun x : ℝ => (((M.m : ℝ) - 1) / (M.m : ℝ)) * ((1 - x) ^ (M.n - 1) / ((M.n : ℝ) - 1)))
        (-(((M.m : ℝ) - 1) / (M.m : ℝ)) * (1 - q) ^ (M.n - 2)) q := by
      have h := (((h1q.fun_pow (M.n - 1)).div_const ((M.n : ℝ) - 1)).const_mul
        (((M.m : ℝ) - 1) / (M.m : ℝ)))
      convert h using 1
      rw [hn_cast1, hn_sub1]
      field_simp [hn1.ne', hm.ne']
    have hsum := hdA.fun_add hdB
    convert hsum using 1
    rw [hpow_n1 (1 - q)]
    field_simp [hm.ne']; ring
  have hJ0_int : IntervalIntegrable (fun q => (1 - q) ^ (M.n - 2) * (1 / (M.m : ℝ) - q))
      volume q0 (1 / (M.m : ℝ)) :=
    (((continuous_const.sub continuous_id).pow _).mul
      (continuous_const.sub continuous_id)).continuousOn.intervalIntegrable
  have hJ0_val : J0 M q0 = FJ (1 / (M.m : ℝ)) - FJ q0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun q _ => hFJ_deriv q) hJ0_int
  rw [hJ0_val]
  unfold cm_convexityGap probScale
  dsimp [FJ]
  have h1m : 1 - 1 / (M.m : ℝ) = ((M.m : ℝ) - 1) / (M.m : ℝ) := by
    field_simp [hm.ne']
  have h1t0 : 1 - t0 = ((M.m : ℝ) - 1) * q0 := by linarith
  have ht0_sub : t0 - q0 = 1 - (M.m : ℝ) * q0 := by linarith
  rw [h1m, h1t0, ht0_sub]
  have hpow1 := hpow_n (((M.m : ℝ) - 1) / (M.m : ℝ))
  have hpow2 := hpow_n (1 - q0)
  rw [hpow1]
  have hterm : ((1 - q0) ^ (M.n - 1) * (1 - (M.m : ℝ) * q0)) +
      ((M.m : ℝ) - 1) * (1 - q0) ^ (M.n - 1) = (M.m : ℝ) * (1 - q0) ^ M.n := by
    rw [hpow2]; ring
  field_simp [hm.ne', hn.ne', hn1.ne']
  rw [hpow2]
  ring

/-- Consequence of Jensen's inequality: `m(n - 1) J0 ≤ η` for `q0 ∈ [0, 1 / m]`. -/
lemma m_mul_n_sub_one_mul_J0_le_convexityGap {q0 t0 : ℝ}
    (hq0 : q0 ∈ Icc (0 : ℝ) (1 / (M.m : ℝ)))
    (hq0_eq : t0 + ((M.m : ℝ) - 1) * q0 = 1) :
    (M.m : ℝ) * ((M.n : ℝ) - 1) * J0 M q0 ≤ cm_convexityGap M.n q0 t0 := by
  have hdiff := convexityGap_sub_J0_eq M hq0_eq
  have hj := theorem2_jensen_ineq M.hm M.hn hq0.1 hq0.2
  have hcoeff : 0 ≤ (M.m : ℝ) / (M.n : ℝ) := div_nonneg M.m_pos_real.le M.n_pos_real.le
  have hnonneg : 0 ≤ cm_convexityGap M.n q0 t0 - (M.m : ℝ) * ((M.n : ℝ) - 1) * J0 M q0 := by
    rw [hdiff]
    exact mul_nonneg hcoeff (sub_nonneg.mpr hj)
  linarith

lemma Vfun_at_inv_m (P : ℝ → ℝ) : Vfun M P (1 / (M.m : ℝ)) = baselineRev M P := by
  unfold Vfun baselineRev pathRev
  have hm : (M.m : ℝ) ≠ 0 := M.m_pos_real.ne'
  have h1 : 1 - ((M.m : ℝ) - 1) * (1 / (M.m : ℝ)) = 1 / (M.m : ℝ) := by
    field_simp [hm]; ring
  rw [h1, sub_zero]
  rfl

lemma Yfun_at_inv_m (P : M.InverseDemand) : Yfun M P.P (1 / (M.m : ℝ)) = 0 := by
  unfold Yfun Market.rhoStar
  have hm : (M.m : ℝ) ≠ 0 := M.m_pos_real.ne'
  have hden : ((M.m : ℝ) - 1) ^ 2 + ((M.n : ℝ) - 1) ≠ 0 := by
    have := M.m_sub_one_pos_real; have := M.n_sub_one_pos_real; positivity
  have hm1 : (M.m : ℝ) * (1 / (M.m : ℝ)) = 1 := by field_simp [hm]
  rw [hm1, P.hP_one]
  field_simp [hm, hden]
  ring

lemma Vfun_continuousOn (P : M.InverseDemand) :
    ContinuousOn (Vfun M P.P) (Icc 0 (1 / (M.m : ℝ))) := by
  have hm : (0 : ℝ) < M.m := M.m_pos_real
  unfold Vfun
  apply ContinuousOn.add
  · exact (((continuous_const.mul (continuous_const.sub (continuous_const.mul continuous_id))).mul
      ((continuous_const.sub continuous_id).pow (M.n - 1)))).continuousOn
  · have hcont_int : ContinuousOn (fun q => M.cournotRev P.P q q * M.W q)
        (Icc 0 (1 / (M.m : ℝ))) := by
      unfold Market.cournotRev
      apply (continuousOn_id.mul ?_).mul (cm_W_continuous M).continuousOn
      apply P.hP_cont.comp ((continuous_id.add (continuous_const.mul continuous_id)).continuousOn)
      intro q hq
      change q + ((M.m : ℝ) - 1) * q ∈ Icc (0 : ℝ) 1
      have hq_arg : q + ((M.m : ℝ) - 1) * q = (M.m : ℝ) * q := by ring
      rw [hq_arg]
      exact ⟨mul_nonneg hm.le hq.1, by have h1 := hq.2; rwa [le_div_iff₀ hm, mul_comm] at h1⟩
    rw [← uIcc_of_le (inv_m_pos M).le]
    apply intervalIntegral.continuousOn_primitive_interval
    rw [uIcc_of_le (inv_m_pos M).le]
    exact hcont_int.integrableOn_Icc

lemma Vfun_hasDerivAt (P : M.InverseDemand) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) (1 / (M.m : ℝ))) :
    HasDerivAt (Vfun M P.P) ((M.n : ℝ) * (1 - q) ^ (M.n - 2) * Yfun M P.P q) q := by
  have hm : (0 : ℝ) < M.m := M.m_pos_real
  have hn_cast1 : ((M.n - 1 : ℕ) : ℝ) = (M.n : ℝ) - 1 := by
    rw [Nat.cast_sub (by have := M.hn; omega), Nat.cast_one]
  have hn_sub1 : M.n - 1 - 1 = M.n - 2 := by omega
  have hpow1 : (1 - q) ^ (M.n - 1) = (1 - q) * (1 - q) ^ (M.n - 2) := by
    have : M.n - 1 = (M.n - 2) + 1 := by have := M.hn; omega
    rw [this, pow_succ']
  have hd1 : HasDerivAt
      (fun x => (M.n : ℝ) * M.rhoStar * (1 - ((M.m : ℝ) - 1) * x) * (1 - x) ^ (M.n - 1))
      (-(M.n : ℝ) * M.rhoStar * (1 - q) ^ (M.n - 2) *
        (((M.m : ℝ) - 1) * (1 - q) + ((M.n : ℝ) - 1) * (1 - ((M.m : ℝ) - 1) * q))) q := by
    have hlin : HasDerivAt (fun x => (M.n : ℝ) * M.rhoStar * (1 - ((M.m : ℝ) - 1) * x))
        (-(M.n : ℝ) * M.rhoStar * ((M.m : ℝ) - 1)) q := by
      have h1 : HasDerivAt (fun x => 1 - ((M.m : ℝ) - 1) * x) (-((M.m : ℝ) - 1)) q := by
        have := (hasDerivAt_const q (1 : ℝ)).fun_sub ((hasDerivAt_id' q).const_mul ((M.m : ℝ) - 1))
        simpa using this
      convert h1.const_mul ((M.n : ℝ) * M.rhoStar) using 1; ring
    have hpow : HasDerivAt (fun x => (1 - x) ^ (M.n - 1))
        (-((M.n : ℝ) - 1) * (1 - q) ^ (M.n - 2)) q := by
      have h1q : HasDerivAt (fun x : ℝ => 1 - x) (-1) q := by
        simpa using (hasDerivAt_const q (1 : ℝ)).fun_sub (hasDerivAt_id' q)
      have hp := h1q.fun_pow (M.n - 1)
      rw [hn_cast1, hn_sub1] at hp
      convert hp using 1; ring
    have hmul := hlin.fun_mul hpow
    convert hmul using 1
    rw [hpow1]; ring
  have hd2 : HasDerivAt
      (fun x => ∫ u in (0 : ℝ)..x, M.cournotRev P.P u u * M.W u)
      (M.cournotRev P.P q q * M.W q) q := by
    have hcont_int : ContinuousOn (fun u => M.cournotRev P.P u u * M.W u)
        (Icc 0 (1 / (M.m : ℝ))) := by
      unfold Market.cournotRev
      apply (continuousOn_id.mul ?_).mul (cm_W_continuous M).continuousOn
      apply P.hP_cont.comp ((continuous_id.add (continuous_const.mul continuous_id)).continuousOn)
      intro u hu
      change u + ((M.m : ℝ) - 1) * u ∈ Icc (0 : ℝ) 1
      have hu_arg : u + ((M.m : ℝ) - 1) * u = (M.m : ℝ) * u := by ring
      rw [hu_arg]
      exact ⟨mul_nonneg hm.le hu.1, by have h1 := hu.2; rwa [le_div_iff₀ hm, mul_comm] at h1⟩
    have hca : ContinuousAt (fun u => M.cournotRev P.P u u * M.W u) q :=
      hcont_int.continuousAt (Icc_mem_nhds hq.1 hq.2)
    have hmeas : StronglyMeasurableAtFilter
        (fun u => M.cournotRev P.P u u * M.W u) (nhds q) volume :=
      (hcont_int.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo q hq
    have hint : IntervalIntegrable (fun u => M.cournotRev P.P u u * M.W u) volume 0 q :=
      (hcont_int.mono (by rw [uIcc_of_le hq.1.le]; exact Icc_subset_Icc_right hq.2.le)).intervalIntegrable
    exact intervalIntegral.integral_hasDerivAt_right hint hmeas hca
  have hsum := hd1.fun_add hd2
  show HasDerivAt (fun x => (M.n : ℝ) * M.rhoStar * (1 - ((M.m : ℝ) - 1) * x) * (1 - x) ^ (M.n - 1) +
      ∫ u in (0 : ℝ)..x, M.cournotRev P.P u u * M.W u) _ q
  convert hsum using 1
  unfold Yfun Market.cournotRev Market.W
  have harg : q + ((M.m : ℝ) - 1) * q = (M.m : ℝ) * q := by ring
  rw [harg]; ring

lemma baselineRev_sub_Vfun_eq (P : M.InverseDemand)
    {q0 : ℝ} (hq0 : q0 ∈ Icc (0 : ℝ) (1 / (M.m : ℝ))) :
    baselineRev M P.P - Vfun M P.P q0 =
      ∫ q in q0..(1 / (M.m : ℝ)), (M.n : ℝ) * (1 - q) ^ (M.n - 2) * Yfun M P.P q := by
  rw [← Vfun_at_inv_m M P.P]
  have hm : (0 : ℝ) < M.m := M.m_pos_real
  have hY_cont : ContinuousOn (fun q => (M.n : ℝ) * (1 - q) ^ (M.n - 2) * Yfun M P.P q)
      (Icc 0 (1 / (M.m : ℝ))) := by
    unfold Yfun
    apply (continuous_const.mul ((continuous_const.sub continuous_id).pow _)).continuousOn.mul
    apply ContinuousOn.sub
    · apply (continuous_const.mul continuous_id).continuousOn.mul
      apply P.hP_cont.comp (continuous_const.mul continuous_id).continuousOn
      intro q hq
      exact ⟨mul_nonneg hm.le hq.1, by have h1 := hq.2; rwa [le_div_iff₀ hm, mul_comm] at h1⟩
    · exact (continuous_const.mul
        ((continuous_const.mul (continuous_const.sub continuous_id)).add
          (continuous_const.mul (continuous_const.sub (continuous_const.mul continuous_id))))).continuousOn
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hq0.2
  · exact (Vfun_continuousOn M P).mono (Icc_subset_Icc_left hq0.1)
  · intro q hq
    exact Vfun_hasDerivAt M P ⟨lt_of_le_of_lt hq0.1 hq.1, hq.2⟩
  · exact (hY_cont.mono (by rw [uIcc_of_le hq0.2]; exact Icc_subset_Icc_left hq0.1)).intervalIntegrable

/-- Case 2 Subcase A (and pure reserve cuts): using ONLY `P ≥ a` (no monotonicity of `ψ_m`!),
`V(q0) - n * a * η ≤ R*`. -/
lemma Vfun_sub_na_eta_le_baseline (P : M.InverseDemand)
    {q0 t0 : ℝ} (hq0 : q0 ∈ Icc (0 : ℝ) (1 / (M.m : ℝ)))
    (hq0_eq : t0 + ((M.m : ℝ) - 1) * q0 = 1) :
    Vfun M P.P q0 - (M.n : ℝ) * M.a * cm_convexityGap M.n q0 t0 ≤ baselineRev M P.P := by
  have hm : (0 : ℝ) < M.m := M.m_pos_real
  have hm1 : (0 : ℝ) < (M.m : ℝ) - 1 := M.m_sub_one_pos_real
  have hmR : (2 : ℝ) ≤ M.m := by exact_mod_cast M.hm
  have hn : (0 : ℝ) < M.n := M.n_pos_real
  have hn1 : (0 : ℝ) < (M.n : ℝ) - 1 := M.n_sub_one_pos_real
  set K := ((M.n : ℝ) - 1) * M.a + (M.n : ℝ) * ((M.m : ℝ) - 1) * M.rhoStar
  -- Pointwise lower bound on Yfun(q) for q ∈ [q0, 1/m] using only P(mq) ≥ a
  have hY_ge : ∀ q ∈ Icc q0 (1 / (M.m : ℝ)),
      -(1 / (M.m : ℝ) - q) * K ≤ Yfun M P.P q := by
    intro q hq
    have hq_nonneg : 0 ≤ q := hq0.1.trans hq.1
    have hmq : (M.m : ℝ) * q ∈ Icc (0 : ℝ) 1 :=
      ⟨mul_nonneg hm.le hq_nonneg, by have h1 := hq.2; rwa [le_div_iff₀ hm, mul_comm] at h1⟩
    have hPa : M.a ≤ P.P ((M.m : ℝ) * q) := (P.hP_mem _ hmq).1
    have hY_at_a :
        ((M.n : ℝ) - 1) * q * M.a -
          M.rhoStar * (((M.m : ℝ) - 1) * (1 - q) + ((M.n : ℝ) - 1) * (1 - ((M.m : ℝ) - 1) * q)) =
        -(1 / (M.m : ℝ) - q) * K := by
      dsimp [K]
      unfold Market.rhoStar
      have hden : ((M.m : ℝ) - 1) ^ 2 + ((M.n : ℝ) - 1) ≠ 0 := by positivity
      field_simp [hm.ne', hden]; ring
    unfold Yfun
    have hmul : ((M.n : ℝ) - 1) * q * M.a ≤ ((M.n : ℝ) - 1) * q * P.P ((M.m : ℝ) * q) :=
      mul_le_mul_of_nonneg_left hPa (mul_nonneg hn1.le hq_nonneg)
    linarith
  -- Integrate from q0 to 1/m
  have hY_int : IntervalIntegrable
      (fun q => (M.n : ℝ) * (1 - q) ^ (M.n - 2) * Yfun M P.P q) volume q0 (1 / (M.m : ℝ)) := by
    have hcont : ContinuousOn (fun q => (M.n : ℝ) * (1 - q) ^ (M.n - 2) * Yfun M P.P q)
        (Icc q0 (1 / (M.m : ℝ))) := by
      unfold Yfun
      apply (continuous_const.mul ((continuous_const.sub continuous_id).pow _)).continuousOn.mul
      apply ContinuousOn.sub
      · apply (continuous_const.mul continuous_id).continuousOn.mul
        apply P.hP_cont.comp (continuous_const.mul continuous_id).continuousOn
        intro q hq
        exact ⟨mul_nonneg hm.le (hq0.1.trans hq.1),
               by have h1 := hq.2; rwa [le_div_iff₀ hm, mul_comm] at h1⟩
      · exact (continuous_const.mul
          ((continuous_const.mul (continuous_const.sub continuous_id)).add
            (continuous_const.mul (continuous_const.sub (continuous_const.mul continuous_id))))).continuousOn
    rw [← uIcc_of_le hq0.2] at hcont
    exact hcont.intervalIntegrable
  have hlow_int : IntervalIntegrable
      (fun q => -(M.n : ℝ) * K * ((1 - q) ^ (M.n - 2) * (1 / (M.m : ℝ) - q)))
      volume q0 (1 / (M.m : ℝ)) :=
    (continuous_const.mul (((continuous_const.sub continuous_id).pow _).mul
      (continuous_const.sub continuous_id))).continuousOn.intervalIntegrable
  have hdiff_ge : -(M.n : ℝ) * K * J0 M q0 ≤ baselineRev M P.P - Vfun M P.P q0 := by
    rw [baselineRev_sub_Vfun_eq M P hq0]
    calc
      -(M.n : ℝ) * K * J0 M q0
          = ∫ q in q0..(1 / (M.m : ℝ)),
              -(M.n : ℝ) * K * ((1 - q) ^ (M.n - 2) * (1 / (M.m : ℝ) - q)) := by
            unfold J0; rw [intervalIntegral.integral_const_mul]
      _ ≤ ∫ q in q0..(1 / (M.m : ℝ)),
              (M.n : ℝ) * (1 - q) ^ (M.n - 2) * Yfun M P.P q := by
            apply intervalIntegral.integral_mono_on hq0.2 hlow_int hY_int
            intro q hq
            have h1q : 0 ≤ (1 - q) ^ (M.n - 2) :=
              pow_nonneg (by linarith [hq.2, inv_m_le_one M]) _
            have hstep := mul_le_mul_of_nonneg_left (hY_ge q hq) (mul_nonneg hn.le h1q)
            linarith
  -- Combine with m(n - 1) J0 ≤ η and κ0 = (m - 1)^2 + n - 1 ≥ n
  have hj := m_mul_n_sub_one_mul_J0_le_convexityGap M hq0 hq0_eq
  have hna_eta : (M.n : ℝ) * M.a * ((M.m : ℝ) * ((M.n : ℝ) - 1) * J0 M q0) ≤
      (M.n : ℝ) * M.a * cm_convexityGap M.n q0 t0 :=
    mul_le_mul_of_nonneg_left hj (mul_nonneg hn.le M.ha0)
  have hJ0_nonneg : 0 ≤ J0 M q0 := J0_nonneg M hq0.2
  set κ0 : ℝ := ((M.m : ℝ) - 1) ^ 2 + ((M.n : ℝ) - 1)
  have hκ0_pos : 0 < κ0 := by dsimp [κ0]; positivity
  have hκ0_ge_n : (M.n : ℝ) ≤ κ0 := by
    dsimp [κ0]
    have : 1 ≤ ((M.m : ℝ) - 1) ^ 2 := by nlinarith
    linarith
  have halg : (M.n : ℝ) * M.a * ((M.m : ℝ) * ((M.n : ℝ) - 1) * J0 M q0) -
      (M.n : ℝ) * K * J0 M q0 =
      (M.n : ℝ) * J0 M q0 * ((M.n : ℝ) - 1) * ((M.m : ℝ) - 1) * M.a * (1 - (M.n : ℝ) / κ0) := by
    dsimp [K, κ0]; unfold Market.rhoStar
    field_simp [hκ0_pos.ne']; ring
  have hfinal_nonneg : 0 ≤ (M.n : ℝ) * J0 M q0 * ((M.n : ℝ) - 1) * ((M.m : ℝ) - 1) * M.a *
      (1 - (M.n : ℝ) / κ0) := by
    have h1 : 0 ≤ 1 - (M.n : ℝ) / κ0 := by
      rw [sub_nonneg, div_le_one hκ0_pos]; exact hκ0_ge_n
    have ha0 := M.ha0
    positivity
  linarith

/-- Pure reserve cut bound (uses ONLY `P ≥ a`, no monotonicity or nonnegativity of `ψ_m`!):
at `t = id`, `ℓ ≥ n * a * η`, any reserve cut earns at most `R*`. -/
theorem pure_reserve_cut_le_baseline (P : M.InverseDemand)
    {q0 t0 ℓ : ℝ}
    (hq0 : q0 ∈ Icc (0 : ℝ) (1 / (M.m : ℝ)))
    (hq0_eq : t0 + ((M.m : ℝ) - 1) * q0 = 1)
    (hrent : (M.n : ℝ) * M.a * cm_convexityGap M.n q0 t0 ≤ ℓ) :
    pathRev M P.P M.rhoStar q0 t0 ℓ id ≤ baselineRev M P.P := by
  have ht0_eq : t0 = 1 - ((M.m : ℝ) - 1) * q0 := by linarith
  have hpath : pathRev M P.P M.rhoStar q0 t0 ℓ id = Vfun M P.P q0 - ℓ := by
    unfold pathRev Vfun
    rw [ht0_eq]; rfl
  rw [hpath]
  have hbound := Vfun_sub_na_eta_le_baseline M P hq0 hq0_eq
  linarith

/-- Case 2 Subcase B: when `MR(m q0) < a`, under monotone `ψ_m` and `ψ_m(a) ≥ 0`,
`V(q0) - n * MR(m q0) * η ≤ R*`. -/
lemma Vfun_sub_nMR_eta_le_baseline (P : M.InverseDemand)
    (hpsi_mono : MonotoneOn M.psi (Icc M.a 1))
    (hpsi_a : 0 ≤ M.psi M.a)
    {q0 t0 : ℝ} (hq0 : q0 ∈ Icc (0 : ℝ) (1 / (M.m : ℝ)))
    (hq0_eq : t0 + ((M.m : ℝ) - 1) * q0 = 1) :
    Vfun M P.P q0 - (M.n : ℝ) * MR M P ((M.m : ℝ) * q0) * cm_convexityGap M.n q0 t0 ≤
      baselineRev M P.P := by
  have hm : (0 : ℝ) < M.m := M.m_pos_real
  have hm1 : (0 : ℝ) < (M.m : ℝ) - 1 := M.m_sub_one_pos_real
  have hmR : (2 : ℝ) ≤ M.m := by exact_mod_cast M.hm
  have hn : (0 : ℝ) < M.n := M.n_pos_real
  have hn1 : (0 : ℝ) < (M.n : ℝ) - 1 := M.n_sub_one_pos_real
  set Z : ℝ :=
    ((M.n : ℝ) - 1) * ((M.m : ℝ) * MR M P ((M.m : ℝ) * q0) - ((M.m : ℝ) - 1) * M.a) +
      (M.n : ℝ) * ((M.m : ℝ) - 1) * M.rhoStar
  -- Derivative of Yfun on (0, 1/m)
  have hY_deriv : ∀ q ∈ Ioo (0 : ℝ) (1 / (M.m : ℝ)),
      HasDerivAt (Yfun M P.P)
        (((M.n : ℝ) - 1) * M.psi1 (P.P ((M.m : ℝ) * q)) +
          (M.n : ℝ) * ((M.m : ℝ) - 1) * M.rhoStar) q := by
    intro q hq
    have hmq_open : (M.m : ℝ) * q ∈ Ioo (0 : ℝ) 1 :=
      ⟨mul_pos hm hq.1, by have h1 := hq.2; rwa [lt_div_iff₀ hm, mul_comm] at h1⟩
    have hmq_icc : (M.m : ℝ) * q ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hmq_open
    have hP_comp : HasDerivAt (fun x => P.P ((M.m : ℝ) * x))
        ((M.m : ℝ) * (-1 / M.f (P.P ((M.m : ℝ) * q)))) q := by
      have hm_lin : HasDerivAt (fun x => (M.m : ℝ) * x) (M.m : ℝ) q := by
        simpa using (hasDerivAt_id' q).const_mul (M.m : ℝ)
      have hc : HasDerivAt (fun x => P.P ((M.m : ℝ) * x))
          ((-1 / M.f (P.P ((M.m : ℝ) * q))) * (M.m : ℝ)) q :=
        (P.hP_deriv_open _ hmq_open).comp q hm_lin
      convert hc using 1; ring
    have hd1 : HasDerivAt (fun x => ((M.n : ℝ) - 1) * x * P.P ((M.m : ℝ) * x))
        (((M.n : ℝ) - 1) * M.psi1 (P.P ((M.m : ℝ) * q))) q := by
      have hlin : HasDerivAt (fun x => ((M.n : ℝ) - 1) * x) ((M.n : ℝ) - 1) q := by
        simpa using (hasDerivAt_id' q).const_mul ((M.n : ℝ) - 1)
      have hmul := hlin.fun_mul hP_comp
      convert hmul using 1
      unfold Market.psi1
      rw [P.hP_right _ hmq_icc]
      have hf : M.f (P.P ((M.m : ℝ) * q)) ≠ 0 := (M.hf_pos _ (P.hP_mem _ hmq_icc)).ne'
      field_simp [hf]; ring
    have hd2 : HasDerivAt
        (fun x => M.rhoStar * (((M.m : ℝ) - 1) * (1 - x) + ((M.n : ℝ) - 1) * (1 - ((M.m : ℝ) - 1) * x)))
        (-((M.n : ℝ) * ((M.m : ℝ) - 1) * M.rhoStar)) q := by
      have ha : HasDerivAt (fun x => ((M.m : ℝ) - 1) * (1 - x)) (-((M.m : ℝ) - 1)) q := by
        have h1 : HasDerivAt (fun x : ℝ => 1 - x) (-1) q := by
          simpa using (hasDerivAt_const q (1 : ℝ)).fun_sub (hasDerivAt_id' q)
        convert h1.const_mul ((M.m : ℝ) - 1) using 1; ring
      have hb : HasDerivAt (fun x => ((M.n : ℝ) - 1) * (1 - ((M.m : ℝ) - 1) * x))
          (-(((M.n : ℝ) - 1) * ((M.m : ℝ) - 1))) q := by
        have h1 : HasDerivAt (fun x => 1 - ((M.m : ℝ) - 1) * x) (-((M.m : ℝ) - 1)) q := by
          simpa using (hasDerivAt_const q (1 : ℝ)).fun_sub ((hasDerivAt_id' q).const_mul ((M.m : ℝ) - 1))
        convert h1.const_mul ((M.n : ℝ) - 1) using 1; ring
      convert (ha.fun_add hb).const_mul M.rhoStar using 1; ring
    have hsub := hd1.fun_sub hd2
    show HasDerivAt (fun x => ((M.n : ℝ) - 1) * x * P.P ((M.m : ℝ) * x) -
        M.rhoStar * (((M.m : ℝ) - 1) * (1 - x) + ((M.n : ℝ) - 1) * (1 - ((M.m : ℝ) - 1) * x))) _ q
    convert hsub using 1; ring
  have hY_cont : ContinuousOn (Yfun M P.P) (Icc 0 (1 / (M.m : ℝ))) := by
    unfold Yfun
    apply ContinuousOn.sub
    · apply (continuous_const.mul continuous_id).continuousOn.mul
      apply P.hP_cont.comp (continuous_const.mul continuous_id).continuousOn
      intro q hq
      exact ⟨mul_nonneg hm.le hq.1, by have h1 := hq.2; rwa [le_div_iff₀ hm, mul_comm] at h1⟩
    · exact (continuous_const.mul
        ((continuous_const.mul (continuous_const.sub continuous_id)).add
          (continuous_const.mul (continuous_const.sub (continuous_const.mul continuous_id))))).continuousOn
  -- Pointwise lower bound: Yfun q ≥ -(1/m - q) * Z on [q0, 1/m] via MVT
  have hY_ge : ∀ q ∈ Icc q0 (1 / (M.m : ℝ)), -(1 / (M.m : ℝ) - q) * Z ≤ Yfun M P.P q := by
    intro q hq
    rcases eq_or_lt_of_le hq.2 with rfl | hlt
    · rw [Yfun_at_inv_m M P]; simp
    have hc_cont : ContinuousOn (Yfun M P.P) (Icc q (1 / (M.m : ℝ))) :=
      hY_cont.mono (Icc_subset_Icc_left (hq0.1.trans hq.1))
    have hc_diff : DifferentiableOn ℝ (Yfun M P.P) (Ioo q (1 / (M.m : ℝ))) := fun c hc =>
      (hY_deriv c ⟨lt_of_le_of_lt (hq0.1.trans hq.1) hc.1, hc.2⟩).differentiableAt.differentiableWithinAt
    obtain ⟨c, hc, hslope⟩ := exists_deriv_eq_slope (Yfun M P.P) hlt hc_cont hc_diff
    have hc_open : c ∈ Ioo (0 : ℝ) (1 / (M.m : ℝ)) := ⟨lt_of_le_of_lt (hq0.1.trans hq.1) hc.1, hc.2⟩
    have hmc_icc : (M.m : ℝ) * c ∈ Icc (0 : ℝ) 1 :=
      ⟨mul_nonneg hm.le hc_open.1.le, by have h1 := hc_open.2.le; rwa [le_div_iff₀ hm, mul_comm] at h1⟩
    have hmq0_icc : (M.m : ℝ) * q0 ∈ Icc (0 : ℝ) 1 :=
      ⟨mul_nonneg hm.le hq0.1, by have h1 := hq0.2; rwa [le_div_iff₀ hm, mul_comm] at h1⟩
    have hpsi1_id : M.psi1 (P.P ((M.m : ℝ) * c)) =
        (M.m : ℝ) * MR M P ((M.m : ℝ) * c) - ((M.m : ℝ) - 1) * P.P ((M.m : ℝ) * c) := by
      unfold Market.psi1 MR Market.psi
      have hf : M.f (P.P ((M.m : ℝ) * c)) ≠ 0 := (M.hf_pos _ (P.hP_mem _ hmc_icc)).ne'
      field_simp [hm.ne', hf]; ring
    have hMR_le : MR M P ((M.m : ℝ) * c) ≤ MR M P ((M.m : ℝ) * q0) :=
      MR_antitoneOn M P hpsi_mono hmq0_icc hmc_icc
        (mul_le_mul_of_nonneg_left (hq.1.trans hc.1.le) hm.le)
    have hPa : M.a ≤ P.P ((M.m : ℝ) * c) := (P.hP_mem _ hmc_icc).1
    have hderiv_le : deriv (Yfun M P.P) c ≤ Z := by
      rw [(hY_deriv c hc_open).deriv, hpsi1_id]
      dsimp [Z]
      have h1 : (M.m : ℝ) * MR M P ((M.m : ℝ) * c) - ((M.m : ℝ) - 1) * P.P ((M.m : ℝ) * c) ≤
          (M.m : ℝ) * MR M P ((M.m : ℝ) * q0) - ((M.m : ℝ) - 1) * M.a := by nlinarith
      nlinarith
    rw [hslope, Yfun_at_inv_m M P, zero_sub, div_le_iff₀ (sub_pos.mpr hlt)] at hderiv_le
    linarith
  -- Integrate from q0 to 1/m
  have hY_int : IntervalIntegrable
      (fun q => (M.n : ℝ) * (1 - q) ^ (M.n - 2) * Yfun M P.P q) volume q0 (1 / (M.m : ℝ)) := by
    have hcont : ContinuousOn (fun q => (M.n : ℝ) * (1 - q) ^ (M.n - 2) * Yfun M P.P q)
        (uIcc q0 (1 / (M.m : ℝ))) := by
      rw [uIcc_of_le hq0.2]
      exact (continuous_const.mul ((continuous_const.sub continuous_id).pow _)).continuousOn.mul
        (hY_cont.mono (Icc_subset_Icc_left hq0.1))
    exact hcont.intervalIntegrable
  have hlow_int : IntervalIntegrable
      (fun q => -(M.n : ℝ) * Z * ((1 - q) ^ (M.n - 2) * (1 / (M.m : ℝ) - q)))
      volume q0 (1 / (M.m : ℝ)) :=
    (continuous_const.mul (((continuous_const.sub continuous_id).pow _).mul
      (continuous_const.sub continuous_id))).continuousOn.intervalIntegrable
  have hdiff_ge : -(M.n : ℝ) * Z * J0 M q0 ≤ baselineRev M P.P - Vfun M P.P q0 := by
    rw [baselineRev_sub_Vfun_eq M P hq0]
    calc
      -(M.n : ℝ) * Z * J0 M q0
          = ∫ q in q0..(1 / (M.m : ℝ)),
              -(M.n : ℝ) * Z * ((1 - q) ^ (M.n - 2) * (1 / (M.m : ℝ) - q)) := by
            unfold J0; rw [intervalIntegral.integral_const_mul]
      _ ≤ ∫ q in q0..(1 / (M.m : ℝ)),
              (M.n : ℝ) * (1 - q) ^ (M.n - 2) * Yfun M P.P q := by
            apply intervalIntegral.integral_mono_on hq0.2 hlow_int hY_int
            intro q hq
            have h1q : 0 ≤ (1 - q) ^ (M.n - 2) :=
              pow_nonneg (by linarith [hq.2, inv_m_le_one M]) _
            have hstep := mul_le_mul_of_nonneg_left (hY_ge q hq) (mul_nonneg hn.le h1q)
            linarith
  -- Combine with m(n - 1) J0 ≤ η and MR(m q0) ≥ 0: the MR(m q0) terms cancel identically!
  have hmq0_icc : (M.m : ℝ) * q0 ∈ Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg hm.le hq0.1, by have h1 := hq0.2; rwa [le_div_iff₀ hm, mul_comm] at h1⟩
  have hMR_nonneg : 0 ≤ MR M P ((M.m : ℝ) * q0) := MR_nonneg M P hpsi_mono hpsi_a hmq0_icc
  have hj := m_mul_n_sub_one_mul_J0_le_convexityGap M hq0 hq0_eq
  have hnMR_eta : (M.n : ℝ) * MR M P ((M.m : ℝ) * q0) * ((M.m : ℝ) * ((M.n : ℝ) - 1) * J0 M q0) ≤
      (M.n : ℝ) * MR M P ((M.m : ℝ) * q0) * cm_convexityGap M.n q0 t0 :=
    mul_le_mul_of_nonneg_left hj (mul_nonneg hn.le hMR_nonneg)
  have hJ0_nonneg : 0 ≤ J0 M q0 := J0_nonneg M hq0.2
  set κ0 : ℝ := ((M.m : ℝ) - 1) ^ 2 + ((M.n : ℝ) - 1)
  have hκ0_pos : 0 < κ0 := by dsimp [κ0]; positivity
  have hκ0_ge_n : (M.n : ℝ) ≤ κ0 := by
    dsimp [κ0]
    have : 1 ≤ ((M.m : ℝ) - 1) ^ 2 := by nlinarith
    linarith
  have halg : (M.n : ℝ) * MR M P ((M.m : ℝ) * q0) * ((M.m : ℝ) * ((M.n : ℝ) - 1) * J0 M q0) -
      (M.n : ℝ) * Z * J0 M q0 =
      (M.n : ℝ) * J0 M q0 * ((M.n : ℝ) - 1) * ((M.m : ℝ) - 1) * M.a * (1 - (M.n : ℝ) / κ0) := by
    dsimp [Z, κ0]; unfold Market.rhoStar
    field_simp [hκ0_pos.ne']; ring
  have hfinal_nonneg : 0 ≤ (M.n : ℝ) * J0 M q0 * ((M.n : ℝ) - 1) * ((M.m : ℝ) - 1) * M.a *
      (1 - (M.n : ℝ) / κ0) := by
    have h1 : 0 ≤ 1 - (M.n : ℝ) / κ0 := by
      rw [sub_nonneg, div_le_one hκ0_pos]; exact hκ0_ge_n
    have ha0 := M.ha0
    positivity
  linarith

/-- Theorem 2, Case 2 (`t0 ≥ 1 / m`, so `q0 ≤ 1 / m`): every deviation gaining traffic
that satisfies Border's condition and Lemma B.1's covered-market rent lower bound earns
at most `R*`. -/
theorem theorem2_case2_gain_traffic (P : M.InverseDemand)
    (hpsi_mono : MonotoneOn M.psi (Icc M.a 1))
    (hpsi_a : 0 ≤ M.psi M.a)
    {q0 t0 ℓ : ℝ} {t : ℝ → ℝ}
    (ht0_ge : 1 / (M.m : ℝ) ≤ t0) (ht0_le_one : t0 ≤ 1)
    (hq0_eq : t0 + ((M.m : ℝ) - 1) * q0 = 1)
    (ht_mono : MonotoneOn t (Icc 0 q0))
    (ht_bounds : ∀ q ∈ Icc (0 : ℝ) q0, 0 ≤ t q ∧ t q ≤ t0)
    (hborder : BorderFeasible M q0 t)
    (hrent : (M.n : ℝ) * M.a * (excessSupply M t q0 + cm_convexityGap M.n q0 t0) ≤ ℓ)
    (hE_ge : 0 ≤ excessSupply M t q0 + cm_convexityGap M.n q0 t0) :
    pathRev M P.P M.rhoStar q0 t0 ℓ t ≤ baselineRev M P.P := by
  have hm : (0 : ℝ) < M.m := M.m_pos_real
  have hm1 : (0 : ℝ) < (M.m : ℝ) - 1 := M.m_sub_one_pos_real
  have hn : (0 : ℝ) < M.n := M.n_pos_real
  have hn1 : (0 : ℝ) < (M.n : ℝ) - 1 := M.n_sub_one_pos_real
  have hq0_nonneg : 0 ≤ q0 := by
    have : 0 ≤ ((M.m : ℝ) - 1) * q0 := by linarith
    exact nonneg_of_mul_nonneg_right this hm1
  have hq0_le : q0 ≤ 1 / (M.m : ℝ) := by
    have h1 : 1 ≤ (M.m : ℝ) * t0 := by
      have h0 := (div_le_iff₀ hm).mp ht0_ge
      linarith
    rw [le_div_iff₀ hm]
    nlinarith
  have hq0_icc : q0 ∈ Icc (0 : ℝ) (1 / (M.m : ℝ)) := ⟨hq0_nonneg, hq0_le⟩
  have hq0_le_one : q0 ≤ 1 := hq0_le.trans (inv_m_le_one M)
  have ht0_eq : t0 = 1 - ((M.m : ℝ) - 1) * q0 := by linarith
  -- Express pathRev - V(q0) = ∫_0^{q0} (Π(t, q) - Π(q, q)) W(q) dq - ℓ
  have hdiff_V : pathRev M P.P M.rhoStar q0 t0 ℓ t - Vfun M P.P q0 =
      (∫ q in (0 : ℝ)..q0, M.cournotRev P.P (t q) q * M.W q) -
      (∫ q in (0 : ℝ)..q0, M.cournotRev P.P q q * M.W q) - ℓ := by
    unfold pathRev Vfun
    rw [ht0_eq]; ring
  -- Integrability of both integrals on [0, q0]
  have ht_dom : ∀ q ∈ Icc (0 : ℝ) q0, t q + ((M.m : ℝ) - 1) * q ∈ Icc (0 : ℝ) 1 := by
    intro q hq
    exact ⟨by have := (ht_bounds q hq).1; nlinarith [hq.1],
           by have := (ht_bounds q hq).2; nlinarith [hq.2]⟩
  have hid_dom : ∀ q ∈ Icc (0 : ℝ) q0, q + ((M.m : ℝ) - 1) * q ∈ Icc (0 : ℝ) 1 := by
    intro q hq
    have harg : q + ((M.m : ℝ) - 1) * q = (M.m : ℝ) * q := by ring
    rw [harg]
    have hmq : (M.m : ℝ) * q ≤ 1 := by
      have h1 := hq.2.trans hq0_le; rwa [le_div_iff₀ hm, mul_comm] at h1
    exact ⟨mul_nonneg hm.le hq.1, hmq⟩
  have hint_t := monotoneOn_cournot_integrable M hq0_nonneg P ht_mono ht_dom
  have hint_id := monotoneOn_cournot_integrable M hq0_nonneg P
    (fun _ _ _ _ hxy => hxy) hid_dom
  -- Apply diagonal tangent bound and Abel IBP on [0, q0]
  let ϱ : ℝ → ℝ := fun q => MR M P ((M.m : ℝ) * q)
  let h : ℝ → ℝ := fun q => ((M.n : ℝ) - 1) * (t q - q) * (1 - q) ^ (M.n - 2)
  have hϱ_cont : ContinuousOn ϱ (Icc 0 q0) := by
    apply (MR_continuousOn M P).comp (continuous_const.mul continuous_id).continuousOn
    intro q hq
    have h1 := hq.2.trans hq0_le; rw [le_div_iff₀ hm, mul_comm] at h1
    exact ⟨mul_nonneg hm.le hq.1, h1⟩
  have hϱ_anti : AntitoneOn ϱ (Icc 0 q0) := by
    intro x hx y hy hxy
    have hx' : (M.m : ℝ) * x ∈ Icc (0 : ℝ) 1 := by
      have h1 := hx.2.trans hq0_le; rw [le_div_iff₀ hm, mul_comm] at h1
      exact ⟨mul_nonneg hm.le hx.1, h1⟩
    have hy' : (M.m : ℝ) * y ∈ Icc (0 : ℝ) 1 := by
      have h1 := hy.2.trans hq0_le; rw [le_div_iff₀ hm, mul_comm] at h1
      exact ⟨mul_nonneg hm.le hy.1, h1⟩
    exact MR_antitoneOn M P hpsi_mono hx' hy' (mul_le_mul_of_nonneg_left hxy hm.le)
  have hh_int : IntervalIntegrable h volume 0 q0 := by
    have hdiff_int : IntervalIntegrable (fun q => t q - q) volume 0 q0 :=
      (ht_mono.mono (by rw [uIcc_of_le hq0_nonneg])).intervalIntegrable.sub
        continuous_id.continuousOn.intervalIntegrable
    have hwt_cont : ContinuousOn (fun q => ((M.n : ℝ) - 1) * (1 - q) ^ (M.n - 2)) (uIcc 0 q0) :=
      (continuous_const.mul ((continuous_const.sub continuous_id).pow (M.n - 2))).continuousOn
    convert hdiff_int.continuousOn_mul hwt_cont using 1
    ext q; dsimp [h]; ring
  have hϱh_int : IntervalIntegrable (fun q => (M.n : ℝ) * (ϱ q * h q)) volume 0 q0 := by
    have hcont : ContinuousOn ϱ (uIcc 0 q0) := by rwa [uIcc_of_le hq0_nonneg]
    exact (hh_int.continuousOn_mul hcont).const_mul (M.n : ℝ)
  have hH_le : ∀ q ∈ Icc (0 : ℝ) q0, ∫ u in (0 : ℝ)..q, h u ≤ 0 := by
    intro q hq
    have hcongr : (∫ u in (0 : ℝ)..q, h u) =
        ((M.n : ℝ) - 1) * ∫ u in (0 : ℝ)..q, (t u - u) * (1 - u) ^ (M.n - 2) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr; intro u _; dsimp [h]; ring
    rw [hcongr]
    exact mul_nonpos_of_nonneg_of_nonpos hn1.le (hborder q hq)
  have hH_q0 : (∫ q in (0 : ℝ)..q0, h q) = excessSupply M t q0 := by
    unfold excessSupply
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr; intro q _; dsimp [h]; ring
  have hint_le :
      (∫ q in (0 : ℝ)..q0, M.cournotRev P.P (t q) q * M.W q) -
        (∫ q in (0 : ℝ)..q0, M.cournotRev P.P q q * M.W q) ≤
      (M.n : ℝ) * MR M P ((M.m : ℝ) * q0) * excessSupply M t q0 := by
    rw [← intervalIntegral.integral_sub hint_t hint_id]
    have hpt : ∀ q ∈ Icc (0 : ℝ) q0,
        M.cournotRev P.P (t q) q * M.W q - M.cournotRev P.P q q * M.W q ≤
          (M.n : ℝ) * (ϱ q * h q) := by
      intro q hq
      have hmq_icc : (M.m : ℝ) * q ∈ Icc (0 : ℝ) 1 := by
        have := hid_dom q hq; have harg : q + ((M.m : ℝ) - 1) * q = (M.m : ℝ) * q := by ring
        rwa [harg] at this
      have htan := cm_tangent_bound_diag M P hpsi_mono (ht_dom q hq) hmq_icc
      have hW : 0 ≤ M.W q := cm_W_nonneg M (hq.2.trans hq0_le_one)
      calc
        M.cournotRev P.P (t q) q * M.W q - M.cournotRev P.P q q * M.W q
            = (M.cournotRev P.P (t q) q - M.cournotRev P.P q q) * M.W q := by ring
        _ ≤ (ϱ q * (t q - q)) * M.W q := mul_le_mul_of_nonneg_right htan hW
        _ = (M.n : ℝ) * (ϱ q * h q) := by dsimp [h, Market.W]; ring
    calc
      (∫ q in (0 : ℝ)..q0, M.cournotRev P.P (t q) q * M.W q - M.cournotRev P.P q q * M.W q)
          ≤ ∫ q in (0 : ℝ)..q0, (M.n : ℝ) * (ϱ q * h q) :=
            intervalIntegral.integral_mono_on hq0_nonneg (hint_t.sub hint_id) hϱh_int hpt
      _ = (M.n : ℝ) * ∫ q in (0 : ℝ)..q0, ϱ q * h q :=
            intervalIntegral.integral_const_mul _ _
      _ ≤ (M.n : ℝ) * (ϱ q0 * ∫ q in (0 : ℝ)..q0, h q) :=
            mul_le_mul_of_nonneg_left
              (cm_integral_antitone_mul_le hq0_nonneg hϱ_cont hϱ_anti hh_int hH_le) hn.le
      _ = (M.n : ℝ) * MR M P ((M.m : ℝ) * q0) * excessSupply M t q0 := by
            rw [hH_q0]; dsimp [ϱ]; ring
  -- Maximize the linear bound over E = excessSupply M t q0 ∈ [-η, 0]
  have hE_nonpos : excessSupply M t q0 ≤ 0 := by
    rw [← hH_q0]; exact hH_le q0 ⟨hq0_nonneg, le_rfl⟩
  by_cases hcase : M.a ≤ MR M P ((M.m : ℝ) * q0)
  · have hlin : (M.n : ℝ) * MR M P ((M.m : ℝ) * q0) * excessSupply M t q0 -
        (M.n : ℝ) * M.a * (excessSupply M t q0 + cm_convexityGap M.n q0 t0) ≤
        -((M.n : ℝ) * M.a * cm_convexityGap M.n q0 t0) := by
      have : (M.n : ℝ) * (MR M P ((M.m : ℝ) * q0) - M.a) * excessSupply M t q0 ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hn.le (sub_nonneg.mpr hcase)) hE_nonpos
      linarith
    have hV := Vfun_sub_na_eta_le_baseline M P hq0_icc hq0_eq
    linarith
  · push Not at hcase
    have hlin : (M.n : ℝ) * MR M P ((M.m : ℝ) * q0) * excessSupply M t q0 -
        (M.n : ℝ) * M.a * (excessSupply M t q0 + cm_convexityGap M.n q0 t0) ≤
        -((M.n : ℝ) * MR M P ((M.m : ℝ) * q0) * cm_convexityGap M.n q0 t0) := by
      have : (M.n : ℝ) * (MR M P ((M.m : ℝ) * q0) - M.a) *
          (excessSupply M t q0 + cm_convexityGap M.n q0 t0) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hn.le (by linarith)) hE_ge
      linarith
    have hV := Vfun_sub_nMR_eta_le_baseline M P hpsi_mono hpsi_a hq0_icc hq0_eq
    linarith

end Case2

/-! ### Main Theorem 2 and Virág's Reserve Game -/

/-- **Theorem 2 (Covered Markets)**:
In a covered market (`0 < M.a`) with nondecreasing Cournot marginal revenue `M.psi`
on `[M.a, 1]` and `0 ≤ M.psi M.a` (equivalently `1 / M.m ≤ M.a * M.f M.a`),
every Border-feasible quantity-path deviation with Lemma B.1's rent lower bound
earns at most the symmetric candidate revenue `R*` at `ρ*`. -/
theorem theorem2_covered_markets (M : Market) (_ha : 0 < M.a) (P : M.InverseDemand)
    (hpsi_mono : MonotoneOn M.psi (Icc M.a 1))
    (hpsi_a : 0 ≤ M.psi M.a)
    {q0 t0 ℓ : ℝ} {t : ℝ → ℝ}
    (ht0_nonneg : 0 ≤ t0) (ht0_le_one : t0 ≤ 1)
    (hq0_eq : t0 + ((M.m : ℝ) - 1) * q0 = 1)
    (hℓ_nonneg : 0 ≤ ℓ)
    (ht_mono : MonotoneOn t (Icc 0 q0))
    (ht_bounds : ∀ q ∈ Icc (0 : ℝ) q0, 0 ≤ t q ∧ t q ≤ t0)
    (hborder : BorderFeasible M q0 t)
    (hrent : (M.n : ℝ) * M.a * (excessSupply M t q0 + cm_convexityGap M.n q0 t0) ≤ ℓ)
    (hE_ge : 0 ≤ excessSupply M t q0 + cm_convexityGap M.n q0 t0) :
    pathRev M P.P M.rhoStar q0 t0 ℓ t ≤ baselineRev M P.P := by
  by_cases ht0 : t0 ≤ 1 / (M.m : ℝ)
  · exact theorem2_case1_lose_traffic M P hpsi_mono hpsi_a
      ht0_nonneg ht0 hq0_eq hℓ_nonneg ht_mono ht_bounds hborder
  · push Not at ht0
    exact theorem2_case2_gain_traffic M P hpsi_mono hpsi_a
      ht0.le ht0_le_one hq0_eq ht_mono ht_bounds hborder hrent hE_ge

/-- **Theorem 2, Virág's Reserve Game Corollary**:
Without any monotonicity assumption on `M.psi`:
1. Pure reserve cuts (`t0 ≥ 1 / m`, `t = id`, `ℓ ≥ n * a * η`) never improve upon `R*`
   for ANY covered distribution (using only `P ≥ a`).
2. Whenever `M.psi ≥ 0` on `[M.a, 1]`, pure reserve increases (`t0 ≤ 1 / m`) also never
   improve upon `R*`.
Hence `M.psi ≥ 0` on `[M.a, 1]` alone suffices for `SPA(ρ*)^m` to be an equilibrium of
Virág's reserve game. -/
theorem theorem2_virag_reserve_game (M : Market) (_ha : 0 < M.a) (P : M.InverseDemand)
    (hpsi_nonneg : ∀ v ∈ Icc M.a 1, 0 ≤ M.psi v) :
    (∀ t0 ∈ Icc (0 : ℝ) (1 / (M.m : ℝ)),
      reserveIncreaseRev M P.P M.rhoStar t0 ≤ baselineRev M P.P) ∧
    (∀ q0 t0 ℓ : ℝ, q0 ∈ Icc (0 : ℝ) (1 / (M.m : ℝ)) →
      t0 + ((M.m : ℝ) - 1) * q0 = 1 →
      (M.n : ℝ) * M.a * cm_convexityGap M.n q0 t0 ≤ ℓ →
      pathRev M P.P M.rhoStar q0 t0 ℓ id ≤ baselineRev M P.P) :=
  ⟨fun _ ht0 => reserveIncreaseRev_le_baseline M P hpsi_nonneg ht0,
   fun _ _ _ hq0 hq0_eq hrent => pure_reserve_cut_le_baseline M P hq0 hq0_eq hrent⟩

/-! ### Example 1: Non-Regular Truncated Pareto Distribution (`m = 2`, `a = 1/2`) -/

section Example1

/-- Derivative of `Real.sqrt` at any strictly positive real number. -/
private lemma hasDerivAt_real_sqrt {x : ℝ} (hx : 0 < x) :
    HasDerivAt Real.sqrt (1 / (2 * Real.sqrt x)) x := by
  have hrpow : HasDerivAt (fun t : ℝ => t ^ (1 / 2 : ℝ)) ((1 / 2 : ℝ) * x ^ ((1 / 2 : ℝ) - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hx.ne')
  have heq : Real.sqrt = fun t : ℝ => t ^ (1 / 2 : ℝ) := by
    ext t; exact Real.sqrt_eq_rpow t
  rw [heq]
  convert hrpow using 1
  have hexp : (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) := by norm_num
  rw [hexp, Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow]
  have hsq : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  rw [Real.sqrt_eq_rpow] at hsq ⊢
  field_simp [hsq]

/-- Shifted linear argument `u(v) = 1 + 198(v - 1/2)` in Example 1. -/
noncomputable def ex1U (v : ℝ) : ℝ := 1 + 198 * (v - 1 / 2)

/-- Survival function `S(v) = (1 + 198(v - 1/2))^(-1/2)` in Example 1. -/
noncomputable def ex1S (v : ℝ) : ℝ := (Real.sqrt (ex1U v))⁻¹

/-- Raw CDF formula `(10/9) * (1 - S(v))` on `[1/2, 1]`. -/
noncomputable def ex1F_raw (v : ℝ) : ℝ := (10 / 9 : ℝ) * (1 - ex1S v)

/-- Truncated Pareto CDF `F(v)` for Example 1 (`0` for `v ≤ 1/2`). -/
noncomputable def ex1F (v : ℝ) : ℝ := if v ≤ 1 / 2 then 0 else ex1F_raw v

/-- Raw density formula `110 * S(v)^3` on `[1/2, 1]`. -/
noncomputable def ex1f_raw (v : ℝ) : ℝ := 110 * (ex1S v) ^ 3

/-- Truncated Pareto density `f(v)` for Example 1 (`0` for `v < 1/2`). -/
noncomputable def ex1f (v : ℝ) : ℝ := if v < 1 / 2 then 0 else ex1f_raw v

/-- Derivative `f'(v) = -32670 * S(v)^5` of the Example 1 density on `[1/2, 1]`. -/
noncomputable def ex1f' (v : ℝ) : ℝ := -32670 * (ex1S v) ^ 5

/-- Explicit closed-form inverse demand `P(z) = 1/2 + (100/(1 + 9z)^2 - 1)/198` for Example 1. -/
noncomputable def ex1P (z : ℝ) : ℝ := 1 / 2 + (100 / (1 + 9 * z) ^ 2 - 1) / 198

private lemma ex1U_pos {v : ℝ} (hv : 1 / 2 ≤ v) : 0 < ex1U v := by
  unfold ex1U; linarith

private lemma ex1S_pos {v : ℝ} (hv : 1 / 2 ≤ v) : 0 < ex1S v :=
  inv_pos.mpr (Real.sqrt_pos.mpr (ex1U_pos hv))

private lemma ex1S_half : ex1S (1 / 2) = 1 := by
  unfold ex1S ex1U; norm_num

private lemma ex1S_one : ex1S 1 = 1 / 10 := by
  unfold ex1S ex1U
  have h100 : (1 : ℝ) + 198 * (1 - 1 / 2) = 10 ^ 2 := by norm_num
  rw [h100, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 10)]
  norm_num

private lemma ex1S_hasDerivAt {v : ℝ} (hv : 0 < ex1U v) :
    HasDerivAt ex1S (-99 * (ex1S v) ^ 3) v := by
  have hu : HasDerivAt ex1U 198 v := by
    unfold ex1U
    have h1 : HasDerivAt (fun x : ℝ => x - 1 / 2) 1 v := by
      simpa using (hasDerivAt_id' v).sub_const (1 / 2 : ℝ)
    have h2 := (hasDerivAt_const v (1 : ℝ)).fun_add (h1.const_mul 198)
    convert h2 using 1; ring
  have hsq : HasDerivAt (fun x => Real.sqrt (ex1U x)) (99 * ex1S v) v := by
    have hc : HasDerivAt (fun x => Real.sqrt (ex1U x))
        ((1 / (2 * Real.sqrt (ex1U v))) * 198) v :=
      (hasDerivAt_real_sqrt hv).comp v hu
    convert hc using 1
    unfold ex1S
    have hne : Real.sqrt (ex1U v) ≠ 0 := (Real.sqrt_pos.mpr hv).ne'
    field_simp [hne]; ring
  have hinv := hsq.fun_inv (Real.sqrt_pos.mpr hv).ne'
  show HasDerivAt (fun x => (Real.sqrt (ex1U x))⁻¹) _ v
  convert hinv using 1
  unfold ex1S
  have hne : Real.sqrt (ex1U v) ≠ 0 := (Real.sqrt_pos.mpr hv).ne'
  field_simp [hne]

private lemma ex1F_raw_hasDerivAt {v : ℝ} (hv : 0 < ex1U v) :
    HasDerivAt ex1F_raw (ex1f_raw v) v := by
  unfold ex1F_raw ex1f_raw
  have h1 := (hasDerivAt_const v (1 : ℝ)).fun_sub (ex1S_hasDerivAt hv)
  have h2 := h1.const_mul (10 / 9 : ℝ)
  convert h2 using 1; ring

private lemma ex1f_raw_hasDerivAt {v : ℝ} (hv : 0 < ex1U v) :
    HasDerivAt ex1f_raw (ex1f' v) v := by
  unfold ex1f_raw ex1f'
  have h1 := ((ex1S_hasDerivAt hv).fun_pow 3).const_mul (110 : ℝ)
  convert h1 using 1; ring

private lemma ex1F_eq_raw {v : ℝ} (hv : 1 / 2 ≤ v) : ex1F v = ex1F_raw v := by
  unfold ex1F
  split_ifs with hle
  · have hveq : v = 1 / 2 := le_antisymm hle hv
    subst hveq
    unfold ex1F_raw
    rw [ex1S_half]; ring
  · rfl

private lemma ex1f_eq_raw {v : ℝ} (hv : 1 / 2 ≤ v) : ex1f v = ex1f_raw v := by
  unfold ex1f
  split_ifs with hlt
  · linarith
  · rfl

/-- **Example 1 (`SmoothMarket` construction)**:
Duopoly (`m = 2`) with `n ≥ 2` buyers, support `[1/2, 1]`, and truncated Pareto
distribution `F(v) = (10/9) * (1 - (1 + 198(v - 1/2))^(-1/2))` on `[1/2, 1]`. -/
noncomputable def example1_pareto_market (n : ℕ) (hn : 2 ≤ n) : SmoothMarket where
  m := 2
  n := n
  hm := le_rfl
  hn := hn
  a := 1 / 2
  ha0 := by norm_num
  ha1 := by norm_num
  F := ex1F
  f := ex1f
  f' := ex1f'
  hF_a := by unfold ex1F; simp
  hF_1 := by
    rw [ex1F_eq_raw (by norm_num : (1 / 2 : ℝ) ≤ 1)]
    unfold ex1F_raw; rw [ex1S_one]; norm_num
  hF_below := fun v hv => by unfold ex1F; exact ite_eq_left_iff.mpr (fun h => absurd hv h)
  hf_below := fun v hv => by unfold ex1f; exact ite_eq_left_iff.mpr (fun h => absurd hv h)
  hf_cont := by
    have hraw : ContinuousOn ex1f_raw (Icc (1 / 2) 1) := fun v hv =>
      (ex1f_raw_hasDerivAt (ex1U_pos hv.1)).continuousAt.continuousWithinAt
    exact hraw.congr (fun v hv => ex1f_eq_raw hv.1)
  hf_pos := fun v hv => by
    rw [ex1f_eq_raw hv.1]
    unfold ex1f_raw
    have hS := ex1S_pos hv.1
    positivity
  hF_deriv_within := fun v hv => by
    rw [ex1f_eq_raw hv.1]
    exact (ex1F_raw_hasDerivAt (ex1U_pos hv.1)).hasDerivWithinAt.congr
      (fun x hx => ex1F_eq_raw hx.1) (ex1F_eq_raw hv.1)
  hF_deriv_open := fun v hv => by
    rw [ex1f_eq_raw hv.1.le]
    have hnhds : ex1F =ᶠ[nhds v] ex1F_raw := by
      filter_upwards [Ioi_mem_nhds hv.1] with x hx
      exact ex1F_eq_raw (le_of_lt hx)
    exact (ex1F_raw_hasDerivAt (ex1U_pos hv.1.le)).congr_of_eventuallyEq hnhds
  hf'_cont := by
    have hS_cont : ContinuousOn ex1S (Icc (1 / 2) 1) := fun v hv =>
      (ex1S_hasDerivAt (ex1U_pos hv.1)).continuousAt.continuousWithinAt
    unfold ex1f'
    exact continuousOn_const.mul (hS_cont.pow 5)
  hf_deriv_within := fun v hv =>
    (ex1f_raw_hasDerivAt (ex1U_pos hv.1)).hasDerivWithinAt.congr
      (fun x hx => ex1f_eq_raw hx.1) (ex1f_eq_raw hv.1)
  hf_deriv_open := fun v hv => by
    have hnhds : ex1f =ᶠ[nhds v] ex1f_raw := by
      filter_upwards [Ioi_mem_nhds hv.1] with x hx
      exact ex1f_eq_raw (le_of_lt hx)
    exact (ex1f_raw_hasDerivAt (ex1U_pos hv.1.le)).congr_of_eventuallyEq hnhds

/-- Explicit inverse demand `P : InverseDemand` for Example 1. -/
noncomputable def example1_inverseDemand (n : ℕ) (hn : 2 ≤ n) :
    (example1_pareto_market n hn).toMarket.InverseDemand where
  P := ex1P
  hP_mem := fun z hz => by
    change ex1P z ∈ Set.Icc (1 / 2 : ℝ) 1
    unfold ex1P
    have hden : 1 ≤ 1 + 9 * z := by linarith [hz.1]
    have hden_le : 1 + 9 * z ≤ 10 := by linarith [hz.2]
    have hsq_ge : (1 : ℝ) ≤ (1 + 9 * z) ^ 2 := by nlinarith
    have hsq_le : (1 + 9 * z) ^ 2 ≤ 100 := by nlinarith
    have hq_ge : 1 ≤ 100 / (1 + 9 * z) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have hq_le : 100 / (1 + 9 * z) ^ 2 ≤ 100 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    constructor <;> linarith
  hP_right := fun z hz => by
    change ex1F (ex1P z) = 1 - z
    have hden : 0 < 1 + 9 * z := by linarith [hz.1]
    have hden_le : 1 + 9 * z ≤ 10 := by linarith [hz.2]
    have hsq_le : (1 + 9 * z) ^ 2 ≤ 100 := by nlinarith
    have hP_ge : (1 / 2 : ℝ) ≤ ex1P z := by
      unfold ex1P
      have : 1 ≤ 100 / (1 + 9 * z) ^ 2 := by rw [le_div_iff₀ (by positivity)]; linarith
      linarith
    rw [ex1F_eq_raw hP_ge]
    unfold ex1F_raw ex1S ex1U ex1P
    have hsimp : 1 + 198 * (1 / 2 + (100 / (1 + 9 * z) ^ 2 - 1) / 198 - 1 / 2) =
        (10 / (1 + 9 * z)) ^ 2 := by
      field_simp [hden.ne']; ring
    rw [hsimp, Real.sqrt_sq (by positivity : 0 ≤ 10 / (1 + 9 * z))]
    field_simp [hden.ne']; ring
  hP_left := fun v hv => by
    change ex1P (1 - ex1F v) = v
    rw [ex1F_eq_raw hv.1]
    unfold ex1P ex1F_raw ex1S
    have hU : 0 < ex1U v := ex1U_pos hv.1
    have hsq : Real.sqrt (ex1U v) ≠ 0 := (Real.sqrt_pos.mpr hU).ne'
    have h1 : 1 + 9 * (1 - (10 / 9 : ℝ) * (1 - (Real.sqrt (ex1U v))⁻¹)) =
        10 / Real.sqrt (ex1U v) := by
      field_simp [hsq]; ring
    rw [h1]
    have hsq2 : (10 / Real.sqrt (ex1U v)) ^ 2 = 100 / ex1U v := by
      rw [div_pow, Real.sq_sqrt hU.le]; norm_num
    rw [hsq2]
    have h2 : 100 / (100 / ex1U v) = ex1U v := by
      field_simp [hU.ne']
    rw [h2]
    unfold ex1U; ring
  hP_zero := by unfold ex1P; norm_num
  hP_one := by change ex1P 1 = 1 / 2; unfold ex1P; norm_num
  hP_cont := by
    unfold ex1P
    apply continuousOn_const.add
    apply ContinuousOn.div_const
    apply ContinuousOn.sub _ continuousOn_const
    apply continuousOn_const.div
    · exact ((continuous_const.add (continuous_const.mul continuous_id)).pow 2).continuousOn
    · intro z hz
      have hpos : 0 < 1 + 9 * z := by linarith [hz.1]
      exact pow_ne_zero 2 hpos.ne'
  hP_strictAnti := fun x hx y hy hxy => by
    unfold ex1P
    have hx' : 0 < 1 + 9 * x := by linarith [hx.1]
    have hy' : 0 < 1 + 9 * y := by linarith [hy.1]
    have hsq : (1 + 9 * x) ^ 2 < (1 + 9 * y) ^ 2 := by nlinarith
    have hdiv : 100 / (1 + 9 * y) ^ 2 < 100 / (1 + 9 * x) ^ 2 := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      linarith
    linarith
  hP_deriv_open := fun z hz => by
    have hden : 0 < 1 + 9 * z := by linarith [hz.1]
    have hsq_le : (1 + 9 * z) ^ 2 ≤ 100 := by nlinarith [hz.2]
    have hP_ge : (1 / 2 : ℝ) ≤ ex1P z := by
      unfold ex1P
      have : 1 ≤ 100 / (1 + 9 * z) ^ 2 := by rw [le_div_iff₀ (by positivity)]; linarith
      linarith
    have hS_val : ex1S (ex1P z) = (1 + 9 * z) / 10 := by
      unfold ex1S ex1U ex1P
      have hsimp : 1 + 198 * (1 / 2 + (100 / (1 + 9 * z) ^ 2 - 1) / 198 - 1 / 2) =
          (10 / (1 + 9 * z)) ^ 2 := by field_simp [hden.ne']; ring
      rw [hsimp, Real.sqrt_sq (by positivity : 0 ≤ 10 / (1 + 9 * z))]
      field_simp [hden.ne']
    have hf_val : ex1f (ex1P z) = 11 * (1 + 9 * z) ^ 3 / 100 := by
      rw [ex1f_eq_raw hP_ge]; unfold ex1f_raw; rw [hS_val]; ring
    change HasDerivAt ex1P (-1 / ex1f (ex1P z)) z
    rw [hf_val]
    have hlin : HasDerivAt (fun x : ℝ => 1 + 9 * x) 9 z := by
      have := (hasDerivAt_const z (1 : ℝ)).fun_add ((hasDerivAt_id' z).const_mul 9)
      simpa using this
    have hpow := hlin.fun_pow 2
    have hdiv := (hasDerivAt_const z (100 : ℝ)).fun_div hpow (by positivity)
    have hsub := hdiv.sub_const (1 : ℝ)
    have hdiv198 := hsub.div_const (198 : ℝ)
    have hadd := (hasDerivAt_const z (1 / 2 : ℝ)).fun_add hdiv198
    show HasDerivAt (fun x => 1 / 2 + (100 / (1 + 9 * x) ^ 2 - 1) / 198) _ z
    convert hadd using 1
    field_simp [hden.ne']; ring
  hP_deriv_within := fun z hz => by
    have hden : 0 < 1 + 9 * z := by linarith [hz.1]
    have hsq_le : (1 + 9 * z) ^ 2 ≤ 100 := by nlinarith [hz.2]
    have hP_ge : (1 / 2 : ℝ) ≤ ex1P z := by
      unfold ex1P
      have : 1 ≤ 100 / (1 + 9 * z) ^ 2 := by rw [le_div_iff₀ (by positivity)]; linarith
      linarith
    have hS_val : ex1S (ex1P z) = (1 + 9 * z) / 10 := by
      unfold ex1S ex1U ex1P
      have hsimp : 1 + 198 * (1 / 2 + (100 / (1 + 9 * z) ^ 2 - 1) / 198 - 1 / 2) =
          (10 / (1 + 9 * z)) ^ 2 := by field_simp [hden.ne']; ring
      rw [hsimp, Real.sqrt_sq (by positivity : 0 ≤ 10 / (1 + 9 * z))]
      field_simp [hden.ne']
    have hf_val : ex1f (ex1P z) = 11 * (1 + 9 * z) ^ 3 / 100 := by
      rw [ex1f_eq_raw hP_ge]; unfold ex1f_raw; rw [hS_val]; ring
    change HasDerivWithinAt ex1P (-1 / ex1f (ex1P z)) (Icc 0 1) z
    rw [hf_val]
    have hlin : HasDerivAt (fun x : ℝ => 1 + 9 * x) 9 z := by
      have := (hasDerivAt_const z (1 : ℝ)).fun_add ((hasDerivAt_id' z).const_mul 9)
      simpa using this
    have hpow := hlin.fun_pow 2
    have hdiv := (hasDerivAt_const z (100 : ℝ)).fun_div hpow (by positivity)
    have hsub := hdiv.sub_const (1 : ℝ)
    have hdiv198 := hsub.div_const (198 : ℝ)
    have hadd := (hasDerivAt_const z (1 / 2 : ℝ)).fun_add hdiv198
    have hderiv : HasDerivAt ex1P (-1 / (11 * (1 + 9 * z) ^ 3 / 100)) z := by
      show HasDerivAt (fun x => 1 / 2 + (100 / (1 + 9 * x) ^ 2 - 1) / 198) _ z
      convert hadd using 1
      field_simp [hden.ne']; ring
    exact hderiv.hasDerivWithinAt

/-- Closed-form curvature in Example 1:
`E(v) = 3 * (1 - (1/10) * sqrt(1 + 198 * (v - 1/2)))` for all `v ∈ [1/2, 1]`. -/
theorem example1_curvatureE (n : ℕ) (hn : 2 ≤ n) {v : ℝ} (hv : v ∈ Icc (1 / 2 : ℝ) 1) :
    curvatureE (example1_pareto_market n hn) v =
      3 * (1 - (1 / 10 : ℝ) * Real.sqrt (1 + 198 * (v - 1 / 2))) := by
  unfold curvatureE
  change -((1 - ex1F v) * ex1f' v) / (ex1f v) ^ 2 = _
  rw [ex1F_eq_raw hv.1, ex1f_eq_raw hv.1]
  unfold ex1F_raw ex1f_raw ex1f' ex1S ex1U
  set r : ℝ := Real.sqrt (1 + 198 * (v - 1 / 2))
  have hr : r ≠ 0 := (Real.sqrt_pos.mpr (ex1U_pos hv.1)).ne'
  field_simp [hr]
  ring

/-- At `v = 1/2`, curvature is `E(1/2) = 27 / 10 > 2`. -/
theorem example1_curvatureE_at_half (n : ℕ) (hn : 2 ≤ n) :
    curvatureE (example1_pareto_market n hn) (1 / 2) = 27 / 10 ∧
      2 < curvatureE (example1_pareto_market n hn) (1 / 2) := by
  have h := example1_curvatureE n hn (by norm_num : (1 / 2 : ℝ) ∈ Set.Icc (1 / 2 : ℝ) 1)
  have hval : curvatureE (example1_pareto_market n hn) (1 / 2) = 27 / 10 := by
    rw [h]; norm_num
  exact ⟨hval, by linarith⟩

/-- At `v = 1/2`, Myerson's virtual valuation is strictly positive:
`ψ_1(1/2) = 27 / 55 > 0` (so a monopolist serves types near `1/2`). -/
theorem example1_psi1_pos_at_half (n : ℕ) (hn : 2 ≤ n) :
    (example1_pareto_market n hn).toMarket.psi1 (1 / 2) = 27 / 55 ∧
      0 < (example1_pareto_market n hn).toMarket.psi1 (1 / 2) := by
  have hval : (example1_pareto_market n hn).toMarket.psi1 (1 / 2) = 27 / 55 := by
    unfold Market.psi1
    change (1 / 2 : ℝ) - (1 - ex1F (1 / 2)) / ex1f (1 / 2) = 27 / 55
    rw [ex1F_eq_raw le_rfl, ex1f_eq_raw le_rfl]
    unfold ex1F_raw ex1f_raw
    rw [ex1S_half]; norm_num
  exact ⟨hval, by linarith⟩

/-- **Example 1 (Monopolist Irons)**:
Myerson's virtual valuation `ψ_1` is strictly decreasing on `[1/2, 1/2 + 91/1782]`
(since `E(v) > 2` on `[1/2, 1/2 + 91/1782)`), while `ψ_1(1/2) > 0`; thus a monopolist
serves types near `1/2` and irons. -/
theorem example1_monopolist_irons (n : ℕ) (hn : 2 ≤ n) :
    StrictAntiOn (example1_pareto_market n hn).toMarket.psi1
      (Icc (1 / 2 : ℝ) (1 / 2 + 91 / 1782)) := by
  let M := (example1_pareto_market n hn).toMarket
  have hsub : Icc (1 / 2 : ℝ) (1 / 2 + 91 / 1782) ⊆ Icc (1 / 2 : ℝ) 1 :=
    Icc_subset_Icc_right (by norm_num)
  have hcont : ContinuousOn M.psi1 (Icc (1 / 2) (1 / 2 + 91 / 1782)) := by
    unfold Market.psi1
    apply continuousOn_id.sub
    apply (continuousOn_const.sub (M.F_continuousOn.mono hsub)).div (M.hf_cont.mono hsub)
    intro v hv
    exact (M.hf_pos v (hsub hv)).ne'
  have hderiv : ∀ v ∈ Ioo (1 / 2 : ℝ) (1 / 2 + 91 / 1782),
      HasDerivAt M.psi1 (2 - curvatureE (example1_pareto_market n hn) v) v := by
    intro v hv
    have hv_open : v ∈ Ioo (1 / 2 : ℝ) 1 := ⟨hv.1, lt_of_lt_of_le hv.2 (by norm_num)⟩
    have hv_icc : v ∈ Icc (1 / 2 : ℝ) 1 := Ioo_subset_Icc_self hv_open
    have hF := M.hF_deriv_open v hv_open
    have hf := (example1_pareto_market n hn).hf_deriv_open v hv_open
    have hnum := (hasDerivAt_const v (1 : ℝ)).fun_sub hF
    have hfrac := hnum.fun_div hf (M.hf_pos v hv_icc).ne'
    have hpsi := (hasDerivAt_id' v).fun_sub hfrac
    show HasDerivAt (fun x => x - (1 - M.F x) / M.f x) _ v
    convert hpsi using 1
    unfold curvatureE
    have hfne : M.f v ≠ 0 := (M.hf_pos v hv_icc).ne'
    change 2 - -((1 - M.F v) * (example1_pareto_market n hn).f' v) / (M.f v) ^ 2 =
      1 - ((0 - M.f v) * M.f v - (1 - M.F v) * (example1_pareto_market n hn).f' v) / (M.f v) ^ 2
    field_simp [hfne]; ring
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hcont
  intro v hv
  rw [interior_Icc] at hv
  rw [(hderiv v hv).deriv]
  have hv_icc : v ∈ Icc (1 / 2 : ℝ) 1 := hsub (Ioo_subset_Icc_self hv)
  rw [example1_curvatureE n hn hv_icc]
  have hu_lt : 1 + 198 * (v - 1 / 2) < (10 / 3 : ℝ) ^ 2 := by linarith [hv.2]
  have hsq_lt : Real.sqrt (1 + 198 * (v - 1 / 2)) < 10 / 3 := by
    have h1 := Real.sqrt_lt_sqrt (ex1U_pos hv.1.le).le hu_lt
    rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 10 / 3)] at h1
  linarith

/-- Curvature in Example 1 satisfies `E(v) < 3 = m + 1` everywhere on `[1/2, 1]`. -/
theorem example1_curvatureE_lt_three (n : ℕ) (hn : 2 ≤ n) {v : ℝ}
    (hv : v ∈ Icc (1 / 2 : ℝ) 1) :
    curvatureE (example1_pareto_market n hn) v < 3 := by
  rw [example1_curvatureE n hn hv]
  have hsq : 0 < Real.sqrt (1 + 198 * (v - 1 / 2)) :=
    Real.sqrt_pos.mpr (ex1U_pos hv.1)
  linarith

/-- Candidate reserve in Example 1: `ρ* = (n - 1) / (2 * n)` for `m = 2`, `a = 1/2`. -/
theorem example1_rhoStar (n : ℕ) (hn : 2 ≤ n) :
    (example1_pareto_market n hn).toMarket.rhoStar = ((n : ℝ) - 1) / (2 * (n : ℝ)) := by
  unfold Market.rhoStar
  change ((n : ℝ) - 1) * (1 / 2 : ℝ) / ((((2 : ℕ) : ℝ) - 1) ^ 2 + ((n : ℝ) - 1)) =
    ((n : ℝ) - 1) / (2 * (n : ℝ))
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hn)
  have hden : ((((2 : ℕ) : ℝ) - 1) ^ 2 + ((n : ℝ) - 1)) = (n : ℝ) := by norm_num
  rw [hden]
  field_simp [hn_pos.ne']

/-- **Example 1 (Duopoly Cournot Condition and Equilibrium)**:
In the Example 1 duopoly (`m = 2`, `a = 1/2`) for every `n ≥ 2`:
1. `ψ_2` is strictly increasing on `[1/2, 1]` (since `E(v) < 3` everywhere).
2. `ψ_2(1/2) = 109 / 220 > 0`.
3. `ρ* = (n - 1) / (2 * n)`.
4. By Theorem 2, every Border-feasible quantity-path deviation with Lemma B.1's rent lower
   bound earns at most the symmetric candidate revenue `R*` at `ρ* = (n - 1) / (2 * n)`. -/
theorem example1_duopoly_cournot (n : ℕ) (hn : 2 ≤ n) :
    let M := (example1_pareto_market n hn).toMarket
    let P := example1_inverseDemand n hn
    StrictMonoOn M.psi (Icc (1 / 2 : ℝ) 1) ∧
    M.psi (1 / 2) = 109 / 220 ∧
    0 < M.psi (1 / 2) ∧
    M.rhoStar = ((n : ℝ) - 1) / (2 * (n : ℝ)) ∧
    (∀ q0 t0 ℓ : ℝ, ∀ t : ℝ → ℝ,
      0 ≤ t0 → t0 ≤ 1 → t0 + q0 = 1 → 0 ≤ ℓ →
      MonotoneOn t (Icc 0 q0) →
      (∀ q ∈ Icc (0 : ℝ) q0, 0 ≤ t q ∧ t q ≤ t0) →
      BorderFeasible M q0 t →
      (n : ℝ) * (1 / 2 : ℝ) * (excessSupply M t q0 + cm_convexityGap n q0 t0) ≤ ℓ →
      0 ≤ excessSupply M t q0 + cm_convexityGap n q0 t0 →
      pathRev M P.P (((n : ℝ) - 1) / (2 * (n : ℝ))) q0 t0 ℓ t ≤ baselineRev M P.P) := by
  intro M P
  have hpsi_half : M.psi (1 / 2) = 109 / 220 := by
    unfold Market.psi
    change (1 / 2 : ℝ) - (1 - ex1F (1 / 2)) / (((2 : ℕ) : ℝ) * ex1f (1 / 2)) = 109 / 220
    rw [ex1F_eq_raw le_rfl, ex1f_eq_raw le_rfl]
    unfold ex1F_raw ex1f_raw
    rw [ex1S_half]; norm_num
  have hpsi_pos : 0 < M.psi (1 / 2) := by linarith
  have hpsi_strict : StrictMonoOn M.psi (Icc (1 / 2 : ℝ) 1) := by
    have hcont : ContinuousOn M.psi (Icc (1 / 2 : ℝ) 1) := cm_psi_continuousOn M
    have hderiv : ∀ v ∈ Ioo (1 / 2 : ℝ) 1,
        HasDerivAt M.psi ((3 - curvatureE (example1_pareto_market n hn) v) / 2) v := by
      intro v hv
      have hv_icc : v ∈ Icc (1 / 2 : ℝ) 1 := Ioo_subset_Icc_self hv
      have hF := M.hF_deriv_open v hv
      have hf := (example1_pareto_market n hn).hf_deriv_open v hv
      have hnum := (hasDerivAt_const v (1 : ℝ)).fun_sub hF
      have hden := hf.const_mul ((M.m : ℝ))
      have hden_ne : (M.m : ℝ) * M.f v ≠ 0 := (mul_pos M.m_pos_real (M.hf_pos v hv_icc)).ne'
      have hfrac := hnum.fun_div hden hden_ne
      have hpsi := (hasDerivAt_id' v).fun_sub hfrac
      show HasDerivAt (fun x => x - (1 - M.F x) / ((M.m : ℝ) * M.f x)) _ v
      convert hpsi using 1
      unfold curvatureE
      have hm2 : (M.m : ℝ) = 2 := by change ((2 : ℕ) : ℝ) = 2; norm_num
      have hfne : M.f v ≠ 0 := (M.hf_pos v hv_icc).ne'
      change (3 - -((1 - M.F v) * (example1_pareto_market n hn).f' v) / (M.f v) ^ 2) / 2 =
        1 - ((0 - M.f v) * ((M.m : ℝ) * M.f v) -
          (1 - M.F v) * ((M.m : ℝ) * (example1_pareto_market n hn).f' v)) /
          ((M.m : ℝ) * M.f v) ^ 2
      rw [hm2]
      field_simp [hfne]; ring
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hcont
    intro v hv
    rw [interior_Icc] at hv
    rw [(hderiv v hv).deriv]
    have hE := example1_curvatureE_lt_three n hn (Ioo_subset_Icc_self hv)
    linarith
  have hrho : M.rhoStar = ((n : ℝ) - 1) / (2 * (n : ℝ)) := example1_rhoStar n hn
  refine ⟨hpsi_strict, hpsi_half, hpsi_pos, hrho, ?_⟩
  intro q0 t0 ℓ t ht0_0 ht0_1 hsum hℓ ht_mono ht_bds hborder hrent hE_ge
  rw [← hrho]
  have hq0_eq : t0 + ((M.m : ℝ) - 1) * q0 = 1 := by
    have hm2 : (M.m : ℝ) = 2 := by change ((2 : ℕ) : ℝ) = 2; norm_num
    rw [hm2]; linarith
  exact theorem2_covered_markets M (by change (0 : ℝ) < 1 / 2; norm_num) P
    hpsi_strict.monotoneOn hpsi_pos.le ht0_0 ht0_1 hq0_eq hℓ ht_mono ht_bds hborder hrent hE_ge

end Example1

end AuctionCompetition
