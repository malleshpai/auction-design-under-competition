import AuctionCompetition.Defs
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.Monotone
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Auction Design under Competition: Cournot Representation, Interior Pools, and Smaller Sellers

Formalization of Sections 4.1–4.2 and Appendix B (Lemma B.1, Proposition 3, Theorem 1,
Corollary 1) of Mallesh M. Pai, *Auction Design under Competition*.

## Main results

1. **Inverse demand construction (`exists_inverseDemand`, `Market.inverseDemand`)**:
   Every `M : Market` admits an inverse demand `P : M.InverseDemand` on `[0, 1]` with
   `F (P z) = 1 - z`, `P (1 - F v) = v`, continuity, strict antitonicity, and derivative
   `P'(z) = -1 / f (P z)`.
2. **Tangent bounds (`tangent_bound_diag`, `tangent_bound_general`)**:
   Under monotone Cournot marginal revenue `ψ_m`, proves the diagonal tangent bound (eq. (9))
   and the generalized tangent bound (eq. (17)) relative to `t^S(q) = min q t0`, together with
   antitonicity of `q ↦ ψ_m(P(t^S(q) + (m - 1)q))`.
3. **Proposition 3 & Lemma B.1 (`prop3_quantity_path_rev`, `prop3_border_q`,
   `lemmaB1_rent_lower_bound`)**:
   Proves the quantity-path revenue representation, Border's feasibility bound in quantity
   coordinates, and Lemma B.1's covered-market rent lower bound (including the corner case
   `v_hat = 1` with `σ(1) > 0`).
4. **Theorem 1 (`theorem1_interior_pools_cournot`)**:
   Exact revenue difference for interior pools and nonpositivity under monotone `ψ_m` on
   the bands, for every `n ≥ 2`.
5. **Corollary 1 (`corollary1_smaller_seller`)**:
   Under `ψ_m` nondecreasing on `[max ρ a, 1]`, any Border-feasible path with `ℓ = 0` and
   `t0 ≤ q0` earns at most the reserve-increase path `t^S(q) = min q t0`.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace AuctionCompetition

/-! ### Section 1: Inverse Demand Construction and Basic Helpers -/

namespace Market

variable (M : Market)

private lemma exists_F_eq_one_sub {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    ∃ v ∈ Icc M.a 1, M.F v = 1 - z := by
  have h1z : 1 - z ∈ Icc (M.F M.a) (M.F 1) := by
    rw [M.hF_a, M.hF_1]
    exact ⟨by linarith [hz.2], by linarith [hz.1]⟩
  exact intermediate_value_Icc M.ha1.le M.F_continuousOn h1z

/-- Constructive (via classical choice) inverse demand `P : [0, 1] → [a, 1]` satisfying
`F (P z) = 1 - z`. -/
noncomputable def inverseDemandFun (z : ℝ) : ℝ :=
  if hz : z ∈ Icc (0 : ℝ) 1 then (M.exists_F_eq_one_sub hz).choose else M.a

private lemma inverseDemandFun_spec {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    M.inverseDemandFun z ∈ Icc M.a 1 ∧ M.F (M.inverseDemandFun z) = 1 - z := by
  simp only [inverseDemandFun, hz, ↓reduceDIte]
  exact (M.exists_F_eq_one_sub hz).choose_spec

private lemma inverseDemandFun_left {v : ℝ} (hv : v ∈ Icc M.a 1) :
    M.inverseDemandFun (1 - M.F v) = v := by
  have hmem : 1 - M.F v ∈ Icc (0 : ℝ) 1 := by
    have hFv := M.F_mem_Icc hv
    exact ⟨by linarith [hFv.2], by linarith [hFv.1]⟩
  have hspec := M.inverseDemandFun_spec hmem
  apply M.F_strictMonoOn.injOn hspec.1 hv
  linarith [hspec.2]

private lemma inverseDemandFun_strictAnti :
    StrictAntiOn M.inverseDemandFun (Icc (0 : ℝ) 1) := by
  intro z₁ hz₁ z₂ hz₂ hlt
  have h₁ := M.inverseDemandFun_spec hz₁
  have h₂ := M.inverseDemandFun_spec hz₂
  by_contra hle
  push Not at hle
  have hFle : M.F (M.inverseDemandFun z₁) ≤ M.F (M.inverseDemandFun z₂) :=
    M.F_strictMonoOn.monotoneOn h₁.1 h₂.1 hle
  linarith [h₁.2, h₂.2]

private lemma inverseDemandFun_continuousOn :
    ContinuousOn M.inverseDemandFun (Icc (0 : ℝ) 1) := by
  let e : Icc M.a 1 ≃ Icc (0 : ℝ) 1 :=
    { toFun := fun v => ⟨1 - M.F v.1, by
        have h := M.F_mem_Icc v.2
        exact ⟨by linarith [h.2], by linarith [h.1]⟩⟩
      invFun := fun z => ⟨M.inverseDemandFun z.1, (M.inverseDemandFun_spec z.2).1⟩
      left_inv := fun v => Subtype.ext (M.inverseDemandFun_left v.2)
      right_inv := fun z => Subtype.ext (by
        have h := (M.inverseDemandFun_spec z.2).2
        linarith) }
  have he_cont : Continuous e := by
    refine Continuous.subtype_mk ?_ _
    have hF_cont : Continuous (fun v : Icc M.a 1 => M.F v.1) :=
      continuousOn_iff_continuous_domRestrict.mp M.F_continuousOn
    exact continuous_const.sub hF_cont
  let hhomeo : Icc M.a 1 ≃ₜ Icc (0 : ℝ) 1 := he_cont.homeoOfEquivCompactToT2
  have hinv_cont : Continuous (fun z : Icc (0 : ℝ) 1 => M.inverseDemandFun z.1) := by
    have heq : (fun z : Icc (0 : ℝ) 1 => M.inverseDemandFun z.1) = Subtype.val ∘ hhomeo.symm := by
      ext z; rfl
    rw [heq]
    exact continuous_subtype_val.comp hhomeo.continuous_symm
  exact continuousOn_iff_continuous_domRestrict.mpr hinv_cont

private lemma inverseDemandFun_hasDerivWithinAt {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt M.inverseDemandFun (-1 / M.f (M.inverseDemandFun z)) (Icc (0 : ℝ) 1) z := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hspec := M.inverseDemandFun_spec hz
  have hf_pos : 0 < M.f (M.inverseDemandFun z) := M.hf_pos _ hspec.1
  have hf_ne : M.f (M.inverseDemandFun z) ≠ 0 := hf_pos.ne'
  have hF_slope :
      Tendsto (slope M.F (M.inverseDemandFun z))
        (𝓝[Icc M.a 1 \ {M.inverseDemandFun z}] M.inverseDemandFun z)
        (𝓝 (M.f (M.inverseDemandFun z))) :=
    (hasDerivWithinAt_iff_tendsto_slope.mp (M.hF_deriv_within _ hspec.1))
  have hP_tendsto :
      Tendsto M.inverseDemandFun (𝓝[Icc (0 : ℝ) 1 \ {z}] z)
        (𝓝[Icc M.a 1 \ {M.inverseDemandFun z}] M.inverseDemandFun z) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨(M.inverseDemandFun_continuousOn z hz).mono sdiff_subset, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with y hy
    refine ⟨(M.inverseDemandFun_spec hy.1).1, ?_⟩
    intro heq
    have hinj := M.inverseDemandFun_strictAnti.injOn hy.1 hz heq
    exact hy.2 hinj
  have hcomp :
      Tendsto (fun y => -((slope M.F (M.inverseDemandFun z) (M.inverseDemandFun y))⁻¹))
        (𝓝[Icc (0 : ℝ) 1 \ {z}] z) (𝓝 (-1 / M.f (M.inverseDemandFun z))) := by
    have h1 := (hF_slope.comp hP_tendsto).inv₀ hf_ne
    have h2 := h1.neg
    simpa [div_eq_mul_inv] using h2
  refine hcomp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hy_spec := M.inverseDemandFun_spec hy.1
  have hy_ne : y ≠ z := hy.2
  have hPy_ne : M.inverseDemandFun y ≠ M.inverseDemandFun z := fun h =>
    hy_ne (M.inverseDemandFun_strictAnti.injOn hy.1 hz h)
  simp only [slope_def_field]
  have hnum : M.F (M.inverseDemandFun y) - M.F (M.inverseDemandFun z) = -(y - z) := by
    linarith [hy_spec.2, hspec.2]
  rw [hnum]
  have hsub1 : y - z ≠ 0 := sub_ne_zero.mpr hy_ne
  have hsub2 : M.inverseDemandFun y - M.inverseDemandFun z ≠ 0 := sub_ne_zero.mpr hPy_ne
  field_simp [hsub1, hsub2]

/-- Explicit construction of `M.InverseDemand` for any `M : Market`. -/
noncomputable def inverseDemand : M.InverseDemand where
  P := M.inverseDemandFun
  hP_mem := fun _ hz => (M.inverseDemandFun_spec hz).1
  hP_right := fun _ hz => (M.inverseDemandFun_spec hz).2
  hP_left := fun _ hv => M.inverseDemandFun_left hv
  hP_zero := by
    have h := M.inverseDemandFun_left (right_mem_Icc.mpr M.ha1.le)
    rwa [M.hF_1, sub_self] at h
  hP_one := by
    have h := M.inverseDemandFun_left (left_mem_Icc.mpr M.ha1.le)
    rwa [M.hF_a, sub_zero] at h
  hP_cont := M.inverseDemandFun_continuousOn
  hP_strictAnti := M.inverseDemandFun_strictAnti
  hP_deriv_open := fun z hz =>
    (M.inverseDemandFun_hasDerivWithinAt (Ioo_subset_Icc_self hz)).hasDerivAt
      (Icc_mem_nhds hz.1 hz.2)
  hP_deriv_within := fun _ hz => M.inverseDemandFun_hasDerivWithinAt hz

/-- **Theorem (Inverse Demand Construction)**: Every market `M` admits an inverse demand
`P : M.InverseDemand` on `[0, 1]`. -/
theorem exists_inverseDemand : Nonempty M.InverseDemand :=
  ⟨M.inverseDemand⟩

/-- Continuity of `M.psi` on `[M.a, 1]`. -/
lemma psi_continuousOn : ContinuousOn M.psi (Icc M.a 1) := by
  unfold Market.psi
  refine continuousOn_id.sub ?_
  refine (continuousOn_const.sub M.F_continuousOn).div ?_ ?_
  · exact continuousOn_const.mul M.hf_cont
  · intro v hv
    exact mul_ne_zero M.m_pos_real.ne' (M.hf_pos v hv).ne'

/-- Nonnegativity of the weighting density `W(q) = n(n-1)(1-q)^(n-2)` on `q ≤ 1`. -/
lemma W_nonneg {q : ℝ} (hq : q ≤ 1) : 0 ≤ M.W q := by
  unfold Market.W
  have hn : (0 : ℝ) ≤ M.n := M.n_pos_real.le
  have hn1 : (0 : ℝ) ≤ (M.n : ℝ) - 1 := M.n_sub_one_pos_real.le
  have h1q : 0 ≤ 1 - q := by linarith
  positivity

/-- Continuity of `W`. -/
lemma W_continuous : Continuous M.W := by
  unfold Market.W
  fun_prop

/-- Algebraic identity expressing `ψ_m(P(z))` in inverse-demand coordinates:
`ψ_m(P(z)) = P(z) + (z / m) * (-1 / f(P(z)))`. -/
lemma psi_comp_P_eq (P : M.InverseDemand) {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    M.psi (P.P z) = P.P z + (z / (M.m : ℝ)) * (-1 / M.f (P.P z)) := by
  unfold Market.psi
  rw [P.hP_right z hz]
  have hm : (M.m : ℝ) ≠ 0 := M.m_pos_real.ne'
  have hf : M.f (P.P z) ≠ 0 := (M.hf_pos _ (P.hP_mem z hz)).ne'
  field_simp [hm, hf]
  ring

end Market

/-! ### Section 2: Concave Probability Scale `h_n`, Convexity Gap `η`, and Tangent Bounds -/

/-- Concave probability scale `h_n(u) = (1 - (1 - u)^n) / n` (Appendix B). -/
noncomputable def h_n (n : ℕ) (u : ℝ) : ℝ :=
  (1 - (1 - u) ^ n) / (n : ℝ)

/-- Nonnegative convexity gap `η = h_n(q0) - h_n(t0) + (1 - q0)^(n - 1) * (t0 - q0)`. -/
noncomputable def convexityGap (n : ℕ) (q0 t0 : ℝ) : ℝ :=
  h_n n q0 - h_n n t0 + (1 - q0) ^ (n - 1) * (t0 - q0)

lemma h_n_zero (n : ℕ) : h_n n 0 = 0 := by
  simp [h_n]

lemma hasDerivAt_h_n {n : ℕ} (hn : 1 ≤ n) (u : ℝ) :
    HasDerivAt (h_n n) ((1 - u) ^ (n - 1)) u := by
  unfold h_n
  have h1 : HasDerivAt (fun x : ℝ => 1 - x) (-1) u := by
    simpa using (hasDerivAt_const u (1 : ℝ)).fun_sub (hasDerivAt_id u)
  have h2 : HasDerivAt (fun x : ℝ => (1 - x) ^ n) ((n : ℝ) * (1 - u) ^ (n - 1) * (-1)) u :=
    h1.pow n
  have h3 : HasDerivAt (fun x : ℝ => 1 - (1 - x) ^ n) (0 - (n : ℝ) * (1 - u) ^ (n - 1) * (-1)) u :=
    (hasDerivAt_const u (1 : ℝ)).fun_sub h2
  have h4 := h3.div_const (n : ℝ)
  have hnR : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.pos_of_ne_zero (by omega)).ne'
  convert h4 using 1
  field_simp [hnR]
  ring

lemma h_n_sub_le_tangent {n : ℕ} (hn : 2 ≤ n) {u v : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    h_n n u - h_n n v ≤ (1 - v) ^ (n - 1) * (u - v) := by
  have hderiv : ∀ x ∈ uIcc v u, HasDerivAt (h_n n) ((1 - x) ^ (n - 1)) x :=
    fun x _ => hasDerivAt_h_n (by omega) x
  have hint : IntervalIntegrable (fun x : ℝ => (1 - x) ^ (n - 1)) volume v u :=
    (Continuous.intervalIntegrable (by fun_prop) v u)
  have hftc : ∫ x in v..u, (1 - x) ^ (n - 1) = h_n n u - h_n n v :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [← hftc]
  rcases le_total v u with hvu | huv
  · have hmono : ∀ x ∈ Icc v u, (1 - x) ^ (n - 1) ≤ (1 - v) ^ (n - 1) := by
      intro x hx
      exact pow_le_pow_left₀ (by linarith [hx.2, hu.2]) (by linarith [hx.1]) (n - 1)
    calc ∫ x in v..u, (1 - x) ^ (n - 1)
        ≤ ∫ _ in v..u, (1 - v) ^ (n - 1) := by
          apply intervalIntegral.integral_mono_on hvu hint intervalIntegrable_const
          exact hmono
      _ = (1 - v) ^ (n - 1) * (u - v) := by
          rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
  · rw [intervalIntegral.integral_symm]
    have hmono : ∀ x ∈ Icc u v, (1 - v) ^ (n - 1) ≤ (1 - x) ^ (n - 1) := by
      intro x hx
      exact pow_le_pow_left₀ (by linarith [hv.2]) (by linarith [hx.2]) (n - 1)
    have hge : (1 - v) ^ (n - 1) * (v - u) ≤ ∫ x in u..v, (1 - x) ^ (n - 1) := by
      calc (1 - v) ^ (n - 1) * (v - u)
          = ∫ _ in u..v, (1 - v) ^ (n - 1) := by
            rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
        _ ≤ ∫ x in u..v, (1 - x) ^ (n - 1) := by
            apply intervalIntegral.integral_mono_on huv intervalIntegrable_const hint.symm
            exact hmono
    linarith

lemma convexityGap_nonneg {n : ℕ} (hn : 2 ≤ n) {q0 t0 : ℝ}
    (hq0 : q0 ∈ Icc (0 : ℝ) 1) (ht0 : t0 ∈ Icc (0 : ℝ) 1) :
    0 ≤ convexityGap n q0 t0 := by
  unfold convexityGap
  have h := h_n_sub_le_tangent hn ht0 hq0
  linarith

lemma integral_u_mul_one_sub_pow {n : ℕ} (hn : 2 ≤ n) (q : ℝ) :
    ((n : ℝ) - 1) * ∫ u in (0 : ℝ)..q, u * (1 - u) ^ (n - 2) =
      h_n n q - q * (1 - q) ^ (n - 1) := by
  let G : ℝ → ℝ := fun x => h_n n x - x * (1 - x) ^ (n - 1)
  have hG_deriv : ∀ x, HasDerivAt G (((n : ℝ) - 1) * (x * (1 - x) ^ (n - 2))) x := by
    intro x
    have h1 := hasDerivAt_h_n (by omega : 1 ≤ n) x
    have h2 : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
      simpa using (hasDerivAt_const x (1 : ℝ)).fun_sub (hasDerivAt_id x)
    have h3 : HasDerivAt (fun y : ℝ => (1 - y) ^ (n - 1))
        (((n - 1 : ℕ) : ℝ) * (1 - x) ^ ((n - 1) - 1) * (-1)) x :=
      h2.pow (n - 1)
    have h4 : HasDerivAt (fun y : ℝ => y * (1 - y) ^ (n - 1))
        (1 * (1 - x) ^ (n - 1) + x * (((n - 1 : ℕ) : ℝ) * (1 - x) ^ ((n - 1) - 1) * (-1))) x :=
      (hasDerivAt_id x).fun_mul h3
    have h5 : HasDerivAt G
        ((1 - x) ^ (n - 1) -
          (1 * (1 - x) ^ (n - 1) + x * (((n - 1 : ℕ) : ℝ) * (1 - x) ^ ((n - 1) - 1) * (-1)))) x :=
      h1.fun_sub h4
    convert h5 using 1
    have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    have hn2 : (n - 1) - 1 = n - 2 := by omega
    rw [hn1, hn2]
    ring
  have hint : IntervalIntegrable (fun u : ℝ => ((n : ℝ) - 1) * (u * (1 - u) ^ (n - 2))) volume 0 q :=
    Continuous.intervalIntegrable (by fun_prop) 0 q
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hG_deriv x) hint
  rw [intervalIntegral.integral_const_mul] at hftc
  have hG0 : G 0 = 0 := by simp [G, h_n_zero]
  simpa [G, hG0] using hftc

/-- Partial derivative of Cournot revenue `s ↦ Π(s, q)` at `s` with `s + (m-1)q ∈ [0, 1]`. -/
lemma cournotRev_hasDerivWithinAt (M : Market) (P : M.InverseDemand) (q : ℝ)
    {s : ℝ} (hs : s + ((M.m : ℝ) - 1) * q ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (fun x => M.cournotRev P.P x q)
      (P.P (s + ((M.m : ℝ) - 1) * q) + s * (-1 / M.f (P.P (s + ((M.m : ℝ) - 1) * q))))
      {x : ℝ | x + ((M.m : ℝ) - 1) * q ∈ Icc (0 : ℝ) 1} s := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  let c : ℝ := ((M.m : ℝ) - 1) * q
  let S : Set ℝ := {x : ℝ | x + c ∈ Icc (0 : ℝ) 1}
  have hshift : Tendsto (fun x : ℝ => x + c) (𝓝[S \ {s}] s) (𝓝[Icc (0 : ℝ) 1 \ {s + c}] (s + c)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨((continuous_id.add continuous_const).continuousAt.continuousWithinAt), ?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact ⟨hx.1, fun h => hx.2 (add_right_cancel h)⟩
  have hP_cont : Tendsto (fun x : ℝ => P.P (x + c)) (𝓝[S \ {s}] s) (𝓝 (P.P (s + c))) :=
    Tendsto.comp ((P.hP_cont (s + c) hs).mono sdiff_subset).tendsto hshift
  have hP_slope : Tendsto (fun x : ℝ => slope P.P (s + c) (x + c))
      (𝓝[S \ {s}] s) (𝓝 (-1 / M.f (P.P (s + c)))) :=
    (hasDerivWithinAt_iff_tendsto_slope.mp (P.hP_deriv_within (s + c) hs)).comp hshift
  have hlim : Tendsto (fun x : ℝ => P.P (x + c) + s * slope P.P (s + c) (x + c))
      (𝓝[S \ {s}] s) (𝓝 (P.P (s + c) + s * (-1 / M.f (P.P (s + c))))) :=
    hP_cont.add (tendsto_const_nhds.mul hP_slope)
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hne : x - s ≠ 0 := sub_ne_zero.mpr hx.2
  simp only [slope_def_field, Market.cournotRev]
  have hsub : (x + c) - (s + c) = x - s := by ring
  rw [hsub]
  field_simp [hne]
  ring

/-- Key identity connecting partial derivative `∂_t Π(s, q)` to Cournot marginal revenue
`MR(z) = ψ_m(P(z))` at `z = s + (m - 1)q`:
`P(z) + s * (-1 / f(P(z))) = ψ_m(P(z)) + ((m - 1) / m) * (s - q) * (-1 / f(P(z)))`. -/
lemma cournotRev_deriv_eq_psi_add (M : Market) (P : M.InverseDemand) (s q : ℝ)
    (hz : s + ((M.m : ℝ) - 1) * q ∈ Icc (0 : ℝ) 1) :
    P.P (s + ((M.m : ℝ) - 1) * q) + s * (-1 / M.f (P.P (s + ((M.m : ℝ) - 1) * q))) =
      M.psi (P.P (s + ((M.m : ℝ) - 1) * q)) +
        (((M.m : ℝ) - 1) / (M.m : ℝ)) * (s - q) * (-1 / M.f (P.P (s + ((M.m : ℝ) - 1) * q))) := by
  rw [M.psi_comp_P_eq P hz]
  have hm : (M.m : ℝ) ≠ 0 := M.m_pos_real.ne'
  field_simp [hm]
  ring

/-- **Core Unified Tangent Bound (Appendix B, eq. (17))**:
Suppose `ψ_m` is nondecreasing on `[P(z_hi), P(z_lo)]` (so `z ↦ ψ_m(P(z))` is nonincreasing on
`[z_lo, z_hi] ⊆ [0, 1]`), and both `t + (m - 1)q` and `t' + (m - 1)q` lie in `[z_lo, z_hi]`.
If either `t' = q` or `t ≤ t' ≤ q`, then:
`Π(t, q) - Π(t', q) ≤ ψ_m(P(t' + (m - 1)q)) * (t - t')`. -/
theorem tangent_bound_eq17 (M : Market) (P : M.InverseDemand)
    {z_lo z_hi q t t' : ℝ}
    (hz_lo : 0 ≤ z_lo) (hz_hi : z_hi ≤ 1)
    (ht_mem : t + ((M.m : ℝ) - 1) * q ∈ Icc z_lo z_hi)
    (ht'_mem : t' + ((M.m : ℝ) - 1) * q ∈ Icc z_lo z_hi)
    (hpsi : MonotoneOn M.psi (Icc (P.P z_hi) (P.P z_lo)))
    (hcase : t' = q ∨ (t ≤ t' ∧ t' ≤ q)) :
    M.cournotRev P.P t q - M.cournotRev P.P t' q ≤
      M.psi (P.P (t' + ((M.m : ℝ) - 1) * q)) * (t - t') := by
  let S : Set ℝ := {x : ℝ | x + ((M.m : ℝ) - 1) * q ∈ Icc (0 : ℝ) 1}
  let g : ℝ → ℝ := fun x =>
    P.P (x + ((M.m : ℝ) - 1) * q) + x * (-1 / M.f (P.P (x + ((M.m : ℝ) - 1) * q)))
  have hmem_Icc : ∀ x ∈ uIcc t' t, x + ((M.m : ℝ) - 1) * q ∈ Icc z_lo z_hi := by
    intro x hx
    rcases le_total t' t with hle | hle
    · rw [uIcc_of_le hle] at hx
      exact ⟨by linarith [hx.1, ht'_mem.1], by linarith [hx.2, ht_mem.2]⟩
    · rw [uIcc_of_ge hle] at hx
      exact ⟨by linarith [hx.1, ht_mem.1], by linarith [hx.2, ht'_mem.2]⟩
  have hmem01 : ∀ x ∈ uIcc t' t, x + ((M.m : ℝ) - 1) * q ∈ Icc (0 : ℝ) 1 := fun x hx =>
    ⟨le_trans hz_lo (hmem_Icc x hx).1, le_trans (hmem_Icc x hx).2 hz_hi⟩
  have hsub : uIcc t' t ⊆ S := fun x hx => hmem01 x hx
  have hderiv : ∀ x ∈ uIcc t' t, HasDerivWithinAt (fun s => M.cournotRev P.P s q) (g x) (uIcc t' t) x :=
    fun x hx => (cournotRev_hasDerivWithinAt M P q (hmem01 x hx)).mono hsub
  have hg_cont : ContinuousOn g (uIcc t' t) := by
    have haff : ContinuousOn (fun x : ℝ => x + ((M.m : ℝ) - 1) * q) (uIcc t' t) :=
      continuousOn_id.add continuousOn_const
    have hP : ContinuousOn (fun x => P.P (x + ((M.m : ℝ) - 1) * q)) (uIcc t' t) :=
      P.hP_cont.comp haff (fun x hx => hmem01 x hx)
    have hf : ContinuousOn (fun x => M.f (P.P (x + ((M.m : ℝ) - 1) * q))) (uIcc t' t) :=
      M.hf_cont.comp hP (fun x hx => P.hP_mem _ (hmem01 x hx))
    refine hP.add (continuousOn_id.mul (continuousOn_const.div hf ?_))
    intro x hx
    exact (M.hf_pos _ (P.hP_mem _ (hmem01 x hx))).ne'
  have hint : IntervalIntegrable g volume t' t := hg_cont.intervalIntegrable
  have hMR_anti : AntitoneOn (fun z => M.psi (P.P z)) (Icc z_lo z_hi) := by
    intro z₁ hz₁ z₂ hz₂ hle
    have hz₁01 : z₁ ∈ Icc (0 : ℝ) 1 := ⟨le_trans hz_lo hz₁.1, le_trans hz₁.2 hz_hi⟩
    have hz₂01 : z₂ ∈ Icc (0 : ℝ) 1 := ⟨le_trans hz_lo hz₂.1, le_trans hz₂.2 hz_hi⟩
    have hz_lo01 : z_lo ∈ Icc (0 : ℝ) 1 := ⟨hz_lo, le_trans (le_trans hz₁.1 hz₁.2) hz_hi⟩
    have hz_hi01 : z_hi ∈ Icc (0 : ℝ) 1 := ⟨le_trans hz_lo (le_trans hz₁.1 hz₁.2), hz_hi⟩
    have hP_anti := P.hP_strictAnti.antitoneOn
    have hv₁ : P.P z₁ ∈ Icc (P.P z_hi) (P.P z_lo) :=
      ⟨hP_anti hz₁01 hz_hi01 hz₁.2, hP_anti hz_lo01 hz₁01 hz₁.1⟩
    have hv₂ : P.P z₂ ∈ Icc (P.P z_hi) (P.P z_lo) :=
      ⟨hP_anti hz₂01 hz_hi01 hz₂.2, hP_anti hz_lo01 hz₂01 hz₂.1⟩
    exact hpsi hv₂ hv₁ (hP_anti hz₁01 hz₂01 hle)
  have hftc_le : ∀ a b : ℝ, a ≤ b → uIcc a b = uIcc t' t →
      ∫ x in a..b, g x = M.cournotRev P.P b q - M.cournotRev P.P a q := by
    intro a b hab heq
    have hcont : ContinuousOn (fun s => M.cournotRev P.P s q) (Icc a b) := by
      intro x hx
      have hx' : x ∈ uIcc t' t := by rwa [← heq, uIcc_of_le hab]
      exact ((hderiv x hx').continuousWithinAt).mono (by rw [← heq, uIcc_of_le hab])
    have hder : ∀ x ∈ Ioo a b, HasDerivAt (fun s => M.cournotRev P.P s q) (g x) x := by
      intro x hx
      have hx' : x ∈ uIcc t' t := by rw [← heq, uIcc_of_le hab]; exact Ioo_subset_Icc_self hx
      have hnbhd : uIcc t' t ∈ 𝓝 x := by rw [← heq, uIcc_of_le hab]; exact Icc_mem_nhds hx.1 hx.2
      exact (hderiv x hx').hasDerivAt hnbhd
    have hint_ab : IntervalIntegrable g volume a b := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
      have : Icc a b = uIcc t' t := by rw [← heq, uIcc_of_le hab]
      rw [this]
      exact hg_cont.integrableOn_compact isCompact_uIcc
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont hder hint_ab
  have hm_frac_pos : 0 < ((M.m : ℝ) - 1) / (M.m : ℝ) :=
    div_pos M.m_sub_one_pos_real M.m_pos_real
  rcases lt_or_ge t' t with hlt | hle
  · -- Case `t' < t`: must have `t' = q`
    have hle : t' ≤ t := hlt.le
    have hftc : ∫ x in t'..t, g x = M.cournotRev P.P t q - M.cournotRev P.P t' q :=
      hftc_le t' t hle rfl
    rw [← hftc]
    have hbound : ∀ x ∈ Icc t' t, g x ≤ M.psi (P.P (t' + ((M.m : ℝ) - 1) * q)) := by
      intro x hx
      have hx_u : x ∈ uIcc t' t := by rwa [uIcc_of_le hle]
      have hx01 := hmem01 x hx_u
      have hx_z := hmem_Icc x hx_u
      have hgx : g x = M.psi (P.P (x + ((M.m : ℝ) - 1) * q)) +
          (((M.m : ℝ) - 1) / (M.m : ℝ)) * (x - q) * (-1 / M.f (P.P (x + ((M.m : ℝ) - 1) * q))) :=
        cournotRev_deriv_eq_psi_add M P x q hx01
      rw [hgx]
      have hMR_le : M.psi (P.P (x + ((M.m : ℝ) - 1) * q)) ≤
          M.psi (P.P (t' + ((M.m : ℝ) - 1) * q)) :=
        hMR_anti ht'_mem hx_z (by linarith [hx.1])
      have hterm_le : (((M.m : ℝ) - 1) / (M.m : ℝ)) * (x - q) *
          (-1 / M.f (P.P (x + ((M.m : ℝ) - 1) * q))) ≤ 0 := by
        rcases hcase with rfl | ⟨ht_le, _⟩
        · have hx_ge : 0 ≤ x - t' := by linarith [hx.1]
          have hf_pos : 0 < M.f (P.P (x + ((M.m : ℝ) - 1) * t')) := M.hf_pos _ (P.hP_mem _ hx01)
          have hneg : -1 / M.f (P.P (x + ((M.m : ℝ) - 1) * t')) ≤ 0 := by
            rw [div_nonpos_iff]; right; exact ⟨by norm_num, hf_pos.le⟩
          exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hm_frac_pos.le hx_ge) hneg
        · exfalso; linarith
      linarith
    calc ∫ x in t'..t, g x
        ≤ ∫ _ in t'..t, M.psi (P.P (t' + ((M.m : ℝ) - 1) * q)) :=
          intervalIntegral.integral_mono_on hle hint intervalIntegrable_const hbound
      _ = M.psi (P.P (t' + ((M.m : ℝ) - 1) * q)) * (t - t') := by
          rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
  · -- Case `t ≤ t'`: either `t' = q` or `t ≤ t' ≤ q`, so `x ≤ t' ≤ q` for all `x ∈ [t, t']`!
    have ht'_le_q : t' ≤ q := by
      rcases hcase with rfl | ⟨_, h2⟩
      · exact le_rfl
      · exact h2
    have hftc : ∫ x in t..t', g x = M.cournotRev P.P t' q - M.cournotRev P.P t q :=
      hftc_le t t' hle (uIcc_comm t t')
    have hbound : ∀ x ∈ Icc t t', M.psi (P.P (t' + ((M.m : ℝ) - 1) * q)) ≤ g x := by
      intro x hx
      have hx_u : x ∈ uIcc t' t := by rw [uIcc_of_ge hle]; exact hx
      have hx01 := hmem01 x hx_u
      have hx_z := hmem_Icc x hx_u
      have hgx : g x = M.psi (P.P (x + ((M.m : ℝ) - 1) * q)) +
          (((M.m : ℝ) - 1) / (M.m : ℝ)) * (x - q) * (-1 / M.f (P.P (x + ((M.m : ℝ) - 1) * q))) :=
        cournotRev_deriv_eq_psi_add M P x q hx01
      rw [hgx]
      have hMR_ge : M.psi (P.P (t' + ((M.m : ℝ) - 1) * q)) ≤
          M.psi (P.P (x + ((M.m : ℝ) - 1) * q)) :=
        hMR_anti hx_z ht'_mem (by linarith [hx.2])
      have hterm_ge : 0 ≤ (((M.m : ℝ) - 1) / (M.m : ℝ)) * (x - q) *
          (-1 / M.f (P.P (x + ((M.m : ℝ) - 1) * q))) := by
        have hx_le : x - q ≤ 0 := by linarith [hx.2, ht'_le_q]
        have hf_pos : 0 < M.f (P.P (x + ((M.m : ℝ) - 1) * q)) := M.hf_pos _ (P.hP_mem _ hx01)
        have hneg : -1 / M.f (P.P (x + ((M.m : ℝ) - 1) * q)) ≤ 0 := by
          rw [div_nonpos_iff]; right; exact ⟨by norm_num, hf_pos.le⟩
        exact mul_nonneg_of_nonpos_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hm_frac_pos.le hx_le) hneg
      linarith
    have hge : M.psi (P.P (t' + ((M.m : ℝ) - 1) * q)) * (t' - t) ≤ ∫ x in t..t', g x := by
      calc M.psi (P.P (t' + ((M.m : ℝ) - 1) * q)) * (t' - t)
          = ∫ _ in t..t', M.psi (P.P (t' + ((M.m : ℝ) - 1) * q)) := by
            rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
        _ ≤ ∫ x in t..t', g x :=
            intervalIntegral.integral_mono_on hle intervalIntegrable_const hint.symm hbound
    linarith

/-- **Diagonal Tangent Bound (Section 4.2, eq. (9))**:
If `ψ_m` is nondecreasing on `[P(z_hi), P(z_lo)]` and both `m * q` and `t + (m - 1) * q` lie
in `[z_lo, z_hi] ⊆ [0, 1]`, then
`Π(t, q) - Π(q, q) ≤ ψ_m(P(m * q)) * (t - q)`. -/
theorem tangent_bound_diag (M : Market) (P : M.InverseDemand)
    {z_lo z_hi q t : ℝ}
    (hz_lo : 0 ≤ z_lo) (hz_hi : z_hi ≤ 1)
    (ht_mem : t + ((M.m : ℝ) - 1) * q ∈ Icc z_lo z_hi)
    (hq_mem : (M.m : ℝ) * q ∈ Icc z_lo z_hi)
    (hpsi : MonotoneOn M.psi (Icc (P.P z_hi) (P.P z_lo))) :
    M.cournotRev P.P t q - M.cournotRev P.P q q ≤
      M.psi (P.P ((M.m : ℝ) * q)) * (t - q) := by
  have hmq : q + ((M.m : ℝ) - 1) * q = (M.m : ℝ) * q := by ring
  rw [← hmq] at hq_mem ⊢
  exact tangent_bound_eq17 M P hz_lo hz_hi ht_mem hq_mem hpsi (Or.inl rfl)

/-- **Generalized Tangent Bound (Appendix B, eq. (17) relative to `t^S(q) = min q t0`)**:
For `t ≤ t0` and `t^S(q) = min q t0`, if `ψ_m` is nondecreasing on `[P(z_hi), P(z_lo)]` and
both `t + (m - 1)q` and `t^S(q) + (m - 1)q` lie in `[z_lo, z_hi] ⊆ [0, 1]`, then
`Π(t, q) - Π(t^S(q), q) ≤ ψ_m(P(t^S(q) + (m - 1)q)) * (t - t^S(q))`. -/
theorem tangent_bound_general (M : Market) (P : M.InverseDemand)
    {z_lo z_hi t0 q t : ℝ}
    (hz_lo : 0 ≤ z_lo) (hz_hi : z_hi ≤ 1)
    (ht_le : t ≤ t0)
    (ht_mem : t + ((M.m : ℝ) - 1) * q ∈ Icc z_lo z_hi)
    (htS_mem : reserveIncreasePath t0 q + ((M.m : ℝ) - 1) * q ∈ Icc z_lo z_hi)
    (hpsi : MonotoneOn M.psi (Icc (P.P z_hi) (P.P z_lo))) :
    M.cournotRev P.P t q - M.cournotRev P.P (reserveIncreasePath t0 q) q ≤
      M.psi (P.P (reserveIncreasePath t0 q + ((M.m : ℝ) - 1) * q)) *
        (t - reserveIncreasePath t0 q) := by
  refine tangent_bound_eq17 M P hz_lo hz_hi ht_mem htS_mem hpsi ?_
  unfold reserveIncreasePath
  rcases le_total q t0 with hle | hle
  · left; exact min_eq_left hle
  · right; rw [min_eq_right hle]; exact ⟨ht_le, hle⟩

/-- Along the reserve-increase path `t^S(q) = min q t0`, the Cournot marginal revenue
`q ↦ ψ_m(P(t^S(q) + (m - 1)q))` is nonincreasing on `[0, q0]` whenever `ψ_m` is
nondecreasing on `[P(t0 + (m - 1)q0), 1]`. -/
theorem antitoneOn_psi_reserveIncrease (M : Market) (P : M.InverseDemand)
    {q0 t0 : ℝ} (ht0 : 0 ≤ t0) (ht0_le : t0 ≤ q0)
    (hz_le : t0 + ((M.m : ℝ) - 1) * q0 ≤ 1)
    (hpsi : MonotoneOn M.psi (Icc (P.P (t0 + ((M.m : ℝ) - 1) * q0)) 1)) :
    AntitoneOn (fun q => M.psi (P.P (reserveIncreasePath t0 q + ((M.m : ℝ) - 1) * q)))
      (Icc (0 : ℝ) q0) := by
  intro q₁ hq₁ q₂ hq₂ hle
  have hm1 : (0 : ℝ) < (M.m : ℝ) - 1 := M.m_sub_one_pos_real
  have hz1 : reserveIncreasePath t0 q₁ + ((M.m : ℝ) - 1) * q₁ ∈
      Icc (0 : ℝ) (t0 + ((M.m : ℝ) - 1) * q0) := by
    unfold reserveIncreasePath
    constructor
    · have : 0 ≤ min q₁ t0 := le_min hq₁.1 ht0
      nlinarith [hq₁.1]
    · have : min q₁ t0 ≤ t0 := min_le_right _ _
      nlinarith [hq₁.2]
  have hz2 : reserveIncreasePath t0 q₂ + ((M.m : ℝ) - 1) * q₂ ∈
      Icc (0 : ℝ) (t0 + ((M.m : ℝ) - 1) * q0) := by
    unfold reserveIncreasePath
    constructor
    · have : 0 ≤ min q₂ t0 := le_min hq₂.1 ht0
      nlinarith [hq₂.1]
    · have : min q₂ t0 ≤ t0 := min_le_right _ _
      nlinarith [hq₂.2]
  have hz1_01 : reserveIncreasePath t0 q₁ + ((M.m : ℝ) - 1) * q₁ ∈ Icc (0 : ℝ) 1 :=
    ⟨hz1.1, le_trans hz1.2 hz_le⟩
  have hz2_01 : reserveIncreasePath t0 q₂ + ((M.m : ℝ) - 1) * q₂ ∈ Icc (0 : ℝ) 1 :=
    ⟨hz2.1, le_trans hz2.2 hz_le⟩
  have hmax_01 : t0 + ((M.m : ℝ) - 1) * q0 ∈ Icc (0 : ℝ) 1 :=
    ⟨by nlinarith [ht0, ht0_le], hz_le⟩
  have hP_anti := P.hP_strictAnti.antitoneOn
  have hv1 : P.P (reserveIncreasePath t0 q₁ + ((M.m : ℝ) - 1) * q₁) ∈
      Icc (P.P (t0 + ((M.m : ℝ) - 1) * q0)) 1 :=
    ⟨hP_anti hz1_01 hmax_01 hz1.2, (P.hP_mem _ hz1_01).2⟩
  have hv2 : P.P (reserveIncreasePath t0 q₂ + ((M.m : ℝ) - 1) * q₂) ∈
      Icc (P.P (t0 + ((M.m : ℝ) - 1) * q0)) 1 :=
    ⟨hP_anti hz2_01 hmax_01 hz2.2, (P.hP_mem _ hz2_01).2⟩
  have hz_ord : reserveIncreasePath t0 q₁ + ((M.m : ℝ) - 1) * q₁ ≤
      reserveIncreasePath t0 q₂ + ((M.m : ℝ) - 1) * q₂ := by
    unfold reserveIncreasePath
    have hmin : min q₁ t0 ≤ min q₂ t0 := min_le_min_right t0 hle
    nlinarith
  exact hpsi hv2 hv1 (hP_anti hz1_01 hz2_01 hz_ord)

/-! ### Section 3: Monotone Integration by Parts and Measure-Theoretic Tools -/

/-- **Monotone Integration-by-Parts Inequality (Second Mean Value / Stieltjes IBP)**:
If `g` is antitone on `[a, b]` (`a ≤ b`), `φ` and `g * φ` are interval-integrable on `[a, b]`,
and every partial integral `∫ u in a..x, φ u ≤ 0` for `x ∈ [a, b]`, then
`∫ x in a..b, g x * φ x ≤ g b * ∫ u in a..b, φ u`.

No differentiability or continuity of `g` is required. -/
theorem integral_antitone_mul_le {a b : ℝ} (hab : a ≤ b)
    {g φ : ℝ → ℝ}
    (hg_anti : AntitoneOn g (Icc a b))
    (hφ_int : IntervalIntegrable φ volume a b)
    (hgφ_int : IntervalIntegrable (fun x => g x * φ x) volume a b)
    (hE : ∀ x ∈ Icc a b, ∫ u in a..x, φ u ≤ 0) :
    ∫ x in a..b, g x * φ x ≤ g b * ∫ u in a..b, φ u := by
  let h : ℝ → ℝ := fun x => g x - g b
  have hh_anti : AntitoneOn h (Icc a b) := fun x hx y hy hxy =>
    sub_le_sub_right (hg_anti hx hy hxy) (g b)
  have hh_nonneg : ∀ x ∈ Icc a b, 0 ≤ h x := fun x hx =>
    sub_nonneg.mpr (hg_anti hx (right_mem_Icc.mpr hab) hx.2)
  have hh_le : ∀ x ∈ Icc a b, h x ≤ h a := fun x hx =>
    hh_anti (left_mem_Icc.mpr hab) hx hx.1
  have hhφ_int : IntervalIntegrable (fun x => h x * φ x) volume a b := by
    have h1 : (fun x => h x * φ x) = fun x => g x * φ x - g b * φ x := by
      ext x; simp [h, sub_mul]
    rw [h1]
    exact hgφ_int.sub (hφ_int.const_mul (g b))
  have hsub_eq : ∫ x in a..b, h x * φ x =
      (∫ x in a..b, g x * φ x) - g b * ∫ u in a..b, φ u := by
    have h1 : (fun x => h x * φ x) = fun x => g x * φ x - g b * φ x := by
      ext x; simp [h, sub_mul]
    rw [h1, intervalIntegral.integral_sub hgφ_int (hφ_int.const_mul (g b)),
      intervalIntegral.integral_const_mul]
  suffices hgoal : ∫ x in a..b, h x * φ x ≤ 0 by linarith
  have hha_nn : 0 ≤ h a := hh_nonneg a (left_mem_Icc.mpr hab)
  rcases eq_or_lt_of_le hha_nn with hha0 | hha_pos
  · have hzero : EqOn (fun x => h x * φ x) 0 (Ioc a b) := by
      intro x hx
      have hx' : x ∈ Icc a b := Ioc_subset_Icc_self hx
      have hhx : h x = 0 := le_antisymm (by linarith [hh_le x hx']) (hh_nonneg x hx')
      simp [hhx]
    rw [intervalIntegral.integral_of_le hab, setIntegral_congr_fun measurableSet_Ioc hzero]
    simp
  · -- Show `∫ h * φ ≤ (h a / N) * ∫ |φ|` for every `N ≥ 1`
    have hbound_N : ∀ N : ℕ, 0 < N →
        ∫ x in a..b, h x * φ x ≤ (h a / (N : ℝ)) * ∫ x in a..b, |φ x| := by
      intro N hN
      have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
      let δ : ℝ := h a / (N : ℝ)
      have hδ_pos : 0 < δ := div_pos hha_pos hNR
      let S : ℕ → Set ℝ := fun k => {x ∈ Icc a b | (k : ℝ) * δ ≤ h x}
      let c : ℕ → ℝ := fun k => sSup (S k)
      have hc_mem : ∀ k ∈ Finset.Icc 1 N, c k ∈ Icc a b := by
        intro k hk
        rw [Finset.mem_Icc] at hk
        have haS : a ∈ S k := by
          refine ⟨left_mem_Icc.mpr hab, ?_⟩
          have hkN : (k : ℝ) ≤ N := Nat.cast_le.mpr hk.2
          have : (k : ℝ) * δ ≤ (N : ℝ) * δ := mul_le_mul_of_nonneg_right hkN hδ_pos.le
          have hNδ : (N : ℝ) * δ = h a := mul_div_cancel₀ (h a) hNR.ne'
          linarith
        have hbdd : BddAbove (S k) := ⟨b, fun x hx => hx.1.2⟩
        exact ⟨le_csSup hbdd haS, csSup_le ⟨a, haS⟩ (fun x hx => hx.1.2)⟩
      let ind : ℝ → ℝ → ℝ := fun t x => if x ≤ t then 1 else 0
      have hind_int : ∀ t ∈ Icc a b,
          IntervalIntegrable (fun x => ind t x * φ x) volume a b ∧
          ∫ x in a..b, ind t x * φ x = ∫ u in a..t, φ u := by
        intro t ht
        have h1_eq : EqOn (fun x => ind t x * φ x) φ (Ioc a t) := by
          intro x hx; simp [ind, hx.2]
        have h2_eq : EqOn (fun x => ind t x * φ x) 0 (Ioc t b) := by
          intro x hx; simp [ind, not_le.mpr hx.1]
        have hint1 : IntervalIntegrable (fun x => ind t x * φ x) volume a t := by
          rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1]
          exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).mp
            (hφ_int.mono_set (uIcc_subset_uIcc_left (mem_uIcc_of_le ht.1 ht.2)))).congr_fun
            (fun x hx => (h1_eq hx).symm) measurableSet_Ioc
        have hint2 : IntervalIntegrable (fun x => ind t x * φ x) volume t b := by
          rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.2]
          exact (integrableOn_zero : IntegrableOn (0 : ℝ → ℝ) (Ioc t b)).congr_fun
            (fun x hx => (h2_eq hx).symm) measurableSet_Ioc
        refine ⟨hint1.trans hint2, ?_⟩
        rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
        have hi1 : ∫ x in a..t, ind t x * φ x = ∫ x in a..t, φ x := by
          rw [intervalIntegral.integral_of_le ht.1, intervalIntegral.integral_of_le ht.1]
          exact setIntegral_congr_fun measurableSet_Ioc h1_eq
        have hi2 : ∫ x in t..b, ind t x * φ x = 0 := by
          rw [intervalIntegral.integral_of_le ht.2]
          rw [setIntegral_congr_fun measurableSet_Ioc h2_eq]
          simp
        linarith
      let hNfun : ℝ → ℝ := fun x => δ * ∑ k ∈ Finset.Icc 1 N, ind (c k) x
      have hsum_int : ∀ (s : Finset ℕ), (∀ k ∈ s, c k ∈ Icc a b) →
          IntervalIntegrable (fun x => ∑ k ∈ s, ind (c k) x * φ x) volume a b ∧
          ∫ x in a..b, (∑ k ∈ s, ind (c k) x * φ x) = ∑ k ∈ s, ∫ x in a..b, ind (c k) x * φ x := by
        intro s
        classical
        refine Finset.induction_on s ?_ ?_
        · intro _
          exact ⟨by simp, by simp⟩
        · intro k s hks ih hmem
          have hk := hind_int (c k) (hmem k (Finset.mem_insert_self k s))
          have hs := ih (fun j hj => hmem j (Finset.mem_insert_of_mem hj))
          have hfun : (fun x => ∑ j ∈ insert k s, ind (c j) x * φ x) =
              fun x => ind (c k) x * φ x + ∑ j ∈ s, ind (c j) x * φ x := by
            ext x; exact Finset.sum_insert hks
          rw [hfun, Finset.sum_insert hks]
          refine ⟨hk.1.add hs.1, ?_⟩
          rw [intervalIntegral.integral_add hk.1 hs.1, hs.2]
      have hhN_int : IntervalIntegrable (fun x => hNfun x * φ x) volume a b := by
        have heq : (fun x => hNfun x * φ x) =
            fun x => δ * ∑ k ∈ Finset.Icc 1 N, ind (c k) x * φ x := by
          ext x; simp [hNfun, Finset.sum_mul, mul_assoc]
        rw [heq]
        exact (hsum_int (Finset.Icc 1 N) hc_mem).1.const_mul δ
      have hhN_nonpos : ∫ x in a..b, hNfun x * φ x ≤ 0 := by
        have heq : (fun x => hNfun x * φ x) =
            fun x => δ * ∑ k ∈ Finset.Icc 1 N, ind (c k) x * φ x := by
          ext x; simp [hNfun, Finset.sum_mul, mul_assoc]
        rw [heq, intervalIntegral.integral_const_mul, (hsum_int (Finset.Icc 1 N) hc_mem).2]
        refine mul_nonpos_of_nonneg_of_nonpos hδ_pos.le ?_
        exact Finset.sum_nonpos (fun k hk => by
          rw [(hind_int (c k) (hc_mem k hk)).2]
          exact hE (c k) (hc_mem k hk))
      -- Bound `(h x - hNfun x) * φ x ≤ δ * |φ x|` outside the finite set `bad = c '' (Icc 1 N)`
      let bad : Set ℝ := ↑((Finset.Icc 1 N).image c)
      have hbad_null : volume bad = 0 := Set.Finite.measure_zero (Finset.finite_toSet _) volume
      have hae : ∀ᵐ x ∂(volume.restrict (Ioc a b)), (h x - hNfun x) * φ x ≤ δ * |φ x| := by
        have hnotbad : ∀ᵐ x ∂(volume.restrict (Ioc a b)), x ∉ bad := by
          rw [ae_restrict_iff' measurableSet_Ioc]
          have hmem : ∀ᵐ x ∂volume, x ∉ bad := by
            rw [ae_iff]; simpa using hbad_null
          filter_upwards [hmem] with x hx _ using hx
        filter_upwards [ae_restrict_mem measurableSet_Ioc, hnotbad] with x hx hxb
        have hxIcc : x ∈ Icc a b := Ioc_subset_Icc_self hx
        have hxne : ∀ k ∈ Finset.Icc 1 N, x ≠ c k := by
          intro k hk heq
          apply hxb
          simp only [bad, Finset.coe_image, mem_image, Finset.mem_coe]
          exact ⟨k, hk, heq.symm⟩
        let m : ℕ := Nat.floor (h x / δ)
        have hratio_nn : 0 ≤ h x / δ := div_nonneg (hh_nonneg x hxIcc) hδ_pos.le
        have hratio_le : h x / δ ≤ N := by
          rw [div_le_iff₀ hδ_pos]
          have hNδ : (N : ℝ) * δ = h a := mul_div_cancel₀ (h a) hNR.ne'
          linarith [hh_le x hxIcc]
        have hm_le_N : m ≤ N := Nat.floor_le_of_le hratio_le
        have hm_mul_le : (m : ℝ) * δ ≤ h x := by
          have := Nat.floor_le hratio_nn
          rwa [le_div_iff₀ hδ_pos] at this
        have hhx_lt : h x < ((m : ℝ) + 1) * δ := by
          have := Nat.lt_floor_add_one (h x / δ)
          rwa [div_lt_iff₀ hδ_pos] at this
        have hiff : ∀ k ∈ Finset.Icc 1 N, x ≤ c k ↔ k ≤ m := by
          intro k hk
          have hne := hxne k hk
          constructor
          · intro hle
            have hlt : x < c k := lt_of_le_of_ne hle hne
            have hneS : (S k).Nonempty := by
              rw [Finset.mem_Icc] at hk
              refine ⟨a, left_mem_Icc.mpr hab, ?_⟩
              have hkN : (k : ℝ) ≤ N := Nat.cast_le.mpr hk.2
              have : (k : ℝ) * δ ≤ (N : ℝ) * δ := mul_le_mul_of_nonneg_right hkN hδ_pos.le
              have hNδ : (N : ℝ) * δ = h a := mul_div_cancel₀ (h a) hNR.ne'
              linarith
            have hbdd : BddAbove (S k) := ⟨b, fun y hy => hy.1.2⟩
            obtain ⟨y, hyS, hxy⟩ := (lt_csSup_iff hbdd hneS).mp hlt
            have hky : (k : ℝ) * δ ≤ h x := le_trans hyS.2 (hh_anti hxIcc hyS.1 hxy.le)
            have hk_le : (k : ℝ) ≤ h x / δ := (le_div_iff₀ hδ_pos).mpr hky
            exact Nat.le_floor hk_le
          · intro hkm
            have hkx : (k : ℝ) * δ ≤ h x := le_trans
              (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hkm) hδ_pos.le) hm_mul_le
            have hbdd : BddAbove (S k) := ⟨b, fun y hy => hy.1.2⟩
            exact le_csSup hbdd ⟨hxIcc, hkx⟩
        have hsum_eq : ∑ k ∈ Finset.Icc 1 N, ind (c k) x = (m : ℝ) := by
          have h1 : ∑ k ∈ Finset.Icc 1 N, ind (c k) x =
              ∑ k ∈ Finset.Icc 1 N, if k ≤ m then (1 : ℝ) else 0 := by
            refine Finset.sum_congr rfl (fun k hk => ?_)
            simp [ind, hiff k hk]
          rw [h1, Finset.sum_boole]
          have hfilt : (Finset.Icc 1 N).filter (fun k => k ≤ m) = Finset.Icc 1 m := by
            ext k
            simp only [Finset.mem_filter, Finset.mem_Icc]
            omega
          rw [hfilt, Nat.card_Icc]
          simp
        have hhN_eq : hNfun x = (m : ℝ) * δ := by
          simp only [hNfun, hsum_eq]; ring
        have hdiff_nn : 0 ≤ h x - hNfun x := by linarith
        have hdiff_le : h x - hNfun x ≤ δ := by linarith
        calc (h x - hNfun x) * φ x
            ≤ (h x - hNfun x) * |φ x| := mul_le_mul_of_nonneg_left (le_abs_self _) hdiff_nn
          _ ≤ δ * |φ x| := mul_le_mul_of_nonneg_right hdiff_le (abs_nonneg _)
      have hdiff_int : ∫ x in a..b, (h x - hNfun x) * φ x ≤ δ * ∫ x in a..b, |φ x| := by
        have hint_lhs : IntervalIntegrable (fun x => (h x - hNfun x) * φ x) volume a b := by
          have heq : (fun x => (h x - hNfun x) * φ x) = fun x => h x * φ x - hNfun x * φ x := by
            ext x; ring
          rw [heq]; exact hhφ_int.sub hhN_int
        have hint_rhs : IntervalIntegrable (fun x => δ * |φ x|) volume a b :=
          hφ_int.abs.const_mul δ
        rw [← intervalIntegral.integral_const_mul]
        rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
        exact integral_mono_ae
          ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hint_lhs)
          ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hint_rhs) hae
      have hsplit : ∫ x in a..b, (h x - hNfun x) * φ x =
          (∫ x in a..b, h x * φ x) - ∫ x in a..b, hNfun x * φ x := by
        have heq : (fun x => (h x - hNfun x) * φ x) = fun x => h x * φ x - hNfun x * φ x := by
          ext x; ring
        rw [heq, intervalIntegral.integral_sub hhφ_int hhN_int]
      linarith
    by_contra hpos
    push Not at hpos
    let I := ∫ x in a..b, h x * φ x
    let C := ∫ x in a..b, |φ x|
    have hC_nn : 0 ≤ C :=
      intervalIntegral.integral_nonneg hab (fun x _ => abs_nonneg (φ x))
    rcases eq_or_lt_of_le hC_nn with hC0 | hC_pos
    · have h1 := hbound_N 1 Nat.one_pos
      change I ≤ h a / (1 : ℕ) * C at h1
      rw [← hC0, mul_zero] at h1
      linarith
    · obtain ⟨N, hN⟩ := exists_nat_gt (h a * C / I)
      have hNpos : 0 < N := by
        have : (0 : ℝ) < h a * C / I := div_pos (mul_pos hha_pos hC_pos) hpos
        exact Nat.cast_pos.mp (lt_trans this hN)
      have hNR : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hNpos
      have h1 := hbound_N N hNpos
      change I ≤ h a / (N : ℝ) * C at h1
      have h2 : h a * C < (N : ℝ) * I := by
        have := (div_lt_iff₀ hpos).mp hN
        linarith
      have h3 : (N : ℝ) * I ≤ h a * C := by
        have h1' : I ≤ h a * C / (N : ℝ) := by convert h1 using 1; ring
        have := (le_div_iff₀ hNR).mp h1'
        linarith
      linarith

/-- Triangle Fubini swap on `[a, b]`:
`∫ x in a..b, (∫ t in a..x, f t) * g x = ∫ t in a..b, f t * (∫ x in t..b, g x)`. -/
lemma integral_integral_mul_swap {a b : ℝ} (hab : a ≤ b)
    {f g : ℝ → ℝ} (hf : IntegrableOn f (Icc a b)) (hg : IntegrableOn g (Icc a b)) :
    ∫ x in a..b, (∫ t in a..x, f t) * g x = ∫ t in a..b, f t * (∫ x in t..b, g x) := by
  let μ := volume.restrict (Icc a b)
  let S : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.1 ≤ p.2}
  let K : ℝ → ℝ → ℝ := fun t x => S.indicator (fun p : ℝ × ℝ => f p.1 * g p.2) (t, x)
  have hS_meas : MeasurableSet S := (isClosed_le continuous_fst continuous_snd).measurableSet
  have hprod : Integrable (fun p : ℝ × ℝ => f p.1 * g p.2) (μ.prod μ) := hf.mul_prod hg
  have hK_int : Integrable (Function.uncurry K) (μ.prod μ) := by
    have heq : Function.uncurry K = S.indicator (fun p : ℝ × ℝ => f p.1 * g p.2) := by
      ext ⟨t, x⟩; rfl
    rw [heq]
    exact hprod.indicator hS_meas
  have hswap := MeasureTheory.integral_integral_swap hK_int
  have hlhs : ∫ t in Icc a b, ∫ x in Icc a b, K t x =
      ∫ t in a..b, f t * (∫ x in t..b, g x) := by
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
    refine setIntegral_congr_fun measurableSet_Icc (fun t ht => ?_)
    have heq : (fun x => K t x) = (Ici t).indicator (fun x => f t * g x) := by
      ext x; simp [K, S, Set.indicator]
    rw [heq, setIntegral_indicator measurableSet_Ici]
    have hinter : Icc a b ∩ Ici t = Icc t b := by
      ext x; simp only [mem_inter_iff, mem_Ici, mem_Icc]
      exact ⟨fun ⟨⟨_, h3⟩, h1⟩ => ⟨h1, h3⟩, fun ⟨h1, h2⟩ => ⟨⟨le_trans ht.1 h1, h2⟩, h1⟩⟩
    rw [hinter, integral_const_mul, intervalIntegral.integral_of_le ht.2, integral_Icc_eq_integral_Ioc]
  have hrhs : ∫ x in Icc a b, ∫ t in Icc a b, K t x =
      ∫ x in a..b, (∫ t in a..x, f t) * g x := by
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
    refine setIntegral_congr_fun measurableSet_Icc (fun x hx => ?_)
    have heq : (fun t => K t x) = (Iic x).indicator (fun t => f t * g x) := by
      ext t; simp [K, S, Set.indicator]
    rw [heq, setIntegral_indicator measurableSet_Iic]
    have hinter : Icc a b ∩ Iic x = Icc a x := by
      ext t; simp only [mem_inter_iff, mem_Iic, mem_Icc]
      exact ⟨fun ⟨⟨h2, _⟩, h1⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨⟨h1, le_trans h2 hx.2⟩, h2⟩⟩
    rw [hinter, integral_mul_const, intervalIntegral.integral_of_le hx.1, integral_Icc_eq_integral_Ioc]
  linarith

/-- Pushforward of the density measure `w(v) dv` on `[a, b]` by the upper-tail primitive
`q(v) = ∫ u in v..b, w u` is Lebesgue measure restricted to `[0, q(a)]`. -/
lemma map_antitone_primitive {a b : ℝ} (hab : a ≤ b)
    {w : ℝ → ℝ} (hw_int : IntegrableOn w (Icc a b)) (hw_nn : ∀ v ∈ Icc a b, 0 ≤ w v) :
    Measure.map (fun v => ∫ u in v..b, w u)
      ((volume.restrict (Icc a b)).withDensity (fun v => ENNReal.ofReal (w v))) =
    volume.restrict (Icc (0 : ℝ) (∫ u in a..b, w u)) := by
  let q : ℝ → ℝ := fun v => ∫ u in v..b, w u
  let μ := (volume.restrict (Icc a b)).withDensity (fun v => ENNReal.ofReal (w v))
  let ν := volume.restrict (Icc (0 : ℝ) (q a))
  have hw_uIcc : IntegrableOn w (uIcc a b) volume := by rwa [uIcc_of_le hab]
  have hw_ivl : IntervalIntegrable w volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hw_int
  have hq_cont : ContinuousOn q (Icc a b) := by
    have h := intervalIntegral.continuousOn_primitive_interval_left hw_uIcc
    rwa [uIcc_of_le hab] at h
  have hq_anti : AntitoneOn q (Icc a b) := by
    intro v₁ hv₁ v₂ hv₂ hle
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hw_ivl.mono_set (uIcc_subset_uIcc (mem_uIcc_of_le hv₁.1 hv₁.2) (mem_uIcc_of_le hv₂.1 hv₂.2)))
      (hw_ivl.mono_set (uIcc_subset_uIcc (mem_uIcc_of_le hv₂.1 hv₂.2) (right_mem_uIcc)))
    have hnn : 0 ≤ ∫ u in v₁..v₂, w u :=
      intervalIntegral.integral_nonneg hle (fun u hu => hw_nn u ⟨le_trans hv₁.1 hu.1, le_trans hu.2 hv₂.2⟩)
    show ∫ u in v₂..b, w u ≤ ∫ u in v₁..b, w u
    linarith
  have hq_b : q b = 0 := intervalIntegral.integral_same
  have hq_a_nn : 0 ≤ q a :=
    intervalIntegral.integral_nonneg hab (fun u hu => hw_nn u hu)
  have hq_mem : ∀ v ∈ Icc a b, q v ∈ Icc (0 : ℝ) (q a) := fun v hv =>
    ⟨by rw [← hq_b]; exact hq_anti hv (right_mem_Icc.mpr hab) hv.2,
     hq_anti (left_mem_Icc.mpr hab) hv hv.1⟩
  have hq_aemeas : AEMeasurable q μ := by
    have hmeas : AEMeasurable q (volume.restrict (Icc a b)) :=
      hq_cont.aemeasurable measurableSet_Icc
    exact hmeas.mono_ac (withDensity_absolutelyContinuous _ _)
  have hμ_fin : IsFiniteMeasure μ := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    have hle : ∫⁻ v in Icc a b, ENNReal.ofReal (w v) ≤ ∫⁻ v in Icc a b, ‖w v‖ₑ := by
      refine lintegral_mono (fun v => ?_)
      rw [← ofReal_norm, Real.norm_eq_abs]
      exact ENNReal.ofReal_le_ofReal (le_abs_self (w v))
    exact lt_of_le_of_lt hle hw_int.2
  have : IsFiniteMeasure (Measure.map q μ) := Measure.isFiniteMeasure_map μ q
  have : IsFiniteMeasure ν := ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
  have hμ_Icc : ∀ v ∈ Icc a b, μ (Icc v b) = ENNReal.ofReal (q v) := by
    intro v hv
    rw [withDensity_apply _ measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc]
    have hinter : Icc v b ∩ Icc a b = Icc v b :=
      inter_eq_left.mpr (Icc_subset_Icc_left hv.1)
    rw [hinter]
    have hv_int : IntegrableOn w (Icc v b) := hw_int.mono_set (Icc_subset_Icc_left hv.1)
    rw [← ofReal_integral_eq_lintegral_ofReal hv_int
      (ae_restrict_of_forall_mem measurableSet_Icc (fun u hu => hw_nn u ⟨le_trans hv.1 hu.1, hu.2⟩))]
    dsimp only [q]
    rw [intervalIntegral.integral_of_le hv.2, integral_Icc_eq_integral_Ioc]
  have hμ_compl : μ (Icc a b)ᶜ = 0 := by
    rw [withDensity_apply _ measurableSet_Icc.compl, Measure.restrict_restrict measurableSet_Icc.compl]
    simp
  have hμ_inter : ∀ s : Set ℝ, μ s = μ (s ∩ Icc a b) := by
    intro s
    apply le_antisymm
    · calc μ s ≤ μ ((s ∩ Icc a b) ∪ (Icc a b)ᶜ) := measure_mono (fun x hx => by
            by_cases h : x ∈ Icc a b
            · exact Or.inl ⟨hx, h⟩
            · exact Or.inr h)
        _ ≤ μ (s ∩ Icc a b) + μ (Icc a b)ᶜ := measure_union_le _ _
        _ = μ (s ∩ Icc a b) := by rw [hμ_compl, add_zero]
    · exact measure_mono inter_subset_left
  apply Measure.ext_of_Iic
  intro c
  rw [Measure.map_apply_of_aemeasurable hq_aemeas measurableSet_Iic, hμ_inter]
  rcases lt_or_ge c 0 with hc0 | hc0
  · have hemp : q ⁻¹' Iic c ∩ Icc a b = ∅ := by
      ext v; simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_empty_iff_false, iff_false, not_and]
      intro hle hv
      linarith [(hq_mem v hv).1]
    have hemp2 : Iic c ∩ Icc (0 : ℝ) (q a) = ∅ := by
      ext x
      simp only [mem_inter_iff, mem_Iic, mem_Icc, mem_empty_iff_false, iff_false, not_and]
      intro h1 h2; linarith
    rw [hemp, measure_empty, Measure.restrict_apply measurableSet_Iic, hemp2, measure_empty]
  · rcases le_or_gt (q a) c with hca | hca
    · have hfull : q ⁻¹' Iic c ∩ Icc a b = Icc a b := by
        ext v; simp only [mem_inter_iff, mem_preimage, mem_Iic, and_iff_right_iff_imp]
        intro hv; exact le_trans (hq_mem v hv).2 hca
      have hfull2 : Iic c ∩ Icc (0 : ℝ) (q a) = Icc (0 : ℝ) (q a) := by
        ext x; simp only [mem_inter_iff, mem_Iic, mem_Icc, and_iff_right_iff_imp]
        intro hx; exact le_trans hx.2 hca
      rw [hfull, hμ_Icc a (left_mem_Icc.mpr hab), Measure.restrict_apply measurableSet_Iic,
        hfull2, Real.volume_Icc, sub_zero]
    · -- `0 ≤ c < q a`: let `v_c := sInf {v ∈ Icc a b | q v ≤ c}`
      let T : Set ℝ := {v ∈ Icc a b | q v ≤ c}
      have hbT : b ∈ T := ⟨right_mem_Icc.mpr hab, by rw [hq_b]; exact hc0⟩
      have hT_ne : T.Nonempty := ⟨b, hbT⟩
      have hT_bdd : BddBelow T := ⟨a, fun v hv => hv.1.1⟩
      let vc := sInf T
      have hvc_mem : vc ∈ Icc a b := ⟨le_csInf hT_ne (fun v hv => hv.1.1), csInf_le hT_bdd hbT⟩
      have hT_closed : IsClosed T := by
        have h1 : T = Icc a b ∩ q ⁻¹' Iic c := rfl
        rw [h1]
        exact hq_cont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
      have hvc_in : vc ∈ T := hT_closed.csInf_mem hT_ne hT_bdd
      have hvc_gt_a : a < vc := by
        rcases eq_or_lt_of_le hvc_mem.1 with heq | hlt
        · exfalso; have := hvc_in.2; rw [← heq] at this; linarith
        · exact hlt
      have hqvc : q vc = c := by
        rcases eq_or_lt_of_le hvc_in.2 with heq | hlt
        · exact heq
        · exfalso
          have hcont_at : ContinuousWithinAt q (Icc a b) vc := hq_cont vc hvc_mem
          have hev : {v | q v < c} ∈ 𝓝[Icc a b] vc :=
            hcont_at.eventually (gt_mem_nhds hlt)
          rw [Metric.mem_nhdsWithin_iff] at hev
          obtain ⟨δ, hδ, hball⟩ := hev
          let v' := max a (vc - δ / 2)
          have hv'_mem : v' ∈ Icc a b := ⟨le_max_left _ _, max_le hab (by linarith [hvc_mem.2])⟩
          have hv'_lt : v' < vc := max_lt hvc_gt_a (by linarith)
          have hv'_dist : v' ∈ Metric.ball vc δ := by
            rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (sub_neg.mpr hv'_lt)]
            have : vc - δ / 2 ≤ v' := le_max_right _ _
            linarith
          have hqv' : q v' < c := hball ⟨hv'_dist, hv'_mem⟩
          have hv'_in : v' ∈ T := ⟨hv'_mem, hqv'.le⟩
          have : vc ≤ v' := csInf_le hT_bdd hv'_in
          linarith
      have hpre : q ⁻¹' Iic c ∩ Icc a b = Icc vc b := by
        ext v; simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Icc]
        constructor
        · intro ⟨hqv, hv⟩
          exact ⟨csInf_le hT_bdd ⟨hv, hqv⟩, hv.2⟩
        · intro ⟨h1, h2⟩
          have hv : v ∈ Icc a b := ⟨le_trans hvc_mem.1 h1, h2⟩
          exact ⟨by rw [← hqvc]; exact hq_anti hvc_mem hv h1, hv⟩
      have hpre2 : Iic c ∩ Icc (0 : ℝ) (q a) = Icc (0 : ℝ) c := by
        ext x; simp only [mem_inter_iff, mem_Iic, mem_Icc]
        exact ⟨fun ⟨h1, h2, _⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1, le_trans h2 hca.le⟩⟩
      rw [hpre, hμ_Icc vc hvc_mem, hqvc, Measure.restrict_apply measurableSet_Iic,
        hpre2, Real.volume_Icc, sub_zero]

/-- Change of variables for any upper-tail primitive `q(v) = ∫ u in v..b, w u` with `w ≥ 0`:
`∫ v in a..b, g (∫ u in v..b, w u) * w v = ∫ q in 0..(∫ u in a..b, w u), g q`. -/
lemma integral_comp_antitone_primitive {a b : ℝ} (hab : a ≤ b)
    {w : ℝ → ℝ} (hw_int : IntegrableOn w (Icc a b)) (hw_nn : ∀ v ∈ Icc a b, 0 ≤ w v)
    {g : ℝ → ℝ}
    (hg : AEStronglyMeasurable g (volume.restrict (Icc (0 : ℝ) (∫ u in a..b, w u)))) :
    ∫ v in a..b, g (∫ u in v..b, w u) * w v = ∫ q in (0 : ℝ)..(∫ u in a..b, w u), g q := by
  let q : ℝ → ℝ := fun v => ∫ u in v..b, w u
  let μ := (volume.restrict (Icc a b)).withDensity (fun v => ENNReal.ofReal (w v))
  have hmap : Measure.map q μ = volume.restrict (Icc (0 : ℝ) (q a)) :=
    map_antitone_primitive hab hw_int hw_nn
  have hw_uIcc : IntegrableOn w (uIcc a b) volume := by rwa [uIcc_of_le hab]
  have hq_cont : ContinuousOn q (Icc a b) := by
    have h := intervalIntegral.continuousOn_primitive_interval_left hw_uIcc
    rwa [uIcc_of_le hab] at h
  have hq_aemeas : AEMeasurable q μ :=
    (hq_cont.aemeasurable measurableSet_Icc).mono_ac (withDensity_absolutelyContinuous _ _)
  have hqa_nn : 0 ≤ q a :=
    intervalIntegral.integral_nonneg hab (fun u hu => hw_nn u hu)
  have h1 : ∫ x in Icc (0 : ℝ) (q a), g x = ∫ v, g (q v) ∂μ := by
    rw [← hmap, integral_map hq_aemeas (by rwa [hmap])]
  have h2 : ∫ v, g (q v) ∂μ = ∫ v in Icc a b, w v * g (q v) := by
    rw [integral_withDensity_eq_integral_toReal_smul₀ (hw_int.aemeasurable.ennreal_ofReal)
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
    refine setIntegral_congr_fun measurableSet_Icc (fun v hv => ?_)
    rw [ENNReal.toReal_ofReal (hw_nn v hv), smul_eq_mul]
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hqa_nn, ← integral_Icc_eq_integral_Ioc, h1, h2]
  refine setIntegral_congr_fun measurableSet_Icc (fun v _ => mul_comm _ _)

/-- Chain rule for powers of an upper-tail primitive `c - ∫ u in v..b, w u` (valid for any
nonnegative integrable `w`, with no differentiability of the primitive required):
`(k + 1) * ∫ v in a..b, (c - ∫ u in v..b, w u)^k * w v = c^(k+1) - (c - ∫ u in a..b, w u)^(k+1)`. -/
lemma pow_sub_pow_eq_integral_antitone {a b c : ℝ} (hab : a ≤ b) (k : ℕ)
    {w : ℝ → ℝ} (hw_int : IntegrableOn w (Icc a b)) (hw_nn : ∀ v ∈ Icc a b, 0 ≤ w v) :
    ((k + 1 : ℕ) : ℝ) * ∫ v in a..b, (c - ∫ u in v..b, w u) ^ k * w v =
      c ^ (k + 1) - (c - ∫ u in a..b, w u) ^ (k + 1) := by
  let g : ℝ → ℝ := fun x => ((k + 1 : ℕ) : ℝ) * (c - x) ^ k
  have hg_cont : Continuous g := by fun_prop
  have hchg := integral_comp_antitone_primitive hab hw_int hw_nn hg_cont.aestronglyMeasurable
  rw [← intervalIntegral.integral_const_mul]
  have heq : (fun v => ((k + 1 : ℕ) : ℝ) * ((c - ∫ u in v..b, w u) ^ k * w v)) =
      fun v => g (∫ u in v..b, w u) * w v := by
    ext v; simp [g, mul_assoc]
  rw [heq, hchg]
  let G : ℝ → ℝ := fun x => -(c - x) ^ (k + 1)
  have hG_deriv : ∀ x, HasDerivAt G (g x) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => c - y) (-1) x := by
      simpa using (hasDerivAt_const x c).fun_sub (hasDerivAt_id x)
    have h2 : HasDerivAt (fun y : ℝ => (c - y) ^ (k + 1))
        (((k + 1 : ℕ) : ℝ) * (c - x) ^ k * (-1)) x := h1.pow (k + 1)
    have h3 := h2.neg
    convert h3 using 1
    simp [g]
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hG_deriv x)
    (hg_cont.intervalIntegrable 0 (∫ u in a..b, w u))
  rw [hftc]
  simp only [G, sub_zero]
  ring

/-! ### Section 4A: Effective Distributions, Allocations, and Border's Constraint -/

lemma visit_le_one (M : Market) (θ : VisitStrategy M) (j : Fin M.m) {v : ℝ}
    (hv : v ∈ Icc M.a 1) : θ.θ j v ≤ 1 := by
  have hsum := θ.hsum v hv
  have hle : θ.θ j v ≤ ∑ k : Fin M.m, θ.θ k v :=
    Finset.single_le_sum (fun k _ => θ.hnonneg k v) (Finset.mem_univ j)
  linarith

lemma f_integrableOn (M : Market) : IntegrableOn M.f (Icc M.a 1) :=
  M.hf_cont.integrableOn_Icc

lemma visit_mul_f_integrableOn (M : Market) (θ : VisitStrategy M) (j : Fin M.m) :
    IntegrableOn (fun u => θ.θ j u * M.f u) (Icc M.a 1) := by
  have hmeas : AEStronglyMeasurable (fun u => θ.θ j u * M.f u) (volume.restrict (Icc M.a 1)) :=
    ((θ.hmeas j).aemeasurable.mul (M.hf_cont.aemeasurable measurableSet_Icc)).aestronglyMeasurable
  refine (f_integrableOn M).mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  have hf_nn : 0 ≤ M.f u := (M.hf_pos u hu).le
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (θ.hnonneg j u) hf_nn)]
  nlinarith [visit_le_one M θ j hu]

lemma effDist_eq_at_a (M : Market) (θ : VisitStrategy M) (j : Fin M.m) {v : ℝ}
    (hv : v ≤ M.a) : effDist M θ j v = effDist M θ j M.a := by
  unfold effDist
  congr 1
  have hzero : ∫ u in v..M.a, θ.θ j u * M.f u = 0 := by
    rw [intervalIntegral.integral_of_le hv, integral_Ioc_eq_integral_Ioo]
    have h0 : EqOn (fun u => θ.θ j u * M.f u) 0 (Ioo v M.a) := by
      intro u hu; simp [M.hf_below u hu.2]
    rw [setIntegral_congr_fun measurableSet_Ioo h0]; simp
  have hint1 : IntervalIntegrable (fun u => θ.θ j u * M.f u) volume v M.a := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hv]
    have h0 : EqOn (fun u => θ.θ j u * M.f u) 0 (Ioo v M.a) := by
      intro u hu; simp [M.hf_below u hu.2]
    exact (integrableOn_zero : IntegrableOn (0 : ℝ → ℝ) (Ioo v M.a)).congr_fun
      (fun u hu => (h0 hu).symm) measurableSet_Ioo
  have hint2 : IntervalIntegrable (fun u => θ.θ j u * M.f u) volume M.a 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le M.ha1.le).mpr (visit_mul_f_integrableOn M θ j)
  rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2, hzero, zero_add]

lemma effDist_one (M : Market) (θ : VisitStrategy M) (j : Fin M.m) :
    effDist M θ j 1 = 1 := by
  simp [effDist]

lemma integral_f_eq_sub_F (M : Market) {v : ℝ} (hv : v ∈ Icc M.a 1) :
    ∫ u in v..1, M.f u = 1 - M.F v := by
  have hcont : ContinuousOn M.F (Icc v 1) := M.F_continuousOn.mono (Icc_subset_Icc_left hv.1)
  have hder : ∀ x ∈ Ioo v 1, HasDerivAt M.F (M.f x) x := fun x hx =>
    M.hF_deriv_open x ⟨lt_of_le_of_lt hv.1 hx.1, hx.2⟩
  have hint : IntervalIntegrable M.f volume v 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hv.2).mpr
      ((f_integrableOn M).mono_set (Icc_subset_Icc_left hv.1))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hv.2 hcont hder hint, M.hF_1]

lemma effDist_monotoneOn (M : Market) (θ : VisitStrategy M) (j : Fin M.m) :
    MonotoneOn (effDist M θ j) (Iic 1) := by
  have hmono_Icc : MonotoneOn (effDist M θ j) (Icc M.a 1) := by
    intro v₁ hv₁ v₂ hv₂ hle
    unfold effDist
    have hint : IntervalIntegrable (fun u => θ.θ j u * M.f u) volume M.a 1 :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le M.ha1.le).mpr (visit_mul_f_integrableOn M θ j)
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hint.mono_set (uIcc_subset_uIcc (mem_uIcc_of_le hv₁.1 hv₁.2) (mem_uIcc_of_le hv₂.1 hv₂.2)))
      (hint.mono_set (uIcc_subset_uIcc (mem_uIcc_of_le hv₂.1 hv₂.2) right_mem_uIcc))
    have hnn : 0 ≤ ∫ u in v₁..v₂, θ.θ j u * M.f u :=
      intervalIntegral.integral_nonneg hle (fun u hu =>
        mul_nonneg (θ.hnonneg j u) (M.hf_pos u ⟨le_trans hv₁.1 hu.1, le_trans hu.2 hv₂.2⟩).le)
    linarith
  intro v₁ hv₁ v₂ hv₂ hle
  rcases le_total v₁ M.a with h1 | h1
  · rw [effDist_eq_at_a M θ j h1]
    rcases le_total v₂ M.a with h2 | h2
    · rw [effDist_eq_at_a M θ j h2]
    · exact hmono_Icc (left_mem_Icc.mpr M.ha1.le) ⟨h2, hv₂⟩ h2
  · exact hmono_Icc ⟨h1, hv₁⟩ ⟨le_trans h1 hle, hv₂⟩ hle

lemma effDist_mem_Icc (M : Market) (θ : VisitStrategy M) (j : Fin M.m) {v : ℝ}
    (hv : v ≤ 1) : effDist M θ j v ∈ Icc (0 : ℝ) 1 := by
  have hle1 : effDist M θ j v ≤ 1 := by
    rw [← effDist_one M θ j]
    exact effDist_monotoneOn M θ j hv (mem_Iic.mpr le_rfl) hv
  have hge0 : 0 ≤ effDist M θ j v := by
    have hge_a : effDist M θ j M.a ≤ effDist M θ j v := by
      rcases le_total v M.a with h | h
      · rw [effDist_eq_at_a M θ j h]
      · exact effDist_monotoneOn M θ j M.ha1.le hv h
    have ha_nn : 0 ≤ effDist M θ j M.a := by
      unfold effDist
      have hle_f : ∫ u in M.a..1, θ.θ j u * M.f u ≤ ∫ u in M.a..1, M.f u := by
        refine intervalIntegral.integral_mono_on M.ha1.le
          ((intervalIntegrable_iff_integrableOn_Icc_of_le M.ha1.le).mpr (visit_mul_f_integrableOn M θ j))
          ((intervalIntegrable_iff_integrableOn_Icc_of_le M.ha1.le).mpr (f_integrableOn M))
          (fun u hu => ?_)
        nlinarith [visit_le_one M θ j hu, (M.hf_pos u hu).le]
      rw [integral_f_eq_sub_F M (left_mem_Icc.mpr M.ha1.le), M.hF_a, sub_zero] at hle_f
      linarith
    linarith
  exact ⟨hge0, hle1⟩

lemma sum_one_sub_effDist (M : Market) (θ : VisitStrategy M) {v : ℝ}
    (hv : v ∈ Icc M.a 1) : ∑ j : Fin M.m, (1 - effDist M θ j v) = 1 - M.F v := by
  have hterm : ∀ j : Fin M.m, 1 - effDist M θ j v = ∫ u in v..1, θ.θ j u * M.f u := by
    intro j; unfold effDist; ring
  simp_rw [hterm]
  have hint : ∀ j : Fin M.m, IntervalIntegrable (fun u => θ.θ j u * M.f u) volume v 1 := fun j =>
    (intervalIntegrable_iff_integrableOn_Icc_of_le hv.2).mpr
      ((visit_mul_f_integrableOn M θ j).mono_set (Icc_subset_Icc_left hv.1))
  have hsum_int : ∀ (s : Finset (Fin M.m)),
      IntervalIntegrable (fun u => ∑ j ∈ s, θ.θ j u * M.f u) volume v 1 ∧
      ∑ j ∈ s, ∫ u in v..1, θ.θ j u * M.f u = ∫ u in v..1, ∑ j ∈ s, θ.θ j u * M.f u := by
    intro s
    classical
    refine Finset.induction_on s ?_ ?_
    · exact ⟨by simp, by simp⟩
    · intro j s hjs ih
      have hfun : (fun u => ∑ k ∈ insert j s, θ.θ k u * M.f u) =
          fun u => θ.θ j u * M.f u + ∑ k ∈ s, θ.θ k u * M.f u := by
        ext u; exact Finset.sum_insert hjs
      rw [hfun, Finset.sum_insert hjs]
      refine ⟨(hint j).add ih.1, ?_⟩
      rw [intervalIntegral.integral_add (hint j) ih.1, ih.2]
  rw [(hsum_int Finset.univ).2, ← integral_f_eq_sub_F M hv]
  rw [intervalIntegral.integral_of_le hv.2, intervalIntegral.integral_of_le hv.2,
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_fun measurableSet_Icc (fun u hu => ?_)
  rw [← Finset.sum_mul, θ.hsum u ⟨le_trans hv.1 hu.1, hu.2⟩, one_mul]

lemma poolAvg_mono_left {n : ℕ} (hn : 1 ≤ n) {x₁ x₂ y : ℝ}
    (hx₁ : 0 ≤ x₁) (hx : x₁ ≤ x₂) (hy : 0 ≤ y) :
    poolAvg n x₁ y ≤ poolAvg n x₂ y := by
  rw [poolAvg_eq_sum n hn, poolAvg_eq_sum n hn]
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
  refine div_le_div_of_nonneg_right ?_ hnR.le
  refine Finset.sum_le_sum (fun k _ => ?_)
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx₁ hx k) (pow_nonneg hy _)

lemma poolAvg_mono_right {n : ℕ} (hn : 1 ≤ n) {x y₁ y₂ : ℝ}
    (hx : 0 ≤ x) (hy₁ : 0 ≤ y₁) (hy : y₁ ≤ y₂) :
    poolAvg n x y₁ ≤ poolAvg n x y₂ := by
  rw [poolAvg_eq_sum n hn, poolAvg_eq_sum n hn]
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
  refine div_le_div_of_nonneg_right ?_ hnR.le
  refine Finset.sum_le_sum (fun k _ => ?_)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy₁ hy _) (pow_nonneg hx _)

lemma poolAvg_self (n : ℕ) (x : ℝ) : poolAvg n x x = x ^ (n - 1) := by
  simp [poolAvg]

lemma poolAvg_mul_sub {n : ℕ} (hn : 1 ≤ n) (x y : ℝ) :
    poolAvg n x y * (y - x) = (y ^ n - x ^ n) / (n : ℝ) := by
  unfold poolAvg
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_ne_zero (by omega)).ne'
  split_ifs with hxy
  · subst hxy; simp
  · have hne : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
    field_simp [hnR, hne]

private lemma list_pairwise_symm {α : Type*} {R : α → α → Prop}
    (hsymm : ∀ a b, R a b → R b a) :
    ∀ {L : List α}, L.Pairwise R → ∀ a ∈ L, ∀ b ∈ L, a ≠ b → R a b := by
  intro L
  induction L with
  | nil => intro _ a ha; simp at ha
  | cons x L ih =>
    intro hpw a ha b hb hne
    rw [List.pairwise_cons] at hpw
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact absurd rfl hne
      · exact hpw.1 b hb'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact hsymm _ _ (hpw.1 a ha')
      · exact ih hpw.2 a ha' b hb' hne

lemma alloc_mem_Icc (M : Market) (mech : HierarchicalMech) {Fj : ℝ → ℝ}
    (hFj_mono : MonotoneOn Fj (Iic 1)) (hFj_mem : ∀ v ≤ 1, Fj v ∈ Icc (0 : ℝ) 1)
    {v : ℝ} (hv : v ≤ 1) : alloc M mech Fj v ∈ Icc (0 : ℝ) 1 := by
  unfold alloc
  split_ifs with hvr
  · exact ⟨le_rfl, zero_le_one⟩
  · cases hfind : mech.pools.find? (fun I => decide (I.α < v ∧ v < I.β)) with
    | none =>
      have h := hFj_mem v hv
      exact ⟨pow_nonneg h.1 _, pow_le_one₀ h.1 h.2⟩
    | some I =>
      have hI_mem : I ∈ mech.pools := List.mem_of_find?_eq_some hfind
      have hI_in := mech.hpools_in I hI_mem
      have hα := hFj_mem I.α (le_trans I.hαβ.le hI_in.2)
      have hβ := hFj_mem I.β hI_in.2
      have hαβ : Fj I.α ≤ Fj I.β := hFj_mono (le_trans I.hαβ.le hI_in.2) hI_in.2 I.hαβ.le
      have hn1 : 1 ≤ M.n := by have := M.hn; omega
      have hge : (Fj I.α) ^ (M.n - 1) ≤ poolAvg M.n (Fj I.α) (Fj I.β) := by
        rw [← poolAvg_self]; exact poolAvg_mono_right hn1 hα.1 hα.1 hαβ
      have hle : poolAvg M.n (Fj I.α) (Fj I.β) ≤ (Fj I.β) ^ (M.n - 1) := by
        rw [← poolAvg_self]; exact poolAvg_mono_left hn1 hα.1 hαβ hβ.1
      exact ⟨le_trans (pow_nonneg hα.1 _) hge, le_trans hle (pow_le_one₀ hβ.1 hβ.2)⟩

lemma alloc_monotoneOn (M : Market) (mech : HierarchicalMech) {Fj : ℝ → ℝ}
    (hFj_mono : MonotoneOn Fj (Iic 1)) (hFj_mem : ∀ v ≤ 1, Fj v ∈ Icc (0 : ℝ) 1) :
    MonotoneOn (alloc M mech Fj) (Iic 1) := by
  have hn1 : 1 ≤ M.n := by have := M.hn; omega
  have hpool_bounds : ∀ I ∈ mech.pools,
      (Fj I.α) ^ (M.n - 1) ≤ poolAvg M.n (Fj I.α) (Fj I.β) ∧
      poolAvg M.n (Fj I.α) (Fj I.β) ≤ (Fj I.β) ^ (M.n - 1) := by
    intro I hI
    have hI_in := mech.hpools_in I hI
    have hα := hFj_mem I.α (le_trans I.hαβ.le hI_in.2)
    have hβ := hFj_mem I.β hI_in.2
    have hαβ : Fj I.α ≤ Fj I.β := hFj_mono (le_trans I.hαβ.le hI_in.2) hI_in.2 I.hαβ.le
    exact ⟨by rw [← poolAvg_self]; exact poolAvg_mono_right hn1 hα.1 hα.1 hαβ,
           by rw [← poolAvg_self]; exact poolAvg_mono_left hn1 hα.1 hαβ hβ.1⟩
  intro v₁ hv₁ v₂ hv₂ hv12
  have hv₁_nonneg : 0 ≤ alloc M mech Fj v₂ := (alloc_mem_Icc M mech hFj_mono hFj_mem hv₂).1
  unfold alloc
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact (alloc_mem_Icc M mech hFj_mono hFj_mem hv₂).1 |> fun h => by
      simpa [alloc, h2] using h
  · exfalso; linarith
  · cases hfind₁ : mech.pools.find? (fun I => decide (I.α < v₁ ∧ v₁ < I.β)) with
    | none =>
      cases hfind₂ : mech.pools.find? (fun I => decide (I.α < v₂ ∧ v₂ < I.β)) with
      | none =>
        exact pow_le_pow_left₀ (hFj_mem v₁ hv₁).1 (hFj_mono hv₁ hv₂ hv12) _
      | some I₂ =>
        have hI₂_mem := List.mem_of_find?_eq_some hfind₂
        have hI₂_pred : I₂.α < v₂ ∧ v₂ < I₂.β := by
          have := List.find?_some hfind₂; simpa using this
        have hnot1 : ¬(I₂.α < v₁ ∧ v₁ < I₂.β) := by
          intro h
          have := List.find?_eq_none.mp hfind₁ I₂ hI₂_mem
          simp [h] at this
        have hv1_le_α2 : v₁ ≤ I₂.α := by
          by_contra hgt; push Not at hgt
          exact hnot1 ⟨hgt, lt_of_le_of_lt hv12 hI₂_pred.2⟩
        have hI₂_in := mech.hpools_in I₂ hI₂_mem
        calc (Fj v₁) ^ (M.n - 1)
            ≤ (Fj I₂.α) ^ (M.n - 1) :=
              pow_le_pow_left₀ (hFj_mem v₁ hv₁).1 (hFj_mono hv₁ (le_trans I₂.hαβ.le hI₂_in.2) hv1_le_α2) _
          _ ≤ poolAvg M.n (Fj I₂.α) (Fj I₂.β) := (hpool_bounds I₂ hI₂_mem).1
    | some I₁ =>
      have hI₁_mem := List.mem_of_find?_eq_some hfind₁
      have hI₁_pred : I₁.α < v₁ ∧ v₁ < I₁.β := by
        have := List.find?_some hfind₁; simpa using this
      have hI₁_in := mech.hpools_in I₁ hI₁_mem
      cases hfind₂ : mech.pools.find? (fun I => decide (I.α < v₂ ∧ v₂ < I.β)) with
      | none =>
        have hnot2 : ¬(I₁.α < v₂ ∧ v₂ < I₁.β) := by
          intro h
          have := List.find?_eq_none.mp hfind₂ I₁ hI₁_mem
          simp [h] at this
        have hβ1_le_v2 : I₁.β ≤ v₂ := by
          by_contra hlt; push Not at hlt
          exact hnot2 ⟨lt_of_lt_of_le hI₁_pred.1 hv12, hlt⟩
        calc poolAvg M.n (Fj I₁.α) (Fj I₁.β)
            ≤ (Fj I₁.β) ^ (M.n - 1) := (hpool_bounds I₁ hI₁_mem).2
          _ ≤ (Fj v₂) ^ (M.n - 1) :=
              pow_le_pow_left₀ (hFj_mem I₁.β hI₁_in.2).1 (hFj_mono hI₁_in.2 hv₂ hβ1_le_v2) _
      | some I₂ =>
        by_cases hIeq : I₁ = I₂
        · subst hIeq; exact le_rfl
        · have hI₂_mem := List.mem_of_find?_eq_some hfind₂
          have hI₂_pred : I₂.α < v₂ ∧ v₂ < I₂.β := by
            have := List.find?_some hfind₂; simpa using this
          have hI₂_in := mech.hpools_in I₂ hI₂_mem
          have hpw := list_pairwise_symm (fun _ _ h => Or.symm h) mech.hpools_disj I₁ hI₁_mem I₂ hI₂_mem hIeq
          have hβ1_le_α2 : I₁.β ≤ I₂.α := by
            rcases hpw with h | h
            · exact h
            · exfalso; linarith [hI₁_pred.1, hI₂_pred.2, hv12]
          calc poolAvg M.n (Fj I₁.α) (Fj I₁.β)
              ≤ (Fj I₁.β) ^ (M.n - 1) := (hpool_bounds I₁ hI₁_mem).2
            _ ≤ (Fj I₂.α) ^ (M.n - 1) :=
                pow_le_pow_left₀ (hFj_mem I₁.β hI₁_in.2).1
                  (hFj_mono hI₁_in.2 (le_trans I₂.hαβ.le hI₂_in.2) hβ1_le_α2) _
            _ ≤ poolAvg M.n (Fj I₂.α) (Fj I₂.β) := (hpool_bounds I₂ hI₂_mem).1

lemma alloc_SPA_eq (M : Market) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (Fj : ℝ → ℝ) (v : ℝ) :
    alloc M (SPA r hr0 hr1) Fj v = if v < r then 0 else (Fj v) ^ (M.n - 1) := by
  simp [alloc, SPA]

lemma payment_zero_of_lt_r (M : Market) (mech : HierarchicalMech) (Fj : ℝ → ℝ)
    {v : ℝ} (hv0 : 0 ≤ v) (hvr : v < mech.r) : payment M mech Fj v = 0 := by
  unfold payment surplus
  have h1 : alloc M mech Fj v = 0 := by simp [alloc, hvr]
  have h2 : ∫ u in (0 : ℝ)..v, alloc M mech Fj u = 0 := by
    rw [intervalIntegral.integral_of_le hv0]
    have h0 : EqOn (alloc M mech Fj) 0 (Ioc 0 v) := by
      intro u hu; simp [alloc, lt_of_le_of_lt hu.2 hvr]
    rw [setIntegral_congr_fun measurableSet_Ioc h0]; simp
  rw [h1, h2]; ring

/-- **Border's Feasibility Inequality for Any Hierarchical Mechanism (eq. (1))**:
For any `mech : HierarchicalMech`, `θ : VisitStrategy M`, `j : Fin M.m`, and `v ∈ [M.a, 1]`:
`∫ u in v..1, alloc M mech (effDist M θ j) u * θ.θ j u * M.f u ≤ h_n M.n (1 - effDist M θ j v)`. -/
theorem hierarchical_border_le (M : Market) (mech : HierarchicalMech)
    (θ : VisitStrategy M) (j : Fin M.m) {v : ℝ} (hv : v ∈ Icc M.a 1) :
    ∫ u in v..1, alloc M mech (effDist M θ j) u * (θ.θ j u * M.f u) ≤
      h_n M.n (1 - effDist M θ j v) := by
  let F1 := effDist M θ j
  let w : ℝ → ℝ := fun u => θ.θ j u * M.f u
  have hw_int : IntegrableOn w (Icc v 1) :=
    (visit_mul_f_integrableOn M θ j).mono_set (Icc_subset_Icc_left hv.1)
  have hw_nn : ∀ u ∈ Icc v 1, 0 ≤ w u := fun u hu =>
    mul_nonneg (θ.hnonneg j u) (M.hf_pos u ⟨le_trans hv.1 hu.1, hu.2⟩).le
  have hF1_mono : MonotoneOn F1 (Iic 1) := effDist_monotoneOn M θ j
  have hF1_mem : ∀ u ≤ 1, F1 u ∈ Icc (0 : ℝ) 1 := fun u hu => effDist_mem_Icc M θ j hu
  have hx_mono : MonotoneOn (alloc M mech F1) (Iic 1) := alloc_monotoneOn M mech hF1_mono hF1_mem
  have hx_int : IntegrableOn (fun u => alloc M mech F1 u * w u) (Icc v 1) := by
    have hxm : AEStronglyMeasurable (alloc M mech F1) (volume.restrict (Icc v 1)) :=
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hv.2).mp
        ((hx_mono.mono (by rw [uIcc_of_le hv.2]; exact fun u hu => hu.2)).intervalIntegrable)).aestronglyMeasurable
    refine hw_int.mono' (hxm.mul hw_int.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    have hxu := alloc_mem_Icc M mech hF1_mono hF1_mem hu.2
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hxu.1 (hw_nn u hu))]
    nlinarith [hxu.2, hw_nn u hu]
  have hpow_int : IntegrableOn (fun u => (F1 u) ^ (M.n - 1) * w u) (Icc v 1) := by
    have hFm : AEStronglyMeasurable (fun u => (F1 u) ^ (M.n - 1)) (volume.restrict (Icc v 1)) := by
      have h1 : AEStronglyMeasurable F1 (volume.restrict (Icc v 1)) :=
        ((intervalIntegrable_iff_integrableOn_Icc_of_le hv.2).mp
          ((hF1_mono.mono (by rw [uIcc_of_le hv.2]; exact fun u hu => hu.2)).intervalIntegrable)).aestronglyMeasurable
      exact h1.pow (M.n - 1)
    refine hw_int.mono' (hFm.mul hw_int.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    have hFu := hF1_mem u hu.2
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hFu.1 _) (hw_nn u hu))]
    nlinarith [pow_le_one₀ (n := M.n - 1) hFu.1 hFu.2, hw_nn u hu]
  -- Evaluate `∫ u in v..1, (F1 u)^(n-1) * w u = h_n n (1 - F1 v)`
  have htop_eq : ∫ u in v..1, (F1 u) ^ (M.n - 1) * w u = h_n M.n (1 - F1 v) := by
    have hch := pow_sub_pow_eq_integral_antitone (c := 1) hv.2 (M.n - 1) hw_int hw_nn
    have hn_eq : M.n - 1 + 1 = M.n := by have := M.hn; omega
    rw [hn_eq, one_pow] at hch
    have hF1_eq : ∀ u, 1 - ∫ s in u..1, w s = F1 u := fun _ => rfl
    simp_rw [hF1_eq] at hch
    unfold h_n
    have hnR : (M.n : ℝ) ≠ 0 := M.n_pos_real.ne'
    have h1sub : 1 - (1 - F1 v) = F1 v := by ring
    rw [h1sub]
    rw [eq_div_iff hnR, mul_comm]
    exact hch
  rw [← htop_eq, intervalIntegral.integral_of_le hv.2, intervalIntegral.integral_of_le hv.2,
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc]
  -- Decompose `Icc v 1` into `U := (⋃ I ∈ mech.pools, Ioo I.α I.β) ∩ Icc v 1` and `Icc v 1 \ U`
  have hmeas_U : ∀ (L : List Pool), MeasurableSet (⋃ I ∈ L, Ioo I.α I.β) := by
    intro L
    induction L with
    | nil => simp
    | cons I L ih =>
      have : (⋃ J ∈ I :: L, Ioo J.α J.β) = Ioo I.α I.β ∪ ⋃ J ∈ L, Ioo J.α J.β := by ext x; simp
      rw [this]; exact measurableSet_Ioo.union ih
  let U : Set ℝ := (⋃ I ∈ mech.pools, Ioo I.α I.β) ∩ Icc v 1
  have hU_meas : MeasurableSet U := (hmeas_U mech.pools).inter measurableSet_Icc
  have hU_sub : U ⊆ Icc v 1 := inter_subset_right
  have hsplit_set : Icc v 1 = (Icc v 1 \ U) ∪ U := (sdiff_union_of_subset hU_sub).symm
  rw [hsplit_set, setIntegral_union disjoint_sdiff_self_left hU_meas
        (hx_int.mono_set sdiff_subset) (hx_int.mono_set hU_sub),
      setIntegral_union disjoint_sdiff_self_left hU_meas
        (hpow_int.mono_set sdiff_subset) (hpow_int.mono_set hU_sub)]
  refine add_le_add ?_ ?_
  · -- Off the pools: `alloc ≤ F1^(n-1)` pointwise
    refine setIntegral_mono_on (hx_int.mono_set sdiff_subset) (hpow_int.mono_set sdiff_subset)
      (measurableSet_Icc.diff hU_meas) (fun u hu => ?_)
    have hnot_pool : ∀ I ∈ mech.pools, ¬(I.α < u ∧ u < I.β) := by
      intro I hI hlt
      exact hu.2 ⟨Set.mem_iUnion₂.mpr ⟨I, hI, hlt⟩, hu.1⟩
    have hfind : mech.pools.find? (fun I => decide (I.α < u ∧ u < I.β)) = none := by
      rw [List.find?_eq_none]
      intro I hI; simp [hnot_pool I hI]
    have hx_le : alloc M mech F1 u ≤ (F1 u) ^ (M.n - 1) := by
      unfold alloc
      split_ifs with hlt
      · exact pow_nonneg (hF1_mem u hu.1.2).1 _
      · rw [hfind]
    exact mul_le_mul_of_nonneg_right hx_le (hw_nn u hu.1)
  · -- On the pools: sum over disjoint pools `I ∈ mech.pools`
    have hpool_le : ∀ I ∈ mech.pools,
        ∫ u in (Ioo I.α I.β ∩ Icc v 1), alloc M mech F1 u * w u ≤
          ∫ u in (Ioo I.α I.β ∩ Icc v 1), (F1 u) ^ (M.n - 1) * w u := by
      intro I hI
      have hI_in := mech.hpools_in I hI
      rcases le_or_gt I.β v with hβv | hvβ
      · have hemp : Ioo I.α I.β ∩ Icc v 1 = ∅ := by
          ext u; simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
          intro h1 h2; linarith [h1.2, h2.1]
        rw [hemp]; simp
      · let c := max v I.α
        have hc_lt : c < I.β := max_lt hvβ I.hαβ
        have hc_ge_v : v ≤ c := le_max_left _ _
        have hc_ge_α : I.α ≤ c := le_max_right _ _
        have hae_set : (Ioo I.α I.β ∩ Icc v 1 : Set ℝ) =ᵐ[volume] Ioo c I.β := by
          rw [ae_eq_set]
          constructor
          · refine measure_mono_null ?_ (measure_singleton v)
            intro u ⟨⟨⟨h1, h2⟩, ⟨h3, _⟩⟩, hnot⟩
            simp only [mem_singleton_iff]
            rcases eq_or_lt_of_le h3 with rfl | hlt
            · rfl
            · exfalso; exact hnot ⟨max_lt hlt h1, h2⟩
          · refine measure_mono_null ?_ measure_empty
            intro u ⟨⟨h1, h2⟩, hnot⟩
            exfalso
            exact hnot ⟨⟨lt_of_le_of_lt hc_ge_α h1, h2⟩,
              ⟨le_trans hc_ge_v h1.le, le_trans h2.le hI_in.2⟩⟩
        rw [setIntegral_congr_set hae_set, setIntegral_congr_set hae_set]
        -- On `Ioo c I.β`, `alloc M mech F1 u = poolAvg M.n (F1 I.α) (F1 I.β)`
        have halloc_eq : EqOn (fun u => alloc M mech F1 u * w u)
            (fun u => poolAvg M.n (F1 I.α) (F1 I.β) * w u) (Ioo c I.β) := by
          intro u hu
          have huI : I.α < u ∧ u < I.β := ⟨lt_of_le_of_lt hc_ge_α hu.1, hu.2⟩
          have hu_ge_r : ¬(u < mech.r) := not_lt.mpr (le_trans hI_in.1 huI.1.le)
          have hfind : mech.pools.find? (fun J => decide (J.α < u ∧ u < J.β)) = some I := by
            obtain ⟨J, hJ⟩ : ∃ J, mech.pools.find? (fun J => decide (J.α < u ∧ u < J.β)) = some J := by
              rcases Option.eq_none_or_eq_some (mech.pools.find? (fun J => decide (J.α < u ∧ u < J.β))) with hnone | ⟨J, hJ⟩
              · exfalso
                have := List.find?_eq_none.mp hnone I hI
                simp [huI] at this
              · exact ⟨J, hJ⟩
            have hJ_mem := List.mem_of_find?_eq_some hJ
            have hJ_pred : J.α < u ∧ u < J.β := by have := List.find?_some hJ; simpa using this
            have hJI : J = I := by
              by_contra hne
              rcases list_pairwise_symm (fun _ _ h => Or.symm h) mech.hpools_disj J hJ_mem I hI hne with h1 | h2
              · linarith [hJ_pred.2, huI.1]
              · linarith [huI.2, hJ_pred.1]
            rwa [hJI] at hJ
          dsimp only [alloc]
          rw [ite_eq_right_iff.mpr (fun h => absurd h hu_ge_r), hfind]
        rw [setIntegral_congr_fun measurableSet_Ioo halloc_eq, integral_const_mul,
          ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hc_lt.le,
          ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hc_lt.le]
        have hw_cβ : IntegrableOn w (Icc c I.β) :=
          hw_int.mono_set (Icc_subset_Icc hc_ge_v hI_in.2)
        have hw_cβ_nn : ∀ u ∈ Icc c I.β, 0 ≤ w u := fun u hu =>
          hw_nn u ⟨le_trans hc_ge_v hu.1, le_trans hu.2 hI_in.2⟩
        -- `∫ u in c..I.β, w u = F1 I.β - F1 c`
        have hint_w_eq : ∫ u in c..I.β, w u = F1 I.β - F1 c := by
          have hw_ivl := (intervalIntegrable_iff_integrableOn_Icc_of_le hv.2).mpr hw_int
          have hsplit := intervalIntegral.integral_add_adjacent_intervals
            (hw_ivl.mono_set (uIcc_subset_uIcc (mem_uIcc_of_le hc_ge_v (le_trans hc_lt.le hI_in.2))
              (mem_uIcc_of_le (le_trans hc_ge_v hc_lt.le) hI_in.2)))
            (hw_ivl.mono_set (uIcc_subset_uIcc (mem_uIcc_of_le (le_trans hc_ge_v hc_lt.le) hI_in.2) right_mem_uIcc))
          show ∫ u in c..I.β, w u = (1 - ∫ u in I.β..1, w u) - (1 - ∫ u in c..1, w u)
          linarith
        -- `∫ u in c..I.β, (F1 u)^(n-1) * w u = ((F1 I.β)^n - (F1 c)^n) / n`
        have hint_pow_eq : ∫ u in c..I.β, (F1 u) ^ (M.n - 1) * w u =
            ((F1 I.β) ^ M.n - (F1 c) ^ M.n) / (M.n : ℝ) := by
          have hch := pow_sub_pow_eq_integral_antitone (c := F1 I.β) hc_lt.le (M.n - 1) hw_cβ hw_cβ_nn
          have hn_eq : M.n - 1 + 1 = M.n := by have := M.hn; omega
          rw [hn_eq] at hch
          have hF_shift : ∀ u ∈ Icc c I.β, F1 I.β - ∫ s in u..I.β, w s = F1 u := by
            intro u hu
            have hw_ivl := (intervalIntegrable_iff_integrableOn_Icc_of_le hv.2).mpr hw_int
            have hsplit := intervalIntegral.integral_add_adjacent_intervals
              (hw_ivl.mono_set (uIcc_subset_uIcc (mem_uIcc_of_le (le_trans hc_ge_v hu.1) (le_trans hu.2 hI_in.2))
                (mem_uIcc_of_le (le_trans hc_ge_v hc_lt.le) hI_in.2)))
              (hw_ivl.mono_set (uIcc_subset_uIcc (mem_uIcc_of_le (le_trans hc_ge_v hc_lt.le) hI_in.2) right_mem_uIcc))
            show (1 - ∫ s in I.β..1, w s) - ∫ s in u..I.β, w s = 1 - ∫ s in u..1, w s
            linarith
          have hcongr : ∫ u in c..I.β, (F1 I.β - ∫ s in u..I.β, w s) ^ (M.n - 1) * w u =
              ∫ u in c..I.β, (F1 u) ^ (M.n - 1) * w u := by
            rw [intervalIntegral.integral_of_le hc_lt.le, intervalIntegral.integral_of_le hc_lt.le,
              ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc]
            refine setIntegral_congr_fun measurableSet_Icc (fun u hu => by rw [hF_shift u hu])
          rw [hcongr, hF_shift c (left_mem_Icc.mpr hc_lt.le)] at hch
          rw [eq_div_iff M.n_pos_real.ne', mul_comm]
          exact hch
        rw [hint_w_eq, hint_pow_eq]
        have hn1 : 1 ≤ M.n := by have := M.hn; omega
        rw [← poolAvg_mul_sub hn1 (F1 c) (F1 I.β)]
        refine mul_le_mul_of_nonneg_right ?_ ?_
        · exact poolAvg_mono_left hn1 (hF1_mem I.α (le_trans I.hαβ.le hI_in.2)).1
            (hF1_mono (le_trans I.hαβ.le hI_in.2) (le_trans hc_lt.le hI_in.2) hc_ge_α)
            (hF1_mem I.β hI_in.2).1
        · exact sub_nonneg.mpr (hF1_mono (le_trans hc_lt.le hI_in.2) hI_in.2 hc_lt.le)
    -- Sum `hpool_le` across the pairwise disjoint list `mech.pools`
    have hsum_le : ∀ (L : List Pool),
        (∀ I ∈ L, I ∈ mech.pools) →
        L.Pairwise (fun I J => I.β ≤ J.α ∨ J.β ≤ I.α) →
        ∫ u in ((⋃ I ∈ L, Ioo I.α I.β) ∩ Icc v 1), alloc M mech F1 u * w u ≤
          ∫ u in ((⋃ I ∈ L, Ioo I.α I.β) ∩ Icc v 1), (F1 u) ^ (M.n - 1) * w u := by
      intro L
      induction L with
      | nil => intro _ _; simp
      | cons I L ih =>
        intro hLin hLpw
        rw [List.pairwise_cons] at hLpw
        have hUeq : (⋃ J ∈ I :: L, Ioo J.α J.β) ∩ Icc v 1 =
            (Ioo I.α I.β ∩ Icc v 1) ∪ ((⋃ J ∈ L, Ioo J.α J.β) ∩ Icc v 1) := by
          ext u; simp [or_and_right]
        rw [hUeq]
        have hdisj : Disjoint (Ioo I.α I.β ∩ Icc v 1) ((⋃ J ∈ L, Ioo J.α J.β) ∩ Icc v 1) := by
          rw [Set.disjoint_left]
          rintro u ⟨hu1, _⟩ ⟨hu2, _⟩
          simp only [mem_iUnion, mem_Ioo] at hu2
          obtain ⟨J, hJ, hJu⟩ := hu2
          rcases hLpw.1 J hJ with h | h
          · linarith [hu1.2, hJu.1]
          · linarith [hJu.2, hu1.1]
        have hmeas2 : MeasurableSet ((⋃ J ∈ L, Ioo J.α J.β) ∩ Icc v 1) :=
          (hmeas_U L).inter measurableSet_Icc
        rw [setIntegral_union hdisj hmeas2 (hx_int.mono_set inter_subset_right) (hx_int.mono_set inter_subset_right),
            setIntegral_union hdisj hmeas2 (hpow_int.mono_set inter_subset_right) (hpow_int.mono_set inter_subset_right)]
        exact add_le_add (hpool_le I (hLin I List.mem_cons_self))
          (ih (fun J hJ => hLin J (List.mem_cons_of_mem I hJ)) hLpw.2)
    exact hsum_le mech.pools (fun _ h => h) mech.hpools_disj

/-- **Border's Equality for a Hierarchical Mechanism**:
Equality holds in `hierarchical_border_le` at `v ∈ [M.a, 1]` whenever:
(1) `θ.θ j = 0` a.e. on `[v, mech.r]` (automatic if `mech.r ≤ v`), and
(2) no pool straddles `v` with positive mass below `v` (automatic if `v = M.a`, or if `v`
    lies outside all open pools). -/
theorem hierarchical_border_eq (M : Market) (mech : HierarchicalMech)
    (θ : VisitStrategy M) (j : Fin M.m) {v : ℝ} (hv : v ∈ Icc M.a 1)
    (hbelow_r : ∀ᵐ u ∂(volume.restrict (Icc v mech.r)), θ.θ j u = 0)
    (hnopool : ∀ I ∈ mech.pools, I.α < v → v < I.β → effDist M θ j I.α = effDist M θ j v) :
    ∫ u in v..1, alloc M mech (effDist M θ j) u * (θ.θ j u * M.f u) =
      h_n M.n (1 - effDist M θ j v) := by
  let F1 := effDist M θ j
  let w : ℝ → ℝ := fun u => θ.θ j u * M.f u
  have hw_int : IntegrableOn w (Icc v 1) :=
    (visit_mul_f_integrableOn M θ j).mono_set (Icc_subset_Icc_left hv.1)
  have hw_nn : ∀ u ∈ Icc v 1, 0 ≤ w u := fun u hu =>
    mul_nonneg (θ.hnonneg j u) (M.hf_pos u ⟨le_trans hv.1 hu.1, hu.2⟩).le
  have hF1_mono : MonotoneOn F1 (Iic 1) := effDist_monotoneOn M θ j
  have hF1_mem : ∀ u ≤ 1, F1 u ∈ Icc (0 : ℝ) 1 := fun u hu => effDist_mem_Icc M θ j hu
  have hx_mono : MonotoneOn (alloc M mech F1) (Iic 1) := alloc_monotoneOn M mech hF1_mono hF1_mem
  have hx_int : IntegrableOn (fun u => alloc M mech F1 u * w u) (Icc v 1) := by
    have hxm : AEStronglyMeasurable (alloc M mech F1) (volume.restrict (Icc v 1)) :=
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hv.2).mp
        ((hx_mono.mono (by rw [uIcc_of_le hv.2]; exact fun u hu => hu.2)).intervalIntegrable)).aestronglyMeasurable
    refine hw_int.mono' (hxm.mul hw_int.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    have hxu := alloc_mem_Icc M mech hF1_mono hF1_mem hu.2
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hxu.1 (hw_nn u hu))]
    nlinarith [hxu.2, hw_nn u hu]
  have hpow_int : IntegrableOn (fun u => (F1 u) ^ (M.n - 1) * w u) (Icc v 1) := by
    have hFm : AEStronglyMeasurable (fun u => (F1 u) ^ (M.n - 1)) (volume.restrict (Icc v 1)) := by
      have h1 : AEStronglyMeasurable F1 (volume.restrict (Icc v 1)) :=
        ((intervalIntegrable_iff_integrableOn_Icc_of_le hv.2).mp
          ((hF1_mono.mono (by rw [uIcc_of_le hv.2]; exact fun u hu => hu.2)).intervalIntegrable)).aestronglyMeasurable
      exact h1.pow (M.n - 1)
    refine hw_int.mono' (hFm.mul hw_int.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    have hFu := hF1_mem u hu.2
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hFu.1 _) (hw_nn u hu))]
    nlinarith [pow_le_one₀ (n := M.n - 1) hFu.1 hFu.2, hw_nn u hu]
  have htop_eq : ∫ u in v..1, (F1 u) ^ (M.n - 1) * w u = h_n M.n (1 - F1 v) := by
    have hch := pow_sub_pow_eq_integral_antitone (c := 1) hv.2 (M.n - 1) hw_int hw_nn
    have hn_eq : M.n - 1 + 1 = M.n := by have := M.hn; omega
    rw [hn_eq, one_pow] at hch
    have hF1_eq : ∀ u, 1 - ∫ s in u..1, w s = F1 u := fun _ => rfl
    simp_rw [hF1_eq] at hch
    unfold h_n
    rw [show 1 - (1 - F1 v) = F1 v by ring, eq_div_iff M.n_pos_real.ne', mul_comm]
    exact hch
  rw [← htop_eq, intervalIntegral.integral_of_le hv.2, intervalIntegral.integral_of_le hv.2,
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc]
  have hmeas_U : ∀ (L : List Pool), MeasurableSet (⋃ I ∈ L, Ioo I.α I.β) := by
    intro L
    induction L with
    | nil => simp
    | cons I L ih =>
      have : (⋃ J ∈ I :: L, Ioo J.α J.β) = Ioo I.α I.β ∪ ⋃ J ∈ L, Ioo J.α J.β := by ext x; simp
      rw [this]; exact measurableSet_Ioo.union ih
  let U : Set ℝ := (⋃ I ∈ mech.pools, Ioo I.α I.β) ∩ Icc v 1
  have hU_meas : MeasurableSet U := (hmeas_U mech.pools).inter measurableSet_Icc
  have hU_sub : U ⊆ Icc v 1 := inter_subset_right
  have hsplit_set : Icc v 1 = (Icc v 1 \ U) ∪ U := (sdiff_union_of_subset hU_sub).symm
  rw [hsplit_set, setIntegral_union disjoint_sdiff_self_left hU_meas
        (hx_int.mono_set sdiff_subset) (hx_int.mono_set hU_sub),
      setIntegral_union disjoint_sdiff_self_left hU_meas
        (hpow_int.mono_set sdiff_subset) (hpow_int.mono_set hU_sub)]
  congr 1
  · -- Off the pools: equal a.e. because `θ.θ j = 0` a.e. on `[v, mech.r]`
    refine setIntegral_congr_ae (measurableSet_Icc.diff hU_meas) ?_
    rw [ae_restrict_iff' measurableSet_Icc] at hbelow_r
    filter_upwards [hbelow_r] with u hu hmem
    have hnot_pool : ∀ I ∈ mech.pools, ¬(I.α < u ∧ u < I.β) := by
      intro I hI hlt
      exact hmem.2 ⟨Set.mem_iUnion₂.mpr ⟨I, hI, hlt⟩, hmem.1⟩
    have hfind : mech.pools.find? (fun I => decide (I.α < u ∧ u < I.β)) = none := by
      rw [List.find?_eq_none]
      intro I hI; simp [hnot_pool I hI]
    unfold alloc
    split_ifs with hlt
    · have hθ0 : θ.θ j u = 0 := hu ⟨hmem.1.1, hlt.le⟩
      simp [w, hθ0]
    · rw [hfind]
  · -- On the pools: equal on each pool because `F1 I.α = F1 (max v I.α)`
    have hpool_eq : ∀ I ∈ mech.pools,
        ∫ u in (Ioo I.α I.β ∩ Icc v 1), alloc M mech F1 u * w u =
          ∫ u in (Ioo I.α I.β ∩ Icc v 1), (F1 u) ^ (M.n - 1) * w u := by
      intro I hI
      have hI_in := mech.hpools_in I hI
      rcases le_or_gt I.β v with hβv | hvβ
      · have hemp : Ioo I.α I.β ∩ Icc v 1 = ∅ := by
          ext u; simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
          intro h1 h2; linarith [h1.2, h2.1]
        rw [hemp]; simp
      · let c := max v I.α
        have hc_lt : c < I.β := max_lt hvβ I.hαβ
        have hc_ge_v : v ≤ c := le_max_left _ _
        have hc_ge_α : I.α ≤ c := le_max_right _ _
        have hF_eq_αc : F1 I.α = F1 c := by
          rcases le_total v I.α with hle | hlt
          · simp [c, max_eq_right hle]
          · rcases eq_or_lt_of_le hlt with rfl | hlt'
            · simp [c]
            · rw [show c = v from max_eq_left hlt'.le]
              exact hnopool I hI hlt' hvβ
        have hae_set : (Ioo I.α I.β ∩ Icc v 1 : Set ℝ) =ᵐ[volume] Ioo c I.β := by
          rw [ae_eq_set]
          constructor
          · refine measure_mono_null ?_ (measure_singleton v)
            intro u ⟨⟨⟨h1, h2⟩, ⟨h3, _⟩⟩, hnot⟩
            simp only [mem_singleton_iff]
            rcases eq_or_lt_of_le h3 with rfl | hlt
            · rfl
            · exfalso; exact hnot ⟨max_lt hlt h1, h2⟩
          · refine measure_mono_null ?_ measure_empty
            intro u ⟨⟨h1, h2⟩, hnot⟩
            exfalso
            exact hnot ⟨⟨lt_of_le_of_lt hc_ge_α h1, h2⟩,
              ⟨le_trans hc_ge_v h1.le, le_trans h2.le hI_in.2⟩⟩
        rw [setIntegral_congr_set hae_set, setIntegral_congr_set hae_set]
        have halloc_eq : EqOn (fun u => alloc M mech F1 u * w u)
            (fun u => poolAvg M.n (F1 I.α) (F1 I.β) * w u) (Ioo c I.β) := by
          intro u hu
          have huI : I.α < u ∧ u < I.β := ⟨lt_of_le_of_lt hc_ge_α hu.1, hu.2⟩
          have hu_ge_r : ¬(u < mech.r) := not_lt.mpr (le_trans hI_in.1 huI.1.le)
          have hfind : mech.pools.find? (fun J => decide (J.α < u ∧ u < J.β)) = some I := by
            obtain ⟨J, hJ⟩ : ∃ J, mech.pools.find? (fun J => decide (J.α < u ∧ u < J.β)) = some J := by
              rcases Option.eq_none_or_eq_some (mech.pools.find? (fun J => decide (J.α < u ∧ u < J.β))) with hnone | ⟨J, hJ⟩
              · exfalso
                have := List.find?_eq_none.mp hnone I hI
                simp [huI] at this
              · exact ⟨J, hJ⟩
            have hJ_mem := List.mem_of_find?_eq_some hJ
            have hJ_pred : J.α < u ∧ u < J.β := by have := List.find?_some hJ; simpa using this
            have hJI : J = I := by
              by_contra hne
              rcases list_pairwise_symm (fun _ _ h => Or.symm h) mech.hpools_disj J hJ_mem I hI hne with h1 | h2
              · linarith [hJ_pred.2, huI.1]
              · linarith [huI.2, hJ_pred.1]
            rwa [hJI] at hJ
          dsimp only [alloc]
          rw [ite_eq_right_iff.mpr (fun h => absurd h hu_ge_r), hfind]
        rw [setIntegral_congr_fun measurableSet_Ioo halloc_eq, integral_const_mul,
          ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hc_lt.le,
          ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hc_lt.le]
        have hw_cβ : IntegrableOn w (Icc c I.β) :=
          hw_int.mono_set (Icc_subset_Icc hc_ge_v hI_in.2)
        have hw_cβ_nn : ∀ u ∈ Icc c I.β, 0 ≤ w u := fun u hu =>
          hw_nn u ⟨le_trans hc_ge_v hu.1, le_trans hu.2 hI_in.2⟩
        have hint_w_eq : ∫ u in c..I.β, w u = F1 I.β - F1 c := by
          have hw_ivl := (intervalIntegrable_iff_integrableOn_Icc_of_le hv.2).mpr hw_int
          have hsplit := intervalIntegral.integral_add_adjacent_intervals
            (hw_ivl.mono_set (uIcc_subset_uIcc (mem_uIcc_of_le hc_ge_v (le_trans hc_lt.le hI_in.2))
              (mem_uIcc_of_le (le_trans hc_ge_v hc_lt.le) hI_in.2)))
            (hw_ivl.mono_set (uIcc_subset_uIcc (mem_uIcc_of_le (le_trans hc_ge_v hc_lt.le) hI_in.2) right_mem_uIcc))
          show ∫ u in c..I.β, w u = (1 - ∫ u in I.β..1, w u) - (1 - ∫ u in c..1, w u)
          linarith
        have hint_pow_eq : ∫ u in c..I.β, (F1 u) ^ (M.n - 1) * w u =
            ((F1 I.β) ^ M.n - (F1 c) ^ M.n) / (M.n : ℝ) := by
          have hch := pow_sub_pow_eq_integral_antitone (c := F1 I.β) hc_lt.le (M.n - 1) hw_cβ hw_cβ_nn
          have hn_eq : M.n - 1 + 1 = M.n := by have := M.hn; omega
          rw [hn_eq] at hch
          have hF_shift : ∀ u ∈ Icc c I.β, F1 I.β - ∫ s in u..I.β, w s = F1 u := by
            intro u hu
            have hw_ivl := (intervalIntegrable_iff_integrableOn_Icc_of_le hv.2).mpr hw_int
            have hsplit := intervalIntegral.integral_add_adjacent_intervals
              (hw_ivl.mono_set (uIcc_subset_uIcc (mem_uIcc_of_le (le_trans hc_ge_v hu.1) (le_trans hu.2 hI_in.2))
                (mem_uIcc_of_le (le_trans hc_ge_v hc_lt.le) hI_in.2)))
              (hw_ivl.mono_set (uIcc_subset_uIcc (mem_uIcc_of_le (le_trans hc_ge_v hc_lt.le) hI_in.2) right_mem_uIcc))
            show (1 - ∫ s in I.β..1, w s) - ∫ s in u..I.β, w s = 1 - ∫ s in u..1, w s
            linarith
          have hcongr : ∫ u in c..I.β, (F1 I.β - ∫ s in u..I.β, w s) ^ (M.n - 1) * w u =
              ∫ u in c..I.β, (F1 u) ^ (M.n - 1) * w u := by
            rw [intervalIntegral.integral_of_le hc_lt.le, intervalIntegral.integral_of_le hc_lt.le,
              ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc]
            refine setIntegral_congr_fun measurableSet_Icc (fun u hu => by rw [hF_shift u hu])
          rw [hcongr, hF_shift c (left_mem_Icc.mpr hc_lt.le)] at hch
          rw [eq_div_iff M.n_pos_real.ne', mul_comm]
          exact hch
        have hn1 : 1 ≤ M.n := by have := M.hn; omega
        rw [hint_w_eq, hint_pow_eq, hF_eq_αc, poolAvg_mul_sub hn1 (F1 c) (F1 I.β)]
    have hsum_eq : ∀ (L : List Pool),
        (∀ I ∈ L, I ∈ mech.pools) →
        L.Pairwise (fun I J => I.β ≤ J.α ∨ J.β ≤ I.α) →
        ∫ u in ((⋃ I ∈ L, Ioo I.α I.β) ∩ Icc v 1), alloc M mech F1 u * w u =
          ∫ u in ((⋃ I ∈ L, Ioo I.α I.β) ∩ Icc v 1), (F1 u) ^ (M.n - 1) * w u := by
      intro L
      induction L with
      | nil => intro _ _; simp
      | cons I L ih =>
        intro hLin hLpw
        rw [List.pairwise_cons] at hLpw
        have hUeq : (⋃ J ∈ I :: L, Ioo J.α J.β) ∩ Icc v 1 =
            (Ioo I.α I.β ∩ Icc v 1) ∪ ((⋃ J ∈ L, Ioo J.α J.β) ∩ Icc v 1) := by
          ext u; simp [or_and_right]
        rw [hUeq]
        have hdisj : Disjoint (Ioo I.α I.β ∩ Icc v 1) ((⋃ J ∈ L, Ioo J.α J.β) ∩ Icc v 1) := by
          rw [Set.disjoint_left]
          rintro u ⟨hu1, _⟩ ⟨hu2, _⟩
          simp only [mem_iUnion, mem_Ioo] at hu2
          obtain ⟨J, hJ, hJu⟩ := hu2
          rcases hLpw.1 J hJ with h | h
          · linarith [hu1.2, hJu.1]
          · linarith [hJu.2, hu1.1]
        have hmeas2 : MeasurableSet ((⋃ J ∈ L, Ioo J.α J.β) ∩ Icc v 1) :=
          (hmeas_U L).inter measurableSet_Icc
        rw [setIntegral_union hdisj hmeas2 (hx_int.mono_set inter_subset_right) (hx_int.mono_set inter_subset_right),
            setIntegral_union hdisj hmeas2 (hpow_int.mono_set inter_subset_right) (hpow_int.mono_set inter_subset_right),
            hpool_eq I (hLin I List.mem_cons_self),
            ih (fun J hJ => hLin J (List.mem_cons_of_mem I hJ)) hLpw.2]
    exact hsum_eq mech.pools (fun _ h => h) mech.hpools_disj

/-! ### Section 4B: Proposition 3 and Lemma B.1 (Quantity-Path Representation & Rent Bound) -/

/-- A localized sequentially rational continuation after seller `j0` deviates to `mech`
while all `m - 1` rivals post `SPA(ρ)` (summarizing Proposition 2(i)–(iii) in Section 3.2).

Note that `hs_below` and `hs_vhat_eq` are gated by `max (min mech.r ρ) M.a < v_hat` (so the
structure is satisfiable when the initial strict-preference segment is empty, `v_hat = v_bar`,
e.g. covered-market reserve increases where `s_1(a) < s_riv(a)` strictly), and `hs_vhat_eq`
additionally requires `v_hat < 1` so the corner case `v_hat = 1` with `σ(1) > 0` is included. -/
structure UnilateralContinuation (M : Market) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (mech : HierarchicalMech) where
  j0 : Fin M.m
  θ : VisitStrategy M
  F_riv : ℝ → ℝ
  hriv_symm : ∀ j : Fin M.m, j ≠ j0 → ∀ v ∈ Icc ρ 1, effDist M θ j v = F_riv v
  v_hat : ℝ
  hv_hat_mem : v_hat ∈ Icc (max (min mech.r ρ) M.a) 1
  hρ_le_vhat : ρ ≤ v_hat
  hθ_below_vhat : ∀ᵐ v ∂(volume.restrict (Icc (max (min mech.r ρ) M.a) v_hat)), θ.θ j0 v = 1
  hθ_below_r : ∀ᵐ v ∂(volume.restrict (Icc (max (min mech.r ρ) M.a) mech.r)), θ.θ j0 v = 0
  hs_below : max (min mech.r ρ) M.a < v_hat → ∀ v ∈ Icc (max (min mech.r ρ) M.a) v_hat,
    surplus M (SPA ρ hρ0 hρ1.le) F_riv v ≤ surplus M mech (effDist M θ j0) v
  hs_vhat_eq : max (min mech.r ρ) M.a < v_hat → v_hat < 1 →
    surplus M mech (effDist M θ j0) v_hat = surplus M (SPA ρ hρ0 hρ1.le) F_riv v_hat
  hs_above : ∀ᵐ v ∂(volume.restrict (Icc v_hat 1)),
    0 < θ.θ j0 v → surplus M mech (effDist M θ j0) v = surplus M (SPA ρ hρ0 hρ1.le) F_riv v
  hx_above : ∀ᵐ v ∂(volume.restrict (Icc v_hat 1)),
    0 < θ.θ j0 v → alloc M mech (effDist M θ j0) v = (F_riv v) ^ (M.n - 1)

namespace UnilateralContinuation

variable {M : Market} {ρ : ℝ} {hρ0 : 0 ≤ ρ} {hρ1 : ρ < 1} {mech : HierarchicalMech}
variable (C : UnilateralContinuation M ρ hρ0 hρ1 mech)

/-- Bottom active type `v_bar = max (min r_1 ρ) a`. -/
def v_bar (_C : UnilateralContinuation M ρ hρ0 hρ1 mech) : ℝ := max (min mech.r ρ) M.a

lemma v_bar_mem_Icc (C : UnilateralContinuation M ρ hρ0 hρ1 mech) : C.v_bar ∈ Icc M.a 1 :=
  ⟨le_max_right _ _, max_le (le_trans (min_le_right _ _) hρ1.le) M.ha1.le⟩

lemma v_bar_le_v_hat : C.v_bar ≤ C.v_hat := C.hv_hat_mem.1

lemma v_hat_mem_Icc_a : C.v_hat ∈ Icc M.a 1 :=
  ⟨le_trans C.v_bar_mem_Icc.1 C.hv_hat_mem.1, C.hv_hat_mem.2⟩

/-- Seller 1's effective distribution `F_1`. -/
noncomputable def F1 (v : ℝ) : ℝ := effDist M C.θ C.j0 v

/-- Seller 1's upper-tail quantity `T(v) = 1 - F_1(v)`. -/
noncomputable def T (v : ℝ) : ℝ := 1 - C.F1 v

/-- Common rival upper-tail quantity `q(v) = 1 - F_riv(v)`. -/
noncomputable def q (v : ℝ) : ℝ := 1 - C.F_riv v

/-- Seller 1's visitor density `w1(v) = θ_1(v) f(v)`. -/
noncomputable def w1 (v : ℝ) : ℝ := C.θ.θ C.j0 v * M.f v

/-- Per-rival visitor density `w_riv(v) = ((1 - θ_1(v)) / (m - 1)) f(v)`. -/
noncomputable def w_riv (v : ℝ) : ℝ := ((1 - C.θ.θ C.j0 v) / ((M.m : ℝ) - 1)) * M.f v

/-- Final rival traffic `q0 = q(v_hat)`. -/
noncomputable def q0 : ℝ := C.q C.v_hat

/-- Final seller 1 traffic `t0 = T(v_bar)`. -/
noncomputable def t0 : ℝ := C.T C.v_bar

/-- Generalized inverse `v(q) = inf {v ∈ [v_hat, 1] | q(v) ≤ q}`. -/
noncomputable def vOfQ (qval : ℝ) : ℝ := sInf {v ∈ Icc C.v_hat 1 | C.q v ≤ qval}

/-- Quantity path `t(q) = T(v(q))`. -/
noncomputable def t (qval : ℝ) : ℝ := C.T (C.vOfQ qval)

/-- Extra rent `ℓ` left to strictly preferring buyers on `[v_bar, v_hat)` (Lemma B.1). -/
noncomputable def ell : ℝ :=
  (M.n : ℝ) * ρ * (1 - C.q0) ^ (M.n - 1) * (C.t0 - C.T C.v_hat) -
    (M.n : ℝ) * ∫ v in C.v_bar..C.v_hat, payment M mech C.F1 v * C.w1 v

lemma exists_rival : ∃ j : Fin M.m, j ≠ C.j0 := by
  have hm : 2 ≤ M.m := M.hm
  by_cases h0 : C.j0.1 = 0
  · refine ⟨⟨1, by omega⟩, ?_⟩
    intro heq
    have := congrArg Fin.val heq
    simp [h0] at this
  · refine ⟨⟨0, by omega⟩, ?_⟩
    intro heq
    have := congrArg Fin.val heq
    exact h0 this.symm

lemma w1_integrableOn : IntegrableOn C.w1 (Icc M.a 1) :=
  visit_mul_f_integrableOn M C.θ C.j0

lemma w1_nonneg {v : ℝ} (hv : v ∈ Icc M.a 1) : 0 ≤ C.w1 v :=
  mul_nonneg (C.θ.hnonneg C.j0 v) (M.hf_pos v hv).le

lemma w_riv_integrableOn : IntegrableOn C.w_riv (Icc M.a 1) := by
  have heq : C.w_riv = fun v => (1 / ((M.m : ℝ) - 1)) * (M.f v - C.w1 v) := by
    ext v; unfold w_riv w1; ring
  rw [heq]
  exact ((f_integrableOn M).sub C.w1_integrableOn).const_mul _

lemma w_riv_nonneg {v : ℝ} (hv : v ∈ Icc M.a 1) : 0 ≤ C.w_riv v := by
  unfold w_riv
  have h1 : 0 ≤ 1 - C.θ.θ C.j0 v := sub_nonneg.mpr (visit_le_one M C.θ C.j0 hv)
  have h2 : 0 < (M.m : ℝ) - 1 := M.m_sub_one_pos_real
  have h3 : 0 ≤ M.f v := (M.hf_pos v hv).le
  exact mul_nonneg (div_nonneg h1 h2.le) h3

/-- Mass conservation on `[max ρ a, 1]`: `T(v) + (m - 1) q(v) = 1 - F(v)`. -/
lemma mass_conservation {v : ℝ} (hv_a : v ∈ Icc M.a 1) (hv_ρ : ρ ≤ v) :
    C.T v + ((M.m : ℝ) - 1) * C.q v = 1 - M.F v := by
  have hsum := sum_one_sub_effDist M C.θ hv_a
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ C.j0)] at hsum
  have hriv_sum : ∑ j ∈ Finset.univ.erase C.j0, (1 - effDist M C.θ j v) =
      ((M.m : ℝ) - 1) * C.q v := by
    have hcongr : ∀ j ∈ Finset.univ.erase C.j0, 1 - effDist M C.θ j v = C.q v := by
      intro j hj
      have hne : j ≠ C.j0 := Finset.ne_of_mem_erase hj
      simp only [q, C.hriv_symm j hne v ⟨hv_ρ, hv_a.2⟩]
    rw [Finset.sum_congr rfl hcongr, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    congr 1
    rw [Nat.cast_sub (by have := M.hm; omega), Nat.cast_one]
  rw [hriv_sum] at hsum
  exact hsum

/-- On `[max ρ a, 1]`, `q(v) = ∫ u in v..1, w_riv u`. -/
lemma q_eq_integral_w_riv {v : ℝ} (hv_a : v ∈ Icc M.a 1) (hv_ρ : ρ ≤ v) :
    C.q v = ∫ u in v..1, C.w_riv u := by
  have hmass := C.mass_conservation hv_a hv_ρ
  have hF : 1 - M.F v = ∫ u in v..1, M.f u := (integral_f_eq_sub_F M hv_a).symm
  have hT : C.T v = ∫ u in v..1, C.w1 u := by unfold T F1 effDist w1; ring
  have hm1_ne : ((M.m : ℝ) - 1) ≠ 0 := M.m_sub_one_pos_real.ne'
  have hint_f : IntervalIntegrable M.f volume v 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hv_a.2).mpr
      ((f_integrableOn M).mono_set (Icc_subset_Icc_left hv_a.1))
  have hint_w1 : IntervalIntegrable C.w1 volume v 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hv_a.2).mpr
      (C.w1_integrableOn.mono_set (Icc_subset_Icc_left hv_a.1))
  have hwriv : ∫ u in v..1, C.w_riv u =
      (1 / ((M.m : ℝ) - 1)) * ((∫ u in v..1, M.f u) - (∫ u in v..1, C.w1 u)) := by
    have heq : C.w_riv = fun u => (1 / ((M.m : ℝ) - 1)) * (M.f u - C.w1 u) := by
      ext u; unfold w_riv w1; ring
    rw [heq, intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hint_f hint_w1]
  rw [hwriv, ← hF, ← hT]
  field_simp [hm1_ne]
  linarith

lemma F_riv_const_on_rho_vhat {v : ℝ} (hv : v ∈ Icc ρ C.v_hat) :
    C.F_riv v = 1 - C.q0 := by
  obtain ⟨j, hj⟩ := C.exists_rival
  have hv_le1 : v ≤ 1 := le_trans hv.2 C.hv_hat_mem.2
  rw [← C.hriv_symm j hj v ⟨hv.1, hv_le1⟩]
  have hvhat_eq : 1 - C.q0 = effDist M C.θ j C.v_hat := by
    unfold q0 q
    rw [C.hriv_symm j hj C.v_hat ⟨C.hρ_le_vhat, C.hv_hat_mem.2⟩]; ring
  rw [hvhat_eq]
  -- Show `∫ u in v..v_hat, θ_j u * f u = 0`
  have hzero : ∫ u in v..C.v_hat, C.θ.θ j u * M.f u = 0 := by
    rw [intervalIntegral.integral_of_le hv.2, ← integral_Icc_eq_integral_Ioc]
    have hae : ∀ᵐ u ∂(volume.restrict (Icc v C.v_hat)), C.θ.θ j u * M.f u = 0 := by
      have hbelow := C.hθ_below_vhat
      rw [ae_restrict_iff' measurableSet_Icc] at hbelow ⊢
      filter_upwards [hbelow] with u hu hmem
      rcases lt_or_ge u C.v_bar with hlt | hge
      · -- `u < v_bar`: since `v ≥ ρ`, `u ≥ ρ`, so `v_bar > ρ`, hence `v_bar = M.a`, so `u < M.a` and `f u = 0`!
        have hu_lt_a : u < M.a := by
          have hvbar_gt_ρ : ρ < C.v_bar := lt_of_le_of_lt (le_trans hv.1 hmem.1) hlt
          have hvbar_eq_a : C.v_bar = M.a := by
            unfold v_bar at hvbar_gt_ρ ⊢
            have hmin : min mech.r ρ ≤ ρ := min_le_right _ _
            exact max_eq_right (by by_contra h; push Not at h; rw [max_eq_left h.le] at hvbar_gt_ρ; linarith)
          rwa [← hvbar_eq_a]
        simp [M.hf_below u hu_lt_a]
      · -- `v_bar ≤ u ≤ v_hat`: `θ_j0 u = 1`, hence `θ_j u = 0`
        have hu_a : u ∈ Icc M.a 1 :=
          ⟨le_trans C.v_bar_mem_Icc.1 hge, le_trans hmem.2 C.hv_hat_mem.2⟩
        have h1 : C.θ.θ C.j0 u = 1 := hu ⟨hge, hmem.2⟩
        have hsum := C.θ.hsum u hu_a
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ C.j0), h1] at hsum
        have hrest : ∑ k ∈ Finset.univ.erase C.j0, C.θ.θ k u = 0 := by linarith
        have hj_mem : j ∈ Finset.univ.erase C.j0 := Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩
        have hle : C.θ.θ j u ≤ ∑ k ∈ Finset.univ.erase C.j0, C.θ.θ k u :=
          Finset.single_le_sum (fun k _ => C.θ.hnonneg k u) hj_mem
        have hj0 : C.θ.θ j u = 0 := le_antisymm (by linarith) (C.θ.hnonneg j u)
        simp [hj0]
    rw [integral_congr_ae hae]; simp
  unfold effDist
  congr 1
  have hint_a1 : IntervalIntegrable (fun u => C.θ.θ j u * M.f u) volume M.a 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le M.ha1.le).mpr (visit_mul_f_integrableOn M C.θ j)
  have hint_v_vh : IntervalIntegrable (fun u => C.θ.θ j u * M.f u) volume v C.v_hat := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hv.2]
    have hae : ∀ᵐ u ∂(volume.restrict (Icc v C.v_hat)), C.θ.θ j u * M.f u = 0 := by
      have hbelow := C.hθ_below_vhat
      rw [ae_restrict_iff' measurableSet_Icc] at hbelow ⊢
      filter_upwards [hbelow] with u hu hmem
      rcases lt_or_ge u C.v_bar with hlt | hge
      · have hu_lt_a : u < M.a := by
          have hvbar_gt_ρ : ρ < C.v_bar := lt_of_le_of_lt (le_trans hv.1 hmem.1) hlt
          have hvbar_eq_a : C.v_bar = M.a := by
            unfold v_bar at hvbar_gt_ρ ⊢
            have hmin : min mech.r ρ ≤ ρ := min_le_right _ _
            exact max_eq_right (by by_contra h; push Not at h; rw [max_eq_left h.le] at hvbar_gt_ρ; linarith)
          rwa [← hvbar_eq_a]
        simp [M.hf_below u hu_lt_a]
      · have hu_a : u ∈ Icc M.a 1 :=
          ⟨le_trans C.v_bar_mem_Icc.1 hge, le_trans hmem.2 C.hv_hat_mem.2⟩
        have h1 : C.θ.θ C.j0 u = 1 := hu ⟨hge, hmem.2⟩
        have hsum := C.θ.hsum u hu_a
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ C.j0), h1] at hsum
        have hj_mem : j ∈ Finset.univ.erase C.j0 := Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩
        have hle : C.θ.θ j u ≤ ∑ k ∈ Finset.univ.erase C.j0, C.θ.θ k u :=
          Finset.single_le_sum (fun k _ => C.θ.hnonneg k u) hj_mem
        have hj0 : C.θ.θ j u = 0 := le_antisymm (by linarith) (C.θ.hnonneg j u)
        simp [hj0]
    have hae' : (0 : ℝ → ℝ) =ᵐ[volume.restrict (Icc v C.v_hat)] fun u => C.θ.θ j u * M.f u := by
      filter_upwards [hae] with u hu; exact hu.symm
    exact (integrableOn_zero : IntegrableOn (0 : ℝ → ℝ) (Icc v C.v_hat)).congr hae'
  have hint_vh_1 : IntervalIntegrable (fun u => C.θ.θ j u * M.f u) volume C.v_hat 1 :=
    hint_a1.mono_set (uIcc_subset_uIcc (mem_uIcc_of_le C.v_hat_mem_Icc_a.1 C.v_hat_mem_Icc_a.2) right_mem_uIcc)
  rw [← intervalIntegral.integral_add_adjacent_intervals hint_v_vh hint_vh_1, hzero, zero_add]

lemma s_riv_on_rho_vhat {v : ℝ} (hv : v ∈ Icc ρ C.v_hat) :
    surplus M (SPA ρ hρ0 hρ1.le) C.F_riv v = (v - ρ) * (1 - C.q0) ^ (M.n - 1) := by
  unfold surplus
  have hpart1 : ∫ u in (0 : ℝ)..ρ, alloc M (SPA ρ hρ0 hρ1.le) C.F_riv u = 0 := by
    rw [intervalIntegral.integral_of_le hρ0, integral_Ioc_eq_integral_Ioo]
    have h0 : EqOn (alloc M (SPA ρ hρ0 hρ1.le) C.F_riv) 0 (Ioo 0 ρ) := by
      intro u hu; simp [alloc_SPA_eq, hu.2]
    rw [setIntegral_congr_fun measurableSet_Ioo h0]; simp
  have hpart2 : ∫ u in ρ..v, alloc M (SPA ρ hρ0 hρ1.le) C.F_riv u =
      (v - ρ) * (1 - C.q0) ^ (M.n - 1) := by
    rw [intervalIntegral.integral_of_le hv.1]
    have hconst : EqOn (alloc M (SPA ρ hρ0 hρ1.le) C.F_riv) (fun _ => (1 - C.q0) ^ (M.n - 1)) (Ioc ρ v) := by
      intro u hu
      rw [alloc_SPA_eq, ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr hu.1.le))]
      rw [C.F_riv_const_on_rho_vhat ⟨hu.1.le, le_trans hu.2 hv.2⟩]
    rw [setIntegral_congr_fun measurableSet_Ioc hconst, ← intervalIntegral.integral_of_le hv.1,
      intervalIntegral.integral_const, smul_eq_mul]
  have hint1 : IntervalIntegrable (alloc M (SPA ρ hρ0 hρ1.le) C.F_riv) volume 0 ρ := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hρ0]
    have h0 : EqOn (alloc M (SPA ρ hρ0 hρ1.le) C.F_riv) 0 (Ioo 0 ρ) := by
      intro u hu; simp [alloc_SPA_eq, hu.2]
    exact (integrableOn_zero : IntegrableOn (0 : ℝ → ℝ) (Ioo 0 ρ)).congr_fun
      (fun u hu => (h0 hu).symm) measurableSet_Ioo
  have hint2 : IntervalIntegrable (alloc M (SPA ρ hρ0 hρ1.le) C.F_riv) volume ρ v := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hv.1]
    have hconst : EqOn (alloc M (SPA ρ hρ0 hρ1.le) C.F_riv) (fun _ => (1 - C.q0) ^ (M.n - 1)) (Ioc ρ v) := by
      intro u hu
      rw [alloc_SPA_eq, ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr hu.1.le))]
      rw [C.F_riv_const_on_rho_vhat ⟨hu.1.le, le_trans hu.2 hv.2⟩]
    exact (integrableOn_const (hs := measure_Ioc_lt_top.ne)).congr_fun
      (fun u hu => (hconst hu).symm) measurableSet_Ioc
  rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2, hpart1, zero_add, hpart2]

lemma q0_mem_Icc : C.q0 ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨j, hj⟩ := C.exists_rival
  have hF := effDist_mem_Icc M C.θ j C.hv_hat_mem.2
  have hq : C.q0 = 1 - effDist M C.θ j C.v_hat := by
    unfold q0 q; rw [C.hriv_symm j hj C.v_hat ⟨C.hρ_le_vhat, C.hv_hat_mem.2⟩]
  rw [hq]
  exact ⟨by linarith [hF.2], by linarith [hF.1]⟩

lemma t0_mem_Icc : C.t0 ∈ Icc (0 : ℝ) 1 := by
  have hF := effDist_mem_Icc M C.θ C.j0 C.v_bar_mem_Icc.2
  unfold t0 T F1
  exact ⟨by linarith [hF.2], by linarith [hF.1]⟩

lemma q_continuousOn_vhat : ContinuousOn C.q (Icc C.v_hat 1) := by
  have hcongr : EqOn C.q (fun v => ∫ u in v..1, C.w_riv u) (Icc C.v_hat 1) := fun v hv =>
    C.q_eq_integral_w_riv ⟨le_trans C.v_hat_mem_Icc_a.1 hv.1, hv.2⟩ (le_trans C.hρ_le_vhat hv.1)
  have hw_uIcc : IntegrableOn C.w_riv (uIcc C.v_hat 1) volume := by
    rw [uIcc_of_le C.hv_hat_mem.2]
    exact C.w_riv_integrableOn.mono_set (Icc_subset_Icc_left C.v_hat_mem_Icc_a.1)
  have hcont := intervalIntegral.continuousOn_primitive_interval_left hw_uIcc
  rw [uIcc_of_le C.hv_hat_mem.2] at hcont
  exact hcont.congr hcongr

lemma q_antitoneOn_vhat : AntitoneOn C.q (Icc C.v_hat 1) := by
  obtain ⟨j, hj⟩ := C.exists_rival
  intro v₁ hv₁ v₂ hv₂ hle
  unfold q
  rw [← C.hriv_symm j hj v₁ ⟨le_trans C.hρ_le_vhat hv₁.1, hv₁.2⟩,
      ← C.hriv_symm j hj v₂ ⟨le_trans C.hρ_le_vhat hv₂.1, hv₂.2⟩]
  linarith [effDist_monotoneOn M C.θ j hv₁.2 hv₂.2 hle]

lemma q_one : C.q 1 = 0 := by
  obtain ⟨j, hj⟩ := C.exists_rival
  unfold q
  rw [← C.hriv_symm j hj 1 ⟨hρ1.le, le_rfl⟩, effDist_one]
  ring

lemma vOfQ_spec {qval : ℝ} (hq : qval ∈ Icc (0 : ℝ) C.q0) :
    C.vOfQ qval ∈ Icc C.v_hat 1 ∧ C.q (C.vOfQ qval) = qval := by
  let S : Set ℝ := {v ∈ Icc C.v_hat 1 | C.q v ≤ qval}
  have h1S : (1 : ℝ) ∈ S := ⟨right_mem_Icc.mpr C.hv_hat_mem.2, by rw [C.q_one]; exact hq.1⟩
  have hS_ne : S.Nonempty := ⟨1, h1S⟩
  have hS_bdd : BddBelow S := ⟨C.v_hat, fun v hv => hv.1.1⟩
  have hmem : C.vOfQ qval ∈ Icc C.v_hat 1 :=
    ⟨le_csInf hS_ne (fun v hv => hv.1.1), csInf_le hS_bdd h1S⟩
  have hS_closed : IsClosed S := by
    have : S = Icc C.v_hat 1 ∩ C.q ⁻¹' Iic qval := rfl
    rw [this]
    exact C.q_continuousOn_vhat.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hin : C.vOfQ qval ∈ S := hS_closed.csInf_mem hS_ne hS_bdd
  refine ⟨hmem, ?_⟩
  rcases eq_or_lt_of_le hq.2 with rfl | hlt_q0
  · have hvh_in : C.v_hat ∈ S := ⟨left_mem_Icc.mpr C.hv_hat_mem.2, le_rfl⟩
    have hle : C.vOfQ C.q0 ≤ C.v_hat := csInf_le hS_bdd hvh_in
    have heq : C.vOfQ C.q0 = C.v_hat := le_antisymm hle hmem.1
    rw [heq]; rfl
  · have hgt_vh : C.v_hat < C.vOfQ qval := by
      rcases eq_or_lt_of_le hmem.1 with heq | hlt
      · exfalso; have := hin.2; rw [← heq] at this; exact not_le_of_gt hlt_q0 this
      · exact hlt
    rcases eq_or_lt_of_le hin.2 with heq | hlt
    · exact heq
    · exfalso
      have hev : {v | C.q v < qval} ∈ 𝓝[Icc C.v_hat 1] C.vOfQ qval :=
        (C.q_continuousOn_vhat _ hmem).eventually (gt_mem_nhds hlt)
      rw [Metric.mem_nhdsWithin_iff] at hev
      obtain ⟨δ, hδ, hball⟩ := hev
      let v' := max C.v_hat (C.vOfQ qval - δ / 2)
      have hv'_mem : v' ∈ Icc C.v_hat 1 :=
        ⟨le_max_left _ _, max_le C.hv_hat_mem.2 (by linarith [hmem.2])⟩
      have hv'_lt : v' < C.vOfQ qval := max_lt hgt_vh (by linarith)
      have hv'_ball : v' ∈ Metric.ball (C.vOfQ qval) δ := by
        rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (sub_neg.mpr hv'_lt)]
        linarith [le_max_right C.v_hat (C.vOfQ qval - δ / 2)]
      have hqv' : C.q v' < qval := hball ⟨hv'_ball, hv'_mem⟩
      have : C.vOfQ qval ≤ v' := csInf_le hS_bdd ⟨hv'_mem, hqv'.le⟩
      linarith

lemma t_monotoneOn : MonotoneOn C.t (Icc (0 : ℝ) C.q0) := by
  intro q₁ hq₁ q₂ hq₂ hle
  have hv_anti : C.vOfQ q₂ ≤ C.vOfQ q₁ := by
    apply csInf_le (s := {v ∈ Icc C.v_hat 1 | C.q v ≤ q₂}) ⟨C.v_hat, fun v hv => hv.1.1⟩
    exact ⟨(C.vOfQ_spec hq₁).1, le_trans (C.vOfQ_spec hq₁).2.le hle⟩
  unfold t T F1
  linarith [effDist_monotoneOn M C.θ C.j0 (C.vOfQ_spec hq₂).1.2 (C.vOfQ_spec hq₁).1.2 hv_anti]

lemma t_mem_Icc {qval : ℝ} (hq : qval ∈ Icc (0 : ℝ) C.q0) : C.t qval ∈ Icc (0 : ℝ) C.t0 := by
  have hv := (C.vOfQ_spec hq).1
  unfold t t0 T F1
  have h1 : effDist M C.θ C.j0 (C.vOfQ qval) ≤ 1 := (effDist_mem_Icc M C.θ C.j0 hv.2).2
  have h2 : effDist M C.θ C.j0 C.v_bar ≤ effDist M C.θ C.j0 (C.vOfQ qval) :=
    effDist_monotoneOn M C.θ C.j0 C.v_bar_mem_Icc.2 hv.2 (le_trans C.hv_hat_mem.1 hv.1)
  exact ⟨by linarith, by linarith⟩

/-- Key pushforward identity on `[v, 1]` for any `v ∈ [v_hat, 1]` and any function `Φ(s, T(s), q(s))`:
`∫ s in v..1, Φ s (C.T s) (C.q s) * C.w_riv s = ∫ u in 0..(C.q v), Φ (C.vOfQ u) (C.t u) u`. -/
lemma integral_comp_q_of_v {v : ℝ} (hv : v ∈ Icc C.v_hat 1)
    {Φ : ℝ → ℝ → ℝ → ℝ}
    (hΦ_meas : AEStronglyMeasurable (fun u => Φ (C.vOfQ u) (C.t u) u)
      (volume.restrict (Icc (0 : ℝ) (C.q v)))) :
    ∫ s in v..1, Φ s (C.T s) (C.q s) * C.w_riv s =
      ∫ u in (0 : ℝ)..(C.q v), Φ (C.vOfQ u) (C.t u) u := by
  have hv_a : v ∈ Icc M.a 1 := ⟨le_trans C.v_hat_mem_Icc_a.1 hv.1, hv.2⟩
  have hv_ρ : ρ ≤ v := le_trans C.hρ_le_vhat hv.1
  have hw_int : IntegrableOn C.w_riv (Icc v 1) :=
    C.w_riv_integrableOn.mono_set (Icc_subset_Icc_left hv_a.1)
  have hw_nn : ∀ s ∈ Icc v 1, 0 ≤ C.w_riv s := fun s hs =>
    C.w_riv_nonneg ⟨le_trans hv_a.1 hs.1, hs.2⟩
  have hqv_eq : C.q v = ∫ u in v..1, C.w_riv u := C.q_eq_integral_w_riv hv_a hv_ρ
  let g : ℝ → ℝ := fun u => Φ (C.vOfQ u) (C.t u) u
  have hchg := integral_comp_antitone_primitive hv.2 hw_int hw_nn (by rwa [← hqv_eq])
  rw [← hqv_eq] at hchg
  rw [← hchg]
  -- Show `C.vOfQ (C.q s) = s` for `μ`-a.e. `s ∈ Icc v 1`, where `μ = (volume.restrict (Icc v 1)).withDensity w_riv`
  let μ := (volume.restrict (Icc v 1)).withDensity (fun s => ENNReal.ofReal (C.w_riv s))
  let q_prim : ℝ → ℝ := fun s => ∫ u in s..1, C.w_riv u
  have hmap : Measure.map q_prim μ = volume.restrict (Icc (0 : ℝ) (C.q v)) := by
    rw [hqv_eq]; exact map_antitone_primitive hv.2 hw_int hw_nn
  let U : Set ℝ := {c : ℝ | ∃ v₁ v₂, v₁ ∈ Icc C.v_hat 1 ∧ v₂ ∈ Icc C.v_hat 1 ∧ v₁ < v₂ ∧ C.q v₁ = c ∧ C.q v₂ = c}
  have hU_count : U.Countable := C.q_antitoneOn_vhat.countable_setOfPred_two_preimages
  have hU_meas : MeasurableSet U := hU_count.measurableSet
  have hU_vol0 : volume U = 0 := hU_count.measure_zero volume
  have hq_prim_eq : ∀ s ∈ Icc v 1, q_prim s = C.q s := fun s hs =>
    (C.q_eq_integral_w_riv ⟨le_trans hv_a.1 hs.1, hs.2⟩ (le_trans hv_ρ hs.1)).symm
  have hq_aemeas : AEMeasurable q_prim μ := by
    have hw_uIcc : IntegrableOn C.w_riv (uIcc v 1) volume := by rwa [uIcc_of_le hv.2]
    have hcont := intervalIntegral.continuousOn_primitive_interval_left hw_uIcc
    rw [uIcc_of_le hv.2] at hcont
    exact (hcont.aemeasurable measurableSet_Icc).mono_ac (withDensity_absolutelyContinuous _ _)
  have hpre_null : μ (q_prim ⁻¹' U) = 0 := by
    rw [← Measure.map_apply_of_aemeasurable hq_aemeas hU_meas, hmap,
      Measure.restrict_apply hU_meas]
    exact measure_mono_null inter_subset_left hU_vol0
  -- From `μ (q_prim ⁻¹' U) = 0`, for volume-a.e. `s ∈ Icc v 1`, either `w_riv s = 0` or `q s ∉ U`
  have hae_eq : ∀ᵐ s ∂(volume.restrict (Icc v 1)),
      Φ s (C.T s) (C.q s) * C.w_riv s = g (q_prim s) * C.w_riv s := by
    have hzero_on_pre : ∫⁻ s in Icc v 1, (q_prim ⁻¹' U).indicator (fun s => ENNReal.ofReal (C.w_riv s)) s = 0 := by
      have hmeas_pre : NullMeasurableSet (q_prim ⁻¹' U) (volume.restrict (Icc v 1)) := by
        have hq_ae_vol : AEMeasurable q_prim (volume.restrict (Icc v 1)) := by
          have hw_uIcc : IntegrableOn C.w_riv (uIcc v 1) volume := by rwa [uIcc_of_le hv.2]
          have hcont := intervalIntegral.continuousOn_primitive_interval_left hw_uIcc
          rw [uIcc_of_le hv.2] at hcont
          exact hcont.aemeasurable measurableSet_Icc
        exact hq_ae_vol.nullMeasurable hU_meas
      have hμ_eq : ∫⁻ s in q_prim ⁻¹' U, ENNReal.ofReal (C.w_riv s) ∂(volume.restrict (Icc v 1)) = 0 := by
        rwa [← withDensity_apply' _ (q_prim ⁻¹' U)]
      rwa [← lintegral_indicator₀ hmeas_pre] at hμ_eq
    have hae_ind : ∀ᵐ s ∂(volume.restrict (Icc v 1)),
        (q_prim ⁻¹' U).indicator (fun s => ENNReal.ofReal (C.w_riv s)) s = 0 := by
      refine (lintegral_eq_zero_iff' ?_).mp hzero_on_pre
      have hq_ae_vol : AEMeasurable q_prim (volume.restrict (Icc v 1)) := by
        have hw_uIcc : IntegrableOn C.w_riv (uIcc v 1) volume := by rwa [uIcc_of_le hv.2]
        have hcont := intervalIntegral.continuousOn_primitive_interval_left hw_uIcc
        rw [uIcc_of_le hv.2] at hcont
        exact hcont.aemeasurable measurableSet_Icc
      exact (hw_int.aemeasurable.ennreal_ofReal).indicator₀ (hq_ae_vol.nullMeasurable hU_meas)
    filter_upwards [ae_restrict_mem measurableSet_Icc, hae_ind] with s hs hind
    have hqs : q_prim s = C.q s := hq_prim_eq s hs
    by_cases hU : q_prim s ∈ U
    · rw [Set.indicator_of_mem (show s ∈ q_prim ⁻¹' U from hU)] at hind
      have hw0 : C.w_riv s = 0 := le_antisymm (ENNReal.ofReal_eq_zero.mp hind) (hw_nn s hs)
      simp [hw0]
    · have hs_vh : s ∈ Icc C.v_hat 1 := ⟨le_trans hv.1 hs.1, hs.2⟩
      have hqs_mem : C.q s ∈ Icc (0 : ℝ) C.q0 :=
        ⟨by rw [← C.q_one]; exact C.q_antitoneOn_vhat hs_vh (right_mem_Icc.mpr C.hv_hat_mem.2) hs_vh.2,
         C.q_antitoneOn_vhat (left_mem_Icc.mpr C.hv_hat_mem.2) hs_vh hs_vh.1⟩
      have hv_spec := C.vOfQ_spec hqs_mem
      have hv_le : C.vOfQ (C.q s) ≤ s :=
        csInf_le (s := {u ∈ Icc C.v_hat 1 | C.q u ≤ C.q s}) ⟨C.v_hat, fun u hu => hu.1.1⟩ ⟨hs_vh, le_rfl⟩
      have hv_eq : C.vOfQ (C.q s) = s := by
        rcases eq_or_lt_of_le hv_le with heq | hlt
        · exact heq
        · exfalso; apply hU; rw [hqs]
          exact ⟨C.vOfQ (C.q s), s, hv_spec.1, hs_vh, hlt, hv_spec.2, rfl⟩
      simp only [g, t, hqs, hv_eq]
  rw [intervalIntegral.integral_of_le hv.2, intervalIntegral.integral_of_le hv.2,
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc]
  exact integral_congr_ae hae_eq

/-- Upper bound `x_1(v) ≤ (1 - q0)^(n - 1)` on `[v_bar, v_hat)` — handles both `v_hat < 1`
and the corner case `v_hat = 1` with `σ(1) > 0`! -/
lemma alloc_le_c0_below_vhat {v : ℝ} (hv : v ∈ Ico C.v_bar C.v_hat) :
    alloc M mech C.F1 v ≤ (1 - C.q0) ^ (M.n - 1) := by
  have hF1_mono : MonotoneOn C.F1 (Iic 1) := effDist_monotoneOn M C.θ C.j0
  have hF1_mem : ∀ u ≤ 1, C.F1 u ∈ Icc (0 : ℝ) 1 := fun u hu => effDist_mem_Icc M C.θ C.j0 hu
  have hx_mono : MonotoneOn (alloc M mech C.F1) (Iic 1) := alloc_monotoneOn M mech hF1_mono hF1_mem
  rcases eq_or_lt_of_le C.hv_hat_mem.2 with hvhat1 | hvhat_lt1
  · -- Corner case `v_hat = 1`: `q0 = q(1) = 0`, so `(1 - q0)^(n - 1) = 1 ≥ alloc`!
    have hq0_zero : C.q0 = 0 := by unfold q0; rw [hvhat1]; exact C.q_one
    rw [hq0_zero, sub_zero, one_pow]
    exact (alloc_mem_Icc M mech hF1_mono hF1_mem (le_trans hv.2.le C.hv_hat_mem.2)).2
  · -- Interior case `v_hat < 1`: `s_1(v_hat) = s_riv(v_hat)`
    have hvbar_lt : max (min mech.r ρ) M.a < C.v_hat := lt_of_le_of_lt hv.1 hv.2
    have hs_eq : surplus M mech C.F1 C.v_hat = surplus M (SPA ρ hρ0 hρ1.le) C.F_riv C.v_hat :=
      C.hs_vhat_eq hvbar_lt hvhat_lt1
    rcases eq_or_lt_of_le C.hρ_le_vhat with hρ_eq | hρ_lt
    · -- `v_hat = ρ`: `s_1(ρ) = s_riv(ρ) = 0`, so `alloc = 0 ≤ (1 - q0)^(n - 1)` on `[v_bar, ρ)`
      have hs0 : surplus M mech C.F1 C.v_hat = 0 := by
        rw [hs_eq, C.s_riv_on_rho_vhat ⟨C.hρ_le_vhat, le_rfl⟩, sub_eq_zero.mpr hρ_eq.symm, zero_mul]
      have hx_nn : 0 ≤ alloc M mech C.F1 v :=
        (alloc_mem_Icc M mech hF1_mono hF1_mem (le_trans hv.2.le C.hv_hat_mem.2)).1
      have hx_le0 : alloc M mech C.F1 v ≤ 0 := by
        by_contra hpos; push Not at hpos
        have hint : IntervalIntegrable (alloc M mech C.F1) volume 0 C.v_hat :=
          (hx_mono.mono (by rw [uIcc_of_le (le_trans M.ha0 C.v_hat_mem_Icc_a.1)]; exact fun u hu => le_trans hu.2 C.hv_hat_mem.2)).intervalIntegrable
        have hsplit := intervalIntegral.integral_add_adjacent_intervals
          (hint.mono_set (uIcc_subset_uIcc left_mem_uIcc (mem_uIcc_of_le (le_trans M.ha0 (le_trans C.v_bar_mem_Icc.1 hv.1)) hv.2.le)))
          (hint.mono_set (uIcc_subset_uIcc (mem_uIcc_of_le (le_trans M.ha0 (le_trans C.v_bar_mem_Icc.1 hv.1)) hv.2.le) right_mem_uIcc))
        have h1 : 0 ≤ ∫ u in (0 : ℝ)..v, alloc M mech C.F1 u :=
          intervalIntegral.integral_nonneg (le_trans M.ha0 (le_trans C.v_bar_mem_Icc.1 hv.1))
            (fun u hu => (alloc_mem_Icc M mech hF1_mono hF1_mem (le_trans hu.2 (le_trans hv.2.le C.hv_hat_mem.2))).1)
        have h2 : alloc M mech C.F1 v * (C.v_hat - v) ≤ ∫ u in v..C.v_hat, alloc M mech C.F1 u := by
          calc alloc M mech C.F1 v * (C.v_hat - v)
              = ∫ _ in v..C.v_hat, alloc M mech C.F1 v := by
                rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
            _ ≤ ∫ u in v..C.v_hat, alloc M mech C.F1 u :=
                intervalIntegral.integral_mono_on hv.2.le intervalIntegrable_const
                  (hint.mono_set (uIcc_subset_uIcc (mem_uIcc_of_le (le_trans M.ha0 (le_trans C.v_bar_mem_Icc.1 hv.1)) hv.2.le) right_mem_uIcc))
                  (fun u hu => hx_mono (le_trans hv.2.le C.hv_hat_mem.2) (le_trans hu.2 C.hv_hat_mem.2) hu.1)
        have hpos_prod : 0 < alloc M mech C.F1 v * (C.v_hat - v) := mul_pos hpos (sub_pos.mpr hv.2)
        unfold surplus at hs0
        linarith
      exact le_trans hx_le0 (pow_nonneg (by linarith [C.q0_mem_Icc.2]) _)
    · -- `ρ < v_hat`: take `w = max v ρ ∈ [v_bar, v_hat) ∩ [ρ, v_hat)`
      let w := max v ρ
      have hw_lt : w < C.v_hat := max_lt hv.2 hρ_lt
      have hw_mem_vbar : w ∈ Icc C.v_bar C.v_hat := ⟨le_trans hv.1 (le_max_left _ _), hw_lt.le⟩
      have hw_mem_ρ : w ∈ Icc ρ C.v_hat := ⟨le_max_right _ _, hw_lt.le⟩
      have hs_w : surplus M (SPA ρ hρ0 hρ1.le) C.F_riv w ≤ surplus M mech C.F1 w :=
        C.hs_below hvbar_lt w hw_mem_vbar
      have hint : IntervalIntegrable (alloc M mech C.F1) volume 0 C.v_hat :=
        (hx_mono.mono (by rw [uIcc_of_le (le_trans M.ha0 C.v_hat_mem_Icc_a.1)]; exact fun u hu => le_trans hu.2 C.hv_hat_mem.2)).intervalIntegrable
      have hsplit := intervalIntegral.integral_add_adjacent_intervals
        (hint.mono_set (uIcc_subset_uIcc left_mem_uIcc (mem_uIcc_of_le (le_trans M.ha0 (le_trans C.v_bar_mem_Icc.1 hw_mem_vbar.1)) hw_lt.le)))
        (hint.mono_set (uIcc_subset_uIcc (mem_uIcc_of_le (le_trans M.ha0 (le_trans C.v_bar_mem_Icc.1 hw_mem_vbar.1)) hw_lt.le) right_mem_uIcc))
      have hge : alloc M mech C.F1 w * (C.v_hat - w) ≤ ∫ u in w..C.v_hat, alloc M mech C.F1 u := by
        calc alloc M mech C.F1 w * (C.v_hat - w)
            = ∫ _ in w..C.v_hat, alloc M mech C.F1 w := by
              rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
          _ ≤ ∫ u in w..C.v_hat, alloc M mech C.F1 u :=
              intervalIntegral.integral_mono_on hw_lt.le intervalIntegrable_const
                (hint.mono_set (uIcc_subset_uIcc (mem_uIcc_of_le (le_trans M.ha0 (le_trans C.v_bar_mem_Icc.1 hw_mem_vbar.1)) hw_lt.le) right_mem_uIcc))
                (fun u hu => hx_mono (le_trans hw_lt.le C.hv_hat_mem.2) (le_trans hu.2 C.hv_hat_mem.2) hu.1)
      have hdiff_sriv : surplus M (SPA ρ hρ0 hρ1.le) C.F_riv C.v_hat -
          surplus M (SPA ρ hρ0 hρ1.le) C.F_riv w = (1 - C.q0) ^ (M.n - 1) * (C.v_hat - w) := by
        rw [C.s_riv_on_rho_vhat ⟨C.hρ_le_vhat, le_rfl⟩, C.s_riv_on_rho_vhat hw_mem_ρ]; ring
      have hle_prod : alloc M mech C.F1 w * (C.v_hat - w) ≤ (1 - C.q0) ^ (M.n - 1) * (C.v_hat - w) := by
        unfold surplus at hs_eq hs_w hdiff_sriv
        linarith
      have hxw_le : alloc M mech C.F1 w ≤ (1 - C.q0) ^ (M.n - 1) :=
        le_of_mul_le_mul_right hle_prod (sub_pos.mpr hw_lt)
      exact le_trans (hx_mono (le_trans hv.2.le C.hv_hat_mem.2) (le_trans hw_lt.le C.hv_hat_mem.2) (le_max_left _ _)) hxw_le

/-- Pointwise rent identity on `[max ρ v_bar, v_hat)`:
`ρ c0 - payment(v) = σ(v_hat) + v δ(v) + ∫_v^{v_hat} δ(u) du`,
where `c0 = (1 - q0)^(n - 1)`, `δ(u) = c0 - x_1(u) ≥ 0`, and `σ(v_hat) = s_1(v_hat) - s_riv(v_hat) ≥ 0`. -/
lemma rent_excess_identity {v : ℝ} (hv : v ∈ Icc (max ρ C.v_bar) C.v_hat) :
    ρ * (1 - C.q0) ^ (M.n - 1) - payment M mech C.F1 v =
      (surplus M mech C.F1 C.v_hat - surplus M (SPA ρ hρ0 hρ1.le) C.F_riv C.v_hat) +
      v * ((1 - C.q0) ^ (M.n - 1) - alloc M mech C.F1 v) +
      ∫ u in v..C.v_hat, ((1 - C.q0) ^ (M.n - 1) - alloc M mech C.F1 u) := by
  have hF1_mono : MonotoneOn C.F1 (Iic 1) := effDist_monotoneOn M C.θ C.j0
  have hF1_mem : ∀ u ≤ 1, C.F1 u ∈ Icc (0 : ℝ) 1 := fun u hu => effDist_mem_Icc M C.θ C.j0 hu
  have hx_mono : MonotoneOn (alloc M mech C.F1) (Iic 1) := alloc_monotoneOn M mech hF1_mono hF1_mem
  have hv0 : 0 ≤ v := le_trans hρ0 (le_trans (le_max_left _ _) hv.1)
  have hint : IntervalIntegrable (alloc M mech C.F1) volume 0 C.v_hat :=
    (hx_mono.mono (by rw [uIcc_of_le (le_trans M.ha0 C.v_hat_mem_Icc_a.1)]; exact fun u hu => le_trans hu.2 C.hv_hat_mem.2)).intervalIntegrable
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hint.mono_set (uIcc_subset_uIcc left_mem_uIcc (mem_uIcc_of_le hv0 hv.2)))
    (hint.mono_set (uIcc_subset_uIcc (mem_uIcc_of_le hv0 hv.2) right_mem_uIcc))
  have hs_riv : surplus M (SPA ρ hρ0 hρ1.le) C.F_riv C.v_hat =
      (C.v_hat - ρ) * (1 - C.q0) ^ (M.n - 1) :=
    C.s_riv_on_rho_vhat ⟨C.hρ_le_vhat, le_rfl⟩
  have hsub_int : ∫ u in v..C.v_hat, ((1 - C.q0) ^ (M.n - 1) - alloc M mech C.F1 u) =
      (C.v_hat - v) * (1 - C.q0) ^ (M.n - 1) - ∫ u in v..C.v_hat, alloc M mech C.F1 u := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const
        (hint.mono_set (uIcc_subset_uIcc (mem_uIcc_of_le hv0 hv.2) right_mem_uIcc)),
      intervalIntegral.integral_const, smul_eq_mul]
  unfold payment surplus at hs_riv ⊢
  linarith

/-- Nonnegativity of extra rent `ℓ ≥ 0` in Proposition 3 (valid for all `ρ ∈ [0, 1)`, all `r_1`,
and including `v_hat = 1, σ(1) > 0`). -/
theorem ell_nonneg : 0 ≤ C.ell := by
  unfold ell
  have hT_diff : C.t0 - C.T C.v_hat = ∫ v in C.v_bar..C.v_hat, C.w1 v := by
    have hw_ivl := (intervalIntegrable_iff_integrableOn_Icc_of_le M.ha1.le).mpr C.w1_integrableOn
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hw_ivl.mono_set (uIcc_subset_uIcc (mem_uIcc_of_le C.v_bar_mem_Icc.1 C.v_bar_mem_Icc.2)
        (mem_uIcc_of_le C.v_hat_mem_Icc_a.1 C.v_hat_mem_Icc_a.2)))
      (hw_ivl.mono_set (uIcc_subset_uIcc (mem_uIcc_of_le C.v_hat_mem_Icc_a.1 C.v_hat_mem_Icc_a.2) right_mem_uIcc))
    unfold t0 T F1 effDist
    dsimp only [w1] at hsplit ⊢
    linarith
  have hw_int : IntervalIntegrable C.w1 volume C.v_bar C.v_hat :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le C.v_bar_le_v_hat).mpr
      (C.w1_integrableOn.mono_set (Icc_subset_Icc C.v_bar_mem_Icc.1 C.hv_hat_mem.2))
  have hF1_mono : MonotoneOn C.F1 (Iic 1) := effDist_monotoneOn M C.θ C.j0
  have hF1_mem : ∀ u ≤ 1, C.F1 u ∈ Icc (0 : ℝ) 1 := fun u hu => effDist_mem_Icc M C.θ C.j0 hu
  have hx_mono : MonotoneOn (alloc M mech C.F1) (Iic 1) := alloc_monotoneOn M mech hF1_mono hF1_mem
  have hpay_int : IntervalIntegrable (fun v => payment M mech C.F1 v * C.w1 v) volume C.v_bar C.v_hat := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le C.v_bar_le_v_hat]
    have hx_ivl : IntervalIntegrable (alloc M mech C.F1) volume 0 1 :=
      (hx_mono.mono (by rw [uIcc_of_le zero_le_one]; exact fun u hu => hu.2)).intervalIntegrable
    have hx_meas : AEStronglyMeasurable (alloc M mech C.F1) (volume.restrict (Icc C.v_bar C.v_hat)) :=
      ((intervalIntegrable_iff_integrableOn_Icc_of_le C.v_bar_le_v_hat).mp
        (hx_ivl.mono_set (uIcc_subset_uIcc (mem_uIcc_of_le (le_trans M.ha0 C.v_bar_mem_Icc.1) C.v_bar_mem_Icc.2)
          (mem_uIcc_of_le (le_trans M.ha0 C.v_hat_mem_Icc_a.1) C.hv_hat_mem.2)))).aestronglyMeasurable
    have hs_cont : ContinuousOn (surplus M mech C.F1) (Icc C.v_bar C.v_hat) := by
      have h1 := intervalIntegral.continuousOn_primitive_interval
        ((intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp hx_ivl |> fun h => by rwa [uIcc_of_le zero_le_one])
      rw [uIcc_of_le zero_le_one] at h1
      exact h1.mono (Icc_subset_Icc (le_trans M.ha0 C.v_bar_mem_Icc.1) C.hv_hat_mem.2)
    have hpm : AEStronglyMeasurable (payment M mech C.F1) (volume.restrict (Icc C.v_bar C.v_hat)) :=
      ((continuousOn_id.aestronglyMeasurable measurableSet_Icc).mul hx_meas).sub
        (hs_cont.aestronglyMeasurable measurableSet_Icc)
    have hw_on : IntegrableOn C.w1 (Icc C.v_bar C.v_hat) :=
      C.w1_integrableOn.mono_set (Icc_subset_Icc C.v_bar_mem_Icc.1 C.hv_hat_mem.2)
    refine (hw_on.const_mul 2).mono' (hpm.mul hw_on.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    have hv01 : v ∈ Icc (0 : ℝ) 1 := ⟨le_trans M.ha0 (le_trans C.v_bar_mem_Icc.1 hv.1), le_trans hv.2 C.hv_hat_mem.2⟩
    have hxv := alloc_mem_Icc M mech hF1_mono hF1_mem hv01.2
    have hsv_nn : 0 ≤ surplus M mech C.F1 v :=
      intervalIntegral.integral_nonneg hv01.1 (fun u hu => (alloc_mem_Icc M mech hF1_mono hF1_mem (le_trans hu.2 hv01.2)).1)
    have hsv_le : surplus M mech C.F1 v ≤ 1 := by
      calc ∫ u in (0 : ℝ)..v, alloc M mech C.F1 u
          ≤ ∫ _ in (0 : ℝ)..v, (1 : ℝ) :=
            intervalIntegral.integral_mono_on hv01.1
              (hx_ivl.mono_set (uIcc_subset_uIcc left_mem_uIcc (mem_uIcc_of_le hv01.1 hv01.2)))
              intervalIntegrable_const (fun u hu => (alloc_mem_Icc M mech hF1_mono hF1_mem (le_trans hu.2 hv01.2)).2)
        _ = v := by simp
        _ ≤ 1 := hv01.2
    have hpay_abs : |payment M mech C.F1 v| ≤ 2 := by
      unfold payment
      rw [abs_le]
      constructor <;> nlinarith [hv01.1, hv01.2, hxv.1, hxv.2]
    have hw_nn : 0 ≤ C.w1 v := C.w1_nonneg ⟨le_trans C.v_bar_mem_Icc.1 hv.1, le_trans hv.2 C.hv_hat_mem.2⟩
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw_nn]
    nlinarith
  rw [hT_diff,
    show (M.n : ℝ) * ρ * (1 - C.q0) ^ (M.n - 1) * (∫ v in C.v_bar..C.v_hat, C.w1 v) -
        (M.n : ℝ) * (∫ v in C.v_bar..C.v_hat, payment M mech C.F1 v * C.w1 v) =
      (M.n : ℝ) * ((ρ * (1 - C.q0) ^ (M.n - 1)) * (∫ v in C.v_bar..C.v_hat, C.w1 v) -
        (∫ v in C.v_bar..C.v_hat, payment M mech C.F1 v * C.w1 v)) by ring,
    ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub (hw_int.const_mul _) hpay_int]
  refine mul_nonneg M.n_pos_real.le ?_
  rw [intervalIntegral.integral_of_le C.v_bar_le_v_hat, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_nonneg measurableSet_Ioo (fun v hv => ?_)
  have hv_mem : v ∈ Ico C.v_bar C.v_hat := ⟨hv.1.le, hv.2⟩
  have hw_nn : 0 ≤ C.w1 v := C.w1_nonneg ⟨le_trans C.v_bar_mem_Icc.1 hv.1.le, le_trans hv.2.le C.hv_hat_mem.2⟩
  have hpt : payment M mech C.F1 v ≤ ρ * (1 - C.q0) ^ (M.n - 1) := by
    rcases lt_or_ge v ρ with hv_lt_ρ | hv_ge_ρ
    · -- `v < ρ`: `v x_1(v) - s_1(v) ≤ v x_1(v) ≤ ρ c0`
      have hv0 : 0 ≤ v := le_trans M.ha0 (le_trans C.v_bar_mem_Icc.1 hv.1.le)
      have hs_nn : 0 ≤ surplus M mech C.F1 v :=
        intervalIntegral.integral_nonneg hv0
          (fun u hu => (alloc_mem_Icc M mech hF1_mono hF1_mem (le_trans hu.2 (le_trans hv.2.le C.hv_hat_mem.2))).1)
      have hx_le := C.alloc_le_c0_below_vhat hv_mem
      have hc0_nn : 0 ≤ (1 - C.q0) ^ (M.n - 1) := pow_nonneg (by linarith [C.q0_mem_Icc.2]) _
      have hx_nn : 0 ≤ alloc M mech C.F1 v :=
        (alloc_mem_Icc M mech hF1_mono hF1_mem (le_trans hv.2.le C.hv_hat_mem.2)).1
      unfold payment
      nlinarith
    · -- `v ≥ ρ`: use `rent_excess_identity`!
      have hid := C.rent_excess_identity ⟨max_le hv_ge_ρ hv.1.le, hv.2.le⟩
      have hσ_nn : 0 ≤ surplus M mech C.F1 C.v_hat - surplus M (SPA ρ hρ0 hρ1.le) C.F_riv C.v_hat :=
        sub_nonneg.mpr (C.hs_below (hv.1.trans hv.2) C.v_hat (right_mem_Icc.mpr C.hv_hat_mem.1))
      have hv0 : 0 ≤ v := le_trans hρ0 hv_ge_ρ
      have hδ_nn : 0 ≤ (1 - C.q0) ^ (M.n - 1) - alloc M mech C.F1 v :=
        sub_nonneg.mpr (C.alloc_le_c0_below_vhat hv_mem)
      have hint_nn : 0 ≤ ∫ u in v..C.v_hat, ((1 - C.q0) ^ (M.n - 1) - alloc M mech C.F1 u) := by
        rw [intervalIntegral.integral_of_le hv.2.le, integral_Ioc_eq_integral_Ioo]
        refine setIntegral_nonneg measurableSet_Ioo (fun u hu =>
          sub_nonneg.mpr (C.alloc_le_c0_below_vhat ⟨le_trans hv.1.le hu.1.le, hu.2⟩))
      nlinarith
  nlinarith

/-- Chain-rule formula for `(F_riv v)^(n - 1)` on `[v_0, v_1] ⊆ [v_hat, 1]`. -/
lemma F_riv_pow_sub_eq_integral {v₀ v₁ : ℝ} (hv₀ : v₀ ∈ Icc C.v_hat 1)
    (hv₁ : v₁ ∈ Icc C.v_hat 1) (hle : v₀ ≤ v₁) :
    ((M.n : ℝ) - 1) * ∫ u in v₀..v₁, (C.F_riv u) ^ (M.n - 2) * C.w_riv u =
      (C.F_riv v₁) ^ (M.n - 1) - (C.F_riv v₀) ^ (M.n - 1) := by
  have hv₀_a : v₀ ∈ Icc M.a 1 := ⟨le_trans C.v_hat_mem_Icc_a.1 hv₀.1, hv₀.2⟩
  have hv₁_a : v₁ ∈ Icc M.a 1 := ⟨le_trans C.v_hat_mem_Icc_a.1 hv₁.1, hv₁.2⟩
  have hw_int : IntegrableOn C.w_riv (Icc v₀ v₁) :=
    C.w_riv_integrableOn.mono_set (Icc_subset_Icc hv₀_a.1 hv₁.2)
  have hw_nn : ∀ u ∈ Icc v₀ v₁, 0 ≤ C.w_riv u := fun u hu =>
    C.w_riv_nonneg ⟨le_trans hv₀_a.1 hu.1, le_trans hu.2 hv₁.2⟩
  have hch := pow_sub_pow_eq_integral_antitone (c := C.F_riv v₁) hle (M.n - 2) hw_int hw_nn
  have hn_eq1 : M.n - 2 + 1 = M.n - 1 := by have := M.hn; omega
  have hn_cast : ((M.n - 1 : ℕ) : ℝ) = (M.n : ℝ) - 1 := by
    rw [Nat.cast_sub (by have := M.hn; omega), Nat.cast_one]
  rw [hn_eq1, hn_cast] at hch
  have hshift : ∀ u ∈ Icc v₀ v₁, C.F_riv v₁ - ∫ s in u..v₁, C.w_riv s = C.F_riv u := by
    intro u hu
    have hu_a : u ∈ Icc M.a 1 := ⟨le_trans hv₀_a.1 hu.1, le_trans hu.2 hv₁.2⟩
    have hqu := C.q_eq_integral_w_riv hu_a (le_trans C.hρ_le_vhat (le_trans hv₀.1 hu.1))
    have hqv1 := C.q_eq_integral_w_riv hv₁_a (le_trans C.hρ_le_vhat hv₁.1)
    have hw_ivl := (intervalIntegrable_iff_integrableOn_Icc_of_le M.ha1.le).mpr C.w_riv_integrableOn
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hw_ivl.mono_set (uIcc_subset_uIcc (mem_uIcc_of_le hu_a.1 hu_a.2) (mem_uIcc_of_le hv₁_a.1 hv₁_a.2)))
      (hw_ivl.mono_set (uIcc_subset_uIcc (mem_uIcc_of_le hv₁_a.1 hv₁_a.2) right_mem_uIcc))
    unfold q at hqu hqv1
    linarith
  have hcongr : ∫ u in v₀..v₁, (C.F_riv v₁ - ∫ s in u..v₁, C.w_riv s) ^ (M.n - 2) * C.w_riv u =
      ∫ u in v₀..v₁, (C.F_riv u) ^ (M.n - 2) * C.w_riv u := by
    rw [intervalIntegral.integral_of_le hle, intervalIntegral.integral_of_le hle,
      ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc]
    exact setIntegral_congr_fun measurableSet_Icc (fun u hu => by rw [hshift u hu])
  rw [hcongr, hshift v₀ (left_mem_Icc.mpr hle)] at hch
  exact hch

/-- **Proposition 3 (Quantity-Path Revenue Representation, eq. (6))**:
Seller 1's expected revenue in the continuation `C` equals
`pathRev M P.P ρ C.q0 C.t0 C.ell C.t = n ρ t0 (1 - q0)^(n - 1) + ∫_0^{q0} Π(t(q), q) W(q) dq - ℓ`
with `0 ≤ C.ell`. -/
theorem prop3_quantity_path_rev (P : M.InverseDemand) :
    sellerRev M mech C.θ C.j0 = pathRev M P.P ρ C.q0 C.t0 C.ell C.t := by
  have hF1_mono : MonotoneOn C.F1 (Iic 1) := effDist_monotoneOn M C.θ C.j0
  have hF1_mem : ∀ u ≤ 1, C.F1 u ∈ Icc (0 : ℝ) 1 := fun u hu => effDist_mem_Icc M C.θ C.j0 hu
  have hx_mono : MonotoneOn (alloc M mech C.F1) (Iic 1) := alloc_monotoneOn M mech hF1_mono hF1_mem
  have hFriv_mem : ∀ u ∈ Icc C.v_hat 1, C.F_riv u ∈ Icc (0 : ℝ) 1 := by
    intro u hu
    obtain ⟨j, hj⟩ := C.exists_rival
    rw [← C.hriv_symm j hj u ⟨le_trans C.hρ_le_vhat hu.1, hu.2⟩]
    exact effDist_mem_Icc M C.θ j hu.2
  have hFriv_cont : ContinuousOn C.F_riv (Icc C.v_hat 1) := by
    have heq : EqOn C.F_riv (fun u => 1 - C.q u) (Icc C.v_hat 1) := fun u _ => by unfold q; ring
    exact (continuousOn_const.sub C.q_continuousOn_vhat).congr heq
  -- Step 1: Split `sellerRev` on `[a, 1]` into `[a, v_bar]` (zero!), `[v_bar, v_hat]`, and `[v_hat, 1]`
  have hpay_int_a1 : IntervalIntegrable (fun v => payment M mech C.F1 v * C.w1 v) volume M.a 1 := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le M.ha1.le]
    have hx_ivl : IntervalIntegrable (alloc M mech C.F1) volume 0 1 :=
      (hx_mono.mono (by rw [uIcc_of_le zero_le_one]; exact fun u hu => hu.2)).intervalIntegrable
    have hx_meas : AEStronglyMeasurable (alloc M mech C.F1) (volume.restrict (Icc M.a 1)) :=
      ((intervalIntegrable_iff_integrableOn_Icc_of_le M.ha1.le).mp
        (hx_ivl.mono_set (uIcc_subset_uIcc (mem_uIcc_of_le M.ha0 M.ha1.le) right_mem_uIcc))).aestronglyMeasurable
    have hs_cont : ContinuousOn (surplus M mech C.F1) (Icc M.a 1) := by
      have h1 := intervalIntegral.continuousOn_primitive_interval
        ((intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp hx_ivl |> fun h => by rwa [uIcc_of_le zero_le_one])
      rw [uIcc_of_le zero_le_one] at h1
      exact h1.mono (Icc_subset_Icc_left M.ha0)
    have hpm : AEStronglyMeasurable (payment M mech C.F1) (volume.restrict (Icc M.a 1)) :=
      ((continuousOn_id.aestronglyMeasurable measurableSet_Icc).mul hx_meas).sub
        (hs_cont.aestronglyMeasurable measurableSet_Icc)
    refine (C.w1_integrableOn.const_mul 2).mono' (hpm.mul C.w1_integrableOn.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    have hv01 : v ∈ Icc (0 : ℝ) 1 := ⟨le_trans M.ha0 hv.1, hv.2⟩
    have hxv := alloc_mem_Icc M mech hF1_mono hF1_mem hv01.2
    have hsv_nn : 0 ≤ surplus M mech C.F1 v :=
      intervalIntegral.integral_nonneg hv01.1 (fun u hu => (alloc_mem_Icc M mech hF1_mono hF1_mem (le_trans hu.2 hv01.2)).1)
    have hsv_le : surplus M mech C.F1 v ≤ 1 := by
      calc ∫ u in (0 : ℝ)..v, alloc M mech C.F1 u
          ≤ ∫ _ in (0 : ℝ)..v, (1 : ℝ) :=
            intervalIntegral.integral_mono_on hv01.1
              (hx_ivl.mono_set (uIcc_subset_uIcc left_mem_uIcc (mem_uIcc_of_le hv01.1 hv01.2)))
              intervalIntegrable_const (fun u hu => (alloc_mem_Icc M mech hF1_mono hF1_mem (le_trans hu.2 hv01.2)).2)
        _ = v := by simp
        _ ≤ 1 := hv01.2
    have hpay_abs : |payment M mech C.F1 v| ≤ 2 := by
      unfold payment; rw [abs_le]; constructor <;> nlinarith [hv01.1, hv01.2, hxv.1, hxv.2]
    have hw_nn : 0 ≤ C.w1 v := C.w1_nonneg hv
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw_nn]; nlinarith
  have hbelow_vbar_zero : ∫ v in M.a..C.v_bar, payment M mech C.F1 v * C.w1 v = 0 := by
    rw [intervalIntegral.integral_of_le C.v_bar_mem_Icc.1, integral_Ioc_eq_integral_Ioo]
    have h0 : EqOn (fun v => payment M mech C.F1 v * C.w1 v) 0 (Ioo M.a C.v_bar) := by
      intro v hv
      have hv_lt_r : v < mech.r := by
        have hgt : M.a < C.v_bar := lt_trans hv.1 hv.2
        have hvbar_eq : C.v_bar = min mech.r ρ := by
          unfold v_bar at hgt ⊢
          exact max_eq_left (by by_contra h; push Not at h; rw [max_eq_right h.le] at hgt; exact lt_irrefl _ hgt)
        have h1 : v < min mech.r ρ := by rw [← hvbar_eq]; exact hv.2
        exact lt_of_lt_of_le h1 (min_le_left _ _)
      simp [payment_zero_of_lt_r M mech C.F1 (le_trans M.ha0 hv.1.le) hv_lt_r]
    rw [setIntegral_congr_fun measurableSet_Ioo h0]; simp
  have hrev_split : sellerRev M mech C.θ C.j0 =
      ((M.n : ℝ) * ∫ v in C.v_bar..C.v_hat, payment M mech C.F1 v * C.w1 v) +
      ((M.n : ℝ) * ∫ v in C.v_hat..1, payment M mech C.F1 v * C.w1 v) := by
    have h1 := intervalIntegral.integral_add_adjacent_intervals
      (hpay_int_a1.mono_set (uIcc_subset_uIcc left_mem_uIcc (mem_uIcc_of_le C.v_bar_mem_Icc.1 C.v_bar_mem_Icc.2)))
      (hpay_int_a1.mono_set (uIcc_subset_uIcc (mem_uIcc_of_le C.v_bar_mem_Icc.1 C.v_bar_mem_Icc.2) right_mem_uIcc))
    have h2 := intervalIntegral.integral_add_adjacent_intervals
      (hpay_int_a1.mono_set (uIcc_subset_uIcc (mem_uIcc_of_le C.v_bar_mem_Icc.1 C.v_bar_mem_Icc.2)
        (mem_uIcc_of_le C.v_hat_mem_Icc_a.1 C.v_hat_mem_Icc_a.2)))
      (hpay_int_a1.mono_set (uIcc_subset_uIcc (mem_uIcc_of_le C.v_hat_mem_Icc_a.1 C.v_hat_mem_Icc_a.2) right_mem_uIcc))
    have hrew : sellerRev M mech C.θ C.j0 = (M.n : ℝ) * ∫ v in M.a..1, payment M mech C.F1 v * C.w1 v := by
      unfold sellerRev F1 w1; congr 1; refine intervalIntegral.integral_congr (fun v _ => by ring)
    rw [hrew, ← h1, hbelow_vbar_zero, zero_add, ← h2, mul_add]
  -- Step 2: Above `v_hat`, replace `payment M mech C.F1 v` by `v * F_riv(v)^(n-1) - s_riv(v)` a.e.
  let s_riv := surplus M (SPA ρ hρ0 hρ1.le) C.F_riv
  have habove_eq_riv : ∫ v in C.v_hat..1, payment M mech C.F1 v * C.w1 v =
      ∫ v in C.v_hat..1, (v * (C.F_riv v) ^ (M.n - 1) - s_riv v) * C.w1 v := by
    rw [intervalIntegral.integral_of_le C.hv_hat_mem.2, intervalIntegral.integral_of_le C.hv_hat_mem.2,
      ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc]
    refine integral_congr_ae ?_
    filter_upwards [C.hs_above, C.hx_above] with v hsv hxv
    rcases eq_or_lt_of_le (C.θ.hnonneg C.j0 v) with h0 | hpos
    · simp [w1, ← h0]
    · have hF1eq : C.F1 = effDist M C.θ C.j0 := rfl
      dsimp only [payment, s_riv]
      rw [hF1eq, hxv hpos, hsv hpos]
  -- Step 3: Compute `∫_{v_hat}^1 (v F_riv^(n-1) - s_riv) w1` via Triangle Fubini!
  let g : ℝ → ℝ := fun s => ((M.n : ℝ) - 1) * (C.F_riv s) ^ (M.n - 2) * C.w_riv s
  have hw1_vh : IntegrableOn C.w1 (Icc C.v_hat 1) :=
    C.w1_integrableOn.mono_set (Icc_subset_Icc_left C.v_hat_mem_Icc_a.1)
  have hwriv_vh : IntegrableOn C.w_riv (Icc C.v_hat 1) :=
    C.w_riv_integrableOn.mono_set (Icc_subset_Icc_left C.v_hat_mem_Icc_a.1)
  have hg_int : IntegrableOn g (Icc C.v_hat 1) := by
    have hcont : ContinuousOn (fun s => ((M.n : ℝ) - 1) * (C.F_riv s) ^ (M.n - 2)) (Icc C.v_hat 1) :=
      continuousOn_const.mul (hFriv_cont.pow _)
    have hivl := ((intervalIntegrable_iff_integrableOn_Icc_of_le C.hv_hat_mem.2).mpr hwriv_vh).continuousOn_mul
      (by rwa [uIcc_of_le C.hv_hat_mem.2])
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le C.hv_hat_mem.2).mp hivl
  have hFpow_int : IntegrableOn (fun u => (C.F_riv u) ^ (M.n - 1)) (Icc C.v_hat 1) :=
    (hFriv_cont.pow _).integrableOn_Icc
  have hvw1_int : IntegrableOn (fun v => v * C.w1 v) (Icc C.v_hat 1) := by
    have hivl := ((intervalIntegrable_iff_integrableOn_Icc_of_le C.hv_hat_mem.2).mpr hw1_vh).continuousOn_mul
      (continuousOn_id (s := uIcc C.v_hat 1))
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le C.hv_hat_mem.2).mp hivl
  have hT_cont : ContinuousOn C.T (Icc C.v_hat 1) := by
    have hw_uIcc : IntegrableOn C.w1 (uIcc C.v_hat 1) volume := by rwa [uIcc_of_le C.hv_hat_mem.2]
    have h1 := intervalIntegral.continuousOn_primitive_interval_left hw_uIcc
    rw [uIcc_of_le C.hv_hat_mem.2] at h1
    exact h1.congr (fun v _ => by unfold T F1 effDist w1; ring)
  have hT_int : IntegrableOn C.T (Icc C.v_hat 1) := hT_cont.integrableOn_Icc
  -- (3a) `∫_{v_hat}^1 s_riv(v) w1(v) = s_riv(v_hat) T(v_hat) + ∫_{v_hat}^1 F_riv(u)^(n-1) T(u)`
  have hs_riv_split : ∀ v ∈ Icc C.v_hat 1,
      s_riv v = s_riv C.v_hat + ∫ u in C.v_hat..v, (C.F_riv u) ^ (M.n - 1) := by
    intro v hv
    have hs_eq : ∫ u in C.v_hat..v, alloc M (SPA ρ hρ0 hρ1.le) C.F_riv u =
        ∫ u in C.v_hat..v, (C.F_riv u) ^ (M.n - 1) := by
      rw [intervalIntegral.integral_of_le hv.1, intervalIntegral.integral_of_le hv.1,
        ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc]
      refine setIntegral_congr_fun measurableSet_Icc (fun u hu => ?_)
      rw [alloc_SPA_eq, ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr (le_trans C.hρ_le_vhat hu.1)))]
    have hint2 : IntervalIntegrable (alloc M (SPA ρ hρ0 hρ1.le) C.F_riv) volume C.v_hat v := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hv.1]
      refine (hFpow_int.mono_set (Icc_subset_Icc_right hv.2)).congr_fun (fun u hu => ?_) measurableSet_Icc
      rw [alloc_SPA_eq, ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr (le_trans C.hρ_le_vhat hu.1)))]
    have hint1 : IntervalIntegrable (alloc M (SPA ρ hρ0 hρ1.le) C.F_riv) volume 0 C.v_hat := by
      have h1 : IntervalIntegrable (alloc M (SPA ρ hρ0 hρ1.le) C.F_riv) volume 0 ρ := by
        rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hρ0]
        refine (integrableOn_zero : IntegrableOn (0 : ℝ → ℝ) (Ioo 0 ρ)).congr_fun (fun u hu => ?_) measurableSet_Ioo
        simp [alloc_SPA_eq, hu.2]
      have h2 : IntervalIntegrable (alloc M (SPA ρ hρ0 hρ1.le) C.F_riv) volume ρ C.v_hat := by
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le C.hρ_le_vhat]
        refine (integrableOn_const (C := (1 - C.q0) ^ (M.n - 1)) (hs := measure_Ioc_lt_top.ne)).congr_fun
          (fun u hu => ?_) measurableSet_Ioc
        rw [alloc_SPA_eq, ite_eq_right_iff.mpr (fun h => absurd h (not_lt.mpr hu.1.le)),
          C.F_riv_const_on_rho_vhat ⟨hu.1.le, hu.2⟩]
      exact h1.trans h2
    unfold s_riv surplus
    rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2, hs_eq]
  have hI_sriv : ∫ v in C.v_hat..1, s_riv v * C.w1 v =
      s_riv C.v_hat * C.T C.v_hat + ∫ u in C.v_hat..1, (C.F_riv u) ^ (M.n - 1) * C.T u := by
    have hcongr : ∫ v in C.v_hat..1, s_riv v * C.w1 v =
        ∫ v in C.v_hat..1, (s_riv C.v_hat * C.w1 v + (∫ u in C.v_hat..v, (C.F_riv u) ^ (M.n - 1)) * C.w1 v) := by
      rw [intervalIntegral.integral_of_le C.hv_hat_mem.2, intervalIntegral.integral_of_le C.hv_hat_mem.2,
        ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc]
      exact setIntegral_congr_fun measurableSet_Icc (fun v hv => by rw [hs_riv_split v hv, add_mul])
    have hint_a : IntervalIntegrable (fun v => s_riv C.v_hat * C.w1 v) volume C.v_hat 1 :=
      ((intervalIntegrable_iff_integrableOn_Icc_of_le C.hv_hat_mem.2).mpr hw1_vh).const_mul _
    have hint_b : IntervalIntegrable (fun v => (∫ u in C.v_hat..v, (C.F_riv u) ^ (M.n - 1)) * C.w1 v)
        volume C.v_hat 1 := by
      have hprim_cont : ContinuousOn (fun v => ∫ u in C.v_hat..v, (C.F_riv u) ^ (M.n - 1)) (uIcc C.v_hat 1) :=
        intervalIntegral.continuousOn_primitive_interval (by rwa [uIcc_of_le C.hv_hat_mem.2])
      exact ((intervalIntegrable_iff_integrableOn_Icc_of_le C.hv_hat_mem.2).mpr hw1_vh).continuousOn_mul hprim_cont
    rw [hcongr, intervalIntegral.integral_add hint_a hint_b, intervalIntegral.integral_const_mul,
      integral_integral_mul_swap C.hv_hat_mem.2 hFpow_int hw1_vh]
    have hT_eq : ∀ u, ∫ v in u..1, C.w1 v = C.T u := fun _ => by unfold T F1 effDist w1; ring
    simp_rw [hT_eq]
  -- (3b) For any `s ∈ [v_hat, 1]`, `∫ v in s..1, v * w1 v - ∫ u in s..1, T u = s * T s`
  have hs_id : ∀ s ∈ Icc C.v_hat 1,
      (∫ v in s..1, v * C.w1 v) - (∫ u in s..1, C.T u) = s * C.T s := by
    intro s hs
    have hswap := integral_integral_mul_swap hs.2
      (integrableOn_const (C := (1 : ℝ)) (hs := measure_Icc_lt_top.ne))
      (hw1_vh.mono_set (Icc_subset_Icc_left hs.1))
    have h1 : ∫ v in s..1, (∫ _ in s..v, (1 : ℝ)) * C.w1 v =
        (∫ v in s..1, v * C.w1 v) - s * C.T s := by
      have heq : (fun v => (∫ _ in s..v, (1 : ℝ)) * C.w1 v) = fun v => v * C.w1 v - s * C.w1 v := by
        ext v; simp [sub_mul]
      rw [heq, intervalIntegral.integral_sub
          ((intervalIntegrable_iff_integrableOn_Icc_of_le hs.2).mpr (hvw1_int.mono_set (Icc_subset_Icc_left hs.1)))
          (((intervalIntegrable_iff_integrableOn_Icc_of_le hs.2).mpr (hw1_vh.mono_set (Icc_subset_Icc_left hs.1))).const_mul s),
        intervalIntegral.integral_const_mul]
      unfold T F1 effDist w1; ring
    have h2 : ∫ u in s..1, (1 : ℝ) * ∫ v in u..1, C.w1 v = ∫ u in s..1, C.T u := by
      congr 1; ext u; unfold T F1 effDist w1; ring
    linarith
  -- (3c) Expand `F_riv(v)^(n-1) = c0 + ∫_{v_hat}^v g` in both integrals and apply Triangle Fubini
  let c0 : ℝ := (1 - C.q0) ^ (M.n - 1)
  have hFriv_vh : C.F_riv C.v_hat = 1 - C.q0 := C.F_riv_const_on_rho_vhat ⟨C.hρ_le_vhat, le_rfl⟩
  have hFpow_exp : ∀ v ∈ Icc C.v_hat 1, (C.F_riv v) ^ (M.n - 1) = c0 + ∫ s in C.v_hat..v, g s := by
    intro v hv
    have h := C.F_riv_pow_sub_eq_integral (left_mem_Icc.mpr C.hv_hat_mem.2) hv hv.1
    rw [hFriv_vh, ← intervalIntegral.integral_const_mul] at h
    have heq : ∫ s in C.v_hat..v, ((M.n : ℝ) - 1) * ((C.F_riv s) ^ (M.n - 2) * C.w_riv s) =
        ∫ s in C.v_hat..v, g s := by congr 1; ext s; simp [g, mul_assoc]
    rw [heq] at h; dsimp only [c0]; linarith
  have hI_v : ∫ v in C.v_hat..1, v * (C.F_riv v) ^ (M.n - 1) * C.w1 v =
      c0 * (∫ v in C.v_hat..1, v * C.w1 v) + ∫ s in C.v_hat..1, g s * (∫ v in s..1, v * C.w1 v) := by
    have hcongr : ∫ v in C.v_hat..1, v * (C.F_riv v) ^ (M.n - 1) * C.w1 v =
        ∫ v in C.v_hat..1, (c0 * (v * C.w1 v) + (∫ s in C.v_hat..v, g s) * (v * C.w1 v)) := by
      rw [intervalIntegral.integral_of_le C.hv_hat_mem.2, intervalIntegral.integral_of_le C.hv_hat_mem.2,
        ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc]
      refine setIntegral_congr_fun measurableSet_Icc (fun v hv => by rw [hFpow_exp v hv]; ring)
    have hint_1 : IntervalIntegrable (fun v => c0 * (v * C.w1 v)) volume C.v_hat 1 :=
      ((intervalIntegrable_iff_integrableOn_Icc_of_le C.hv_hat_mem.2).mpr hvw1_int).const_mul _
    have hint_2 : IntervalIntegrable (fun v => (∫ s in C.v_hat..v, g s) * (v * C.w1 v)) volume C.v_hat 1 := by
      have hprim_cont : ContinuousOn (fun v => ∫ s in C.v_hat..v, g s) (uIcc C.v_hat 1) :=
        intervalIntegral.continuousOn_primitive_interval (by rwa [uIcc_of_le C.hv_hat_mem.2])
      exact ((intervalIntegrable_iff_integrableOn_Icc_of_le C.hv_hat_mem.2).mpr hvw1_int).continuousOn_mul hprim_cont
    rw [hcongr, intervalIntegral.integral_add hint_1 hint_2, intervalIntegral.integral_const_mul,
      integral_integral_mul_swap C.hv_hat_mem.2 hg_int hvw1_int]
  have hI_T : ∫ u in C.v_hat..1, (C.F_riv u) ^ (M.n - 1) * C.T u =
      c0 * (∫ u in C.v_hat..1, C.T u) + ∫ s in C.v_hat..1, g s * (∫ u in s..1, C.T u) := by
    have hcongr : ∫ u in C.v_hat..1, (C.F_riv u) ^ (M.n - 1) * C.T u =
        ∫ u in C.v_hat..1, (c0 * C.T u + (∫ s in C.v_hat..u, g s) * C.T u) := by
      rw [intervalIntegral.integral_of_le C.hv_hat_mem.2, intervalIntegral.integral_of_le C.hv_hat_mem.2,
        ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc]
      refine setIntegral_congr_fun measurableSet_Icc (fun u hu => by rw [hFpow_exp u hu]; ring)
    have hint_1 : IntervalIntegrable (fun u => c0 * C.T u) volume C.v_hat 1 :=
      ((intervalIntegrable_iff_integrableOn_Icc_of_le C.hv_hat_mem.2).mpr hT_int).const_mul _
    have hint_2 : IntervalIntegrable (fun u => (∫ s in C.v_hat..u, g s) * C.T u) volume C.v_hat 1 := by
      have hprim_cont : ContinuousOn (fun u => ∫ s in C.v_hat..u, g s) (uIcc C.v_hat 1) :=
        intervalIntegral.continuousOn_primitive_interval (by rwa [uIcc_of_le C.hv_hat_mem.2])
      exact ((intervalIntegrable_iff_integrableOn_Icc_of_le C.hv_hat_mem.2).mpr hT_int).continuousOn_mul hprim_cont
    rw [hcongr, intervalIntegral.integral_add hint_1 hint_2, intervalIntegral.integral_const_mul,
      integral_integral_mul_swap C.hv_hat_mem.2 hg_int hT_int]
  -- Combine `hI_v`, `hI_sriv`, `hI_T` and `hs_id`
  have habove_comb : ∫ v in C.v_hat..1, (v * (C.F_riv v) ^ (M.n - 1) - s_riv v) * C.w1 v =
      ρ * c0 * C.T C.v_hat + ∫ s in C.v_hat..1, s * C.T s * g s := by
    have hsplit_sub : ∫ v in C.v_hat..1, (v * (C.F_riv v) ^ (M.n - 1) - s_riv v) * C.w1 v =
        (∫ v in C.v_hat..1, v * (C.F_riv v) ^ (M.n - 1) * C.w1 v) -
        (∫ v in C.v_hat..1, s_riv v * C.w1 v) := by
      have heq : (fun v => (v * (C.F_riv v) ^ (M.n - 1) - s_riv v) * C.w1 v) =
          fun v => v * (C.F_riv v) ^ (M.n - 1) * C.w1 v - s_riv v * C.w1 v := by ext v; ring
      have hint_a : IntervalIntegrable (fun v => v * (C.F_riv v) ^ (M.n - 1) * C.w1 v) volume C.v_hat 1 := by
        have h1 := ((intervalIntegrable_iff_integrableOn_Icc_of_le C.hv_hat_mem.2).mpr hvw1_int).continuousOn_mul
          (by rw [uIcc_of_le C.hv_hat_mem.2]; exact hFriv_cont.pow (M.n - 1))
        refine h1.congr (fun v _ => by simp only [Pi.pow_apply]; ring)
      have hint_b : IntervalIntegrable (fun v => s_riv v * C.w1 v) volume C.v_hat 1 := by
        have h1 := intervalIntegral.continuousOn_primitive_interval
          (by rwa [uIcc_of_le C.hv_hat_mem.2] : IntegrableOn (fun u => (C.F_riv u) ^ (M.n - 1)) (uIcc C.v_hat 1) volume)
        have hs_cont : ContinuousOn s_riv (uIcc C.v_hat 1) := by
          rw [uIcc_of_le C.hv_hat_mem.2] at h1 ⊢
          exact (continuousOn_const.add h1).congr (fun v hv => hs_riv_split v hv)
        exact ((intervalIntegrable_iff_integrableOn_Icc_of_le C.hv_hat_mem.2).mpr hw1_vh).continuousOn_mul hs_cont
      rw [heq, intervalIntegral.integral_sub hint_a hint_b]
    rw [hsplit_sub, hI_v, hI_sriv, hI_T]
    have hdiff_g : (∫ s in C.v_hat..1, g s * ∫ v in s..1, v * C.w1 v) -
        (∫ s in C.v_hat..1, g s * ∫ u in s..1, C.T u) =
        ∫ s in C.v_hat..1, s * C.T s * g s := by
      have hint_g1 : IntervalIntegrable (fun s => g s * ∫ v in s..1, v * C.w1 v) volume C.v_hat 1 := by
        have hcont : ContinuousOn (fun s => ∫ v in s..1, v * C.w1 v) (uIcc C.v_hat 1) :=
          intervalIntegral.continuousOn_primitive_interval_left (by rwa [uIcc_of_le C.hv_hat_mem.2])
        exact ((intervalIntegrable_iff_integrableOn_Icc_of_le C.hv_hat_mem.2).mpr hg_int).mul_continuousOn hcont
      have hint_g2 : IntervalIntegrable (fun s => g s * ∫ u in s..1, C.T u) volume C.v_hat 1 := by
        have hcont : ContinuousOn (fun s => ∫ u in s..1, C.T u) (uIcc C.v_hat 1) :=
          intervalIntegral.continuousOn_primitive_interval_left (by rwa [uIcc_of_le C.hv_hat_mem.2])
        exact ((intervalIntegrable_iff_integrableOn_Icc_of_le C.hv_hat_mem.2).mpr hg_int).mul_continuousOn hcont
      rw [← intervalIntegral.integral_sub hint_g1 hint_g2,
        intervalIntegral.integral_of_le C.hv_hat_mem.2, intervalIntegral.integral_of_le C.hv_hat_mem.2,
        ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc]
      refine setIntegral_congr_fun measurableSet_Icc (fun s hs => ?_)
      rw [← mul_sub, hs_id s hs, mul_comm]
    have hsriv_vh : s_riv C.v_hat = (C.v_hat - ρ) * c0 :=
      C.s_riv_on_rho_vhat ⟨C.hρ_le_vhat, le_rfl⟩
    have hvh_id := hs_id C.v_hat (left_mem_Icc.mpr C.hv_hat_mem.2)
    have hmul_id : c0 * (∫ v in C.v_hat..1, v * C.w1 v) - c0 * (∫ u in C.v_hat..1, C.T u) =
        c0 * (C.v_hat * C.T C.v_hat) := by
      rw [← mul_sub, hvh_id]
    rw [hsriv_vh]
    linarith
  -- Step 4: Change variables `n * ∫_{v_hat}^1 s T(s) g(s) = ∫_0^{q0} Π(t(q), q) W(q) dq`
  have hcournot_eq : (M.n : ℝ) * ∫ s in C.v_hat..1, s * C.T s * g s =
      ∫ u in (0 : ℝ)..C.q0, M.cournotRev P.P (C.t u) u * M.W u := by
    let Φ : ℝ → ℝ → ℝ → ℝ := fun s Tval qval => Tval * s * M.W qval
    have hq0_nn : 0 ≤ C.q0 := C.q0_mem_Icc.1
    have hΦ_meas : AEStronglyMeasurable (fun u => Φ (C.vOfQ u) (C.t u) u)
        (volume.restrict (Icc (0 : ℝ) C.q0)) := by
      have ht_int : IntervalIntegrable C.t volume 0 C.q0 :=
        (C.t_monotoneOn.mono (by rw [uIcc_of_le hq0_nn])).intervalIntegrable
      have ht_m : AEStronglyMeasurable C.t (volume.restrict (Icc (0 : ℝ) C.q0)) :=
        ((intervalIntegrable_iff_integrableOn_Icc_of_le hq0_nn).mp ht_int).aestronglyMeasurable
      have hv_anti : AntitoneOn C.vOfQ (Icc (0 : ℝ) C.q0) := fun q₁ hq₁ q₂ hq₂ hle =>
        csInf_le (s := {v ∈ Icc C.v_hat 1 | C.q v ≤ q₂}) ⟨C.v_hat, fun v hv => hv.1.1⟩
          ⟨(C.vOfQ_spec hq₁).1, le_trans (C.vOfQ_spec hq₁).2.le hle⟩
      have hv_int : IntervalIntegrable C.vOfQ volume 0 C.q0 :=
        (hv_anti.mono (by rw [uIcc_of_le hq0_nn])).intervalIntegrable
      have hv_m : AEStronglyMeasurable C.vOfQ (volume.restrict (Icc (0 : ℝ) C.q0)) :=
        ((intervalIntegrable_iff_integrableOn_Icc_of_le hq0_nn).mp hv_int).aestronglyMeasurable
      exact (ht_m.mul hv_m).mul M.W_continuous.aestronglyMeasurable
    have hchg := C.integral_comp_q_of_v (left_mem_Icc.mpr C.hv_hat_mem.2) hΦ_meas
    have hlhs : (M.n : ℝ) * ∫ s in C.v_hat..1, s * C.T s * g s =
        ∫ s in C.v_hat..1, Φ s (C.T s) (C.q s) * C.w_riv s := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1; ext s
      simp only [Φ, g, Market.W, q]
      have h1 : 1 - (1 - C.F_riv s) = C.F_riv s := by ring
      rw [h1]; ring
    rw [hlhs, hchg]
    change ∫ u in (0 : ℝ)..C.q0, Φ (C.vOfQ u) (C.t u) u =
      ∫ u in (0 : ℝ)..C.q0, M.cournotRev P.P (C.t u) u * M.W u
    rw [intervalIntegral.integral_of_le hq0_nn, intervalIntegral.integral_of_le hq0_nn,
      ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc]
    refine setIntegral_congr_fun measurableSet_Icc (fun u hu => ?_)
    have hv_spec := C.vOfQ_spec hu
    have hv_a : C.vOfQ u ∈ Icc M.a 1 := ⟨le_trans C.v_hat_mem_Icc_a.1 hv_spec.1.1, hv_spec.1.2⟩
    have hv_ρ : ρ ≤ C.vOfQ u := le_trans C.hρ_le_vhat hv_spec.1.1
    have hmass := C.mass_conservation hv_a hv_ρ
    rw [hv_spec.2] at hmass
    have hP_eq : P.P (C.t u + ((M.m : ℝ) - 1) * u) = C.vOfQ u := by
      unfold t; rw [hmass, P.hP_left _ hv_a]
    simp only [Φ, Market.cournotRev, hP_eq]
  -- Step 5: Assemble `sellerRev = pathRev`
  unfold pathRev ell at *
  rw [hrev_split, habove_eq_riv, habove_comb, mul_add, hcournot_eq]
  dsimp only [c0]
  ring

/-- **Border's Integral Identity in Quantity Coordinates (Appendix B, eq. (16))**:
For every `v ∈ [v_hat, 1]`,
`∫_v^1 F_riv(u)^(n - 1) θ_1(u) f(u) du = E(q(v)) + h_n(q(v)) + (T(v) - q(v)) * (1 - q(v))^(n - 1)`. -/
theorem prop3_border_identity {v : ℝ} (hv : v ∈ Icc C.v_hat 1) :
    ∫ u in v..1, (C.F_riv u) ^ (M.n - 1) * C.w1 u =
      excessSupply M C.t (C.q v) + h_n M.n (C.q v) + (C.T v - C.q v) * (1 - C.q v) ^ (M.n - 1) := by
  have hv_a : v ∈ Icc M.a 1 := ⟨le_trans C.v_hat_mem_Icc_a.1 hv.1, hv.2⟩
  have hv_ρ : ρ ≤ v := le_trans C.hρ_le_vhat hv.1
  let g : ℝ → ℝ := fun s => ((M.n : ℝ) - 1) * (C.F_riv s) ^ (M.n - 2) * C.w_riv s
  have hFriv_mem : ∀ u ∈ Icc v 1, C.F_riv u ∈ Icc (0 : ℝ) 1 := by
    intro u hu
    obtain ⟨j, hj⟩ := C.exists_rival
    rw [← C.hriv_symm j hj u ⟨le_trans hv_ρ hu.1, hu.2⟩]
    exact effDist_mem_Icc M C.θ j hu.2
  have hFriv_cont : ContinuousOn C.F_riv (Icc v 1) := by
    have heq : EqOn C.F_riv (fun u => 1 - C.q u) (Icc v 1) := fun _ _ => by unfold q; ring
    exact (continuousOn_const.sub (C.q_continuousOn_vhat.mono (Icc_subset_Icc_left hv.1))).congr heq
  have hw1_v : IntegrableOn C.w1 (Icc v 1) :=
    C.w1_integrableOn.mono_set (Icc_subset_Icc_left hv_a.1)
  have hwriv_v : IntegrableOn C.w_riv (Icc v 1) :=
    C.w_riv_integrableOn.mono_set (Icc_subset_Icc_left hv_a.1)
  have hg_int : IntegrableOn g (Icc v 1) := by
    have hcont : ContinuousOn (fun s => ((M.n : ℝ) - 1) * (C.F_riv s) ^ (M.n - 2)) (Icc v 1) :=
      continuousOn_const.mul (hFriv_cont.pow _)
    have hivl := ((intervalIntegrable_iff_integrableOn_Icc_of_le hv.2).mpr hwriv_v).continuousOn_mul
      (by rwa [uIcc_of_le hv.2])
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hv.2).mp hivl
  have hFpow_exp : ∀ u ∈ Icc v 1, (C.F_riv u) ^ (M.n - 1) =
      (C.F_riv v) ^ (M.n - 1) + ∫ s in v..u, g s := by
    intro u hu
    have h := C.F_riv_pow_sub_eq_integral hv ⟨le_trans hv.1 hu.1, hu.2⟩ hu.1
    rw [← intervalIntegral.integral_const_mul] at h
    have heq : ∫ s in v..u, ((M.n : ℝ) - 1) * ((C.F_riv s) ^ (M.n - 2) * C.w_riv s) =
        ∫ s in v..u, g s := by congr 1; ext s; simp [g, mul_assoc]
    rw [heq] at h; linarith
  have hpart : ∫ u in v..1, (C.F_riv u) ^ (M.n - 1) * C.w1 u =
      (C.F_riv v) ^ (M.n - 1) * C.T v + ∫ s in v..1, g s * C.T s := by
    have hcongr : ∫ u in v..1, (C.F_riv u) ^ (M.n - 1) * C.w1 u =
        ∫ u in v..1, ((C.F_riv v) ^ (M.n - 1) * C.w1 u + (∫ s in v..u, g s) * C.w1 u) := by
      rw [intervalIntegral.integral_of_le hv.2, intervalIntegral.integral_of_le hv.2,
        ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc]
      exact setIntegral_congr_fun measurableSet_Icc (fun u hu => by rw [hFpow_exp u hu, add_mul])
    have hint1 : IntervalIntegrable (fun u => (C.F_riv v) ^ (M.n - 1) * C.w1 u) volume v 1 :=
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hv.2).mpr hw1_v).const_mul _
    have hint2 : IntervalIntegrable (fun u => (∫ s in v..u, g s) * C.w1 u) volume v 1 := by
      have hprim_cont : ContinuousOn (fun u => ∫ s in v..u, g s) (uIcc v 1) :=
        intervalIntegral.continuousOn_primitive_interval (by rwa [uIcc_of_le hv.2])
      exact ((intervalIntegrable_iff_integrableOn_Icc_of_le hv.2).mpr hw1_v).continuousOn_mul hprim_cont
    rw [hcongr, intervalIntegral.integral_add hint1 hint2, intervalIntegral.integral_const_mul,
      integral_integral_mul_swap hv.2 hg_int hw1_v]
    have hT_eq : ∀ s, ∫ u in s..1, C.w1 u = C.T s := fun _ => by unfold T F1 effDist w1; ring
    simp_rw [hT_eq]
  have hqv_mem : C.q v ∈ Icc (0 : ℝ) C.q0 :=
    ⟨by rw [← C.q_one]; exact C.q_antitoneOn_vhat hv (right_mem_Icc.mpr C.hv_hat_mem.2) hv.2,
     C.q_antitoneOn_vhat (left_mem_Icc.mpr C.hv_hat_mem.2) hv hv.1⟩
  have hchg : ∫ s in v..1, g s * C.T s =
      ((M.n : ℝ) - 1) * ∫ u in (0 : ℝ)..(C.q v), C.t u * (1 - u) ^ (M.n - 2) := by
    let Φ : ℝ → ℝ → ℝ → ℝ := fun _ Tval qval => ((M.n : ℝ) - 1) * (Tval * (1 - qval) ^ (M.n - 2))
    have hΦ_meas : AEStronglyMeasurable (fun u => Φ (C.vOfQ u) (C.t u) u)
        (volume.restrict (Icc (0 : ℝ) (C.q v))) := by
      have ht_int : IntervalIntegrable C.t volume 0 (C.q v) :=
        ((C.t_monotoneOn.mono (Icc_subset_Icc_right hqv_mem.2)).mono (by rw [uIcc_of_le hqv_mem.1])).intervalIntegrable
      have ht_m : AEStronglyMeasurable C.t (volume.restrict (Icc (0 : ℝ) (C.q v))) :=
        ((intervalIntegrable_iff_integrableOn_Icc_of_le hqv_mem.1).mp ht_int).aestronglyMeasurable
      exact ((ht_m.mul (Continuous.aestronglyMeasurable (by fun_prop))).const_mul _)
    have h1 := C.integral_comp_q_of_v hv hΦ_meas
    have hlhs : ∫ s in v..1, g s * C.T s = ∫ s in v..1, Φ s (C.T s) (C.q s) * C.w_riv s := by
      congr 1; ext s
      simp only [Φ, g, q]
      have hsub : 1 - (1 - C.F_riv s) = C.F_riv s := by ring
      rw [hsub]; ring
    rw [hlhs, h1]
    simp only [Φ, intervalIntegral.integral_const_mul]
  rw [hpart, hchg]
  have hu_pow := integral_u_mul_one_sub_pow M.hn (C.q v)
  have ht_int : IntervalIntegrable (fun u => C.t u * (1 - u) ^ (M.n - 2)) volume 0 (C.q v) :=
    (((C.t_monotoneOn.mono (Icc_subset_Icc_right hqv_mem.2)).mono (by rw [uIcc_of_le hqv_mem.1])).intervalIntegrable).mul_continuousOn
      (Continuous.continuousOn (by fun_prop))
  have hu_int : IntervalIntegrable (fun u => u * (1 - u) ^ (M.n - 2)) volume 0 (C.q v) :=
    Continuous.intervalIntegrable (by fun_prop) 0 (C.q v)
  have hexcess : excessSupply M C.t (C.q v) =
      (((M.n : ℝ) - 1) * ∫ u in (0 : ℝ)..(C.q v), C.t u * (1 - u) ^ (M.n - 2)) -
      (((M.n : ℝ) - 1) * ∫ u in (0 : ℝ)..(C.q v), u * (1 - u) ^ (M.n - 2)) := by
    unfold excessSupply
    rw [← mul_sub, ← intervalIntegral.integral_sub ht_int hu_int]
    congr 1; congr 1; ext u; ring
  have h1q : 1 - C.q v = C.F_riv v := by unfold q; ring
  rw [hexcess, hu_pow, h1q]
  ring

/-- **Proposition 3 (Border's Feasibility Constraint in Quantity Coordinates, eq. (7))**:
`∫_0^q (t(u) - u)(1 - u)^(n - 2) du ≤ 0` for all `q ∈ [0, q0]`. -/
theorem prop3_border_q : BorderFeasible M C.q0 C.t := by
  intro qval hq
  have hv_spec := C.vOfQ_spec hq
  have hv := hv_spec.1
  have hv_a : C.vOfQ qval ∈ Icc M.a 1 := ⟨le_trans C.v_hat_mem_Icc_a.1 hv.1, hv.2⟩
  have hid := C.prop3_border_identity hv
  rw [hv_spec.2] at hid
  -- Compare `∫_{v(q)}^1 F_riv^(n-1) w1` with `∫_{v(q)}^1 x_1 w1 ≤ h_n(T(v(q)))`
  have heq_alloc : ∫ u in (C.vOfQ qval)..1, (C.F_riv u) ^ (M.n - 1) * C.w1 u =
      ∫ u in (C.vOfQ qval)..1, alloc M mech C.F1 u * C.w1 u := by
    rw [intervalIntegral.integral_of_le hv.2, intervalIntegral.integral_of_le hv.2,
      ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc]
    refine integral_congr_ae ?_
    show ∀ᵐ u ∂(volume.restrict (Icc (C.vOfQ qval) 1)),
      (C.F_riv u) ^ (M.n - 1) * C.w1 u = alloc M mech C.F1 u * C.w1 u
    have hxa := C.hx_above
    rw [ae_restrict_iff' measurableSet_Icc] at hxa ⊢
    filter_upwards [hxa] with u hu hmem
    rcases eq_or_lt_of_le (C.θ.hnonneg C.j0 u) with h0 | hpos
    · simp [w1, ← h0]
    · have hF1eq : C.F1 = effDist M C.θ C.j0 := rfl
      rw [hF1eq, hu ⟨le_trans hv.1 hmem.1, hmem.2⟩ hpos]
  have hble : ∫ u in (C.vOfQ qval)..1, alloc M mech C.F1 u * C.w1 u ≤ h_n M.n (C.T (C.vOfQ qval)) :=
    hierarchical_border_le M mech C.θ C.j0 hv_a
  have hTv_mem : C.T (C.vOfQ qval) ∈ Icc (0 : ℝ) 1 := by
    have hF := effDist_mem_Icc M C.θ C.j0 hv.2
    unfold T F1; exact ⟨by linarith [hF.2], by linarith [hF.1]⟩
  have hqv_mem01 : qval ∈ Icc (0 : ℝ) 1 := ⟨hq.1, le_trans hq.2 C.q0_mem_Icc.2⟩
  have hconc := h_n_sub_le_tangent M.hn hTv_mem hqv_mem01
  have hE_nonpos : excessSupply M C.t qval ≤ 0 := by linarith
  unfold excessSupply at hE_nonpos
  exact nonpos_of_mul_nonpos_right hE_nonpos M.n_sub_one_pos_real

/-- **Lemma B.1 (Bottom-Boundary Excess Identity)**:
`E(q0) + η = ∫_{v_bar}^{v_hat} ((1 - q0)^(n - 1) - x_1(v)) θ_1(v) f(v) dv ≥ 0`. -/
theorem lemmaB1_excess_add_eta_eq :
    excessSupply M C.t C.q0 + convexityGap M.n C.q0 C.t0 =
      ∫ v in C.v_bar..C.v_hat, ((1 - C.q0) ^ (M.n - 1) - alloc M mech C.F1 v) * C.w1 v ∧
    0 ≤ excessSupply M C.t C.q0 + convexityGap M.n C.q0 C.t0 := by
  -- Apply `hierarchical_border_eq` at `C.v_bar`
  have hnopool : ∀ I ∈ mech.pools, I.α < C.v_bar → C.v_bar < I.β →
      effDist M C.θ C.j0 I.α = effDist M C.θ C.j0 C.v_bar := by
    intro I hI hα _
    have hI_in := mech.hpools_in I hI
    have hvbar_eq_a : C.v_bar = M.a := by
      unfold v_bar at hα ⊢
      have h1 : min mech.r ρ ≤ I.α := le_trans (min_le_left _ _) hI_in.1
      exact max_eq_right (by by_contra h; push Not at h; rw [max_eq_left h.le] at hα; linarith)
    rw [hvbar_eq_a] at hα ⊢
    exact effDist_eq_at_a M C.θ C.j0 hα.le
  have hbeq : ∫ u in C.v_bar..1, alloc M mech C.F1 u * C.w1 u = h_n M.n C.t0 :=
    hierarchical_border_eq M mech C.θ C.j0 C.v_bar_mem_Icc C.hθ_below_r hnopool
  have hF1_mono : MonotoneOn C.F1 (Iic 1) := effDist_monotoneOn M C.θ C.j0
  have hF1_mem : ∀ u ≤ 1, C.F1 u ∈ Icc (0 : ℝ) 1 := fun u hu => effDist_mem_Icc M C.θ C.j0 hu
  have hx_mono : MonotoneOn (alloc M mech C.F1) (Iic 1) := alloc_monotoneOn M mech hF1_mono hF1_mem
  have hx_int_full : IntervalIntegrable (fun u => alloc M mech C.F1 u * C.w1 u) volume C.v_bar 1 := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le C.v_bar_mem_Icc.2]
    have hw_on : IntegrableOn C.w1 (Icc C.v_bar 1) :=
      C.w1_integrableOn.mono_set (Icc_subset_Icc_left C.v_bar_mem_Icc.1)
    have hxm : AEStronglyMeasurable (alloc M mech C.F1) (volume.restrict (Icc C.v_bar 1)) :=
      ((intervalIntegrable_iff_integrableOn_Icc_of_le C.v_bar_mem_Icc.2).mp
        ((hx_mono.mono (by rw [uIcc_of_le C.v_bar_mem_Icc.2]; exact fun u hu => hu.2)).intervalIntegrable)).aestronglyMeasurable
    refine hw_on.mono' (hxm.mul hw_on.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    have hxu := alloc_mem_Icc M mech hF1_mono hF1_mem hu.2
    have hwu := C.w1_nonneg ⟨le_trans C.v_bar_mem_Icc.1 hu.1, hu.2⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hxu.1 hwu)]; nlinarith [hxu.2]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hx_int_full.mono_set (uIcc_subset_uIcc left_mem_uIcc (mem_uIcc_of_le C.v_bar_le_v_hat C.hv_hat_mem.2)))
    (hx_int_full.mono_set (uIcc_subset_uIcc (mem_uIcc_of_le C.v_bar_le_v_hat C.hv_hat_mem.2) right_mem_uIcc))
  have habove_eq : ∫ u in C.v_hat..1, alloc M mech C.F1 u * C.w1 u =
      excessSupply M C.t C.q0 + h_n M.n C.q0 + (C.T C.v_hat - C.q0) * (1 - C.q0) ^ (M.n - 1) := by
    have heq : ∫ u in C.v_hat..1, alloc M mech C.F1 u * C.w1 u =
        ∫ u in C.v_hat..1, (C.F_riv u) ^ (M.n - 1) * C.w1 u := by
      rw [intervalIntegral.integral_of_le C.hv_hat_mem.2, intervalIntegral.integral_of_le C.hv_hat_mem.2,
        ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc]
      refine integral_congr_ae ?_
      filter_upwards [C.hx_above] with u hu
      rcases eq_or_lt_of_le (C.θ.hnonneg C.j0 u) with h0 | hpos
      · simp [w1, ← h0]
      · have hF1eq : C.F1 = effDist M C.θ C.j0 := rfl
        rw [hF1eq, hu hpos]
    rw [heq]
    exact C.prop3_border_identity (left_mem_Icc.mpr C.hv_hat_mem.2)
  have hT_diff : C.t0 - C.T C.v_hat = ∫ v in C.v_bar..C.v_hat, C.w1 v := by
    have hw_ivl := (intervalIntegrable_iff_integrableOn_Icc_of_le M.ha1.le).mpr C.w1_integrableOn
    have hs := intervalIntegral.integral_add_adjacent_intervals
      (hw_ivl.mono_set (uIcc_subset_uIcc (mem_uIcc_of_le C.v_bar_mem_Icc.1 C.v_bar_mem_Icc.2)
        (mem_uIcc_of_le C.v_hat_mem_Icc_a.1 C.v_hat_mem_Icc_a.2)))
      (hw_ivl.mono_set (uIcc_subset_uIcc (mem_uIcc_of_le C.v_hat_mem_Icc_a.1 C.v_hat_mem_Icc_a.2) right_mem_uIcc))
    unfold t0 T F1 effDist
    dsimp only [w1] at hs ⊢
    linarith
  have hw_vh : IntervalIntegrable C.w1 volume C.v_bar C.v_hat :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le C.v_bar_le_v_hat).mpr
      (C.w1_integrableOn.mono_set (Icc_subset_Icc C.v_bar_mem_Icc.1 C.hv_hat_mem.2))
  have hδ_eq : ∫ v in C.v_bar..C.v_hat, ((1 - C.q0) ^ (M.n - 1) - alloc M mech C.F1 v) * C.w1 v =
      (1 - C.q0) ^ (M.n - 1) * (C.t0 - C.T C.v_hat) -
      ∫ v in C.v_bar..C.v_hat, alloc M mech C.F1 v * C.w1 v := by
    have heq : (fun v => ((1 - C.q0) ^ (M.n - 1) - alloc M mech C.F1 v) * C.w1 v) =
        fun v => (1 - C.q0) ^ (M.n - 1) * C.w1 v - alloc M mech C.F1 v * C.w1 v := by
      ext v; ring
    rw [heq, intervalIntegral.integral_sub (hw_vh.const_mul _)
        (hx_int_full.mono_set (uIcc_subset_uIcc left_mem_uIcc (mem_uIcc_of_le C.v_bar_le_v_hat C.hv_hat_mem.2))),
      intervalIntegral.integral_const_mul, ← hT_diff]
  have hid_main : excessSupply M C.t C.q0 + convexityGap M.n C.q0 C.t0 =
      ∫ v in C.v_bar..C.v_hat, ((1 - C.q0) ^ (M.n - 1) - alloc M mech C.F1 v) * C.w1 v := by
    unfold convexityGap
    linarith
  refine ⟨hid_main, ?_⟩
  rw [hid_main, intervalIntegral.integral_of_le C.v_bar_le_v_hat, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_nonneg measurableSet_Ioo (fun v hv => ?_)
  exact mul_nonneg (sub_nonneg.mpr (C.alloc_le_c0_below_vhat ⟨hv.1.le, hv.2⟩))
    (C.w1_nonneg ⟨le_trans C.v_bar_mem_Icc.1 hv.1.le, le_trans hv.2.le C.hv_hat_mem.2⟩)

/-- **Lemma B.1(i) (Indifferent Customers)**:
When the initial strict-preference segment is empty (`v_hat = v_bar`), `ℓ = 0` and
`E(q0) = -η(n, q0, t0)`. -/
theorem lemmaB1_indifferent (h : C.v_hat = C.v_bar) :
    C.ell = 0 ∧ excessSupply M C.t C.q0 = -convexityGap M.n C.q0 C.t0 := by
  have h1 : C.ell = 0 := by
    unfold ell t0
    rw [h, sub_self, mul_zero, intervalIntegral.integral_same, mul_zero, sub_self]
  have h2 := C.lemmaB1_excess_add_eta_eq.1
  rw [h, intervalIntegral.integral_same] at h2
  exact ⟨h1, by linarith⟩

/-- **Lemma B.1(ii) (Covered-Market Rent Lower Bound)**:
If the market is covered and rivals' reserve is slack (`ρ < M.a`), then
`0 ≤ E(q0) + η` and `n * M.a * (E(q0) + η) ≤ ℓ`.
Holds for EVERY unilateral deviation, including the `v_hat = 1, σ(1) > 0` corner case! -/
theorem lemmaB1_rent_lower_bound (hρa : ρ < M.a) :
    0 ≤ excessSupply M C.t C.q0 + convexityGap M.n C.q0 C.t0 ∧
    (M.n : ℝ) * M.a * (excessSupply M C.t C.q0 + convexityGap M.n C.q0 C.t0) ≤ C.ell := by
  have hB1 := C.lemmaB1_excess_add_eta_eq
  refine ⟨hB1.2, ?_⟩
  rw [hB1.1]
  have hvbar_eq_a : C.v_bar = M.a := by
    unfold v_bar
    exact max_eq_right (le_trans (min_le_right _ _) hρa.le)
  have hT_diff : C.t0 - C.T C.v_hat = ∫ v in C.v_bar..C.v_hat, C.w1 v := by
    have hw_ivl := (intervalIntegrable_iff_integrableOn_Icc_of_le M.ha1.le).mpr C.w1_integrableOn
    have hs := intervalIntegral.integral_add_adjacent_intervals
      (hw_ivl.mono_set (uIcc_subset_uIcc (mem_uIcc_of_le C.v_bar_mem_Icc.1 C.v_bar_mem_Icc.2)
        (mem_uIcc_of_le C.v_hat_mem_Icc_a.1 C.v_hat_mem_Icc_a.2)))
      (hw_ivl.mono_set (uIcc_subset_uIcc (mem_uIcc_of_le C.v_hat_mem_Icc_a.1 C.v_hat_mem_Icc_a.2) right_mem_uIcc))
    unfold t0 T F1 effDist
    dsimp only [w1] at hs ⊢
    linarith
  have hw_int : IntervalIntegrable C.w1 volume C.v_bar C.v_hat :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le C.v_bar_le_v_hat).mpr
      (C.w1_integrableOn.mono_set (Icc_subset_Icc C.v_bar_mem_Icc.1 C.hv_hat_mem.2))
  have hF1_mono : MonotoneOn C.F1 (Iic 1) := effDist_monotoneOn M C.θ C.j0
  have hF1_mem : ∀ u ≤ 1, C.F1 u ∈ Icc (0 : ℝ) 1 := fun u hu => effDist_mem_Icc M C.θ C.j0 hu
  have hx_mono : MonotoneOn (alloc M mech C.F1) (Iic 1) := alloc_monotoneOn M mech hF1_mono hF1_mem
  have hx_ivl : IntervalIntegrable (alloc M mech C.F1) volume 0 1 :=
    (hx_mono.mono (by rw [uIcc_of_le zero_le_one]; exact fun u hu => hu.2)).intervalIntegrable
  have hx_w1_int : IntervalIntegrable (fun v => alloc M mech C.F1 v * C.w1 v) volume C.v_bar C.v_hat := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le C.v_bar_le_v_hat]
    have hw_on : IntegrableOn C.w1 (Icc C.v_bar C.v_hat) :=
      C.w1_integrableOn.mono_set (Icc_subset_Icc C.v_bar_mem_Icc.1 C.hv_hat_mem.2)
    have hxm : AEStronglyMeasurable (alloc M mech C.F1) (volume.restrict (Icc C.v_bar C.v_hat)) :=
      ((intervalIntegrable_iff_integrableOn_Icc_of_le C.v_bar_le_v_hat).mp
        (hx_ivl.mono_set (uIcc_subset_uIcc (mem_uIcc_of_le (le_trans M.ha0 C.v_bar_mem_Icc.1) C.v_bar_mem_Icc.2)
          (mem_uIcc_of_le (le_trans M.ha0 C.v_hat_mem_Icc_a.1) C.hv_hat_mem.2)))).aestronglyMeasurable
    refine hw_on.mono' (hxm.mul hw_on.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    have hxv := alloc_mem_Icc M mech hF1_mono hF1_mem (le_trans hv.2 C.hv_hat_mem.2)
    have hwv := C.w1_nonneg ⟨le_trans C.v_bar_mem_Icc.1 hv.1, le_trans hv.2 C.hv_hat_mem.2⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hxv.1 hwv)]; nlinarith [hxv.2]
  have hpay_int : IntervalIntegrable (fun v => payment M mech C.F1 v * C.w1 v) volume C.v_bar C.v_hat := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le C.v_bar_le_v_hat]
    have hx_meas : AEStronglyMeasurable (alloc M mech C.F1) (volume.restrict (Icc C.v_bar C.v_hat)) :=
      ((intervalIntegrable_iff_integrableOn_Icc_of_le C.v_bar_le_v_hat).mp
        (hx_ivl.mono_set (uIcc_subset_uIcc (mem_uIcc_of_le (le_trans M.ha0 C.v_bar_mem_Icc.1) C.v_bar_mem_Icc.2)
          (mem_uIcc_of_le (le_trans M.ha0 C.v_hat_mem_Icc_a.1) C.hv_hat_mem.2)))).aestronglyMeasurable
    have hs_cont : ContinuousOn (surplus M mech C.F1) (Icc C.v_bar C.v_hat) := by
      have h1 := intervalIntegral.continuousOn_primitive_interval
        ((intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp hx_ivl |> fun h => by rwa [uIcc_of_le zero_le_one])
      rw [uIcc_of_le zero_le_one] at h1
      exact h1.mono (Icc_subset_Icc (le_trans M.ha0 C.v_bar_mem_Icc.1) C.hv_hat_mem.2)
    have hpm : AEStronglyMeasurable (payment M mech C.F1) (volume.restrict (Icc C.v_bar C.v_hat)) :=
      ((continuousOn_id.aestronglyMeasurable measurableSet_Icc).mul hx_meas).sub
        (hs_cont.aestronglyMeasurable measurableSet_Icc)
    have hw_on : IntegrableOn C.w1 (Icc C.v_bar C.v_hat) :=
      C.w1_integrableOn.mono_set (Icc_subset_Icc C.v_bar_mem_Icc.1 C.hv_hat_mem.2)
    refine (hw_on.const_mul 2).mono' (hpm.mul hw_on.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    have hv01 : v ∈ Icc (0 : ℝ) 1 := ⟨le_trans M.ha0 (le_trans C.v_bar_mem_Icc.1 hv.1), le_trans hv.2 C.hv_hat_mem.2⟩
    have hxv := alloc_mem_Icc M mech hF1_mono hF1_mem hv01.2
    have hsv_nn : 0 ≤ surplus M mech C.F1 v :=
      intervalIntegral.integral_nonneg hv01.1 (fun u hu => (alloc_mem_Icc M mech hF1_mono hF1_mem (le_trans hu.2 hv01.2)).1)
    have hsv_le : surplus M mech C.F1 v ≤ 1 := by
      calc ∫ u in (0 : ℝ)..v, alloc M mech C.F1 u
          ≤ ∫ _ in (0 : ℝ)..v, (1 : ℝ) :=
            intervalIntegral.integral_mono_on hv01.1
              (hx_ivl.mono_set (uIcc_subset_uIcc left_mem_uIcc (mem_uIcc_of_le hv01.1 hv01.2)))
              intervalIntegrable_const (fun u hu => (alloc_mem_Icc M mech hF1_mono hF1_mem (le_trans hu.2 hv01.2)).2)
        _ = v := by simp
        _ ≤ 1 := hv01.2
    have hpay_abs : |payment M mech C.F1 v| ≤ 2 := by
      unfold payment; rw [abs_le]; constructor <;> nlinarith [hv01.1, hv01.2, hxv.1, hxv.2]
    have hw_nn : 0 ≤ C.w1 v := C.w1_nonneg ⟨le_trans C.v_bar_mem_Icc.1 hv.1, le_trans hv.2 C.hv_hat_mem.2⟩
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw_nn]; nlinarith
  have hδ_int : IntervalIntegrable (fun v => ((1 - C.q0) ^ (M.n - 1) - alloc M mech C.F1 v) * C.w1 v)
      volume C.v_bar C.v_hat := by
    have heq : (fun v => ((1 - C.q0) ^ (M.n - 1) - alloc M mech C.F1 v) * C.w1 v) =
        fun v => (1 - C.q0) ^ (M.n - 1) * C.w1 v - alloc M mech C.F1 v * C.w1 v := by ext v; ring
    rw [heq]; exact (hw_int.const_mul _).sub hx_w1_int
  have hLHS : (M.n : ℝ) * M.a * ∫ v in C.v_bar..C.v_hat, ((1 - C.q0) ^ (M.n - 1) - alloc M mech C.F1 v) * C.w1 v =
      (M.n : ℝ) * ∫ v in C.v_bar..C.v_hat, M.a * (((1 - C.q0) ^ (M.n - 1) - alloc M mech C.F1 v) * C.w1 v) := by
    rw [mul_assoc, intervalIntegral.integral_const_mul]
  have hRHS : C.ell = (M.n : ℝ) * ∫ v in C.v_bar..C.v_hat,
      (ρ * (1 - C.q0) ^ (M.n - 1) * C.w1 v - payment M mech C.F1 v * C.w1 v) := by
    unfold ell
    rw [hT_diff,
      show (M.n : ℝ) * ρ * (1 - C.q0) ^ (M.n - 1) * (∫ v in C.v_bar..C.v_hat, C.w1 v) -
          (M.n : ℝ) * (∫ v in C.v_bar..C.v_hat, payment M mech C.F1 v * C.w1 v) =
        (M.n : ℝ) * ((ρ * (1 - C.q0) ^ (M.n - 1)) * (∫ v in C.v_bar..C.v_hat, C.w1 v) -
          (∫ v in C.v_bar..C.v_hat, payment M mech C.F1 v * C.w1 v)) by ring,
      ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (hw_int.const_mul _) hpay_int]
  rw [hLHS, hRHS]
  refine mul_le_mul_of_nonneg_left ?_ M.n_pos_real.le
  rw [intervalIntegral.integral_of_le C.v_bar_le_v_hat, intervalIntegral.integral_of_le C.v_bar_le_v_hat,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_mono_on
    (((intervalIntegrable_iff_integrableOn_Ioo_of_le C.v_bar_le_v_hat).mp (hδ_int.const_mul M.a)))
    (((intervalIntegrable_iff_integrableOn_Ioo_of_le C.v_bar_le_v_hat).mp ((hw_int.const_mul _).sub hpay_int)))
    measurableSet_Ioo (fun v hv => ?_)
  have hv_mem : v ∈ Ico C.v_bar C.v_hat := ⟨hv.1.le, hv.2⟩
  have hv_ge_a : M.a ≤ v := by rw [← hvbar_eq_a]; exact hv.1.le
  have hv_ge_max : max ρ C.v_bar ≤ v := max_le (le_trans hρa.le hv_ge_a) hv.1.le
  have hid := C.rent_excess_identity ⟨hv_ge_max, hv.2.le⟩
  have hσ_nn : 0 ≤ surplus M mech C.F1 C.v_hat - surplus M (SPA ρ hρ0 hρ1.le) C.F_riv C.v_hat :=
    sub_nonneg.mpr (C.hs_below (hv.1.trans hv.2) C.v_hat (right_mem_Icc.mpr C.hv_hat_mem.1))
  have hδ_nn : 0 ≤ (1 - C.q0) ^ (M.n - 1) - alloc M mech C.F1 v :=
    sub_nonneg.mpr (C.alloc_le_c0_below_vhat hv_mem)
  have hint_nn : 0 ≤ ∫ u in v..C.v_hat, ((1 - C.q0) ^ (M.n - 1) - alloc M mech C.F1 u) := by
    rw [intervalIntegral.integral_of_le hv.2.le, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_nonneg measurableSet_Ioo (fun u hu =>
      sub_nonneg.mpr (C.alloc_le_c0_below_vhat ⟨le_trans hv.1.le hu.1.le, hu.2⟩))
  have hw_nn : 0 ≤ C.w1 v := C.w1_nonneg ⟨hv_ge_a, le_trans hv.2.le C.hv_hat_mem.2⟩
  have hpt : M.a * ((1 - C.q0) ^ (M.n - 1) - alloc M mech C.F1 v) ≤
      ρ * (1 - C.q0) ^ (M.n - 1) - payment M mech C.F1 v := by nlinarith
  nlinarith

end UnilateralContinuation

/-- Top-level wrapper for Proposition 3 (quantity-path revenue identity). -/
theorem prop3_quantity_path_rev {M : Market} {ρ : ℝ} {hρ0 : 0 ≤ ρ} {hρ1 : ρ < 1}
    {mech : HierarchicalMech} (C : UnilateralContinuation M ρ hρ0 hρ1 mech)
    (P : M.InverseDemand) :
    sellerRev M mech C.θ C.j0 = pathRev M P.P ρ C.q0 C.t0 C.ell C.t ∧ 0 ≤ C.ell :=
  ⟨C.prop3_quantity_path_rev P, C.ell_nonneg⟩

/-- Top-level wrapper for Proposition 3 (Border's constraint in quantity coordinates). -/
theorem prop3_border_q {M : Market} {ρ : ℝ} {hρ0 : 0 ≤ ρ} {hρ1 : ρ < 1}
    {mech : HierarchicalMech} (C : UnilateralContinuation M ρ hρ0 hρ1 mech) :
    BorderFeasible M C.q0 C.t :=
  C.prop3_border_q

/-- Top-level wrapper for Lemma B.1(i) (indifferent customers: `v_hat = v_bar` implies `ℓ = 0`
and `E(q0) = -η(n, q0, t0)`). -/
theorem lemmaB1_indifferent {M : Market} {ρ : ℝ} {hρ0 : 0 ≤ ρ} {hρ1 : ρ < 1}
    {mech : HierarchicalMech} (C : UnilateralContinuation M ρ hρ0 hρ1 mech)
    (h : C.v_hat = C.v_bar) :
    C.ell = 0 ∧ excessSupply M C.t C.q0 = -convexityGap M.n C.q0 C.t0 :=
  C.lemmaB1_indifferent h

/-- Top-level wrapper for Lemma B.1(ii) (covered-market rent lower bound, including `v_hat = 1, σ(1) > 0`). -/
theorem lemmaB1_rent_lower_bound {M : Market} {ρ : ℝ} {hρ0 : 0 ≤ ρ} {hρ1 : ρ < 1}
    {mech : HierarchicalMech} (C : UnilateralContinuation M ρ hρ0 hρ1 mech)
    (hρa : ρ < M.a) :
    0 ≤ excessSupply M C.t C.q0 + convexityGap M.n C.q0 C.t0 ∧
    (M.n : ℝ) * M.a * (excessSupply M C.t C.q0 + convexityGap M.n C.q0 C.t0) ≤ C.ell :=
  C.lemmaB1_rent_lower_bound hρa

/-! ### Section 5: Theorem 1 — Interior Pools and Cournot's Condition -/

/-- Part (i) of Theorem 1 at the quantity-path level: subtracting `SPA(ρ)^m` (`t = id`)
from an interior-pool path with identical `(q_ρ, q_ρ)` and `ℓ = 0` yields the exact
Cournot difference integral (eq. (8)). -/
theorem theorem1_part_i_exact_diff (M : Market) (P : M.InverseDemand)
    (ρ q_ρ : ℝ) {t : ℝ → ℝ}
    (ht_int : IntervalIntegrable (fun q => M.cournotRev P.P (t q) q * M.W q) volume 0 q_ρ)
    (hid_int : IntervalIntegrable (fun q => M.cournotRev P.P q q * M.W q) volume 0 q_ρ) :
    pathRev M P.P ρ q_ρ q_ρ 0 t - pathRev M P.P ρ q_ρ q_ρ 0 id =
      ∫ q in (0 : ℝ)..q_ρ, (M.cournotRev P.P (t q) q - M.cournotRev P.P q q) * M.W q := by
  unfold pathRev
  simp only [id_eq, sub_zero]
  rw [show (M.n : ℝ) * ρ * q_ρ * (1 - q_ρ) ^ (M.n - 1) +
        (∫ q in (0 : ℝ)..q_ρ, M.cournotRev P.P (t q) q * M.W q) -
      ((M.n : ℝ) * ρ * q_ρ * (1 - q_ρ) ^ (M.n - 1) +
        (∫ q in (0 : ℝ)..q_ρ, M.cournotRev P.P q q * M.W q)) =
      (∫ q in (0 : ℝ)..q_ρ, M.cournotRev P.P (t q) q * M.W q) -
        (∫ q in (0 : ℝ)..q_ρ, M.cournotRev P.P q q * M.W q) by ring]
  rw [← intervalIntegral.integral_sub ht_int hid_int]
  congr 1; ext q; ring

/-- Single merged-band bound for Theorem 1:
On any merged band `[q_lo, q_hi] ⊆ [0, 1/m]` where `t` stays within `[q_lo, q_hi]`
(so `t(q) + (m - 1)q ∈ [m q_lo, m q_hi]`), `E` is nonpositive on `[q_lo, q_hi]` relative to
`q_lo` and has weighted mean zero on `[q_lo, q_hi]`, and `ψ_m` is nondecreasing on
`[P(m q_hi), P(m q_lo)]`, the band's contribution to `D` is nonpositive for every `n ≥ 2`. -/
theorem theorem1_single_band (M : Market) (P : M.InverseDemand)
    {q_lo q_hi : ℝ} (hq_lo : 0 ≤ q_lo) (hle : q_lo ≤ q_hi)
    (hq_hi : (M.m : ℝ) * q_hi ≤ 1)
    {t : ℝ → ℝ}
    (ht_range : ∀ q ∈ Icc q_lo q_hi, t q ∈ Icc q_lo q_hi)
    (ht_int : IntervalIntegrable t volume q_lo q_hi)
    (hPit_int : IntervalIntegrable (fun q => M.cournotRev P.P (t q) q * M.W q) volume q_lo q_hi)
    (hborder : ∀ q ∈ Icc q_lo q_hi, ∫ u in q_lo..q, (t u - u) * (1 - u) ^ (M.n - 2) ≤ 0)
    (hzeromean : ∫ u in q_lo..q_hi, (t u - u) * (1 - u) ^ (M.n - 2) = 0)
    (hpsi : MonotoneOn M.psi (Icc (P.P ((M.m : ℝ) * q_hi)) (P.P ((M.m : ℝ) * q_lo)))) :
    ∫ q in q_lo..q_hi, (M.cournotRev P.P (t q) q - M.cournotRev P.P q q) * M.W q ≤ 0 := by
  have hm_pos : (0 : ℝ) < M.m := M.m_pos_real
  have hm1_pos : (0 : ℝ) < (M.m : ℝ) - 1 := M.m_sub_one_pos_real
  have hq_hi_le_one : q_hi ≤ 1 := by
    have : (2 : ℝ) ≤ M.m := by exact_mod_cast M.hm
    nlinarith
  have hz_lo : 0 ≤ (M.m : ℝ) * q_lo := by positivity
  let g : ℝ → ℝ := fun q => M.psi (P.P ((M.m : ℝ) * q))
  let φ : ℝ → ℝ := fun q => (t q - q) * M.W q
  have hg_cont : ContinuousOn g (Icc q_lo q_hi) := by
    have hmul : ContinuousOn (fun q : ℝ => (M.m : ℝ) * q) (Icc q_lo q_hi) :=
      continuousOn_const.mul continuousOn_id
    have hP : ContinuousOn (fun q => P.P ((M.m : ℝ) * q)) (Icc q_lo q_hi) :=
      P.hP_cont.comp hmul (fun q hq => ⟨by nlinarith [hq.1], by nlinarith [hq.2]⟩)
    exact M.psi_continuousOn.comp hP (fun q hq =>
      P.hP_mem _ ⟨by nlinarith [hq.1], by nlinarith [hq.2]⟩)
  have hPiq_cont : ContinuousOn (fun q => M.cournotRev P.P q q * M.W q) (Icc q_lo q_hi) := by
    unfold Market.cournotRev
    have haff : ContinuousOn (fun q : ℝ => q + ((M.m : ℝ) - 1) * q) (Icc q_lo q_hi) :=
      continuousOn_id.add (continuousOn_const.mul continuousOn_id)
    have hP : ContinuousOn (fun q => P.P (q + ((M.m : ℝ) - 1) * q)) (Icc q_lo q_hi) :=
      P.hP_cont.comp haff (fun q hq => ⟨by nlinarith [hq.1], by nlinarith [hq.2]⟩)
    exact (continuousOn_id.mul hP).mul M.W_continuous.continuousOn
  have hPiq_int : IntervalIntegrable (fun q => M.cournotRev P.P q q * M.W q) volume q_lo q_hi :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hle).mpr hPiq_cont.integrableOn_Icc
  have hφ_int : IntervalIntegrable φ volume q_lo q_hi := by
    have h1 : IntervalIntegrable (fun q => t q - q) volume q_lo q_hi :=
      ht_int.sub (continuous_id.intervalIntegrable q_lo q_hi)
    exact h1.mul_continuousOn (by rw [uIcc_of_le hle]; exact M.W_continuous.continuousOn)
  have hgφ_int : IntervalIntegrable (fun q => g q * φ q) volume q_lo q_hi :=
    hφ_int.continuousOn_mul (by rw [uIcc_of_le hle]; exact hg_cont)
  have hlhs_int : IntervalIntegrable
      (fun q => (M.cournotRev P.P (t q) q - M.cournotRev P.P q q) * M.W q) volume q_lo q_hi := by
    have heq : (fun q => (M.cournotRev P.P (t q) q - M.cournotRev P.P q q) * M.W q) =
        fun q => M.cournotRev P.P (t q) q * M.W q - M.cournotRev P.P q q * M.W q := by
      ext q; ring
    rw [heq]; exact hPit_int.sub hPiq_int
  have hpt : ∀ q ∈ Icc q_lo q_hi,
      (M.cournotRev P.P (t q) q - M.cournotRev P.P q q) * M.W q ≤ g q * φ q := by
    intro q hq
    have htq := ht_range q hq
    have htb := tangent_bound_diag M P (q := q) (t := t q) hz_lo hq_hi
      (⟨by nlinarith [htq.1, hq.1], by nlinarith [htq.2, hq.2]⟩)
      (⟨by nlinarith [hq.1], by nlinarith [hq.2]⟩) hpsi
    have hW_nn : 0 ≤ M.W q := M.W_nonneg (le_trans hq.2 hq_hi_le_one)
    calc (M.cournotRev P.P (t q) q - M.cournotRev P.P q q) * M.W q
        ≤ (M.psi (P.P ((M.m : ℝ) * q)) * (t q - q)) * M.W q :=
          mul_le_mul_of_nonneg_right htb hW_nn
      _ = g q * φ q := by simp only [g, φ]; ring
  have hg_anti : AntitoneOn g (Icc q_lo q_hi) := by
    intro q₁ hq₁ q₂ hq₂ hq12
    have hP_anti := P.hP_strictAnti.antitoneOn
    have hz1 : (M.m : ℝ) * q₁ ∈ Icc (0 : ℝ) 1 := ⟨by nlinarith [hq₁.1], by nlinarith [hq₁.2]⟩
    have hz2 : (M.m : ℝ) * q₂ ∈ Icc (0 : ℝ) 1 := ⟨by nlinarith [hq₂.1], by nlinarith [hq₂.2]⟩
    have hzlo : (M.m : ℝ) * q_lo ∈ Icc (0 : ℝ) 1 := ⟨hz_lo, by nlinarith⟩
    have hzhi : (M.m : ℝ) * q_hi ∈ Icc (0 : ℝ) 1 := ⟨by nlinarith, hq_hi⟩
    have hv1 : P.P ((M.m : ℝ) * q₁) ∈ Icc (P.P ((M.m : ℝ) * q_hi)) (P.P ((M.m : ℝ) * q_lo)) :=
      ⟨hP_anti hz1 hzhi (by nlinarith [hq₁.2]), hP_anti hzlo hz1 (by nlinarith [hq₁.1])⟩
    have hv2 : P.P ((M.m : ℝ) * q₂) ∈ Icc (P.P ((M.m : ℝ) * q_hi)) (P.P ((M.m : ℝ) * q_lo)) :=
      ⟨hP_anti hz2 hzhi (by nlinarith [hq₂.2]), hP_anti hzlo hz2 (by nlinarith [hq₂.1])⟩
    exact hpsi hv2 hv1 (hP_anti hz1 hz2 (by nlinarith))
  have hE_nonpos : ∀ q ∈ Icc q_lo q_hi, ∫ u in q_lo..q, φ u ≤ 0 := by
    intro q hq
    have hrew : ∀ u, φ u = ((M.n : ℝ) * ((M.n : ℝ) - 1)) * ((t u - u) * (1 - u) ^ (M.n - 2)) := by
      intro u; simp only [φ, Market.W]; ring
    simp_rw [hrew, intervalIntegral.integral_const_mul]
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg M.n_pos_real.le M.n_sub_one_pos_real.le) (hborder q hq)
  have hE_zero : ∫ u in q_lo..q_hi, φ u = 0 := by
    have hrew : ∀ u, φ u = ((M.n : ℝ) * ((M.n : ℝ) - 1)) * ((t u - u) * (1 - u) ^ (M.n - 2)) := by
      intro u; simp only [φ, Market.W]; ring
    simp_rw [hrew, intervalIntegral.integral_const_mul]
    rw [hzeromean, mul_zero]
  calc ∫ q in q_lo..q_hi, (M.cournotRev P.P (t q) q - M.cournotRev P.P q q) * M.W q
      ≤ ∫ q in q_lo..q_hi, g q * φ q :=
        intervalIntegral.integral_mono_on hle hlhs_int hgφ_int hpt
    _ ≤ g q_hi * ∫ u in q_lo..q_hi, φ u :=
        integral_antitone_mul_le hle hg_anti hφ_int hgφ_int hE_nonpos
    _ = 0 := by rw [hE_zero, mul_zero]

/-- **Theorem 1 (Interior Pools and Cournot's Condition — Multi-Band Version)**:
For any finite collection of pairwise disjoint merged bands `bands` in `[0, q_ρ]`
(with `m * q_ρ ≤ 1`), if `t` is nondecreasing on `[0, q_ρ]`, equals `q` off the open bands,
is Border-feasible on `[0, q_ρ]`, has `E = 0` at every band endpoint (equivalently, weighted
mean zero on each band and zero excess off the bands), and `ψ_m` is nondecreasing on each
band `[P(m q_hi), P(m q_lo)]`, then:
1. `pathRev M P.P ρ q_ρ q_ρ 0 t - pathRev M P.P ρ q_ρ q_ρ 0 id = ∫_0^{q_ρ} [Π(t(q), q) - Π(q, q)] W(q) dq`, and
2. `D ≤ 0` for every `n ≥ 2`. -/
theorem theorem1_interior_pools_cournot (M : Market) (P : M.InverseDemand)
    (ρ q_ρ : ℝ) (hq_ρ0 : 0 ≤ q_ρ) (hq_ρ_le : (M.m : ℝ) * q_ρ ≤ 1)
    (bands : List (ℝ × ℝ))
    (hbands_in : ∀ b ∈ bands, 0 ≤ b.1 ∧ b.1 ≤ b.2 ∧ b.2 ≤ q_ρ)
    (hbands_disj : bands.Pairwise (fun b₁ b₂ => b₁.2 ≤ b₂.1 ∨ b₂.2 ≤ b₁.1))
    {t : ℝ → ℝ}
    (ht_mono : MonotoneOn t (Icc (0 : ℝ) q_ρ))
    (ht_off : ∀ q ∈ Icc (0 : ℝ) q_ρ, (∀ b ∈ bands, ¬(b.1 < q ∧ q < b.2)) → t q = q)
    (hborder : BorderFeasible M q_ρ t)
    (hend : ∀ b ∈ bands, excessSupply M t b.1 = 0 ∧ excessSupply M t b.2 = 0)
    (hpsi : ∀ b ∈ bands, MonotoneOn M.psi (Icc (P.P ((M.m : ℝ) * b.2)) (P.P ((M.m : ℝ) * b.1)))) :
    pathRev M P.P ρ q_ρ q_ρ 0 t - pathRev M P.P ρ q_ρ q_ρ 0 id =
      ∫ q in (0 : ℝ)..q_ρ, (M.cournotRev P.P (t q) q - M.cournotRev P.P q q) * M.W q ∧
    ∫ q in (0 : ℝ)..q_ρ, (M.cournotRev P.P (t q) q - M.cournotRev P.P q q) * M.W q ≤ 0 := by
  have hm_pos : (0 : ℝ) < M.m := M.m_pos_real
  have hm1_pos : (0 : ℝ) < (M.m : ℝ) - 1 := M.m_sub_one_pos_real
  have ht_bounds : ∀ q ∈ Icc (0 : ℝ) q_ρ, t q ∈ Icc (0 : ℝ) q_ρ := by
    intro q hq
    have h0 : t 0 = 0 := ht_off 0 (left_mem_Icc.mpr hq_ρ0) (fun b hb ⟨h1, _⟩ => by linarith [(hbands_in b hb).1])
    have h1 : t q_ρ = q_ρ := ht_off q_ρ (right_mem_Icc.mpr hq_ρ0) (fun b hb ⟨_, h2⟩ => by linarith [(hbands_in b hb).2.2])
    exact ⟨by rw [← h0]; exact ht_mono (left_mem_Icc.mpr hq_ρ0) hq hq.1,
           by rw [← h1]; exact ht_mono hq (right_mem_Icc.mpr hq_ρ0) hq.2⟩
  have ht_int : IntervalIntegrable t volume 0 q_ρ :=
    (ht_mono.mono (by rw [uIcc_of_le hq_ρ0])).intervalIntegrable
  -- Integrability of `Π(t(q), q) * W(q)` (bounded & a.e. strongly measurable since `t` is monotone)
  have hPit_int : IntervalIntegrable (fun q => M.cournotRev P.P (t q) q * M.W q) volume 0 q_ρ := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hq_ρ0]
    have ht_meas : AEMeasurable t (volume.restrict (Icc (0 : ℝ) q_ρ)) :=
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hq_ρ0).mp ht_int).aemeasurable
    have harg_meas : AEMeasurable (fun q => t q + ((M.m : ℝ) - 1) * q) (volume.restrict (Icc (0 : ℝ) q_ρ)) :=
      ht_meas.add (aemeasurable_id.const_mul _)
    have harg_mem : ∀ q ∈ Icc (0 : ℝ) q_ρ, t q + ((M.m : ℝ) - 1) * q ∈ Icc (0 : ℝ) 1 := by
      intro q hq
      have htq := ht_bounds q hq
      exact ⟨by nlinarith [htq.1, hq.1], by nlinarith [htq.2, hq.2]⟩
    let Pext : ℝ → ℝ := fun z => P.P (max 0 (min 1 z))
    have hPext_cont : Continuous Pext :=
      P.hP_cont.comp_continuous (continuous_const.max (continuous_const.min continuous_id))
        (fun z => ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩)
    have hP_meas : AEMeasurable (fun q => P.P (t q + ((M.m : ℝ) - 1) * q)) (volume.restrict (Icc (0 : ℝ) q_ρ)) := by
      refine (hPext_cont.measurable.comp_aemeasurable harg_meas).congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc] with q hq
      have hm := harg_mem q hq
      simp only [Function.comp_apply, Pext, min_eq_right hm.2, max_eq_right hm.1]
    have hfun_meas : AEStronglyMeasurable (fun q => M.cournotRev P.P (t q) q * M.W q)
        (volume.restrict (Icc (0 : ℝ) q_ρ)) :=
      ((ht_meas.mul hP_meas).mul M.W_continuous.measurable.aemeasurable).aestronglyMeasurable
    have hq_le_one : q_ρ ≤ 1 := by
      have : (2 : ℝ) ≤ M.m := by exact_mod_cast M.hm
      nlinarith
    have hbdd : ∀ q ∈ Icc (0 : ℝ) q_ρ, ‖M.cournotRev P.P (t q) q * M.W q‖ ≤
        q_ρ * 1 * ((M.n : ℝ) * ((M.n : ℝ) - 1)) := by
      intro q hq
      have htq := ht_bounds q hq
      have hPmem := P.hP_mem _ (harg_mem q hq)
      have hPnn : 0 ≤ P.P (t q + ((M.m : ℝ) - 1) * q) := le_trans M.ha0 hPmem.1
      have hW_nn : 0 ≤ M.W q := M.W_nonneg (le_trans hq.2 hq_le_one)
      have hW_le : M.W q ≤ (M.n : ℝ) * ((M.n : ℝ) - 1) := by
        unfold Market.W
        have hpow : (1 - q) ^ (M.n - 2) ≤ 1 := pow_le_one₀ (by linarith [hq.2]) (by linarith [hq.1])
        have hn : (0 : ℝ) ≤ (M.n : ℝ) * ((M.n : ℝ) - 1) :=
          mul_nonneg M.n_pos_real.le M.n_sub_one_pos_real.le
        nlinarith
      unfold Market.cournotRev
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg htq.1 hPnn) hW_nn)]
      have h1 : t q * P.P (t q + ((M.m : ℝ) - 1) * q) ≤ q_ρ * 1 :=
        mul_le_mul htq.2 hPmem.2 hPnn hq_ρ0
      exact mul_le_mul h1 hW_le hW_nn (mul_nonneg hq_ρ0 zero_le_one)
    exact IntegrableOn.of_bound measure_Icc_lt_top hfun_meas _
      (ae_restrict_of_forall_mem measurableSet_Icc hbdd)
  have hid_int : IntervalIntegrable (fun q => M.cournotRev P.P q q * M.W q) volume 0 q_ρ := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hq_ρ0]
    have hcont : ContinuousOn (fun q => M.cournotRev P.P q q * M.W q) (Icc (0 : ℝ) q_ρ) := by
      unfold Market.cournotRev
      have haff : ContinuousOn (fun q : ℝ => q + ((M.m : ℝ) - 1) * q) (Icc (0 : ℝ) q_ρ) :=
        continuousOn_id.add (continuousOn_const.mul continuousOn_id)
      have hP : ContinuousOn (fun q => P.P (q + ((M.m : ℝ) - 1) * q)) (Icc (0 : ℝ) q_ρ) :=
        P.hP_cont.comp haff (fun q hq => ⟨by nlinarith [hq.1], by nlinarith [hq.2]⟩)
      exact (continuousOn_id.mul hP).mul M.W_continuous.continuousOn
    exact hcont.integrableOn_Icc
  refine ⟨theorem1_part_i_exact_diff M P ρ q_ρ hPit_int hid_int, ?_⟩
  -- Decompose the integral over `[0, q_ρ]` as the sum of integrals over the disjoint bands
  let Dfun : ℝ → ℝ := fun q => (M.cournotRev P.P (t q) q - M.cournotRev P.P q q) * M.W q
  have hD_int : IntegrableOn Dfun (Icc (0 : ℝ) q_ρ) := by
    have heq : Dfun = fun q => M.cournotRev P.P (t q) q * M.W q - M.cournotRev P.P q q * M.W q := by
      ext q; simp [Dfun]; ring
    rw [heq]
    exact ((intervalIntegrable_iff_integrableOn_Icc_of_le hq_ρ0).mp hPit_int).sub
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hq_ρ0).mp hid_int)
  have hmeas_biUnion : ∀ (L : List (ℝ × ℝ)), MeasurableSet (⋃ x ∈ L, Ioo x.1 x.2) := by
    intro L
    induction L with
    | nil => simp
    | cons b L ih =>
      have hunion : (⋃ x ∈ b :: L, Ioo x.1 x.2) = Ioo b.1 b.2 ∪ ⋃ x ∈ L, Ioo x.1 x.2 := by
        ext q; simp
      rw [hunion]
      exact measurableSet_Ioo.union ih
  -- Helper: `∫ q in (⋃ b ∈ L, Ioo b.1 b.2), Dfun q = (L.map (fun b => ∫ q in b.1..b.2, Dfun q)).sum`
  have hsum_eq : ∀ (L : List (ℝ × ℝ)),
      (∀ b ∈ L, 0 ≤ b.1 ∧ b.1 ≤ b.2 ∧ b.2 ≤ q_ρ) →
      L.Pairwise (fun b₁ b₂ => b₁.2 ≤ b₂.1 ∨ b₂.2 ≤ b₁.1) →
      ∫ q in (⋃ b ∈ L, Ioo b.1 b.2), Dfun q = (L.map (fun b => ∫ q in b.1..b.2, Dfun q)).sum := by
    intro L
    induction L with
    | nil =>
      intro _ _; simp
    | cons b L ih =>
      intro hLin hLdisj
      rw [List.pairwise_cons] at hLdisj
      have hb := hLin b List.mem_cons_self
      have hL' : ∀ b' ∈ L, 0 ≤ b'.1 ∧ b'.1 ≤ b'.2 ∧ b'.2 ≤ q_ρ :=
        fun b' hb' => hLin b' (List.mem_cons_of_mem b hb')
      have hunion : (⋃ x ∈ b :: L, Ioo x.1 x.2) = Ioo b.1 b.2 ∪ ⋃ x ∈ L, Ioo x.1 x.2 := by
        ext q; simp
      rw [hunion, List.map_cons, List.sum_cons]
      have hdisj : Disjoint (Ioo b.1 b.2) (⋃ x ∈ L, Ioo x.1 x.2) := by
        rw [Set.disjoint_iUnion₂_right]
        intro b' hb'
        rw [Set.disjoint_left]
        intro q hq1 hq2
        rcases hLdisj.1 b' hb' with hle1 | hle2
        · linarith [hq1.2, hq2.1]
        · linarith [hq2.2, hq1.1]
      have hmeas2 : MeasurableSet (⋃ x ∈ L, Ioo x.1 x.2) := hmeas_biUnion L
      have hint1 : IntegrableOn Dfun (Ioo b.1 b.2) :=
        hD_int.mono_set (Ioo_subset_Icc_self.trans (Icc_subset_Icc hb.1 hb.2.2))
      have hint2 : IntegrableOn Dfun (⋃ x ∈ L, Ioo x.1 x.2) := by
        refine hD_int.mono_set ?_
        intro q hq
        simp only [mem_iUnion, mem_Ioo] at hq
        obtain ⟨b', hb', hq1, hq2⟩ := hq
        have hb'in := hL' b' hb'
        exact ⟨le_trans hb'in.1 hq1.le, le_trans hq2.le hb'in.2.2⟩
      rw [setIntegral_union hdisj hmeas2 hint1 hint2, ih hL' hLdisj.2]
      congr 1
      rw [intervalIntegral.integral_of_le hb.2.1, integral_Ioc_eq_integral_Ioo]
  have hzero_off : ∫ q in (0 : ℝ)..q_ρ, Dfun q = ∫ q in (⋃ b ∈ bands, Ioo b.1 b.2), Dfun q := by
    rw [intervalIntegral.integral_of_le hq_ρ0, ← integral_Icc_eq_integral_Ioc]
    have hsub : (⋃ b ∈ bands, Ioo b.1 b.2) ⊆ Icc (0 : ℝ) q_ρ := by
      intro q hq
      simp only [mem_iUnion, mem_Ioo] at hq
      obtain ⟨b, hb, h1, h2⟩ := hq
      have hbin := hbands_in b hb
      exact ⟨le_trans hbin.1 h1.le, le_trans h2.le hbin.2.2⟩
    have hmeasU : MeasurableSet (⋃ b ∈ bands, Ioo b.1 b.2) := hmeas_biUnion bands
    rw [← integral_indicator measurableSet_Icc, ← integral_indicator hmeasU]
    congr 1; ext q
    by_cases hqU : q ∈ ⋃ b ∈ bands, Ioo b.1 b.2
    · rw [Set.indicator_of_mem (hsub hqU), Set.indicator_of_mem hqU]
    · rw [Set.indicator_of_notMem hqU]
      by_cases hqI : q ∈ Icc (0 : ℝ) q_ρ
      · rw [Set.indicator_of_mem hqI]
        have hnot : ∀ b ∈ bands, ¬(b.1 < q ∧ q < b.2) := by
          intro b hb hlt
          exact hqU (Set.mem_iUnion₂.mpr ⟨b, hb, hlt⟩)
        simp [Dfun, ht_off q hqI hnot]
      · rw [Set.indicator_of_notMem hqI]
  rw [hzero_off, hsum_eq bands hbands_in hbands_disj]
  have hpw_disj : ∀ b₁ ∈ bands, ∀ b₂ ∈ bands, b₁ ≠ b₂ → b₁.2 ≤ b₂.1 ∨ b₂.2 ≤ b₁.1 := by
    have haux : ∀ (L : List (ℝ × ℝ)),
        L.Pairwise (fun b₁ b₂ => b₁.2 ≤ b₂.1 ∨ b₂.2 ≤ b₁.1) →
        ∀ b₁ ∈ L, ∀ b₂ ∈ L, b₁ ≠ b₂ → b₁.2 ≤ b₂.1 ∨ b₂.2 ≤ b₁.1 := by
      intro L
      induction L with
      | nil => intro _ b₁ hb₁; simp at hb₁
      | cons a L ih =>
        intro hpw b₁ hb₁ b₂ hb₂ hne
        rw [List.pairwise_cons] at hpw
        rcases List.mem_cons.mp hb₁ with rfl | h1
        · rcases List.mem_cons.mp hb₂ with rfl | h2
          · exact absurd rfl hne
          · exact hpw.1 b₂ h2
        · rcases List.mem_cons.mp hb₂ with rfl | h2
          · exact (hpw.1 b₁ h1).symm
          · exact ih hpw.2 b₁ h1 b₂ h2 hne
    exact haux bands hbands_disj
  -- Each band integral is `≤ 0` by `theorem1_single_band`
  have hband_le : ∀ b ∈ bands, ∫ q in b.1..b.2, Dfun q ≤ 0 := by
    intro b hb
    have hbin := hbands_in b hb
    have hb_end := hend b hb
    have hn1_pos : (0 : ℝ) < (M.n : ℝ) - 1 := M.n_sub_one_pos_real
    have hE1_zero : ∫ u in (0 : ℝ)..b.1, (t u - u) * (1 - u) ^ (M.n - 2) = 0 := by
      have h := hb_end.1
      unfold excessSupply at h
      exact (mul_eq_zero.mp h).resolve_left hn1_pos.ne'
    have hE2_zero : ∫ u in (0 : ℝ)..b.2, (t u - u) * (1 - u) ^ (M.n - 2) = 0 := by
      have h := hb_end.2
      unfold excessSupply at h
      exact (mul_eq_zero.mp h).resolve_left hn1_pos.ne'
    have hφ0_int : IntervalIntegrable (fun u => (t u - u) * (1 - u) ^ (M.n - 2)) volume 0 q_ρ := by
      have h1 : IntervalIntegrable (fun u => t u - u) volume 0 q_ρ :=
        ht_int.sub (continuous_id.intervalIntegrable 0 q_ρ)
      exact h1.mul_continuousOn (Continuous.continuousOn (by fun_prop))
    have ht_b1 : t b.1 = b.1 := by
      apply ht_off b.1 ⟨hbin.1, le_trans hbin.2.1 hbin.2.2⟩
      intro b' hb' ⟨h1, h2⟩
      by_cases heq : b' = b
      · subst heq; linarith
      · rcases hpw_disj b hb b' hb' (Ne.symm heq) with hle1 | hle2
        · linarith [hbin.2.1]
        · linarith
    have ht_b2 : t b.2 = b.2 := by
      apply ht_off b.2 ⟨le_trans hbin.1 hbin.2.1, hbin.2.2⟩
      intro b' hb' ⟨h1, h2⟩
      by_cases heq : b' = b
      · subst heq; linarith
      · rcases hpw_disj b hb b' hb' (Ne.symm heq) with hle1 | hle2
        · linarith
        · linarith [hbin.2.1]
    have ht_range : ∀ q ∈ Icc b.1 b.2, t q ∈ Icc b.1 b.2 := by
      intro q hq
      have hq_in : q ∈ Icc (0 : ℝ) q_ρ := ⟨le_trans hbin.1 hq.1, le_trans hq.2 hbin.2.2⟩
      exact ⟨by rw [← ht_b1]; exact ht_mono ⟨hbin.1, le_trans hbin.2.1 hbin.2.2⟩ hq_in hq.1,
             by rw [← ht_b2]; exact ht_mono hq_in ⟨le_trans hbin.1 hbin.2.1, hbin.2.2⟩ hq.2⟩
    have hborder_b : ∀ q ∈ Icc b.1 b.2, ∫ u in b.1..q, (t u - u) * (1 - u) ^ (M.n - 2) ≤ 0 := by
      intro q hq
      have hsplit := intervalIntegral.integral_add_adjacent_intervals
        (hφ0_int.mono_set (uIcc_subset_uIcc left_mem_uIcc (mem_uIcc_of_le hbin.1 (le_trans hbin.2.1 hbin.2.2))))
        (hφ0_int.mono_set (uIcc_subset_uIcc (mem_uIcc_of_le hbin.1 (le_trans hbin.2.1 hbin.2.2))
          (mem_uIcc_of_le (le_trans hbin.1 hq.1) (le_trans hq.2 hbin.2.2))))
      have hq_le0 := hborder q ⟨le_trans hbin.1 hq.1, le_trans hq.2 hbin.2.2⟩
      linarith
    have hzeromean_b : ∫ u in b.1..b.2, (t u - u) * (1 - u) ^ (M.n - 2) = 0 := by
      have hsplit := intervalIntegral.integral_add_adjacent_intervals
        (hφ0_int.mono_set (uIcc_subset_uIcc left_mem_uIcc (mem_uIcc_of_le hbin.1 (le_trans hbin.2.1 hbin.2.2))))
        (hφ0_int.mono_set (uIcc_subset_uIcc (mem_uIcc_of_le hbin.1 (le_trans hbin.2.1 hbin.2.2))
          (mem_uIcc_of_le (le_trans hbin.1 hbin.2.1) hbin.2.2)))
      linarith
    exact theorem1_single_band M P hbin.1 hbin.2.1 (by nlinarith [hbin.2.2])
      ht_range
      (ht_int.mono_set (uIcc_subset_uIcc (mem_uIcc_of_le hbin.1 (le_trans hbin.2.1 hbin.2.2))
        (mem_uIcc_of_le (le_trans hbin.1 hbin.2.1) hbin.2.2)))
      (hPit_int.mono_set (uIcc_subset_uIcc (mem_uIcc_of_le hbin.1 (le_trans hbin.2.1 hbin.2.2))
        (mem_uIcc_of_le (le_trans hbin.1 hbin.2.1) hbin.2.2)))
      hborder_b hzeromean_b (hpsi b hb)
  have hlist_nonpos : ∀ (L : List (ℝ × ℝ)), (∀ b ∈ L, ∫ q in b.1..b.2, Dfun q ≤ 0) →
      (L.map (fun b => ∫ q in b.1..b.2, Dfun q)).sum ≤ 0 := by
    intro L
    induction L with
    | nil => intro _; simp
    | cons b L ih =>
      intro h
      rw [List.map_cons, List.sum_cons]
      have h1 := h b List.mem_cons_self
      have h2 := ih (fun b' hb' => h b' (List.mem_cons_of_mem b hb'))
      linarith
  exact hlist_nonpos bands hband_le

/-- Global-monotonicity specialization of Theorem 1: if `ψ_m` is nondecreasing on
`[P(m q_ρ), 1]`, any Border-feasible monotone path on `[0, q_ρ]` with `t(0) = 0`, `t(q_ρ) = q_ρ`,
and `E(q_ρ) = 0` earns `D ≤ 0` for every `n ≥ 2`. -/
theorem theorem1_interior_pools_cournot_global (M : Market) (P : M.InverseDemand)
    (q_ρ : ℝ) (hq_ρ0 : 0 ≤ q_ρ) (hq_ρ_le : (M.m : ℝ) * q_ρ ≤ 1)
    {t : ℝ → ℝ}
    (ht_range : ∀ q ∈ Icc (0 : ℝ) q_ρ, t q ∈ Icc (0 : ℝ) q_ρ)
    (ht_int : IntervalIntegrable t volume 0 q_ρ)
    (hPit_int : IntervalIntegrable (fun q => M.cournotRev P.P (t q) q * M.W q) volume 0 q_ρ)
    (hborder : BorderFeasible M q_ρ t)
    (hzeromean : ∫ u in (0 : ℝ)..q_ρ, (t u - u) * (1 - u) ^ (M.n - 2) = 0)
    (hpsi : MonotoneOn M.psi (Icc (P.P ((M.m : ℝ) * q_ρ)) 1)) :
    ∫ q in (0 : ℝ)..q_ρ, (M.cournotRev P.P (t q) q - M.cournotRev P.P q q) * M.W q ≤ 0 := by
  have hpsi' : MonotoneOn M.psi (Icc (P.P ((M.m : ℝ) * q_ρ)) (P.P ((M.m : ℝ) * 0))) := by
    simpa [mul_zero, P.hP_zero] using hpsi
  exact theorem1_single_band M P le_rfl hq_ρ0 hq_ρ_le ht_range ht_int hPit_int hborder hzeromean hpsi'

/-! ### Section 6: Corollary 1 — A Smaller Seller Does Not Pool -/

/-- Exact weighted excess supply of the reserve-increase path `t^S(q) = min q t0` at `q0`:
`E^S(q0) = -η(n, q0, t0)` for `0 ≤ t0 ≤ q0`. -/
lemma excessSupply_reserveIncreasePath (M : Market) {q0 t0 : ℝ}
    (ht0 : 0 ≤ t0) (ht0_le : t0 ≤ q0) :
    excessSupply M (reserveIncreasePath t0) q0 = -convexityGap M.n q0 t0 := by
  unfold excessSupply reserveIncreasePath convexityGap
  have hcont : Continuous (fun u : ℝ => (min u t0 - u) * (1 - u) ^ (M.n - 2)) := by fun_prop
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := volume) 0 t0) (hcont.intervalIntegrable (μ := volume) t0 q0)
  rw [← hsplit]
  have hpart1 : ∫ u in (0 : ℝ)..t0, (min u t0 - u) * (1 - u) ^ (M.n - 2) = 0 := by
    rw [intervalIntegral.integral_of_le ht0]
    have hzero : EqOn (fun u : ℝ => (min u t0 - u) * (1 - u) ^ (M.n - 2)) 0 (Ioc 0 t0) := by
      intro u hu; simp [min_eq_left hu.2]
    rw [setIntegral_congr_fun measurableSet_Ioc hzero]; simp
  have hpart2 : ∫ u in t0..q0, (min u t0 - u) * (1 - u) ^ (M.n - 2) =
      t0 * (∫ u in t0..q0, (1 - u) ^ (M.n - 2)) - ∫ u in t0..q0, u * (1 - u) ^ (M.n - 2) := by
    have heq : EqOn (fun u : ℝ => (min u t0 - u) * (1 - u) ^ (M.n - 2))
        (fun u : ℝ => t0 * (1 - u) ^ (M.n - 2) - u * (1 - u) ^ (M.n - 2)) (Ioc t0 q0) := by
      intro u hu; simp [min_eq_right hu.1.le, sub_mul]
    rw [intervalIntegral.integral_of_le ht0_le, setIntegral_congr_fun measurableSet_Ioc heq,
      ← intervalIntegral.integral_of_le ht0_le,
      intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) t0 q0)
        (Continuous.intervalIntegrable (by fun_prop) t0 q0),
      intervalIntegral.integral_const_mul]
  rw [hpart1, zero_add, hpart2, mul_sub]
  -- Evaluate `(n - 1) * ∫ t0..q0, (1 - u)^(n - 2) = (1 - t0)^(n - 1) - (1 - q0)^(n - 1)`
  have hpow : ((M.n : ℝ) - 1) * ∫ u in t0..q0, (1 - u) ^ (M.n - 2) =
      (1 - t0) ^ (M.n - 1) - (1 - q0) ^ (M.n - 1) := by
    let F : ℝ → ℝ := fun u => -(1 - u) ^ (M.n - 1)
    have hF_deriv : ∀ u, HasDerivAt F (((M.n : ℝ) - 1) * (1 - u) ^ (M.n - 2)) u := by
      intro u
      have h1 : HasDerivAt (fun y : ℝ => 1 - y) (-1) u := by
        simpa using (hasDerivAt_const u (1 : ℝ)).fun_sub (hasDerivAt_id u)
      have h2 : HasDerivAt (fun y : ℝ => (1 - y) ^ (M.n - 1))
          (((M.n - 1 : ℕ) : ℝ) * (1 - u) ^ ((M.n - 1) - 1) * (-1)) u := h1.pow (M.n - 1)
      have h3 := h2.neg
      convert h3 using 1
      have hn1 : ((M.n - 1 : ℕ) : ℝ) = (M.n : ℝ) - 1 := by
        rw [Nat.cast_sub (by have := M.hn; omega), Nat.cast_one]
      have hn2 : (M.n - 1) - 1 = M.n - 2 := by have := M.hn; omega
      rw [hn1, hn2]; ring
    rw [← intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hF_deriv u)
      (Continuous.intervalIntegrable (by fun_prop) t0 q0)]
    simp [F]; ring
  -- Evaluate `(n - 1) * ∫ t0..q0, u * (1 - u)^(n - 2)` via `integral_u_mul_one_sub_pow`
  have hu_split : ∫ u in t0..q0, u * (1 - u) ^ (M.n - 2) =
      (∫ u in (0 : ℝ)..q0, u * (1 - u) ^ (M.n - 2)) - ∫ u in (0 : ℝ)..t0, u * (1 - u) ^ (M.n - 2) := by
    have h := intervalIntegral.integral_add_adjacent_intervals
      (Continuous.intervalIntegrable (by fun_prop) 0 t0 :
        IntervalIntegrable (fun u : ℝ => u * (1 - u) ^ (M.n - 2)) volume 0 t0)
      (Continuous.intervalIntegrable (by fun_prop) t0 q0)
    linarith
  have hu_q0 := integral_u_mul_one_sub_pow M.hn q0
  have hu_t0 := integral_u_mul_one_sub_pow M.hn t0
  have h1 : ((M.n : ℝ) - 1) * (t0 * ∫ u in t0..q0, (1 - u) ^ (M.n - 2)) =
      t0 * ((1 - t0) ^ (M.n - 1) - (1 - q0) ^ (M.n - 1)) := by
    rw [← mul_assoc, mul_comm ((M.n : ℝ) - 1) t0, mul_assoc, hpow]
  have h2 : ((M.n : ℝ) - 1) * ∫ u in t0..q0, u * (1 - u) ^ (M.n - 2) =
      (h_n M.n q0 - q0 * (1 - q0) ^ (M.n - 1)) - (h_n M.n t0 - t0 * (1 - t0) ^ (M.n - 1)) := by
    rw [hu_split, mul_sub, hu_q0, hu_t0]
  linarith

/-- **Corollary 1 (A Smaller Seller Does Not Pool — Core Path Inequality)**:
Suppose `0 ≤ t0 ≤ q0` with `t0 + (m - 1) q0 ≤ 1`, and `ψ_m` is nondecreasing on
`[P(t0 + (m - 1) q0), 1]`. Then for any Border-feasible quantity path `t` on `[0, q0]` with
`0 ≤ t(q) ≤ t0`, `excessSupply M t q0 = -convexityGap M.n q0 t0` (as holds when `ℓ = 0`),
and `ℓ = 0`:
`pathRev M P.P ρ q0 t0 0 t ≤ pathRev M P.P ρ q0 t0 0 (reserveIncreasePath t0)`. -/
theorem corollary1_smaller_seller (M : Market) (P : M.InverseDemand)
    (ρ q0 t0 : ℝ)
    (ht0 : 0 ≤ t0) (ht0_le : t0 ≤ q0) (hz_le : t0 + ((M.m : ℝ) - 1) * q0 ≤ 1)
    {t : ℝ → ℝ}
    (ht_range : ∀ q ∈ Icc (0 : ℝ) q0, t q ∈ Icc (0 : ℝ) t0)
    (ht_int : IntervalIntegrable t volume 0 q0)
    (hPit_int : IntervalIntegrable (fun q => M.cournotRev P.P (t q) q * M.W q) volume 0 q0)
    (hborder : BorderFeasible M q0 t)
    (hexcess : excessSupply M t q0 = -convexityGap M.n q0 t0)
    (hpsi : MonotoneOn M.psi (Icc (P.P (t0 + ((M.m : ℝ) - 1) * q0)) 1)) :
    pathRev M P.P ρ q0 t0 0 t ≤ pathRev M P.P ρ q0 t0 0 (reserveIncreasePath t0) := by
  have hq0_nn : 0 ≤ q0 := le_trans ht0 ht0_le
  have hm1_pos : (0 : ℝ) < (M.m : ℝ) - 1 := M.m_sub_one_pos_real
  have hq0_le_one : q0 ≤ 1 := by
    have : (1 : ℝ) ≤ (M.m : ℝ) - 1 := by
      have : (2 : ℝ) ≤ M.m := by exact_mod_cast M.hm
      linarith
    nlinarith
  let tS := reserveIncreasePath t0
  let ϱ : ℝ → ℝ := fun q => M.psi (P.P (tS q + ((M.m : ℝ) - 1) * q))
  let φ : ℝ → ℝ := fun q => (t q - tS q) * M.W q
  have htS_cont : Continuous tS := continuous_id.min continuous_const
  have htS_mem : ∀ q ∈ Icc (0 : ℝ) q0,
      tS q + ((M.m : ℝ) - 1) * q ∈ Icc (0 : ℝ) (t0 + ((M.m : ℝ) - 1) * q0) := by
    intro q hq
    exact ⟨by have : 0 ≤ min q t0 := le_min hq.1 ht0; simp only [tS, reserveIncreasePath]; nlinarith [hq.1],
           by have : min q t0 ≤ t0 := min_le_right q t0; simp only [tS, reserveIncreasePath]; nlinarith [hq.2]⟩
  have hϱ_cont : ContinuousOn ϱ (Icc (0 : ℝ) q0) := by
    have harg : ContinuousOn (fun q => tS q + ((M.m : ℝ) - 1) * q) (Icc (0 : ℝ) q0) :=
      htS_cont.continuousOn.add (continuousOn_const.mul continuousOn_id)
    have hP : ContinuousOn (fun q => P.P (tS q + ((M.m : ℝ) - 1) * q)) (Icc (0 : ℝ) q0) :=
      P.hP_cont.comp harg (fun q hq => ⟨(htS_mem q hq).1, le_trans (htS_mem q hq).2 hz_le⟩)
    exact M.psi_continuousOn.comp hP (fun q hq =>
      P.hP_mem _ ⟨(htS_mem q hq).1, le_trans (htS_mem q hq).2 hz_le⟩)
  have hPitS_cont : ContinuousOn (fun q => M.cournotRev P.P (tS q) q * M.W q) (Icc (0 : ℝ) q0) := by
    unfold Market.cournotRev
    have harg : ContinuousOn (fun q => tS q + ((M.m : ℝ) - 1) * q) (Icc (0 : ℝ) q0) :=
      htS_cont.continuousOn.add (continuousOn_const.mul continuousOn_id)
    have hP : ContinuousOn (fun q => P.P (tS q + ((M.m : ℝ) - 1) * q)) (Icc (0 : ℝ) q0) :=
      P.hP_cont.comp harg (fun q hq => ⟨(htS_mem q hq).1, le_trans (htS_mem q hq).2 hz_le⟩)
    exact (htS_cont.continuousOn.mul hP).mul M.W_continuous.continuousOn
  have hPitS_int : IntervalIntegrable (fun q => M.cournotRev P.P (tS q) q * M.W q) volume 0 q0 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hq0_nn).mpr hPitS_cont.integrableOn_Icc
  have hφ_int : IntervalIntegrable φ volume 0 q0 :=
    (ht_int.sub (htS_cont.intervalIntegrable 0 q0)).mul_continuousOn
      (by rw [uIcc_of_le hq0_nn]; exact M.W_continuous.continuousOn)
  have hϱφ_int : IntervalIntegrable (fun q => ϱ q * φ q) volume 0 q0 :=
    hφ_int.continuousOn_mul (by rw [uIcc_of_le hq0_nn]; exact hϱ_cont)
  have hdiff_int : IntervalIntegrable
      (fun q => (M.cournotRev P.P (t q) q - M.cournotRev P.P (tS q) q) * M.W q) volume 0 q0 := by
    have heq : (fun q => (M.cournotRev P.P (t q) q - M.cournotRev P.P (tS q) q) * M.W q) =
        fun q => M.cournotRev P.P (t q) q * M.W q - M.cournotRev P.P (tS q) q * M.W q := by
      ext q; ring
    rw [heq]; exact hPit_int.sub hPitS_int
  have hpsi' : MonotoneOn M.psi (Icc (P.P (t0 + ((M.m : ℝ) - 1) * q0)) (P.P 0)) := by
    rwa [P.hP_zero]
  have hpt : ∀ q ∈ Icc (0 : ℝ) q0,
      (M.cournotRev P.P (t q) q - M.cournotRev P.P (tS q) q) * M.W q ≤ ϱ q * φ q := by
    intro q hq
    have htq := ht_range q hq
    have htb := tangent_bound_general M P le_rfl hz_le htq.2
      ⟨by nlinarith [htq.1, hq.1], by nlinarith [htq.2, hq.2]⟩
      (htS_mem q hq) hpsi'
    have hW_nn : 0 ≤ M.W q := M.W_nonneg (le_trans hq.2 hq0_le_one)
    calc (M.cournotRev P.P (t q) q - M.cournotRev P.P (tS q) q) * M.W q
        ≤ (ϱ q * (t q - tS q)) * M.W q := mul_le_mul_of_nonneg_right htb hW_nn
      _ = ϱ q * φ q := by simp only [φ]; ring
  have hϱ_anti : AntitoneOn ϱ (Icc (0 : ℝ) q0) :=
    antitoneOn_psi_reserveIncrease M P ht0 ht0_le hz_le hpsi
  -- Show `N(q) = ∫ u in 0..q, φ u ≤ 0` on `[0, q0]` and `N(q0) = 0`
  have hN_nonpos : ∀ q ∈ Icc (0 : ℝ) q0, ∫ u in (0 : ℝ)..q, φ u ≤ 0 := by
    intro q hq
    have hrew : ∀ u, φ u = ((M.n : ℝ) * ((M.n : ℝ) - 1)) * ((t u - tS u) * (1 - u) ^ (M.n - 2)) := by
      intro u; simp only [φ, Market.W]; ring
    simp_rw [hrew, intervalIntegral.integral_const_mul]
    refine mul_nonpos_of_nonneg_of_nonpos (mul_nonneg M.n_pos_real.le M.n_sub_one_pos_real.le) ?_
    rcases le_or_gt q t0 with hqt0 | ht0q
    · have heq : EqOn (fun u => (t u - tS u) * (1 - u) ^ (M.n - 2))
          (fun u => (t u - u) * (1 - u) ^ (M.n - 2)) (Ioc 0 q) := by
        intro u hu; simp [tS, reserveIncreasePath, min_eq_left (le_trans hu.2 hqt0)]
      rw [intervalIntegral.integral_of_le hq.1, setIntegral_congr_fun measurableSet_Ioc heq,
        ← intervalIntegral.integral_of_le hq.1]
      exact hborder q hq
    · have hψ_int : IntervalIntegrable (fun u => (t u - tS u) * (1 - u) ^ (M.n - 2)) volume 0 q0 :=
        (ht_int.sub (htS_cont.intervalIntegrable 0 q0)).mul_continuousOn
          (Continuous.continuousOn (by fun_prop))
      have hsplit := intervalIntegral.integral_add_adjacent_intervals
        (hψ_int.mono_set (uIcc_subset_uIcc left_mem_uIcc (mem_uIcc_of_le ht0 ht0_le)))
        (hψ_int.mono_set (uIcc_subset_uIcc (mem_uIcc_of_le ht0 ht0_le) (mem_uIcc_of_le hq.1 hq.2)))
      rw [← hsplit]
      have h1 : ∫ u in (0 : ℝ)..t0, (t u - tS u) * (1 - u) ^ (M.n - 2) ≤ 0 := by
        have heq : EqOn (fun u => (t u - tS u) * (1 - u) ^ (M.n - 2))
            (fun u => (t u - u) * (1 - u) ^ (M.n - 2)) (Ioc 0 t0) := by
          intro u hu; simp [tS, reserveIncreasePath, min_eq_left hu.2]
        rw [intervalIntegral.integral_of_le ht0, setIntegral_congr_fun measurableSet_Ioc heq,
          ← intervalIntegral.integral_of_le ht0]
        exact hborder t0 ⟨ht0, ht0_le⟩
      have h2 : ∫ u in t0..q, (t u - tS u) * (1 - u) ^ (M.n - 2) ≤ 0 := by
        calc ∫ u in t0..q, (t u - tS u) * (1 - u) ^ (M.n - 2)
            ≤ ∫ _ in t0..q, (0 : ℝ) := by
              refine intervalIntegral.integral_mono_on ht0q.le
                (hψ_int.mono_set (uIcc_subset_uIcc (mem_uIcc_of_le ht0 ht0_le) (mem_uIcc_of_le hq.1 hq.2)))
                intervalIntegrable_const (fun u hu => ?_)
              have hu0 : u ∈ Icc (0 : ℝ) q0 := ⟨le_trans ht0 hu.1, le_trans hu.2 hq.2⟩
              have htSu : tS u = t0 := min_eq_right hu.1
              rw [htSu]
              exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (ht_range u hu0).2)
                (pow_nonneg (by linarith [hu0.2]) _)
          _ = 0 := by simp
      linarith
  have hN_zero : ∫ u in (0 : ℝ)..q0, φ u = 0 := by
    have hrew : ∀ u, φ u = (M.n : ℝ) * (((M.n : ℝ) - 1) * ((t u - u) * (1 - u) ^ (M.n - 2)) -
        ((M.n : ℝ) - 1) * ((tS u - u) * (1 - u) ^ (M.n - 2))) := by
      intro u; simp only [φ, Market.W]; ring
    have hint1 : IntervalIntegrable (fun u => (t u - u) * (1 - u) ^ (M.n - 2)) volume 0 q0 :=
      (ht_int.sub (continuous_id.intervalIntegrable 0 q0)).mul_continuousOn
        (Continuous.continuousOn (by fun_prop))
    have hint2 : IntervalIntegrable (fun u => (tS u - u) * (1 - u) ^ (M.n - 2)) volume 0 q0 :=
      Continuous.intervalIntegrable (by fun_prop) 0 q0
    simp_rw [hrew, intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_sub (hint1.const_mul _) (hint2.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have hE1 : ((M.n : ℝ) - 1) * ∫ u in (0 : ℝ)..q0, (t u - u) * (1 - u) ^ (M.n - 2) =
        -convexityGap M.n q0 t0 := hexcess
    have hE2 : ((M.n : ℝ) - 1) * ∫ u in (0 : ℝ)..q0, (tS u - u) * (1 - u) ^ (M.n - 2) =
        -convexityGap M.n q0 t0 := excessSupply_reserveIncreasePath M ht0 ht0_le
    rw [hE1, hE2, sub_self, mul_zero]
  have hdiff_le : ∫ q in (0 : ℝ)..q0,
      (M.cournotRev P.P (t q) q - M.cournotRev P.P (tS q) q) * M.W q ≤ 0 := by
    calc ∫ q in (0 : ℝ)..q0, (M.cournotRev P.P (t q) q - M.cournotRev P.P (tS q) q) * M.W q
        ≤ ∫ q in (0 : ℝ)..q0, ϱ q * φ q :=
          intervalIntegral.integral_mono_on hq0_nn hdiff_int hϱφ_int hpt
      _ ≤ ϱ q0 * ∫ u in (0 : ℝ)..q0, φ u :=
          integral_antitone_mul_le hq0_nn hϱ_anti hφ_int hϱφ_int hN_nonpos
      _ = 0 := by rw [hN_zero, mul_zero]
  have hrev_sub : pathRev M P.P ρ q0 t0 0 t - pathRev M P.P ρ q0 t0 0 tS =
      ∫ q in (0 : ℝ)..q0, (M.cournotRev P.P (t q) q - M.cournotRev P.P (tS q) q) * M.W q := by
    unfold pathRev
    simp only [sub_zero]
    rw [show (M.n : ℝ) * ρ * t0 * (1 - q0) ^ (M.n - 1) +
          (∫ q in (0 : ℝ)..q0, M.cournotRev P.P (t q) q * M.W q) -
        ((M.n : ℝ) * ρ * t0 * (1 - q0) ^ (M.n - 1) +
          (∫ q in (0 : ℝ)..q0, M.cournotRev P.P (tS q) q * M.W q)) =
        (∫ q in (0 : ℝ)..q0, M.cournotRev P.P (t q) q * M.W q) -
          (∫ q in (0 : ℝ)..q0, M.cournotRev P.P (tS q) q * M.W q) by ring]
    rw [← intervalIntegral.integral_sub hPit_int hPitS_int]
    congr 1; ext q; ring
  linarith

/-- Corollary 1 stated directly with `ψ_m` nondecreasing on `[max ρ a, 1]` when
`t0 + (m - 1) q0 ≤ 1 - F(max ρ a)`. -/
theorem corollary1_smaller_seller_of_rho (M : Market) (P : M.InverseDemand)
    (ρ q0 t0 : ℝ) (hρ1 : ρ < 1)
    (ht0 : 0 ≤ t0) (ht0_le : t0 ≤ q0)
    (hz_le_rho : t0 + ((M.m : ℝ) - 1) * q0 ≤ 1 - M.F (max ρ M.a))
    {t : ℝ → ℝ}
    (ht_range : ∀ q ∈ Icc (0 : ℝ) q0, t q ∈ Icc (0 : ℝ) t0)
    (ht_int : IntervalIntegrable t volume 0 q0)
    (hPit_int : IntervalIntegrable (fun q => M.cournotRev P.P (t q) q * M.W q) volume 0 q0)
    (hborder : BorderFeasible M q0 t)
    (hexcess : excessSupply M t q0 = -convexityGap M.n q0 t0)
    (hpsi : MonotoneOn M.psi (Icc (max ρ M.a) 1)) :
    pathRev M P.P ρ q0 t0 0 t ≤ pathRev M P.P ρ q0 t0 0 (reserveIncreasePath t0) := by
  have hmax_mem : max ρ M.a ∈ Icc M.a 1 := ⟨le_max_right _ _, max_le hρ1.le M.ha1.le⟩
  have hF_mem := M.F_mem_Icc hmax_mem
  have hz_le_one : t0 + ((M.m : ℝ) - 1) * q0 ≤ 1 := by linarith [hF_mem.1]
  have hz_nn : 0 ≤ t0 + ((M.m : ℝ) - 1) * q0 := by
    have := M.m_sub_one_pos_real; nlinarith [ht0, ht0_le]
  have hP_ge : max ρ M.a ≤ P.P (t0 + ((M.m : ℝ) - 1) * q0) := by
    rw [← P.hP_left (max ρ M.a) hmax_mem]
    exact P.hP_strictAnti.antitoneOn ⟨hz_nn, hz_le_one⟩ ⟨by linarith [hF_mem.2], by linarith [hF_mem.1]⟩
      hz_le_rho
  exact corollary1_smaller_seller M P ρ q0 t0 ht0 ht0_le hz_le_one ht_range ht_int hPit_int
    hborder hexcess (hpsi.mono (Icc_subset_Icc_left hP_ge))

end AuctionCompetition
