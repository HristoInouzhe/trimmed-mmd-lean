import StatFormal.Archive.Wave24c.Statements
import StatFormal.Archive.Wave23a.RouteProbContent
import StatFormal.Archive.OTFD.Wave22b.RouteExp

/-!
# Route — scenario paths of the entropic map (C `prop:cond-paths`, T `prop:paths-M`) (untrusted)

With `q(u) = softmax(s(u)/ε)`, `s_j(u) = a_j + κ⟨z_j, u⟩`, and `d = u − u'`:
`κ ⟨Q̂(u) − Q̂(u'), d⟩ = ε Σ_j (q_j(u) − q_j(u')) (log q_j(u) − log q_j(u'))`, because `κ⟨z_j, d⟩/ε` and
`log q_j(u) − log q_j(u')` differ by a constant (the log-normalisers) and `Σ_j (q_j(u) − q_j(u')) = 0`. Every term is
`≥ 0`; if the sum vanishes, `q(u) = q(u')`, so `⟨z_j, d⟩` is constant in `j`, `d ⊥ vectorSpan{z_j}`, and an affinely
spanning family forces `d = 0`. Rays `u = t v` give the monotone (strict) paths.
-/

noncomputable section
open MeasureTheory Set Filter Topology Finset
open scoped InnerProductSpace RealInnerProductSpace ENNReal

namespace StatFormal.Wave24c

open StatFormal.OTFD.Bands (softmax)

section General
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma softmax_pos' {n : ℕ} (x : Fin n → ℝ) (j : Fin n) : 0 < softmax x j := by
  unfold softmax
  have : (0 : ℝ) < ∑ k, Real.exp (x k) :=
    Finset.sum_pos (fun k _ => Real.exp_pos _) ⟨j, Finset.mem_univ _⟩
  positivity

lemma sum_softmax' {n : ℕ} (x : Fin n → ℝ) (hn : 0 < n) : ∑ j, softmax x j = 1 := by
  unfold softmax
  have : (0 : ℝ) < ∑ k, Real.exp (x k) :=
    Finset.sum_pos (fun k _ => Real.exp_pos _) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  rw [← Finset.sum_div, div_self this.ne']

lemma log_softmax' {n : ℕ} (x : Fin n → ℝ) (j : Fin n) :
    Real.log (softmax x j) = x j - Real.log (∑ k, Real.exp (x k)) := by
  unfold softmax
  have : (0 : ℝ) < ∑ k, Real.exp (x k) :=
    Finset.sum_pos (fun k _ => Real.exp_pos _) ⟨j, Finset.mem_univ _⟩
  rw [Real.log_div (Real.exp_pos _).ne' this.ne', Real.log_exp]

lemma mul_log_sub_nonneg {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : 0 ≤ (x - y) * (Real.log x - Real.log y) := by
  rcases le_total y x with h | h
  · exact mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 (Real.log_le_log hy h))
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 h) (sub_nonpos.2 (Real.log_le_log hx h))

lemma eq_of_mul_log_sub_eq_zero {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h : (x - y) * (Real.log x - Real.log y) = 0) : x = y := by
  rcases mul_eq_zero.1 h with h | h
  · linarith
  · exact Real.log_injOn_pos hx hy (by linarith)

/-- The key identity: `κ⟨Q̂(u) − Q̂(u'), u − u'⟩ = ε Σ_j (q_j − q'_j)(log q_j − log q'_j)`. -/
lemma lseMap_inner_eq {n : ℕ} (ε κ : ℝ) (hε : 0 < ε) (a : Fin n → ℝ) (z : Fin n → E) (u u' : E) :
    κ * ⟪lseMap ε κ a z u - lseMap ε κ a z u', u - u'⟫ =
      ε * ∑ j, (softmax (fun i => (a i + κ * ⟪z i, u⟫) / ε) j - softmax (fun i => (a i + κ * ⟪z i, u'⟫) / ε) j) *
        (Real.log (softmax (fun i => (a i + κ * ⟪z i, u⟫) / ε) j) -
          Real.log (softmax (fun i => (a i + κ * ⟪z i, u'⟫) / ε) j)) := by
  set x : Fin n → ℝ := fun i => (a i + κ * ⟪z i, u⟫) / ε with hx
  set x' : Fin n → ℝ := fun i => (a i + κ * ⟪z i, u'⟫) / ε with hx'
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [lseMap]
  have hlhs : ⟪lseMap ε κ a z u - lseMap ε κ a z u', u - u'⟫ =
      ∑ j, (softmax x j - softmax x' j) * ⟪z j, u - u'⟫ := by
    simp only [lseMap, ← hx, ← hx', ← Finset.sum_sub_distrib, sum_inner, ← sub_smul, real_inner_smul_left]
  set L := Real.log (∑ k, Real.exp (x k))
  set L' := Real.log (∑ k, Real.exp (x' k))
  have hterm : ∀ j, κ * ⟪z j, u - u'⟫ = ε * ((Real.log (softmax x j) - Real.log (softmax x' j)) + (L - L')) := by
    intro j
    rw [log_softmax', log_softmax', inner_sub_right]
    simp only [hx, hx']
    field_simp
    ring
  have hsum0 : ∑ j, (softmax x j - softmax x' j) = 0 := by
    rw [Finset.sum_sub_distrib, sum_softmax' x hn, sum_softmax' x' hn, sub_self]
  rw [hlhs, Finset.mul_sum]
  have : ∀ j, κ * ((softmax x j - softmax x' j) * ⟪z j, u - u'⟫) =
      ε * ((softmax x j - softmax x' j) * (Real.log (softmax x j) - Real.log (softmax x' j))) +
        ε * (L - L') * (softmax x j - softmax x' j) := by
    intro j
    have := hterm j
    calc κ * ((softmax x j - softmax x' j) * ⟪z j, u - u'⟫)
        = (softmax x j - softmax x' j) * (κ * ⟪z j, u - u'⟫) := by ring
      _ = _ := by rw [this]; ring
  rw [Finset.sum_congr rfl (fun j _ => this j), Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    hsum0, mul_zero, add_zero]

/-- Monotonicity of the entropic map: `⟨Q̂(u) − Q̂(u'), u − u'⟩ ≥ 0`. -/
lemma lseMap_inner_nonneg {n : ℕ} {ε κ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) (a : Fin n → ℝ) (z : Fin n → E)
    (u u' : E) : 0 ≤ ⟪lseMap ε κ a z u - lseMap ε κ a z u', u - u'⟫ := by
  have h := lseMap_inner_eq ε κ hε a z u u'
  have hr : 0 ≤ κ * ⟪lseMap ε κ a z u - lseMap ε κ a z u', u - u'⟫ := by
    rw [h]
    exact mul_nonneg hε.le (Finset.sum_nonneg fun j _ =>
      mul_log_sub_nonneg (softmax_pos' _ j) (softmax_pos' _ j))
  exact (mul_nonneg_iff_of_pos_left hκ).1 hr

/-- Strict monotonicity of the entropic map when the `z_j` affinely span: `u ≠ u'` gives `⟨Q̂(u) − Q̂(u'), u − u'⟩ > 0`. -/
lemma lseMap_inner_pos {n : ℕ} {ε κ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) (a : Fin n → ℝ) (z : Fin n → E)
    (hspan : affineSpan ℝ (Set.range z) = ⊤) {u u' : E} (huu : u ≠ u') :
    0 < ⟪lseMap ε κ a z u - lseMap ε κ a z u', u - u'⟫ := by
  rcases (lseMap_inner_nonneg hε hκ a z u u').lt_or_eq with h | h
  · exact h
  exfalso
  set x : Fin n → ℝ := fun i => (a i + κ * ⟪z i, u⟫) / ε with hx
  set x' : Fin n → ℝ := fun i => (a i + κ * ⟪z i, u'⟫) / ε with hx'
  have hid := lseMap_inner_eq ε κ hε a z u u'
  rw [← h, mul_zero] at hid
  have hsum : ∑ j, (softmax x j - softmax x' j) * (Real.log (softmax x j) - Real.log (softmax x' j)) = 0 := by
    have := hid.symm
    rcases mul_eq_zero.1 this with h1 | h1
    · exact absurd h1 hε.ne'
    · exact h1
  have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
    mul_log_sub_nonneg (softmax_pos' x j) (softmax_pos' x' j))).1 hsum
  have heq : ∀ j, softmax x j = softmax x' j := fun j =>
    eq_of_mul_log_sub_eq_zero (softmax_pos' x j) (softmax_pos' x' j) (hall j (Finset.mem_univ _))
  set L := Real.log (∑ k, Real.exp (x k))
  set L' := Real.log (∑ k, Real.exp (x' k))
  -- `κ⟨z_j, d⟩ = ε (L − L')` for every `j`
  have hconst : ∀ j, κ * ⟪z j, u - u'⟫ = ε * (L - L') := by
    intro j
    have h1 := log_softmax' x j
    have h2 := log_softmax' x' j
    rw [heq j] at h1
    have hxx : x j - x' j = L - L' := by linarith
    simp only [hx, hx'] at hxx
    rw [inner_sub_right]
    field_simp at hxx
    linarith
  -- `d` is orthogonal to the vector span
  set d := u - u'
  have hvs : vectorSpan ℝ (Set.range z) = ⊤ := by
    rw [← direction_affineSpan, hspan, AffineSubspace.direction_top]
  have hle : vectorSpan ℝ (Set.range z) ≤ (ℝ ∙ d)ᗮ := by
    rw [vectorSpan_def, Submodule.span_le]
    rintro w ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right, vsub_eq_sub, inner_sub_right]
    have hi := hconst i
    have hj := hconst j
    rw [real_inner_comm (z i) d, real_inner_comm (z j) d]
    have : κ * (⟪z i, d⟫ - ⟪z j, d⟫) = 0 := by linarith
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 hκ.ne'
    · linarith
  have hd : d ∈ (ℝ ∙ d)ᗮ := hle (by rw [hvs]; exact Submodule.mem_top)
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_self_eq_zero] at hd
  exact huu (sub_eq_zero.1 hd)

/-- Along a ray: `t ≤ t'` gives `⟨v, Q̂(t v)⟩ ≤ ⟨v, Q̂(t' v)⟩`. -/
lemma lseMap_ray_mono {n : ℕ} {ε κ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) (a : Fin n → ℝ) (z : Fin n → E) (v : E)
    {t t' : ℝ} (htt : t ≤ t') : ⟪v, lseMap ε κ a z (t • v)⟫ ≤ ⟪v, lseMap ε κ a z (t' • v)⟫ := by
  rcases htt.lt_or_eq with hlt | heq
  · have h := lseMap_inner_nonneg hε hκ a z (t' • v) (t • v)
    rw [← sub_smul, real_inner_smul_right, real_inner_comm] at h
    have h2 : 0 ≤ ⟪v, lseMap ε κ a z (t' • v) - lseMap ε κ a z (t • v)⟫ :=
      (mul_nonneg_iff_of_pos_left (sub_pos.2 hlt)).1 h
    rw [inner_sub_right] at h2
    linarith
  · rw [heq]

/-- Along a ray, strictly: `t < t'`, `v ≠ 0` and affinely spanning `z_j`. -/
lemma lseMap_ray_strict {n : ℕ} {ε κ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) (a : Fin n → ℝ) (z : Fin n → E)
    (hspan : affineSpan ℝ (Set.range z) = ⊤) {v : E} (hv : v ≠ 0) {t t' : ℝ} (htt : t < t') :
    ⟪v, lseMap ε κ a z (t • v)⟫ < ⟪v, lseMap ε κ a z (t' • v)⟫ := by
  have hne : t' • v ≠ t • v := by
    intro h
    have : (t' - t) • v = 0 := by rw [sub_smul, h, sub_self]
    rcases smul_eq_zero.1 this with h0 | h0
    · linarith
    · exact hv h0
  have h := lseMap_inner_pos hε hκ a z hspan hne
  rw [← sub_smul, real_inner_smul_right, real_inner_comm] at h
  have h2 : 0 < ⟪v, lseMap ε κ a z (t' • v) - lseMap ε κ a z (t • v)⟫ :=
    pos_of_mul_pos_right h (sub_pos.2 htt).le
  rw [inner_sub_right] at h2
  linarith

lemma lseMap_path_monotoneOn {n : ℕ} {ε κ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) (a : Fin n → ℝ) (z : Fin n → E)
    (v : E) {S : Set ℝ} {τ : ℝ → ℝ} (hτ : MonotoneOn τ S) :
    MonotoneOn (fun p => ⟪v, lseMap ε κ a z (τ p • v)⟫) S :=
  fun _ hp _ hq hpq => lseMap_ray_mono hε hκ a z v (hτ hp hq hpq)

lemma lseMap_path_strictMonoOn {n : ℕ} {ε κ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) (a : Fin n → ℝ) (z : Fin n → E)
    (hspan : affineSpan ℝ (Set.range z) = ⊤) {v : E} (hv : v ≠ 0) {S : Set ℝ} {τ : ℝ → ℝ}
    (hτ : StrictMonoOn τ S) : StrictMonoOn (fun p => ⟪v, lseMap ε κ a z (τ p • v)⟫) S :=
  fun _ hp _ hq hpq => lseMap_ray_strict hε hκ a z hspan hv (hτ hp hq hpq)

end General

/-! ### The calibration inverse `τ_p = c_K^{-1}(p)` -/

section Calib
variable {K : ℕ}

local notation "Eu" => EuclideanSpace ℝ (Fin K)

lemma cdfKInv_monotoneOn (μ : Measure Eu) (ρ : Eu → ℝ) (h1 : StatFormal.Wave23a.cdfK μ ρ 1 = 1) :
    MonotoneOn (StatFormal.Wave23a.cdfKInv μ ρ) (Icc 0 1) := by
  intro p hp p' hp' hpp
  unfold StatFormal.Wave23a.cdfKInv
  refine csInf_le_csInf ⟨0, fun t ht => ht.1.1⟩ ?_ ?_
  · exact ⟨1, ⟨zero_le_one, le_rfl⟩, by rw [h1]; exact hp'.2⟩
  · intro t ht
    exact ⟨ht.1, le_trans hpp ht.2⟩

lemma cdfKInv_strictMonoOn (μ : Measure Eu) (ρ : Eu → ℝ)
    (hc : ContinuousOn (StatFormal.Wave23a.cdfK μ ρ) (Icc 0 1)) (h0 : StatFormal.Wave23a.cdfK μ ρ 0 = 0)
    (h1 : StatFormal.Wave23a.cdfK μ ρ 1 = 1) : StrictMonoOn (StatFormal.Wave23a.cdfKInv μ ρ) (Icc 0 1) := by
  intro p hp p' hp' hpp
  rcases (cdfKInv_monotoneOn μ ρ h1 hp hp' hpp.le).lt_or_eq with h | h
  · exact h
  · exfalso
    have e1 := (StatFormal.Wave23a.cdfK_inv_spec μ ρ hc h0 h1 hp).2
    have e2 := (StatFormal.Wave23a.cdfK_inv_spec μ ρ hc h0 h1 hp').2
    rw [h] at e1
    linarith

end Calib

/-! ### C `prop:cond-paths` -/

theorem cond_paths_mono : Claims.cond_paths_mono := by
  intro K n ε a Z μ ρ v hε h1
  exact lseMap_path_monotoneOn hε two_pos a Z v (cdfKInv_monotoneOn μ ρ h1)

theorem cond_paths_strict : Claims.cond_paths_strict := by
  intro K n ε a Z μ ρ v hε hspan hv hc h0 h1
  exact lseMap_path_strictMonoOn hε two_pos a Z hspan hv (cdfKInv_strictMonoOn μ ρ hc h0 h1)

/-! ### T `prop:paths-M` -/

theorem paths_M_mono : Claims.paths_M_mono := by
  intro K n ε κ a z ρK v hε hκ hρ
  exact ⟨lseMap_path_monotoneOn hε hκ a z v hρ,
    fun hspan hρs hv => lseMap_path_strictMonoOn hε hκ a z hspan hv hρs⟩

theorem paths_M_level : Claims.paths_M_level := by
  intro K C μ Q F Φ Ψ B ρK p v hΨ hFQ hQB hv hρ0 hint hc
  have hQ := hQB _ hint
  rw [hΨ _ hQ, hFQ _ hint, norm_smul, hv, mul_one, Real.norm_eq_abs, abs_of_nonneg hρ0, hc]
  refine ⟨rfl, fun hpos => ?_⟩
  simp only [signMap, norm_smul, hv, mul_one, Real.norm_eq_abs, abs_of_nonneg hρ0, smul_smul,
    inv_mul_cancel₀ hpos.ne', one_smul]

lemma norm_lseMap_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ} (ε κ : ℝ)
    (a : Fin n → ℝ) (z : Fin n → E) {B : ℝ} (hB : 0 ≤ B) (hz : ∀ j, ‖z j‖ ≤ B) (u : E) :
    ‖lseMap ε κ a z u‖ ≤ B := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [lseMap, hB]
  unfold lseMap
  calc ‖∑ j, softmax (fun i => (a i + κ * ⟪z i, u⟫) / ε) j • z j‖
      ≤ ∑ j, ‖softmax (fun i => (a i + κ * ⟪z i, u⟫) / ε) j • z j‖ := norm_sum_le _ _
    _ ≤ ∑ j, softmax (fun i => (a i + κ * ⟪z i, u⟫) / ε) j * B := by
        apply Finset.sum_le_sum; intro j _
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (softmax_pos' _ j)]
        exact mul_le_mul_of_nonneg_left (hz j) (softmax_pos' _ j).le
    _ = B := by rw [← Finset.sum_mul, sum_softmax' _ hn, one_mul]

theorem paths_M_uniform : Claims.paths_M_uniform := by
  intro K n T V W M _ _ _ _ _ Ex D vbar ι Λ b B ε κ δ ρK Q a z hε hκ hδ hδ1 hΛ hρ hρ0 hLB hι hb hz hQ
  have hmem1 : (1 - δ) ∈ Ico (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hB : 0 ≤ B := le_trans (norm_nonneg _) (hQ 0 (by rw [norm_zero]; exact hρ0 _ hmem1))
  -- `lem:exp` (frozen `LengthBound`, pointwise bound of Wave 22b) with `eq:Hembed`, on the coefficient ball
  have hrec : ∀ x y : EuclideanSpace ℝ (Fin K), ‖x‖ ≤ B → ‖y‖ ≤ B →
      (⨆ t, edist (Ex t (vbar t + ι x t)) (Ex t (vbar t + ι y t))) ≤
        StatFormal.OTFD.Wave22b.Lb D b * ENNReal.ofReal (Λ * ‖x - y‖) := by
    intro x y hx hy
    refine iSup_le fun t => ?_
    refine (StatFormal.OTFD.Wave22b.exp_pointwise hLB t (hb x hx t) (hb y hy t)).trans ?_
    gcongr
    have hsub : vbar t + ι x t - (vbar t + ι y t) = ι (x - y) t := by
      rw [map_sub, Pi.sub_apply]; abel
    rw [hsub, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hι _ _)
  have hbound : ∀ (m : ℕ) (S : ℝ), (∀ u, ‖u‖ ≤ ρK (1 - δ) → ‖lseMap ε κ (a m) (z m) u - Q u‖ ≤ S) →
      ∀ p ∈ Icc (0 : ℝ) (1 - δ), ∀ v : EuclideanSpace ℝ (Fin K), ‖v‖ = 1 →
        (⨆ t, edist (Ex t (vbar t + ι (lseMap ε κ (a m) (z m) (ρK p • v)) t))
            (Ex t (vbar t + ι (Q (ρK p • v)) t))) ≤
          StatFormal.OTFD.Wave22b.Lb D b * ENNReal.ofReal (Λ * S) := by
    intro m S hS p hp v hv
    have hpm : p ∈ Ico (0 : ℝ) 1 := ⟨hp.1, by linarith [hp.2]⟩
    have hu : ‖ρK p • v‖ ≤ ρK (1 - δ) := by
      rw [norm_smul, hv, mul_one, Real.norm_eq_abs, abs_of_nonneg (hρ0 p hpm)]
      exact hρ hpm hmem1 hp.2
    refine (hrec _ _ (norm_lseMap_le ε κ (a m) (z m) hB (hz m) (ρK p • v)) (hQ _ hu)).trans ?_
    gcongr
    exact hS _ hu
  refine ⟨hbound, fun hLb hconv η hη => ?_⟩
  have hLr : 0 ≤ (StatFormal.OTFD.Wave22b.Lb D b).toReal := ENNReal.toReal_nonneg
  have hden : 0 < (StatFormal.OTFD.Wave22b.Lb D b).toReal * Λ + 1 := by positivity
  have hη' : 0 < η / ((StatFormal.OTFD.Wave22b.Lb D b).toReal * Λ + 1) := div_pos hη hden
  filter_upwards [hconv _ hη'] with m hm p hp v hv
  refine (hbound m _ hm p hp v hv).trans ?_
  have hrw : StatFormal.OTFD.Wave22b.Lb D b * ENNReal.ofReal (Λ * (η / ((StatFormal.OTFD.Wave22b.Lb D b).toReal * Λ + 1)))
      = ENNReal.ofReal ((StatFormal.OTFD.Wave22b.Lb D b).toReal *
          (Λ * (η / ((StatFormal.OTFD.Wave22b.Lb D b).toReal * Λ + 1)))) := by
    rw [ENNReal.ofReal_mul hLr, ENNReal.ofReal_toReal hLb]
  rw [hrw]
  apply ENNReal.ofReal_le_ofReal
  rw [← mul_assoc, mul_div_assoc', div_le_iff₀ hden]
  nlinarith [mul_nonneg hLr hΛ]

end StatFormal.Wave24c
