import StatFormal.Archive.Wave23c.RouteEllPhi
import StatFormal.Lib.MatchedGrid.Cells
import StatFormal.Lib.MatchedGrid.Gaussian
import TauCeti.Probability.Quantile

set_option linter.style.longLine false

/-!
# The midpoint bound for the squared Gaussian quantile

`h(p) = {Φ^{-1}(p)}²` satisfies the Hermite–Hadamard midpoint inequality on every cell `[l/q, (l+1)/q]`
(it is convex on each half `(0, ½]`, `[½, 1)`, which is all that is used; the cell containing `½` in its interior has
midpoint `½`, where `h = 0`), so `q⁻¹ Σ_{l<q} h((l + ½)/q) ≤ ∫_0^1 h = E Z² = 1`.

Convexity on `[½, 1)` is obtained without derivatives: for `0 ≤ y`, `0 ≤ d`, the Gaussian mass of `(y + d, y + 2d]` is
at most that of `(y, y + d]` (the density decreases on `[0, ∞)`), hence `Φ^{-1}(m + t) − Φ^{-1}(m) ≥
Φ^{-1}(m) − Φ^{-1}(m − t)` for `½ ≤ m − t`, `m + t < 1`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace StatFormal.Foundations.MatchedGrid

open StatFormal.Wave23c (Φn Φn_strictMono Φn_continuous Φn_neg)

/-- `Φ^{-1}`, the Tau Ceti quantile of `N(0, 1)`. -/
abbrev Φq (t : ℝ) : ℝ := (gaussianReal 0 1).quantile t

lemma Φn_Φq {t : ℝ} (h0 : 0 < t) (h1 : t < 1) : Φn (Φq t) = t := by
  apply le_antisymm _ (Measure.le_cdf_quantile _ h1)
  by_contra hgt
  push Not at hgt
  have hev : ∀ᶠ x in 𝓝 (Φq t), t < Φn x := Φn_continuous.continuousAt.eventually (lt_mem_nhds hgt)
  obtain ⟨x, hx1, hx2⟩ :=
    ((hev.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin : ∀ᶠ x in 𝓝[<] Φq t, _ ∧ _).exists
  have := (Measure.lt_quantile_iff (gaussianReal 0 1) h0 h1 (x := x)).1 hx2
  exact lt_asymm this hx1

lemma Φq_Φn (y : ℝ) : Φq (Φn y) = y := by
  have h0 : 0 < Φn y := StatFormal.Wave23c.Φn_pos y
  have h1 : Φn y < 1 := StatFormal.Wave23c.Φn_lt_one y
  apply le_antisymm ((Measure.quantile_le_iff _ h0 h1).2 le_rfl)
  by_contra hlt
  push Not at hlt
  have := Φn_strictMono hlt
  rw [Φn_Φq h0 h1] at this
  exact lt_irrefl _ this

lemma Φn_zero : Φn 0 = 1 / 2 := by
  have := Φn_neg 0
  rw [neg_zero] at this
  linarith

lemma Φq_half : Φq (1 / 2) = 0 := by rw [← Φn_zero, Φq_Φn]

lemma Φq_one_sub {p : ℝ} (h0 : 0 < p) (h1 : p < 1) : Φq (1 - p) = -Φq p := by
  rw [← Φn_Φq h0 h1, ← Φn_neg, Φq_Φn, Φn_Φq h0 h1]

lemma measurable_Φq : Measurable Φq := Measure.measurable_quantile _

/-- The Gaussian mass of `(a, b]` is `Φ(b) − Φ(a)`. -/
lemma gauss_Ioc (a b : ℝ) : gaussianReal 0 1 (Ioc a b) = ENNReal.ofReal (Φn b - Φn a) := by
  rw [← (cdf (gaussianReal 0 1)).measure_Ioc, measure_cdf]

lemma gaussianPDF_add_le {y d : ℝ} (hy : 0 ≤ y) (hd : 0 ≤ d) : gaussianPDF 0 1 (y + d) ≤ gaussianPDF 0 1 y := by
  unfold gaussianPDF
  refine ENNReal.ofReal_le_ofReal ?_
  rw [gaussianPDFReal, gaussianPDFReal]
  gcongr
  nlinarith

/-- Unimodality: `Φ(y + 2d) − Φ(y + d) ≤ Φ(y + d) − Φ(y)` for `y, d ≥ 0`. -/
lemma Φn_incr_le {y d : ℝ} (hy : 0 ≤ y) (hd : 0 ≤ d) : Φn (y + d + d) - Φn (y + d) ≤ Φn (y + d) - Φn y := by
  have hmono := Φn_strictMono.monotone
  have key : gaussianReal 0 1 (Ioc (y + d) (y + d + d)) ≤ gaussianReal 0 1 (Ioc y (y + d)) := by
    rw [gaussianReal_apply 0 one_ne_zero, gaussianReal_apply 0 one_ne_zero]
    have hpre : (fun x : ℝ => x + d) ⁻¹' Ioc (y + d) (y + d + d) = Ioc y (y + d) := by
      ext x; simp
    rw [← (measurePreserving_add_right volume d).setLIntegral_comp_preimage_emb
      (MeasurableEquiv.addRight d).measurableEmbedding, hpre]
    refine setLIntegral_mono (measurable_gaussianPDF 0 1) fun x hx => gaussianPDF_add_le (hy.trans hx.1.le) hd
  rw [gauss_Ioc, gauss_Ioc] at key
  exact (ENNReal.ofReal_le_ofReal_iff (by linarith [hmono (show y ≤ y + d by linarith)])).1 key

/-- Midpoint convexity of `(Φ^{-1})²` on `[½, 1)`. -/
lemma sq_Φq_mid_upper {s s' : ℝ} (hs : 1 / 2 ≤ s) (hss : s ≤ s') (hs' : s' < 1) :
    2 * Φq ((s + s') / 2) ^ 2 ≤ Φq s ^ 2 + Φq s' ^ 2 := by
  have hmono : MonotoneOn Φq (Ioo 0 1) := Measure.monotoneOn_quantile _
  set m := (s + s') / 2
  have hm1 : 1 / 2 ≤ m := by simp only [m]; linarith
  have hm2 : m < 1 := by simp only [m]; linarith
  have mem : ∀ {r}, 1 / 2 ≤ r → r < 1 → r ∈ Ioo (0 : ℝ) 1 := fun h1 h2 => ⟨by linarith, h2⟩
  set x := Φq m
  set v := Φq s
  set u := Φq s'
  have hv0 : 0 ≤ v := by
    rw [← Φq_half]; exact hmono (mem le_rfl (by norm_num)) (mem hs (by linarith)) hs
  have hvx : v ≤ x := hmono (mem hs (by linarith)) (mem hm1 hm2) (by simp only [m]; linarith)
  have hxu : x ≤ u := hmono (mem hm1 hm2) (mem (by linarith) hs') (by simp only [m]; linarith)
  have hkey : 2 * x - v ≤ u := by
    by_contra hlt
    push Not at hlt
    have h1 := Φn_strictMono hlt
    rw [Φn_Φq (by linarith) hs'] at h1
    have h2 := Φn_incr_le hv0 (sub_nonneg.2 hvx)
    rw [show v + (x - v) + (x - v) = 2 * x - v by ring, show v + (x - v) = x by ring, Φn_Φq (by linarith) hm2,
      Φn_Φq (by linarith) (by linarith)] at h2
    simp only [m] at h2
    linarith
  nlinarith

/-- Midpoint convexity of `(Φ^{-1})²` on each half of `(0, 1)`. -/
lemma sq_Φq_mid {s s' : ℝ} (hss : s ≤ s') (h : (1 / 2 ≤ s ∧ s' < 1) ∨ (0 < s ∧ s' ≤ 1 / 2)) :
    2 * Φq ((s + s') / 2) ^ 2 ≤ Φq s ^ 2 + Φq s' ^ 2 := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact sq_Φq_mid_upper h1 hss h2
  · have := sq_Φq_mid_upper (s := 1 - s') (s' := 1 - s) (by linarith) (by linarith) (by linarith)
    rw [show (1 - s' + (1 - s)) / 2 = 1 - (s + s') / 2 by ring, Φq_one_sub (by linarith) (by linarith),
      Φq_one_sub (by linarith) (by linarith), Φq_one_sub (by linarith) (by linarith)] at this
    simp only [neg_sq] at this
    linarith

/-- Hermite–Hadamard on a cell lying in one half of `(0, 1)`. -/
lemma cell_mid_le {a b : ℝ} (h : (1 / 2 ≤ a ∧ b ≤ 1) ∨ (0 ≤ a ∧ b ≤ 1 / 2)) :
    ENNReal.ofReal (Φq ((a + b) / 2) ^ 2) * ENNReal.ofReal (b - a) ≤
      ∫⁻ p in Ioo a b, ENNReal.ofReal (Φq p ^ 2) := by
  set F : ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal (Φq p ^ 2)
  have hF : Measurable F := ENNReal.measurable_ofReal.comp (measurable_Φq.pow_const 2)
  have hrefl : ∫⁻ p in Ioo a b, F (a + b - p) = ∫⁻ p in Ioo a b, F p := by
    have hpre : (fun p : ℝ => a + b - p) ⁻¹' Ioo a b = Ioo a b := by
      ext p; simp only [mem_preimage, mem_Ioo]; constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
    conv_lhs => rw [← hpre]
    exact (Measure.measurePreserving_sub_left volume (a + b)).setLIntegral_comp_preimage_emb
      (MeasurableEquiv.subLeft (a + b)).measurableEmbedding F (Ioo a b)
  have hpt : ∀ p ∈ Ioo a b, ENNReal.ofReal (2 * Φq ((a + b) / 2) ^ 2) ≤ F p + F (a + b - p) := by
    intro p hp
    simp only [F]
    rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rcases le_total p (a + b - p) with hle | hle
    · have := sq_Φq_mid hle (by rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
                                · exact Or.inl ⟨by linarith [hp.1], by linarith [hp.1]⟩
                                · exact Or.inr ⟨by linarith [hp.1], by linarith [hp.1]⟩)
      rwa [show (p + (a + b - p)) / 2 = (a + b) / 2 by ring] at this
    · have := sq_Φq_mid hle (by rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
                                · exact Or.inl ⟨by linarith [hp.2], by linarith [hp.2]⟩
                                · exact Or.inr ⟨by linarith [hp.2], by linarith [hp.2]⟩)
      rw [show (a + b - p + p) / 2 = (a + b) / 2 by ring] at this
      linarith
  have h2 : ENNReal.ofReal (2 * Φq ((a + b) / 2) ^ 2) * ENNReal.ofReal (b - a) ≤
      (∫⁻ p in Ioo a b, F p) + ∫⁻ p in Ioo a b, F p := by
    calc ENNReal.ofReal (2 * Φq ((a + b) / 2) ^ 2) * ENNReal.ofReal (b - a)
        = ∫⁻ _ in Ioo a b, ENNReal.ofReal (2 * Φq ((a + b) / 2) ^ 2) := by
          rw [setLIntegral_const, Real.volume_Ioo, mul_comm]
      _ ≤ ∫⁻ p in Ioo a b, (F p + F (a + b - p)) := setLIntegral_mono (hF.add (hF.comp (by fun_prop))) hpt
      _ = (∫⁻ p in Ioo a b, F p) + ∫⁻ p in Ioo a b, F (a + b - p) := lintegral_add_left hF (fun p => F (a + b - p))
      _ = _ := by rw [hrefl]
  rw [show (∫⁻ p in Ioo a b, F p) + ∫⁻ p in Ioo a b, F p = 2 * ∫⁻ p in Ioo a b, F p from (two_mul _).symm,
    ENNReal.ofReal_mul (by norm_num), mul_assoc, ENNReal.ofReal_ofNat] at h2
  exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).1 h2

/-- `∫_0^1 {Φ^{-1}}² = E Z² = 1` (inverse transform sampling). -/
lemma lintegral_sq_Φq : ∫⁻ p in Ioc 0 1, ENNReal.ofReal (Φq p ^ 2) = 1 := by
  have hm : Measurable fun x : ℝ => ENNReal.ofReal (x ^ 2) :=
    ENNReal.measurable_ofReal.comp (measurable_id.pow_const 2)
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm,
    ← lintegral_map (f := fun x : ℝ => ENNReal.ofReal (x ^ 2)) hm measurable_Φq,
    Measure.map_quantile_volume_Ioo, lintegral_sq_gaussianReal_zero]
  simp

/-- One cell: `q⁻¹ h((l + ½)/q) ≤ ∫_{(l/q, (l+1)/q]} h`. -/
lemma cell_mid_le' {q l : ℕ} (hl : l < q) :
    ENNReal.ofReal (Φq (((l : ℝ) + 1 / 2) / q) ^ 2) * ENNReal.ofReal (1 / q) ≤
      ∫⁻ p in Ioc ((l : ℝ) / q) (((l + 1 : ℕ) : ℝ) / q), ENNReal.ofReal (Φq p ^ 2) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast (Nat.zero_lt_of_lt hl)
  have hmid : ((l : ℝ) / q + ((l + 1 : ℕ) : ℝ) / q) / 2 = ((l : ℝ) + 1 / 2) / q := by push_cast; field_simp; ring
  have hlen : ((l + 1 : ℕ) : ℝ) / q - (l : ℝ) / q = 1 / q := by push_cast; field_simp; ring
  rcases lt_trichotomy (2 * l + 1) q with h | h | h
  · -- lower half
    have h' : (2 * (l : ℝ) + 2) ≤ q := by exact_mod_cast h
    have := cell_mid_le (a := (l : ℝ) / q) (b := ((l + 1 : ℕ) : ℝ) / q)
      (Or.inr ⟨by positivity, by rw [div_le_iff₀ hq]; push_cast; linarith⟩)
    rw [hmid, hlen] at this
    exact this.trans (lintegral_mono_set Ioo_subset_Ioc_self)
  · -- the middle cell, midpoint `½`
    have h' : (2 * (l : ℝ) + 1) = q := by exact_mod_cast h
    have : ((l : ℝ) + 1 / 2) / q = 1 / 2 := by rw [div_eq_iff hq.ne']; linarith
    rw [this, Φq_half]
    simp
  · -- upper half
    have h' : (q : ℝ) ≤ 2 * l := by exact_mod_cast (show q ≤ 2 * l by omega)
    have h'' : (l : ℝ) + 1 ≤ q := by exact_mod_cast hl
    have := cell_mid_le (a := (l : ℝ) / q) (b := ((l + 1 : ℕ) : ℝ) / q)
      (Or.inl ⟨by rw [le_div_iff₀ hq]; linarith, by rw [div_le_iff₀ hq]; push_cast; linarith⟩)
    rw [hmid, hlen] at this
    exact this.trans (lintegral_mono_set Ioo_subset_Ioc_self)

/-- **The midpoint bound** `q⁻¹ Σ_{l<q} {Φ^{-1}((l + ½)/q)}² ≤ ∫_0^1 {Φ^{-1}}² = 1`. -/
theorem midpoint_sq_Φq_le {q : ℕ} (hq : 1 ≤ q) :
    (q : ℝ)⁻¹ * ∑ l : Fin q, Φq (((l : ℝ) + 1 / 2) / q) ^ 2 ≤ 1 := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hsum : ∑ l : Fin q, ENNReal.ofReal (Φq (((l : ℝ) + 1 / 2) / q) ^ 2) * ENNReal.ofReal (1 / q) ≤ 1 := by
    calc _ ≤ ∑ l : Fin q, ∫⁻ p in Ioc (((l : ℕ) : ℝ) / q) ((((l : ℕ) + 1 : ℕ) : ℝ) / q), ENNReal.ofReal (Φq p ^ 2) :=
          Finset.sum_le_sum fun l _ => cell_mid_le' l.2
      _ = ∫⁻ p in Ioc 0 1, ENNReal.ofReal (Φq p ^ 2) := by
          rw [← lintegral_finsetSum_measure,
            Fin.sum_univ_eq_sum_range (fun l => volume.restrict (Ioc ((l : ℝ) / q) (((l + 1 : ℕ) : ℝ) / q))),
            ← restrict_Ioc_eq_sum volume (fun l : ℕ => (l : ℝ) / q) ?_ q]
          · simp [hq'.ne']
          · intro a b hab
            simp only
            gcongr
      _ = 1 := lintegral_sq_Φq
  have hnn : ∀ l : Fin q, 0 ≤ Φq (((l : ℝ) + 1 / 2) / q) ^ 2 * (1 / q) := fun l => by positivity
  simp_rw [← ENNReal.ofReal_mul (sq_nonneg _)] at hsum
  rw [← ENNReal.ofReal_sum_of_nonneg (fun l _ => hnn l), ENNReal.ofReal_le_one, ← Finset.sum_mul] at hsum
  rw [mul_comm, ← one_div]
  exact hsum

end StatFormal.Foundations.MatchedGrid
