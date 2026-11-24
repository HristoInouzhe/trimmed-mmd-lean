import StatFormal.Archive.Wave24a.Statements
import TauCeti.Probability.McDiarmid
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Moments.SubGaussian

/-!
# Route — A `prop:parsimony`, the reference-only tolerance (untrusted)

The proof of `prop:selector`(i) at one candidate with `D = 0`: all `n_v + m_v` points are i.i.d. `Υ#μ`.
* Bounded differences: `|D̂(a,b) − D̂(a',b')| ≤ (4/n)Σ‖a_i − a'_i‖ + (4/m)Σ‖b_j − b'_j‖`, so changing one point moves
  `D̂` by at most `8R/n_v` or `8R/m_v`; McDiarmid (Tau Ceti) gives the sub-Gaussian proxy `16R²h`.
* Mean: every off-diagonal pair of coordinates has the same law (permutation invariance of `μ^{⊗(n+m)}`), so
  `E D̂ = e(2 − (n−1)/n − (m−1)/m) = e h ≤ 2Rh` with `e = E‖Υ(U) − Υ(U')‖ ≤ 2R`.
* Tail at `t = R(32h log(2/γ))^{1/2}`: `P(D̂ > 2Rh + t) ≤ e^{−t²/(32R²h)} = γ/2 ≤ γ` (one-sided McDiarmid; the
  paper's two-sided `2e^{…}` is not needed), and `D̂ ≥ −4R` makes the quantile's set bounded below.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal NNReal

namespace StatFormal.Wave24a

section Det
variable {E : Type*} [NormedAddCommGroup E]

lemma abs_dsum_sub_le {ι κ : Type*} [Fintype ι] [Fintype κ] (f g h : ι → κ → ℝ)
    (hfg : ∀ i j, |f i j - g i j| ≤ h i j) :
    |∑ i, ∑ j, f i j - ∑ i, ∑ j, g i j| ≤ ∑ i, ∑ j, h i j := by
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => hfg i j)

lemma abs_norm_sub_sub_le (x y x' y' : E) : |‖x - y‖ - ‖x' - y'‖| ≤ ‖x - x'‖ + ‖y - y'‖ := by
  refine (abs_norm_sub_norm_le _ _).trans ?_
  calc ‖x - y - (x' - y')‖ = ‖(x - x') - (y - y')‖ := by congr 1; abel
    _ ≤ ‖x - x'‖ + ‖y - y'‖ := norm_sub_le _ _

lemma edVstat_sub_le {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (a a' : Fin n → E) (b b' : Fin m → E) :
    |edVstat a b - edVstat a' b'| ≤
      4 / (n : ℝ) * ∑ i, ‖a i - a' i‖ + 4 / (m : ℝ) * ∑ j, ‖b j - b' j‖ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  set A := ∑ i, ‖a i - a' i‖
  set B := ∑ j, ‖b j - b' j‖
  have hX := abs_dsum_sub_le (fun i j => ‖a i - b j‖) (fun i j => ‖a' i - b' j‖)
    (fun i j => ‖a i - a' i‖ + ‖b j - b' j‖) fun i j => abs_norm_sub_sub_le _ _ _ _
  have hY := abs_dsum_sub_le (fun i i' => ‖a i - a i'‖) (fun i i' => ‖a' i - a' i'‖)
    (fun i i' => ‖a i - a' i‖ + ‖a i' - a' i'‖) fun i j => abs_norm_sub_sub_le _ _ _ _
  have hW := abs_dsum_sub_le (fun j j' => ‖b j - b j'‖) (fun j j' => ‖b' j - b' j'‖)
    (fun j j' => ‖b j - b' j‖ + ‖b j' - b' j'‖) fun i j => abs_norm_sub_sub_le _ _ _ _
  have eX : ∑ i : Fin n, ∑ j : Fin m, (‖a i - a' i‖ + ‖b j - b' j‖) = m * A + n * B := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      A, B, ← Finset.mul_sum] <;> ring
  have eY : ∑ i : Fin n, ∑ i' : Fin n, (‖a i - a' i‖ + ‖a i' - a' i'‖) = 2 * n * A := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      A, ← Finset.mul_sum] <;> ring
  have eW : ∑ j : Fin m, ∑ j' : Fin m, (‖b j - b' j‖ + ‖b j' - b' j'‖) = 2 * m * B := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      B, ← Finset.mul_sum] <;> ring
  rw [eX] at hX; rw [eY] at hY; rw [eW] at hW
  have hdiff : edVstat a b - edVstat a' b' =
      2 / ((n : ℝ) * m) * (∑ i, ∑ j, ‖a i - b j‖ - ∑ i, ∑ j, ‖a' i - b' j‖) -
      1 / (n : ℝ) ^ 2 * (∑ i, ∑ i', ‖a i - a i'‖ - ∑ i, ∑ i', ‖a' i - a' i'‖) -
      1 / (m : ℝ) ^ 2 * (∑ j, ∑ j', ‖b j - b j'‖ - ∑ j, ∑ j', ‖b' j - b' j'‖) := by
    unfold edVstat; ring
  rw [hdiff]
  have c1 : 0 ≤ 2 / ((n : ℝ) * m) := by positivity
  have c2 : 0 ≤ 1 / (n : ℝ) ^ 2 := by positivity
  have c3 : 0 ≤ 1 / (m : ℝ) ^ 2 := by positivity
  calc _ ≤ |2 / ((n : ℝ) * m) * (∑ i, ∑ j, ‖a i - b j‖ - ∑ i, ∑ j, ‖a' i - b' j‖)| +
        |1 / (n : ℝ) ^ 2 * (∑ i, ∑ i', ‖a i - a i'‖ - ∑ i, ∑ i', ‖a' i - a' i'‖)| +
        |1 / (m : ℝ) ^ 2 * (∑ j, ∑ j', ‖b j - b j'‖ - ∑ j, ∑ j', ‖b' j - b' j'‖)| := by
        exact (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ 2 / ((n : ℝ) * m) * (m * A + n * B) + 1 / (n : ℝ) ^ 2 * (2 * n * A) + 1 / (m : ℝ) ^ 2 * (2 * m * B) := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg c1, abs_of_nonneg c2, abs_of_nonneg c3]
        gcongr
    _ = 4 / (n : ℝ) * A + 4 / (m : ℝ) * B := by
        field_simp; ring

lemma edVstat_bounds {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) {R : ℝ} (a : Fin n → E) (b : Fin m → E)
    (ha : ∀ i, ‖a i‖ ≤ R) (hb : ∀ j, ‖b j‖ ≤ R) : -(4 * R) ≤ edVstat a b ∧ edVstat a b ≤ 4 * R := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hd : ∀ x y : E, ‖x‖ ≤ R → ‖y‖ ≤ R → ‖x - y‖ ≤ 2 * R := fun x y hx hy =>
    (norm_sub_le x y).trans (by linarith)
  have hX : ∑ i, ∑ j, ‖a i - b j‖ ≤ n * m * (2 * R) := by
    calc _ ≤ ∑ _i : Fin n, ∑ _j : Fin m, 2 * R := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          hd _ _ (ha i) (hb j)
      _ = n * m * (2 * R) := by simp; ring
  have hY : ∑ i, ∑ i', ‖a i - a i'‖ ≤ n * n * (2 * R) := by
    calc _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, 2 * R := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          hd _ _ (ha i) (ha j)
      _ = n * n * (2 * R) := by simp; ring
  have hW : ∑ j, ∑ j', ‖b j - b j'‖ ≤ m * m * (2 * R) := by
    calc _ ≤ ∑ _i : Fin m, ∑ _j : Fin m, 2 * R := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          hd _ _ (hb i) (hb j)
      _ = m * m * (2 * R) := by simp; ring
  have h0X : 0 ≤ ∑ i, ∑ j, ‖a i - b j‖ := by positivity
  have h0Y : 0 ≤ ∑ i, ∑ i', ‖a i - a i'‖ := by positivity
  have h0W : 0 ≤ ∑ j, ∑ j', ‖b j - b j'‖ := by positivity
  unfold edVstat
  constructor
  · have e1 : 1 / (n : ℝ) ^ 2 * ∑ i, ∑ i', ‖a i - a i'‖ ≤ 2 * R := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]; nlinarith
    have e2 : 1 / (m : ℝ) ^ 2 * ∑ j, ∑ j', ‖b j - b j'‖ ≤ 2 * R := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]; nlinarith
    have e3 : 0 ≤ 2 / ((n : ℝ) * m) * ∑ i, ∑ j, ‖a i - b j‖ := by positivity
    linarith
  · have e3 : 2 / ((n : ℝ) * m) * ∑ i, ∑ j, ‖a i - b j‖ ≤ 4 * R := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
    have e1 : 0 ≤ 1 / (n : ℝ) ^ 2 * ∑ i, ∑ i', ‖a i - a i'‖ := by positivity
    have e2 : 0 ≤ 1 / (m : ℝ) ^ 2 * ∑ j, ∑ j', ‖b j - b j'‖ := by positivity
    linarith

end Det

theorem parsimony_tolerance_tendsto : Claims.parsimony_tolerance_tendsto := by
  intro R γ nv mv _ _ hnv hmv
  have hinv : ∀ {s : ℕ → ℕ}, Tendsto s atTop atTop → Tendsto (fun k => 1 / (s k : ℝ)) atTop (𝓝 0) := by
    intro s hs
    exact (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hs)).congr fun k => by
      simp [one_div]
  have hh : Tendsto (fun k => 1 / (nv k : ℝ) + 1 / (mv k : ℝ)) atTop (𝓝 0) := by
    simpa using (hinv hnv).add (hinv hmv)
  have h1 : Tendsto (fun k => 2 * R * (1 / (nv k : ℝ) + 1 / (mv k : ℝ))) atTop (𝓝 0) := by
    simpa using hh.const_mul (2 * R)
  have h2 : Tendsto (fun k => R * √(32 * (1 / (nv k : ℝ) + 1 / (mv k : ℝ)) * Real.log (2 / γ))) atTop
      (𝓝 0) := by
    have := ((hh.const_mul 32).mul_const (Real.log (2 / γ))).sqrt.const_mul R
    simpa using this
  simpa [parsBound] using h1.add h2

section Prob
variable {𝒰 : Type*} [MeasurableSpace 𝒰] (μ : Measure 𝒰) [IsProbabilityMeasure μ]

lemma integral_comp_perm_pi {ι : Type*} [Fintype ι] (σ : Equiv.Perm ι) (G : (ι → 𝒰) → ℝ) :
    ∫ z, G (fun i => z (σ i)) ∂(Measure.pi fun _ : ι => μ) = ∫ z, G z ∂(Measure.pi fun _ : ι => μ) := by
  have mp := measurePreserving_arrowCongr' (fun _ : ι => μ) (fun _ : ι => μ) σ.symm
    (MeasurableEquiv.refl 𝒰) (fun _ => MeasurePreserving.id μ)
  have h : ∀ z : ι → 𝒰, (MeasurableEquiv.arrowCongr' σ.symm (MeasurableEquiv.refl 𝒰)) z = fun i => z (σ i) :=
    fun z => by
      ext i
      simp [MeasurableEquiv.arrowCongr', Equiv.arrowCongr', Equiv.arrowCongr]
  rw [← mp.integral_comp' G]
  simp_rw [h]

lemma exists_perm_pair {ι : Type*} [DecidableEq ι] {k0 l0 k l : ι} (h0 : k0 ≠ l0) (h : k ≠ l) :
    ∃ σ : Equiv.Perm ι, σ k0 = k ∧ σ l0 = l := by
  set l1 := Equiv.swap k0 k l0 with hl1
  have hkl1 : k ≠ l1 := by
    intro hk
    have : Equiv.swap k0 k k0 = Equiv.swap k0 k l0 := by rw [Equiv.swap_apply_left, ← hl1, hk]
    exact h0 ((Equiv.swap k0 k).injective this)
  refine ⟨(Equiv.swap k0 k).trans (Equiv.swap l1 l), ?_, ?_⟩
  · simp only [Equiv.trans_apply, Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne hkl1 h
  · simp only [Equiv.trans_apply, ← hl1, Equiv.swap_apply_left]

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma measurable_pairNorm {ι : Type*} {Υ : 𝒰 → E} (hΥ : Measurable Υ) (k l : ι) :
    Measurable fun z : ι → 𝒰 => ‖Υ (z k) - Υ (z l)‖ :=
  ((hΥ.comp (measurable_pi_apply k)).sub (hΥ.comp (measurable_pi_apply l))).norm

lemma integrable_pairNorm {ι : Type*} [Fintype ι] {Υ : 𝒰 → E} (hΥ : Measurable Υ) {R : ℝ}
    (hR : ∀ u, ‖Υ u‖ ≤ R) (k l : ι) :
    Integrable (fun z : ι → 𝒰 => ‖Υ (z k) - Υ (z l)‖) (Measure.pi fun _ : ι => μ) := by
  refine Integrable.of_bound (C := 2 * R) (measurable_pairNorm hΥ k l).aestronglyMeasurable
    (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact (norm_sub_le _ _).trans (by linarith [hR (z k), hR (z l)])

lemma integral_dsum {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β] (F : α → β → (ι → 𝒰) → ℝ)
    (hF : ∀ i j, Integrable (F i j) (Measure.pi fun _ : ι => μ)) :
    ∫ z, ∑ i, ∑ j, F i j z ∂(Measure.pi fun _ : ι => μ) = ∑ i, ∑ j, ∫ z, F i j z ∂(Measure.pi fun _ : ι => μ) := by
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ fun j _ => hF i j)]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact integral_finset_sum _ fun j _ => hF i j

lemma integral_edVstat {nv mv : ℕ} (hn : 1 ≤ nv) (hm : 1 ≤ mv) {Υ : 𝒰 → E} (hΥ : Measurable Υ) {R : ℝ}
    (hR : ∀ u, ‖Υ u‖ ≤ R) :
    ∫ z, edVstat (fun i => Υ (z (Sum.inl i))) (fun j => Υ (z (Sum.inr j))) ∂(Measure.pi fun _ : Fin nv ⊕ Fin mv => μ)
      ≤ 2 * R * (1 / (nv : ℝ) + 1 / (mv : ℝ)) := by
  classical
  set P := Measure.pi fun _ : Fin nv ⊕ Fin mv => μ
  set g : (Fin nv ⊕ Fin mv) → (Fin nv ⊕ Fin mv) → (Fin nv ⊕ Fin mv → 𝒰) → ℝ :=
    fun k l z => ‖Υ (z k) - Υ (z l)‖ with hg
  have hint := integrable_pairNorm (ι := Fin nv ⊕ Fin mv) μ hΥ hR
  set k0 : Fin nv ⊕ Fin mv := Sum.inl ⟨0, hn⟩
  set l0 : Fin nv ⊕ Fin mv := Sum.inr ⟨0, hm⟩
  set e := ∫ z, g k0 l0 z ∂P with he
  have hpair : ∀ k l, k ≠ l → ∫ z, g k l z ∂P = e := by
    intro k l hkl
    obtain ⟨σ, hσk, hσl⟩ := exists_perm_pair (show k0 ≠ l0 from Sum.inl_ne_inr) hkl
    have := integral_comp_perm_pi μ σ (g k0 l0)
    simp only [hg, hσk, hσl] at this
    exact this
  have hdiag : ∀ k, ∫ z, g k k z ∂P = 0 := fun k => by simp [hg]
  have hval : ∀ k l, ∫ z, g k l z ∂P = if k = l then 0 else e := fun k l => by
    split_ifs with h
    · rw [h]; exact hdiag l
    · exact hpair k l h
  have hn0 : (0 : ℝ) < nv := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < mv := by exact_mod_cast hm
  have hcount : ∀ (N : ℕ) (f : Fin N → Fin nv ⊕ Fin mv), Function.Injective f →
      ∑ i : Fin N, ∑ i' : Fin N, (if f i = f i' then (0 : ℝ) else e) = N * (N - 1) * e := by
    intro N f hf
    have : ∀ i : Fin N, ∑ i' : Fin N, (if f i = f i' then (0 : ℝ) else e) = (N - 1) * e := by
      intro i
      have h1 : ∀ i' : Fin N, (if f i = f i' then (0 : ℝ) else e) = e - (if i = i' then e else 0) := by
        intro i'
        by_cases h : i = i'
        · subst h; simp
        · rw [if_neg (hf.ne h), if_neg h, sub_zero]
      simp_rw [h1, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    simp_rw [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hE : ∫ z, edVstat (fun i => Υ (z (Sum.inl i))) (fun j => Υ (z (Sum.inr j))) ∂P =
      e * (1 / (nv : ℝ) + 1 / (mv : ℝ)) := by
    have hD : (fun z => edVstat (fun i => Υ (z (Sum.inl i))) (fun j => Υ (z (Sum.inr j)))) = fun z =>
        2 / ((nv : ℝ) * mv) * ∑ i, ∑ j, g (Sum.inl i) (Sum.inr j) z -
          1 / (nv : ℝ) ^ 2 * ∑ i, ∑ i', g (Sum.inl i) (Sum.inl i') z -
          1 / (mv : ℝ) ^ 2 * ∑ j, ∑ j', g (Sum.inr j) (Sum.inr j') z := rfl
    have iX : Integrable (fun z => ∑ i : Fin nv, ∑ j : Fin mv, g (Sum.inl i) (Sum.inr j) z) P :=
      integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hint _ _
    have iY : Integrable (fun z => ∑ i : Fin nv, ∑ i' : Fin nv, g (Sum.inl i) (Sum.inl i') z) P :=
      integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hint _ _
    have iW : Integrable (fun z => ∑ j : Fin mv, ∑ j' : Fin mv, g (Sum.inr j) (Sum.inr j') z) P :=
      integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hint _ _
    have iXY : Integrable (fun z => 2 / ((nv : ℝ) * mv) * ∑ i, ∑ j, g (Sum.inl i) (Sum.inr j) z -
        1 / (nv : ℝ) ^ 2 * ∑ i, ∑ i', g (Sum.inl i) (Sum.inl i') z) P :=
      (iX.const_mul _).sub (iY.const_mul _)
    rw [hD, integral_sub iXY (iW.const_mul _),
      integral_sub (iX.const_mul _) (iY.const_mul _), integral_const_mul, integral_const_mul,
      integral_const_mul, integral_dsum μ _ (fun i j => hint _ _), integral_dsum μ _ (fun i j => hint _ _),
      integral_dsum μ _ (fun i j => hint _ _)]
    have hval' : ∀ k l, ∫ z, ‖Υ (z k) - Υ (z l)‖ ∂(Measure.pi fun _ : Fin nv ⊕ Fin mv => μ) =
        if k = l then 0 else e := hval
    simp only [hval']
    rw [hcount nv Sum.inl Sum.inl_injective, hcount mv Sum.inr Sum.inr_injective]
    simp only [reduceCtorEq, if_false, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  have he2 : e ≤ 2 * R := by
    calc e ≤ ∫ _z, 2 * R ∂P := integral_mono (hint _ _) (integrable_const _) fun z =>
          (norm_sub_le _ _).trans (by linarith [hR (z k0), hR (z l0)])
      _ = 2 * R := by simp
  rw [hE]
  have hh : 0 ≤ 1 / (nv : ℝ) + 1 / (mv : ℝ) := by positivity
  nlinarith

end Prob

theorem parsimony_tolerance : Claims.parsimony_tolerance := by
  intro 𝒰 E _ _ _ _ _ μ _ Υ R γ nv mv hΥ hR hn hm hγ0 hγ1
  classical
  set P := Measure.pi fun _ : Fin nv ⊕ Fin mv => μ with hP
  set f : (Fin nv ⊕ Fin mv → 𝒰) → ℝ :=
    fun z => edVstat (fun i => Υ (z (Sum.inl i))) (fun j => Υ (z (Sum.inr j))) with hf
  obtain ⟨u0⟩ := nonempty_of_isProbabilityMeasure μ
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR u0)
  have hn0 : (0 : ℝ) < nv := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < mv := by exact_mod_cast hm
  set h := 1 / (nv : ℝ) + 1 / (mv : ℝ) with hh
  have hhpos : 0 < h := by positivity
  have hbd : ∀ z, -(4 * R) ≤ f z ∧ f z ≤ 4 * R := fun z =>
    edVstat_bounds hn hm _ _ (fun i => hR _) (fun j => hR _)
  have hfm : Measurable f := by
    simp only [hf, edVstat]
    refine ((Measurable.const_mul ?_ _).sub (Measurable.const_mul ?_ _)).sub (Measurable.const_mul ?_ _) <;>
      exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => measurable_pairNorm hΥ _ _
  set S := {s : ℝ | P {ω | s < f ω} ≤ ENNReal.ofReal γ} with hS
  have hbdd : BddBelow S := by
    refine ⟨-(4 * R), fun s hs => ?_⟩
    by_contra hlt
    push_neg at hlt
    have huniv : {ω | s < f ω} = univ := eq_univ_of_forall fun ω => hlt.trans_le (hbd ω).1
    rw [hS, mem_setOf_eq, huniv, measure_univ, ← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff hγ0.le] at hs
    linarith
  suffices hmem : parsBound R γ nv mv ∈ S from csInf_le hbdd hmem
  rcases hR0.eq_or_lt with hR00 | hRpos
  · -- `R = 0`: the statistic vanishes
    subst hR00
    have hf0 : ∀ z, f z = 0 := fun z => by
      have := hbd z; simp at this; linarith [this.1, this.2]
    have hpb : parsBound 0 γ nv mv = 0 := by simp [parsBound]
    rw [hS, mem_setOf_eq, hpb]
    simp [hf0]
  -- `R > 0`: McDiarmid
  set c : Fin nv ⊕ Fin mv → ℝ := Sum.elim (fun _ => 8 * R / nv) (fun _ => 8 * R / mv) with hc
  have hdiff : ∀ (k : Fin nv ⊕ Fin mv) (x x' : Fin nv ⊕ Fin mv → 𝒰), (∀ l, l ≠ k → x l = x' l) →
      |f x - f x'| ≤ c k := by
    intro k x x' hxx'
    have hb := edVstat_sub_le hn hm (fun i => Υ (x (Sum.inl i))) (fun i => Υ (x' (Sum.inl i)))
      (fun j => Υ (x (Sum.inr j))) (fun j => Υ (x' (Sum.inr j)))
    have hd2 : ∀ l, ‖Υ (x l) - Υ (x' l)‖ ≤ 2 * R := fun l => (norm_sub_le _ _).trans (by linarith [hR (x l), hR (x' l)])
    have hz : ∀ l, l ≠ k → ‖Υ (x l) - Υ (x' l)‖ = 0 := fun l hl => by rw [hxx' l hl, sub_self, norm_zero]
    refine hb.trans ?_
    rcases k with i0 | j0
    · have hA : ∑ i, ‖Υ (x (Sum.inl i)) - Υ (x' (Sum.inl i))‖ ≤ 2 * R := by
        rw [Finset.sum_eq_single i0 (fun i _ hi => hz _ (by simpa using hi)) (by simp)]
        exact hd2 _
      have hB : ∑ j, ‖Υ (x (Sum.inr j)) - Υ (x' (Sum.inr j))‖ = 0 :=
        Finset.sum_eq_zero fun j _ => hz _ (by simp)
      rw [hB, mul_zero, add_zero]
      simp only [hc, Sum.elim_inl]
      calc 4 / (nv : ℝ) * _ ≤ 4 / (nv : ℝ) * (2 * R) := by gcongr
        _ = 8 * R / nv := by ring
    · have hB : ∑ j, ‖Υ (x (Sum.inr j)) - Υ (x' (Sum.inr j))‖ ≤ 2 * R := by
        rw [Finset.sum_eq_single j0 (fun j _ hj => hz _ (by simpa using hj)) (by simp)]
        exact hd2 _
      have hA : ∑ i, ‖Υ (x (Sum.inl i)) - Υ (x' (Sum.inl i))‖ = 0 :=
        Finset.sum_eq_zero fun i _ => hz _ (by simp)
      rw [hA, mul_zero, zero_add]
      simp only [hc, Sum.elim_inr]
      calc 4 / (mv : ℝ) * _ ≤ 4 / (mv : ℝ) * (2 * R) := by gcongr
        _ = 8 * R / mv := by ring
  have hsg := TauCeti.Probability.hasSubgaussianMGF_of_bounded_differences μ f hfm c hdiff
  have hc0 : ∀ k, 0 ≤ c k := fun k => by rcases k with i | j <;> simp [hc] <;> positivity
  have hv : ((∑ k, (c k).toNNReal ^ 2 / 4 : ℝ≥0) : ℝ) = 16 * R ^ 2 * h := by
    push_cast [Real.coe_toNNReal _ (hc0 _)]
    rw [Fintype.sum_sum_type]
    simp only [hc, Sum.elim_inl, Sum.elim_inr, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hh]; field_simp; ring
  set t := R * √(32 * h * Real.log (2 / γ)) with ht
  have hL : 0 < Real.log (2 / γ) := Real.log_pos (by rw [lt_div_iff₀ hγ0]; linarith)
  have ht0 : 0 ≤ t := by positivity
  have htail := hsg.measure_ge_le ht0
  rw [hv] at htail
  have hexp : -t ^ 2 / (2 * (16 * R ^ 2 * h)) = -Real.log (2 / γ) := by
    rw [ht, mul_pow, Real.sq_sqrt (by positivity)]
    field_simp; ring
  rw [hexp, Real.exp_neg, Real.exp_log (by positivity), inv_div] at htail
  have hEf := integral_edVstat μ hn hm hΥ hR
  have hsub : {ω | parsBound R γ nv mv < f ω} ⊆ {ω | t ≤ f ω - ∫ y, f y ∂P} := by
    intro ω hω
    simp only [mem_setOf_eq, parsBound] at hω ⊢
    rw [← hh] at hω
    have : ∫ y, f y ∂P ≤ 2 * R * h := hEf
    linarith
  rw [hS, mem_setOf_eq]
  calc P {ω | parsBound R γ nv mv < f ω} ≤ P {ω | t ≤ f ω - ∫ y, f y ∂P} := measure_mono hsub
    _ = ENNReal.ofReal (P.real {ω | t ≤ f ω - ∫ y, f y ∂P}) := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (γ / 2) := ENNReal.ofReal_le_ofReal htail
    _ ≤ ENNReal.ofReal γ := ENNReal.ofReal_le_ofReal (by linarith)

example : Claims.parsimony_tolerance := parsimony_tolerance
example : Claims.parsimony_tolerance_tendsto := parsimony_tolerance_tendsto

end StatFormal.Wave24a
