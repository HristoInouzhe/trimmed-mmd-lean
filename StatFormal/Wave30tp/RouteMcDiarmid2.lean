import StatFormal.Wave30tp.Statements
import StatFormal.Lib.Concentration.HilbertMeanTail
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Route (library-grade): McDiarmid on a product of two product measures, and the Hilbert two-sample mean

Untrusted proof material.

* `map_splitMap`: `(P ⊗ Q)^{⊗(Fin n ⊕ Fin m)}` pushed forward by `z ↦ ((z (inl i)).1)_i, ((z (inr j)).2)_j)` is
  `P^{⊗n} ⊗ Q^{⊗m}`. This turns two independent samples from different laws into one i.i.d. sample (from `P ⊗ Q`), to
  which Tau Ceti's McDiarmid (identical coordinates, coordinate-dependent constants) applies.
* `mcdiarmid_two_sample`: **two-sample McDiarmid** — if changing one `X_i` moves `f` by at most `cX` and one `Y_j` by at
  most `cY`, then `P(f − E f ≥ ε) ≤ exp(−2ε²/(n cX² + m cY²))` under `P^{⊗n} ⊗ Q^{⊗m}`.
* `twoDev_tail`: for mean-zero bounded `ψ₁` (under `P`), `ψ₂` (under `Q`) with `E‖ψ₁‖² ≤ σ₁`, `E‖ψ₂‖² ≤ σ₂` and
  oscillations `c₁`, `c₂`: `P(‖n⁻¹Σψ₁(X_i) − m⁻¹Σψ₂(Y_j)‖ > √(σ₁/n + σ₂/m) + √((c₁²/n + c₂²/m) L/2)) ≤ e^{−L}`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal

namespace StatFormal.Wave30tp

section McD

variable {β : Type*} [MeasurableSpace β]

/-- One `P ⊗ Q` draw per index of `Fin n ⊕ Fin m`, keeping the first coordinate on the left block and the second on
the right block. -/
def splitMap (n m : ℕ) (z : Fin n ⊕ Fin m → β × β) : (Fin n → β) × (Fin m → β) :=
  (fun i => (z (Sum.inl i)).1, fun j => (z (Sum.inr j)).2)

theorem measurable_splitMap (n m : ℕ) : Measurable (splitMap (β := β) n m) := by
  refine Measurable.prodMk ?_ ?_ <;> refine measurable_pi_iff.2 (fun i => ?_)
  · exact measurable_fst.comp (measurable_pi_apply _)
  · exact measurable_snd.comp (measurable_pi_apply _)

theorem map_splitMap (P Q : Measure β) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (n m : ℕ) :
    (Measure.pi fun _ : Fin n ⊕ Fin m => P.prod Q).map (splitMap n m) = sampleLaw P Q n m := by
  have e := measurePreserving_sumPiEquivProdPi (fun _ : Fin n ⊕ Fin m => P.prod Q)
  have hf : Measurable fun (x : Fin n → β × β) (i : Fin n) => (x i).1 :=
    measurable_pi_iff.2 fun i => measurable_fst.comp (measurable_pi_apply i)
  have hg : Measurable fun (y : Fin m → β × β) (j : Fin m) => (y j).2 :=
    measurable_pi_iff.2 fun j => measurable_snd.comp (measurable_pi_apply j)
  have hfac : splitMap (β := β) n m =
      Prod.map (fun (x : Fin n → β × β) (i : Fin n) => (x i).1)
        (fun (y : Fin m → β × β) (j : Fin m) => (y j).2) ∘
        (MeasurableEquiv.sumPiEquivProdPi fun _ : Fin n ⊕ Fin m => β × β) := by
    funext z; rfl
  rw [hfac, ← Measure.map_map (hf.prodMap hg) e.measurable, e.map_eq,
    ← Measure.map_prod_map _ _ hf hg]
  rw [Measure.pi_map_pi (fun _ => measurable_fst.aemeasurable),
    Measure.pi_map_pi (fun _ => measurable_snd.aemeasurable)]
  simp [sampleLaw]

instance (P Q : Measure β) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (n m : ℕ) :
    IsProbabilityMeasure (sampleLaw P Q n m) := by
  unfold sampleLaw; infer_instance

/-- **Two-sample McDiarmid.** Under `P^{⊗n} ⊗ Q^{⊗m}`, a measurable `f` with bounded differences `cX` in each `X_i`
and `cY` in each `Y_j` satisfies `P(f − E f ≥ ε) ≤ exp(−ε²/(2 (n cX² + m cY²)/4))`. -/
theorem mcdiarmid_two_sample (P Q : Measure β) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {n m : ℕ}
    (f : (Fin n → β) × (Fin m → β) → ℝ) (hf : Measurable f) {cX cY : ℝ} (hcX : 0 ≤ cX) (hcY : 0 ≤ cY)
    (hX : ∀ (x : Fin n → β) (y : Fin m → β) (i : Fin n) (b : β),
      |f (Function.update x i b, y) - f (x, y)| ≤ cX)
    (hY : ∀ (x : Fin n → β) (y : Fin m → β) (j : Fin m) (b : β),
      |f (x, Function.update y j b) - f (x, y)| ≤ cY)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (sampleLaw P Q n m).real {z | ε ≤ f z - ∫ w, f w ∂(sampleLaw P Q n m)} ≤
      Real.exp (-ε ^ 2 / (2 * ((n * cX ^ 2 + m * cY ^ 2) / 4))) := by
  set ν : Measure (β × β) := P.prod Q
  set μ := Measure.pi fun _ : Fin n ⊕ Fin m => ν with hμ
  set g : (Fin n ⊕ Fin m → β × β) → ℝ := fun z => f (splitMap n m z) with hgdef
  have hgm : Measurable g := hf.comp (measurable_splitMap n m)
  set c : Fin n ⊕ Fin m → ℝ := Sum.elim (fun _ => cX) (fun _ => cY) with hc
  have hbd : ∀ (k : Fin n ⊕ Fin m) (x x' : Fin n ⊕ Fin m → β × β),
      (∀ l, l ≠ k → x l = x' l) → |g x - g x'| ≤ c k := by
    intro k x x' hxx
    cases k with
    | inl i =>
      have hs : splitMap n m x' = (Function.update (splitMap n m x).1 i (x' (Sum.inl i)).1,
          (splitMap n m x).2) := by
        refine Prod.ext ?_ ?_
        · funext i'
          simp only [splitMap, Function.update_apply]
          split_ifs with h
          · subst h; rfl
          · exact congrArg Prod.fst (hxx (Sum.inl i') (by simpa using h)).symm
        · funext j
          simp only [splitMap]
          exact congrArg Prod.snd (hxx (Sum.inr j) (by simp)).symm
      simp only [hgdef, hs, hc, Sum.elim_inl]
      rw [abs_sub_comm]
      exact hX _ _ i _
    | inr j =>
      have hs : splitMap n m x' = ((splitMap n m x).1,
          Function.update (splitMap n m x).2 j (x' (Sum.inr j)).2) := by
        refine Prod.ext ?_ ?_
        · funext i
          simp only [splitMap]
          exact congrArg Prod.fst (hxx (Sum.inl i) (by simp)).symm
        · funext j'
          simp only [splitMap, Function.update_apply]
          split_ifs with h
          · subst h; rfl
          · exact congrArg Prod.snd (hxx (Sum.inr j') (by simpa using h)).symm
      simp only [hgdef, hs, hc, Sum.elim_inr]
      rw [abs_sub_comm]
      exact hY _ _ j _
  have hsg := TauCeti.Probability.hasSubgaussianMGF_of_bounded_differences ν g hgm c hbd
  have htail := hsg.measure_ge_le hε
  have hmap := map_splitMap P Q n m
  set I := ∫ w, f w ∂(sampleLaw P Q n m) with hI
  have hint : ∫ z, g z ∂μ = I := by
    rw [hI, ← hmap, integral_map (measurable_splitMap n m).aemeasurable hf.aestronglyMeasurable]
  have hset : MeasurableSet {z | ε ≤ f z - I} :=
    measurableSet_le measurable_const (hf.sub measurable_const)
  have hreal : (sampleLaw P Q n m).real {z | ε ≤ f z - I} =
      μ.real {z | ε ≤ g z - ∫ z', g z' ∂μ} := by
    have h1 : (sampleLaw P Q n m).real {z | ε ≤ f z - I} =
        μ.real (splitMap n m ⁻¹' {z | ε ≤ f z - I}) := by
      rw [← hmap, measureReal_def, Measure.map_apply (measurable_splitMap n m) hset, measureReal_def]
    rw [h1, hint]; rfl
  have hproxy : (((∑ k, (c k).toNNReal ^ 2 / 4 : ℝ≥0)) : ℝ) = (n * cX ^ 2 + m * cY ^ 2) / 4 := by
    push_cast
    rw [Fintype.sum_sum_type]
    simp only [hc, Sum.elim_inl, Sum.elim_inr, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Real.coe_toNNReal _ hcX, Real.coe_toNNReal _ hcY]
    ring
  rw [hreal]
  rw [hproxy] at htail
  exact htail

end McD

section Hilbert

variable {β : Type*} [MeasurableSpace β]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The two-sample deviation `n⁻¹Σψ₁(X_i) − m⁻¹Σψ₂(Y_j)`. -/
def twoDev (ψ1 ψ2 : β → H) {n m : ℕ} (z : (Fin n → β) × (Fin m → β)) : H :=
  (n : ℝ)⁻¹ • ∑ i, ψ1 (z.1 i) - (m : ℝ)⁻¹ • ∑ j, ψ2 (z.2 j)

/-- One-sample average `n⁻¹Σψ(X_i)`. -/
def avg (ψ : β → H) {n : ℕ} (x : Fin n → β) : H := (n : ℝ)⁻¹ • ∑ i, ψ (x i)

theorem stronglyMeasurable_avg {ψ : β → H} (hψ : StronglyMeasurable ψ) (n : ℕ) :
    StronglyMeasurable (avg ψ (n := n)) :=
  StronglyMeasurable.const_smul
    (Finset.stronglyMeasurable_fun_sum _ fun i _ => hψ.comp_measurable (measurable_pi_apply i)) _

theorem norm_avg_le {ψ : β → H} {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ x, ‖ψ x‖ ≤ K) {n : ℕ} (x : Fin n → β) :
    ‖avg ψ x‖ ≤ K := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simpa [avg] using hK0
  · have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 hn
    rw [avg, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hnpos]
    calc (n : ℝ)⁻¹ * ‖∑ i, ψ (x i)‖ ≤ (n : ℝ)⁻¹ * ∑ _i : Fin n, K := by
          gcongr; exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hK _)
      _ = K := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp

theorem integral_avg_eq_zero (P : Measure β) [IsProbabilityMeasure P] {ψ : β → H}
    (hψ : StronglyMeasurable ψ) {K : ℝ} (hK : ∀ x, ‖ψ x‖ ≤ K) (h0 : ∫ x, ψ x ∂P = 0) (n : ℕ) :
    ∫ x, avg ψ x ∂(Measure.pi fun _ : Fin n => P) = 0 := by
  have hint : ∀ i : Fin n, Integrable (fun x : Fin n → β => ψ (x i)) (Measure.pi fun _ : Fin n => P) :=
    fun i => Integrable.of_bound (hψ.comp_measurable (measurable_pi_apply i)).aestronglyMeasurable K
      (ae_of_all _ fun x => hK _)
  simp only [avg]
  rw [integral_smul, integral_finsetSum _ fun i _ => hint i]
  simp_rw [StatFormal.Concentration.integral_comp_eval _ hψ.aestronglyMeasurable, h0]
  simp

theorem integral_norm_avg_sq (P : Measure β) [IsProbabilityMeasure P] {ψ : β → H}
    (hψ : StronglyMeasurable ψ) {K : ℝ} (hK : ∀ x, ‖ψ x‖ ≤ K) (h0 : ∫ x, ψ x ∂P = 0) {n : ℕ}
    (hn : n ≠ 0) :
    ∫ x, ‖avg ψ x‖ ^ 2 ∂(Measure.pi fun _ : Fin n => P) = (∫ y, ‖ψ y‖ ^ 2 ∂P) / n := by
  have h := StatFormal.Concentration.integral_norm_meanDev_sq (P := P) hn hψ hK
  rw [h0, norm_zero] at h
  have heq : ∀ x : Fin n → β, StatFormal.Concentration.meanDev P ψ n x = avg ψ x := by
    intro x; simp [StatFormal.Concentration.meanDev, avg, h0]
  simp_rw [heq] at h
  rw [h]; ring

theorem twoDev_eq (ψ1 ψ2 : β → H) {n m : ℕ} (z : (Fin n → β) × (Fin m → β)) :
    twoDev ψ1 ψ2 z = avg ψ1 z.1 - avg ψ2 z.2 := rfl

theorem stronglyMeasurable_twoDev {ψ1 ψ2 : β → H} (h1 : StronglyMeasurable ψ1) (h2 : StronglyMeasurable ψ2)
    (n m : ℕ) : StronglyMeasurable (twoDev ψ1 ψ2 (n := n) (m := m)) :=
  ((stronglyMeasurable_avg h1 n).comp_measurable measurable_fst).sub
    ((stronglyMeasurable_avg h2 m).comp_measurable measurable_snd)

/-- Second moment of the two-sample deviation: `E‖A − B‖² = E‖ψ₁‖²/n + E‖ψ₂‖²/m` (cross term `0` by independence). -/
theorem integral_norm_twoDev_sq (P Q : Measure β) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {ψ1 ψ2 : β → H} (h1 : StronglyMeasurable ψ1) (h2 : StronglyMeasurable ψ2) {K : ℝ}
    (hK1 : ∀ x, ‖ψ1 x‖ ≤ K) (hK2 : ∀ x, ‖ψ2 x‖ ≤ K) (h01 : ∫ x, ψ1 x ∂P = 0) (h02 : ∫ x, ψ2 x ∂Q = 0)
    {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    ∫ z, ‖twoDev ψ1 ψ2 z‖ ^ 2 ∂(sampleLaw P Q n m) =
      (∫ y, ‖ψ1 y‖ ^ 2 ∂P) / n + (∫ y, ‖ψ2 y‖ ^ 2 ∂Q) / m := by
  set Pn := Measure.pi fun _ : Fin n => P
  set Qm := Measure.pi fun _ : Fin m => Q
  have hA := stronglyMeasurable_avg h1 n
  have hB := stronglyMeasurable_avg h2 m
  have hK0 : 0 ≤ K := by
    obtain ⟨x⟩ := nonempty_of_isProbabilityMeasure P
    exact (norm_nonneg _).trans (hK1 x)
  have hAb : ∀ x : Fin n → β, ‖avg ψ1 x‖ ≤ K := fun x => norm_avg_le hK0 hK1 x
  have hBb : ∀ y : Fin m → β, ‖avg ψ2 y‖ ≤ K := fun y => norm_avg_le hK0 hK2 y
  have hpt : ∀ z : (Fin n → β) × (Fin m → β), ‖twoDev ψ1 ψ2 z‖ ^ 2 =
      ‖avg ψ1 z.1‖ ^ 2 - 2 * inner ℝ (avg ψ1 z.1) (avg ψ2 z.2) + ‖avg ψ2 z.2‖ ^ 2 := fun z => by
    rw [twoDev_eq, norm_sub_sq_real]
  simp_rw [hpt]
  have iA : Integrable (fun z : (Fin n → β) × (Fin m → β) => ‖avg ψ1 z.1‖ ^ 2) (sampleLaw P Q n m) :=
    Integrable.of_bound ((hA.comp_measurable measurable_fst).norm.pow 2).aestronglyMeasurable (K ^ 2)
      (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hAb _) 2)
  have iB : Integrable (fun z : (Fin n → β) × (Fin m → β) => ‖avg ψ2 z.2‖ ^ 2) (sampleLaw P Q n m) :=
    Integrable.of_bound ((hB.comp_measurable measurable_snd).norm.pow 2).aestronglyMeasurable (K ^ 2)
      (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hBb _) 2)
  have hinner_m : StronglyMeasurable fun z : (Fin n → β) × (Fin m → β) =>
      inner ℝ (avg ψ1 z.1) (avg ψ2 z.2) :=
    (hA.comp_measurable measurable_fst).inner (hB.comp_measurable measurable_snd)
  have iC : Integrable (fun z : (Fin n → β) × (Fin m → β) => 2 * inner ℝ (avg ψ1 z.1) (avg ψ2 z.2))
      (sampleLaw P Q n m) :=
    (Integrable.of_bound hinner_m.aestronglyMeasurable (K * K) (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs]
      refine (abs_real_inner_le_norm _ _).trans ?_
      exact mul_le_mul (hAb _) (hBb _) (norm_nonneg _) ((norm_nonneg _).trans (hAb z.1)))).const_mul 2
  have iAC : Integrable (fun z : (Fin n → β) × (Fin m → β) =>
      ‖avg ψ1 z.1‖ ^ 2 - 2 * inner ℝ (avg ψ1 z.1) (avg ψ2 z.2)) (sampleLaw P Q n m) := iA.sub iC
  rw [integral_add iAC iB, integral_sub iA iC]
  have eA : ∫ z, ‖avg ψ1 z.1‖ ^ 2 ∂(sampleLaw P Q n m) = (∫ y, ‖ψ1 y‖ ^ 2 ∂P) / n := by
    rw [sampleLaw, integral_fun_fst (fun x : Fin n → β => ‖avg ψ1 x‖ ^ 2)]
    simp only [probReal_univ, one_smul]
    exact integral_norm_avg_sq P h1 hK1 h01 hn
  have eB : ∫ z, ‖avg ψ2 z.2‖ ^ 2 ∂(sampleLaw P Q n m) = (∫ y, ‖ψ2 y‖ ^ 2 ∂Q) / m := by
    rw [sampleLaw, integral_fun_snd (fun y : Fin m → β => ‖avg ψ2 y‖ ^ 2)]
    simp only [probReal_univ, one_smul]
    exact integral_norm_avg_sq Q h2 hK2 h02 hm
  have eC : ∫ z, 2 * inner ℝ (avg ψ1 z.1) (avg ψ2 z.2) ∂(sampleLaw P Q n m) = 0 := by
    rw [integral_const_mul]
    have hint : Integrable (fun z : (Fin n → β) × (Fin m → β) => inner ℝ (avg ψ1 z.1) (avg ψ2 z.2))
        (Pn.prod Qm) :=
      Integrable.of_bound hinner_m.aestronglyMeasurable (K * K) (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs]
        refine (abs_real_inner_le_norm _ _).trans ?_
        exact mul_le_mul (hAb _) (hBb _) (norm_nonneg _) ((norm_nonneg _).trans (hAb z.1)))
    have hBint : Integrable (avg ψ2 (n := m)) Qm :=
      Integrable.of_bound hB.aestronglyMeasurable K (ae_of_all _ hBb)
    rw [sampleLaw, integral_prod _ hint]
    have : ∀ x : Fin n → β, ∫ y, inner ℝ (avg ψ1 x) (avg ψ2 y) ∂Qm = 0 := fun x => by
      rw [integral_inner hBint, integral_avg_eq_zero Q h2 hK2 h02 m, inner_zero_right]
    simp_rw [this]
    simp
  rw [eA, eB, eC]
  ring

/-- **Hilbert two-sample tail.** For mean-zero bounded strongly measurable `ψ₁` (under `P`), `ψ₂` (under `Q`) with
`E‖ψ₁‖² ≤ σ₁`, `E‖ψ₂‖² ≤ σ₂` and `‖ψ_k(x) − ψ_k(x')‖ ≤ c_k`, and `L ≥ 0`:
`P(‖A − B‖ > √(σ₁/n + σ₂/m) + √((c₁²/n + c₂²/m) L/2)) ≤ e^{−L}`. -/
theorem twoDev_tail (P Q : Measure β) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {ψ1 ψ2 : β → H} (h1 : StronglyMeasurable ψ1) (h2 : StronglyMeasurable ψ2) {K : ℝ}
    (hK1 : ∀ x, ‖ψ1 x‖ ≤ K) (hK2 : ∀ x, ‖ψ2 x‖ ≤ K) (h01 : ∫ x, ψ1 x ∂P = 0) (h02 : ∫ x, ψ2 x ∂Q = 0)
    {σ1 σ2 : ℝ} (hσ1 : ∫ y, ‖ψ1 y‖ ^ 2 ∂P ≤ σ1) (hσ2 : ∫ y, ‖ψ2 y‖ ^ 2 ∂Q ≤ σ2)
    {c1 c2 : ℝ} (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hd1 : ∀ x x', ‖ψ1 x - ψ1 x'‖ ≤ c1)
    (hd2 : ∀ x x', ‖ψ2 x - ψ2 x'‖ ≤ c2) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) {L : ℝ} (hL : 0 ≤ L) :
    sampleLaw P Q n m {z | √(σ1 / n + σ2 / m) + √((c1 ^ 2 / n + c2 ^ 2 / m) * L / 2) <
      ‖twoDev ψ1 ψ2 z‖} ≤ ENNReal.ofReal (Real.exp (-L)) := by
  have hn0 : n ≠ 0 := by omega
  have hm0 : m ≠ 0 := by omega
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.2 (by omega)
  set μ := sampleLaw P Q n m
  set F : (Fin n → β) × (Fin m → β) → ℝ := fun z => ‖twoDev ψ1 ψ2 z‖ with hF
  have hFsm : StronglyMeasurable F := (stronglyMeasurable_twoDev h1 h2 n m).norm
  have hK0 : 0 ≤ K := by
    obtain ⟨x⟩ := nonempty_of_isProbabilityMeasure P
    exact (norm_nonneg _).trans (hK1 x)
  have hFb : ∀ z, ‖F z‖ ≤ 2 * K := fun z => by
    rw [hF, Real.norm_eq_abs, abs_norm, twoDev_eq]
    exact (norm_sub_le _ _).trans (by linarith [norm_avg_le hK0 hK1 z.1, norm_avg_le hK0 hK2 z.2])
  -- the mean bound
  have hsq : ∫ z, F z ^ 2 ∂μ ≤ σ1 / n + σ2 / m := by
    have := integral_norm_twoDev_sq P Q h1 h2 hK1 hK2 h01 h02 hn0 hm0
    change ∫ z, ‖twoDev ψ1 ψ2 z‖ ^ 2 ∂μ ≤ _
    rw [this]
    gcongr
  have hmean : ∫ z, F z ∂μ ≤ √(σ1 / n + σ2 / m) := by
    have hmem : MemLp F 2 μ := MemLp.of_bound hFsm.aestronglyMeasurable (2 * K) (ae_of_all _ hFb)
    have hvar := variance_eq_sub hmem
    have hv0 := variance_nonneg F μ
    have hE2 : (∫ z, F z ∂μ) ^ 2 ≤ σ1 / n + σ2 / m := by
      have : μ[F ^ 2] = ∫ z, F z ^ 2 ∂μ := by simp [Pi.pow_apply]
      linarith
    exact (le_abs_self _).trans (Real.abs_le_sqrt hE2)
  set V := c1 ^ 2 / n + c2 ^ 2 / m with hV
  rcases (show 0 ≤ V by positivity).eq_or_lt with hV0 | hVpos
  · -- no oscillation: `ψ₁ = ψ₂ = 0`, the deviation vanishes
    have hc1z : c1 = 0 := by
      have : c1 ^ 2 / n = 0 := by
        have h1' : 0 ≤ c1 ^ 2 / n := by positivity
        have h2' : 0 ≤ c2 ^ 2 / m := by positivity
        linarith
      have := (div_eq_zero_iff.1 this).resolve_right hnpos.ne'
      exact pow_eq_zero_iff (by norm_num) |>.1 this
    have hc2z : c2 = 0 := by
      have : c2 ^ 2 / m = 0 := by
        have h1' : 0 ≤ c1 ^ 2 / n := by positivity
        have h2' : 0 ≤ c2 ^ 2 / m := by positivity
        linarith
      have := (div_eq_zero_iff.1 this).resolve_right hmpos.ne'
      exact pow_eq_zero_iff (by norm_num) |>.1 this
    have hconst : ∀ {ψ : β → H} {ν : Measure β} [IsProbabilityMeasure ν], (∀ x x', ‖ψ x - ψ x'‖ ≤ 0) →
        ∫ x, ψ x ∂ν = 0 → ∀ x, ψ x = 0 := by
      intro ψ ν _ hd h0 x
      have hc : ∀ y, ψ y = ψ x := fun y => sub_eq_zero.1 (norm_le_zero_iff.1 (hd y x))
      have : ∫ y, ψ y ∂ν = ψ x := by simp_rw [hc]; simp
      rw [← this, h0]
    have z1 := hconst (hc1z ▸ hd1) h01
    have z2 := hconst (hc2z ▸ hd2) h02
    have hempty : {z : (Fin n → β) × (Fin m → β) |
        √(σ1 / n + σ2 / m) + √(V * L / 2) < ‖twoDev ψ1 ψ2 z‖} = ∅ := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      simp [twoDev, z1, z2]
      positivity
    rw [hempty, measure_empty]; exact zero_le
  · -- McDiarmid
    set ε := √(V * L / 2) with hε
    have hε0 : 0 ≤ ε := Real.sqrt_nonneg _
    have hFm : Measurable F := hFsm.measurable
    have hX : ∀ (x : Fin n → β) (y : Fin m → β) (i : Fin n) (b : β),
        |F (Function.update x i b, y) - F (x, y)| ≤ c1 / n := by
      intro x y i b
      refine (abs_norm_sub_norm_le _ _).trans ?_
      have : twoDev ψ1 ψ2 (Function.update x i b, y) - twoDev ψ1 ψ2 (x, y) =
          (n : ℝ)⁻¹ • (ψ1 b - ψ1 (x i)) := by
        simp only [twoDev]
        rw [sub_sub_sub_cancel_right, ← smul_sub, ← Finset.sum_sub_distrib]
        congr 1
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hj; simp [Function.update_of_ne hj]
        · simp
      rw [this, norm_smul, Real.norm_eq_abs, abs_inv, Nat.abs_cast, div_eq_inv_mul]
      gcongr
      exact hd1 _ _
    have hY : ∀ (x : Fin n → β) (y : Fin m → β) (j : Fin m) (b : β),
        |F (x, Function.update y j b) - F (x, y)| ≤ c2 / m := by
      intro x y j b
      refine (abs_norm_sub_norm_le _ _).trans ?_
      have : twoDev ψ1 ψ2 (x, Function.update y j b) - twoDev ψ1 ψ2 (x, y) =
          -((m : ℝ)⁻¹ • (ψ2 b - ψ2 (y j))) := by
        simp only [twoDev]
        rw [sub_sub_sub_cancel_left, ← smul_sub, ← Finset.sum_sub_distrib, ← smul_neg, neg_sub]
        congr 1
        rw [Finset.sum_eq_single j]
        · simp
        · intro j' _ hj; simp [Function.update_of_ne hj]
        · simp
      rw [this, norm_neg, norm_smul, Real.norm_eq_abs, abs_inv, Nat.abs_cast, div_eq_inv_mul]
      gcongr
      exact hd2 _ _
    have htail := mcdiarmid_two_sample P Q F hFm (div_nonneg hc1 hnpos.le) (div_nonneg hc2 hmpos.le)
      hX hY hε0
    have hprox : (n : ℝ) * (c1 / n) ^ 2 + m * (c2 / m) ^ 2 = V := by
      rw [hV]; field_simp
    rw [hprox] at htail
    have hexp : -ε ^ 2 / (2 * (V / 4)) = -L := by
      rw [hε, Real.sq_sqrt (by positivity)]
      field_simp
      ring
    rw [hexp] at htail
    have hsub : {z | √(σ1 / n + σ2 / m) + √((c1 ^ 2 / n + c2 ^ 2 / m) * L / 2) < ‖twoDev ψ1 ψ2 z‖} ⊆
        {z | ε ≤ F z - ∫ w, F w ∂μ} := by
      intro z hz
      simp only [Set.mem_setOf_eq] at hz ⊢
      change _ < F z at hz
      rw [← hV] at hz
      linarith
    calc μ {z | √(σ1 / n + σ2 / m) + √((c1 ^ 2 / n + c2 ^ 2 / m) * L / 2) < ‖twoDev ψ1 ψ2 z‖}
        ≤ μ {z | ε ≤ F z - ∫ w, F w ∂μ} := measure_mono hsub
      _ = ENNReal.ofReal (μ.real {z | ε ≤ F z - ∫ w, F w ∂μ}) := (ofReal_measureReal).symm
      _ ≤ ENNReal.ofReal (Real.exp (-L)) := ENNReal.ofReal_le_ofReal htail

end Hilbert

end StatFormal.Wave30tp
