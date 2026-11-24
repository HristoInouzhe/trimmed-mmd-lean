import StatFormal.Archive.TrimmedMMD.ZeroSet.Statements
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Attainment of the infimum `D_α` (helper for `zeroeq`)

`lem:attainment` of the paper, in the form needed for `eq:zeroeq` (⇒): if `D_α(P,Q) = 0` then
there are trimmings of `P` and `Q` with the *same* embedding.

Route (Hilbert space, no weak topology):
* `nonempty_iInter_of_closed_convex`: in a real Hilbert space a decreasing sequence of nonempty
  closed convex sets with a common norm bound has nonempty intersection. Proof: the minimal-norm
  points `x_n` (`exists_norm_eq_iInf_of_complete_convex`) satisfy `‖x_m − x_n‖² ≤ ‖x_m‖² − ‖x_n‖²`
  for `m ≥ n` (variational inequality), so they form a Cauchy sequence; its limit lies in every set.
* trimming densities of `P` are encoded as the set `Kset P α ⊆ L²(P)` cut out by the continuous
  linear constraints `0 ≤ ⟪1_A, h⟫ ≤ c·P(A)`, `⟪1, h⟫ = 1` (closed and convex), and the embedding
  `h ↦ ∫ h φ dP` is a bounded linear map `L²(P) → H`;
* apply the lemma in `WithLp 2 (L²(P) × L²(P))` to
  `F_n = {(h,k) ∈ Kset P α × Kset Q α : ‖emb h − emb k‖ ≤ 1/(n+1)}` (nonempty since `D_α = 0`).
Untrusted helper file.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace

namespace StatFormal.TrimmedMMD.ZeroSet

open StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional

/-! ### Nested closed convex sets in a Hilbert space -/

theorem nonempty_iInter_of_closed_convex {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (F : ℕ → Set E) (hne : ∀ n, (F n).Nonempty)
    (hcl : ∀ n, IsClosed (F n)) (hcv : ∀ n, Convex ℝ (F n)) (hanti : Antitone F) (M : ℝ)
    (hb : ∀ n, ∀ x ∈ F n, ‖x‖ ^ 2 ≤ M) : (⋂ n, F n).Nonempty := by
  have hmin : ∀ n, ∃ v ∈ F n, ∀ w ∈ F n, ‖v‖ ^ 2 + ‖w - v‖ ^ 2 ≤ ‖w‖ ^ 2 := by
    intro n
    obtain ⟨v, hv, hvmin⟩ :=
      exists_norm_eq_iInf_of_complete_convex (hne n) (hcl n).isComplete (hcv n) 0
    refine ⟨v, hv, fun w hw => ?_⟩
    have hin := (norm_eq_iInf_iff_real_inner_le_zero (hcv n) hv).1 hvmin w hw
    have hexp : ‖w‖ ^ 2 = ‖v‖ ^ 2 + 2 * ⟪v, w - v⟫_ℝ + ‖w - v‖ ^ 2 := by
      have : w = v + (w - v) := by abel
      conv_lhs => rw [this]
      rw [norm_add_sq_real]
    rw [zero_sub, inner_neg_left] at hin
    linarith
  choose x hxF hxmin using hmin
  set a : ℕ → ℝ := fun n => ‖x n‖ ^ 2 with ha
  have hmono : Monotone a := by
    intro n m hnm
    have := hxmin n (x m) (hanti hnm (hxF m))
    have : 0 ≤ ‖x m - x n‖ ^ 2 := sq_nonneg _
    simp only [ha]; linarith
  have hbdd : BddAbove (range a) := ⟨M, by rintro _ ⟨n, rfl⟩; exact hb n _ (hxF n)⟩
  have hlim : Tendsto a atTop (𝓝 (⨆ n, a n)) := tendsto_atTop_ciSup hmono hbdd
  have hle : ∀ n, a n ≤ ⨆ n, a n := fun n => le_ciSup hbdd n
  have hcauchy : CauchySeq x := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hlim) (ε ^ 2) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    have h1 := hxmin N (x n) (hanti hn (hxF n))
    have h2 := hN N le_rfl
    rw [Real.dist_eq, abs_lt] at h2
    have h3 := hle n
    rw [dist_eq_norm]
    have h4 : ‖x n - x N‖ ^ 2 < ε ^ 2 := by simp only [ha] at h2 h3; linarith
    by_contra hcon
    push Not at hcon
    nlinarith [norm_nonneg (x n - x N)]
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hcauchy
  exact ⟨z, mem_iInter.2 fun n =>
    (hcl n).mem_of_tendsto hz (eventually_atTop.2 ⟨n, fun m hm => hanti hm (hxF m)⟩)⟩

/-! ### Trimming densities as a closed convex subset of `L²(P)` -/

section L2

variable {𝒳 : Type*} [MeasurableSpace 𝒳] (P : Measure 𝒳) [IsProbabilityMeasure P]

/-- `1_A ∈ L²(P)`. -/
def indL (A : {A : Set 𝒳 // MeasurableSet A}) : Lp ℝ 2 P :=
  indicatorConstLp 2 A.2 (measure_ne_top P A.1) (1 : ℝ)

theorem inner_indL (A : {A : Set 𝒳 // MeasurableSet A}) (h : Lp ℝ 2 P) :
    ⟪indL P A, h⟫_ℝ = ∫ x in A.1, h x ∂P :=
  L2.inner_indicatorConstLp_one A.2 (measure_ne_top P A.1) h

/-- The trimming densities of `P` at level `α`, as elements of `L²(P)`. -/
def Kset (α : ℝ) : Set (Lp ℝ 2 P) :=
  {h | (∀ A : {A : Set 𝒳 // MeasurableSet A},
      0 ≤ ⟪indL P A, h⟫_ℝ ∧ ⟪indL P A, h⟫_ℝ ≤ 1 / (1 - α) * P.real A.1) ∧
    ⟪indL P ⟨univ, MeasurableSet.univ⟩, h⟫_ℝ = 1}

theorem mem_Kset {α : ℝ} {h : Lp ℝ 2 P} :
    h ∈ Kset P α ↔ (∀ A, MeasurableSet A →
      0 ≤ ∫ x in A, h x ∂P ∧ ∫ x in A, h x ∂P ≤ 1 / (1 - α) * P.real A) ∧
      ∫ x, h x ∂P = 1 := by
  simp only [Kset, mem_ofPred_eq, inner_indL, Subtype.forall, setIntegral_univ]

theorem isClosed_Kset (α : ℝ) : IsClosed (Kset P α) := by
  have hc : ∀ A : {A : Set 𝒳 // MeasurableSet A},
      Continuous fun h : Lp ℝ 2 P => ⟪indL P A, h⟫_ℝ := fun A =>
        continuous_const.inner continuous_id
  simp only [Kset, ofPred_and, ofPred_forall]
  exact (isClosed_iInter fun A => (isClosed_le continuous_const (hc A)).inter
    (isClosed_le (hc A) continuous_const)).inter (isClosed_eq (hc _) continuous_const)

theorem convex_Kset (α : ℝ) : Convex ℝ (Kset P α) := by
  intro h₁ hh₁ h₂ hh₂ a b ha hb hab
  simp only [Kset, mem_ofPred_eq, inner_add_right, inner_smul_right] at hh₁ hh₂ ⊢
  refine ⟨fun A => ⟨?_, ?_⟩, ?_⟩
  · have := (hh₁.1 A).1; have := (hh₂.1 A).1; positivity
  · have h1 := (hh₁.1 A).2; have h2 := (hh₂.1 A).2
    have e1 := mul_le_mul_of_nonneg_left h1 ha
    have e2 := mul_le_mul_of_nonneg_left h2 hb
    calc a * ⟪indL P A, h₁⟫_ℝ + b * ⟪indL P A, h₂⟫_ℝ
        ≤ a * (1 / (1 - α) * P.real A.1) + b * (1 / (1 - α) * P.real A.1) := add_le_add e1 e2
      _ = 1 / (1 - α) * P.real A.1 := by rw [← add_mul, hab, one_mul]
  · rw [hh₁.2, hh₂.2, mul_one, mul_one, hab]

theorem ae_bounds_of_mem_Kset {α : ℝ} {h : Lp ℝ 2 P} (hK : h ∈ Kset P α) :
    ∀ᵐ x ∂P, 0 ≤ h x ∧ h x ≤ 1 / (1 - α) := by
  rw [mem_Kset] at hK
  have hint : Integrable (fun x => h x) P := (Lp.memLp h).integrable one_le_two
  have h0 := ae_nonneg_of_forall_setIntegral_nonneg hint fun s hs _ => (hK.1 s hs).1
  have h1 := ae_le_of_forall_setIntegral_le hint (integrable_const (1 / (1 - α)))
    fun s hs _ => by rw [setIntegral_const, smul_eq_mul, mul_comm]; exact (hK.1 s hs).2
  filter_upwards [h0, h1] with x hx0 hx1
  exact ⟨hx0, hx1⟩

theorem norm_le_of_mem_Kset {α : ℝ} (hα1 : α < 1) {h : Lp ℝ 2 P} (hK : h ∈ Kset P α) :
    ‖h‖ ≤ 1 / (1 - α) := by
  have hc : 0 ≤ 1 / (1 - α) := le_of_lt (one_div_pos.2 (by linarith))
  have := Lp.norm_le_of_ae_bound hc ((ae_bounds_of_mem_Kset P hK).mono fun x hx => by
    rw [Real.norm_of_nonneg hx.1]; exact hx.2)
  have h1 : measureUnivNNReal P = 1 := by simp [measureUnivNNReal]
  rw [h1] at this
  simpa using this

/-! ### The embedding `L²(P) → H` -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The embedding `h ↦ ∫ h φ dP`. -/
def emb (φ : 𝒳 → H) (h : Lp ℝ 2 P) : H := ∫ x, h x • φ x ∂P

variable {P}

omit [IsProbabilityMeasure P] [CompleteSpace H] in
theorem integrable_smul_of_bound {φ : 𝒳 → H} {κ : ℝ} (hφ : StronglyMeasurable φ)
    (hκ : ∀ x, ‖φ x‖ ≤ κ) {f : 𝒳 → ℝ} (hf : Integrable f P) :
    Integrable (fun x => f x • φ x) P :=
  (hf.norm.mul_const κ).mono' (hf.aestronglyMeasurable.smul hφ.aestronglyMeasurable)
    (ae_of_all _ fun x => by
      rw [norm_smul]; exact mul_le_mul_of_nonneg_left (hκ x) (norm_nonneg _))

omit [CompleteSpace H] in
theorem integrable_Lp_smul {φ : 𝒳 → H} {κ : ℝ} (hφ : StronglyMeasurable φ)
    (hκ : ∀ x, ‖φ x‖ ≤ κ) (h : Lp ℝ 2 P) : Integrable (fun x => h x • φ x) P :=
  integrable_smul_of_bound hφ hκ ((Lp.memLp h).integrable one_le_two)

omit [CompleteSpace H] in
theorem emb_add {φ : 𝒳 → H} {κ : ℝ} (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (h₁ h₂ : Lp ℝ 2 P) : emb P φ (h₁ + h₂) = emb P φ h₁ + emb P φ h₂ := by
  unfold emb
  rw [← integral_add (integrable_Lp_smul hφ hκ h₁) (integrable_Lp_smul hφ hκ h₂)]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_add h₁ h₂] with x hx
  rw [hx, Pi.add_apply, add_smul]

omit [IsProbabilityMeasure P] [CompleteSpace H] in
theorem emb_smul (φ : 𝒳 → H) (a : ℝ) (h : Lp ℝ 2 P) : emb P φ (a • h) = a • emb P φ h := by
  unfold emb
  rw [← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_smul a h] with x hx
  rw [hx, Pi.smul_apply, smul_eq_mul, mul_smul]

theorem integral_norm_le_norm (h : Lp ℝ 2 P) : ∫ x, ‖h x‖ ∂P ≤ ‖h‖ := by
  rw [integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable h),
    ← eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable h), Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top h) (eLpNorm_le_eLpNorm_of_exponent_le one_le_two)

omit [CompleteSpace H] in
theorem norm_emb_le {φ : 𝒳 → H} {κ : ℝ} (hκ : ∀ x, ‖φ x‖ ≤ κ)
    (h : Lp ℝ 2 P) : ‖emb P φ h‖ ≤ κ * ‖h‖ := by
  have hκ0 : 0 ≤ κ := (norm_nonneg _).trans (hκ (nonempty_of_isProbabilityMeasure P).some)
  have hint : Integrable (fun x => h x) P := (Lp.memLp h).integrable one_le_two
  calc ‖emb P φ h‖ ≤ ∫ x, ‖h x‖ * κ ∂P :=
        norm_integral_le_of_norm_le (hint.norm.mul_const κ) (ae_of_all _ fun x => by
          rw [norm_smul]; exact mul_le_mul_of_nonneg_left (hκ x) (norm_nonneg _))
    _ = κ * ∫ x, ‖h x‖ ∂P := by rw [integral_mul_const, mul_comm]
    _ ≤ κ * ‖h‖ := mul_le_mul_of_nonneg_left (integral_norm_le_norm h) hκ0

omit [CompleteSpace H] in
theorem continuous_emb {φ : 𝒳 → H} {κ : ℝ} (hφ : StronglyMeasurable φ)
    (hκ : ∀ x, ‖φ x‖ ≤ κ) : Continuous (emb P φ) :=
  AddMonoidHomClass.continuous_of_bound
    ({ toFun := emb P φ, map_zero' := by simpa using emb_smul φ 0 0,
       map_add' := emb_add hφ hκ } : Lp ℝ 2 P →+ H) κ (norm_emb_le hκ)

/-! ### Conversions between trimmings and `Kset` -/

omit [CompleteSpace H] in
theorem exists_Kset_of_trim {α : ℝ} {g : 𝒳 → ℝ} (hg : IsTrimDensity P α g) (φ : 𝒳 → H) :
    ∃ h ∈ Kset P α, emb P φ h = ∫ x, g x • φ x ∂P := by
  have hmem : MemLp g 2 P := MemLp.of_bound hg.1.aestronglyMeasurable (1 / (1 - α))
    (ae_of_all _ fun x => by rw [Real.norm_of_nonneg (hg.2.1 x).1]; exact (hg.2.1 x).2)
  have hcoe : (hmem.toLp g : 𝒳 → ℝ) =ᵐ[P] g := MemLp.coeFn_toLp hmem
  have hgi : Integrable g P := Integrable.of_mem_Icc 0 (1 / (1 - α)) hg.1.aemeasurable
    (ae_of_all _ fun x => ⟨(hg.2.1 x).1, (hg.2.1 x).2⟩)
  refine ⟨hmem.toLp g, ?_, ?_⟩
  · rw [mem_Kset]
    refine ⟨fun A hA => ?_, ?_⟩
    · rw [integral_congr_ae (ae_restrict_of_ae hcoe)]
      refine ⟨setIntegral_nonneg hA fun x _ => (hg.2.1 x).1, ?_⟩
      calc ∫ x in A, g x ∂P ≤ ∫ _ in A, 1 / (1 - α) ∂P :=
            setIntegral_mono hgi.integrableOn (integrable_const _).integrableOn
              fun x => (hg.2.1 x).2
        _ = 1 / (1 - α) * P.real A := by rw [setIntegral_const, smul_eq_mul, mul_comm]
    · rw [integral_congr_ae hcoe, hg.2.2]
  · unfold emb
    exact integral_congr_ae (hcoe.mono fun x hx => by simp only [hx])

omit [CompleteSpace H] in
theorem exists_trim_of_Kset {α : ℝ} (hα1 : α < 1) {h : Lp ℝ 2 P} (hK : h ∈ Kset P α)
    (φ : 𝒳 → H) : ∃ g, IsTrimDensity P α g ∧ ∫ x, g x • φ x ∂P = emb P φ h := by
  have hc : 0 ≤ 1 / (1 - α) := le_of_lt (one_div_pos.2 (by linarith))
  have hae := ae_bounds_of_mem_Kset P hK
  have hm : AEMeasurable (fun x => h x) P := (Lp.aestronglyMeasurable h).aemeasurable
  set g : 𝒳 → ℝ := fun x => max 0 (min (1 / (1 - α)) (hm.mk _ x)) with hg
  have hgh : g =ᵐ[P] fun x => h x := by
    filter_upwards [hae, hm.ae_eq_mk] with x hx hxe
    simp only [hg, ← hxe, min_eq_right hx.2, max_eq_right hx.1]
  refine ⟨g, ⟨measurable_const.max (measurable_const.min hm.measurable_mk),
    fun x => ⟨le_max_left _ _, max_le hc (min_le_left _ _)⟩, ?_⟩, ?_⟩
  · rw [integral_congr_ae hgh]; exact ((mem_Kset P).1 hK).2
  · unfold emb
    exact integral_congr_ae (hgh.mono fun x hx => by simp only [hx])

end L2

/-! ### Attainment -/

theorem exists_common_of_Dpop_eq_zero {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {P Q : Measure 𝒳} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {φ : 𝒳 → H} {κ α : ℝ} (hφ : StronglyMeasurable φ)
    (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hD : Dpop φ P Q α = 0) :
    ∃ gP gQ : 𝒳 → ℝ, IsTrimDensity P α gP ∧ IsTrimDensity Q α gQ ∧
      ∫ x, gP x • φ x ∂P = ∫ x, gQ x • φ x ∂Q := by
  set c := 1 / (1 - α) with hc_def
  have hc1 : 1 ≤ c := by rw [hc_def]; exact one_le_one_div (by linarith) (by linarith)
  -- the minimisation domain
  let F : ℕ → Set (WithLp 2 (Lp ℝ 2 P × Lp ℝ 2 Q)) := fun n =>
    (WithLp.fst ⁻¹' Kset P α ∩ WithLp.snd ⁻¹' Kset Q α) ∩
      {x | ‖emb P φ x.fst - emb Q φ x.snd‖ ≤ 1 / ((n : ℝ) + 1)}
  have one_trim : ∀ (μ : Measure 𝒳) [IsProbabilityMeasure μ], IsTrimDensity μ α fun _ => 1 :=
    fun μ _ => ⟨measurable_const, fun _ => ⟨zero_le_one, hc1⟩, by simp⟩
  have hne : ∀ n, (F n).Nonempty := by
    intro n
    set S := {r | ∃ a ∈ region φ α P, ∃ b ∈ region φ α Q, r = ‖a - b‖} with hS
    have hSne : S.Nonempty := ⟨_, _, ⟨fun _ => 1, (one_trim P).1, (one_trim P).2.1,
      (one_trim P).2.2, rfl⟩, _, ⟨fun _ => 1, (one_trim Q).1, (one_trim Q).2.1, (one_trim Q).2.2,
      rfl⟩, rfl⟩
    have hlt : sInf S < 1 / ((n : ℝ) + 1) := by
      have : sInf S = 0 := hD
      rw [this]; positivity
    obtain ⟨_, ⟨a, ⟨gP, hgP1, hgP2, hgP3, rfl⟩, b, ⟨gQ, hgQ1, hgQ2, hgQ3, rfl⟩, rfl⟩, hr⟩ :=
      exists_lt_of_csInf_lt hSne hlt
    obtain ⟨hP, hPK, hPe⟩ := exists_Kset_of_trim (P := P) ⟨hgP1, hgP2, hgP3⟩ φ
    obtain ⟨hQ, hQK, hQe⟩ := exists_Kset_of_trim (P := Q) ⟨hgQ1, hgQ2, hgQ3⟩ φ
    refine ⟨WithLp.toLp 2 (hP, hQ), ⟨hPK, hQK⟩, ?_⟩
    change ‖emb P φ hP - emb Q φ hQ‖ ≤ _
    rw [hPe, hQe]; exact hr.le
  have hcl : ∀ n, IsClosed (F n) := by
    intro n
    refine (((isClosed_Kset P α).preimage (WithLp.continuous_fst 2 _ _)).inter
      ((isClosed_Kset Q α).preimage (WithLp.continuous_snd 2 _ _))).inter
      (isClosed_le ?_ continuous_const)
    exact (((continuous_emb hφ hκ).comp (WithLp.continuous_fst 2 _ _)).sub
      ((continuous_emb hφ hκ).comp (WithLp.continuous_snd 2 _ _))).norm
  have hcv : ∀ n, Convex ℝ (F n) := by
    intro n x hx y hy a b ha hb hab
    obtain ⟨⟨hx1, hx2⟩, hx3⟩ := hx
    obtain ⟨⟨hy1, hy2⟩, hy3⟩ := hy
    simp only [mem_ofPred_eq] at hx3 hy3
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · change (a • x + b • y).fst ∈ Kset P α
      rw [WithLp.add_fst, WithLp.smul_fst, WithLp.smul_fst]
      exact convex_Kset P α hx1 hy1 ha hb hab
    · change (a • x + b • y).snd ∈ Kset Q α
      rw [WithLp.add_snd, WithLp.smul_snd, WithLp.smul_snd]
      exact convex_Kset Q α hx2 hy2 ha hb hab
    · change ‖emb P φ (a • x + b • y).fst - emb Q φ (a • x + b • y).snd‖ ≤ _
      rw [WithLp.add_fst, WithLp.smul_fst, WithLp.smul_fst, WithLp.add_snd, WithLp.smul_snd,
        WithLp.smul_snd, emb_add hφ hκ, emb_add hφ hκ, emb_smul, emb_smul, emb_smul, emb_smul]
      have : a • emb P φ x.fst + b • emb P φ y.fst - (a • emb Q φ x.snd + b • emb Q φ y.snd) =
          a • (emb P φ x.fst - emb Q φ x.snd) + b • (emb P φ y.fst - emb Q φ y.snd) := by
        simp only [smul_sub]; abel
      rw [this]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      calc a * ‖emb P φ x.fst - emb Q φ x.snd‖ + b * ‖emb P φ y.fst - emb Q φ y.snd‖
          ≤ a * (1 / ((n : ℝ) + 1)) + b * (1 / ((n : ℝ) + 1)) :=
            add_le_add (mul_le_mul_of_nonneg_left hx3 ha) (mul_le_mul_of_nonneg_left hy3 hb)
        _ = 1 / ((n : ℝ) + 1) := by rw [← add_mul, hab, one_mul]
  have hanti : Antitone F := by
    intro n m hnm x hx
    refine ⟨hx.1, ?_⟩
    have h := hx.2
    simp only [mem_ofPred_eq] at h ⊢
    refine h.trans ?_
    gcongr
  have hb : ∀ n, ∀ x ∈ F n, ‖x‖ ^ 2 ≤ c ^ 2 + c ^ 2 := by
    intro n x hx
    rw [WithLp.prod_norm_sq_eq_of_L2]
    have h1 := norm_le_of_mem_Kset P hα1 hx.1.1
    have h2 := norm_le_of_mem_Kset Q hα1 hx.1.2
    gcongr
  obtain ⟨z, hz⟩ := nonempty_iInter_of_closed_convex F hne hcl hcv hanti _ hb
  rw [mem_iInter] at hz
  have hzero : emb P φ z.fst = emb Q φ z.snd := by
    by_contra hne'
    have hd : 0 < ‖emb P φ z.fst - emb Q φ z.snd‖ := norm_pos_iff.2 (sub_ne_zero.2 hne')
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hd
    have := (hz n).2
    simp only [mem_ofPred_eq] at this
    linarith
  obtain ⟨gP, hgP, hgPe⟩ := exists_trim_of_Kset hα1 (hz 0).1.1 φ
  obtain ⟨gQ, hgQ, hgQe⟩ := exists_trim_of_Kset hα1 (hz 0).1.2 φ
  exact ⟨gP, gQ, hgP, hgQ, by rw [hgPe, hgQe, hzero]⟩

end StatFormal.TrimmedMMD.ZeroSet
