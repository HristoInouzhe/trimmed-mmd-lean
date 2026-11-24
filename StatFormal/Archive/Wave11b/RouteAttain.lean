import StatFormal.Archive.Wave11b.Statements
import StatFormal.Archive.Wave8a.RouteGeorep
import StatFormal.Archive.TrimmedMMD.ZeroSet.Attain
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Route: trimmed MMD `lem:attainment`

* Convexity and the bound `κ` are direct (Bochner triangle inequality).
* **Closedness and attainment, no weak topology.** The trimming densities form a closed convex bounded set
  `Kset ⊆ L²(P)` (frozen-free helper `TrimmedMMD/ZeroSet/Attain`), and `h ↦ ∫ h φ dP` is a bounded linear map
  `L²(P) → H`. Nested closed convex sets `K ∩ {‖A x − c‖ ≤ D + 1/(n+1)}` in a Hilbert space with a common bound
  meet (`nonempty_iInter_of_closed_convex`), which gives a point with `‖A x − c‖ ≤ D`: with `c = z`, `D = 0`
  this is norm-closedness; in `L²(P) × L²(Q)` with `D = D_{α,k}` it is attainment (i), and (ii) follows.
* **Weak compactness.** Banach–Alaoglu (`WeakDual.isCompact_closedBall`) transported by the Riesz map: the
  closed ball is compact in `WeakSpace ℝ H`; the region is a convex norm-closed subset of it, hence weakly
  closed (Mazur, `Convex.toWeakSpace_closure`), hence weakly compact.
* The common trimming in (ii) is characteristicness applied to the two trimmings with the same embedding
  (`Wave8a.embed_eq`).
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace

namespace StatFormal.Wave11b

open StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional
open StatFormal.TrimmedMMD.ZeroSet

/-! ### A nested-intersection attainment lemma -/

theorem exists_le_of_approx {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (K : Set E) (hK : IsClosed K) (hKc : Convex ℝ K)
    (M : ℝ) (hb : ∀ x ∈ K, ‖x‖ ^ 2 ≤ M) (A : E →ₗ[ℝ] H) (hA : Continuous A) (c : H) (D : ℝ)
    (h : ∀ n : ℕ, ∃ x ∈ K, ‖A x - c‖ ≤ D + 1 / ((n : ℝ) + 1)) : ∃ x ∈ K, ‖A x - c‖ ≤ D := by
  let F : ℕ → Set E := fun n => K ∩ {x | ‖A x - c‖ ≤ D + 1 / ((n : ℝ) + 1)}
  have hne : ∀ n, (F n).Nonempty := fun n => by
    obtain ⟨x, hx, hxn⟩ := h n; exact ⟨x, hx, hxn⟩
  have hcl : ∀ n, IsClosed (F n) := fun n =>
    hK.inter (isClosed_le ((hA.sub continuous_const).norm) continuous_const)
  have hcv : ∀ n, Convex ℝ (F n) := by
    intro n x hx y hy a b ha hb' hab
    refine ⟨hKc hx.1 hy.1 ha hb' hab, ?_⟩
    have hx2 : ‖A x - c‖ ≤ D + 1 / ((n : ℝ) + 1) := hx.2
    have hy2 : ‖A y - c‖ ≤ D + 1 / ((n : ℝ) + 1) := hy.2
    change ‖A (a • x + b • y) - c‖ ≤ _
    have e : A (a • x + b • y) - c = a • (A x - c) + b • (A y - c) := by
      rw [map_add, map_smul, map_smul, smul_sub, smul_sub]
      have : c = a • c + b • c := by rw [← add_smul, hab, one_smul]
      conv_lhs => rw [this]
      abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb']
    calc a * ‖A x - c‖ + b * ‖A y - c‖
        ≤ a * (D + 1 / ((n : ℝ) + 1)) + b * (D + 1 / ((n : ℝ) + 1)) :=
          add_le_add (mul_le_mul_of_nonneg_left hx2 ha) (mul_le_mul_of_nonneg_left hy2 hb')
      _ = D + 1 / ((n : ℝ) + 1) := by rw [← add_mul, hab, one_mul]
  have hanti : Antitone F := by
    intro n m hnm x hx
    refine ⟨hx.1, ?_⟩
    have h1 : ‖A x - c‖ ≤ D + 1 / ((m : ℝ) + 1) := hx.2
    change ‖A x - c‖ ≤ D + 1 / ((n : ℝ) + 1)
    refine h1.trans ?_
    gcongr
  obtain ⟨x, hx⟩ := nonempty_iInter_of_closed_convex F hne hcl hcv hanti M
    (fun n x hx => hb x hx.1)
  rw [mem_iInter] at hx
  refine ⟨x, (hx 0).1, le_of_forall_pos_lt_add fun ε hε => ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  have := (hx n).2
  change ‖A x - c‖ ≤ _ at this
  linarith

section Region

variable {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {P : Measure 𝒳} [IsProbabilityMeasure P] {φ : 𝒳 → H} {κ α : ℝ}

/-- The embedding as a linear map `L²(P) → H`. -/
def embL (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) : Lp ℝ 2 P →ₗ[ℝ] H where
  toFun := emb P φ
  map_add' := emb_add hφ hκ
  map_smul' := emb_smul φ

theorem region_iff (hα1 : α < 1) (z : H) :
    z ∈ region φ α P ↔ ∃ h ∈ Kset P α, emb P φ h = z := by
  constructor
  · rintro ⟨g, hg, hgb, hg1, rfl⟩
    obtain ⟨h, hK, he⟩ := exists_Kset_of_trim (P := P) ⟨hg, hgb, hg1⟩ φ
    exact ⟨h, hK, he⟩
  · rintro ⟨h, hK, rfl⟩
    obtain ⟨g, ⟨hg, hgb, hg1⟩, he⟩ := exists_trim_of_Kset hα1 hK φ
    exact ⟨g, hg, hgb, hg1, he.symm⟩

theorem region_convex (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα1 : α < 1) :
    Convex ℝ (region φ α P) := by
  intro z₁ hz₁ z₂ hz₂ a b ha hb hab
  rw [region_iff hα1] at hz₁ hz₂ ⊢
  obtain ⟨h₁, hK₁, rfl⟩ := hz₁
  obtain ⟨h₂, hK₂, rfl⟩ := hz₂
  refine ⟨a • h₁ + b • h₂, convex_Kset P α hK₁ hK₂ ha hb hab, ?_⟩
  rw [emb_add hφ hκ, emb_smul, emb_smul]

theorem region_bounded (hκ : ∀ x, ‖φ x‖ ≤ κ) : ∀ z ∈ region φ α P, ‖z‖ ≤ κ := by
  rintro _ ⟨g, hg, hgb, hg1, rfl⟩
  have hgi : Integrable g P := IsTrimDensity.integrable ⟨hg, hgb, hg1⟩
  calc ‖∫ x, g x • φ x ∂P‖ ≤ ∫ x, g x * κ ∂P :=
        norm_integral_le_of_norm_le (hgi.mul_const κ) (ae_of_all _ fun x => by
          rw [norm_smul, Real.norm_of_nonneg (hgb x).1]
          exact mul_le_mul_of_nonneg_left (hκ x) (hgb x).1)
    _ = κ := by rw [integral_mul_const, hg1, one_mul]

theorem region_closed (hφ : StronglyMeasurable φ) (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα1 : α < 1) :
    IsClosed (region φ α P) := by
  refine isClosed_of_closure_subset fun z hz => ?_
  rw [region_iff hα1]
  have happrox : ∀ n : ℕ, ∃ h ∈ Kset P α, ‖embL hφ hκ h - z‖ ≤ 0 + 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨y, hy, hyz⟩ := Metric.mem_closure_iff.1 hz (1 / ((n : ℝ) + 1)) (by positivity)
    obtain ⟨h, hK, rfl⟩ := (region_iff hα1 y).1 hy
    refine ⟨h, hK, ?_⟩
    rw [zero_add, ← dist_eq_norm, dist_comm]
    exact hyz.le
  obtain ⟨h, hK, hle⟩ := exists_le_of_approx (Kset P α) (isClosed_Kset P α) (convex_Kset P α)
    ((1 / (1 - α)) ^ 2) (fun h hh => by
      have := norm_le_of_mem_Kset P hα1 hh
      gcongr) (embL hφ hκ) (continuous_emb hφ hκ) z 0 happrox
  refine ⟨h, hK, ?_⟩
  have : ‖emb P φ h - z‖ = 0 := le_antisymm hle (norm_nonneg _)
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

end Region

theorem attain_convex : Claims.attain_convex := by
  intro 𝒳 H _ _ _ _ P _ φ κ α hφ hκ _ hα1
  exact region_convex hφ hκ hα1

theorem attain_bounded : Claims.attain_bounded := by
  intro 𝒳 H _ _ _ _ P _ φ κ α _ hκ _ _
  exact region_bounded hκ

theorem attain_closed : Claims.attain_closed := by
  intro 𝒳 H _ _ _ _ P _ φ κ α hφ hκ _ hα1
  exact region_closed hφ hκ hα1

/-! ### Weak compactness -/

/-- Closed balls of a real Hilbert space are weakly compact (Banach–Alaoglu through the Riesz map). -/
theorem isCompact_toWeakSpace_closedBall {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (r : ℝ) : IsCompact (toWeakSpace ℝ H '' Metric.closedBall (0 : H) r) := by
  let f : WeakDual ℝ H → WeakSpace ℝ H := fun ℓ =>
    toWeakSpace ℝ H ((InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual ℓ))
  have hf : Continuous f := by
    refine WeakBilin.continuous_of_continuous_eval _ fun y => ?_
    have e : (fun ℓ : WeakDual ℝ H => (topDualPairing ℝ H).flip (f ℓ) y) =
        fun ℓ => ℓ ((InnerProductSpace.toDual ℝ H).symm y) := by
      funext ℓ
      change y ((InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual ℓ)) = _
      conv_lhs => rw [← (InnerProductSpace.toDual ℝ H).apply_symm_apply y]
      rw [InnerProductSpace.toDual_apply_apply, real_inner_comm, ← InnerProductSpace.toDual_apply_apply,
        LinearIsometryEquiv.apply_symm_apply]
      rfl
    rw [e]
    exact WeakDual.eval_continuous _
  have hK := WeakDual.isCompact_closedBall (𝕜 := ℝ) (E := H) 0 r
  have himg : f '' (WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 r) =
      toWeakSpace ℝ H '' Metric.closedBall (0 : H) r := by
    ext w
    constructor
    · rintro ⟨ℓ, hℓ, rfl⟩
      refine ⟨_, ?_, rfl⟩
      simp only [mem_preimage, Metric.mem_closedBall, dist_zero_right] at hℓ ⊢
      rwa [LinearIsometryEquiv.norm_map]
    · rintro ⟨x, hx, rfl⟩
      refine ⟨StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H x), ?_, ?_⟩
      · simp only [mem_preimage, Metric.mem_closedBall, dist_zero_right] at hx ⊢
        change ‖InnerProductSpace.toDual ℝ H x‖ ≤ r
        rwa [LinearIsometryEquiv.norm_map]
      · change toWeakSpace ℝ H ((InnerProductSpace.toDual ℝ H).symm
          (InnerProductSpace.toDual ℝ H x)) = _
        rw [LinearIsometryEquiv.symm_apply_apply]
  rw [← himg]
  exact hK.image hf

theorem attain_weak_compact : Claims.attain_weak_compact := by
  intro 𝒳 H _ _ _ _ P _ φ κ α hφ hκ _ hα1
  have hcl : IsClosed (toWeakSpace ℝ H '' region φ α P) := by
    rw [← closure_eq_iff_isClosed, ← (region_convex hφ hκ hα1).toWeakSpace_closure ℝ,
      (region_closed hφ hκ hα1).closure_eq]
  refine (isCompact_toWeakSpace_closedBall κ).of_isClosed_subset hcl (image_mono fun z hz => ?_)
  simpa [Metric.mem_closedBall, dist_zero_right] using region_bounded hκ z hz

/-! ### Attainment -/

theorem exists_attain_Dpop {𝒳 H : Type*} [MeasurableSpace 𝒳] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {P Q : Measure 𝒳} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {φ : 𝒳 → H} {κ α : ℝ} (hφ : StronglyMeasurable φ)
    (hκ : ∀ x, ‖φ x‖ ≤ κ) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    ∃ a ∈ region φ α P, ∃ b ∈ region φ α Q, ‖a - b‖ = Dpop φ P Q α := by
  set c := 1 / (1 - α) with hc_def
  have hc1 : 1 ≤ c := by rw [hc_def]; exact one_le_one_div (by linarith) (by linarith)
  set S := {r | ∃ a ∈ region φ α P, ∃ b ∈ region φ α Q, r = ‖a - b‖} with hS
  have one_trim : ∀ (μ : Measure 𝒳) [IsProbabilityMeasure μ], IsTrimDensity μ α fun _ => 1 :=
    fun μ _ => ⟨measurable_const, fun _ => ⟨zero_le_one, hc1⟩, by simp⟩
  have hSne : S.Nonempty := ⟨_, _, ⟨fun _ => 1, (one_trim P).1, (one_trim P).2.1,
    (one_trim P).2.2, rfl⟩, _, ⟨fun _ => 1, (one_trim Q).1, (one_trim Q).2.1, (one_trim Q).2.2,
    rfl⟩, rfl⟩
  have hSbdd : BddBelow S := ⟨0, by rintro _ ⟨a, -, b, -, rfl⟩; exact norm_nonneg _⟩
  have hD : Dpop φ P Q α = sInf S := rfl
  let A : WithLp 2 (Lp ℝ 2 P × Lp ℝ 2 Q) →ₗ[ℝ] H :=
    { toFun := fun x => emb P φ x.fst - emb Q φ x.snd
      map_add' := fun x y => by
        rw [WithLp.add_fst, WithLp.add_snd, emb_add hφ hκ, emb_add hφ hκ]; abel
      map_smul' := fun a x => by
        rw [WithLp.smul_fst, WithLp.smul_snd, emb_smul, emb_smul, RingHom.id_apply, smul_sub] }
  have hA : Continuous A :=
    ((continuous_emb hφ hκ).comp (WithLp.continuous_fst 2 _ _)).sub
      ((continuous_emb hφ hκ).comp (WithLp.continuous_snd 2 _ _))
  have happrox : ∀ n : ℕ, ∃ x ∈ WithLp.fst ⁻¹' Kset P α ∩ WithLp.snd ⁻¹' Kset Q α,
      ‖A x - 0‖ ≤ Dpop φ P Q α + 1 / ((n : ℝ) + 1) := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hlt : sInf S < Dpop φ P Q α + 1 / ((n : ℝ) + 1) := by rw [← hD]; linarith
    obtain ⟨_, ⟨a, ha, b, hb, rfl⟩, hr⟩ := exists_lt_of_csInf_lt hSne hlt
    obtain ⟨hP, hPK, rfl⟩ := (region_iff hα1 a).1 ha
    obtain ⟨hQ, hQK, rfl⟩ := (region_iff hα1 b).1 hb
    exact ⟨WithLp.toLp 2 (hP, hQ), ⟨hPK, hQK⟩, by rw [sub_zero]; exact hr.le⟩
  obtain ⟨x, hx, hle⟩ := exists_le_of_approx _
    (((isClosed_Kset P α).preimage (WithLp.continuous_fst 2 _ _)).inter
      ((isClosed_Kset Q α).preimage (WithLp.continuous_snd 2 _ _)))
    (by
      intro x hx y hy a b ha hb hab
      refine ⟨?_, ?_⟩
      · change (a • x + b • y).fst ∈ Kset P α
        rw [WithLp.add_fst, WithLp.smul_fst, WithLp.smul_fst]
        exact convex_Kset P α hx.1 hy.1 ha hb hab
      · change (a • x + b • y).snd ∈ Kset Q α
        rw [WithLp.add_snd, WithLp.smul_snd, WithLp.smul_snd]
        exact convex_Kset Q α hx.2 hy.2 ha hb hab)
    (c ^ 2 + c ^ 2) (fun x hx => by
      rw [WithLp.prod_norm_sq_eq_of_L2]
      have h1 := norm_le_of_mem_Kset P hα1 hx.1
      have h2 := norm_le_of_mem_Kset Q hα1 hx.2
      gcongr) A hA 0 _ happrox
  refine ⟨emb P φ x.fst, (region_iff hα1 _).2 ⟨_, hx.1, rfl⟩, emb Q φ x.snd,
    (region_iff hα1 _).2 ⟨_, hx.2, rfl⟩, le_antisymm ?_ ?_⟩
  · simpa [A] using hle
  · rw [hD]
    exact csInf_le hSbdd ⟨_, (region_iff hα1 _).2 ⟨_, hx.1, rfl⟩, _,
      (region_iff hα1 _).2 ⟨_, hx.2, rfl⟩, rfl⟩

theorem attain_inf : Claims.attain_inf := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ α hφ hκ hα0 hα1
  obtain ⟨a, ha, b, hb, hab⟩ := exists_attain_Dpop (P := P) (Q := Q) hφ hκ hα0 hα1
  rw [← StatFormal.Wave8a.embed_eq P φ hα1] at ha
  rw [← StatFormal.Wave8a.embed_eq Q φ hα1] at hb
  obtain ⟨P', hP', rfl⟩ := ha
  obtain ⟨Q', hQ', rfl⟩ := hb
  refine ⟨P', hP', Q', hQ', ?_⟩
  rw [hab, StatFormal.Wave8a.georep_dist 𝒳 H P Q φ κ α hφ hκ hα0 hα1]

theorem attain_zero : Claims.attain_zero := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ α hφ hκ hα0 hα1 hD
  obtain ⟨P', hP', Q', hQ', h⟩ := attain_inf 𝒳 H P Q φ κ α hφ hκ hα0 hα1
  rw [hD] at h
  have he : ∫ x, φ x ∂P' = ∫ x, φ x ∂Q' := sub_eq_zero.1 (norm_eq_zero.1 h)
  refine ⟨∫ x, φ x ∂P', ?_, ?_⟩
  · rw [← StatFormal.Wave8a.embed_eq P φ hα1]; exact ⟨P', hP', rfl⟩
  · rw [← StatFormal.Wave8a.embed_eq Q φ hα1, he]; exact ⟨Q', hQ', rfl⟩

theorem attain_common : Claims.attain_common := by
  intro 𝒳 H _ _ _ _ P Q _ _ φ κ α hφ hκ hchar hα0 hα1 z ⟨hzP, hzQ⟩
  rw [← StatFormal.Wave8a.embed_eq P φ hα1] at hzP
  rw [← StatFormal.Wave8a.embed_eq Q φ hα1] at hzQ
  obtain ⟨P', hP', rfl⟩ := hzP
  obtain ⟨Q', hQ', hQe⟩ := hzQ
  have : P' = Q' := hchar P' Q' hP'.1 hQ'.1 hQe.symm
  exact ⟨P', ⟨hP', this ▸ hQ'⟩, rfl⟩

end StatFormal.Wave11b
