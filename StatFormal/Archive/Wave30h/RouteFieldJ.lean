import StatFormal.Archive.Wave30h.RouteOP
import StatFormal.Archive.Wave30h.RouteTransfer
import StatFormal.Archive.Wave9b.RouteField

/-!
# Route — `thm:field` and `cor:field-local` in the journal form, `def:standardisable` old ⇒ new (untrusted)

Core (`core_one`): for one realisation, `S'` `L`-Lipschitz, `Ŝ_ν⁻¹ − S' = h + k` with `k` `K`-Lipschitz, and any
measurable `S̃` (the true `S_s`, or the standardiser of an approximating member) with `δ = W₂((S̃)_#R, γ)`:
`‖Ŝ_ν⁻¹ ∘ Ŝ − S' ∘ S̃‖_{L²(R)} ≤ ‖h‖_∞ + ‖k‖_{L²(γ)} + K(‖Ŝ − S̃‖_{L²(R)} + δ) + L‖Ŝ − S̃‖_{L²(R)}` — the term
`h(Ŝ(X))` by the sup norm, `k(Ŝ(X))` by `lem:transfer` at the perturbed law `Ŝ_#R` (whose distance to `γ` is at most
`‖Ŝ − S̃‖ + δ`), and `S'(Ŝ X) − S'(S̃ X)` by the Lipschitz constant. Then `W₂(T̂_#R, ν) ≤ core + Lδ` because
`(S' ∘ S̃)_#R = S'_#(S̃_#R)` is within `Lδ` of `S'_#γ = ν`.
`thm:field` is the case `S̃ = S_s` (`δ = 0`); its rate is `fieldlocal_rate` with `δ = 0`.
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology TauCeti
open scoped ENNReal NNReal

namespace StatFormal.Wave30h

open StatFormal.Wave9b (Standardises BigOP LipschitzWhp field_exact_one w2_map_map_le)
open StatFormal.OTFD.WaveL1 (Euc)

variable {d : ℕ}

lemma eLpNorm_comp_le_supNorm {R : Measure (Euc d)} [IsProbabilityMeasure R] {h F : Euc d → Euc d}
    (hm : Measurable fun x => h (F x)) :
    eLpNorm (fun x => h (F x)) 2 R ≤ supNorm h := by
  have : eLpNorm (fun _ : Euc d => supNorm h) 2 R = supNorm h := by
    rw [eLpNorm_const _ (by norm_num) (IsProbabilityMeasure.ne_zero R)]
    simp
  rw [← this]
  refine eLpNorm_mono_enorm hm.aestronglyMeasurable fun x => ?_
  simp only [enorm_eq_self]
  exact le_iSup (fun z => ‖h z‖ₑ) (F x)

lemma eLpNorm_lip_comp_sub {R : Measure (Euc d)} {S' F G : Euc d → Euc d} {L : ℝ≥0} (hS' : LipschitzWith L S')
    (hF : Measurable F) (hG : Measurable G) :
    eLpNorm (fun x => S' (F x) - S' (G x)) 2 R ≤ L * eLpNorm (fun x => F x - G x) 2 R := by
  have hm := hS'.continuous.measurable
  refine (eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' (g := fun x => F x - G x) (c := L) ?_
    (.of_forall fun x => ?_) 2).trans_eq ?_
  · exact ((hm.comp hF).sub (hm.comp hG)).aestronglyMeasurable
  · simpa [edist_eq_enorm_sub] using hS'.edist_le_mul (F x) (G x)
  · simp [ENNReal.smul_def]

/-- The core estimate of the proofs of `thm:field` and `cor:field-local` (one group, one realisation). -/
lemma core_one {R γ : Measure (Euc d)} [IsProbabilityMeasure R] [IsProbabilityMeasure γ]
    {St Shat S' Sνinvhat h k : Euc d → Euc d} {L K : ℝ≥0}
    (hSt : Measurable St) (hShat : Measurable Shat) (hinv : Measurable Sνinvhat) (hS' : LipschitzWith L S')
    (hk : LipschitzWith K k) (hdec : ∀ z, Sνinvhat z - S' z = h z + k z) :
    eLpNorm (fun x => Sνinvhat (Shat x) - S' (St x)) 2 R ≤
      supNorm h + eLpNorm k 2 γ +
        K * (eLpNorm (fun x => Shat x - St x) 2 R + wassersteinEDist 2 (R.map St) γ) +
        L * eLpNorm (fun x => Shat x - St x) 2 R := by
  have hkm : Measurable k := hk.continuous.measurable
  have hS'm : Measurable S' := hS'.continuous.measurable
  have hhm : Measurable h := by
    have : h = fun z => Sνinvhat z - S' z - k z := by
      funext z; rw [hdec z]; abel
    rw [this]; exact (hinv.sub hS'm).sub hkm
  set a : Euc d → Euc d := fun x => h (Shat x)
  set b : Euc d → Euc d := fun x => k (Shat x)
  set c : Euc d → Euc d := fun x => S' (Shat x) - S' (St x)
  have hsplit : (fun x => Sνinvhat (Shat x) - S' (St x)) = (a + b) + c := by
    funext x
    have := hdec (Shat x)
    simp only [a, b, c, Pi.add_apply]
    rw [← this]; abel
  have ha : eLpNorm a 2 R ≤ supNorm h := eLpNorm_comp_le_supNorm (hhm.comp hShat)
  have hc : eLpNorm c 2 R ≤ L * eLpNorm (fun x => Shat x - St x) 2 R := eLpNorm_lip_comp_sub hS' hShat hSt
  have hb : eLpNorm b 2 R ≤
      eLpNorm k 2 γ + K * (eLpNorm (fun x => Shat x - St x) 2 R + wassersteinEDist 2 (R.map St) γ) := by
    have e1 : eLpNorm b 2 R = eLpNorm k 2 (R.map Shat) :=
      (eLpNorm_map_measure hkm.aestronglyMeasurable hShat.aemeasurable).symm
    have : IsProbabilityMeasure (R.map Shat) := inferInstance
    rw [e1]
    refine (transfer_general measurable_edist (R.map Shat) γ hk).trans ?_
    have hw : wassersteinEDist 2 (R.map Shat) γ ≤
        eLpNorm (fun x => Shat x - St x) 2 R + wassersteinEDist 2 (R.map St) γ :=
      (wassersteinEDist_triangle measurable_edist (by norm_num) _ (R.map St) _).trans
        (add_le_add (w2_map_map_le R hShat hSt) le_rfl)
    gcongr
  have hab : eLpNorm (a + b) 2 R ≤ eLpNorm a 2 R + eLpNorm b 2 R := eLpNorm_add_le (by norm_num)
  have habc : eLpNorm ((a + b) + c) 2 R ≤ eLpNorm (a + b) 2 R + eLpNorm c 2 R := eLpNorm_add_le (by norm_num)
  rw [hsplit]
  calc eLpNorm ((a + b) + c) 2 R ≤ eLpNorm a 2 R + eLpNorm b 2 R + eLpNorm c 2 R :=
        habc.trans (add_le_add hab le_rfl)
    _ ≤ supNorm h + (eLpNorm k 2 γ +
          K * (eLpNorm (fun x => Shat x - St x) 2 R + wassersteinEDist 2 (R.map St) γ)) +
          L * eLpNorm (fun x => Shat x - St x) 2 R := add_le_add (add_le_add ha hb) hc
    _ = _ := by ring

lemma map_S'_eq {ν γ : Measure (Euc d)} {Sν Sνinv S' : Euc d → Euc d} (hν : Standardises ν γ Sν Sνinv)
    (hS' : Measurable S') (hae : S' =ᵐ[γ] Sνinv) : γ.map S' = ν := by
  have hγν : γ.map Sνinv = ν := by
    have := field_exact_one hν hν
    obtain ⟨hνm, hνim, hνmap, -, -⟩ := hν
    rw [← hνmap, Measure.map_map hνim hνm]; exact this
  rw [Measure.map_congr hae, hγν]

/-- `W₂(T̂_#R, ν) ≤ Lδ + core`. -/
lemma w2_one {R ν γ : Measure (Euc d)} [IsProbabilityMeasure R] [IsProbabilityMeasure γ]
    {St Shat Sν Sνinv S' Sνinvhat h k : Euc d → Euc d} {L K : ℝ≥0}
    (hν : Standardises ν γ Sν Sνinv) (hS' : LipschitzWith L S') (hae : S' =ᵐ[γ] Sνinv)
    (hSt : Measurable St) (hShat : Measurable Shat) (hinv : Measurable Sνinvhat) (hk : LipschitzWith K k)
    (hdec : ∀ z, Sνinvhat z - S' z = h z + k z) :
    wassersteinEDist 2 (R.map (Sνinvhat ∘ Shat)) ν ≤
      L * wassersteinEDist 2 (R.map St) γ + supNorm h + eLpNorm k 2 γ +
        K * (eLpNorm (fun x => Shat x - St x) 2 R + wassersteinEDist 2 (R.map St) γ) +
        L * eLpNorm (fun x => Shat x - St x) 2 R := by
  have hS'm : Measurable S' := hS'.continuous.measurable
  have : IsProbabilityMeasure (R.map St) := inferInstance
  have h1 : wassersteinEDist 2 (R.map (Sνinvhat ∘ Shat)) (R.map (S' ∘ St)) ≤
      eLpNorm (fun x => Sνinvhat (Shat x) - S' (St x)) 2 R :=
    w2_map_map_le R (hinv.comp hShat) (hS'm.comp hSt)
  have h2 : wassersteinEDist 2 (R.map (S' ∘ St)) ν ≤ L * wassersteinEDist 2 (R.map St) γ := by
    rw [← Measure.map_map hS'm hSt, ← map_S'_eq hν hS'm hae]
    exact wassersteinEDist_map_le_mul measurable_edist hS'm hS' _ _
  calc _ ≤ wassersteinEDist 2 (R.map (Sνinvhat ∘ Shat)) (R.map (S' ∘ St)) +
        wassersteinEDist 2 (R.map (S' ∘ St)) ν :=
        wassersteinEDist_triangle measurable_edist (by norm_num) _ _ _
    _ ≤ (supNorm h + eLpNorm k 2 γ +
          K * (eLpNorm (fun x => Shat x - St x) 2 R + wassersteinEDist 2 (R.map St) γ) +
          L * eLpNorm (fun x => Shat x - St x) 2 R) + L * wassersteinEDist 2 (R.map St) γ :=
        add_le_add (h1.trans (core_one hSt hShat hinv hS' hk hdec)) h2
    _ = _ := by ring

lemma gap_le_sum {R : Fin 2 → Measure (Euc d)} {ν : Measure (Euc d)} [IsFiniteMeasure ν] {T : Fin 2 → Euc d → Euc d}
    {B : Fin 2 → ℝ≥0∞} (hB : ∀ s, wassersteinEDist 2 ((R s).map (T s)) ν ≤ B s) :
    wassersteinEDist 2 ((R 0).map (T 0)) ((R 1).map (T 1)) ≤ ∑ s, B s := by
  rw [Fin.sum_univ_two]
  calc _ ≤ wassersteinEDist 2 ((R 0).map (T 0)) ν + wassersteinEDist 2 ν ((R 1).map (T 1)) :=
        wassersteinEDist_triangle measurable_edist (by norm_num) _ _ _
    _ ≤ B 0 + B 1 := by
        rw [wassersteinEDist_comm measurable_edist 2 ν]
        exact add_le_add (hB 0) (hB 1)

/-! ### `cor:field-local`, deterministic -/

theorem fieldlocal_bound : Claims.fieldlocal_bound := by
  intro d R ν γ St Shat Sν Sνinv S' Sνinvhat h k L K hR hν hγ hSν hS' hae hSt hShat hinv hk hdec
  exact gap_le_sum (R := R) (T := fun s => Sνinvhat ∘ Shat s) fun s => by
    have := hR s
    exact w2_one hSν hS' hae (hSt s) (hShat s) hinv hk hdec

/-! ### `thm:field`, deterministic -/

theorem fieldJ_bound : Claims.fieldJ_bound := by
  intro d R ν γ S Sinv Shat Sν Sνinv S' Sνinvhat h k L K hR hν hγ hS hSν hS' hae hShat hinv hk hdec
  have hδ : ∀ s, wassersteinEDist 2 ((R s).map (S s)) γ = 0 := fun s => by
    rw [(hS s).2.2.1]; exact wassersteinEDist_self_of_measurable_edist measurable_edist 2 γ
  have one : ∀ s, eLpNorm (fun x => Sνinvhat (Shat s x) - Sνinv (S s x)) 2 (R s) ≤
      supNorm h + eLpNorm k 2 γ + K * eLpNorm (fun x => Shat s x - S s x) 2 (R s) +
        L * eLpNorm (fun x => Shat s x - S s x) 2 (R s) := fun s => by
    have := hR s
    have hae' : ∀ᵐ x ∂(R s), S' (S s x) = Sνinv (S s x) := by
      have : S' =ᵐ[(R s).map (S s)] Sνinv := by rw [(hS s).2.2.1]; exact hae
      exact ae_of_ae_map (hS s).1.aemeasurable this
    have heq : eLpNorm (fun x => Sνinvhat (Shat s x) - Sνinv (S s x)) 2 (R s) =
        eLpNorm (fun x => Sνinvhat (Shat s x) - S' (S s x)) 2 (R s) :=
      eLpNorm_congr_ae (hae'.mono fun x hx => by simp [hx])
    rw [heq]
    have := core_one (R := R s) (γ := γ) (hS s).1 (hShat s) hinv hS' hk hdec
    simpa [hδ s] using this
  have two : ∀ s, wassersteinEDist 2 ((R s).map (Sνinvhat ∘ Shat s)) ν ≤
      supNorm h + eLpNorm k 2 γ + K * eLpNorm (fun x => Shat s x - S s x) 2 (R s) +
        L * eLpNorm (fun x => Shat s x - S s x) 2 (R s) := fun s => by
    have := hR s
    have := w2_one (R := R s) hSν hS' hae (hS s).1 (hShat s) hinv hk hdec
    simpa [hδ s] using this
  exact ⟨one, two, gap_le_sum two⟩

/-! ### Rates -/

lemma bigOP_ofReal_rate {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {r : ℕ → ℝ} : BigOP P r (fun n _ => ENNReal.ofReal (r n)) := by
  intro η hη
  refine ⟨1, 0, fun n _ => ⟨univ, MeasurableSet.univ, ?_, fun _ _ => by simp⟩⟩
  rw [measure_univ]; exact ENNReal.ofReal_le_one.2 (by linarith)

lemma bigOP_rate_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {r r' : ℕ → ℝ} (hr : ∀ n, 0 ≤ r n) (hrr : ∀ n, r n ≤ r' n) {X : ℕ → Ω → ℝ≥0∞} (hX : BigOP P r X) :
    BigOP P r' X :=
  bigOP_rate_mono hr zero_le_one (Eventually.of_forall fun n => by simpa using hrr n) hX

theorem fieldlocal_rate : Claims.fieldlocal_rate := by
  intro d R ν γ St Sν Sνinv Ω _ P Shat Sνinvhat r δ L hP hr hδ hR hν hγ hSν hSt hδW hShat hinv hO hJ
  obtain ⟨S', h, k, hS', hae, hdec, hOh, hLk, hOk⟩ := hJ
  have hrδ : ∀ n, 0 ≤ r n + δ n := fun n => add_nonneg (hr n) (hδ n)
  have up : ∀ {X : ℕ → Ω → ℝ≥0∞}, BigOP P r X → BigOP P (fun n => r n + δ n) X :=
    fun hX => bigOP_rate_le hr (fun n => le_add_of_nonneg_right (hδ n)) hX
  have upδ : BigOP P (fun n => r n + δ n) (fun n _ => ENNReal.ofReal (δ n)) :=
    bigOP_rate_le hδ (fun n => le_add_of_nonneg_left (hr n)) bigOP_ofReal_rate
  -- the two random pieces: `Z` (no Lipschitz factor) and `W` (multiplied by `Lip k`)
  let fw : ℕ → Ω → Fin 2 → ℝ≥0∞ := fun n ω s => eLpNorm (fun x => Shat n ω s x - St n s x) 2 (R n s)
  let Z : ℕ → Ω → ℝ≥0∞ := fun n ω => ∑ s : Fin 2, (L * ENNReal.ofReal (δ n) + supNorm (h n ω) +
    eLpNorm (k n ω) 2 γ + L * fw n ω s)
  let W : ℕ → Ω → ℝ≥0∞ := fun n ω => ∑ s : Fin 2, (fw n ω s + ENNReal.ofReal (δ n))
  have hZ : BigOP P (fun n => r n + δ n) Z := by
    simp only [Z, Fin.sum_univ_two]
    have hfw : ∀ s, BigOP P (fun n => r n + δ n) (fun n ω => (L : ℝ≥0∞) * fw n ω s) :=
      fun s => bigOP_const_mul hrδ L (up (hO s))
    have hpiece : ∀ s, BigOP P (fun n => r n + δ n) (fun n ω => L * ENNReal.ofReal (δ n) +
        supNorm (h n ω) + eLpNorm (k n ω) 2 γ + L * fw n ω s) := fun s =>
      bigOP_add hrδ (bigOP_add hrδ (bigOP_add hrδ (bigOP_const_mul hrδ L upδ) (up hOh)) (up hOk)) (hfw s)
    exact bigOP_add hrδ (hpiece 0) (hpiece 1)
  have hW : BigOP P (fun n => r n + δ n) W := by
    simp only [W, Fin.sum_univ_two]
    exact bigOP_add hrδ (bigOP_add hrδ (up (hO 0)) upδ) (bigOP_add hrδ (up (hO 1)) upδ)
  refine bigOP_of_lip hrδ (Q := fun n ω K => LipschitzWith K (k n ω)) hLk ?_ hZ hW
  intro n ω K hK
  have hb := fieldlocal_bound d (R n) ν γ (St n) (Shat n ω) Sν Sνinv S' (Sνinvhat n ω) (h n ω) (k n ω) L K
    (hR n) hν hγ hSν hS' hae (hSt n) (hShat n ω) (hinv n ω) hK (hdec n ω)
  refine hb.trans ?_
  simp only [Z, W, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun s _ => ?_
  have hδs := hδW n s
  calc (L : ℝ≥0∞) * wassersteinEDist 2 ((R n s).map (St n s)) γ + supNorm (h n ω) + eLpNorm (k n ω) 2 γ +
        K * (eLpNorm (fun x => Shat n ω s x - St n s x) 2 (R n s) + wassersteinEDist 2 ((R n s).map (St n s)) γ) +
        L * eLpNorm (fun x => Shat n ω s x - St n s x) 2 (R n s)
      ≤ L * ENNReal.ofReal (δ n) + supNorm (h n ω) + eLpNorm (k n ω) 2 γ +
        K * (fw n ω s + ENNReal.ofReal (δ n)) + L * fw n ω s := by gcongr
    _ = _ := by ring

theorem fieldJ_rate : Claims.fieldJ_rate := by
  intro d R ν γ S Sinv Sν Sνinv Ω _ P Shat Sνinvhat r L hP hr hR hν hγ hS hSν hShat hinv hO hJ
  have h := fieldlocal_rate d (fun _ => R) ν γ (fun _ => S) Sν Sνinv Ω P Shat Sνinvhat r (fun _ => 0) L hP hr
    (fun _ => le_rfl) (fun _ => hR) hν hγ hSν (fun _ s => (hS s).1)
    (fun _ s => by
      rw [(hS s).2.2.1, wassersteinEDist_self_of_measurable_edist measurable_edist 2 γ]; exact zero_le)
    hShat hinv hO hJ
  simpa using h

/-! ### `def:standardisable`: old ⇒ new -/

/-- Coordinatewise McShane extension of a map into `ℝ^m` that is `K`-Lipschitz on `s`. -/
lemma LipschitzOnWith.extend_euc {m : ℕ} {f : Euc d → Euc m} {s : Set (Euc d)} {K : ℝ≥0}
    (hf : LipschitzOnWith K f s) : ∃ g : Euc d → Euc m, LipschitzWith (NNReal.sqrt m * K) g ∧ EqOn f g s := by
  have hi : ∀ i, LipschitzOnWith K (fun x => f x i) s := fun i =>
    LipschitzOnWith.of_dist_le_mul fun x hx y hy =>
      (PiLp.dist_apply_le (f x) (f y) i).trans (hf.dist_le_mul x hx y hy)
  choose g hg heq using fun i => (hi i).extend_real
  refine ⟨fun x => WithLp.toLp 2 fun i => g i x, LipschitzWith.of_dist_le_mul fun x y => ?_, fun x hx => ?_⟩
  · rw [EuclideanSpace.dist_eq]
    have hb : ∀ i, dist (g i x) (g i y) ^ 2 ≤ (K * dist x y) ^ 2 := fun i =>
      pow_le_pow_left₀ dist_nonneg ((hg i).dist_le_mul x y) 2
    calc √(∑ i, dist ((WithLp.toLp 2 fun i => g i x : Euc m) i) ((WithLp.toLp 2 fun i => g i y : Euc m) i) ^ 2)
        ≤ √(∑ _i : Fin m, (K * dist x y) ^ 2) := Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => by simpa using hb i)
      _ = ↑(NNReal.sqrt m * K) * dist x y := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (by positivity)]
          simp [mul_assoc]
  · ext i; exact heq i hx

theorem stdz_old_to_new : Claims.stdz_old_to_new := by
  intro d γ _ Sinv A Ω _ P _ Sinvhat r L hr hA hLA hmeas hO hLip
  obtain ⟨S', hS', heq⟩ := LipschitzOnWith.extend_euc hLA
  have hae : S' =ᵐ[γ] Sinv := by
    refine measure_mono_null (fun z hz => ?_) hA
    by_contra hzA
    exact hz (heq (by simpa using hzA)).symm
  refine ⟨NNReal.sqrt d * L, S', fun _ _ _ => 0, fun n ω z => Sinvhat n ω z - S' z, hS', hae,
    fun n ω z => by simp, ?_, ?_, ?_⟩
  · simpa [supNorm] using (bigOP_zero (P := P) (r := r))
  · intro η hη
    obtain ⟨B, hBm, hBt, hBL⟩ := hLip
    have hev : ∀ᶠ n in atTop, ENNReal.ofReal (1 - η) < P (B n) := by
      refine hBt.eventually (lt_mem_nhds ?_)
      rw [← ENNReal.ofReal_one]
      exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 (by linarith)
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    exact ⟨L + NNReal.sqrt d * L, N, fun n hn => ⟨B n, hBm n, (hN n hn).le, fun ω hω => (hBL n ω hω).sub hS'⟩⟩
  · refine bigOP_mono (fun n ω => (eLpNorm_congr_ae (hae.mono fun z hz => by simp [hz])).le) hO

/-! ### Route check against the frozen Wave 9b `field_rate` -/

/-- Route check: in the setting of the frozen Wave 9b `field_rate` (old `def:standardisable`), together with the
old clause "`S_ν⁻¹` is `L`-Lipschitz on the support of `γ`" (here: on a set of full `γ`-measure), the frozen
conclusion follows from the journal theorem through `stdz_old_to_new`. (The frozen claim dropped that clause, which
its proof does not use; the journal theorem instead drops the Lipschitz property of `Ŝ_ν⁻¹`. Neither Lean statement
is an instance of the other; the journal statement generalises the PAPER's old theorem. Critic's refinement: when
`liminf r_n = 0` the frozen hypotheses already force the old clause — `S_ν⁻¹` is the `L²(γ)`-limit of `L`-Lipschitz
realisations `Ŝ_ν⁻¹(n, ωₙ)`, hence `L`-Lipschitz on a set of full `γ`-measure along an a.e.-convergent subsequence — so
the frozen claim is subsumed there; it is strictly separate only for rates bounded away from `0`.) -/
theorem fieldJ_route_old (d : ℕ) (R : Fin 2 → Measure (Euc d)) (ν γ : Measure (Euc d))
    (S Sinv : Fin 2 → Euc d → Euc d) (Sν Sνinv : Euc d → Euc d) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (Shat : ℕ → Ω → Fin 2 → Euc d → Euc d) (Sνinvhat : ℕ → Ω → Euc d → Euc d) (r : ℕ → ℝ) (L : ℝ≥0)
    (A : Set (Euc d)) (hP : IsProbabilityMeasure P) (hr : ∀ n, 0 ≤ r n)
    (hR : ∀ s, IsProbabilityMeasure (R s)) (hν : IsProbabilityMeasure ν) (hγ : IsProbabilityMeasure γ)
    (hS : ∀ s, Standardises (R s) γ (S s) (Sinv s)) (hSν : Standardises ν γ Sν Sνinv)
    (hShat : ∀ n ω s, Measurable (Shat n ω s)) (hinv : ∀ n ω, Measurable (Sνinvhat n ω))
    (hO : ∀ s, BigOP P r fun n ω => eLpNorm (fun x => Shat n ω s x - S s x) 2 (R s))
    (hOi : BigOP P r (fun n ω => eLpNorm (fun z => Sνinvhat n ω z - Sνinv z) 2 γ))
    (hLip : LipschitzWhp P L Sνinvhat) (hA : γ Aᶜ = 0) (hLA : LipschitzOnWith L Sνinv A) :
    BigOP P r fun n ω => wassersteinEDist 2 ((R 0).map (Sνinvhat n ω ∘ Shat n ω 0))
      ((R 1).map (Sνinvhat n ω ∘ Shat n ω 1)) := by
  obtain ⟨L', hJ⟩ := stdz_old_to_new d γ Sνinv A Ω P Sνinvhat r L hr hA hLA hinv hOi hLip
  exact fieldJ_rate d R ν γ S Sinv Sν Sνinv Ω P Shat Sνinvhat r L' hP hr hR hν hγ hS hSν hShat hinv hO hJ

end StatFormal.Wave30h
