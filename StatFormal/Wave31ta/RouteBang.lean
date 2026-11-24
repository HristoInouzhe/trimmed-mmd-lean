import StatFormal.Wave31ta.Statements
import StatFormal.Wave30tw.Proofs
import StatFormal.Wave30ts.Proofs
import StatFormal.Wave30tl.Proofs
import StatFormal.Archive.Wave30ah.Proofs
import StatFormal.Archive.WaveP1d.Proofs
import StatFormal.Archive.Wave8a.Proofs
import StatFormal.Archive.TrimmedMMD.BangBang.Proofs

/-!
# Wave 31ta — route: `prop:bangbang (v2 short)` and the v2 coupled threshold (untrusted proof material)

* `bangbang_v2`: the certified `Wave30ah.bangbang_set`, `TrimmedMMD.BangBang.bangbang_i`, `bangbang_ii`, `WaveP1d.bangbang_iii`
  at one level `α = β`, with `Wave8a.georep_empirical` (the empirical region is the capped-simplex polytope) and `Wave8a.georep_qp`
  (`D̂² = qp` at a minimiser). `kfloor n α < n ↔ 0 < α` (`n ≥ 1`); at `α = 0` the capped simplex is the uniform vector.
* `tauV2Cpl_facts`: the minimum of three valid thresholds (Wave30tu instance route `valid_min`, `tauA_valid`, `tauP_valid`, Wave30ts
  `coupled_cpl`), continuity and growth from the Wave30tw routes, `CrossingFacts` from `Wave30tw.crossingFacts_of`.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace RealInnerProductSpace Pointwise

namespace StatFormal.Wave31ta.RBang

open StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional
  StatFormal.TrimmedMMD.BangBang StatFormal.TrimmedMMD.Projection StatFormal.Wave4b

/-- `⌊k(1−α)⌋ < k ↔ 0 < α` for `k ≥ 1`, `0 ≤ α < 1`. -/
theorem kfloor_lt_iff {k : ℕ} {α : ℝ} (hk : 1 ≤ k) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    kfloor k α < k ↔ 0 < α := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  constructor
  · intro h
    by_contra hα
    have hα' : α = 0 := le_antisymm (not_lt.1 hα) hα0
    subst hα'
    simp [kfloor] at h
  · intro hα
    unfold kfloor
    rw [Nat.floor_lt (mul_nonneg (by positivity) (by linarith))]
    nlinarith

/-- If `⌊k(1−α)⌋ = k` (so `α = 0`), every point of the capped simplex is at the cap. -/
theorem capped_eq_cap {k : ℕ} {α : ℝ} (hk : 1 ≤ k) (hα0 : 0 ≤ α) (hα1 : α < 1) (hkf : kfloor k α = k)
    {w : Fin k → ℝ} (hw : w ∈ capped k α) : ∀ i, w i = cap k α := by
  have hα : α = 0 := by
    by_contra h
    have := (kfloor_lt_iff hk hα0 hα1).2 (lt_of_le_of_ne hα0 (Ne.symm h))
    omega
  subst hα
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hcap : cap k 0 = 1 / k := by simp [cap]
  have hsum : ∑ i, (cap k 0 - w i) = 0 := by
    rw [Finset.sum_sub_distrib, hw.2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hcap]
    field_simp
    ring
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sub_nonneg.2 (hw.1 i).2)).1 hsum
  intro i
  have := hz i (Finset.mem_univ i)
  linarith

variable {𝒳 H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem qp_eq_witness (φ : 𝒳 → H) {n m : ℕ} (x : Fin n → 𝒳) (y : Fin m → 𝒳) (p : (Fin n → ℝ) × (Fin m → ℝ)) :
    qp (fun i => φ (x i)) (fun j => φ (y j)) p = ‖witness φ x y p‖ ^ 2 := rfl

end StatFormal.Wave31ta.RBang

namespace StatFormal.Wave31ta

open StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Concentration StatFormal.TrimmedMMD.Unconditional
  StatFormal.TrimmedMMD.BangBang StatFormal.TrimmedMMD.Projection StatFormal.Wave4b StatFormal.Wave31ta.RBang

theorem bangbang_v2 : Claims.bangbang_v2 := by
  intro 𝒳 H _ _ _ _ φ α n m x y hφ hα0 hα1 hn hm T
  have hn' : 0 < n := hn
  have hm' : 0 < m := hm
  set xs : Fin n → H := fun i => φ (x i) with hxs
  set ys : Fin m → H := fun j => φ (y j) with hys
  -- the set of minimisers
  have hset := StatFormal.Wave30ah.bangbang_set H n m xs ys α α hn' hm' hα0 hα1 hα0 hα1
  obtain ⟨-, huniq⟩ := bangbang_i H n m xs ys α α hn' hm' hα0 hα1 hα0 hα1
  obtain ⟨p0, hp0, hmin0', hD0'⟩ := StatFormal.Wave8a.georep_qp 𝒳 H φ α n m x y hφ hα0 hα1 hn' hm'
  have hmin0 : IsMinOn (qp xs ys) (capped n α ×ˢ capped m α) p0 := hmin0'
  have hD0 : Demp φ x y α ^ 2 = qp xs ys p0 := hD0'
  have hregx := StatFormal.Wave8a.georep_empirical 𝒳 H φ α n x hφ hα0 hα1 hn'
  have hregy := StatFormal.Wave8a.georep_empirical 𝒳 H φ α m y hφ hα0 hα1 hm'
  have hDnn := StatFormal.Wave30tl.Demp_nonneg φ x y α
  -- every minimiser has `‖d̂‖ = D̂`
  have hnormD : ∀ p ∈ T, ‖witness φ x y p‖ = Demp φ x y α := by
    intro p hp
    have h1 : qp xs ys p ≤ qp xs ys p0 := hp.2 hp0
    have h2 : qp xs ys p0 ≤ qp xs ys p := hmin0 hp.1
    have heq : ‖witness φ x y p‖ ^ 2 = Demp φ x y α ^ 2 := by
      rw [hD0]; exact le_antisymm h1 h2
    exact (pow_left_inj₀ (norm_nonneg _) hDnn two_ne_zero).1 heq
  refine ⟨hset, fun p hp => ⟨⟨?_, ?_⟩, hnormD p hp⟩, fun p hp p' hp' => huniq p hp.1 p' hp'.1 hp.2 hp'.2,
    fun hpos p hp => ?_, fun hz => ?_⟩
  · -- membership in the difference of the regions
    rw [hregx, hregy]
    exact ⟨_, ⟨p.1, hp.1.1, rfl⟩, _, ⟨p.2, hp.1.2, rfl⟩, rfl⟩
  · -- minimal norm
    rw [hregx, hregy]
    rintro z ⟨a, ⟨w, hw, rfl⟩, b, ⟨v, hv, rfl⟩, rfl⟩
    have hle : qp xs ys p ≤ qp xs ys (w, v) := hp.2 (show (w, v) ∈ capped n α ×ˢ capped m α from ⟨hw, hv⟩)
    rw [qp_eq_witness, qp_eq_witness] at hle
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hle
  · -- (ii)
    have hqp : 0 < qp xs ys p := by
      rw [qp_eq_witness, hnormD p hp]; positivity
    refine ⟨fun hk => ?_, fun hk => capped_eq_cap hn hα0 hα1 hk hp.1.1, fun hk => ?_,
      fun hk => capped_eq_cap hm hα0 hα1 hk hp.1.2⟩
    · have hkm : kfloor m α < m := (kfloor_lt_iff hm hα0 hα1).2 ((kfloor_lt_iff hn hα0 hα1).1 hk)
      obtain ⟨h1, h2, h3, -, -, -⟩ :=
        bangbang_ii H n m xs ys α α p hn' hm' hα0 hα1 hα0 hα1 hk hkm hp.1 hp.2 hqp
      exact ⟨h1, h2, h3⟩
    · have hkn : kfloor n α < n := (kfloor_lt_iff hn hα0 hα1).2 ((kfloor_lt_iff hm hα0 hα1).1 hk)
      obtain ⟨-, -, -, h4, h5, h6⟩ :=
        bangbang_ii H n m xs ys α α p hn' hm' hα0 hα1 hα0 hα1 hkn hk hp.1 hp.2 hqp
      exact ⟨h4, h5, h6⟩
  · -- (iii)
    have hq0 : qp xs ys p0 = 0 := by rw [← hD0, hz]; ring
    exact StatFormal.WaveP1d.bangbang_iii H n m xs ys α α p0 hn' hm' hα0 hα1 hα0 hα1 hp0 hmin0 hq0

theorem tauV2Cpl_facts : Claims.tauV2Cpl_facts := by
  intro 𝒳 H _ _ _ _ _ φ κ D δ n m hne hφ hκ hD hk0 hdiag hδ0 hδ1 hn hm
  obtain ⟨x0⟩ := hne
  obtain ⟨hκ0, hD0⟩ := StatFormal.Wave30tu.Instance.consts_nonneg hκ hD x0
  have hA := StatFormal.Wave30tu.Instance.tauA_valid hφ hκ hD x0 hδ0 hδ1 hn hm
  have hP := StatFormal.Wave30tu.Instance.tauP_valid hφ hκ hD x0 hδ0 hδ1 hn hm
  obtain ⟨hCv, hCm, hCn, -⟩ :=
    StatFormal.Wave30ts.coupled_cpl 𝒳 H φ κ D δ n m hφ hκ hD hk0 hdiag hD0 hδ0 hδ1 hn hm
  have hC : StatFormal.Wave30tu.ValidThreshold φ n m δ (fun α => StatFormal.Wave30ts.tauCpl D κ α δ n m) :=
    ⟨hCn, hCm, hCv⟩
  have hV : StatFormal.Wave30tu.ValidThreshold φ n m δ (fun α => tauV2Cpl κ D α δ n m) :=
    StatFormal.Wave30tu.Instance.valid_min hA (StatFormal.Wave30tu.Instance.valid_min hP hC)
  have hcont : ContinuousOn (fun α => tauV2Cpl κ D α δ n m) (Ioo 0 1) :=
    (StatFormal.Wave30tu.Instance.tauA_continuousOn κ D δ n m).inf
      ((StatFormal.Wave30tu.Instance.tauP_continuousOn _ _ _ δ n m).inf
        (StatFormal.Wave30tw.tauCpl_continuousOn hD0 hδ0 hδ1 hn hm))
  have htend : 0 < D → 0 < κ → Tendsto (fun α => tauV2Cpl κ D α δ n m) (𝓝[<] 1) atTop := fun hDp hκp =>
    StatFormal.Wave30tw.tendsto_min_atTop (StatFormal.Wave30tw.tauA_tendsto hκ0 hDp hδ0 hδ1 hn hm)
      (StatFormal.Wave30tw.tendsto_min_atTop (StatFormal.Wave30tw.tauP_tendsto hDp hD0 hδ0 hδ1 hn hm)
        ((StatFormal.Wave30tw.tauCpl_tendsto_iff hD0 hδ0 hδ1 hn hm).2 hκp.ne'))
  refine ⟨hV, fun α _ => min_le_left _ _, fun h2κ α hα => (min_le_left _ _).trans
    (StatFormal.Wave30tr.thmA_compare κ D α δ n m hD0 h2κ hα.1 hα.2 hδ0 hδ1 hn hm), hcont, htend, ?_⟩
  refine StatFormal.Wave30tw.crossingFacts_of hφ hκ hn hm fun _ => ⟨hV.1, hV.2.1, hcont, fun hc => ?_⟩
  obtain ⟨hDp, hκp⟩ := StatFormal.Wave30tw.consts_pos_of_nonconst hκ hD hc
  exact htend hDp hκp

end StatFormal.Wave31ta
