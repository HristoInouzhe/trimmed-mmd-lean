import StatFormal.Wave31to.RouteC
import StatFormal.Wave31tl.RouteClaims
import StatFormal.Wave30tu.RouteMain
import StatFormal.Wave30tu.Full.Route
import StatFormal.Wave30tr.Proofs
import StatFormal.Wave30tr.RouteConst
import StatFormal.Archive.TrimmedMMD.ZeroSet.Proofs
import StatFormal.Wave30tz.RouteLower

/-!
# Route D (untrusted): `prop:newrates` (i), (ii) and `prop:newconverse`

* (i): on `E⁰ ∩ E⁻` (certified `Wave30tu.oneevent`, the `LowerTool` event), `α⋆` is in the crossing set and, for every
  `ε ∈ (ω^←(t), α⋆]`, `ω(ε) > t` and no level `α ≤ α⋆ − ε` crosses (antitone `D`, monotone `τ`, `τ^A`).
* (ii-a): the route `Wave31tl.Core.core_lower` with `D_* = ω(ε)` and `x_j = (α⋆ − α_j)/ε`, the profile bound from the monotone ratio
  of the certified `Wave31ti.pathconvex_ii`, the packing sum `Wave31tl.Basic.sum_exp_le_Jeps`.
* (ii-b): `core_lower` at `x_j = 1` for each `ε ∈ (ω^←(t), α⋆]`, continuity from below (`Monotone.measure_iUnion`), the route
  `Wave31tl.Route.two_sided` (validity, certified `Wave30tz.lo_upper`).
* converse: `E⁺` of the certified `Wave30tr.thmA` at `δ′`; `τ^A(·,δ) − τ^A(·,δ′) ≥ g_{n,m}`.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace

namespace StatFormal.Wave31to.RouteD

open StatFormal.TrimmedMMD StatFormal.TrimmedMMD.Unconditional StatFormal.Distances StatFormal.Wave30tu
  StatFormal.Wave30tq StatFormal.Wave30tp StatFormal.Wave30tz StatFormal.Wave31tl StatFormal.Wave31to.RouteB

/-! ### The generalised inverse -/

section GenInv

variable {ω : ℝ → ℝ} {αs t : ℝ}

theorem genInv_bdd : BddAbove {e | e ∈ Icc (0 : ℝ) αs ∧ ω e ≤ t} := ⟨αs, fun _ he => he.1.2⟩

theorem genInv_nonneg (hαs : 0 ≤ αs) (h0 : ω 0 ≤ t) : 0 ≤ genInv ω αs t :=
  le_csSup genInv_bdd ⟨⟨le_rfl, hαs⟩, h0⟩

theorem genInv_le (hαs : 0 ≤ αs) (h0 : ω 0 ≤ t) : genInv ω αs t ≤ αs :=
  csSup_le ⟨0, ⟨le_rfl, hαs⟩, h0⟩ fun _ he => he.1.2

theorem lt_of_genInv_lt (hαs : 0 ≤ αs) (h0 : ω 0 ≤ t) {e : ℝ} (he : genInv ω αs t < e) (heα : e ≤ αs) :
    t < ω e := by
  by_contra h
  have he0 : 0 ≤ e := (genInv_nonneg hαs h0).trans he.le
  have : e ≤ genInv ω αs t := le_csSup genInv_bdd ⟨⟨he0, heα⟩, not_lt.1 h⟩
  linarith

end GenInv

/-! ### (i) -/

theorem newrates_i_route : Claims.newrates_i := by
  intro X K _ _ _ _ _ P Q _ _ φ κ δ δ' τ τA ω n m hφ hκ hα1 hmono hω0 hωD hδ0 hδ1 hδ'0 hδ'1 hn hm hτ hτA
  set αs := tvDist P Q with hαsdef
  have hαs0 : 0 ≤ αs := tvDist_nonneg P Q
  obtain ⟨hmeas0, hprob0, -⟩ := StatFormal.Wave30tu.oneevent X K P Q φ κ δ τ n m hφ hκ hδ0 hδ1 hn hm hτ hα1
  have hτ' := hτ
  obtain ⟨hτA0, hτAm, E', hE'm, hE'p, hE'⟩ := hτA
  obtain ⟨hτ0, hτm, -⟩ := hτ'
  refine ⟨{z | Demp φ z.1 z.2 αs ≤ τ αs} ∩ E', hmeas0.inter hE'm, ?_, ?_⟩
  · have := inter_prob (μ := (Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin m => Q)) hmeas0 hE'm
      hδ0.le hδ'0.le hprob0 hE'p
    exact this
  · rintro z ⟨hz0, hz'⟩
    set t := τ αs + τA αs
    have hmemα : αs ∈ crossSet (Demp φ z.1 z.2) τ := ⟨⟨hαs0, hα1⟩, hz0⟩
    have hne : (crossSet (Demp φ z.1 z.2) τ).Nonempty := ⟨αs, hmemα⟩
    refine ⟨?_, alphaHat_le_of_mem hmemα⟩
    have hD0 : Dpop φ P Q αs = 0 :=
      StatFormal.TrimmedMMD.ZeroSet.zero_of_tv_le X K P Q φ κ αs hφ hκ hαs0 hα1 le_rfl
    have ht0 : 0 ≤ t := add_nonneg (hτ0 αs ⟨hαs0, hα1⟩) (hτA0 αs ⟨hαs0, hα1⟩)
    have hω00 : ω 0 ≤ t := by
      have := hωD 0 ⟨le_rfl, hαs0⟩
      rw [sub_zero, hD0] at this; linarith
    have hkey : ∀ e, genInv ω αs t < e → e ≤ αs → αs - e ≤ alphaHat (Demp φ z.1 z.2) τ := by
      intro e he heα
      have hωe : t < ω e := lt_of_genInv_lt hαs0 hω00 he heα
      have he0 : 0 < e := lt_of_le_of_lt (genInv_nonneg hαs0 hω00) he
      refine le_csInf hne ?_
      intro a ha
      by_contra hlt
      have hlt' : a < αs - e := not_le.1 hlt
      obtain ⟨⟨ha0, ha1⟩, hDa⟩ := ha
      have h1 := hE' z hz' a ⟨ha0, ha1⟩
      have h2 : Dpop φ P Q (αs - e) ≤ Dpop φ P Q a :=
        StatFormal.Wave30tz.dpop_antitone X K φ κ P Q a (αs - e) hφ hκ ha0 hlt'.le (by linarith)
      have h3 : τA a ≤ τA αs := hτAm ⟨ha0, ha1⟩ ⟨hαs0, hα1⟩ (by linarith)
      have h4 : τ a ≤ τ αs := hτm ⟨ha0, ha1⟩ ⟨hαs0, hα1⟩ (by linarith)
      have h5 := hωD e ⟨he0.le, heα⟩
      linarith
    have hG := genInv_le hαs0 hω00 (ω := ω)
    rcases eq_or_lt_of_le hG with hGe | hGlt
    · rw [hGe, sub_self]; exact alphaHat_nonneg hne
    · by_contra h
      have h' : alphaHat (Demp φ z.1 z.2) τ < αs - genInv ω αs t := not_le.1 h
      have hah0 := alphaHat_nonneg hne
      set e := (genInv ω αs t + (αs - alphaHat (Demp φ z.1 z.2) τ)) / 2
      have := hkey e (by simp only [e]; linarith) (by simp only [e]; linarith)
      simp only [e] at this
      linarith

theorem newrates_i_full_route : Claims.newrates_i_full := by
  intro X K _ _ _ _ _ P Q _ _ φ κ D δ δ' ω n m hφ hκ hD hα1 hmono hω0 hωD hδ0 hδ1 hδ'0 hδ'1 hn hm
  obtain ⟨x0⟩ := nonempty_of_isProbabilityMeasure P
  have hκ0 : 0 ≤ κ := (norm_nonneg _).trans (hκ x0)
  have hD0 : 0 ≤ D := by simpa using hD x0 x0
  have hvalid := (StatFormal.Wave30tu.Full.tauFull_threshold X K φ κ D δ n m ⟨x0⟩ hφ hκ hD hδ0 hδ1 hn hm).1
  obtain ⟨-, hmonoA, hnonnegA⟩ := StatFormal.Wave30tr.tauA_scale κ D δ' n m hκ0 hD0 hδ'0 hδ'1 hn hm
  obtain ⟨-, Em, -, -, hEmm, hEmp, -, hEm⟩ := StatFormal.Wave30tr.thmA X K φ κ D P Q δ' n m hφ hκ hD hδ'0 hδ'1 hn hm
  have hlow : LowerTool φ P Q n m δ' (fun α => StatFormal.Wave30tr.tauA κ D α δ' n m) :=
    ⟨hnonnegA, hmonoA, Em, hEmm, hEmp, hEm⟩
  have := newrates_i_route X K P Q φ κ δ δ' (fun α => StatFormal.Wave30tu.Full.tauFull κ D α δ n m)
    (fun α => StatFormal.Wave30tr.tauA κ D α δ' n m) ω n m hφ hκ hα1 hmono hω0 hωD hδ0 hδ1 hδ'0 hδ'1 hn hm hvalid hlow
  beta_reduce at this
  exact this

/-! ### (ii) -/

theorem u_le_D {X : Type} [MeasurableSpace X] {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    [CompleteSpace K] (φ : X → K) (P Q : Measure X) {a : ℝ} (ha : 0 ≤ a) : StatFormal.Wave31ti.uPath φ P Q a ≤ Dpop φ P Q a := by
  unfold StatFormal.Wave31ti.uPath
  have := dpop_nonneg φ P Q a
  nlinarith

theorem newrates_ii_a_route : Claims.newrates_ii_a := by
  intro X K _ _ _ _ _ φ κ Dφ P Q _ _ ω J n m α δ s2 η h0 ε R B hφ hκ hDφ hD2 hκpos hmono hω0 hωu hαs1 hgrid hJ
    hδ0 hδ1 hs20 hs24 hRun hB hn1 hm1 hr1 hN hη0 hη1 hh0 hgap hε hεα hcond
  classical
  set αs := tvDist P Q
  have hαs0 : 0 < αs := hε.trans_le hεα
  have hβ0 : 0 ≤ beta αs := by
    unfold beta
    have : 0 < 1 - αs := by linarith
    positivity
  have hJeps : 1 ≤ Jeps J ε h0 := by
    unfold Jeps
    refine le_min (by exact_mod_cast hJ) ?_
    have : 0 ≤ ε / h0 := by positivity
    linarith
  obtain ⟨x0⟩ := nonempty_of_isProbabilityMeasure P
  have hDφ0 : 0 ≤ Dφ := by simpa using hDφ x0 x0
  have hn1r : (0 : ℝ) < fitCard R.lx 1 := by exact_mod_cast hn1
  have hm1r : (0 : ℝ) < fitCard R.ly 1 := by exact_mod_cast hm1
  have hr10 : 0 < rOne R.lx R.ly := by unfold rOne; positivity
  have hβ1 : 1 ≤ beta αs := Core.one_le_beta' hαs0.le hαs1
  have hDs : 0 < ω ε := lt_of_lt_of_le (mul_pos (by linarith)
    (lt_of_lt_of_le (Route.Tfit_pos hκpos hDφ0 hr10) (le_max_left _ _))) hcond
  have hpc := StatFormal.Wave31ti.pathconvex_ii X K P Q φ κ hφ hκ hαs0 hαs1
  refine Core.core_lower P Q hφ hκ hDφ hD2 hgrid hδ0 hδ1 hs20 hs24 hRun hB hn1 hm1 hr1 hN hη0 hη1
    (αs := αs) (a := αs - ε) (Ds := ω ε) (J' := Jeps J ε h0) (fun j => (αs - α j) / ε) hαs1 (by linarith)
    hDs ?_ hJeps
    ((mul_le_mul_of_nonneg_left (le_max_left _ _) hβ0).trans hcond)
    ((mul_le_mul_of_nonneg_left (le_max_right _ _) hβ0).trans hcond) ?_
  · intro j hj
    have hαj0 : 0 ≤ α j := (hgrid.2 j).1
    have hx1 : 1 ≤ (αs - α j) / ε := by rw [le_div_iff₀ hε]; linarith
    refine ⟨hx1, ?_⟩
    have hratio0 := hpc.1 (⟨hε, hεα⟩ : ε ∈ Ioc 0 αs) (⟨by linarith, by linarith⟩ : αs - α j ∈ Ioc 0 αs)
      (by linarith : ε ≤ αs - α j)
    have hratio : StatFormal.Wave31ti.uPath φ P Q (αs - ε) / ε ≤
        StatFormal.Wave31ti.uPath φ P Q (α j) / (αs - α j) := by
      have e1 : tvDist P Q - (αs - α j) = α j := by simp only [αs]; ring
      simp only at hratio0
      rw [e1] at hratio0
      exact hratio0
    have hωle := hωu ε ⟨hε.le, hεα⟩
    have hpos : 0 < αs - α j := by linarith
    calc ω ε * ((αs - α j) / ε)
        ≤ StatFormal.Wave31ti.uPath φ P Q (αs - ε) * ((αs - α j) / ε) :=
          mul_le_mul_of_nonneg_right hωle (by linarith)
      _ = StatFormal.Wave31ti.uPath φ P Q (αs - ε) / ε * (αs - α j) := by ring
      _ ≤ StatFormal.Wave31ti.uPath φ P Q (α j) / (αs - α j) * (αs - α j) :=
          mul_le_mul_of_nonneg_right hratio hpos.le
      _ = StatFormal.Wave31ti.uPath φ P Q (α j) := div_mul_cancel₀ _ hpos.ne'
      _ ≤ Dpop φ P Q (α j) := u_le_D φ P Q hαj0
  · intro A hA
    have hA2 : Real.log 2 ≤ A := le_trans (Real.log_le_log (by norm_num) (by
      rw [le_div_iff₀ hη0]; nlinarith)) hA
    exact Basic.sum_exp_le_Jeps hgap hh0 hε hA2

theorem newrates_ii_b_route : Claims.newrates_ii_b := by
  intro X K _ _ _ _ _ φ κ Dφ P Q _ _ ω J n m α δ s2 η h R B hφ hκ hDφ hD2 hmono hω0 hωu hαs1 hgrid hJ hδ0 hδ1
    hs20 hs24 hRun hB hn1 hm1 hr1 hN hη0 hη1 hmesh
  classical
  set αs := tvDist P Q with hαsdef
  set t := tNM κ Dφ αs s2 δ η (rOne R.lx R.ly) B J R.N with htdef
  set G := genInv ω αs t with hGdef
  refine Route.two_sided P Q hgrid hδ0 hδ1 hη0.le (by norm_num) (by norm_num) hRun.1 ?_
  by_cases hlow : αs - h - G ≤ 0
  · exact Route.lower_trivial P Q R hgrid hlow
  have hlow' : 0 < αs - h - G := not_le.1 hlow
  have hαs0 : 0 ≤ αs := tvDist_nonneg P Q
  have hh0 : 0 ≤ h := Basic.mesh_nonneg α hmesh hαs0
  obtain ⟨x0⟩ := nonempty_of_isProbabilityMeasure P
  have hDφ0 : 0 ≤ Dφ := by simpa using hDφ x0 x0
  have hβ1 : 1 ≤ beta αs := Core.one_le_beta' hαs0 hαs1
  have hκ0 : 0 ≤ κ := (norm_nonneg _).trans (hκ x0)
  have hn1r : (0 : ℝ) < fitCard R.lx 1 := by exact_mod_cast hn1
  have hm1r : (0 : ℝ) < fitCard R.ly 1 := by exact_mod_cast hm1
  have hr10 : 0 < rOne R.lx R.ly := by unfold rOne; positivity
  have hTfit0 : 0 ≤ Tfit κ Dφ η (rOne R.lx R.ly) B := by unfold Tfit; positivity
  have hβ0 : 0 ≤ beta αs := by linarith
  have ht0 : 0 ≤ t := by rw [htdef]; unfold tNM; exact mul_nonneg hβ0 (hTfit0.trans (le_max_left _ _))
  have hD0 : Dpop φ P Q αs = 0 :=
    StatFormal.TrimmedMMD.ZeroSet.zero_of_tv_le X K P Q φ κ αs hφ hκ hαs0 hαs1 le_rfl
  have hω00 : ω 0 ≤ t := by
    have := hωu 0 ⟨le_rfl, hαs0⟩
    unfold StatFormal.Wave31ti.uPath at this
    rw [sub_zero, hD0, mul_zero] at this; linarith
  have hG0 : 0 ≤ G := genInv_nonneg hαs0 hω00
  have hJr : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  -- one level
  have hstep : ∀ e, G < e → e ≤ αs →
      sampleLaw P Q n m {z | R.alphaLo α δ z.1 z.2 < αs - h - e} ≤ ENNReal.ofReal η := by
    intro e he heα
    have hωe : t < ω e := lt_of_genInv_lt hαs0 hω00 he heα
    have hDs : 0 < ω e := lt_of_le_of_lt ht0 hωe
    have he0 : 0 ≤ e := hG0.trans he.le
    have hfitc : beta αs * Tfit κ Dφ η (rOne R.lx R.ly) B ≤ ω e := by
      refine le_trans ?_ hωe.le
      rw [htdef]; unfold tNM; exact mul_le_mul_of_nonneg_left (le_max_left _ _) hβ0
    have hbetc : beta αs * Tbet Dφ s2 (Real.log (1 / δ)) η (J : ℝ) R.N ≤ ω e := by
      refine le_trans ?_ hωe.le
      rw [htdef]; unfold tNM; exact mul_le_mul_of_nonneg_left (le_max_right _ _) hβ0
    have hsum : ∀ A : ℝ, Real.log (2 * (J : ℝ) / η) ≤ A →
        ∑ j ∈ Finset.univ.filter (fun j => α j ≤ αs - e), Real.exp (-(A * (fun _ : Fin J => (1 : ℝ)) j ^ 2)) ≤
          (J : ℝ) * Real.exp (-A) := by
      intro A _
      simp only [one_pow, mul_one]
      rw [Finset.sum_const, nsmul_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
    have hDj : ∀ j, α j ≤ αs - e → ω e * (fun _ : Fin J => (1 : ℝ)) j ≤ Dpop φ P Q (α j) := by
      intro j hj
      have hαj0 : 0 ≤ α j := (hgrid.2 j).1
      rw [mul_one]
      calc ω e ≤ StatFormal.Wave31ti.uPath φ P Q (αs - e) := hωu e ⟨he0, heα⟩
        _ ≤ Dpop φ P Q (αs - e) := u_le_D φ P Q (by linarith)
        _ ≤ Dpop φ P Q (α j) := StatFormal.Wave30tz.dpop_antitone X K φ κ P Q (α j) (αs - e) hφ hκ hαj0 hj
            (by linarith)
    have hcore := Core.core_lower P Q hφ hκ hDφ hD2 hgrid hδ0 hδ1 hs20 hs24 hRun hB hn1 hm1 hr1 hN hη0 hη1
      (αs := αs) (a := αs - e) (Ds := ω e) (J' := (J : ℝ)) (fun _ => 1) hαs1 (by linarith) hDs
      (fun j hj => ⟨le_rfl, hDj j hj⟩) hJr hfitc hbetc hsum
    refine le_trans (measure_mono fun z hz => ?_) hcore
    simp only [mem_setOf_eq] at hz ⊢
    have := Basic.floor_ge_of_mesh α hmesh he0 heα
    linarith
  -- continuity from below along `e_k = G + (α⋆ − G)/(k+2)`
  have hGlt : G < αs := by linarith
  set e : ℕ → ℝ := fun k => G + (αs - G) / ((k : ℝ) + 2) with hedef
  have hepos : ∀ k : ℕ, 0 < (αs - G) / ((k : ℝ) + 2) := fun k => by
    have : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    exact div_pos (by linarith) this
  have hele : ∀ k : ℕ, (αs - G) / ((k : ℝ) + 2) ≤ αs - G := fun k => by
    have h1 : (1 : ℝ) ≤ (k : ℝ) + 2 := by have := Nat.cast_nonneg (α := ℝ) k; linarith
    exact div_le_self (by linarith) h1
  have hunion : {z : (Fin n → X) × (Fin m → X) | R.alphaLo α δ z.1 z.2 < αs - h - G} =
      ⋃ k : ℕ, {z : (Fin n → X) × (Fin m → X) | R.alphaLo α δ z.1 z.2 < αs - h - e k} := by
    ext z
    simp only [mem_setOf_eq, mem_iUnion, e]
    constructor
    · intro hz
      set d := αs - h - G - R.alphaLo α δ z.1 z.2
      have hd : 0 < d := by simp only [d]; linarith
      obtain ⟨k, hk⟩ := exists_nat_gt ((αs - G) / d)
      refine ⟨k, ?_⟩
      have hk2 : (αs - G) / d < (k : ℝ) + 2 := by linarith
      have : (αs - G) / ((k : ℝ) + 2) < d := by
        rw [div_lt_iff₀ (by positivity)]
        rw [div_lt_iff₀ hd] at hk2
        linarith
      simp only [d] at this
      linarith
    · rintro ⟨k, hk⟩
      linarith [hepos k]
  have hmono_sets : Monotone (fun k : ℕ => {z : (Fin n → X) × (Fin m → X) | R.alphaLo α δ z.1 z.2 < αs - h - e k}) := by
    intro k l hkl z hz
    simp only [mem_setOf_eq, e] at hz ⊢
    have hkl' : ((k : ℝ) + 2) ≤ (l : ℝ) + 2 := by exact_mod_cast Nat.add_le_add_right hkl 2
    have : (αs - G) / ((l : ℝ) + 2) ≤ (αs - G) / ((k : ℝ) + 2) :=
      div_le_div_of_nonneg_left (by linarith) (by positivity) hkl'
    linarith
  rw [hunion, hmono_sets.measure_iUnion]
  exact iSup_le fun k => hstep (e k) (by simp only [e]; linarith [hepos k]) (by simp only [e]; linarith [hele k])

/-! ### `prop:newconverse` -/

theorem newconverse_route : Claims.newconverse := by
  intro X K _ _ _ _ _ P Q _ _ φ κ D δ δ' n m hφ hκ hD hα1 hδ0 hδδ' hδ'1 hn hm
  set αs := tvDist P Q
  have hαs0 : 0 ≤ αs := tvDist_nonneg P Q
  obtain ⟨x0⟩ := nonempty_of_isProbabilityMeasure P
  have hD0 : 0 ≤ D := by simpa using hD x0 x0
  have hδ'0 : 0 < δ' := hδ0.trans hδδ'
  have hL : Real.log (1 / δ') ≤ Real.log (1 / δ) :=
    Real.log_le_log (by positivity) (one_div_le_one_div_of_le hδ0 hδδ'.le)
  have hL'0 : 0 ≤ Real.log (1 / δ') := Real.log_nonneg (by rw [le_div_iff₀ hδ'0]; linarith)
  have hg0 : 0 ≤ gNM D δ δ' n m := by
    unfold gNM
    exact mul_nonneg (mul_nonneg hD0 (Real.sqrt_nonneg _)) (sub_nonneg.2 (Real.sqrt_le_sqrt hL))
  have hDz : Dpop φ P Q αs = 0 :=
    StatFormal.TrimmedMMD.ZeroSet.zero_of_tv_le X K P Q φ κ αs hφ hκ hαs0 hα1 le_rfl
  refine ⟨by rw [hDz]; exact hg0, ?_⟩
  obtain ⟨Ep, -, hEpm, hEpp, -, -, hEp, -⟩ :=
    StatFormal.Wave30tr.thmA X K φ κ D P Q δ' n m hφ hκ hD hδ'0 hδ'1 hn hm
  refine ⟨Ep, hEpm, hEpp, fun z hz ε hε hDε => ?_⟩
  set a := αs - ε
  have ha0 : 0 ≤ a := by simp only [a]; linarith [hε.2]
  have ha1 : a < 1 := by simp only [a]; linarith [hε.1]
  have h1 := (hEp z hz a ⟨ha0, ha1⟩).1
  have hs0 : 0 ≤ sNM n m := by unfold sNM; positivity
  have hdiff : gNM D δ δ' n m ≤ StatFormal.Wave30tr.tauA κ D a δ n m - StatFormal.Wave30tr.tauA κ D a δ' n m := by
    unfold StatFormal.Wave30tr.tauA gNM
    have e1 : √(sNM n m * Real.log (1 / δ) / 2) = √(sNM n m / 2) * √(Real.log (1 / δ)) := by
      rw [← Real.sqrt_mul (by positivity)]; congr 1; ring
    have e2 : √(sNM n m * Real.log (1 / δ') / 2) = √(sNM n m / 2) * √(Real.log (1 / δ')) := by
      rw [← Real.sqrt_mul (by positivity)]; congr 1; ring
    rw [e1, e2]
    have hs : (1 / (n : ℝ) + 1 / (m : ℝ)) = sNM n m := rfl
    rw [hs]
    set g := D * √(sNM n m / 2) * (√(Real.log (1 / δ)) - √(Real.log (1 / δ')))
    have hg : 0 ≤ g := by
      simp only [g]
      exact mul_nonneg (mul_nonneg hD0 (Real.sqrt_nonneg _)) (sub_nonneg.2 (Real.sqrt_le_sqrt hL))
    have hb : 1 ≤ 1 / (1 - a) := by rw [le_div_iff₀ (by linarith)]; linarith
    have : 1 / (1 - a) * (2 * κ * √(sNM n m) + 2 * κ * (StatFormal.Wave30tr.ek n + StatFormal.Wave30tr.ek m) +
          D * (√(sNM n m / 2) * √(Real.log (1 / δ)))) -
        1 / (1 - a) * (2 * κ * √(sNM n m) + 2 * κ * (StatFormal.Wave30tr.ek n + StatFormal.Wave30tr.ek m) +
          D * (√(sNM n m / 2) * √(Real.log (1 / δ')))) = 1 / (1 - a) * g := by
      simp only [g]; ring
    rw [this]
    nlinarith
  have hmem : a ∈ crossSet (Demp φ z.1 z.2) (fun α => StatFormal.Wave30tr.tauA κ D α δ n m) :=
    ⟨⟨ha0, ha1⟩, by simp only; linarith⟩
  have := alphaHat_le_of_mem hmem
  simp only [a] at this
  linarith

end StatFormal.Wave31to.RouteD
