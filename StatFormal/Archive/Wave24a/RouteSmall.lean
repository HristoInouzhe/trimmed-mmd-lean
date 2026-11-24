import StatFormal.Archive.Wave24a.Statements

/-!
# Route — B `prop:jensen`, TM `prop:sinkmono`, A `cor:app-hard-envelope` (untrusted)

* `jensen`: Jensen's inequality `ConvexOn.map_sum_le` for the weights `π_ij/α_i` (nonnegative, summing to one).
* `sinkmono`: `1/(1 − α)` is nondecreasing on `[0,1)`, so the caps nest; an infimum over a larger set is smaller.
* `app_hard_envelope`: the paper's construction `K*_n = r` on `[N_r, N_{r+1})`, with `N_r` chosen so that
  `max_{K ≤ r} A_K(n) ≤ 1/(r+1)` for `n ≥ N_r`.
-/

noncomputable section
open MeasureTheory Set Filter Topology Finset
open scoped ENNReal

namespace StatFormal.Wave24a

theorem jensen : Claims.jensen := by
  intro E _ _ n m g π α u hg hπ hrow hα i
  have hw0 : ∀ j ∈ (Finset.univ : Finset (Fin m)), 0 ≤ π i j / α i := fun j _ => div_nonneg (hπ i j) (hα i).le
  have hw1 : ∑ j, π i j / α i = 1 := by
    rw [← Finset.sum_div, hrow i, div_self (hα i).ne']
  have h := hg.map_sum_le hw0 hw1 (fun j _ => Set.mem_univ (u j))
  simp only [smul_eq_mul] at h
  linarith

theorem trimSet_mono : Claims.trimSet_mono := by
  intro X _ P α α' h0 hαα' h1 Q ⟨hQ, hac, hle⟩
  refine ⟨hQ, hac, hle.mono fun x hx => hx.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  exact one_div_le_one_div_of_le (by linarith) (by linarith)

theorem sinkmono : Claims.sinkmono := by
  intro X _ Δ P Q _ _ α hα α' hα' hαα'
  simp only [trimmedDisc]
  refine iInf₂_mono' fun P' hP' => ⟨P', trimSet_mono X P α α' hα.1 hαα' hα'.2 hP', ?_⟩
  exact iInf₂_mono' fun Q' hQ' => ⟨Q', trimSet_mono X Q α α' hα.1 hαα' hα'.2 hQ', le_rfl⟩

/-! ### The envelope lemma -/

/-- `M_r(n) = max_{K ≤ r} A_K(n)` tends to `0`. -/
lemma tendsto_sup_range (A : ℕ → ℕ → ℝ) (hA : ∀ K, Tendsto (A K) atTop (𝓝 0)) (r : ℕ) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ K ≤ r, A K n ≤ ε := by
  intro ε hε
  have : ∀ K ∈ Finset.range (r + 1), ∀ᶠ n in atTop, A K n ≤ ε := fun K _ =>
    (hA K).eventually (ge_mem_nhds hε)
  have h := (Filter.eventually_all_finset _).2 this
  filter_upwards [h] with n hn K hK
  exact hn K (Finset.mem_range.2 (Nat.lt_succ_of_le hK))

theorem app_hard_envelope : Claims.app_hard_envelope := by
  intro A S hA hS
  -- `N r`: from `N r` on, `A_K(n) ≤ 1/(r+1)` for all `K ≤ r`; made strictly increasing
  have hN : ∀ r : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∀ K ≤ r, A K n ≤ 1 / ((r : ℝ) + 1) := fun r =>
    Filter.eventually_atTop.1 (tendsto_sup_range A hA r _ (by positivity))
  choose N0 hN0 using hN
  -- strictly increasing version
  let N : ℕ → ℕ := fun r => (∑ k ∈ Finset.range (r + 1), N0 k) + r
  have hNmono : StrictMono N := by
    refine strictMono_nat_of_lt_succ fun r => ?_
    simp only [N, Finset.sum_range_succ]
    omega
  have hNge : ∀ r, N0 r ≤ N r := fun r => by
    simp only [N]
    have := Finset.single_le_sum (f := N0) (fun _ _ => Nat.zero_le _) (Finset.self_mem_range_succ r)
    omega
  -- `K*_n = max{r : N r ≤ n}` (`0` if none)
  classical
  let Kstar : ℕ → ℕ := fun n => ((Finset.range (n + 1)).filter fun r => N r ≤ n).sup id
  have hNr : ∀ r, r ≤ N r := fun r => hNmono.id_le r
  have hK_le : ∀ n r, N r ≤ n → r ≤ Kstar n := fun n r h =>
    Finset.le_sup (f := id) (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by have := hNr r; omega), h⟩)
  have hK_spec : ∀ n, N 0 ≤ n → N (Kstar n) ≤ n := by
    intro n hn
    have hne : ((Finset.range (n + 1)).filter fun r => N r ≤ n).Nonempty :=
      ⟨0, Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.succ_pos _), hn⟩⟩
    obtain ⟨r, hr, hreq⟩ := Finset.exists_mem_eq_sup _ hne id
    rw [show Kstar n = r from hreq]
    exact (Finset.mem_filter.1 hr).2
  have hKmono : Monotone Kstar := by
    intro n n' hnn'
    exact Finset.sup_mono_fun (fun _ _ => le_rfl) |>.trans' (Finset.sup_mono (by
      intro r hr
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hr
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by have := Finset.mem_range.1 h1; omega), h2.trans hnn'⟩))
  refine ⟨Kstar, hKmono, ?_, ?_⟩
  · refine tendsto_atTop_atTop.2 fun r => ⟨N r, fun n hn => hK_le n r hn⟩
  · intro e Kn he hb hKn hle
    rw [Metric.tendsto_atTop]
    intro ε hε
    -- choose `r` with `1/(r+1) < ε/2`, then `n` large so that `K*_n ≥ r` and `S(K_n) < ε/2`
    obtain ⟨r, hr⟩ := exists_nat_one_div_lt (half_pos hε)
    have hSev : ∀ᶠ n in atTop, |S (Kn n)| < ε / 2 := by
      have := (hS.comp hKn).eventually (Metric.ball_mem_nhds 0 (half_pos hε))
      filter_upwards [this] with n hn
      simpa [Real.dist_eq] using hn
    obtain ⟨n0, hn0⟩ := Filter.eventually_atTop.1 (hSev.and hle)
    refine ⟨max n0 (N r), fun n hn => ?_⟩
    have hn0' := hn0 n (le_of_max_le_left hn)
    have hNr' : N r ≤ n := le_of_max_le_right hn
    have hN0n : N 0 ≤ n := (hNmono.monotone (Nat.zero_le r)).trans hNr'
    set q := Kstar n with hq
    have hrq : r ≤ q := hK_le n r hNr'
    have hNq : N0 q ≤ n := (hNge q).trans (hK_spec n hN0n)
    have hAq : A (Kn n) n ≤ 1 / ((q : ℝ) + 1) := hN0 q n hNq (Kn n) hn0'.2
    have hq1 : 1 / ((q : ℝ) + 1) ≤ 1 / ((r : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hrq 1)
    have h1 := hb n (Kn n)
    have h0 := he n (Kn n)
    have hS' := hn0'.1
    rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
    have := abs_lt.1 hS'
    linarith

example : Claims.jensen := jensen
example : Claims.trimSet_mono := trimSet_mono
example : Claims.sinkmono := sinkmono
example : Claims.app_hard_envelope := app_hard_envelope

end StatFormal.Wave24a
