import StatFormal.Wave30tz.Statements

/-!
# `KS⁺` on finitely supported laws: it depends only on the order a function induces on the support (library)

Library component (untrusted). `KS⁺_{P,Q}(f) = sup_x {P(f > x) − Q(f > x)}` (`Wave30tz.ksPlus`).

* `measureReal_lt_eq_filter`: for `P` carried by a finite set `S` (`P Sᶜ = 0`), `P(f > x) = P({a ∈ S : f a > x})`;
* `exists_filter_lt_eq`: if `f` and `f₀` induce the same strict order on `S`, every up-set `{a ∈ S : f a > x}` of `f` is an up-set
  `{a ∈ S : f₀ a > x'}` of `f₀`;
* `ksPlus_eq_of_order_iff`: hence `KS⁺(f) = KS⁺(f₀)` (the two suprema range over the same set of values);
* `order_iff_of_close`: a perturbation of `f₀` by less than half its smallest gap on `S` preserves the strict order on `S`;
* `ksPlus_eq_of_close`: **`KS⁺` is locally constant** at a function with distinct values on the support. No measurability is used
  (`ksPlus` reads the outer measures of the up-sets).
-/

set_option linter.style.longLine false

noncomputable section
open MeasureTheory Set

namespace StatFormal.Alpha0Witness

open StatFormal.Wave30tz

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-- For a law carried by a finite set `S`, `P(f > x)` is the mass of the up-set of `f` in `S`. -/
theorem measureReal_lt_eq_filter (P : Measure 𝒳) {S : Finset 𝒳} (hS : P (↑S : Set 𝒳)ᶜ = 0) (f : 𝒳 → ℝ) (x : ℝ) :
    P.real {z | x < f z} = P.real ↑(S.filter fun a => x < f a) := by
  classical
  have e : (↑(S.filter fun a => x < f a) : Set 𝒳) = {z | x < f z} ∩ ↑S := by
    ext z
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Set.mem_inter_iff, Finset.mem_coe]
    tauto
  rw [e, measureReal_def, measureReal_def, measure_inter_conull hS]

/-- If `f` and `f₀` induce the same strict order on `S`, every up-set of `f` on `S` is an up-set of `f₀`. -/
theorem exists_filter_lt_eq {α : Type*} {S : Finset α} {f f₀ : α → ℝ}
    (h : ∀ a ∈ S, ∀ b ∈ S, (f a < f b ↔ f₀ a < f₀ b)) (x : ℝ) :
    ∃ x' : ℝ, S.filter (fun a => x < f a) = S.filter (fun a => x' < f₀ a) := by
  classical
  set L := S.filter fun a => ¬ x < f a with hL
  by_cases hne : L.Nonempty
  · obtain ⟨c, hcL, hcmax⟩ := Finset.exists_max_image L f hne
    obtain ⟨hcS, hcx⟩ := Finset.mem_filter.1 hcL
    refine ⟨f₀ c, Finset.filter_congr fun a ha => ?_⟩
    constructor
    · intro hxa
      exact (h c hcS a ha).1 (lt_of_le_of_lt (not_lt.1 hcx) hxa)
    · intro hca
      by_contra hxa
      exact absurd (hcmax a (Finset.mem_filter.2 ⟨ha, hxa⟩)) (not_le.2 ((h c hcS a ha).2 hca))
  · refine ⟨-(∑ a ∈ S, |f₀ a|) - 1, Finset.filter_congr fun a ha => ?_⟩
    have hxa : x < f a := by
      by_contra hxa
      exact hne ⟨a, Finset.mem_filter.2 ⟨ha, hxa⟩⟩
    have h1 : |f₀ a| ≤ ∑ b ∈ S, |f₀ b| := Finset.single_le_sum (f := fun b => |f₀ b|) (fun b _ => abs_nonneg _) ha
    have h2 : -|f₀ a| ≤ f₀ a := neg_abs_le _
    constructor
    · intro _; linarith
    · intro _; exact hxa

/-- `KS⁺` depends only on the strict order a function induces on a finite set carrying both laws. -/
theorem ksPlus_eq_of_order_iff (P Q : Measure 𝒳) {S : Finset 𝒳} (hP : P (↑S : Set 𝒳)ᶜ = 0) (hQ : Q (↑S : Set 𝒳)ᶜ = 0)
    {f f₀ : 𝒳 → ℝ} (h : ∀ a ∈ S, ∀ b ∈ S, (f a < f b ↔ f₀ a < f₀ b)) : ksPlus P Q f = ksPlus P Q f₀ := by
  have key : ∀ {f f₀ : 𝒳 → ℝ}, (∀ a ∈ S, ∀ b ∈ S, (f a < f b ↔ f₀ a < f₀ b)) →
      Set.range (fun x : ℝ => P.real {z | x < f z} - Q.real {z | x < f z}) ⊆
        Set.range (fun x : ℝ => P.real {z | x < f₀ z} - Q.real {z | x < f₀ z}) := by
    intro f f₀ h r ⟨x, hx⟩
    obtain ⟨x', hx'⟩ := exists_filter_lt_eq h x
    refine ⟨x', ?_⟩
    rw [← hx]
    simp only
    rw [measureReal_lt_eq_filter P hP, measureReal_lt_eq_filter Q hQ, measureReal_lt_eq_filter P hP f,
      measureReal_lt_eq_filter Q hQ f, hx']
  have e : Set.range (fun x : ℝ => P.real {z | x < f z} - Q.real {z | x < f z}) =
      Set.range (fun x : ℝ => P.real {z | x < f₀ z} - Q.real {z | x < f₀ z}) :=
    Set.Subset.antisymm (key h) (key fun a ha b hb => (h a ha b hb).symm)
  unfold ksPlus iSup
  rw [e]

/-- A perturbation of `f₀` by less than `g₀/2` on `S`, where `0 < g₀` is at most every gap of `f₀` on `S`, preserves the strict
order on `S`. -/
theorem order_iff_of_close {α : Type*} {S : Finset α} {f f₀ : α → ℝ} {g₀ : ℝ} (hg₀ : 0 < g₀)
    (hgap : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → g₀ ≤ |f₀ a - f₀ b|) (hclose : ∀ a ∈ S, |f a - f₀ a| < g₀ / 2) :
    ∀ a ∈ S, ∀ b ∈ S, (f a < f b ↔ f₀ a < f₀ b) := by
  have mono : ∀ a ∈ S, ∀ b ∈ S, f₀ a < f₀ b → f a < f b := by
    intro a ha b hb hab
    have hne : a ≠ b := fun h => by subst h; exact lt_irrefl _ hab
    have hg := hgap a ha b hb hne
    rw [abs_sub_comm, abs_of_pos (sub_pos.2 hab)] at hg
    have h1 := abs_lt.1 (hclose a ha)
    have h2 := abs_lt.1 (hclose b hb)
    linarith [h1.2, h2.1]
  intro a ha b hb
  refine ⟨fun hab => ?_, mono a ha b hb⟩
  by_cases heq : a = b
  · subst heq; exact absurd hab (lt_irrefl _)
  rcases lt_trichotomy (f₀ a) (f₀ b) with h | h | h
  · exact h
  · have hg := hgap a ha b hb heq
    rw [h, sub_self, abs_zero] at hg
    linarith
  · exact absurd (mono b hb a ha h) (not_lt.2 hab.le)

/-- **`KS⁺` is locally constant** at `f₀` on finitely supported laws: if `P, Q` are carried by a finite set `S`, `0 < g₀` is at
most every gap `|f₀ a − f₀ b|` (`a ≠ b ∈ S`), and `|f − f₀| < g₀/2` on `S`, then `KS⁺(f) = KS⁺(f₀)`. -/
theorem ksPlus_eq_of_close (P Q : Measure 𝒳) {S : Finset 𝒳} (hP : P (↑S : Set 𝒳)ᶜ = 0) (hQ : Q (↑S : Set 𝒳)ᶜ = 0)
    {f f₀ : 𝒳 → ℝ} {g₀ : ℝ} (hg₀ : 0 < g₀) (hgap : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → g₀ ≤ |f₀ a - f₀ b|)
    (hclose : ∀ a ∈ S, |f a - f₀ a| < g₀ / 2) : ksPlus P Q f = ksPlus P Q f₀ :=
  ksPlus_eq_of_order_iff P Q hP hQ (order_iff_of_close hg₀ hgap hclose)

end StatFormal.Alpha0Witness
