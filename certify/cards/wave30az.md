# Fidelity card — wave 30az: default-certified audit, misc batch — ICL lem:cond-osc, lem:cond-metric; SB prop:randpenalty, thm:decay (caveat REFUTED, long paper), journal lem:quantiles (REFUTED at u = 0); paper2 thm:npmle (maximiser clause REFUTED for measurable rules); trimmed-mmd lem:trimmedmean, prop:witnessstab

Lean: `StatFormal/Archive/Wave30az/Statements.lean` (frozen; composes frozen ICL cond_osc_*, cond_metric*, Wave18b, Wave8a sharp_*, Wave30ao
`sharp_printed`, Wave29d lindsay_gen_*, BangBang, Wave4b, Wave8a `georep_empirical`), 9 routes. Critic (2026-10-21): ACCEPT ×22,
ACCEPT-WITH-NOTE ×2; all three refutations confirmed in the printed settings; witnesses (printed plans at N(0, I_d), U[0,1], the free end on
[−1,1], n = 3 trimmed means) in `~/.cache/w30az-critic/Witness.lean`. **Author: approved (automatic on AI-audit PASS, per author decision 2026-10-21).**

## Covered
* ICL lem:cond-osc (ii) i.i.d. risk bound (`cond_osc_iid`); lem:cond-metric fixed floor, norm form, parameter ball (`cond_metric_*`).
* SB prop:randpenalty positivity at t = 1 for the printed plan, d = 1 and every d (`randpenalty_printed_one`, `_trace`; both versions).
* SB thm:decay: G_ε ≥ W₂ (`decay_ge_W2`), equality at ε > 0 for equal groups (`decay_equal_groups`), the long paper's "equality only at
  ε = 0" REFUTED (`decay_eq_refuted`).
* SB journal lem:quantiles: F⁻¹(0) = −∞ under the printed convention (`quantiles_zero_printed`), the printed [0,1] bound REFUTED
  (`quantiles_printed_refuted`), the corrected form (`quantiles_closed`).
* paper2 thm:npmle for a Feller kernel on compact metric L: duality with a maximiser for continuous exponents (`npmle_gen_duality`),
  sup = min with the dual attained for every bounded measurable rule (`npmle_gen_strong`), weak duality, convexity, correction, programme;
  the maximiser clause REFUTED for bounded measurable rules (`npmle_attain_refuted`).
* trimmed-mmd lem:trimmedmean minimum, sufficiency, uniqueness; prop:witnessstab without MeasurableSingletonClass and the O_P((n∧m)^{-1/4})
  rate (`witnessstab_gen`, `witnessstab_rate`).

## Not covered
thm:decay translated-group equality and the ε = 0 side; prop:randpenalty linked to the Wave18b kernel varK (stated with condVar).

## Paper notes (applied 2026-10-21, DEFECTS #172–#174)
#172 SB long thm:decay caveat (journal wording adopted); #173 SB journal quantile convention F⁻¹(0); #174 paper2 thm:npmle maximiser clause.

## Fidelity review
Independent AI audit, method v1 (certify/AUDIT_METHOD.md), 2026-10-27 — PASS with notes (28 targets, each claim back-translated blind and compared with the printed text).
Notes: Three refutation targets (decay_eq_refuted, quantiles_printed_refuted with quantiles_zero_printed, npmle_attain_refuted) document pre-fix wording; all three fixes (DEFECTS #172-#174) are in the current texts (long thm:decay at :2307, journal s_setting.tex:30 convention, paper2 main.tex thm:npmle), and the companion positive claims match the current wording. Journal 'identical text' thm:decay / prop:randpenalty targets: fine after #172 (texts now aligned). COVERAGE notes checked for all 8 labels: none overclaims (lem:quantiles credits Wave30az but its F_n bound and DKW rate are Wave30h targets — cosmetic attribution).
