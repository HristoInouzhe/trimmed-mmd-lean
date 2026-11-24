# Fidelity card — wave 30v: trimmed-mmd conj:boundary (the limiting law at the contact level) and lem:separation (equality form)

Lean: `StatFormal/Archive/Wave30v/Statements.lean` (frozen; new def `HasHadamardDirDeriv` (full, non-tangential, sequential Shapiro form), support functions
of compact convex sets), `Proofs.lean`, routes `Route{Sup,Geom,Value,Delta}` (route theorems: `boundary_sup_hadamard` (Danskin/Römisch),
`boundary_contact_argmax`, `boundary_polar_infDist` (Moreau), `boundary_delta_method` (Shapiro/Fang–Santos), `boundary_sup_limit` (abstract core
of Theorem A)). Critic (2026-10-20): 7 targets (ACCEPT ×1, ACCEPT-WITH-NOTE ×6); 5 library facts routed; all math verdicts confirmed.
**Author: approved (automatic on AI-audit PASS, per author decision 2026-10-21).**
UPDATE (2026-10-20, author request): the paper now states `thm:boundary` (unconditional limit law, "Theorem A") and `cor:boundary-linear` in place of
conj:boundary (supplement section supp:boundary). Mapping: `boundary_value_hadamard` = deterministic core of thm:boundary (ii) (support-function form);
`boundary_tangent_cone` = K = cl(T_Q − T_P); `boundary_translation` = the corollary's dist(x,K) identity; `boundary_dist_dual` = eq:bddual (lem:separation);
`boundary_limit_linear` is a CONDITIONAL analogue of the corollary (whole-ball linear support-function CLT assumed); `boundary_conditional` is HISTORICAL
(the former conjecture's implication from (B2)/(B3), no longer printed). Targets keep their frozen `conj:boundary (…)` labels; Steps 1–2 of the new proof
(lem:cvar lift, Donsker CLT) are formalised in wave 30z.

## Covered
* conj:boundary as printed: `boundary_conditional` — (B2) in joint form (weaker than the printed marginal + independence form) and (B3) imply
  √N D̂ ⇒ dist(X, cl T) = sup over K°∩B₁ — a CMT + Slutsky consequence of its hypotheses ((B1) unused).
* `boundary_value_hadamard`: the value function is Hadamard directionally (not fully) differentiable at a contact pair, with explicit derivative
  sup over Ball ∩ (B − A)° of [−H_A(−g) − H_B(g)] (the printed "directionally, not fully, differentiable"); `boundary_tangent_cone`
  (K = cl(T_Q − T_P) = cl cone(B − A), independent of the contact point); `boundary_translation` (in translation directions the derivative is the
  printed limit); `boundary_limit` (the contact limit law, CONDITIONAL on a whole-ball support-function CLT — an upgrade, not printed);
  `boundary_limit_linear` (the printed limit without (B3)).
* lem:separation, equality form in ℝ^r: `boundary_dist_dual` (dist(A,B) = sup_{‖g‖≤1}(−h_A(−g) − h_B(g)); overlaps Wave17a `separation`).

## Not covered
The Moreau step to ‖Π_{K°}X‖ (no projection defined); the joint-from-marginal (B2) step; the lem:cvar lift and the Donsker CLT — hence the
UNCONDITIONAL Theorem A (paper-side argument, critic-checked) is not certified; the counterexamples ((B2) at α* = TV, chi-bar-square, α*_r < TV)
are by hand and Monte Carlo only.

## Paper notes (critic-confirmed)
DEFECTS #147 (S2): "chi-bar-square" (supplement.tex:2282, paper.tex:2277) false in general (dim K° ≥ 2, Cov ∉ ℝI). DEFECTS #148 (S2): the r = 1
"trimmed means of scalars, hence asymptotically normal" needs unique α*-quantiles (two-atom contact example: (B2) fails, limit atom 1/4). DEFECTS
#149 (S3): α* must be the r-feature contact level α*_r ≤ TV; (B2)'s "equivalently, a support-function CLT near ν" is not equivalent; the conjecture
is a two-line consequence of its hypotheses — relabel as a proposition with (B2)/(B3) open; optional upgrade to Theorem A.

## Audit additions (2026-10-27)
- Target label corrected: `boundary_value_hadamard` "conj:boundary (boundary_value_hadamard)" -> "thm:boundary (ii) deterministic core (boundary_value_hadamard)".
- Target label corrected: `boundary_tangent_cone` "conj:boundary (boundary_tangent_cone)" -> "thm:boundary (ii) K = cl(T_Q - T_P) (boundary_tangent_cone)".
- Target label corrected: `boundary_translation` "conj:boundary (boundary_translation)" -> "cor:boundary-linear dist identity (boundary_translation)".
- Target label corrected: `boundary_limit` "conj:boundary (boundary_limit)" -> "superseded analogue of the boundary limit law, whole-ball CLT assumed (boundary_limit)".
- Target label corrected: `boundary_limit_linear` "conj:boundary (boundary_limit_linear)" -> "superseded analogue of the translation-type limit (boundary_limit_linear)".
- Target label corrected: `boundary_conditional` "conj:boundary (boundary_conditional)" -> "former boundary conjecture, no longer printed (boundary_conditional)".

## Fidelity review
Independent AI audit, method v1 (certify/AUDIT_METHOD.md), 2026-10-27 — FLAG (7 targets, each claim back-translated blind and compared with the printed text). A second-opinion review the same day confirmed every flag; the fixes above were applied. No Lean claim was found unfaithful. Verdict after fixes: PASS with notes.
Notes: All seven claims are mathematically correct readings with no junk (supportFn sSup over bounded nonempty sets; valueDeriv sSup over a nonempty compact set; TendstoInDistribution carries measurability). The card's UPDATE section gives the mapping to thm:boundary / cor:boundary-linear / eq:bddual. Card line refs stale (thm:boundary now supplement.tex:2815, cor:boundary-linear :2847, eq:bddual :3010).
* FLAG (resolved) `boundary_value_hadamard, boundary_tangent_cone, boundary_translation, boundary_limit, boundary_limit_linear, boundary_conditional`: Wrong/stale label: the six targets are labelled 'conj:boundary (...)', but conj:boundary no longer exists in the trimmed-mmd sources (replaced by thm:boundary and cor:boundary-linear, supplement supp:boundary). COVERAGE.md (trimmed-mmd preamble) still lists `conj:boundary` among 'certified items outside the extracted environments'. The card discloses that the frozen labels were kept, but the checklist requires the label to be right.
