# Fidelity audit method v1 (2026-10-27)

The gate (`tools/certify.py check`) certifies that each proof proves exactly its frozen statement, with only the axioms propext,
Classical.choice and Quot.sound. It does not certify that a frozen statement says what the paper says. That is the job of the fidelity
review recorded on each card. The author decided (2026-10-21) that a card whose review PASSES under this method is approved by him
automatically; cards that are FLAGGED stay "Author: PENDING" until he answers the listed questions. Every approval line says so.

## Reviewer
An independent AI reviewer (Claude), separate from the agents that drafted and criticised the wave, working from the frozen files only.

## Per claim
1. **Blind back-translation.** Read the frozen `Statements.lean` definition (and the definitions it uses) and write, before opening the
   paper, a plain-mathematics statement of what the Lean claim asserts: objects, hypotheses, quantifiers, conclusion.
2. **Comparison.** Open the printed result (located by label in the current paper source) and compare clause by clause.
3. **Checklist.**
   - junk values: division by 0, `toReal`/`toNNReal` of ∞, `sSup`/`sInf` of empty or unbounded sets, `Measure.map` of a non-measurable map,
     `deriv` of a non-differentiable function, Bochner integrals of non-integrable functions, `log 0`;
   - vacuity: hypotheses jointly satisfiable in the paper's setting (a witness exists or is evident);
   - smuggling: no hypothesis restates the conclusion or a step the paper proves;
   - quantifier order and scope (∀/∃, almost surely, uniformly);
   - hypotheses weaker than printed (fine: a generalisation) or stronger than printed (must be declared on the card);
   - textbook bridges and premises supplied by other results: declared on the card;
   - the label and paper id of each target are right.
4. **Coverage note.** The coverage note for the label must not claim more than the certified claims give.

## Per card verdict
- **PASS**: every claim faithful; deviations are generalisations or declared encodings.
- **PASS with notes**: faithful; cosmetic issues (line numbers, wording) recorded.
- **FLAG**: an undeclared stronger hypothesis, a junk-value or vacuity risk, a misread clause, a wrong label, or an overclaiming
  coverage note. Each flag carries a precise question for the author or a proposed fix.

## Recording
A PASS card gets
`Fidelity review: independent AI audit, method v1 (certify/AUDIT_METHOD.md), <date> — PASS[ with notes]` and
`**Author: approved (automatic on AI-audit PASS, per author decision 2026-10-21).**` replacing `**Author: PENDING.**`.
A FLAG card gets the review line with FLAG and the questions, and keeps `**Author: PENDING.**`.
