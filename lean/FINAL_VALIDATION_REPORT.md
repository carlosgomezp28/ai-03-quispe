# Final Validation Report: Agentic Delegation and the Language Frontier of Software Developers: A Model and Evidence from Claude Code on GitHub

Updated: 2026-09-01

## 1. Human Verdict

No human semantic review has been performed, and no human-review row is
approved. The evidence-based closeout classification is **partially
formalized**.

## 2. Closeout Status

- Completion status: partially formalized.
- One-sentence recap: The paper's central algebraic and finite-sum results are
  proved, but two printed strictness claims need conditions absent from their
  proposition statements, and several surrounding probabilistic and
  comparative-static claims remain outside the formalized scope.

## 3. Source and Scope

- Paper: *Agentic Delegation and the Language Frontier of Software Developers:
  A Model and Evidence from Claude Code on GitHub*, Alexander Quispe and Kevin
  Xu.
- Source: [arXiv:2605.25438v2](https://arxiv.org/abs/2605.25438v2), version 2,
  dated 2026-07-07.
- Checked scope: four source-model definition blocks, three displayed
  assumptions, and five displayed propositions in the named-theory inventory.
- Empirical estimates, figures, tables, regressions, and tool classifications
  are outside this formalization's declared scope.

## 4. Researcher Summary of Checked Results

The following complete source claims are proved as stated:

- the Generation-1 and Generation-2 menus, activity indicator, and finite
  active-language count definitions;
- Proposition 1, that menu expansion weakly expands the language frontier path
  by path;
- Proposition 2, identifying the unfamiliar-language activation band, its CDF
  mass, and the nonnegative expected count expansion; and
- Proposition 4, the comparable-candidate product formula and its weak
  monotonicity in ability and candidate-set size.

Several exact subclaims in broader source blocks are also proved: the three
production-surplus formulas; the solo, conversational, delegation, and
effective threshold formulas and their algebraic difference; the finite-signal
precision and posterior-parameter formulas and strict precision increase; the
nonnegative part of the dynamic cumulative-language result; and the weak part
of repository expansion.

The printed strict part of Proposition 3 is false on its stated domain. Strict
growth and strict concavity require a nonempty unfamiliar-language frontier and
an interior post-agent hazard, not merely a positive one. The strict part of
Proposition 5 likewise needs positive opportunity probability in at least one
lowered entry-cost band.

## 5. Remaining Boundaries and Gaps

- The production block checks the displayed surplus algebra, but does not
  construct the Normal productivity model, derive the CARA certainty
  equivalents probabilistically, or prove that agent competence increases in
  capability.
- The threshold block checks the displayed formulas and foothold identity, but
  does not prove the claimed higher-ability and higher-capability comparative
  statics from the verification technology.
- The learning block checks the finite precision algebra and posterior
  parameter formulas, but does not construct conditionally independent Normal
  signals, a posterior kernel, or a full Normal-conjugacy theorem.
- Proposition 3's nonnegative cumulative gap is proved as printed; its strict
  clause is proved only for the corrected nonempty, interior-hazard domain.
- Proposition 5's weak expansion is proved as printed; its strict clause is
  proved only with positive probability mass in a lowered-cost interval.

## 6. Additional Assumptions Beyond Paper

- For the strict dynamic claim: the unfamiliar-language set must be nonempty,
  and every post-agent hazard used in the strict conclusion must satisfy
  \(0 < p^2 < 1\). These conditions are absent from the printed proposition.
- For strict repository expansion: at least one repository's lowered entry-cost
  interval must have positive opportunity probability. This condition appears
  in the source proof but is absent from the printed proposition statement.

These conditions are visible in the proved corrected endpoints; they have not
been silently attributed to the archival proposition statements.

## 7. Proof-Strategy Deviations

- The learning result is verified as finite algebra on precisions and means,
  rather than by formalizing the source's probability-kernel conjugacy
  derivation.
- Continuous CDFs are represented by atomless probability measures on the real
  line, which is the equivalent measure-theoretic condition needed for the
  half-open interval identity.
- Language and repository collections are finite sets, matching the source's
  finite sums.

## 8. Proof Tricks Worth Reusing

- Reduce frontier expansion to monotonicity of an indicator under maximum-menu
  inclusion, then sum the pointwise inequalities.
- Express threshold activation as a half-open interval and use atomlessness to
  turn its probability into a CDF difference.
- Prove dynamic strictness through first and second finite differences, keeping
  endpoint and nonemptiness hypotheses explicit.
- Derive strict expected expansion from a weak finite-sum comparison plus one
  summand with positive interval mass.

## 9. Generalizations, Conjectures, and Extensions

- A complete probability-space treatment of the Normal learning model would
  close the main learning boundary.
- The verification-technology assumption could be connected to differentiable
  comparative statics for the activation-threshold reduction.

## 10. Mathematical Typos or Other Fixes Suggested in the Source Paper

1. Proposition 3 should add a nonempty unfamiliar-language frontier and
   \(0 < p^2 < 1\) before claiming strict increase and strict concavity. If the
   frontier is empty, the cumulative gap is identically zero. If \(p^2=1\),
   the gap reaches its maximum after the first horizon and is then constant.
2. Proposition 5 should require positive opportunity mass in at least one
   repository's lowered entry-cost interval before claiming strict expected
   expansion. The source proof already uses this positive-mass premise.

Neither archival statement has been treated as corrected or paper-owner
approved.

## 11. Paper Issues or Caveats

The two missing-condition findings in Section 10 are theorem-statement defects,
not proof-engineering limitations. Because the proved endpoints add substantive
conditions and no paper-owner correction has been supplied, the proper status
is partially formalized rather than formalized with a caveat.

## 12. Detailed Formalization Evidence

- Lean footprint: 799 lines across `Assumptions.lean`, `MainTheorems.lean`,
  `PaperInterface.lean`, and `ProofInterface.lean`.
- The paper-facing interface contains nine transparent `...Spec : Prop`
  declarations. Each has an exact-type theorem endpoint in
  `ProofInterface.lean`.
- The raw source-to-expanded-Spec screening records four `matches` judgments
  and five `mismatch` judgments. The mismatches preserve incomplete source
  bundles or genuine missing-condition defects; they are not proof failures for
  the narrower visible Specs.
- Sixteen retained paper-local definition prerequisites have explicit
  `matches` decisions.
- Fifty theorem-facing inputs have occurrence-indexed source-record judgments.
  Those judgments validate source model data and premises and expressly do not
  override the five source/Spec mismatches.
- The source-proof-fidelity ledger reviews all five proposition proof scopes,
  the model-definition algebra, and the learning update. It records exactly two
  source-statement defects, both with `partially_formalized` impact.
- No material reusable EconCSLib declaration lies directly on the nine-Spec
  dependency surface.

Pinned source evidence:

- frozen TeX surface SHA-256:
  `99ee555dad291679321b8d3f348787e54861903c99e01595ab8cb42fd3d42031`;
- arXiv v2 source archive SHA-256:
  `1b3e7968697bcb306f7c96fbdb60e93d8c49eb805afb15ce00271084da24a296`.

## 13. Paper Assumption Provenance

The source inventory contains three explicitly displayed assumptions, each
represented by a named declaration in `Assumptions.lean`. The premise-level
source-record review source-anchors the theorem-facing inputs, but the generic
independent `assumption_match_llm.json` ledger has no completed items. No human
approval is claimed.

| Assumption declaration | Source condition | Current evidence | Closeout disposition |
| --- | --- | --- | --- |
| `assumption_augmentation_requires_foothold` | Conversational augmentation requires existing language skill | Named source assumption and source-map atom; premise-level source records present | Source condition recorded; independent generic assumption review and human review pending |
| `assumption_verification_technology` | Verification cost and residual error weakly fall in the stated inputs, with verification cost strictly falling in ability | Named source assumption and source-map atom; premise-level source records present | Source condition recorded; associated threshold comparative statics remain unproved |
| `assumption_comparable_unfamiliar_language_candidates` | Unfamiliar candidates share a common nonnegative, ability-monotone activation increment | Named source assumption and source-map atom; used by the Proposition 4 interface | Source condition recorded; no human approval claimed |

## 14. Displayed Formula Provenance

| Paper formula or definition block | Lean realization | Current result |
| --- | --- | --- |
| Production surpluses, Equations (1)--(3) | `soloSurplus`, `copilotSurplus`, `delegationSurplus`; `production_mode_surplusesSpec` | Algebra proved exactly; surrounding Normal/CARA and competence-monotonicity semantics remain partial |
| Menus, activity, and monthly count | `generationOneValue`, `generationTwoValue`, `activityIndicator`, `activeLanguageCount`; `generation_menus_and_activitySpec` | Proved as stated |
| Activation thresholds, Equations (4)--(8) | five threshold definitions; `activation_thresholdsSpec` | Formula algebra, foothold consequence, and advantage identity proved; comparative statics remain partial |
| Learning update | `totalSignalPrecision`, `precisionWeightedSignalMean`, `posteriorPrecision`, `posteriorMean`; `learning_after_agentic_interactionSpec` | Displayed formulas and strict precision increase proved; probability-model derivation remains partial |

All sixteen listed definitions have current semantic-prerequisite `matches`
decisions in `audit/paper_semantic_prerequisite_decisions.json`.

## 15. Library Lift Pass

- Reusable library extraction candidates: none identified.
- The recorded direct dependency surface for all nine Specs contains no
  material reusable library declarations requiring a source-semantic bridge.
- The source-record review treats all theorem-facing inputs as source model
  data or source conditions; it does not convert those inputs into proof credit
  for missing source conclusions.

## 16. DAG Audit

- `docs/DependencyDAG.tex` is present and records the paper-local dependency
  structure.
- The PDF path listed in `status.json` is not present in the current folder, so
  no rendered-layout approval is claimed.
- No human topology or layout approval has been recorded.

## 17. Validation Checks

Existing proof evidence before this documentation-only closeout:

- `lake build QX26AgenticDelegation`: passed.
- Focused `PaperInterface` and `ProofInterface` builds: passed.
- Conclusion-provenance audit: passed with zero errors.

Final targeted closeout checks on 2026-09-01:

- `python3 scripts/paper_contribution.py check QX26AgenticDelegation --fast`:
  passed.
- Targeted scan of the paper's Lean files: no `sorry` or `admit` declarations.
- `git diff --check`: passed as part of the fast check.

No `FINAL_CLOSURE_RECEIPT.md` is issued. The repository protocol reserves that
receipt for a frozen successful semantic closeout, while this paper retains
five explicit source/Spec mismatches, unpopulated generic assumption and
coverage ledgers, and no human review.

## 18. Paper Definitions Checked

- The three production-mode surplus equations are definitionally verified.
- The two generation menus, activity indicator, and active-language count are
  definitionally verified.
- The solo, conversational, delegation, Generation-1, and Generation-2
  thresholds are verified, including the unfamiliar-language foothold identity
  and exact delegation-advantage formula.
- Total signal precision, the precision-weighted signal mean, posterior
  precision, and posterior mean are definitionally verified for a finite
  nonempty signal family with positive variances.

## 19. Named Theorem Statements Checked

| Paper claim | Lean interface endpoint | Status |
| --- | --- | --- |
| Proposition 1: frontier expansion | `frontier_expansionSpec` / `frontier_expansion` | Proved as stated |
| Proposition 2: activation band for unfamiliar languages | `activation_band_unfamiliar_languagesSpec` / `activation_band_unfamiliar_languages` | Proved as stated |
| Proposition 3: dynamic cumulative-language effect | `dynamic_cumulative_language_effectSpec` / `dynamic_cumulative_language_effect` | Nonnegative clause proved as stated; strict clauses proved with nonempty frontier and `0 < p² < 1`; archival strict claim is defective |
| Proposition 4: specialist and ability heterogeneity | `specialist_and_ability_heterogeneitySpec` / `specialist_and_ability_heterogeneity` | Proved as stated |
| Proposition 5: repository expansion | `repository_expansionSpec` / `repository_expansion` | Weak clause proved as stated; strict clause proved with positive opportunity mass; archival statement omits that premise |

The theorem `dynamic_strictness_boundary_counterexample` proves the allowed
`p² = 1` counterexample. The empty-frontier counterexample is immediate from
the finite sum and is recorded in the source-proof-fidelity defect.

## 20. Paper-Facing Statement Validator Ledger

The following are agent/audit judgments, not human approvals. Human review is
pending for every row.

| Paper-facing statement | Raw source-to-expanded-Spec judgment | Reason for current disposition |
| --- | --- | --- |
| `production_mode_surplusesSpec` | Mismatch / partial | Equations (1)--(3) match, but the bundled Normal/CARA semantics and competence monotonicity are absent |
| `generation_menus_and_activitySpec` | Matches | Menu, indicator, and finite-count definitions agree with the source |
| `activation_thresholdsSpec` | Mismatch / partial | Equations (4)--(8) match, but the bundled ability/capability comparative statics are absent |
| `learning_after_agentic_interactionSpec` | Mismatch / partial | Update algebra matches, but Normal signals, conditional independence, posterior kernel, and conjugacy are absent |
| `frontier_expansionSpec` | Matches | Pathwise indicator and finite-count monotonicity agree with Proposition 1 |
| `activation_band_unfamiliar_languagesSpec` | Matches | Half-open band, CDF difference, and nonnegative expected expansion agree with Proposition 2 |
| `dynamic_cumulative_language_effectSpec` | Mismatch / partial | The archival strict claim lacks nonempty-frontier and interior-hazard conditions |
| `specialist_and_ability_heterogeneitySpec` | Matches | Product formula and both weak monotonicity conclusions agree with Proposition 4 |
| `repository_expansionSpec` | Mismatch / partial | The archival strict claim lacks the proof's positive-mass premise |

## 21. Source-Coverage Audit Ledger

- Source inventory: twelve named-theory items in the frozen arXiv v2 TeX
  surface—four source-model definition blocks, three assumptions, and five
  propositions.
- Lean routes: nine paper-facing Specs cover the four definition blocks and
  five propositions; the three displayed assumptions have named declarations
  in `Assumptions.lean`.
- Current semantic result: four complete source bundles match their expanded
  Specs; five are partial or mismatched for the reasons in Section 20.
- The four matching rows have independent source-atom-to-Spec correspondence
  receipts. The five partial rows deliberately have no equivalence receipt.
- The generic `paper_coverage_llm.json` ledger is unpopulated. Coverage is
  therefore reported from the curated statement map, the raw v11 source/Spec
  decisions, the source-record review, and the source-proof-fidelity ledger,
  without claiming a completed generic coverage-validator pass.
- No row-local or paper-level human approval is recorded.

This evidence supports a completed **partial** closeout only. It does not
support full-formalization status or archival equivalence for the two corrected
strictness endpoints.
