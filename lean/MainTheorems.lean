import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Tactic

/-!
# Paper-Facing Theorems: Agentic Delegation and the Language Frontier of Software Developers: A Model and Evidence from Claude Code on GitHub

This file is the implementation theorem layer for the source paper. Keep
source-faithful definitions and theorem wrappers here, and expose only the
compact human-review subset in `PaperInterface.lean`.

During the statement-first phase, each exact paper-facing proposition lives in a
transparent `<name>Spec : Prop` declaration in `PaperInterface.lean`; the paired
theorem/lemma endpoint belongs in `ProofInterface.lean` and has exactly that
type. Add proof implementations here only after those specifications pass v11
raw-source-to-expanded-Spec review and recursive premise provenance audit. Before full closeout, the v11
realization audit independently binds pinned source atoms to the elaborated Spec
and accounts for the complete Lean closure; a proof hole or a declaration name
is never evidence for that correspondence.
-/

namespace QX26AgenticDelegation

noncomputable section

/-- Solo-production certainty-equivalent surplus. -/
def soloSurplus (opportunity skill mean riskAversion precision activationCost : ℝ) : ℝ :=
  opportunity + skill * mean - riskAversion * skill ^ 2 / (2 * precision) - activationCost

/-- Conversational-assistant certainty-equivalent surplus. -/
def copilotSurplus
    (opportunity skill mean riskAversion precision activationCost copilotGain copilotCost : ℝ) :
    ℝ :=
  soloSurplus opportunity skill mean riskAversion precision activationCost +
    copilotGain * skill - copilotCost

/-- Agentic-delegation certainty-equivalent surplus. -/
def delegationSurplus
    (opportunity skill mean ability capability delegationShare riskAversion precision
      activationCost delegationCost : ℝ)
    (agentCompetence : ℝ → ℝ) (verificationCost : ℝ → ℝ → ℝ)
    (residualVariance : ℝ → ℝ → ℝ → ℝ) : ℝ :=
  opportunity + (1 - delegationShare) * skill * mean +
    delegationShare * ability * agentCompetence capability -
    verificationCost ability skill - delegationCost - activationCost -
    riskAversion / 2 *
      (((1 - delegationShare) ^ 2 * skill ^ 2) / precision +
        residualVariance ability skill capability)

/-- Best certainty-equivalent surplus before the agentic option is available. -/
def generationOneValue (solo copilot : ℝ) : ℝ :=
  max solo copilot

/-- Best certainty-equivalent surplus after the agentic option is available. -/
def generationTwoValue (solo copilot delegation : ℝ) : ℝ :=
  max (max solo copilot) delegation

/-- Solo-production opportunity threshold. -/
def soloThreshold (skill mean riskAversion precision activationCost : ℝ) : ℝ :=
  activationCost - skill * mean + riskAversion * skill ^ 2 / (2 * precision)

/-- Conversational-assistant opportunity threshold. -/
def copilotThreshold
    (skill mean riskAversion precision activationCost copilotGain copilotCost : ℝ) : ℝ :=
  soloThreshold skill mean riskAversion precision activationCost -
    (copilotGain * skill - copilotCost)

/-- Agentic-delegation opportunity threshold. -/
def delegationThreshold
    (skill mean ability capability delegationShare riskAversion precision activationCost
      delegationCost : ℝ)
    (agentCompetence : ℝ → ℝ) (verificationCost : ℝ → ℝ → ℝ)
    (residualVariance : ℝ → ℝ → ℝ → ℝ) : ℝ :=
  activationCost - (1 - delegationShare) * skill * mean -
    delegationShare * ability * agentCompetence capability +
    verificationCost ability skill + delegationCost +
    riskAversion / 2 *
      (((1 - delegationShare) ^ 2 * skill ^ 2) / precision +
        residualVariance ability skill capability)

/-- The Generation-1 threshold is the minimum of solo and conversational thresholds. -/
def generationOneThreshold
    (soloThreshold copilotGain skill copilotCost : ℝ) : ℝ :=
  soloThreshold - max 0 (copilotGain * skill - copilotCost)

/-- The post-agent threshold is the lower of the old and delegation thresholds. -/
def generationTwoThreshold (generationOne delegation : ℝ) : ℝ :=
  min generationOne delegation

/-- The paper's binary activity indicator, represented as a natural number. -/
def activityIndicator (surplus : ℝ) : ℕ :=
  if 0 ≤ surplus then 1 else 0

/-- Number of active languages in a finite language set. -/
def activeLanguageCount
    {Language : Type*} (languages : Finset Language) (surplus : Language → ℝ) : ℕ :=
  ∑ language ∈ languages, activityIndicator (surplus language)

/-- Total precision of the conditionally independent learning signals. -/
def totalSignalPrecision
    {Signal : Type*} (signals : Finset Signal) (signalVariance : Signal → ℝ) : ℝ :=
  ∑ signal ∈ signals, 1 / signalVariance signal

/-- Precision-weighted mean of the observed learning signals. -/
def precisionWeightedSignalMean
    {Signal : Type*} (signals : Finset Signal) (signalValue signalVariance : Signal → ℝ) : ℝ :=
  (∑ signal ∈ signals, signalValue signal / signalVariance signal) /
    totalSignalPrecision signals signalVariance

/-- Posterior precision after incorporating all learning signals. -/
def posteriorPrecision (priorPrecision signalPrecision : ℝ) : ℝ :=
  priorPrecision + signalPrecision

/-- Posterior productivity mean after incorporating the precision-weighted signals. -/
def posteriorMean
    (priorPrecision priorMean signalPrecision weightedSignalMean : ℝ) : ℝ :=
  (priorPrecision * priorMean + signalPrecision * weightedSignalMean) /
    (priorPrecision + signalPrecision)

/-- Positive-variance signals have strictly positive total precision. -/
theorem totalSignalPrecision_pos
    {Signal : Type*} (signals : Finset Signal) (signalVariance : Signal → ℝ)
    (hne : signals.Nonempty)
    (hvariance : ∀ signal ∈ signals, 0 < signalVariance signal) :
    0 < totalSignalPrecision signals signalVariance := by
  unfold totalSignalPrecision
  exact Finset.sum_pos
    (fun signal hsignal => one_div_pos.mpr (hvariance signal hsignal)) hne

/-- Adding an option to a maximization menu cannot lower its activity indicator. -/
theorem activityIndicator_mono {oldValue newValue : ℝ} (h : oldValue ≤ newValue) :
    activityIndicator oldValue ≤ activityIndicator newValue := by
  simp only [activityIndicator]
  split_ifs with hold hnew
  · simp
  · exfalso
    exact hnew (hold.trans h)
  · simp
  · simp

/-- The indicator difference induced by a strict threshold reduction is the activation band. -/
theorem threshold_indicator_sub_eq_band
    {delegationThreshold soloThreshold opportunity : ℝ}
    (hthreshold : delegationThreshold < soloThreshold) :
    ((if delegationThreshold ≤ opportunity then 1 else 0) : ℤ) -
        (if soloThreshold ≤ opportunity then 1 else 0) =
      if delegationThreshold ≤ opportunity ∧ opportunity < soloThreshold then 1 else 0 := by
  by_cases hdelegation : delegationThreshold ≤ opportunity
  · by_cases hsolo : soloThreshold ≤ opportunity
    · have hopportunity : ¬ opportunity < soloThreshold := not_lt.mpr hsolo
      simp [hdelegation, hsolo, hopportunity]
    · have hopportunity : opportunity < soloThreshold := lt_of_not_ge hsolo
      simp [hdelegation, hsolo, hopportunity]
  · have hsolo : ¬ soloThreshold ≤ opportunity := by
      exact fun h => hdelegation (hthreshold.le.trans h)
    simp [hdelegation, hsolo]

/-- For an atomless probability law, activation-band mass is a CDF difference. -/
theorem bandProbability_eq_cdf_sub
    (opportunityLaw : MeasureTheory.Measure ℝ)
    (hprobability : opportunityLaw Set.univ = 1)
    (hatomless : ∀ x, opportunityLaw {x} = 0)
    {lower upper : ℝ} (hthreshold : lower ≤ upper) :
    opportunityLaw.real (Set.Ico lower upper) =
      opportunityLaw.real (Set.Iic upper) - opportunityLaw.real (Set.Iic lower) := by
  letI : MeasureTheory.IsProbabilityMeasure opportunityLaw := ⟨hprobability⟩
  letI : MeasureTheory.NoAtoms opportunityLaw := ⟨hatomless⟩
  calc
    opportunityLaw.real (Set.Ico lower upper) =
        opportunityLaw.real (Set.Ioc lower upper) :=
      MeasureTheory.measureReal_congr MeasureTheory.Ico_ae_eq_Ioc
    _ = opportunityLaw.real (Set.Iic upper \ Set.Iic lower) := by
      rw [Set.Iic_diff_Iic]
    _ = opportunityLaw.real (Set.Iic upper) - opportunityLaw.real (Set.Iic lower) :=
      MeasureTheory.measureReal_diff (Set.Iic_subset_Iic.mpr hthreshold)
        measurableSet_Iic

/-- A weak reduction in every activation threshold gives nonnegative expected expansion. -/
theorem expected_band_expansion_nonneg
    {Language : Type*} (languages : Finset Language)
    (generationOne generationTwo : Language → ℝ)
    (opportunityLaw : Language → MeasureTheory.Measure ℝ)
    (hprobability : ∀ language, opportunityLaw language Set.univ = 1)
    (hatomless : ∀ language x, opportunityLaw language {x} = 0)
    (hthreshold : ∀ language ∈ languages, generationTwo language ≤ generationOne language) :
    (∑ language ∈ languages,
        (opportunityLaw language).real
          (Set.Ico (generationTwo language) (generationOne language))) =
        ∑ language ∈ languages,
          ((opportunityLaw language).real (Set.Iic (generationOne language)) -
            (opportunityLaw language).real (Set.Iic (generationTwo language))) ∧
      0 ≤ ∑ language ∈ languages,
        ((opportunityLaw language).real (Set.Iic (generationOne language)) -
          (opportunityLaw language).real (Set.Iic (generationTwo language))) := by
  constructor
  · apply Finset.sum_congr rfl
    intro language hlanguage
    exact bandProbability_eq_cdf_sub (opportunityLaw language)
      (hprobability language) (hatomless language) (hthreshold language hlanguage)
  · apply Finset.sum_nonneg
    intro language hlanguage
    rw [← bandProbability_eq_cdf_sub (opportunityLaw language)
      (hprobability language) (hatomless language) (hthreshold language hlanguage)]
    exact MeasureTheory.measureReal_nonneg

/-- Monotonicity of one-minus-hazard powers gives the nonnegative cumulative gap. -/
theorem cumulative_gap_nonneg
    {Language : Type*} (unfamiliar : Finset Language)
    (oldHazard newHazard : Language → ℝ) (horizon : ℕ)
    (_hold_nonneg : ∀ language ∈ unfamiliar, 0 ≤ oldHazard language)
    (hnew_le_one : ∀ language ∈ unfamiliar, newHazard language ≤ 1)
    (hhazard : ∀ language ∈ unfamiliar, oldHazard language ≤ newHazard language) :
    0 ≤ ∑ language ∈ unfamiliar,
      ((1 - oldHazard language) ^ (horizon + 1) -
        (1 - newHazard language) ^ (horizon + 1)) := by
  apply Finset.sum_nonneg
  intro language hlanguage
  apply sub_nonneg.mpr
  exact pow_le_pow_left₀ (by linarith [hnew_le_one language hlanguage])
    (by linarith [hhazard language hlanguage]) _

/-- With interior hazards and a nonempty frontier, the closed-frontier gap grows strictly. -/
theorem closed_frontier_gap_strict_mono
    {Language : Type*} (unfamiliar : Finset Language) (hazard : Language → ℝ)
    (hne : unfamiliar.Nonempty)
    (hpos : ∀ language ∈ unfamiliar, 0 < hazard language)
    (hlt : ∀ language ∈ unfamiliar, hazard language < 1) (horizon : ℕ) :
    (∑ language ∈ unfamiliar,
        (1 - (1 - hazard language) ^ (horizon + 1))) <
      ∑ language ∈ unfamiliar,
        (1 - (1 - hazard language) ^ (horizon + 2)) := by
  apply Finset.sum_lt_sum_of_nonempty hne
  intro language hlanguage
  have hbase_pos : 0 < 1 - hazard language := by linarith [hlt language hlanguage]
  have hbase_lt_one : 1 - hazard language < 1 := by linarith [hpos language hlanguage]
  linarith [pow_lt_pow_right_of_lt_one₀ hbase_pos hbase_lt_one (by omega : horizon + 1 < horizon + 2)]

/-- With interior hazards, successive closed-frontier gains strictly decrease. -/
theorem closed_frontier_gap_strict_concave
    {Language : Type*} (unfamiliar : Finset Language) (hazard : Language → ℝ)
    (hne : unfamiliar.Nonempty)
    (hpos : ∀ language ∈ unfamiliar, 0 < hazard language)
    (hlt : ∀ language ∈ unfamiliar, hazard language < 1) (horizon : ℕ) :
    ((∑ language ∈ unfamiliar,
          (1 - (1 - hazard language) ^ (horizon + 3))) -
        ∑ language ∈ unfamiliar,
          (1 - (1 - hazard language) ^ (horizon + 2))) <
      ((∑ language ∈ unfamiliar,
          (1 - (1 - hazard language) ^ (horizon + 2))) -
        ∑ language ∈ unfamiliar,
          (1 - (1 - hazard language) ^ (horizon + 1))) := by
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_lt_sum_of_nonempty hne
  intro language hlanguage
  have hbase_pos : 0 < 1 - hazard language := by linarith [hlt language hlanguage]
  have hbase_lt_one : 1 - hazard language < 1 := by linarith [hpos language hlanguage]
  have hpower :
      (1 - hazard language) ^ (horizon + 2) <
        (1 - hazard language) ^ (horizon + 1) :=
    pow_lt_pow_right_of_lt_one₀ hbase_pos hbase_lt_one (by omega)
  have hleft :
      (1 - (1 - hazard language) ^ (horizon + 3)) -
          (1 - (1 - hazard language) ^ (horizon + 2)) =
        hazard language * (1 - hazard language) ^ (horizon + 2) := by
    rw [show horizon + 3 = (horizon + 2) + 1 by omega, pow_succ]
    ring
  have hright :
      (1 - (1 - hazard language) ^ (horizon + 2)) -
          (1 - (1 - hazard language) ^ (horizon + 1)) =
        hazard language * (1 - hazard language) ^ (horizon + 1) := by
    rw [show horizon + 2 = (horizon + 1) + 1 by omega, pow_succ]
    ring
  rw [hleft, hright]
  exact mul_lt_mul_of_pos_left hpower (hpos language hlanguage)

/-- The printed dynamic strictness clause fails at the boundary hazard `p² = 1`. -/
theorem dynamic_strictness_boundary_counterexample :
    ¬ ((1 - (1 - (1 : ℝ)) ^ (0 + 1)) < (1 - (1 - (1 : ℝ)) ^ (0 + 2))) := by
  norm_num

/-- Expected activation is monotone in ability under the symmetry assumption. -/
theorem specialist_expansion_mono_ability
    {Language : Type*} (unfamiliar : Finset Language) (commonIncrement : ℝ → ℝ)
    (hmono : Monotone commonIncrement) {ability ability' : ℝ} (hability : ability ≤ ability') :
    (∑ _language ∈ unfamiliar, commonIncrement ability) ≤
      ∑ _language ∈ unfamiliar, commonIncrement ability' := by
  apply Finset.sum_le_sum
  intro language hlanguage
  exact hmono hability

/-- Expected activation is monotone when the unfamiliar-language set expands. -/
theorem specialist_expansion_mono_candidates
    {Language : Type*} {smaller larger : Finset Language} (commonIncrement : ℝ → ℝ)
    (hnonneg : ∀ ability, 0 ≤ commonIncrement ability) (hsubset : smaller ⊆ larger)
    (ability : ℝ) :
    (∑ _language ∈ smaller, commonIncrement ability) ≤
      ∑ _language ∈ larger, commonIncrement ability := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hsubset fun _ _ _ => hnonneg ability

/-- Lower repository entry costs weakly increase expected repository access. -/
theorem repository_expected_expansion
    {Repository : Type*} (repositories : Finset Repository)
    (oldCost newCost : Repository → ℝ)
    (opportunityLaw : Repository → MeasureTheory.Measure ℝ)
    (hprobability : ∀ repository, opportunityLaw repository Set.univ = 1)
    (hcost : ∀ repository ∈ repositories, newCost repository ≤ oldCost repository) :
    (∑ repository ∈ repositories,
        (opportunityLaw repository).real (Set.Ici (oldCost repository))) ≤
      ∑ repository ∈ repositories,
        (opportunityLaw repository).real (Set.Ici (newCost repository)) := by
  apply Finset.sum_le_sum
  intro repository hrepository
  letI : MeasureTheory.IsProbabilityMeasure (opportunityLaw repository) :=
    ⟨hprobability repository⟩
  exact MeasureTheory.measureReal_mono (Set.Ici_subset_Ici.mpr (hcost repository hrepository))

/-- Positive opportunity mass in one activation band gives strict expected expansion. -/
theorem repository_expected_expansion_strict
    {Repository : Type*} (repositories : Finset Repository)
    (oldCost newCost : Repository → ℝ)
    (opportunityLaw : Repository → MeasureTheory.Measure ℝ)
    (hprobability : ∀ repository, opportunityLaw repository Set.univ = 1)
    (hcost : ∀ repository ∈ repositories, newCost repository ≤ oldCost repository)
    (hband : ∃ repository ∈ repositories,
      0 < (opportunityLaw repository).real
        (Set.Ico (newCost repository) (oldCost repository))) :
    (∑ repository ∈ repositories,
        (opportunityLaw repository).real (Set.Ici (oldCost repository))) <
      ∑ repository ∈ repositories,
        (opportunityLaw repository).real (Set.Ici (newCost repository)) := by
  apply Finset.sum_lt_sum
  · intro repository hrepository
    letI : MeasureTheory.IsProbabilityMeasure (opportunityLaw repository) :=
      ⟨hprobability repository⟩
    exact MeasureTheory.measureReal_mono
      (Set.Ici_subset_Ici.mpr (hcost repository hrepository))
  · rcases hband with ⟨repository, hrepository, hpositive⟩
    refine ⟨repository, hrepository, ?_⟩
    letI : MeasureTheory.IsProbabilityMeasure (opportunityLaw repository) :=
      ⟨hprobability repository⟩
    have hdiff :
        (opportunityLaw repository).real
            (Set.Ici (newCost repository) \ Set.Ici (oldCost repository)) =
          (opportunityLaw repository).real (Set.Ici (newCost repository)) -
            (opportunityLaw repository).real (Set.Ici (oldCost repository)) :=
      MeasureTheory.measureReal_diff
        (Set.Ici_subset_Ici.mpr (hcost repository hrepository)) measurableSet_Ici
        (by finiteness)
    rw [Set.Ici_diff_Ici] at hdiff
    linarith

end

end QX26AgenticDelegation
