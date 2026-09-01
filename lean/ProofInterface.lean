import QX26AgenticDelegation.PaperInterface

/-!
# Proof Interface: Agentic Delegation and the Language Frontier of Software Developers: A Model and Evidence from Claude Code on GitHub

This file contains exact-type proof endpoints for the transparent propositions
in `PaperInterface.lean`. It is not a human semantic-review surface: one source
claim is reviewed once, against its expanded `...Spec : Prop` declaration.
-/

namespace QX26AgenticDelegation

noncomputable section

theorem production_mode_surpluses
    (opportunity skill mean ability capability delegationShare riskAversion precision
      activationCost copilotGain copilotCost delegationCost : ℝ)
    (agentCompetence : ℝ → ℝ) (verificationCost : ℝ → ℝ → ℝ)
    (residualVariance : ℝ → ℝ → ℝ → ℝ)
    (hskill : 0 ≤ skill ∧ skill ≤ 1) (hability : 0 ≤ ability)
    (hdelegationShare : 0 < delegationShare ∧ delegationShare ≤ 1)
    (hriskAversion : 0 < riskAversion) (hprecision : 0 < precision) :
    production_mode_surplusesSpec opportunity skill mean ability capability delegationShare
      riskAversion precision activationCost copilotGain copilotCost delegationCost
      agentCompetence verificationCost residualVariance hskill hability hdelegationShare
      hriskAversion hprecision := by
  simp [production_mode_surplusesSpec, soloSurplus, copilotSurplus, delegationSurplus]

theorem generation_menus_and_activity : generation_menus_and_activitySpec := by
  intro Language languages solo copilot delegation
  simp [generationOneValue, generationTwoValue, activityIndicator, activeLanguageCount]

theorem activation_thresholds
    (skill mean ability capability delegationShare riskAversion precision activationCost
      copilotGain copilotCost delegationCost : ℝ)
    (agentCompetence : ℝ → ℝ) (verificationCost : ℝ → ℝ → ℝ)
    (residualVariance : ℝ → ℝ → ℝ → ℝ)
    (hprecision : 0 < precision) :
    activation_thresholdsSpec skill mean ability capability delegationShare riskAversion
      precision activationCost copilotGain copilotCost delegationCost agentCompetence
      verificationCost residualVariance hprecision := by
  unfold activation_thresholdsSpec
  refine ⟨rfl, rfl, ?_, rfl, rfl, ?_, ?_⟩
  · simpa [generationOneThreshold, copilotThreshold] using
      (min_sub_sub_left
        (soloThreshold skill mean riskAversion precision activationCost) 0
        (copilotGain * skill - copilotCost)).symm
  · intro hfoothold
    simp [generationOneThreshold, max_eq_left hfoothold]
  · simp only [soloThreshold, delegationThreshold]
    ring

theorem learning_after_agentic_interaction : learning_after_agentic_interactionSpec := by
  intro Signal signals signalValue signalVariance priorPrecision priorMean hne hvariance
  dsimp only
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  exact lt_add_of_pos_right priorPrecision
    (totalSignalPrecision_pos signals signalVariance hne hvariance)

theorem frontier_expansion : frontier_expansionSpec := by
  intro Language languages solo copilot delegation
  constructor
  · intro language hlanguage
    apply activityIndicator_mono
    simpa [generationOneValue, generationTwoValue] using
      (le_max_left (max (solo language) (copilot language)) (delegation language))
  · unfold activeLanguageCount
    apply Finset.sum_le_sum
    intro language hlanguage
    apply activityIndicator_mono
    simpa [generationOneValue, generationTwoValue] using
      (le_max_left (max (solo language) (copilot language)) (delegation language))

theorem activation_band_unfamiliar_languages :
    activation_band_unfamiliar_languagesSpec := by
  constructor
  · intro gamma unfamiliarSkill copilotCost lower upper opportunity opportunityLaw
      hfoothold hreduction hprobability hatomless
    have hthreshold : lower < upper := sub_pos.mp hreduction
    exact ⟨threshold_indicator_sub_eq_band hthreshold,
      bandProbability_eq_cdf_sub opportunityLaw hprobability hatomless hthreshold.le⟩
  · intro Language languages generationOne generationTwo opportunityLaw
      hprobability hatomless hthreshold
    exact expected_band_expansion_nonneg languages generationOne generationTwo
      opportunityLaw hprobability hatomless hthreshold

theorem dynamic_cumulative_language_effect : dynamic_cumulative_language_effectSpec := by
  intro Language unfamiliar oldHazard newHazard horizon
  dsimp only
  intro hold_nonneg hnew_le_one hhazard
  constructor
  · exact cumulative_gap_nonneg unfamiliar oldHazard newHazard horizon
      hold_nonneg hnew_le_one hhazard
  · intro hne hold_zero hnew_pos hnew_lt_one
    have hgap (eventTime : ℕ) :
        (∑ language ∈ unfamiliar,
            ((1 - oldHazard language) ^ (eventTime + 1) -
              (1 - newHazard language) ^ (eventTime + 1))) =
          ∑ language ∈ unfamiliar,
            (1 - (1 - newHazard language) ^ (eventTime + 1)) := by
      apply Finset.sum_congr rfl
      intro language hlanguage
      rw [hold_zero language hlanguage]
      norm_num
    constructor
    · rw [hgap horizon, hgap (horizon + 1)]
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        closed_frontier_gap_strict_mono unfamiliar newHazard hne hnew_pos
          hnew_lt_one horizon
    · rw [hgap (horizon + 2), hgap (horizon + 1), hgap horizon]
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        closed_frontier_gap_strict_concave unfamiliar newHazard hne hnew_pos
          hnew_lt_one horizon

theorem specialist_and_ability_heterogeneity :
    specialist_and_ability_heterogeneitySpec := by
  intro Language unfamiliar activationIncrement commonIncrement hsame hnonneg hmono
  refine ⟨?_, ?_, ?_⟩
  · intro ability
    calc
      (∑ language ∈ unfamiliar, activationIncrement language ability) =
          ∑ language ∈ unfamiliar, commonIncrement ability := by
        apply Finset.sum_congr rfl
        intro language hlanguage
        exact hsame language hlanguage ability
      _ = (unfamiliar.card : ℝ) * commonIncrement ability := by simp
  · intro ability ability' hability
    exact specialist_expansion_mono_ability unfamiliar commonIncrement hmono hability
  · intro larger hsubset ability
    exact specialist_expansion_mono_candidates commonIncrement hnonneg hsubset ability

theorem repository_expansion : repository_expansionSpec := by
  intro Repository repositories oldCost newCost opportunityLaw hprobability hcost
  constructor
  · exact repository_expected_expansion repositories oldCost newCost opportunityLaw
      hprobability hcost
  · intro hband
    exact repository_expected_expansion_strict repositories oldCost newCost opportunityLaw
      hprobability hcost hband

end

end QX26AgenticDelegation
