import QX26AgenticDelegation.Assumptions

/-!
# Human-Facing Paper Interface: Agentic Delegation and the Language Frontier

Each transparent declaration below is one source-facing semantic target. The
paired exact-type proof endpoint is kept separately in `ProofInterface.lean`.
-/

namespace QX26AgenticDelegation

noncomputable section

/-! ## Source-model definitions -/

/-- The three certainty-equivalent production-mode surpluses in Section 3. -/
def production_mode_surplusesSpec
    (opportunity skill mean ability capability delegationShare riskAversion precision
      activationCost copilotGain copilotCost delegationCost : ℝ)
    (agentCompetence : ℝ → ℝ) (verificationCost : ℝ → ℝ → ℝ)
    (residualVariance : ℝ → ℝ → ℝ → ℝ)
    (hskill : 0 ≤ skill ∧ skill ≤ 1) (hability : 0 ≤ ability)
    (hdelegationShare : 0 < delegationShare ∧ delegationShare ≤ 1)
    (hriskAversion : 0 < riskAversion) (hprecision : 0 < precision) : Prop :=
  soloSurplus opportunity skill mean riskAversion precision activationCost =
      opportunity + skill * mean - riskAversion * skill ^ 2 / (2 * precision) -
        activationCost ∧
    copilotSurplus opportunity skill mean riskAversion precision activationCost
        copilotGain copilotCost =
      soloSurplus opportunity skill mean riskAversion precision activationCost +
        copilotGain * skill - copilotCost ∧
    delegationSurplus opportunity skill mean ability capability delegationShare
        riskAversion precision activationCost delegationCost agentCompetence
        verificationCost residualVariance =
      opportunity + (1 - delegationShare) * skill * mean +
        delegationShare * ability * agentCompetence capability -
        verificationCost ability skill - delegationCost - activationCost -
        riskAversion / 2 *
          (((1 - delegationShare) ^ 2 * skill ^ 2) / precision +
            residualVariance ability skill capability)

/-- The old/new menus, activity indicator, and finite monthly language count. -/
def generation_menus_and_activitySpec : Prop :=
  ∀ {Language : Type*} (languages : Finset Language)
      (solo copilot delegation : Language → ℝ),
    (∀ language,
      generationOneValue (solo language) (copilot language) =
        max (solo language) (copilot language)) ∧
    (∀ language,
      generationTwoValue (solo language) (copilot language) (delegation language) =
        max (max (solo language) (copilot language)) (delegation language)) ∧
    (∀ language,
      activityIndicator (generationOneValue (solo language) (copilot language)) =
        if 0 ≤ max (solo language) (copilot language) then 1 else 0) ∧
    activeLanguageCount languages (fun language =>
        generationOneValue (solo language) (copilot language)) =
      ∑ language ∈ languages,
        if 0 ≤ max (solo language) (copilot language) then 1 else 0

/-- Solo, conversational, delegation, and effective activation thresholds. -/
def activation_thresholdsSpec
    (skill mean ability capability delegationShare riskAversion precision activationCost
      copilotGain copilotCost delegationCost : ℝ)
    (agentCompetence : ℝ → ℝ) (verificationCost : ℝ → ℝ → ℝ)
    (residualVariance : ℝ → ℝ → ℝ → ℝ)
    (hprecision : 0 < precision) : Prop :=
  soloThreshold skill mean riskAversion precision activationCost =
      activationCost - skill * mean + riskAversion * skill ^ 2 / (2 * precision) ∧
    copilotThreshold skill mean riskAversion precision activationCost copilotGain copilotCost =
      soloThreshold skill mean riskAversion precision activationCost -
        (copilotGain * skill - copilotCost) ∧
    generationOneThreshold
        (soloThreshold skill mean riskAversion precision activationCost)
        copilotGain skill copilotCost =
      min (soloThreshold skill mean riskAversion precision activationCost)
        (copilotThreshold skill mean riskAversion precision activationCost
          copilotGain copilotCost) ∧
    delegationThreshold skill mean ability capability delegationShare riskAversion precision
        activationCost delegationCost agentCompetence verificationCost residualVariance =
      activationCost - (1 - delegationShare) * skill * mean -
        delegationShare * ability * agentCompetence capability +
        verificationCost ability skill + delegationCost +
        riskAversion / 2 *
          (((1 - delegationShare) ^ 2 * skill ^ 2) / precision +
            residualVariance ability skill capability) ∧
    generationTwoThreshold
        (generationOneThreshold
          (soloThreshold skill mean riskAversion precision activationCost)
          copilotGain skill copilotCost)
        (delegationThreshold skill mean ability capability delegationShare riskAversion
          precision activationCost delegationCost agentCompetence verificationCost
          residualVariance) =
      min
        (generationOneThreshold
          (soloThreshold skill mean riskAversion precision activationCost)
          copilotGain skill copilotCost)
        (delegationThreshold skill mean ability capability delegationShare riskAversion
          precision activationCost delegationCost agentCompetence verificationCost
          residualVariance) ∧
    (copilotGain * skill - copilotCost ≤ 0 →
      generationOneThreshold
          (soloThreshold skill mean riskAversion precision activationCost)
          copilotGain skill copilotCost =
        soloThreshold skill mean riskAversion precision activationCost) ∧
    soloThreshold skill mean riskAversion precision activationCost -
        delegationThreshold skill mean ability capability delegationShare riskAversion
          precision activationCost delegationCost agentCompetence verificationCost
          residualVariance =
      delegationShare * (ability * agentCompetence capability - skill * mean) -
        verificationCost ability skill - delegationCost +
        riskAversion / 2 *
          (((2 * delegationShare - delegationShare ^ 2) * skill ^ 2) / precision -
            residualVariance ability skill capability)

/-- The appendix's Normal-learning precision and posterior-mean update. -/
def learning_after_agentic_interactionSpec : Prop :=
  ∀ {Signal : Type*} (signals : Finset Signal)
      (signalValue signalVariance : Signal → ℝ) (priorPrecision priorMean : ℝ),
    signals.Nonempty →
    (∀ signal ∈ signals, 0 < signalVariance signal) →
    let signalPrecision := totalSignalPrecision signals signalVariance
    let weightedSignalMean :=
      precisionWeightedSignalMean signals signalValue signalVariance
    signalPrecision = ∑ signal ∈ signals, 1 / signalVariance signal ∧
      weightedSignalMean =
        (∑ signal ∈ signals, signalValue signal / signalVariance signal) /
          signalPrecision ∧
      posteriorPrecision priorPrecision signalPrecision = priorPrecision + signalPrecision ∧
      posteriorMean priorPrecision priorMean signalPrecision weightedSignalMean =
        (priorPrecision * priorMean + signalPrecision * weightedSignalMean) /
          (priorPrecision + signalPrecision) ∧
      priorPrecision < posteriorPrecision priorPrecision signalPrecision

/-! ## Main-text propositions -/

/-- Proposition 1: menu expansion weakly expands the language frontier path by path. -/
def frontier_expansionSpec : Prop :=
  ∀ {Language : Type*} (languages : Finset Language)
      (solo copilot delegation : Language → ℝ),
    (∀ language ∈ languages,
      activityIndicator (generationOneValue (solo language) (copilot language)) ≤
        activityIndicator
          (generationTwoValue (solo language) (copilot language) (delegation language))) ∧
    activeLanguageCount languages (fun language =>
        generationOneValue (solo language) (copilot language)) ≤
      activeLanguageCount languages (fun language =>
        generationTwoValue (solo language) (copilot language) (delegation language))

/-- Proposition 2: strict threshold reductions generate the activation band and its CDF mass. -/
def activation_band_unfamiliar_languagesSpec : Prop :=
  (∀ (gamma unfamiliarSkill copilotCost delegationThreshold soloThreshold opportunity : ℝ)
      (opportunityLaw : MeasureTheory.Measure ℝ),
    gamma * unfamiliarSkill - copilotCost ≤ 0 →
    0 < soloThreshold - delegationThreshold →
    opportunityLaw Set.univ = 1 →
    (∀ x, opportunityLaw {x} = 0) →
    (((if delegationThreshold ≤ opportunity then 1 else 0) : ℤ) -
          (if soloThreshold ≤ opportunity then 1 else 0) =
        (if delegationThreshold ≤ opportunity ∧ opportunity < soloThreshold then 1 else 0)) ∧
      opportunityLaw.real (Set.Ico delegationThreshold soloThreshold) =
        opportunityLaw.real (Set.Iic soloThreshold) -
          opportunityLaw.real (Set.Iic delegationThreshold)) ∧
  ∀ {Language : Type*} (languages : Finset Language)
      (generationOne generationTwo : Language → ℝ)
      (opportunityLaw : Language → MeasureTheory.Measure ℝ),
    (∀ language, opportunityLaw language Set.univ = 1) →
    (∀ language x, opportunityLaw language {x} = 0) →
    (∀ language ∈ languages, generationTwo language ≤ generationOne language) →
    (∑ language ∈ languages,
        (opportunityLaw language).real
          (Set.Ico (generationTwo language) (generationOne language))) =
        ∑ language ∈ languages,
          ((opportunityLaw language).real (Set.Iic (generationOne language)) -
            (opportunityLaw language).real (Set.Iic (generationTwo language))) ∧
      0 ≤ ∑ language ∈ languages,
        ((opportunityLaw language).real (Set.Iic (generationOne language)) -
          (opportunityLaw language).real (Set.Iic (generationTwo language)))

/--
Proposition 3, with the interior-hazard and nonempty-frontier conditions needed
for the source's printed strict-growth and strict-concavity clause.
-/
def dynamic_cumulative_language_effectSpec : Prop :=
  ∀ {Language : Type*} (unfamiliar : Finset Language)
      (oldHazard newHazard : Language → ℝ) (horizon : ℕ),
    let cumulativeGap : ℕ → ℝ := fun eventTime =>
      ∑ language ∈ unfamiliar,
        ((1 - oldHazard language) ^ (eventTime + 1) -
          (1 - newHazard language) ^ (eventTime + 1))
    (∀ language ∈ unfamiliar, 0 ≤ oldHazard language) →
    (∀ language ∈ unfamiliar, newHazard language ≤ 1) →
    (∀ language ∈ unfamiliar, oldHazard language ≤ newHazard language) →
    0 ≤ cumulativeGap horizon ∧
      (unfamiliar.Nonempty →
        (∀ language ∈ unfamiliar, oldHazard language = 0) →
        (∀ language ∈ unfamiliar, 0 < newHazard language) →
        (∀ language ∈ unfamiliar, newHazard language < 1) →
        cumulativeGap horizon < cumulativeGap (horizon + 1) ∧
          cumulativeGap (horizon + 2) - cumulativeGap (horizon + 1) <
            cumulativeGap (horizon + 1) - cumulativeGap horizon)

/-! ## Appendix propositions -/

/-- Proposition 4: symmetric unfamiliar candidates favor high-ability specialists. -/
def specialist_and_ability_heterogeneitySpec : Prop :=
  ∀ {Language : Type*} (unfamiliar : Finset Language)
      (activationIncrement : Language → ℝ → ℝ) (commonIncrement : ℝ → ℝ),
    (∀ language ∈ unfamiliar, ∀ ability,
      activationIncrement language ability = commonIncrement ability) →
    (∀ ability, 0 ≤ commonIncrement ability) →
    Monotone commonIncrement →
    (∀ ability,
      (∑ language ∈ unfamiliar, activationIncrement language ability) =
        (unfamiliar.card : ℝ) * commonIncrement ability) ∧
    (∀ {ability ability'}, ability ≤ ability' →
      (∑ language ∈ unfamiliar, commonIncrement ability) ≤
        ∑ language ∈ unfamiliar, commonIncrement ability') ∧
    ∀ (larger : Finset Language), unfamiliar ⊆ larger → ∀ ability,
      (∑ language ∈ unfamiliar, commonIncrement ability) ≤
        ∑ language ∈ larger, commonIncrement ability

/-- Proposition 5: lower language entry costs expand expected repository access. -/
def repository_expansionSpec : Prop :=
  ∀ {Repository : Type*} (repositories : Finset Repository)
      (oldCost newCost : Repository → ℝ)
      (opportunityLaw : Repository → MeasureTheory.Measure ℝ),
    (∀ repository, opportunityLaw repository Set.univ = 1) →
    (∀ repository ∈ repositories, newCost repository ≤ oldCost repository) →
    ((∑ repository ∈ repositories,
          (opportunityLaw repository).real (Set.Ici (oldCost repository))) ≤
      (∑ repository ∈ repositories,
          (opportunityLaw repository).real (Set.Ici (newCost repository)))) ∧
    ((∃ repository ∈ repositories,
        0 < (opportunityLaw repository).real
          (Set.Ico (newCost repository) (oldCost repository))) →
      (∑ repository ∈ repositories,
          (opportunityLaw repository).real (Set.Ici (oldCost repository))) <
        ∑ repository ∈ repositories,
          (opportunityLaw repository).real (Set.Ici (newCost repository)))

end

end QX26AgenticDelegation
