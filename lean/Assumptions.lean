import QX26AgenticDelegation.MainTheorems

/-!
# Paper Assumptions: Agentic Delegation and the Language Frontier

This file records the three assumptions explicitly named by the source paper.
They are model conditions, not substitute proofs of any paper proposition.
-/

namespace QX26AgenticDelegation

/-- Assumption 1: conversational augmentation needs existing language skill. -/
abbrev assumption_augmentation_requires_foothold
    (gamma unfamiliarSkill familiarSkill copilotCost : ℝ) : Prop :=
  gamma * unfamiliarSkill - copilotCost ≤ 0 ∧
    0 < gamma * familiarSkill - copilotCost

/-- Assumption 2: verification cost and residual error fall with the stated inputs. -/
abbrev assumption_verification_technology
    (verificationCost : ℝ → ℝ → ℝ)
    (residualVariance : ℝ → ℝ → ℝ → ℝ) : Prop :=
  (∀ ability skill,
      ∃ derivative,
        HasDerivAt (fun x => verificationCost x skill) derivative ability ∧
          derivative < 0) ∧
    (∀ ability skill,
      ∃ derivative,
        HasDerivAt (fun x => verificationCost ability x) derivative skill ∧
          derivative ≤ 0) ∧
    (∀ ability skill capability,
      ∃ derivative,
        HasDerivAt
            (fun x => residualVariance x skill capability) derivative ability ∧
          derivative ≤ 0) ∧
    (∀ ability skill capability,
      ∃ derivative,
        HasDerivAt
            (fun x => residualVariance ability x capability) derivative skill ∧
          derivative ≤ 0) ∧
    ∀ ability skill capability,
      ∃ derivative,
        HasDerivAt
            (fun x => residualVariance ability skill x) derivative capability ∧
          derivative ≤ 0

/-- Assumption 3: unfamiliar-language candidates have a common activation increment. -/
abbrev assumption_comparable_unfamiliar_language_candidates
    {Language : Type*} (unfamiliar : Finset Language)
    (activationIncrement : Language → ℝ → ℝ) (commonIncrement : ℝ → ℝ) :
    Prop :=
  (∀ language ∈ unfamiliar, ∀ ability,
      activationIncrement language ability = commonIncrement ability) ∧
    (∀ ability, 0 ≤ commonIncrement ability) ∧
    Monotone commonIncrement

end QX26AgenticDelegation
