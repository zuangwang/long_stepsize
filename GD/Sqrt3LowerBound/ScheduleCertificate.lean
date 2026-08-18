import GD.Sqrt3LowerBound.ScheduleNormalization

/-!
# Certificate bounds for an actual schedule

This file instantiates the normalized entropy theorem with the chronological
rank-prefix chain of `Schedule.lean`.  The conclusion is existential: it
returns the concrete marked subset that carries the stated contribution.
-/

namespace GD.Sqrt3LowerBound

open scoped BigOperators

theorem rankPrefix_chronologicalDensity {T : ℕ} {α : Fin T → ℝ}
    (hα : ∀ t, 0 ≤ α t) (q : ℕ)
    (hq : q ≤ positiveSurplusCount α) :
    let c := rankPrefix α q hq
    let hc : ∀ t ∈ c, 0 < stepSurplus α t :=
      fun _ ht ↦ rankPrefix_surplus_pos α q hq ht
    let d := scheduleChainData α hα c hc
    d.chronologicalDensity
        (rankMass (positiveSurplusCount α) (cappedMass α)
          (rankedSurplus α) q) =
      rankDensity (positiveSurplusCount α) (cappedMass α)
        (rankedSurplus α) q := by
  dsimp only
  unfold ChainData.chronologicalDensity rankDensity
  rw [sum_scheduleChain_delta_map, rankPrefix_sum_map, rankPrefix_card]

/-- The abstract half-density result specialized to the actual schedule and
the actual prefix of its `q` largest surpluses. -/
theorem scheduleHalfDensityContribution {T : ℕ} {α : Fin T → ℝ}
    (hα : ∀ t, 0 ≤ α t) (q : ℕ) (hq2 : 2 ≤ q)
    (hq : q ≤ positiveSurplusCount α)
    (hdensity : rankDensity (positiveSurplusCount α) (cappedMass α)
      (rankedSurplus α) q ≤ densityThreshold) :
    HasChainContribution α hα
      (1 / (5 * rankMass (positiveSurplusCount α) (cappedMass α)
        (rankedSurplus α) q)) := by
  let c := rankPrefix α q hq
  let hc : ∀ t ∈ c, 0 < stepSurplus α t :=
    fun _ ht ↦ rankPrefix_surplus_pos α q hq ht
  let d := scheduleChainData α hα c hc
  let mass := rankMass (positiveSurplusCount α) (cappedMass α)
    (rankedSurplus α) q
  have hcard : c.card = q := rankPrefix_card α q hq
  have hJ2 : 2 ≤ c.card := by omega
  have hJ1 : 1 ≤ c.card := by omega
  have hJreal : ((c.card - 1 : ℕ) : ℝ) + 1 = (c.card : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hJ1
  have hmass : 0 < mass := by
    dsimp [mass]
    apply rankMass_pos (positiveSurplusCount α) (cappedMass α)
      (rankedSurplus α) q hq (cappedMass_pos hα)
    intro i hi
    exact (rankedSurplus_pos α hi).le
  have hpartition :
      (∑ i, d.omega i) + (1 + d.terminalGap) = mass := by
    dsimp [d, mass, c, hc]
    exact scheduleChain_rankMass_partition hα q hq
  have hdensityEq : d.chronologicalDensity mass =
      rankDensity (positiveSurplusCount α) (cappedMass α)
        (rankedSurplus α) q := by
    dsimp [d, mass, c, hc]
    exact rankPrefix_chronologicalDensity hα q hq
  have hsumB :
      (∑ i ∈ Finset.range ((c.card - 1) + 1),
          (d.normalizedState mass hJ1 hmass i).b) =
        (c.card : ℝ) - d.normalizedEndMass mass := by
    simpa [Nat.sub_add_cancel hJ1] using
      d.normalized_sum_b mass hJ1 hmass hpartition
  have hsumU :
      (∑ i ∈ Finset.range ((c.card - 1) + 1),
          (d.normalizedState mass hJ1 hmass i).u) =
        2 * (c.card : ℝ) *
          rankDensity (positiveSurplusCount α) (cappedMass α)
            (rankedSurplus α) q := by
    have hu := d.normalized_sum_u mass hJ1 hmass
    rw [hdensityEq] at hu
    simpa [Nat.sub_add_cancel hJ1] using hu
  have hcert :
      1 / (2 * mass *
        inverseChainProduct (d.normalizedState mass hJ1 hmass) (c.card - 1)
          (d.normalizedTerminal mass)) ≤ d.contribution := by
    rw [d.reciprocal_inverseChainProduct_eq_contribution mass hJ2 hmass]
  have hbound := halfDensityCertificate
    (d.normalizedState mass hJ1 hmass) (c.card - 1) (by omega)
    (d.normalizedTerminal mass) mass
    (rankDensity (positiveSurplusCount α) (cappedMass α)
      (rankedSurplus α) q)
    (d.normalizedEndMass mass) d.contribution
    (d.normalizedTerminal_pos mass hJ1 hmass)
    (by simpa only [hJreal] using
      d.normalizedTerminal_lt mass hJ1 hmass hpartition)
    hmass (d.normalizedEndMass_pos mass hJ1 hmass)
    (by simpa only [hJreal] using hsumB)
    (by simpa only [hJreal] using hsumU)
    hcert hdensity
  exact ⟨c, hc, hbound⟩

end GD.Sqrt3LowerBound
