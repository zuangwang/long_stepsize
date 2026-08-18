import GD.Sqrt3LowerBound.RankCutoff

/-!
# Schedules, ranked surpluses, and chronological marked chains

This file supplies the combinatorial objects that were implicit in the
scalar interfaces of the earlier development.  A schedule is a nonnegative
finite vector.  Positive surpluses are ranked by value (with the time index
as a deterministic tie breaker), while marked-chain blocks are restored to
chronological order.
-/

namespace GD.Sqrt3LowerBound

open scoped BigOperators

/-- Excess over the unit cap at one normalized GD step. -/
noncomputable def stepSurplus {T : ℕ} (α : Fin T → ℝ) (t : Fin T) : ℝ :=
  max (α t - 1) 0

/-- The capped part of the schedule, including the leading unit mass. -/
noncomputable def cappedMass {T : ℕ} (α : Fin T → ℝ) : ℝ :=
  1 + ∑ t, min (α t) 1

/-- Time indices carrying a strictly positive surplus. -/
noncomputable def positiveSurplusIndices {T : ℕ} (α : Fin T → ℝ) : Finset (Fin T) :=
  Finset.univ.filter fun t ↦ 0 < stepSurplus α t

/-- Number of positive surpluses. -/
noncomputable def positiveSurplusCount {T : ℕ} (α : Fin T → ℝ) : ℕ :=
  (positiveSurplusIndices α).card

theorem stepSurplus_nonneg {T : ℕ} (α : Fin T → ℝ) (t : Fin T) :
    0 ≤ stepSurplus α t := by
  simp [stepSurplus]

theorem step_eq_capped_add_surplus {T : ℕ} {α : Fin T → ℝ}
    (_hα : ∀ t, 0 ≤ α t) (t : Fin T) :
    α t = min (α t) 1 + stepSurplus α t := by
  unfold stepSurplus
  rcases le_total (α t) 1 with h | h
  · rw [min_eq_left h, max_eq_right (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, max_eq_left (sub_nonneg.mpr h)]
    ring

theorem cappedMass_pos {T : ℕ} {α : Fin T → ℝ}
    (hα : ∀ t, 0 ≤ α t) : 0 < cappedMass α := by
  unfold cappedMass
  have hterm : ∀ t, 0 ≤ min (α t) 1 := by
    intro t
    exact le_min (hα t) (by norm_num)
  have hsum : 0 ≤ ∑ t, min (α t) 1 := Finset.sum_nonneg fun _ _ ↦ hterm _
  linarith

theorem cappedMass_le_horizon {T : ℕ} {α : Fin T → ℝ}
    (_hα : ∀ t, 0 ≤ α t) : cappedMass α ≤ T + 1 := by
  unfold cappedMass
  have hsum : (∑ t, min (α t) 1) ≤ ∑ _t : Fin T, (1 : ℝ) := by
    exact Finset.sum_le_sum fun _ _ ↦ min_le_right _ _
  norm_num [Nat.cast_add, Nat.cast_one] at hsum ⊢
  linarith

theorem positiveSurplusCount_le {T : ℕ} (α : Fin T → ℝ) :
    positiveSurplusCount α ≤ T := by
  unfold positiveSurplusCount positiveSurplusIndices
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp)

/-! ## Deterministic ranking -/

/-- The order first compares surplus in descending order and then time in
ascending order.  The second component makes the key injective. -/
@[reducible] noncomputable def surplusLinearOrder {T : ℕ}
    (α : Fin T → ℝ) : LinearOrder (Fin T) :=
  LinearOrder.lift' (fun t ↦ toLex (-stepSurplus α t, (t : ℕ))) (by
    intro i j hij
    exact Fin.ext (congrArg (Prod.snd ∘ ofLex) hij))

/-- Positive-surplus times, ranked by decreasing surplus. -/
noncomputable def rankedTimes {T : ℕ} (α : Fin T → ℝ) : List (Fin T) := by
  letI := surplusLinearOrder α
  exact (positiveSurplusIndices α).sort (surplusLinearOrder α).le

theorem rankedTimes_length {T : ℕ} (α : Fin T → ℝ) :
    (rankedTimes α).length = positiveSurplusCount α := by
  unfold rankedTimes positiveSurplusCount
  letI := surplusLinearOrder α
  exact Finset.length_sort _

theorem rankedTimes_nodup {T : ℕ} (α : Fin T → ℝ) :
    (rankedTimes α).Nodup := by
  unfold rankedTimes
  letI := surplusLinearOrder α
  exact Finset.sort_nodup _ _

theorem rankedTimes_mem_iff {T : ℕ} (α : Fin T → ℝ) (t : Fin T) :
    t ∈ rankedTimes α ↔ 0 < stepSurplus α t := by
  unfold rankedTimes positiveSurplusIndices
  letI := surplusLinearOrder α
  rw [Finset.mem_sort]
  simp

/-- The time at zero-based surplus rank `i`. -/
noncomputable def rankedTime {T : ℕ} (α : Fin T → ℝ)
    (i : Fin (positiveSurplusCount α)) : Fin T :=
  (rankedTimes α).get ⟨i, by simp [rankedTimes_length]⟩

theorem rankedTime_injective {T : ℕ} (α : Fin T → ℝ) :
    Function.Injective (rankedTime α) := by
  intro i j hij
  apply Fin.ext
  have hn := rankedTimes_nodup α
  exact (List.getElem_inj hn).mp hij

theorem rankedTime_surplus_pos {T : ℕ} (α : Fin T → ℝ)
    (i : Fin (positiveSurplusCount α)) :
    0 < stepSurplus α (rankedTime α i) := by
  rw [← rankedTimes_mem_iff]
  exact List.get_mem _ _

/-- Ranked surplus extended by zero after the last positive rank. -/
noncomputable def rankedSurplus {T : ℕ} (α : Fin T → ℝ) (i : ℕ) : ℝ :=
  if hi : i < positiveSurplusCount α then
    stepSurplus α (rankedTime α ⟨i, hi⟩)
  else 0

theorem rankedSurplus_pos {T : ℕ} (α : Fin T → ℝ) {i : ℕ}
    (hi : i < positiveSurplusCount α) : 0 < rankedSurplus α i := by
  simp only [rankedSurplus, dif_pos hi]
  exact rankedTime_surplus_pos α ⟨i, hi⟩

theorem rankedSurplus_antitone {T : ℕ} (α : Fin T → ℝ) :
    Antitone (rankedSurplus α) := by
  intro i j hij
  by_cases hj : j < positiveSurplusCount α
  · have hi : i < positiveSurplusCount α := lt_of_le_of_lt hij hj
    simp only [rankedSurplus, dif_pos hi, dif_pos hj]
    letI := surplusLinearOrder α
    have hp : List.Pairwise (surplusLinearOrder α).le (rankedTimes α) := by
      unfold rankedTimes
      letI := surplusLinearOrder α
      simpa only using
        (positiveSurplusIndices α).pairwise_sort (surplusLinearOrder α).le
    have hrel := hp.rel_get_of_le (show
      (⟨i, by simpa [rankedTimes_length] using hi⟩ : Fin (rankedTimes α).length) ≤
        ⟨j, by simpa [rankedTimes_length] using hj⟩ from hij)
    have hrel' : (surplusLinearOrder α).le
        ((rankedTimes α).get ⟨i, by simpa [rankedTimes_length] using hi⟩)
        ((rankedTimes α).get ⟨j, by simpa [rankedTimes_length] using hj⟩) := hrel
    change toLex (-stepSurplus α ((rankedTimes α).get ⟨i, _⟩),
        (((rankedTimes α).get ⟨i, _⟩ : Fin T) : ℕ)) ≤
      toLex (-stepSurplus α ((rankedTimes α).get ⟨j, _⟩),
        (((rankedTimes α).get ⟨j, _⟩ : Fin T) : ℕ)) at hrel'
    rw [Prod.Lex.toLex_le_toLex] at hrel'
    have hsurplus :
        stepSurplus α ((rankedTimes α).get ⟨j, by
          simpa [rankedTimes_length] using hj⟩) ≤
        stepSurplus α ((rankedTimes α).get ⟨i, by
          simpa [rankedTimes_length] using hi⟩) := by
      rcases hrel' with hlt | ⟨heq, _⟩
      · exact (neg_lt_neg_iff.mp hlt).le
      · exact neg_le_neg_iff.mp heq.le
    simpa [rankedTime] using hsurplus
  · have hjzero : rankedSurplus α j = 0 := by simp [rankedSurplus, hj]
    rw [hjzero]
    by_cases hi : i < positiveSurplusCount α
    · simpa [rankedSurplus, hi] using
        stepSurplus_nonneg α (rankedTime α ⟨i, hi⟩)
    · simp [rankedSurplus, hi]

/-- The first `q` ranked times, viewed as an unordered marked subset. -/
noncomputable def rankPrefix {T : ℕ} (α : Fin T → ℝ) (q : ℕ)
    (hq : q ≤ positiveSurplusCount α) : Finset (Fin T) :=
  Finset.univ.image fun i : Fin q ↦
    rankedTime α ⟨i, lt_of_lt_of_le i.isLt hq⟩

theorem rankPrefix_card {T : ℕ} (α : Fin T → ℝ) (q : ℕ)
    (hq : q ≤ positiveSurplusCount α) :
    (rankPrefix α q hq).card = q := by
  unfold rankPrefix
  rw [Finset.card_image_of_injective]
  · simp
  · intro i j hij
    apply Fin.ext
    exact congrArg (fun k : Fin (positiveSurplusCount α) ↦ k.val)
      (rankedTime_injective α hij)

theorem rankPrefix_surplus_pos {T : ℕ} (α : Fin T → ℝ) (q : ℕ)
    (hq : q ≤ positiveSurplusCount α) {t : Fin T}
    (ht : t ∈ rankPrefix α q hq) : 0 < stepSurplus α t := by
  simp only [rankPrefix, Finset.mem_image, Finset.mem_univ, true_and] at ht
  obtain ⟨i, rfl⟩ := ht
  exact rankedTime_surplus_pos α _

theorem stepSurplus_eq_sub_of_pos {T : ℕ} {α : Fin T → ℝ} {t : Fin T}
    (ht : 0 < stepSurplus α t) : stepSurplus α t = α t - 1 := by
  unfold stepSurplus at ht ⊢
  have : 0 < α t - 1 := by simpa using ht
  exact max_eq_left this.le

theorem rankPrefix_sum_surplus {T : ℕ} (α : Fin T → ℝ) (q : ℕ)
    (hq : q ≤ positiveSurplusCount α) :
    (∑ t ∈ rankPrefix α q hq, stepSurplus α t) =
      ∑ i ∈ Finset.range q, rankedSurplus α i := by
  unfold rankPrefix
  rw [Finset.sum_image]
  · rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    have hiq : i < q := Finset.mem_range.mp hi
    simp [hiq, rankedSurplus, lt_of_lt_of_le hiq hq]
  · intro i _ j _ hij
    apply Fin.ext
    exact congrArg (fun k : Fin (positiveSurplusCount α) ↦ k.val)
      (rankedTime_injective α hij)

theorem positiveIndices_eq_ranked_image {T : ℕ} (α : Fin T → ℝ) :
    positiveSurplusIndices α =
      Finset.univ.image (rankedTime α) := by
  ext t
  constructor
  · intro ht
    have hmem : t ∈ rankedTimes α := by
      rw [rankedTimes_mem_iff]
      simpa [positiveSurplusIndices] using ht
    obtain ⟨i, hi⟩ := List.get_of_mem hmem
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨⟨i, by simpa [rankedTimes_length] using i.isLt⟩, ?_⟩
    simpa [rankedTime] using hi
  · intro ht
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at ht
    obtain ⟨i, rfl⟩ := ht
    unfold positiveSurplusIndices
    simp [rankedTime_surplus_pos]

theorem sum_rankedSurplus {T : ℕ} (α : Fin T → ℝ) :
    (∑ i ∈ Finset.range (positiveSurplusCount α), rankedSurplus α i) =
      ∑ t, stepSurplus α t := by
  have hpositive :
      (∑ t ∈ positiveSurplusIndices α, stepSurplus α t) =
        ∑ t, stepSurplus α t := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro t _ ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at ht
    exact le_antisymm ht (stepSurplus_nonneg α t)
  rw [← hpositive, positiveIndices_eq_ranked_image]
  rw [Finset.sum_image]
  · rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    have hiN : i < positiveSurplusCount α := Finset.mem_range.mp hi
    simp [rankedSurplus, hiN]
  · intro i _ j _ hij
    exact rankedTime_injective α hij

theorem capped_add_surplus_eq_total {T : ℕ} {α : Fin T → ℝ}
    (hα : ∀ t, 0 ≤ α t) :
    cappedMass α + (∑ t, stepSurplus α t) = 1 + ∑ t, α t := by
  unfold cappedMass
  rw [add_assoc, ← Finset.sum_add_distrib]
  apply congrArg (fun x : ℝ ↦ 1 + x)
  apply Finset.sum_congr rfl
  intro t _
  exact (step_eq_capped_add_surplus hα t).symm

/-! ## Chronological marked-chain data -/

/-- The number of marked times strictly before `t`. -/
noncomputable def marksBefore {T : ℕ} (c : Finset (Fin T)) (t : Fin T) : ℕ :=
  (c.filter fun u ↦ u < t).card

theorem marksBefore_le_card {T : ℕ} (c : Finset (Fin T)) (t : Fin T) :
    marksBefore c t ≤ c.card := by
  unfold marksBefore
  exact Finset.card_filter_le _ _

/-- Sum of unmarked steps in the chronological gap having exactly `i`
marked predecessors.  The terminal gap is obtained by taking `i = c.card`. -/
noncomputable def chronologicalGap {T : ℕ} (α : Fin T → ℝ)
    (c : Finset (Fin T)) (i : ℕ) : ℝ :=
  ∑ t ∈ Finset.univ.filter (fun t ↦ t ∉ c ∧ marksBefore c t = i), α t

theorem chronologicalGap_nonneg {T : ℕ} {α : Fin T → ℝ}
    (hα : ∀ t, 0 ≤ α t) (c : Finset (Fin T)) (i : ℕ) :
    0 ≤ chronologicalGap α c i := by
  unfold chronologicalGap
  exact Finset.sum_nonneg fun t _ ↦ hα t

/-- Marked times restored to chronological order. -/
noncomputable def chronologicalTimes {T : ℕ} (c : Finset (Fin T)) : List (Fin T) :=
  c.sort (· ≤ ·)

theorem chronologicalTimes_length {T : ℕ} (c : Finset (Fin T)) :
    (chronologicalTimes c).length = c.card := Finset.length_sort _

/-- The `i`th marked time in chronological order. -/
noncomputable def chronologicalTime {T : ℕ} (c : Finset (Fin T))
    (i : Fin c.card) : Fin T :=
  (chronologicalTimes c).get ⟨i, by simp [chronologicalTimes_length]⟩

theorem chronologicalTime_mem {T : ℕ} (c : Finset (Fin T)) (i : Fin c.card) :
    chronologicalTime c i ∈ c := by
  rw [← Finset.mem_sort (s := c) (· ≤ ·)]
  exact List.get_mem _ _

theorem chronologicalTime_injective {T : ℕ} (c : Finset (Fin T)) :
    Function.Injective (chronologicalTime c) := by
  intro i j hij
  apply Fin.ext
  exact (List.getElem_inj (Finset.sort_nodup c (· ≤ ·))).mp hij

theorem chronologicalTime_image {T : ℕ} (c : Finset (Fin T)) :
    Finset.univ.image (chronologicalTime c) = c := by
  ext t
  constructor
  · intro ht
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at ht
    obtain ⟨i, rfl⟩ := ht
    exact chronologicalTime_mem c i
  · intro ht
    have hmem : t ∈ chronologicalTimes c := by
      unfold chronologicalTimes
      rwa [Finset.mem_sort]
    obtain ⟨i, hi⟩ := List.get_of_mem hmem
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨⟨i, by simpa [chronologicalTimes_length] using i.isLt⟩, ?_⟩
    simpa [chronologicalTime] using hi

/-- The chronological gaps partition all unmarked steps. -/
theorem sum_chronologicalGap {T : ℕ} (α : Fin T → ℝ)
    (c : Finset (Fin T)) :
    (∑ i : Fin c.card, chronologicalGap α c i) +
        chronologicalGap α c c.card =
      ∑ t ∈ Finset.univ \ c, α t := by
  let g : Fin T → Fin (c.card + 1) := fun t ↦
    ⟨marksBefore c t, Nat.lt_succ_of_le (marksBefore_le_card c t)⟩
  have hf := Finset.sum_fiberwise (Finset.univ \ c) g α
  have hfiber : ∀ j : Fin (c.card + 1),
      (∑ t ∈ Finset.univ \ c with g t = j, α t) =
        chronologicalGap α c j := by
    intro j
    apply Finset.sum_congr
    · ext t
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and, g]
      constructor
      · rintro ⟨htc, hj⟩
        exact ⟨htc, congrArg Fin.val hj⟩
      · rintro ⟨htc, hj⟩
        exact ⟨htc, Fin.ext hj⟩
    · intro _ _
      rfl
  simp_rw [hfiber] at hf
  rw [Fin.sum_univ_castSucc] at hf
  simpa using hf

/-- Compressed chronological data associated with a marked subset. -/
structure ChainData (J : ℕ) where
  omega : Fin J → ℝ
  delta : Fin J → ℝ
  terminalGap : ℝ
  omega_pos : ∀ i, 0 < omega i
  delta_pos : ∀ i, 0 < delta i
  terminalGap_nonneg : 0 ≤ terminalGap

namespace ChainData

noncomputable def scale {J : ℕ} (d : ChainData J) (i : Fin J) : ℝ :=
  d.omega i + d.delta i

noncomputable def terminalScale {J : ℕ} (d : ChainData J) : ℝ :=
  1 + 2 * d.terminalGap

noncomputable def nextScale {J : ℕ} (d : ChainData J) (i : Fin J) : ℝ :=
  if h : i.val + 1 < J then d.scale ⟨i.val + 1, h⟩ else d.terminalScale

noncomputable def rho {J : ℕ} (d : ChainData J) (i : Fin J) : ℝ :=
  d.delta i * d.nextScale i /
    (d.omega i * (d.scale i + d.nextScale i))

noncomputable def contribution {J : ℕ} (d : ChainData J) : ℝ :=
  (1 / d.terminalScale) * ∏ i, d.rho i

theorem scale_pos {J : ℕ} (d : ChainData J) (i : Fin J) : 0 < d.scale i := by
  unfold scale
  exact add_pos (d.omega_pos i) (d.delta_pos i)

theorem terminalScale_pos {J : ℕ} (d : ChainData J) : 0 < d.terminalScale := by
  unfold terminalScale
  linarith [d.terminalGap_nonneg]

theorem nextScale_pos {J : ℕ} (d : ChainData J) (i : Fin J) : 0 < d.nextScale i := by
  unfold nextScale
  split_ifs with h
  · exact d.scale_pos _
  · exact d.terminalScale_pos

theorem rho_pos {J : ℕ} (d : ChainData J) (i : Fin J) : 0 < d.rho i := by
  unfold rho
  exact div_pos (mul_pos (d.delta_pos i) (d.nextScale_pos i))
    (mul_pos (d.omega_pos i) (add_pos (d.scale_pos i) (d.nextScale_pos i)))

theorem contribution_pos {J : ℕ} (d : ChainData J) : 0 < d.contribution := by
  unfold contribution
  exact mul_pos (one_div_pos.mpr d.terminalScale_pos)
    (Finset.prod_pos fun i _ ↦ d.rho_pos i)

end ChainData

/-- The chronological chain induced by marking `c`. -/
noncomputable def scheduleChainData {T : ℕ} (α : Fin T → ℝ)
    (hα : ∀ t, 0 ≤ α t) (c : Finset (Fin T))
    (hc : ∀ t ∈ c, 0 < stepSurplus α t) : ChainData c.card where
  omega i := 1 + chronologicalGap α c i
  delta i := stepSurplus α (chronologicalTime c i)
  terminalGap := chronologicalGap α c c.card
  omega_pos i := by linarith [chronologicalGap_nonneg hα c i]
  delta_pos i := hc _ (chronologicalTime_mem c i)
  terminalGap_nonneg := chronologicalGap_nonneg hα c c.card

theorem scheduleChain_mass_partition {T : ℕ} (α : Fin T → ℝ)
    (hα : ∀ t, 0 ≤ α t) (c : Finset (Fin T))
    (hc : ∀ t ∈ c, 0 < stepSurplus α t) :
    (∑ i, (scheduleChainData α hα c hc).omega i) +
        (1 + (scheduleChainData α hα c hc).terminalGap) =
      1 + c.card + ∑ t ∈ Finset.univ \ c, α t := by
  change (∑ i : Fin c.card, (1 + chronologicalGap α c i)) +
      (1 + chronologicalGap α c c.card) = _
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one]
  rw [← sum_chronologicalGap α c]
  ring

theorem rankPrefix_sum_steps {T : ℕ} {α : Fin T → ℝ}
    (_hα : ∀ t, 0 ≤ α t) (q : ℕ)
    (hq : q ≤ positiveSurplusCount α) :
    (∑ t ∈ rankPrefix α q hq, α t) =
      q + ∑ i ∈ Finset.range q, rankedSurplus α i := by
  calc
    (∑ t ∈ rankPrefix α q hq, α t) =
        ∑ t ∈ rankPrefix α q hq, (1 + stepSurplus α t) := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [stepSurplus_eq_sub_of_pos (rankPrefix_surplus_pos α q hq ht)]
          ring
    _ = q + ∑ t ∈ rankPrefix α q hq, stepSurplus α t := by
      rw [Finset.sum_add_distrib]
      simp [rankPrefix_card]
    _ = q + ∑ i ∈ Finset.range q, rankedSurplus α i := by
      rw [rankPrefix_sum_surplus]

/-- `rankMass` is exactly the leading unit, one capped unit per selected
long step, and the full mass of every unmarked step. -/
theorem rankMass_eq_unmarked {T : ℕ} {α : Fin T → ℝ}
    (hα : ∀ t, 0 ≤ α t) (q : ℕ)
    (hq : q ≤ positiveSurplusCount α) :
    rankMass (positiveSurplusCount α) (cappedMass α)
        (rankedSurplus α) q =
      1 + q + ∑ t ∈ Finset.univ \ rankPrefix α q hq, α t := by
  have hsplit := Finset.sum_sdiff
    (f := α) (show rankPrefix α q hq ⊆ (Finset.univ : Finset (Fin T)) by simp)
  have hselected := rankPrefix_sum_steps hα q hq
  unfold rankMass
  rw [sum_rankedSurplus, capped_add_surplus_eq_total hα]
  linarith

theorem scheduleChain_rankMass_partition {T : ℕ} {α : Fin T → ℝ}
    (hα : ∀ t, 0 ≤ α t) (q : ℕ)
    (hq : q ≤ positiveSurplusCount α) :
    let c := rankPrefix α q hq
    let hc : ∀ t ∈ c, 0 < stepSurplus α t :=
      fun _ ht ↦ rankPrefix_surplus_pos α q hq ht
    (∑ i, (scheduleChainData α hα c hc).omega i) +
        (1 + (scheduleChainData α hα c hc).terminalGap) =
      rankMass (positiveSurplusCount α) (cappedMass α)
        (rankedSurplus α) q := by
  dsimp only
  rw [scheduleChain_mass_partition, rankPrefix_card,
    rankMass_eq_unmarked hα q hq]

theorem sum_scheduleChain_delta_map {T : ℕ} (α : Fin T → ℝ)
    (hα : ∀ t, 0 ≤ α t) (c : Finset (Fin T))
    (hc : ∀ t ∈ c, 0 < stepSurplus α t) (f : ℝ → ℝ) :
    (∑ i, f ((scheduleChainData α hα c hc).delta i)) =
      ∑ t ∈ c, f (stepSurplus α t) := by
  change (∑ i : Fin c.card, f (stepSurplus α (chronologicalTime c i))) = _
  calc
    (∑ i : Fin c.card, f (stepSurplus α (chronologicalTime c i))) =
        ∑ i ∈ (Finset.univ : Finset (Fin c.card)),
          f (stepSurplus α (chronologicalTime c i)) := rfl
    _ = ∑ t ∈ Finset.univ.image (chronologicalTime c),
          f (stepSurplus α t) := by
      symm
      apply Finset.sum_image
      intro i _ j _ hij
      exact chronologicalTime_injective c hij
    _ = ∑ t ∈ c, f (stepSurplus α t) := by
      rw [chronologicalTime_image]

theorem rankPrefix_sum_map {T : ℕ} (α : Fin T → ℝ) (q : ℕ)
    (hq : q ≤ positiveSurplusCount α) (f : ℝ → ℝ) :
    (∑ t ∈ rankPrefix α q hq, f (stepSurplus α t)) =
      ∑ i ∈ Finset.range q, f (rankedSurplus α i) := by
  unfold rankPrefix
  rw [Finset.sum_image]
  · rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    have hiq : i < q := Finset.mem_range.mp hi
    simp [hiq, rankedSurplus, lt_of_lt_of_le hiq hq]
  · intro i _ j _ hij
    apply Fin.ext
    exact congrArg (fun k : Fin (positiveSurplusCount α) ↦ k.val)
      (rankedTime_injective α hij)

theorem sum_rankPrefixChain_delta_inv {T : ℕ} {α : Fin T → ℝ}
    (hα : ∀ t, 0 ≤ α t) (q : ℕ)
    (hq : q ≤ positiveSurplusCount α) :
    let c := rankPrefix α q hq
    let hc : ∀ t ∈ c, 0 < stepSurplus α t :=
      fun _ ht ↦ rankPrefix_surplus_pos α q hq ht
    (∑ i, ((scheduleChainData α hα c hc).delta i)⁻¹) =
      ∑ i ∈ Finset.range q, (rankedSurplus α i)⁻¹ := by
  dsimp only
  rw [sum_scheduleChain_delta_map, rankPrefix_sum_map]

theorem rankPrefixChain_delta_ge_last {T : ℕ} {α : Fin T → ℝ}
    (hα : ∀ t, 0 ≤ α t) (q : ℕ) (hq1 : 1 ≤ q)
    (hq : q ≤ positiveSurplusCount α)
    (i : Fin (rankPrefix α q hq).card) :
    rankedSurplus α (q - 1) ≤
      (scheduleChainData α hα (rankPrefix α q hq)
        (fun _ ht ↦ rankPrefix_surplus_pos α q hq ht)).delta i := by
  change rankedSurplus α (q - 1) ≤
    stepSurplus α (chronologicalTime (rankPrefix α q hq) i)
  have hmem := chronologicalTime_mem (rankPrefix α q hq) i
  simp only [rankPrefix, Finset.mem_image, Finset.mem_univ, true_and] at hmem
  obtain ⟨r, hr⟩ := hmem
  have hrank : rankedSurplus α (q - 1) ≤ rankedSurplus α r :=
    rankedSurplus_antitone α (Nat.le_sub_one_of_lt r.isLt)
  have hrN : r.val < positiveSurplusCount α := lt_of_lt_of_le r.isLt hq
  have hlastN : q - 1 < positiveSurplusCount α := lt_of_lt_of_le
    (Nat.sub_lt hq1 (by omega)) hq
  rw [rankedSurplus, dif_pos hlastN] at hrank ⊢
  rw [rankedSurplus, dif_pos hrN] at hrank
  change rankedTime α ⟨r, _⟩ =
    chronologicalTime (rankPrefix α q hq) i at hr
  rw [← hr]
  simpa only using hrank

/-- A scalar lower bound carried by one concrete chronological marked chain. -/
def HasChainContribution {T : ℕ} (α : Fin T → ℝ) (hα : ∀ t, 0 ≤ α t)
    (bound : ℝ) : Prop :=
  ∃ (c : Finset (Fin T)) (hc : ∀ t ∈ c, 0 < stepSurplus α t),
    bound ≤ (scheduleChainData α hα c hc).contribution

theorem HasChainContribution.mono {T : ℕ} {α : Fin T → ℝ}
    {hα : ∀ t, 0 ≤ α t} {a b : ℝ}
    (hab : a ≤ b) (hb : HasChainContribution α hα b) :
    HasChainContribution α hα a := by
  obtain ⟨c, hc, hbound⟩ := hb
  exact ⟨c, hc, hab.trans hbound⟩

end GD.Sqrt3LowerBound
