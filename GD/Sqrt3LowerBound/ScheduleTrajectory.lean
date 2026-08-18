import GD.Sqrt3LowerBound.MarkedStage

/-!
# A literal GD trajectory for a marked schedule

The prefix statistics below locate each physical time inside its chronological
marked block.  They are then used to prove the GD update at every step and to
package the realized Moreau envelope as a normalized hard instance.
-/

namespace GD.Sqrt3LowerBound

open scoped BigOperators Gradient

noncomputable def prefixMarked {T : ℕ} (c : Finset (Fin T)) (n : ℕ) :
    Finset (Fin T) := c.filter fun t ↦ t.val < n

noncomputable def prefixMarkCount {T : ℕ} (c : Finset (Fin T)) (n : ℕ) : ℕ :=
  (prefixMarked c n).card

noncomputable def prefixGapSet {T : ℕ} (c : Finset (Fin T)) (n : ℕ) :
    Finset (Fin T) :=
  Finset.univ.filter fun t ↦
    t.val < n ∧ t ∉ c ∧ marksBefore c t = prefixMarkCount c n

noncomputable def prefixGap {T : ℕ} (α : Fin T → ℝ)
    (c : Finset (Fin T)) (n : ℕ) : ℝ :=
  ∑ t ∈ prefixGapSet c n, α t

theorem prefixMarkCount_eq_marksBefore {T : ℕ} (c : Finset (Fin T))
    (t : Fin T) : prefixMarkCount c t.val = marksBefore c t := by
  unfold prefixMarkCount prefixMarked marksBefore
  congr 1

theorem prefixMarkCount_succ {T : ℕ} (c : Finset (Fin T))
    (n : ℕ) (hn : n < T) :
    prefixMarkCount c (n + 1) =
      prefixMarkCount c n + if (⟨n, hn⟩ : Fin T) ∈ c then 1 else 0 := by
  let t : Fin T := ⟨n, hn⟩
  have hnot : t ∉ prefixMarked c n := by
    simp [prefixMarked, t]
  by_cases ht : t ∈ c
  · have hset : prefixMarked c (n + 1) = insert t (prefixMarked c n) := by
      ext u
      simp only [prefixMarked, Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨huc, hu⟩
        by_cases hut : u = t
        · exact Or.inl hut
        · right
          exact ⟨huc, by
            have hune : u.val ≠ n := by
              intro hval
              apply hut
              apply Fin.ext
              exact hval
            omega⟩
      · rintro (rfl | ⟨huc, hu⟩)
        · exact ⟨ht, by simp [t]⟩
        · exact ⟨huc, by omega⟩
    unfold prefixMarkCount
    rw [hset, Finset.card_insert_of_notMem hnot]
    change (⟨n, hn⟩ : Fin T) ∈ c at ht
    simp [ht, Nat.add_comm]
  · have hset : prefixMarked c (n + 1) = prefixMarked c n := by
      ext u
      simp only [prefixMarked, Finset.mem_filter]
      constructor
      · rintro ⟨huc, hu⟩
        refine ⟨huc, ?_⟩
        have hune : u.val ≠ n := by
          intro hval
          apply ht
          have : u = t := Fin.ext hval
          simpa [this] using huc
        omega
      · rintro ⟨huc, hu⟩
        exact ⟨huc, by omega⟩
    change (⟨n, hn⟩ : Fin T) ∉ c at ht
    simp [prefixMarkCount, hset, ht]

theorem prefixGap_zero {T : ℕ} (α : Fin T → ℝ) (c : Finset (Fin T)) :
    prefixGap α c 0 = 0 := by
  unfold prefixGap prefixGapSet
  simp

theorem prefixGap_succ_of_not_mem {T : ℕ} (α : Fin T → ℝ)
    (c : Finset (Fin T)) (n : ℕ) (hn : n < T)
    (ht : (⟨n, hn⟩ : Fin T) ∉ c) :
    prefixGap α c (n + 1) = prefixGap α c n + α ⟨n, hn⟩ := by
  let t : Fin T := ⟨n, hn⟩
  have hcount : prefixMarkCount c (n + 1) = prefixMarkCount c n := by
    rw [prefixMarkCount_succ c n hn]
    simp [ht]
  have hmark : marksBefore c t = prefixMarkCount c n := by
    exact (prefixMarkCount_eq_marksBefore c t).symm
  have hnot : t ∉ prefixGapSet c n := by
    simp [prefixGapSet, t]
  have hset : prefixGapSet c (n + 1) = insert t (prefixGapSet c n) := by
    ext u
    simp only [prefixGapSet, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert]
    rw [hcount]
    constructor
    · rintro ⟨hu, huc, hm⟩
      by_cases hut : u = t
      · exact Or.inl hut
      · right
        refine ⟨?_, huc, hm⟩
        have hune : u.val ≠ n := by
          intro hval
          apply hut
          apply Fin.ext
          exact hval
        omega
    · rintro (rfl | ⟨hu, huc, hm⟩)
      · exact ⟨by simp [t], ht, hmark⟩
      · exact ⟨by omega, huc, hm⟩
  unfold prefixGap
  rw [hset, Finset.sum_insert hnot]
  ring

theorem marksBefore_mono {T : ℕ} (c : Finset (Fin T))
    {u t : Fin T} (hut : u ≤ t) : marksBefore c u ≤ marksBefore c t := by
  unfold marksBefore
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, lt_of_lt_of_le hx.2 hut⟩

theorem marksBefore_add_one_le {T : ℕ} (c : Finset (Fin T))
    {t u : Fin T} (htc : t ∈ c) (htu : t < u) :
    marksBefore c t + 1 ≤ marksBefore c u := by
  let s := c.filter fun x ↦ x < t
  have hnot : t ∉ s := by simp [s]
  have hsubset : insert t s ⊆ c.filter fun x ↦ x < u := by
    intro x hx
    simp only [Finset.mem_insert] at hx
    simp only [Finset.mem_filter]
    rcases hx with rfl | hx
    · exact ⟨htc, htu⟩
    · simp only [s, Finset.mem_filter] at hx
      exact ⟨hx.1, lt_trans hx.2 htu⟩
  have hc := Finset.card_le_card hsubset
  rw [Finset.card_insert_of_notMem hnot] at hc
  exact hc

theorem prefixGap_succ_of_mem {T : ℕ} (α : Fin T → ℝ)
    (c : Finset (Fin T)) (n : ℕ) (hn : n < T)
    (ht : (⟨n, hn⟩ : Fin T) ∈ c) :
    prefixGap α c (n + 1) = 0 := by
  let t : Fin T := ⟨n, hn⟩
  have hcount : prefixMarkCount c (n + 1) = prefixMarkCount c n + 1 := by
    rw [prefixMarkCount_succ c n hn]
    simp [ht]
  have hmark : marksBefore c t = prefixMarkCount c n := by
    exact (prefixMarkCount_eq_marksBefore c t).symm
  have hempty : prefixGapSet c (n + 1) = ∅ := by
    ext u
    constructor
    · intro hu
      simp only [prefixGapSet, Finset.mem_filter, Finset.mem_univ, true_and] at hu
      obtain ⟨hun, huc, hm⟩ := hu
      have hut : u ≤ t := by
        apply Fin.le_iff_val_le_val.2
        change u.val ≤ n
        omega
      have hune : u ≠ t := by
        intro h
        apply huc
        simpa [h] using ht
      have hult : u < t := lt_of_le_of_ne hut hune
      have hmono := marksBefore_mono c hult.le
      rw [hmark] at hmono
      rw [hcount] at hm
      omega
    · simp
  unfold prefixGap
  rw [hempty]
  simp

theorem marksBefore_chronologicalTime {T : ℕ} (c : Finset (Fin T))
    (i : Fin c.card) : marksBefore c (chronologicalTime c i) = i.val := by
  let e := c.orderEmbOfFin rfl
  have he : chronologicalTime c = e := by
    funext j
    rfl
  have hset :
      c.filter (fun x ↦ x < chronologicalTime c i) =
        (Finset.Iio i).image e := by
    ext x
    constructor
    · intro hx
      simp only [Finset.mem_filter] at hx
      have hmem : x ∈ Finset.univ.image (chronologicalTime c) := by
        rw [chronologicalTime_image]
        exact hx.1
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hmem
      obtain ⟨r, rfl⟩ := hmem
      simp only [Finset.mem_image]
      refine ⟨r, ?_, by rw [← he]⟩
      rw [Finset.mem_Iio]
      have hlt : e r < e i := by simpa [← he] using hx.2
      exact e.lt_iff_lt.mp hlt
    · intro hx
      simp only [Finset.mem_image] at hx
      obtain ⟨r, hr, rfl⟩ := hx
      rw [Finset.mem_Iio] at hr
      simp only [Finset.mem_filter]
      constructor
      · exact Finset.orderEmbOfFin_mem c rfl r
      · rw [he]
        exact e.strictMono hr
  unfold marksBefore
  rw [hset, Finset.card_image_of_injective]
  · exact Fin.card_Iio i
  · exact e.injective

theorem prefixMarkCount_lt_card_of_mem {T : ℕ} (c : Finset (Fin T))
    (n : ℕ) (hn : n < T) (ht : (⟨n, hn⟩ : Fin T) ∈ c) :
    prefixMarkCount c n < c.card := by
  unfold prefixMarkCount
  apply Finset.card_lt_card
  constructor
  · exact Finset.filter_subset _ _
  · intro hsub
    have htPrefix : (⟨n, hn⟩ : Fin T) ∈ prefixMarked c n := hsub ht
    simp [prefixMarked] at htPrefix

theorem chronologicalTime_at_prefixCount {T : ℕ} (c : Finset (Fin T))
    (n : ℕ) (hn : n < T) (ht : (⟨n, hn⟩ : Fin T) ∈ c) :
    chronologicalTime c
      ⟨prefixMarkCount c n, prefixMarkCount_lt_card_of_mem c n hn ht⟩ =
        ⟨n, hn⟩ := by
  let t : Fin T := ⟨n, hn⟩
  have htImage : t ∈ Finset.univ.image (chronologicalTime c) := by
    rw [chronologicalTime_image]
    exact ht
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at htImage
  obtain ⟨j, hj⟩ := htImage
  have hjrank := marksBefore_chronologicalTime c j
  have hnrank := prefixMarkCount_eq_marksBefore c t
  have hrank : j.val = prefixMarkCount c n := by
    rw [hj] at hjrank
    have hnrank' : prefixMarkCount c n = marksBefore c t := by
      simpa [t] using hnrank
    exact (hnrank'.trans hjrank).symm
  have hfin : j =
      ⟨prefixMarkCount c n, prefixMarkCount_lt_card_of_mem c n hn ht⟩ :=
    Fin.ext hrank
  calc
    chronologicalTime c
        ⟨prefixMarkCount c n, prefixMarkCount_lt_card_of_mem c n hn ht⟩ =
      chronologicalTime c j := congrArg (chronologicalTime c) hfin.symm
    _ = t := hj
    _ = ⟨n, hn⟩ := rfl

theorem prefixGap_eq_chronologicalGap_of_mem {T : ℕ} (α : Fin T → ℝ)
    (c : Finset (Fin T)) (n : ℕ) (hn : n < T)
    (ht : (⟨n, hn⟩ : Fin T) ∈ c) :
    prefixGap α c n = chronologicalGap α c (prefixMarkCount c n) := by
  let t : Fin T := ⟨n, hn⟩
  have hmark : marksBefore c t = prefixMarkCount c n := by
    simpa [t] using (prefixMarkCount_eq_marksBefore c t).symm
  have hset : prefixGapSet c n =
      Finset.univ.filter
        (fun u ↦ u ∉ c ∧ marksBefore c u = prefixMarkCount c n) := by
    ext u
    simp only [prefixGapSet, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hun, huc, hm⟩
      exact ⟨huc, hm⟩
    · rintro ⟨huc, hm⟩
      refine ⟨?_, huc, hm⟩
      rcases lt_trichotomy u t with hut | hut | hut
      · exact hut
      · subst u
        exact (huc ht).elim
      · have hmore := marksBefore_add_one_le c ht hut
        rw [hmark, hm] at hmore
        omega
  unfold prefixGap chronologicalGap
  rw [hset]

theorem prefixMarkCount_at_horizon {T : ℕ} (c : Finset (Fin T)) :
    prefixMarkCount c T = c.card := by
  unfold prefixMarkCount prefixMarked
  congr 1
  ext t
  simp

theorem prefixGap_at_horizon {T : ℕ} (α : Fin T → ℝ)
    (c : Finset (Fin T)) :
    prefixGap α c T = chronologicalGap α c c.card := by
  have hc := prefixMarkCount_at_horizon c
  unfold prefixGap prefixGapSet chronologicalGap
  rw [hc]
  congr 1
  ext t
  simp

theorem prefixGap_nonneg {T : ℕ} {α : Fin T → ℝ}
    (hα : ∀ t, 0 ≤ α t) (c : Finset (Fin T)) (n : ℕ) :
    0 ≤ prefixGap α c n := by
  unfold prefixGap
  exact Finset.sum_nonneg fun t _ ↦ hα t

theorem prefixGap_le_chronologicalGap {T : ℕ} {α : Fin T → ℝ}
    (hα : ∀ t, 0 ≤ α t) (c : Finset (Fin T)) (n : ℕ) :
    prefixGap α c n ≤ chronologicalGap α c (prefixMarkCount c n) := by
  unfold prefixGap chronologicalGap
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro t ht
    simp only [prefixGapSet, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    exact ⟨ht.2.1, ht.2.2⟩
  · intro t _ _
    exact hα t

theorem prefixMarkCount_le_card {T : ℕ} (c : Finset (Fin T)) (n : ℕ) :
    prefixMarkCount c n ≤ c.card := by
  unfold prefixMarkCount
  exact Finset.card_le_card (Finset.filter_subset _ _)

noncomputable def scheduleState {T : ℕ} (α : Fin T → ℝ)
    (hα : ∀ t, 0 ≤ α t) (c : Finset (Fin T))
    (hc : ∀ t ∈ c, 0 < stepSurplus α t) (n : ℕ) :
    ChainData.StageSpace c.card :=
  let d := scheduleChainData α hα c hc
  let k := prefixMarkCount c n
  if hk : k < c.card then
    d.internalPath ⟨k, hk⟩ (prefixGap α c n)
  else
    d.terminalPath (prefixGap α c n)

theorem scheduleState_zero {T : ℕ} (α : Fin T → ℝ)
    (hα : ∀ t, 0 ≤ α t) (c : Finset (Fin T))
    (hc : ∀ t ∈ c, 0 < stepSurplus α t) :
    scheduleState α hα c hc 0 =
      (scheduleChainData α hα c hc).stagePoint 0 := by
  by_cases hcard : 0 < c.card
  · simp [scheduleState, prefixMarkCount, prefixMarked, prefixGap_zero,
      hcard, ChainData.internalPath]
  · have hcard0 : c.card = 0 := by omega
    simp [scheduleState, prefixMarkCount, prefixMarked, prefixGap_zero,
      hcard, ChainData.terminalPath]
    congr 1
    apply Fin.ext
    simp [hcard0]

theorem scheduleState_horizon {T : ℕ} (α : Fin T → ℝ)
    (hα : ∀ t, 0 ≤ α t) (c : Finset (Fin T))
    (hc : ∀ t ∈ c, 0 < stepSurplus α t) :
    scheduleState α hα c hc T =
      (scheduleChainData α hα c hc).terminalPath
        (scheduleChainData α hα c hc).terminalGap := by
  simp [scheduleState, prefixMarkCount_at_horizon, prefixGap_at_horizon,
    scheduleChainData]

theorem scheduleState_step_of_mem {T : ℕ} (α : Fin T → ℝ)
    (hα : ∀ t, 0 ≤ α t) (c : Finset (Fin T))
    (hc : ∀ t ∈ c, 0 < stepSurplus α t)
    (n : ℕ) (hn : n < T) (ht : (⟨n, hn⟩ : Fin T) ∈ c) :
    scheduleState α hα c hc (n + 1) =
      scheduleState α hα c hc n - α ⟨n, hn⟩ •
        finiteProjection (scheduleChainData α hα c hc).markedVertex
          (scheduleState α hα c hc n) := by
  let t : Fin T := ⟨n, hn⟩
  let d := scheduleChainData α hα c hc
  let k := prefixMarkCount c n
  have hklt : k < c.card := prefixMarkCount_lt_card_of_mem c n hn ht
  let i : Fin c.card := ⟨k, hklt⟩
  have htime : chronologicalTime c i = t := by
    exact chronologicalTime_at_prefixCount c n hn ht
  have hgap : prefixGap α c n = chronologicalGap α c k :=
    prefixGap_eq_chronologicalGap_of_mem α c n hn ht
  have htau : prefixGap α c n = d.omega i - 1 := by
    rw [hgap]
    change chronologicalGap α c k = 1 + chronologicalGap α c k - 1
    ring
  have halpha : α t = 1 + d.delta i := by
    have hdelta : d.delta i = stepSurplus α t := by
      change stepSurplus α (chronologicalTime c i) = stepSurplus α t
      rw [htime]
    rw [hdelta, stepSurplus_eq_sub_of_pos (hc t ht)]
    ring
  have hcurrent : scheduleState α hα c hc n =
      d.internalPath i (prefixGap α c n) := by
    simp [scheduleState, d, k, i, hklt]
  have hproj : finiteProjection d.markedVertex
      (d.internalPath i (prefixGap α c n)) = d.stageGradient i.castSucc := by
    apply d.internalProjection
    · exact prefixGap_nonneg hα c n
    · rw [htau]
  have hcount : prefixMarkCount c (n + 1) = k + 1 := by
    rw [prefixMarkCount_succ c n hn]
    simp [ht, k]
  have hgapNext : prefixGap α c (n + 1) = 0 :=
    prefixGap_succ_of_mem α c n hn ht
  have hnext : scheduleState α hα c hc (n + 1) = d.stagePoint i.succ := by
    by_cases hnextlt : k + 1 < c.card
    · let iNext : Fin c.card := ⟨k + 1, hnextlt⟩
      have hcoord : iNext.castSucc = i.succ := by apply Fin.ext; rfl
      rw [show scheduleState α hα c hc (n + 1) =
          d.internalPath iNext 0 by
        simp [scheduleState, d, hcount, hgapNext, hnextlt, iNext]]
      unfold ChainData.internalPath
      simp only [zero_smul, sub_zero]
      rw [hcoord]
    · have hlast : i.succ = Fin.last c.card := by
        apply Fin.ext
        change k + 1 = c.card
        have hle := prefixMarkCount_le_card c (n + 1)
        rw [hcount] at hle
        omega
      rw [show scheduleState α hα c hc (n + 1) =
          d.terminalPath 0 by
        simp [scheduleState, d, hcount, hgapNext, hnextlt]]
      unfold ChainData.terminalPath
      simp only [zero_smul, sub_zero]
      rw [hlast]
  rw [hnext, hcurrent, hproj]
  change d.stagePoint i.succ =
    d.internalPath i (prefixGap α c n) - α t • d.stageGradient i.castSucc
  rw [htau, halpha]
  exact (d.selectedTransition i).symm

theorem scheduleState_step_of_not_mem {T : ℕ} (α : Fin T → ℝ)
    (hα : ∀ t, 0 ≤ α t) (c : Finset (Fin T))
    (hc : ∀ t ∈ c, 0 < stepSurplus α t)
    (n : ℕ) (hn : n < T) (ht : (⟨n, hn⟩ : Fin T) ∉ c) :
    scheduleState α hα c hc (n + 1) =
      scheduleState α hα c hc n - α ⟨n, hn⟩ •
        finiteProjection (scheduleChainData α hα c hc).markedVertex
          (scheduleState α hα c hc n) := by
  let t : Fin T := ⟨n, hn⟩
  let d := scheduleChainData α hα c hc
  let k := prefixMarkCount c n
  have hcount : prefixMarkCount c (n + 1) = k := by
    rw [prefixMarkCount_succ c n hn]
    simp [ht, k]
  have hgapNext : prefixGap α c (n + 1) = prefixGap α c n + α t := by
    simpa [t] using prefixGap_succ_of_not_mem α c n hn ht
  by_cases hklt : k < c.card
  · let i : Fin c.card := ⟨k, hklt⟩
    have hcurrent : scheduleState α hα c hc n =
        d.internalPath i (prefixGap α c n) := by
      simp [scheduleState, d, k, i, hklt]
    have hnext : scheduleState α hα c hc (n + 1) =
        d.internalPath i (prefixGap α c n + α t) := by
      simp [scheduleState, d, k, i, hcount, hgapNext, hklt]
    have htau : prefixGap α c n ≤ d.omega i - 1 := by
      have hle := prefixGap_le_chronologicalGap hα c n
      change prefixGap α c n ≤ 1 + chronologicalGap α c k - 1
      simpa [k] using hle
    have hproj : finiteProjection d.markedVertex
        (d.internalPath i (prefixGap α c n)) = d.stageGradient i.castSucc :=
      d.internalProjection i _ (prefixGap_nonneg hα c n) htau
    rw [hnext, hcurrent, hproj]
    exact (d.internalPath_add_step i (α t) (prefixGap α c n)).symm
  · have hk : k = c.card := by
      have hle := prefixMarkCount_le_card c n
      change k ≤ c.card at hle
      omega
    have hcurrent : scheduleState α hα c hc n =
        d.terminalPath (prefixGap α c n) := by
      simp [scheduleState, d, k, hklt]
    have hnext : scheduleState α hα c hc (n + 1) =
        d.terminalPath (prefixGap α c n + α t) := by
      simp [scheduleState, d, k, hcount, hgapNext, hklt]
    have htau : prefixGap α c n ≤ d.terminalGap := by
      have hle := prefixGap_le_chronologicalGap hα c n
      rw [show prefixMarkCount c n = c.card by exact hk] at hle
      exact hle
    have hproj : finiteProjection d.markedVertex
        (d.terminalPath (prefixGap α c n)) =
          d.stageGradient (Fin.last c.card) :=
      d.terminalProjection _ (prefixGap_nonneg hα c n) htau
    rw [hnext, hcurrent, hproj]
    exact (d.terminalPath_add_step (α t) (prefixGap α c n)).symm

theorem scheduleState_step {T : ℕ} (α : Fin T → ℝ)
    (hα : ∀ t, 0 ≤ α t) (c : Finset (Fin T))
    (hc : ∀ t ∈ c, 0 < stepSurplus α t)
    (n : ℕ) (hn : n < T) :
    scheduleState α hα c hc (n + 1) =
      scheduleState α hα c hc n - α ⟨n, hn⟩ •
        finiteProjection (scheduleChainData α hα c hc).markedVertex
          (scheduleState α hα c hc n) := by
  by_cases ht : (⟨n, hn⟩ : Fin T) ∈ c
  · exact scheduleState_step_of_mem α hα c hc n hn ht
  · exact scheduleState_step_of_not_mem α hα c hc n hn ht

/-- A concrete normalized smooth convex objective and its literal GD path. -/
structure NormalizedGDInstance (T : ℕ) (α : Fin T → ℝ) where
  dim : ℕ
  dim_le : dim ≤ T + 1
  f : EuclideanSpace ℝ (Fin dim) → ℝ
  x : Fin (T + 1) → EuclideanSpace ℝ (Fin dim)
  convex : ConvexOn ℝ Set.univ f
  hasGradient : ∀ y, HasGradientAt f (∇ f y) y
  oneSmooth : LipschitzWith 1 (∇ f)
  zero_minimizer : f 0 = 0 ∧ ∀ y, f 0 ≤ f y
  initial_norm : ‖x 0‖ = 1
  gd_step : ∀ t : Fin T,
    x t.succ = x t.castSucc - α t • ∇ f (x t.castSucc)
  final_gap : ℝ
  final_gap_eq : f (x (Fin.last T)) - f 0 = final_gap

noncomputable def chainNormalizedInstance {T : ℕ} (α : Fin T → ℝ)
    (hα : ∀ t, 0 ≤ α t) (c : Finset (Fin T))
    (hc : ∀ t ∈ c, 0 < stepSurplus α t) : NormalizedGDInstance T α := by
  let d := scheduleChainData α hα c hc
  let path : Fin (T + 1) → ChainData.StageSpace c.card := fun n ↦
    scheduleState α hα c hc n.val
  refine
    { dim := c.card + 1
      dim_le := ?_
      f := d.markedEnvelope
      x := path
      convex := d.markedEnvelope_convex
      hasGradient := fun y ↦
        (d.markedEnvelope_hasGradient y).differentiableAt.hasGradientAt
      oneSmooth := d.markedEnvelope_one_smooth
      zero_minimizer := d.markedEnvelope_minimized_at_zero
      initial_norm := ?_
      gd_step := ?_
      final_gap := d.contribution / 2
      final_gap_eq := ?_ }
  · simpa using Nat.add_le_add_right (Finset.card_le_univ c) 1
  · dsimp [path]
    rw [scheduleState_zero]
    exact d.stagePoint_zero_norm
  · intro t
    dsimp [path]
    rw [scheduleState_step α hα c hc t.val t.isLt]
    have hgrad : ∇ d.markedEnvelope = finiteProjection d.markedVertex :=
      finiteEnvelope_gradient d.markedVertex
    rw [hgrad]
  · dsimp [path]
    rw [scheduleState_horizon]
    exact d.finalEnvelopeGap

end GD.Sqrt3LowerBound
