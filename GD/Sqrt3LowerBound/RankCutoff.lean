import GD.Sqrt3LowerBound.TemporalProduct

/-!
# Ranked surplus cutoffs and Lyapunov dynamics

This file formalizes Sections 5 and 6 of the report.  Surpluses use zero-based
indices: `δ 0` is the report's `δ_[1]`.  Thus `rankMass N cap δ q` is `M_q`,
and `rankGain ... q` / `rankDensity ... q` are defined for positive `q`.
-/

namespace GD.Sqrt3LowerBound

open scoped BigOperators

/-- Residual mass after the largest `q` surpluses have been selected. -/
noncomputable def rankMass (N : ℕ) (cap : ℝ) (δ : ℕ → ℝ) (q : ℕ) : ℝ :=
  cap + (∑ i ∈ Finset.range N, δ i) - ∑ i ∈ Finset.range q, δ i

/-- The normalized cutoff gain `q δ_[q] / M_q` (zero-based `δ (q-1)`). -/
noncomputable def rankGain
    (N : ℕ) (cap : ℝ) (δ : ℕ → ℝ) (q : ℕ) : ℝ :=
  (q : ℝ) * δ (q - 1) / rankMass N cap δ q

/-- The reciprocal-surplus density at cutoff `q`. -/
noncomputable def rankDensity
    (N : ℕ) (cap : ℝ) (δ : ℕ → ℝ) (q : ℕ) : ℝ :=
  rankMass N cap δ q / (q : ℝ) ^ 2 *
    ∑ i ∈ Finset.range q, (δ i)⁻¹

theorem rankMass_at_top (N : ℕ) (cap : ℝ) (δ : ℕ → ℝ) :
    rankMass N cap δ N = cap := by
  unfold rankMass
  ring

theorem rankMass_step
    (N : ℕ) (cap : ℝ) (δ : ℕ → ℝ) (q : ℕ) (hq : 1 ≤ q) :
    rankMass N cap δ (q - 1) = rankMass N cap δ q + δ (q - 1) := by
  have hqeq : q - 1 + 1 = q := Nat.sub_add_cancel hq
  conv_rhs =>
    lhs
    rw [← hqeq]
  unfold rankMass
  rw [Finset.sum_range_succ]
  ring

/-- First identity in Lemma 5.1 (`Neighboring cutoffs`). -/
theorem rankMass_ratio
    (N : ℕ) (cap : ℝ) (δ : ℕ → ℝ) (q : ℕ)
    (hq : 1 ≤ q) (hM : 0 < rankMass N cap δ q) :
    rankMass N cap δ (q - 1) / rankMass N cap δ q =
      1 + rankGain N cap δ q / q := by
  rw [rankMass_step N cap δ q hq]
  unfold rankGain
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  field_simp [hM.ne', hq0]

/-- The product `density * gain ≤ 1` follows directly from sorted positive
surpluses. -/
theorem density_mul_gain_le_one
    (N : ℕ) (cap : ℝ) (δ : ℕ → ℝ) (q : ℕ)
    (hq : 1 ≤ q)
    (hδpos : ∀ i < q, 0 < δ i)
    (hδsorted : ∀ i < q, δ (q - 1) ≤ δ i)
    (hM : 0 < rankMass N cap δ q) :
    rankDensity N cap δ q * rankGain N cap δ q ≤ 1 := by
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast hq
  have hsum :
      (∑ i ∈ Finset.range q, (δ i)⁻¹) * δ (q - 1) ≤ q := by
    calc
      (∑ i ∈ Finset.range q, (δ i)⁻¹) * δ (q - 1) =
          ∑ i ∈ Finset.range q, ((δ i)⁻¹ * δ (q - 1)) := by
            rw [Finset.sum_mul]
      _ ≤ ∑ _i ∈ Finset.range q, (1 : ℝ) := by
        gcongr with i hi
        have hiq : i < q := Finset.mem_range.mp hi
        exact (inv_mul_le_one₀ (hδpos i hiq)).2 (hδsorted i hiq)
      _ = q := by simp
  have hrewrite :
      rankDensity N cap δ q * rankGain N cap δ q =
        ((∑ i ∈ Finset.range q, (δ i)⁻¹) * δ (q - 1)) / q := by
    unfold rankDensity rankGain
    field_simp [hM.ne', ne_of_gt hq0]
  rw [hrewrite]
  calc
    ((∑ i ∈ Finset.range q, (δ i)⁻¹) * δ (q - 1)) / q ≤ q / q := by
      exact div_le_div_of_nonneg_right hsum hq0.le
    _ = 1 := div_self (ne_of_gt hq0)

/-- Gain transition in Lemma 5.1. -/
theorem rankGain_transition
    (N : ℕ) (cap : ℝ) (δ : ℕ → ℝ) (q : ℕ)
    (hq : 1 ≤ q) (_hqN : q < N)
    (hM : 0 < rankMass N cap δ q)
    (hMnext : 0 < rankMass N cap δ (q + 1))
    (hsorted : δ q ≤ δ (q - 1)) :
    rankGain N cap δ q / q *
        (1 + rankGain N cap δ (q + 1) / (q + 1)) ≥
      rankGain N cap δ (q + 1) / (q + 1) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hq10 : ((q + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hstep := rankMass_step N cap δ (q + 1) (by omega)
  simp only [Nat.add_sub_cancel] at hstep
  have hg : rankGain N cap δ q / q =
      δ (q - 1) / rankMass N cap δ q := by
    unfold rankGain
    field_simp [hq0]
  have hgnext : rankGain N cap δ (q + 1) / (q + 1) =
      δ q / rankMass N cap δ (q + 1) := by
    unfold rankGain
    simp only [Nat.add_sub_cancel]
    field_simp [hq10]
    norm_num [Nat.cast_add, Nat.cast_one]
    ring
  rw [hg, hgnext]
  have hfactor :
      1 + δ q / rankMass N cap δ (q + 1) =
        rankMass N cap δ q / rankMass N cap δ (q + 1) := by
    rw [hstep]
    field_simp [hMnext.ne']
  rw [hfactor]
  have hcancel :
      δ (q - 1) / rankMass N cap δ q *
          (rankMass N cap δ q / rankMass N cap δ (q + 1)) =
        δ (q - 1) / rankMass N cap δ (q + 1) := by
    field_simp [hM.ne', hMnext.ne']
  rw [hcancel]
  exact div_le_div_of_nonneg_right hsorted hMnext.le

/-- Rearranged gain upper bound from Lemma 5.1. -/
theorem rankGain_next_le
    (N : ℕ) (cap : ℝ) (δ : ℕ → ℝ) (q : ℕ)
    (hq : 1 ≤ q) (hqN : q < N)
    (hM : 0 < rankMass N cap δ q)
    (hMnext : 0 < rankMass N cap δ (q + 1))
    (hsorted : δ q ≤ δ (q - 1))
    (hsmall : rankGain N cap δ q < q) :
    rankGain N cap δ (q + 1) ≤
      (q + 1) * rankGain N cap δ q /
        (q - rankGain N cap δ q) := by
  have htrans := rankGain_transition N cap δ q hq hqN hM hMnext hsorted
  have hden : 0 < (q : ℝ) - rankGain N cap δ q := by
    exact sub_pos.mpr hsmall
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast hq
  have hq1 : 0 < ((q + 1 : ℕ) : ℝ) := by positivity
  apply (le_div_iff₀ hden).2
  field_simp [ne_of_gt hq0, ne_of_gt hq1] at htrans
  nlinarith

/-- Exact density recurrence in Lemma 5.1. -/
theorem rankDensity_recurrence
    (N : ℕ) (cap : ℝ) (δ : ℕ → ℝ) (q : ℕ)
    (hq : 1 ≤ q) (_hqN : q < N)
    (hδ : 0 < δ q)
    (_hM : 0 < rankMass N cap δ q)
    (hMnext : 0 < rankMass N cap δ (q + 1)) :
    rankDensity N cap δ (q + 1) =
      q ^ 2 * rankDensity N cap δ q /
          ((q + 1) * (q + 1 + rankGain N cap δ (q + 1))) +
        1 / ((q + 1) * rankGain N cap δ (q + 1)) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hq10 : ((q + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hstep := rankMass_step N cap δ (q + 1) (by omega)
  simp only [Nat.add_sub_cancel] at hstep
  unfold rankDensity rankGain
  rw [Finset.sum_range_succ]
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  field_simp [hδ.ne', hMnext.ne', hq0, hq10]
  rw [hstep]
  ring

/-! ## Endpoint Lyapunov drift -/

/-- The lower-bound exponent. -/
noncomputable def criticalExponent : ℝ := Real.sqrt 3

/-- The density threshold. -/
noncomputable def densityThreshold : ℝ := 1 / 2

/-- The drift remainder constant, simplified at the endpoint parameters. -/
noncomputable def driftConstant : ℝ := 18 / (1 + criticalExponent)

/-- Lyapunov weight from equation (5.8). -/
noncomputable def lyapunovWeight (z : ℝ) : ℝ :=
  z / (densityThreshold * (z + criticalExponent + 1))

/-- The one-cutoff Lyapunov potential. -/
noncomputable def lyapunovPotential (gain density : ℝ) : ℝ :=
  lyapunovWeight gain * (density - densityThreshold)

theorem criticalExponent_sq : criticalExponent ^ 2 = 3 := by
  unfold criticalExponent
  exact Real.sq_sqrt (by norm_num)

theorem criticalExponent_gt_one : 1 < criticalExponent := by
  have hs0 : 0 ≤ criticalExponent := Real.sqrt_nonneg _
  nlinarith [criticalExponent_sq]

theorem critical_identity :
    (criticalExponent - 1) * (criticalExponent + 1) = 2 := by
  nlinarith [criticalExponent_sq]

theorem driftConstant_pos : 0 < driftConstant := by
  unfold driftConstant
  positivity [criticalExponent_gt_one]

private theorem lyapunovWeight_nonneg {z : ℝ} (hz : 0 ≤ z) :
    0 ≤ lyapunovWeight z := by
  unfold lyapunovWeight densityThreshold
  positivity [criticalExponent_gt_one]

private theorem lyapunovWeight_mono {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    lyapunovWeight a ≤ lyapunovWeight b := by
  have hc : 0 < criticalExponent + 1 := by
    linarith [criticalExponent_gt_one]
  have hda : 0 < densityThreshold * (a + criticalExponent + 1) := by
    unfold densityThreshold
    have : 0 < a + criticalExponent + 1 := by
      linarith [criticalExponent_gt_one]
    positivity
  have hdb : 0 < densityThreshold * (b + criticalExponent + 1) := by
    unfold densityThreshold
    have hb0 : 0 ≤ b := ha.trans hab
    have : 0 < b + criticalExponent + 1 := by
      linarith [criticalExponent_gt_one]
    positivity
  unfold lyapunovWeight
  apply (div_le_div_iff₀ hda hdb).2
  unfold densityThreshold
  nlinarith [mul_nonneg (sub_nonneg.mpr hab) hc.le]

private theorem lyapunovWeight_ratio {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    (a / b) * lyapunovWeight b ≤ lyapunovWeight a := by
  have hb : 0 < b := ha.trans_le hab
  have hc : 0 < criticalExponent + 1 := by
    linarith [criticalExponent_gt_one]
  have hda : 0 < a + criticalExponent + 1 := by
    linarith [criticalExponent_gt_one]
  have hdb : 0 < b + criticalExponent + 1 := by
    linarith [criticalExponent_gt_one]
  have hformA :
      lyapunovWeight a = 2 * a / (a + criticalExponent + 1) := by
    unfold lyapunovWeight densityThreshold
    field_simp [hda.ne']
  have hformB :
      lyapunovWeight b = 2 * b / (b + criticalExponent + 1) := by
    unfold lyapunovWeight densityThreshold
    field_simp [hdb.ne']
  rw [hformA, hformB]
  have hcancel :
      (a / b) * (2 * b / (b + criticalExponent + 1)) =
        2 * a / (b + criticalExponent + 1) := by
    field_simp [hb.ne']
  rw [hcancel]
  have hden : a + criticalExponent + 1 ≤ b + criticalExponent + 1 := by linarith
  have hinv := one_div_le_one_div_of_le hda hden
  calc
    2 * a / (b + criticalExponent + 1) =
        (2 * a) * (1 / (b + criticalExponent + 1)) := by ring
    _ ≤ (2 * a) * (1 / (a + criticalExponent + 1)) := by
      exact mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = 2 * a / (a + criticalExponent + 1) := by ring

private theorem weight_times_transition_le
    {n gainPrev gain : ℝ}
    (hn : n - 1 > 2)
    (_hgainPrev : 0 < gainPrev) (hgainPrev_le : gainPrev ≤ 2)
    (hgain : 0 < gain)
    (htransition : gain ≤ n * gainPrev / (n - 1 - gainPrev)) :
    lyapunovWeight gain * ((n - 1) ^ 2 / (n * (n + gain))) ≤
      lyapunovWeight gainPrev := by
  have hn0 : 0 < n := by linarith
  have hden : 0 < n - 1 - gainPrev := by linarith
  have hng : 0 < n + gain := by positivity
  have hlow0 : 0 < (n - 1) * gain / (n + gain) := by positivity
  have hcross := (le_div_iff₀ hden).mp htransition
  have hlow : (n - 1) * gain / (n + gain) ≤ gainPrev := by
    apply (div_le_iff₀ hng).2
    nlinarith
  have hmono := lyapunovWeight_mono hlow0.le hlow
  have hratio := lyapunovWeight_ratio hlow0 (show
      (n - 1) * gain / (n + gain) ≤ gain by
        apply (div_le_iff₀ hng).2
        nlinarith [mul_pos hgain hgain])
  have hratio_eq :
      (((n - 1) * gain / (n + gain)) / gain) * lyapunovWeight gain =
        ((n - 1) / (n + gain)) * lyapunovWeight gain := by
    field_simp [hgain.ne', hng.ne']
  rw [hratio_eq] at hratio
  have ht :
      lyapunovWeight gain * ((n - 1) ^ 2 / (n * (n + gain))) ≤
        ((n - 1) / (n + gain)) * lyapunovWeight gain := by
    have hw0 := lyapunovWeight_nonneg hgain.le
    calc
      lyapunovWeight gain * ((n - 1) ^ 2 / (n * (n + gain))) =
          (((n - 1) / n) * ((n - 1) / (n + gain))) *
            lyapunovWeight gain := by field_simp [hn0.ne', hng.ne']
      _ ≤ (1 * ((n - 1) / (n + gain))) * lyapunovWeight gain := by
        gcongr
        exact (div_le_one hn0).2 (by linarith)
      _ = ((n - 1) / (n + gain)) * lyapunovWeight gain := by ring
  exact ht.trans (hratio.trans hmono)

/-- Lemma 5.2 (`One-step Lyapunov drift`) at the endpoint
`β = √3`, `densityThreshold = 1/2`. -/
theorem oneStepLyapunovDrift
    {n gainPrev gain densityPrev density : ℝ}
    (hn : n - 1 > 2)
    (hdensityPrev : densityThreshold ≤ densityPrev)
    (hgainPrev : 0 < gainPrev) (hgainPrev_le : gainPrev ≤ 2)
    (hgain : 0 < gain) (hgain_le : gain ≤ 2)
    (htransition : gain ≤ n * gainPrev / (n - 1 - gainPrev))
    (hrecurrence : density =
      (n - 1) ^ 2 * densityPrev / (n * (n + gain)) + 1 / (n * gain)) :
    lyapunovPotential gain density - lyapunovPotential gainPrev densityPrev ≤
      (criticalExponent - 1 - gain) / n + driftConstant / n ^ 2 := by
  have hn0 : 0 < n := by linarith
  have hng : 0 < n + gain := by positivity
  have hwtransition := weight_times_transition_le
    hn hgainPrev hgainPrev_le hgain htransition
  let transitionScale : ℝ := (n - 1) ^ 2 / (n * (n + gain))
  let epsilon : ℝ :=
    1 / (n * gain) -
      densityThreshold * (n * (gain + 2) - 1) / (n * (n + gain))
  have hcenter : density - densityThreshold =
      transitionScale * (densityPrev - densityThreshold) + epsilon := by
    rw [hrecurrence]
    dsimp [transitionScale, epsilon, densityThreshold]
    field_simp [hn0.ne', hgain.ne', hng.ne']
    ring
  have hcenter0 : 0 ≤ densityPrev - densityThreshold := sub_nonneg.mpr hdensityPrev
  have hpotential :
      lyapunovPotential gain density -
          lyapunovPotential gainPrev densityPrev ≤
        lyapunovWeight gain * epsilon := by
    have hscaled :
        (lyapunovWeight gain * transitionScale) *
            (densityPrev - densityThreshold) ≤
          lyapunovWeight gainPrev *
            (densityPrev - densityThreshold) := by
      exact mul_le_mul_of_nonneg_right hwtransition hcenter0
    unfold lyapunovPotential
    rw [hcenter]
    nlinarith
  have hdenBeta : 0 < gain + criticalExponent + 1 := by
    linarith [criticalExponent_gt_one]
  have hexact :
      lyapunovWeight gain * epsilon =
        1 / n *
          (criticalExponent - 1 - gain +
            gain * (1 + gain * (gain + 2)) /
              ((n + gain) * (gain + criticalExponent + 1))) := by
    dsimp [epsilon, lyapunovWeight, densityThreshold]
    field_simp [hn0.ne', hgain.ne', hng.ne', hdenBeta.ne']
    nth_rewrite 1 [← critical_identity]
    ring
  let remainder : ℝ :=
    gain * (1 + gain * (gain + 2)) /
      ((n + gain) * (gain + criticalExponent + 1))
  have hgg : gain * (gain + 2) ≤ 8 := by
    calc
      gain * (gain + 2) ≤ 2 * 4 := by
        exact mul_le_mul hgain_le (by linarith) (by linarith) (by norm_num)
      _ = 8 := by norm_num
  have hpoly : gain * (1 + gain * (gain + 2)) ≤ 18 := by
    calc
      gain * (1 + gain * (gain + 2)) ≤ 2 * 9 := by
        exact mul_le_mul hgain_le (by linarith) (by positivity) (by norm_num)
      _ = 18 := by norm_num
  have hbase : 0 < n * (criticalExponent + 1) := by
    positivity [criticalExponent_gt_one]
  have hden : 0 < (n + gain) * (gain + criticalExponent + 1) := by
    positivity
  have hdenLower :
      n * (criticalExponent + 1) ≤
        (n + gain) * (gain + criticalExponent + 1) := by
    exact mul_le_mul (by linarith) (by linarith)
      (by linarith [criticalExponent_gt_one]) hng.le
  have hcross :
      gain * (1 + gain * (gain + 2)) *
          (n * (criticalExponent + 1)) ≤
        18 * ((n + gain) * (gain + criticalExponent + 1)) := by
    calc
      gain * (1 + gain * (gain + 2)) *
          (n * (criticalExponent + 1)) ≤
          18 * (n * (criticalExponent + 1)) := by gcongr
      _ ≤ 18 * ((n + gain) * (gain + criticalExponent + 1)) := by gcongr
  have hremainder : remainder ≤ driftConstant / n := by
    have hfrac :
        gain * (1 + gain * (gain + 2)) /
            ((n + gain) * (gain + criticalExponent + 1)) ≤
          18 / (n * (criticalExponent + 1)) :=
      (div_le_div_iff₀ hden hbase).2 hcross
    dsimp [remainder]
    calc
      gain * (1 + gain * (gain + 2)) /
          ((n + gain) * (gain + criticalExponent + 1)) ≤
          18 / (n * (criticalExponent + 1)) := hfrac
      _ = driftConstant / n := by
        unfold driftConstant
        have hbeta1 : criticalExponent + 1 ≠ 0 := by
          linarith [criticalExponent_gt_one]
        have hbeta1' : 1 + criticalExponent ≠ 0 := by
          linarith [criticalExponent_gt_one]
        field_simp [hn0.ne', hbeta1, hbeta1']
        ring
  rw [hexact] at hpotential
  dsimp [remainder] at hremainder
  calc
    lyapunovPotential gain density - lyapunovPotential gainPrev densityPrev ≤
        1 / n * (criticalExponent - 1 - gain + remainder) := by
          simpa [remainder] using hpotential
    _ ≤ 1 / n *
        (criticalExponent - 1 - gain + driftConstant / n) := by
          gcongr
    _ = (criticalExponent - 1 - gain) / n +
        driftConstant / n ^ 2 := by field_simp [hn0.ne']

/-! ## Finite tail estimates -/

private theorem sum_range_forward_difference
    (V : ℕ → ℝ) (k m : ℕ) :
    (∑ i ∈ Finset.range m, (V (k + i + 1) - V (k + i))) =
      V (k + m) - V k := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [Nat.add_assoc]
      ring

private theorem sum_range_backward_difference
    (V : ℕ → ℝ) (k m : ℕ) :
    (∑ i ∈ Finset.range m, (V (k + i) - V (k + i + 1))) =
      V k - V (k + m) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [Nat.add_assoc]
      ring

private theorem inv_nat_succ_le_log_ratio (a : ℕ) (ha : 1 ≤ a) :
    1 / ((a + 1 : ℕ) : ℝ) ≤
      Real.log (((a + 1 : ℕ) : ℝ) / (a : ℝ)) := by
  have ha0 : 0 < (a : ℝ) := by exact_mod_cast ha
  have hratio : 0 < ((a + 1 : ℕ) : ℝ) / (a : ℝ) := by positivity
  have h := Real.one_sub_inv_le_log_of_pos hratio
  convert h using 1
  field_simp [ha0.ne']
  norm_num [Nat.cast_add, Nat.cast_one]

private theorem harmonic_tail_le_log_ratio (k m : ℕ) (hk : 1 ≤ k) :
    (∑ i ∈ Finset.range m, 1 / ((k + i + 1 : ℕ) : ℝ)) ≤
      Real.log ((k + m : ℝ) / (k : ℝ)) := by
  induction m with
  | zero =>
      have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
      simp [hk0]
  | succ m ih =>
      rw [Finset.sum_range_succ]
      have hstep := inv_nat_succ_le_log_ratio (k + m) (by omega)
      have hbound :
          (∑ i ∈ Finset.range m, 1 / ((k + i + 1 : ℕ) : ℝ)) +
              1 / ((k + m + 1 : ℕ) : ℝ) ≤
            Real.log ((k + (m + 1) : ℝ) / (k : ℝ)) := by
        calc
        (∑ i ∈ Finset.range m, 1 / ((k + i + 1 : ℕ) : ℝ)) +
            1 / ((k + m + 1 : ℕ) : ℝ) ≤
          Real.log ((k + m : ℝ) / (k : ℝ)) +
            Real.log (((k + m + 1 : ℕ) : ℝ) / ((k + m : ℕ) : ℝ)) :=
              add_le_add ih hstep
        _ = Real.log ((k + (m + 1) : ℝ) / (k : ℝ)) := by
          have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
          have hkm0 : ((k + m : ℕ) : ℝ) ≠ 0 := by positivity
          have hkm10 : ((k + m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
          rw [Real.log_div (by positivity) hk0,
            Real.log_div hkm10 hkm0,
            Real.log_div (by positivity) hk0]
          push_cast
          ring_nf
      simpa only [Nat.cast_succ, Nat.cast_add, Nat.cast_one] using hbound

private theorem reciprocal_square_tail_le_one (k m : ℕ) (hk : 1 ≤ k) :
    (∑ i ∈ Finset.range m, 1 / (((k + i + 1 : ℕ) : ℝ) ^ 2)) ≤ 1 := by
  have hterm : ∀ i,
      1 / (((k + i + 1 : ℕ) : ℝ) ^ 2) ≤
        1 / ((k + i : ℝ) * ((k + i + 1 : ℕ) : ℝ)) := by
    intro i
    have ha : 0 < (k + i : ℝ) := by positivity
    have hb : 0 < ((k + i + 1 : ℕ) : ℝ) := by positivity
    apply one_div_le_one_div_of_le (mul_pos ha hb)
    norm_num [Nat.cast_add, Nat.cast_one] at ha hb ⊢
    nlinarith
  calc
    (∑ i ∈ Finset.range m, 1 / (((k + i + 1 : ℕ) : ℝ) ^ 2)) ≤
        ∑ i ∈ Finset.range m,
          1 / ((k + i : ℝ) * ((k + i + 1 : ℕ) : ℝ)) := by
            exact Finset.sum_le_sum fun i hi ↦ hterm i
    _ = ∑ i ∈ Finset.range m,
          (1 / (k + i : ℝ) - 1 / ((k + i + 1 : ℕ) : ℝ)) := by
            apply Finset.sum_congr rfl
            intro i hi
            have ha : (k + i : ℝ) ≠ 0 := by positivity
            have hb : ((k + i + 1 : ℕ) : ℝ) ≠ 0 := by positivity
            field_simp [ha, hb]
            norm_num [Nat.cast_add, Nat.cast_one]
    _ = 1 / (k : ℝ) - 1 / (k + m : ℝ) := by
      simpa using sum_range_backward_difference (fun q ↦ 1 / (q : ℝ)) k m
    _ ≤ 1 / (k : ℝ) := by
      have : 0 ≤ 1 / (k + m : ℝ) := by positivity
      linarith
    _ ≤ 1 := by
      have hk0 : 0 < (k : ℝ) := by exact_mod_cast hk
      exact (div_le_one hk0).2 (by exact_mod_cast hk)

private theorem pi_sq_div_six_ge_one : (1 : ℝ) ≤ Real.pi ^ 2 / 6 := by
  have hp := Real.pi_gt_three
  nlinarith [sq_nonneg (Real.pi - 3)]

/-- Uniform potential estimate (equation (5.13)). -/
theorem lyapunovPotential_bounds
    {gain density : ℝ}
    (hgain : 0 < gain)
    (hdensity : densityThreshold ≤ density)
    (hproduct : density * gain ≤ 1) :
    0 ≤ lyapunovPotential gain density ∧
      lyapunovPotential gain density ≤
        1 / (densityThreshold * (criticalExponent + 1)) := by
  have hw0 := lyapunovWeight_nonneg hgain.le
  have hcenter0 : 0 ≤ density - densityThreshold := sub_nonneg.mpr hdensity
  refine ⟨mul_nonneg hw0 hcenter0, ?_⟩
  have hden0 : 0 < densityThreshold * (gain + criticalExponent + 1) := by
    unfold densityThreshold
    positivity [criticalExponent_gt_one]
  have hbase0 : 0 < densityThreshold * (criticalExponent + 1) := by
    unfold densityThreshold
    positivity [criticalExponent_gt_one]
  have hfirst :
      lyapunovPotential gain density ≤
        gain * density /
          (densityThreshold * (gain + criticalExponent + 1)) := by
    calc
      lyapunovPotential gain density =
          gain * (density - densityThreshold) /
            (densityThreshold * (gain + criticalExponent + 1)) := by
              unfold lyapunovPotential lyapunovWeight
              ring
      _ ≤ gain * density /
          (densityThreshold * (gain + criticalExponent + 1)) := by
        apply div_le_div_of_nonneg_right _ hden0.le
        have hthreshold0 : 0 ≤ densityThreshold := by
          unfold densityThreshold
          norm_num
        exact mul_le_mul_of_nonneg_left
          (sub_le_self density hthreshold0) hgain.le
  have hsecond :
      gain * density /
          (densityThreshold * (gain + criticalExponent + 1)) ≤
        1 / (densityThreshold * (gain + criticalExponent + 1)) := by
    exact div_le_div_of_nonneg_right (by nlinarith [hproduct]) hden0.le
  have hthird :
      1 / (densityThreshold * (gain + criticalExponent + 1)) ≤
        1 / (densityThreshold * (criticalExponent + 1)) := by
    apply one_div_le_one_div_of_le hbase0
    unfold densityThreshold
    nlinarith
  exact hfirst.trans (hsecond.trans hthird)

/-! ## Tail-budget transport -/

/-- The bounded endpoint and accumulated drift budget in (5.16). -/
noncomputable def endpointBudget : ℝ :=
  1 / (densityThreshold * (criticalExponent + 1)) +
    Real.pi ^ 2 / 6 * driftConstant

/-- The universal propagation constant `Γ_prop` from (5.15). -/
noncomputable def propagationConstant : ℝ := 2 * Real.exp endpointBudget

theorem endpointBudget_pos : 0 < endpointBudget := by
  unfold endpointBudget densityThreshold
  have hbeta : 0 < criticalExponent + 1 := by
    linarith [criticalExponent_gt_one]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hdrift := driftConstant_pos
  positivity

theorem propagationConstant_pos : 0 < propagationConstant := by
  unfold propagationConstant
  positivity

private theorem prod_range_successive_ratio
    (mass : ℕ → ℝ) (k m : ℕ)
    (hmass : ∀ q, k ≤ q → q ≤ k + m → mass q ≠ 0) :
    (∏ i ∈ Finset.range m, mass (k + i) / mass (k + i + 1)) =
      mass k / mass (k + m) := by
  induction m with
  | zero =>
      simp [hmass k (by omega) (by omega)]
  | succ m ih =>
      rw [Finset.prod_range_succ]
      have hprefix :
          (∏ i ∈ Finset.range m, mass (k + i) / mass (k + i + 1)) =
            mass k / mass (k + m) := by
        apply ih
        intro q hkq hq
        exact hmass q hkq (by omega)
      rw [hprefix]
      have hmid : mass (k + m) ≠ 0 := hmass _ (by omega) (by omega)
      have hend : mass (k + m + 1) ≠ 0 := hmass _ (by omega) (by omega)
      simp only [Nat.add_assoc]
      field_simp [hmid, hend]

/-- Abstract finite telescope underlying Lemma 5.3.  This theorem isolates
the analytic summation step: neighboring mass ratios, the one-step drift,
and endpoint potential bounds imply the power-weighted mass estimate. -/
theorem coreTailBudgetTransport
    (mass gain potential : ℕ → ℝ) (cap : ℝ) (k N : ℕ)
    (hk : 1 ≤ k) (hkN : k ≤ N)
    (hcap : 0 < cap)
    (hmass : ∀ q, k ≤ q → q ≤ N → 0 < mass q)
    (htop : mass N = cap)
    (hratio : ∀ n, k < n → n ≤ N →
      mass (n - 1) / mass n = 1 + gain n / (n : ℝ))
    (hdrift : ∀ n, k < n → n ≤ N →
      potential n - potential (n - 1) ≤
        (criticalExponent - 1 - gain n) / (n : ℝ) +
          driftConstant / (n : ℝ) ^ 2)
    (hpotentialNonneg : 0 ≤ potential N)
    (hpotentialStart : potential k ≤
      1 / (densityThreshold * (criticalExponent + 1))) :
    mass k * (k : ℝ) ^ (criticalExponent - 1) ≤
      Real.exp endpointBudget * cap *
        (N : ℝ) ^ (criticalExponent - 1) := by
  let m := N - k
  have hkm : k + m = N := by
    dsimp [m]
    omega
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast hk
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast hk.trans hkN
  have hsumDrift :
      (∑ i ∈ Finset.range m,
          gain (k + i + 1) / ((k + i + 1 : ℕ) : ℝ)) ≤
        (criticalExponent - 1) *
            (∑ i ∈ Finset.range m,
              1 / ((k + i + 1 : ℕ) : ℝ)) +
          driftConstant *
            (∑ i ∈ Finset.range m,
              1 / (((k + i + 1 : ℕ) : ℝ) ^ 2)) +
          potential k - potential N := by
    calc
      (∑ i ∈ Finset.range m,
          gain (k + i + 1) / ((k + i + 1 : ℕ) : ℝ)) ≤
        ∑ i ∈ Finset.range m,
          ((criticalExponent - 1) /
              ((k + i + 1 : ℕ) : ℝ) +
            driftConstant / (((k + i + 1 : ℕ) : ℝ) ^ 2) +
            (potential (k + i) - potential (k + i + 1))) := by
          apply Finset.sum_le_sum
          intro i hi
          have hi' : i < m := Finset.mem_range.mp hi
          have hnLower : k < k + i + 1 := by omega
          have hnUpper : k + i + 1 ≤ N := by omega
          have hd := hdrift (k + i + 1) hnLower hnUpper
          have hn0 : (0 : ℝ) < ((k + i + 1 : ℕ) : ℝ) := by positivity
          simp only [Nat.add_sub_cancel] at hd
          field_simp [hn0.ne'] at hd ⊢
          nlinarith
      _ = (criticalExponent - 1) *
            (∑ i ∈ Finset.range m,
              1 / ((k + i + 1 : ℕ) : ℝ)) +
          driftConstant *
            (∑ i ∈ Finset.range m,
              1 / (((k + i + 1 : ℕ) : ℝ) ^ 2)) +
          potential k - potential N := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
            have hfirst :
                (∑ i ∈ Finset.range m,
                    (criticalExponent - 1) /
                      ((k + i + 1 : ℕ) : ℝ)) =
                  (criticalExponent - 1) *
                    (∑ i ∈ Finset.range m,
                      1 / ((k + i + 1 : ℕ) : ℝ)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              ring
            have hsecond :
                (∑ i ∈ Finset.range m,
                    driftConstant / (((k + i + 1 : ℕ) : ℝ) ^ 2)) =
                  driftConstant *
                    (∑ i ∈ Finset.range m,
                      1 / (((k + i + 1 : ℕ) : ℝ) ^ 2)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              ring
            rw [hfirst, hsecond, sum_range_backward_difference, hkm]
            ring
  have hsum :
      (∑ i ∈ Finset.range m,
          gain (k + i + 1) / ((k + i + 1 : ℕ) : ℝ)) ≤
        (criticalExponent - 1) * Real.log ((N : ℝ) / (k : ℝ)) +
          endpointBudget := by
    have hharm :
        (∑ i ∈ Finset.range m,
          1 / ((k + i + 1 : ℕ) : ℝ)) ≤
            Real.log ((N : ℝ) / (k : ℝ)) := by
      simpa [← hkm, Nat.cast_add] using harmonic_tail_le_log_ratio k m hk
    have hsquare := reciprocal_square_tail_le_one k m hk
    have hsquarePi :
        (∑ i ∈ Finset.range m,
          1 / (((k + i + 1 : ℕ) : ℝ) ^ 2)) ≤ Real.pi ^ 2 / 6 :=
      hsquare.trans pi_sq_div_six_ge_one
    have hpow : 0 ≤ criticalExponent - 1 :=
      (sub_pos.mpr criticalExponent_gt_one).le
    have hdrift0 := driftConstant_pos.le
    calc
      (∑ i ∈ Finset.range m,
          gain (k + i + 1) / ((k + i + 1 : ℕ) : ℝ)) ≤
          (criticalExponent - 1) *
              (∑ i ∈ Finset.range m,
                1 / ((k + i + 1 : ℕ) : ℝ)) +
            driftConstant *
              (∑ i ∈ Finset.range m,
                1 / (((k + i + 1 : ℕ) : ℝ) ^ 2)) +
            potential k - potential N := hsumDrift
      _ ≤ (criticalExponent - 1) * Real.log ((N : ℝ) / (k : ℝ)) +
          driftConstant * (Real.pi ^ 2 / 6) +
          1 / (densityThreshold * (criticalExponent + 1)) := by
            nlinarith [mul_le_mul_of_nonneg_left hharm hpow,
              mul_le_mul_of_nonneg_left hsquarePi hdrift0]
      _ = (criticalExponent - 1) * Real.log ((N : ℝ) / (k : ℝ)) +
          endpointBudget := by
            unfold endpointBudget
            ring
  have hproductRatio :
      mass k / cap =
        ∏ i ∈ Finset.range m,
          mass (k + i) / mass (k + i + 1) := by
    have htelescope := prod_range_successive_ratio mass k m (by
      intro q hkq hq
      rw [hkm] at hq
      exact (hmass q hkq hq).ne')
    rw [hkm, htop] at htelescope
    exact htelescope.symm
  have hproductExp :
      (∏ i ∈ Finset.range m,
          mass (k + i) / mass (k + i + 1)) ≤
        Real.exp (∑ i ∈ Finset.range m,
          gain (k + i + 1) / ((k + i + 1 : ℕ) : ℝ)) := by
    rw [Real.exp_sum]
    apply Finset.prod_le_prod
    · intro i hi
      have hi' : i < m := Finset.mem_range.mp hi
      exact div_nonneg
        (hmass _ (by omega) (by omega)).le
        (hmass _ (by omega) (by omega)).le
    · intro i hi
      have hi' : i < m := Finset.mem_range.mp hi
      have hratio' := hratio (k + i + 1) (by omega) (by omega)
      simp only [Nat.add_sub_cancel] at hratio'
      rw [hratio']
      simpa [add_comm] using
        (Real.add_one_le_exp
          (gain (k + i + 1) / ((k + i + 1 : ℕ) : ℝ)))
  have hmassExp :
      mass k ≤ cap * Real.exp
        ((criticalExponent - 1) * Real.log ((N : ℝ) / (k : ℝ)) +
          endpointBudget) := by
    have hratioBound :
        mass k / cap ≤ Real.exp
          ((criticalExponent - 1) * Real.log ((N : ℝ) / (k : ℝ)) +
            endpointBudget) := by
      rw [hproductRatio]
      exact hproductExp.trans (Real.exp_le_exp.mpr hsum)
    have h := (div_le_iff₀ hcap).mp hratioBound
    simpa [mul_comm] using h
  have hpowerIdentity :
      Real.exp
          ((criticalExponent - 1) * Real.log ((N : ℝ) / (k : ℝ)) +
            endpointBudget) *
          (k : ℝ) ^ (criticalExponent - 1) =
        Real.exp endpointBudget *
          (N : ℝ) ^ (criticalExponent - 1) := by
    rw [Real.rpow_def_of_pos hk0, Real.rpow_def_of_pos hN0,
      Real.log_div hN0.ne' hk0.ne']
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    mass k * (k : ℝ) ^ (criticalExponent - 1) ≤
        (cap * Real.exp
          ((criticalExponent - 1) * Real.log ((N : ℝ) / (k : ℝ)) +
            endpointBudget)) *
          (k : ℝ) ^ (criticalExponent - 1) := by
            gcongr
    _ = Real.exp endpointBudget * cap *
        (N : ℝ) ^ (criticalExponent - 1) := by
          rw [mul_assoc, hpowerIdentity]
          ring

/-- Positivity of every residual mass up to the top cutoff. -/
theorem rankMass_pos
    (N : ℕ) (cap : ℝ) (δ : ℕ → ℝ) (q : ℕ)
    (hqN : q ≤ N) (hcap : 0 < cap)
    (hδ : ∀ i < N, 0 ≤ δ i) :
    0 < rankMass N cap δ q := by
  have hsum :
      (∑ i ∈ Finset.range q, δ i) ≤
        ∑ i ∈ Finset.range N, δ i := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono hqN) (by
        intro i hiN hiq
        exact hδ i (Finset.mem_range.mp hiN))
  unfold rankMass
  linarith

theorem rankGain_pos
    (N : ℕ) (cap : ℝ) (δ : ℕ → ℝ) (q : ℕ)
    (hq : 1 ≤ q) (hδ : 0 < δ (q - 1))
    (hM : 0 < rankMass N cap δ q) :
    0 < rankGain N cap δ q := by
  unfold rankGain
  positivity

/-- Above half density, the ordered-cutoff gain is strictly below two. -/
theorem rankGain_lt_two_of_dense
    (N : ℕ) (cap : ℝ) (δ : ℕ → ℝ) (q : ℕ)
    (hq : 1 ≤ q)
    (hδpos : ∀ i < q, 0 < δ i)
    (hδsorted : ∀ i < q, δ (q - 1) ≤ δ i)
    (hM : 0 < rankMass N cap δ q)
    (hdense : densityThreshold < rankDensity N cap δ q) :
    rankGain N cap δ q < 2 := by
  have hproduct := density_mul_gain_le_one N cap δ q hq
    hδpos hδsorted hM
  have hgain := rankGain_pos N cap δ q hq (hδpos _ (by omega)) hM
  unfold densityThreshold at hdense
  nlinarith

/-- The concrete ranked-surplus data satisfy the abstract one-step drift
hypothesis whenever both adjacent cutoffs have density above one half. -/
theorem rankedOneStepLyapunovDrift
    (N : ℕ) (cap : ℝ) (δ : ℕ → ℝ) (n : ℕ)
    (hn : 3 < n) (hnN : n ≤ N)
    (hcap : 0 < cap)
    (hδpos : ∀ i < N, 0 < δ i)
    (hδsorted : Antitone δ)
    (hdensityPrev : densityThreshold < rankDensity N cap δ (n - 1))
    (hdensity : densityThreshold < rankDensity N cap δ n) :
    lyapunovPotential
          (rankGain N cap δ n) (rankDensity N cap δ n) -
        lyapunovPotential
          (rankGain N cap δ (n - 1)) (rankDensity N cap δ (n - 1)) ≤
      (criticalExponent - 1 - rankGain N cap δ n) / (n : ℝ) +
        driftConstant / (n : ℝ) ^ 2 := by
  have hn1 : 1 ≤ n - 1 := by omega
  have hn1N : n - 1 < N := by omega
  have hnPred : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  have hMprev : 0 < rankMass N cap δ (n - 1) :=
    rankMass_pos N cap δ (n - 1) (by omega) hcap (by
      intro i hi
      exact (hδpos i hi).le)
  have hM : 0 < rankMass N cap δ n :=
    rankMass_pos N cap δ n hnN hcap (by
      intro i hi
      exact (hδpos i hi).le)
  have hsortedAt : ∀ i < n - 1, δ (n - 1 - 1) ≤ δ i := by
    intro i hi
    exact hδsorted (by omega)
  have hsortedNext : ∀ i < n, δ (n - 1) ≤ δ i := by
    intro i hi
    exact hδsorted (by omega)
  have hgainPrevPos : 0 < rankGain N cap δ (n - 1) :=
    rankGain_pos N cap δ (n - 1) hn1 (hδpos _ (by omega)) hMprev
  have hgainPos : 0 < rankGain N cap δ n :=
    rankGain_pos N cap δ n (by omega) (hδpos _ (by omega)) hM
  have hgainPrevLt : rankGain N cap δ (n - 1) < 2 :=
    rankGain_lt_two_of_dense N cap δ (n - 1) hn1
      (fun i hi ↦ hδpos i (by omega)) hsortedAt hMprev hdensityPrev
  have hgainLt : rankGain N cap δ n < 2 :=
    rankGain_lt_two_of_dense N cap δ n (by omega)
      (fun i hi ↦ hδpos i (by omega)) hsortedNext hM hdensity
  have htransition :
      rankGain N cap δ n ≤
        (n : ℝ) * rankGain N cap δ (n - 1) /
          ((n : ℝ) - 1 - rankGain N cap δ (n - 1)) := by
    have hMnext : 0 < rankMass N cap δ (n - 1 + 1) := by
      simpa only [hnPred] using hM
    have h := rankGain_next_le N cap δ (n - 1) hn1 hn1N
      hMprev hMnext (hδsorted (by omega)) (by
        have hncast : (2 : ℝ) < (n - 1 : ℕ) := by exact_mod_cast (show 2 < n - 1 by omega)
        linarith)
    simpa [hnPred, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_add,
      Nat.cast_one] using h
  have hrecurrence :
      rankDensity N cap δ n =
        ((n : ℝ) - 1) ^ 2 * rankDensity N cap δ (n - 1) /
            ((n : ℝ) * ((n : ℝ) + rankGain N cap δ n)) +
          1 / ((n : ℝ) * rankGain N cap δ n) := by
    have hMnext : 0 < rankMass N cap δ (n - 1 + 1) := by
      simpa only [hnPred] using hM
    have h := rankDensity_recurrence N cap δ (n - 1) hn1 hn1N
      (hδpos _ (by omega)) hMprev hMnext
    simpa [hnPred, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_add,
      Nat.cast_one] using h
  apply oneStepLyapunovDrift
    (n := (n : ℝ))
    (gainPrev := rankGain N cap δ (n - 1))
    (gain := rankGain N cap δ n)
    (densityPrev := rankDensity N cap δ (n - 1))
    (density := rankDensity N cap δ n)
  · have hncast : (3 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    linarith
  · exact hdensityPrev.le
  · exact hgainPrevPos
  · exact hgainPrevLt.le
  · exact hgainPos
  · exact hgainLt.le
  · exact htransition
  · exact hrecurrence

/-- Core form of Lemma 5.3, assuming every cutoff from `k` through `N`
has density above one half. -/
theorem rankedCoreTailBudgetTransport
    (N : ℕ) (cap : ℝ) (δ : ℕ → ℝ) (k : ℕ)
    (hk : 3 ≤ k) (hkN : k ≤ N)
    (hcap : 0 < cap)
    (hδpos : ∀ i < N, 0 < δ i)
    (hδsorted : Antitone δ)
    (hdense : ∀ q, k ≤ q → q ≤ N →
      densityThreshold < rankDensity N cap δ q) :
    rankMass N cap δ k * (k : ℝ) ^ (criticalExponent - 1) ≤
      Real.exp endpointBudget * cap *
        (N : ℝ) ^ (criticalExponent - 1) := by
  let mass : ℕ → ℝ := rankMass N cap δ
  let gain : ℕ → ℝ := rankGain N cap δ
  let density : ℕ → ℝ := rankDensity N cap δ
  let potential : ℕ → ℝ := fun q ↦
    lyapunovPotential (gain q) (density q)
  have hmass : ∀ q, k ≤ q → q ≤ N → 0 < mass q := by
    intro q hkq hqN
    exact rankMass_pos N cap δ q hqN hcap (fun i hi ↦ (hδpos i hi).le)
  have hgainPos : ∀ q, k ≤ q → q ≤ N → 0 < gain q := by
    intro q hkq hqN
    exact rankGain_pos N cap δ q (by omega) (hδpos _ (by omega))
      (hmass q hkq hqN)
  have hproduct : ∀ q, k ≤ q → q ≤ N → density q * gain q ≤ 1 := by
    intro q hkq hqN
    apply density_mul_gain_le_one N cap δ q (by omega)
    · intro i hi
      exact hδpos i (by omega)
    · intro i hi
      exact hδsorted (by omega)
    · exact hmass q hkq hqN
  apply coreTailBudgetTransport mass gain potential cap k N
  · omega
  · exact hkN
  · exact hcap
  · exact hmass
  · exact rankMass_at_top N cap δ
  · intro n hkn hnN
    exact rankMass_ratio N cap δ n (by omega) (hmass n (by omega) hnN)
  · intro n hkn hnN
    exact rankedOneStepLyapunovDrift N cap δ n (by omega) hnN hcap
      hδpos hδsorted (hdense (n - 1) (by omega) (by omega))
      (hdense n (by omega) hnN)
  · exact (lyapunovPotential_bounds
      (hgainPos N hkN le_rfl) (hdense N hkN le_rfl).le
      (hproduct N hkN le_rfl)).1
  · exact (lyapunovPotential_bounds
      (hgainPos k le_rfl hkN) (hdense k le_rfl hkN).le
      (hproduct k le_rfl hkN)).2

/-- Lemma 5.3 (`Tail-budget transport`) with the report's exact boundary
hypothesis and universal factor `Γ_prop`. -/
theorem tailBudgetTransport
    (N : ℕ) (cap : ℝ) (δ : ℕ → ℝ) (k : ℕ)
    (hk : 3 ≤ k) (hkN : k ≤ N)
    (hcap : 0 < cap)
    (hδpos : ∀ i < N, 0 < δ i)
    (hδsorted : Antitone δ)
    (hdense : ∀ q, k < q → q ≤ N →
      densityThreshold < rankDensity N cap δ q) :
    rankMass N cap δ k * (k : ℝ) ^ (criticalExponent - 1) ≤
      propagationConstant * cap *
        (N : ℝ) ^ (criticalExponent - 1) := by
  by_cases hkTop : k = N
  · subst N
    have hGamma : 1 ≤ propagationConstant := by
      unfold propagationConstant
      have hexp : 1 < Real.exp endpointBudget :=
        Real.one_lt_exp_iff.mpr endpointBudget_pos
      nlinarith
    have hbase :
        0 ≤ cap * (k : ℝ) ^ (criticalExponent - 1) := by
      exact mul_nonneg hcap.le
        (Real.rpow_nonneg (by positivity : 0 ≤ (k : ℝ)) _)
    rw [rankMass_at_top]
    calc
      cap * (k : ℝ) ^ (criticalExponent - 1) =
          1 * (cap * (k : ℝ) ^ (criticalExponent - 1)) := by ring
      _ ≤ propagationConstant *
          (cap * (k : ℝ) ^ (criticalExponent - 1)) := by
            exact mul_le_mul_of_nonneg_right hGamma hbase
      _ = propagationConstant * cap *
          (k : ℝ) ^ (criticalExponent - 1) := by ring
  · have hkNextN : k + 1 ≤ N := by omega
    have hcore := rankedCoreTailBudgetTransport N cap δ (k + 1)
      (by omega) hkNextN hcap hδpos hδsorted (by
        intro q hkq hqN
        exact hdense q (by omega) hqN)
    have hMnext : 0 < rankMass N cap δ (k + 1) :=
      rankMass_pos N cap δ (k + 1) hkNextN hcap
        (fun i hi ↦ (hδpos i hi).le)
    have hM : 0 < rankMass N cap δ k :=
      rankMass_pos N cap δ k hkN hcap
        (fun i hi ↦ (hδpos i hi).le)
    have hgainLt : rankGain N cap δ (k + 1) < 2 := by
      apply rankGain_lt_two_of_dense N cap δ (k + 1) (by omega)
      · intro i hi
        exact hδpos i (by omega)
      · intro i hi
        exact hδsorted (by omega)
      · exact hMnext
      · exact hdense (k + 1) (by omega) hkNextN
    have hmassRatio :
        rankMass N cap δ k / rankMass N cap δ (k + 1) < 2 := by
      have hratio := rankMass_ratio N cap δ (k + 1) (by omega) hMnext
      simp only [Nat.add_sub_cancel] at hratio
      rw [hratio]
      have hkReal : (2 : ℝ) < (k + 1 : ℕ) := by
        exact_mod_cast (show 2 < k + 1 by omega)
      have hden : (0 : ℝ) < (k + 1 : ℕ) := by positivity
      have hquot : rankGain N cap δ (k + 1) / (k + 1 : ℕ) < 1 :=
        (div_lt_one hden).2 (hgainLt.trans hkReal)
      linarith
    have hmassBoundary :
        rankMass N cap δ k ≤ 2 * rankMass N cap δ (k + 1) := by
      exact (div_lt_iff₀ hMnext).mp hmassRatio |>.le
    have hpowMono :
        (k : ℝ) ^ (criticalExponent - 1) ≤
          (k + 1 : ℕ) ^ (criticalExponent - 1) := by
      apply Real.rpow_le_rpow
      · positivity
      · norm_num [Nat.cast_add, Nat.cast_one]
      · exact (sub_pos.mpr criticalExponent_gt_one).le
    have hMnextNonneg : 0 ≤ rankMass N cap δ (k + 1) := hMnext.le
    calc
      rankMass N cap δ k * (k : ℝ) ^ (criticalExponent - 1) ≤
          (2 * rankMass N cap δ (k + 1)) *
            (k : ℝ) ^ (criticalExponent - 1) := by
              exact mul_le_mul_of_nonneg_right hmassBoundary
                (Real.rpow_nonneg (by positivity : 0 ≤ (k : ℝ)) _)
      _ ≤ (2 * rankMass N cap δ (k + 1)) *
          (k + 1 : ℕ) ^ (criticalExponent - 1) := by
            exact mul_le_mul_of_nonneg_left hpowMono (by positivity)
      _ = 2 * (rankMass N cap δ (k + 1) *
          (k + 1 : ℕ) ^ (criticalExponent - 1)) := by ring
      _ ≤ 2 * (Real.exp endpointBudget * cap *
          (N : ℝ) ^ (criticalExponent - 1)) := by gcongr
      _ = propagationConstant * cap *
          (N : ℝ) ^ (criticalExponent - 1) := by
            unfold propagationConstant
            ring

end GD.Sqrt3LowerBound
