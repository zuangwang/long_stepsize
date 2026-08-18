import GD.Sqrt3LowerBound.ScheduleCertificate

/-!
# The finite rank-prefix certificate

This file proves the bounded-rank branch directly for the only ranks used by
the complete scan (`q ≤ 3`).  Unlike the former scalar interface, every case
returns either the empty chain or an explicit chronological global-rank
prefix.
-/

namespace GD.Sqrt3LowerBound

open scoped BigOperators

namespace ChainData

noncomputable def prefixShape (x : ℝ) : ℝ := x * (x + 2)

theorem rho_inv_identity {J : ℕ} (d : ChainData J) (i : Fin J) :
    (d.rho i)⁻¹ =
      d.omega i / d.delta i + d.omega i / d.nextScale i +
        d.omega i ^ 2 / (d.delta i * d.nextScale i) := by
  unfold rho scale
  have hω := d.omega_pos i
  have hδ := d.delta_pos i
  have hn := d.nextScale_pos i
  field_simp [hω.ne', hδ.ne', hn.ne']
  ring

theorem internal_rho_inv_le {J : ℕ} (d : ChainData J)
    (dmin : ℝ) (hdmin : 0 < dmin)
    (hdelta : ∀ i, dmin ≤ d.delta i)
    (i : ℕ) (hi : i + 1 < J) :
    (d.rhoNat i)⁻¹ ≤ prefixShape (d.omega ⟨i, by omega⟩ / dmin) := by
  have hi0 : i < J := by omega
  rw [rhoNat_of_lt d hi0, rho_inv_identity]
  unfold nextScale prefixShape
  simp only [dif_pos hi]
  let ii : Fin J := ⟨i, hi0⟩
  let jj : Fin J := ⟨i + 1, hi⟩
  have hω : 0 ≤ d.omega ii := (d.omega_pos ii).le
  have hδi : dmin ≤ d.delta ii := hdelta ii
  have hδj : dmin ≤ d.delta jj := hdelta jj
  have hn : dmin ≤ d.scale jj := hδj.trans (by
    unfold scale
    linarith [d.omega_pos jj])
  have hinvδ : (d.delta ii)⁻¹ ≤ dmin⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hdmin hδi
  have hinvn : (d.scale jj)⁻¹ ≤ dmin⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hdmin hn
  have hfirst : d.omega ii / d.delta ii ≤ d.omega ii / dmin := by
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hinvδ hω
  have hsecond : d.omega ii / d.scale jj ≤ d.omega ii / dmin := by
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hinvn hω
  have hprod :
      (d.delta ii * d.scale jj)⁻¹ ≤ (dmin * dmin)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le
      (mul_pos hdmin hdmin)
      (mul_le_mul hδi hn hdmin.le (d.delta_pos ii).le)
  have hthird :
      d.omega ii ^ 2 / (d.delta ii * d.scale jj) ≤
        d.omega ii ^ 2 / (dmin * dmin) := by
    simpa [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_left hprod (sq_nonneg (d.omega ii))
  dsimp [ii, jj] at hfirst hsecond hthird ⊢
  calc
    d.omega ⟨i, hi0⟩ / d.delta ⟨i, hi0⟩ +
          d.omega ⟨i, hi0⟩ / d.scale ⟨i + 1, hi⟩ +
          d.omega ⟨i, hi0⟩ ^ 2 /
            (d.delta ⟨i, hi0⟩ * d.scale ⟨i + 1, hi⟩) ≤
        d.omega ⟨i, hi0⟩ / dmin +
          d.omega ⟨i, hi0⟩ / dmin +
          d.omega ⟨i, hi0⟩ ^ 2 / (dmin * dmin) :=
      add_le_add (add_le_add hfirst hsecond) hthird
    _ = (d.omega ⟨i, hi0⟩ / dmin) *
        (d.omega ⟨i, hi0⟩ / dmin + 2) := by
      field_simp [hdmin.ne']
      ring

theorem terminal_rho_identity {J : ℕ} (d : ChainData J) (hJ : 1 ≤ J) :
    d.terminalScale * (d.rhoNat (J - 1))⁻¹ =
      d.omega ⟨J - 1, by omega⟩ *
        (1 + (d.omega ⟨J - 1, by omega⟩ + d.terminalScale) /
          d.delta ⟨J - 1, by omega⟩) := by
  have hlast : J - 1 < J := by omega
  rw [rhoNat_of_lt d hlast, rho_inv_identity]
  unfold nextScale
  simp only [dif_neg (show ¬(J - 1 + 1 < J) by omega)]
  have ht := d.terminalScale_pos
  have hδ := d.delta_pos ⟨J - 1, hlast⟩
  field_simp [ht.ne', hδ.ne']
  ring

theorem prefix_internal_product_le {J : ℕ} (d : ChainData J)
    (mass dmin : ℝ) (hJ1 : 1 ≤ J) (hJ3 : J ≤ 3)
    (_hmass : 0 < mass) (hdmin : 0 < dmin)
    (hdelta : ∀ i, dmin ≤ d.delta i)
    (hpartition : (∑ i, d.omega i) + (1 + d.terminalGap) = mass)
    (hloaded : mass ≤ J * dmin) :
    (∏ i ∈ Finset.range (J - 1), (d.rhoNat i)⁻¹) ≤
      (8 : ℝ) ^ (J - 1) := by
  have hsumomega : (∑ i, d.omega i) ≤ mass := by
    have : 0 ≤ 1 + d.terminalGap := by linarith [d.terminalGap_nonneg]
    linarith
  have hsumratio : (∑ i, d.omega i / dmin) ≤ J := by
    rw [← Finset.sum_div]
    apply (div_le_iff₀ hdmin).2
    exact hsumomega.trans hloaded
  interval_cases J
  · norm_num
  · simp only [Nat.reduceSubDiff, Finset.prod_range_succ, Finset.prod_range_zero,
      one_mul, pow_one]
    have hfac := internal_rho_inv_le d dmin hdmin hdelta 0 (by omega)
    have hx : d.omega ⟨0, by omega⟩ / dmin ≤ 2 := by
      have hsum : d.omega ⟨0, by omega⟩ / dmin +
          d.omega ⟨1, by omega⟩ / dmin ≤ 2 := by
        simpa [Fin.sum_univ_two] using hsumratio
      have hnonneg : 0 ≤ d.omega ⟨1, by omega⟩ / dmin :=
        div_nonneg (d.omega_pos _).le hdmin.le
      linarith
    have hx0 : 0 ≤ d.omega ⟨0, by omega⟩ / dmin :=
      div_nonneg (d.omega_pos _).le hdmin.le
    unfold prefixShape at hfac
    nlinarith
  · simp only [Nat.reduceSubDiff, Finset.prod_range_succ,
      Finset.prod_range_zero, one_mul, pow_two]
    have hfac0 := internal_rho_inv_le d dmin hdmin hdelta 0 (by omega)
    have hfac1 := internal_rho_inv_le d dmin hdmin hdelta 1 (by omega)
    let x := d.omega ⟨0, by omega⟩ / dmin
    let y := d.omega ⟨1, by omega⟩ / dmin
    have hx : 0 ≤ x := by
      dsimp [x]
      exact div_nonneg (d.omega_pos _).le hdmin.le
    have hy : 0 ≤ y := by
      dsimp [y]
      exact div_nonneg (d.omega_pos _).le hdmin.le
    have hxy : x + y ≤ 3 := by
      have hsum : x + y + d.omega ⟨2, by omega⟩ / dmin ≤ 3 := by
        simpa [Fin.sum_univ_succ, Fin.sum_univ_two, x, y, add_assoc] using hsumratio
      have hlast : 0 ≤ d.omega ⟨2, by omega⟩ / dmin :=
        div_nonneg (d.omega_pos _).le hdmin.le
      linarith
    have hx5 : x * (x + 2) ≤ 5 * x := by nlinarith
    have hy5 : y * (y + 2) ≤ 5 * y := by nlinarith
    have hxyprod : 4 * (x * y) ≤ 9 := by nlinarith [sq_nonneg (x - y)]
    unfold prefixShape at hfac0 hfac1
    have hrho1 : 0 < d.rhoNat 1 := by
      rw [rhoNat_of_lt d (by omega)]
      exact d.rho_pos _
    calc
      (d.rhoNat 0)⁻¹ * (d.rhoNat 1)⁻¹ ≤
          (x * (x + 2)) * (y * (y + 2)) := by
        exact mul_le_mul hfac0 hfac1 (inv_pos.mpr hrho1).le (by nlinarith)
      _ ≤ (5 * x) * (5 * y) :=
        mul_le_mul hx5 hy5 (by positivity) (by positivity)
      _ ≤ 8 * 8 := by nlinarith

theorem prefix_terminal_product_le {J : ℕ} (d : ChainData J)
    (mass dmin : ℝ) (hJ : 1 ≤ J) (hmass : 0 < mass)
    (_hdmin : 0 < dmin) (hdelta : ∀ i, dmin ≤ d.delta i)
    (hpartition : (∑ i, d.omega i) + (1 + d.terminalGap) = mass)
    (hloaded : mass ≤ J * dmin) :
    d.terminalScale * (d.rhoNat (J - 1))⁻¹ ≤ 3 * J * mass := by
  rw [terminal_rho_identity d hJ]
  let last : Fin J := ⟨J - 1, by omega⟩
  let omegaEnd := 1 + d.terminalGap
  have hωle : d.omega last ≤ mass := by
    have hsingle : d.omega last ≤ ∑ i, d.omega i :=
      Finset.single_le_sum (fun i _ ↦ (d.omega_pos i).le) (Finset.mem_univ last)
    have hend : 0 ≤ omegaEnd := by dsimp [omegaEnd]; linarith [d.terminalGap_nonneg]
    linarith
  have hpair : d.omega last + d.terminalScale ≤ 2 * mass := by
    have hpairMass : d.omega last + omegaEnd ≤ mass := by
      have hsingle : d.omega last ≤ ∑ i, d.omega i :=
        Finset.single_le_sum (fun i _ ↦ (d.omega_pos i).le) (Finset.mem_univ last)
      linarith
    unfold terminalScale
    dsimp [omegaEnd] at hpairMass ⊢
    nlinarith [d.omega_pos last]
  have hδlast : dmin ≤ d.delta last := hdelta last
  have hratio : (d.omega last + d.terminalScale) / d.delta last ≤ 2 * J := by
    have hden : 0 < d.delta last := d.delta_pos last
    apply (div_le_iff₀ hden).2
    have hmassJ : mass ≤ (J : ℝ) * d.delta last :=
      hloaded.trans (mul_le_mul_of_nonneg_left hδlast (by positivity))
    nlinarith
  dsimp [last] at hωle hpair hδlast hratio ⊢
  have hJreal : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hfactor :
      1 + (d.omega ⟨J - 1, by omega⟩ + d.terminalScale) /
          d.delta ⟨J - 1, by omega⟩ ≤ 1 + 2 * (J : ℝ) := by
    linarith
  have hmul :
      d.omega ⟨J - 1, by omega⟩ *
          (1 + (d.omega ⟨J - 1, by omega⟩ + d.terminalScale) /
            d.delta ⟨J - 1, by omega⟩) ≤
        mass * (1 + 2 * (J : ℝ)) := by
    exact mul_le_mul hωle hfactor
      (by
        have : 0 < (d.omega ⟨J - 1, by omega⟩ + d.terminalScale) /
            d.delta ⟨J - 1, by omega⟩ := by
          exact div_pos (add_pos (d.omega_pos _) d.terminalScale_pos)
            (d.delta_pos _)
        linarith)
      hmass.le
  nlinarith [mul_nonneg hmass.le (sub_nonneg.mpr hJreal)]

theorem loadedPrefixContribution {J : ℕ} (d : ChainData J)
    (mass dmin : ℝ) (hJ1 : 1 ≤ J) (hJ3 : J ≤ 3)
    (hmass : 0 < mass) (hdmin : 0 < dmin)
    (hdelta : ∀ i, dmin ≤ d.delta i)
    (hpartition : (∑ i, d.omega i) + (1 + d.terminalGap) = mass)
    (hloaded : mass ≤ J * dmin) :
    1 / (3 * J * mass * (8 : ℝ) ^ (J - 1)) ≤ d.contribution := by
  have hi := prefix_internal_product_le d mass dmin hJ1 hJ3 hmass hdmin
    hdelta hpartition hloaded
  have ht := prefix_terminal_product_le d mass dmin hJ1 hmass hdmin
    hdelta hpartition hloaded
  have hfull :
      d.terminalScale * (∏ i, (d.rho i)⁻¹) ≤
        3 * J * mass * (8 : ℝ) ^ (J - 1) := by
    have hsplit :
        (∏ i, (d.rho i)⁻¹) =
          (∏ i ∈ Finset.range (J - 1), (d.rhoNat i)⁻¹) *
            (d.rhoNat (J - 1))⁻¹ := by
      rw [Finset.prod_inv_distrib, prod_rhoNat,
        ← Finset.prod_inv_distrib, ← Finset.prod_range_succ]
      congr 2
      omega
    rw [hsplit]
    calc
      d.terminalScale *
          ((∏ i ∈ Finset.range (J - 1), (d.rhoNat i)⁻¹) *
            (d.rhoNat (J - 1))⁻¹) =
          (d.terminalScale * (d.rhoNat (J - 1))⁻¹) *
            (∏ i ∈ Finset.range (J - 1), (d.rhoNat i)⁻¹) := by ring
      _ ≤ (3 * J * mass) * (8 : ℝ) ^ (J - 1) :=
        mul_le_mul ht hi
          ((Finset.prod_pos fun i hi ↦ inv_pos.mpr (by
            rw [rhoNat_of_lt d (by
              have := Finset.mem_range.mp hi
              omega)]
            exact d.rho_pos _)).le)
          (by positivity)
      _ = 3 * J * mass * (8 : ℝ) ^ (J - 1) := by ring
  have hleft : 0 < d.terminalScale * ∏ i, (d.rho i)⁻¹ := by
    exact mul_pos d.terminalScale_pos (Finset.prod_pos fun i _ ↦ inv_pos.mpr (d.rho_pos i))
  have hright : 0 < 3 * J * mass * (8 : ℝ) ^ (J - 1) := by positivity
  have hinv := one_div_le_one_div_of_le hleft hfull
  unfold contribution
  rw [Finset.prod_inv_distrib] at hinv
  have hp : 0 < ∏ i, d.rho i := Finset.prod_pos fun i _ ↦ d.rho_pos i
  field_simp [d.terminalScale_pos.ne', hp.ne'] at hinv ⊢
  exact hinv

end ChainData

theorem emptyChainContribution {T : ℕ} {α : Fin T → ℝ}
    (hα : ∀ t, 0 ≤ α t) :
    HasChainContribution α hα
      (1 / (2 * rankMass (positiveSurplusCount α) (cappedMass α)
        (rankedSurplus α) 0)) := by
  let c : Finset (Fin T) := ∅
  let hc : ∀ t ∈ c, 0 < stepSurplus α t := by simp [c]
  let d := scheduleChainData α hα c hc
  let mass := rankMass (positiveSurplusCount α) (cappedMass α)
    (rankedSurplus α) 0
  have hmassEq : mass = 1 + ∑ t, α t := by
    dsimp [mass]
    simpa [rankPrefix] using rankMass_eq_unmarked hα 0 (Nat.zero_le _)
  have hsum : 0 ≤ ∑ t, α t := Finset.sum_nonneg fun t _ ↦ hα t
  have hmass : 0 < mass := by rw [hmassEq]; linarith
  have hvalue : d.contribution = 1 / (1 + 2 * ∑ t, α t) := by
    simp [d, c, scheduleChainData, ChainData.contribution,
      ChainData.terminalScale, chronologicalGap, marksBefore]
  have hden : 0 < 2 * mass - 1 := by rw [hmassEq]; nlinarith
  have hinv : 1 / (2 * mass) ≤ 1 / (2 * mass - 1) := by
    exact one_div_le_one_div_of_le hden (by linarith)
  refine ⟨c, hc, ?_⟩
  change 1 / (2 * mass) ≤ d.contribution
  rw [hvalue, hmassEq]
  rw [hmassEq] at hinv
  convert hinv using 1
  all_goals ring

theorem scheduleLoadedPrefixContribution {T : ℕ} {α : Fin T → ℝ}
    (hα : ∀ t, 0 ≤ α t) (k : ℕ) (hk1 : 1 ≤ k) (hk3 : k ≤ 3)
    (hkN : k ≤ positiveSurplusCount α)
    (hloaded : rankMass (positiveSurplusCount α) (cappedMass α)
      (rankedSurplus α) k ≤ k * rankedSurplus α (k - 1)) :
    HasChainContribution α hα
      (1 / (3 * k *
        rankMass (positiveSurplusCount α) (cappedMass α)
          (rankedSurplus α) k * (8 : ℝ) ^ (k - 1))) := by
  let c := rankPrefix α k hkN
  let hc : ∀ t ∈ c, 0 < stepSurplus α t :=
    fun _ ht ↦ rankPrefix_surplus_pos α k hkN ht
  let d := scheduleChainData α hα c hc
  let mass := rankMass (positiveSurplusCount α) (cappedMass α)
    (rankedSurplus α) k
  let dmin := rankedSurplus α (k - 1)
  have hcard : c.card = k := rankPrefix_card α k hkN
  have hmass : 0 < mass := by
    dsimp [mass]
    apply rankMass_pos _ _ _ _ hkN (cappedMass_pos hα)
    intro i hi
    exact (rankedSurplus_pos α hi).le
  have hdmin : 0 < dmin := by
    dsimp [dmin]
    apply rankedSurplus_pos α
    exact lt_of_lt_of_le (Nat.sub_lt hk1 (by omega)) hkN
  have hdelta : ∀ i, dmin ≤ d.delta i := by
    intro i
    dsimp [d, dmin, c, hc]
    exact rankPrefixChain_delta_ge_last hα k hk1 hkN i
  have hpartition : (∑ i, d.omega i) + (1 + d.terminalGap) = mass := by
    dsimp [d, mass, c, hc]
    exact scheduleChain_rankMass_partition hα k hkN
  have hbound := d.loadedPrefixContribution mass dmin
    (by omega) (by omega) hmass hdmin hdelta hpartition (by
      dsimp [mass, dmin]
      simpa [hcard] using hloaded)
  refine ⟨c, hc, ?_⟩
  simpa [hcard, mass] using hbound

private theorem cutoff_reciprocal_mono {mass denominator : ℝ}
    (hmass : 0 < mass) (hdenominator : 0 < denominator)
    (hden : denominator ≤ 768 * mass) :
    (1 / 768 : ℝ) / mass ≤ 1 / denominator := by
  calc
    (1 / 768 : ℝ) / mass = 1 / (768 * mass) := by
      field_simp [hmass.ne']
    _ ≤ 1 / denominator := one_div_le_one_div_of_le hdenominator hden

/-- Concrete bounded-rank prefix certificate.  This is the bridge consumed
by the complete cutoff scan; no external `hempty` or `hprefix` premise
remains. -/
theorem scheduleFiniteCutoffContribution {T : ℕ} {α : Fin T → ℝ}
    (hα : ∀ t, 0 ≤ α t) (q : ℕ) (hq3 : q ≤ 3)
    (hqN : q ≤ positiveSurplusCount α) :
    HasChainContribution α hα
      ((1 / 768 : ℝ) /
        rankMass (positiveSurplusCount α) (cappedMass α)
          (rankedSurplus α) q) := by
  let N := positiveSurplusCount α
  let cap := cappedMass α
  let δ := rankedSurplus α
  let M : ℕ → ℝ := fun j ↦ rankMass N cap δ j
  have hcap : 0 < cap := by dsimp [cap]; exact cappedMass_pos hα
  have hδ : ∀ i < N, 0 < δ i := by
    intro i hi
    exact rankedSurplus_pos α hi
  have hMpos : ∀ j, j ≤ N → 0 < M j := by
    intro j hj
    dsimp [M]
    exact rankMass_pos N cap δ j hj hcap fun i hi ↦ (hδ i hi).le
  have hstep : ∀ j, 1 ≤ j → M (j - 1) = M j + δ (j - 1) := by
    intro j hj
    exact rankMass_step N cap δ j hj
  change HasChainContribution α hα ((1 / 768 : ℝ) / M q)
  interval_cases q
  · have hM0 := hMpos 0 (by omega)
    apply HasChainContribution.mono
      (cutoff_reciprocal_mono (mass := M 0) (denominator := 2 * M 0)
        hM0 (mul_pos (by norm_num) hM0) (by nlinarith))
    simpa [M, N, cap, δ] using emptyChainContribution hα
  · have hM0 := hMpos 0 (by omega)
    have hM1 := hMpos 1 (by omega)
    have hd0 := hδ 0 (by omega)
    have hs1 := hstep 1 (by omega)
    norm_num at hs1
    by_cases hload1 : M 1 ≤ (1 : ℝ) * δ 0
    · have hcand := scheduleLoadedPrefixContribution hα 1 (by omega) (by omega)
        (by simpa [N] using hqN) (by simpa [M, N, cap, δ] using hload1)
      apply HasChainContribution.mono
        (cutoff_reciprocal_mono (mass := M 1)
          (denominator := 3 * (1 : ℝ) * M 1 * 8 ^ (1 - 1)) hM1 (by positivity)
          (show 3 * (1 : ℝ) * M 1 * 8 ^ (1 - 1) ≤ 768 * M 1 by norm_num; nlinarith))
      simpa [M, N, cap, δ] using hcand
    · have hlight1 : δ 0 < M 1 := by nlinarith
      have hcand := emptyChainContribution hα
      apply HasChainContribution.mono
        (cutoff_reciprocal_mono (mass := M 1) (denominator := 2 * M 0)
          hM1 (mul_pos (by norm_num) hM0) (by nlinarith))
      simpa [M, N, cap, δ] using hcand
  · have hM0 := hMpos 0 (by omega)
    have hM1 := hMpos 1 (by omega)
    have hM2 := hMpos 2 (by omega)
    have hd0 := hδ 0 (by omega)
    have hd1 := hδ 1 (by omega)
    have hs1 := hstep 1 (by omega)
    have hs2 := hstep 2 (by omega)
    norm_num at hs1 hs2
    by_cases hload2 : M 2 ≤ (2 : ℝ) * δ 1
    · have hcand := scheduleLoadedPrefixContribution hα 2 (by omega) (by omega)
        (by simpa [N] using hqN) (by simpa [M, N, cap, δ] using hload2)
      apply HasChainContribution.mono
        (cutoff_reciprocal_mono (mass := M 2)
          (denominator := 3 * (2 : ℝ) * M 2 * 8 ^ (2 - 1)) hM2 (by positivity)
          (show 3 * (2 : ℝ) * M 2 * 8 ^ (2 - 1) ≤ 768 * M 2 by norm_num; nlinarith))
      simpa [M, N, cap, δ] using hcand
    · have hlight2 : 2 * δ 1 < M 2 := by nlinarith
      by_cases hload1 : M 1 ≤ (1 : ℝ) * δ 0
      · have hcand := scheduleLoadedPrefixContribution hα 1 (by omega) (by omega)
          (by omega) (by simpa [M, N, cap, δ] using hload1)
        have hden : 3 * (1 : ℝ) * M 1 * 8 ^ (1 - 1) ≤ 768 * M 2 := by
          norm_num
          nlinarith
        apply HasChainContribution.mono
          (cutoff_reciprocal_mono (mass := M 2)
            (denominator := 3 * (1 : ℝ) * M 1 * 8 ^ (1 - 1))
            hM2 (by positivity) hden)
        simpa [M, N, cap, δ] using hcand
      · have hlight1 : δ 0 < M 1 := by nlinarith
        have hcand := emptyChainContribution hα
        have hden : 2 * M 0 ≤ 768 * M 2 := by nlinarith
        apply HasChainContribution.mono
          (cutoff_reciprocal_mono (mass := M 2) (denominator := 2 * M 0)
            hM2 (mul_pos (by norm_num) hM0) hden)
        simpa [M, N, cap, δ] using hcand
  · have hM0 := hMpos 0 (by omega)
    have hM1 := hMpos 1 (by omega)
    have hM2 := hMpos 2 (by omega)
    have hM3 := hMpos 3 (by omega)
    have hd0 := hδ 0 (by omega)
    have hd1 := hδ 1 (by omega)
    have hd2 := hδ 2 (by omega)
    have hs1 := hstep 1 (by omega)
    have hs2 := hstep 2 (by omega)
    have hs3 := hstep 3 (by omega)
    norm_num at hs1 hs2 hs3
    by_cases hload3 : M 3 ≤ (3 : ℝ) * δ 2
    · have hcand := scheduleLoadedPrefixContribution hα 3 (by omega) (by omega)
        (by simpa [N] using hqN) (by simpa [M, N, cap, δ] using hload3)
      apply HasChainContribution.mono
        (cutoff_reciprocal_mono (mass := M 3)
          (denominator := 3 * (3 : ℝ) * M 3 * 8 ^ (3 - 1)) hM3 (by positivity)
          (show 3 * (3 : ℝ) * M 3 * 8 ^ (3 - 1) ≤ 768 * M 3 by norm_num; nlinarith))
      simpa [M, N, cap, δ] using hcand
    · have hlight3 : 3 * δ 2 < M 3 := by nlinarith
      by_cases hload2 : M 2 ≤ (2 : ℝ) * δ 1
      · have hcand := scheduleLoadedPrefixContribution hα 2 (by omega) (by omega)
          (by omega) (by simpa [M, N, cap, δ] using hload2)
        have hden : 3 * (2 : ℝ) * M 2 * 8 ^ (2 - 1) ≤ 768 * M 3 := by
          norm_num
          nlinarith
        apply HasChainContribution.mono
          (cutoff_reciprocal_mono (mass := M 3)
            (denominator := 3 * (2 : ℝ) * M 2 * 8 ^ (2 - 1))
            hM3 (by positivity) hden)
        simpa [M, N, cap, δ] using hcand
      · have hlight2 : 2 * δ 1 < M 2 := by nlinarith
        by_cases hload1 : M 1 ≤ (1 : ℝ) * δ 0
        · have hcand := scheduleLoadedPrefixContribution hα 1 (by omega) (by omega)
            (by omega) (by simpa [M, N, cap, δ] using hload1)
          have hden : 3 * (1 : ℝ) * M 1 * 8 ^ (1 - 1) ≤ 768 * M 3 := by
            norm_num
            nlinarith
          apply HasChainContribution.mono
            (cutoff_reciprocal_mono (mass := M 3)
              (denominator := 3 * (1 : ℝ) * M 1 * 8 ^ (1 - 1))
              hM3 (by positivity) hden)
          simpa [M, N, cap, δ] using hcand
        · have hlight1 : δ 0 < M 1 := by nlinarith
          have hcand := emptyChainContribution hα
          have hden : 2 * M 0 ≤ 768 * M 3 := by nlinarith
          apply HasChainContribution.mono
            (cutoff_reciprocal_mono (mass := M 3) (denominator := 2 * M 0)
              hM3 (mul_pos (by norm_num) hM0) hden)
          simpa [M, N, cap, δ] using hcand

end GD.Sqrt3LowerBound
