import GD.Sqrt3LowerBound.Schedule

/-!
# Chronological normalization of a concrete marked chain

The results in this file prove equations (3.6), (3.8), (3.11), and (3.14)
from the report for an actual `ChainData`.  In particular, the abstract
`BlockState` sequence used by `halfDensityCertificate` is constructed here,
and its inverse product is proved to be exactly the reciprocal of the same
chain contribution.
-/

namespace GD.Sqrt3LowerBound

open scoped BigOperators

namespace ChainData

/-- Average residual mass per marked step. -/
noncomputable def meanMass {J : ℕ} (_d : ChainData J) (mass : ℝ) : ℝ :=
  mass / J

theorem meanMass_pos {J : ℕ} (d : ChainData J) {mass : ℝ}
    (hJ : 1 ≤ J) (hmass : 0 < mass) : 0 < d.meanMass mass := by
  unfold meanMass
  exact div_pos hmass (by exact_mod_cast hJ)

/-- The normalized state `(b_i,u_i)`; values beyond the chain are harmless
defaults, because all theorems use only `i < J`. -/
noncomputable def normalizedState {J : ℕ} (d : ChainData J)
    (mass : ℝ) (hJ : 1 ≤ J) (hmass : 0 < mass) (i : ℕ) : BlockState :=
  if hi : i < J then
    { b := d.omega ⟨i, hi⟩ / d.meanMass mass
      u := 2 * d.meanMass mass / d.delta ⟨i, hi⟩
      b_pos := div_pos (d.omega_pos _) (d.meanMass_pos hJ hmass)
      u_pos := div_pos (mul_pos (by norm_num) (d.meanMass_pos hJ hmass))
        (d.delta_pos _) }
  else
    { b := 1, u := 1, b_pos := by norm_num, u_pos := by norm_num }

theorem normalizedState_b {J : ℕ} (d : ChainData J)
    (mass : ℝ) (hJ : 1 ≤ J) (hmass : 0 < mass) {i : ℕ} (hi : i < J) :
    (d.normalizedState mass hJ hmass i).b =
      d.omega ⟨i, hi⟩ / d.meanMass mass := by
  simp [normalizedState, hi]

theorem normalizedState_u {J : ℕ} (d : ChainData J)
    (mass : ℝ) (hJ : 1 ≤ J) (hmass : 0 < mass) {i : ℕ} (hi : i < J) :
    (d.normalizedState mass hJ hmass i).u =
      2 * d.meanMass mass / d.delta ⟨i, hi⟩ := by
  simp [normalizedState, hi]

theorem normalizedState_scale {J : ℕ} (d : ChainData J)
    (mass : ℝ) (hJ : 1 ≤ J) (hmass : 0 < mass) {i : ℕ} (hi : i < J) :
    (d.normalizedState mass hJ hmass i).scale =
      d.scale ⟨i, hi⟩ / d.meanMass mass := by
  rw [BlockState.scale, normalizedState_b d mass hJ hmass hi,
    normalizedState_u d mass hJ hmass hi]
  unfold scale
  have hm := d.meanMass_pos hJ hmass
  have hd := d.delta_pos ⟨i, hi⟩
  field_simp [hm.ne', hd.ne']

/-- Density expressed in chronological rather than ranked order. -/
noncomputable def chronologicalDensity {J : ℕ} (d : ChainData J)
    (mass : ℝ) : ℝ :=
  mass / (J : ℝ) ^ 2 * ∑ i, (d.delta i)⁻¹

noncomputable def normalizedTerminal {J : ℕ} (d : ChainData J)
    (mass : ℝ) : ℝ := d.terminalScale / d.meanMass mass

noncomputable def normalizedEndMass {J : ℕ} (d : ChainData J)
    (mass : ℝ) : ℝ := (1 + d.terminalGap) / d.meanMass mass

/-- Total natural-number indexing of `rho`, used only to remove dependent
casts in finite range products. -/
noncomputable def rhoNat {J : ℕ} (d : ChainData J) (i : ℕ) : ℝ :=
  if hi : i < J then d.rho ⟨i, hi⟩ else 1

theorem rhoNat_of_lt {J : ℕ} (d : ChainData J) {i : ℕ} (hi : i < J) :
    d.rhoNat i = d.rho ⟨i, hi⟩ := by
  simp [rhoNat, hi]

theorem prod_rhoNat {J : ℕ} (d : ChainData J) :
    (∏ i, d.rho i) = ∏ i ∈ Finset.range J, d.rhoNat i := by
  rw [Finset.prod_fin_eq_prod_range]
  apply Finset.prod_congr rfl
  intro i hi
  simp [rhoNat, Finset.mem_range.mp hi]

theorem normalized_sum_b {J : ℕ} (d : ChainData J) (mass : ℝ)
    (hJ : 1 ≤ J) (hmass : 0 < mass)
    (hpartition : (∑ i, d.omega i) + (1 + d.terminalGap) = mass) :
    (∑ i ∈ Finset.range J, (d.normalizedState mass hJ hmass i).b) =
      J - d.normalizedEndMass mass := by
  have hm := d.meanMass_pos hJ hmass
  rw [Finset.sum_range]
  have hb :
      (∑ i : Fin J, (d.normalizedState mass hJ hmass i).b) =
        ∑ i : Fin J, d.omega i / d.meanMass mass := by
    apply Finset.sum_congr rfl
    intro i _
    exact normalizedState_b d mass hJ hmass i.isLt
  rw [hb]
  rw [← Finset.sum_div]
  unfold normalizedEndMass meanMass
  have hJ0 : (J : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hJ)
  field_simp [hm.ne', hmass.ne', hJ0]
  nlinarith

theorem normalized_sum_u {J : ℕ} (d : ChainData J) (mass : ℝ)
    (hJ : 1 ≤ J) (hmass : 0 < mass) :
    (∑ i ∈ Finset.range J, (d.normalizedState mass hJ hmass i).u) =
      2 * J * d.chronologicalDensity mass := by
  rw [Finset.sum_range]
  have hu :
      (∑ i : Fin J, (d.normalizedState mass hJ hmass i).u) =
        ∑ i : Fin J, 2 * d.meanMass mass / d.delta i := by
    apply Finset.sum_congr rfl
    intro i _
    exact normalizedState_u d mass hJ hmass i.isLt
  rw [hu]
  simp only [div_eq_mul_inv]
  rw [← Finset.mul_sum]
  unfold chronologicalDensity meanMass
  have hJ0 : (J : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hJ)
  field_simp [hJ0]

theorem normalizedTerminal_pos {J : ℕ} (d : ChainData J) (mass : ℝ)
    (hJ : 1 ≤ J) (hmass : 0 < mass) :
    0 < d.normalizedTerminal mass := by
  unfold normalizedTerminal
  exact div_pos d.terminalScale_pos (d.meanMass_pos hJ hmass)

theorem normalizedEndMass_pos {J : ℕ} (d : ChainData J) (mass : ℝ)
    (hJ : 1 ≤ J) (hmass : 0 < mass) :
    0 < d.normalizedEndMass mass := by
  unfold normalizedEndMass
  exact div_pos (by linarith [d.terminalGap_nonneg])
    (d.meanMass_pos hJ hmass)

theorem normalizedTerminal_lt {J : ℕ} (d : ChainData J) (mass : ℝ)
    (hJ : 1 ≤ J) (hmass : 0 < mass)
    (hpartition : (∑ i, d.omega i) + (1 + d.terminalGap) = mass) :
    d.normalizedTerminal mass < 2 * J := by
  have homega : 0 < ∑ i, d.omega i :=
    Finset.sum_pos (fun i _ ↦ d.omega_pos i)
      ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hendlt : 1 + d.terminalGap < mass := by linarith
  have hterminal : d.terminalScale < 2 * mass := by
    unfold terminalScale
    linarith
  unfold normalizedTerminal meanMass
  have hJpos : 0 < (J : ℝ) := by exact_mod_cast hJ
  apply (div_lt_iff₀ (div_pos hmass hJpos)).2
  field_simp [hmass.ne', hJpos.ne']
  nlinarith

theorem normalized_edge_eq_rho_inv {J : ℕ} (d : ChainData J)
    (mass : ℝ) (hJ : 1 ≤ J) (hmass : 0 < mass)
    (i : ℕ) (hi : i + 1 < J) :
    edgeFactor (d.normalizedState mass hJ hmass i)
        (d.normalizedState mass hJ hmass (i + 1)) =
      (d.rho ⟨i, lt_trans (Nat.lt_succ_self i) hi⟩)⁻¹ := by
  have hi0 : i < J := lt_trans (Nat.lt_succ_self i) hi
  rw [edgeFactor, normalizedState_b d mass hJ hmass hi0,
    normalizedState_u d mass hJ hmass hi0,
    normalizedState_scale d mass hJ hmass hi0,
    normalizedState_scale d mass hJ hmass hi]
  unfold rho nextScale
  simp only [dif_pos hi]
  unfold scale meanMass
  have hmean := d.meanMass_pos hJ hmass
  have hω := d.omega_pos ⟨i, hi0⟩
  have hδ := d.delta_pos ⟨i, hi0⟩
  have hnext := d.scale_pos ⟨i + 1, hi⟩
  field_simp [hmean.ne', hω.ne', hδ.ne', hnext.ne']

theorem normalized_terminal_factor {J : ℕ} (d : ChainData J)
    (mass : ℝ) (hJ : 1 ≤ J) (hmass : 0 < mass) :
    let n := J - 1
    ((d.normalizedState mass hJ hmass n).b *
        (d.normalizedState mass hJ hmass n).u *
        ((d.normalizedState mass hJ hmass n).scale +
          d.normalizedTerminal mass) / (4 * (n + 1 : ℝ))) =
      d.terminalScale / (2 * mass) *
        (d.rho ⟨J - 1, Nat.sub_lt (by omega) (by omega)⟩)⁻¹ := by
  dsimp only
  have hn : J - 1 < J := Nat.sub_lt (by omega) (by omega)
  have hsucc : J - 1 + 1 = J := Nat.sub_add_cancel hJ
  rw [normalizedState_b d mass hJ hmass hn,
    normalizedState_u d mass hJ hmass hn,
    normalizedState_scale d mass hJ hmass hn]
  unfold normalizedTerminal rho nextScale
  simp only [dif_neg (show ¬(J - 1 + 1 < J) by omega)]
  unfold scale meanMass
  have hmean := d.meanMass_pos hJ hmass
  have hω := d.omega_pos ⟨J - 1, hn⟩
  have hδ := d.delta_pos ⟨J - 1, hn⟩
  have ht := d.terminalScale_pos
  have hsuccR : ((J - 1 : ℕ) : ℝ) + 1 = (J : ℝ) := by
    exact_mod_cast hsucc
  field_simp [hmean.ne', hmass.ne', hω.ne', hδ.ne', ht.ne']
  simp only [hsuccR]
  ring

/-- Exact bridge between the temporal-product normalization and the
concrete chronological `rho` product. -/
theorem inverseChainProduct_eq {J : ℕ} (d : ChainData J)
    (mass : ℝ) (hJ : 2 ≤ J) (hmass : 0 < mass) :
    inverseChainProduct (d.normalizedState mass (by omega) hmass) (J - 1)
        (d.normalizedTerminal mass) =
      d.terminalScale / (2 * mass) * ∏ i, (d.rho i)⁻¹ := by
  let hJ1 : 1 ≤ J := by omega
  unfold inverseChainProduct
  rw [normalized_terminal_factor d mass hJ1 hmass]
  have hedge :
      (∏ i ∈ Finset.range (J - 1),
          edgeFactor (d.normalizedState mass hJ1 hmass i)
            (d.normalizedState mass hJ1 hmass (i + 1))) =
        ∏ i ∈ Finset.range (J - 1), (d.rhoNat i)⁻¹ := by
    apply Finset.prod_congr rfl
    intro i hi
    have hi' : i < J - 1 := Finset.mem_range.mp hi
    rw [rhoNat_of_lt d (by omega)]
    exact normalized_edge_eq_rho_inv d mass hJ1 hmass i (by omega)
  rw [hedge]
  have hprod :
      (∏ i, (d.rho i)⁻¹) =
        (∏ i ∈ Finset.range (J - 1), (d.rhoNat i)⁻¹) *
          (d.rhoNat (J - 1))⁻¹ := by
    rw [Finset.prod_inv_distrib, prod_rhoNat,
      ← Finset.prod_inv_distrib, ← Finset.prod_range_succ]
    congr 2
    omega
  rw [hprod]
  rw [rhoNat_of_lt d (by omega)]
  ring

theorem reciprocal_inverseChainProduct_eq_contribution {J : ℕ}
    (d : ChainData J) (mass : ℝ) (hJ : 2 ≤ J) (hmass : 0 < mass) :
    1 / (2 * mass *
      inverseChainProduct (d.normalizedState mass (by omega) hmass) (J - 1)
        (d.normalizedTerminal mass)) = d.contribution := by
  rw [inverseChainProduct_eq d mass hJ hmass]
  unfold contribution
  have ht := d.terminalScale_pos
  have hp : 0 < ∏ i, d.rho i := Finset.prod_pos fun i _ ↦ d.rho_pos i
  rw [Finset.prod_inv_distrib]
  field_simp [hmass.ne', ht.ne', hp.ne']

end ChainData

end GD.Sqrt3LowerBound
