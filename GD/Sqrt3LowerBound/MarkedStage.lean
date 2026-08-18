import GD.Sqrt3LowerBound.Realization
import GD.Sqrt3LowerBound.MoreauEnvelope

/-!
# Concrete marked-stage geometry

This file constructs the Euclidean polytope used in the report's marked-stage
realization.  Unlike the earlier terminal algebra, the declarations here
identify the projection (and hence the gradient) on every point of every
chronological block.
-/

namespace GD.Sqrt3LowerBound

open scoped BigOperators RealInnerProductSpace Gradient

namespace ChainData

/-- Euclidean space with one orthogonal coordinate per stage. -/
abbrev StageSpace (J : ℕ) := EuclideanSpace ℝ (Fin (J + 1))

/-- The square-root transition parameter. -/
noncomputable def kappa {J : ℕ} (d : ChainData J) (i : Fin J) : ℝ :=
  Real.sqrt (d.rho i)

theorem kappa_pos {J : ℕ} (d : ChainData J) (i : Fin J) :
    0 < d.kappa i := Real.sqrt_pos.2 (d.rho_pos i)

theorem kappa_sq {J : ℕ} (d : ChainData J) (i : Fin J) :
    d.kappa i ^ 2 = d.rho i := Real.sq_sqrt (d.rho_pos i).le

/-- Amplitude of coordinate `i`. -/
noncomputable def amplitude {J : ℕ} (d : ChainData J) (i : ℕ) : ℝ :=
  stageAmplitude (fun n ↦ Real.sqrt (d.rhoNat n)) i

@[simp] theorem amplitude_zero {J : ℕ} (d : ChainData J) :
    d.amplitude 0 = 1 := rfl

theorem amplitude_succ {J : ℕ} (d : ChainData J) {i : ℕ} (hi : i < J) :
    d.amplitude (i + 1) = d.kappa ⟨i, hi⟩ * d.amplitude i := by
  simp only [amplitude, stageAmplitude, kappa]
  rw [rhoNat_of_lt d hi]

theorem amplitude_pos {J : ℕ} (d : ChainData J) (i : ℕ) :
    0 < d.amplitude i := by
  induction i with
  | zero => simp
  | succ i ih =>
      simp only [amplitude, stageAmplitude]
      exact mul_pos (Real.sqrt_pos.2 (by
        unfold rhoNat
        split_ifs with hi
        · exact d.rho_pos _
        · norm_num)) ih

/-- The point `P_i = σ_i u_i`. -/
noncomputable def stagePoint {J : ℕ} (d : ChainData J)
    (i : Fin (J + 1)) : StageSpace J :=
  EuclideanSpace.single i (d.amplitude i)

/-- Scale at a stage: `Ω_i` internally and `Ω_J` at the terminal stage. -/
noncomputable def geometricScale {J : ℕ} (d : ChainData J)
    (i : Fin (J + 1)) : ℝ :=
  if hi : i.val < J then d.scale ⟨i, hi⟩ else d.terminalScale

theorem geometricScale_pos {J : ℕ} (d : ChainData J) (i : Fin (J + 1)) :
    0 < d.geometricScale i := by
  unfold geometricScale
  split_ifs with hi
  · exact d.scale_pos _
  · exact d.terminalScale_pos

@[simp] theorem geometricScale_internal {J : ℕ} (d : ChainData J) (i : Fin J) :
    d.geometricScale i.castSucc = d.scale i := by
  simp [geometricScale]

@[simp] theorem geometricScale_terminal {J : ℕ} (d : ChainData J) :
    d.geometricScale (Fin.last J) = d.terminalScale := by
  simp [geometricScale]

/-- The candidate projected gradient `p_i`. -/
noncomputable def stageGradient {J : ℕ} (d : ChainData J)
    (i : Fin (J + 1)) : StageSpace J :=
  EuclideanSpace.single i (d.amplitude i / d.geometricScale i) -
    if hi : i.val < J then
      EuclideanSpace.single (⟨i.val + 1, by omega⟩ : Fin (J + 1))
        (d.amplitude i * d.kappa ⟨i, hi⟩ / d.geometricScale i)
    else 0

theorem stageGradient_internal {J : ℕ} (d : ChainData J) (i : Fin J) :
    d.stageGradient i.castSucc =
      EuclideanSpace.single i.castSucc (d.amplitude i / d.scale i) -
      EuclideanSpace.single i.succ
        (d.amplitude i * d.kappa i / d.scale i) := by
  simp only [stageGradient, Fin.val_castSucc, i.isLt, dite_true,
    geometricScale_internal]
  congr 2

theorem stageGradient_terminal {J : ℕ} (d : ChainData J) :
    d.stageGradient (Fin.last J) =
      EuclideanSpace.single (Fin.last J)
        (d.amplitude J / d.terminalScale) := by
  simp [stageGradient, geometricScale]

/-- Vertices of the polytope: zero and all stage gradients. -/
noncomputable def markedVertex {J : ℕ} (d : ChainData J) :
    Option (Fin (J + 1)) → StageSpace J
  | none => 0
  | some i => d.stageGradient i

/-- The direct finite-polytope Moreau envelope realizing the chain. -/
noncomputable def markedEnvelope {J : ℕ} (d : ChainData J) :
    StageSpace J → ℝ :=
  finiteEnvelope d.markedVertex

theorem zero_mem_markedPolytope {J : ℕ} (d : ChainData J) :
    (0 : StageSpace J) ∈ finitePolytope d.markedVertex := by
  apply subset_convexHull ℝ _
  exact ⟨none, rfl⟩

theorem markedEnvelope_convex {J : ℕ} (d : ChainData J) :
    ConvexOn ℝ Set.univ d.markedEnvelope :=
  finiteEnvelope_convex d.markedVertex

theorem markedEnvelope_hasGradient {J : ℕ} (d : ChainData J) (x : StageSpace J) :
    HasGradientAt d.markedEnvelope (finiteProjection d.markedVertex x) x :=
  finiteEnvelope_hasGradient d.markedVertex x

theorem markedEnvelope_one_smooth {J : ℕ} (d : ChainData J) :
    LipschitzWith 1 (∇ d.markedEnvelope) :=
  finiteEnvelope_one_smooth d.markedVertex

theorem markedEnvelope_minimized_at_zero {J : ℕ} (d : ChainData J) :
    d.markedEnvelope 0 = 0 ∧ ∀ x, d.markedEnvelope 0 ≤ d.markedEnvelope x :=
  finiteEnvelope_minimized_at_zero d.markedVertex d.zero_mem_markedPolytope

/-- Point on an internal block after cumulative gap mass `τ`. -/
noncomputable def internalPath {J : ℕ} (d : ChainData J)
    (i : Fin J) (τ : ℝ) : StageSpace J :=
  d.stagePoint i.castSucc - τ • d.stageGradient i.castSucc

/-- Point on the terminal block after cumulative terminal mass `τ`. -/
noncomputable def terminalPath {J : ℕ} (d : ChainData J) (τ : ℝ) : StageSpace J :=
  d.stagePoint (Fin.last J) - τ • d.stageGradient (Fin.last J)

/-- The residual used by the projection criterion on an internal block. -/
noncomputable def internalResidual {J : ℕ} (d : ChainData J)
    (i : Fin J) (a : ℝ) : StageSpace J :=
  d.internalPath i (a - 1) - d.stageGradient i.castSucc

theorem internalResidual_eq {J : ℕ} (d : ChainData J)
    (i : Fin J) (a : ℝ) :
    d.internalResidual i a =
      EuclideanSpace.single i.castSucc
        (d.amplitude i * (d.scale i - a) / d.scale i) +
      EuclideanSpace.single i.succ
        (d.amplitude i * d.kappa i * a / d.scale i) := by
  rw [internalResidual, internalPath, stageGradient_internal]
  unfold stagePoint
  ext k
  by_cases hki : k = i.castSucc
  · subst k
    simp [Fin.val_castSucc, i.castSucc_lt_succ.ne]
    field_simp [d.scale_pos i |>.ne']
    ring
  · by_cases hkn : k = i.succ
    · subst k
      simp [hki, Fin.val_castSucc]
      field_simp [d.scale_pos i |>.ne']
      ring
    · simp [hki, hkn]

theorem internal_inner_self {J : ℕ} (d : ChainData J) (i : Fin J) (a : ℝ) :
    inner ℝ (d.internalResidual i a) (d.stageGradient i.castSucc) =
      d.amplitude i ^ 2 / d.scale i ^ 2 *
        (d.scale i - a * (1 + d.kappa i ^ 2)) := by
  rw [internalResidual_eq, stageGradient_internal]
  simp only [inner_add_left, inner_sub_right,
    EuclideanSpace.inner_single_left]
  simp [i.castSucc_lt_succ.ne]
  field_simp [d.scale_pos i |>.ne']
  ring

theorem internal_inner_next {J : ℕ} (d : ChainData J) (i : Fin J) (a : ℝ) :
    inner ℝ (d.internalResidual i a) (d.stageGradient i.succ) =
      d.amplitude i ^ 2 * d.kappa i ^ 2 * a /
        (d.scale i * d.nextScale i) := by
  rw [internalResidual_eq]
  by_cases hi : i.val + 1 < J
  · let j : Fin J := ⟨i.val + 1, hi⟩
    have hjsucc : j.castSucc = i.succ := by apply Fin.ext; rfl
    rw [← hjsucc, stageGradient_internal]
    simp only [inner_add_left, inner_sub_right,
      EuclideanSpace.inner_single_left]
    have hne : i.castSucc ≠ j.castSucc := by
      intro h
      have hv := congrArg Fin.val h
      simp [j] at hv
    have hneNext : i.castSucc ≠ j.succ := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_castSucc, Fin.val_succ] at hv
      change i.val = (i.val + 1) + 1 at hv
      omega
    have hsame : i.succ = j.castSucc := hjsucc.symm
    simp [hne, hneNext, j.castSucc_lt_succ.ne]
    rw [amplitude_succ d i.isLt]
    have hnscale : d.nextScale i = d.scale j := by
      simp [nextScale, hi, j]
    rw [hnscale]
    field_simp [d.scale_pos i |>.ne', d.scale_pos j |>.ne']
  · have hisLast : i.succ = Fin.last J := by
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_last]
      omega
    rw [hisLast, stageGradient_terminal]
    simp only [inner_add_left, EuclideanSpace.inner_single_left]
    have hne : i.castSucc ≠ Fin.last J := (Fin.castSucc_lt_last i).ne
    simp [hne, nextScale, hi]
    have hival : i.val + 1 = J := congrArg Fin.val hisLast
    have hamp : d.amplitude J = d.kappa i * d.amplitude i := by
      calc
        d.amplitude J = d.amplitude (i.val + 1) := congrArg d.amplitude hival.symm
        _ = d.kappa i * d.amplitude i := amplitude_succ d i.isLt
    rw [hamp]
    field_simp [d.scale_pos i |>.ne', d.terminalScale_pos.ne']

theorem internal_inner_previous {J : ℕ} (d : ChainData J)
    (i r : Fin J) (a : ℝ) (hri : r.val + 1 = i.val) :
    inner ℝ (d.internalResidual i a) (d.stageGradient r.castSucc) =
      -(d.amplitude i ^ 2 * (d.scale i - a) /
        (d.scale r * d.scale i)) := by
  rw [internalResidual_eq, stageGradient_internal]
  simp only [inner_add_left, inner_sub_right,
    EuclideanSpace.inner_single_left]
  have hcoord : r.succ = i.castSucc := by apply Fin.ext; exact hri
  have hne0 : i.castSucc ≠ r.castSucc := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
    omega
  have hne1 : i.succ ≠ r.castSucc := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
    omega
  have hne2 : i.succ ≠ r.succ := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
    omega
  have hcoord' : i.castSucc = r.succ := hcoord.symm
  simp [hne1, hne2, hcoord',
    r.castSucc_lt_succ.ne]
  have hamp : d.amplitude i = d.kappa r * d.amplitude r := by
    have h := amplitude_succ d r.isLt
    rw [hri] at h
    exact h
  rw [hamp]
  field_simp [d.scale_pos i |>.ne', d.scale_pos r |>.ne']

theorem internal_inner_far {J : ℕ} (d : ChainData J)
    (i r : Fin J) (a : ℝ)
    (h0 : r.val ≠ i.val) (h1 : r.val ≠ i.val + 1)
    (h2 : r.val + 1 ≠ i.val) :
    inner ℝ (d.internalResidual i a) (d.stageGradient r.castSucc) = 0 := by
  rw [internalResidual_eq, stageGradient_internal]
  simp only [inner_add_left, inner_sub_right,
    EuclideanSpace.inner_single_left]
  have h00 : i.castSucc ≠ r.castSucc := by
    intro h; apply h0; exact (congrArg Fin.val h).symm
  have h01 : i.castSucc ≠ r.succ := by
    intro h; apply h2; exact (congrArg Fin.val h).symm
  have h10 : i.succ ≠ r.castSucc := by
    intro h; apply h1; exact (congrArg Fin.val h).symm
  have h11 : i.succ ≠ r.succ := by
    intro h
    apply h0
    have hv := congrArg Fin.val h
    simp only [Fin.val_succ] at hv
    omega
  simp [h00, h01, h10, h11]

theorem internal_inner_terminal_of_not_last {J : ℕ} (d : ChainData J)
    (i : Fin J) (a : ℝ) (hi : i.val + 1 < J) :
    inner ℝ (d.internalResidual i a) (d.stageGradient (Fin.last J)) = 0 := by
  rw [internalResidual_eq, stageGradient_terminal]
  simp only [inner_add_left, EuclideanSpace.inner_single_left]
  have h0 : i.castSucc ≠ Fin.last J := (Fin.castSucc_lt_last i).ne
  have h1 : i.succ ≠ Fin.last J := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
    omega
  simp [h0, h1]

/-- Scalar inequality at the heart of the nonterminal projection check. -/
theorem transition_dominance
    {omega delta next a : ℝ}
    (hω : 0 < omega) (hδ : 0 < delta) (hn : 0 < next)
    (ha1 : 1 ≤ a) (haω : a ≤ omega) :
    let scale := omega + delta
    let rho := delta * next / (omega * (scale + next))
    rho * a / (scale * next) ≤
      (scale - a * (1 + rho)) / scale ^ 2 := by
  dsimp only
  have hs : 0 < omega + delta := add_pos hω hδ
  have hsn : 0 < omega + delta + next := add_pos hs hn
  have hden : 0 < omega * (omega + delta + next) := mul_pos hω hsn
  let rho := delta * next / (omega * (omega + delta + next))
  have hrho : 0 < rho := div_pos (mul_pos hδ hn) hden
  have hcoreEq :
      rho * a * (omega + delta + next) = delta * next * a / omega := by
    dsimp [rho]
    field_simp [hω.ne', hsn.ne']
  have hcore :
      rho * a * (omega + delta + next) ≤
        next * (omega + delta - a) := by
    rw [hcoreEq]
    apply (div_le_iff₀ hω).2
    calc
      delta * next * a ≤ delta * next * omega :=
        mul_le_mul_of_nonneg_left haω (mul_nonneg hδ.le hn.le)
      _ = (next * delta) * omega := by ring
      _ ≤ (next * (omega + delta - a)) * omega := by
        apply mul_le_mul_of_nonneg_right _ hω.le
        exact mul_le_mul_of_nonneg_left (by linarith) hn.le
      _ = next * (omega + delta - a) * omega := by ring
  apply (div_le_div_iff₀ (mul_pos hs hn) (sq_pos_of_pos hs)).2
  change rho * a * (omega + delta) ^ 2 ≤
    (omega + delta - a * (1 + rho)) * ((omega + delta) * next)
  nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hcore)]

theorem internal_next_le_self {J : ℕ} (d : ChainData J) (i : Fin J) (a : ℝ)
    (ha1 : 1 ≤ a) (haω : a ≤ d.omega i) :
    inner ℝ (d.internalResidual i a) (d.stageGradient i.succ) ≤
      inner ℝ (d.internalResidual i a) (d.stageGradient i.castSucc) := by
  rw [internal_inner_next, internal_inner_self, kappa_sq]
  have hdom := transition_dominance (d.omega_pos i) (d.delta_pos i)
    (d.nextScale_pos i) ha1 haω
  simp only [scale, rho] at hdom ⊢
  have hmul := mul_le_mul_of_nonneg_left hdom (sq_nonneg (d.amplitude i))
  simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul

theorem internal_self_nonneg {J : ℕ} (d : ChainData J) (i : Fin J) (a : ℝ)
    (ha1 : 1 ≤ a) (haω : a ≤ d.omega i) :
    0 ≤ inner ℝ (d.internalResidual i a) (d.stageGradient i.castSucc) := by
  have hnextPos :
      0 ≤ inner ℝ (d.internalResidual i a) (d.stageGradient i.succ) := by
    rw [internal_inner_next]
    positivity [d.amplitude_pos i, d.kappa_pos i, d.scale_pos i,
      d.nextScale_pos i]
  exact hnextPos.trans (internal_next_le_self d i a ha1 haω)

/-- The intended gradient is the polytope projection throughout an internal
gap, including the query just before its selected long step. -/
theorem internalProjection {J : ℕ} (d : ChainData J) (i : Fin J) (τ : ℝ)
    (hτ0 : 0 ≤ τ) (hτ : τ ≤ d.omega i - 1) :
    finiteProjection d.markedVertex (d.internalPath i τ) =
      d.stageGradient i.castSucc := by
  let a := τ + 1
  have ha1 : 1 ≤ a := by dsimp [a]; linarith
  have haω : a ≤ d.omega i := by dsimp [a]; linarith
  have hres :
      d.internalPath i τ - d.stageGradient i.castSucc =
        d.internalResidual i a := by
    unfold internalResidual
    congr 2
    dsimp [a]
    ring
  apply finiteProjection_eq_of_vertex_max
  · exact ⟨some i.castSucc, rfl⟩
  · intro vertex
    change inner ℝ
      (d.internalPath i τ - d.stageGradient i.castSucc)
        (d.markedVertex vertex) ≤
      inner ℝ (d.internalPath i τ - d.stageGradient i.castSucc)
        (d.stageGradient i.castSucc)
    rw [hres]
    cases vertex with
    | none =>
        simp only [markedVertex, inner_zero_right]
        exact internal_self_nonneg d i a ha1 haω
    | some j =>
        simp only [markedVertex]
        by_cases hself : j = i.castSucc
        · subst j
          exact le_rfl
        by_cases hnext : j = i.succ
        · subst j
          exact internal_next_le_self d i a ha1 haω
        by_cases hj : j.val < J
        · let r : Fin J := ⟨j.val, hj⟩
          have hrj : r.castSucc = j := by apply Fin.ext; rfl
          rw [← hrj]
          have hr0 : r.val ≠ i.val := by
            intro h
            apply hself
            apply Fin.ext
            exact h
          have hr1 : r.val ≠ i.val + 1 := by
            intro h
            apply hnext
            apply Fin.ext
            exact h
          by_cases hr2 : r.val + 1 = i.val
          · rw [internal_inner_previous d i r a hr2]
            have hnumer : 0 ≤
                d.amplitude i ^ 2 * (d.scale i - a) := by
              apply mul_nonneg (sq_nonneg _)
              unfold scale
              linarith [d.delta_pos i]
            have hden : 0 ≤ d.scale r * d.scale i :=
              mul_nonneg (d.scale_pos r).le (d.scale_pos i).le
            have hquot : 0 ≤
                d.amplitude i ^ 2 * (d.scale i - a) /
                  (d.scale r * d.scale i) := div_nonneg hnumer hden
            exact (neg_nonpos.mpr hquot).trans
              (internal_self_nonneg d i a ha1 haω)
          · rw [internal_inner_far d i r a hr0 hr1 hr2]
            exact internal_self_nonneg d i a ha1 haω
        · have hjLast : j = Fin.last J := by
            apply Fin.ext
            simp only [Fin.val_last]
            omega
          subst j
          have hiNext : i.val + 1 < J := by
            by_contra h
            apply hnext
            apply Fin.ext
            simp only [Fin.val_last, Fin.val_succ]
            omega
          rw [internal_inner_terminal_of_not_last d i a hiNext]
          exact internal_self_nonneg d i a ha1 haω

theorem terminalResidual_eq {J : ℕ} (d : ChainData J) (τ : ℝ) :
    d.terminalPath τ - d.stageGradient (Fin.last J) =
      EuclideanSpace.single (Fin.last J)
        (d.amplitude J * (d.terminalScale - τ - 1) / d.terminalScale) := by
  rw [terminalPath, stageGradient_terminal]
  unfold stagePoint
  ext k
  by_cases hk : k = Fin.last J
  · subst k
    simp
    field_simp [d.terminalScale_pos.ne']
  · simp [hk]

theorem terminal_inner_self {J : ℕ} (d : ChainData J) (τ : ℝ) :
    inner ℝ (d.terminalPath τ - d.stageGradient (Fin.last J))
        (d.stageGradient (Fin.last J)) =
      d.amplitude J ^ 2 * (d.terminalScale - τ - 1) /
        d.terminalScale ^ 2 := by
  rw [terminalResidual_eq, stageGradient_terminal]
  simp only [EuclideanSpace.inner_single_left]
  simp
  field_simp [d.terminalScale_pos.ne']

/-- The terminal gradient remains the projection throughout the last gap. -/
theorem terminalProjection {J : ℕ} (d : ChainData J) (τ : ℝ)
    (_hτ0 : 0 ≤ τ) (hτ : τ ≤ d.terminalGap) :
    finiteProjection d.markedVertex (d.terminalPath τ) =
      d.stageGradient (Fin.last J) := by
  have hcoef : 0 ≤ d.terminalScale - τ - 1 := by
    unfold terminalScale
    linarith [d.terminalGap_nonneg]
  have hself : 0 ≤
      inner ℝ (d.terminalPath τ - d.stageGradient (Fin.last J))
        (d.stageGradient (Fin.last J)) := by
    rw [terminal_inner_self]
    positivity [d.amplitude_pos J, d.terminalScale_pos]
  have hselfFormula : 0 ≤
      d.amplitude J ^ 2 * (d.terminalScale - τ - 1) /
        d.terminalScale ^ 2 := by
    rwa [← terminal_inner_self]
  apply finiteProjection_eq_of_vertex_max
  · exact ⟨some (Fin.last J), rfl⟩
  · intro vertex
    cases vertex with
    | none =>
        simp only [markedVertex, inner_zero_right]
        exact hself
    | some j =>
        simp only [markedVertex]
        by_cases hj : j = Fin.last J
        · subst j
          exact le_rfl
        have hjlt : j.val < J := by
          have hjne : j.val ≠ J := by
            intro hval
            apply hj
            apply Fin.ext
            simpa using hval
          omega
        let r : Fin J := ⟨j.val, hjlt⟩
        have hrj : r.castSucc = j := by apply Fin.ext; rfl
        rw [← hrj, terminal_inner_self, terminalResidual_eq,
          stageGradient_internal]
        simp only [inner_sub_right, EuclideanSpace.inner_single_left]
        have hlast0 : Fin.last J ≠ r.castSucc :=
          (Fin.castSucc_lt_last r).ne'
        by_cases hlast1 : Fin.last J = r.succ
        · simp [hlast1, r.castSucc_lt_succ.ne]
          have hnonneg : 0 ≤
              d.amplitude J * (d.terminalScale - τ - 1) /
                d.terminalScale :=
            div_nonneg (mul_nonneg (d.amplitude_pos J).le hcoef)
              d.terminalScale_pos.le
          have hgrad : 0 ≤
              d.amplitude r * d.kappa r / d.scale r :=
            div_nonneg
              (mul_nonneg (d.amplitude_pos r).le (d.kappa_pos r).le)
              (d.scale_pos r).le
          exact (neg_nonpos.mpr (mul_nonneg hnonneg hgrad)).trans hselfFormula
        · simp [hlast0, hlast1]
          exact hselfFormula

theorem internalPath_add_step {J : ℕ} (d : ChainData J)
    (i : Fin J) (s τ : ℝ) :
    d.internalPath i τ - s • d.stageGradient i.castSucc =
      d.internalPath i (τ + s) := by
  unfold internalPath
  rw [add_smul]
  abel

theorem terminalPath_add_step {J : ℕ} (d : ChainData J) (s τ : ℝ) :
    d.terminalPath τ - s • d.stageGradient (Fin.last J) =
      d.terminalPath (τ + s) := by
  unfold terminalPath
  rw [add_smul]
  abel

/-- A complete internal gap followed by its selected long step reaches the
next orthogonal stage point exactly. -/
theorem selectedTransition {J : ℕ} (d : ChainData J) (i : Fin J) :
    d.internalPath i (d.omega i - 1) -
        (1 + d.delta i) • d.stageGradient i.castSucc =
      d.stagePoint i.succ := by
  rw [internalPath_add_step]
  have hsum : d.omega i - 1 + (1 + d.delta i) = d.scale i := by
    unfold scale
    ring
  rw [hsum]
  unfold internalPath stagePoint
  rw [stageGradient_internal]
  simp only [Fin.val_castSucc, Fin.val_succ]
  rw [amplitude_succ d i.isLt]
  ext k
  by_cases hki : k = i.castSucc
  · subst k
    simp [i.castSucc_lt_succ.ne]
    field_simp [d.scale_pos i |>.ne']
    ring
  · by_cases hkn : k = i.succ
    · subst k
      simp [hki]
      field_simp [d.scale_pos i |>.ne']
    · simp [hki, hkn]

theorem stagePoint_zero_norm {J : ℕ} (d : ChainData J) :
    ‖d.stagePoint 0‖ = 1 := by
  simp [stagePoint]

theorem amplitude_sq {J : ℕ} (d : ChainData J) :
    d.amplitude J ^ 2 = ∏ i, d.rho i := by
  rw [amplitude, stageAmplitude_sq, prod_rhoNat]
  apply Finset.prod_congr rfl
  intro i hi
  have hiJ : i < J := Finset.mem_range.mp hi
  rw [rhoNat_of_lt d hiJ]
  exact Real.sq_sqrt (d.rho_pos ⟨i, hiJ⟩).le

/-- The exact objective gap at the end of the terminal block. -/
theorem finalEnvelopeGap {J : ℕ} (d : ChainData J) :
    d.markedEnvelope (d.terminalPath d.terminalGap) - d.markedEnvelope 0 =
      d.contribution / 2 := by
  have hproj := d.terminalProjection d.terminalGap d.terminalGap_nonneg le_rfl
  have hzero := d.markedEnvelope_minimized_at_zero
  rw [hzero.1]
  unfold markedEnvelope finiteEnvelope
  rw [hproj]
  unfold envelopeScore terminalPath stagePoint
  rw [stageGradient_terminal]
  simp only [EuclideanSpace.inner_single_left]
  simp [PiLp.norm_single]
  rw [abs_of_pos (d.amplitude_pos J), abs_of_pos d.terminalScale_pos]
  change terminalEnvelopeGap (d.amplitude J) d.terminalGap = d.contribution / 2
  rw [terminalEnvelopeGap_eq d.terminalGap_nonneg, amplitude_sq]
  unfold contribution
  unfold ChainData.terminalScale GD.Sqrt3LowerBound.terminalScale
  have ht : 1 + 2 * d.terminalGap ≠ 0 := by
    linarith [d.terminalGap_nonneg]
  field_simp [ht]

end ChainData

end GD.Sqrt3LowerBound
