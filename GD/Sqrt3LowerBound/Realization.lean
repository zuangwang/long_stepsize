import GD.Sqrt3LowerBound.Certificate

/-!
# Marked-stage realization algebra

This file formalizes the exact amplitude and terminal-value calculations in
Proposition 3.1.  The report's geometric construction chooses orthogonal
coordinates with amplitudes `σ (i+1) = κ i * σ i`; the final Moreau-envelope
value then depends only on these amplitudes and the terminal scale.
-/

namespace GD.Sqrt3LowerBound

open scoped BigOperators

/-- Amplitude of the marked orthogonal coordinate after `n` transitions. -/
noncomputable def stageAmplitude (κ : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => κ n * stageAmplitude κ n

theorem stageAmplitude_sq (κ : ℕ → ℝ) (n : ℕ) :
    stageAmplitude κ n ^ 2 =
      ∏ i ∈ Finset.range n, κ i ^ 2 := by
  induction n with
  | zero => simp [stageAmplitude]
  | succ n ih =>
      rw [stageAmplitude, Finset.prod_range_succ, mul_pow, ih]
      ring

/-- Terminal scale `Ω_J = 1 + 2 τ_end`. -/
noncomputable def terminalScale (τEnd : ℝ) : ℝ := 1 + 2 * τEnd

theorem terminalScale_pos {τEnd : ℝ} (hτ : 0 ≤ τEnd) :
    0 < terminalScale τEnd := by
  unfold terminalScale
  linarith

/-- Last coordinate after the terminal gap steps. -/
noncomputable def terminalCoordinate (σ τEnd : ℝ) : ℝ :=
  σ - τEnd * (σ / terminalScale τEnd)

/-- Last projected gradient coordinate. -/
noncomputable def terminalGradientCoordinate (σ τEnd : ℝ) : ℝ :=
  σ / terminalScale τEnd

/-- The direct envelope value `<p,x> - ‖p‖²/2` in the final coordinate. -/
noncomputable def terminalEnvelopeGap (σ τEnd : ℝ) : ℝ :=
  terminalGradientCoordinate σ τEnd * terminalCoordinate σ τEnd -
    terminalGradientCoordinate σ τEnd ^ 2 / 2

/-- Exact terminal calculation in equation (3.10). -/
theorem terminalEnvelopeGap_eq {σ τEnd : ℝ} (hτ : 0 ≤ τEnd) :
    terminalEnvelopeGap σ τEnd = σ ^ 2 / (2 * terminalScale τEnd) := by
  have hΩ := terminalScale_pos hτ
  unfold terminalEnvelopeGap terminalGradientCoordinate terminalCoordinate
  field_simp [hΩ.ne']
  unfold terminalScale
  ring

/-- Proposition 3.1's realized-gap formula, after the geometric projection
checks have identified the intended constant gradients on every block. -/
theorem markedStageRealizedGapAlgebra
    (κ : ℕ → ℝ) (J : ℕ) (τEnd : ℝ) (hτ : 0 ≤ τEnd) :
    terminalEnvelopeGap (stageAmplitude κ J) τEnd =
      1 / (2 * terminalScale τEnd) *
        ∏ i ∈ Finset.range J, κ i ^ 2 := by
  rw [terminalEnvelopeGap_eq hτ, stageAmplitude_sq]
  ring

/-- Choosing `κ_i = sqrt ρ_i` converts the realized gap into one half of
the scalar chain contribution, as in equation (3.12). -/
theorem markedStageRealizedGap_of_rho
    (ρ : ℕ → ℝ) (J : ℕ) (τEnd : ℝ)
    (hρ : ∀ i < J, 0 ≤ ρ i) (hτ : 0 ≤ τEnd) :
    terminalEnvelopeGap
        (stageAmplitude (fun i ↦ Real.sqrt (ρ i)) J) τEnd =
      (1 / terminalScale τEnd *
        ∏ i ∈ Finset.range J, ρ i) / 2 := by
  rw [markedStageRealizedGapAlgebra _ J τEnd hτ]
  have hprod :
      (∏ i ∈ Finset.range J, Real.sqrt (ρ i) ^ 2) =
        ∏ i ∈ Finset.range J, ρ i := by
    apply Finset.prod_congr rfl
    intro i hi
    exact Real.sq_sqrt (hρ i (Finset.mem_range.mp hi))
  rw [hprod]
  ring

/-- Dimension count for a chain with at most `N` marked transitions. -/
theorem markedStage_dimension_bound {J N T : ℕ}
    (hJN : J ≤ N) (hNT : N + 1 ≤ T + 1) :
    J + 1 ≤ T + 1 := by omega

/-- End-to-end composition of the scalar certificate, horizon reduction,
realized normalized gap, and physical scaling.  The certificate hypotheses
are precisely the two branches proved by the temporal-product and
finite-prefix arguments. -/
theorem sqrtThreeLowerBound_from_certificate
    (T N : ℕ) (cap certificate normalizedGap physicalGap L R : ℝ)
    (δ : ℕ → ℝ)
    (hcap : 0 < cap)
    (hδpos : ∀ i < N, 0 < δ i)
    (hδsorted : Antitone δ)
    (hlowDensity : ∀ q, 3 ≤ q → q ≤ N →
      rankDensity N cap δ q ≤ densityThreshold →
        1 / (5 * rankMass N cap δ q) ≤ certificate)
    (hfinite : ∀ q, q ≤ min 3 N →
      finiteCutoffConstant / rankMass N cap δ q ≤ certificate)
    (hcapT : cap ≤ T + 1) (hNT : N + 1 ≤ T + 1)
    (hrealized : certificate / 2 ≤ normalizedGap)
    (hL : 0 < L) (hR : 0 < R)
    (hphysical : physicalGap = L * R ^ 2 * normalizedGap) :
    lowerBoundConstant * L * R ^ 2 *
      ((T + 1 : ℕ) : ℝ) ^ (-criticalExponent) ≤ physicalGap := by
  have hscan := completeCutoffScan N cap certificate δ hcap hδpos
    hδsorted hlowDensity hfinite
  have hhorizon := normalizedHorizonBound T N cap certificate hcap
    hcapT hNT hscan
  have hbasePos : 0 < ((T + 1 : ℕ) : ℝ) ^ criticalExponent :=
    Real.rpow_pos_of_pos (by positivity) _
  have hnormalized :
      scheduleConstant / 2 *
          ((T + 1 : ℕ) : ℝ) ^ (-criticalExponent) ≤ normalizedGap := by
    calc
      scheduleConstant / 2 *
          ((T + 1 : ℕ) : ℝ) ^ (-criticalExponent) =
        (scheduleConstant /
          ((T + 1 : ℕ) : ℝ) ^ criticalExponent) / 2 := by
            rw [Real.rpow_neg (by positivity)]
            field_simp [hbasePos.ne']
      _ ≤ certificate / 2 := by gcongr
      _ ≤ normalizedGap := hrealized
  exact physicalScalingBound T L R normalizedGap physicalGap hL hR
    hphysical hnormalized

end GD.Sqrt3LowerBound
