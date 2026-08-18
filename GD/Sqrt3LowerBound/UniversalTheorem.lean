import GD.Sqrt3LowerBound.ScheduleTrajectory

/-!
# Universal predetermined-stepsize lower bound

This file closes the witness bridges: it turns the scalar schedule certificate
into a concrete normalized GD trajectory, then performs the exact translation
and physical scaling needed for arbitrary `L`, `R`, and prescribed initial
point.
-/

namespace GD.Sqrt3LowerBound

open scoped Gradient

/-- Every nonnegative normalized schedule has a concrete hard GD instance. -/
theorem normalizedScheduleInstance {T : ℕ} {α : Fin T → ℝ}
    (hα : ∀ t, 0 ≤ α t) :
    ∃ I : NormalizedGDInstance T α,
      lowerBoundConstant * ((T + 1 : ℕ) : ℝ) ^ (-criticalExponent) ≤
        I.final_gap := by
  obtain ⟨c, hc, hbound⟩ := scheduleHorizonContribution hα
  let I := chainNormalizedInstance α hα c hc
  refine ⟨I, ?_⟩
  have hbasePos : 0 < ((T + 1 : ℕ) : ℝ) ^ criticalExponent :=
    Real.rpow_pos_of_pos (by positivity) _
  have hhalf :
      (scheduleConstant / ((T + 1 : ℕ) : ℝ) ^ criticalExponent) / 2 ≤
        (scheduleChainData α hα c hc).contribution / 2 := by
    gcongr
  change lowerBoundConstant * ((T + 1 : ℕ) : ℝ) ^ (-criticalExponent) ≤
    (scheduleChainData α hα c hc).contribution / 2
  calc
    lowerBoundConstant * ((T + 1 : ℕ) : ℝ) ^ (-criticalExponent) =
        (scheduleConstant / ((T + 1 : ℕ) : ℝ) ^ criticalExponent) / 2 := by
      unfold lowerBoundConstant
      rw [Real.rpow_neg (by positivity)]
      field_simp [hbasePos.ne']
    _ ≤ (scheduleChainData α hα c hc).contribution / 2 := hhalf

noncomputable def normalizedCoordinate {d : ℕ} (R : ℝ)
    (xStar : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
  R⁻¹ • fun y ↦ y - xStar

noncomputable def physicalObjective {T : ℕ} {α : Fin T → ℝ}
    (I : NormalizedGDInstance T α) (L R : ℝ)
    (xStar : EuclideanSpace ℝ (Fin I.dim)) :
    EuclideanSpace ℝ (Fin I.dim) → ℝ :=
  (L * R ^ 2) • (I.f ∘ normalizedCoordinate R xStar)

noncomputable def physicalGradient {T : ℕ} {α : Fin T → ℝ}
    (I : NormalizedGDInstance T α) (L R : ℝ)
    (xStar : EuclideanSpace ℝ (Fin I.dim)) :
    EuclideanSpace ℝ (Fin I.dim) → EuclideanSpace ℝ (Fin I.dim) :=
  (L * R) • (∇ I.f ∘ normalizedCoordinate R xStar)

theorem physicalObjective_hasGradient {T : ℕ} {α : Fin T → ℝ}
    (I : NormalizedGDInstance T α) (L R : ℝ) (hR : R ≠ 0)
    (xStar y : EuclideanSpace ℝ (Fin I.dim)) :
    HasGradientAt
      (physicalObjective I L R xStar)
      (physicalGradient I L R xStar y) y := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hsub : HasFDerivAt (fun z ↦ z - xStar)
      (ContinuousLinearMap.id ℝ _) y :=
    (hasFDerivAt_id y).sub_const xStar
  have hcoord : HasFDerivAt (normalizedCoordinate R xStar)
      (R⁻¹ • ContinuousLinearMap.id ℝ _) y := by
    exact hsub.const_smul R⁻¹
  have hcomp := (I.hasGradient (normalizedCoordinate R xStar y)).hasFDerivAt.comp y hcoord
  have hout := hcomp.const_smul (L * R ^ 2)
  unfold physicalObjective physicalGradient
  apply hout.congr_fderiv
  ext z
  simp
  field_simp [hR]

theorem physicalObjective_convex {T : ℕ} {α : Fin T → ℝ}
    (I : NormalizedGDInstance T α) (L R : ℝ) (hL : 0 ≤ L)
    (xStar : EuclideanSpace ℝ (Fin I.dim)) :
    ConvexOn ℝ Set.univ (physicalObjective I L R xStar) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hbase := I.convex.2
    (show normalizedCoordinate R xStar x ∈ Set.univ by simp)
    (show normalizedCoordinate R xStar y ∈ Set.univ by simp)
    ha hb hab
  have hscale := mul_le_mul_of_nonneg_left hbase
    (mul_nonneg hL (sq_nonneg R))
  simp only [normalizedCoordinate, Pi.smul_apply] at hscale
  unfold physicalObjective normalizedCoordinate
  dsimp only [Function.comp_apply, Pi.smul_apply]
  rw [show R⁻¹ • (a • x + b • y - xStar) =
      a • (R⁻¹ • (x - xStar)) + b • (R⁻¹ • (y - xStar)) by
    calc
      R⁻¹ • (a • x + b • y - xStar) =
          R⁻¹ • (a • x + b • y - (a + b) • xStar) := by
            rw [hab, one_smul]
      _ = a • (R⁻¹ • (x - xStar)) + b • (R⁻¹ • (y - xStar)) := by
            module]
  convert hscale using 1 <;> ring

theorem physicalGradient_lipschitz {T : ℕ} {α : Fin T → ℝ}
    (I : NormalizedGDInstance T α) (L R : ℝ)
    (hL : 0 < L) (hR : 0 < R)
    (xStar x y : EuclideanSpace ℝ (Fin I.dim)) :
    ‖physicalGradient I L R xStar x - physicalGradient I L R xStar y‖ ≤
      L * ‖x - y‖ := by
  have hbase := I.oneSmooth.dist_le_mul
    (normalizedCoordinate R xStar x) (normalizedCoordinate R xStar y)
  simp only [NNReal.coe_one, one_mul, dist_eq_norm] at hbase
  have hcoord :
      normalizedCoordinate R xStar x - normalizedCoordinate R xStar y =
        R⁻¹ • (x - y) := by
    unfold normalizedCoordinate
    dsimp only [Pi.smul_apply]
    module
  have hcoordNorm :
      ‖normalizedCoordinate R xStar x - normalizedCoordinate R xStar y‖ =
        R⁻¹ * ‖x - y‖ := by
    rw [hcoord, norm_smul]
    simp [abs_of_pos hR]
  have hgrad :
      physicalGradient I L R xStar x - physicalGradient I L R xStar y =
        (L * R) •
          (∇ I.f (normalizedCoordinate R xStar x) -
            ∇ I.f (normalizedCoordinate R xStar y)) := by
    unfold physicalGradient
    dsimp only [Pi.smul_apply, Function.comp_apply]
    module
  rw [hgrad, norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos hL hR)]
  calc
    L * R *
        ‖∇ I.f (normalizedCoordinate R xStar x) -
          ∇ I.f (normalizedCoordinate R xStar y)‖ ≤
      L * R *
        ‖normalizedCoordinate R xStar x - normalizedCoordinate R xStar y‖ := by
          gcongr
    _ = L * ‖x - y‖ := by
      rw [hcoordNorm]
      field_simp [hR.ne']

theorem physicalObjective_gradient {T : ℕ} {α : Fin T → ℝ}
    (I : NormalizedGDInstance T α) (L R : ℝ) (hR : R ≠ 0)
    (xStar : EuclideanSpace ℝ (Fin I.dim)) :
    ∇ (physicalObjective I L R xStar) = physicalGradient I L R xStar :=
  gradient_eq fun y ↦ physicalObjective_hasGradient I L R hR xStar y

theorem physicalObjective_minimized {T : ℕ} {α : Fin T → ℝ}
    (I : NormalizedGDInstance T α) (L R : ℝ) (hL : 0 ≤ L)
    (xStar : EuclideanSpace ℝ (Fin I.dim)) :
    physicalObjective I L R xStar xStar = 0 ∧
      ∀ y, physicalObjective I L R xStar xStar ≤
        physicalObjective I L R xStar y := by
  have hscale : 0 ≤ L * R ^ 2 := mul_nonneg hL (sq_nonneg R)
  constructor
  · unfold physicalObjective normalizedCoordinate
    simp [I.zero_minimizer.1]
  · intro y
    unfold physicalObjective normalizedCoordinate
    dsimp only [Function.comp_apply, Pi.smul_apply]
    have hmin := I.zero_minimizer.2 (R⁻¹ • (y - xStar))
    simpa [I.zero_minimizer.1] using mul_le_mul_of_nonneg_left hmin hscale

noncomputable def physicalTrajectory {T : ℕ} {α : Fin T → ℝ}
    (I : NormalizedGDInstance T α) (R : ℝ)
    (xStar : EuclideanSpace ℝ (Fin I.dim)) :
    Fin (T + 1) → EuclideanSpace ℝ (Fin I.dim) :=
  fun n ↦ xStar + R • I.x n

theorem normalizedCoordinate_physicalTrajectory {T : ℕ}
    {α : Fin T → ℝ} (I : NormalizedGDInstance T α)
    (R : ℝ) (hR : R ≠ 0) (xStar : EuclideanSpace ℝ (Fin I.dim))
    (n : Fin (T + 1)) :
    normalizedCoordinate R xStar (physicalTrajectory I R xStar n) = I.x n := by
  unfold normalizedCoordinate physicalTrajectory
  dsimp only [Pi.smul_apply]
  rw [add_sub_cancel_left]
  simp [smul_smul, hR]

theorem physicalTrajectory_step {T : ℕ} {α η : Fin T → ℝ}
    (I : NormalizedGDInstance T α) (L R : ℝ) (hR : R ≠ 0)
    (hαη : ∀ t, α t = L * η t)
    (xStar : EuclideanSpace ℝ (Fin I.dim)) (t : Fin T) :
    physicalTrajectory I R xStar t.succ =
      physicalTrajectory I R xStar t.castSucc - η t •
        physicalGradient I L R xStar
          (physicalTrajectory I R xStar t.castSucc) := by
  unfold physicalGradient
  dsimp only [Pi.smul_apply, Function.comp_apply]
  rw [normalizedCoordinate_physicalTrajectory I R hR xStar]
  unfold physicalTrajectory
  rw [I.gd_step t, hαη t]
  module

/-- The full physical witness appearing in the universal theorem. -/
structure PhysicalGDInstance (T : ℕ) (η : Fin T → ℝ) (L R : ℝ) (d : ℕ)
    (xInit : EuclideanSpace ℝ (Fin d)) where
  f : EuclideanSpace ℝ (Fin d) → ℝ
  xStar : EuclideanSpace ℝ (Fin d)
  x : Fin (T + 1) → EuclideanSpace ℝ (Fin d)
  convex : ConvexOn ℝ Set.univ f
  hasGradient : ∀ y, HasGradientAt f (∇ f y) y
  L_smooth : ∀ y z, ‖∇ f y - ∇ f z‖ ≤ L * ‖y - z‖
  zero_minimizer : f xStar = 0 ∧ ∀ y, f xStar ≤ f y
  initial_point : x 0 = xInit
  initial_distance : ‖xInit - xStar‖ = R
  gd_step : ∀ t : Fin T,
    x t.succ = x t.castSucc - η t • ∇ f (x t.castSucc)
  final_gap : ℝ
  final_gap_eq : f (x (Fin.last T)) - f xStar = final_gap

/-- Translate and scale a normalized instance around an arbitrary initial point. -/
noncomputable def physicalize {T : ℕ} {α η : Fin T → ℝ}
    (I : NormalizedGDInstance T α) (L R : ℝ)
    (hL : 0 < L) (hR : 0 < R) (hαη : ∀ t, α t = L * η t)
    (xInit : EuclideanSpace ℝ (Fin I.dim)) :
    PhysicalGDInstance T η L R I.dim xInit := by
  let xStar : EuclideanSpace ℝ (Fin I.dim) := xInit - R • I.x 0
  let f := physicalObjective I L R xStar
  let path := physicalTrajectory I R xStar
  have hRne : R ≠ 0 := hR.ne'
  have hgrad : ∇ f = physicalGradient I L R xStar := by
    exact physicalObjective_gradient I L R hRne xStar
  refine
    { f := f
      xStar := xStar
      x := path
      convex := physicalObjective_convex I L R hL.le xStar
      hasGradient := ?_
      L_smooth := ?_
      zero_minimizer := physicalObjective_minimized I L R hL.le xStar
      initial_point := ?_
      initial_distance := ?_
      gd_step := ?_
      final_gap := L * R ^ 2 * I.final_gap
      final_gap_eq := ?_ }
  · intro y
    exact (physicalObjective_hasGradient I L R hRne xStar y).differentiableAt.hasGradientAt
  · intro y z
    rw [hgrad]
    exact physicalGradient_lipschitz I L R hL hR xStar y z
  · dsimp [path, physicalTrajectory, xStar]
    module
  · dsimp [xStar]
    rw [show xInit - (xInit - R • I.x 0) = R • I.x 0 by module,
      norm_smul, I.initial_norm]
    simp [abs_of_pos hR]
  · intro t
    dsimp [path]
    rw [hgrad]
    exact physicalTrajectory_step I L R hRne hαη xStar t
  · dsimp [f, path]
    have hxStar : normalizedCoordinate R xStar xStar = 0 := by
      unfold normalizedCoordinate
      simp
    unfold physicalObjective
    dsimp only [Pi.smul_apply, Function.comp_apply]
    rw [normalizedCoordinate_physicalTrajectory I R hRne xStar]
    rw [hxStar]
    change L * R ^ 2 * I.f (I.x (Fin.last T)) -
      L * R ^ 2 * I.f 0 = L * R ^ 2 * I.final_gap
    rw [← mul_sub, I.final_gap_eq]

/-- The report's universal `sqrt 3` lower bound with all witness quantifiers. -/
theorem universalSqrtThreeLowerBound
    (T : ℕ) (_hT : 1 ≤ T) (L R : ℝ) (hL : 0 < L) (hR : 0 < R)
    (η : Fin T → ℝ) (hη : ∀ t, 0 ≤ η t) :
    ∃ d : ℕ, d ≤ T + 1 ∧
      ∀ xInit : EuclideanSpace ℝ (Fin d),
        ∃ W : PhysicalGDInstance T η L R d xInit,
          lowerBoundConstant * L * R ^ 2 *
              ((T + 1 : ℕ) : ℝ) ^ (-criticalExponent) ≤
            W.f (W.x (Fin.last T)) - W.f W.xStar := by
  let α : Fin T → ℝ := fun t ↦ L * η t
  have hα : ∀ t, 0 ≤ α t := fun t ↦ mul_nonneg hL.le (hη t)
  obtain ⟨I, hgap⟩ := normalizedScheduleInstance hα
  refine ⟨I.dim, I.dim_le, ?_⟩
  intro xInit
  let W := physicalize I L R hL hR (fun _ ↦ rfl) xInit
  refine ⟨W, ?_⟩
  rw [W.final_gap_eq]
  change lowerBoundConstant * L * R ^ 2 *
      ((T + 1 : ℕ) : ℝ) ^ (-criticalExponent) ≤
    L * R ^ 2 * I.final_gap
  have hscaled := mul_le_mul_of_nonneg_left hgap
    (mul_nonneg hL.le (sq_nonneg R))
  calc
    lowerBoundConstant * L * R ^ 2 *
        ((T + 1 : ℕ) : ℝ) ^ (-criticalExponent) =
      L * R ^ 2 *
        (lowerBoundConstant *
          ((T + 1 : ℕ) : ℝ) ^ (-criticalExponent)) := by ring
    _ ≤ L * R ^ 2 * I.final_gap := hscaled

end GD.Sqrt3LowerBound
