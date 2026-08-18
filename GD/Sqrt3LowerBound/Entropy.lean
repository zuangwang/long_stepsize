import Mathlib

/-!
# Entropy estimates for the `√3` gradient-descent lower bound

This file formalizes Section 4 of `results/sqrt3_lower_bound_report.tex`.
The central statement is `twoState_blockScale`, the two-state block-scale
inequality used to control the full temporally ordered reciprocal product.
-/

namespace GD.Sqrt3LowerBound

/-- The nonnegative entropy `t - 1 - log t` used in the report. -/
noncomputable def ent (t : ℝ) : ℝ := t - 1 - Real.log t

theorem ent_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ ent t := by
  unfold ent
  linarith [Real.log_le_sub_one_of_pos ht]

/-- The elementary maximum `m * exp (1-m) ≤ 1` on the positive reals. -/
theorem mul_exp_one_sub_le_one {m : ℝ} (hm : 0 < m) :
    m * Real.exp (1 - m) ≤ 1 := by
  have hlog : Real.log m ≤ m - 1 := Real.log_le_sub_one_of_pos hm
  have hexp : Real.exp (Real.log m) ≤ Real.exp (m - 1) :=
    Real.exp_le_exp.mpr hlog
  have hmle : m ≤ Real.exp (m - 1) := by
    simpa [Real.exp_log hm] using hexp
  calc
    m * Real.exp (1 - m) ≤ Real.exp (m - 1) * Real.exp (1 - m) := by
      gcongr
    _ = 1 := by
      rw [← Real.exp_add]
      norm_num

private theorem exp_half_log_add_eq_sqrt_mul {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    Real.exp ((Real.log a + Real.log c) / 2) = Real.sqrt (a * c) := by
  have hsq_exp : Real.exp ((Real.log a + Real.log c) / 2) ^ 2 = a * c := by
    calc
      Real.exp ((Real.log a + Real.log c) / 2) ^ 2 =
          Real.exp ((Real.log a + Real.log c) / 2 +
            (Real.log a + Real.log c) / 2) := by
              rw [pow_two, ← Real.exp_add]
      _ = Real.exp (Real.log a + Real.log c) := by ring_nf
      _ = Real.exp (Real.log a) * Real.exp (Real.log c) := Real.exp_add _ _
      _ = a * c := by rw [Real.exp_log ha, Real.exp_log hc]
  have hsq_sqrt : Real.sqrt (a * c) ^ 2 = a * c :=
    Real.sq_sqrt (mul_nonneg ha.le hc.le)
  nlinarith [Real.exp_pos ((Real.log a + Real.log c) / 2), Real.sqrt_nonneg (a * c)]

/-- Scalar form of equation (4.2) in the report. -/
theorem scalar_entropy {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    Real.exp (-(ent a + ent c) / 2) * (a + c) ≤ 2 * Real.sqrt (a * c) := by
  let m : ℝ := (a + c) / 2
  have hm : 0 < m := by dsimp [m]; positivity
  have hfactor :
      Real.exp (-(ent a + ent c) / 2) =
        Real.exp (1 - m) * Real.sqrt (a * c) := by
    rw [← exp_half_log_add_eq_sqrt_mul ha hc, ← Real.exp_add]
    congr 1
    dsimp [m, ent]
    ring
  rw [hfactor]
  have hsqrt : 0 ≤ Real.sqrt (a * c) := Real.sqrt_nonneg _
  have hm_bound := mul_exp_one_sub_le_one hm
  calc
    (Real.exp (1 - m) * Real.sqrt (a * c)) * (a + c) =
        2 * (m * Real.exp (1 - m)) * Real.sqrt (a * c) := by
          dsimp [m]
          ring
    _ ≤ 2 * 1 * Real.sqrt (a * c) := by gcongr
    _ = 2 * Real.sqrt (a * c) := by ring

private theorem scalar_entropy_inv {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    Real.exp (-(ent a + ent c) / 2) * (a⁻¹ + c⁻¹) ≤
      2 / Real.sqrt (a * c) := by
  have hp : 0 < a * c := mul_pos ha hc
  have hs : 0 < Real.sqrt (a * c) := Real.sqrt_pos.2 hp
  have hmain := scalar_entropy ha hc
  calc
    Real.exp (-(ent a + ent c) / 2) * (a⁻¹ + c⁻¹) =
        (Real.exp (-(ent a + ent c) / 2) * (a + c)) / (a * c) := by
          field_simp
          all_goals ring
    _ ≤ (2 * Real.sqrt (a * c)) / (a * c) := by
      exact div_le_div_of_nonneg_right hmain hp.le
    _ = 2 / Real.sqrt (a * c) := by
      have hs_sq : Real.sqrt (a * c) ^ 2 = a * c := Real.sq_sqrt hp.le
      field_simp
      nlinarith

private theorem block_cauchy {b u b' u' : ℝ}
    (hb : 0 < b) (hu : 0 < u) (hb' : 0 < b') (hu' : 0 < u') :
    Real.sqrt (b * b') + 2 / Real.sqrt (u * u') ≤
      Real.sqrt ((b + 2 / u) * (b' + 2 / u')) := by
  have hterm₁ : Real.sqrt b * Real.sqrt b' = Real.sqrt (b * b') := by
    rw [Real.sqrt_mul hb.le]
  have huu : 0 < u * u' := mul_pos hu hu'
  have hU : 0 < Real.sqrt (u * u') := Real.sqrt_pos.2 huu
  have hterm₂ :
      Real.sqrt (2 / u) * Real.sqrt (2 / u') = 2 / Real.sqrt (u * u') := by
    have hleft : 0 ≤ Real.sqrt (2 / u) * Real.sqrt (2 / u') := mul_nonneg (by positivity) (by positivity)
    have hright : 0 ≤ 2 / Real.sqrt (u * u') := by positivity
    have hsqu : Real.sqrt (u * u') ^ 2 = u * u' := Real.sq_sqrt huu.le
    have hsquare :
        (Real.sqrt (2 / u) * Real.sqrt (2 / u')) ^ 2 =
          (2 / Real.sqrt (u * u')) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
      field_simp
      nlinarith
    nlinarith
  have hbscale : 0 ≤ b + 2 / u := by positivity
  have hraw := Real.sum_sqrt_mul_sqrt_le
    (Finset.univ : Finset (Fin 2))
    (f := ![b, 2 / u]) (g := ![b', 2 / u'])
    (by intro i; fin_cases i <;> simp <;> positivity)
    (by intro i; fin_cases i <;> simp <;> positivity)
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hraw
  rw [hterm₁, hterm₂, ← Real.sqrt_mul hbscale] at hraw
  exact hraw

/-- A positive normalized block state `(b,u)` from equation (3.5). -/
structure BlockState where
  b : ℝ
  u : ℝ
  b_pos : 0 < b
  u_pos : 0 < u

namespace BlockState

/-- The normalized block scale `r = b + 2/u`. -/
noncomputable def scale (s : BlockState) : ℝ := s.b + 2 / s.u

/-- The endpoint entropy `ent(b) + ent(u)`. -/
noncomputable def entropy (s : BlockState) : ℝ := ent s.b + ent s.u

theorem scale_pos (s : BlockState) : 0 < s.scale := by
  unfold scale
  exact add_pos s.b_pos (div_pos (by norm_num) s.u_pos)

theorem entropy_nonneg (s : BlockState) : 0 ≤ s.entropy := by
  unfold entropy
  exact add_nonneg (ent_nonneg s.b_pos) (ent_nonneg s.u_pos)

end BlockState

/-- The two-state block-scale inequality (Lemma 4.1 / equation (4.2) in the
report).  This is the new local estimate that permits the full path entropy
to telescope. -/
theorem twoState_blockScale (s t : BlockState) :
    (s.scale + t.scale) / (2 * Real.sqrt (s.scale * t.scale)) ≤
      Real.exp ((s.entropy + t.entropy) / 2) := by
  let cb := Real.exp (-(ent s.b + ent t.b) / 2)
  let cu := Real.exp (-(ent s.u + ent t.u) / 2)
  have hcb0 : 0 ≤ cb := (Real.exp_pos _).le
  have hcu0 : 0 ≤ cu := (Real.exp_pos _).le
  have hcb1 : cb ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    have hs := ent_nonneg s.b_pos
    have ht := ent_nonneg t.b_pos
    linarith
  have hcu1 : cu ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    have hs := ent_nonneg s.u_pos
    have ht := ent_nonneg t.u_pos
    linarith
  have hb := scalar_entropy s.b_pos t.b_pos
  have hu := scalar_entropy_inv s.u_pos t.u_pos
  change cb * (s.b + t.b) ≤ 2 * Real.sqrt (s.b * t.b) at hb
  change cu * (s.u⁻¹ + t.u⁻¹) ≤ 2 / Real.sqrt (s.u * t.u) at hu
  have hweighted :
      cb * cu * (s.scale + t.scale) ≤
        2 * Real.sqrt (s.scale * t.scale) := by
    calc
      cb * cu * (s.scale + t.scale) =
          cu * (cb * (s.b + t.b)) +
            2 * cb * (cu * (s.u⁻¹ + t.u⁻¹)) := by
              unfold BlockState.scale
              field_simp
              all_goals ring
      _ ≤ cu * (2 * Real.sqrt (s.b * t.b)) +
            2 * cb * (2 / Real.sqrt (s.u * t.u)) := by gcongr
      _ ≤ 1 * (2 * Real.sqrt (s.b * t.b)) +
            2 * 1 * (2 / Real.sqrt (s.u * t.u)) := by gcongr
      _ = 2 * (Real.sqrt (s.b * t.b) +
            2 / Real.sqrt (s.u * t.u)) := by ring
      _ ≤ 2 * Real.sqrt (s.scale * t.scale) := by
        gcongr
        simpa [BlockState.scale] using
          block_cauchy s.b_pos s.u_pos t.b_pos t.u_pos
  have hcoeff :
      cb * cu = Real.exp (-(s.entropy + t.entropy) / 2) := by
    dsimp [cb, cu, BlockState.entropy]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hcoeff] at hweighted
  have hscale : 0 < 2 * Real.sqrt (s.scale * t.scale) := by
    have : 0 < s.scale * t.scale := mul_pos s.scale_pos t.scale_pos
    positivity
  apply (div_le_iff₀ hscale).2
  calc
    s.scale + t.scale =
        Real.exp ((s.entropy + t.entropy) / 2) *
          (Real.exp (-(s.entropy + t.entropy) / 2) *
            (s.scale + t.scale)) := by
              rw [← mul_assoc, ← Real.exp_add]
              ring_nf
              simp
    _ ≤ Real.exp ((s.entropy + t.entropy) / 2) *
          (2 * Real.sqrt (s.scale * t.scale)) := by gcongr

end GD.Sqrt3LowerBound
