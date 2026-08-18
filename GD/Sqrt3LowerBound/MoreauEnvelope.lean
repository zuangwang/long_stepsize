import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Topology

/-!
# A finite-polytope Moreau envelope

This file proves the convex-analysis facts used by the marked-stage
realization instead of packaging them as assumptions.  The gradient is the
metric projection onto a finite convex hull; it is firmly nonexpansive, and
the direct envelope is convex, differentiable, and one-smooth.
-/

namespace GD.Sqrt3LowerBound

open scoped RealInnerProductSpace Gradient
open Set Filter Asymptotics

section Projection

variable {ι E : Type*} [Fintype ι] [Nonempty ι]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def finitePolytope (v : ι → E) : Set E :=
  convexHull ℝ (Set.range v)

omit [Fintype ι] in
theorem finitePolytope_nonempty (v : ι → E) : (finitePolytope v).Nonempty := by
  exact (Set.range_nonempty v).mono (subset_convexHull ℝ _)

omit [Fintype ι] [Nonempty ι] in
theorem finitePolytope_convex (v : ι → E) : Convex ℝ (finitePolytope v) :=
  convex_convexHull ℝ _

omit [Nonempty ι] in
theorem finitePolytope_compact (v : ι → E) : IsCompact (finitePolytope v) := by
  apply Set.Finite.isCompact_convexHull ℝ
  exact Set.finite_range v

/-- Metric projection onto the finite convex hull. -/
noncomputable def finiteProjection (v : ι → E) (x : E) : E :=
  Classical.choose (exists_norm_eq_iInf_of_complete_convex
    (finitePolytope_nonempty v) (finitePolytope_compact v).isComplete
    (finitePolytope_convex v) x)

theorem finiteProjection_mem (v : ι → E) (x : E) :
    finiteProjection v x ∈ finitePolytope v :=
  (Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex
    (finitePolytope_nonempty v) (finitePolytope_compact v).isComplete
    (finitePolytope_convex v) x)).1

theorem finiteProjection_min (v : ι → E) (x : E) :
    ‖x - finiteProjection v x‖ =
      ⨅ p : finitePolytope v, ‖x - (p : E)‖ :=
  (Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex
    (finitePolytope_nonempty v) (finitePolytope_compact v).isComplete
    (finitePolytope_convex v) x)).2

/-- Variational characterization of the projection. -/
theorem finiteProjection_variational (v : ι → E) (x : E)
    {p : E} (hp : p ∈ finitePolytope v) :
    inner ℝ (x - finiteProjection v x) (p - finiteProjection v x) ≤ 0 := by
  exact ((norm_eq_iInf_iff_real_inner_le_zero (finitePolytope_convex v)
    (finiteProjection_mem v x)).mp (finiteProjection_min v x)) p hp

/-- Converse variational characterization, including uniqueness. -/
theorem finiteProjection_eq_of_variational (v : ι → E) (x p : E)
    (hp : p ∈ finitePolytope v)
    (hvar : ∀ z ∈ finitePolytope v, inner ℝ (x - p) (z - p) ≤ 0) :
    finiteProjection v x = p := by
  let π := finiteProjection v x
  have hπp := finiteProjection_variational v x hp
  have hpπ := hvar π (finiteProjection_mem v x)
  have hsum := add_nonpos hπp hpπ
  have hsq : ‖π - p‖ ^ 2 ≤ 0 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right] at hsum ⊢
    rw [real_inner_comm p π] at hsum ⊢
    linarith
  have hnorm : ‖π - p‖ = 0 := by
    nlinarith [norm_nonneg (π - p)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- It is enough to check the projection inequality at the finitely many
vertices: linear inequalities persist under convex hull. -/
theorem finiteProjection_eq_of_vertex_max (v : ι → E) (x p : E)
    (hp : p ∈ Set.range v)
    (hmax : ∀ i, inner ℝ (x - p) (v i) ≤ inner ℝ (x - p) p) :
    finiteProjection v x = p := by
  have hpPoly : p ∈ finitePolytope v := subset_convexHull ℝ _ hp
  apply finiteProjection_eq_of_variational v x p hpPoly
  intro z hz
  have hlinear : IsLinearMap ℝ (fun w : E ↦ inner ℝ (x - p) w) :=
    (innerSL ℝ (x - p)).toLinearMap.isLinear
  have hconv : Convex ℝ {w : E | inner ℝ (x - p) w ≤ inner ℝ (x - p) p} :=
    convex_halfSpace_le hlinear _
  have hall : z ∈ {w : E | inner ℝ (x - p) w ≤ inner ℝ (x - p) p} := by
    apply convexHull_min _ hconv hz
    rintro _ ⟨i, rfl⟩
    exact hmax i
  simp only [Set.mem_setOf_eq] at hall
  simp only [inner_sub_right]
  linarith

/-- Firm nonexpansiveness of projection. -/
theorem finiteProjection_firm (v : ι → E) (x y : E) :
    ‖finiteProjection v x - finiteProjection v y‖ ^ 2 ≤
      inner ℝ (finiteProjection v x - finiteProjection v y) (x - y) := by
  have hx := finiteProjection_variational v x (finiteProjection_mem v y)
  have hy := finiteProjection_variational v y (finiteProjection_mem v x)
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right] at hx hy ⊢
  rw [real_inner_comm (finiteProjection v x) (finiteProjection v y)] at hy ⊢
  rw [real_inner_comm x (finiteProjection v x),
    real_inner_comm x (finiteProjection v y),
    real_inner_comm y (finiteProjection v x),
    real_inner_comm y (finiteProjection v y)] at ⊢
  linarith

theorem finiteProjection_nonexpansive (v : ι → E) (x y : E) :
    ‖finiteProjection v x - finiteProjection v y‖ ≤ ‖x - y‖ := by
  have hfirm := finiteProjection_firm v x y
  have hcauchy := real_inner_le_norm
    (finiteProjection v x - finiteProjection v y) (x - y)
  let a := ‖finiteProjection v x - finiteProjection v y‖
  let b := ‖x - y‖
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  dsimp [a, b] at ha hb ⊢
  nlinarith

theorem finiteProjection_lipschitz (v : ι → E) :
    LipschitzWith 1 (finiteProjection v) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  exact finiteProjection_nonexpansive v x y

/-- The direct Moreau-envelope score. -/
noncomputable def envelopeScore (p x : E) : ℝ :=
  inner ℝ p x - ‖p‖ ^ 2 / 2

/-- Direct form of the Moreau envelope of the support function. -/
noncomputable def finiteEnvelope (v : ι → E) (x : E) : ℝ :=
  envelopeScore (finiteProjection v x) x

theorem envelopeScore_le (v : ι → E) (x : E) {p : E}
    (hp : p ∈ finitePolytope v) :
    envelopeScore p x ≤ finiteEnvelope v x := by
  have hvar := finiteProjection_variational v x hp
  let π := finiteProjection v x
  have hid :
      finiteEnvelope v x - envelopeScore p x =
        -inner ℝ (x - π) (p - π) + ‖p - π‖ ^ 2 / 2 := by
    unfold finiteEnvelope envelopeScore
    dsimp [π]
    rw [norm_sub_sq_real]
    simp only [inner_sub_left, inner_sub_right]
    rw [real_inner_comm p x, real_inner_comm (finiteProjection v x) x,
      real_inner_comm p (finiteProjection v x), real_inner_self_eq_norm_sq]
    ring
  rw [← sub_nonneg, hid]
  change inner ℝ (x - π) (p - π) ≤ 0 at hvar
  nlinarith [sq_nonneg ‖p - π‖]

theorem finiteEnvelope_increment_lower (v : ι → E) (x y : E) :
    inner ℝ (finiteProjection v x) (y - x) ≤
      finiteEnvelope v y - finiteEnvelope v x := by
  have hscore := envelopeScore_le v y (finiteProjection_mem v x)
  unfold finiteEnvelope envelopeScore at hscore ⊢
  simp only [inner_sub_right]
  linarith

theorem finiteEnvelope_increment_upper (v : ι → E) (x y : E) :
    finiteEnvelope v y - finiteEnvelope v x ≤
      inner ℝ (finiteProjection v y) (y - x) := by
  have hscore := envelopeScore_le v x (finiteProjection_mem v y)
  unfold finiteEnvelope envelopeScore at hscore ⊢
  simp only [inner_sub_right]
  linarith

theorem finiteEnvelope_remainder_nonneg (v : ι → E) (x y : E) :
    0 ≤ finiteEnvelope v y - finiteEnvelope v x -
      inner ℝ (finiteProjection v x) (y - x) := by
  linarith [finiteEnvelope_increment_lower v x y]

theorem finiteEnvelope_remainder_le (v : ι → E) (x y : E) :
    finiteEnvelope v y - finiteEnvelope v x -
        inner ℝ (finiteProjection v x) (y - x) ≤ ‖y - x‖ ^ 2 := by
  have hu := finiteEnvelope_increment_upper v x y
  have hc := real_inner_le_norm
    (finiteProjection v y - finiteProjection v x) (y - x)
  have hlip := finiteProjection_nonexpansive v y x
  have hnorm :
      ‖finiteProjection v y - finiteProjection v x‖ * ‖y - x‖ ≤
        ‖y - x‖ ^ 2 := by
    nlinarith [norm_nonneg (y - x)]
  have hinter :
      inner ℝ (finiteProjection v y - finiteProjection v x) (y - x) ≤
        ‖y - x‖ ^ 2 := hc.trans hnorm
  simp only [inner_sub_left] at hinter
  linarith

theorem finiteEnvelope_convex (v : ι → E) :
    ConvexOn ℝ Set.univ (finiteEnvelope v) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  let z := a • x + b • y
  let p := finiteProjection v z
  have hpx := envelopeScore_le v x (finiteProjection_mem v z)
  have hpy := envelopeScore_le v y (finiteProjection_mem v z)
  have hz : finiteEnvelope v z = envelopeScore p z := rfl
  have ha' := mul_le_mul_of_nonneg_left hpx ha
  have hb' := mul_le_mul_of_nonneg_left hpy hb
  have hsplit :
      envelopeScore p z =
        a * envelopeScore p x + b * envelopeScore p y := by
    unfold envelopeScore
    dsimp [z]
    simp only [inner_add_right, real_inner_smul_right]
    calc
      a * inner ℝ p x + b * inner ℝ p y - ‖p‖ ^ 2 / 2 =
          a * inner ℝ p x + b * inner ℝ p y -
            (a + b) * (‖p‖ ^ 2 / 2) := by rw [hab]; ring
      _ = a * (inner ℝ p x - ‖p‖ ^ 2 / 2) +
          b * (inner ℝ p y - ‖p‖ ^ 2 / 2) := by ring
  rw [hz, hsplit]
  exact add_le_add ha' hb'

variable [CompleteSpace E]

theorem finiteEnvelope_hasGradient (v : ι → E) (x : E) :
    HasGradientAt (finiteEnvelope v) (finiteProjection v x) x := by
  rw [hasGradientAt_iff_isLittleO_nhds_zero]
  let remainder : E → ℝ := fun h ↦
    finiteEnvelope v (x + h) - finiteEnvelope v x -
      inner ℝ (finiteProjection v x) h
  have hbound : ∀ h, ‖remainder h‖ ≤ 1 * ‖(‖h‖ ^ 2 : ℝ)‖ := by
    intro h
    have hlo := finiteEnvelope_remainder_nonneg v x (x + h)
    have hup := finiteEnvelope_remainder_le v x (x + h)
    have hsub : x + h - x = h := by abel
    rw [hsub] at hlo hup
    dsimp [remainder]
    simpa [Real.norm_eq_abs, abs_of_nonneg hlo,
      abs_of_nonneg (sq_nonneg ‖h‖)] using hup
  have hbig : remainder =O[nhds 0] fun h : E ↦ (‖h‖ ^ 2 : ℝ) :=
    IsBigO.of_bound 1 (Filter.Eventually.of_forall hbound)
  have hlittle := hbig.trans_isLittleO
    (isLittleO_norm_pow_id (E' := E) (by omega : 1 < 2))
  simpa [remainder] using hlittle

theorem finiteEnvelope_gradient (v : ι → E) :
    ∇ (finiteEnvelope v) = finiteProjection v :=
  gradient_eq (finiteEnvelope_hasGradient v)

theorem finiteEnvelope_one_smooth (v : ι → E) :
    LipschitzWith 1 (∇ (finiteEnvelope v)) := by
  rw [finiteEnvelope_gradient v]
  exact finiteProjection_lipschitz v

omit [CompleteSpace E] in
theorem finiteEnvelope_minimized_at_zero (v : ι → E)
    (hzero : (0 : E) ∈ finitePolytope v) :
    finiteEnvelope v 0 = 0 ∧ ∀ x, finiteEnvelope v 0 ≤ finiteEnvelope v x := by
  have hnonneg : ∀ x, 0 ≤ finiteEnvelope v x := by
    intro x
    simpa [envelopeScore] using envelopeScore_le v x hzero
  have hzeroUpper : finiteEnvelope v 0 ≤ 0 := by
    unfold finiteEnvelope envelopeScore
    have hsquare : 0 ≤ ‖finiteProjection v 0‖ ^ 2 := sq_nonneg _
    simp only [inner_zero_right, zero_sub]
    linarith
  have hz : finiteEnvelope v 0 = 0 := le_antisymm hzeroUpper (hnonneg 0)
  exact ⟨hz, fun x ↦ hz.le.trans (hnonneg x)⟩

end Projection

end GD.Sqrt3LowerBound
