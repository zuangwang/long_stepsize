import GD.Sqrt3LowerBound.Entropy

/-!
# The exact temporal reciprocal product

This file formalizes equations (3.11), (4.4), and (4.5) of the report.  It
keeps every chronological edge and proves the endpoint-entropy telescope as
a finite-product theorem.
-/

namespace GD.Sqrt3LowerBound

open scoped BigOperators

/-- The normalized reciprocal factor on one nonterminal edge. -/
noncomputable def edgeFactor (s t : BlockState) : ℝ :=
  s.b * s.u / 2 * (s.scale + t.scale) / t.scale

theorem edgeFactor_pos (s t : BlockState) : 0 < edgeFactor s t := by
  unfold edgeFactor
  exact div_pos
    (mul_pos (div_pos (mul_pos s.b_pos s.u_pos) (by norm_num))
      (add_pos s.scale_pos t.scale_pos))
    t.scale_pos

private theorem state_mul_eq_exp (s : BlockState) :
    s.b * s.u = Real.exp (s.b + s.u - 2 - s.entropy) := by
  have harg : s.b + s.u - 2 - s.entropy = Real.log s.b + Real.log s.u := by
    unfold BlockState.entropy ent
    ring
  rw [harg, Real.exp_add, Real.exp_log s.b_pos, Real.exp_log s.u_pos]

private theorem sqrt_scale_mul_div (s t : BlockState) :
    Real.sqrt (s.scale * t.scale) / t.scale =
      Real.sqrt (s.scale / t.scale) := by
  have hs : 0 < s.scale := s.scale_pos
  have ht : 0 < t.scale := t.scale_pos
  have hsqrt_t : 0 < Real.sqrt t.scale := Real.sqrt_pos.2 ht
  calc
    Real.sqrt (s.scale * t.scale) / t.scale =
        (Real.sqrt s.scale * Real.sqrt t.scale) / t.scale := by
          rw [Real.sqrt_mul hs.le]
    _ = Real.sqrt s.scale / Real.sqrt t.scale := by
      have hsq : Real.sqrt t.scale ^ 2 = t.scale := Real.sq_sqrt ht.le
      field_simp
      nlinarith
    _ = Real.sqrt (s.scale / t.scale) := by
      rw [Real.sqrt_div hs.le]

/-- One exact reciprocal transition bounded by its entropy-weighted form. -/
theorem edgeFactor_entropy (s t : BlockState) :
    edgeFactor s t ≤
      Real.exp (s.b + s.u - 2 - s.entropy +
        (s.entropy + t.entropy) / 2) *
      Real.sqrt (s.scale / t.scale) := by
  have htwo := twoState_blockScale s t
  have hsqrt : 0 < Real.sqrt (s.scale * t.scale) := by
    exact Real.sqrt_pos.2 (mul_pos s.scale_pos t.scale_pos)
  have ht : 0 < t.scale := t.scale_pos
  have hrewrite :
      edgeFactor s t =
        (s.b * s.u) *
          ((s.scale + t.scale) /
            (2 * Real.sqrt (s.scale * t.scale))) *
          (Real.sqrt (s.scale * t.scale) / t.scale) := by
    unfold edgeFactor
    field_simp
  rw [hrewrite]
  calc
    (s.b * s.u) *
          ((s.scale + t.scale) / (2 * Real.sqrt (s.scale * t.scale))) *
          (Real.sqrt (s.scale * t.scale) / t.scale) ≤
        (s.b * s.u) * Real.exp ((s.entropy + t.entropy) / 2) *
          (Real.sqrt (s.scale * t.scale) / t.scale) := by
            apply mul_le_mul_of_nonneg_right
            · exact mul_le_mul_of_nonneg_left htwo
                (mul_nonneg s.b_pos.le s.u_pos.le)
            · exact div_nonneg (Real.sqrt_nonneg _) ht.le
    _ = Real.exp (s.b + s.u - 2 - s.entropy +
          (s.entropy + t.entropy) / 2) *
        Real.sqrt (s.scale / t.scale) := by
      rw [state_mul_eq_exp, ← Real.exp_add, sqrt_scale_mul_div]

private theorem sqrt_ratio_telescope (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (n : ℕ) :
    Real.sqrt (r 0 / r n) * Real.sqrt (r n / r (n + 1)) =
      Real.sqrt (r 0 / r (n + 1)) := by
  rw [← Real.sqrt_mul (div_nonneg (hr 0).le (hr n).le)]
  congr 1
  field_simp [(hr n).ne', (hr (n + 1)).ne']

/-- Abstract finite-product telescope.  The edge exponent is deliberately
split into a bulk term `A i` and a discrete boundary difference. -/
theorem product_entropy_telescope
    (R A e r : ℕ → ℝ)
    (hR : ∀ i, 0 ≤ R i)
    (hr : ∀ i, 0 < r i)
    (hedge : ∀ i,
      R i ≤ Real.exp (A i + (e (i + 1) - e i) / 2) *
        Real.sqrt (r i / r (i + 1))) :
    ∀ n : ℕ,
      (∏ i ∈ Finset.range n, R i) ≤
        Real.exp ((∑ i ∈ Finset.range n, A i) + (e n - e 0) / 2) *
          Real.sqrt (r 0 / r n) := by
  intro n
  induction n with
  | zero => simp [(hr 0).ne']
  | succ n ih =>
      rw [Finset.prod_range_succ, Finset.sum_range_succ]
      calc
        (∏ i ∈ Finset.range n, R i) * R n ≤
            (Real.exp ((∑ i ∈ Finset.range n, A i) + (e n - e 0) / 2) *
              Real.sqrt (r 0 / r n)) *
            (Real.exp (A n + (e (n + 1) - e n) / 2) *
              Real.sqrt (r n / r (n + 1))) := by
                exact mul_le_mul ih (hedge n) (hR n) (by positivity)
        _ = Real.exp ((∑ i ∈ Finset.range n, A i) + A n +
              (e (n + 1) - e 0) / 2) *
            Real.sqrt (r 0 / r (n + 1)) := by
          rw [mul_mul_mul_comm, ← Real.exp_add, sqrt_ratio_telescope r hr n]
          congr 2
          ring

/-- Equation (4.5): all interior entropy terms cancel in the complete
chronological path, leaving only its two endpoint states. -/
theorem exactTemporalProduct (s : ℕ → BlockState) (n : ℕ) :
    (∏ i ∈ Finset.range n, edgeFactor (s i) (s (i + 1))) ≤
      Real.exp
          ((∑ i ∈ Finset.range n, ((s i).b + (s i).u - 2)) +
            ((s n).entropy - (s 0).entropy) / 2) *
        Real.sqrt ((s 0).scale / (s n).scale) := by
  apply product_entropy_telescope
      (R := fun i ↦ edgeFactor (s i) (s (i + 1)))
      (A := fun i ↦ (s i).b + (s i).u - 2)
      (e := fun i ↦ (s i).entropy)
      (r := fun i ↦ (s i).scale)
      (fun i ↦ (edgeFactor_pos (s i) (s (i + 1))).le)
      (fun i ↦ (s i).scale_pos)
  intro i
  convert edgeFactor_entropy (s i) (s (i + 1)) using 1
  all_goals ring_nf

/-- Rewriting one entropy exponential exposes its elementary maximizer. -/
theorem exp_neg_ent {t : ℝ} (ht : 0 < t) :
    Real.exp (-ent t) = t * Real.exp (1 - t) := by
  have harg : -ent t = Real.log t + (1 - t) := by
    unfold ent
    ring
  rw [harg, Real.exp_add, Real.exp_log ht]

/-- A deliberately loose version of `supₓ x² exp(1-x) = 4/e`, sufficient
for the endpoint constant in the report. -/
theorem sq_mul_exp_one_sub_lt_two {x : ℝ} (hx : 0 < x) :
    x ^ 2 * Real.exp (1 - x) < 2 := by
  have hmax := Real.mul_exp_neg_le_exp_neg_one (x / 2)
  have hleft : 0 ≤ (x / 2) * Real.exp (-(x / 2)) := by positivity
  have hright : 0 ≤ Real.exp (-1) := (Real.exp_pos _).le
  have hsquare :
      ((x / 2) * Real.exp (-(x / 2))) ^ 2 ≤
        Real.exp (-1) ^ 2 :=
    (sq_le_sq₀ hleft hright).2 hmax
  have hexp_half : Real.exp (-(x / 2)) ^ 2 = Real.exp (-x) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsquare' : x ^ 2 / 4 * Real.exp (-x) ≤ Real.exp (-2) := by
    calc
      x ^ 2 / 4 * Real.exp (-x) =
          ((x / 2) * Real.exp (-(x / 2))) ^ 2 := by
            rw [mul_pow, hexp_half]
            ring
      _ ≤ Real.exp (-1) ^ 2 := hsquare
      _ = Real.exp (-2) := by
        rw [pow_two, ← Real.exp_add]
        norm_num
  have hscaled :
      x ^ 2 * Real.exp (1 - x) ≤ 4 * Real.exp (-1) := by
    have hexp_split : Real.exp (1 - x) = Real.exp 1 * Real.exp (-x) := by
      rw [← Real.exp_add]
      congr 1
    calc
      x ^ 2 * Real.exp (1 - x) =
          (4 * Real.exp 1) * (x ^ 2 / 4 * Real.exp (-x)) := by
            rw [hexp_split]
            ring
      _ ≤ (4 * Real.exp 1) * Real.exp (-2) := by gcongr
      _ = 4 * (Real.exp 1 * Real.exp (-2)) := by ring
      _ = 4 * Real.exp (-1) := by rw [← Real.exp_add]; norm_num
  have hnumeric : 4 * Real.exp (-1) < 2 := by
    rw [Real.exp_neg]
    change 4 / Real.exp 1 < 2
    rw [div_lt_iff₀ (Real.exp_pos 1)]
    nlinarith [Real.exp_one_gt_two]
  exact hscaled.trans_lt hnumeric

/-- The endpoint quantities `E⁺` and `E⁻` in equation (4.6). -/
noncomputable def endpointPlus (s : BlockState) : ℝ :=
  s.scale * Real.exp (-s.entropy)

noncomputable def endpointMinus (s : BlockState) : ℝ :=
  s.scale⁻¹ * Real.exp (-s.entropy)

private theorem exp_neg_state_entropy (s : BlockState) :
    Real.exp (-s.entropy) =
      (s.b * Real.exp (1 - s.b)) * (s.u * Real.exp (1 - s.u)) := by
  unfold BlockState.entropy
  rw [show -(ent s.b + ent s.u) = -ent s.b + -ent s.u by ring,
    Real.exp_add, exp_neg_ent s.b_pos, exp_neg_ent s.u_pos]

private theorem endpointPlus_expansion (s : BlockState) :
    endpointPlus s =
      (s.b ^ 2 * Real.exp (1 - s.b)) *
          (s.u * Real.exp (1 - s.u)) +
        2 * (s.b * Real.exp (1 - s.b)) * Real.exp (1 - s.u) := by
  unfold endpointPlus BlockState.scale
  rw [exp_neg_state_entropy]
  field_simp [s.u_pos.ne']

/-- Equation (4.7), with the report's convenient uniform constant `8`. -/
theorem endpointPlus_lt_eight (s : BlockState) : endpointPlus s < 8 := by
  have hb₁ := mul_exp_one_sub_le_one s.b_pos
  have hu₁ := mul_exp_one_sub_le_one s.u_pos
  have hb₂ := sq_mul_exp_one_sub_lt_two s.b_pos
  have heu : Real.exp (1 - s.u) < 3 := by
    have hlt : Real.exp (1 - s.u) < Real.exp 1 :=
      Real.exp_lt_exp.mpr (by linarith [s.u_pos])
    exact hlt.trans Real.exp_one_lt_three
  have hfirst :
      (s.b ^ 2 * Real.exp (1 - s.b)) *
          (s.u * Real.exp (1 - s.u)) < 2 := by
    calc
      (s.b ^ 2 * Real.exp (1 - s.b)) *
          (s.u * Real.exp (1 - s.u)) ≤
          (s.b ^ 2 * Real.exp (1 - s.b)) * 1 := by gcongr
      _ < 2 := by simpa using hb₂
  have hsecond :
      2 * (s.b * Real.exp (1 - s.b)) * Real.exp (1 - s.u) < 6 := by
    calc
      2 * (s.b * Real.exp (1 - s.b)) * Real.exp (1 - s.u) ≤
          2 * 1 * Real.exp (1 - s.u) := by gcongr
      _ < 2 * 1 * 3 := by gcongr
      _ = 6 := by norm_num
  rw [endpointPlus_expansion]
  linarith

/-- Equation (4.8), again in the loose `< 1` form used by the report. -/
theorem endpointMinus_lt_one (s : BlockState) : endpointMinus s < 1 := by
  have hb₁ := mul_exp_one_sub_le_one s.b_pos
  have hu₂ := sq_mul_exp_one_sub_lt_two s.u_pos
  have hinv : s.scale⁻¹ ≤ s.u / 2 := by
    have hbase : 2 / s.u ≤ s.scale := by
      unfold BlockState.scale
      linarith [s.b_pos]
    have h := (inv_le_inv₀ s.scale_pos (div_pos (by norm_num) s.u_pos)).2 hbase
    calc
      s.scale⁻¹ ≤ (2 / s.u)⁻¹ := h
      _ = s.u / 2 := by field_simp
  have hprod :
      (s.b * Real.exp (1 - s.b)) *
          (s.u ^ 2 * Real.exp (1 - s.u)) < 2 := by
    calc
      (s.b * Real.exp (1 - s.b)) *
          (s.u ^ 2 * Real.exp (1 - s.u)) ≤
          1 * (s.u ^ 2 * Real.exp (1 - s.u)) := by gcongr
      _ < 1 * 2 := by gcongr
      _ = 2 := by norm_num
  unfold endpointMinus
  rw [exp_neg_state_entropy]
  calc
    s.scale⁻¹ *
        ((s.b * Real.exp (1 - s.b)) *
          (s.u * Real.exp (1 - s.u))) ≤
      (s.u / 2) *
        ((s.b * Real.exp (1 - s.b)) *
          (s.u * Real.exp (1 - s.u))) := by
            exact mul_le_mul_of_nonneg_right hinv
              (mul_nonneg
                (mul_nonneg s.b_pos.le (Real.exp_pos _).le)
                (mul_nonneg s.u_pos.le (Real.exp_pos _).le))
    _ = ((s.b * Real.exp (1 - s.b)) *
          (s.u ^ 2 * Real.exp (1 - s.u))) / 2 := by ring
    _ < 1 := by linarith

theorem endpointPlus_pos (s : BlockState) : 0 < endpointPlus s := by
  unfold endpointPlus
  exact mul_pos s.scale_pos (Real.exp_pos _)

theorem endpointMinus_pos (s : BlockState) : 0 < endpointMinus s := by
  unfold endpointMinus
  exact mul_pos (inv_pos.2 s.scale_pos) (Real.exp_pos _)

/-- The uniformly bounded endpoint expression in equation (4.9). -/
theorem endpointFactor_le_five_halves
    (s t : BlockState) (q rEnd : ℝ)
    (hq : 2 ≤ q) (_hrEnd : 0 < rEnd) (hrEnd_lt : rEnd < 2 * q) :
    (Real.sqrt (endpointPlus s * endpointPlus t) +
        rEnd * Real.sqrt (endpointPlus s * endpointMinus t)) / (4 * q) ≤
      5 / 2 := by
  have hpp : endpointPlus s * endpointPlus t < 64 := by
    calc
      endpointPlus s * endpointPlus t < 8 * endpointPlus t := by
        exact mul_lt_mul_of_pos_right (endpointPlus_lt_eight s) (endpointPlus_pos t)
      _ < 8 * 8 := by
        exact mul_lt_mul_of_pos_left (endpointPlus_lt_eight t) (by norm_num)
      _ = 64 := by norm_num
  have hpm : endpointPlus s * endpointMinus t < 8 := by
    calc
      endpointPlus s * endpointMinus t < 8 * endpointMinus t := by
        exact mul_lt_mul_of_pos_right (endpointPlus_lt_eight s) (endpointMinus_pos t)
      _ < 8 * 1 := by
        exact mul_lt_mul_of_pos_left (endpointMinus_lt_one t) (by norm_num)
      _ = 8 := by norm_num
  have hspp : Real.sqrt (endpointPlus s * endpointPlus t) < 8 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num [pow_two]
    exact hpp
  have hspm : Real.sqrt (endpointPlus s * endpointMinus t) < 3 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num [pow_two]
    exact hpm.trans (by norm_num)
  have hrmul :
      rEnd * Real.sqrt (endpointPlus s * endpointMinus t) < (2 * q) * 3 := by
    exact mul_lt_mul hrEnd_lt hspm.le
      (Real.sqrt_pos.2 (mul_pos (endpointPlus_pos s) (endpointMinus_pos t)))
      (by positivity)
  have hq0 : 0 < 4 * q := by positivity
  apply (div_le_iff₀ hq0).2
  nlinarith

private theorem boundaryMinus_identity (s t : BlockState) :
    Real.exp ((t.entropy - s.entropy) / 2) *
        Real.sqrt (s.scale / t.scale) * Real.exp (-t.entropy) =
      Real.sqrt (endpointPlus s * endpointMinus t) := by
  have hexp :
      Real.exp ((t.entropy - s.entropy) / 2) * Real.exp (-t.entropy) =
        Real.exp (-(s.entropy + t.entropy) / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hratio : 0 ≤ s.scale / t.scale :=
    div_nonneg s.scale_pos.le t.scale_pos.le
  have hexp_sq :
      Real.exp (-(s.entropy + t.entropy) / 2) ^ 2 =
        Real.exp (-(s.entropy + t.entropy)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hradicand :
      endpointPlus s * endpointMinus t =
        Real.exp (-(s.entropy + t.entropy)) * (s.scale / t.scale) := by
    calc
      endpointPlus s * endpointMinus t =
          (s.scale / t.scale) *
            (Real.exp (-s.entropy) * Real.exp (-t.entropy)) := by
              unfold endpointPlus endpointMinus
              field_simp [t.scale_pos.ne']
      _ = (s.scale / t.scale) *
            Real.exp (-(s.entropy + t.entropy)) := by
              rw [← Real.exp_add]
              congr 2
              ring
      _ = Real.exp (-(s.entropy + t.entropy)) *
            (s.scale / t.scale) := by ring
  have hleft_sq :
      (Real.exp (-(s.entropy + t.entropy) / 2) *
        Real.sqrt (s.scale / t.scale)) ^ 2 =
          endpointPlus s * endpointMinus t := by
    rw [mul_pow, hexp_sq, Real.sq_sqrt hratio, hradicand]
  have hleft0 :
      0 ≤ Real.exp (-(s.entropy + t.entropy) / 2) *
        Real.sqrt (s.scale / t.scale) := by positivity
  have hright0 : 0 ≤ Real.sqrt (endpointPlus s * endpointMinus t) :=
    Real.sqrt_nonneg _
  have hright_sq :
      Real.sqrt (endpointPlus s * endpointMinus t) ^ 2 =
        endpointPlus s * endpointMinus t :=
    Real.sq_sqrt (mul_nonneg (endpointPlus_pos s).le (endpointMinus_pos t).le)
  calc
    Real.exp ((t.entropy - s.entropy) / 2) *
        Real.sqrt (s.scale / t.scale) * Real.exp (-t.entropy) =
      Real.exp (-(s.entropy + t.entropy) / 2) *
        Real.sqrt (s.scale / t.scale) := by rw [mul_right_comm, hexp]
    _ = Real.sqrt (endpointPlus s * endpointMinus t) := by nlinarith

private theorem endpointMinus_scale_sq (t : BlockState) :
    endpointMinus t * t.scale ^ 2 = endpointPlus t := by
  unfold endpointMinus endpointPlus
  field_simp [t.scale_pos.ne']

private theorem boundaryPlus_identity (s t : BlockState) :
    (Real.exp ((t.entropy - s.entropy) / 2) *
        Real.sqrt (s.scale / t.scale) * Real.exp (-t.entropy)) * t.scale =
      Real.sqrt (endpointPlus s * endpointPlus t) := by
  rw [boundaryMinus_identity]
  have hA : 0 ≤ endpointPlus s * endpointMinus t :=
    mul_nonneg (endpointPlus_pos s).le (endpointMinus_pos t).le
  have hleft_sq :
      (Real.sqrt (endpointPlus s * endpointMinus t) * t.scale) ^ 2 =
        endpointPlus s * endpointPlus t := by
    rw [mul_pow, Real.sq_sqrt hA, mul_assoc, endpointMinus_scale_sq]
  have hright_sq :
      Real.sqrt (endpointPlus s * endpointPlus t) ^ 2 =
        endpointPlus s * endpointPlus t :=
    Real.sq_sqrt (mul_nonneg (endpointPlus_pos s).le (endpointPlus_pos t).le)
  have hleft0 : 0 ≤ Real.sqrt (endpointPlus s * endpointMinus t) * t.scale := by
    exact mul_nonneg (Real.sqrt_nonneg _) t.scale_pos.le
  have hright0 : 0 ≤ Real.sqrt (endpointPlus s * endpointPlus t) :=
    Real.sqrt_nonneg _
  nlinarith

/-- The dimensionless inverse-chain product from equation (3.13), indexed by
`n + 1` states and `n` chronological nonterminal edges. -/
noncomputable def inverseChainProduct
    (s : ℕ → BlockState) (n : ℕ) (rEnd : ℝ) : ℝ :=
  ((s n).b * (s n).u * ((s n).scale + rEnd) /
      (4 * (n + 1 : ℝ))) *
    ∏ i ∈ Finset.range n, edgeFactor (s i) (s (i + 1))

/-- Proposition 4.2 (`Exact temporal product`) in the report. -/
theorem globalTemporalProduct
    (s : ℕ → BlockState) (n : ℕ) (hn : 1 ≤ n)
    (rEnd : ℝ) (hrEnd : 0 < rEnd)
    (hrEnd_lt : rEnd < 2 * (n + 1 : ℝ)) :
    inverseChainProduct s n rEnd ≤
      (5 / 2 : ℝ) *
        Real.exp (∑ i ∈ Finset.range (n + 1),
          ((s i).b + (s i).u - 2)) := by
  let bulk : ℕ → ℝ := fun i ↦ (s i).b + (s i).u - 2
  have hpath := exactTemporalProduct s n
  have hq : (2 : ℝ) ≤ (n + 1 : ℝ) := by
    exact_mod_cast Nat.succ_le_succ hn
  have hcoeff0 :
      0 ≤ (s n).b * (s n).u * ((s n).scale + rEnd) /
        (4 * (n + 1 : ℝ)) := by
    exact (div_pos
      (mul_pos (mul_pos (s n).b_pos (s n).u_pos)
        (add_pos (s n).scale_pos hrEnd))
      (mul_pos (by norm_num) (by exact_mod_cast Nat.succ_pos n))).le
  have hfirst : inverseChainProduct s n rEnd ≤
      ((s n).b * (s n).u * ((s n).scale + rEnd) /
          (4 * (n + 1 : ℝ))) *
        (Real.exp
            ((∑ i ∈ Finset.range n, bulk i) +
              ((s n).entropy - (s 0).entropy) / 2) *
          Real.sqrt ((s 0).scale / (s n).scale)) := by
    unfold inverseChainProduct
    apply mul_le_mul_of_nonneg_left
    · simpa [bulk] using hpath
    · exact hcoeff0
  have hlastSplit :
      Real.exp ((s n).b + (s n).u - 2 - (s n).entropy) =
        Real.exp (bulk n) * Real.exp (-(s n).entropy) := by
    rw [← Real.exp_add]
    congr 1
  have hpathSplit :
      Real.exp
          ((∑ i ∈ Finset.range n, bulk i) +
            ((s n).entropy - (s 0).entropy) / 2) =
        Real.exp (∑ i ∈ Finset.range n, bulk i) *
          Real.exp (((s n).entropy - (s 0).entropy) / 2) := by
    rw [Real.exp_add]
  have hbulkSplit :
      Real.exp ((∑ i ∈ Finset.range n, bulk i) + bulk n) =
        Real.exp (∑ i ∈ Finset.range n, bulk i) * Real.exp (bulk n) := by
    rw [Real.exp_add]
  have hrearrange :
      ((s n).b * (s n).u * ((s n).scale + rEnd) /
          (4 * (n + 1 : ℝ))) *
        (Real.exp
            ((∑ i ∈ Finset.range n, bulk i) +
              ((s n).entropy - (s 0).entropy) / 2) *
          Real.sqrt ((s 0).scale / (s n).scale)) =
      Real.exp ((∑ i ∈ Finset.range n, bulk i) + bulk n) *
        ((Real.sqrt (endpointPlus (s 0) * endpointPlus (s n)) +
            rEnd * Real.sqrt (endpointPlus (s 0) * endpointMinus (s n))) /
          (4 * (n + 1 : ℝ))) := by
    rw [state_mul_eq_exp, hlastSplit, hpathSplit, hbulkSplit,
      ← boundaryPlus_identity (s 0) (s n),
      ← boundaryMinus_identity (s 0) (s n)]
    ring
  rw [hrearrange] at hfirst
  have hend := endpointFactor_le_five_halves
    (s 0) (s n) (n + 1 : ℝ) rEnd hq hrEnd hrEnd_lt
  calc
    inverseChainProduct s n rEnd ≤
        Real.exp ((∑ i ∈ Finset.range n, bulk i) + bulk n) *
          ((Real.sqrt (endpointPlus (s 0) * endpointPlus (s n)) +
              rEnd * Real.sqrt (endpointPlus (s 0) * endpointMinus (s n))) /
            (4 * (n + 1 : ℝ))) := hfirst
    _ ≤ Real.exp ((∑ i ∈ Finset.range n, bulk i) + bulk n) * (5 / 2) := by
      gcongr
    _ = (5 / 2 : ℝ) *
        Real.exp (∑ i ∈ Finset.range (n + 1),
          ((s i).b + (s i).u - 2)) := by
      rw [Finset.sum_range_succ]
      dsimp [bulk]
      ring

theorem inverseChainProduct_pos
    (s : ℕ → BlockState) (n : ℕ) (rEnd : ℝ) (hrEnd : 0 < rEnd) :
    0 < inverseChainProduct s n rEnd := by
  unfold inverseChainProduct
  apply mul_pos
  · exact div_pos
      (mul_pos (mul_pos (s n).b_pos (s n).u_pos)
        (add_pos (s n).scale_pos hrEnd))
      (mul_pos (by norm_num) (by exact_mod_cast Nat.succ_pos n))
  · exact Finset.prod_pos fun i _ ↦ edgeFactor_pos (s i) (s (i + 1))

/-- Corollary 4.3 (`Half-density certificate`) in an explicit normalized-data
interface.  The hypotheses are exactly equations (3.6), (3.8), and (3.14)
needed after a schedule has been chronologically normalized. -/
theorem halfDensityCertificate
    (s : ℕ → BlockState) (n : ℕ) (hn : 1 ≤ n)
    (rEnd mass density bEnd certificate : ℝ)
    (hrEnd : 0 < rEnd) (hrEnd_lt : rEnd < 2 * (n + 1 : ℝ))
    (hmass : 0 < mass) (hbEnd : 0 < bEnd)
    (hsumB : (∑ i ∈ Finset.range (n + 1), (s i).b) =
      (n + 1 : ℝ) - bEnd)
    (hsumU : (∑ i ∈ Finset.range (n + 1), (s i).u) =
      2 * (n + 1 : ℝ) * density)
    (hcertificate : 1 / (2 * mass * inverseChainProduct s n rEnd) ≤ certificate)
    (hdensity : density ≤ 1 / 2) :
    1 / (5 * mass) ≤ certificate := by
  let q : ℝ := n + 1
  have hq0 : 0 < q := by dsimp [q]; positivity
  have hsumU_le :
      (∑ i ∈ Finset.range (n + 1), (s i).u) ≤ q := by
    rw [hsumU]
    dsimp [q]
    nlinarith
  have hbulk :
      (∑ i ∈ Finset.range (n + 1), ((s i).b + (s i).u - 2)) =
        (∑ i ∈ Finset.range (n + 1), (s i).b) +
          (∑ i ∈ Finset.range (n + 1), (s i).u) - 2 * q := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    simp [q]
    ring
  have hbulk_neg :
      (∑ i ∈ Finset.range (n + 1), ((s i).b + (s i).u - 2)) < 0 := by
    rw [hbulk, hsumB]
    dsimp [q] at hsumU_le ⊢
    linarith
  have hexp_le :
      Real.exp (∑ i ∈ Finset.range (n + 1),
        ((s i).b + (s i).u - 2)) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr hbulk_neg.le
  have hproduct := globalTemporalProduct s n hn rEnd hrEnd hrEnd_lt
  have hproduct_le : inverseChainProduct s n rEnd ≤ 5 / 2 := by
    calc
      inverseChainProduct s n rEnd ≤
          (5 / 2 : ℝ) *
            Real.exp (∑ i ∈ Finset.range (n + 1),
              ((s i).b + (s i).u - 2)) := hproduct
      _ ≤ (5 / 2 : ℝ) * 1 := by gcongr
      _ = 5 / 2 := by ring
  have hproduct_pos := inverseChainProduct_pos s n rEnd hrEnd
  have hfrac :
      1 / (5 * mass) ≤
        1 / (2 * mass * inverseChainProduct s n rEnd) := by
    apply (div_le_div_iff₀
      (mul_pos (by norm_num) hmass)
      (mul_pos (mul_pos (by norm_num) hmass) hproduct_pos)).2
    calc
      1 * (2 * mass * inverseChainProduct s n rEnd) =
          2 * (mass * inverseChainProduct s n rEnd) := by ring
      _ ≤ 2 * (mass * (5 / 2)) := by
        gcongr
      _ = 1 * (5 * mass) := by ring
  exact hfrac.trans hcertificate

end GD.Sqrt3LowerBound
