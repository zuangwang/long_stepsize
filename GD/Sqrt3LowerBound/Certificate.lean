import GD.Sqrt3LowerBound.FinitePrefix

/-!
# The finite cutoff scan and the schedule certificate

This file formalizes Section 7 of the report once the two certificate inputs
have been established: the half-density bound and the bounded-rank prefix
bound.  The complete scan, including the `N < 3` branch, is proved here.
-/

namespace GD.Sqrt3LowerBound

/-- The report's uniform bounded-rank constant `c_fin = 1 / 768`. -/
noncomputable def finiteCutoffConstant : ℝ := 1 / 768

/-- The explicit universal schedule constant in equation (6.11). -/
noncomputable def scheduleConstant : ℝ :=
  min finiteCutoffConstant
    (((3 : ℝ) ^ (criticalExponent - 1) / propagationConstant) *
      min (1 / 5) finiteCutoffConstant)

theorem finiteCutoffConstant_pos : 0 < finiteCutoffConstant := by
  unfold finiteCutoffConstant
  norm_num

theorem scheduleConstant_pos : 0 < scheduleConstant := by
  unfold scheduleConstant
  apply lt_min
  · exact finiteCutoffConstant_pos
  · apply mul_pos
    · exact div_pos
        (Real.rpow_pos_of_pos (by norm_num) _)
        propagationConstant_pos
    · exact lt_min (by norm_num) finiteCutoffConstant_pos

/-- Corollary 6.2 (`Uniform finite-cutoff constant`) extracted from the
finite-prefix estimate.  This checks all edge cases `q = 0,1,2,3` and the
numerical identity `c_fin = 1 / 768`. -/
theorem uniformFiniteCutoffConstant
    (q : ℕ) (mass certificate : ℝ)
    (hq : q ≤ 3) (hmass : 0 < mass)
    (hempty : q = 0 → 1 / (2 * mass) ≤ certificate)
    (hprefix : 1 ≤ q →
      1 / (4 * mass * (q : ℝ) * (8 : ℝ) ^ (q - 1)) ≤ certificate) :
    finiteCutoffConstant / mass ≤ certificate := by
  by_cases hq0 : q = 0
  · have hcoeff : finiteCutoffConstant ≤ (1 / 2 : ℝ) := by
      unfold finiteCutoffConstant
      norm_num
    have hscaled := div_le_div_of_nonneg_right hcoeff hmass.le
    calc
      finiteCutoffConstant / mass ≤ (1 / 2 : ℝ) / mass := hscaled
      _ = 1 / (2 * mass) := by field_simp [hmass.ne']
      _ ≤ certificate := hempty hq0
  · have hq1 : 1 ≤ q := by omega
    have hcoeff :
        finiteCutoffConstant ≤
          1 / (4 * (q : ℝ) * (8 : ℝ) ^ (q - 1)) := by
      interval_cases q <;> norm_num [finiteCutoffConstant]
    have hscaled := div_le_div_of_nonneg_right hcoeff hmass.le
    calc
      finiteCutoffConstant / mass ≤
          (1 / (4 * (q : ℝ) * (8 : ℝ) ^ (q - 1))) / mass := hscaled
      _ = 1 / (4 * mass * (q : ℝ) * (8 : ℝ) ^ (q - 1)) := by
        have hqReal : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq1)
        field_simp [hmass.ne', hqReal]
      _ ≤ certificate := hprefix hq1

private theorem transport_to_reciprocal_bound
    {mass cap a b b' gamma c : ℝ}
    (hmass : 0 < mass) (hcap : 0 < cap)
    (_ha : 0 < a) (hb : 0 < b) (hb' : 0 < b')
    (hgamma : 0 < gamma) (hc : 0 ≤ c)
    (htransport : mass * a ≤ gamma * cap * b)
    (hbb' : b ≤ b') :
    (c * a / gamma) / (cap * b') ≤ c / mass := by
  apply (div_le_div_iff₀ (mul_pos hcap hb') hmass).2
  calc
    (c * a / gamma) * mass = c * (mass * a) / gamma := by ring
    _ ≤ c * (gamma * cap * b) / gamma := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left htransport hc) hgamma.le
    _ = c * (cap * b) := by field_simp [hgamma.ne']
    _ ≤ c * (cap * b') := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hbb' hcap.le) hc
    _ = c * (cap * b') := rfl

private theorem nat_rpow_succ_mono (N : ℕ) :
    (N : ℝ) ^ (criticalExponent - 1) ≤
      ((N + 1 : ℕ) : ℝ) ^ (criticalExponent - 1) := by
  apply Real.rpow_le_rpow
  · positivity
  · norm_num [Nat.cast_add, Nat.cast_one]
  · exact (sub_pos.mpr criticalExponent_gt_one).le

/-- Proposition 6.3 (`Certificate lower bound`).  `certificate` is the
maximized scalar certificate.  The two hypotheses are exactly the outputs of
the half-density and finite-prefix lemmas, respectively. -/
theorem completeCutoffScan
    (N : ℕ) (cap certificate : ℝ) (δ : ℕ → ℝ)
    (hcap : 0 < cap)
    (hδpos : ∀ i < N, 0 < δ i)
    (hδsorted : Antitone δ)
    (hlowDensity : ∀ q, 3 ≤ q → q ≤ N →
      rankDensity N cap δ q ≤ densityThreshold →
        1 / (5 * rankMass N cap δ q) ≤ certificate)
    (hfinite : ∀ q, q ≤ min 3 N →
      finiteCutoffConstant / rankMass N cap δ q ≤ certificate) :
    scheduleConstant /
        (cap * ((N + 1 : ℕ) : ℝ) ^ (criticalExponent - 1)) ≤ certificate := by
  classical
  let low : ℕ → Prop := fun q ↦
    3 ≤ q ∧ rankDensity N cap δ q ≤ densityThreshold
  by_cases hLow : ∃ q, q ≤ N ∧ low q
  · let k := Nat.findGreatest low N
    obtain ⟨q, hqN, hqLow⟩ := hLow
    have hkLow : low k := Nat.findGreatest_spec hqN hqLow
    have hk : 3 ≤ k := hkLow.1
    have hkN : k ≤ N := Nat.findGreatest_le N
    have hdense : ∀ r, k < r → r ≤ N →
        densityThreshold < rankDensity N cap δ r := by
      intro r hkr hrN
      have hnot := Nat.findGreatest_is_greatest (P := low) hkr hrN
      have hr3 : 3 ≤ r := hk.trans (Nat.le_of_lt hkr)
      dsimp [low] at hnot
      exact lt_of_not_ge (fun h ↦ hnot ⟨hr3, h⟩)
    have htransport := tailBudgetTransport N cap δ k hk hkN hcap
      hδpos hδsorted hdense
    have hMk := rankMass_pos N cap δ k hkN hcap
      (fun i hi ↦ (hδpos i hi).le)
    have ha : 0 < (3 : ℝ) ^ (criticalExponent - 1) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hkPow :
        (3 : ℝ) ^ (criticalExponent - 1) ≤
          (k : ℝ) ^ (criticalExponent - 1) := by
      apply Real.rpow_le_rpow
      · norm_num
      · exact_mod_cast hk
      · exact (sub_pos.mpr criticalExponent_gt_one).le
    have htransportThree :
        rankMass N cap δ k *
            (3 : ℝ) ^ (criticalExponent - 1) ≤
          propagationConstant * cap *
            (N : ℝ) ^ (criticalExponent - 1) := by
      exact (mul_le_mul_of_nonneg_left hkPow hMk.le).trans htransport
    have hNpos : 0 < (N : ℝ) ^ (criticalExponent - 1) := by
      apply Real.rpow_pos_of_pos
      exact_mod_cast (show 0 < N by omega)
    have hNsuccPos : 0 < ((N + 1 : ℕ) : ℝ) ^ (criticalExponent - 1) :=
      Real.rpow_pos_of_pos (by positivity) _
    have hreciprocal := transport_to_reciprocal_bound
      hMk hcap ha hNpos hNsuccPos propagationConstant_pos
      (show 0 ≤ (1 / 5 : ℝ) by norm_num) htransportThree
      (nat_rpow_succ_mono N)
    have hcoefficient :
        scheduleConstant ≤
          (1 / 5 : ℝ) *
            (3 : ℝ) ^ (criticalExponent - 1) / propagationConstant := by
      calc
        scheduleConstant ≤
            ((3 : ℝ) ^ (criticalExponent - 1) / propagationConstant) *
              min (1 / 5) finiteCutoffConstant := min_le_right _ _
        _ ≤ ((3 : ℝ) ^ (criticalExponent - 1) / propagationConstant) *
              (1 / 5) := by
                gcongr
                exact (div_nonneg (Real.rpow_nonneg (by norm_num) _)
                  propagationConstant_pos.le)
                exact min_le_left _ _
        _ = (1 / 5 : ℝ) *
              (3 : ℝ) ^ (criticalExponent - 1) / propagationConstant := by ring
    have hden : 0 < cap * ((N + 1 : ℕ) : ℝ) ^ (criticalExponent - 1) :=
      mul_pos hcap hNsuccPos
    calc
      scheduleConstant /
          (cap * ((N + 1 : ℕ) : ℝ) ^ (criticalExponent - 1)) ≤
        (((1 / 5 : ℝ) *
            (3 : ℝ) ^ (criticalExponent - 1) / propagationConstant) /
          (cap * ((N + 1 : ℕ) : ℝ) ^ (criticalExponent - 1))) := by
            exact div_le_div_of_nonneg_right hcoefficient hden.le
      _ ≤ (1 / 5 : ℝ) / rankMass N cap δ k := hreciprocal
      _ = 1 / (5 * rankMass N cap δ k) := by ring
      _ ≤ certificate := hlowDensity k hk hkN hkLow.2
  · by_cases hNlarge : 3 ≤ N
    · have hdense : ∀ q, 3 < q → q ≤ N →
          densityThreshold < rankDensity N cap δ q := by
        intro q hq3 hqN
        exact lt_of_not_ge fun h ↦ hLow ⟨q, hqN, ⟨by omega, h⟩⟩
      have htransport := tailBudgetTransport N cap δ 3 (by omega) hNlarge
        hcap hδpos hδsorted hdense
      have hM3 := rankMass_pos N cap δ 3 hNlarge hcap
        (fun i hi ↦ (hδpos i hi).le)
      have ha : 0 < (3 : ℝ) ^ (criticalExponent - 1) :=
        Real.rpow_pos_of_pos (by norm_num) _
      have hNpos : 0 < (N : ℝ) ^ (criticalExponent - 1) := by
        apply Real.rpow_pos_of_pos
        exact_mod_cast (show 0 < N by omega)
      have hNsuccPos : 0 < ((N + 1 : ℕ) : ℝ) ^ (criticalExponent - 1) :=
        Real.rpow_pos_of_pos (by positivity) _
      have hreciprocal := transport_to_reciprocal_bound
        hM3 hcap ha hNpos hNsuccPos propagationConstant_pos
        finiteCutoffConstant_pos.le htransport (nat_rpow_succ_mono N)
      have hcoefficient :
          scheduleConstant ≤
            finiteCutoffConstant *
              (3 : ℝ) ^ (criticalExponent - 1) / propagationConstant := by
        calc
          scheduleConstant ≤
              ((3 : ℝ) ^ (criticalExponent - 1) / propagationConstant) *
                min (1 / 5) finiteCutoffConstant := min_le_right _ _
          _ ≤ ((3 : ℝ) ^ (criticalExponent - 1) / propagationConstant) *
                finiteCutoffConstant := by
                  gcongr
                  exact (div_nonneg (Real.rpow_nonneg (by norm_num) _)
                    propagationConstant_pos.le)
                  exact min_le_right _ _
          _ = finiteCutoffConstant *
                (3 : ℝ) ^ (criticalExponent - 1) / propagationConstant := by ring
      have hden : 0 < cap * ((N + 1 : ℕ) : ℝ) ^ (criticalExponent - 1) :=
        mul_pos hcap hNsuccPos
      calc
        scheduleConstant /
            (cap * ((N + 1 : ℕ) : ℝ) ^ (criticalExponent - 1)) ≤
          ((finiteCutoffConstant *
              (3 : ℝ) ^ (criticalExponent - 1) / propagationConstant) /
            (cap * ((N + 1 : ℕ) : ℝ) ^ (criticalExponent - 1))) := by
              exact div_le_div_of_nonneg_right hcoefficient hden.le
        _ ≤ finiteCutoffConstant / rankMass N cap δ 3 := hreciprocal
        _ ≤ certificate := hfinite 3 (by simp [hNlarge])
    · have hNsmall : N ≤ 3 := by omega
      have htop := hfinite N (by simp [hNsmall])
      rw [rankMass_at_top] at htop
      have hpowOne :
          1 ≤ ((N + 1 : ℕ) : ℝ) ^ (criticalExponent - 1) := by
        have hbase : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
          exact_mod_cast (show 1 ≤ N + 1 by omega)
        simpa using Real.one_le_rpow hbase
          (sub_pos.mpr criticalExponent_gt_one).le
      have hScheduleFinite : scheduleConstant ≤ finiteCutoffConstant :=
        min_le_left _ _
      have hden : 0 < cap * ((N + 1 : ℕ) : ℝ) ^ (criticalExponent - 1) := by
        exact mul_pos hcap (Real.rpow_pos_of_pos (by positivity) _)
      have hleft :
          scheduleConstant /
              (cap * ((N + 1 : ℕ) : ℝ) ^ (criticalExponent - 1)) ≤
            finiteCutoffConstant / cap := by
        apply (div_le_div_iff₀ hden hcap).2
        calc
          scheduleConstant * cap ≤ finiteCutoffConstant * cap := by gcongr
          _ ≤ finiteCutoffConstant *
              (cap * ((N + 1 : ℕ) : ℝ) ^ (criticalExponent - 1)) := by
                have hc := finiteCutoffConstant_pos.le
                nlinarith [mul_le_mul_of_nonneg_left hpowOne hcap.le]
      exact hleft.trans htop

/-- Witness-preserving form of `completeCutoffScan`.  Any downward-closed
predicate of scalar bounds can be scanned, so in particular the predicate
"some concrete marked chain has at least this contribution" survives the
case split. -/
theorem completeCutoffScan_mono
    (N : ℕ) (cap : ℝ) (δ : ℕ → ℝ) (P : ℝ → Prop)
    (hmono : ∀ {a b : ℝ}, a ≤ b → P b → P a)
    (hcap : 0 < cap)
    (hδpos : ∀ i < N, 0 < δ i)
    (hδsorted : Antitone δ)
    (hlowDensity : ∀ q, 3 ≤ q → q ≤ N →
      rankDensity N cap δ q ≤ densityThreshold →
        P (1 / (5 * rankMass N cap δ q)))
    (hfinite : ∀ q, q ≤ min 3 N →
      P (finiteCutoffConstant / rankMass N cap δ q)) :
    P (scheduleConstant /
      (cap * ((N + 1 : ℕ) : ℝ) ^ (criticalExponent - 1))) := by
  classical
  let low : ℕ → Prop := fun q ↦
    3 ≤ q ∧ rankDensity N cap δ q ≤ densityThreshold
  by_cases hLow : ∃ q, q ≤ N ∧ low q
  · let k := Nat.findGreatest low N
    obtain ⟨q, hqN, hqLow⟩ := hLow
    have hkLow : low k := Nat.findGreatest_spec hqN hqLow
    have hk : 3 ≤ k := hkLow.1
    have hkN : k ≤ N := Nat.findGreatest_le N
    have hdense : ∀ r, k < r → r ≤ N →
        densityThreshold < rankDensity N cap δ r := by
      intro r hkr hrN
      have hnot := Nat.findGreatest_is_greatest (P := low) hkr hrN
      have hr3 : 3 ≤ r := hk.trans (Nat.le_of_lt hkr)
      dsimp [low] at hnot
      exact lt_of_not_ge (fun h ↦ hnot ⟨hr3, h⟩)
    have htransport := tailBudgetTransport N cap δ k hk hkN hcap
      hδpos hδsorted hdense
    have hMk := rankMass_pos N cap δ k hkN hcap
      (fun i hi ↦ (hδpos i hi).le)
    have ha : 0 < (3 : ℝ) ^ (criticalExponent - 1) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hkPow :
        (3 : ℝ) ^ (criticalExponent - 1) ≤
          (k : ℝ) ^ (criticalExponent - 1) := by
      apply Real.rpow_le_rpow
      · norm_num
      · exact_mod_cast hk
      · exact (sub_pos.mpr criticalExponent_gt_one).le
    have htransportThree :
        rankMass N cap δ k * (3 : ℝ) ^ (criticalExponent - 1) ≤
          propagationConstant * cap * (N : ℝ) ^ (criticalExponent - 1) :=
      (mul_le_mul_of_nonneg_left hkPow hMk.le).trans htransport
    have hNpos : 0 < (N : ℝ) ^ (criticalExponent - 1) := by
      apply Real.rpow_pos_of_pos
      exact_mod_cast (show 0 < N by omega)
    have hNsuccPos : 0 < ((N + 1 : ℕ) : ℝ) ^ (criticalExponent - 1) :=
      Real.rpow_pos_of_pos (by positivity) _
    have hreciprocal := transport_to_reciprocal_bound
      hMk hcap ha hNpos hNsuccPos propagationConstant_pos
      (show 0 ≤ (1 / 5 : ℝ) by norm_num) htransportThree
      (nat_rpow_succ_mono N)
    have hcoefficient :
        scheduleConstant ≤ (1 / 5 : ℝ) *
          (3 : ℝ) ^ (criticalExponent - 1) / propagationConstant := by
      calc
        scheduleConstant ≤
            ((3 : ℝ) ^ (criticalExponent - 1) / propagationConstant) *
              min (1 / 5) finiteCutoffConstant := min_le_right _ _
        _ ≤ ((3 : ℝ) ^ (criticalExponent - 1) / propagationConstant) *
              (1 / 5) := by
                gcongr
                exact div_nonneg (Real.rpow_nonneg (by norm_num) _)
                  propagationConstant_pos.le
                exact min_le_left _ _
        _ = (1 / 5 : ℝ) *
              (3 : ℝ) ^ (criticalExponent - 1) / propagationConstant := by ring
    have hden : 0 < cap * ((N + 1 : ℕ) : ℝ) ^ (criticalExponent - 1) :=
      mul_pos hcap hNsuccPos
    have hgoal :
        scheduleConstant /
            (cap * ((N + 1 : ℕ) : ℝ) ^ (criticalExponent - 1)) ≤
          1 / (5 * rankMass N cap δ k) := by
      calc
        scheduleConstant /
            (cap * ((N + 1 : ℕ) : ℝ) ^ (criticalExponent - 1)) ≤
          (((1 / 5 : ℝ) *
              (3 : ℝ) ^ (criticalExponent - 1) / propagationConstant) /
            (cap * ((N + 1 : ℕ) : ℝ) ^ (criticalExponent - 1))) :=
              div_le_div_of_nonneg_right hcoefficient hden.le
        _ ≤ (1 / 5 : ℝ) / rankMass N cap δ k := hreciprocal
        _ = 1 / (5 * rankMass N cap δ k) := by ring
    exact hmono hgoal (hlowDensity k hk hkN hkLow.2)
  · by_cases hNlarge : 3 ≤ N
    · have hdense : ∀ q, 3 < q → q ≤ N →
          densityThreshold < rankDensity N cap δ q := by
        intro q hq3 hqN
        exact lt_of_not_ge fun h ↦ hLow ⟨q, hqN, ⟨by omega, h⟩⟩
      have htransport := tailBudgetTransport N cap δ 3 (by omega) hNlarge
        hcap hδpos hδsorted hdense
      have hM3 := rankMass_pos N cap δ 3 hNlarge hcap
        (fun i hi ↦ (hδpos i hi).le)
      have ha : 0 < (3 : ℝ) ^ (criticalExponent - 1) :=
        Real.rpow_pos_of_pos (by norm_num) _
      have hNpos : 0 < (N : ℝ) ^ (criticalExponent - 1) := by
        apply Real.rpow_pos_of_pos
        exact_mod_cast (show 0 < N by omega)
      have hNsuccPos : 0 < ((N + 1 : ℕ) : ℝ) ^ (criticalExponent - 1) :=
        Real.rpow_pos_of_pos (by positivity) _
      have hreciprocal := transport_to_reciprocal_bound
        hM3 hcap ha hNpos hNsuccPos propagationConstant_pos
        finiteCutoffConstant_pos.le htransport (nat_rpow_succ_mono N)
      have hcoefficient :
          scheduleConstant ≤ finiteCutoffConstant *
            (3 : ℝ) ^ (criticalExponent - 1) / propagationConstant := by
        calc
          scheduleConstant ≤
              ((3 : ℝ) ^ (criticalExponent - 1) / propagationConstant) *
                min (1 / 5) finiteCutoffConstant := min_le_right _ _
          _ ≤ ((3 : ℝ) ^ (criticalExponent - 1) / propagationConstant) *
                finiteCutoffConstant := by
                  gcongr
                  exact div_nonneg (Real.rpow_nonneg (by norm_num) _)
                    propagationConstant_pos.le
                  exact min_le_right _ _
          _ = finiteCutoffConstant *
                (3 : ℝ) ^ (criticalExponent - 1) / propagationConstant := by ring
      have hden : 0 < cap * ((N + 1 : ℕ) : ℝ) ^ (criticalExponent - 1) :=
        mul_pos hcap hNsuccPos
      have hgoal :
          scheduleConstant /
              (cap * ((N + 1 : ℕ) : ℝ) ^ (criticalExponent - 1)) ≤
            finiteCutoffConstant / rankMass N cap δ 3 := by
        calc
          scheduleConstant /
              (cap * ((N + 1 : ℕ) : ℝ) ^ (criticalExponent - 1)) ≤
            ((finiteCutoffConstant *
                (3 : ℝ) ^ (criticalExponent - 1) / propagationConstant) /
              (cap * ((N + 1 : ℕ) : ℝ) ^ (criticalExponent - 1))) :=
                div_le_div_of_nonneg_right hcoefficient hden.le
          _ ≤ finiteCutoffConstant / rankMass N cap δ 3 := hreciprocal
      exact hmono hgoal (hfinite 3 (by simp [hNlarge]))
    · have hNsmall : N ≤ 3 := by omega
      have htop := hfinite N (by simp [hNsmall])
      rw [rankMass_at_top] at htop
      have hpowOne :
          1 ≤ ((N + 1 : ℕ) : ℝ) ^ (criticalExponent - 1) := by
        have hbase : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
          exact_mod_cast (show 1 ≤ N + 1 by omega)
        simpa using Real.one_le_rpow hbase
          (sub_pos.mpr criticalExponent_gt_one).le
      have hScheduleFinite : scheduleConstant ≤ finiteCutoffConstant :=
        min_le_left _ _
      have hden : 0 < cap * ((N + 1 : ℕ) : ℝ) ^ (criticalExponent - 1) :=
        mul_pos hcap (Real.rpow_pos_of_pos (by positivity) _)
      have hgoal :
          scheduleConstant /
              (cap * ((N + 1 : ℕ) : ℝ) ^ (criticalExponent - 1)) ≤
            finiteCutoffConstant / cap := by
        apply (div_le_div_iff₀ hden hcap).2
        calc
          scheduleConstant * cap ≤ finiteCutoffConstant * cap := by gcongr
          _ ≤ finiteCutoffConstant *
              (cap * ((N + 1 : ℕ) : ℝ) ^ (criticalExponent - 1)) := by
                have hc := finiteCutoffConstant_pos.le
                nlinarith [mul_le_mul_of_nonneg_left hpowOne hcap.le]
      exact hmono hgoal htop

/-- Proposition 6.3 instantiated for a nonnegative finite schedule.  The
result contains the marked chain selected by the scan. -/
theorem scheduleCutoffContribution {T : ℕ} {α : Fin T → ℝ}
    (hα : ∀ t, 0 ≤ α t) :
    HasChainContribution α hα
      (scheduleConstant /
        (cappedMass α *
          ((positiveSurplusCount α + 1 : ℕ) : ℝ) ^
            (criticalExponent - 1))) := by
  apply completeCutoffScan_mono
    (positiveSurplusCount α) (cappedMass α) (rankedSurplus α)
    (HasChainContribution α hα)
  · intro a b hab hb
    exact HasChainContribution.mono hab hb
  · exact cappedMass_pos hα
  · intro i hi
    exact rankedSurplus_pos α hi
  · exact rankedSurplus_antitone α
  · intro q hq3 hqN hdensity
    exact scheduleHalfDensityContribution hα q (by omega) hqN hdensity
  · intro q hq
    have hq3 : q ≤ 3 := hq.trans (min_le_left _ _)
    have hqN : q ≤ positiveSurplusCount α := hq.trans (min_le_right _ _)
    simpa [finiteCutoffConstant] using
      scheduleFiniteCutoffContribution hα q hq3 hqN

/-- The report's normalized horizon simplification: the cap and number of
positive surpluses each cost at most one factor of `T + 1`. -/
theorem normalizedHorizonBound
    (T N : ℕ) (cap certificate : ℝ)
    (hcap : 0 < cap)
    (hcapT : cap ≤ T + 1)
    (hNT : N + 1 ≤ T + 1)
    (hcertificate : scheduleConstant /
      (cap * ((N + 1 : ℕ) : ℝ) ^ (criticalExponent - 1)) ≤ certificate) :
    scheduleConstant / ((T + 1 : ℕ) : ℝ) ^ criticalExponent ≤ certificate := by
  have hTpos : 0 < ((T + 1 : ℕ) : ℝ) ^ criticalExponent :=
    Real.rpow_pos_of_pos (by positivity) _
  have hNpow :
      ((N + 1 : ℕ) : ℝ) ^ (criticalExponent - 1) ≤
        ((T + 1 : ℕ) : ℝ) ^ (criticalExponent - 1) := by
    apply Real.rpow_le_rpow
    · positivity
    · exact_mod_cast hNT
    · exact (sub_pos.mpr criticalExponent_gt_one).le
  have hdenBound :
      cap * ((N + 1 : ℕ) : ℝ) ^ (criticalExponent - 1) ≤
        ((T + 1 : ℕ) : ℝ) ^ criticalExponent := by
    have hcapT' : cap ≤ ((T + 1 : ℕ) : ℝ) := by
      simpa [Nat.cast_add, Nat.cast_one] using hcapT
    calc
      cap * ((N + 1 : ℕ) : ℝ) ^ (criticalExponent - 1) ≤
          ((T + 1 : ℕ) : ℝ) *
            ((T + 1 : ℕ) : ℝ) ^ (criticalExponent - 1) := by
            exact mul_le_mul hcapT' hNpow
              (Real.rpow_nonneg (by positivity) _) (by positivity)
      _ = ((T + 1 : ℕ) : ℝ) ^ criticalExponent := by
        rw [show criticalExponent = 1 + (criticalExponent - 1) by ring,
          Real.rpow_add (by positivity)]
        simp
  have hsmallDen : 0 < cap * ((N + 1 : ℕ) : ℝ) ^ (criticalExponent - 1) :=
    mul_pos hcap (Real.rpow_pos_of_pos (by positivity) _)
  have hconst := scheduleConstant_pos.le
  have hfrac :
      scheduleConstant / ((T + 1 : ℕ) : ℝ) ^ criticalExponent ≤
        scheduleConstant /
          (cap * ((N + 1 : ℕ) : ℝ) ^ (criticalExponent - 1)) := by
    exact div_le_div_of_nonneg_left hconst hsmallDen hdenBound
  exact hfrac.trans hcertificate

/-- The witness-preserving normalized horizon bound for an arbitrary
nonnegative schedule of length `T`. -/
theorem scheduleHorizonContribution {T : ℕ} {α : Fin T → ℝ}
    (hα : ∀ t, 0 ≤ α t) :
    HasChainContribution α hα
      (scheduleConstant / ((T + 1 : ℕ) : ℝ) ^ criticalExponent) := by
  have hscan := scheduleCutoffContribution hα
  have hcapT : cappedMass α ≤ T + 1 := cappedMass_le_horizon hα
  have hNT : positiveSurplusCount α + 1 ≤ T + 1 := by
    exact Nat.add_le_add_right (positiveSurplusCount_le α) 1
  have hscalar := normalizedHorizonBound T (positiveSurplusCount α)
    (cappedMass α)
    (scheduleConstant /
      (cappedMass α *
        ((positiveSurplusCount α + 1 : ℕ) : ℝ) ^
          (criticalExponent - 1)))
    (cappedMass_pos hα) hcapT hNT le_rfl
  exact HasChainContribution.mono hscalar hscan

/-- The universal lower-bound constant used in the physical theorem. -/
noncomputable def lowerBoundConstant : ℝ := scheduleConstant / 2

theorem lowerBoundConstant_pos : 0 < lowerBoundConstant := by
  unfold lowerBoundConstant
  positivity [scheduleConstant_pos]

theorem criticalExponent_lt_two : criticalExponent < 2 := by
  have hnonneg : 0 ≤ criticalExponent := by
    unfold criticalExponent
    exact Real.sqrt_nonneg _
  nlinarith [criticalExponent_sq]

theorem endpointBudget_closedForm :
    endpointBudget =
      (2 + 3 * Real.pi ^ 2) / (1 + criticalExponent) := by
  have hden : 1 + criticalExponent ≠ 0 := by
    linarith [criticalExponent_gt_one]
  have hden' : criticalExponent + 1 ≠ 0 := by
    linarith [criticalExponent_gt_one]
  unfold endpointBudget densityThreshold driftConstant
  field_simp [hden, hden']
  ring

theorem propagationConstant_gt_three : 3 < propagationConstant := by
  have hdenPos : 0 < criticalExponent + 1 := by
    linarith [criticalExponent_gt_one]
  have hdenLt : criticalExponent + 1 < 3 := by
    linarith [criticalExponent_lt_two]
  have hfrac : (2 / 3 : ℝ) < 2 / (criticalExponent + 1) := by
    apply (div_lt_div_iff₀ (by norm_num) hdenPos).2
    nlinarith
  have hpiTerm :
      0 ≤ Real.pi ^ 2 / 6 * driftConstant := by
    exact mul_nonneg (div_nonneg (sq_nonneg _) (by norm_num))
      driftConstant_pos.le
  have hbudget : (1 / 2 : ℝ) < endpointBudget := by
    have hfirst :
        1 / (densityThreshold * (criticalExponent + 1)) =
          2 / (criticalExponent + 1) := by
      unfold densityThreshold
      field_simp [hdenPos.ne']
    unfold endpointBudget
    rw [hfirst]
    linarith
  have hexp := Real.add_one_le_exp endpointBudget
  unfold propagationConstant
  nlinarith

/-- Closed form (7.4) for the universal physical lower-bound constant. -/
theorem explicitLowerBoundConstant :
    lowerBoundConstant =
      (3 : ℝ) ^ (criticalExponent - 1) /
        (3072 * Real.exp
          ((2 + 3 * Real.pi ^ 2) / (1 + criticalExponent))) := by
  have hfiniteFifth : finiteCutoffConstant < (1 / 5 : ℝ) := by
    norm_num [finiteCutoffConstant]
  have hpowLt : (3 : ℝ) ^ (criticalExponent - 1) < 3 := by
    have hexponent : criticalExponent - 1 < 1 := by
      linarith [criticalExponent_lt_two]
    simpa using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 3)
      hexponent
  have hratio :
      (3 : ℝ) ^ (criticalExponent - 1) / propagationConstant < 1 :=
    (div_lt_one propagationConstant_pos).2
      (hpowLt.trans propagationConstant_gt_three)
  have hsecondLt :
      ((3 : ℝ) ^ (criticalExponent - 1) / propagationConstant) *
          finiteCutoffConstant < finiteCutoffConstant := by
    nlinarith [mul_lt_mul_of_pos_right hratio finiteCutoffConstant_pos]
  unfold lowerBoundConstant scheduleConstant
  rw [min_eq_right hfiniteFifth.le, min_eq_right hsecondLt.le]
  unfold finiteCutoffConstant propagationConstant
  rw [endpointBudget_closedForm]
  have hexp : Real.exp
      ((2 + 3 * Real.pi ^ 2) / (1 + criticalExponent)) ≠ 0 :=
    (Real.exp_pos _).ne'
  field_simp [hexp]
  ring

/-- Algebraic scaling step from a normalized realized gap to physical
smoothness `L` and radius `R`. -/
theorem physicalScalingBound
    (T : ℕ) (L R normalizedGap physicalGap : ℝ)
    (hL : 0 < L) (_hR : 0 < R)
    (hphysical : physicalGap = L * R ^ 2 * normalizedGap)
    (hnormalized : scheduleConstant / 2 *
      ((T + 1 : ℕ) : ℝ) ^ (-criticalExponent) ≤ normalizedGap) :
    lowerBoundConstant * L * R ^ 2 *
      ((T + 1 : ℕ) : ℝ) ^ (-criticalExponent) ≤ physicalGap := by
  rw [hphysical]
  unfold lowerBoundConstant
  nlinarith [mul_le_mul_of_nonneg_left hnormalized
    (mul_nonneg hL.le (sq_nonneg R))]

end GD.Sqrt3LowerBound
