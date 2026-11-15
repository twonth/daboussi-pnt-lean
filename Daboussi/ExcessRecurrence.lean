import Daboussi.SmoothLogarithms
import Daboussi.Limsup

open Finset MeasureTheory ArithmeticFunction

namespace Daboussi

theorem smoothLambda_nonneg (y : ℝ) (n : ℕ) : 0 ≤ restrictSmooth y vonMangoldt n := by
  unfold restrictSmooth
  simp only [coe_mk]
  split_ifs
  · exact vonMangoldt_nonneg
  · rfl

theorem smoothM_log_integrable (y x : ℝ) :
    IntegrableOn (fun t => smoothM t y / t) (Set.Icc 1 x) := by
  simpa only [div_eq_mul_inv] using
    (smoothM_integrable y x).mul_continuousOn (continuousOn_inv_Icc x) isCompact_Icc

theorem psi_log_integrable (y x : ℝ) :
    IntegrableOn (fun t => psi t y / t) (Set.Icc 1 x) := by
  simpa only [div_eq_mul_inv] using
    (psi_integrable y x).mul_continuousOn (continuousOn_inv_Icc x) isCompact_Icc

theorem excess_integrable (y x : ℝ) : IntegrableOn (excess y) (Set.Icc 1 x) := by
  have h := (excess_log_integrable y x).mul_continuousOn continuousOn_id isCompact_Icc
  apply h.congr_fun _ measurableSet_Icc
  intro t ht
  exact div_mul_cancel₀ _ (by linarith [ht.1])

/-- Triangle inequality applied to the signed logarithmic identity. -/
theorem abs_smoothM_log_le (y : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    |smoothM x y| * Real.log x ≤
      (∑ d ∈ Icc 1 ⌊x⌋₊, restrictSmooth y vonMangoldt d * |smoothM (x / d) y|) +
        ∫ t in 1..x, |smoothM t y| / t := by
  have h := smoothM_log_identity y hx
  have hn := abs_add_le
    (-(∑ d ∈ Icc 1 ⌊x⌋₊, restrictSmooth y vonMangoldt d * smoothM (x / d) y))
    (∫ t in 1..x, smoothM t y / t)
  rw [← h, abs_mul, abs_of_nonneg (Real.log_nonneg hx), abs_neg] at hn
  apply hn.trans (add_le_add _ _)
  · apply (abs_sum_le_sum_abs _ _).trans_eq
    apply sum_congr rfl
    intro d _
    rw [abs_mul, abs_of_nonneg (smoothLambda_nonneg y d)]
  · have hi := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := fun t => smoothM t y / t) hx
    simpa only [Real.norm_eq_abs, abs_div] using hi.trans_eq (intervalIntegral.integral_congr
      (fun t ht => by rw [Real.norm_eq_abs, abs_div, abs_of_pos (show 0 < t by rw [Set.uIcc_of_le hx] at ht; linarith [ht.1])]))

/-- Equation (excess-inequality): subtract the counting identity and take positive parts. -/
theorem excess_recurrence (y : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    excess y x * Real.log x ≤
      (∑ d ∈ Icc 1 ⌊x⌋₊, restrictSmooth y vonMangoldt d / d * excess y (x / d)) +
        (∫ t in 1..x, excess y t) / x := by
  have hx0 : 0 < x := by linarith
  have hM := abs_smoothM_log_le y hx
  have hψ := psi_log_identity y hx
  have hψa := congrArg (fun z : ℝ => a * z) hψ
  have hψi : IntervalIntegrable (fun t => psi t y / t) volume 1 x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr (psi_log_integrable y x)
  have hMi : IntervalIntegrable (fun t => |smoothM t y| / t) volume 1 x := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr
    have habs : IntegrableOn (fun t => |smoothM t y|) (Set.Icc 1 x) := (smoothM_integrable y x).abs
    simpa only [div_eq_mul_inv] using
      habs.mul_continuousOn (continuousOn_inv_Icc x) isCompact_Icc
  have hEi : IntervalIntegrable (excess y) volume 1 x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr (excess_integrable y x)
  have hInt : (∫ t in 1..x, |smoothM t y| / t) - a * (∫ t in 1..x, psi t y / t) ≤
      ∫ t in 1..x, excess y t := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hMi (hψi.const_mul a)]
    apply intervalIntegral.integral_mono_on hx (hMi.sub (hψi.const_mul a)) hEi
    intro t ht
    simpa only [excess, mul_div_assoc] using le_max_left (|smoothM t y| / t - a * psi t y / t) 0
  have hSum : (∑ d ∈ Icc 1 ⌊x⌋₊, restrictSmooth y vonMangoldt d * |smoothM (x / d) y|) -
      a * (∑ d ∈ Icc 1 ⌊x⌋₊, restrictSmooth y vonMangoldt d * psi (x / d) y) ≤
      x * (∑ d ∈ Icc 1 ⌊x⌋₊, restrictSmooth y vonMangoldt d / d * excess y (x / d)) := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    apply sum_le_sum
    intro d hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (mem_Icc.mp hd).1
    have hxd : 0 < x / d := div_pos hx0 hd0
    have he := mul_le_mul_of_nonneg_left
      (le_max_left (|smoothM (x / d) y| / (x / d) - a * psi (x / d) y / (x / d)) 0)
      (mul_nonneg (smoothLambda_nonneg y d) hxd.le)
    change restrictSmooth y vonMangoldt d * (x / d) *
      (|smoothM (x / d) y| / (x / d) - a * psi (x / d) y / (x / d)) ≤
      restrictSmooth y vonMangoldt d * (x / d) * excess y (x / d) at he
    convert he using 1 <;> field_simp <;> ring
  have hraw : (|smoothM x y| / x - a * psi x y / x) * Real.log x ≤
      (∑ d ∈ Icc 1 ⌊x⌋₊, restrictSmooth y vonMangoldt d / d * excess y (x / d)) +
        (∫ t in 1..x, excess y t) / x := by
    convert (div_le_div_of_nonneg_right (show
      (|smoothM x y| - a * psi x y) * Real.log x ≤
        x * (∑ d ∈ Icc 1 ⌊x⌋₊, restrictSmooth y vonMangoldt d / d * excess y (x / d)) +
          ∫ t in 1..x, excess y t by nlinarith only [hM, hψa, hInt, hSum]) hx0.le) using 1 <;> field_simp <;> ring
  have hR : 0 ≤ (∑ d ∈ Icc 1 ⌊x⌋₊, restrictSmooth y vonMangoldt d / d * excess y (x / d)) +
      (∫ t in 1..x, excess y t) / x := by
    apply add_nonneg
    · exact sum_nonneg (fun d _ => mul_nonneg (div_nonneg (smoothLambda_nonneg y d) (Nat.cast_nonneg _))
        (excess_nonneg _ _))
    · exact div_nonneg (intervalIntegral.integral_nonneg hx (fun t _ => excess_nonneg y t)) hx0.le
  unfold excess
  rw [max_mul_of_nonneg _ _ (Real.log_nonneg hx), zero_mul]
  exact max_le hraw hR

end Daboussi
