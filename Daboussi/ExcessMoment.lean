import Daboussi.ExcessFubini
import Daboussi.ExcessScaling

open Finset MeasureTheory Filter ArithmeticFunction

namespace Daboussi

theorem excess_recurrence_fixed {y : ℝ} (hy : 2 ≤ y) {x : ℝ} (hx : 1 ≤ x) :
    excess y x * Real.log x ≤
      (∑ d ∈ Icc 1 (primorial y), restrictSmooth y vonMangoldt d / d * excess y (x / d)) +
        (∫ t in 1..x, excess y t) / x := by
  by_cases hP : (primorial y : ℝ) ≤ x
  · rw [excess_eq_zero_above hy hP, zero_mul]
    apply add_nonneg
    · exact sum_nonneg (fun d _ => mul_nonneg (div_nonneg (smoothLambda_nonneg y d) (Nat.cast_nonneg _))
        (excess_nonneg _ _))
    · exact div_nonneg (intervalIntegral.integral_nonneg hx (fun t _ => excess_nonneg y t)) (by linarith)
  · apply (excess_recurrence y hx).trans
    apply add_le_add _ le_rfl
    apply sum_le_sum_of_subset_of_nonneg
    · exact Icc_subset_Icc_right (Nat.floor_le_of_le (le_of_lt (lt_of_not_ge hP)))
    · intro d _ _
      exact mul_nonneg (div_nonneg (smoothLambda_nonneg y d) (Nat.cast_nonneg _)) (excess_nonneg _ _)

/-- Integrating the recurrence, with finite support justifying a finite prime-power sum. -/
theorem excess_moment_le_coefficient {y : ℝ} (hy : 2 ≤ y) :
    (∫ t in Set.Ioi (1 : ℝ), excess y t * Real.log t / t) ≤
      (1 + ∑ d ∈ Icc 1 (primorial y), restrictSmooth y vonMangoldt d / d) * logMass (excess y) := by
  have hi (d : ℕ) (hd : d ∈ Icc 1 (primorial y)) :
      IntegrableOn (fun x => (restrictSmooth y vonMangoldt d / d) * (excess y (x / d) / x)) (Set.Ioi 1) :=
    (scaled_excess_integrable hy (by exact_mod_cast (mem_Icc.mp hd).1)).const_mul _
  have hsum : IntegrableOn (fun x => ∑ d ∈ Icc 1 (primorial y),
      (restrictSmooth y vonMangoldt d / d) * (excess y (x / d) / x)) (Set.Ioi 1) :=
    integrable_finset_sum _ hi
  have hbound : (∫ t in Set.Ioi (1 : ℝ), excess y t * Real.log t / t) ≤
      ∫ x in Set.Ioi (1 : ℝ), ((∑ d ∈ Icc 1 (primorial y),
        (restrictSmooth y vonMangoldt d / d) * (excess y (x / d) / x)) +
          (∫ t in 1..x, excess y t) / x / x) := by
    apply integral_mono_ae (excess_moment_integrable hy) (hsum.add (excess_average_integrable hy))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have h := div_le_div_of_nonneg_right (excess_recurrence_fixed hy hx.le) (le_trans zero_le_one hx.le)
    simpa only [add_div, sum_div, mul_div_assoc, Pi.add_apply] using h
  apply hbound.trans_eq
  rw [integral_add hsum (excess_average_integrable hy), integral_finset_sum _ hi, excess_average_mass hy]
  simp_rw [integral_const_mul]
  have he : (∑ d ∈ Icc 1 (primorial y), (restrictSmooth y vonMangoldt d / d) *
      (∫ x in Set.Ioi (1 : ℝ), excess y (x / d) / x)) =
      (∑ d ∈ Icc 1 (primorial y), restrictSmooth y vonMangoldt d / d) * logMass (excess y) := by
    rw [sum_mul]
    apply sum_congr rfl
    intro d hd
    rw [scaled_excess_mass hy (by exact_mod_cast (mem_Icc.mp hd).1)]
  rw [he]
  ring

end Daboussi
