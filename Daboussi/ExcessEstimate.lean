import Daboussi.ThreeRanges
import Daboussi.MertensCoefficient
import Daboussi.BelowIntegral

open Filter MeasureTheory
open scoped Topology

namespace Daboussi

theorem excess_mass_le_product {y : ℝ} (hy : 2 ≤ y) :
    logMass (excess y) ≤ ∏ p ∈ smallPrimes y, (1 - (p : ℝ)⁻¹)⁻¹ := by
  rw [← smooth_mass_eq_euler_product (show 0 ≤ y by linarith)]
  apply integral_mono_ae (excess_mass_integrable (by linarith)) (smooth_mass_integrable (by linarith))
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := zero_lt_one.trans ht
  apply div_le_div_of_nonneg_right _ ht0.le
  unfold excess
  apply max_le
  · have hm := div_le_div_of_nonneg_right (abs_smoothM_le_psi t y) ht0.le
    have hp := div_nonneg (mul_nonneg a_nonneg (psi_nonneg t y)) ht0.le
    linarith
  · exact div_nonneg (psi_nonneg t y) ht0.le

/-- The complete three-range estimate from §4. -/
theorem smooth_excess_three_ranges :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ∀ᶠ y in atTop,
      logMass (excess y) ≤ belowExcess y + ε * Real.log y + (belowExcess y + C) / ε := by
  obtain ⟨A, hA, hcoeff⟩ := mertens_coefficient_upper
  obtain ⟨B, hB, hprod⟩ := mertens_product_upper
  refine ⟨A * B, fun ε hε => ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with y hy
  apply three_range_integral_bound hy hε hA.le
  · exact (excess_moment_le_coefficient hy).trans
      (mul_le_mul_of_nonneg_right (hcoeff y hy (primorial y)) (excess_mass_nonneg y))
  · exact (excess_mass_le_product hy).trans (hprod y hy)

/-- Equation (excess-goal) of the paper. -/
theorem smooth_excess_small :
    Tendsto (fun y => logMass (excess y) / Real.log y) atTop (nhds 0) := by
  obtain ⟨C, hC⟩ := smooth_excess_three_ranges
  exact excess_mass_small below_excess_small (Eventually.of_forall excess_mass_nonneg) hC

end Daboussi
