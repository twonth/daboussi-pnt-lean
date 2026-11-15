import Daboussi.SmoothMass
import Daboussi.Limsup

open MeasureTheory Filter

namespace Daboussi

theorem measurable_smoothM (y : ℝ) : Measurable (fun t => smoothM t y) := by
  classical
  let f : ℕ → ℝ := fun N => ∑ n ∈ (Finset.Icc 1 N).filter (Smooth y),
    (ArithmeticFunction.moebius n : ℝ)
  change Measurable (fun t : ℝ => f ⌊t⌋₊)
  exact (measurable_of_countable f).comp Nat.measurable_floor

theorem smooth_abs_mass_integrable {y : ℝ} (hy : 0 ≤ y) :
    IntegrableOn (fun t => |smoothM t y| / t / t) (Set.Ioi 1) := by
  apply (smooth_mass_integrable hy).mono'
  · have hm : Measurable (fun t => |smoothM t y|) := by
      simpa only [Real.norm_eq_abs] using (measurable_smoothM y).norm
    exact (hm.div measurable_id |>.div measurable_id).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans zero_lt_one ht
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (div_nonneg (abs_nonneg _) ht0.le) ht0.le)]
    exact div_le_div_of_nonneg_right
      (div_le_div_of_nonneg_right (abs_smoothM_le_psi t y) ht0.le) ht0.le

theorem excess_mass_integrable {y : ℝ} (hy : 0 ≤ y) :
    IntegrableOn (fun t => excess y t / t) (Set.Ioi 1) := by
  have h := ((smooth_abs_mass_integrable hy).sub ((smooth_mass_integrable hy).const_mul a)).sup
    (integrable_zero ℝ ℝ (volume.restrict (Set.Ioi 1)))
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  change max (|smoothM t y| / t / t - a * (psi t y / t / t)) 0 = excess y t / t
  unfold excess
  rw [← max_div_div_right ht0.le, zero_div]
  congr 1
  ring

theorem deficit_mass_integrable {y : ℝ} (hy : 0 ≤ y) :
    IntegrableOn (fun t => deficit y t / t) (Set.Ioi 1) := by
  have h := (((smooth_mass_integrable hy).const_mul a).sub (smooth_abs_mass_integrable hy)).sup
    (integrable_zero ℝ ℝ (volume.restrict (Set.Ioi 1)))
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  change max (a * (psi t y / t / t) - |smoothM t y| / t / t) 0 = deficit y t / t
  unfold deficit
  rw [← max_div_div_right ht0.le, zero_div]
  congr 1
  ring

end Daboussi
