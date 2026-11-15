import Daboussi.ExcessSupport
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

open MeasureTheory

namespace Daboussi

theorem integral_eq_Ioi_one {f : ℝ → ℝ} (hf : ∀ x < 1, f x = 0) :
    (∫ x, f x) = ∫ x in Set.Ioi (1 : ℝ), f x := by
  have h := setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (μ := volume)
    (f := f) MeasurableSet.univ (Set.subset_univ (Set.Ici (1 : ℝ))) (by
      intro x hx
      exact hf x (lt_of_not_ge hx.2))
  simpa only [Measure.restrict_univ, integral_Ici_eq_integral_Ioi] using h

theorem excess_density_global_integrable {y : ℝ} (hy : 2 ≤ y) :
    Integrable (fun t => excess y t / t) := by
  simpa only [div_eq_mul_inv] using excess_mul_global_integrable hy (continuousOn_inv_Icc _)

theorem scaled_excess_eq {d : ℝ} (hd : 0 < d) (y x : ℝ) :
    excess y (x / d) / x = d⁻¹ * (excess y (d⁻¹ * x) / (d⁻¹ * x)) := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [show d⁻¹ * x = x / d by ring]
    field_simp

theorem scaled_excess_integrable {y d : ℝ} (hy : 2 ≤ y) (hd : 1 ≤ d) :
    IntegrableOn (fun x => excess y (x / d) / x) (Set.Ioi 1) := by
  have hd0 : 0 < d := by linarith
  have hi := (integrable_comp_mul_left_iff (fun t => excess y t / t)
    (inv_ne_zero hd0.ne')).mpr (excess_density_global_integrable hy)
  have he : (fun x => excess y (x / d) / x) =
      (fun x => d⁻¹ * (excess y (d⁻¹ * x) / (d⁻¹ * x))) := funext (scaled_excess_eq hd0 y)
  rw [he]
  exact (hi.const_mul _).restrict

/-- The substitution x = d t in the prime-power contribution. -/
theorem scaled_excess_mass {y d : ℝ} (hy : 2 ≤ y) (hd : 1 ≤ d) :
    (∫ x in Set.Ioi (1 : ℝ), excess y (x / d) / x) = logMass (excess y) := by
  have hd0 : 0 < d := by linarith
  have hz : ∀ x < 1, excess y (x / d) / x = 0 := by
    intro x hx
    rw [excess_eq_zero_below ((div_lt_one hd0).mpr (hx.trans_le hd)) y, zero_div]
  rw [← integral_eq_Ioi_one hz]
  have he : (fun x => excess y (x / d) / x) =
      (fun x => d⁻¹ * (excess y (d⁻¹ * x) / (d⁻¹ * x))) := funext (scaled_excess_eq hd0 y)
  rw [he, integral_const_mul, Measure.integral_comp_mul_left (fun t => excess y t / t) d⁻¹,
    inv_inv, abs_of_pos hd0, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hd0.ne', one_mul]
  exact integral_eq_Ioi_one (fun x hx => by rw [excess_eq_zero_below hx y, zero_div])

end Daboussi
