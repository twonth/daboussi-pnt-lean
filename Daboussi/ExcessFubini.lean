import Daboussi.ExcessSupport
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Filter

namespace Daboussi

noncomputable def excessTriangle (y : ℝ) (p : ℝ × ℝ) : ℝ :=
  if p.1 ≤ p.2 then excess y p.1 * (p.2⁻¹ * p.2⁻¹) else 0

theorem excessTriangle_integrable {y : ℝ} (hy : 2 ≤ y) :
    Integrable (excessTriangle y) ((volume.restrict (Set.Ioi 1)).prod (volume.restrict (Set.Ioi 1))) := by
  have hi := ((excess_global_integrable hy).restrict (s := Set.Ioi (1 : ℝ))).mul_prod
    (inv_sq_integrable (by norm_num : (0 : ℝ) < 1))
  exact hi.indicator (measurableSet_le measurable_fst measurable_snd)

theorem excessTriangle_integral_right (y : ℝ) {t : ℝ} (ht : 1 ≤ t) :
    (∫ x in Set.Ioi (1 : ℝ), excessTriangle y (t, x)) = excess y t / t := by
  have he : (fun x => excessTriangle y (t, x)) = (fun x => excess y t * tailKernel t x) := by
    funext x
    simp only [excessTriangle, tailKernel, Set.indicator, Set.mem_Ici]
    split_ifs <;> simp
  rw [he, integral_const_mul, tailKernel_mass ht, div_eq_mul_inv]

theorem excessTriangle_integral_left (y : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    (∫ t in Set.Ioi (1 : ℝ), excessTriangle y (t, x)) = (∫ t in 1..x, excess y t) / x / x := by
  have he : (fun t => excessTriangle y (t, x)) =
      (fun t => (Set.Iic x).indicator (excess y) t * (x⁻¹ * x⁻¹)) := by
    funext t
    simp only [excessTriangle, Set.indicator, Set.mem_Iic]
    split_ifs <;> simp
  rw [he, integral_mul_const, setIntegral_indicator measurableSet_Iic,
    intervalIntegral.integral_of_le hx]
  have hs : Set.Ioi (1 : ℝ) ∩ Set.Iic x = Set.Ioc 1 x := by ext t; rfl
  rw [hs]
  ring

theorem excess_average_integrable {y : ℝ} (hy : 2 ≤ y) :
    IntegrableOn (fun x => (∫ t in 1..x, excess y t) / x / x) (Set.Ioi 1) := by
  apply (excessTriangle_integrable hy).integral_prod_right.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact excessTriangle_integral_left y hx.le

/-- The second change of integration order in §4. -/
theorem excess_average_mass {y : ℝ} (hy : 2 ≤ y) :
    (∫ x in Set.Ioi (1 : ℝ), (∫ t in 1..x, excess y t) / x / x) = logMass (excess y) := by
  have h := integral_integral_swap (f := fun t x => excessTriangle y (t, x)) (excessTriangle_integrable hy)
  have hleft : (fun x => ∫ t in Set.Ioi (1 : ℝ), excessTriangle y (t, x)) =ᵐ[volume.restrict (Set.Ioi 1)]
      (fun x => (∫ t in 1..x, excess y t) / x / x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact excessTriangle_integral_left y hx.le
  have hright : (fun t => ∫ x in Set.Ioi (1 : ℝ), excessTriangle y (t, x)) =ᵐ[volume.restrict (Set.Ioi 1)]
      (fun t => excess y t / t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact excessTriangle_integral_right y ht.le
  rw [integral_congr_ae hleft, integral_congr_ae hright] at h
  exact h.symm

end Daboussi
