import Daboussi.ExcessMoment
import Daboussi.Reduction

open MeasureTheory Filter

namespace Daboussi

/-- The three ranges of §4, expressed as one pointwise majorant before integration. -/
theorem three_range_integral_bound {y ε A B : ℝ} (hy : 2 ≤ y) (hε : 0 < ε)
    (hA : 0 ≤ A)
    (hmoment : (∫ t in Set.Ioi (1 : ℝ), excess y t * Real.log t / t) ≤
      (Real.log y + A) * logMass (excess y))
    (hmass : logMass (excess y) ≤ B * Real.log y) :
    logMass (excess y) ≤ belowExcess y + ε * Real.log y + (belowExcess y + A * B) / ε := by
  let l := Real.log y
  let z := Real.exp ((1 + ε) * l)
  let f : ℝ → ℝ := fun t => excess y t / t
  let low : ℝ → ℝ := (Set.Ioc 1 y).indicator f
  let mid : ℝ → ℝ := (Set.Ioc y z).indicator (fun t : ℝ => t⁻¹)
  let w : ℝ → ℝ := fun t => excess y t * Real.log t / t - l * f t
  have hy0 : 0 < y := by linarith
  have hl : 0 < l := Real.log_pos (by linarith)
  have hz0 : 0 < z := Real.exp_pos _
  have hyz : y ≤ z := by
    change y ≤ Real.exp ((1 + ε) * Real.log y)
    rw [← Real.exp_log hy0]
    apply Real.exp_le_exp.mpr
    rw [Real.log_exp]
    nlinarith
  have hlogz : Real.log z = (1 + ε) * l := Real.log_exp _
  have hf : IntegrableOn f (Set.Ioi 1) := excess_mass_integrable (by linarith)
  have hlow : IntegrableOn low (Set.Ioi 1) := ((excess_density_global_integrable hy).indicator measurableSet_Ioc).restrict
  have hmid : IntegrableOn mid (Set.Ioi 1) := by
    apply Integrable.restrict
    apply (integrable_indicator_iff measurableSet_Ioc).mpr
    exact ((continuousOn_inv_Icc z).integrableOn_Icc).mono_set (by
      intro t ht; exact ⟨(show 1 ≤ y by linarith).trans ht.1.le, ht.2⟩)
  have hw : IntegrableOn w (Set.Ioi 1) := (excess_moment_integrable hy).sub (hf.const_mul l)
  have hlo : (∫ t in Set.Ioi (1 : ℝ), low t) = belowExcess y := by
    dsimp only [low]
    rw [setIntegral_indicator measurableSet_Ioc]
    have he : Set.Ioi (1 : ℝ) ∩ Set.Ioc 1 y = Set.Ioc 1 y := Set.inter_eq_right.mpr (fun t ht => ht.1)
    rw [he]
    exact (intervalIntegral.integral_of_le (by linarith : 1 ≤ y)).symm
  have hmi : (∫ t in Set.Ioi (1 : ℝ), mid t) = ε * l := by
    dsimp only [mid]
    rw [setIntegral_indicator measurableSet_Ioc]
    have he : Set.Ioi (1 : ℝ) ∩ Set.Ioc y z = Set.Ioc y z :=
      Set.inter_eq_right.mpr (fun t ht => (show 1 < y by linarith).trans ht.1)
    rw [he, ← intervalIntegral.integral_of_le hyz, integral_inv_of_pos hy0 hz0,
      Real.log_div hz0.ne' hy0.ne', hlogz]
    dsimp [l]; ring
  have hpoint : ∀ t ∈ Set.Ioi (1 : ℝ), ε * l * f t ≤
      (ε * l + l) * low t + (ε * l) * mid t + w t := by
    intro t ht
    have ht1 : 1 < t := ht
    have ht0 : 0 < t := by linarith
    have hf0 : 0 ≤ f t := div_nonneg (excess_nonneg y t) ht0.le
    have hwval : w t = (Real.log t - l) * f t := by dsimp [w, f]; ring
    rw [hwval]
    by_cases hty : t ≤ y
    · have hlo' : low t = f t := Set.indicator_of_mem (show t ∈ Set.Ioc 1 y from ⟨ht1, hty⟩) _
      have hmi' : mid t = 0 := Set.indicator_of_notMem (by intro h; exact (not_lt_of_ge hty) h.1) _
      rw [hlo', hmi']
      nlinarith [Real.log_nonneg ht1.le]
    · have hyt : y < t := lt_of_not_ge hty
      have hlo' : low t = 0 := Set.indicator_of_notMem (by intro h; exact hty h.2) _
      rw [hlo', mul_zero, zero_add]
      by_cases htz : t ≤ z
      · have hmi' : mid t = t⁻¹ := Set.indicator_of_mem (show t ∈ Set.Ioc y z from ⟨hyt, htz⟩) _
        rw [hmi']
        have hlog : l ≤ Real.log t := Real.log_le_log hy0 hyt.le
        have hf1 : f t ≤ t⁻¹ := by
          simpa only [one_div] using div_le_div_of_nonneg_right (excess_le_one a_nonneg ht1.le) ht0.le
        have hmul := mul_le_mul_of_nonneg_left hf1 (mul_nonneg hε.le hl.le)
        nlinarith [mul_nonneg (sub_nonneg.mpr hlog) hf0]
      · have hmi' : mid t = 0 := Set.indicator_of_notMem (by intro h; exact htz h.2) _
        rw [hmi', mul_zero, zero_add]
        have hlog : (1 + ε) * l ≤ Real.log t := hlogz ▸ Real.log_le_log hz0 (le_of_not_ge htz)
        nlinarith [mul_nonneg (sub_nonneg.mpr hlog) hf0]
  have hi := integral_mono_ae (hf.const_mul (ε * l))
    (((hlow.const_mul (ε * l + l)).add (hmid.const_mul (ε * l))).add hw)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hpoint))
  simp only [Pi.add_apply] at hi
  have hisum : IntegrableOn (fun t => (ε * l + l) * low t + (ε * l) * mid t) (Set.Ioi 1) :=
    (hlow.const_mul (ε * l + l)).add (hmid.const_mul (ε * l))
  rw [integral_const_mul, integral_add hisum hw,
    integral_add (hlow.const_mul (ε * l + l)) (hmid.const_mul (ε * l)), integral_const_mul,
    integral_const_mul, hlo, hmi] at hi
  have hwint : (∫ t in Set.Ioi (1 : ℝ), w t) =
      (∫ t in Set.Ioi (1 : ℝ), excess y t * Real.log t / t) - l * logMass (excess y) := by
    exact (integral_sub (excess_moment_integrable hy) (hf.const_mul l)).trans
      (by rw [integral_const_mul]; rfl)
  rw [hwint] at hi
  change ε * l * logMass (excess y) ≤ _ at hi
  have hAB := mul_le_mul_of_nonneg_left hmass hA
  have hraw : ε * l * logMass (excess y) ≤
      ε * l * (belowExcess y + ε * l + (belowExcess y + A * B) / ε) := by
    have hc : ε * l * ((belowExcess y + A * B) / ε) = l * (belowExcess y + A * B) := by field_simp
    rw [mul_add, mul_add, hc]
    dsimp only [l] at *
    nlinarith only [hi, hmoment, hAB]
  exact (mul_le_mul_iff_right₀ (mul_pos hε hl)).mp hraw

end Daboussi
