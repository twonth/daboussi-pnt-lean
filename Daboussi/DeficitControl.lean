import Daboussi.Comparison
import Daboussi.Blocks

open MeasureTheory Filter

namespace Daboussi

theorem fundamental_le_deficit_mass {y : ℝ} (hy : 2 ≤ y) :
    fundamentalIntegral y ≤ logMass (deficit y) + a := by
  have hy1 : 1 ≤ y := by linarith
  have hi := (deficit_mass_integrable (show 0 ≤ y by linarith)).add
    ((inv_sq_integrable (by norm_num : (0 : ℝ) < 1)).const_mul a)
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioi (1 : ℝ))]
      (fun t => deficit y t / t + a * (t⁻¹ * t⁻¹)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact add_nonneg (div_nonneg (le_max_right _ _) (le_trans zero_le_one ht.le))
      (mul_nonneg a_nonneg (mul_self_nonneg _))
  have hsub : Set.Ioc (1 : ℝ) y ⊆ Set.Ioi 1 := fun _ ht => ht.1
  change (∫ t in 1..y, fundamentalDensity t) ≤ _
  rw [intervalIntegral.integral_of_le hy1]
  calc
    _ ≤ ∫ t in Set.Ioc (1 : ℝ) y, (deficit y t / t + a * (t⁻¹ * t⁻¹)) := by
      apply setIntegral_mono_on ((fundamental_density_integrable y).mono_set Set.Ioc_subset_Icc_self)
        (hi.mono_set hsub) measurableSet_Ioc
      intro t ht
      have hb := div_le_div_of_nonneg_right (deficit_below ht.1.le ht.2)
        (show 0 ≤ t by linarith [ht.1])
      unfold fundamentalDensity
      have he : (max (a - |M t| / t) 0 - a / t) / t =
          max (a - |M t| / t) 0 / t - a * (t⁻¹ * t⁻¹) := by ring
      rw [he] at hb
      dsimp only [Pi.add_apply]
      linarith
    _ ≤ ∫ t in Set.Ioi (1 : ℝ), (deficit y t / t + a * (t⁻¹ * t⁻¹)) :=
      setIntegral_mono_set hi hnonneg (Eventually.of_forall hsub)
    _ = _ := by
      rw [integral_add (deficit_mass_integrable (by linarith))
        ((inv_sq_integrable (by norm_num : (0 : ℝ) < 1)).const_mul a),
        integral_const_mul, inv_sq_integral (by norm_num : (0 : ℝ) < 1)]
      simp [logMass]

/-- The final bound in §3, including the integrated floor correction. -/
theorem deficit_control :
    ∀ᶠ y in atTop, fundamentalIntegral y ≤ logMass (excess y) + a := by
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with y hy
  exact (fundamental_le_deficit_mass hy).trans (add_le_add (deficit_mass_le_excess_mass hy) le_rfl)

end Daboussi
