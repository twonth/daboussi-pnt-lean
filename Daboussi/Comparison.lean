import Daboussi.FloorBands
import Daboussi.SmoothStepMass
import Daboussi.Balance

open Finset Filter MeasureTheory

namespace Daboussi

noncomputable def roughDensity (y : ℝ) : ℝ := (primorial y).totient / (primorial y : ℝ)

theorem roughDensity_pos (y : ℝ) : 0 < roughDensity y := by
  apply div_pos
  · exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (primorial_ne_zero y))
  · exact_mod_cast Nat.pos_of_ne_zero (primorial_ne_zero y)

/-- Periodic coprime counting, applied to each constant band of the smooth sum. -/
theorem a_le_density_stepMass {y : ℝ} (hy : 2 ≤ y) :
    a ≤ roughDensity y * stepMass y := by
  let K : ℝ := roughDensity y + (primorial y).totient
  apply a_le_of_affine_bound (C := K * ∑ j ∈ Ico 1 (primorial y), |smoothM j y|)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  apply (abs_M_le_bands hx hy).trans
  calc
    _ ≤ ∑ j ∈ Ico 1 (primorial y), |smoothM j y| *
        (roughDensity y * (x / j - x / (j + 1)) + K) := by
      apply sum_le_sum
      intro j hj
      have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Ico.mp hj).1
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact rough_interval_le (primorial_ne_zero y) (div_nonneg hx (by positivity))
        (div_le_div_of_nonneg_left hx hj0 (by linarith))
    _ = (roughDensity y * stepMass y) * x + K * ∑ j ∈ Ico 1 (primorial y), |smoothM j y| := by
      unfold stepMass
      simp only [mul_sum, sum_mul, ← sum_add_distrib]
      apply sum_congr rfl
      intro j hj
      ring

theorem roughDensity_euler_product {y : ℝ} (hy : 0 ≤ y) :
    roughDensity y * (∏ p ∈ smallPrimes y, (1 - (p : ℝ)⁻¹)⁻¹) = 1 := by
  have h := Nat.totient_eq_mul_prod_factors (primorial y)
  have hr : ((primorial y).totient : ℝ) = (primorial y : ℝ) *
      ∏ p ∈ (primorial y).primeFactors, (1 - (p : ℝ)⁻¹) := by
    have h' := congrArg (fun q : ℚ => (q : ℝ)) h
    simpa only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_prod, Rat.cast_sub,
      Rat.cast_one, Rat.cast_inv] using h'
  rw [primorial_primeFactors] at hr
  have hP : (primorial y : ℝ) ≠ 0 := by exact_mod_cast primorial_ne_zero y
  have hprod : (∏ p ∈ smallPrimes y, (1 - (p : ℝ)⁻¹)) ≠ 0 := by
    apply prod_ne_zero_iff.mpr
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast ((mem_smallPrimes hy p).mp hp).1.two_le
    have hi : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ (by linarith)).mpr (by linarith)
    linarith
  unfold roughDensity
  rw [hr]
  rw [mul_div_cancel_left₀ _ hP, prod_inv_distrib, mul_inv_cancel₀ hprod]

/-- Proposition 3 of the paper. -/
theorem smooth_comparison {y : ℝ} (hy : 2 ≤ y) :
    0 ≤ logMass (fun t => |smoothM t y| / t - a * psi t y / t) := by
  have hy0 : 0 ≤ y := by linarith
  have hbound := a_le_density_stepMass hy
  have hprod := roughDensity_euler_product hy0
  have hmass : a * logMass (fun t => psi t y / t) ≤ stepMass y := by
    rw [smooth_mass_eq_euler_product hy0]
    apply (mul_le_mul_iff_right₀ (roughDensity_pos y)).mp
    calc
      roughDensity y * (a * ∏ p ∈ smallPrimes y, (1 - (p : ℝ)⁻¹)⁻¹) =
          a * (roughDensity y * ∏ p ∈ smallPrimes y, (1 - (p : ℝ)⁻¹)⁻¹) := by ring
      _ = a := by rw [hprod, mul_one]
      _ ≤ _ := hbound
  have heq : (fun t => (|smoothM t y| / t - a * psi t y / t) / t) =
      (fun t => |smoothM t y| / t / t - a * (psi t y / t / t)) := by
    funext t; ring
  unfold logMass
  rw [heq, integral_sub (smooth_abs_mass_integrable hy0)
    ((smooth_mass_integrable hy0).const_mul a), integral_const_mul]
  change 0 ≤ logMass (fun t => |smoothM t y| / t) - a * logMass (fun t => psi t y / t)
  rw [smooth_abs_mass_eq_stepMass hy]
  linarith

theorem deficit_mass_le_excess_mass {y : ℝ} (hy : 2 ≤ y) :
    logMass (deficit y) ≤ logMass (excess y) :=
  balance_of_comparison y (excess_mass_integrable (by linarith))
    (deficit_mass_integrable (by linarith)) (smooth_comparison hy)

end Daboussi
