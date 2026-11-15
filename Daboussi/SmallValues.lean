import Daboussi.Steps
import Daboussi.SignedIntegral
import Daboussi.IntegralRegularity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open Finset MeasureTheory

namespace Daboussi

theorem M_div_sq_integrable (Y : ℝ) :
    IntegrableOn (fun t => M t / t / t) (Set.Icc 1 Y) := by
  have hm : IntegrableOn M (Set.Icc 1 Y) := summatory_integrable (fun n => (ArithmeticFunction.moebius n : ℝ)) Y
  have hm' := hm.mul_continuousOn (continuousOn_inv_Icc Y) isCompact_Icc
  simpa only [div_eq_mul_inv] using
    hm'.mul_continuousOn (continuousOn_inv_Icc Y) isCompact_Icc

theorem signed_interval_bound {X Y : ℝ} (hX : 1 ≤ X) (hXY : X ≤ Y) :
    |∫ t in X..Y, M t / t / t| < 6 := by
  have hY := hX.trans hXY
  have hi1 : IntervalIntegrable (fun t => M t / t / t) volume 1 X :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hX).mpr (M_div_sq_integrable X)
  have hi2 : IntervalIntegrable (fun t => M t / t / t) volume X Y :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hXY).mpr
      ((M_div_sq_integrable Y).mono_set (Set.Icc_subset_Icc_left hX))
  have hadd := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  have h1 := signed_integral_bound X hX
  have h2 := signed_integral_bound Y hY
  have htri := abs_add_le (∫ t in (1 : ℝ)..Y, M t / t / t)
    (-(∫ t in (1 : ℝ)..X, M t / t / t))
  have heq : (∫ t in (1 : ℝ)..Y, M t / t / t) + -(∫ t in (1 : ℝ)..X, M t / t / t) =
      ∫ t in X..Y, M t / t / t := by linarith
  rw [heq, abs_neg] at htri
  linarith

theorem exists_small_value (ha : 0 < a) {X : ℝ} (hX : 1 ≤ X) :
    ∃ u ∈ Set.Icc X (Real.exp (12 / a) * X), |M u| ≤ a / 2 * u := by
  let B := Real.exp (12 / a)
  have hX0 : 0 < X := by linarith
  have hB : 1 < B := Real.one_lt_exp_iff.mpr (div_pos (by norm_num) ha)
  have hXY : X ≤ B * X := by nlinarith
  have hY : 1 ≤ B * X := hX.trans hXY
  have hY0 : 0 < B * X := by positivity
  by_contra h
  push Not at h
  have hlarge : ∀ t ∈ Set.Icc X (B * X), a / 2 * t < |M t| := h
  have hnz : ∀ t ∈ Set.Icc X (B * X), M t ≠ 0 := by
    intro t ht hz
    have hh := hlarge t ht
    have ht0 : 0 < t := hX0.trans_le ht.1
    rw [hz, abs_zero] at hh
    have : 0 < a / 2 * t := mul_pos (by linarith) ht0
    linarith
  have hmi : IntervalIntegrable (fun t => M t / t / t) volume X (B * X) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hXY).mpr
      ((M_div_sq_integrable (B * X)).mono_set (Set.Icc_subset_Icc_left hX))
  have hinv : IntervalIntegrable (fun t : ℝ => t⁻¹) volume X (B * X) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hXY).mpr
      ((continuousOn_inv_Icc (B * X)).integrableOn_Icc.mono_set (Set.Icc_subset_Icc_left hX))
  have hbase : (∫ t in X..(B * X), (a / 2) * t⁻¹) = 6 := by
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hX0 hY0,
      mul_div_cancel_right₀ B hX0.ne']
    change a / 2 * Real.log (Real.exp (12 / a)) = 6
    rw [Real.log_exp]
    field_simp
    <;> ring
  have hbnd := signed_interval_bound hX hXY
  rcases M_constant_sign hX0.le hXY hnz with hpos | hneg
  · have hlow : (∫ t in X..(B * X), (a / 2) * t⁻¹) ≤
        ∫ t in X..(B * X), M t / t / t := by
      apply intervalIntegral.integral_mono_on hXY (hinv.const_mul _) hmi
      intro t ht
      have ht0 := hX0.trans_le ht.1
      have hh := (hlarge t ht).le
      rw [abs_of_pos (hpos t ht)] at hh
      have hd : a / 2 ≤ M t / t := (le_div_iff₀ ht0).mpr hh
      simpa only [div_eq_mul_inv] using div_le_div_of_nonneg_right hd ht0.le
    rw [hbase] at hlow
    exact (not_le_of_gt hbnd) (hlow.trans (le_abs_self _))
  · have hlow : (∫ t in X..(B * X), (a / 2) * t⁻¹) ≤
        ∫ t in X..(B * X), -(M t / t / t) := by
      apply intervalIntegral.integral_mono_on hXY (hinv.const_mul _) hmi.neg
      intro t ht
      have ht0 := hX0.trans_le ht.1
      have hh := (hlarge t ht).le
      rw [abs_of_neg (hneg t ht)] at hh
      have hd : a / 2 ≤ -M t / t := (le_div_iff₀ ht0).mpr hh
      simpa only [div_eq_mul_inv, neg_mul, Pi.neg_apply] using div_le_div_of_nonneg_right hd ht0.le
    rw [hbase, intervalIntegral.integral_neg] at hlow
    exact (not_le_of_gt hbnd) (hlow.trans (neg_le_abs _))

end Daboussi
