import Daboussi.Reduction
import Daboussi.IntegralRegularity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open Filter MeasureTheory
open scoped Topology

namespace Daboussi

theorem below_excess_eventual_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ᶠ y in atTop, belowExcess y ≤ C + ε * Real.log y := by
  have hhalf : 0 < ε / 2 := by linarith
  have hlim : Tendsto (fun t : ℝ => a / t) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hev := (eventually_normalized_M_lt hhalf).and
    (hlim.eventually (gt_mem_nhds hhalf))
  obtain ⟨T, hT⟩ := eventually_atTop.mp hev
  let U := max 1 T
  have hU : 1 ≤ U := le_max_left _ _
  have hU0 : 0 < U := by linarith
  refine ⟨Real.log U, ?_⟩
  filter_upwards [eventually_ge_atTop U] with y hy
  have hy1 : 1 ≤ y := hU.trans hy
  have hy0 : 0 < y := hU0.trans_le hy
  have hE1 : IntervalIntegrable (fun t => excess y t / t) volume 1 U :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hU).mpr (excess_log_integrable y U)
  have hE2 : IntervalIntegrable (fun t => excess y t / t) volume U y :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hy).mpr
      ((excess_log_integrable y y).mono_set (Set.Icc_subset_Icc_left hU))
  have hInv1 : IntervalIntegrable (fun t : ℝ => t⁻¹) volume 1 U :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hU).mpr
      (continuousOn_inv_Icc U).integrableOn_Icc
  have hInv2 : IntervalIntegrable (fun t : ℝ => t⁻¹) volume U y :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hy).mpr
      ((continuousOn_inv_Icc y).integrableOn_Icc.mono_set (Set.Icc_subset_Icc_left hU))
  have hlow : (∫ t in (1 : ℝ)..U, excess y t / t) ≤ Real.log U := by
    calc
      _ ≤ ∫ t in (1 : ℝ)..U, t⁻¹ := by
        apply intervalIntegral.integral_mono_on hU hE1 hInv1
        intro t ht
        simpa only [one_div] using
          div_le_div_of_nonneg_right (excess_le_one a_nonneg ht.1) (by linarith [ht.1])
      _ = _ := by rw [integral_inv_of_pos (by norm_num) hU0, div_one]
  have hhigh : (∫ t in U..y, excess y t / t) ≤ ε * (Real.log y - Real.log U) := by
    calc
      _ ≤ ∫ t in U..y, ε * t⁻¹ := by
        apply intervalIntegral.integral_mono_on hy hE2 (hInv2.const_mul ε)
        intro t ht
        have ht1 := hU.trans ht.1
        have htT : T ≤ t := (le_max_right 1 T).trans ht.1
        have hh := hT t htT
        have hsmall := excess_below ht1 ht.2 hhalf.le hh.1.le
        have hEt : excess y t ≤ ε := by linarith [hh.2]
        simpa only [div_eq_mul_inv] using
          div_le_div_of_nonneg_right hEt (by linarith [ht1])
      _ = _ := by
        rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hU0 hy0,
          Real.log_div (ne_of_gt hy0) (ne_of_gt hU0)]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hE1 hE2
  unfold belowExcess
  rw [← hsplit]
  have hlogU : 0 ≤ Real.log U := Real.log_nonneg hU
  nlinarith

/-- §4, equation (below), proved by the paper's fixed-T argument. -/
theorem below_excess_small :
    Tendsto (fun y => belowExcess y / Real.log y) atTop (nhds 0) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with y hy
    have hn : 0 ≤ belowExcess y := by
      apply intervalIntegral.integral_nonneg hy.le
      intro t ht
      exact div_nonneg (excess_nonneg y t) (by linarith [ht.1])
    exact hb.trans_le (div_nonneg hn (Real.log_pos hy).le)
  · intro b hb
    obtain ⟨C, hC⟩ := below_excess_eventual_bound (show 0 < b / 2 by linarith)
    have hlim : Tendsto (fun y : ℝ => C / Real.log y + b / 2) atTop (nhds (b / 2)) := by
      simpa using (tendsto_const_nhds.div_atTop Real.tendsto_log_atTop).add_const (b / 2)
    have hev := hlim.eventually (gt_mem_nhds (show b / 2 < b by linarith))
    filter_upwards [hC, hev, eventually_gt_atTop (1 : ℝ)] with y hy hy' hy1
    have hl := Real.log_pos hy1
    calc
      belowExcess y / Real.log y ≤ (C + b / 2 * Real.log y) / Real.log y :=
        div_le_div_of_nonneg_right hy hl.le
      _ = C / Real.log y + b / 2 := by field_simp
      _ < b := hy'

end Daboussi
