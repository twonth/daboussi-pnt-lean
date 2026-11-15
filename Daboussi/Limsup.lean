import Daboussi.Basic
import Mathlib.Topology.Order.LiminfLimsup

open Filter
open scoped Topology

namespace Daboussi

theorem normalized_M_nonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ |M x| / x := by
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  exact div_nonneg (abs_nonneg _) hx

theorem normalized_M_le_one : ∀ᶠ x : ℝ in atTop, |M x| / x ≤ 1 := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (div_le_one hx).mpr (abs_M_le_self hx.le)

theorem normalized_M_bounded : atTop.IsBoundedUnder (· ≤ ·) (fun x : ℝ => |M x| / x) :=
  ⟨1, normalized_M_le_one⟩

theorem a_nonneg : 0 ≤ a := by
  apply le_limsup_of_le normalized_M_bounded
  intro b hb
  obtain ⟨x, hx, hx'⟩ := (normalized_M_nonneg.and hb).exists
  exact hx.trans hx'

theorem a_le_one : a ≤ 1 := by
  have hbelow : atTop.IsBoundedUnder (· ≥ ·) (fun x : ℝ => |M x| / x) :=
    ⟨0, normalized_M_nonneg⟩
  exact limsup_le_of_le hbelow.isCoboundedUnder_le normalized_M_le_one

theorem eventually_normalized_M_lt {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, |M x| / x < a + ε := by
  exact eventually_lt_add_pos_of_limsup_le normalized_M_bounded (le_refl a) hε

/-- Converting `a = 0` to the manuscript's main conclusion. -/
theorem main_of_a_eq_zero (ha : a = 0) :
    Tendsto (fun x : ℝ => M x / x) atTop (nhds 0) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    have he := eventually_normalized_M_lt (show 0 < -b by linarith)
    filter_upwards [he, eventually_gt_atTop (0 : ℝ)] with x hx hpos
    rw [ha, zero_add] at hx
    have habs : |M x / x| < -b := by simpa [abs_div, abs_of_pos hpos] using hx
    linarith [(abs_lt.mp habs).1]
  · intro b hb
    have he := eventually_normalized_M_lt hb
    filter_upwards [he, eventually_gt_atTop (0 : ℝ)] with x hx hpos
    rw [ha, zero_add] at hx
    exact (div_le_div_of_nonneg_right (le_abs_self _) hpos.le).trans_lt hx

end Daboussi
