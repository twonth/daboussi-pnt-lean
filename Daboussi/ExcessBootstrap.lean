import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

/-!
The final three-range argument of §4, separated from its arithmetic inputs.
`L`, `N`, `T` are the masses below y, in [y,y^(1+ε)], and above y^(1+ε).
`W` is the logarithmically weighted tail. These lemmas have explicit hypotheses:
they do not assert that the manuscript's integrals satisfy those hypotheses.
-/

open Filter
open scoped Topology

namespace Daboussi

/-- Move the contribution below y to the other side of the centered moment bound. -/
theorem weighted_tail_bound {W B S L C l : ℝ}
    (hcentered : W - B ≤ C * S) (hbelow : B ≤ l * L)
    (hmass : S ≤ l) (hC : 0 ≤ C) :
    W ≤ l * L + C * l := by
  have := mul_le_mul_of_nonneg_left hmass hC
  linarith

/-- Quantitative three-range estimate; the constant already absorbs the O(log y) bound. -/
theorem three_range_bound {S L N T W C l ε : ℝ}
    (hl : 0 < l) (hε : 0 < ε)
    (hsplit : S ≤ L + N + T)
    (hnear : N ≤ ε * l)
    (hfar : ε * l * T ≤ W)
    (hweighted : W ≤ l * L + C * l) :
    S ≤ L + ε * l + (L + C) / ε := by
  have ht : ε * T ≤ L + C := by
    nlinarith [hfar.trans hweighted]
  have ht' : T ≤ (L + C) / ε := (le_div_iff₀ hε).mpr (by nlinarith)
  linarith

/-- Let ε decrease only after taking the limit in the scale parameter. -/
theorem three_range_limit {S L R : ℝ → ℝ}
    (hL : Tendsto L atTop (nhds 0))
    (hR : Tendsto R atTop (nhds 0))
    (hS : ∀ᶠ y in atTop, 0 ≤ S y)
    (hbound : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ y in atTop, S y ≤ L y + ε + (L y + R y) / ε) :
    Tendsto S atTop (nhds 0) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    filter_upwards [hS] with y hy
    exact hb.trans_le hy
  · intro b hb
    have hε : 0 < b / 2 := by linarith
    have hlim : Tendsto (fun y => L y + b / 2 + (L y + R y) / (b / 2))
        atTop (nhds (b / 2)) := by
      convert (hL.add_const (b / 2)).add ((hL.add hR).div_const (b / 2)) using 1 <;> simp
    have hu := hlim.eventually (gt_mem_nhds (show b / 2 < b by linarith))
    filter_upwards [hbound (b / 2) hε, hu] with y hy hy'
    exact hy.trans_lt hy'

/-- The paper's O(log y)-to-o(log y) upgrade, given its three integral estimates. -/
theorem excess_mass_small {S L : ℝ → ℝ} {C : ℝ}
    (hL : Tendsto (fun y => L y / Real.log y) atTop (nhds 0))
    (hS : ∀ᶠ y in atTop, 0 ≤ S y)
    (hbound : ∀ ε : ℝ, 0 < ε → ∀ᶠ y in atTop,
      S y ≤ L y + ε * Real.log y + (L y + C) / ε) :
    Tendsto (fun y => S y / Real.log y) atTop (nhds 0) := by
  have hlog : ∀ᶠ y : ℝ in atTop, 0 < Real.log y :=
    (eventually_gt_atTop 1).mono fun _ hy => Real.log_pos hy
  have hR : Tendsto (fun y : ℝ => C / Real.log y) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  apply three_range_limit hL hR
  · filter_upwards [hS, hlog] with y hy hl
    exact div_nonneg hy hl.le
  · intro ε hε
    filter_upwards [hbound ε hε, hlog] with y hy hl
    calc
      S y / Real.log y ≤ (L y + ε * Real.log y + (L y + C) / ε) / Real.log y :=
        div_le_div_of_nonneg_right hy hl.le
      _ = L y / Real.log y + ε + (L y / Real.log y + C / Real.log y) / ε := by
        field_simp
        <;> ring

end Daboussi
