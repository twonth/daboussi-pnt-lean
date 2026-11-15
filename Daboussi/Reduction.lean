import Daboussi.BelowCutoff
import Daboussi.Balance
import Daboussi.ExcessBootstrap

open Filter MeasureTheory
open scoped Topology

namespace Daboussi

noncomputable def belowExcess (y : ℝ) : ℝ :=
  ∫ t in (1 : ℝ)..y, excess y t / t

theorem excess_mass_nonneg (y : ℝ) : 0 ≤ logMass (excess y) := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact div_nonneg (excess_nonneg y t) (by exact le_trans (by norm_num) ht.le)

theorem fundamentalIntegral_nonneg {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ fundamentalIntegral x := by
  apply intervalIntegral.integral_nonneg hx
  intro t ht
  exact div_nonneg (le_max_right _ _) (by linarith [ht.1])

/-- The reduction immediately before §4: excess mass controls the Fundamental Lemma. -/
theorem fundamental_of_excess
    (hsmall : Tendsto (fun y => logMass (excess y) / Real.log y) atTop (nhds 0))
    (hcontrol : ∀ᶠ y in atTop, fundamentalIntegral y ≤ logMass (excess y) + a) :
    Tendsto (fun y => fundamentalIntegral y / Real.log y) atTop (nhds 0) := by
  have hlog : ∀ᶠ y : ℝ in atTop, 0 < Real.log y :=
    (eventually_gt_atTop 1).mono fun _ hy => Real.log_pos hy
  have hlim : Tendsto (fun y => (logMass (excess y) + a) / Real.log y)
      atTop (nhds 0) := by
    simpa only [add_div, add_zero] using
      hsmall.add (tendsto_const_nhds.div_atTop Real.tendsto_log_atTop)
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_ge_atTop (1 : ℝ), hlog] with y hy hl
    exact div_nonneg (fundamentalIntegral_nonneg hy) hl.le
  · filter_upwards [hcontrol, hlog] with y hy hl
    exact div_le_div_of_nonneg_right hy hl.le

/-- The final contradiction, once the disjoint-block lower bound is established. -/
theorem a_zero_of_fundamental
    (hfund : Tendsto (fun y => fundamentalIntegral y / Real.log y) atTop (nhds 0))
    (hblocks : 0 < a → ∃ c : ℝ, 0 < c ∧
      ∃ᶠ x in atTop, c ≤ fundamentalIntegral x / Real.log x) : a = 0 := by
  apply le_antisymm _ a_nonneg
  by_contra ha
  obtain ⟨c, hc, hfreq⟩ := hblocks (lt_of_not_ge ha)
  have hev := hfund.eventually (gt_mem_nhds hc)
  obtain ⟨x, hx, hx'⟩ := (hfreq.and_eventually hev).exists
  exact (not_lt_of_ge hx) hx'

/-- Explicit dependency interface for the manuscript's route.
All four hypotheses concern the actual functions defined from the Möbius function;
none is an alternative PNT theorem. All four inputs are proved in this development. -/
theorem main_from_paper_estimates
    (hbelow : Tendsto (fun y => belowExcess y / Real.log y) atTop (nhds 0))
    (hranges : ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ∀ᶠ y in atTop,
      logMass (excess y) ≤ belowExcess y + ε * Real.log y + (belowExcess y + C) / ε)
    (hcontrol : ∀ᶠ y in atTop, fundamentalIntegral y ≤ logMass (excess y) + a)
    (hblocks : 0 < a → ∃ c : ℝ, 0 < c ∧
      ∃ᶠ x in atTop, c ≤ fundamentalIntegral x / Real.log x) :
    Tendsto (fun x : ℝ => M x / x) atTop (nhds 0) := by
  obtain ⟨C, hC⟩ := hranges
  have he := excess_mass_small hbelow
    (Eventually.of_forall excess_mass_nonneg) hC
  exact main_of_a_eq_zero (a_zero_of_fundamental (fundamental_of_excess he hcontrol) hblocks)

end Daboussi
