import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

open MeasureTheory Filter

namespace Daboussi

noncomputable def tailKernel (c t : ℝ) : ℝ :=
  (Set.Ici c).indicator (fun t : ℝ => t⁻¹ * t⁻¹) t

theorem tailKernel_nonneg (c t : ℝ) : 0 ≤ tailKernel c t := by
  unfold tailKernel
  exact Set.indicator_nonneg (fun t _ => mul_self_nonneg _) t

theorem inv_sq_rpow : (fun t : ℝ => t ^ (-2 : ℝ)) = (fun t : ℝ => t⁻¹ * t⁻¹) := by
  funext t
  rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg_natCast]
  simp [zpow_neg, pow_two]

theorem inv_sq_integrable {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => t⁻¹ * t⁻¹) (Set.Ioi c) := by
  rw [← inv_sq_rpow]
  exact integrableOn_Ioi_rpow_of_lt (by norm_num) hc

theorem inv_sq_integral {c : ℝ} (hc : 0 < c) :
    (∫ t in Set.Ioi c, t⁻¹ * t⁻¹) = c⁻¹ := by
  rw [← inv_sq_rpow, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hc]
  norm_num [Real.rpow_neg_one]

theorem tailKernel_integrable {c : ℝ} (hc : 0 < c) : Integrable (tailKernel c) := by
  apply (integrable_indicator_iff measurableSet_Ici).mpr
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  exact inv_sq_integrable hc

theorem tailKernel_mass {c : ℝ} (hc : 1 ≤ c) :
    (∫ t in Set.Ioi (1 : ℝ), tailKernel c t) = c⁻¹ := by
  change (∫ t in Set.Ioi (1 : ℝ), (Set.Ici c).indicator (fun t : ℝ => t⁻¹ * t⁻¹) t) = c⁻¹
  rw [setIntegral_indicator measurableSet_Ici]
  rcases eq_or_lt_of_le hc with h | h
  · subst c
    have he : Set.Ioi (1 : ℝ) ∩ Set.Ici 1 = Set.Ioi 1 := by ext t; simp; intro h; exact h.le
    rw [he]
    exact inv_sq_integral (by norm_num)
  · have he : Set.Ioi (1 : ℝ) ∩ Set.Ici c = Set.Ici c := by
      apply Set.inter_eq_right.mpr
      intro t ht
      exact h.trans_le ht
    rw [he, integral_Ici_eq_integral_Ioi]
    exact inv_sq_integral (by linarith)

/-- Tonelli's argument for a nonnegative series, with the integrability conclusion
included explicitly instead of relying on the totalized Bochner integral. -/
theorem integrable_nonneg_series {ι : Type*} [Countable ι]
    {F : ι → ℝ → ℝ} {g : ℝ → ℝ} {μ : Measure ℝ}
    (hF : ∀ i, Integrable (F i) μ)
    (hpos : ∀ i t, 0 ≤ F i t)
    (hsum : ∀ t, HasSum (fun i => F i t) (g t))
    (hg : AEStronglyMeasurable g μ)
    (hmass : Summable (fun i => ∫ t, F i t ∂μ)) : Integrable g μ := by
  have hgn : ∀ t, 0 ≤ g t := fun t => le_of_tendsto_of_tendsto'
    tendsto_const_nhds (hsum t) (fun s => Finset.sum_nonneg fun i _ => hpos i t)
  refine ⟨hg, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hgn)]
  have heq : (fun t => ENNReal.ofReal (g t)) =
      (fun t => ∑' i, ENNReal.ofReal (F i t)) := by
    funext t
    rw [← (hsum t).tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun i => hpos i t) (hsum t).summable]
  rw [heq, lintegral_tsum (fun i => (hF i).aestronglyMeasurable.aemeasurable.ennreal_ofReal)]
  have he (i : ι) : (∫⁻ t, ENNReal.ofReal (F i t) ∂μ) = ENNReal.ofReal (∫ t, F i t ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal (hF i) (Eventually.of_forall (hpos i))).symm
  simp_rw [he]
  exact lt_top_iff_ne_top.mpr hmass.tsum_ofReal_ne_top

end Daboussi
