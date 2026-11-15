import Daboussi.SmallValues
import Daboussi.Reduction
import Daboussi.GeometricAveraging
import Mathlib.Analysis.SpecificLimits.Basic

open Filter MeasureTheory
open scoped Topology

namespace Daboussi

noncomputable def fundamentalDensity (t : ℝ) : ℝ := max (a - |M t| / t) 0 / t

theorem fundamental_density_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ fundamentalDensity t :=
  div_nonneg (le_max_right _ _) ht

theorem fundamental_density_integrable (Y : ℝ) :
    IntegrableOn fundamentalDensity (Set.Icc 1 Y) := by
  have hm : IntegrableOn (fun t => |M t|) (Set.Icc 1 Y) :=
    (summatory_integrable (fun n => (ArithmeticFunction.moebius n : ℝ)) Y).abs
  have hm' := hm.mul_continuousOn (continuousOn_inv_Icc Y) isCompact_Icc
  have hc : IntegrableOn (fun _ : ℝ => a) (Set.Icc 1 Y) := continuousOn_const.integrableOn_Icc
  have hg : IntegrableOn (fun t => max (a - |M t| / t) 0) (Set.Icc 1 Y) := by
    have heq : (fun t => max (a - |M t| / t) 0) =
        ((fun _ => a) - (fun t => |M t| * t⁻¹)) ⊔ (0 : ℝ → ℝ) := by
      funext t
      simp [div_eq_mul_inv]
    rw [heq]
    exact (hc.sub hm').sup (integrable_zero ℝ ℝ (volume.restrict (Set.Icc 1 Y)))
  change IntegrableOn (fun t => max (a - |M t| / t) 0 / t) (Set.Icc 1 Y)
  simpa only [div_eq_mul_inv] using
    hg.mul_continuousOn (continuousOn_inv_Icc Y) isCompact_Icc

theorem fundamental_density_interval {X Y : ℝ} (hX : 1 ≤ X) (hXY : X ≤ Y) :
    IntervalIntegrable fundamentalDensity volume X Y :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le hXY).mpr
    ((fundamental_density_integrable Y).mono_set (Set.Icc_subset_Icc_left hX))

theorem fundamental_increment {X Y : ℝ} (hX : 1 ≤ X) (hXY : X ≤ Y) :
    fundamentalIntegral X + (∫ t in X..Y, fundamentalDensity t) = fundamentalIntegral Y := by
  exact intervalIntegral.integral_add_adjacent_intervals
    (fundamental_density_interval le_rfl hX) (fundamental_density_interval hX hXY)

theorem deficit_on_block (ha : 0 < a) {X : ℝ} (hX : 8 / a ≤ X) :
    a / 4 * Real.log (1 + a / 8) ≤
      ∫ t in X..(2 * Real.exp (12 / a) * X), fundamentalDensity t := by
  have ha1 := a_le_one
  have hX1 : 1 ≤ X := by
    have h8 : 8 ≤ X * a := (div_le_iff₀ ha).mp hX
    have hXpos : 0 < X := lt_of_lt_of_le (div_pos (by norm_num) ha) hX
    nlinarith
  obtain ⟨u, hu, hsmall⟩ := exists_small_value ha hX1
  have hu0 : 0 < u := by linarith [hu.1]
  have hu8 : 1 ≤ a * u / 8 := by
    have : 8 ≤ X * a := (div_le_iff₀ ha).mp hX
    nlinarith [mul_le_mul_of_nonneg_left hu.1 ha.le]
  let v := u * (1 + a / 8)
  have huv : u ≤ v := by dsimp [v]; nlinarith
  have hB0 : 0 < Real.exp (12 / a) := Real.exp_pos _
  have hv : v ≤ 2 * Real.exp (12 / a) * X := by
    dsimp [v]
    nlinarith [hu.2]
  have hfar : X ≤ 2 * Real.exp (12 / a) * X := hu.1.trans (huv.trans hv)
  have hloc : ∀ t ∈ Set.Icc u v, a / 4 / t ≤ fundamentalDensity t := by
    intro t ht
    have ht0 := hu0.trans_le ht.1
    have hMt := local_smallness ha.le hu8 ht.1 ht.2 hsmall (M_change hu0.le ht.1)
    have hmdiv : |M t| / t ≤ 3 * a / 4 := (div_le_iff₀ ht0).mpr hMt
    apply div_le_div_of_nonneg_right _ ht0.le
    exact (show a / 4 ≤ a - |M t| / t by linarith).trans (le_max_left _ _)
  have hi : IntervalIntegrable fundamentalDensity volume u v :=
    fundamental_density_interval (hX1.trans hu.1) huv
  have hiInv : IntervalIntegrable (fun t : ℝ => t⁻¹) volume u v := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le huv).mpr
    exact ((continuousOn_inv_Icc v).integrableOn_Icc).mono_set
      (Set.Icc_subset_Icc_left (hX1.trans hu.1))
  have hlower : a / 4 * Real.log (1 + a / 8) ≤ ∫ t in u..v, fundamentalDensity t := by
    have hm := intervalIntegral.integral_mono_on huv (hiInv.const_mul (a / 4)) hi
      (fun t ht => by simpa only [div_eq_mul_inv] using hloc t ht)
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hu0 (hu0.trans_le huv)] at hm
    have heq : v / u = 1 + a / 8 := by dsimp [v]; field_simp
    simpa only [heq] using hm
  apply hlower.trans
  apply intervalIntegral.integral_mono_interval hu.1 huv hv _ (fundamental_density_interval hX1 hfar)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact fundamental_density_nonneg (by linarith [ht.1])

/-- The disjoint-block contradiction from §2, before applying the Fundamental Lemma. -/
theorem block_deficit_growth :
    0 < a → ∃ c : ℝ, 0 < c ∧
      ∃ᶠ x in atTop, c ≤ fundamentalIntegral x / Real.log x := by
  intro ha
  have hX₀ : (1 : ℝ) ≤ 8 / a := (le_div_iff₀ ha).mpr (by linarith [a_le_one])
  have hB : 1 < Real.exp (12 / a) := Real.one_lt_exp_iff.mpr (div_pos (by norm_num) ha)
  have hr : 1 < 2 * Real.exp (12 / a) := by linarith
  have hδ : 0 < a / 4 * Real.log (1 + a / 8) :=
    mul_pos (by linarith) (Real.log_pos (by linarith))
  apply geometric_block_growth fundamentalIntegral hr hX₀ hδ (fundamentalIntegral_nonneg hX₀)
  intro X hX
  have hX1 := hX₀.trans hX
  have hXY : X ≤ 2 * Real.exp (12 / a) * X := by nlinarith
  have hb := deficit_on_block ha hX
  have hi := fundamental_increment hX1 hXY
  linarith

end Daboussi
