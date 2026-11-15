import Daboussi.Definitions
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic

open Finset ArithmeticFunction

namespace Daboussi

theorem abs_mu_le_one (n : ℕ) : |(moebius n : ℝ)| ≤ 1 := by
  exact_mod_cast (abs_moebius_le_one (n := n))

theorem abs_smoothM_le_psi (x y : ℝ) : |smoothM x y| ≤ psi x y := by
  calc
    _ ≤ ∑ n ∈ smoothNumbers x y, |(moebius n : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ smoothNumbers x y, (1 : ℝ) :=
      sum_le_sum fun n _ => abs_mu_le_one n
    _ = _ := by simp [psi]

theorem smooth_of_le {n : ℕ} {y : ℝ} (hn : 1 ≤ n) (hny : (n : ℝ) ≤ y) :
    Smooth y n := by
  intro p _ hp
  exact (Nat.cast_le.mpr (Nat.le_of_dvd (by omega) hp)).trans hny

theorem smoothNumbers_eq_Icc {x y : ℝ} (hxy : x ≤ y) :
    smoothNumbers x y = Icc 1 ⌊x⌋₊ := by
  classical
  apply filter_eq_self.mpr
  intro n hn
  have hn' := mem_Icc.mp hn
  have hx : 0 ≤ x := by
    by_contra h
    have : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
    omega
  exact smooth_of_le hn'.1 ((Nat.cast_le.mpr hn'.2).trans ((Nat.floor_le hx).trans hxy))

theorem smoothM_eq_M {x y : ℝ} (hxy : x ≤ y) : smoothM x y = M x := by
  simp only [smoothM, M, smoothNumbers_eq_Icc hxy]

theorem psi_eq_floor {x y : ℝ} (hxy : x ≤ y) : psi x y = (⌊x⌋₊ : ℝ) := by
  simp [psi, smoothNumbers_eq_Icc hxy, Nat.card_Icc]

theorem psi_nonneg (x y : ℝ) : 0 ≤ psi x y := by
  unfold psi
  positivity

theorem psi_le_floor (x y : ℝ) : psi x y ≤ (⌊x⌋₊ : ℝ) := by
  classical
  have h := card_filter_le (Icc 1 ⌊x⌋₊) (Smooth y)
  simpa [psi, smoothNumbers, Nat.card_Icc] using (Nat.cast_le (α := ℝ)).mpr h

theorem abs_M_le_self {x : ℝ} (hx : 0 ≤ x) : |M x| ≤ x := by
  rw [← smoothM_eq_M (le_refl x)]
  exact (abs_smoothM_le_psi x x).trans ((psi_le_floor x x).trans (Nat.floor_le hx))

theorem excess_nonneg (y t : ℝ) : 0 ≤ excess y t := le_max_right _ _

theorem excess_le_one {y t : ℝ} (ha : 0 ≤ a) (ht : 1 ≤ t) : excess y t ≤ 1 := by
  have ht0 : 0 < t := by linarith
  apply max_le _ (by norm_num)
  have hp : 0 ≤ a * psi t y / t := by positivity [psi_nonneg t y]
  have hm : |smoothM t y| / t ≤ 1 := by
    apply (div_le_one ht0).mpr
    exact (abs_smoothM_le_psi t y).trans ((psi_le_floor t y).trans (Nat.floor_le ht0.le))
  linarith

theorem excess_sub_deficit (y t : ℝ) :
    excess y t - deficit y t = |smoothM t y| / t - a * psi t y / t := by
  unfold excess deficit
  by_cases h : |smoothM t y| / t ≤ a * psi t y / t
  · rw [max_eq_right (sub_nonpos.mpr h), max_eq_left (sub_nonneg.mpr h)]
    ring
  · rw [max_eq_left (by linarith), max_eq_right (by linarith)]
    ring

/-- The elementary positive-part inequality used below the smoothness cutoff. -/
theorem positive_part_sub (v h : ℝ) (hh : 0 ≤ h) :
    max v 0 - h ≤ max (v - h) 0 := by
  by_cases hv : 0 ≤ v
  · rw [max_eq_left hv]
    exact le_max_left _ _
  · rw [max_eq_right (le_of_not_ge hv)]
    exact (by linarith : (0 : ℝ) - h ≤ 0).trans (le_max_right _ _)

/-- The local persistence estimate in the proof after the Fundamental Lemma. -/
theorem local_smallness {b u t mU mT : ℝ}
    (hb : 0 ≤ b) (hu : 1 ≤ b * u / 8) (hut : u ≤ t)
    (htu : t ≤ u * (1 + b / 8))
    (hsmall : |mU| ≤ b / 2 * u)
    (hjump : |mT - mU| ≤ t - u + 1) :
    |mT| ≤ (3 * b / 4) * t := by
  have htri : |mT| ≤ |mU| + |mT - mU| := by
    convert abs_add_le mU (mT - mU) using 1 <;> ring_nf
  have hnear : t - u ≤ b * u / 8 := by nlinarith
  have hscale : b * u ≤ b * t := mul_le_mul_of_nonneg_left hut hb
  nlinarith

end Daboussi
