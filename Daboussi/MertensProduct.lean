import Daboussi.MertensUpper
import Daboussi.SmoothSupport
import Mathlib.Analysis.PSeries

open Finset

namespace Daboussi

theorem smallPrimes_eq_primesBelow (y : ℝ) :
    smallPrimes y = Nat.primesBelow (⌊y⌋₊ + 1) := by
  ext p
  simp [smallPrimes, Nat.mem_primesLE, Nat.mem_primesBelow, Nat.lt_succ_iff, and_comm]

theorem reciprocal_factor_bound {p : ℝ} (hp : 2 ≤ p) :
    1 / (p - 1) ≤ 1 / p + 2 * (p ^ 2)⁻¹ := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  field_simp
  nlinarith

/-- The upper-bound form of Mertens' product estimate used in §4. -/
theorem mertens_product_upper : ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 2 ≤ y →
    (∏ p ∈ smallPrimes y, (1 - (p : ℝ)⁻¹)⁻¹) ≤ C * Real.log y := by
  obtain ⟨B, hB⟩ := AmicableMertens.sum_inv_prime_le
  let T : ℝ := ∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹
  have hT : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) := Real.summable_nat_pow_inv.mpr (by norm_num)
  refine ⟨Real.exp (B + 2 * T), Real.exp_pos _, ?_⟩
  intro y hy
  have hp2 (p : ℕ) (hp : p ∈ smallPrimes y) : (2 : ℝ) ≤ p := by
    exact_mod_cast ((mem_smallPrimes (by linarith) p).mp hp).1.two_le
  have he : (∏ p ∈ smallPrimes y, (1 - (p : ℝ)⁻¹)⁻¹) =
      ∏ p ∈ smallPrimes y, (1 + 1 / ((p : ℝ) - 1)) := by
    apply prod_congr rfl
    intro p hp
    have h0 : (p : ℝ) ≠ 0 := by linarith [hp2 p hp]
    have h1 : (p : ℝ) - 1 ≠ 0 := by linarith [hp2 p hp]
    field_simp
    ring
  have hs : (∑ p ∈ smallPrimes y, 1 / ((p : ℝ) - 1)) ≤ Real.log (Real.log y) + B + 2 * T := by
    calc
      _ ≤ ∑ p ∈ smallPrimes y, (1 / (p : ℝ) + 2 * ((p : ℝ) ^ 2)⁻¹) :=
        sum_le_sum (fun p hp => reciprocal_factor_bound (hp2 p hp))
      _ = (∑ p ∈ smallPrimes y, 1 / (p : ℝ)) + 2 * ∑ p ∈ smallPrimes y, ((p : ℝ) ^ 2)⁻¹ := by
        rw [sum_add_distrib, mul_sum]
      _ ≤ _ := add_le_add (by simpa only [smallPrimes_eq_primesBelow] using hB y hy)
        (mul_le_mul_of_nonneg_left (hT.sum_le_tsum _ (fun n _ => inv_nonneg.mpr (sq_nonneg _))) (by norm_num))
  rw [he]
  calc
    _ ≤ ∏ p ∈ smallPrimes y, Real.exp (1 / ((p : ℝ) - 1)) := by
      apply prod_le_prod₀
      · intro p hp
        have := hp2 p hp
        exact add_nonneg zero_le_one (div_nonneg zero_le_one (by linarith))
      · intro p hp
        simpa only [add_comm] using Real.add_one_le_exp (1 / ((p : ℝ) - 1))
    _ = Real.exp (∑ p ∈ smallPrimes y, 1 / ((p : ℝ) - 1)) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (Real.log (Real.log y) + B + 2 * T) := Real.exp_le_exp.mpr hs
    _ = Real.exp (B + 2 * T) * Real.log y := by
      rw [show Real.log (Real.log y) + B + 2 * T = (B + 2 * T) + Real.log (Real.log y) by ring,
        Real.exp_add, Real.exp_log (Real.log_pos (by linarith))]

end Daboussi
