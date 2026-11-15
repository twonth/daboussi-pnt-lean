import Daboussi.MertensProduct
import Daboussi.ExcessRecurrence
import Mathlib.Data.Nat.Factorization.PrimePow

open Finset ArithmeticFunction
attribute [local instance] Classical.propDecidable

namespace Daboussi

theorem prime_power_geometric_bound {p : ℕ} (hp : p.Prime) (N : ℕ) :
    (∑ k ∈ Icc 1 N, Real.log p / (p : ℝ) ^ k) ≤ Real.log p / ((p : ℝ) - 1) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hgeo := hasSum_geometric_of_lt_one (inv_nonneg.mpr hp0.le)
    ((inv_lt_one₀ hp0).mpr (by linarith))
  have hg : (∑ k ∈ Ico 1 (N + 1), ((p : ℝ)⁻¹)^k) ≤ (p : ℝ)⁻¹ / (1 - (p : ℝ)⁻¹) := by
    have hb := hgeo.summable.sum_le_tsum (Ico 0 (N + 1))
      (fun k _ => pow_nonneg (inv_nonneg.mpr hp0.le) k)
    rw [hgeo.tsum_eq, sum_eq_sum_Ico_succ_bot (by omega : 0 < N + 1)] at hb
    simp only [pow_zero] at hb
    have he : (1 - (p : ℝ)⁻¹)⁻¹ = 1 + (p : ℝ)⁻¹ / (1 - (p : ℝ)⁻¹) := by
      have hne : 1 - (p : ℝ)⁻¹ ≠ 0 := by have := (inv_lt_one₀ hp0).mpr (show (1 : ℝ) < p by linarith); linarith
      have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
      field_simp
      <;> ring
    rw [he] at hb
    linarith
  have he : (∑ k ∈ Icc 1 N, Real.log p / (p : ℝ) ^ k) =
      Real.log p * ∑ k ∈ Ico 1 (N + 1), ((p : ℝ)⁻¹) ^ k := by
    rw [mul_sum]
    simp only [Ico_add_one_right_eq_Icc, div_eq_mul_inv, inv_pow]
  rw [he]
  apply (mul_le_mul_of_nonneg_left hg (Real.log_natCast_nonneg p)).trans_eq
  have hne : 1 - (p : ℝ)⁻¹ ≠ 0 := by have := (inv_lt_one₀ hp0).mpr (show (1 : ℝ) < p by linarith); linarith
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  field_simp

/-- Every nonzero term is a power of one of the primes at most y. -/
theorem smoothLambda_sum_le {y : ℝ} (hy : 0 ≤ y) (N : ℕ) :
    (∑ n ∈ Icc 1 N, restrictSmooth y vonMangoldt n / n) ≤
      ∑ p ∈ smallPrimes y, Real.log p / ((p : ℝ) - 1) := by
  let s := (Icc 1 N).filter (fun n => Smooth y n ∧ IsPrimePow n)
  let e : ℕ → ℕ × ℕ := fun n => (n.minFac, n.factorization n.minFac)
  have hn (n : ℕ) (h : n ∈ s) : n.minFac ^ n.factorization n.minFac = n :=
    (mem_filter.mp h).2.2.minFac_pow_factorization_eq
  have hp (n : ℕ) (h : n ∈ s) : n.minFac.Prime :=
    Nat.minFac_prime (mem_filter.mp h).2.2.ne_one
  have hsum : (∑ n ∈ Icc 1 N, restrictSmooth y vonMangoldt n / n) =
      ∑ n ∈ s, Real.log n.minFac / n := by
    simp only [s, sum_filter, restrictSmooth, coe_mk, vonMangoldt_apply]
    apply sum_congr rfl
    intro n _; split_ifs <;> simp_all
  rw [hsum]
  calc
    _ ≤ ∑ q ∈ smallPrimes y ×ˢ Icc 1 N, Real.log q.1 / (q.1 : ℝ) ^ q.2 := by
      apply sum_le_sum_of_injOn e
      · intro n hn' m hm' he
        have he' := congrArg (fun q : ℕ × ℕ => q.1 ^ q.2) he
        simpa only [e, hn n hn', hn m hm'] using he'
      · intro q hq
        obtain ⟨n, hns, rfl⟩ := mem_image.mp hq
        apply mem_product.mpr
        constructor
        · exact (mem_smallPrimes hy _).mpr ⟨hp n hns, (mem_filter.mp hns).2.1 _ (hp n hns) (Nat.minFac_dvd n)⟩
        · have hk : 1 ≤ n.factorization n.minFac := by
            by_contra h
            have hz : n.factorization n.minFac = 0 := by omega
            have heq := hn n hns
            rw [hz, pow_zero] at heq
            exact (mem_filter.mp hns).2.2.ne_one heq.symm
          have hkN : n.factorization n.minFac ≤ N := by
            have hmul := Nat.mul_factorization_le (n := n) (p := n.minFac)
            have htwo := (hp n hns).two_le
            have hN := (mem_Icc.mp (mem_filter.mp hns).1).2
            nlinarith
          exact mem_Icc.mpr ⟨hk, hkN⟩
      · intro n hns
        dsimp [e]
        rw [← Nat.cast_pow, hn n hns]
      · intro q hq _
        exact div_nonneg (Real.log_natCast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)
    _ ≤ _ := by
      rw [sum_product]
      apply sum_le_sum
      intro p hp'
      exact prime_power_geometric_bound ((mem_smallPrimes hy p).mp hp').1 N

noncomputable def primePowerError (n : ℕ) : ℝ :=
  if n.Prime then Real.log n / ((n : ℝ) * ((n : ℝ) - 1)) else 0

theorem primePowerError_nonneg (n : ℕ) : 0 ≤ primePowerError n := by
  unfold primePowerError
  split_ifs with hp
  · have hp2 : (2 : ℝ) ≤ n := by exact_mod_cast hp.two_le
    exact div_nonneg (Real.log_natCast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (by linarith))
  · rfl

theorem primePowerError_summable : Summable primePowerError := by
  have hs := (Real.summable_nat_rpow.mpr (by norm_num : (-3 / 2 : ℝ) < -1)).mul_left 4
  apply hs.of_nonneg_of_le primePowerError_nonneg
  intro n
  unfold primePowerError
  split_ifs with hp
  · have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hp.two_le
    have hn0 : (0 : ℝ) < n := by linarith
    have hl := Real.log_le_rpow_div (Nat.cast_nonneg n) (by norm_num : (0 : ℝ) < 1 / 2)
    have hd : (n : ℝ)^2 / 2 ≤ (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
    calc
      _ ≤ ((n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2)) / ((n : ℝ)^2 / 2) := by
        apply div_le_div₀ (by positivity) hl (by positivity) hd
      _ = 4 * (n : ℝ) ^ (-3 / 2 : ℝ) := by
        rw [show (-3 / 2 : ℝ) = (1 / 2 : ℝ) - 2 by norm_num,
          Real.rpow_sub hn0, Real.rpow_two]
        ring
  · positivity

theorem mertens_coefficient_upper : ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 2 ≤ y → ∀ N : ℕ,
    1 + (∑ n ∈ Icc 1 N, restrictSmooth y vonMangoldt n / n) ≤ Real.log y + C := by
  obtain ⟨B, hB⟩ := AmicableMertens.sum_log_div_prime_le
  let T := ∑' n, primePowerError n
  refine ⟨|B| + |T| + 1, by positivity, ?_⟩
  intro y hy N
  have hs := smoothLambda_sum_le (show 0 ≤ y by linarith) N
  have he : (∑ p ∈ smallPrimes y, Real.log p / ((p : ℝ) - 1)) =
      (∑ p ∈ smallPrimes y, Real.log p / p) + ∑ p ∈ smallPrimes y, primePowerError p := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro p hp
    have hp' := ((mem_smallPrimes (by linarith) p).mp hp).1
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp'.two_le
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
    simp only [primePowerError, if_pos hp']
    field_simp
    <;> ring
  rw [he] at hs
  have hb : (∑ p ∈ smallPrimes y, Real.log p / p) ≤ Real.log y + B := by
    simpa only [smallPrimes_eq_primesBelow] using hB y hy
  have ht : (∑ p ∈ smallPrimes y, primePowerError p) ≤ T :=
    primePowerError_summable.sum_le_tsum _ (fun n _ => primePowerError_nonneg n)
  linarith [le_abs_self B, le_abs_self T]

end Daboussi
