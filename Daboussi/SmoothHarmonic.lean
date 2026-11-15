import Daboussi.SmoothSupport
import Mathlib.NumberTheory.EulerProduct.Basic

open Finset

namespace Daboussi

noncomputable def invNat : ℕ →* ℝ where
  toFun n := (n : ℝ)⁻¹
  map_one' := by simp
  map_mul' m n := by simp [mul_comm]

theorem invNat_norm_prime {p : ℕ} (hp : p.Prime) : ‖invNat p‖ < 1 := by
  change ‖(p : ℝ)⁻¹‖ < 1
  rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p))]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [inv_lt_one₀ hp0]
  simpa using (show (1 : ℝ) < p by exact_mod_cast hp.one_lt)

/-- The finite Euler product gives the full harmonic mass of smooth numbers,
without using asymptotics for their counting function. -/
theorem smooth_harmonic_hasSum (y : ℝ) :
    HasSum (fun n : Nat.factoredNumbers (smallPrimes y) => ((n : ℕ) : ℝ)⁻¹)
      (∏ p ∈ smallPrimes y, (1 - (p : ℝ)⁻¹)⁻¹) := by
  have h := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := invNat) invNat_norm_prime (smallPrimes y)).2
  have hf : (smallPrimes y).filter Nat.Prime = smallPrimes y := by
    apply filter_eq_self.mpr
    intro p hp
    exact (Nat.mem_primesLE.mp hp).2
  simpa only [hf, invNat, MonoidHom.coe_mk, OneHom.coe_mk] using h

theorem smooth_harmonic_summable (y : ℝ) :
    Summable (fun n : Nat.factoredNumbers (smallPrimes y) => ((n : ℕ) : ℝ)⁻¹) :=
  (smooth_harmonic_hasSum y).summable

end Daboussi
