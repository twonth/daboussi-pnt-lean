import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

open Filter
open scoped Topology

namespace Daboussi

/-- Summing a fixed positive contribution over multiplicative blocks forces
a positive logarithmic average along the block endpoints. -/
theorem geometric_block_growth (F : ℝ → ℝ) {r X₀ δ : ℝ}
    (hr : 1 < r) (hX : 1 ≤ X₀) (hδ : 0 < δ)
    (hF : 0 ≤ F X₀)
    (hstep : ∀ X : ℝ, X₀ ≤ X → F X + δ ≤ F (r * X)) :
    ∃ c : ℝ, 0 < c ∧ ∃ᶠ x in atTop, c ≤ F x / Real.log x := by
  have hr0 : 0 < r := by linarith
  have hX0 : 0 < X₀ := by linarith
  have hlr : 0 < Real.log r := Real.log_pos hr
  have hlX : 0 ≤ Real.log X₀ := Real.log_nonneg hX
  have hscale (n : ℕ) : X₀ ≤ r ^ n * X₀ := by
    have hp : 1 ≤ r ^ n := one_le_pow₀ hr.le
    nlinarith
  have hgrowth (n : ℕ) : (n : ℝ) * δ ≤ F (r ^ n * X₀) := by
    induction n with
    | zero => simpa using hF
    | succ n ih =>
      have hs := hstep (r ^ n * X₀) (hscale n)
      have he : r * (r ^ n * X₀) = r ^ (n + 1) * X₀ := by ring
      rw [he] at hs
      push_cast
      linarith
  let D := Real.log r + Real.log X₀
  have hD : 0 < D := by dsimp [D]; linarith
  refine ⟨δ / D, div_pos hδ hD, ?_⟩
  have hbound (n : ℕ) (hn : 1 ≤ n) : δ / D ≤ F (r ^ n * X₀) / Real.log (r ^ n * X₀) := by
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hlog : Real.log (r ^ n * X₀) = (n : ℝ) * Real.log r + Real.log X₀ := by
      rw [Real.log_mul (pow_ne_zero _ hr0.ne') hX0.ne', Real.log_pow]
    have hlpos : 0 < Real.log (r ^ n * X₀) := by rw [hlog]; nlinarith
    have hupper : Real.log (r ^ n * X₀) ≤ (n : ℝ) * D := by
      rw [hlog]
      dsimp [D]
      nlinarith
    apply (le_div_iff₀ hlpos).mpr
    calc
      δ / D * Real.log (r ^ n * X₀) ≤ δ / D * ((n : ℝ) * D) :=
        mul_le_mul_of_nonneg_left hupper (div_pos hδ hD).le
      _ = (n : ℝ) * δ := by field_simp <;> ring
      _ ≤ _ := hgrowth n
  have ht : Tendsto (fun n : ℕ => r ^ n * X₀) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hr).atTop_mul_const hX0
  apply frequently_atTop.mpr
  intro R
  obtain ⟨n, hnR, hn⟩ := ((ht.eventually (eventually_ge_atTop R)).and
    (eventually_ge_atTop (1 : ℕ))).exists
  exact ⟨r ^ n * X₀, hnR, hbound n hn⟩

end Daboussi
