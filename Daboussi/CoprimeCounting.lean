import Daboussi.Limsup
import Mathlib.Data.Nat.Totient

open Finset Filter
open scoped Topology

namespace Daboussi

noncomputable def roughInterval (P : ℕ) (l u : ℝ) : ℝ :=
  ((Ioc ⌊l⌋₊ ⌊u⌋₊).filter (fun c => c.Coprime P)).card

theorem coprime_count_nat (P m n : ℕ) (hP : P ≠ 0) (hmn : m ≤ n) :
    ((Ioc m n).filter (fun c => c.Coprime P)).card ≤ P.totient * ((n - m) / P + 1) := by
  have he : Ioc m n = Ico (m + 1) (m + 1 + (n - m)) := by
    ext c
    simp only [mem_Ioc, mem_Ico]
    omega
  rw [he]
  simpa only [Nat.coprime_comm] using Nat.Ico_filter_coprime_le (m + 1) (n - m) hP

/-- The one-sided periodic coprime-count estimate needed in Proposition 3.
Its error depends only on P, not on the interval endpoints. -/
theorem rough_interval_le {P : ℕ} (hP : P ≠ 0) {l u : ℝ} (hl : 0 ≤ l) (hlu : l ≤ u) :
    roughInterval P l u ≤ (P.totient : ℝ) / P * (u - l) +
      ((P.totient : ℝ) / P + P.totient) := by
  have hf := Nat.floor_le_floor hlu
  have hcount := coprime_count_nat P ⌊l⌋₊ ⌊u⌋₊ hP hf
  have hcast : roughInterval P l u ≤
      (P.totient : ℝ) * (((⌊u⌋₊ - ⌊l⌋₊) / P : ℕ) + 1) := by
    unfold roughInterval
    exact_mod_cast hcount
  have hdiv : (((⌊u⌋₊ - ⌊l⌋₊) / P : ℕ) : ℝ) ≤ ((⌊u⌋₊ - ⌊l⌋₊ : ℕ) : ℝ) / P :=
    Nat.cast_div_le
  have hlen : ((⌊u⌋₊ - ⌊l⌋₊ : ℕ) : ℝ) ≤ u - l + 1 := by
    rw [Nat.cast_sub hf]
    have hu := Nat.floor_le (hl.trans hlu)
    have hl' := Nat.lt_floor_add_one l
    linarith
  have hP0 : (0 : ℝ) < P := by exact_mod_cast (Nat.pos_of_ne_zero hP)
  calc
    roughInterval P l u ≤ (P.totient : ℝ) * (((⌊u⌋₊ - ⌊l⌋₊ : ℕ) : ℝ) / P + 1) :=
      hcast.trans (mul_le_mul_of_nonneg_left (add_le_add hdiv le_rfl) (Nat.cast_nonneg _))
    _ ≤ (P.totient : ℝ) * ((u - l + 1) / P + 1) :=
      mul_le_mul_of_nonneg_left (add_le_add (div_le_div_of_nonneg_right hlen hP0.le) le_rfl)
        (Nat.cast_nonneg _)
    _ = _ := by ring

theorem a_le_of_affine_bound {A C : ℝ}
    (h : ∀ᶠ x : ℝ in atTop, |M x| ≤ A * x + C) : a ≤ A := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hlim : Tendsto (fun x : ℝ => C / x) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have he := hlim.eventually (gt_mem_nhds hε)
  have hu : ∀ᶠ x : ℝ in atTop, |M x| / x ≤ A + ε := by
    filter_upwards [h, he, eventually_gt_atTop (0 : ℝ)] with x hx hcx hx0
    have hd := div_le_div_of_nonneg_right hx hx0.le
    have hid : (A * x + C) / x = A + C / x := by field_simp
    rw [hid] at hd
    linarith
  have hb : atTop.IsBoundedUnder (· ≥ ·) (fun x : ℝ => |M x| / x) :=
    ⟨0, normalized_M_nonneg⟩
  exact limsup_le_of_le hb.isCoboundedUnder_le hu

end Daboussi
