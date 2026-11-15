import Daboussi.Basic
import Mathlib.Algebra.BigOperators.Intervals

open Finset ArithmeticFunction

namespace Daboussi

def integerM (N : ℕ) : ℤ := ∑ n ∈ Ioc 0 N, moebius n

theorem M_eq_integerM (x : ℝ) : M x = (integerM ⌊x⌋₊ : ℝ) := by
  simp [M, integerM, ← Icc_add_one_left_eq_Ioc]

theorem integerM_succ (N : ℕ) : integerM (N + 1) = integerM N + moebius (N + 1) := by
  exact sum_Ioc_succ_top (Nat.zero_le N) _

theorem integerM_jump (N : ℕ) : |integerM (N + 1) - integerM N| ≤ 1 := by
  rw [integerM_succ, add_sub_cancel_left]
  exact abs_moebius_le_one

theorem integerM_change {m n : ℕ} (hmn : m ≤ n) :
    |(integerM n : ℝ) - integerM m| ≤ (n - m : ℕ) := by
  have h := sum_Ioc_consecutive (fun k => (moebius k : ℝ)) (Nat.zero_le m) hmn
  have h' : (integerM n : ℝ) - integerM m = ∑ k ∈ Ioc m n, (moebius k : ℝ) := by
    simp only [integerM, Int.cast_sum] at *
    linarith
  rw [h']
  calc
    _ ≤ ∑ k ∈ Ioc m n, |(moebius k : ℝ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Ioc m n, (1 : ℝ) := sum_le_sum fun k _ => abs_mu_le_one k
    _ = _ := by simp

theorem M_change {u t : ℝ} (hu : 0 ≤ u) (hut : u ≤ t) :
    |M t - M u| ≤ t - u + 1 := by
  have hfloor := Nat.floor_le_floor hut
  rw [M_eq_integerM, M_eq_integerM]
  have h := integerM_change hfloor
  rw [Nat.cast_sub hfloor] at h
  have ht := Nat.floor_le (hu.trans hut)
  have hu' := Nat.lt_floor_add_one u
  linarith

/-- Integer-valued functions with jumps at most one cannot change sign without vanishing. -/
theorem integer_positive_of_no_zero (z : ℕ → ℤ)
    (hstep : ∀ k, |z (k + 1) - z k| ≤ 1)
    {m n : ℕ} (hmn : m ≤ n) (hm : 0 < z m)
    (hnz : ∀ k, m ≤ k → k ≤ n → z k ≠ 0) : 0 < z n := by
  induction n, hmn using Nat.le_induction with
  | base => exact hm
  | succ k hmk ih =>
    have hk : 0 < z k := ih (fun j hj hjk => hnz j hj (by omega))
    have hs := (abs_le.mp (hstep k)).1
    have hn := hnz (k + 1) (by omega) le_rfl
    omega

theorem integer_negative_of_no_zero (z : ℕ → ℤ)
    (hstep : ∀ k, |z (k + 1) - z k| ≤ 1)
    {m n : ℕ} (hmn : m ≤ n) (hm : z m < 0)
    (hnz : ∀ k, m ≤ k → k ≤ n → z k ≠ 0) : z n < 0 := by
  have h := integer_positive_of_no_zero (fun k => -z k)
    (fun k => by
      have he : -z (k + 1) - -z k = -(z (k + 1) - z k) := by ring
      rw [he, abs_neg]
      exact hstep k) hmn (by omega)
    (fun k hmk hkn => neg_ne_zero.mpr (hnz k hmk hkn))
  omega

theorem M_floor_eq (x : ℝ) : M (⌊x⌋₊ : ℝ) = M x := by
  simp [M]

/-- The constant-sign assertion used on [X,BX] in §2. -/
theorem M_constant_sign {X Y : ℝ} (hX : 0 ≤ X) (hXY : X ≤ Y)
    (hnz : ∀ t ∈ Set.Icc X Y, M t ≠ 0) :
    (∀ t ∈ Set.Icc X Y, 0 < M t) ∨ (∀ t ∈ Set.Icc X Y, M t < 0) := by
  have hbase : M X ≠ 0 := hnz X ⟨le_rfl, hXY⟩
  have hknz : ∀ k, ⌊X⌋₊ ≤ k → k ≤ ⌊Y⌋₊ → integerM k ≠ 0 := by
    intro k hkX hkY
    by_cases hk : k = ⌊X⌋₊
    · subst k
      intro hz
      apply hbase
      rw [M_eq_integerM, hz, Int.cast_zero]
    · have hXk : X ≤ (k : ℝ) := by
        have hlt : ⌊X⌋₊ < k := by omega
        have : X < (⌊X⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one X
        have : (⌊X⌋₊ : ℝ) + 1 ≤ k := by exact_mod_cast hlt
        linarith
      have hkY' : (k : ℝ) ≤ Y := (Nat.cast_le.mpr hkY).trans (Nat.floor_le (hX.trans hXY))
      have h := hnz k ⟨hXk, hkY'⟩
      simpa [M_eq_integerM] using h
  rcases lt_or_gt_of_ne hbase with hneg | hpos
  · right
    intro t ht
    rw [M_eq_integerM]
    suffices hn : integerM ⌊t⌋₊ < 0 by exact_mod_cast hn
    apply integer_negative_of_no_zero integerM integerM_jump (Nat.floor_le_floor ht.1)
    · exact_mod_cast (show (integerM ⌊X⌋₊ : ℝ) < 0 by simpa [M_eq_integerM] using hneg)
    · intro k hkX hkt
      exact hknz k hkX (hkt.trans (Nat.floor_le_floor ht.2))
  · left
    intro t ht
    rw [M_eq_integerM]
    suffices hn : 0 < integerM ⌊t⌋₊ by exact_mod_cast hn
    apply integer_positive_of_no_zero integerM integerM_jump (Nat.floor_le_floor ht.1)
    · exact_mod_cast (show (0 : ℝ) < (integerM ⌊X⌋₊ : ℝ) by simpa [M_eq_integerM] using hpos)
    · intro k hkX hkt
      exact hknz k hkX (hkt.trans (Nat.floor_le_floor ht.2))

end Daboussi
