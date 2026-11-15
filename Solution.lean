import Daboussi.Fundamental

/-! Theorem 1, proved by the smooth-number argument in the supplied paper. -/

open Filter
open scoped Topology

theorem Daboussi.mobius_summatory_limit :
    Tendsto (fun x : ℝ =>
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.moebius n : ℝ)) / x)
      atTop (nhds 0) := by
  exact Daboussi.main_of_a_eq_zero Daboussi.limsup_eq_zero
