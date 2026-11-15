import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Topology.Instances.Real.Lemmas

open Filter
open scoped Topology

/-- Pollack's Theorem 1: the summatory Möbius function is o(x). -/
theorem Daboussi.mobius_summatory_limit :
    Tendsto (fun x : ℝ =>
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.moebius n : ℝ)) / x)
      atTop (nhds 0) := by
  sorry
