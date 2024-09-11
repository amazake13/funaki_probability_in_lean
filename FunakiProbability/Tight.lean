import Mathlib.Probability.Notation
import Mathlib.Probability.CDF

open MeasureTheory Filter Topology ProbabilityTheory

variable (μs : ℕ → Measure ℝ)

def tight : Prop :=
  ∀ ε > 0, ∃ M > 0, ∀ n, (μs n) {x | |x| ≤ M} ≥ 1 - ε

def right_continuous (f : ℝ → ℝ) : Prop :=
  ∀ x, ContinuousWithinAt f (Set.Ici x) x

noncomputable
def subseq_cdfs_at (k : ℕ → ℕ) (x : ℝ) : ℕ → ℝ := fun n => (cdf ∘ μs ∘ k) n x

theorem helly_selection : (∃ k : ℕ → ℕ, ∃ F : ℝ → ℝ, Monotone F ∧ right_continuous F
  ∧ StrictMono k ∧ (∀ x, ContinuousAt F x → Tendsto (subseq_cdfs_at μs k x) atTop (𝓝 (F x)))):= by
  sorry
