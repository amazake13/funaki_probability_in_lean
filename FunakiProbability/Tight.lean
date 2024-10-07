import Mathlib.Probability.Notation
import Mathlib.Probability.CDF

open Filter Topology ProbabilityTheory

section HellySelection

variable (Fs : ℕ → ℝ → ℝ)
  (rcont : ∀ n x, ContinuousWithinAt (Fs n) (Set.Ici x) x)
  (mono : ∀ n, Monotone (Fs n))
  (bdd : ∀ n x, Fs n x ∈ Set.Icc 0 1)
  (r' : ℕ → ℝ)


def subseq_exists : ∀ n (s : ℕ → ℕ), ∃ (s' : ℕ → ℕ), StrictMono s'
  ∧ ∃ l, Tendsto (fun k ↦ Fs ((s ∘ s') k) (r' n)) atTop (𝓝 l) := by
  intro n s
  have h_bdd : ∀ k, Fs (s k) (r' n) ∈ Set.Icc 0 1 := fun k ↦ bdd _ _
  have h_compact : IsCompact (Set.Icc 0 1 : Set ℝ) := isCompact_Icc
  obtain ⟨l, _, s', hs'⟩ := h_compact.tendsto_subseq h_bdd
  exists s'
  constructor
  · exact hs'.left
  · exact ⟨l, hs'.right⟩

noncomputable def reduce (n : ℕ) (s : ℕ → ℕ) : ℕ → ℕ :=
  Classical.choose (subseq_exists Fs bdd r' n s)

noncomputable def seqseq : ℕ → (ℕ → ℕ)
  | 0 => id
  | Nat.succ n => seqseq n ∘ (reduce Fs bdd r' n (seqseq n))


theorem helly_selection
  (Fs : ℕ → ℝ → ℝ)
  (rcont : ∀ n x, ContinuousWithinAt (Fs n) (Set.Ici x) x)
  (mono : ∀ n, Monotone (Fs n))
  (bdd : ∀ n x, Fs n x ∈ Set.Icc 0 1) :
  ∃ φ : ℕ → ℕ, StrictMono φ ∧
  ∃ F : ℝ → ℝ, Monotone F ∧ (∀ x, ContinuousWithinAt F (Set.Ici x) x)
  ∧ (∀ x, ContinuousAt F x → Tendsto (fun n ↦ Fs (φ n) x) atTop (𝓝 (F x))):= by
  -- ℚは可算集合より有理数を列挙する
  obtain ⟨r, hr⟩ : ∃ r : ℕ → ℚ, Function.Surjective r := by
    exact exists_surjective_nat ℚ
  -- 'r'をℝに拡張する
  let r' : ℕ → ℝ := fun n ↦ (r n : ℝ)

  -- let P : ℕ → (ℕ → ℕ) → Prop := fun n s ↦ ∃ l, Tendsto (fun k ↦ Fs (s k) (r' n)) atTop (𝓝 l)
  -- have subseq_exists : ∀ n (s : ℕ → ℕ), StrictMono s → ∃ s', StrictMono s' ∧ P n (s ∘ s') := by
  --   intro n s hs
  --   let seq := fun k ↦ Fs (s k) (r' n)
  --   have h_bdd : ∀ k, seq k ∈ Set.Icc 0 1 := fun k ↦ bdd _ _
  --   have h_compact : IsCompact (Set.Icc 0 1 : Set ℝ) := isCompact_Icc
  --   obtain ⟨l, hl, s', hs'⟩ := h_compact.tendsto_subseq h_bdd
  --   exists s'
  --   constructor
  --   · exact hs'.left
  --   · exact ⟨l, hs'.right⟩

  let diag_seq := fun n ↦ seqseq Fs bdd r' n n
