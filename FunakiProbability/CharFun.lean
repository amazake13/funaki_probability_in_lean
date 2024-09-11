import Mathlib.Probability.Notation

open MeasureTheory Complex

namespace FunakiProbability

noncomputable
def charFun (μ : Measure ℝ) (t : ℝ) : ℂ := ∫ x, exp (I * t * x) ∂μ
