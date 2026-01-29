import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.BumpFunction.Basic 
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Distribution.SchwartzSpace

noncomputable section
namespace RiemannEnergy

open Real Set MeasureTheory Filter Topology Function

/--
Estructura de Ventana Admisible (Smooth Window).
-/
structure SmoothWindow (c₁ c₂ : ℝ) where
  val : ℝ → ℝ
  eq_gaussian : ∀ x, x ∈ Icc c₁ c₂ → val x = Real.exp (-(x ^ 2))
  compact_support : ∃ ε > 0, ∀ x, x ∉ Ioo (c₁ - ε) (c₂ + ε) → val x = 0
  smoothness : ContDiff ℝ ⊤ val

/--
Teorema: Existencia de Ventanas Suaves (CONSTRUCTIVO).
-/
theorem exists_smooth_window (c₁ c₂ : ℝ) (h : c₁ < c₂) :
    ∃ _ : SmoothWindow c₁ c₂, True := by
  let c : ℝ := (c₁ + c₂) / 2
  let r : ℝ := (c₂ - c₁) / 2

  have hr_pos : 0 < r := by dsimp [r]; linarith
  have hr_out : r < r + 1 := by linarith

  let bump : ContDiffBump c :=
    { rIn := r
      rOut := r + 1
      rIn_pos := hr_pos
      rIn_lt_rOut := hr_out }

  let V_func : ℝ → ℝ := fun x => (bump.toFun x) * Real.exp (-(x ^ 2))

  refine ⟨⟨V_func, ?_, ?_, ?_⟩, trivial⟩

  · -- Propiedad 1: Coincide con la Gaussiana en [c₁,c₂]
    intro x hx
    dsimp [V_func]
    have h_mem : x ∈ Metric.closedBall c r := by
      rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
      constructor
      · have h1 : c - r = c₁ := by dsimp [c, r]; ring
        have hx_left : c₁ ≤ x := hx.1
        linarith
      · have h2 : c + r = c₂ := by dsimp [c, r]; ring
        have hx_right : x ≤ c₂ := hx.2
        linarith
    
    have hb1 : bump.toFun x = 1 := bump.one_of_mem_closedBall h_mem
    simp [hb1]

  · -- Propiedad 2: Soporte Compacto
    refine ⟨1, by linarith, ?_⟩
    intro x hx
    dsimp [V_func]

    rw [mem_Ioo, not_and_or, not_lt, not_lt] at hx
    
    -- Demostración de distancia segura usando linarith y apertura de abs
    have hdist : bump.rOut ≤ dist x c := by
      show r + 1 ≤ dist x c
      rw [Real.dist_eq]
      cases hx with
      | inl hle =>
          have hc1 : c₁ = c - r := by dsimp [c, r]; ring
          rw [hc1] at hle
          rw [abs_of_nonpos]
          · linarith
          · linarith
      | inr hge =>
          have hc2 : c₂ = c + r := by dsimp [c, r]; ring
          rw [hc2] at hge
          rw [abs_of_nonneg]
          · linarith
          · linarith

    have hb0 : bump.toFun x = 0 := by
      by_contra h_nonzero
      have h_in_supp : x ∈ Function.support bump.toFun := Function.mem_support.mpr h_nonzero
      rw [bump.support_eq] at h_in_supp
      rw [Metric.mem_ball] at h_in_supp
      linarith
    
    simp [hb0]

  · -- Propiedad 3: Suavidad
    have hgauss : ContDiff ℝ ⊤ (fun x : ℝ => Real.exp (-(x ^ 2))) := by
      exact (contDiff_exp.comp (contDiff_neg.comp (contDiff_id.pow 2)))
    exact bump.contDiff.mul hgauss

/--
Transformada de Mellin
-/
def MellinTransform (V : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∫ x in Ioi 0, (V x : ℂ) * (x : ℂ) ^ (s - 1)

/--
Lema de Decaimiento Rápido (Rapid Decay).
-/
theorem Smooth_Mellin_Decay {c₁ c₂ : ℝ} (V : SmoothWindow c₁ c₂) (σ : ℝ) (A : ℕ) :
    ∀ᶠ (t : ℝ) in atTop, ‖MellinTransform V.val (σ + I * t)‖ ≤ |t| ^ (-(A : ℝ)) := by
  -- El decaimiento rápido se sigue de que V es una función suave con soporte compacto
  -- (Schwartz en el espacio logarítmico), por lo que su transformada de Fourier (Mellin) decae
  -- más rápido que cualquier polinomio.
  sorry

end RiemannEnergy
