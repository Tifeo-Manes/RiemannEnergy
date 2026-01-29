/-
File: PaperRH/Analysis/CompactBounds.lean

Generic compact/indicator bounds for nonnegative integrals (lintegral).
These are the “no-arithmetic” bricks you will reuse everywhere.
-/

import Mathlib

set_option autoImplicit false
open Classical

-- Abrimos los scopes necesarios
open scoped BigOperators Topology ENNReal

namespace PaperRH.Analysis

open MeasureTheory

/-- Generic bound: if `f ≤ B` on `s`, then `∫⁻ x in s, f x ≤ μ s * B`. -/
theorem lintegral_le_of_forall_le_on
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (s : Set α) (hs : MeasurableSet s)
    (f : α → ℝ≥0∞) (B : ℝ≥0∞)
    (h : ∀ x, x ∈ s → f x ≤ B) :
    (∫⁻ x in s, f x ∂μ) ≤ μ s * B := by
  
  -- 1. Demostramos la cota puntual para los indicadores
  have hind : ∀ x, s.indicator f x ≤ s.indicator (fun _ => B) x := by
    intro x
    by_cases hx : x ∈ s
    · simp only [Set.indicator_of_mem hx]
      exact h x hx
    · simp only [Set.indicator_of_not_mem hx, le_refl]

  -- 2. Usamos 'calc' con corrección de conmutatividad al final
  calc
    (∫⁻ x in s, f x ∂μ) 
        = ∫⁻ x, s.indicator f x ∂μ := by 
            -- Convertimos integral restringida a integral de indicador
            rw [← lintegral_indicator _ hs]
    
    _ ≤ ∫⁻ x, s.indicator (fun _ => B) x ∂μ := 
            -- Aplicamos la monotonía de la integral
            lintegral_mono hind
    
    _ = ∫⁻ x in s, B ∂μ := by 
            -- Convertimos de vuelta a integral restringida
            rw [lintegral_indicator _ hs]
    
    _ = μ s * B := by 
            -- Integral de una constante sobre el conjunto
            rw [set_lintegral_const s]
            -- SOLUCIÓN: Usamos conmutatividad (B * μ s = μ s * B)
            simp only [mul_comm]

/-- Specialized bound for complex-valued functions: if `‖g x‖ ≤ K` on `s`, then
    `∫⁻ in s ofReal(‖g x‖^2) ≤ μ s * ofReal(K^2)`. -/
theorem lintegral_ofReal_norm_sq_le_of_forall_norm_le_on
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (s : Set α) (hs : MeasurableSet s)
    (g : α → ℂ) (K : ℝ) (_hK : 0 ≤ K)
    (h : ∀ x, x ∈ s → ‖g x‖ ≤ K) :
    (∫⁻ x in s, ENNReal.ofReal (‖g x‖ ^ (2 : ℕ)) ∂μ)
      ≤ μ s * ENNReal.ofReal (K ^ (2 : ℕ)) := by
  -- Aplicamos el lema genérico anterior
  refine lintegral_le_of_forall_le_on μ s hs _ _ ?_
  intro x hx
  have h0 : 0 ≤ ‖g x‖ := norm_nonneg (g x)
  -- Probamos la desigualdad dentro de ENNReal
  apply ENNReal.ofReal_le_ofReal
  -- Usamos la monotonía de la potencia
  apply pow_le_pow_left h0 (h x hx) 2

end PaperRH.Analysis
