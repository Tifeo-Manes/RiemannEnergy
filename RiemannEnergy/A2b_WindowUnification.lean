import Mathlib

set_option autoImplicit false
-- Desactivamos el límite de cómputo para asegurar que las integrales complejas terminen
set_option maxHeartbeats 0

open scoped BigOperators Topology ENNReal
open Classical MeasureTheory

namespace PaperRH.A2b

noncomputable section

/-!
  ================================================================================
  1. DEFINICIONES BÁSICAS
  ================================================================================
-/

/-- Intervalo local del paper [1,2]. -/
def I : Set ℝ := Set.Icc (1 : ℝ) 2

/-- La medibilidad del intervalo es necesaria. -/
lemma measurableSet_I : MeasurableSet I := measurableSet_Icc

/-- Estructura para funciones acotadas (Data). -/
structure BoundedOn (s : Set ℝ) (f : ℝ → ℂ) where
  mk ::
  (M : ℝ)
  (hM : 0 ≤ M)
  (bound : ∀ x, x ∈ s → ‖f x‖ ≤ M)

/-- Estructura para convergencia C0 (Prop). -/
structure CloseOnI (s : Set ℝ) (f g : ℝ → ℂ) : Prop where
  mk ::
  (bound : ∀ (t : ℝ) (J : ℕ),
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ x, x ∈ s → ‖f x - g x‖ ≤ C * |t| ^ (-(J : ℝ))))

/-- Estructura para el peso superior (Data). -/
structure WeightUpper (s : Set ℝ) (ω : ℝ → ℝ≥0∞) where
  mk ::
  (W : ℝ≥0∞)
  (upper : ∀ x, x ∈ s → ω x ≤ W)

/-!
  ================================================================================
  2. DATOS DUALES Y PRIMALES
  ================================================================================
-/

structure DualData where
  V    : ℝ → ℂ
  η    : ℝ → ℂ
  WSN  : ℝ → ℂ
  Winf : ℝ → ℂ
  hV   : ∀ x, V x = η x * Winf x

def DualData.Wloc (D : DualData) : ℝ → ℂ := fun x => D.η x * D.WSN x

lemma dual_diff_factor (D : DualData) :
  ∀ x, D.Wloc x - D.V x = D.η x * (D.WSN x - D.Winf x) := by
  intro x
  dsimp [DualData.Wloc]
  rw [D.hV x]
  ring

structure PrimalData where
  V    : ℝ → ℂ
  η    : ℝ → ℂ
  VSN  : ℝ → ℂ
  Vinf : ℝ → ℂ
  hP   : ∀ x, V x = η x * Vinf x

def PrimalData.Vloc (P : PrimalData) : ℝ → ℂ := fun x => P.η x * P.VSN x

lemma primal_diff_factor (P : PrimalData) :
  ∀ x, P.Vloc x - P.V x = P.η x * (P.VSN x - P.Vinf x) := by
  intro x
  dsimp [PrimalData.Vloc]
  rw [P.hP x]
  ring

/-!
  ================================================================================
  3. TEOREMAS DE UNIFICACIÓN (FINAL)
  ================================================================================
-/

theorem WindowUnification_dual_L2_weighted
    (D : DualData)
    (hη : BoundedOn I D.η)
    (hClose : CloseOnI I D.WSN D.Winf)
    (ω : ℝ → ℝ≥0∞) (hW : WeightUpper I ω) :
    ∀ (t : ℝ) (J : ℕ),
      ∃ K : ℝ, 0 ≤ K ∧
        (∫⁻ x in I, (ω x) * ENNReal.ofReal (‖D.Wloc x - D.V x‖ ^ (2 : ℕ)) ∂volume)
          ≤ (volume I) * (hW.W * ENNReal.ofReal (K ^ (2 : ℕ))) := by
  intro t J
  rcases hClose.bound t J with ⟨C, hC0, hC⟩
  
  let powTerm : ℝ := |t| ^ (-(J : ℝ))
  let K : ℝ := hη.M * (C * powTerm)
  
  have hK0 : 0 ≤ K := by
    have hPow0 : 0 ≤ powTerm := Real.rpow_nonneg (abs_nonneg t) _
    have : 0 ≤ C * powTerm := mul_nonneg hC0 hPow0
    dsimp [K]
    exact mul_nonneg hη.hM this

  refine ⟨K, hK0, ?_⟩

  have hPoint :
      ∀ x, x ∈ I →
        (ω x) * ENNReal.ofReal (‖D.Wloc x - D.V x‖ ^ (2 : ℕ))
          ≤ hW.W * ENNReal.ofReal (K ^ (2 : ℕ)) := by
    intro x hx
    have hω : ω x ≤ hW.W := hW.upper x hx
    have hηx : ‖D.η x‖ ≤ hη.M := hη.bound x hx
    have hWx : ‖D.WSN x - D.Winf x‖ ≤ C * powTerm := hC x hx
    
    have hNorm : ‖D.Wloc x - D.V x‖ ≤ K := by
      rw [dual_diff_factor D x, norm_mul]
      dsimp [K]
      apply le_trans (mul_le_mul hηx hWx (norm_nonneg _) hη.hM)
      apply le_of_eq; ring

    have hSq : ENNReal.ofReal (‖D.Wloc x - D.V x‖ ^ (2 : ℕ))
             ≤ ENNReal.ofReal (K ^ (2 : ℕ)) := by
      apply ENNReal.ofReal_le_ofReal
      apply pow_le_pow_left (norm_nonneg _) hNorm 2

    apply mul_le_mul hω hSq (by simp) (by simp)

  let f_integrand := fun x => (ω x) * ENNReal.ofReal (‖D.Wloc x - D.V x‖ ^ 2)
  let C_bound := hW.W * ENNReal.ofReal (K ^ (2 : ℕ))
  
  have h_mono : ∀ x, I.indicator f_integrand x ≤ I.indicator (fun _ => C_bound) x := by
    intro x
    by_cases hx : x ∈ I
    · simp only [Set.indicator_of_mem hx]
      exact hPoint x hx
    · simp only [Set.indicator_of_not_mem hx, le_refl]

  rw [← lintegral_indicator _ measurableSet_I]
  apply le_trans (lintegral_mono h_mono)
  rw [lintegral_indicator _ measurableSet_I]
  
  -- SOLUCIÓN FINAL:
  -- 1. Aplicamos integral constante
  rw [set_lintegral_const I]
  -- 2. Expandimos definición de C_bound
  dsimp only [C_bound]
  -- 3. Acomodamos asociatividad y conmutatividad
  simp only [mul_comm, mul_assoc, mul_left_comm]
  -- 4. Cerramos explícitamente la reflexividad (A ≤ A)
  exact le_refl _


theorem WindowUnification_primal_L2_weighted
    (P : PrimalData)
    (hη : BoundedOn I P.η)
    (hClose : CloseOnI I P.VSN P.Vinf)
    (ω : ℝ → ℝ≥0∞) (hW : WeightUpper I ω) :
    ∀ (t : ℝ) (J : ℕ),
      ∃ K : ℝ, 0 ≤ K ∧
        (∫⁻ x in I, (ω x) * ENNReal.ofReal (‖P.Vloc x - P.V x‖ ^ (2 : ℕ)) ∂volume)
          ≤ (volume I) * (hW.W * ENNReal.ofReal (K ^ (2 : ℕ))) := by
  intro t J
  rcases hClose.bound t J with ⟨C, hC0, hC⟩
  
  let powTerm : ℝ := |t| ^ (-(J : ℝ))
  let K : ℝ := hη.M * (C * powTerm)
  
  have hK0 : 0 ≤ K := by
    have hPow0 : 0 ≤ powTerm := Real.rpow_nonneg (abs_nonneg t) _
    have : 0 ≤ C * powTerm := mul_nonneg hC0 hPow0
    dsimp [K]
    exact mul_nonneg hη.hM this

  refine ⟨K, hK0, ?_⟩

  have hPoint :
      ∀ x, x ∈ I →
        (ω x) * ENNReal.ofReal (‖P.Vloc x - P.V x‖ ^ (2 : ℕ))
          ≤ hW.W * ENNReal.ofReal (K ^ (2 : ℕ)) := by
    intro x hx
    have hω : ω x ≤ hW.W := hW.upper x hx
    have hηx : ‖P.η x‖ ≤ hη.M := hη.bound x hx
    have hVx : ‖P.VSN x - P.Vinf x‖ ≤ C * powTerm := hC x hx
    
    have hNorm : ‖P.Vloc x - P.V x‖ ≤ K := by
      rw [primal_diff_factor P x, norm_mul]
      dsimp [K]
      apply le_trans (mul_le_mul hηx hVx (norm_nonneg _) hη.hM)
      apply le_of_eq; ring

    have hSq : ENNReal.ofReal (‖P.Vloc x - P.V x‖ ^ (2 : ℕ))
             ≤ ENNReal.ofReal (K ^ (2 : ℕ)) := by
      apply ENNReal.ofReal_le_ofReal
      apply pow_le_pow_left (norm_nonneg _) hNorm 2

    apply mul_le_mul hω hSq (by simp) (by simp)

  let f_integrand := fun x => (ω x) * ENNReal.ofReal (‖P.Vloc x - P.V x‖ ^ 2)
  let C_bound := hW.W * ENNReal.ofReal (K ^ (2 : ℕ))

  have h_mono : ∀ x, I.indicator f_integrand x ≤ I.indicator (fun _ => C_bound) x := by
    intro x
    by_cases hx : x ∈ I
    · simp only [Set.indicator_of_mem hx]
      exact hPoint x hx
    · simp only [Set.indicator_of_not_mem hx, le_refl]

  rw [← lintegral_indicator _ measurableSet_I]
  apply le_trans (lintegral_mono h_mono)
  rw [lintegral_indicator _ measurableSet_I]
  
  -- SOLUCIÓN FINAL:
  rw [set_lintegral_const I]
  dsimp only [C_bound]
  simp only [mul_comm, mul_assoc, mul_left_comm]
  exact le_refl _

end

end PaperRH.A2b
