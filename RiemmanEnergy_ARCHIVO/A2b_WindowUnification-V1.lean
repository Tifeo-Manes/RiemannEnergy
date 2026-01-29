import Mathlib

set_option autoImplicit false

-- Abrimos los scopes necesarios
open scoped BigOperators Topology
open Classical MeasureTheory

namespace PaperRH.A2b

noncomputable section

/-- Intervalo local del paper. -/
def I : Set ℝ := Set.Icc (1 : ℝ) 2

/-- Banda de σ del paper. -/
def InBand (δ σ : ℝ) : Prop :=
  (1/2 : ℝ) + δ ≤ σ ∧ σ ≤ (1 : ℝ) - δ

/-- Peso dual: x^{-2(1-σ)}. -/
def wDual (σ x : ℝ) : ℝ := Real.rpow x (-2 * (1 - σ))

/-- Peso primal: x^{-2σ}. -/
def wPrimal (σ x : ℝ) : ℝ := Real.rpow x (-2 * σ)

/-- Diferencia local al cuadrado (norma en ℂ). -/
def sq (z : ℂ) : ℝ := ‖z‖ ^ (2 : ℕ)

/-!
Lema genérico (compacto):
Si en I=[1,2] tenemos ‖f x‖ ≤ K, entonces ∫_I ‖f x‖^2 ≤ (vol I) * K^2.
-/
axiom integral_sq_le_of_sup
  (f : ℝ → ℂ) (K : ℝ) :
  (0 ≤ K) →
  (∀ x, x ∈ I → ‖f x‖ ≤ K) →
  (∫ x in I, sq (f x) ∂volume)
    ≤ (volume I).toReal * (K^2)

/-!
Hipótesis “C⁰-close” del Módulo A2-b.
-/
structure C0Close (ProfileSN ProfileInf : ℝ → ℂ) : Prop where
  (bound :
    ∀ (t : ℝ) (J : ℕ),
      ∃ C : ℝ, 0 ≤ C ∧
        (∀ x, x ∈ I → ‖ProfileSN x - ProfileInf x‖ ≤ C * |t| ^ (-(J : ℝ))))

/-!
Datos mínimos para la unificación dual.
-/
structure DualData where
  V    : ℝ → ℂ
  η    : ℝ → ℂ
  WSN  : ℝ → ℂ
  Winf : ℝ → ℂ
  hV   : ∀ x, V x = η x * Winf x

/-- El dual local del paper: W_loc(x) = η(x) W_SN(x). -/
def DualData.Wloc (D : DualData) : ℝ → ℂ := fun x => D.η x * D.WSN x

/-- Diferencia clave: W_loc - V = η (W_SN - W_inf). -/
lemma dual_diff_factor (D : DualData) :
  ∀ x, D.Wloc x - D.V x = D.η x * (D.WSN x - D.Winf x) := by
  intro x
  dsimp [DualData.Wloc]
  rw [D.hV x]
  ring

/-!
Unificación dual (versión Lean).
-/
theorem WindowUnification_dual_L2
  (δ : ℝ) (D : DualData)
  (hη : ∃ M : ℝ, 0 ≤ M ∧ (∀ x, x ∈ I → ‖D.η x‖ ≤ M))
  (hClose : C0Close D.WSN D.Winf) :
  ∀ (t : ℝ) (J : ℕ),
    ∃ C' : ℝ, 0 ≤ C' ∧
      (∫ x in I, sq (D.Wloc x - D.V x) ∂volume)
        ≤ C' * |t| ^ (-(2 * (J : ℝ))) := by
  intro t J
  rcases hη with ⟨M, hM0, hM⟩
  rcases hClose.bound t J with ⟨C, hC0, hC⟩

  -- 1. Cota superior (Sup bound) en I
  let K := (M * C) * |t| ^ (-(J : ℝ))

  have hSupDiff : ∀ x, x ∈ I → ‖D.Wloc x - D.V x‖ ≤ K := by
    intro x hx
    rw [dual_diff_factor D x]
    rw [norm_mul]
    have h_prod : ‖D.η x‖ * ‖D.WSN x - D.Winf x‖ ≤ M * (C * |t| ^ (-(J : ℝ))) := by
      apply mul_le_mul (hM x hx) (hC x hx) (norm_nonneg _) hM0
    apply le_trans h_prod
    dsimp [K]
    apply le_of_eq; ring

  -- 2. Pasar de Sup a L2
  have hK0 : 0 ≤ K := by
    dsimp [K]
    apply mul_nonneg (mul_nonneg hM0 hC0)
    apply Real.rpow_nonneg (abs_nonneg t)

  have hL2 := integral_sq_le_of_sup (fun x => D.Wloc x - D.V x) K hK0 hSupDiff

  -- 3. Ajuste final de constantes
  let C' := (volume I).toReal * (M * C)^2
  exists C'
  constructor
  · -- C' >= 0
    apply mul_nonneg
    · exact ENNReal.toReal_nonneg -- Corrección aquí
    · apply pow_two_nonneg
  · -- Desigualdad final
    dsimp [C', K] at hL2 ⊢
    -- Simplificación de exponentes
    have hPow : ((M * C) * |t| ^ (-(J : ℝ))) ^ 2 = (M * C) ^ 2 * |t| ^ (-(2 * (J : ℝ))) := by
      rw [mul_pow]
      congr 1
      rw [←Real.rpow_natCast] -- Corrección deprecation
      rw [←Real.rpow_mul (abs_nonneg t)]
      ring
    
    rw [hPow] at hL2
    -- Alineamos paréntesis: convertimos A * (B * C) en A * B * C
    rw [← mul_assoc] at hL2
    exact hL2

end

end PaperRH.A2b
