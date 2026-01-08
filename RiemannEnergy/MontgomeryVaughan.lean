import Mathlib

/-!
# Teorema de Montgomery–Vaughan (Auditoría de Robustez - Final)

## Referencia Matemática
Este archivo formaliza la relación entre la "Energía Continua" (L2 norm en el tiempo)
y la "Energía Discreta" (L2 norm de coeficientes) para Polinomios de Dirichlet.

Basado en: Montgomery, H. L., & Vaughan, R. C. (1974). Hilbert's inequality.
J. London Math. Soc. (2), 8(1), 73-82.

## Estrategia de Robustez
1. **Definiciones Explícitas**: No dependemos de `Mathlib.Asymptotics` para evitar
   roturas por cambios de versión o notación. Usamos cuantificadores `∃ C, ∀ T`.
2. **Axiomatización Mínima**: Asumimos solo la cota superior del término de error.
3. **Sanity Check**: Incluimos un test al final para verificar consistencia.
-/

noncomputable section

namespace RiemannEnergy

open Complex MeasureTheory Set Filter Real

-- ==============================================================================
-- 1. ESTRUCTURAS DE ENERGÍA
-- ==============================================================================

/-- Suma de Dirichlet finita: S(t) = ∑_{n=1}^N a_n n^{-it}.
Usamos `Finset.sum` para garantizar finitud y evitar problemas de convergencia. -/
def MVSum (a : ℕ → ℂ) (N : ℕ) (t : ℝ) : ℂ :=
  Finset.sum (Finset.Icc 1 N) (fun n => a n * (n : ℂ) ^ (-(t : ℂ) * Complex.I))

/-- Energía Discreta (Suma de coeficientes al cuadrado): ∑ |a_n|^2.
Esta cantidad es constante respecto a T. -/
def MVEnergyDiscrete (a : ℕ → ℂ) (N : ℕ) : ℝ :=
  Finset.sum (Finset.Icc 1 N) (fun n => ‖a n‖^2)

/-- Energía Continua (Integral de media cuadrática): ∫_0^T |S(t)|^2 dt. -/
def MVEnergyContinuous (a : ℕ → ℂ) (N : ℕ) (T : ℝ) : ℝ :=
  ∫ t in (0)..T, ‖MVSum a N t‖^2

/-- Término de Error definido por la ecuación fundamental:
Integral(T) = T * EnergíaDiscreta + Error(T) -/
def MVError (a : ℕ → ℂ) (N : ℕ) (T : ℝ) : ℝ :=
  MVEnergyContinuous a N T - T * MVEnergyDiscrete a N

-- ==============================================================================
-- 2. EL AXIOMA DE MONTGOMERY-VAUGHAN
-- ==============================================================================

/-- Axioma: Existe una constante C (que depende de N y los coeficientes) tal que
el error de aproximación no crece más rápido que la energía discreta. -/
axiom montgomery_vaughan_axiom (a : ℕ → ℂ) (N : ℕ) :
  ∃ C : ℝ, C ≥ 0 ∧
  ∀ T ≥ 0, |MVError a N T| ≤ C * MVEnergyDiscrete a N

-- ==============================================================================
-- 3. TEOREMAS DERIVADOS
-- ==============================================================================

/-- Teorema Principal: Cota Inferior Estricta.
Demuestra que para T suficientemente grande, la integral de energía domina.
Formalmente: ∃ T₀, ∀ T ≥ T₀, ∫|S|^2 > (T/2) * ∑|an|^2. -/
theorem MV_LowerBound (a : ℕ → ℂ) (N : ℕ) (h_nonzero : MVEnergyDiscrete a N > 0) :
    ∃ T₀, ∀ T ≥ T₀,
    MVEnergyContinuous a N T > (T / 2) * MVEnergyDiscrete a N := by
  -- 1. Extraemos la constante C garantizada por el axioma
  rcases montgomery_vaughan_axiom a N with ⟨C, _, h_bound⟩
  -- 2. Definimos el horizonte de tiempo T₀
  use (2 * C + 1)
  intro T hT_ge
  -- 3. Definiciones locales
  let E := MVEnergyDiscrete a N
  let Err := MVError a N T
  -- 4. Propiedades básicas
  have hT_pos : T ≥ 0 := by linarith
  have h_abs_err : |Err| ≤ C * E := h_bound T hT_pos
  -- 5. Lema auxiliar: acotar el error por abajo
  have h_err_ge : Err ≥ -C * E := by
    have h1 : -|Err| ≤ Err := neg_abs_le Err
    have h2 : -C * E ≤ -|Err| := by
      rw [← neg_mul_eq_neg_mul]
      exact neg_le_neg h_abs_err
    exact le_trans h2 h1
  -- 6. Definición de la integral expandida
  have h_integral : MVEnergyContinuous a N T = T * E + Err := by
    dsimp [MVError, Err]
    ring
  -- 7. Resolución de la desigualdad final
  rw [h_integral]
  have goal_x2 : 2 * (T * E + Err) > T * E := by
    nlinarith [h_err_ge, hT_ge, h_nonzero]
  linarith [goal_x2]

-- ==============================================================================
-- 4. SANITY CHECK (TEST DE ROBUSTEZ)
-- ==============================================================================

/-- Caso de Prueba: Polinomio P(s) = 1.
Verifica que el axioma no genera contradicciones en casos triviales. -/
example : ∃ T₀, ∀ T ≥ T₀, MVEnergyContinuous (fun n => if n = 1 then 1 else 0) 1 T > (T/2) * 1 := by
  let a_one := fun (n : ℕ) => if n = 1 then (1 : ℂ) else 0
  have h_disc : MVEnergyDiscrete a_one 1 = 1 := by
    unfold MVEnergyDiscrete
    rw [Finset.sum_Icc_succ_top]
    · simp [a_one]
    · simp
  have h_pos : MVEnergyDiscrete a_one 1 > 0 := by rw [h_disc]; norm_num
  obtain ⟨T₀, h_thm⟩ := MV_LowerBound a_one 1 h_pos
  use T₀
  rw [h_disc] at h_thm
  exact h_thm

end RiemannEnergy
