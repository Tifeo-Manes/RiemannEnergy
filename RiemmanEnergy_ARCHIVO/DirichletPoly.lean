import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Dirichlet polynomials (Infraestructura Completa)

En este módulo definimos las estructuras base para los polinomios de Dirichlet.
-/

noncomputable section

-- Abrimos scopes necesarios para notación
open scoped BigOperators
open MeasureTheory

namespace RiemannEnergy

/--
Un polinomio de Dirichlet finito:
Datos de longitud `N` y una función de coeficientes `coeff`.
-/
structure DirichletPoly where
  N : ℕ
  coeff : ℕ → ℂ

namespace DirichletPoly

/-- Evaluación del polinomio en un punto complejo `s`. -/
def eval (P : DirichletPoly) (s : ℂ) : ℂ :=
  (Finset.Icc 1 P.N).sum (fun n => P.coeff n * (n : ℂ) ^ (-s))

/-- Función auxiliar A(t) = P(σ + it) para una parte real fija σ. -/
def A_of (P : DirichletPoly) (σ t : ℝ) : ℂ :=
  let s : ℂ := (σ : ℂ) + Complex.I * (t : ℂ)
  P.eval s

/-- Energía Discreta: ∑ |a_n|^2. -/
def discreteEnergy (P : DirichletPoly) : ℝ :=
  (Finset.Icc 1 P.N).sum (fun n => ‖P.coeff n‖ ^ 2)

/--
Energía Diagonal Pura:
La suma de los cuadrados de los coeficientes ponderados por n^{-2σ}.
-/
def diagonalEnergy (P : DirichletPoly) (σ : ℝ) : ℝ :=
  (Finset.Icc 1 P.N).sum (fun n =>
    ‖P.coeff n‖ ^ 2 * (n : ℝ) ^ (-2 * σ))

/-- Lema básico: La energía discreta es siempre no negativa. -/
lemma discreteEnergy_nonneg (P : DirichletPoly) :
    0 ≤ P.discreteEnergy := by
  apply Finset.sum_nonneg
  intro n _
  apply sq_nonneg

/--
Energía continua local asociada a `P`, con parte real `σ` y ventana `[-H, H]`.
USO ROBUSTO: Integral de intervalo orientada (-H)..H.
-/
def continuousEnergyLoc (P : DirichletPoly) (σ H : ℝ) : ℝ :=
  ∫ t in (-H)..H, ‖P.A_of σ t‖ ^ 2

end DirichletPoly
end RiemannEnergy
