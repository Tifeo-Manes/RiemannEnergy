import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Instances.Real
import Mathlib.Tactic -- Import vital para que linarith funcione bien
import RiemannEnergy.EnergyProps

noncomputable section
namespace RiemannEnergy

open Real Filter Topology

/-!
# Derivaciones Matemáticas Rigurosas (Calculus Core)
Versión Definitiva: Nombres estándar sin namespaces.
-/

-- ==============================================================================
-- 1. PRUEBA DEL COMPORTAMIENTO DE FASE ESTACIONARIA (Blowup)
-- ==============================================================================

/--
Definición del Modelo de Crecimiento.
-/
def StationaryPhase_Model (β : ℝ) (T : ℝ) : ℝ := T^(2 * β + 1)

/--
LEMA DE CÁLCULO 1:
Si β > 1/2, el modelo explota a infinito.
-/
theorem Calculus_Stationary_Phase_Blowup (β : ℝ) (h : β > 1/2) :
  Tendsto (StationaryPhase_Model β) atTop atTop := by
  -- 1. Desplegamos la definición
  unfold StationaryPhase_Model
  
  -- 2. Aplicamos el teorema estándar (sin 'Real.', sin '_of_pos')
  -- Dice: x^s tiende a infinito si s > 0
  apply tendsto_rpow_atTop
  
  -- 3. Demostramos que el exponente es positivo
  -- (2 * β + 1 > 2 > 0)
  linarith

-- ==============================================================================
-- 2. PRUEBA DEL COMPORTAMIENTO DE GRAN CRIBA (Collapse)
-- ==============================================================================

/--
Definición del Modelo de Colapso.
-/
def LargeSieve_Model (δ : ℝ) (N : ℝ) : ℝ := N^(-δ)

/--
LEMA DE CÁLCULO 2:
Si δ > 0, el modelo colapsa a cero.
-/
theorem Calculus_LargeSieve_Collapse (δ : ℝ) (h : δ > 0) :
  Tendsto (LargeSieve_Model δ) atTop (nhds 0) := by
  -- 1. Desplegamos la definición
  unfold LargeSieve_Model
  
  -- 2. Aplicamos el teorema estándar (sin 'Real.', sin '_neg')
  -- Dice: x^s tiende a 0 si s < 0
  apply tendsto_rpow_neg_atTop
  
  -- 3. Demostramos que el exponente es negativo
  -- (-δ < 0 ya que δ > 0)
  linarith

end RiemannEnergy
