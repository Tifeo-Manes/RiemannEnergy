import RiemannEnergy
import RiemannEnergy.Program

/-
  Fichero principal mínimo. Definimos "tests fantasma" para que Lean
  verifique los tipos clave del programa.
-/

-- Lado lógico puro: de hipótesis analíticas a ausencia de ceros off-critical.
def _test_noOffCriticalZero :
    RiemannEnergy.AnalyticHypotheses → ¬ RiemannEnergy.HasOffCriticalZero :=
  RiemannEnergy.noOffCriticalZero

-- AFE suavizada: existencia del modelo y su validez.
def _test_AFE (A : RiemannEnergy.SmoothAFE) :=
  RiemannEnergy.AFE_smooth_model A

-- Pilares empaquetados: de `Pillars` a ausencia de ceros off-critical.
def _test_pillars (h : RiemannEnergy.Pillars) :
    ¬ RiemannEnergy.HasOffCriticalZero :=
  RiemannEnergy.noOffCriticalZero (h.toAnalyticHypotheses)

-- Programa RH completo: Pilares I–V ⇒ no hay ceros off-critical.
def _test_program (P : RiemannEnergy.ProgramRH) :
    ¬ RiemannEnergy.HasOffCriticalZero :=
  RiemannEnergy.ProgramRH.noOffCriticalZero_from_program P

def main : IO Unit :=
  IO.println "RiemannEnergy project builds."
