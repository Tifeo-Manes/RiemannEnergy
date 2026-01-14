import Mathlib
import RiemannEnergy.RiemannZeros
import RiemannEnergy.SmoothWindow

noncomputable section
namespace RiemannEnergy
open Complex Real Nat Topology

/--
Función de Von Mangoldt Λ(n) definida rigurosamente.
Es el "detector de primos": vale log p si n = p^k, 0 en otro caso.
-/
def VonMangoldt (n : ℕ) : ℝ := 
  if IsPrimePow n then Real.log (n.minFac : ℝ) else 0

/-- 
El Flujo Aritmético V(t) - Definición Mejorada (Hard Analysis).
Ahora depende explícitamente de una 'SmoothWindow' V.
Esto garantiza que la suma esté bien comportada y tenga propiedades de decaimiento rápido.
-/
def ArithmeticFlow (t : ℝ) {c₁ c₂ : ℝ} (V : SmoothWindow c₁ c₂) : ℂ := 
  -- CORRECCIÓN: Usamos Real.pi para evitar ambigüedad con la función contadora de primos π(n)
  let N_t := Real.sqrt (t / (2 * Real.pi))
  
  -- Solo sumamos sobre n tales que n / N_t esté en el soporte de V
  -- Como V tiene soporte compacto, solo hay un número finito de tales n.
  -- Tomamos M como el mayor entero tal que M ≤ c₂ * N_t, más 1 para asegurar.
  let M := Nat.ceil (c₂ * N_t)
  
  Finset.sum (Finset.range (M+1)) (fun n => 
    (VonMangoldt n : ℂ) * (V.val (n / N_t)) * cexp (I * t * Real.log n) / Real.sqrt n)

/--
La Energía Real del sistema (Suma parcial normalizada).
Esta es la cantidad física que sometemos a estrés (Saturación vs Colapso).
-/
def TheRealEnergy (N : ℕ) : ℝ := 
  Finset.sum (Finset.range N) (fun n => (VonMangoldt n) / Real.sqrt n)

/--
Axioma de Guinand-Weil: Fórmula Explícita.
Conecta la suma sobre los Ceros (izquierda) con el Flujo Aritmético (derecha).
Ahora requerimos que la función de prueba 'g' venga derivada de una SmoothWindow
para asegurar la convergencia absoluta de ambos lados.
-/
axiom ax_Weil_Explicit_Formula {c₁ c₂ : ℝ} (V : SmoothWindow c₁ c₂) :
  let g := fun (u : ℝ) => MellinTransform V.val (1/2 + I * u)
  ∑' (ρ : ℂ), (if riemannZeta ρ = 0 then g ρ.im else 0) = ∫ t, g t * ArithmeticFlow t V

end RiemannEnergy
