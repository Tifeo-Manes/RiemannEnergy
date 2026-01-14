import Mathlib
import RiemannEnergy.DirichletPoly
import RiemannEnergy.MontgomeryVaughan

/-!
# Desigualdad de Nikolskii (Formalización Robusta - Corregida)

Corrección:
Se ha corregido el acceso al grado del polinomio. En lugar de usar `N` (variable libre),
usamos `P.N` (el campo N de la estructura DirichletPoly).
-/

noncomputable section

namespace RiemannEnergy

open Complex MeasureTheory Set Filter Real Asymptotics
open scoped Interval

-- =========================================================
-- 1. DEFINICIONES DE NORMAS
-- =========================================================

/-- Norma L-infinito (Supremo) en un intervalo [T, T+H] -/
def L_infty_norm (P : DirichletPoly) (T H : ℝ) : ℝ :=
  sSup {x | ∃ t ∈ Icc (T - H) (T + H), x = ‖P.eval t‖}

/-- Norma L2 (Energía) en un intervalo [T, T+H] -/
def L2_norm_sq (P : DirichletPoly) (T H : ℝ) : ℝ :=
  ∫ t in (T - H)..(T + H), ‖P.eval t‖^2

-- =========================================================
-- 2. LA PROPIEDAD DE NIKOLSKII
-- =========================================================

/--
Propiedad: SatisfiesNikolskii
Un polinomio P satisface la propiedad de Nikolskii si sus picos ($L^\infty$)
están controlados por su energía ($L^2$) de manera "casi" óptima.

Formalmente: (NormaInfinito)^2 ≤ C * N * (Energía / H).
-/
def SatisfiesNikolskii (P : DirichletPoly) : Prop :=
  ∃ C > 0, ∀ (T H : ℝ), H ≥ 1 →
    -- CORRECCIÓN AQUÍ: Usamos (P.N : ℝ) en lugar de N
    (L_infty_norm P T H)^2 ≤ C * (P.N : ℝ) * (L2_norm_sq P T H / H)

/-!
Nota técnica:
El factor (P.N : ℝ) convierte el número natural N del polinomio a un número real
para poder multiplicarlo por la constante C y las normas.
-/

end RiemannEnergy
