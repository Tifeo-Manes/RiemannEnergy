/-!
# Main.lean — Cierre del proyecto

Este archivo sirve como “entry point” estándar para `lake build` / `lean Main.lean`.
Importa el punto de entrada limpio `RiemannEnergy` y fija alias estables para los teoremas
finales del cierre A2-b→A2-a (familias en `t`).

No añade axiomas ni `sorry`.
-/

import RiemannEnergy

noncomputable section

namespace RiemannEnergy

/-- Alias estable (dual). -/
theorem Main_gap_stability_eventually_dual_fam :=
  Gap_stability_eventually_dual_fam

/-- Alias estable (primal). -/
theorem Main_gap_stability_eventually_primal_fam :=
  Gap_stability_eventually_primal_fam

end RiemannEnergy
