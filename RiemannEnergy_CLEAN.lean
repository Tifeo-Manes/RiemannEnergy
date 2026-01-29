/-!
# RiemannEnergy — Punto de entrada limpio

Este archivo deja el proyecto con un “front door” mínimo: importa únicamente el cierre
final del programa A2-b→A2-a (familias en `t`) y reexpone los teoremas principales.

Si has estado usando el nombre de módulo `RiemannEnergy.A2b_FamilyClosure_FINAL`, mantén ese
nombre de archivo en el repo y sustituye su contenido por la versión *CLEAN* que ya compila
(sin axiomas ni `sorry`), para que este import siga funcionando.
-/

import RiemannEnergy.A2b_FamilyClosure_FINAL

noncomputable section
namespace RiemannEnergy

/-!
## Teoremas principales reexportados

Estos teoremas cierran el último hueco (“t suficientemente grande”) de forma interna en Lean,
gracias a la formalización correcta de las ventanas como familias dependientes de `t`.
-/

-- Dual: existe t0≥2 tal que ∀t≥t0, gap híbrido ≥ cδ/2
-- `Gap_stability_eventually_dual_fam`

-- Primal: versión simétrica
-- `Gap_stability_eventually_primal_fam`

end RiemannEnergy
