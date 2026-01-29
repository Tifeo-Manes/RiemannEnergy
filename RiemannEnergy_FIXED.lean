
/-!
# RiemannEnergy

Punto de entrada **mínimo** del proyecto.

⚠️ En Lean, los `import` **deben ir al principio del archivo** (antes de `namespace`,
`section`, `set_option`, definiciones, etc.). Este archivo está ordenado para cumplirlo.
-/

import RiemannEnergy.A2b_FamilyClosure_FINAL

noncomputable section
namespace RiemannEnergy

-- Aquí no hace falta nada más: al importar `A2b_FamilyClosure_FINAL` arrastras transitivamente
-- todos los módulos necesarios para el cierre (A2-b → CloseHyp → Gap_stability).

end RiemannEnergy
