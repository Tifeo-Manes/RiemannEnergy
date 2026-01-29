# RiemannEnergy (Lean 4.8) — cierre formal del programa A2-b → A2-a

Este repositorio contiene una formalización en **Lean 4.8** (Mathlib) de un “pipeline” analítico que encadena:

**A2-b (unificación L² ponderada)** → **cota `EwENN` (lintegral ENNReal)** → **`CloseHyp`** → **A2-a (`Gap_stability`)**,

y cierra el último hueco habitual (“**t suficientemente grande**”) mediante una formalización correcta de las **ventanas como familias dependientes de `t`**.

---

## 1) Cómo compilar

Requisitos:

- Lean **4.8.x**
- mathlib (vía `lake`)

Comandos típicos:

```bash
lake build
```

Para auditar que no quedan `sorry`:

```bash
lake env lean --no-sorry Main.lean
```

---

## 2) Punto de entrada del proyecto

El “front door” mínimo es:

- `RiemannEnergy.lean`  
  que **solo importa** el cierre final:

```lean
import RiemannEnergy.A2b_FamilyClosure_FINAL
```
Para disponer de un entry-point estándar del proyecto:

- `Main.lean`  
  importa `RiemannEnergy` y fija alias estables para los teoremas finales.

---

## 3) Resultado matemático “exportado” por el cierre

En el cierre final (familias en `t`) se obtiene:

- **Dual (familia):**
  ```lean
  Gap_stability_eventually_dual_fam :
    ∃ t0 ≥ 2, ∀ t ≥ t0, ∀ σ ∈ Iδ δ, Ghyb V (Wloc t) σ ≥ (1/2) * cδ
  ```

- **Primal (familia):**
  ```lean
  Gap_stability_eventually_primal_fam :
    ∃ t0 ≥ 2, ∀ t ≥ t0, ∀ σ ∈ Iδ δ, Ghyb V (Vloc t) σ ≥ (1/2) * cδ
  ```

En `Main.lean` se reexportan como alias:

- `RiemannEnergy.Main_gap_stability_eventually_dual_fam`
- `RiemannEnergy.Main_gap_stability_eventually_primal_fam`

---

## 4) Dónde se cierra “t suficientemente grande”

El paso “**t grande**” **no se postula** como axioma: se demuestra por aritmética real una vez que
las ventanas se formalizan como **familias**:

- en lugar de `WSN : ℝ → ℂ`, se usa
  `WSN : ℝ → ℝ → ℂ` (i.e., `WSN t x`)
- la hipótesis de cercanía es uniforme en `t`, con constante `C_J` independiente de `t`:

  \[
  \forall J,\ \exists C_J \ge 0,\ \forall t,\forall x\in I,\
  \|WSN(t,x)-Winf(x)\|\le \frac{C_J}{|t|^J}.
  \]

A partir de ahí se prueba un lema puramente real del tipo:

> si `A ≥ 0` y `ε > 0`, entonces existe `t0 ≥ 2` con `∀ t ≥ t0, A/t ≤ ε`.

Este es el mecanismo formal que reemplaza la intuición analítica de “tomar t suficientemente grande”.

---

## 5) Estructura de archivos (módulos principales)

### Núcleo del cierre final

- `RiemannEnergy/A2b_FamilyClosure_FINAL.lean`  
  Cierre final “familias en t”. Encadena A2-b → `EwENN` → `CloseHyp` → `Gap_stability`
  y prueba el paso “t grande” internamente.

- `RiemannEnergy/A2bToA2a_CloseHyp.lean`  
  Traducción **ENNReal lintegral** (`EwENN`) → **real integral** (`Ew`) y empaquetado de `CloseHyp`.

- `RiemannEnergy/A2bBridge.lean`  
  Puente A2-b → cota `EwENN` (con peso `omegaSigma`).

- `RiemannEnergy/GapStability.lean`  
  Módulo A2-a: de `CloseHyp` deduce la cota positiva del gap híbrido.

### Módulos auxiliares usados por A2-b / A2-a

- `RiemannEnergy/A2b_WindowUnification.lean`  
  Unificación ponderada L² (forma “A2-b”).

- `RiemannEnergy/WeightedCS.lean`  
  Lemas funcionales / Cauchy–Schwarz ponderado y utilidades relacionadas.

- `RiemannEnergy/CompactBounds.lean`  
  Cotas uniformes / compactificación (si aplica en tu desarrollo).

---

## 6) Tabla de dependencias (quién importa a quién)

> Nota: en Lean los imports son transitivos. La tabla siguiente describe las **dependencias directas**
> tal como se organiza el cierre final del programa.

| Archivo / módulo | Importa directamente | Rol |
|---|---|---|
| `RiemannEnergy.lean` | `RiemannEnergy.A2b_FamilyClosure_FINAL` | Root mínimo del proyecto |
| `Main.lean` | `RiemannEnergy` | Entry-point y alias estables |
| `A2b_FamilyClosure_FINAL.lean` | `A2bToA2a_CloseHyp`, `A2bBridge` (+ Mathlib básico) | Cierre final sin axiomas |
| `A2bToA2a_CloseHyp.lean` | `A2bBridge`, `GapStability` (+ Mathlib integrales) | `EwENN`→`Ew` y `CloseHyp` |
| `A2bBridge.lean` | `A2b_WindowUnification`, `GapStability` (+ Mathlib) | A2-b → `EwENN` |
| `GapStability.lean` | `WeightedCS` (+ Mathlib) | A2-a (`Gap_stability`) |
| `A2b_WindowUnification.lean` | Mathlib | Unificación L² ponderada |
| `WeightedCS.lean` | Mathlib | Lemas de desigualdades/medida/normas |
| `CompactBounds.lean` | Mathlib | Cotas en compactos (si se usa) |

### Mapa (grafo) de alto nivel

```
Main.lean
└── RiemannEnergy.lean
    └── RiemannEnergy/A2b_FamilyClosure_FINAL.lean
        ├── RiemannEnergy/A2bToA2a_CloseHyp.lean
        │   ├── RiemannEnergy/A2bBridge.lean
        │   │   └── RiemannEnergy/A2b_WindowUnification.lean
        │   └── RiemannEnergy/GapStability.lean
        │       └── RiemannEnergy/WeightedCS.lean
        └── RiemannEnergy/A2bBridge.lean
```

---

## 7) Cómo auditar el cierre (sin axiomas/sorries)

### 7.1 Buscar `sorry` / `axiom` en el repo
```bash
grep -RIn --exclude-dir=.lake -E "\bsorry\b|\badmit\b" .
grep -RIn --exclude-dir=.lake -E "\baxiom\b|\bconstant\b" RiemannEnergy
```

### 7.2 Ver axiomas usados por el teorema final
En un archivo de auditoría:

```lean
import RiemannEnergy

#print axioms RiemannEnergy.Gap_stability_eventually_dual_fam
#print axioms RiemannEnergy.Gap_stability_eventually_primal_fam
```

---

## 8) Cómo regenerar automáticamente un mapa de imports

Para listar imports:

```bash
grep -RIn --exclude-dir=.lake '^import ' RiemannEnergy
```

Para ver el orden de compilación que decide `lake`:

```bash
lake build -Ktrace=true
```

---

## 9) Contacto / referencia

- Autor: R. Gonmar [r.gonmar(arroba)diabasa.es]
- Paper asociado: `Paper_RH_Programa_Incondicional_FINAL_UNICO_CLEAN9_INCOND_FINAL.tex`
