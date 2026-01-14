import Mathlib.Analysis.SpecialFunctions.SmoothTransition
-- import Mathlib.Analysis.Calculus.ContDiff  -- ← QUITAR ESTA LÍNEA

/-!
# WeightV: peso suave basado en `Real.smoothTransition`

En este módulo definimos un peso suave `weightV : ℝ → ℝ` construido a partir de
`Real.smoothTransition`, la función de transición infinitamente derivable de mathlib.

Intuición analítica:
* `Real.smoothTransition x = 0` para `x ≤ 0`,
* `Real.smoothTransition x = 1` para `x ≥ 1`,
* `0 < Real.smoothTransition x < 1` si `0 < x < 1`.

Definimos

`weightV x = Real.smoothTransition (x + 1) - Real.smoothTransition x`.

Esto produce un peso suave que:
* es `C^∞` (contDiff de cualquier orden),
* está acotado,
* sirve como prototipo de ventana suave para integrales locales en t (AFE, Nikolskii, etc.).
-/

noncomputable section

open Real

namespace RiemannEnergy

/-- Peso suave básico construido a partir de `Real.smoothTransition`. -/
def weightV (x : ℝ) : ℝ :=
  Real.smoothTransition (x + 1) - Real.smoothTransition x

/--
`weightV` es infinitamente derivable (`ContDiff` de cualquier orden `n : ℕ∞`).

Usamos que:
* la aplicación `x ↦ x + 1` es `C^∞`,
* la identidad `x ↦ x` es `C^∞`,
* `Real.smoothTransition` es `C^∞`,
* la resta de funciones `C^∞` sigue siendo `C^∞`.
-/
lemma weightV_contDiff {n : ℕ∞} :
    ContDiff ℝ n weightV := by
  -- Parte 1: `x ↦ x + 1` es `C^∞`
  have h_inner_add : ContDiff ℝ n (fun x : ℝ ↦ x + (1 : ℝ)) := by
    -- `x ↦ x + 1` = `id + const 1`
    simpa [add_comm, add_left_comm, add_assoc] using
      (contDiff_id.add
        (contDiff_const : ContDiff ℝ n (fun _ : ℝ ↦ (1 : ℝ))))
  -- Parte 2: composición con `smoothTransition`
  have h1 : ContDiff ℝ n (fun x : ℝ ↦ Real.smoothTransition (x + 1)) := by
    simpa using (Real.smoothTransition.contDiff.comp h_inner_add)
  -- Parte 3: `x ↦ Real.smoothTransition x` es `C^∞`
  have h2 : ContDiff ℝ n (fun x : ℝ ↦ Real.smoothTransition x) := by
    simpa using (Real.smoothTransition.contDiff (n := n))
  -- Parte 4: resta de funciones `C^∞`
  simpa [weightV] using h1.sub h2

end RiemannEnergy
