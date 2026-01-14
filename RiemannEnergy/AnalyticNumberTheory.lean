import Mathlib
import Mathlib.Analysis.SpecificLimits.Basic
import RiemannEnergy.EnergyProps
import RiemannEnergy.ExplicitFormulas

noncomputable section
namespace RiemannEnergy
open Real Filter Topology

/--
Axioma Físico: Decaimiento de Potencias (Paper IV).
La energía decae al menos como n^-δ.
-/
axiom ax_Moebius_Power_Decay :
  ∃ (δ : ℝ), δ > 0 ∧ ∀ (n : ℕ), n > 0 → |TheRealEnergy n| ≤ (n : ℝ) ^ (-δ)

/--
Lema Auxiliar: Los naturales tienden a infinito en los reales.
Demostración manual para robustez.
-/
lemma nat_goes_to_infinity : Tendsto (fun (n : ℕ) => (n : ℝ)) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  obtain ⟨n, hn⟩ := exists_nat_ge b
  use n
  intro m hm
  apply le_trans hn
  exact Nat.cast_le.mpr hm

/--
TEOREMA: El Colapso es consecuencia del decaimiento.
-/
theorem Derived_Collapse_Constructive : Collapse TheRealEnergy := by
  rw [Collapse, Metric.tendsto_nhds]
  intro ε h_eps
  obtain ⟨δ, h_del, h_bnd⟩ := ax_Moebius_Power_Decay
  -- Paso 1: Límite en Reales (x^-δ -> 0)
  have h_lim_real : Tendsto (fun (x:ℝ) => x ^ (-δ)) atTop (nhds 0) :=
    tendsto_rpow_neg_atTop h_del
  -- Paso 2: Composición con Naturales
  have h_lim : Tendsto (fun (n:ℕ) => (n:ℝ)^(-δ)) atTop (nhds 0) :=
    h_lim_real.comp nat_goes_to_infinity
  -- Paso 3: Definición métrica
  rw [Metric.tendsto_nhds] at h_lim
  filter_upwards [h_lim ε h_eps, Filter.eventually_gt_atTop 0] with n h_small_real h_pos
  -- Paso 4: Ajuste de Tipos
  rw [dist_0_eq_abs] at h_small_real ⊢
  have h_abs_pos : |(n:ℝ)^(-δ)| = (n:ℝ)^(-δ) := 
    abs_of_pos (rpow_pos_of_pos (Nat.cast_pos.mpr h_pos) _)
  rw [h_abs_pos] at h_small_real
  -- Paso 5: Cálculo final
  calc |TheRealEnergy n|
      ≤ (n:ℝ)^(-δ) := h_bnd n h_pos
    _ < ε          := h_small_real

end RiemannEnergy
