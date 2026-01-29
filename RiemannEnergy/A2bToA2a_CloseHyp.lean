
/-
File: RiemannEnergy/A2bToA2a_CloseHyp.lean   (PATCH v2)

Fix principal (mathlib Lean 4.8):
  `integral_eq_lintegral_of_nonneg_ae` en tu versión espera
  `AEStronglyMeasurable f μ` (no `Integrable f μ`).
  Por tanto, pasamos `hf_int.aestronglyMeasurable`.

Además, usamos `hK0` para evitar warning de variable sin uso.
-/

import Mathlib.MeasureTheory.Integral.Lebesgue
import RiemannEnergy.A2bBridge
import RiemannEnergy.GapStability

set_option autoImplicit false

open Classical
open MeasureTheory
open scoped BigOperators

namespace RiemannEnergy

noncomputable section

def ewIntegrand (F : ℝ → ℂ) (σ : ℝ) : ℝ → ℝ :=
  fun x => ‖F x‖ ^ (2 : ℕ) * w (1 - σ) x

lemma ewIntegrand_continuousOn {F : ℝ → ℂ} (σ : ℝ)
    (hF : ContinuousOn F I) :
    ContinuousOn (ewIntegrand F σ) I := by
  have hnorm : ContinuousOn (fun x => ‖F x‖) I :=
    continuous_norm.comp_continuousOn hF
  have hpow : ContinuousOn (fun x => ‖F x‖ ^ (2 : ℕ)) I := hnorm.pow 2
  exact hpow.mul (w_continuous (1 - σ))

lemma ewIntegrand_nonneg_ae {F : ℝ → ℂ} (σ : ℝ) :
    ∀ᵐ x : ℝ ∂μI, 0 ≤ ewIntegrand F σ x := by
  refine ae_mem_I.mono ?_
  intro x hx
  dsimp [ewIntegrand]
  have hn : 0 ≤ ‖F x‖ ^ (2 : ℕ) := by positivity
  have hw : 0 ≤ w (1 - σ) x := w_nonneg (1 - σ) x hx
  exact mul_nonneg hn hw

theorem Ew_eq_toReal_EwENN {F : ℝ → ℂ} (σ : ℝ)
    (hF : ContinuousOn F I) :
    Ew F σ = (EwENN F σ).toReal := by
  classical
  let f : ℝ → ℝ := ewIntegrand F σ

  have hf_int : Integrable f μI :=
    integrable_of_continuousOn (ewIntegrand_continuousOn (F := F) σ hF)
  have hf_nonneg : ∀ᵐ x : ℝ ∂μI, 0 ≤ f x := by
    simpa [f] using (ewIntegrand_nonneg_ae (F := F) σ)

  have hEw : Ew F σ = ∫ x : ℝ, f x ∂μI := by
    simp [Ew, P, f, ewIntegrand]

  -- FIX: tu mathlib pide `AEStronglyMeasurable f μI`
  have h_toReal :
      (∫ x : ℝ, f x ∂μI) =
        (∫⁻ x : ℝ, ENNReal.ofReal (f x) ∂μI).toReal := by
    simpa using
      (integral_eq_lintegral_of_nonneg_ae hf_nonneg hf_int.aestronglyMeasurable)

  have h_lintegral :
      (∫⁻ x : ℝ, ENNReal.ofReal (f x) ∂μI) = EwENN F σ := by
    have h_restrict :
        (∫⁻ x : ℝ, ENNReal.ofReal (f x) ∂μI)
          = (∫⁻ x in I, ENNReal.ofReal (f x) ∂volume) := by
      simp [μI, Measure.restrict_restrict, Set.inter_eq_left.mpr (by intro x hx; exact hx)]

    have h_ae :
        (fun x => ENNReal.ofReal (f x)) =ᵐ[volume.restrict I]
          (fun x => (omegaSigma σ x) * ENNReal.ofReal (‖F x‖ ^ (2 : ℕ))) := by
      refine (ae_restrict_mem measurableSet_I).mono ?_
      intro x hx
      have hn : 0 ≤ ‖F x‖ ^ (2 : ℕ) := by positivity
      have hw : 0 ≤ w (1 - σ) x := w_nonneg (1 - σ) x hx
      have : ENNReal.ofReal (f x) =
          ENNReal.ofReal (w (1 - σ) x) * ENNReal.ofReal (‖F x‖ ^ (2 : ℕ)) := by
        simpa [f, ewIntegrand, mul_comm, mul_left_comm, mul_assoc,
              ENNReal.ofReal_mul, hw, hn]
      simpa [omegaSigma, this, mul_assoc, mul_left_comm, mul_comm]

    calc
      (∫⁻ x : ℝ, ENNReal.ofReal (f x) ∂μI)
          = (∫⁻ x in I, ENNReal.ofReal (f x) ∂volume) := h_restrict
      _ = (∫⁻ x in I, (omegaSigma σ x) * ENNReal.ofReal (‖F x‖ ^ (2 : ℕ)) ∂volume) := by
            exact lintegral_congr_ae h_ae
      _ = EwENN F σ := rfl

  calc
    Ew F σ
        = ∫ x : ℝ, f x ∂μI := hEw
    _ = (∫⁻ x : ℝ, ENNReal.ofReal (f x) ∂μI).toReal := h_toReal
    _ = (EwENN F σ).toReal := by simpa [h_lintegral]

theorem Ew_le_of_EwENN_le
    {F : ℝ → ℂ} (σ : ℝ) (hF : ContinuousOn F I)
    {K : ℝ} (hK0 : 0 ≤ K)
    (hENN : EwENN F σ ≤ (volume I) * ENNReal.ofReal (K ^ (2 : ℕ))) :
    Ew F σ ≤ (volume I).toReal * (K ^ (2 : ℕ)) := by
  have hEw : Ew F σ = (EwENN F σ).toReal :=
    Ew_eq_toReal_EwENN (F := F) σ hF

  have hvol : (volume I) ≠ (⊤ : ENNReal) := by
    have hlt : (volume I) < (⊤ : ENNReal) := by
      simpa [I] using (measure_Icc_lt_top (a := (1 : ℝ)) (b := (2 : ℝ)) (μ := (volume : Measure ℝ)))
    exact ne_of_lt hlt

  have hKtop : ENNReal.ofReal (K ^ (2 : ℕ)) ≠ (⊤ : ENNReal) := by simp
  have hb : (volume I) * ENNReal.ofReal (K ^ (2 : ℕ)) ≠ (⊤ : ENNReal) :=
    ENNReal.mul_ne_top hvol hKtop
  have ha : EwENN F σ ≠ (⊤ : ENNReal) := ne_top_of_le_ne_top hb hENN

  have h_toReal :
      (EwENN F σ).toReal ≤ ((volume I) * ENNReal.ofReal (K ^ (2 : ℕ))).toReal := by
    exact (ENNReal.toReal_le_toReal ha hb).2 hENN

  -- usamos hK0 para evitar warning:
  have hKsq : 0 ≤ (K ^ (2 : ℕ)) := by
    -- (K^2) ≥ 0 si K ≥ 0
    exact pow_nonneg hK0 _

  have hRHS :
      ((volume I) * ENNReal.ofReal (K ^ (2 : ℕ))).toReal
        = (volume I).toReal * (K ^ (2 : ℕ)) := by
    calc
      ((volume I) * ENNReal.ofReal (K ^ (2 : ℕ))).toReal
          = (volume I).toReal * (ENNReal.ofReal (K ^ (2 : ℕ))).toReal := by
              simpa using (ENNReal.toReal_mul hvol hKtop)
      _ = (volume I).toReal * (K ^ (2 : ℕ)) := by
              simp [ENNReal.toReal_ofReal, hKsq]

  have : (EwENN F σ).toReal ≤ (volume I).toReal * (K ^ (2 : ℕ)) := by
    simpa [hRHS] using h_toReal
  simpa [hEw] using this

theorem CloseHyp_of_EwENN_bound
    {δ : ℝ} {V W : ℝ → ℂ} (ε : ℝ)
    (hDiffCont : ContinuousOn (fun x => W x - V x) I)
    (hSmall :
      ∀ σ, σ ∈ Iδ δ →
        ∃ K : ℝ, 0 ≤ K ∧
          EwENN (fun x => W x - V x) σ ≤ (volume I) * ENNReal.ofReal (K ^ (2 : ℕ)) ∧
          (volume I).toReal * (K ^ (2 : ℕ)) ≤ ε ^ (2 : ℕ)) :
    CloseHyp δ V W ε := by
  intro σ hσ
  rcases hSmall σ hσ with ⟨K, hK0, hENN, hKsmall⟩
  have hEw : Ew (fun x => W x - V x) σ ≤ (volume I).toReal * (K ^ (2 : ℕ)) :=
    Ew_le_of_EwENN_le (F := fun x => W x - V x) σ hDiffCont hK0 hENN
  exact le_trans hEw hKsmall

end

end RiemannEnergy
