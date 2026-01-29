
/-
File: RiemannEnergy/A2b_FamilyClosure.lean (PATCH2)

Fixes:
1) Evita problemas de `Complex.abs` vs `‖·‖` en `mul_le_mul` usando `by positivity`/`by simpa`.
2) Evita subgoal numérico `2 - 1 = 1` usando `simp; norm_num` al calcular `(volume I).toReal`.
3) Elimina el hueco lógico: el `K` del Lema de Unificación no puede tratarse como igual a `A/t`
   si se obtiene por un `∃ K`. Introducimos versiones *explícitas* (con `Classical.choose`) en las
   que `K` es definicionalmente `hη.M * (C_J / |t|^J)`, y así se formaliza “t grande” sin axiomas.

Este archivo está diseñado para reemplazar tu `A2b_FamilyClosure_FINAL.lean`.
-/

import Mathlib.MeasureTheory.Integral.Lebesgue
import RiemannEnergy.A2bToA2a_CloseHyp
import RiemannEnergy.A2bBridge

set_option autoImplicit false

open Classical
open MeasureTheory
open scoped BigOperators

namespace PaperRH
namespace A2bFam

noncomputable section

structure DualDataFam where
  V    : ℝ → ℂ
  η    : ℝ → ℂ
  WSN  : ℝ → ℝ → ℂ
  Winf : ℝ → ℂ
  hV   : ∀ x, V x = η x * Winf x

def DualDataFam.Wloc (D : DualDataFam) (t : ℝ) : ℝ → ℂ :=
  fun x => D.η x * D.WSN t x

lemma dual_diff_factor (D : DualDataFam) (t : ℝ) :
  ∀ x, D.Wloc t x - D.V x = D.η x * (D.WSN t x - D.Winf x) := by
  intro x
  dsimp [DualDataFam.Wloc]
  rw [D.hV x]
  ring

structure PrimalDataFam where
  V    : ℝ → ℂ
  η    : ℝ → ℂ
  VSN  : ℝ → ℝ → ℂ
  Vinf : ℝ → ℂ
  hP   : ∀ x, V x = η x * Vinf x

def PrimalDataFam.Vloc (P : PrimalDataFam) (t : ℝ) : ℝ → ℂ :=
  fun x => P.η x * P.VSN t x

lemma primal_diff_factor (P : PrimalDataFam) (t : ℝ) :
  ∀ x, P.Vloc t x - P.V x = P.η x * (P.VSN t x - P.Vinf x) := by
  intro x
  dsimp [PrimalDataFam.Vloc]
  rw [P.hP x]
  ring

/-- Cierre uniforme en x con constante C_J independiente de t. -/
structure CloseOnIFam (s : Set ℝ) (WSN : ℝ → ℝ → ℂ) (Winf : ℝ → ℂ) : Prop where
  bound : ∀ (J : ℕ), ∃ C : ℝ, 0 ≤ C ∧
    ∀ (t : ℝ) (x : ℝ), x ∈ s → ‖WSN t x - Winf x‖ ≤ C / (|t| ^ J)

end
end A2bFam
end PaperRH

namespace RiemannEnergy

noncomputable section

open PaperRH.A2b
open PaperRH.A2bFam

/-
================================================================================
A2-b (familia): unificación ponderada L² con K EXPLÍCITO (via choose)
================================================================================
-/

/-- Constante C_J elegida de `CloseOnIFam.bound`. -/
noncomputable def Cfam {s} {WSN} {Winf} (hClose : CloseOnIFam s WSN Winf) (J : ℕ) : ℝ :=
  Classical.choose (hClose.bound J)

lemma Cfam_nonneg {s} {WSN} {Winf} (hClose : CloseOnIFam s WSN Winf) (J : ℕ) :
    0 ≤ Cfam (hClose := hClose) J :=
  (Classical.choose_spec (hClose.bound J)).1

lemma Cfam_bound {s} {WSN} {Winf} (hClose : CloseOnIFam s WSN Winf) (J : ℕ) :
    ∀ t x, x ∈ s → ‖WSN t x - Winf x‖ ≤ Cfam (hClose := hClose) J / (|t| ^ J) :=
  (Classical.choose_spec (hClose.bound J)).2

/-- Lema principal dual con K explícito (no `∃ K`). -/
theorem WindowUnification_dual_L2_weighted_fam_explicit
    (D : DualDataFam)
    (hη : BoundedOn RiemannEnergy.I D.η)
    (hClose : CloseOnIFam RiemannEnergy.I D.WSN D.Winf)
    (ω : ℝ → ENNReal) (hW : WeightUpper RiemannEnergy.I ω) :
    ∀ (t : ℝ) (J : ℕ),
      let C := Cfam (hClose := hClose) J
      let K := hη.M * (C / (|t| ^ J))
      (∫⁻ x in RiemannEnergy.I,
          (ω x) * ENNReal.ofReal (‖D.Wloc t x - D.V x‖ ^ (2 : ℕ)) ∂volume)
        ≤ (volume RiemannEnergy.I) * (hW.W * ENNReal.ofReal (K ^ (2 : ℕ))) := by
  intro t J
  classical
  let C : ℝ := Cfam (hClose := hClose) J
  let denom : ℝ := |t| ^ J
  let powTerm : ℝ := C / denom
  let K : ℝ := hη.M * powTerm

  have hC0 : 0 ≤ C := Cfam_nonneg (hClose := hClose) J

  have _hK0 : 0 ≤ K := by
    have hden0 : 0 ≤ denom := pow_nonneg (abs_nonneg t) J
    have hp0 : 0 ≤ powTerm := by
      dsimp [powTerm, denom]
      exact div_nonneg hC0 hden0
    exact mul_nonneg hη.hM hp0

  have hPoint :
      ∀ x, x ∈ RiemannEnergy.I →
        (ω x) * ENNReal.ofReal (‖D.Wloc t x - D.V x‖ ^ (2 : ℕ))
          ≤ hW.W * ENNReal.ofReal (K ^ (2 : ℕ)) := by
    intro x hx
    have hω : ω x ≤ hW.W := hW.upper x hx
    have hηx : ‖D.η x‖ ≤ hη.M := hη.bound x hx
    have hWx : ‖D.WSN t x - D.Winf x‖ ≤ powTerm := by
      -- bound elegido por choose
      simpa [C, powTerm, denom] using (Cfam_bound (hClose := hClose) J t x hx)

    have hdiff0 : 0 ≤ ‖D.WSN t x - D.Winf x‖ := by positivity

    have hNorm : ‖D.Wloc t x - D.V x‖ ≤ K := by
      rw [PaperRH.A2bFam.dual_diff_factor D t x, norm_mul]
      dsimp [K]
      -- ‖η‖*‖diff‖ ≤ M*powTerm
      have : ‖D.η x‖ * ‖D.WSN t x - D.Winf x‖ ≤ hη.M * powTerm :=
        mul_le_mul hηx hWx hdiff0 hη.hM
      simpa [mul_assoc, mul_left_comm, mul_comm] using this

    have hSq :
        ENNReal.ofReal (‖D.Wloc t x - D.V x‖ ^ (2 : ℕ))
          ≤ ENNReal.ofReal (K ^ (2 : ℕ)) := by
      apply ENNReal.ofReal_le_ofReal
      exact pow_le_pow_left (norm_nonneg _) hNorm 2

    -- combinar con el peso
    exact mul_le_mul hω hSq (by simp) (by simp)

  let f_integrand :=
    fun x => (ω x) * ENNReal.ofReal (‖D.Wloc t x - D.V x‖ ^ (2 : ℕ))
  let C_bound := hW.W * ENNReal.ofReal (K ^ (2 : ℕ))

  have h_mono :
      ∀ x, (RiemannEnergy.I).indicator f_integrand x
            ≤ (RiemannEnergy.I).indicator (fun _ => C_bound) x := by
    intro x
    by_cases hx : x ∈ RiemannEnergy.I
    · simp [Set.indicator_of_mem hx, f_integrand, C_bound]
      exact hPoint x hx
    · simp [Set.indicator_of_not_mem hx, f_integrand, C_bound]

  -- Integrar indicador y constante
  rw [← lintegral_indicator _ RiemannEnergy.measurableSet_I]
  apply le_trans (lintegral_mono h_mono)
  rw [lintegral_indicator _ RiemannEnergy.measurableSet_I]
  rw [set_lintegral_const RiemannEnergy.I]
  dsimp [C_bound]
  simp [mul_comm, mul_left_comm, mul_assoc, C, K, powTerm, denom]

/-- Lema principal primal con K explícito. -/
theorem WindowUnification_primal_L2_weighted_fam_explicit
    (P : PrimalDataFam)
    (hη : BoundedOn RiemannEnergy.I P.η)
    (hClose : CloseOnIFam RiemannEnergy.I P.VSN P.Vinf)
    (ω : ℝ → ENNReal) (hW : WeightUpper RiemannEnergy.I ω) :
    ∀ (t : ℝ) (J : ℕ),
      let C := Cfam (hClose := hClose) J
      let K := hη.M * (C / (|t| ^ J))
      (∫⁻ x in RiemannEnergy.I,
          (ω x) * ENNReal.ofReal (‖P.Vloc t x - P.V x‖ ^ (2 : ℕ)) ∂volume)
        ≤ (volume RiemannEnergy.I) * (hW.W * ENNReal.ofReal (K ^ (2 : ℕ))) := by
  intro t J
  classical
  let C : ℝ := Cfam (hClose := hClose) J
  let denom : ℝ := |t| ^ J
  let powTerm : ℝ := C / denom
  let K : ℝ := hη.M * powTerm

  have hC0 : 0 ≤ C := Cfam_nonneg (hClose := hClose) J

  have _hK0 : 0 ≤ K := by
    have hden0 : 0 ≤ denom := pow_nonneg (abs_nonneg t) J
    have hp0 : 0 ≤ powTerm := by
      dsimp [powTerm, denom]
      exact div_nonneg hC0 hden0
    exact mul_nonneg hη.hM hp0

  have hPoint :
      ∀ x, x ∈ RiemannEnergy.I →
        (ω x) * ENNReal.ofReal (‖P.Vloc t x - P.V x‖ ^ (2 : ℕ))
          ≤ hW.W * ENNReal.ofReal (K ^ (2 : ℕ)) := by
    intro x hx
    have hω : ω x ≤ hW.W := hW.upper x hx
    have hηx : ‖P.η x‖ ≤ hη.M := hη.bound x hx
    have hVx : ‖P.VSN t x - P.Vinf x‖ ≤ powTerm := by
      simpa [C, powTerm, denom] using (Cfam_bound (hClose := hClose) J t x hx)

    have hdiff0 : 0 ≤ ‖P.VSN t x - P.Vinf x‖ := by positivity

    have hNorm : ‖P.Vloc t x - P.V x‖ ≤ K := by
      rw [PaperRH.A2bFam.primal_diff_factor P t x, norm_mul]
      dsimp [K]
      have : ‖P.η x‖ * ‖P.VSN t x - P.Vinf x‖ ≤ hη.M * powTerm :=
        mul_le_mul hηx hVx hdiff0 hη.hM
      simpa [mul_assoc, mul_left_comm, mul_comm] using this

    have hSq :
        ENNReal.ofReal (‖P.Vloc t x - P.V x‖ ^ (2 : ℕ))
          ≤ ENNReal.ofReal (K ^ (2 : ℕ)) := by
      apply ENNReal.ofReal_le_ofReal
      exact pow_le_pow_left (norm_nonneg _) hNorm 2

    exact mul_le_mul hω hSq (by simp) (by simp)

  let f_integrand :=
    fun x => (ω x) * ENNReal.ofReal (‖P.Vloc t x - P.V x‖ ^ (2 : ℕ))
  let C_bound := hW.W * ENNReal.ofReal (K ^ (2 : ℕ))

  have h_mono :
      ∀ x, (RiemannEnergy.I).indicator f_integrand x
            ≤ (RiemannEnergy.I).indicator (fun _ => C_bound) x := by
    intro x
    by_cases hx : x ∈ RiemannEnergy.I
    · simp [Set.indicator_of_mem hx, f_integrand, C_bound]
      exact hPoint x hx
    · simp [Set.indicator_of_not_mem hx, f_integrand, C_bound]

  rw [← lintegral_indicator _ RiemannEnergy.measurableSet_I]
  apply le_trans (lintegral_mono h_mono)
  rw [lintegral_indicator _ RiemannEnergy.measurableSet_I]
  rw [set_lintegral_const RiemannEnergy.I]
  dsimp [C_bound]
  simp [mul_comm, mul_left_comm, mul_assoc, C, K, powTerm, denom]

/-
================================================================================
Paso “t grande” (puro álgebra real)
================================================================================
-/

/-- Si A≥0 y ε>0, existe t0≥2 con ∀t≥t0, A/t ≤ ε. -/
lemma exists_t0_ge_two_forall_t_ge_t0_div_le
    (A ε : ℝ) (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ t0 : ℝ, (2 : ℝ) ≤ t0 ∧ ∀ t : ℝ, t0 ≤ t → A / t ≤ ε := by
  classical
  let t0 : ℝ := max (2 : ℝ) (A / ε)
  refine ⟨t0, le_max_left _ _, ?_⟩
  intro t ht
  have ht0_pos : 0 < t0 := lt_of_lt_of_le (by norm_num) (le_max_left _ _)

  have hA_divε : A / ε ≤ t0 := le_max_right _ _
  have hA_le : A ≤ t0 * ε := (div_le_iff hε).1 hA_divε
  have hA_div_t0 : A / t0 ≤ ε := by
    have : A ≤ ε * t0 := by simpa [mul_comm, mul_left_comm, mul_assoc] using hA_le
    exact (div_le_iff ht0_pos).2 this

  have hinv : (t)⁻¹ ≤ (t0)⁻¹ := by
    have := inv_le_inv_of_le ht0_pos ht
    simpa using this

  have hmono : A / t ≤ A / t0 := by
    have : A * t⁻¹ ≤ A * t0⁻¹ := mul_le_mul_of_nonneg_left hinv hA
    simpa [div_eq_mul_inv, mul_assoc] using this

  exact le_trans hmono hA_div_t0

/-
================================================================================
Cierre final: A2-b(familia) -> CloseHyp -> Gap_stability, sin axiomas
================================================================================
-/

/-- Dual: existe t0≥2 tal que ∀t≥t0, gap híbrido ≥ cδ/2. -/
theorem Gap_stability_eventually_dual_fam
    {δ : ℝ} (hδ : δ < (1/4 : ℝ))
    (D : DualDataFam)
    (hη : BoundedOn RiemannEnergy.I D.η)
    (hClose : CloseOnIFam RiemannEnergy.I D.WSN D.Winf)
    (hVcont : ContinuousOn D.V RiemannEnergy.I)
    (hWcont : ∀ t : ℝ, ContinuousOn (D.Wloc t) RiemannEnergy.I)
    (hData : GapStabilityData δ D.V) :
    ∃ t0 : ℝ, (2 : ℝ) ≤ t0 ∧
      ∀ t : ℝ, t0 ≤ t →
        ∀ σ, σ ∈ Iδ δ →
          Ghyb D.V (D.Wloc t) σ ≥ (1/2 : ℝ) * hData.cδ := by
  classical
  let ε : ℝ := εδ hData.cδ hData.Mδ

  have hεpos : 0 < ε := by
    have hfrac : 0 < hData.cδ / (8 * hData.Mδ) := by
      have hden : 0 < (8 : ℝ) * hData.Mδ := by nlinarith [hData.hMδ_pos]
      exact div_pos hData.hcδ_pos hden
    have : 0 < min hData.Mδ (hData.cδ / (8 * hData.Mδ)) :=
      (lt_min_iff).2 ⟨hData.hMδ_pos, hfrac⟩
    simpa [ε, εδ] using this

  let C1 : ℝ := Cfam (hClose := hClose) 1
  have hC10 : 0 ≤ C1 := Cfam_nonneg (hClose := hClose) 1
  let A : ℝ := hη.M * C1
  have hA0 : 0 ≤ A := mul_nonneg hη.hM hC10

  rcases exists_t0_ge_two_forall_t_ge_t0_div_le A ε hA0 hεpos with ⟨t0, ht0, hAdiv⟩
  refine ⟨t0, ht0, ?_⟩
  intro t ht σ hσ

  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) (le_trans ht0 ht)
  have habs : |t| = t := abs_of_nonneg (le_of_lt htpos)

  have hDiffCont : ContinuousOn (fun x => D.Wloc t x - D.V x) RiemannEnergy.I :=
    (hWcont t).sub hVcont

  have hCloseHyp : CloseHyp δ D.V (D.Wloc t) ε := by
    refine CloseHyp_of_EwENN_bound (δ := δ) (V := D.V) (W := (D.Wloc t)) (ε := ε)
      hDiffCont ?_
    intro σ hσ
    let hWσ : WeightUpper RiemannEnergy.I (omegaSigma σ) :=
      weightUpper_omegaSigma (δ := δ) (σ := σ) hσ hδ
    have hW1 : hWσ.W = (1 : ENNReal) := rfl

    -- K(t) explícito para J=1
    let Kt : ℝ := hη.M * (C1 / (|t| ^ (1 : ℕ)))

    have hIne :
        (∫⁻ x in RiemannEnergy.I,
            (omegaSigma σ x) * ENNReal.ofReal (‖D.Wloc t x - D.V x‖ ^ (2 : ℕ)) ∂volume)
          ≤ (volume RiemannEnergy.I) * (hWσ.W * ENNReal.ofReal (Kt ^ (2 : ℕ))) := by
      -- Instanciar el lema explícito
      simpa [C1, Kt] using
        (WindowUnification_dual_L2_weighted_fam_explicit
          (D := D) (hη := hη) (hClose := hClose) (ω := omegaSigma σ) (hW := hWσ) t 1)

    have hENN :
        EwENN (fun x => D.Wloc t x - D.V x) σ
          ≤ (volume RiemannEnergy.I) * ENNReal.ofReal (Kt ^ (2 : ℕ)) := by
      simpa [EwENN, omegaSigma, hW1, one_mul, mul_assoc, mul_left_comm, mul_comm] using hIne

    have hKt0 : 0 ≤ Kt := by
      have hden0 : 0 ≤ |t| ^ (1 : ℕ) := pow_nonneg (abs_nonneg t) 1
      have : 0 ≤ (C1 / (|t| ^ (1 : ℕ))) := div_nonneg hC10 hden0
      exact mul_nonneg hη.hM this

    have hKt_eq : Kt = A / t := by
      -- Kt = M*(C1/|t|) = (M*C1)/t = A/t, porque |t|=t y |t|^1=|t|
      simp [Kt, A, C1, habs, pow_one, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

    have hKt_le : Kt ≤ ε := by
      simpa [hKt_eq] using (hAdiv t ht)

    have hKpow : Kt ^ (2 : ℕ) ≤ ε ^ (2 : ℕ) :=
      pow_le_pow_left hKt0 hKt_le 2

    have hvol : (volume RiemannEnergy.I).toReal = (1 : ℝ) := by
      simp [RiemannEnergy.I]
      norm_num

    have hKsmall : (volume RiemannEnergy.I).toReal * (Kt ^ (2 : ℕ)) ≤ ε ^ (2 : ℕ) := by
      simpa [hvol] using hKpow

    refine ⟨Kt, hKt0, hENN, hKsmall⟩

  -- Aplicar Gap_stability
  simpa [ε] using
    (Gap_stability (δ := δ) (_hδ := hδ) (V := D.V) (W := D.Wloc t)
      (hVcont := hVcont) (hWcont := hWcont t)
      (hData := hData) (hClose := hCloseHyp)) σ hσ

/-- Primal: versión simétrica. -/
theorem Gap_stability_eventually_primal_fam
    {δ : ℝ} (hδ : δ < (1/4 : ℝ))
    (P : PrimalDataFam)
    (hη : BoundedOn RiemannEnergy.I P.η)
    (hClose : CloseOnIFam RiemannEnergy.I P.VSN P.Vinf)
    (hVcont : ContinuousOn P.V RiemannEnergy.I)
    (hWcont : ∀ t : ℝ, ContinuousOn (P.Vloc t) RiemannEnergy.I)
    (hData : GapStabilityData δ P.V) :
    ∃ t0 : ℝ, (2 : ℝ) ≤ t0 ∧
      ∀ t : ℝ, t0 ≤ t →
        ∀ σ, σ ∈ Iδ δ →
          Ghyb P.V (P.Vloc t) σ ≥ (1/2 : ℝ) * hData.cδ := by
  classical
  let ε : ℝ := εδ hData.cδ hData.Mδ

  have hεpos : 0 < ε := by
    have hfrac : 0 < hData.cδ / (8 * hData.Mδ) := by
      have hden : 0 < (8 : ℝ) * hData.Mδ := by nlinarith [hData.hMδ_pos]
      exact div_pos hData.hcδ_pos hden
    have : 0 < min hData.Mδ (hData.cδ / (8 * hData.Mδ)) :=
      (lt_min_iff).2 ⟨hData.hMδ_pos, hfrac⟩
    simpa [ε, εδ] using this

  let C1 : ℝ := Cfam (hClose := hClose) 1
  have hC10 : 0 ≤ C1 := Cfam_nonneg (hClose := hClose) 1
  let A : ℝ := hη.M * C1
  have hA0 : 0 ≤ A := mul_nonneg hη.hM hC10

  rcases exists_t0_ge_two_forall_t_ge_t0_div_le A ε hA0 hεpos with ⟨t0, ht0, hAdiv⟩
  refine ⟨t0, ht0, ?_⟩
  intro t ht σ hσ

  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) (le_trans ht0 ht)
  have habs : |t| = t := abs_of_nonneg (le_of_lt htpos)

  have hDiffCont : ContinuousOn (fun x => P.Vloc t x - P.V x) RiemannEnergy.I :=
    (hWcont t).sub hVcont

  have hCloseHyp : CloseHyp δ P.V (P.Vloc t) ε := by
    refine CloseHyp_of_EwENN_bound (δ := δ) (V := P.V) (W := (P.Vloc t)) (ε := ε)
      hDiffCont ?_
    intro σ hσ
    let hWσ : WeightUpper RiemannEnergy.I (omegaSigma σ) :=
      weightUpper_omegaSigma (δ := δ) (σ := σ) hσ hδ
    have hW1 : hWσ.W = (1 : ENNReal) := rfl

    let Kt : ℝ := hη.M * (C1 / (|t| ^ (1 : ℕ)))

    have hIne :
        (∫⁻ x in RiemannEnergy.I,
            (omegaSigma σ x) * ENNReal.ofReal (‖P.Vloc t x - P.V x‖ ^ (2 : ℕ)) ∂volume)
          ≤ (volume RiemannEnergy.I) * (hWσ.W * ENNReal.ofReal (Kt ^ (2 : ℕ))) := by
      simpa [C1, Kt] using
        (WindowUnification_primal_L2_weighted_fam_explicit
          (P := P) (hη := hη) (hClose := hClose) (ω := omegaSigma σ) (hW := hWσ) t 1)

    have hENN :
        EwENN (fun x => P.Vloc t x - P.V x) σ
          ≤ (volume RiemannEnergy.I) * ENNReal.ofReal (Kt ^ (2 : ℕ)) := by
      simpa [EwENN, omegaSigma, hW1, one_mul, mul_assoc, mul_left_comm, mul_comm] using hIne

    have hKt0 : 0 ≤ Kt := by
      have hden0 : 0 ≤ |t| ^ (1 : ℕ) := pow_nonneg (abs_nonneg t) 1
      have : 0 ≤ (C1 / (|t| ^ (1 : ℕ))) := div_nonneg hC10 hden0
      exact mul_nonneg hη.hM this

    have hKt_eq : Kt = A / t := by
      simp [Kt, A, C1, habs, pow_one, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

    have hKt_le : Kt ≤ ε := by
      simpa [hKt_eq] using (hAdiv t ht)

    have hKpow : Kt ^ (2 : ℕ) ≤ ε ^ (2 : ℕ) :=
      pow_le_pow_left hKt0 hKt_le 2

    have hvol : (volume RiemannEnergy.I).toReal = (1 : ℝ) := by
      simp [RiemannEnergy.I]
      norm_num

    have hKsmall : (volume RiemannEnergy.I).toReal * (Kt ^ (2 : ℕ)) ≤ ε ^ (2 : ℕ) := by
      simpa [hvol] using hKpow

    refine ⟨Kt, hKt0, hENN, hKsmall⟩

  simpa [ε] using
    (Gap_stability (δ := δ) (_hδ := hδ) (V := P.V) (W := P.Vloc t)
      (hVcont := hVcont) (hWcont := hWcont t)
      (hData := hData) (hClose := hCloseHyp)) σ hσ

end

end RiemannEnergy