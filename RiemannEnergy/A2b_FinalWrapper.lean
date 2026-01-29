
/-
File: RiemannEnergy/A2b_FinalWrapper.lean  (PATCH: remove `in` after `let`)

En Lean 4, el `let ...` en tipos/Propositions se escribe con `;` (no con `in`).
Los errores “unexpected token 'in'” se arreglan sustituyendo:

  let K := ... in P

por

  let K := ...; P

Este wrapper encadena:
  A2-b -> EwENN bound -> CloseHyp -> Gap_stability
y deja explícita la única hipótesis analítica externa: `hChooseSmall` (“t grande”).
-/

import RiemannEnergy.A2bToA2a_CloseHyp

set_option autoImplicit false

open Classical
open MeasureTheory

namespace RiemannEnergy

noncomputable section

open PaperRH.A2b

/-- Cierra A2-b (dual) -> Gap_stability, dejando explícito `hChooseSmall`. -/
theorem Gap_stability_from_A2b_dual
    {δ : ℝ} (hδ : δ < (1/4 : ℝ))
    (D : DualData)
    (hη : BoundedOn RiemannEnergy.I D.η)
    (hClose : CloseOnI RiemannEnergy.I D.WSN D.Winf)
    (hVcont : ContinuousOn D.V RiemannEnergy.I)
    (hWcont : ContinuousOn D.Wloc RiemannEnergy.I)
    (hData : GapStabilityData δ D.V)
    (t : ℝ) (J : ℕ)
    /- Hipótesis “t grande”: el K elegido por el puente A2-b es suficientemente pequeño. -/
    (hChooseSmall :
      ∀ σ (hσ : σ ∈ Iδ δ),
        let K :=
          Classical.choose
            (EwENN_bound_of_A2b_dual (δ := δ) hδ D hη hClose t J σ hσ);
        (volume RiemannEnergy.I).toReal * (K ^ (2 : ℕ))
            ≤ (εδ hData.cδ hData.Mδ) ^ (2 : ℕ)) :
    ∀ σ, σ ∈ Iδ δ → Ghyb D.V D.Wloc σ ≥ (1/2 : ℝ) * hData.cδ := by
  -- Construimos CloseHyp δ V W ε con ε = εδ(cδ,Mδ)
  have hDiffCont : ContinuousOn (fun x => D.Wloc x - D.V x) RiemannEnergy.I :=
    hWcont.sub hVcont

  have hCloseHyp :
      CloseHyp δ D.V D.Wloc (εδ hData.cδ hData.Mδ) := by
    refine CloseHyp_of_EwENN_bound
      (δ := δ) (V := D.V) (W := D.Wloc) (ε := (εδ hData.cδ hData.Mδ))
      hDiffCont ?_
    intro σ hσ
    -- Aplicar el puente A2-b para este σ.
    let hex :=
      EwENN_bound_of_A2b_dual (δ := δ) hδ D hη hClose t J σ hσ
    let K : ℝ := Classical.choose hex
    have hKspec :
        0 ≤ K ∧
          EwENN (fun x => D.Wloc x - D.V x) σ
            ≤ (volume RiemannEnergy.I) * ENNReal.ofReal (K ^ (2 : ℕ)) :=
      Classical.choose_spec hex
    have hKsmall :
        (volume RiemannEnergy.I).toReal * (K ^ (2 : ℕ))
            ≤ (εδ hData.cδ hData.Mδ) ^ (2 : ℕ) := by
      -- Desplegar el `let K := Classical.choose hex; ...` en `hChooseSmall`
      simpa [K, hex] using (hChooseSmall σ hσ)
    refine ⟨K, hKspec.1, hKspec.2, hKsmall⟩

  -- Aplicar A2-a
  simpa using
    (Gap_stability (δ := δ) (_hδ := hδ) (V := D.V) (W := D.Wloc)
      (hVcont := hVcont) (hWcont := hWcont)
      (hData := hData) (hClose := hCloseHyp))

/-- Cierra A2-b (primal) -> Gap_stability, dejando explícito `hChooseSmall`. -/
theorem Gap_stability_from_A2b_primal
    {δ : ℝ} (hδ : δ < (1/4 : ℝ))
    (P0 : PrimalData)
    (hη : BoundedOn RiemannEnergy.I P0.η)
    (hClose : CloseOnI RiemannEnergy.I P0.VSN P0.Vinf)
    (hVcont : ContinuousOn P0.V RiemannEnergy.I)
    (hWcont : ContinuousOn P0.Vloc RiemannEnergy.I)
    (hData : GapStabilityData δ P0.V)
    (t : ℝ) (J : ℕ)
    (hChooseSmall :
      ∀ σ (hσ : σ ∈ Iδ δ),
        let K :=
          Classical.choose
            (EwENN_bound_of_A2b_primal (δ := δ) hδ P0 hη hClose t J σ hσ);
        (volume RiemannEnergy.I).toReal * (K ^ (2 : ℕ))
            ≤ (εδ hData.cδ hData.Mδ) ^ (2 : ℕ)) :
    ∀ σ, σ ∈ Iδ δ → Ghyb P0.V P0.Vloc σ ≥ (1/2 : ℝ) * hData.cδ := by
  have hDiffCont : ContinuousOn (fun x => P0.Vloc x - P0.V x) RiemannEnergy.I :=
    hWcont.sub hVcont

  have hCloseHyp :
      CloseHyp δ P0.V P0.Vloc (εδ hData.cδ hData.Mδ) := by
    refine CloseHyp_of_EwENN_bound
      (δ := δ) (V := P0.V) (W := P0.Vloc) (ε := (εδ hData.cδ hData.Mδ))
      hDiffCont ?_
    intro σ hσ
    let hex :=
      EwENN_bound_of_A2b_primal (δ := δ) hδ P0 hη hClose t J σ hσ
    let K : ℝ := Classical.choose hex
    have hKspec :
        0 ≤ K ∧
          EwENN (fun x => P0.Vloc x - P0.V x) σ
            ≤ (volume RiemannEnergy.I) * ENNReal.ofReal (K ^ (2 : ℕ)) :=
      Classical.choose_spec hex
    have hKsmall :
        (volume RiemannEnergy.I).toReal * (K ^ (2 : ℕ))
            ≤ (εδ hData.cδ hData.Mδ) ^ (2 : ℕ) := by
      simpa [K, hex] using (hChooseSmall σ hσ)
    refine ⟨K, hKspec.1, hKspec.2, hKsmall⟩

  simpa using
    (Gap_stability (δ := δ) (_hδ := hδ) (V := P0.V) (W := P0.Vloc)
      (hVcont := hVcont) (hWcont := hWcont)
      (hData := hData) (hClose := hCloseHyp))

end

end RiemannEnergy
