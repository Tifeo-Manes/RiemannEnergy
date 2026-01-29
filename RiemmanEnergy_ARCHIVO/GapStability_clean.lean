/-
File: RiemannEnergy/GapStability.lean

A2-a (paper): Stability of diagonal gap under weighted L² closeness on I=[1,2].

Depends on:
  - `RiemannEnergy/WeightedCS.lean` (weighted CS + Minkowski + basic bounds)

This file is written as an interface-style lemma: topological/compactness layers
(min/max on compact sets) are packaged into `GapStabilityData`.
-/

import RiemannEnergy.WeightedCS

set_option autoImplicit false

open Classical
open MeasureTheory

noncomputable section

namespace RiemannEnergy

/-- The σ-window used in the paper: a compact interval around 1/2. -/
def Iδ (δ : ℝ) : Set ℝ := Set.Icc ((1/2 : ℝ) - δ) ((1/2 : ℝ) + δ)

/-- Gap functional `G_U(σ) = P_U(1-σ) - P_U(σ)`. -/
def G (U : ℝ → ℂ) (σ : ℝ) : ℝ :=
  P U (1 - σ) - P U σ

/-- Hybrid gap `G_{V,W}(σ) = P_W(1-σ) - P_V(σ)`. -/
def Ghyb (V W : ℝ → ℂ) (σ : ℝ) : ℝ :=
  P W (1 - σ) - P V σ

/--
Interface data for the constants used in the paper.

We package:
  * `cδ` : a uniform positive lower bound for `G V σ` on `Iδ δ`.
  * `Mδ` : a uniform upper bound for `‖V‖_σ` on `Iδ δ`.

This avoids a compactness/min-max layer in Lean for now.
-/
-- NOTE: this must live in `Type` (not `Prop`) because it contains numerical fields
-- like `cδ` and `Mδ`. If declared as `: Prop`, Lean cannot generate projections.
structure GapStabilityData (δ : ℝ) (V : ℝ → ℂ) : Type where
  cδ : ℝ
  Mδ : ℝ
  hcδ_pos : 0 < cδ
  hMδ_pos : 0 < Mδ
  hcδ_le : ∀ σ, σ ∈ Iδ δ → cδ ≤ G V σ
  hMδ_ge : ∀ σ, σ ∈ Iδ δ → nrm V σ ≤ Mδ

/-- `ε_δ := min(M_δ, c_δ/(8 M_δ))`. -/
def εδ (cδ Mδ : ℝ) : ℝ :=
  min Mδ (cδ / (8 * Mδ))

/--
Closeness hypothesis (paper): uniformly for σ∈Iδ,
  `Ew(W−V,σ) ≤ ε²`.
-/
def CloseHyp (δ : ℝ) (V W : ℝ → ℂ) (ε : ℝ) : Prop :=
  ∀ σ, σ ∈ Iδ δ → Ew (fun x => W x - V x) σ ≤ ε ^ (2 : ℕ)

/-- Algebraic identity linking hybrid gap to the pure gap plus perturbation at (1-σ). -/
lemma Ghyb_eq_G_add (V W : ℝ → ℂ) (σ : ℝ) :
    Ghyb V W σ = G V σ + (P W (1 - σ) - P V (1 - σ)) := by
  unfold Ghyb G
  ring

/-- If `Ew F σ ≤ ε²` and `ε ≥ 0`, then `nrm F σ ≤ ε`. -/
lemma nrm_le_of_Ew_le_sq {F : ℝ → ℂ} {σ ε : ℝ}
    (hε : 0 ≤ ε) (hE : Ew F σ ≤ ε ^ (2 : ℕ)) : nrm F σ ≤ ε := by
  -- nrm = sqrt(Ew)
  dsimp [nrm]
  have hE' : Ew F σ ≤ ε^2 := by
    simpa [pow_two] using hE
  have hs : Real.sqrt (Ew F σ) ≤ Real.sqrt (ε^2) :=
    Real.sqrt_le_sqrt hE'
  -- sqrt(ε^2) = |ε| = ε since ε≥0
  simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg hε] using hs

/--
Paper Lemma A2-a (Lean version):

If V has a uniform positive gap `cδ` on `Iδ δ` and W is close to V in the
weighted L² energy (hence in the induced norm), then the hybrid gap stays
≥ `cδ/2` on `Iδ δ`.
-/
theorem Gap_stability
    {δ : ℝ} (_hδ : δ < (1/4 : ℝ))
    (V W : ℝ → ℂ)
    (hVcont : ContinuousOn V RiemannEnergy.I)
    (hWcont : ContinuousOn W RiemannEnergy.I)
    (hData : GapStabilityData δ V)
    (hClose : CloseHyp δ V W (εδ hData.cδ hData.Mδ)) :
    ∀ σ, σ ∈ Iδ δ → Ghyb V W σ ≥ (1/2 : ℝ) * hData.cδ := by
  intro σ hσ

  -- Notation
  set ε : ℝ := εδ hData.cδ hData.Mδ

  have hc0 : 0 ≤ hData.cδ := le_of_lt hData.hcδ_pos
  have hM0 : 0 ≤ hData.Mδ := le_of_lt hData.hMδ_pos

  -- ε ≥ 0 and the two defining upper bounds
  have hε0 : 0 ≤ ε := by
    have h1 : 0 ≤ hData.Mδ := hM0
    have h2 : 0 ≤ hData.cδ / (8 * hData.Mδ) := by
      have : 0 < 8 * hData.Mδ := by nlinarith [hData.hMδ_pos]
      exact div_nonneg hc0 (le_of_lt this)
    -- 0 ≤ min a b
    exact le_min h1 h2

  have hε_le_M : ε ≤ hData.Mδ := by
    simp [ε, εδ] using (min_le_left hData.Mδ (hData.cδ / (8 * hData.Mδ)))

  have hε_le_frac : ε ≤ hData.cδ / (8 * hData.Mδ) := by
    simp [ε, εδ] using (min_le_right hData.Mδ (hData.cδ / (8 * hData.Mδ)))

  -- Unfold close hypothesis into a usable function
  have hClose' : ∀ σ, σ ∈ Iδ δ → Ew (fun x => W x - V x) σ ≤ ε ^ (2 : ℕ) := by
    simpa [CloseHyp, ε] using hClose

  -- From Ew(W−V,σ) ≤ ε², get ‖W−V‖_σ ≤ ε
  have hEw : Ew (fun x => W x - V x) σ ≤ ε ^ (2 : ℕ) := hClose' σ hσ
  have hWV : nrm (fun x => W x - V x) σ ≤ ε :=
    nrm_le_of_Ew_le_sq (F := fun x => W x - V x) (σ := σ) (ε := ε) hε0 hEw

  -- Bound ‖V‖_σ ≤ Mδ
  have hV : nrm V σ ≤ hData.Mδ := hData.hMδ_ge σ hσ

  -- Triangle: ‖W‖ ≤ ‖V‖ + ‖W−V‖
  have hSubCont : ContinuousOn (fun x => W x - V x) RiemannEnergy.I :=
    hWcont.sub hVcont

  have htri : nrm (fun x => V x + (W x - V x)) σ ≤ nrm V σ + nrm (fun x => W x - V x) σ :=
    RiemannEnergy.nrm_triangle (W := V) (V := fun x => W x - V x) σ hVcont hSubCont

  have hVWfun : (fun x => V x + (W x - V x)) = W := by
    funext x
    -- V + (W - V) = V + W - V = W
    simp [add_sub_assoc] using (add_sub_cancel (V x) (W x))

  have hW : nrm W σ ≤ nrm V σ + nrm (fun x => W x - V x) σ := by
    simpa [hVWfun] using htri

  have hW_le_M_plus_ε : nrm W σ ≤ hData.Mδ + ε := by
    -- combine triangle with bounds on V and W-V
    have : nrm V σ + nrm (fun x => W x - V x) σ ≤ hData.Mδ + ε :=
      add_le_add hV hWV
    exact le_trans hW this

  have hW_le_2M : nrm W σ ≤ 2 * hData.Mδ := by
    have : hData.Mδ + ε ≤ 2 * hData.Mδ := by
      nlinarith [hε_le_M]
    exact le_trans hW_le_M_plus_ε this

  have hSum_le_3M : nrm W σ + nrm V σ ≤ 3 * hData.Mδ := by
    nlinarith [hW_le_2M, hV]

  -- Perturbation bound at (1-σ): from WeightedCS
  have hPert0 :
      |P W (1 - σ) - P V (1 - σ)|
        ≤ nrm (fun x => W x - V x) σ * (nrm W σ + nrm V σ) :=
    RiemannEnergy.abs_P_sub_le (W := W) (V := V) σ hWcont hVcont

  have hSum0 : 0 ≤ (nrm W σ + nrm V σ) := by
    nlinarith [nrm_nonneg W σ, nrm_nonneg V σ]

  have hPert1 :
      |P W (1 - σ) - P V (1 - σ)| ≤ ε * (nrm W σ + nrm V σ) := by
    have hmul :
        nrm (fun x => W x - V x) σ * (nrm W σ + nrm V σ)
          ≤ ε * (nrm W σ + nrm V σ) :=
      mul_le_mul_of_nonneg_right hWV hSum0
    exact le_trans hPert0 hmul

  have hPert2 :
      |P W (1 - σ) - P V (1 - σ)| ≤ ε * (3 * hData.Mδ) := by
    have hmul : ε * (nrm W σ + nrm V σ) ≤ ε * (3 * hData.Mδ) :=
      mul_le_mul_of_nonneg_left hSum_le_3M hε0
    exact le_trans hPert1 hmul

  -- Squeeze ε*(3Mδ) using ε ≤ cδ/(8Mδ)
  have hMne : (hData.Mδ : ℝ) ≠ 0 := ne_of_gt hData.hMδ_pos

  have hPert3 :
      ε * (3 * hData.Mδ) ≤ (3/8 : ℝ) * hData.cδ := by
    have h3M0 : 0 ≤ (3 * hData.Mδ) := by nlinarith [hM0]
    have hmul :
        ε * (3 * hData.Mδ) ≤ (hData.cδ / (8 * hData.Mδ)) * (3 * hData.Mδ) :=
      mul_le_mul_of_nonneg_right hε_le_frac h3M0
    have hsimp :
        (hData.cδ / (8 * hData.Mδ)) * (3 * hData.Mδ) = (3/8 : ℝ) * hData.cδ := by
      field_simp [hMne]
      ring
    exact le_trans hmul (by simp [hsimp])

  have h38_le_half : (3/8 : ℝ) ≤ (1/2 : ℝ) := by
    norm_num

  have hPert4 :
      |P W (1 - σ) - P V (1 - σ)| ≤ (1/2 : ℝ) * hData.cδ := by
    have h38 : |P W (1 - σ) - P V (1 - σ)| ≤ (3/8 : ℝ) * hData.cδ :=
      le_trans hPert2 hPert3
    have hscale : (3/8 : ℝ) * hData.cδ ≤ (1/2 : ℝ) * hData.cδ :=
      mul_le_mul_of_nonneg_right h38_le_half hc0
    exact le_trans h38 hscale

  -- Now the gap: Ghyb = G(V) + b, with G(V) ≥ cδ and b ≥ -|b|
  have hGapV : hData.cδ ≤ G V σ := hData.hcδ_le σ hσ

  let b : ℝ := P W (1 - σ) - P V (1 - σ)

  have hLower : hData.cδ - |b| ≤ Ghyb V W σ := by
    have hEq : Ghyb V W σ = G V σ + b := by
      simpa [b] using (Ghyb_eq_G_add V W σ)
    have hb : -|b| ≤ b := neg_abs_le b
    have : hData.cδ - |b| ≤ G V σ + b := by
      linarith [hGapV, hb]
    simpa [hEq] using this

  -- Use |b| ≤ (1/2) cδ and finish by linear arithmetic
  have hb : |b| ≤ (1/2 : ℝ) * hData.cδ := by
    simpa [b] using hPert4

  have hfinal_le : (1/2 : ℝ) * hData.cδ ≤ Ghyb V W σ := by
    -- from cδ - |b| ≤ Ghyb and |b| ≤ cδ/2
    linarith [hLower, hb]

  -- return in ≥ form
  exact hfinal_le

end RiemannEnergy
