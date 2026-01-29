/-
File: RiemannEnergy/A2bBridge.lean

Bridge A2-b (weighted L² window unification) -> A2-a style closeness bound,
expressed as an ENNReal lintegral bound.

This module is interface-first: it gives you a uniform-in-σ ENNReal-lintegral
version of the A2-a closeness bound directly from A2-b, without committing yet
to the conversion `lintegral (ENNReal.ofReal ...) -> real integral`.

Notes:
  * The interval `I` must coincide definitionally with `RiemannEnergy.I`.
  * We reuse the weight `w` from `RiemannEnergy.WeightedCS`.
-/

import Mathlib.MeasureTheory.Integral.Lebesgue
import RiemannEnergy.GapStability
import RiemannEnergy.A2b_WindowUnification

set_option autoImplicit false

open Classical
open MeasureTheory

namespace RiemannEnergy

noncomputable section

-- The A2-b window-unification API is expected under `PaperRH.A2b`.
-- If your file uses a different namespace, adapt the `open` line below.
open PaperRH.A2b

/-- ENNReal weight corresponding to the paper weight x^{-2(1-σ)}. -/
def omegaSigma (σ : ℝ) : ℝ → ENNReal :=
  fun x => ENNReal.ofReal (w (1 - σ) x)

/-- ENNReal weighted energy: ∫⁻_{x∈I} ωσ(σ,x) * ofReal(‖F(x)‖^2). -/
def EwENN (F : ℝ → ℂ) (σ : ℝ) : ENNReal :=
  ∫⁻ x in I, (omegaSigma σ x) * ENNReal.ofReal (‖F x‖ ^ (2 : ℕ)) ∂volume

/--
Uniform weight-upper bound on I=[1,2]: for σ in the band Iδ(δ) with δ < 1/4,
we have σ < 1, hence 1-σ > 0 so exponent -(2*(1-σ)) ≤ 0. For x ≥ 1,
this gives w(1-σ,x) ≤ 1, hence omegaSigma σ x ≤ 1.
-/
def weightUpper_omegaSigma
    {δ σ : ℝ} (hσ : σ ∈ Iδ δ) (hδ : δ < (1/4 : ℝ)) :
    WeightUpper I (omegaSigma σ) := by
  classical
  refine { W := (1 : ENNReal), upper := ?_ }
  intro x hx
  have hx1 : (1 : ℝ) ≤ x := (Set.mem_Icc.mp hx).1

  -- From σ ∈ [1/2-δ, 1/2+δ] and δ < 1/4 we get σ < 1.
  have hσ_lt_one : σ < 1 := by
    have hσ_upper : σ ≤ (1/2 : ℝ) + δ := (Set.mem_Icc.mp hσ).2
    have : (1/2 : ℝ) + δ < 1 := by linarith [hδ]
    exact lt_of_le_of_lt hσ_upper this
  have h1σ : 0 ≤ (1 - σ) := by
    have : 0 < (1 - σ) := sub_pos.mpr hσ_lt_one
    exact le_of_lt this

  have hexp : (-(2 * (1 - σ))) ≤ 0 := by
    nlinarith [h1σ]

  have hw_le : w (1 - σ) x ≤ 1 := by
    -- w(τ,x) = x ^ (-(2*τ)), with τ = 1-σ.
    -- For x ≥ 1 and exponent ≤ 0 we get x^exponent ≤ 1.
    have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx1
    have hpow : x ^ (-(2 * (1 - σ))) ≤ 1 := by
      -- `x ^ y ≤ 1 ↔ (1 ≤ x ∧ y ≤ 0) ∨ (x ≤ 1 ∧ 0 ≤ y)`
      have hiff := (Real.rpow_le_one_iff_of_pos (x := x) (y := (-(2 * (1 - σ)))) hxpos)
      -- use the `1 ≤ x ∧ y ≤ 0` branch
      exact hiff.2 (Or.inl ⟨hx1, hexp⟩)
    simpa [w, mul_assoc, mul_left_comm, mul_comm] using hpow

  have : ENNReal.ofReal (w (1 - σ) x) ≤ (1 : ENNReal) := by
    -- `ENNReal.ofReal_le_ofReal` needs both sides nonnegative; `0 ≤ 1` is trivial.
    simpa using (ENNReal.ofReal_le_ofReal hw_le)

  simpa [omegaSigma] using this

/--
A2-b (dual) gives, for each (t,J), a K with a weighted L² bound.
Taking ω = omegaSigma σ and W=1 yields an ENNReal-weighted Ew-bound.
-/
theorem EwENN_bound_of_A2b_dual
    {δ : ℝ} (hδ : δ < (1/4 : ℝ))
    (D : DualData)
    (hη : BoundedOn I D.η)
    (hClose : CloseOnI I D.WSN D.Winf) :
    ∀ (t : ℝ) (J : ℕ) (σ : ℝ),
      σ ∈ Iδ δ →
      ∃ K : ℝ, 0 ≤ K ∧
        EwENN (fun x => D.Wloc x - D.V x) σ
          ≤ (volume I) * ENNReal.ofReal (K ^ (2 : ℕ)) := by
  intro t J σ hσ
  let hW : WeightUpper I (omegaSigma σ) :=
    weightUpper_omegaSigma (δ := δ) (σ := σ) hσ hδ
  rcases WindowUnification_dual_L2_weighted
      D hη hClose (ω := omegaSigma σ) hW t J with ⟨K, hK0, hA⟩
  refine ⟨K, hK0, ?_⟩
  -- Unfold EwENN and simplify W=1
  have hW1 : hW.W = (1 : ENNReal) := rfl
  simpa [EwENN, omegaSigma, hW1, one_mul, mul_assoc, mul_left_comm, mul_comm] using hA

/-- Same bridge for A2-b primal. -/
theorem EwENN_bound_of_A2b_primal
    {δ : ℝ} (hδ : δ < (1/4 : ℝ))
    (P0 : PrimalData)
    (hη : BoundedOn I P0.η)
    (hClose : CloseOnI I P0.VSN P0.Vinf) :
    ∀ (t : ℝ) (J : ℕ) (σ : ℝ),
      σ ∈ Iδ δ →
      ∃ K : ℝ, 0 ≤ K ∧
        EwENN (fun x => P0.Vloc x - P0.V x) σ
          ≤ (volume I) * ENNReal.ofReal (K ^ (2 : ℕ)) := by
  intro t J σ hσ
  let hW : WeightUpper I (omegaSigma σ) :=
    weightUpper_omegaSigma (δ := δ) (σ := σ) hσ hδ
  rcases WindowUnification_primal_L2_weighted
      P0 hη hClose (ω := omegaSigma σ) hW t J with ⟨K, hK0, hA⟩
  refine ⟨K, hK0, ?_⟩
  have hW1 : hW.W = (1 : ENNReal) := rfl
  simpa [EwENN, omegaSigma, hW1, one_mul, mul_assoc, mul_left_comm, mul_comm] using hA


/-- Unicode alias for `omegaSigma`. -/
abbrev ωσ (σ : ℝ) : ℝ → ENNReal := omegaSigma σ

/-- Backwards-compatible alias for the weight-upper lemma. -/
def weightUpper_ωσ
    {δ σ : ℝ} (hσ : σ ∈ Iδ δ) (hδ : δ < (1/4 : ℝ)) :
    WeightUpper I (ωσ σ) := by
  simpa [ωσ] using (weightUpper_omegaSigma (δ := δ) (σ := σ) hσ hδ)

end

end RiemannEnergy
