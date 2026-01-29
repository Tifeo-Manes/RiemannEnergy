import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.ContinuousFunction.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.SetIntegral

open scoped BigOperators
open MeasureTheory

namespace RiemannEnergy

noncomputable section

set_option maxRecDepth 2048
set_option maxHeartbeats 20000000

/-!
Weighted CS / Minkowski en el intervalo I = [1,2] con medida restringida.
-/

-- Intervalo y medida
def I : Set ℝ := Set.Icc (1 : ℝ) 2

lemma measurableSet_I : MeasurableSet I := by
  exact measurableSet_Icc

lemma isCompact_I : IsCompact I := by
  exact isCompact_Icc

def μI : Measure ℝ := Measure.restrict volume I

lemma ae_mem_I : ∀ᵐ x : ℝ ∂μI, x ∈ I := by
  have : μI = volume.restrict I := rfl
  rw [this]
  exact ae_restrict_mem measurableSet_I

-- Integrabilidad desde continuidad en compacto
theorem integrable_of_continuousOn {f : ℝ → ℝ} (hf : ContinuousOn f I) :
    Integrable f μI := by
  have hOn : IntegrableOn f I volume :=
    hf.integrableOn_compact isCompact_I
  exact hOn

theorem integrable_of_continuousOn_complex {F : ℝ → ℂ} (hF : ContinuousOn F I) :
    Integrable F μI := by
  have hOn : IntegrableOn F I volume :=
    hF.integrableOn_compact isCompact_I
  exact hOn

-- Peso: w(σ,x) = x^(-2σ)
def w (σ : ℝ) : ℝ → ℝ := fun x => x ^ (-(2 * σ))

lemma w_continuous (σ : ℝ) : ContinuousOn (w σ) I := by
  intro x hx
  have hxpos : 0 < x := by linarith [hx.1]
  have : ContinuousAt (fun (x : ℝ) => x ^ (-(2 * σ))) x :=
    Real.continuousAt_rpow_const x (-(2 * σ)) (Or.inl (ne_of_gt hxpos))
  exact this.continuousWithinAt

lemma w_nonneg (σ x : ℝ) (hx : x ∈ I) : 0 ≤ w σ x := by
  have hx1 : 1 ≤ x := hx.1
  have hx0 : 0 ≤ x := by linarith
  dsimp [w]
  exact Real.rpow_nonneg hx0 _

-- Energía ponderada y norma asociada
def P (F : ℝ → ℂ) (σ : ℝ) : ℝ :=
  ∫ x : ℝ, ‖F x‖ ^ 2 * w σ x ∂μI

def Ew (F : ℝ → ℂ) (σ : ℝ) : ℝ := P F (1 - σ)

def nrm (F : ℝ → ℂ) (σ : ℝ) : ℝ := Real.sqrt (Ew F σ)

lemma Ew_nonneg (F : ℝ → ℂ) (σ : ℝ) : 0 ≤ Ew F σ := by
  unfold Ew P
  simp only [μI]
  refine setIntegral_nonneg measurableSet_I ?_
  intro x hx
  have hw : 0 ≤ w (1 - σ) x := w_nonneg (1 - σ) x hx
  have : 0 ≤ ‖F x‖ ^ 2 := by nlinarith [norm_nonneg (F x)]
  positivity

lemma nrm_nonneg (F : ℝ → ℂ) (σ : ℝ) : 0 ≤ nrm F σ :=
  Real.sqrt_nonneg _

/-!
Cauchy-Schwarz para integrales reales
-/

theorem cs_integral_mul_real {f g : ℝ → ℝ}
    (hf : ContinuousOn f I) (hg : ContinuousOn g I) :
    (∫ x : ℝ, f x * g x ∂μI) ^ 2 ≤ (∫ x : ℝ, f x ^ 2 ∂μI) * (∫ x : ℝ, g x ^ 2 ∂μI) := by
  set A : ℝ := ∫ x : ℝ, f x ^ 2 ∂μI
  set B : ℝ := ∫ x : ℝ, g x ^ 2 ∂μI
  set C : ℝ := ∫ x : ℝ, f x * g x ∂μI

  have hA : 0 ≤ A := integral_nonneg (fun x => by positivity)
  have hB : 0 ≤ B := integral_nonneg (fun x => by positivity)

  -- Q(t) = ∫ (f + t g)² ≥ 0
  have h_nonneg : ∀ t : ℝ, 0 ≤ ∫ x : ℝ, (f x + t * g x) ^ 2 ∂μI :=
    fun t => integral_nonneg (fun x => by positivity)

  -- Expand Q(t)
  have h_expand :
      ∀ t : ℝ,
        ∫ x : ℝ, (f x + t * g x) ^ 2 ∂μI = A + 2 * t * C + t ^ 2 * B := by
    intro t
    have h1 : Integrable (fun x => f x ^ 2) μI :=
      integrable_of_continuousOn (hf.pow 2)

    have h2_cont : ContinuousOn (fun x => 2 * t * (f x * g x)) I := by
      have hconst : ContinuousOn (fun _x : ℝ => (2 * t : ℝ)) I := continuousOn_const
      simpa [mul_assoc] using hconst.mul (hf.mul hg)

    have h2 : Integrable (fun x => 2 * t * (f x * g x)) μI :=
      integrable_of_continuousOn h2_cont

    have h3_cont : ContinuousOn (fun x => t ^ 2 * g x ^ 2) I := by
      have hconst : ContinuousOn (fun _x : ℝ => (t ^ 2 : ℝ)) I := continuousOn_const
      simpa [mul_assoc] using hconst.mul (hg.pow 2)

    have h3 : Integrable (fun x => t ^ 2 * g x ^ 2) μI :=
      integrable_of_continuousOn h3_cont

    have h12 : Integrable (fun x => f x ^ 2 + 2 * t * (f x * g x)) μI :=
      integrable_of_continuousOn ((hf.pow 2).add h2_cont)

    calc
      ∫ x : ℝ, (f x + t * g x) ^ 2 ∂μI
          =
          ∫ x : ℝ, (f x ^ 2 + 2 * t * (f x * g x) + t ^ 2 * g x ^ 2) ∂μI := by
            refine integral_congr_ae (ae_mem_I.mono fun x hx => ?_)
            ring
      _ =
          ∫ x : ℝ, (f x ^ 2 + 2 * t * (f x * g x)) ∂μI
            + ∫ x : ℝ, t ^ 2 * g x ^ 2 ∂μI := by
            rw [integral_add h12 h3]
      _ =
          (∫ x : ℝ, f x ^ 2 ∂μI + ∫ x : ℝ, 2 * t * (f x * g x) ∂μI)
            + ∫ x : ℝ, t ^ 2 * g x ^ 2 ∂μI := by
            rw [integral_add h1 h2]
      _ =
          ∫ x : ℝ, f x ^ 2 ∂μI
            + (∫ x : ℝ, 2 * t * (f x * g x) ∂μI + ∫ x : ℝ, t ^ 2 * g x ^ 2 ∂μI) := by
            ring
      _ =
          ∫ x : ℝ, f x ^ 2 ∂μI
            + ((2 * t) * ∫ x : ℝ, f x * g x ∂μI + (t ^ 2) * ∫ x : ℝ, g x ^ 2 ∂μI) := by
            -- pull out constants (evita `simp` pesado)
            have hC' :
                (∫ x : ℝ, 2 * t * (f x * g x) ∂μI)
                  = (2 * t) * (∫ x : ℝ, f x * g x ∂μI) := by
              simpa [mul_assoc] using
                (integral_mul_left (2 * t) (fun x : ℝ => f x * g x) (μ := μI))
            have hB' :
                (∫ x : ℝ, t ^ 2 * g x ^ 2 ∂μI)
                  = (t ^ 2) * (∫ x : ℝ, g x ^ 2 ∂μI) := by
              simpa [mul_assoc] using
                (integral_mul_left (t ^ 2) (fun x : ℝ => g x ^ 2) (μ := μI))
            -- reescribe con hC', hB'
            simp [hC', hB', add_assoc]
      _ = A + 2 * t * C + t ^ 2 * B := by
            dsimp [A, B, C]
            ring

  -- Main inequality C^2 ≤ A*B
  have hC2 : C ^ 2 ≤ A * B := by
    by_cases hB0 : B = 0
    · -- If B = 0 then Q(t) = A + 2 t C ≥ 0 for all t forces C = 0
      have hC0 : C = 0 := by
        by_contra hC0
        set t : ℝ := -(A + 1) / (2 * C)
        have hQ : 0 ≤ ∫ x : ℝ, (f x + t * g x) ^ 2 ∂μI := h_nonneg t
        -- rewrite using the expansion and B=0
        have hQ' : 0 ≤ A + 2 * t * C := by
          simpa [h_expand t, hB0] using hQ
        have ht : A + 2 * t * C = -1 := by
          -- compute with t = -(A+1)/(2C)
          field_simp [t, hC0]
          ring
        have : (0 : ℝ) ≤ -1 := by simpa [ht] using hQ'
        linarith
      -- `subst` expects a variable name; here we just rewrite via simp
      simp [hB0, hC0]
    · have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
      set t : ℝ := -C / B
      have hQ : 0 ≤ ∫ x : ℝ, (f x + t * g x) ^ 2 ∂μI := h_nonneg t
      have hQ' : 0 ≤ A + 2 * t * C + t ^ 2 * B := by
        simpa [h_expand t] using hQ
      have ht : A + 2 * t * C + t ^ 2 * B = A - C ^ 2 / B := by
        field_simp [t, hBpos.ne']
        ring
      have hQ'' : 0 ≤ A - C ^ 2 / B := by simpa [ht] using hQ'
      have hdiv : C ^ 2 / B ≤ A := by linarith
      have hmul : (C ^ 2 / B) * B ≤ A * B := mul_le_mul_of_nonneg_right hdiv hB
      -- simplify the left side
      simpa [div_eq_mul_inv, mul_assoc, hBpos.ne'] using hmul

  -- Return to the original statement
  simpa [A, B, C] using hC2



theorem abs_integral_mul_le {f g : ℝ → ℝ}
    (hf : ContinuousOn f I) (hg : ContinuousOn g I) :
    |∫ x : ℝ, f x * g x ∂μI| ≤
      Real.sqrt (∫ x : ℝ, f x ^ 2 ∂μI) * Real.sqrt (∫ x : ℝ, g x ^ 2 ∂μI) := by
  set A : ℝ := ∫ x : ℝ, f x ^ 2 ∂μI
  set B : ℝ := ∫ x : ℝ, g x ^ 2 ∂μI
  set C : ℝ := ∫ x : ℝ, f x * g x ∂μI

  have hA : 0 ≤ A := integral_nonneg (fun x => by positivity)
  have hB : 0 ≤ B := integral_nonneg (fun x => by positivity)

  have h_cs : C ^ 2 ≤ A * B := by
    simpa [A, B, C] using (cs_integral_mul_real (f := f) (g := g) hf hg)

  have h_abs : |C| ≤ Real.sqrt A * Real.sqrt B := by
    calc
      |C| = Real.sqrt (C ^ 2) := by
        simpa using (Real.sqrt_sq_eq_abs C).symm
      _ ≤ Real.sqrt (A * B) := by
        exact Real.sqrt_le_sqrt h_cs
      _ = Real.sqrt A * Real.sqrt B := by
        simpa using (Real.sqrt_mul hA B)

  simpa [A, B, C] using h_abs



theorem sqrt_integral_minkowski {f g : ℝ → ℝ}
    (hf : ContinuousOn f I) (hg : ContinuousOn g I) :
    Real.sqrt (∫ x : ℝ, (f x + g x) ^ 2 ∂μI) ≤
      Real.sqrt (∫ x : ℝ, f x ^ 2 ∂μI) + Real.sqrt (∫ x : ℝ, g x ^ 2 ∂μI) := by
  set A : ℝ := ∫ x : ℝ, f x ^ 2 ∂μI
  set B : ℝ := ∫ x : ℝ, g x ^ 2 ∂μI
  set C : ℝ := ∫ x : ℝ, f x * g x ∂μI

  have hA : 0 ≤ A := integral_nonneg (fun x => by positivity)
  have hB : 0 ≤ B := integral_nonneg (fun x => by positivity)

  have h_cs_abs : |C| ≤ Real.sqrt A * Real.sqrt B := by
    simpa [A, B, C] using (abs_integral_mul_le (f := f) (g := g) hf hg)

  -- Expansion of ∫(f+g)²
  have h_expand : ∫ x : ℝ, (f x + g x) ^ 2 ∂μI = A + 2 * C + B := by
    have h1 : Integrable (fun x => f x ^ 2) μI :=
      integrable_of_continuousOn (hf.pow 2)

    have h2_cont : ContinuousOn (fun x => 2 * (f x * g x)) I := by
      have hconst : ContinuousOn (fun _x : ℝ => (2 : ℝ)) I := continuousOn_const
      simpa [mul_assoc] using hconst.mul (hf.mul hg)

    have h2 : Integrable (fun x => 2 * (f x * g x)) μI :=
      integrable_of_continuousOn h2_cont

    have h3 : Integrable (fun x => g x ^ 2) μI :=
      integrable_of_continuousOn (hg.pow 2)

    have h12 : Integrable (fun x => f x ^ 2 + 2 * (f x * g x)) μI :=
      integrable_of_continuousOn ((hf.pow 2).add h2_cont)

    calc
      ∫ x : ℝ, (f x + g x) ^ 2 ∂μI
          = ∫ x : ℝ, (f x ^ 2 + 2 * f x * g x + g x ^ 2) ∂μI := by
            refine integral_congr_ae (ae_mem_I.mono fun x hx => ?_)
            ring
      _ = ∫ x : ℝ, ((f x ^ 2 + 2 * (f x * g x)) + g x ^ 2) ∂μI := by
            refine integral_congr_ae (ae_mem_I.mono fun x hx => ?_)
            ring
      _ = ∫ x : ℝ, (f x ^ 2 + 2 * (f x * g x)) ∂μI + ∫ x : ℝ, g x ^ 2 ∂μI := by
            simpa [add_assoc] using (integral_add h12 h3)
      _ = (∫ x : ℝ, f x ^ 2 ∂μI + ∫ x : ℝ, 2 * (f x * g x) ∂μI) + ∫ x : ℝ, g x ^ 2 ∂μI := by
            rw [integral_add h1 h2]
      _ = ∫ x : ℝ, f x ^ 2 ∂μI + (∫ x : ℝ, 2 * (f x * g x) ∂μI + ∫ x : ℝ, g x ^ 2 ∂μI) := by
            ring
      _ = ∫ x : ℝ, f x ^ 2 ∂μI + (2 * ∫ x : ℝ, f x * g x ∂μI + ∫ x : ℝ, g x ^ 2 ∂μI) := by
            simp [integral_mul_left, mul_assoc]
      _ = A + 2 * C + B := by
            dsimp [A, B, C]
            ring

  -- bound cross term using C ≤ |C| ≤ √A√B
  have hC_le : C ≤ Real.sqrt A * Real.sqrt B :=
    le_trans (le_abs_self C) h_cs_abs

  have h_ineq : A + 2 * C + B ≤ A + 2 * (Real.sqrt A * Real.sqrt B) + B := by
    linarith

  have h_sq : (Real.sqrt A + Real.sqrt B) ^ 2 = A + 2 * (Real.sqrt A * Real.sqrt B) + B := by
    calc
      (Real.sqrt A + Real.sqrt B) ^ 2
          = (Real.sqrt A) ^ 2 + 2 * Real.sqrt A * Real.sqrt B + (Real.sqrt B) ^ 2 := by
            ring
      _ = A + 2 * (Real.sqrt A * Real.sqrt B) + B := by
            rw [Real.sq_sqrt hA, Real.sq_sqrt hB]
            ring

  have h_sum : A + 2 * C + B ≤ (Real.sqrt A + Real.sqrt B) ^ 2 := by
    -- rewrite RHS using h_sq and apply h_ineq
    simpa [h_sq] using h_ineq

  calc
    Real.sqrt (∫ x : ℝ, (f x + g x) ^ 2 ∂μI)
        = Real.sqrt (A + 2 * C + B) := by rw [h_expand]
    _ ≤ Real.sqrt ((Real.sqrt A + Real.sqrt B) ^ 2) := by
          exact Real.sqrt_le_sqrt h_sum
    _ = |Real.sqrt A + Real.sqrt B| := by
          simpa using (Real.sqrt_sq_eq_abs (Real.sqrt A + Real.sqrt B))
    _ = Real.sqrt A + Real.sqrt B := by
          have : 0 ≤ Real.sqrt A + Real.sqrt B := by positivity
          simpa [this] using (abs_of_nonneg this)


theorem nrm_triangle (W V : ℝ → ℂ) (σ : ℝ)
    (hW : ContinuousOn W I) (hV : ContinuousOn V I) :
    nrm (fun x => W x + V x) σ ≤ nrm W σ + nrm V σ := by
  let wt : ℝ → ℝ := w (1 - σ)
  have hwt : ContinuousOn wt I := w_continuous (1 - σ)
  
  -- Raíz cuadrada del peso es continua en I
  have hswt_on_I : ContinuousOn (fun x => Real.sqrt (wt x)) I :=
    Real.continuous_sqrt.comp_continuousOn hwt
  
  -- Funciones auxiliares
  let a : ℝ → ℝ := fun x => ‖W x‖ * Real.sqrt (wt x)
  let b : ℝ → ℝ := fun x => ‖V x‖ * Real.sqrt (wt x)
  let c : ℝ → ℝ := fun x => ‖W x + V x‖ * Real.sqrt (wt x)
  
  have hnormW : ContinuousOn (fun x => ‖W x‖) I :=
    continuous_norm.comp_continuousOn hW
  
  have hnormV : ContinuousOn (fun x => ‖V x‖) I :=
    continuous_norm.comp_continuousOn hV
  
  have hWV : ContinuousOn (fun x => W x + V x) I := hW.add hV
  have hnormWV : ContinuousOn (fun x => ‖W x + V x‖) I :=
    continuous_norm.comp_continuousOn hWV
    
  have ha : ContinuousOn a I :=
    ContinuousOn.mul hnormW hswt_on_I
  have hb : ContinuousOn b I :=
    ContinuousOn.mul hnormV hswt_on_I
  have hc : ContinuousOn c I :=
    ContinuousOn.mul hnormWV hswt_on_I
  
  -- Desigualdad puntual
  have h_pointwise : ∀ x ∈ I, c x ≤ a x + b x := by
    intro x _
    dsimp [a, b, c]
    have h_norm : ‖W x + V x‖ ≤ ‖W x‖ + ‖V x‖ := norm_add_le (W x) (V x)
    have h_nonneg : 0 ≤ Real.sqrt (wt x) := Real.sqrt_nonneg _
    calc
      ‖W x + V x‖ * Real.sqrt (wt x) ≤ (‖W x‖ + ‖V x‖) * Real.sqrt (wt x) :=
        mul_le_mul_of_nonneg_right h_norm h_nonneg
      _ = ‖W x‖ * Real.sqrt (wt x) + ‖V x‖ * Real.sqrt (wt x) := by ring
      _ = a x + b x := rfl
  
  have h_sq_pointwise : ∀ᵐ x ∂μI, c x ^ 2 ≤ (a x + b x) ^ 2 := by
    refine ae_mem_I.mono ?_
    intro x hx
    have hc0 : 0 ≤ c x := by
      dsimp [c]
      exact mul_nonneg (norm_nonneg (W x + V x)) (Real.sqrt_nonneg _)
    exact pow_le_pow_left hc0 (h_pointwise x hx) 2
  
  -- Comparación de integrales
  have h_integral : ∫ x, c x ^ 2 ∂μI ≤ ∫ x, (a x + b x) ^ 2 ∂μI :=
    integral_mono_ae (integrable_of_continuousOn (hc.pow 2))
      (integrable_of_continuousOn ((ha.add hb).pow 2)) h_sq_pointwise
  
  -- Aplicar Minkowski
  have h_minkowski : Real.sqrt (∫ x, (a x + b x) ^ 2 ∂μI) ≤ 
                    Real.sqrt (∫ x, a x ^ 2 ∂μI) + Real.sqrt (∫ x, b x ^ 2 ∂μI) :=
    sqrt_integral_minkowski ha hb
  
  -- Relacionar con las normas originales
  have h_eq1 : (fun x => c x ^ 2) =ᵐ[μI] fun x => ‖W x + V x‖ ^ 2 * wt x := by
    refine ae_mem_I.mono ?_
    intro x hx
    dsimp [c, wt]
    have h_nonneg : 0 ≤ w (1 - σ) x := w_nonneg (1 - σ) x hx
    calc
      (‖W x + V x‖ * Real.sqrt (w (1 - σ) x)) ^ 2
          = ‖W x + V x‖ ^ 2 * (Real.sqrt (w (1 - σ) x)) ^ 2 := by ring
      _ = ‖W x + V x‖ ^ 2 * w (1 - σ) x := by rw [Real.sq_sqrt h_nonneg]
  
  have h_eq2 : (fun x => a x ^ 2) =ᵐ[μI] fun x => ‖W x‖ ^ 2 * wt x := by
    refine ae_mem_I.mono ?_
    intro x hx
    dsimp [a, wt]
    have h_nonneg : 0 ≤ w (1 - σ) x := w_nonneg (1 - σ) x hx
    calc
      (‖W x‖ * Real.sqrt (w (1 - σ) x)) ^ 2
          = ‖W x‖ ^ 2 * (Real.sqrt (w (1 - σ) x)) ^ 2 := by ring
      _ = ‖W x‖ ^ 2 * w (1 - σ) x := by rw [Real.sq_sqrt h_nonneg]
  
  have h_eq3 : (fun x => b x ^ 2) =ᵐ[μI] fun x => ‖V x‖ ^ 2 * wt x := by
    refine ae_mem_I.mono ?_
    intro x hx
    dsimp [b, wt]
    have h_nonneg : 0 ≤ w (1 - σ) x := w_nonneg (1 - σ) x hx
    calc
      (‖V x‖ * Real.sqrt (w (1 - σ) x)) ^ 2
          = ‖V x‖ ^ 2 * (Real.sqrt (w (1 - σ) x)) ^ 2 := by ring
      _ = ‖V x‖ ^ 2 * w (1 - σ) x := by rw [Real.sq_sqrt h_nonneg]
  
  calc
    nrm (fun x => W x + V x) σ
        = Real.sqrt (∫ x, ‖W x + V x‖ ^ 2 * wt x ∂μI) := by
          simp [nrm, Ew, P, wt]
    _ = Real.sqrt (∫ x, c x ^ 2 ∂μI) := by rw [integral_congr_ae h_eq1]
    _ ≤ Real.sqrt (∫ x, (a x + b x) ^ 2 ∂μI) := Real.sqrt_le_sqrt h_integral
    _ ≤ Real.sqrt (∫ x, a x ^ 2 ∂μI) + Real.sqrt (∫ x, b x ^ 2 ∂μI) := h_minkowski
    _ = Real.sqrt (∫ x, ‖W x‖ ^ 2 * wt x ∂μI) + Real.sqrt (∫ x, ‖V x‖ ^ 2 * wt x ∂μI) := by
          rw [integral_congr_ae h_eq2, integral_congr_ae h_eq3]
    _ = nrm W σ + nrm V σ := by simp [nrm, Ew, P, wt]

theorem abs_P_sub_le (W V : ℝ → ℂ) (σ : ℝ)
    (hW : ContinuousOn W I) (hV : ContinuousOn V I) :
    |P W (1 - σ) - P V (1 - σ)| ≤ nrm (fun x => W x - V x) σ * (nrm W σ + nrm V σ) := by
  let wt : ℝ → ℝ := w (1 - σ)
  have hwt : ContinuousOn wt I := w_continuous (1 - σ)
  
  -- Raíz cuadrada del peso es continua en I
  have hswt_on_I : ContinuousOn (fun x => Real.sqrt (wt x)) I :=
    Real.continuous_sqrt.comp_continuousOn hwt
  
  -- Funciones auxiliares
  let f : ℝ → ℝ := fun x => ‖W x - V x‖ * Real.sqrt (wt x)
  let g : ℝ → ℝ := fun x => (‖W x‖ + ‖V x‖) * Real.sqrt (wt x)
  
  have hnormW : ContinuousOn (fun x => ‖W x‖) I :=
    continuous_norm.comp_continuousOn hW
  
  have hnormV : ContinuousOn (fun x => ‖V x‖) I :=
    continuous_norm.comp_continuousOn hV
  
  have hWV : ContinuousOn (fun x => W x - V x) I := hW.sub hV
  have hnormWV : ContinuousOn (fun x => ‖W x - V x‖) I :=
    continuous_norm.comp_continuousOn hWV
  
  have hf : ContinuousOn f I :=
    ContinuousOn.mul hnormWV hswt_on_I
    
  have hsum : ContinuousOn (fun x => ‖W x‖ + ‖V x‖) I :=
    hnormW.add hnormV
  have hg : ContinuousOn g I :=
    ContinuousOn.mul hsum hswt_on_I
  
  -- Diferencia de P
  have h1 : Integrable (fun x => ‖W x‖ ^ 2 * wt x) μI := by
    refine integrable_of_continuousOn ?_
    exact ((continuous_norm.comp_continuousOn hW).pow 2).mul hwt
  have h2 : Integrable (fun x => ‖V x‖ ^ 2 * wt x) μI := by
    refine integrable_of_continuousOn ?_
    exact ((continuous_norm.comp_continuousOn hV).pow 2).mul hwt
  
  have h_diff : P W (1 - σ) - P V (1 - σ) = ∫ x, (‖W x‖ ^ 2 - ‖V x‖ ^ 2) * wt x ∂μI := by
    unfold P
    calc
      ∫ x : ℝ, ‖W x‖ ^ 2 * w (1 - σ) x ∂μI - ∫ x : ℝ, ‖V x‖ ^ 2 * w (1 - σ) x ∂μI
          = ∫ x : ℝ, (‖W x‖ ^ 2 * w (1 - σ) x - ‖V x‖ ^ 2 * w (1 - σ) x) ∂μI := by
            rw [integral_sub h1 h2]
      _ = ∫ x : ℝ, (‖W x‖ ^ 2 - ‖V x‖ ^ 2) * w (1 - σ) x ∂μI := by
            refine integral_congr_ae (ae_mem_I.mono fun x _ => ?_)
            ring
  
  rw [h_diff]
  
  -- Cota puntual
  have h_pointwise : ∀ᵐ x ∂μI, |(‖W x‖ ^ 2 - ‖V x‖ ^ 2) * wt x| ≤ f x * g x := by
    refine ae_mem_I.mono ?_
    intro x hx
    have hwt_pos : 0 ≤ wt x := w_nonneg (1 - σ) x hx
    
    -- Factorización
    have h_factor : ‖W x‖ ^ 2 - ‖V x‖ ^ 2 = (‖W x‖ - ‖V x‖) * (‖W x‖ + ‖V x‖) := by
      ring
      
    -- Desigualdad de normas
    have h_norm_diff : |‖W x‖ - ‖V x‖| ≤ ‖W x - V x‖ :=
      abs_norm_sub_norm_le (W x) (V x)
    
    calc
      |(‖W x‖ ^ 2 - ‖V x‖ ^ 2) * wt x|
          = |‖W x‖ ^ 2 - ‖V x‖ ^ 2| * wt x := by rw [abs_mul, abs_of_nonneg hwt_pos]
      _ = |(‖W x‖ - ‖V x‖) * (‖W x‖ + ‖V x‖)| * wt x := by rw [h_factor]
      _ = |‖W x‖ - ‖V x‖| * (‖W x‖ + ‖V x‖) * wt x := by
            rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖W x‖ + ‖V x‖)]
      _ ≤ ‖W x - V x‖ * (‖W x‖ + ‖V x‖) * wt x := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h_norm_diff ?_) hwt_pos
            positivity
      _ = ‖W x - V x‖ * (‖W x‖ + ‖V x‖) * (Real.sqrt (wt x)) ^ 2 := by rw [Real.sq_sqrt hwt_pos]
      _ = (‖W x - V x‖ * Real.sqrt (wt x)) * ((‖W x‖ + ‖V x‖) * Real.sqrt (wt x)) := by ring
      _ = f x * g x := rfl
  
  -- Cota de la integral
  have h_integral_bound : ∫ x, |(‖W x‖ ^ 2 - ‖V x‖ ^ 2) * wt x| ∂μI ≤ ∫ x, f x * g x ∂μI := by
    refine integral_mono_ae ?_ ?_ h_pointwise
    · refine integrable_of_continuousOn ?_
      have h1 : ContinuousOn (fun x => ‖W x‖ ^ 2) I :=
        (continuous_norm.comp_continuousOn hW).pow 2
      have h2 : ContinuousOn (fun x => ‖V x‖ ^ 2) I :=
        (continuous_norm.comp_continuousOn hV).pow 2
      exact ((h1.sub h2).mul hwt).abs
    · exact integrable_of_continuousOn (hf.mul hg)
  
  -- Aplicar Cauchy-Schwarz
  have h_cs : |∫ x, f x * g x ∂μI| ≤ 
              Real.sqrt (∫ x, f x ^ 2 ∂μI) * Real.sqrt (∫ x, g x ^ 2 ∂μI) :=
    abs_integral_mul_le hf hg
  
  -- La integral f*g es no negativa
  have h_nonneg : 0 ≤ ∫ x, f x * g x ∂μI := by
    refine integral_nonneg ?_
    intro x
    have hf_pos : 0 ≤ f x := by
      dsimp [f]
      exact mul_nonneg (norm_nonneg (W x - V x)) (Real.sqrt_nonneg _)
    have hg_pos : 0 ≤ g x := by
      dsimp [g]
      exact mul_nonneg (by positivity) (Real.sqrt_nonneg _)
    exact mul_nonneg hf_pos hg_pos
    
  rw [abs_of_nonneg h_nonneg] at h_cs
  
  -- Relacionar con normas
  have h_f_sq : (fun x => f x ^ 2) =ᵐ[μI] fun x => ‖W x - V x‖ ^ 2 * wt x := by
    refine ae_mem_I.mono ?_
    intro x hx
    dsimp [f, wt]
    have h_nonneg : 0 ≤ w (1 - σ) x := w_nonneg (1 - σ) x hx
    calc
      (‖W x - V x‖ * Real.sqrt (w (1 - σ) x)) ^ 2
          = ‖W x - V x‖ ^ 2 * (Real.sqrt (w (1 - σ) x)) ^ 2 := by ring
      _ = ‖W x - V x‖ ^ 2 * w (1 - σ) x := by rw [Real.sq_sqrt h_nonneg]
  
  have h_g_bound : Real.sqrt (∫ x, g x ^ 2 ∂μI) ≤ nrm W σ + nrm V σ := by
    have hg_eq : (fun x => g x ^ 2) =ᵐ[μI] fun x => ((‖W x‖ * Real.sqrt (wt x)) + (‖V x‖ * Real.sqrt (wt x))) ^ 2 := by
      refine ae_mem_I.mono ?_
      intro x _
      dsimp [g]
      ring
    have h_integral_eq : ∫ x, g x ^ 2 ∂μI = ∫ x, ((‖W x‖ * Real.sqrt (wt x)) + (‖V x‖ * Real.sqrt (wt x))) ^ 2 ∂μI :=
      integral_congr_ae hg_eq
    rw [h_integral_eq]
    have h_minkowski : Real.sqrt (∫ x, ((‖W x‖ * Real.sqrt (wt x)) + (‖V x‖ * Real.sqrt (wt x))) ^ 2 ∂μI) ≤
                      Real.sqrt (∫ x, (‖W x‖ * Real.sqrt (wt x)) ^ 2 ∂μI) + 
                      Real.sqrt (∫ x, (‖V x‖ * Real.sqrt (wt x)) ^ 2 ∂μI) :=
      sqrt_integral_minkowski (ContinuousOn.mul hnormW hswt_on_I) (ContinuousOn.mul hnormV hswt_on_I)
    have ha_sq : (fun x => (‖W x‖ * Real.sqrt (wt x)) ^ 2) =ᵐ[μI] fun x => ‖W x‖ ^ 2 * wt x := by
      refine ae_mem_I.mono ?_
      intro x hx
      have h_nonneg : 0 ≤ w (1 - σ) x := w_nonneg (1 - σ) x hx
      dsimp [wt]
      calc
        (‖W x‖ * Real.sqrt (w (1 - σ) x)) ^ 2 = ‖W x‖ ^ 2 * (Real.sqrt (w (1 - σ) x)) ^ 2 := by ring
        _ = ‖W x‖ ^ 2 * w (1 - σ) x := by rw [Real.sq_sqrt h_nonneg]
    have hb_sq : (fun x => (‖V x‖ * Real.sqrt (wt x)) ^ 2) =ᵐ[μI] fun x => ‖V x‖ ^ 2 * wt x := by
      refine ae_mem_I.mono ?_
      intro x hx
      have h_nonneg : 0 ≤ w (1 - σ) x := w_nonneg (1 - σ) x hx
      dsimp [wt]
      calc
        (‖V x‖ * Real.sqrt (w (1 - σ) x)) ^ 2 = ‖V x‖ ^ 2 * (Real.sqrt (w (1 - σ) x)) ^ 2 := by ring
        _ = ‖V x‖ ^ 2 * w (1 - σ) x := by rw [Real.sq_sqrt h_nonneg]
    have H1 : Real.sqrt (∫ x, (‖W x‖ * Real.sqrt (wt x)) ^ 2 ∂μI) = nrm W σ := by
      rw [integral_congr_ae ha_sq]
      simp [nrm, Ew, P, wt]
    have H2 : Real.sqrt (∫ x, (‖V x‖ * Real.sqrt (wt x)) ^ 2 ∂μI) = nrm V σ := by
      rw [integral_congr_ae hb_sq]
      simp [nrm, Ew, P, wt]
    rw [H1, H2] at h_minkowski
    exact h_minkowski
  
  -- Calcular norma de W-V
  have h_nrm_diff : nrm (fun x => W x - V x) σ = Real.sqrt (∫ x, f x ^ 2 ∂μI) := by
    have : ∫ x, f x ^ 2 ∂μI = ∫ x, ‖W x - V x‖ ^ 2 * wt x ∂μI :=
      integral_congr_ae h_f_sq
    simp [nrm, Ew, P, wt, this]
  
  -- Ensamblar la prueba: |∫ f| ≤ ∫ |f|
  have h_int_abs : |∫ x, (‖W x‖ ^ 2 - ‖V x‖ ^ 2) * wt x ∂μI| ≤ 
                   ∫ x, |(‖W x‖ ^ 2 - ‖V x‖ ^ 2) * wt x| ∂μI := by
    calc
      |∫ x, (‖W x‖ ^ 2 - ‖V x‖ ^ 2) * wt x ∂μI| = 
          ‖∫ x, (‖W x‖ ^ 2 - ‖V x‖ ^ 2) * wt x ∂μI‖ := by rw [Real.norm_eq_abs]
      _ ≤ ∫ x, ‖(‖W x‖ ^ 2 - ‖V x‖ ^ 2) * wt x‖ ∂μI := norm_integral_le_integral_norm _
      _ = ∫ x, |(‖W x‖ ^ 2 - ‖V x‖ ^ 2) * wt x| ∂μI := by simp_rw [Real.norm_eq_abs]
  
  calc
    |∫ x, (‖W x‖ ^ 2 - ‖V x‖ ^ 2) * wt x ∂μI|
        ≤ ∫ x, |(‖W x‖ ^ 2 - ‖V x‖ ^ 2) * wt x| ∂μI := h_int_abs
    _ ≤ ∫ x, f x * g x ∂μI := h_integral_bound
    _ ≤ Real.sqrt (∫ x, f x ^ 2 ∂μI) * Real.sqrt (∫ x, g x ^ 2 ∂μI) := h_cs
    _ = nrm (fun x => W x - V x) σ * Real.sqrt (∫ x, g x ^ 2 ∂μI) := by rw [h_nrm_diff]
    _ ≤ nrm (fun x => W x - V x) σ * (nrm W σ + nrm V σ) := by
        exact mul_le_mul_of_nonneg_left h_g_bound (nrm_nonneg _ _)

end

end RiemannEnergy
