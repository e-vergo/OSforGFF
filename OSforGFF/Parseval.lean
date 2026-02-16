/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/
import OSforGFF.FourierTransforms
import OSforGFF.CovarianceMomentum
import Dress

/-!
# Parseval Identity for Covariance

This file proves the fundamental Parseval identity relating the position-space
covariance bilinear form to the momentum-space propagator.

### Statement

For a Schwartz test function f : TestFunctionℂ and mass m > 0:

  (∫∫ f(x) * C(x,y) * conj(f(y)) dx dy).re = ∫ |f̂(k)|² * P(k) dk

where:
- C(x,y) = freeCovariance m x y is the position-space propagator
- P(k) = freePropagatorMomentum m k = 1/(‖k‖² + m²) is the momentum-space propagator
- f̂ = SchwartzMap.fourierTransformCLM ℂ f is the Fourier transform

### Proof Strategy

1. **Substitute Fourier representation of C(x,y)**:
   C(x,y) = (∫ P(k) e^{-ik·(x-y)} dk / (2π)^d).re

2. **Apply Fubini** to swap integrals (integrate over x and y first):
   ∫∫∫ f(x) * P(k) * e^{-ik·(x-y)} * conj(f(y)) dx dy dk

3. **Recognize Fourier transforms**:
   - ∫ f(x) e^{-ikx} dx relates to f̂(k)
   - ∫ conj(f(y)) e^{iky} dy relates to conj(f̂(k))

4. **Handle normalization mismatch**:
   - Physics convention: exp(-i k·x) with (2π)^d normalization
   - Mathlib convention: exp(-2πi ⟨v,w⟩) (unitary normalization)

5. **Combine** to get |f̂(k)|² * P(k)

### Main Difficulties

- Normalization: Physics uses exp(-ik·x)/(2π)^d, Mathlib uses exp(-2πi⟨x,k⟩)
- Multiple integrability conditions need verification
- Fubini requires showing the triple integral is absolutely convergent
-/

section ParsevalCovariance

open MeasureTheory Complex Real SchwartzMap
open scoped MeasureTheory ComplexConjugate Real InnerProductSpace BigOperators

-- We need access to the basic definitions
variable {d : ℕ} [NeZero d]

/-- Normalization constant for the Fourier transform. -/
@[blueprint "def:fourier-normalization"
  (title := "Fourier Normalization Constant")]
noncomputable def fourierNormalization (d : ℕ) : ℝ := (2 * Real.pi) ^ d

/-! ### Bridge Lemmas

These lemmas connect the physics-convention Fourier transform (used in freeCovariance)
to Mathlib's convention (used in SchwartzMap.fourierTransformCLM).
-/


/-! ### Fourier Transform Convention Analysis

**IMPORTANT**: There is a convention mismatch between physics and Mathlib Fourier transforms.

**Mathlib convention** (from `Real.fourierIntegral_eq`):
  `𝓕 f(k) = ∫ f(x) exp(-2πi⟨x, k⟩) dx`

**Physics convention** (used in `freeCovariance`):
  `f̂_phys(k) = ∫ f(x) exp(-i⟨k, x⟩) dx`

**Relationship**:
  `f̂_phys(k) = 𝓕 f(k/(2π))`

This means:
  `|f̂_phys(k)|² = |𝓕 f(k/(2π))|²`   (evaluated at DIFFERENT momenta)

NOT:
  `|f̂_phys(k)|² = (2π)^d |𝓕 f(k)|²`  (this is FALSE for generic f)

**Impact on Parseval identity**:

After Fubini, the LHS becomes:
  `(1/(2π)^d) ∫_k P(k) |f̂_phys(k)|² dk`

With change of variables `p = k/(2π)`:
  `= ∫_p P(2πp) |𝓕 f(p)|² dp`
  `= ∫_p |𝓕 f(p)|² / (4π²‖p‖² + m²) dp`

So the correct Parseval identity using Mathlib's FT should have propagator `1/(4π²‖p‖² + m²)`,
NOT `1/(‖p‖² + m²)`.

The axiom `parseval_covariance_schwartz` in Covariance.lean now correctly uses
`freePropagatorMomentum_mathlib m k = 1/((2π)²‖k‖² + m²)` with Mathlib's `fourierTransformCLM`.
-/

/-- The relationship between physics and Mathlib propagators under rescaling.
    `freePropagatorMomentum_mathlib` is defined in CovarianceMomentum.lean. -/
@[blueprint "lem:free-propagator-momentum-rescale"
  (title := "Propagator Rescaling under Momentum Change of Variables")]
lemma freePropagatorMomentum_rescale (m : ℝ) (k : SpaceTime) :
    freePropagatorMomentum m ((2 * Real.pi) • k) = freePropagatorMomentum_mathlib m k := by
  simp only [freePropagatorMomentum, freePropagatorMomentum_mathlib]
  congr 1
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos Real.two_pi_pos]
  ring


/-- The scaling factor for momentum integration change of variables. -/
@[blueprint "def:momentum-scale-factor"
  (title := "Momentum Scale Factor")
  (statement := /-- The momentum scaling factor $2\pi$ for Fourier transform conventions. -/)]
noncomputable def momentumScaleFactor : ℝ := 2 * Real.pi
@[blueprint "lem:momentum-scale-factor-pos"
  (title := "Momentum Scale Factor Positivity")
  (statement := /-- The momentum scale factor $2\pi > 0$. -/)]

lemma momentumScaleFactor_pos : 0 < momentumScaleFactor := Real.two_pi_pos
@[blueprint "lem:momentum-scale-factor-ne-zero"
  (title := "Momentum Scale Factor Nonzero")
  (statement := /-- The momentum scale factor $2\pi \ne 0$. -/)]

lemma momentumScaleFactor_ne_zero : momentumScaleFactor ≠ 0 := momentumScaleFactor_pos.ne'

/-- The scaling map on momentum space: k ↦ 2πk -/
@[blueprint "def:momentum-scale"
  (title := "Momentum Scaling Map")
  (statement := /-- The linear map $k \mapsto 2\pi k$ on momentum space. -/)]
noncomputable def momentumScale : SpaceTime →ₗ[ℝ] SpaceTime :=
  momentumScaleFactor • LinearMap.id

/-- The momentum scaling as a linear equivalence. -/
@[blueprint "def:momentum-scale-equiv"
  (title := "Momentum Scale Equivalence")
  (statement := /-- The momentum scaling $k \mapsto 2\pi k$ as a linear equivalence. -/)]
noncomputable def momentumScaleEquiv : SpaceTime ≃ₗ[ℝ] SpaceTime :=
  LinearEquiv.smulOfUnit (Units.mk0 momentumScaleFactor momentumScaleFactor_ne_zero)

/-! ### Physics vs Mathlib Fourier Transform Bridge

The "physics" Fourier transform uses convention `∫ f(x) exp(-i⟨k,x⟩) dx`
while Mathlib uses `∫ f(x) exp(-2πi⟨x,ξ⟩) dx`.

Key relationship: `f̂_phys(2πξ) = 𝓕f(ξ)` -/

/-- The physics-convention Fourier transform of a Schwartz function.
    Uses `exp(-i⟨k,x⟩)` instead of Mathlib's `exp(-2πi⟨x,ξ⟩)`. -/
@[blueprint "def:physics-fourier"
  (title := "Physics Fourier Transform")
  (statement := /-- The physics convention Fourier transform $\hat{f}(k) = \int f(x) e^{-i\langle k, x \rangle}\,dx$ (without $2\pi$ factors). -/)
  (latexEnv := "definition")
  (latexLabel := "def:physics-fourier")]
noncomputable def physicsFourierTransform (f : TestFunctionℂ) (k : SpaceTime) : ℂ :=
  ∫ x, f x * Complex.exp (-Complex.I * ((@inner ℝ SpaceTime _ k x : ℝ) : ℂ)) ∂volume

/-- The regulated Fourier covariance equals the full complex Fourier integral (not just the real part).
    The regulator exp(-α‖k‖²) ensures absolute convergence. -/
@[blueprint "lem:free-covariance-regulated-eq-complex-integral"
  (title := "Regulated Covariance as Complex Integral")
  (statement := /-- The regulated covariance equals the complex Fourier integral: $\tilde{C}_\alpha(x,y) = \int_{\mathbb{R}^4} e^{-\alpha \|k\|^2} \tilde{C}(k) e^{-i k \cdot (x-y)} dk$. -/)]
lemma freeCovariance_regulated_eq_complex_integral (α : ℝ) (m : ℝ) (x y : SpaceTime) :
    (freeCovariance_regulated α m x y : ℂ) =
    ∫ k, ((Real.exp (-α * ‖k‖^2) * freePropagatorMomentum m k / fourierNormalization STDimension : ℝ) : ℂ) *
      Complex.exp (-Complex.I * ((@inner ℝ SpaceTime _ k (x - y) : ℝ) : ℂ)) ∂volume := by
  simp only [freeCovariance_regulated, fourierNormalization]
  -- The integral is real (im = 0), so ↑(I.re) = I
  set f : SpaceTime → ℂ := fun k => ↑(Real.exp (-α * ‖k‖ ^ 2) * freePropagatorMomentum m k /
    (2 * Real.pi) ^ STDimension) * Complex.exp (-Complex.I * ↑⟪k, x - y⟫_ℝ)
  set I : ℂ := ∫ k, f k with hI
  -- f(-k) = conj(f(k))
  have hf_conj : ∀ k, f (-k) = starRingEnd ℂ (f k) := fun k => by
    simp only [f, norm_neg, freePropagator_even, inner_neg_left,
      map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_neg, Complex.conj_I, neg_neg]
    congr 1
    simp only [Complex.ofReal_neg, neg_mul, mul_neg, neg_neg]
  -- So I = ∫f(k) = ∫f(-k) = ∫conj(f(k)) = conj(I)
  have h_self_conj : I = starRingEnd ℂ I := by
    have h1 : I = ∫ k, f (-k) := (integral_comp_neg_spacetime f).symm
    conv_rhs => rw [← integral_conj]
    rw [h1]
    congr 1; funext k; exact hf_conj k
  have h_im_zero : I.im = 0 := by
    have : I.im = -I.im := by
      calc I.im = (starRingEnd ℂ I).im := by rw [← h_self_conj]
        _ = -I.im := Complex.conj_im I
    linarith
  calc (I.re : ℂ) = I.re + I.im * Complex.I := by simp [h_im_zero]
    _ = I := Complex.re_add_im I

/-! ### Regulated Parseval Identity - Full Proof

The following section contains the complete proof of the regulated Parseval identity,
replacing the previous axiom. The proof uses:
- Gaussian regulator for absolute convergence
- Fubini theorem for integral reordering
- Phase factorization for separating x and y integrals
- Change of variables from physics to Mathlib Fourier convention
-/

/-- The phase factor exp(-i⟨k,x-y⟩) is bounded by 1 in norm. -/
@[blueprint "lem:phase-bound"
  (title := "Phase Factor Norm Bound")
  (statement := /-- The phase factor $e^{-i\langle k, x-y \rangle}$ has norm at most 1. -/)]
lemma phase_bound (k x y : SpaceTime) :
    ‖Complex.exp (-Complex.I * Complex.ofReal ⟪k, x - y⟫_ℝ)‖ ≤ 1 := by
  have h : -Complex.I * Complex.ofReal ⟪k, x - y⟫_ℝ = Complex.ofReal (-⟪k, x - y⟫_ℝ) * Complex.I := by
    simp only [Complex.ofReal_neg, neg_mul]
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

/-- The free propagator is bounded by 1/m². -/
@[blueprint "lem:free-propagator-momentum-le-inv-sq"
  (title := "Free Propagator Upper Bound")
  (statement := /-- The free propagator satisfies $\tilde{C}(k) \le \frac{1}{m^2}$ for all $k$. -/)]
lemma freePropagatorMomentum_le_inv_sq (m : ℝ) [Fact (0 < m)] (k : SpaceTime) :
    freePropagatorMomentum m k ≤ 1 / m^2 := by
  simp only [freePropagatorMomentum]
  apply one_div_le_one_div_of_le
  · exact pow_pos (Fact.out : 0 < m) 2
  · linarith [sq_nonneg ‖k‖]

/-- The free propagator is strictly positive. -/
@[blueprint "lem:free-propagator-momentum-pos"
  (title := "Free Propagator Positivity")
  (statement := /-- The free propagator $\tilde{C}(k) > 0$ for all $k$. -/)]
lemma freePropagatorMomentum_pos' (m : ℝ) [Fact (0 < m)] (k : SpaceTime) :
    0 < freePropagatorMomentum m k := by
  simp only [freePropagatorMomentum]
  apply one_div_pos.mpr
  apply add_pos_of_nonneg_of_pos (sq_nonneg _)
  exact pow_pos (Fact.out : 0 < m) 2

/-- The Gaussian regulator exp(-α‖k‖²) is integrable for α > 0. -/
@[blueprint "lem:gaussian-regulator-integrable-2"
  (title := "Gaussian Regulator Integrability")
  (statement := /-- For $\alpha > 0$, the Gaussian regulator $e^{-\alpha \|k\|^2}$ is integrable. -/)]
lemma gaussian_regulator_integrable (α : ℝ) (hα : 0 < α) :
    Integrable (fun k : SpaceTime => Real.exp (-α * ‖k‖^2)) volume := by
  have hα_re : (0 : ℝ) < (α : ℂ).re := by simp [hα]
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := SpaceTime) hα_re 0 0
  simp only [zero_mul, add_zero] at h
  have h' : Integrable (fun k : SpaceTime => (Real.exp (-α * ‖k‖^2) : ℂ)) volume := by
    have heq : ∀ k : SpaceTime, Complex.exp (-↑α * ↑‖k‖ ^ 2) = ↑(Real.exp (-α * ‖k‖ ^ 2)) := by
      intro k
      simp only [← Complex.ofReal_neg, ← Complex.ofReal_mul, ← Complex.ofReal_pow, Complex.ofReal_exp]
    simp_rw [heq] at h
    exact h
  exact h'.re

/-- The Gaussian regulator is continuous. -/
@[blueprint "lem:gaussian-regulator-continuous"
  (title := "Gaussian Regulator Continuity")
  (statement := /-- The Gaussian regulator $e^{-\alpha \|k\|^2}$ is continuous. -/)]
lemma gaussian_regulator_continuous (α : ℝ) :
    Continuous (fun k : SpaceTime => Real.exp (-α * ‖k‖^2)) := by
  refine Real.continuous_exp.comp ?_
  have h1 : Continuous (fun k : SpaceTime => α * ‖k‖^2) := continuous_const.mul (continuous_norm.pow 2)
  convert h1.neg using 1
  ext k; ring

/-- The norm of the regulated propagator as a complex number. -/
@[blueprint "lem:regulated-propagator-norm"
  (title := "Regulated Propagator Norm")
  (statement := /-- The norm of the regulated propagator equals its real value: $\left\|e^{-\alpha \|k\|^2} \tilde{C}(k) / (2\pi)^4\right\| = e^{-\alpha \|k\|^2} \tilde{C}(k) / (2\pi)^4$. -/)]
lemma regulated_propagator_norm (α : ℝ) (m : ℝ) [Fact (0 < m)] (k : SpaceTime) :
    ‖(Real.exp (-α * ‖k‖^2) * freePropagatorMomentum m k / (2 * Real.pi) ^ STDimension : ℂ)‖ =
    Real.exp (-α * ‖k‖^2) * freePropagatorMomentum m k / (2 * Real.pi) ^ STDimension := by
  have hprop_nonneg : 0 ≤ freePropagatorMomentum m k := le_of_lt (freePropagatorMomentum_pos' m k)
  have hC_nonneg : (0 : ℝ) ≤ (2 * Real.pi) ^ STDimension := pow_nonneg (by positivity) _
  have hval_nonneg : 0 ≤ Real.exp (-α * ‖k‖^2) * freePropagatorMomentum m k / (2 * Real.pi) ^ STDimension :=
    div_nonneg (mul_nonneg (Real.exp_nonneg _) hprop_nonneg) hC_nonneg
  have h : (Real.exp (-α * ‖k‖^2) * freePropagatorMomentum m k / (2 * Real.pi) ^ STDimension : ℂ) =
      ↑(Real.exp (-α * ‖k‖^2) * freePropagatorMomentum m k / (2 * Real.pi) ^ STDimension) := by
    push_cast; ring
  rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hval_nonneg]

/-- The inner product function is measurable. -/
@[blueprint "lem:measurable-inner-fixed"
  (title := "Measurability of Inner Product with Fixed Vector")
  (statement := /-- The function $x \mapsto \langle k, x \rangle$ is measurable for fixed $k$. -/)]
lemma measurable_inner_fixed (k : SpaceTime) : Measurable (fun x : SpaceTime => ⟪k, x⟫_ℝ) :=
  measurable_const.inner measurable_id

/-- The phase exponential exp(-i⟨k,x⟩) is measurable. -/
@[blueprint "lem:measurable-phase-exp"
  (title := "Measurability of Phase Exponential")
  (statement := /-- The function $x \mapsto e^{-i\langle k, x \rangle}$ is measurable. -/)]
lemma measurable_phase_exp (k : SpaceTime) :
    Measurable (fun x : SpaceTime => Complex.exp (-Complex.I * Complex.ofReal ⟪k, x⟫_ℝ)) := by
  apply Complex.measurable_exp.comp
  apply Measurable.const_mul
  exact Complex.measurable_ofReal.comp (measurable_inner_fixed k)

/-- The conjugate phase exponential exp(i⟨k,x⟩) is measurable. -/
@[blueprint "lem:measurable-phase-exp-conj"
  (title := "Measurability of Conjugate Phase Exponential")
  (statement := /-- The function $x \mapsto e^{i\langle k, x \rangle}$ is measurable. -/)]
lemma measurable_phase_exp_conj (k : SpaceTime) :
    Measurable (fun x : SpaceTime => Complex.exp (Complex.I * Complex.ofReal ⟪k, x⟫_ℝ)) := by
  apply Complex.measurable_exp.comp
  apply Measurable.const_mul
  exact Complex.measurable_ofReal.comp (measurable_inner_fixed k)

/-- A Schwartz function times the phase exp(-i⟨k,x⟩) is integrable. -/
@[blueprint "lem:schwartz-mul-phase-integrable"
  (title := "Integrability of Schwartz Function Times Phase")
  (statement := /-- A Schwartz function times $e^{-i\langle k, x \rangle}$ is integrable. -/)]
lemma schwartz_mul_phase_integrable (f : TestFunctionℂ) (k : SpaceTime) :
    Integrable (fun x => f x * Complex.exp (-Complex.I * Complex.ofReal ⟪k, x⟫_ℝ)) volume := by
  apply SchwartzMap.integrable_mul_bounded (μ := volume) f _ (measurable_phase_exp k)
  intro x
  rw [norm_exp_neg_I_mul_real]

/-- The conjugate of a Schwartz function times the phase exp(i⟨k,y⟩) is integrable. -/
@[blueprint "lem:schwartz-conj-mul-phase-integrable"
  (title := "Integrability of Conjugate Schwartz Function Times Phase")
  (statement := /-- The conjugate of a Schwartz function times $e^{i\langle k, y \rangle}$ is integrable. -/)]
lemma schwartz_conj_mul_phase_integrable (f : TestFunctionℂ) (k : SpaceTime) :
    Integrable (fun y => starRingEnd ℂ (f y) * Complex.exp (Complex.I * Complex.ofReal ⟪k, y⟫_ℝ)) volume := by
  have hf_conj_int : Integrable (fun y => starRingEnd ℂ (f y)) volume :=
    SchwartzMap.integrable_conj (μ := volume) f
  have hg_meas := measurable_phase_exp_conj k
  have hg_bdd : ∀ y, ‖Complex.exp (Complex.I * Complex.ofReal ⟪k, y⟫_ℝ)‖ ≤ 1 := by
    intro y; rw [norm_exp_I_mul_real]
  have h := hf_conj_int.bdd_mul hg_meas.aestronglyMeasurable (Filter.Eventually.of_forall hg_bdd)
  convert h using 1
  ext y; ring

/-- The bounding function for the triple integrand is integrable. -/
@[blueprint "lem:triple-bound-integrable"
  (title := "Integrability of Triple Integral Bounding Function")
  (statement := /-- The bounding function for the regulated triple integral is integrable. -/)]
lemma triple_bound_integrable (α : ℝ) (hα : 0 < α) (m : ℝ) [Fact (0 < m)] (f : TestFunctionℂ) :
    Integrable (fun p : SpaceTime × SpaceTime × SpaceTime =>
      ‖f p.1‖ * ((1 / m^2 / (2 * Real.pi) ^ STDimension) * Real.exp (-α * ‖p.2.2‖^2)) * ‖f p.2.1‖)
      (volume.prod (volume.prod volume)) := by
  have hf_int : Integrable f volume := f.integrable
  have h1 : Integrable (fun x : SpaceTime => ‖f x‖) volume := hf_int.norm
  have hgauss := gaussian_regulator_integrable α hα
  have h2 : Integrable (fun k : SpaceTime => (1 / m^2 / (2 * Real.pi) ^ STDimension) *
      Real.exp (-α * ‖k‖^2)) volume := Integrable.const_mul hgauss _
  have h3 : Integrable (fun y : SpaceTime => ‖f y‖) volume := hf_int.norm
  have hyk : Integrable (fun p : SpaceTime × SpaceTime =>
      ‖f p.1‖ * ((1 / m^2 / (2 * Real.pi) ^ STDimension) * Real.exp (-α * ‖p.2‖^2)))
      (volume.prod volume) := Integrable.mul_prod h3 h2
  have h := Integrable.mul_prod h1 hyk
  convert h using 1
  ext ⟨x, y, k⟩
  ring

/-- The triple integrand is bounded by the integrable bounding function. -/
@[blueprint "lem:triple-integrand-norm-le"
  (title := "Norm Bound for Triple Integrand")
  (statement := /-- The triple integrand is bounded by the integrable bounding function. -/)]
lemma triple_integrand_norm_le (α : ℝ) (m : ℝ) [Fact (0 < m)] (f : TestFunctionℂ)
    (x y k : SpaceTime) :
    ‖f x * (Real.exp (-α * ‖k‖^2) * freePropagatorMomentum m k / (2 * Real.pi) ^ STDimension : ℂ) *
      Complex.exp (-Complex.I * Complex.ofReal ⟪k, x - y⟫_ℝ) * starRingEnd ℂ (f y)‖ ≤
    ‖f x‖ * ((1 / m^2 / (2 * Real.pi) ^ STDimension) * Real.exp (-α * ‖k‖^2)) * ‖f y‖ := by
  have hphase := phase_bound k x y
  have hprop := freePropagatorMomentum_le_inv_sq m k
  have hprop_nonneg : 0 ≤ freePropagatorMomentum m k := le_of_lt (freePropagatorMomentum_pos' m k)
  have hC_nonneg : (0 : ℝ) ≤ (2 * Real.pi) ^ STDimension := pow_nonneg (by positivity) _
  have hconj_norm : ‖starRingEnd ℂ (f y)‖ = ‖f y‖ := RCLike.norm_conj (f y)
  calc ‖f x * (Real.exp (-α * ‖k‖^2) * freePropagatorMomentum m k / (2 * Real.pi) ^ STDimension : ℂ) *
        Complex.exp (-Complex.I * Complex.ofReal ⟪k, x - y⟫_ℝ) * starRingEnd ℂ (f y)‖
    _ = ‖f x‖ * ‖(Real.exp (-α * ‖k‖^2) * freePropagatorMomentum m k / (2 * Real.pi) ^ STDimension : ℂ)‖ *
        ‖Complex.exp (-Complex.I * Complex.ofReal ⟪k, x - y⟫_ℝ)‖ * ‖starRingEnd ℂ (f y)‖ := by
      simp only [norm_mul]
    _ ≤ ‖f x‖ * ‖(Real.exp (-α * ‖k‖^2) * freePropagatorMomentum m k / (2 * Real.pi) ^ STDimension : ℂ)‖ *
        1 * ‖f y‖ := by
      gcongr
      · exact hconj_norm.le
    _ = ‖f x‖ * (Real.exp (-α * ‖k‖^2) * freePropagatorMomentum m k / (2 * Real.pi) ^ STDimension) * ‖f y‖ := by
      rw [mul_one, regulated_propagator_norm]
    _ ≤ ‖f x‖ * (1 / m^2 / (2 * Real.pi) ^ STDimension * Real.exp (-α * ‖k‖^2)) * ‖f y‖ := by
      gcongr
      calc Real.exp (-α * ‖k‖^2) * freePropagatorMomentum m k / (2 * Real.pi) ^ STDimension
        _ ≤ Real.exp (-α * ‖k‖^2) * (1 / m^2) / (2 * Real.pi) ^ STDimension := by
            gcongr
        _ = 1 / m^2 / (2 * Real.pi) ^ STDimension * Real.exp (-α * ‖k‖^2) := by ring

/-- The regulated integrand is integrable in all variables jointly. -/
@[blueprint "lem:regulated-triple-integrable"
  (title := "Integrability of Regulated Triple Integrand")
  (statement := /-- The regulated integrand is integrable in all three variables. -/)]
lemma regulated_triple_integrable (α : ℝ) (hα : 0 < α) (m : ℝ) [Fact (0 < m)] (f : TestFunctionℂ) :
    Integrable (fun p : SpaceTime × SpaceTime × SpaceTime =>
      let (x, y, k) := p
      f x * (Real.exp (-α * ‖k‖^2) * freePropagatorMomentum m k / (2 * Real.pi) ^ STDimension : ℂ) *
        Complex.exp (-Complex.I * Complex.ofReal ⟪k, x - y⟫_ℝ) * starRingEnd ℂ (f y))
      (volume.prod (volume.prod volume)) := by
  have h_bound := triple_bound_integrable α hα m f
  refine h_bound.mono' ?meas ?bound
  case meas =>
    apply AEStronglyMeasurable.mul
    apply AEStronglyMeasurable.mul
    apply AEStronglyMeasurable.mul
    · exact f.continuous.aestronglyMeasurable.comp_measurable measurable_fst
    · have hcont : Continuous (fun k : SpaceTime =>
          (Real.exp (-α * ‖k‖^2) * freePropagatorMomentum m k / (2 * Real.pi) ^ STDimension : ℂ)) := by
        have h1 : Continuous (fun k : SpaceTime =>
            Real.exp (-α * ‖k‖^2) * freePropagatorMomentum m k / (2 * Real.pi) ^ STDimension) :=
          ((gaussian_regulator_continuous α).mul (freePropagator_continuous (m := m))).div_const _
        have h2 : Continuous (fun k : SpaceTime =>
            (Real.exp (-α * ‖k‖^2) * freePropagatorMomentum m k / (2 * Real.pi) ^ STDimension : ℂ)) := by
          convert Complex.continuous_ofReal.comp h1 using 1
          ext k
          simp only [Function.comp_apply, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow,
            Complex.ofReal_ofNat]
        exact h2
      exact hcont.aestronglyMeasurable.comp_measurable (measurable_snd.comp measurable_snd)
    · have h_inner_meas : Measurable (fun p : SpaceTime × SpaceTime × SpaceTime => ⟪p.2.2, p.1 - p.2.1⟫_ℝ) :=
        Measurable.inner measurable_snd.snd (measurable_fst.sub measurable_snd.fst)
      have h_phase_meas : Measurable (fun p : SpaceTime × SpaceTime × SpaceTime =>
          -Complex.I * Complex.ofReal ⟪p.2.2, p.1 - p.2.1⟫_ℝ) := by
        exact (measurable_const.mul (Complex.measurable_ofReal.comp h_inner_meas))
      exact Complex.continuous_exp.aestronglyMeasurable.comp_measurable h_phase_meas
    · have hcont : Continuous (fun y => starRingEnd ℂ (f y)) := f.continuous.star
      exact hcont.aestronglyMeasurable.comp_measurable measurable_snd.fst
  case bound =>
    filter_upwards with ⟨x, y, k⟩
    exact triple_integrand_norm_le α m f x y k

/-- Phase factorization: exp(-i⟨k,x-y⟩) = exp(-i⟨k,x⟩) · exp(i⟨k,y⟩) -/
@[blueprint "lem:phase-factorization"
  (title := "Phase Factorization for Inner Products")
  (statement := /-- $e^{-i\langle k, x-y \rangle} = e^{-i\langle k, x \rangle} \cdot e^{i\langle k, y \rangle}$. -/)]
lemma phase_factorization (k x y : SpaceTime) :
    Complex.exp (-Complex.I * Complex.ofReal ⟪k, x - y⟫_ℝ) =
    Complex.exp (-Complex.I * Complex.ofReal ⟪k, x⟫_ℝ) * Complex.exp (Complex.I * Complex.ofReal ⟪k, y⟫_ℝ) := by
  rw [inner_sub_right]
  simp only [Complex.ofReal_sub]
  rw [← Complex.exp_add]
  congr 1
  ring

/-- The physics Fourier transform at k. -/
@[blueprint "def:physics-ft"
  (title := "Physics Fourier Transform")
  (statement := /-- $\hat{f}(k) = \int f(x) e^{-i\langle k, x \rangle}\,dx$ (physics convention). -/)]
noncomputable def physicsFT (f : TestFunctionℂ) (k : SpaceTime) : ℂ :=
  ∫ x, f x * Complex.exp (-Complex.I * Complex.ofReal ⟪k, x⟫_ℝ) ∂volume

/-- Norm squared rescaling: ‖c • x‖² = c² ‖x‖² for c ≥ 0. -/
@[blueprint "lem:norm-sq-smul-eq"
  (title := "Norm Squared Under Scalar Multiplication")
  (statement := /-- $\|c \cdot x\|^2 = c^2 \|x\|^2$ for $c \ge 0$. -/)]
lemma norm_sq_smul_eq (c : ℝ) (hc : 0 ≤ c) (x : SpaceTime) :
    ‖c • x‖^2 = c^2 * ‖x‖^2 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
  ring

/-- The physics FT at 2πξ equals the Mathlib FT at ξ. -/
@[blueprint "lem:physics-ft-rescale"
  (title := "Physics FT at 2pi*xi Equals Mathlib FT")
  (statement := /-- $\hat{f}_{\text{phys}}(2\pi\xi) = \mathcal{F}f(\xi)$. -/)]
lemma physicsFT_rescale (f : TestFunctionℂ) (ξ : SpaceTime) :
    physicsFT f ((2 * Real.pi) • ξ) = (SchwartzMap.fourierTransformCLM ℂ f) ξ := by
  simp only [physicsFT, SchwartzMap.fourierTransformCLM_apply]
  show _ = FourierTransform.fourier (⇑f) ξ
  rw [Real.fourier_eq]
  congr 1
  ext x
  simp only [inner_smul_left, mul_comm (f x)]
  congr 1
  rw [Real.fourierChar_apply]
  simp only [starRingEnd_apply, star_trivial]
  rw [real_inner_comm ξ x]
  congr 1
  simp only [mul_neg, Complex.ofReal_neg, neg_mul]
  ring

/-- The integrand transforms correctly under k = 2π•p. -/
@[blueprint "lem:integrand-rescale"
  (title := "Integrand Transform under Momentum Rescaling")
  (statement := /-- The regulated integrand transforms correctly under $k = 2\pi p$. -/)]
lemma integrand_rescale (α : ℝ) (m : ℝ) (f : TestFunctionℂ) (p : SpaceTime) :
    Real.exp (-α * ‖(2 * Real.pi) • p‖^2) * freePropagatorMomentum m ((2 * Real.pi) • p) /
      (2 * Real.pi) ^ STDimension * ‖physicsFT f ((2 * Real.pi) • p)‖^2
    = Real.exp (-α * (2 * Real.pi)^2 * ‖p‖^2) *
      ‖(SchwartzMap.fourierTransformCLM ℂ f) p‖^2 * freePropagatorMomentum_mathlib m p /
      (2 * Real.pi) ^ STDimension := by
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have h2pi_nonneg : (0 : ℝ) ≤ 2 * Real.pi := le_of_lt h2pi_pos
  rw [norm_sq_smul_eq (2 * Real.pi) h2pi_nonneg p]
  rw [freePropagatorMomentum_rescale m p]
  rw [physicsFT_rescale f p]
  have exp_eq : -α * ((2 * Real.pi) ^ 2 * ‖p‖ ^ 2) = -α * (2 * Real.pi) ^ 2 * ‖p‖ ^ 2 := by ring
  rw [exp_eq]
  ring
@[blueprint "lem:change-of-variables-momentum"
  (title := "Change of Variables in Momentum Space")
  (statement := /-- Momentum change of variables converts physics propagator to Mathlib convention. -/)]
lemma change_of_variables_momentum (α : ℝ) (m : ℝ) (f : TestFunctionℂ) :
    ∫ k, Real.exp (-α * ‖k‖^2) * freePropagatorMomentum m k / (2 * Real.pi) ^ STDimension *
        ‖physicsFT f k‖^2 ∂volume
    = ∫ p, Real.exp (-α * (2 * Real.pi)^2 * ‖p‖^2) *
        ‖(SchwartzMap.fourierTransformCLM ℂ f) p‖^2 * freePropagatorMomentum_mathlib m p ∂volume := by
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have h2pi_ne : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt h2pi_pos
  have h2pi_nonneg : (0 : ℝ) ≤ 2 * Real.pi := le_of_lt h2pi_pos
  let g : SpaceTime → ℝ := fun k =>
    Real.exp (-α * ‖k‖^2) * freePropagatorMomentum m k / (2 * Real.pi) ^ STDimension * ‖physicsFT f k‖^2
  have h_finrank : Module.finrank ℝ SpaceTime = STDimension := finrank_euclideanSpace_fin
  have h_subst := MeasureTheory.Measure.integral_comp_smul (μ := volume) g (2 * Real.pi)
  have h_rearranged : ∫ k, g k ∂volume = |2 * Real.pi| ^ STDimension * ∫ p, g ((2 * Real.pi) • p) ∂volume := by
    rw [h_subst, h_finrank]
    rw [abs_inv, abs_pow, smul_eq_mul]
    field_simp
  simp only [g] at h_rearranged
  rw [h_rearranged]
  have h_integrand : ∀ p, g ((2 * Real.pi) • p) =
      Real.exp (-α * (2 * Real.pi)^2 * ‖p‖^2) *
      ‖(SchwartzMap.fourierTransformCLM ℂ f) p‖^2 * freePropagatorMomentum_mathlib m p /
      (2 * Real.pi) ^ STDimension := fun p => integrand_rescale α m f p
  have h_int_eq : ∫ (p : SpaceTime),
      Real.exp (-α * ‖(2 * Real.pi) • p‖ ^ 2) * freePropagatorMomentum m ((2 * Real.pi) • p) /
        (2 * Real.pi) ^ STDimension * ‖physicsFT f ((2 * Real.pi) • p)‖ ^ 2 =
      ∫ p, Real.exp (-α * (2 * Real.pi)^2 * ‖p‖^2) *
        ‖(SchwartzMap.fourierTransformCLM ℂ f) p‖^2 * freePropagatorMomentum_mathlib m p /
        (2 * Real.pi) ^ STDimension := by
    congr 1; ext p; exact h_integrand p
  rw [h_int_eq]
  rw [← MeasureTheory.integral_const_mul]
  congr 1
  ext p
  rw [abs_of_pos h2pi_pos]
  field_simp

/-- After Fubini, the inner k-integral factorizes. -/
@[blueprint "lem:regulated-fubini-factorization"
  (title := "Fubini Factorization of Regulated Covariance")
  (statement := /-- After Fubini, the $k$-integral factorizes into products of Fourier transforms. -/)]
lemma regulated_fubini_factorization (α : ℝ) (hα : 0 < α) (m : ℝ) [Fact (0 < m)] (f : TestFunctionℂ) :
    (∫ x, ∫ y, f x * (freeCovariance_regulated α m x y : ℂ) * (starRingEnd ℂ (f y)) ∂volume ∂volume).re
    = (∫ k, ((Real.exp (-α * ‖k‖^2) * freePropagatorMomentum m k / (2 * Real.pi) ^ STDimension : ℝ) : ℂ) *
        (∫ x, f x * Complex.exp (-Complex.I * Complex.ofReal ⟪k, x⟫_ℝ) ∂volume) *
        (∫ y, starRingEnd ℂ (f y) * Complex.exp (Complex.I * Complex.ofReal ⟪k, y⟫_ℝ) ∂volume) ∂volume).re := by
  have h_int := regulated_triple_integrable α hα m f
  let amplitude : SpaceTime → ℂ := fun k =>
    ((Real.exp (-α * ‖k‖^2) * freePropagatorMomentum m k / (2 * Real.pi) ^ STDimension : ℝ) : ℂ)
  have h_expand : ∀ x y, (freeCovariance_regulated α m x y : ℂ) =
      ∫ k, amplitude k * Complex.exp (-Complex.I * Complex.ofReal ⟪k, x - y⟫_ℝ) := by
    intro x y
    rw [freeCovariance_regulated_eq_complex_integral]
    simp only [fourierNormalization, amplitude]
  have h_lhs_triple : (∫ x, ∫ y, f x * (freeCovariance_regulated α m x y : ℂ) * starRingEnd ℂ (f y)) =
      ∫ x, ∫ y, ∫ k, f x * amplitude k * Complex.exp (-Complex.I * Complex.ofReal ⟪k, x - y⟫_ℝ) *
        starRingEnd ℂ (f y) := by
    congr 1
    ext x
    congr 1
    ext y
    rw [h_expand]
    rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_mul_const]
    congr 1
    ext k
    ring
  let F : SpaceTime → SpaceTime → SpaceTime → ℂ := fun x y k =>
    f x * amplitude k * Complex.exp (-Complex.I * Complex.ofReal ⟪k, x - y⟫_ℝ) * starRingEnd ℂ (f y)
  have h_F_integrable : Integrable (fun p : SpaceTime × SpaceTime × SpaceTime => F p.1 p.2.1 p.2.2)
      (volume.prod (volume.prod volume)) := by
    convert h_int using 1
    ext ⟨x, y, k⟩
    simp only [F, amplitude]
    push_cast
    ring
  have h_fubini : ∫ x, ∫ y, ∫ k, F x y k = ∫ k, ∫ x, ∫ y, F x y k := fubini_triple_reorder h_F_integrable
  have h_factor_xy : ∀ k,
      (∫ x, ∫ y, F x y k) =
      amplitude k * (∫ x, f x * Complex.exp (-Complex.I * Complex.ofReal ⟪k, x⟫_ℝ)) *
        (∫ y, starRingEnd ℂ (f y) * Complex.exp (Complex.I * Complex.ofReal ⟪k, y⟫_ℝ)) := by
    intro k
    simp only [F]
    have h_phase := phase_factorization
    calc ∫ x, ∫ y, f x * amplitude k * Complex.exp (-Complex.I * Complex.ofReal ⟪k, x - y⟫_ℝ) *
          starRingEnd ℂ (f y)
      _ = ∫ x, ∫ y, f x * amplitude k * (Complex.exp (-Complex.I * Complex.ofReal ⟪k, x⟫_ℝ) *
            Complex.exp (Complex.I * Complex.ofReal ⟪k, y⟫_ℝ)) * starRingEnd ℂ (f y) := by
          congr 1; ext x; congr 1; ext y; rw [h_phase]
      _ = ∫ x, ∫ y, (amplitude k * f x * Complex.exp (-Complex.I * Complex.ofReal ⟪k, x⟫_ℝ)) *
            (starRingEnd ℂ (f y) * Complex.exp (Complex.I * Complex.ofReal ⟪k, y⟫_ℝ)) := by
          congr 1; ext x; congr 1; ext y; ring
      _ = (∫ x, amplitude k * f x * Complex.exp (-Complex.I * Complex.ofReal ⟪k, x⟫_ℝ)) *
            (∫ y, starRingEnd ℂ (f y) * Complex.exp (Complex.I * Complex.ofReal ⟪k, y⟫_ℝ)) := by
          let g : SpaceTime → ℂ := fun x => amplitude k * f x * Complex.exp (-Complex.I * Complex.ofReal ⟪k, x⟫_ℝ)
          let h : SpaceTime → ℂ := fun y => starRingEnd ℂ (f y) * Complex.exp (Complex.I * Complex.ofReal ⟪k, y⟫_ℝ)
          have h_eq : ∀ x y, g x * h y = amplitude k * f x * Complex.exp (-Complex.I * Complex.ofReal ⟪k, x⟫_ℝ) *
                (starRingEnd ℂ (f y) * Complex.exp (Complex.I * Complex.ofReal ⟪k, y⟫_ℝ)) := fun x y => rfl
          have h_integrable : Integrable (fun p : SpaceTime × SpaceTime => g p.1 * h p.2) (volume.prod volume) := by
            apply Integrable.mul_prod
            · have h_prod := schwartz_mul_phase_integrable f k
              have h_const := h_prod.const_mul (amplitude k)
              convert h_const using 1
              ext x; ring
            · exact schwartz_conj_mul_phase_integrable f k
          rw [MeasureTheory.integral_integral h_integrable, MeasureTheory.integral_prod_mul g h]
      _ = amplitude k * (∫ x, f x * Complex.exp (-Complex.I * Complex.ofReal ⟪k, x⟫_ℝ)) *
            (∫ y, starRingEnd ℂ (f y) * Complex.exp (Complex.I * Complex.ofReal ⟪k, y⟫_ℝ)) := by
          have heq : ∀ x, amplitude k * f x * Complex.exp (-Complex.I * Complex.ofReal ⟪k, x⟫_ℝ) =
              amplitude k * (f x * Complex.exp (-Complex.I * Complex.ofReal ⟪k, x⟫_ℝ)) := by
            intro x; ring
          simp_rw [heq, MeasureTheory.integral_const_mul]
  rw [h_lhs_triple, h_fubini]
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards with k
  simp only [F]
  exact h_factor_xy k

/-- The x-integral in the factorized form equals the physics FT. -/
@[blueprint "lem:x-integral-eq-physics-ft"
  (title := "X-Integral Equals Physics Fourier Transform")
  (statement := /-- $\int f(x) e^{-i\langle k, x \rangle}\,dx = \hat{f}_{\text{phys}}(k)$. -/)]
lemma x_integral_eq_physicsFT (f : TestFunctionℂ) (k : SpaceTime) :
    ∫ x, f x * Complex.exp (-Complex.I * Complex.ofReal ⟪k, x⟫_ℝ) ∂volume = physicsFT f k := rfl

/-- The y-integral with conjugate equals the conjugate of the physics FT. -/
@[blueprint "lem:y-integral-eq-physics-ft-conj"
  (title := "Y-Integral Equals Conjugate of Physics FT")
  (statement := /-- $\int \overline{f(y)} e^{i\langle k, y \rangle}\,dy = \overline{\hat{f}_{\text{phys}}(k)}$. -/)]
lemma y_integral_eq_physicsFT_conj (f : TestFunctionℂ) (k : SpaceTime) :
    ∫ y, starRingEnd ℂ (f y) * Complex.exp (Complex.I * Complex.ofReal ⟪k, y⟫_ℝ) ∂volume =
    starRingEnd ℂ (physicsFT f k) := by
  unfold physicsFT
  rw [← integral_conj]
  congr 1
  ext y
  simp only [starRingEnd_apply, map_mul]
  congr 1
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal, neg_neg, neg_mul]

/-- The product physicsFT f k * conj(physicsFT f k) = ‖physicsFT f k‖² -/
@[blueprint "lem:physics-ft-mul-conj"
  (title := "Physics FT Norm Squared Formula")
  (statement := /-- $\hat{f}(k) \cdot \overline{\hat{f}(k)} = |\hat{f}(k)|^2$. -/)]
lemma physicsFT_mul_conj (f : TestFunctionℂ) (k : SpaceTime) :
    physicsFT f k * starRingEnd ℂ (physicsFT f k) = (‖physicsFT f k‖^2 : ℂ) := by
  have h := Complex.mul_conj (physicsFT f k)
  simp only [starRingEnd_apply] at h ⊢
  rw [h]
  simp only [Complex.ofReal_pow, Complex.normSq_eq_norm_sq]

/-- The factorized form simplifies to an integral of |physics FT|². -/
@[blueprint "lem:factorized-to-physics-ft-norm-sq"
  (title := "Factorized Form to Physics FT Norm Squared")
  (statement := /-- The factorized integral simplifies to $\int |\hat{f}_{\text{phys}}(k)|^2$ times propagator. -/)]
lemma factorized_to_physicsFT_norm_sq (α : ℝ) (m : ℝ) (f : TestFunctionℂ) :
    (∫ k, ((Real.exp (-α * ‖k‖^2) * freePropagatorMomentum m k / (2 * Real.pi) ^ STDimension : ℝ) : ℂ) *
        (∫ x, f x * Complex.exp (-Complex.I * Complex.ofReal ⟪k, x⟫_ℝ) ∂volume) *
        (∫ y, starRingEnd ℂ (f y) * Complex.exp (Complex.I * Complex.ofReal ⟪k, y⟫_ℝ) ∂volume) ∂volume).re
    = ∫ k, Real.exp (-α * ‖k‖^2) * freePropagatorMomentum m k / (2 * Real.pi) ^ STDimension *
        ‖physicsFT f k‖^2 ∂volume := by
  simp_rw [x_integral_eq_physicsFT, y_integral_eq_physicsFT_conj]
  have h : ∀ k, ((Real.exp (-α * ‖k‖^2) * freePropagatorMomentum m k / (2 * Real.pi) ^ STDimension : ℝ) : ℂ) *
      physicsFT f k * starRingEnd ℂ (physicsFT f k) =
      ((Real.exp (-α * ‖k‖^2) * freePropagatorMomentum m k / (2 * Real.pi) ^ STDimension *
        ‖physicsFT f k‖^2 : ℝ) : ℂ) := by
    intro k
    rw [mul_assoc, physicsFT_mul_conj]
    push_cast
    ring
  simp_rw [h]
  have h_re : ∫ k, ((Real.exp (-α * ‖k‖^2) * freePropagatorMomentum m k / (2 * Real.pi) ^ STDimension *
      ‖physicsFT f k‖^2 : ℝ) : ℂ) ∂volume =
      (((∫ k, Real.exp (-α * ‖k‖^2) * freePropagatorMomentum m k / (2 * Real.pi) ^ STDimension *
        ‖physicsFT f k‖^2 ∂volume : ℝ)) : ℂ) := integral_ofReal
  rw [h_re]
  simp only [Complex.ofReal_re]

/-- **Parseval identity for regulated covariance (proven theorem).**

    This is the fundamental identity relating the position-space covariance integral
    to the momentum-space integral. The regulator exp(-α‖k‖²) ensures absolute convergence.

    The proof proceeds by:
    1. Expanding freeCovariance_regulated as a Fourier integral
    2. Applying Fubini (justified by regulated_triple_integrable)
    3. Factoring the phase using phase_factorization
    4. Recognizing the x and y integrals as Fourier transforms
    5. Accounting for normalization factors via change of variables -/
@[blueprint "thm:parseval-covariance-schwartz-regulated-2"
  (title := "Parseval Identity for Regulated Covariance")]
theorem parseval_covariance_schwartz_regulated (α : ℝ) (hα : 0 < α) (m : ℝ) [Fact (0 < m)] (f : TestFunctionℂ) :
    (∫ x, ∫ y, f x * (freeCovariance_regulated α m x y : ℂ) * (starRingEnd ℂ (f y)) ∂volume ∂volume).re
    = ∫ k, Real.exp (-α * (2 * Real.pi)^2 * ‖k‖^2) * ‖(SchwartzMap.fourierTransformCLM ℂ f) k‖^2 * freePropagatorMomentum_mathlib m k ∂volume := by
  -- Step 1: Apply Fubini and phase factorization
  rw [regulated_fubini_factorization α hα m f]
  -- Step 2: Simplify to integral of |physics FT|²
  rw [factorized_to_physicsFT_norm_sq]
  -- Step 3: Change of variables k = 2πp
  rw [change_of_variables_momentum]

/-- Continuity of the mathlib propagator. -/
@[blueprint "lem:continuous-free-propagator-momentum-mathlib"
  (title := "Continuity of Mathlib Propagator")
  (statement := /-- The Mathlib propagator $\frac{1}{(2\pi)^2\|k\|^2 + m^2}$ is continuous. -/)]
lemma continuous_freePropagatorMomentum_mathlib (m : ℝ) [Fact (0 < m)] :
    Continuous fun k => freePropagatorMomentum_mathlib m k := by
  unfold freePropagatorMomentum_mathlib
  have hdenom_cont : Continuous fun k : SpaceTime => (2 * Real.pi)^2 * ‖k‖^2 + m^2 :=
    Continuous.add (continuous_const.mul (continuous_norm.pow 2)) continuous_const
  refine Continuous.div continuous_const hdenom_cont ?h_ne
  intro k
  have hmpos : 0 < m := Fact.out
  have h1 : 0 ≤ (2 * Real.pi)^2 * ‖k‖^2 := by positivity
  have h2 : 0 < m^2 := sq_pos_of_pos hmpos
  linarith

/-- The integrand ‖f̂(k)‖² * P(k) is integrable for Schwartz f. -/
@[blueprint "lem:integrable-schwartz-propagator-mathlib"
  (title := "Integrability of Schwartz-Propagator Product")]
lemma integrable_schwartz_propagator_mathlib (m : ℝ) [Fact (0 < m)] (f : TestFunctionℂ) :
    Integrable (fun k => ‖(SchwartzMap.fourierTransformCLM ℂ f) k‖^2 *
      freePropagatorMomentum_mathlib m k) volume := by
  -- The Fourier transform squared is integrable (Schwartz → L²)
  have hF_sq_int : Integrable (fun k => ‖(SchwartzMap.fourierTransformCLM ℂ f) k‖^2) volume :=
    schwartz_L2_integrable (SchwartzMap.fourierTransformCLM ℂ f)
  -- The propagator is bounded by 1/m²
  have h_bound : ∀ k, freePropagatorMomentum_mathlib m k ≤ 1 / m^2 := fun k => by
    unfold freePropagatorMomentum_mathlib
    have hmpos : 0 < m := Fact.out
    have hm2pos : 0 < m^2 := sq_pos_of_pos hmpos
    have hden : m^2 ≤ (2 * Real.pi)^2 * ‖k‖^2 + m^2 := by linarith [sq_nonneg (2 * Real.pi * ‖k‖)]
    rw [one_div, one_div]
    exact inv_anti₀ hm2pos hden
  have h_nonneg : ∀ k, 0 ≤ ‖(SchwartzMap.fourierTransformCLM ℂ f) k‖^2 *
      freePropagatorMomentum_mathlib m k := fun k =>
    mul_nonneg (sq_nonneg _) (freePropagatorMomentum_mathlib_nonneg m Fact.out k)
  have h_meas : AEStronglyMeasurable (fun k => ‖(SchwartzMap.fourierTransformCLM ℂ f) k‖^2 *
      freePropagatorMomentum_mathlib m k) volume := by
    apply AEStronglyMeasurable.mul
    · exact (SchwartzMap.continuous _).norm.pow 2 |>.aestronglyMeasurable
    · exact (continuous_freePropagatorMomentum_mathlib m).aestronglyMeasurable
  refine Integrable.mono' (hF_sq_int.const_mul (1 / m^2)) h_meas ?_
  filter_upwards with k
  rw [Real.norm_of_nonneg (h_nonneg k)]
  calc ‖(SchwartzMap.fourierTransformCLM ℂ f) k‖^2 * freePropagatorMomentum_mathlib m k
      ≤ ‖(SchwartzMap.fourierTransformCLM ℂ f) k‖^2 * (1 / m^2) := by
        apply mul_le_mul_of_nonneg_left (h_bound k) (sq_nonneg _)
    _ = 1 / m^2 * ‖(SchwartzMap.fourierTransformCLM ℂ f) k‖^2 := by ring

/-- The unregulated Parseval identity as a limit.
    This theorem explicitly shows that the regulated covariance integral converges
    to the unregulated momentum-space integral as α → 0⁺.

    The proof uses dominated convergence to pass from the regulated identity
    (parseval_covariance_schwartz_regulated) to the unregulated limit. -/
@[blueprint "thm:parseval-covariance-schwartz-correct"
  (title := "Unregulated Parseval Identity as Limit")]
theorem parseval_covariance_schwartz_correct (m : ℝ) [Fact (0 < m)] (f : TestFunctionℂ) :
    Filter.Tendsto
      (fun α => (∫ x, ∫ y, f x * (freeCovariance_regulated α m x y : ℂ) * (starRingEnd ℂ (f y)) ∂volume ∂volume).re)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ k, ‖(SchwartzMap.fourierTransformCLM ℂ f) k‖^2 * freePropagatorMomentum_mathlib m k ∂volume)) := by
  -- Use the regulated Parseval identity to rewrite
  have h_eq : ∀ α > 0, (∫ x, ∫ y, f x * (freeCovariance_regulated α m x y : ℂ) *
      (starRingEnd ℂ (f y)) ∂volume ∂volume).re =
      ∫ k, Real.exp (-α * (2 * Real.pi)^2 * ‖k‖^2) * ‖(SchwartzMap.fourierTransformCLM ℂ f) k‖^2 *
        freePropagatorMomentum_mathlib m k ∂volume := fun α hα =>
    parseval_covariance_schwartz_regulated α hα m f
  -- Define the dominating function
  let g : SpaceTime → ℝ := fun k => ‖(SchwartzMap.fourierTransformCLM ℂ f) k‖^2 *
    freePropagatorMomentum_mathlib m k
  have hg_int : Integrable g volume := integrable_schwartz_propagator_mathlib m f
  -- The key step: show the regulated momentum integral converges to the unregulated one
  have h_tendsto : Filter.Tendsto
      (fun α => ∫ k, Real.exp (-α * (2 * Real.pi)^2 * ‖k‖^2) * ‖(SchwartzMap.fourierTransformCLM ℂ f) k‖^2 *
        freePropagatorMomentum_mathlib m k ∂volume)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ k, g k ∂volume)) := by
    -- Apply dominated convergence
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence g ?_ ?_ hg_int ?_
    · -- 1. Each integrand is AE strongly measurable
      filter_upwards with α
      have h_exp_cont : Continuous fun k : SpaceTime => Real.exp (-α * (2 * Real.pi)^2 * ‖k‖^2) :=
        Real.continuous_exp.comp (continuous_const.mul (continuous_norm.pow 2))
      have h_sq_cont : Continuous fun k : SpaceTime => ‖(SchwartzMap.fourierTransformCLM ℂ f) k‖^2 :=
        (SchwartzMap.continuous _).norm.pow 2
      have h_prod_cont : Continuous fun k : SpaceTime =>
          Real.exp (-α * (2 * Real.pi)^2 * ‖k‖^2) * ‖(SchwartzMap.fourierTransformCLM ℂ f) k‖^2 *
          freePropagatorMomentum_mathlib m k :=
        (h_exp_cont.mul h_sq_cont).mul (continuous_freePropagatorMomentum_mathlib m)
      exact h_prod_cont.aestronglyMeasurable
    · -- 2. Pointwise bound: |exp(-α c ‖k‖²) * g(k)| ≤ g(k) for α > 0
      filter_upwards [self_mem_nhdsWithin] with α (hα : 0 < α)
      filter_upwards with k
      have h_prod_nonneg : 0 ≤ Real.exp (-α * (2 * Real.pi)^2 * ‖k‖^2) *
          ‖(SchwartzMap.fourierTransformCLM ℂ f) k‖^2 * freePropagatorMomentum_mathlib m k :=
        mul_nonneg (mul_nonneg (Real.exp_nonneg _) (sq_nonneg _))
          (freePropagatorMomentum_mathlib_nonneg m Fact.out k)
      rw [Real.norm_of_nonneg h_prod_nonneg]
      have h_exp_le_one : Real.exp (-α * (2 * Real.pi)^2 * ‖k‖^2) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : 0 ≤ α * (2 * Real.pi)^2 * ‖k‖^2 := by positivity
        linarith
      have h_prop_nonneg := freePropagatorMomentum_mathlib_nonneg m Fact.out k
      calc Real.exp (-α * (2 * Real.pi)^2 * ‖k‖^2) * ‖(SchwartzMap.fourierTransformCLM ℂ f) k‖^2 *
            freePropagatorMomentum_mathlib m k
          ≤ 1 * ‖(SchwartzMap.fourierTransformCLM ℂ f) k‖^2 * freePropagatorMomentum_mathlib m k := by
            gcongr
        _ = g k := by simp only [one_mul]; rfl
    · -- 3. Pointwise convergence: exp(-α c ‖k‖²) * g(k) → g(k) as α → 0⁺
      filter_upwards with k
      have h_exp_tendsto : Filter.Tendsto (fun α => Real.exp (-α * (2 * Real.pi)^2 * ‖k‖^2))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
        have h1 : Filter.Tendsto (fun α : ℝ => α) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
          tendsto_nhdsWithin_of_tendsto_nhds Filter.tendsto_id
        have h2 : Filter.Tendsto (fun α : ℝ => -α * (2 * Real.pi)^2 * ‖k‖^2)
            (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
          have : Filter.Tendsto (fun α : ℝ => α * ((2 * Real.pi)^2 * ‖k‖^2))
              (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by simpa using h1.mul_const ((2 * Real.pi)^2 * ‖k‖^2)
          have h3 := this.neg
          simp only [neg_zero] at h3
          refine h3.congr (fun α => ?_)
          ring
        rw [← Real.exp_zero]
        exact Real.continuous_exp.continuousAt.tendsto.comp h2
      have h_tendsto_mul : Filter.Tendsto
          (fun α => Real.exp (-α * (2 * Real.pi)^2 * ‖k‖^2) * g k)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 * g k)) := h_exp_tendsto.mul_const (g k)
      simp only [one_mul] at h_tendsto_mul
      convert h_tendsto_mul using 1
      ext α; simp only [g]; ring
  -- Conclude by transferring along the equality
  refine h_tendsto.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with α hα
  exact (h_eq α hα).symm

/-- **Complex bilinear form convergence (general f, g):** The regulated bilinear covariance
    form converges to the Bessel form as α → 0⁺ for arbitrary complex test functions f, g.

    **Proof outline:** Dominated convergence theorem on the product space:
    1. Pointwise convergence: `freeCovariance_regulated_limit_eq_freeCovariance`
    2. Dominator: exp(m²) × |f(x)| × |C_Bessel(x,y)| × |g(y)| is integrable
    3. Bound: `freeCovariance_regulated_le_const_mul_freeCovariance` gives the uniform bound -/
@[blueprint "thm:bilinear-covariance-regulated-tendsto"
  (title := "Bilinear Covariance Convergence")
  (statement := /-- The regulated bilinear covariance form converges to the Bessel form as $\alpha \to 0^+$. -/)]
theorem bilinear_covariance_regulated_tendstoℂ (m : ℝ) [Fact (0 < m)] (f g : TestFunctionℂ) :
    Filter.Tendsto
      (fun α => ∫ x, ∫ y, f x * (freeCovariance_regulated α m x y : ℂ) * (starRingEnd ℂ (g y)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ x, ∫ y, f x * (freeCovariance m x y : ℂ) * (starRingEnd ℂ (g y)))) := by
  -- **Proof Strategy:** DCT on the product space SpaceTime × SpaceTime.
  have hm : 0 < m := Fact.out
  -- Define the integrands on product space
  let F : ℝ → SpaceTime × SpaceTime → ℂ := fun α p =>
    f p.1 * (freeCovariance_regulated α m p.1 p.2 : ℂ) * starRingEnd ℂ (g p.2)
  let F_limit : SpaceTime × SpaceTime → ℂ := fun p =>
    f p.1 * (freeCovariance m p.1 p.2 : ℂ) * starRingEnd ℂ (g p.2)
  -- Define the dominating function (scaled Bessel form)
  let bound : SpaceTime × SpaceTime → ℝ := fun p =>
    Real.exp (m^2) * ‖f p.1‖ * |freeCovariance m p.1 p.2| * ‖g p.2‖
  -- The bound is integrable (scaling of freeCovarianceℂ_bilinear_integrable)
  have h_bound_int : Integrable bound (volume.prod volume) := by
    -- Use freeCovarianceℂ_bilinear_integrable': f * C * g is integrable
    -- Then Integrable.norm gives ‖f‖ * |C| * ‖g‖ integrable, and const_mul scales by exp(m²)
    have h_int := freeCovarianceℂ_bilinear_integrable' m f g
    -- The norm of f(x) * C(x,y) * g(y) equals ‖f(x)‖ * |C(x,y)| * ‖g(y)‖
    have h_norm_eq : ∀ p : SpaceTime × SpaceTime,
        ‖f p.1 * (freeCovariance m p.1 p.2 : ℂ) * g p.2‖ = ‖f p.1‖ * |freeCovariance m p.1 p.2| * ‖g p.2‖ := by
      intro p
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    -- Rewrite bound in terms of the norm
    have h_bound_eq : bound = fun p => Real.exp (m^2) * ‖f p.1 * (freeCovariance m p.1 p.2 : ℂ) * g p.2‖ := by
      ext p
      simp only [bound, h_norm_eq]
      ring
    rw [h_bound_eq]
    exact h_int.norm.const_mul _
  -- Pointwise convergence for a.e. (x, y) (diagonal has measure zero)
  have h_ae_tendsto : ∀ᵐ p ∂(volume.prod volume),
      Filter.Tendsto (fun α => F α p) (nhdsWithin 0 (Set.Ioi 0)) (nhds (F_limit p)) := by
    -- The diagonal {(x,x)} has measure zero in SpaceTime × SpaceTime (volume.prod volume).
    -- Use ae_prod_iff to reduce to: for a.e. x, for a.e. y, the statement holds.
    -- For any fixed x, the set {x} has measure zero, so for a.e. y, x ≠ y.
    -- Off-diagonal: freeCovariance_regulated_limit_eq_freeCovariance gives pointwise convergence.
    -- For all (x, y) with x ≠ y, we have pointwise convergence.
    -- The diagonal has measure zero, so this is a.e.
    -- Strategy: filter_upwards with a criterion that holds a.e.
    have h_diag_null : (volume.prod volume) {p : SpaceTime × SpaceTime | p.1 = p.2} = 0 := by
      -- Use Fubini: ∫∫ 1_{x=y} dμ(x) dμ(y) = ∫ μ({y}) dμ(x) = ∫ 0 dμ(x) = 0
      have h_meas : MeasurableSet {p : SpaceTime × SpaceTime | p.1 = p.2} := measurableSet_diagonal
      rw [MeasureTheory.Measure.prod_apply h_meas]
      simp only [Set.preimage_setOf_eq]
      -- For each x, the slice {y | x = y} = {x} has measure 0
      have h_slice : ∀ x, (volume : Measure SpaceTime) {y : SpaceTime | x = y} = 0 := by
        intro x
        have h_eq : {y : SpaceTime | x = y} = {x} := by
          ext y; simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, eq_comm]
        rw [h_eq]
        exact MeasureTheory.measure_singleton x
      simp only [h_slice, MeasureTheory.lintegral_zero]
    rw [MeasureTheory.measure_eq_zero_iff_ae_notMem] at h_diag_null
    filter_upwards [h_diag_null] with p hp
    have hxy : p.1 ≠ p.2 := fun h => hp (Set.mem_setOf.mpr h)
    -- Now p.1 ≠ p.2, so we can use freeCovariance_regulated_limit_eq_freeCovariance
    have hC := freeCovariance_regulated_limit_eq_freeCovariance m hm p.1 p.2 hxy
    -- F α p = f x * C_α(x,y) * conj(g y), and we need convergence of this
    simp only [F, F_limit]
    apply Filter.Tendsto.mul
    apply Filter.Tendsto.mul
    · exact tendsto_const_nhds
    · exact Filter.Tendsto.comp Complex.continuous_ofReal.continuousAt hC
    · exact tendsto_const_nhds
  -- Uniform bound: ‖F α p‖ ≤ bound p for α ∈ (0, 1]
  have h_bound : ∀ᶠ α in nhdsWithin 0 (Set.Ioi 0), ∀ᵐ p ∂(volume.prod volume), ‖F α p‖ ≤ bound p := by
    -- For α ∈ (0, 1]: |C_reg(α, x, y)| ≤ exp(m²) × C_Bessel(x, y) for x ≠ y
    -- The set (0, 1] ∩ (0, ∞) = (0, 1] is a neighborhood of 0 in nhdsWithin 0 (Ioi 0)
    have h_mem : Set.Ioo 0 1 ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
      rw [mem_nhdsWithin]
      refine ⟨Set.Iio 1, isOpen_Iio, by norm_num, ?_⟩
      intro x ⟨hx_lt, hx_pos⟩
      exact ⟨hx_pos, hx_lt⟩
    filter_upwards [h_mem] with α ⟨hα_pos, hα_lt1⟩
    -- Now α ∈ (0, 1), need to show a.e. bound
    -- Diagonal has measure zero, use same argument as before
    have h_diag_null : (volume.prod volume) {p : SpaceTime × SpaceTime | p.1 = p.2} = 0 := by
      have h_meas : MeasurableSet {p : SpaceTime × SpaceTime | p.1 = p.2} := measurableSet_diagonal
      rw [MeasureTheory.Measure.prod_apply h_meas]
      simp only [Set.preimage_setOf_eq]
      have h_slice : ∀ x, (volume : Measure SpaceTime) {y : SpaceTime | x = y} = 0 := by
        intro x
        have h_eq : {y : SpaceTime | x = y} = {x} := by
          ext y; simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, eq_comm]
        rw [h_eq]; exact MeasureTheory.measure_singleton x
      simp only [h_slice, MeasureTheory.lintegral_zero]
    rw [MeasureTheory.measure_eq_zero_iff_ae_notMem] at h_diag_null
    filter_upwards [h_diag_null] with p hp
    have hxy : p.1 ≠ p.2 := fun h => hp (Set.mem_setOf.mpr h)
    -- Now use the covariance bound
    have h_cov_bound := freeCovariance_regulated_le_const_mul_freeCovariance m hm p.1 p.2 hxy α hα_pos (le_of_lt hα_lt1)
    -- ‖F α p‖ = ‖f(x)‖ × |C_reg| × ‖g(y)‖
    simp only [F, bound]
    calc ‖f p.1 * (freeCovariance_regulated α m p.1 p.2 : ℂ) * starRingEnd ℂ (g p.2)‖
        = ‖f p.1‖ * |freeCovariance_regulated α m p.1 p.2| * ‖g p.2‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, RCLike.norm_conj]
      _ ≤ ‖f p.1‖ * (Real.exp (m^2) * freeCovariance m p.1 p.2) * ‖g p.2‖ := by
          apply mul_le_mul_of_nonneg_right
          apply mul_le_mul_of_nonneg_left h_cov_bound (norm_nonneg _)
          exact norm_nonneg _
      _ = Real.exp (m^2) * ‖f p.1‖ * freeCovariance m p.1 p.2 * ‖g p.2‖ := by ring
      _ = Real.exp (m^2) * ‖f p.1‖ * |freeCovariance m p.1 p.2| * ‖g p.2‖ := by
          congr 1
          rw [abs_of_nonneg (le_of_lt (freeCovarianceBessel_pos m hm p.1 p.2 hxy))]
  -- Each F α is AE strongly measurable
  have h_meas : ∀ᶠ α in nhdsWithin 0 (Set.Ioi 0), AEStronglyMeasurable (F α) (volume.prod volume) := by
    -- F α p = f(p.1) * C_α(p.1, p.2) * conj(g(p.2))
    -- Each factor is AEStronglyMeasurable, so their product is too
    filter_upwards [self_mem_nhdsWithin] with α hα
    simp only [F]
    -- f ∘ fst is strongly measurable (Schwartz is continuous)
    have hf_meas : StronglyMeasurable (fun p : SpaceTime × SpaceTime => f p.1) :=
      (f.continuous.comp continuous_fst).stronglyMeasurable
    -- g ∘ snd is strongly measurable
    have hg_meas : StronglyMeasurable (fun p : SpaceTime × SpaceTime => starRingEnd ℂ (g p.2)) :=
      ((Complex.continuous_conj.comp g.continuous).comp continuous_snd).stronglyMeasurable
    -- The regulated covariance is AEStronglyMeasurable
    have hC_meas := aestronglyMeasurable_freeCovariance_regulated α (Set.mem_Ioi.mp hα) m hm
    exact (hf_meas.aestronglyMeasurable.mul hC_meas).mul hg_meas.aestronglyMeasurable
  -- Apply DCT on product space
  have h_prod_tendsto := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    bound h_meas h_bound h_bound_int h_ae_tendsto
  -- Convert back to iterated integrals using Fubini
  -- The product integral equals the iterated integral via Fubini theorem
  -- For F α and F_limit, the integrability and Fubini application are standard
  -- We use that ‖conj z‖ = ‖z‖ to transfer integrability from f*C*g to f*C*conj(g)
  --
  -- Technical note: The proof requires showing:
  -- 1. F α is integrable (follows from freeCovariance_regulated_bilinear_integrable + norm equality)
  -- 2. F_limit is integrable (follows from freeCovarianceℂ_bilinear_integrable' + norm equality)
  -- 3. Fubini converts product integrals to iterated integrals
  --
  -- These are routine measure theory facts that follow from ‖conj z‖ = ‖z‖.
  have h_fubini_reg : ∀ᶠ α in nhdsWithin 0 (Set.Ioi 0),
      ∫ p, F α p ∂(volume.prod volume) =
        ∫ x, ∫ y, f x * (freeCovariance_regulated α m x y : ℂ) * starRingEnd ℂ (g y) := by
    filter_upwards [self_mem_nhdsWithin] with α hα
    -- Integrability of F α follows from the non-conjugate version (norms are equal)
    have h_int := freeCovariance_regulated_bilinear_integrable α (Set.mem_Ioi.mp hα) m f g
    -- The function F α differs from f*C*g only by conjugation of g, which preserves norms
    -- Transfer integrability using norm equality ‖conj z‖ = ‖z‖
    have h_norm_eq : ∀ p : SpaceTime × SpaceTime,
        ‖f p.1 * (freeCovariance_regulated α m p.1 p.2 : ℂ) * g p.2‖ = ‖F α p‖ := fun p => by
      simp only [F, norm_mul, RCLike.norm_conj]
    have hF_meas : AEStronglyMeasurable (F α) (volume.prod volume) := by
      simp only [F]
      have hf_meas : StronglyMeasurable (fun p : SpaceTime × SpaceTime => f p.1) :=
        (f.continuous.comp continuous_fst).stronglyMeasurable
      have hg_meas : StronglyMeasurable (fun p : SpaceTime × SpaceTime => starRingEnd ℂ (g p.2)) :=
        ((Complex.continuous_conj.comp g.continuous).comp continuous_snd).stronglyMeasurable
      have hC_meas := aestronglyMeasurable_freeCovariance_regulated α (Set.mem_Ioi.mp hα) m hm
      exact (hf_meas.aestronglyMeasurable.mul hC_meas).mul hg_meas.aestronglyMeasurable
    have h_int_F : Integrable (F α) (volume.prod volume) :=
      h_int.congr' hF_meas (Filter.Eventually.of_forall h_norm_eq)
    -- Apply Fubini: ∫ F α ∂(prod) = ∫∫ F α (x,y) dy dx
    exact MeasureTheory.integral_prod (F α) h_int_F
  have h_fubini_limit : ∫ p, F_limit p ∂(volume.prod volume) =
      ∫ x, ∫ y, f x * (freeCovariance m x y : ℂ) * starRingEnd ℂ (g y) := by
    -- Same structure as h_fubini_reg: F_limit is integrable and Fubini applies
    have h_int := freeCovarianceℂ_bilinear_integrable' m f g
    -- Transfer integrability using norm equality ‖conj z‖ = ‖z‖
    have h_norm_eq : ∀ p : SpaceTime × SpaceTime,
        ‖f p.1 * (freeCovariance m p.1 p.2 : ℂ) * g p.2‖ = ‖F_limit p‖ := fun p => by
      simp only [F_limit, norm_mul, RCLike.norm_conj]
    have hF_meas : AEStronglyMeasurable F_limit (volume.prod volume) := by
      simp only [F_limit]
      have hf_meas : StronglyMeasurable (fun p : SpaceTime × SpaceTime => f p.1) :=
        (f.continuous.comp continuous_fst).stronglyMeasurable
      have hg_meas : StronglyMeasurable (fun p : SpaceTime × SpaceTime => starRingEnd ℂ (g p.2)) :=
        ((Complex.continuous_conj.comp g.continuous).comp continuous_snd).stronglyMeasurable
      have hC_meas := aestronglyMeasurable_freeCovariance m
      exact (hf_meas.aestronglyMeasurable.mul hC_meas).mul hg_meas.aestronglyMeasurable
    have h_int_F : Integrable F_limit (volume.prod volume) :=
      h_int.congr' hF_meas (Filter.Eventually.of_forall h_norm_eq)
    -- Apply Fubini: ∫ F_limit ∂(prod) = ∫∫ F_limit (x,y) dy dx
    exact MeasureTheory.integral_prod F_limit h_int_F
  -- Combine: use Filter.Tendsto.congr
  rw [← h_fubini_limit]
  exact h_prod_tendsto.congr' h_fubini_reg

/-- **Complex convergence for the symmetric case (f = f):**
The regulated bilinear form converges to the Bessel form in ℂ when both test functions are the same.

This is a direct corollary of `bilinear_covariance_regulated_tendstoℂ` with g = f. -/
@[blueprint "thm:bilinear-covariance-regulated-tendsto-self"
  (title := "Bilinear Covariance Convergence (Symmetric Case)")
  (statement := /-- The regulated bilinear form with $f = g$ converges to the Bessel form. -/)]
theorem bilinear_covariance_regulated_tendsto_self (m : ℝ) [Fact (0 < m)] (f : TestFunctionℂ) :
    Filter.Tendsto
      (fun α => ∫ x, ∫ y, f x * (freeCovariance_regulated α m x y : ℂ) * (starRingEnd ℂ (f y)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ x, ∫ y, f x * (freeCovariance m x y : ℂ) * (starRingEnd ℂ (f y)))) :=
  bilinear_covariance_regulated_tendstoℂ m f f

end ParsevalCovariance

/-! ## Global Definitions

The following definitions are placed outside the section to ensure they are
accessible globally without namespace qualification. -/

section GlobalBilinearDefs

open MeasureTheory Complex Real
open scoped InnerProductSpace

/-- Bilinear extension of the covariance for complex test functions.
    This is the distributional formulation: the double integral is well-defined
    for Schwartz test functions due to the L¹ integrability of the Bessel kernel. -/
@[blueprint "def:free-covariance-3"
  (title := "Complex Bilinear Covariance Form")]
noncomputable def freeCovarianceℂ_bilinear (m : ℝ) (f g : TestFunctionℂ) : ℂ :=
  ∫ x, ∫ y, (f x) * (freeCovariance m x y) * (g y)

end GlobalBilinearDefs
