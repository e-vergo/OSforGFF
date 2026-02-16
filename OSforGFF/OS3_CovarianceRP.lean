/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/

import OSforGFF.Basic
import OSforGFF.PositiveTimeTestFunction_real
import OSforGFF.FourierTransforms
import OSforGFF.CovarianceMomentum
import OSforGFF.OS3_MixedRep
import OSforGFF.OS3_MixedRepInfra
import OSforGFF.Parseval
import OSforGFF.Covariance
import Dress
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Proof of Reflection Positivity for the Bessel Covariance

This file contains the complete proof of reflection positivity (OS3) for the free scalar field
using the unregulated Bessel covariance kernel.

## Main Results

* `freeCovariance_reflection_positive_bilinear` : For any test function f supported on
  positive time, the reflection positivity inner product is non-negative:
  ⟨Θf, f⟩_C = ∫∫ f*(Θx) C(x,y) f(y) dx dy ≥ 0

* `freeCovariance_reflection_positive_real` : Real-valued version of the reflection positivity
  theorem for real test functions.

## Proof Structure (RPProof Namespace)

The direct proof proceeds in 8 parts without spatial regulator or limit arguments:

1. Define `rpInnerProduct m f = ∫∫ conj(f(Θx)) C(x,y) f(y)`
2. Change of variables → `∫∫ conj(f(x)) C(Θx,y) f(y)`
3. Mixed representation → `(1/(2(2π)^{d-1})) ∫_{k_sp} ∫∫ (1/ω) exp(-ω|t|) ...`
4. Factorization using positive-time support: `exp(-ω|t|) = exp(-ω(x₀+y₀))`
5. Result: `(1/(2(2π)^{d-1})) ∫_{k_sp} (1/ω) |F_ω(-k_sp)|²`
6. Non-negativity of integrand and prefactor → `Re(...) ≥ 0`

**Key insight:** The mixed representation from `bessel_bilinear_eq_mixed_representation`
already contains the factorizable form `(1/ω) exp(-ω|t|)`. For positive-time test
functions, `|t| = |-x₀-y₀| = x₀+y₀`, so the exponential factorizes directly.
No Lorentzian inversion (converting back to k₀ integral) is needed.

## Organization

- **QFT namespace**: Public API definitions and main theorems
- **QFT.RPProof namespace**: Direct proof machinery (self-contained, 8 parts)
- **Bridge section**: Connects RPProof to QFT API

The bridge lemma `rpInnerProduct_eq_rpProof` is `rfl` since both use the same
Bessel kernel definition.
-/

namespace QFT

open MeasureTheory Complex Real Filter
open scoped ENNReal NNReal Topology ComplexConjugate Real InnerProductSpace BigOperators

/-! ## Reflection Positivity Inner Product

The reflection positivity inner product is defined using the distributional bilinear form
composed with the star operation. This is the mathematically correct formulation that
avoids non-convergent pointwise integrals. -/

/-- The reflection positivity inner product using the distributional bilinear form:
    ⟨Θf, f⟩_C = freeCovarianceℂ_bilinear m (star f) f
             = ∫∫ conj(f(Θx)) * C(x,y) * f(y) dx dy

    The star operation on TestFunctionℂ is defined as:
    (star f)(x) = conj(f(Θx))  (time reflection composed with conjugation)

    This is the distributional formulation that is mathematically well-defined
    for Schwartz test functions. -/
@[blueprint "def:rp-inner-product"
  (title := "Reflection Positivity Inner Product")
  (statement := /-- $\langle f, f \rangle_{\text{RP}} = C_{\text{bilinear}}(f^*, f)$: the RP inner product for complex test functions. -/)
]
noncomputable def rpInnerProduct (m : ℝ) (f : TestFunctionℂ) : ℂ :=
  freeCovarianceℂ_bilinear m (star f) f

/-! ## Direct Proof of Reflection Positivity

The following namespace contains the complete self-contained proof of reflection positivity
using the direct momentum representation approach. -/

namespace RPProof

open MeasureTheory Complex Real
open scoped ComplexConjugate

/-! ## Part 1: Core Definitions -/
@[blueprint "def:time-reflection-2"
  (title := "Euclidean Time Reflection")
  (statement := /-- $\Theta(x_0, \vec{x}) = (-x_0, \vec{x})$: Euclidean time reflection. -/)
]
noncomputable def timeReflection (x : SpaceTime) : SpaceTime :=
  (WithLp.equiv 2 _).symm (Function.update x.ofLp 0 (-x.ofLp 0))
@[blueprint "lem:time-reflection-involutive"
  (title := "Time Reflection Involutive")
  (statement := /-- $\Theta^2 = \mathrm{id}$: time reflection is an involution. -/)
]
lemma timeReflection_involutive : Function.Involutive timeReflection := by
  intro x
  simp only [timeReflection]
  apply PiLp.ext
  intro i
  simp only [WithLp.equiv_symm_apply]
  by_cases hi : i = 0 <;> simp [hi, Function.update]

@[blueprint "def:spatial-dot"
  (title := "Spatial Dot Product")
  (statement := /-- $\vec{k} \cdot \vec{x} = \sum_i k_i x_i$. -/)
]
noncomputable def spatialDot (k_spatial x_spatial : SpatialCoords) : ℝ :=
  ∑ i, k_spatial i * x_spatial i
@[blueprint "def:free-covariance-2"
  (title := "Complex Free Covariance Bilinear (Local)")
  (statement := /-- $C(f,g) = \int\!\!\int f(x)\, C(x,y)\, g(y)\, dx\, dy$ for complex test functions. -/)
]
noncomputable def freeCovarianceℂ_bilinear (m : ℝ) (f g : TestFunctionℂ) : ℂ :=
  ∫ x, ∫ y, (f x) * (_root_.freeCovariance m x y) * (g y)
@[blueprint "def:weighted-laplace-fourier"
  (title := "Weighted Laplace-Fourier Transform")
  (statement := /-- $\tilde{f}(\vec{k}) = \int f(x)\, e^{-\omega x_0}\, e^{-i\vec{k}\cdot\vec{x}}\, dx$ with $\omega = \sqrt{\|\vec{k}\|^2 + m^2}$. -/)
]
noncomputable def weightedLaplaceFourier (m : ℝ) (f : TestFunctionℂ) (k_sp : SpatialCoords) : ℂ :=
  let ω := Real.sqrt (‖k_sp‖^2 + m^2)
  ∫ x : SpaceTime, f x * Complex.exp (-ω * x 0) *
    Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x))
@[blueprint "def:rp-inner-product-2"
  (title := "RP Inner Product (Local Copy)")
  (statement := /-- Local copy of $\langle f, f \rangle_{\text{RP}} = C(f^*, f)$ for the direct proof namespace. -/)
]
noncomputable def rpInnerProduct (m : ℝ) (f : TestFunctionℂ) : ℂ :=
  freeCovarianceℂ_bilinear m (star f) f

/-! ## Part 2: Change of Variables -/

variable (m : ℝ) [Fact (0 < m)]

@[blueprint "lem:star-apply"
  (title := "Star Function Evaluation")
  (statement := /-- $(f^*)(x) = \overline{f(\Theta x)}$: star combines conjugation with time reflection. -/)
]
lemma star_apply (f : TestFunctionℂ) (x : SpaceTime) :
    (star f) x = starRingEnd ℂ (f (timeReflection x)) := rfl

omit [Fact (0 < m)] in
@[blueprint "thm:rp-inner-product-eq-bessel-reflected"
  (title := "RP Inner Product via Reflected Bessel Kernel")
  (statement := /-- $\langle f, f \rangle_{\text{RP}} = \int\!\!\int \overline{f(x)}\, C(\Theta x, y)\, f(y)\, dx\, dy$: change of variables. -/)
]
theorem rpInnerProduct_eq_bessel_reflected (f : TestFunctionℂ) :
    rpInnerProduct m f =
      ∫ x : SpaceTime, ∫ y : SpaceTime,
        (starRingEnd ℂ (f x)) * (_root_.freeCovariance m (timeReflection x) y : ℂ) * f y := by
  unfold rpInnerProduct freeCovarianceℂ_bilinear
  have h_star : ∀ x, (star f) x = starRingEnd ℂ (f (timeReflection x)) := star_apply f
  simp_rw [h_star]
  have h_mp := QFT.timeReflection_measurePreserving
  have h_inv : ∀ x, timeReflection (timeReflection x) = x := fun x => by
    simp [timeReflection, Function.update]
  let G := fun x => ∫ y, (starRingEnd ℂ (f (timeReflection x))) *
      (_root_.freeCovariance m x y : ℂ) * f y
  have h_cov : ∫ x, G x = ∫ x, G (timeReflection x) :=
    (h_mp.integral_comp QFT.timeReflectionLE.toMeasurableEquiv.measurableEmbedding G).symm
  conv_lhs => rw [h_cov]
  congr 1; ext x; simp only [G]; congr 1; ext y; rw [h_inv x]

/-! ## Part 3: Mixed Representation (Direct Approach) -/

/-- The mixed representation from the Schwinger pathway.
    This is more direct than the k₀-inside form for proving reflection positivity,
    because `(1/ω) exp(-ω|t|)` already factorizes for positive-time test functions. -/
@[blueprint "thm:mixed-representation"
  (title := "Mixed Representation of RP Inner Product")
  (keyDeclaration := true)
  (statement := /-- $\langle f, f \rangle_{\text{RP}} = \frac{1}{2(2\pi)^{d-1}} \int_{\vec{k}} \frac{1}{\omega} e^{-\omega|t|} \cdot (\text{phase})$: the mixed position-momentum representation. -/)]
theorem mixed_representation (f : TestFunctionℂ)
    (hf_supp : ∀ x, x 0 ≤ 0 → f x = 0) :
    rpInnerProduct m f =
    (1 / (2 * (2 * Real.pi) ^ (STDimension - 1)) : ℝ) *
    ∫ k_sp : SpatialCoords, ∫ x : SpaceTime, ∫ y : SpaceTime,
      let ω := Real.sqrt (‖k_sp‖^2 + m^2)
      (starRingEnd ℂ (f x)) * f y *
      (1 / ω : ℝ) *
      Complex.exp (-(|-(x 0) - y 0| : ℝ) * ω) *
      Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) := by
  rw [rpInnerProduct_eq_bessel_reflected]
  exact bessel_bilinear_eq_mixed_representation m f hf_supp

/-! ## Part 4: Key Lemmas -/
@[blueprint "lem:energy-pos"
  (title := "Energy Positivity")
  (statement := /-- $\omega(\vec{k}) = \sqrt{\|\vec{k}\|^2 + m^2} > 0$ for $m > 0$. -/)
]
lemma energy_pos (k_sp : SpatialCoords) : 0 < Real.sqrt (‖k_sp‖^2 + m^2) := by
  apply Real.sqrt_pos_of_pos
  have hm : 0 < m := Fact.out
  nlinarith [sq_nonneg ‖k_sp‖]

/-! ## Part 5: Factorization Helpers -/

omit [Fact (0 < m)] in
@[blueprint "lem:abs-neg-sum-nonneg"
  (title := "Absolute Value of Negated Sum")
  (statement := /-- $|-x_0 - y_0| = x_0 + y_0$ for $x_0, y_0 \geq 0$. -/)
]
lemma abs_neg_sum_nonneg (x0 y0 : ℝ) (hx : 0 ≤ x0) (hy : 0 ≤ y0) :
    |-x0 - y0| = x0 + y0 := by
  rw [abs_of_nonpos (by linarith : -x0 - y0 ≤ 0)]; ring

omit [Fact (0 < m)] in
@[blueprint "lem:spatial-dot-sub"
  (title := "Spatial Dot Subtraction")
  (statement := /-- $\vec{k} \cdot (\vec{x} - \vec{y}) = \vec{k} \cdot \vec{x} - \vec{k} \cdot \vec{y}$. -/)
]
lemma spatialDot_sub (k_sp x_sp y_sp : SpatialCoords) :
    spatialDot k_sp (x_sp - y_sp) = spatialDot k_sp x_sp - spatialDot k_sp y_sp := by
  simp only [spatialDot]
  have h : ∀ i, k_sp i * (x_sp - y_sp) i = k_sp i * x_sp i - k_sp i * y_sp i := by
    intro i; simp only [PiLp.sub_apply, mul_sub]
  simp_rw [h, Finset.sum_sub_distrib]

omit [Fact (0 < m)] in
@[blueprint "lem:exp-spatial-phase-factor"
  (title := "Spatial Phase Factorization")
  (statement := /-- $e^{-i\vec{k}\cdot(\vec{x}-\vec{y})} = e^{-i\vec{k}\cdot\vec{x}} \cdot e^{i\vec{k}\cdot\vec{y}}$. -/)
]
lemma exp_spatial_phase_factor (k_sp : SpatialCoords) (x_sp y_sp : SpatialCoords) :
    Complex.exp (-Complex.I * spatialDot k_sp (x_sp - y_sp)) =
    Complex.exp (-Complex.I * spatialDot k_sp x_sp) *
    Complex.exp (Complex.I * spatialDot k_sp y_sp) := by
  rw [← Complex.exp_add, spatialDot_sub]; congr 1; push_cast; ring
@[blueprint "def:x-integral-factor"
  (title := "X-Integral Factor")
  (statement := /-- $X(\vec{k}) = \int \overline{f(x)}\, e^{-\omega x_0}\, e^{-i\vec{k}\cdot\vec{x}}\, dx$. -/)
]
noncomputable def xIntegralFactor (f : TestFunctionℂ) (ω : ℝ) (k_sp : SpatialCoords) : ℂ :=
  ∫ x : SpaceTime, (starRingEnd ℂ (f x)) *
    Complex.exp (-(ω * x 0)) * Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x))

@[blueprint "def:y-integral-factor"
  (title := "Y-Integral Factor")
  (statement := /-- $Y(\vec{k}) = \int f(y)\, e^{-\omega y_0}\, e^{i\vec{k}\cdot\vec{y}}\, dy$. -/)
]
noncomputable def yIntegralFactor (f : TestFunctionℂ) (ω : ℝ) (k_sp : SpatialCoords) : ℂ :=
  ∫ y : SpaceTime, f y *
    Complex.exp (-(ω * y 0)) * Complex.exp (Complex.I * spatialDot k_sp (spatialPart y))

omit [Fact (0 < m)] in
@[blueprint "lem:norm-neg-eq"
  (title := "Norm Negation Invariance")
  (statement := /-- $\|-\vec{k}\| = \|\vec{k}\|$. -/)
]
lemma norm_neg_eq (k_sp : SpatialCoords) : ‖-k_sp‖ = ‖k_sp‖ := norm_neg k_sp

omit [Fact (0 < m)] in
@[blueprint "lem:spatial-dot-neg-left"
  (title := "Spatial Dot Negation")
  (statement := /-- $(-\vec{k}) \cdot \vec{x} = -(\vec{k} \cdot \vec{x})$. -/)
]
lemma spatialDot_neg_left (k_sp x_sp : SpatialCoords) :
    spatialDot (-k_sp) x_sp = -spatialDot k_sp x_sp := by
  simp only [spatialDot]
  have h : ∀ i, (-k_sp) i * x_sp i = -(k_sp i * x_sp i) := by
    intro i; simp only [PiLp.neg_apply, neg_mul]
  simp_rw [h, Finset.sum_neg_distrib]

omit [Fact (0 < m)] in
@[blueprint "lem:x-integral-factor-eq-conj-neg"
  (title := "X Factor Equals Conjugate of Neg Transform")
  (statement := /-- $X(\vec{k}) = \overline{\tilde{f}(-\vec{k})}$ for positive-time $f$. -/)
]
lemma xIntegralFactor_eq_conj_neg (f : TestFunctionℂ) (k_sp : SpatialCoords)
    (_hf_support : ∀ x : SpaceTime, x 0 < 0 → f x = 0) :
    xIntegralFactor f (Real.sqrt (‖k_sp‖^2 + m^2)) k_sp =
    starRingEnd ℂ (weightedLaplaceFourier m f (-k_sp)) := by
  simp only [xIntegralFactor, weightedLaplaceFourier]
  have h_norm : ‖-k_sp‖ = ‖k_sp‖ := norm_neg_eq k_sp
  have h_dot : ∀ x_sp, spatialDot (-k_sp) x_sp = -spatialDot k_sp x_sp := spatialDot_neg_left k_sp
  simp only [h_norm, h_dot, Complex.ofReal_neg]
  have h_exp_neg : ∀ (a : ℝ), Complex.exp (-Complex.I * -↑a) = Complex.exp (Complex.I * ↑a) := by
    intro a; congr 1; ring
  simp only [h_exp_neg]
  rw [← integral_conj]
  congr 1; ext x; simp only [map_mul]
  have h_star_exp : ∀ z : ℂ, starRingEnd ℂ (Complex.exp z) = Complex.exp (starRingEnd ℂ z) := by
    intro z
    have h1 : starRingEnd ℂ (Complex.exp z) = conj (Complex.exp z) := rfl
    have h2 : starRingEnd ℂ z = conj z := rfl
    rw [h1, h2, ← Complex.exp_conj]
  simp only [h_star_exp]
  congr 1
  · simp only [map_neg, map_mul, Complex.conj_ofReal]; congr 1; ring_nf
  · simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]

omit [Fact (0 < m)] in
@[blueprint "lem:y-integral-factor-eq-neg"
  (title := "Y Factor Equals Neg Transform")
  (statement := /-- $Y(\vec{k}) = \tilde{f}(-\vec{k})$. -/)
]
lemma yIntegralFactor_eq_neg (f : TestFunctionℂ) (k_sp : SpatialCoords) :
    yIntegralFactor f (Real.sqrt (‖k_sp‖^2 + m^2)) k_sp =
    weightedLaplaceFourier m f (-k_sp) := by
  simp only [yIntegralFactor, weightedLaplaceFourier]
  have h_norm : ‖-k_sp‖ = ‖k_sp‖ := norm_neg_eq k_sp
  have h_dot : ∀ x_sp, spatialDot (-k_sp) x_sp = -spatialDot k_sp x_sp := spatialDot_neg_left k_sp
  simp only [h_norm]; congr 1; ext x; simp only [h_dot, Complex.ofReal_neg]
  congr 1
  · congr 1; ring_nf
  · congr 1; simp only [neg_mul_neg]

/-! ## Part 6: Factorization to Squared Norm (Direct Approach) -/

/-- **Direct factorization** from the mixed representation.

    For positive-time test functions, the mixed representation integrand
    `(1/ω) exp(-ω|t|) exp(-ik_sp·r)` factorizes directly because:
    - `|t| = |-x₀-y₀| = x₀+y₀` when `x₀, y₀ ≥ 0`
    - `exp(-ω(x₀+y₀)) = exp(-ωx₀) · exp(-ωy₀)`
    - `exp(-ik_sp·r) = exp(-ik_sp·x_sp) · exp(+ik_sp·y_sp)`

    This avoids the round-trip through k₀ space that the old proof used. -/
@[blueprint "thm:factorization-to-squared-norm-direct"
  (title := "Factorization to Squared Norm")
  (statement := /-- The integrand factors as $X(\vec{k}) \cdot Y(\vec{k}) = (1/\omega) |\tilde{f}(-\vec{k})|^2$ for positive-time $f$. -/)
]
theorem factorization_to_squared_norm_direct (f : TestFunctionℂ) (k_sp : SpatialCoords)
    (hf_support : ∀ x : SpaceTime, x 0 < 0 → f x = 0) :
    let ω := Real.sqrt (‖k_sp‖^2 + m^2)
    ∫ x : SpaceTime, ∫ y : SpaceTime,
      (starRingEnd ℂ (f x)) * f y *
      (1 / ω : ℝ) *
      Complex.exp (-(|-(x 0) - y 0| : ℝ) * ω) *
      Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) =
    ((1 / ω * Complex.normSq (weightedLaplaceFourier m f (-k_sp)) : ℝ) : ℂ) := by
  intro ω
  have hω : 0 < ω := energy_pos m k_sp
  -- Step 1: Rearrange using positive-time support
  -- For x₀, y₀ ≥ 0: |−x₀−y₀| = x₀+y₀, so exp(-ω|t|) = exp(-ωx₀)·exp(-ωy₀)
  have h_rearrange : ∀ x y : SpaceTime,
      (starRingEnd ℂ (f x)) * f y *
        (1 / ω : ℝ) *
        Complex.exp (-(|-(x 0) - y 0| : ℝ) * ω) *
        Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x - spatialPart y)) =
      ((1 / ω : ℝ) : ℂ) *
        ((starRingEnd ℂ (f x)) * Complex.exp (-ω * (x 0)) *
          Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x))) *
        (f y * Complex.exp (-ω * (y 0)) *
          Complex.exp (Complex.I * spatialDot k_sp (spatialPart y))) := by
    intro x y
    by_cases hx : x 0 < 0
    · simp only [hf_support x hx, map_zero, zero_mul, mul_zero]
    · by_cases hy : y 0 < 0
      · simp only [hf_support y hy, mul_zero, zero_mul]
      · push_neg at hx hy
        have h_abs : |-(x 0) - y 0| = x 0 + y 0 := abs_neg_sum_nonneg (x 0) (y 0) hx hy
        rw [h_abs]
        -- Normalize casts: ↑(a + b) → ↑a + ↑b
        simp only [Complex.ofReal_add]
        -- The mixed rep has exp(-(↑x₀ + ↑y₀) * ω), need to match exp(-ω * x₀) * exp(-ω * y₀)
        have h_exp_factor : Complex.exp (-(↑(x 0) + ↑(y 0)) * ↑ω) =
            Complex.exp (-↑ω * ↑(x 0)) * Complex.exp (-↑ω * ↑(y 0)) := by
          rw [← Complex.exp_add]; congr 1; ring
        rw [exp_spatial_phase_factor k_sp (spatialPart x) (spatialPart y)]
        rw [h_exp_factor]; ring
  simp_rw [h_rearrange]
  -- Step 2: Factor the double integral via Fubini
  let fx := fun x : SpaceTime =>
    (starRingEnd ℂ (f x)) * Complex.exp (-(ω * x 0)) *
      Complex.exp (-Complex.I * spatialDot k_sp (spatialPart x))
  let gy := fun y : SpaceTime =>
    f y * Complex.exp (-(ω * y 0)) *
      Complex.exp (Complex.I * spatialDot k_sp (spatialPart y))
  have hfx_eq : ∫ x : SpaceTime, fx x = xIntegralFactor f ω k_sp := rfl
  have hgy_eq : ∫ y : SpaceTime, gy y = yIntegralFactor f ω k_sp := rfl
  have hX : xIntegralFactor f ω k_sp = starRingEnd ℂ (weightedLaplaceFourier m f (-k_sp)) :=
    xIntegralFactor_eq_conj_neg m f k_sp hf_support
  have hY : yIntegralFactor f ω k_sp = weightedLaplaceFourier m f (-k_sp) :=
    yIntegralFactor_eq_neg m f k_sp
  have h_normSq : ∀ A : ℂ, (starRingEnd ℂ A) * A = (Complex.normSq A : ℂ) := by
    intro A; rw [← Complex.normSq_eq_conj_mul_self]
  have h_fubini : ∫ x : SpaceTime, ∫ y : SpaceTime, (↑(1 / ω) : ℂ) * fx x * gy y =
      (↑(1 / ω) : ℂ) * (∫ x, fx x) * (∫ y, gy y) := by
    have h_pull_const : ∀ (c : ℂ) (g : SpaceTime → ℂ),
        ∫ z : SpaceTime, c * g z = c * ∫ z, g z := by
      intro c g; simp_rw [← smul_eq_mul]; exact MeasureTheory.integral_smul c g
    have h_inner : ∀ x, ∫ y : SpaceTime, (↑(1 / ω) : ℂ) * fx x * gy y =
        (↑(1 / ω) * fx x) * ∫ y, gy y := fun x => h_pull_const (↑(1 / ω) * fx x) gy
    simp_rw [h_inner]
    have h_comm : ∀ x, (↑(1 / ω) * fx x) * ∫ y, gy y = (∫ y, gy y) * (↑(1 / ω) * fx x) := by
      intro x; ring
    simp_rw [h_comm]; rw [h_pull_const, h_pull_const]; ring
  have h_integrand_eq : ∀ x y : SpaceTime,
      (↑(1 / ω) : ℂ) *
        ((starRingEnd ℂ) (f x) * Complex.exp (-↑ω * ↑(x 0)) *
          Complex.exp (-Complex.I * ↑(spatialDot k_sp (spatialPart x)))) *
        (f y * Complex.exp (-↑ω * ↑(y 0)) *
          Complex.exp (Complex.I * ↑(spatialDot k_sp (spatialPart y)))) =
      (↑(1 / ω) : ℂ) * fx x * gy y := by
    intro x y; simp only [fx, gy, neg_mul]
  simp_rw [h_integrand_eq]
  calc ∫ x : SpaceTime, ∫ y : SpaceTime, (↑(1 / ω) : ℂ) * fx x * gy y
      = (↑(1 / ω) : ℂ) * (∫ x, fx x) * (∫ y, gy y) := h_fubini
    _ = (↑(1 / ω) : ℂ) * xIntegralFactor f ω k_sp * yIntegralFactor f ω k_sp := by
        rw [hfx_eq, hgy_eq]
    _ = (↑(1 / ω) : ℂ) * starRingEnd ℂ (weightedLaplaceFourier m f (-k_sp)) *
          weightedLaplaceFourier m f (-k_sp) := by rw [hX, hY]
    _ = (↑(1 / ω) : ℂ) * (starRingEnd ℂ (weightedLaplaceFourier m f (-k_sp)) *
          weightedLaplaceFourier m f (-k_sp)) := by ring
    _ = (↑(1 / ω) : ℂ) * (Complex.normSq (weightedLaplaceFourier m f (-k_sp)) : ℂ) := by
        rw [h_normSq]
    _ = ↑(1 / ω * Complex.normSq (weightedLaplaceFourier m f (-k_sp))) := by
        simp only [Complex.ofReal_mul]

/-! ## Part 7: Final Representation -/

/-- The RP inner product equals `(1/(2(2π)^{d-1})) ∫_{k_sp} (1/ω) |F_ω(-k_sp)|²`.

    This follows directly from the mixed representation + factorization,
    without going through the k₀-inside form. -/
@[blueprint "thm:rp-equals-squared-norm-integral"
  (title := "RP Equals Squared Norm Integral")
  (statement := /-- $\langle f, f \rangle_{\text{RP}} = \frac{1}{2(2\pi)^{d-1}} \int_{\vec{k}} \frac{|\tilde{f}(-\vec{k})|^2}{\omega(\vec{k})}\, d\vec{k}$. -/)
]
theorem rp_equals_squared_norm_integral (f : TestFunctionℂ)
    (hf_supp : ∀ x : SpaceTime, x 0 ≤ 0 → f x = 0) :
    rpInnerProduct m f =
    (1 / (2 * (2 * Real.pi) ^ (STDimension - 1)) : ℝ) *
    ∫ k_sp : SpatialCoords,
      ((1 / Real.sqrt (‖k_sp‖^2 + m^2) *
        Complex.normSq (weightedLaplaceFourier m f (-k_sp)) : ℝ) : ℂ) := by
  have hf_support : ∀ x : SpaceTime, x 0 < 0 → f x = 0 := fun x hx =>
    hf_supp x (le_of_lt hx)
  rw [mixed_representation m f hf_supp]
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards with k_sp
  exact factorization_to_squared_norm_direct m f k_sp hf_support

/-! ## Part 8: Direct Reflection Positivity -/

/-- **Theorem**: Direct proof of reflection positivity without spatial regulator.

    For test functions supported on positive time (t > 0), the RP inner product
    ⟨Θf, f⟩_C has non-negative real part.

    Proof: By `rp_equals_squared_norm_integral`,
      ⟨Θf, f⟩_C = (1/(2(2π)^{d-1})) * ∫_{k_sp} (1/ω) |F_ω(-k_sp)|² dk_sp
    Both the prefactor and integrand are non-negative. -/
@[blueprint "thm:free-covariance-reflection-positive-direct"
  (title := "Reflection Positivity (Direct Proof)")
  (keyDeclaration := true)
  (statement := /-- $\operatorname{Re}\langle f, f \rangle_{\text{RP}} \geq 0$ for positive-time $f$: direct proof via non-negative integrand $|\tilde{f}|^2/\omega$. -/)
  (proof := /--
    The goal is to show $\mathrm{Re}\langle\Theta f, f\rangle_C \ge 0$ for any complex test
    function $f$ with $f(x) = 0$ when $x_0 \le 0$.

    \textbf{Step 1 (Schwinger representation):} Replace $C(\Theta x, y)$ by its proper-time
    representation:
    $C(\Theta x, y) = \int_0^\infty e^{-sm^2} H(s, \|\Theta x - y\|)\, ds$
    where $H(s, r) = (4\pi s)^{-d/2} e^{-r^2/(4s)}$ is the heat kernel.

    \textbf{Step 2 (Fourier decomposition):} Write the heat kernel as a Fourier integral and
    decompose $k = (k_0, \vec{k})$ to separate the time and spatial contributions. Three
    Fubini interchanges are proved with explicit integrability bounds.

    \textbf{Step 3 (Proper-time integral):} After separating momentum components, the
    $s$-integral evaluates analytically:
    $\int_0^\infty \sqrt{\pi/s}\, e^{-t^2/(4s)}\, e^{-s\omega^2}\, ds
     = (\pi/\omega)\, e^{-\omega|t|}$
    where $\omega = \sqrt{\|\vec{k}\|^2 + m^2}$.

    \textbf{Step 4 (Factorization):} For positive-time test functions ($x_0 > 0$, $y_0 > 0$),
    we have $|-x_0 - y_0| = x_0 + y_0$, giving the key factorization
    $e^{-\omega(x_0 + y_0)} = e^{-\omega x_0} \cdot e^{-\omega y_0}$. The double integral
    factors into $|F_\omega(\vec{k})|^2$ where $F_\omega$ is the weighted Laplace--Fourier
    transform.

    \textbf{Step 5 (Non-negativity):} The final form is:
    $\langle\Theta f, f\rangle_C = \frac{1}{2(2\pi)^3}
     \int_{\mathbb{R}^3} \frac{1}{\omega(\vec{k})}\, |F_\omega(-\vec{k})|^2\, d\vec{k}$
    Since $\omega > 0$ (because $m > 0$) and $|F_\omega|^2 \ge 0$, the integrand is
    pointwise non-negative.
  -/)
]
theorem freeCovariance_reflection_positive_direct (f : TestFunctionℂ)
    (hf_supp : ∀ x : SpaceTime, x 0 ≤ 0 → f x = 0) :
    0 ≤ (rpInnerProduct m f).re := by
  rw [rp_equals_squared_norm_integral m f hf_supp]
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  apply mul_nonneg
  · -- (1/(2(2π)^{d-1})) ≥ 0
    apply one_div_nonneg.mpr
    apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    apply pow_nonneg
    apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) Real.pi_pos.le
  · -- Re(∫ ↑(real_val)) = ∫ real_val ≥ 0
    have h_integral_real : (∫ k_sp : SpatialCoords,
        ((1 / Real.sqrt (‖k_sp‖ ^ 2 + m ^ 2) *
          Complex.normSq (weightedLaplaceFourier m f (-k_sp)) : ℝ) : ℂ)) =
        ↑(∫ k_sp : SpatialCoords,
          (1 / Real.sqrt (‖k_sp‖ ^ 2 + m ^ 2) *
            Complex.normSq (weightedLaplaceFourier m f (-k_sp)))) :=
      integral_ofReal
    rw [h_integral_real, Complex.ofReal_re]
    apply MeasureTheory.integral_nonneg
    intro k_sp
    apply mul_nonneg
    · exact one_div_nonneg.mpr (Real.sqrt_nonneg _)
    · exact Complex.normSq_nonneg _

end RPProof

/-! ## Bridge to Direct Proof -/

/-- **Bridge Lemma**: The QFT namespace rpInnerProduct equals the RPProof rpInnerProduct.

    Both are defined using the same Bessel kernel C(x,y) = (m/(4π²r)) K₁(mr),
    so this equality holds by definition (rfl). -/
@[blueprint "lem:rp-inner-product-eq-rp-proof"
  (title := "RP Inner Product Bridge Lemma")
  (statement := /-- The QFT and RPProof definitions of the RP inner product agree (by definition). -/)
]
lemma rpInnerProduct_eq_rpProof (m : ℝ) [Fact (0 < m)] (f : TestFunctionℂ) :
    rpInnerProduct m f = RPProof.rpInnerProduct m f := by
  -- Both sides expand to the same integral using freeCovariance (Bessel)
  unfold rpInnerProduct RPProof.rpInnerProduct
  unfold freeCovarianceℂ_bilinear RPProof.freeCovarianceℂ_bilinear
  rfl

/-- **Main Reflection Positivity Theorem** (Bilinear Form)

    For any complex test function f supported on positive time (x₀ ≥ 0),
    the reflection positivity inner product is non-negative:

    Re⟨Θf, f⟩_C ≥ 0

    where C is the unregulated Bessel covariance kernel.

    **Proof:** Bridge to RPProof, then apply the direct proof
    via momentum representation and non-negativity of the integrand. -/
@[blueprint "thm:free-covariance-reflection-positive-bilinear"
  (title := "Reflection Positivity of Free Covariance (Complex)")
  (keyDeclaration := true)
  (statement := /-- $\operatorname{Re}\langle \Theta f, f \rangle_C \geq 0$ for complex positive-time test functions. -/)
]
theorem freeCovariance_reflection_positive_bilinear (m : ℝ) [Fact (0 < m)] (f : TestFunctionℂ)
    (hf_supp : ∀ x : SpaceTime, x 0 ≤ 0 → f x = 0) :
  0 ≤ (rpInnerProduct m f).re := by
  rw [rpInnerProduct_eq_rpProof]
  exact RPProof.freeCovariance_reflection_positive_direct m f hf_supp

/-! ## Connection to Real Test Functions

The result extends to real test functions via embedding. -/

/-- For real test functions, `star (toComplex f) = compTimeReflection (toComplex f)`.
    This is because conjugation is identity for real-valued functions. -/
@[blueprint "lem:star-to-complex-eq-comp-time-reflection"
  (title := "Star of Real Equals Time Reflection")
  (statement := /-- $(\iota f)^* = \Theta(\iota f)$: for real $f$, conjugation is trivial so star reduces to time reflection. -/)
]
lemma star_toComplex_eq_compTimeReflection (f : TestFunction) :
    star (toComplex f) = compTimeReflection (toComplex f) := by
  ext x
  -- star f is defined as starTestFunction f
  -- starTestFunction f x = starRingEnd ℂ ((compTimeReflection f) x)
  simp only [star, starTestFunction]
  -- Now goal: starRingEnd ℂ ((compTimeReflection (toComplex f)) x) = (compTimeReflection (toComplex f)) x
  exact compTimeReflection_toComplex_star_eq f x

/-- The rpInnerProduct of a real test function equals the complex bilinear form
    with compTimeReflection. -/
@[blueprint "lem:rp-inner-product-to-complex-eq"
  (title := "RP Inner Product for Real Functions")
  (statement := /-- $\langle \iota f, \iota f \rangle_{\text{RP}} = C(\Theta(\iota f), \iota f)$ for real test functions. -/)
]
lemma rpInnerProduct_toComplex_eq (m : ℝ) (f : TestFunction) :
    rpInnerProduct m (toComplex f) =
      freeCovarianceℂ_bilinear m (compTimeReflection (toComplex f)) (toComplex f) := by
  unfold rpInnerProduct
  rw [star_toComplex_eq_compTimeReflection]

/-- For real test functions, the reflection positivity inner product is non-negative. -/
@[blueprint "thm:covariance-rp-real"
  (title := "Covariance Reflection Positivity (Real)")
  (keyDeclaration := true)
  (statement := /-- For real positive-time test functions $f$, the reflection positivity inner product is non-negative: $\int\!\!\int (\theta f)(x)\, C(x,y)\, f(y)\, dx\, dy \ge 0$. -/)
  (uses := [freeCovariance_reflection_positive_bilinear, freeCovariance, compTimeReflectionReal])
  (latexEnv := "theorem")
  (latexLabel := "thm:covariance-rp-real")]
theorem freeCovariance_reflection_positive_bilinear_real (m : ℝ) [Fact (0 < m)] (f : TestFunction)
    (hf_supp : ∀ x : SpaceTime, x 0 ≤ 0 → f x = 0) :
  0 ≤ ∫ x, ∫ y, (QFT.compTimeReflectionReal f) x * freeCovariance m x y * f y := by
  -- Use the complex theorem for toComplex f
  have h_complex := freeCovariance_reflection_positive_bilinear m (toComplex f) (by
    intro x hx
    simp only [toComplex_apply]
    rw [hf_supp x hx]
    simp)
  -- Connect the real integral to the complex one via real_integral_eq_complex_re
  rw [real_integral_eq_complex_re m f]
  -- Show that the complex integral equals rpInnerProduct
  have h_eq : (∫ x, ∫ y, (QFT.compTimeReflection (toComplex f)) x * (freeCovariance m x y : ℂ)
        * (toComplex f) y ∂volume ∂volume)
      = rpInnerProduct m (toComplex f) := by
    rw [rpInnerProduct_toComplex_eq]
    rfl
  rw [h_eq]
  exact h_complex

/-- Alias for `freeCovariance_reflection_positive_bilinear_real` to match expected name. -/
@[blueprint "thm:free-covariance-reflection-positive-real"
  (title := "Reflection Positivity of Free Covariance (Real)")
  (statement := /-- $\int\!\!\int (\Theta f)(x)\, C(x,y)\, f(y)\, dx\, dy \geq 0$ for real positive-time test functions. -/)
]
theorem freeCovariance_reflection_positive_real (m : ℝ) [Fact (0 < m)] (f : TestFunction)
    (hf_supp : ∀ x : SpaceTime, x 0 ≤ 0 → f x = 0) :
  0 ≤ ∫ x, ∫ y, (QFT.compTimeReflectionReal f) x * freeCovariance m x y * f y :=
  freeCovariance_reflection_positive_bilinear_real m f hf_supp

end QFT
