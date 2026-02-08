# Free Covariance

The free massive scalar field propagator $C(x, y)$ and its properties. The construction proceeds from momentum space through Fourier transform to position space, establishing all the analytic properties needed for the OS axioms.

## Mathematical Background

The free Euclidean propagator for a massive scalar field with mass $m > 0$ in $d = 4$ dimensions is defined in momentum space as:

$$\hat{C}(k) = \frac{1}{\|k\|^2 + m^2}$$

The position-space kernel is obtained by inverse Fourier transform:

$$C(x - y) = \frac{1}{(2\pi)^4} \int_{\mathbb{R}^4} \frac{e^{ik\cdot(x-y)}}{\|k\|^2 + m^2}\  d^4k$$

In 4D, this evaluates to the Bessel function representation:

$$C(x, y) = \frac{m}{4\pi^2 \|x - y\|} K_1(m\|x - y\|)$$

where $K_1$ is the modified Bessel function of the second kind. Key properties:
- **Positivity:** $C(x, y) > 0$ for $x \ne y$
- **Symmetry:** $C(x, y) = C(y, x)$
- **Euclidean invariance:** $C(gx, gy) = C(x, y)$ for all $g \in E(4)$
- **Singularity:** $C(x, y) \sim \text{const}/\|x-y\|^2$ as $x \to y$
- **Exponential decay:** $C(x, y) \sim \text{const} \cdot e^{-m\|x-y\|}/\|x-y\|^{3/2}$ as $\|x-y\| \to \infty$

## Proof Strategy

The construction and verification involves four major components:

### 1. Schwinger Representation and Heat Kernel

The propagator admits a proper-time (Schwinger) representation:

$$\frac{1}{\|k\|^2 + m^2} = \int_0^{\infty} e^{-t(\|k\|^2 + m^2)}\  dt$$

Performing the Fourier transform under the proper-time integral yields the **heat kernel representation**:

$$C(x, y) = \int_0^{\infty} e^{-tm^2} H_t(\|x-y\|)\  dt$$

where $H_t(r) = \frac{1}{16\pi^2 t^2} e^{-r^2/(4t)}$ is the 4D heat kernel.

### 2. Regularization Strategy

To rigorously justify Fubini-type exchanges of integration, a Gaussian regulator $e^{-\alpha\|k\|^2}$ is introduced:

$$C_\alpha(x, y) = \int \frac{e^{-\alpha\|k\|^2} e^{ik\cdot(x-y)}}{\|k\|^2 + m^2} \frac{dk}{(2\pi)^4}$$

This makes all integrals absolutely convergent. The true covariance is recovered as $\alpha \to 0^+$. The key technical result is that $C_\alpha(x, y) = C_\alpha^{\text{Schwinger}}(\|x-y\|)$, where the right-hand side involves a regulated Schwinger integral that can be explicitly bounded.

### 3. Bilinear Form and Parseval Identity

For test functions $f, g \in \mathcal{S}(\mathbb{R}^4, \mathbb{C})$, the bilinear covariance form is:

$$\langle f, Cg\rangle = \iint \overline{f(x)}\  C(x-y)\  g(y)\  dx\  dy$$

The **Parseval identity** relates this to momentum space:

$$\mathrm{Re}\langle f, Cf\rangle = \int \frac{|\hat{f}(k)|^2}{\|k\|^2 + m^2}\  dk$$

This immediately gives **positive semi-definiteness**: $\mathrm{Re}\langle f, Cf\rangle \ge 0$ since the integrand is non-negative.

### 4. Hilbert Space Embedding

The covariance form factors through a Hilbert space. Define the map $T\colon \text{TestFunction} \to L^2$ by:

$$Tf(k) = \hat{f}(k) \sqrt{\frac{1}{\|k\|^2 + m^2}}$$

Then $C(f, f) = \|Tf\|^2$, establishing the Hilbert space embedding required by the Minlos theorem.

## Key Declarations

### Momentum Space (`CovarianceMomentum.lean`)

| Declaration | Description |
|-------------|-------------|
| [`freePropagatorMomentum`](../OSforGFF/CovarianceMomentum.lean#L129) | $\hat{C}(k) = 1/(\|k\|^2 + m^2)$ in physics conventions |
| [`freePropagatorMomentum_mathlib`](../OSforGFF/CovarianceMomentum.lean#L141) | Same in Mathlib Fourier conventions |
| [`freePropagator_pos`](../OSforGFF/CovarianceMomentum.lean#L2093) | $\hat{C}(k) > 0$ |
| [`freePropagator_bounded`](../OSforGFF/CovarianceMomentum.lean#L2102) | $\hat{C}(k) \le 1/m^2$ |
| [`freePropagator_even`](../OSforGFF/CovarianceMomentum.lean#L133) | $\hat{C}(-k) = \hat{C}(k)$ |
| [`freePropagator_smooth`](../OSforGFF/CovarianceMomentum.lean#L2060) | $\hat{C}$ is smooth |
| [`freeCovariance_regulated`](../OSforGFF/CovarianceMomentum.lean#L169) | Gaussian-regulated propagator $C_\alpha(x,y)$ in position space |
| [`freeCovariance`](../OSforGFF/CovarianceMomentum.lean#L469) | The covariance $C(x,y)$ (limit of $C_\alpha$) |
| [`freeCovarianceBessel`](../OSforGFF/CovarianceMomentum.lean#L463) | Bessel representation: $C(x,y) = \frac{m}{4\pi^2 r} K_1(mr)$ |
| [`freeCovarianceKernel`](../OSforGFF/CovarianceMomentum.lean#L1690) | Translation-invariant kernel $C(x-y)$ |
| [`schwingerIntegrand`](../OSforGFF/CovarianceMomentum.lean#L202) | Schwinger integrand $e^{-t(\|k\|^2+m^2)}$ |
| [`schwinger_representation`](../OSforGFF/CovarianceMomentum.lean#L221) | $\int_0^\infty e^{-t(\|k\|^2+m^2)}\ dt = 1/(\|k\|^2+m^2)$ |
| [`heatKernelPositionSpace`](../OSforGFF/CovarianceMomentum.lean#L237) | 4D heat kernel $H_t(r)$ |
| [`heatKernelPositionSpace_integral_eq_one`](../OSforGFF/CovarianceMomentum.lean#L373) | $\int H_t = 1$ |
| [`covarianceSchwingerRep`](../OSforGFF/CovarianceMomentum.lean#L413) | Schwinger representation of covariance |
| [`covarianceSchwingerRep_eq_besselFormula`](../OSforGFF/CovarianceMomentum.lean#L438) | $C^{\text{Schwinger}} = \frac{m}{4\pi^2 r} K_1(mr)$ |
| [`momentumWeight`](../OSforGFF/CovarianceMomentum.lean#L2159) | $\|k\|^2 + m^2$ as a weight function |
| [`momentumWeightSqrt`](../OSforGFF/CovarianceMomentum.lean#L2168) | $\sqrt{1/(\|k\|^2 + m^2)}$ |
| [`momentumWeightSqrt_mul_CLM`](../OSforGFF/CovarianceMomentum.lean#L2290) | Multiplication by $\sqrt{\hat{C}(k)}$ as CLM on $L^2$ |

### Convergence and Bounds (`CovarianceMomentum.lean`)

| Declaration | Description |
|-------------|-------------|
| [`freeCovariance_regulated_tendsto_bessel`](../OSforGFF/CovarianceMomentum.lean#L1164) | $C_\alpha \to C_{\text{Bessel}}$ as $\alpha \to 0^+$ |
| [`freeCovariance_regulated_limit_eq_freeCovariance`](../OSforGFF/CovarianceMomentum.lean#L1197) | $C_\alpha \to C$ as $\alpha \to 0^+$ |
| [`freeCovariance_regulated_le_const_mul_freeCovariance`](../OSforGFF/CovarianceMomentum.lean#L1318) | $|C_\alpha| \le e^{m^2} C$ for $\alpha \in (0,1]$ |
| [`freeCovariance_regulated_uniformly_bounded`](../OSforGFF/CovarianceMomentum.lean#L1364) | $C_\alpha$ is uniformly bounded |
| [`freeCovariance_symmetric`](../OSforGFF/CovarianceMomentum.lean#L2044) | $C(x,y) = C(y,x)$ |
| [`freeCovarianceBessel_pos`](../OSforGFF/CovarianceMomentum.lean#L479) | $C(x,y) > 0$ for $x \ne y$ |
| [`freeCovarianceKernel_decay_bound`](../OSforGFF/CovarianceMomentum.lean#L1732) | $|C(z)| \le \text{const} \cdot \|z\|^{-2}$ |
| [`freeCovariance_exponential_bound`](../OSforGFF/CovarianceMomentum.lean#L1893) | $|C(u,v)| \le \text{const} \cdot e^{-m\|u-v\|}$ for large separation |
| [`freeCovarianceKernel_integrable`](../OSforGFF/CovarianceMomentum.lean#L1699) | $C_{\text{kernel}} \in L^1$ |
| [`freeCovarianceKernel_continuousOn`](../OSforGFF/CovarianceMomentum.lean#L1972) | $C_{\text{kernel}}$ continuous on $\{z \ne 0\}$ |
| [`fubini_schwinger_fourier`](../OSforGFF/CovarianceMomentum.lean#L825) | $C_\alpha(x,y) = C_\alpha^{\text{Schwinger}}(\|x-y\|)$ |
| [`gaussianFT_eq_heatKernel_times_norm`](../OSforGFF/CovarianceMomentum.lean#L538) | Gaussian FT $= (2\pi)^d H_t(\|z\|)$ |

### Parseval Identity (`Parseval.lean`)

| Declaration | Description |
|-------------|-------------|
| [`parseval_covariance_schwartz_regulated`](../OSforGFF/Parseval.lean#L593) | $\mathrm{Re}\langle f, C_\alpha f\rangle = \int G_\alpha |\hat{f}|^2 \hat{C}\ dk$ |
| [`parseval_covariance_schwartz_correct`](../OSforGFF/Parseval.lean#L653) | $\mathrm{Re}\langle f, C_\alpha f\rangle \to \int |\hat{f}|^2 \hat{C}\ dk$ as $\alpha \to 0^+$ |
| [`bilinear_covariance_regulated_tendstoℂ`](../OSforGFF/Parseval.lean#L739) | $\langle f, C_\alpha g\rangle \to \langle f, Cg\rangle$ as $\alpha \to 0^+$ |
| [`regulated_fubini_factorization`](../OSforGFF/Parseval.lean#L455) | $\mathrm{Re}\langle f, C_\alpha f\rangle$ factors through Fourier transforms |
| [`change_of_variables_momentum`](../OSforGFF/Parseval.lean#L418) | Rescaling from physics to Mathlib Fourier conventions |
| [`physicsFourierTransform`](../OSforGFF/Parseval.lean#L138) | Physics-convention Fourier transform |
| [`physicsFT_rescale`](../OSforGFF/Parseval.lean#L386) | Relation between physics FT and Mathlib FT |
| [`freeCovarianceℂ_bilinear`](../OSforGFF/OS3_CovarianceRP.lean#L108) | The bilinear form $\langle f, Cg\rangle$ on complex test functions |

### Covariance Properties (`Covariance.lean`, `CovarianceR.lean`)

| Declaration | Description |
|-------------|-------------|
| [`freeCovarianceℂ_bilinear_integrable`](../OSforGFF/Covariance.lean#L206) | $f(x)\ C(x,y)\ g(y)$ is integrable for Schwartz $f, g$ |
| [`freeCovarianceℂ_positive`](../OSforGFF/Covariance.lean#L631) | $\mathrm{Re}\langle f, Cf\rangle \ge 0$ |
| [`parseval_covariance_schwartz_bessel`](../OSforGFF/Covariance.lean#L658) | $\mathrm{Re}\langle f, Cf\rangle = \int |\hat{f}|^2 \hat{C}\ dk$ (final form) |
| [`freeCovariance_euclidean_invariant`](../OSforGFF/Covariance.lean#L404) | $C(gx, gy) = C(x, y)$ for $g \in E(4)$ |
| [`covariance_timeReflection_invariant`](../OSforGFF/Covariance.lean#L425) | $C(\Theta x, \Theta y) = C(x, y)$ |
| [`freeCovarianceℂ_bilinear_symm`](../OSforGFF/Covariance.lean#L558) | $\langle f, Cg\rangle = \langle g, Cf\rangle$ |
| [`freeCovarianceℂ_bilinear_add_left`](../OSforGFF/Covariance.lean#L525) | Additivity in first argument |
| [`freeCovarianceℂ_bilinear_smul_left`](../OSforGFF/Covariance.lean#L535) | Homogeneity in first argument |
| [`freeCovarianceFormR`](../OSforGFF/CovarianceR.lean#L48) | Restriction to real test functions |
| [`freeCovarianceFormR_pos`](../OSforGFF/CovarianceR.lean#L465) | $0 \le C(f, f)$ for real $f$ |
| [`freeCovarianceFormR_symm`](../OSforGFF/CovarianceR.lean#L479) | $C(f, g) = C(g, f)$ for real $f, g$ |
| [`freeCovarianceFormR_continuous`](../OSforGFF/CovarianceR.lean#L452) | $f \mapsto C(f, f)$ is continuous |

### Hilbert Space Embedding (`CovarianceR.lean`)

| Declaration | Description |
|-------------|-------------|
| [`sqrtPropagatorMap`](../OSforGFF/CovarianceR.lean#L90) | $Tf(k) = \hat{f}(k)\sqrt{\hat{C}(k)}$ |
| [`sqrtPropagatorMap_memLp`](../OSforGFF/CovarianceR.lean#L150) | $Tf \in L^2$ |
| [`sqrtPropagatorMap_norm_eq_covariance`](../OSforGFF/CovarianceR.lean#L205) | $\|Tf\|^2 = C(f,f)$ |
| [`embeddingMap`](../OSforGFF/CovarianceR.lean#L271) | $T$ as a linear map $\text{TestFunction} \to L^2$ |
| [`embeddingMapCLM`](../OSforGFF/CovarianceR.lean#L298) | $T$ as a continuous linear map |
| [`sqrtPropagatorEmbedding`](../OSforGFF/CovarianceR.lean#L343) | $\exists\  H, T$ with $C(f,f) = \|Tf\|^2$ |
| [`freeCovarianceFormR_eq_normSq`](../OSforGFF/CovarianceR.lean#L433) | $C(f,f) = \|\text{embeddingMap}\ f\|^2$ |
| [`embeddingMap_continuous`](../OSforGFF/CovarianceR.lean#L440) | $\text{embeddingMap}$ is continuous |

### Reflection Positivity Ingredients (`CovarianceR.lean`)

| Declaration | Description |
|-------------|-------------|
| [`freeCovarianceFormR_reflection_invariant`](../OSforGFF/CovarianceR.lean#L604) | $C(\Theta f, \Theta g) = C(f, g)$ |
| [`freeCovarianceFormR_reflection_cross`](../OSforGFF/CovarianceR.lean#L686) | $C(\Theta f, g) = C(\Theta g, f)$ |
| [`freeCovarianceFormR_left_linear_any_right`](../OSforGFF/CovarianceR.lean#L728) | Linearity of $\sum_i c_i\  C(\Theta f_i, g)$ |

## Detailed Proof Outline

### Parseval Identity

The Parseval identity is proved in four stages:

**Stage 1: Regulated Fubini factorization.** For the regulated integral $\langle f, C_\alpha f\rangle$, the Gaussian regulator $e^{-\alpha\|k\|^2}$ makes the triple integral $(x, y, k)$ absolutely convergent. Apply Fubini to reorder integration, obtaining:

$$\mathrm{Re}\langle f, C_\alpha f\rangle = \int_k G_\alpha(k) \cdot |\hat{f}(k)|^2 \cdot \hat{C}(k)\  dk$$

where $G_\alpha(k) = e^{-\alpha\|k\|^2}$ is the regulator.

**Stage 2: Change of variables.** Rescale from physics Fourier conventions ($\int e^{ikx}$) to Mathlib conventions ($\int e^{-2\pi i k \cdot x}$), absorbing factors of $(2\pi)^d$.

**Stage 3: Monotone convergence.** As $\alpha \to 0^+$, the regulated integrand increases monotonically to the unregulated integrand. The dominated convergence theorem (with dominator $|\hat{f}|^2/m^2$) gives convergence.

**Stage 4: Bilinear extension.** Extend from $\langle f, Cf\rangle$ to $\langle f, Cg\rangle$ via the polarization identity.

### Schwinger Representation

1. Evaluate $\int_0^\infty e^{-t(a^2+m^2)}\ dt = 1/(a^2+m^2)$ for $a^2 = \|k\|^2$.
2. Exchange the $k$-integral and $t$-integral (Fubini, justified by the regulator).
3. The inner $k$-integral is a Gaussian integral giving the heat kernel: $\int e^{-t\|k\|^2 - ik\cdot z}\ dk = (2\pi)^d H_t(\|z\|)$.
4. Complete the square to obtain the Schwinger representation of $C(x,y)$.
5. Evaluate via the Laplace integral (`LaplaceIntegral.lean`) to get the Bessel form.

## References

- Glimm, J. and Jaffe, A. *Quantum Physics: A Functional Integral Point of View*, Ch. 6.
- Osterwalder, K. and Schrader, R. "Axioms for Euclidean Green's functions II", *Comm. Math. Phys.* 42 (1975), 281-305.
- Simon, B. *Functional Integration and Quantum Physics*, Academic Press (1979).
- The rp_proof_explained.md document in this repository for the spatial regularization strategy.
