/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Dress

/-!
Positive Definite Functions

This file contains the definition of positive definite functions and basic lemmas.
Extracted from Minlos.lean to avoid circular imports with GaussianRBF.lean.

Key definitions:
- `IsPositiveDefinite`: A function φ : α → ℂ is positive definite if for any finite
  collection of points and complex coefficients, ∑ᵢⱼ c̄ᵢ cⱼ φ(xᵢ - xⱼ) ≥ 0

Key lemmas:
- `isPositiveDefinite_precomp_linear`: Composition with linear map preserves PD
-/

open Complex
open BigOperators

/-! ## Positive Definiteness -/

/-- A function φ : α → ℂ is positive definite if for any finite collection
    of points x₁, ..., xₘ and complex coefficients c₁, ..., cₘ, we have
    ∑ᵢⱼ c̄ᵢ cⱼ φ(xᵢ - xⱼ) ≥ 0

    This is the standard definition in harmonic analysis and probability theory. -/
@[blueprint "def:positive-definite"
  (title := "Positive Definite Function")
  (statement := /-- A function $\varphi : \alpha \to \mathbb{C}$ is positive definite if $\sum_{i,j} \overline{c_i} c_j \varphi(x_i - x_j) \geq 0$ for all finite collections and coefficients. -/)
  (latexEnv := "definition")
  (latexLabel := "def:positive-definite")]
def IsPositiveDefinite {α : Type*} [AddGroup α] (φ : α → ℂ) : Prop :=
  ∀ (m : ℕ) (x : Fin m → α) (c : Fin m → ℂ),
    0 ≤ (∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * φ (x i - x j)).re

/-- Composition preserves positive definiteness: if ψ is positive definite on H and
    T : E →ₗ[ℝ] H is linear, then ψ ∘ T is positive definite on E. -/
@[blueprint "lem:pd-precomp-linear"
  (title := "Linear Precomposition Preserves Positive Definiteness")
  (statement := /-- If $\psi$ is positive definite on $H$ and $T : E \to_{\mathbb{R}} H$ is linear, then $\psi \circ T$ is positive definite on $E$. -/)
  (uses := [IsPositiveDefinite])
  (latexEnv := "lemma")
  (latexLabel := "lem:pd-precomp-linear")]
lemma isPositiveDefinite_precomp_linear
  {E H : Type*} [AddCommGroup E] [AddCommGroup H]
  [Module ℝ E] [Module ℝ H]
  (ψ : H → ℂ) (hPD : IsPositiveDefinite ψ) (T : E →ₗ[ℝ] H) :
  IsPositiveDefinite (fun f : E => ψ (T f)) := fun m x c => by
  simpa using hPD m (fun i => T (x i)) c
