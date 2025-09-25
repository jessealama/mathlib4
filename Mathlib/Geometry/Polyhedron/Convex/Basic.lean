/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Convex Polyhedra

This file defines convex polyhedra using two separate representations:
- H-representation: intersection of finitely many half-spaces
- V-representation: convex hull of finitely many points

These are kept as separate structure types. We prove their equivalence for bounded sets
(Minkowski-Weyl theorem).

## Main definitions

* `HalfSpace` - A half-space defined by a linear inequality
* `HPolyhedron` - H-representation as intersection of half-spaces
* `VPolyhedron` - V-representation as convex hull of finite set

## Main results

* `HPolyhedron.to_VPolyhedron` - Every bounded H-polyhedron has a V-representation (TODO)
* `VPolyhedron.to_HPolyhedron` - Every V-polyhedron has an H-representation (TODO)

## Implementation notes

We work in general finite-dimensional inner product spaces, but specialize to `ℝ³`
for Euler's polyhedron formula.

-/

open Set Finset
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A half-space in a real inner product space, defined by a linear inequality `⟨a, x⟩ ≤ b` -/
structure HalfSpace (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  normal : E
  bound : ℝ

namespace HalfSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Points satisfying a half-space inequality -/
def toSet (h : HalfSpace E) : Set E :=
  {x | ⟪h.normal, x⟫ ≤ h.bound}

/-- The boundary hyperplane of a half-space -/
def boundary (h : HalfSpace E) : Set E :=
  {x | ⟪h.normal, x⟫ = h.bound}

lemma convex (h : HalfSpace E) : Convex ℝ h.toSet := by
  intro x hx y hy a b ha hb hab
  simp only [toSet, Set.mem_setOf_eq] at hx hy ⊢
  calc ⟪h.normal, a • x + b • y⟫
      = a * ⟪h.normal, x⟫ + b * ⟪h.normal, y⟫ := by
        simp only [inner_add_right, inner_smul_right]
    _ ≤ a * h.bound + b * h.bound := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hx ha
        · exact mul_le_mul_of_nonneg_left hy hb
    _ = h.bound := by rw [← add_mul, hab, one_mul]

end HalfSpace

/-- H-representation: a polyhedron as intersection of finitely many half-spaces -/
structure HPolyhedron (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  halfSpaces : Finset (HalfSpace E)
  nonempty : halfSpaces.Nonempty

namespace HPolyhedron

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The set of points in a polyhedron given by H-representation -/
def toSet (P : HPolyhedron E) : Set E :=
  ⋂ h ∈ P.halfSpaces, (h : HalfSpace E).toSet

lemma convex (P : HPolyhedron E) : Convex ℝ P.toSet := by
  apply convex_iInter₂
  intros h _
  exact HalfSpace.convex h

/-- A bounded subset of a real inner product space -/
def isBounded (P : HPolyhedron E) : Prop :=
  ∃ R > 0, P.toSet ⊆ Metric.ball 0 R

end HPolyhedron

/-- V-representation: a polyhedron as convex hull of finitely many points -/
structure VPolyhedron (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  vertices : Finset E
  nonempty : vertices.Nonempty

namespace VPolyhedron

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The set of points in a polyhedron given by V-representation -/
def toSet (P : VPolyhedron E) : Set E :=
  convexHull ℝ (P.vertices : Set E)

lemma convex (P : VPolyhedron E) : Convex ℝ P.toSet :=
  convex_convexHull _ _

lemma compact (P : VPolyhedron E) : IsCompact P.toSet := by
  have : (P.vertices : Set E).Finite := Finset.finite_toSet P.vertices
  exact this.isCompact_convexHull

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- Convert a V-polyhedron to an H-polyhedron (use supporting hyperplanes) -/
noncomputable def toHPolyhedron (P : VPolyhedron E) : HPolyhedron E :=
  sorry  -- This requires finding the supporting hyperplanes

end FiniteDimensional

end VPolyhedron

/-- Convert a bounded H-polyhedron to a V-polyhedron (vertices are extreme points) -/
noncomputable def HPolyhedron.toVPolyhedron {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (P : HPolyhedron E) (hb : P.isBounded) : VPolyhedron E :=
  sorry  -- This requires proving that bounded H-polyhedra have finitely many extreme points

/-- Minkowski-Weyl theorem: bounded H-polyhedra and V-polyhedra represent the same objects -/
theorem minkowski_weyl {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (P : HPolyhedron E) (hb : P.isBounded) :
    (P.toVPolyhedron hb).toHPolyhedron.toSet = P.toSet := sorry

/-- H-polyhedra in ℝ³ -/
abbrev HPolyhedron3D := HPolyhedron (EuclideanSpace ℝ (Fin 3))

/-- V-polyhedra in ℝ³ -/
abbrev VPolyhedron3D := VPolyhedron (EuclideanSpace ℝ (Fin 3))
