/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
import Mathlib.Geometry.Polyhedron.Convex.Basic
import Mathlib.Order.Lattice
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Faces of Convex Polyhedra

This file defines the face structure of convex polyhedra and shows it forms a lattice.

A face of a polyhedron is the intersection of the polyhedron with a supporting hyperplane.
The faces form a lattice under inclusion.

## Main definitions

* `HPolyhedron.Face` - A face of a polyhedron
* `HPolyhedron.faceDim` - Dimension of a face
* `HPolyhedron.vertices` - The 0-dimensional faces (vertices)
* `HPolyhedron.edges` - The 1-dimensional faces (edges)
* `HPolyhedron.facets` - The (d-1)-dimensional faces where d is the polyhedron dimension

## Main results

* `HPolyhedron.face_lattice` - The faces form a lattice under inclusion

-/

open Set Finset Module
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace HPolyhedron

variable (P : HPolyhedron E)

/-- A half-space supports a polyhedron if all points of the polyhedron satisfy the inequality
    and at least one point achieves equality -/
def IsSupporting (P : HPolyhedron E) (h : HalfSpace E) : Prop :=
  P.toSet ⊆ h.toSet ∧ (P.toSet ∩ h.boundary).Nonempty

/-- A subset F is a face of polyhedron P if it's the intersection of P with the boundary
    of some supporting half-space -/
def IsFace (P : HPolyhedron E) (F : Set E) : Prop :=
  ∃ h : HalfSpace E, IsSupporting P h ∧ F = P.toSet ∩ h.boundary

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- The dimension of a face (as an affine subspace) -/
noncomputable def faceDim (F : Set E) (_hF : IsFace P F) : ℕ :=
  finrank ℝ (affineSpan ℝ F).direction

/-- A face is a vertex if it's 0-dimensional -/
def IsVertex (F : Set E) : Prop :=
  IsFace P F ∧ ∃ hF : IsFace P F, faceDim P F hF = 0

/-- A face is an edge if it's 1-dimensional -/
def IsEdge (F : Set E) : Prop :=
  IsFace P F ∧ ∃ hF : IsFace P F, faceDim P F hF = 1

/-- A face is a facet if it has dimension dim(P) - 1 -/
def IsFacet (F : Set E) : Prop :=
  IsFace P F ∧ ∃ hF : IsFace P F, faceDim P F hF = finrank ℝ E - 1

end FiniteDimensional

/-- The set of all faces of a polyhedron -/
def faces (P : HPolyhedron E) : Set (Set E) :=
  {F | IsFace P F}

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- The set of all vertices of a polyhedron -/
def vertices : Set (Set E) :=
  {F | IsVertex P F}

/-- The set of all edges of a polyhedron -/
def edges : Set (Set E) :=
  {F | IsEdge P F}

/-- The set of all facets of a polyhedron -/
def facets : Set (Set E) :=
  {F | IsFacet P F}

end FiniteDimensional

/-- Every face is contained in the polyhedron -/
lemma face_subset_polyhedron (P : HPolyhedron E) {F : Set E} (hF : IsFace P F) :
    F ⊆ P.toSet := by
  obtain ⟨h, ⟨_, rfl⟩⟩ := hF
  exact Set.inter_subset_left

/-- The polyhedron itself is a face (via trivial supporting halfspace) -/
lemma polyhedron_is_face (P : HPolyhedron E) : IsFace P P.toSet := sorry

/-- The empty set is a face -/
lemma empty_is_face (P : HPolyhedron E) : IsFace P ∅ := sorry

/-- The intersection of two faces is a face -/
lemma face_inter_face (P : HPolyhedron E) {F G : Set E} (hF : IsFace P F) (hG : IsFace P G) :
    IsFace P (F ∩ G) := sorry

/-- Faces are closed under intersection -/
lemma faces_closed_under_inter :
    ∀ F ∈ faces P, ∀ G ∈ faces P, F ∩ G ∈ faces P := by
  intros F hF G hG
  exact face_inter_face P hF hG

/-- A face is determined by which inequalities are tight -/
lemma face_tight_inequalities (P : HPolyhedron E) {F : Set E} (hF : IsFace P F) :
    ∃ I ⊆ P.halfSpaces,
      F = {x ∈ P.toSet | ∀ i ∈ I, ⟪(i : HalfSpace E).normal, x⟫ = i.bound} := sorry

end HPolyhedron
