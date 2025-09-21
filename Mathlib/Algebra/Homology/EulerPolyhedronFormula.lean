/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
import Mathlib.Algebra.Homology.EulerPolyhedronFormula.Basic

/-!
# Euler Polyhedron Formula

This module proves Euler's polyhedron formula using homological algebra and chain complexes.

## Main Components

- `GeometricPolyhedron`: A polyhedron structure with the chain complex property (∂² = 0)
- `toChainComplex`: Constructs the chain complex from a geometric polyhedron
- `toAugmentedComplex`: Constructs the augmented chain complex
- `isAcyclic`: Defines acyclicity for the augmented complex

## Key Results

The main theorem `euler_polyhedron_formula` states that for an acyclic geometric polyhedron P
of dimension d, the Euler characteristic equals 1 + (-1)^d.

### Special Cases
- `euler_formula_2d`: For 2-dimensional polyhedra (surfaces), V - E + F = 2
- `euler_formula_1d`: For 1-dimensional polyhedra (polygons), V - E = 0

## Approach

The proof uses the augmented chain complex of the polyhedron. The key insight is that
for an acyclic complex, the Euler characteristic can be computed via a telescoping sum,
yielding the alternating sum of face counts.

## References

* [Grünbaum, *Convex Polytopes*][gruenbaum2003]
* [Lakatos, *Proofs and Refutations*][lakatos1976]
* [Richeson, *Euler's Gem*][richeson2008]
-/

open Polyhedron

variable {α : Type} [Fintype α]

/-- For a geometric polyhedron with spherical homology and positive dimension,
    the Euler characteristic of the chain complex equals 1 + (-1)^d.

    This is the main theorem that connects the combinatorial Euler characteristic
    (alternating sum of face counts) with the topological homology. -/
theorem euler_polyhedron_formula (GP : GeometricPolyhedron α) [DecidableEq α]
    (hdim : 0 < GP.toPolyhedron.dim) (hsphere : hasSphericalHomology GP) :
    ChainComplex.eulerChar (toChainComplex GP) = 1 + (-1 : ℤ)^GP.toPolyhedron.dim := by
  -- Direct application of the spherical_euler_char theorem
  exact spherical_euler_char GP hdim hsphere

/-- Corollary: For geometric polyhedra representing surfaces of 3D solids, we get V - E + F = 2
    This is the classical Euler formula. With the simplified structure, dim=2 for a 2-sphere. -/
theorem euler_formula_2d (GP : GeometricPolyhedron α) [DecidableEq α]
    (hsphere : hasSphericalHomology GP) (h_dim : GP.toPolyhedron.dim = 2) :
    (faceCount GP.toPolyhedron 0 : ℤ) - (faceCount GP.toPolyhedron 1 : ℤ) +
      (faceCount GP.toPolyhedron 2 : ℤ) = 2 := by
  -- Use the main theorem
  have hdim_pos : 0 < GP.toPolyhedron.dim := by rw [h_dim]; norm_num
  have h_main := euler_polyhedron_formula GP hdim_pos hsphere
  rw [h_dim] at h_main
  -- h_main : ChainComplex.eulerChar (toChainComplex GP) = 1 + (-1)^2 = 1 + 1 = 2
  simp only [pow_two] at h_main

  -- Connect chain complex Euler char to face counts
  have h_face_sum := chain_euler_char_eq_face_sum GP
  rw [h_dim] at h_face_sum

  -- Expand the sum for dim = 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h_face_sum
  simp only [pow_zero, pow_one, pow_two, one_mul, neg_mul] at h_face_sum

  -- Combine with h_main: ChainComplex.eulerChar = 2
  rw [h_main] at h_face_sum
  -- h_face_sum now says: 2 = sum...
  simp only [neg_neg] at h_face_sum
  -- Simplify 1 + -1 * -1 = 1 + 1 = 2
  norm_num at h_face_sum
  -- Convert -a to subtraction
  rw [← sub_eq_add_neg] at h_face_sum
  exact h_face_sum.symm

/-- Special case: For 1-dimensional geometric polyhedra (cycles/polygons), V - E = 0 -/
theorem euler_formula_1d (GP : GeometricPolyhedron α) [DecidableEq α]
    (hsphere : hasSphericalHomology GP) (h_dim : GP.toPolyhedron.dim = 1) :
    (faceCount GP.toPolyhedron 0 : ℤ) = (faceCount GP.toPolyhedron 1 : ℤ) := by
  have hdim_pos : 0 < GP.toPolyhedron.dim := by rw [h_dim]; norm_num
  have hformula := euler_polyhedron_formula GP hdim_pos hsphere
  -- For a 1-dimensional polyhedron: χ(P) = 1 + (-1)^1 = 1 - 1 = 0
  rw [h_dim] at hformula
  simp at hformula
  -- Use face count relation
  have h_face_sum := chain_euler_char_eq_face_sum GP
  rw [h_dim] at h_face_sum
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h_face_sum
  simp [pow_zero, pow_one] at h_face_sum
  rw [hformula] at h_face_sum
  have : (faceCount GP.toPolyhedron 0 : ℤ) - (faceCount GP.toPolyhedron 1 : ℤ) = 0 := by
    linarith only [h_face_sum]
  linarith only [this]
