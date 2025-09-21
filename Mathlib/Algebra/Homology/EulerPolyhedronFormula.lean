/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
import Mathlib.Algebra.Homology.EulerPolyhedronFormula.Basic

/-!
# Euler Polyhedron Formula

This file imports the main results about Euler's polyhedron formula.

The core machinery and proofs are in `Mathlib.Algebra.Homology.EulerPolyhedronFormula.Basic`.

## Main Result

The theorem `eulerChar_eq_one_add_neg_one_pow_dim_of_spherical` states that for a geometric
polyhedron with spherical homology of dimension d, the Euler characteristic equals 1 + (-1)^d.

This is a general homological result that underlies the classical Euler polyhedron formula
V - E + F = 2 for convex polyhedra.
-/

