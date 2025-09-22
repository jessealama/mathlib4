/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.ComplexShape
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Homology.EulerCharacteristic
import Mathlib.Algebra.Homology.EulerPoincare
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dimension.Subsingleton
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
# Euler Polyhedron Formula via Homological Algebra

This file provides the core homological machinery for proving Euler's polyhedron formula
using chain complexes and homological algebra from Mathlib.

The key insight is that a geometric polyhedron gives rise to a chain complex
with spherical homology, so the Euler-Poincaré characteristic formula applies.

## Main definitions

* `Polyhedron`: A combinatorial polyhedron with faces, dimensions, and incidence relations
* `GeometricPolyhedron`: A polyhedron equipped with a chain complex structure

## Main results

* `chain_euler_char_eq_face_sum`: The Euler characteristic of the chain complex equals
  the alternating sum of face counts
* `eulerChar_eq_one_add_neg_one_pow_dim_of_spherical`: For polyhedra with spherical homology,
  the Euler characteristic equals 1 + (-1)^dim
-/

open CategoryTheory Limits HomologicalComplex Module

/-- A polyhedron parameterized by its face type α.
    A combinatorial structure with faces and incidence relations.
    Faces have dimensions from 0 (vertices) to dim (top-dimensional faces). -/
structure Polyhedron (α : Type) [Fintype α] where
  /-- Face dimension function from 0 to dim -/
  face_dim : α → ℤ
  /-- The topological dimension. For a 2-sphere (surface of 3D polyhedron), dim = 2. -/
  dim : ℕ

  -- Dimension constraints
  /-- All faces have dimension between 0 and dim -/
  dim_range : ∀ f : α, 0 ≤ face_dim f ∧ face_dim f ≤ dim
  /-- There exists at least one face of each dimension from 0 to dim -/
  dim_surjective : ∀ k : ℤ, 0 ≤ k ∧ k ≤ dim → ∃ f : α, face_dim f = k

  /-- Incidence relation between faces -/
  incident : α → α → Bool
  /-- Incidence only occurs between adjacent dimensions -/
  incident_dims : ∀ f g : α, incident f g → (face_dim g = face_dim f + 1)

  /-- Each edge (1-dimensional face) is incident to exactly 2 vertices -/
  edge_vertex_count : ∀ e : α, face_dim e = 1 →
    ∃ (v1 v2 : α), face_dim v1 = 0 ∧ face_dim v2 = 0 ∧
      incident v1 e ∧ incident v2 e ∧ v1 ≠ v2 ∧
      (∀ v : α, face_dim v = 0 → incident v e → (v = v1 ∨ v = v2))

namespace Polyhedron

variable {α : Type} [Fintype α] (P : Polyhedron α)

end Polyhedron

section

variable {α : Type} [Fintype α] (P : Polyhedron α)


/-- Face count for dimension k (now works with ℤ dimensions) -/
def faceCount (P : Polyhedron α) (k : ℤ) : ℕ :=
  Fintype.card { f : α // P.face_dim f = k }

open CategoryTheory

/-- Type representing k-dimensional chains (functions supported on k-faces) -/
def kChains (P : Polyhedron α) (k : ℤ) : Type :=
  { f : α // P.face_dim f = k } → ZMod 2

/-- AddCommGroup structure for k-dimensional chains -/
instance (P : Polyhedron α) (k : ℤ) : AddCommGroup (kChains P k) :=
  Pi.addCommGroup

/-- Module structure for k-dimensional chains -/
instance (P : Polyhedron α) (k : ℤ) : Module (ZMod 2) (kChains P k) :=
  Pi.module _ _ _

/-- k-dimensional chains form a finite-dimensional module -/
instance (P : Polyhedron α) (k : ℤ) : FiniteDimensional (ZMod 2) (kChains P k) := by
  -- kChains P k is functions from a finite type to ZMod 2
  unfold kChains
  -- Functions from a finite type to a finite field are finite-dimensional
  infer_instance

/-- k-dimensional chains form an additive commutative monoid -/
instance (P : Polyhedron α) (k : ℤ) : AddCommMonoid (kChains P k) := by
  -- kChains P k is functions from a finite type to ZMod 2
  unfold kChains
  infer_instance

/-- k-dimensional chains form a finite module -/
instance (P : Polyhedron α) (k : ℤ) : Module.Finite (ZMod 2) (kChains P k) := by
  -- kChains P k is functions from a finite type to ZMod 2
  unfold kChains
  -- Functions from a finite type to a finite ring form a finite module
  infer_instance

/-- Extensionality for k-chains: two chains are equal if they agree on all k-faces -/
@[ext]
lemma kChains_ext {P : Polyhedron α} {k : ℤ} (f g : kChains P k)
    (h : ∀ x, f x = g x) : f = g :=
  funext h

/-- The boundary operator: maps k-chains to (k-1)-chains -/
noncomputable def boundary (P : Polyhedron α) (k : ℤ) :
    kChains P k →ₗ[ZMod 2] kChains P (k - 1) where
  toFun := fun chain => fun ⟨g, hg⟩ =>
    -- Sum over all k-faces incident to g (a (k-1)-face)
    Finset.sum Finset.univ fun f : { f : α // P.face_dim f = k } =>
      if P.incident g f.val then chain f else 0
  map_add' := fun x y => by
    -- The boundary operator is linear
    funext ⟨g, hg⟩
    -- Simplify by unfolding the definition
    dsimp only
    -- Use the fact that the sum of if-then-else can be split
    have h : ∀ (f : { f : α // P.face_dim f = k }),
      (if P.incident g f.val then (x + y) f else 0) =
      (if P.incident g f.val then x f else 0) +
      (if P.incident g f.val then y f else 0) := by
      intro f
      by_cases hf : P.incident g f.val
      · simp only [if_pos hf]
        rfl
      · simp only [if_neg hf, add_zero]
    simp_rw [h]
    -- Now we have a sum of (x f + y f) which we need to split
    -- This is the same as boundary applied to x plus boundary applied to y
    -- Split the sum using Finset.sum_add_distrib
    rw [Finset.sum_add_distrib]
    rfl
  map_smul' := fun r x => by
    -- The boundary operator respects scalar multiplication
    funext ⟨g, hg⟩
    -- Simplify by unfolding the definition
    dsimp only
    simp only [RingHom.id_apply]
    -- Use the fact that scalar multiplication distributes through if-then-else
    have h : ∀ (f : { f : α // P.face_dim f = k }),
      (if P.incident g f.val then (r • x) f else 0) =
      r • (if P.incident g f.val then x f else 0) := by
      intro f
      by_cases hf : P.incident g f.val
      · simp only [if_pos hf]
        rfl
      · simp only [if_neg hf, smul_zero]
    simp_rw [h]
    -- Apply scalar multiplication distributes over sum
    rw [← Finset.smul_sum]
    rfl

/-- A geometric polyhedron is a polyhedron that satisfies the chain complex property.
    This property ensures that the boundary of a boundary is zero (∂² = 0),
    which is a fundamental property of geometric polyhedra: each k-face is reached
    from each (k+2)-face through an even number of paths. -/
structure GeometricPolyhedron (α : Type) [Fintype α] extends Polyhedron α where
  /-- The boundary of boundary equals zero - this is the chain complex property -/
  boundary_of_boundary_eq_zero : ∀ k : ℤ,
    (boundary toPolyhedron (k - 1)) ∘ₗ (boundary toPolyhedron k) = 0

/-- The boundary composition property applied to an element -/
lemma boundary_comp_apply_eq_zero (GP : GeometricPolyhedron α) (i : ℤ)
    (x : kChains GP.toPolyhedron i) :
    boundary GP.toPolyhedron (i - 1) (boundary GP.toPolyhedron i x) = 0 := by
  rw [← LinearMap.comp_apply, GP.boundary_of_boundary_eq_zero i]
  rfl

/-- The chain complex of a geometric polyhedron over ZMod 2 (ℤ-indexed) -/
noncomputable def toChainComplex (GP : GeometricPolyhedron α) :
    ChainComplex (ModuleCat (ZMod 2)) ℤ where
  X k := ModuleCat.of (ZMod 2) (kChains GP.toPolyhedron k)
  d i j :=
    if h : i = j + 1 then
      -- Map from i-chains to j-chains where j = i - 1
      -- The boundary operator maps from dimension i to dimension (i - 1)
      -- Since j = i - 1, this is exactly what we need
      ModuleCat.ofHom (by
        have eq : i - 1 = j := by omega
        rw [← eq]
        exact boundary GP.toPolyhedron i)
    else 0
  shape := fun i j hij => by
    exact dif_neg (fun h => hij (by simp [ComplexShape.down, h]))
  d_comp_d' := fun i j k => by
    -- We need to show that d i j ≫ d j k = 0
    intros hij hjk

    -- From the shape condition, we have j + 1 = i and k + 1 = j
    have hi_eq : i = j + 1 := hij.symm
    have hj_eq : j = k + 1 := hjk.symm

    -- Unfold the definitions of d i j and d j k
    simp only [dif_pos hi_eq, dif_pos hj_eq]

    -- The goal is to show a composition of ModuleCat morphisms equals zero
    -- We'll show they're equal by showing they agree on all elements
    ext x y
    have bound_zero := boundary_comp_apply_eq_zero GP j

    -- The indices work out: j - 1 = k
    have idx : j - 1 = k := by omega

    -- The computation with coercions preserves the zero result
    -- We need to show the composition equals zero

    -- Use the fact that the composition of ModuleCat morphisms is computed pointwise
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_zero,
               LinearMap.zero_apply]

    -- The key indices relationships
    have eq1 : i - 1 = j := by omega
    have eq2 : j - 1 = k := by omega

    -- We use the boundary_of_boundary_eq_zero property
    have bd_zero := GP.boundary_of_boundary_eq_zero i

    -- This says: (boundary (i-1)) ∘ₗ (boundary i) = 0
    -- Apply functional extensionality
    simp only [LinearMap.ext_iff, LinearMap.comp_apply, LinearMap.zero_apply] at bd_zero

    -- bd_zero now says: ∀ x, boundary (i-1) (boundary i x) = 0
    -- With eq1 and eq2, this becomes: boundary j (boundary i x) = 0

    -- The goal has casts that align the types. These casts are essentially identity
    -- functions after accounting for the index equalities eq1 and eq2.

    -- Simplify the linear map composition in the goal
    simp only [LinearMap.comp_apply]

    -- Now we need to show that the casted boundaries composed give 0
    -- The casts preserve the computation, so we can apply bd_zero

    -- Use substitution to align indices
    -- bd_zero x gives us that boundary (i-1) (boundary i x) = 0 as functions
    have h_func := bd_zero x
    -- This means the function is the zero function, so applying to any y gives 0
    have h : ∀ z, (boundary GP.toPolyhedron (i - 1)) ((boundary GP.toPolyhedron i) x) z = 0 := by
      intro z
      rw [h_func]
      rfl

    -- Now we need to show the casted version equals zero
    -- The casts adjust indices but preserve the computation
    -- Since i - 1 = j and j - 1 = k, the casted boundaries match up

    -- Key observation: i - 1 - 1 = k
    have eq3 : i - 1 - 1 = k := by omega

    -- Now y has the right type after substitution
    -- We can apply h to get the zero result
    specialize h (eq3 ▸ y : { f // GP.face_dim f = i - 1 - 1 })

    -- The goal involves casts that essentially become identity after index adjustment
    -- The casted boundaries are equal to the uncasted ones after accounting for indices
    convert h using 2

    -- We need to show the equality of the casted vs uncasted application
    -- The goal has cast operations that we need to simplify

    -- Unfold what the casts are doing
    -- cast uses the proof that the types are equal to transport the value
    -- Since eq1: i-1 = j and eq2: j-1 = k, we have matching types

    -- The cast on boundary j uses eq1 to convert j to i-1
    -- The cast on boundary i keeps it as boundary i but adjusts the codomain

    -- Apply the fact that after the casts, we get the same computation
    -- The ⋯.mpr are casts that come from the equality proofs
    -- We need to show these casts preserve the computation

    -- Since the boundaries compose to zero regardless of the casts,
    -- and h already shows the result is zero, we need to show both sides are equal

    -- Both sides compute the composition of boundaries, just with different type alignments
    -- The LHS uses casts to align types, the RHS uses direct computation with a cast on y

    -- Since both compose boundaries that result in zero, they are equal
    -- We use the fact that the casts are just type alignments based on eq1, eq2, eq3

    -- The key insight: both sides are computing the same thing (boundary composition)
    -- just with different type alignments via casts

    -- Since h shows the RHS is 0, and we know boundary ∘ boundary = 0,
    -- the LHS must also be 0, making them equal

    -- Complete the proof by using subst to eliminate the index equalities,
    -- making the types match
    subst eq1 eq2

    -- Now the types align and we can use reflexivity
    rfl

/-- A polyhedron has spherical homology if it has the homology of a sphere:
    H_0 = 1 (connected), H_dim = 1 (encloses a region), and H_k = 0 for all other k -/
def hasSphericalHomology (GP : GeometricPolyhedron α) : Prop :=
  -- H_0 = 1 (connected)
  Module.finrank (ZMod 2) ((toChainComplex GP).homology 0) = 1 ∧
  -- H_dim = 1 (the polyhedron encloses a region)
  Module.finrank (ZMod 2) ((toChainComplex GP).homology GP.dim) = 1 ∧
  -- H_k = 0 for all other k
  ∀ k : ℤ, k ≠ 0 → k ≠ GP.dim →
    Module.finrank (ZMod 2) ((toChainComplex GP).homology k) = 0

/-- The dimension of k-chains equals the number of k-faces. -/
lemma kChains_finrank (P : Polyhedron α) (k : ℤ) :
    Module.finrank (ZMod 2) (kChains P k) = Fintype.card { f : α // P.face_dim f = k } := by
  unfold kChains
  exact Module.finrank_pi (ZMod 2)

-- FiniteDimensional instance for the chain complex
instance (GP : GeometricPolyhedron α) (i : ℕ) :
    FiniteDimensional (ZMod 2) ((toChainComplex GP).X i) := by
  simp only [toChainComplex]
  exact inferInstance

-- The chain modules are finite over ZMod 2
instance (GP : GeometricPolyhedron α) (i : ℤ) :
    Module.Finite (ZMod 2) ((toChainComplex GP).X i) := by
  simp only [toChainComplex]
  infer_instance

-- The chain complex has homology at every index
instance (GP : GeometricPolyhedron α) (i : ℤ) :
    (toChainComplex GP).HasHomology i := inferInstance

/-- Face dimensions are always at least 0 -/
lemma face_dim_nonneg (GP : GeometricPolyhedron α) (f : α) :
    GP.toPolyhedron.face_dim f ≥ 0 := by
  exact (GP.toPolyhedron.dim_range f).1

/-- Face dimensions are at most the polyhedron dimension -/
lemma face_dim_le_dim (GP : GeometricPolyhedron α) (f : α) :
    GP.toPolyhedron.face_dim f ≤ GP.dim := by
  exact (GP.toPolyhedron.dim_range f).2

/-- When the index type is empty, there is exactly one element: zero -/
lemma kChains_unique_of_isEmpty (P : Polyhedron α) (k : ℤ)
    (h : IsEmpty { f : α // P.face_dim f = k }) :
    ∀ (f : kChains P k), f = 0 := by
  intro f
  funext x
  exact (h.false x).elim

/-- When the index type is empty, the chain space is trivial -/
lemma kChains_isZero_of_isEmpty (P : Polyhedron α) (k : ℤ)
    (h : IsEmpty { f : α // P.face_dim f = k }) :
    IsZero (ModuleCat.of (ZMod 2) (kChains P k)) := by
  have h0 : ∀ (x : kChains P k), x = 0 := kChains_unique_of_isEmpty P k h
  have h_sub : Subsingleton (kChains P k) := by
    constructor
    intros x y
    rw [h0 x, h0 y]
  exact ModuleCat.isZero_of_subsingleton _

/-- When there are no faces of dimension k, the chain space is trivial -/
lemma kChains_isZero_of_no_faces (P : Polyhedron α) (k : ℤ)
    (h : ∀ f : α, P.face_dim f ≠ k) :
    IsZero (ModuleCat.of (ZMod 2) (kChains P k)) := by
  have h_empty : IsEmpty { f : α // P.face_dim f = k } := by
    constructor
    intro ⟨f, hf⟩
    exact h f hf
  exact kChains_isZero_of_isEmpty P k h_empty

/-- The chain complex is zero for dimensions below 0 -/
lemma chainComplex_isZero_below (GP : GeometricPolyhedron α) (k : ℤ) (hk : k < 0) :
    IsZero ((toChainComplex GP).X k) := by
  apply kChains_isZero_of_no_faces
  intro f hf
  have : GP.toPolyhedron.face_dim f ≥ 0 := face_dim_nonneg GP f
  omega

/-- The chain complex is zero for dimensions above dim -/
lemma chainComplex_isZero_above (GP : GeometricPolyhedron α) (k : ℤ)
    (hk : k > GP.dim) :
    IsZero ((toChainComplex GP).X k) := by
  apply kChains_isZero_of_no_faces
  intro f hf
  have : GP.toPolyhedron.face_dim f ≤ GP.dim := face_dim_le_dim GP f
  omega

/-- The chain complex has zero rank for negative dimensions -/
lemma chainComplex_finrank_eq_zero_of_neg (GP : GeometricPolyhedron α) (k : ℤ) (hk : k < 0) :
    Module.finrank (ZMod 2) ((toChainComplex GP).X k) = 0 := by
  have h_iso : IsZero ((toChainComplex GP).X k) := chainComplex_isZero_below GP k hk
  have h_sub : Subsingleton ↑((toChainComplex GP).X k) :=
    ModuleCat.subsingleton_of_isZero h_iso
  have h_rank : Module.rank (ZMod 2) ↑((toChainComplex GP).X k) = 0 :=
    rank_subsingleton' (ZMod 2) ↑((toChainComplex GP).X k)
  exact Module.finrank_eq_zero_of_rank_eq_zero h_rank

/-- The chain complex has zero rank above the polyhedron dimension -/
lemma chainComplex_finrank_eq_zero_of_gt_dim (GP : GeometricPolyhedron α) (k : ℤ)
    (hk : k > GP.dim) :
    Module.finrank (ZMod 2) ((toChainComplex GP).X k) = 0 := by
  have h_iso : IsZero ((toChainComplex GP).X k) := chainComplex_isZero_above GP k hk
  have h_sub : Subsingleton ↑((toChainComplex GP).X k) :=
    ModuleCat.subsingleton_of_isZero h_iso
  have h_rank : Module.rank (ZMod 2) ↑((toChainComplex GP).X k) = 0 :=
    rank_subsingleton' (ZMod 2) ↑((toChainComplex GP).X k)
  exact Module.finrank_eq_zero_of_rank_eq_zero h_rank

/-- If a chain module has finrank 0, then its homology has finrank 0 -/
lemma homology_finrank_zero_of_chain_finrank_zero (C : ChainComplex (ModuleCat (ZMod 2)) ℤ)
    (i : ℤ) [C.HasHomology i] [Module.Finite (ZMod 2) (C.X i)]
    (h : Module.finrank (ZMod 2) (C.X i) = 0) :
    Module.finrank (ZMod 2) (C.homology i) = 0 := by
  have h_zero_obj : IsZero (C.X i) := by
    have h_subsingleton : Subsingleton (C.X i) := by
      rw [← Module.finrank_zero_iff (R := ZMod 2)]
      exact h
    exact ModuleCat.isZero_of_subsingleton _

  have d_from_zero : C.d i (i - 1) = 0 := by
    exact h_zero_obj.eq_zero_of_src _

  have d_to_zero : C.d (i + 1) i = 0 := by
    exact h_zero_obj.eq_zero_of_tgt _

  have ker_is_whole : LinearMap.ker (C.d i (i - 1)).hom = ⊤ := by
    rw [d_from_zero]
    simp only [ModuleCat.hom_zero]
    exact LinearMap.ker_zero

  have im_is_bot : LinearMap.range (C.d (i + 1) i).hom = ⊥ := by
    rw [d_to_zero]
    simp only [ModuleCat.hom_zero]
    exact LinearMap.range_zero

  have homology_zero : IsZero (C.homology i) := by
    apply ShortComplex.isZero_homology_of_isZero_X₂
    exact h_zero_obj

  have : Module.finrank (ZMod 2) (C.homology i) = 0 := by
    have h_sub : Subsingleton (C.homology i) :=
      ModuleCat.subsingleton_of_isZero homology_zero
    rw [Module.finrank_zero_iff (R := ZMod 2)]
    exact h_sub

  exact this

/-- The homology at dimension 0 is 1-dimensional (connected component) -/
lemma homology_finrank_eq_one_at_zero_of_spherical (GP : GeometricPolyhedron α)
    (hsphere : hasSphericalHomology GP) :
    Module.finrank (ZMod 2) ((toChainComplex GP).homology 0) = 1 := by
  exact hsphere.1

/-- The homology at the top dimension is 1-dimensional for polyhedra with spherical homology.
    This represents the fact that the polyhedron encloses a region. -/
lemma homology_finrank_eq_one_at_dim_of_spherical (GP : GeometricPolyhedron α)
    (hsphere : hasSphericalHomology GP) :
    Module.finrank (ZMod 2) ((toChainComplex GP).homology GP.dim) = 1 := by
  exact hsphere.2.1

/-- Homology vanishes for negative dimensions -/
lemma homology_finrank_eq_zero_of_neg (GP : GeometricPolyhedron α)
    (k : ℤ) (hk : k < 0) :
    Module.finrank (ZMod 2) ((toChainComplex GP).homology k) = 0 := by
  have h_chain : Module.finrank (ZMod 2) ((toChainComplex GP).X k) = 0 :=
    chainComplex_finrank_eq_zero_of_neg GP k hk
  exact homology_finrank_zero_of_chain_finrank_zero (toChainComplex GP) k h_chain

/-- Homology vanishes for dimensions above GP.dim -/
lemma homology_finrank_eq_zero_of_gt_dim (GP : GeometricPolyhedron α)
    (k : ℤ) (hk : k > GP.dim) :
    Module.finrank (ZMod 2) ((toChainComplex GP).homology k) = 0 := by
  have h_chain : Module.finrank (ZMod 2) ((toChainComplex GP).X k) = 0 :=
    chainComplex_finrank_eq_zero_of_gt_dim GP k hk
  exact homology_finrank_zero_of_chain_finrank_zero (toChainComplex GP) k h_chain

/-- Splitting a sum over [0, dim+1) into first element, middle elements, and last element -/
lemma sum_split_first_last_int {R : Type*} [Ring R] (f : ℤ → R) (dim : ℕ) (hdim : 0 < dim) :
    (∑ i ∈ Finset.Ico (0 : ℤ) ((dim : ℤ) + 1), f i) =
    f 0 + (∑ i ∈ Finset.Ico (1 : ℤ) (dim : ℤ), f i) + f dim := by
  have h_bij : ∀ i ∈ Finset.Ico (0 : ℤ) ((dim : ℤ) + 1), 0 ≤ i ∧ i ≤ dim := by
    intros i hi
    simp only [Finset.mem_Ico] at hi
    omega

  -- split [0, dim+1) = {0} ∪ [1, dim) ∪ {dim}
  have h1 : Finset.Ico (0 : ℤ) ((dim : ℤ) + 1) =
      {(0 : ℤ)} ∪ Finset.Ico (1 : ℤ) ((dim : ℤ) + 1) := by
    ext x
    simp only [Finset.mem_Ico, Finset.mem_union, Finset.mem_singleton]
    constructor
    · intro ⟨h0, hdim1⟩
      by_cases hx : x = 0
      · left; exact hx
      · right; omega
    · intro h
      cases h with
      | inl h => subst h; omega
      | inr h => omega

  have h2 : Finset.Ico (1 : ℤ) ((dim : ℤ) + 1) = Finset.Ico (1 : ℤ) (dim : ℤ) ∪ {(dim : ℤ)} := by
    ext x
    simp only [Finset.mem_Ico, Finset.mem_union, Finset.mem_singleton]
    constructor
    · intro ⟨h1, hdim1⟩
      by_cases hx : x = dim
      · right; exact hx
      · left; omega
    · intro h
      cases h with
      | inl h => omega
      | inr h => subst h; omega

  rw [h1, Finset.sum_union, Finset.sum_singleton, h2, Finset.sum_union, Finset.sum_singleton]
  · simp only [add_assoc]
  · simp only [Finset.disjoint_singleton_right, Finset.mem_Ico]
    omega
  · simp only [Finset.disjoint_singleton_left, Finset.mem_Ico]
    omega

/-- The chain complex has zero rank outside the range [0, dim] -/
lemma chainComplex_finrank_zero_outside (GP : GeometricPolyhedron α) (k : ℤ)
    (hk : k ∉ Finset.Ico (0 : ℤ) ((GP.dim : ℤ) + 1)) :
    Module.finrank (ZMod 2) ((toChainComplex GP).X k) = 0 := by
  simp only [Finset.mem_Ico, not_and_or, not_lt] at hk
  cases hk with
  | inl h =>
    exact chainComplex_finrank_eq_zero_of_neg GP k (by omega)
  | inr h =>
    exact chainComplex_finrank_eq_zero_of_gt_dim GP k (by omega)

/-- The chain complex has finite support: only non-zero in [0, dim] -/
lemma chain_finite_support (GP : GeometricPolyhedron α) :
    {i : ℤ | Module.finrank (ZMod 2) ((toChainComplex GP).X i) ≠ 0}.Finite := by
  apply Set.Finite.subset (Finset.finite_toSet (Finset.Ico (0 : ℤ) ((GP.dim : ℤ) + 1)))
  intro i hi
  simp at hi
  by_contra h_not_in
  rw [Finset.mem_coe] at h_not_in
  have : Module.finrank (ZMod 2) ((toChainComplex GP).X i) = 0 :=
    chainComplex_finrank_zero_outside GP i h_not_in
  exact hi this

/-- The homology has finite support for polyhedra with spherical homology -/
lemma homology_finite_support (GP : GeometricPolyhedron α)
    (hsphere : hasSphericalHomology GP) :
    {i : ℤ | Module.finrank (ZMod 2) ((toChainComplex GP).homology i) ≠ 0}.Finite := by
  apply Set.Finite.subset (Finset.finite_toSet {0, (GP.dim : ℤ)})
  intro i hi
  simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]

  by_cases h0 : i = 0
  · left; exact h0
  by_cases hdim : i = GP.dim
  · right; exact hdim

  exfalso
  apply hi
  exact hsphere.2.2 i h0 hdim

/-- The Euler characteristic of the chain complex equals the alternating sum of face counts -/
theorem chain_euler_char_eq_face_sum (GP : GeometricPolyhedron α) :
    ChainComplex.eulerChar (toChainComplex GP) =
    ∑ k ∈ Finset.range (GP.dim + 1), (-1 : ℤ)^k * (faceCount GP.toPolyhedron k : ℤ) := by
  have h_support : ∀ i ∉ Finset.Ico (0 : ℤ) ((GP.dim : ℤ) + 1),
      Module.finrank (ZMod 2) ((toChainComplex GP).X i) = 0 :=
    chainComplex_finrank_zero_outside GP

  rw [ChainComplex.eulerChar_eq_boundedEulerChar _
      (Finset.Ico (0 : ℤ) ((GP.dim : ℤ) + 1)) h_support]

  simp only [ChainComplex.boundedEulerChar]

  -- X k has rank equal to faceCount
  have h_finrank : ∀ k : ℤ, k ∈ Finset.Ico (0 : ℤ) ((GP.dim : ℤ) + 1) →
      Module.finrank (ZMod 2) ((toChainComplex GP).X k) = faceCount GP.toPolyhedron k := by
    intro k hk
    simp only [Finset.mem_Ico] at hk
    simp only [toChainComplex]
    rw [kChains_finrank]
    rfl

  apply Finset.sum_bij
    (fun i hi => Int.natAbs i)

  · intro i hi
    simp only [Finset.mem_Ico] at hi
    simp only [Finset.mem_range]
    have : 0 ≤ i := hi.1
    have : i < (GP.dim : ℤ) + 1 := hi.2
    omega

  · intro i₁ hi₁ i₂ hi₂ h_eq
    simp only [Finset.mem_Ico] at hi₁ hi₂
    have h1 : 0 ≤ i₁ := hi₁.1
    have h2 : 0 ≤ i₂ := hi₂.1
    have eq1 : i₁ = ↑(Int.natAbs i₁) := (Int.natAbs_of_nonneg h1).symm
    have eq2 : i₂ = ↑(Int.natAbs i₂) := (Int.natAbs_of_nonneg h2).symm
    rw [eq1, eq2, h_eq]

  · intro n hn
    simp only [Finset.mem_range] at hn
    use (n : ℤ)
    refine ⟨?_, ?_⟩
    · simp only [Finset.mem_Ico]
      omega
    · rfl

  · intro i hi
    simp only [Finset.mem_Ico] at hi
    have hi_nonneg : 0 ≤ i := hi.1
    have hi_ico : i ∈ Finset.Ico (0 : ℤ) ((GP.dim : ℤ) + 1) := by
      simp only [Finset.mem_Ico]
      exact hi
    rw [h_finrank i hi_ico]
    congr 1
    congr 1
    rw [Int.natAbs_of_nonneg hi_nonneg]

theorem eulerChar_eq_one_add_neg_one_pow_dim_of_spherical (GP : GeometricPolyhedron α)
    (hdim : 0 < GP.dim) (hsphere : hasSphericalHomology GP) :
    ChainComplex.eulerChar (toChainComplex GP) = 1 + (-1 : ℤ)^GP.dim := by
  calc ChainComplex.eulerChar (toChainComplex GP)

    -- Step 2: Apply Euler-Poincaré formula
    = ChainComplex.homologyEulerChar (toChainComplex GP) := by {
      have chain_supp := chain_finite_support GP
      have homology_supp := homology_finite_support GP hsphere

      let indices := Finset.Ico (0 : ℤ) ((GP.dim : ℤ) + 1)

      have hc : ChainComplex.eulerChar (toChainComplex GP) =
                ChainComplex.boundedEulerChar (toChainComplex GP) indices := by
        apply ChainComplex.eulerChar_eq_boundedEulerChar
        exact chainComplex_finrank_zero_outside GP

      have hh : ChainComplex.homologyEulerChar (toChainComplex GP) =
                ChainComplex.homologyBoundedEulerChar (toChainComplex GP) indices := by
        apply ChainComplex.homologyEulerChar_eq_homologyBoundedEulerChar
        intro i hi
        by_cases h : i < 0
        · exact homology_finrank_eq_zero_of_neg GP i h
        · push_neg at h
          have : i ≥ (GP.dim : ℤ) + 1 := by
            by_contra h_not
            push_neg at h_not
            have : i ∈ Finset.Ico (0 : ℤ) ((GP.dim : ℤ) + 1) := by
              simp [Finset.mem_Ico, h, h_not]
            exact hi this
          have : i > GP.dim := by omega
          exact homology_finrank_eq_zero_of_gt_dim GP i this

      rw [hc, hh]
      apply ChainComplex.eulerChar_eq_homology_eulerChar
      · omega
      · intro i hi
        have : IsZero ((toChainComplex GP).X i) := chainComplex_isZero_below GP i hi
        exact this
      · intro i hi
        have : IsZero ((toChainComplex GP).X i) := chainComplex_isZero_above GP i hi
        exact this
    }

    -- convert infinite sum to bounded sum over [0, dim]
    _ = ChainComplex.homologyBoundedEulerChar (toChainComplex GP)
          (Finset.Ico (0 : ℤ) ((GP.dim : ℤ) + 1)) := by
      apply ChainComplex.homologyEulerChar_eq_homologyBoundedEulerChar
      intro i hi
      simp only [Finset.mem_Ico, not_and_or] at hi
      cases hi with
      | inl h_low =>
        simp only [not_le] at h_low
        exact homology_finrank_eq_zero_of_neg GP i h_low
      | inr h_high =>
        simp only [not_lt] at h_high
        have : i > GP.dim := by omega
        exact homology_finrank_eq_zero_of_gt_dim GP i this

    -- expand bounded sum
    _ = (∑ i ∈ Finset.Ico (0 : ℤ) ((GP.dim : ℤ) + 1),
          (-1 : ℤ)^Int.natAbs i *
          (Module.finrank (ZMod 2) ((toChainComplex GP).homology i) : ℤ)) := by
      rfl  -- By definition of homologyBoundedEulerChar

    -- split sum into H_0, middle terms, and H_dim
    _ = (Module.finrank (ZMod 2) ((toChainComplex GP).homology 0) : ℤ) +
        (∑ i ∈ Finset.Ico (1 : ℤ) (GP.dim : ℤ),
          (-1 : ℤ)^Int.natAbs i *
          (Module.finrank (ZMod 2) ((toChainComplex GP).homology i) : ℤ)) +
        (-1 : ℤ)^GP.dim *
        (Module.finrank (ZMod 2) ((toChainComplex GP).homology GP.dim) : ℤ) := by
      rw [sum_split_first_last_int _ _ hdim]
      simp only [Int.natAbs_zero, pow_zero, one_mul, Int.natAbs_cast]

    -- middle terms vanish
    _ = (Module.finrank (ZMod 2) ((toChainComplex GP).homology 0) : ℤ) +
        0 +
        (-1 : ℤ)^GP.dim *
        (Module.finrank (ZMod 2) ((toChainComplex GP).homology GP.dim) : ℤ) := by
      congr 1
      congr 1
      apply Finset.sum_eq_zero
      intros i hi
      simp only [Finset.mem_Ico] at hi
      have h_ne_0 : i ≠ 0 := by omega
      have h_ne_dim : i ≠ GP.dim := by omega
      have : Module.finrank (ZMod 2) ((toChainComplex GP).homology i) = 0 :=
        hsphere.2.2 i h_ne_0 h_ne_dim
      simp [this]

    -- H_0 = H_dim = 1
    _ = 1 + 0 + (-1 : ℤ)^GP.dim * 1 := by
      rw [homology_finrank_eq_one_at_zero_of_spherical GP hsphere,
          homology_finrank_eq_one_at_dim_of_spherical GP hsphere]
      simp

    _ = 1 + (-1 : ℤ)^GP.dim := by ring

end
