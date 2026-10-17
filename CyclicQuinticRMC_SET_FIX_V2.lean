-- SET-FIX V2: explicit Set carrier and mem_generated conversions.
import Mathlib
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic

/-!
# Real cyclic quintics and restricted marked-ruler constructibility

Pinned environment: Lean 4.34.0, Mathlib tag v4.34.0
Mathlib commit: 5ed2965256430c3649e86755f9576b54eca72435

The final theorem is `RMCQuintic.real_galois_quintic_constructible`.
The permitted finite constructions are explicitly defined by `Constructible`.
No cubic or sextic root constructor is assumed. The final `#print axioms`
command audits dependencies, including any accidentally admitted proof.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false


/-!
# The cyclic conjugate matrix is nonsingular

For an automorphism `sigma` of exact order five and a `K`-basis
`b : Fin 5 → L`, form the matrix

    A i j = sigma^i (b j).

Dedekind independence makes the five automorphisms independent as functions.
Evaluation on the basis preserves that independence, so the rows of `A` are
independent. Hence `A` is invertible and its determinant is nonzero.
-/

namespace CyclicQuintic

/-!
## 1. The first five powers are distinct
-/

theorem five_powers_injective
    {G : Type*} [Group G]
    (sigma : G) (horder : orderOf sigma = 5) :
    Function.Injective (fun i : Fin 5 => sigma ^ (i : ℕ)) := by
  intro i j hij
  have hmod :
      (i : ℕ) % orderOf sigma = (j : ℕ) % orderOf sigma :=
    (pow_inj_mod
      (x := sigma)
      (n := (i : ℕ))
      (m := (j : ℕ))).mp hij
  apply Fin.ext
  simpa [
    horder,
    Nat.mod_eq_of_lt i.isLt,
    Nat.mod_eq_of_lt j.isLt
  ] using hmod

/-!
## 2. Dedekind independence as ordinary functions
-/

theorem five_algEquiv_powers_function_independent
    {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (sigma : L ≃ₐ[K] L)
    (horder : orderOf sigma = 5) :
    LinearIndependent L
      (fun i : Fin 5 =>
        fun x : L => (sigma ^ (i : ℕ)) x) := by
  let chars : Fin 5 → (L →* L) :=
    fun i => (sigma ^ (i : ℕ)).toMonoidHom

  have hchars : Function.Injective chars := by
    intro i j hij
    apply five_powers_injective sigma horder
    ext x
    exact congrArg (fun f : L →* L => f x) hij

  have hli :
      LinearIndependent L
        (fun i : Fin 5 => ⇑(chars i)) :=
    (linearIndependent_monoidHom L L).comp chars hchars

  simpa [chars] using hli

/-!
## 3. Forget the linear-map structure

This map sends a `K`-linear map to its underlying function. It is itself
`L`-linear because scalar multiplication occurs pointwise in the codomain.
-/

def coeKLinear
    {K L : Type*}
    [Field K] [Field L] [Algebra K L] :
    (L →ₗ[K] L) →ₗ[L] (L → L) where
  toFun f := fun x => f x
  map_add' f g := by
    rfl
  map_smul' c f := by
    rfl

/-!
## 4. Independence as `K`-linear maps

The images under `coeKLinear` are the independent functions from the
Dedekind theorem, so the original `K`-linear maps are independent too.
-/

theorem five_algEquiv_powers_kLinear_independent
    {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (sigma : L ≃ₐ[K] L)
    (horder : orderOf sigma = 5) :
    LinearIndependent L
      (fun i : Fin 5 =>
        (sigma ^ (i : ℕ)).toLinearMap) := by
  apply LinearIndependent.of_comp
    (coeKLinear (K := K) (L := L))
  simpa [coeKLinear, Function.comp_def] using
    five_algEquiv_powers_function_independent sigma horder

/-!
## 5. Evaluation on a five-element basis
-/

noncomputable def evalOnBasis
    {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (b : Module.Basis (Fin 5) K L) :
    (L →ₗ[K] L) →ₗ[L] (Fin 5 → L) where
  toFun f := fun i => f (b i)
  map_add' f g := by
    ext i
    rfl
  map_smul' c f := by
    ext i
    rfl

theorem evalOnBasis_injective
    {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (b : Module.Basis (Fin 5) K L) :
    Function.Injective (evalOnBasis b) := by
  intro f g hfg
  apply b.ext
  intro i
  exact congrFun hfg i

/-!
## 6. The cyclic conjugate matrix

Its rows are the five automorphisms evaluated on the five basis elements.
-/

noncomputable def conjugateMatrix
    {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (sigma : L ≃ₐ[K] L)
    (b : Module.Basis (Fin 5) K L) :
    Matrix (Fin 5) (Fin 5) L :=
  fun i j => (sigma ^ (i : ℕ)) (b j)

/-!
## 7. The matrix rows are linearly independent
-/

theorem conjugateMatrix_rows_independent
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (sigma : L ≃ₐ[K] L)
    (horder : orderOf sigma = 5)
    (b : Module.Basis (Fin 5) K L) :
    LinearIndependent L (conjugateMatrix sigma b).row := by

  have hmaps :
      LinearIndependent L
        (fun i : Fin 5 =>
          (sigma ^ (i : ℕ)).toLinearMap) :=
    five_algEquiv_powers_kLinear_independent sigma horder

  have hInjective :
      Function.Injective (evalOnBasis b) :=
    evalOnBasis_injective b

  have hker :
      (evalOnBasis b).ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr hInjective

  have heval :
      LinearIndependent L
        ((evalOnBasis b) ∘
          fun i : Fin 5 =>
            (sigma ^ (i : ℕ)).toLinearMap) :=
    hmaps.map' (evalOnBasis b) hker

  change LinearIndependent L
    (fun i : Fin 5 =>
      fun j : Fin 5 =>
        (sigma ^ (i : ℕ)) (b j))

  simpa [evalOnBasis, Function.comp_def, AlgEquiv.coe_pow]
    using heval

/-!
## 8. Independent rows imply matrix invertibility
-/

-- The second branch intentionally supports Mathlib before the theorem rename.
set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
theorem conjugateMatrix_isUnit
    {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (sigma : L ≃ₐ[K] L)
    (horder : orderOf sigma = 5)
    (b : Module.Basis (Fin 5) K L) :
    IsUnit (conjugateMatrix sigma b) := by
  first
  | exact Matrix.linearIndependent_row_iff_isUnit.mp
      (conjugateMatrix_rows_independent sigma horder b)
  | exact Matrix.linearIndependent_rows_iff_isUnit.mp
      (conjugateMatrix_rows_independent sigma horder b)

/-!
## 9. Therefore its determinant is a unit
-/

theorem conjugateMatrix_det_isUnit
    {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (sigma : L ≃ₐ[K] L)
    (horder : orderOf sigma = 5)
    (b : Module.Basis (Fin 5) K L) :
    IsUnit (conjugateMatrix sigma b).det := by
  exact
    (Matrix.isUnit_iff_isUnit_det
      (conjugateMatrix sigma b)).mp
      (conjugateMatrix_isUnit sigma horder b)

/-!
## 10. Final nonsingularity statement
-/

theorem conjugateMatrix_det_ne_zero
    {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (sigma : L ≃ₐ[K] L)
    (horder : orderOf sigma = 5)
    (b : Module.Basis (Fin 5) K L) :
    (conjugateMatrix sigma b).det ≠ 0 := by
  exact
    (conjugateMatrix_det_isUnit
      sigma horder b).ne_zero



end CyclicQuintic

namespace CyclicQuintic

/-!
# Cyclic conjugate coordinates

The conjugate matrix has entries

    A i j = sigma^i (b j).

Given a coordinate vector `v : Fin 5 → L`, multiplication by `A`
produces the vector

    i ↦ ∑ j, sigma^i (b j) * v j.

Because `A` is a unit, this coordinate transformation is injective.
Since its source and target are the same finite-dimensional space, it
upgrades to a linear equivalence.

This is the algebraic bridge needed before transporting density and
open positivity conditions.
-/

noncomputable def conjugateCoordinateMap
    {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (sigma : L ≃ₐ[K] L)
    (b : Module.Basis (Fin 5) K L) :
    (Fin 5 → L) →ₗ[L] (Fin 5 → L) :=
  Matrix.toLin' (conjugateMatrix sigma b)


theorem conjugateCoordinateMap_apply
    {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (sigma : L ≃ₐ[K] L)
    (b : Module.Basis (Fin 5) K L)
    (v : Fin 5 → L) :
    conjugateCoordinateMap sigma b v =
      fun i : Fin 5 =>
        ∑ j : Fin 5,
          (sigma ^ (i : ℕ)) (b j) * v j := by
  ext i
  simp [
    conjugateCoordinateMap,
    conjugateMatrix,
    Matrix.toLin'_apply',
    Matrix.mulVec,
    dotProduct
  ]


theorem conjugateCoordinateMap_apply_component
    {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (sigma : L ≃ₐ[K] L)
    (b : Module.Basis (Fin 5) K L)
    (v : Fin 5 → L)
    (i : Fin 5) :
    conjugateCoordinateMap sigma b v i =
      ∑ j : Fin 5,
        (sigma ^ (i : ℕ)) (b j) * v j := by
  exact congrFun (conjugateCoordinateMap_apply sigma b v) i


theorem conjugateCoordinateMap_injective
    {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (sigma : L ≃ₐ[K] L)
    (horder : orderOf sigma = 5)
    (b : Module.Basis (Fin 5) K L) :
    Function.Injective (conjugateCoordinateMap sigma b) := by

  have hunit :
      IsUnit (conjugateMatrix sigma b) :=
    conjugateMatrix_isUnit sigma horder b

  have hcols :
      LinearIndependent L
        (conjugateMatrix sigma b).col :=
    Matrix.linearIndependent_cols_of_isUnit hunit

  have hmul :
      Function.Injective
        (conjugateMatrix sigma b).mulVec :=
    Matrix.mulVec_injective_iff.mpr hcols

  simpa only [
    conjugateCoordinateMap,
    Matrix.toLin'_apply',
    Matrix.coe_mulVecLin
  ] using hmul


noncomputable def conjugateCoordinateEquiv
    {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (sigma : L ≃ₐ[K] L)
    (horder : orderOf sigma = 5)
    (b : Module.Basis (Fin 5) K L) :
    (Fin 5 → L) ≃ₗ[L] (Fin 5 → L) :=
  LinearEquiv.ofInjectiveEndo
    (conjugateCoordinateMap sigma b)
    (conjugateCoordinateMap_injective sigma horder b)


theorem conjugateCoordinateEquiv_apply
    {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (sigma : L ≃ₐ[K] L)
    (horder : orderOf sigma = 5)
    (b : Module.Basis (Fin 5) K L)
    (v : Fin 5 → L) :
    conjugateCoordinateEquiv sigma horder b v =
      conjugateCoordinateMap sigma b v := by
  simp [conjugateCoordinateEquiv]


theorem conjugateCoordinateEquiv_apply_component
    {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (sigma : L ≃ₐ[K] L)
    (horder : orderOf sigma = 5)
    (b : Module.Basis (Fin 5) K L)
    (v : Fin 5 → L)
    (i : Fin 5) :
    conjugateCoordinateEquiv sigma horder b v i =
      ∑ j : Fin 5,
        (sigma ^ (i : ℕ)) (b j) * v j := by
  rw [conjugateCoordinateEquiv_apply]
  exact conjugateCoordinateMap_apply_component sigma b v i


theorem conjugateCoordinateMap_surjective
    {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (sigma : L ≃ₐ[K] L)
    (horder : orderOf sigma = 5)
    (b : Module.Basis (Fin 5) K L) :
    Function.Surjective (conjugateCoordinateMap sigma b) := by

  have hsurjective :
      Function.Surjective
        (conjugateCoordinateEquiv sigma horder b) :=
    (conjugateCoordinateEquiv sigma horder b).surjective

  simpa [conjugateCoordinateEquiv] using hsurjective


theorem conjugateCoordinateMap_bijective
    {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (sigma : L ≃ₐ[K] L)
    (horder : orderOf sigma = 5)
    (b : Module.Basis (Fin 5) K L) :
    Function.Bijective (conjugateCoordinateMap sigma b) := by
  constructor
  · exact conjugateCoordinateMap_injective sigma horder b
  · exact conjugateCoordinateMap_surjective sigma horder b


theorem exists_unique_conjugate_coordinates
    {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (sigma : L ≃ₐ[K] L)
    (horder : orderOf sigma = 5)
    (b : Module.Basis (Fin 5) K L)
    (y : Fin 5 → L) :
    ∃! v : Fin 5 → L,
      conjugateCoordinateMap sigma b v = y := by

  have hbijective :
      Function.Bijective
        (conjugateCoordinateMap sigma b) :=
    conjugateCoordinateMap_bijective sigma horder b

  obtain ⟨v, hv⟩ := hbijective.2 y

  refine ⟨v, hv, ?_⟩

  intro w hw

  apply hbijective.1

  exact hw.trans hv.symm


theorem conjugateCoordinateEquiv_inverse_identity
    {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (sigma : L ≃ₐ[K] L)
    (horder : orderOf sigma = 5)
    (b : Module.Basis (Fin 5) K L)
    (y : Fin 5 → L) :
    conjugateCoordinateEquiv sigma horder b
        ((conjugateCoordinateEquiv sigma horder b).symm y) =
      y := by
  exact (conjugateCoordinateEquiv sigma horder b).apply_symm_apply y


theorem conjugateCoordinateEquiv_forward_identity
    {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (sigma : L ≃ₐ[K] L)
    (horder : orderOf sigma = 5)
    (b : Module.Basis (Fin 5) K L)
    (v : Fin 5 → L) :
    (conjugateCoordinateEquiv sigma horder b).symm
        (conjugateCoordinateEquiv sigma horder b v) =
      v := by
  exact (conjugateCoordinateEquiv sigma horder b).symm_apply_apply v

end CyclicQuintic

namespace CyclicQuintic

/-!
# The real conjugate-coordinate homeomorphism

Suppose the cyclic quintic field `L` admits a field embedding

    ι : L →+* ℝ.

Applying `ι` entrywise to the abstract conjugate matrix gives a real
five-by-five matrix. Because field embeddings are injective, its
determinant remains nonzero.

The resulting real linear map is therefore an equivalence. Since its
domain and codomain are finite-dimensional real vector spaces, it is
automatically continuous in both directions.

This is the topological bridge required for the density argument.
-/

/-!
## 1. Map the conjugate matrix into the real numbers
-/

noncomputable def realConjugateMatrix
    {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (ι : L →+* ℝ)
    (sigma : L ≃ₐ[K] L)
    (b : Module.Basis (Fin 5) K L) :
    Matrix (Fin 5) (Fin 5) ℝ :=
  (conjugateMatrix sigma b).map ι


theorem realConjugateMatrix_apply
    {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (ι : L →+* ℝ)
    (sigma : L ≃ₐ[K] L)
    (b : Module.Basis (Fin 5) K L)
    (i j : Fin 5) :
    realConjugateMatrix ι sigma b i j =
      ι ((sigma ^ (i : ℕ)) (b j)) := by
  rfl


/-!
## 2. The determinant commutes with the real embedding
-/

theorem realConjugateMatrix_det
    {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (ι : L →+* ℝ)
    (sigma : L ≃ₐ[K] L)
    (b : Module.Basis (Fin 5) K L) :
    (realConjugateMatrix ι sigma b).det =
      ι ((conjugateMatrix sigma b).det) := by

  simpa [realConjugateMatrix] using
    (RingHom.map_det
      ι
      (conjugateMatrix sigma b)).symm


/-!
## 3. Nonsingularity survives the real embedding
-/

theorem realConjugateMatrix_det_ne_zero
    {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (ι : L →+* ℝ)
    (sigma : L ≃ₐ[K] L)
    (horder : orderOf sigma = 5)
    (b : Module.Basis (Fin 5) K L) :
    (realConjugateMatrix ι sigma b).det ≠ 0 := by

  rw [realConjugateMatrix_det]

  apply (map_ne_zero ι).mpr

  exact
    conjugateMatrix_det_ne_zero
      sigma horder b


/-!
## 4. Therefore the real matrix is a unit
-/

theorem realConjugateMatrix_isUnit
    {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (ι : L →+* ℝ)
    (sigma : L ≃ₐ[K] L)
    (horder : orderOf sigma = 5)
    (b : Module.Basis (Fin 5) K L) :
    IsUnit (realConjugateMatrix ι sigma b) := by

  apply
    (Matrix.isUnit_iff_isUnit_det
      (realConjugateMatrix ι sigma b)).mpr

  exact isUnit_iff_ne_zero.mpr
    (realConjugateMatrix_det_ne_zero
      ι sigma horder b)


/-!
## 5. The corresponding real linear map
-/

noncomputable def realConjugateLinearMap
    {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (ι : L →+* ℝ)
    (sigma : L ≃ₐ[K] L)
    (b : Module.Basis (Fin 5) K L) :
    (Fin 5 → ℝ) →ₗ[ℝ] (Fin 5 → ℝ) :=
  Matrix.toLin' (realConjugateMatrix ι sigma b)


theorem realConjugateLinearMap_apply
    {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (ι : L →+* ℝ)
    (sigma : L ≃ₐ[K] L)
    (b : Module.Basis (Fin 5) K L)
    (v : Fin 5 → ℝ) :
    realConjugateLinearMap ι sigma b v =
      fun i : Fin 5 =>
        ∑ j : Fin 5,
          ι ((sigma ^ (i : ℕ)) (b j)) * v j := by
  ext i
  simp [
    realConjugateLinearMap,
    realConjugateMatrix,
    conjugateMatrix,
    Matrix.toLin'_apply',
    Matrix.mulVec,
    dotProduct
  ]


theorem realConjugateLinearMap_apply_component
    {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (ι : L →+* ℝ)
    (sigma : L ≃ₐ[K] L)
    (b : Module.Basis (Fin 5) K L)
    (v : Fin 5 → ℝ)
    (i : Fin 5) :
    realConjugateLinearMap ι sigma b v i =
      ∑ j : Fin 5,
        ι ((sigma ^ (i : ℕ)) (b j)) * v j := by
  exact congrFun
    (realConjugateLinearMap_apply ι sigma b v) i


/-!
## 6. Injectivity of the real coordinate map
-/

theorem realConjugateLinearMap_injective
    {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (ι : L →+* ℝ)
    (sigma : L ≃ₐ[K] L)
    (horder : orderOf sigma = 5)
    (b : Module.Basis (Fin 5) K L) :
    Function.Injective
      (realConjugateLinearMap ι sigma b) := by

  have hunit :
      IsUnit (realConjugateMatrix ι sigma b) :=
    realConjugateMatrix_isUnit
      ι sigma horder b

  have hcols :
      LinearIndependent ℝ
        (realConjugateMatrix ι sigma b).col :=
    Matrix.linearIndependent_cols_of_isUnit hunit

  have hmul :
      Function.Injective
        (realConjugateMatrix ι sigma b).mulVec :=
    Matrix.mulVec_injective_iff.mpr hcols

  simpa only [
    realConjugateLinearMap,
    Matrix.toLin'_apply',
    Matrix.coe_mulVecLin
  ] using hmul


/-!
## 7. Upgrade to a real linear equivalence
-/

noncomputable def realConjugateLinearEquiv
    {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (ι : L →+* ℝ)
    (sigma : L ≃ₐ[K] L)
    (horder : orderOf sigma = 5)
    (b : Module.Basis (Fin 5) K L) :
    (Fin 5 → ℝ) ≃ₗ[ℝ] (Fin 5 → ℝ) :=
  LinearEquiv.ofInjectiveEndo
    (realConjugateLinearMap ι sigma b)
    (realConjugateLinearMap_injective
      ι sigma horder b)


theorem realConjugateLinearEquiv_apply
    {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (ι : L →+* ℝ)
    (sigma : L ≃ₐ[K] L)
    (horder : orderOf sigma = 5)
    (b : Module.Basis (Fin 5) K L)
    (v : Fin 5 → ℝ) :
    realConjugateLinearEquiv ι sigma horder b v =
      realConjugateLinearMap ι sigma b v := by
  simp [realConjugateLinearEquiv]


theorem realConjugateLinearEquiv_apply_component
    {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (ι : L →+* ℝ)
    (sigma : L ≃ₐ[K] L)
    (horder : orderOf sigma = 5)
    (b : Module.Basis (Fin 5) K L)
    (v : Fin 5 → ℝ)
    (i : Fin 5) :
    realConjugateLinearEquiv ι sigma horder b v i =
      ∑ j : Fin 5,
        ι ((sigma ^ (i : ℕ)) (b j)) * v j := by
  rw [realConjugateLinearEquiv_apply]
  exact
    realConjugateLinearMap_apply_component
      ι sigma b v i


/-!
## 8. The equivalence is continuous in both directions
-/

noncomputable def realConjugateContinuousEquiv
    {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (ι : L →+* ℝ)
    (sigma : L ≃ₐ[K] L)
    (horder : orderOf sigma = 5)
    (b : Module.Basis (Fin 5) K L) :
    (Fin 5 → ℝ) ≃L[ℝ] (Fin 5 → ℝ) :=
  (realConjugateLinearEquiv
    ι sigma horder b).toContinuousLinearEquiv


theorem realConjugateContinuousEquiv_continuous
    {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (ι : L →+* ℝ)
    (sigma : L ≃ₐ[K] L)
    (horder : orderOf sigma = 5)
    (b : Module.Basis (Fin 5) K L) :
    Continuous
      (realConjugateContinuousEquiv
        ι sigma horder b) := by
  exact
    (realConjugateContinuousEquiv
      ι sigma horder b).continuous


theorem realConjugateContinuousEquiv_symm_continuous
    {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (ι : L →+* ℝ)
    (sigma : L ≃ₐ[K] L)
    (horder : orderOf sigma = 5)
    (b : Module.Basis (Fin 5) K L) :
    Continuous
      (realConjugateContinuousEquiv
        ι sigma horder b).symm := by
  exact
    (realConjugateContinuousEquiv
      ι sigma horder b).symm.continuous


/-!
## 9. The transformation is an open map
-/

theorem realConjugateContinuousEquiv_isOpenMap
    {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (ι : L →+* ℝ)
    (sigma : L ≃ₐ[K] L)
    (horder : orderOf sigma = 5)
    (b : Module.Basis (Fin 5) K L) :
    IsOpenMap
      (realConjugateContinuousEquiv
        ι sigma horder b) := by
  exact
    (realConjugateContinuousEquiv
      ι sigma horder b).toHomeomorph.isOpenMap


theorem realConjugate_image_open
    {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (ι : L →+* ℝ)
    (sigma : L ≃ₐ[K] L)
    (horder : orderOf sigma = 5)
    (b : Module.Basis (Fin 5) K L)
    (U : Set (Fin 5 → ℝ))
    (hU : IsOpen U) :
    IsOpen
      (realConjugateContinuousEquiv
        ι sigma horder b '' U) := by
  exact
    realConjugateContinuousEquiv_isOpenMap
      ι sigma horder b U hU


/-!
## 10. Open target regions have open, nonempty preimages
-/

theorem realConjugate_preimage_open
    {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (ι : L →+* ℝ)
    (sigma : L ≃ₐ[K] L)
    (horder : orderOf sigma = 5)
    (b : Module.Basis (Fin 5) K L)
    (U : Set (Fin 5 → ℝ))
    (hU : IsOpen U) :
    IsOpen
      (realConjugateContinuousEquiv
        ι sigma horder b ⁻¹' U) := by
  exact hU.preimage
    (realConjugateContinuousEquiv_continuous
      ι sigma horder b)


theorem realConjugate_preimage_nonempty
    {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (ι : L →+* ℝ)
    (sigma : L ≃ₐ[K] L)
    (horder : orderOf sigma = 5)
    (b : Module.Basis (Fin 5) K L)
    (U : Set (Fin 5 → ℝ))
    (hU : U.Nonempty) :
    (realConjugateContinuousEquiv
      ι sigma horder b ⁻¹' U).Nonempty := by

  obtain ⟨y, hy⟩ := hU

  refine
    ⟨(realConjugateContinuousEquiv
        ι sigma horder b).symm y, ?_⟩

  simpa using hy


/-!
## 11. Exact inverse identities
-/

theorem realConjugateContinuousEquiv_apply_symm
    {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (ι : L →+* ℝ)
    (sigma : L ≃ₐ[K] L)
    (horder : orderOf sigma = 5)
    (b : Module.Basis (Fin 5) K L)
    (y : Fin 5 → ℝ) :
    realConjugateContinuousEquiv ι sigma horder b
        ((realConjugateContinuousEquiv
          ι sigma horder b).symm y) =
      y := by
  exact
    (realConjugateContinuousEquiv
      ι sigma horder b).apply_symm_apply y


theorem realConjugateContinuousEquiv_symm_apply
    {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (ι : L →+* ℝ)
    (sigma : L ≃ₐ[K] L)
    (horder : orderOf sigma = 5)
    (b : Module.Basis (Fin 5) K L)
    (v : Fin 5 → ℝ) :
    (realConjugateContinuousEquiv
      ι sigma horder b).symm
        (realConjugateContinuousEquiv
          ι sigma horder b v) =
      v := by
  exact
    (realConjugateContinuousEquiv
      ι sigma horder b).symm_apply_apply v

end CyclicQuintic

namespace CyclicQuintic

noncomputable section

/-!
# Dense rational conjugate tuples and open-template selection

This module connects three ingredients:

1. rational five-tuples are dense in real five-space;
2. the real cyclic-conjugate coordinate transformation is a homeomorphism;
3. every nonempty open admissible region therefore contains a conjugate
   tuple arising from rational basis coefficients.

It also packages the sign-change argument that produces a root of the
residual cubic between two prescribed endpoints.
-/

/-!
## Block 1A: Nested five-tuples

Nested products are convenient because density follows by repeatedly using
`DenseRange.prodMap`.
-/

abbrev RatCoeffFive :=
  ℚ × (ℚ × (ℚ × (ℚ × ℚ)))

abbrev RealCoeffFive :=
  ℝ × (ℝ × (ℝ × (ℝ × ℝ)))


def castRatToReal (q : ℚ) : ℝ :=
  q


def castCoeffFive :
    RatCoeffFive → RealCoeffFive :=
  Prod.map castRatToReal
    (Prod.map castRatToReal
      (Prod.map castRatToReal
        (Prod.map castRatToReal castRatToReal)))


theorem castRatToReal_denseRange :
    DenseRange castRatToReal := by
  change DenseRange (Rat.cast : ℚ → ℝ)
  exact Rat.denseRange_cast


theorem castCoeffFive_denseRange :
    DenseRange castCoeffFive := by
  unfold castCoeffFive

  exact
    castRatToReal_denseRange.prodMap
      (castRatToReal_denseRange.prodMap
        (castRatToReal_denseRange.prodMap
          (castRatToReal_denseRange.prodMap
            castRatToReal_denseRange)))


/-!
## Block 1B: Convert nested five-tuples to functions on `Fin 5`
-/

def realCoeffFiveToFun
    (x : RealCoeffFive) :
    Fin 5 → ℝ :=
  ![
    x.1,
    x.2.1,
    x.2.2.1,
    x.2.2.2.1,
    x.2.2.2.2
  ]


def funToRealCoeffFive
    (x : Fin 5 → ℝ) :
    RealCoeffFive :=
  (
    x 0,
    (
      x 1,
      (
        x 2,
        (
          x 3,
          x 4
        )
      )
    )
  )


noncomputable def realCoeffFiveLinearEquiv :
    RealCoeffFive ≃ₗ[ℝ] (Fin 5 → ℝ) where

  toFun :=
    realCoeffFiveToFun

  invFun :=
    funToRealCoeffFive

  map_add' x y := by
    ext i
    fin_cases i <;> rfl

  map_smul' c x := by
    ext i
    fin_cases i <;> rfl

  left_inv x := by
    rcases x with ⟨x0, xrest⟩
    rcases xrest with ⟨x1, xrest⟩
    rcases xrest with ⟨x2, xrest⟩
    rcases xrest with ⟨x3, x4⟩
    rfl

  right_inv x := by
    funext i
    fin_cases i <;> rfl


noncomputable def realCoeffFiveContinuousEquiv :
    RealCoeffFive ≃L[ℝ] (Fin 5 → ℝ) :=
  realCoeffFiveLinearEquiv.toContinuousLinearEquiv


theorem realCoeffFiveContinuousEquiv_apply
    (x : RealCoeffFive) :
    realCoeffFiveContinuousEquiv x =
      realCoeffFiveToFun x := by
  rfl


theorem realCoeffFiveContinuousEquiv_continuous :
    Continuous realCoeffFiveContinuousEquiv := by
  exact realCoeffFiveContinuousEquiv.continuous


theorem realCoeffFiveContinuousEquiv_surjective :
    Function.Surjective realCoeffFiveContinuousEquiv := by
  exact realCoeffFiveContinuousEquiv.surjective


/-!
## Block 1C: Rational vectors inside `Fin 5 → ℝ`
-/

def castCoeffFiveFun
    (q : RatCoeffFive) :
    Fin 5 → ℝ :=
  realCoeffFiveToFun (castCoeffFive q)


theorem castCoeffFiveFun_eq
    (q : RatCoeffFive) :
    castCoeffFiveFun q =
      realCoeffFiveContinuousEquiv
        (castCoeffFive q) := by
  rfl


theorem castCoeffFiveFun_denseRange :
    DenseRange castCoeffFiveFun := by

  have hdense :
      DenseRange
        (realCoeffFiveContinuousEquiv ∘
          castCoeffFive) :=
    realCoeffFiveContinuousEquiv.surjective.denseRange.comp
      castCoeffFive_denseRange
      realCoeffFiveContinuousEquiv.continuous

  change DenseRange
      (fun x : RatCoeffFive =>
      realCoeffFiveContinuousEquiv (castCoeffFive x))
  exact hdense


/-!
## Block 2A: Apply the real cyclic-conjugate homeomorphism

For rational basis coefficients `q`, `rationalConjugateTuple` is the real
five-tuple obtained after multiplication by the real conjugate matrix.
-/

def rationalConjugateTuple
    {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (ι : L →+* ℝ)
    (sigma : L ≃ₐ[K] L)
    (horder : orderOf sigma = 5)
    (b : Module.Basis (Fin 5) K L)
    (q : RatCoeffFive) :
    Fin 5 → ℝ :=
  realConjugateContinuousEquiv
    ι sigma horder b
    (castCoeffFiveFun q)


theorem rationalConjugateTuple_apply
    {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (ι : L →+* ℝ)
    (sigma : L ≃ₐ[K] L)
    (horder : orderOf sigma = 5)
    (b : Module.Basis (Fin 5) K L)
    (q : RatCoeffFive)
    (i : Fin 5) :
    rationalConjugateTuple
        ι sigma horder b q i =
      ∑ j : Fin 5,
        ι ((sigma ^ (i : ℕ)) (b j)) *
          castCoeffFiveFun q j := by

  change
    realConjugateContinuousEquiv
        ι sigma horder b
        (castCoeffFiveFun q) i =
      _

  change
    realConjugateLinearEquiv
        ι sigma horder b
        (castCoeffFiveFun q) i =
      _

  exact
    realConjugateLinearEquiv_apply_component
      ι sigma horder b
      (castCoeffFiveFun q) i


theorem rationalConjugateTuple_denseRange
    {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (ι : L →+* ℝ)
    (sigma : L ≃ₐ[K] L)
    (horder : orderOf sigma = 5)
    (b : Module.Basis (Fin 5) K L) :
    DenseRange
      (rationalConjugateTuple
        ι sigma horder b) := by

  have hdense :
      DenseRange
        (realConjugateContinuousEquiv
          ι sigma horder b ∘
            castCoeffFiveFun) :=
    (realConjugateContinuousEquiv
      ι sigma horder b).surjective.denseRange.comp
        castCoeffFiveFun_denseRange
        (realConjugateContinuousEquiv
          ι sigma horder b).continuous

  change DenseRange
    (fun x : RatCoeffFive =>
      (realConjugateContinuousEquiv ι sigma horder b)
        (castCoeffFiveFun x))
  exact hdense


/-!
## Block 2B: Every nonempty open set is hit
-/

theorem rationalConjugateTuple_hits_open
    {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (ι : L →+* ℝ)
    (sigma : L ≃ₐ[K] L)
    (horder : orderOf sigma = 5)
    (b : Module.Basis (Fin 5) K L)
    (U : Set (Fin 5 → ℝ))
    (hUopen : IsOpen U)
    (hUne : U.Nonempty) :
    ∃ q : RatCoeffFive,
      rationalConjugateTuple
        ι sigma horder b q ∈ U := by

  have hdense :
      Dense
        (Set.range
          (rationalConjugateTuple
            ι sigma horder b)) :=
    rationalConjugateTuple_denseRange
      ι sigma horder b

  have hmeet :
      (U ∩
        Set.range
          (rationalConjugateTuple
            ι sigma horder b)).Nonempty :=
    (TopologicalSpace.isTopologicalBasis_opens.dense_iff.mp
      hdense)
      U hUopen hUne

  rcases hmeet with
    ⟨x, hxU, q, hq⟩

  refine ⟨q, ?_⟩

  simpa [hq] using hxU


/-!
## Block 3A: A finite family of strict inequalities

If every function in a finite family is continuous, the region on which
all of them are strictly positive is open.
-/

def finiteStrictPositiveRegion
    {X I : Type*}
    [TopologicalSpace X]
    (f : I → X → ℝ) :
    Set X :=
  {x | ∀ i, 0 < f i x}


theorem finiteStrictPositiveRegion_isOpen
    {X ι : Type*}
    [TopologicalSpace X]
    [Finite ι]
    (f : ι → X → ℝ)
    (hf : ∀ i, Continuous (f i)) :
    IsOpen (finiteStrictPositiveRegion f) := by
  rw [show
    finiteStrictPositiveRegion f =
      ⋂ i : ι, {x | 0 < f i x} by
        ext x
        simp [finiteStrictPositiveRegion]
  ]
  exact isOpen_iInter_of_finite
    (fun i =>
      isOpen_lt continuous_const (hf i))


theorem mem_finiteStrictPositiveRegion
    {X I : Type*}
    [TopologicalSpace X]
    (f : I → X → ℝ)
    (x : X) :
    x ∈ finiteStrictPositiveRegion f ↔
      ∀ i, 0 < f i x := by
  rfl


theorem finiteStrictPositiveRegion_nonempty
    {X I : Type*}
    [TopologicalSpace X]
    (f : I → X → ℝ)
    (x : X)
    (hx : ∀ i, 0 < f i x) :
    (finiteStrictPositiveRegion f).Nonempty := by
  exact ⟨x, hx⟩


/-!
## Block 3B: Rational conjugates hit every finite strict region
-/

theorem rationalConjugateTuple_hits_strict_region
    {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    {I : Type*}
    [Finite I]
    (ι : L →+* ℝ)
    (sigma : L ≃ₐ[K] L)
    (horder : orderOf sigma = 5)
    (b : Module.Basis (Fin 5) K L)
    (f : I → (Fin 5 → ℝ) → ℝ)
    (hf : ∀ i, Continuous (f i))
    (template : Fin 5 → ℝ)
    (htemplate : ∀ i, 0 < f i template) :
    ∃ q : RatCoeffFive,
      ∀ i,
        0 <
          f i
            (rationalConjugateTuple
              ι sigma horder b q) := by

  let U : Set (Fin 5 → ℝ) :=
    finiteStrictPositiveRegion f

  have hUopen : IsOpen U := by
    exact finiteStrictPositiveRegion_isOpen f hf

  have hUne : U.Nonempty := by
    exact
      finiteStrictPositiveRegion_nonempty
        f template htemplate

  obtain ⟨q, hq⟩ :=
    rationalConjugateTuple_hits_open
      ι sigma horder b U hUopen hUne

  refine ⟨q, ?_⟩

  exact hq


/-!
## Block 3C: Open sign-change regions for a residual cubic

For fixed endpoints `lo` and `hi`, the conditions

    H x lo < 0
    0 < H x hi

are strict open conditions on `x`, provided the two endpoint evaluations
depend continuously on `x`.
-/

def cubicSignChangeRegion
    {X : Type*}
    [TopologicalSpace X]
    (H : X → ℝ → ℝ)
    (lo hi : ℝ) :
    Set X :=
  {x | H x lo < 0 ∧ 0 < H x hi}


theorem cubicSignChangeRegion_isOpen
    {X : Type*}
    [TopologicalSpace X]
    (H : X → ℝ → ℝ)
    (lo hi : ℝ)
    (hloContinuous :
      Continuous (fun x => H x lo))
    (hhiContinuous :
      Continuous (fun x => H x hi)) :
    IsOpen (cubicSignChangeRegion H lo hi) := by

  exact
    (isOpen_lt
      hloContinuous
      continuous_const).and
    (isOpen_lt
      continuous_const
      hhiContinuous)


/-!
## Block 3D: A sign change produces a root strictly between the endpoints
-/

theorem exists_root_between_of_sign_change
    (F : ℝ → ℝ)
    (lo hi : ℝ)
    (hlohi : lo ≤ hi)
    (hcontinuous : Continuous F)
    (hlo : F lo < 0)
    (hhi : 0 < F hi) :
    ∃ u : ℝ,
      lo < u ∧
      u < hi ∧
      F u = 0 := by

  have hzero :
      (0 : ℝ) ∈ Set.Icc (F lo) (F hi) := by
    constructor
    · exact le_of_lt hlo
    · exact le_of_lt hhi

  rcases
      intermediate_value_Icc
        hlohi
        hcontinuous.continuousOn
        hzero
    with
      ⟨u, hu, hroot⟩

  refine ⟨u, ?_, ?_, hroot⟩

  · by_contra hnot

    have hueq : u = lo :=
      le_antisymm
        (le_of_not_gt hnot)
        hu.1

    subst u

    linarith

  · by_contra hnot

    have hueq : u = hi :=
      le_antisymm
        hu.2
        (le_of_not_gt hnot)

    subst u

    linarith


theorem cubicSignChangeRegion_has_root
    {X : Type*}
    [TopologicalSpace X]
    (H : X → ℝ → ℝ)
    (lo hi : ℝ)
    (hlohi : lo ≤ hi)
    (x : X)
    (hx : x ∈ cubicSignChangeRegion H lo hi)
    (hcontinuous : Continuous (H x)) :
    ∃ u : ℝ,
      lo < u ∧
      u < hi ∧
      H x u = 0 := by

  exact
    exists_root_between_of_sign_change
      (H x)
      lo hi
      hlohi
      hcontinuous
      hx.1
      hx.2


/-!
## Block 3E: Combine geometric positivity and cubic sign change

There are five geometric quantities:

* normalization `lambda`;
* the selected square-root branch `m + 4h`;
* `c²`;
* `a²`;
* `rho²`.

The admissible region additionally requires the residual cubic to have
opposite signs at `lo` and `hi`.
-/

def universalAdmissibleRegion
    {X : Type*}
    [TopologicalSpace X]
    (lambdaValue : X → ℝ)
    (mPlusFourH : X → ℝ)
    (cSquared : X → ℝ)
    (aSquared : X → ℝ)
    (rhoSquared : X → ℝ)
    (H : X → ℝ → ℝ)
    (lo hi : ℝ) :
    Set X :=
  {
    x |
      0 < lambdaValue x ∧
      0 < mPlusFourH x ∧
      0 < cSquared x ∧
      0 < aSquared x ∧
      0 < rhoSquared x ∧
      H x lo < 0 ∧
      0 < H x hi
  }


theorem universalAdmissibleRegion_isOpen
    {X : Type*}
    [TopologicalSpace X]
    (lambdaValue : X → ℝ)
    (mPlusFourH : X → ℝ)
    (cSquared : X → ℝ)
    (aSquared : X → ℝ)
    (rhoSquared : X → ℝ)
    (H : X → ℝ → ℝ)
    (lo hi : ℝ)
    (hlambda : Continuous lambdaValue)
    (hmPlusFourH : Continuous mPlusFourH)
    (hcSquared : Continuous cSquared)
    (haSquared : Continuous aSquared)
    (hrhoSquared : Continuous rhoSquared)
    (hHlo : Continuous (fun x => H x lo))
    (hHhi : Continuous (fun x => H x hi)) :
    IsOpen
      (universalAdmissibleRegion
        lambdaValue
        mPlusFourH
        cSquared
        aSquared
        rhoSquared
        H lo hi) := by

  have h1 :
      IsOpen {x : X | 0 < lambdaValue x} :=
    isOpen_lt continuous_const hlambda

  have h2 :
      IsOpen {x : X | 0 < mPlusFourH x} :=
    isOpen_lt continuous_const hmPlusFourH

  have h3 :
      IsOpen {x : X | 0 < cSquared x} :=
    isOpen_lt continuous_const hcSquared

  have h4 :
      IsOpen {x : X | 0 < aSquared x} :=
    isOpen_lt continuous_const haSquared

  have h5 :
      IsOpen {x : X | 0 < rhoSquared x} :=
    isOpen_lt continuous_const hrhoSquared

  have h6 :
      IsOpen {x : X | H x lo < 0} :=
    isOpen_lt hHlo continuous_const

  have h7 :
      IsOpen {x : X | 0 < H x hi} :=
    isOpen_lt continuous_const hHhi

  simpa [
    universalAdmissibleRegion,
    and_assoc
  ] using
    h1.and
      (h2.and
        (h3.and
          (h4.and
            (h5.and
              (h6.and h7)))))


/-!
## Block 3F: Master density-and-root selection theorem

This is the principal result of this mega-submission.

If the positive template belongs to the admissible open region, then some
rational basis coefficient vector produces an actual cyclic conjugate tuple
in the same region. Its residual cubic consequently has a real root between
`lo` and `hi`.
-/

theorem choose_rational_conjugates_and_cubic_root
    {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (ι : L →+* ℝ)
    (sigma : L ≃ₐ[K] L)
    (horder : orderOf sigma = 5)
    (b : Module.Basis (Fin 5) K L)
    (lambdaValue : (Fin 5 → ℝ) → ℝ)
    (mPlusFourH : (Fin 5 → ℝ) → ℝ)
    (cSquared : (Fin 5 → ℝ) → ℝ)
    (aSquared : (Fin 5 → ℝ) → ℝ)
    (rhoSquared : (Fin 5 → ℝ) → ℝ)
    (H : (Fin 5 → ℝ) → ℝ → ℝ)
    (lo hi : ℝ)
    (hlohi : lo ≤ hi)
    (hlambda : Continuous lambdaValue)
    (hmPlusFourH : Continuous mPlusFourH)
    (hcSquared : Continuous cSquared)
    (haSquared : Continuous aSquared)
    (hrhoSquared : Continuous rhoSquared)
    (hHlo : Continuous (fun x => H x lo))
    (hHhi : Continuous (fun x => H x hi))
    (hHvertical :
      ∀ x : Fin 5 → ℝ,
        Continuous (H x))
    (template : Fin 5 → ℝ)
    (htemplate :
      template ∈
        universalAdmissibleRegion
          lambdaValue
          mPlusFourH
          cSquared
          aSquared
          rhoSquared
          H lo hi) :
    ∃ q : RatCoeffFive,
    ∃ u : ℝ,
      rationalConjugateTuple
          ι sigma horder b q ∈
        universalAdmissibleRegion
          lambdaValue
          mPlusFourH
          cSquared
          aSquared
          rhoSquared
          H lo hi ∧
      lo < u ∧
      u < hi ∧
      H
        (rationalConjugateTuple
          ι sigma horder b q)
        u = 0 := by

  let U : Set (Fin 5 → ℝ) :=
    universalAdmissibleRegion
      lambdaValue
      mPlusFourH
      cSquared
      aSquared
      rhoSquared
      H lo hi

  have hUopen : IsOpen U := by
    exact
      universalAdmissibleRegion_isOpen
        lambdaValue
        mPlusFourH
        cSquared
        aSquared
        rhoSquared
        H lo hi
        hlambda
        hmPlusFourH
        hcSquared
        haSquared
        hrhoSquared
        hHlo
        hHhi

  have hUne : U.Nonempty := by
    exact ⟨template, htemplate⟩

  obtain ⟨q, hq⟩ :=
    rationalConjugateTuple_hits_open
      ι sigma horder b
      U hUopen hUne

  have hsign :
      H
          (rationalConjugateTuple
            ι sigma horder b q)
          lo < 0 ∧
        0 <
          H
            (rationalConjugateTuple
              ι sigma horder b q)
            hi := by
    exact ⟨hq.2.2.2.2.2.1, hq.2.2.2.2.2.2⟩

  obtain ⟨u, hlu, huhi, hroot⟩ :=
    exists_root_between_of_sign_change
      (H
        (rationalConjugateTuple
          ι sigma horder b q))
      lo hi
      hlohi
      (hHvertical
        (rationalConjugateTuple
          ι sigma horder b q))
      hsign.1
      hsign.2

  exact
    ⟨q, u, hq, hlu, huhi, hroot⟩

end

end CyclicQuintic


set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RMCQuintic

/-- Coordinates closed under field operations, compass square roots, and the
actual distance-one fixed-point line/circle verging constraints. -/
structure Closed (C : Subfield ℝ) : Prop where
  sqrt_mem : ∀ {x : ℝ}, x ∈ C → 0 ≤ x → Real.sqrt x ∈ C
  verge_mem : ∀ {a b c r X Y V W : ℝ},
    a ∈ C → b ∈ C → c ∈ C → r ∈ C → a ≠ 0 → 0 < r →
    V = a → (X-b)^2 + (Y-c)^2 = r^2 →
    X*W = Y*V → (X-V)^2 + (Y-W)^2 = 1 → X ∈ C ∧ Y ∈ C

/-- Every real solution of the reconstructed verging equation is obtainable
from the actual geometric operation, provided its elementary exceptions are excluded. -/
theorem verge_root_mem (C : Subfield ℝ) (hc : Closed C)
    {a b c r h z : ℝ}
    (ha : a ∈ C) (hb : b ∈ C) (hc' : c ∈ C) (hr : r ∈ C)
    (hh : h ∈ C) (ha0 : a ≠ 0) (hc0 : c ≠ 0) (hr0 : 0 < r)
    (hrel : r^2 = b^2+c^2+h)
    (hz0 : z ≠ 0) (hz1 : z ≠ 1)
    (hz : ((z^2-h)*(z-1)-2*a*b*z)^2 + 4*a^2*c^2*z^2
      - 4*c^2*z^2*(z-1)^2 = 0) : z ∈ C := by
  let X := a*z/(z-1)
  let Y := (z^2-h-2*b*X)/(2*c)
  have hd : z-1 ≠ 0 := sub_ne_zero.mpr hz1
  have hs : X^2+Y^2 = z^2 := by
    dsimp [X, Y]
    field_simp [hd, hc0]
    nlinarith [hz]
  have hy : 2*c*Y = z^2-h-2*b*X := by
    dsimp [Y]
    field_simp
  have hcircle : (X-b)^2+(Y-c)^2=r^2 := by
    nlinarith [hs, hrel]
  have hv : ((z-1)/z)*X = a := by
    dsimp [X]
    field_simp [hz0, hd]
  have hcol : X*(((z-1)/z)*Y) = Y*(((z-1)/z)*X) := by ring
  have hdist : (X-((z-1)/z)*X)^2+(Y-((z-1)/z)*Y)^2=1 := by
    field_simp [hz0]
    nlinarith [hs]
  obtain ⟨hX, _⟩ := hc.verge_mem ha hb hc' hr ha0 hr0 hv hcircle hcol hdist
  have hxsub : X-a ≠ 0 := by
    dsimp [X]
    intro H
    have heq : a*z = a*(z-1) := (div_eq_iff hd).mp (sub_eq_zero.mp H)
    apply ha0
    nlinarith
  have hrecover : z = X/(X-a) := by
    apply (eq_div_iff hxsub).2
    dsimp [X]
    field_simp [hd]
    ring
  rw [hrecover]
  exact C.div_mem hX (C.sub_mem hX ha)

/-- Reconstruction using only field operations and three positive square roots. -/
theorem sextic_root_mem (C : Subfield ℝ) (hc : Closed C)
    {v2 v3 v4 v5 h z : ℝ}
    (h2 : v2 ∈ C) (h3 : v3 ∈ C) (h4 : v4 ∈ C) (hh : h ∈ C)
    (hh0 : h ≠ 0)
    (h5 : v5 = -(2-2*v2-v3)*h-2*h^2)
    (hq : 0 < (v3-(2-2*v2-v3)-4*h)/8)
    (hA : 0 < (v4-(h+(2-2*v2-v3)/2)^2+2*h+
      4*((v3-(2-2*v2-v3)-4*h)/8))/(4*((v3-(2-2*v2-v3)-4*h)/8)))
    (hr : 0 < h+(2-2*v2-v3)^2/(16*((v4-(h+(2-2*v2-v3)/2)^2+2*h+
      4*((v3-(2-2*v2-v3)-4*h)/8))/(4*((v3-(2-2*v2-v3)-4*h)/8))))+
      (v3-(2-2*v2-v3)-4*h)/8)
    (hz : z^6-2*z^5+v2*z^4+v3*z^3+v4*z^2+v5*z+h^2=0) : z ∈ C := by
  let m := 2-2*v2-v3
  let q := (v3-m-4*h)/8
  let A := (v4-(h+m/2)^2+2*h+4*q)/(4*q)
  let a := Real.sqrt A
  let c := Real.sqrt q
  let b := m/(4*a)
  let r := Real.sqrt (h+m^2/(16*A)+q)
  have hm : m ∈ C := by dsimp [m]; exact C.sub_mem (C.sub_mem (by norm_num) (C.mul_mem (by norm_num) h2)) h3
  have hqm : q ∈ C := by
    dsimp [q]
    exact C.div_mem (C.sub_mem (C.sub_mem h3 hm) (C.mul_mem (by norm_num) hh)) (by norm_num)
  have hAm : A ∈ C := by
    dsimp [A]
    exact C.div_mem (C.add_mem (C.add_mem (C.sub_mem h4 (C.pow_mem (C.add_mem hh (C.div_mem hm (by norm_num))) 2))
      (C.mul_mem (by norm_num) hh)) (C.mul_mem (by norm_num) hqm)) (C.mul_mem (by norm_num) hqm)
  have hq0 : 0 < q := hq
  have hA0 : 0 < A := hA
  have ha0 : 0 < a := Real.sqrt_pos.2 hA0
  have hc0 : 0 < c := Real.sqrt_pos.2 hq0
  have ha2 : a^2=A := Real.sq_sqrt (le_of_lt hA0)
  have hc2 : c^2=q := Real.sq_sqrt (le_of_lt hq0)
  have ham : a ∈ C := hc.sqrt_mem hAm (le_of_lt hA0)
  have hcm : c ∈ C := hc.sqrt_mem hqm (le_of_lt hq0)
  have hbm : b ∈ C := C.div_mem hm (C.mul_mem (by norm_num) ham)
  have hrm : r ∈ C := hc.sqrt_mem
    (C.add_mem (C.add_mem hh (C.div_mem (C.pow_mem hm 2) (C.mul_mem (by norm_num) hAm))) hqm) (le_of_lt hr)
  have hr0 : 0 < r := Real.sqrt_pos.2 hr
  have hab : 4*a*b=m := by dsimp [b]; field_simp
  have hb2 : b^2=m^2/(16*A) := by
    dsimp [b]
    rw [div_pow]
    congr 1
    nlinarith [ha2]
  have hrr : r^2=b^2+c^2+h := by
    rw [hb2, hc2, Real.sq_sqrt (le_of_lt hr)]
    ring
  have hv3 : v3=4*a*b+4*h+8*c^2 := by rw [hc2]; dsimp [q]; nlinarith [hab]
  have hv2 : v2=1-4*a*b-2*h-4*c^2 := by
    rw [hc2]
    dsimp [q, m] at *
    nlinarith [hab]
  have hv4 : v4=(h+2*a*b)^2-2*h-4*c^2+4*a^2*c^2 := by
    rw [ha2, hc2]
    have hab' : 2*a*b=m/2 := by linarith [hab]
    rw [hab']
    dsimp [A]
    field_simp
    ring
  have hv5 : v5=-4*a*b*h-2*h^2 := by rw [h5]; nlinarith [hab]
  have hgeom : ((z^2-h)*(z-1)-2*a*b*z)^2+4*a^2*c^2*z^2-
      4*c^2*z^2*(z-1)^2=0 := by
    rw [hv2, hv3, hv4, hv5] at hz
    nlinarith only [hz]
  have hz0 : z ≠ 0 := by
    intro H
    subst z
    simp only [zero_pow (by omega : 6 ≠ 0), zero_pow (by omega : 5 ≠ 0),
      zero_pow (by omega : 4 ≠ 0), zero_pow (by omega : 3 ≠ 0), zero_pow (by omega : 2 ≠ 0),
      mul_zero, sub_zero, zero_add] at hz
    exact hh0 (eq_zero_of_pow_eq_zero hz)
  have hz1 : z ≠ 1 := by
    intro H
    subst z
    nlinarith [sq_nonneg (2*a*b), mul_pos (sq_pos_of_pos ha0) (sq_pos_of_pos hc0)]
  exact verge_root_mem C hc ham hbm hcm hrm hh (ne_of_gt ha0) (ne_of_gt hc0)
    hr0 hrr hz0 hz1 hgeom

end RMCQuintic


namespace RMCQuintic

/-- A real square root with either sign is available by compass construction. -/
theorem square_mem (C : Subfield ℝ) (hc : Closed C) {x : ℝ}
    (hx : x^2 ∈ C) : x ∈ C := by
  have ha : |x| ∈ C := by
    rw [← Real.sqrt_sq_eq_abs]
    exact hc.sqrt_mem hx (sq_nonneg x)
  rcases le_total 0 x with hp | hn
  · simpa [abs_of_nonneg hp] using ha
  · have := C.neg_mem ha
    simpa [abs_of_nonpos hn] using this

/-- Depressed cubic with nonzero linear coefficient, using actual line/circle verging. -/
theorem depressed_nonzero_mem (C : Subfield ℝ) (hc : Closed C)
    {p q u : ℝ} (hp : p ∈ C) (hq : q ∈ C) (hp0 : p ≠ 0)
    (hu : u^3+p*u+q=0) : u ∈ C := by
  by_cases hq0 : q=0
  · rw [hq0] at hu
    have hf : u*(u^2+p)=0 := by nlinarith only [hu]
    rcases mul_eq_zero.mp hf with hz | hs
    · rw [hz]; exact C.zero_mem
    · apply square_mem C hc
      have he : u^2 = -p := by linarith
      rw [he]
      exact C.neg_mem hp
  obtain ⟨n, hn⟩ := exists_nat_gt (|u|+|p|+3)
  let N : ℝ := n
  have hN : 0 < N := by dsimp [N]; linarith [abs_nonneg u, abs_nonneg p]
  have hNu : |u| < N := by dsimp [N]; linarith [abs_nonneg p]
  have hNp : |p|+2 < N := by dsimp [N]; linarith [abs_nonneg u]
  have hNm : N ∈ C := by dsimp [N]; exact natCast_mem C n
  let v := u/N
  let p' := p/N^2
  let q' := q/N^3
  have hN0 := ne_of_gt hN
  have hvabs : |v| < 1 := by
    dsimp [v]
    rw [abs_div, abs_of_pos hN]
    exact (div_lt_one hN).2 hNu
  have hv2 : v^2 < 1 := by
    have hvb := abs_lt.mp hvabs
    nlinarith [mul_pos (by linarith : 0 < 1-v) (by linarith : 0 < 1+v)]
  have hp' : p' ∈ C := C.div_mem hp (C.pow_mem hNm 2)
  have hq' : q' ∈ C := C.div_mem hq (C.pow_mem hNm 3)
  have hp'0 : p' ≠ 0 := div_ne_zero hp0 (pow_ne_zero _ hN0)
  have hq'0 : q' ≠ 0 := div_ne_zero hq0 (pow_ne_zero _ hN0)
  have hvroot : v^3+p'*v+q'=0 := by
    dsimp [v, p', q']
    field_simp [hN0]
    nlinarith only [hu]
  have hv0 : v ≠ 0 := by
    intro H
    rw [H] at hvroot
    simp at hvroot
    exact hq'0 hvroot
  have hpbound : -1/2 < p' := by
    dsimp [p']
    apply (lt_div_iff₀ (sq_pos_of_pos hN)).2
    have hb : 2*|p| < N^2 := by nlinarith [sq_nonneg (N-1), abs_nonneg p]
    nlinarith [neg_abs_le p]
  let a := 2*q'/p'
  let b := -a/p'
  let h := 1+2*a^2/p'
  let r := Real.sqrt (b^2+h)
  have ha : a ∈ C := C.div_mem (C.mul_mem (by norm_num) hq') hp'
  have hb : b ∈ C := C.div_mem (C.neg_mem ha) hp'
  have hh : h ∈ C := C.add_mem (by norm_num)
    (C.div_mem (C.mul_mem (by norm_num) (C.pow_mem ha 2)) hp')
  have ha0 : a ≠ 0 := div_ne_zero (mul_ne_zero (by norm_num) hq'0) hp'0
  have hrExpr : b^2+h=1+a^2*(1+2*p')/p'^2 := by
    dsimp [b, h]
    field_simp
    ring
  have hrpos : 0 < b^2+h := by
    rw [hrExpr]
    have : 0 ≤ a^2*(1+2*p')/p'^2 := div_nonneg
      (mul_nonneg (sq_nonneg a) (by linarith)) (sq_nonneg p')
    linarith
  have hrm : r ∈ C := hc.sqrt_mem (C.add_mem (C.pow_mem hb 2) hh) (le_of_lt hrpos)
  have hr0 : 0 < r := Real.sqrt_pos.2 hrpos
  have hr2 : r^2=b^2+h := Real.sq_sqrt (le_of_lt hrpos)
  let X := v+a
  by_cases hX0 : X=0
  · have hu' : u = -N*a := by
      dsimp [X, v] at hX0
      have hv : u/N = -a := by linarith
      have := (div_eq_iff hN0).mp hv
      nlinarith only [this]
    rw [hu']
    exact C.mul_mem (C.neg_mem hNm) ha
  have hfact : v^2*(h+2*b*X)-X^2=(-2*a/p')*(v^3+p'*v+q') := by
    dsimp [X, h, b, a]
    field_simp [hp'0]
    ring
  have hpower : h+2*b*X=X^2/v^2 := by
    apply (eq_div_iff (pow_ne_zero _ hv0)).2
    rw [hvroot, mul_zero] at hfact
    nlinarith only [hfact]
  let Y := Real.sqrt (X^2*(1/v^2-1))
  have hrad : 0 ≤ X^2*(1/v^2-1) := by
    apply mul_nonneg (sq_nonneg X)
    have : 1 ≤ 1/v^2 := (le_div_iff₀ (sq_pos_of_ne_zero hv0)).2 (by nlinarith)
    linarith
  have hY2 : Y^2=X^2*(1/v^2-1) := Real.sq_sqrt hrad
  have hs : X^2+Y^2=X^2/v^2 := by rw [hY2]; ring
  have hcircle : (X-b)^2+(Y-0)^2=r^2 := by
    rw [hr2]
    nlinarith only [hs, hpower]
  have hline : (a/X)*X=a := by field_simp [hX0]
  have hcol : X*((a/X)*Y)=Y*((a/X)*X) := by ring
  have hdist : (X-(a/X)*X)^2+(Y-(a/X)*Y)^2=1 := by
    have hvX : X-a=v := by dsimp [X]; ring
    have hs' : v^2*(X^2+Y^2)=X^2 := by rw [hs]; field_simp [hv0]
    field_simp [hX0]
    nlinarith only [hs', hvX]
  obtain ⟨hXm, _⟩ := hc.verge_mem ha hb (C.zero_mem) hrm ha0 hr0
    hline hcircle hcol hdist
  have hu' : u=N*(X-a) := by dsimp [X, v]; field_simp; ring
  rw [hu']
  exact C.mul_mem hNm (C.sub_mem hXm ha)

/-- Every real depressed cubic root is constructible in the stated geometric model. -/
theorem depressed_mem (C : Subfield ℝ) (hc : Closed C)
    {p q u : ℝ} (hp : p ∈ C) (hq : q ∈ C)
    (hu : u^3+p*u+q=0) : u ∈ C := by
  by_cases hp0 : p=0
  · by_cases hq0 : q=0
    · rw [hp0, hq0] at hu
      have : u=0 := by simpa using eq_zero_of_pow_eq_zero (by simpa using hu : u^3=0)
      rw [this]
      exact C.zero_mem
    let y := u^2+u
    have hy : y^3+(3*q)*y+(q-q^2)=0 := by
      have hu' : u^3 = -q := by rw [hp0] at hu; nlinarith only [hu]
      dsimp [y]
      have heq : (u^2+u)^3+3*q*(u^2+u)+(q-q^2)=
        (u^3+q)*(u^3+3*u^2+3*u+1-q) := by ring
      rw [heq, hu']
      ring
    have hym : y ∈ C := depressed_nonzero_mem C hc
      (C.mul_mem (by norm_num) hq) (C.sub_mem hq (C.pow_mem hq 2))
      (mul_ne_zero (by norm_num) hq0) hy
    have hypos : 0 < y+1 := by dsimp [y]; nlinarith [sq_nonneg (u+1/2)]
    have hrecovery : u=(y-q)/(y+1) := by
      apply (eq_div_iff (ne_of_gt hypos)).2
      dsimp [y]
      rw [hp0] at hu
      nlinarith only [hu]
    rw [hrecovery]
    exact C.div_mem (C.sub_mem hym hq) (C.add_mem hym (C.one_mem))
  · exact depressed_nonzero_mem C hc hp hq hp0 hu

/-- No algebraic-root constructor is assumed: this follows from distance-one verging. -/
theorem cubic_mem (C : Subfield ℝ) (hc : Closed C)
    {b0 b1 b2 b3 u : ℝ}
    (h0 : b0 ∈ C) (h1 : b1 ∈ C) (h2 : b2 ∈ C) (h3 : b3 ∈ C)
    (h30 : b3 ≠ 0) (hu : b0+b1*u+b2*u^2+b3*u^3=0) : u ∈ C := by
  let B := b2/b3
  let v := u+B/3
  let p := b1/b3-B^2/3
  let q := 2*B^3/27-B*b1/(3*b3)+b0/b3
  have hB : B ∈ C := C.div_mem h2 h3
  have hp : p ∈ C := C.sub_mem (C.div_mem h1 h3) (C.div_mem (C.pow_mem hB 2) (by norm_num))
  have hq : q ∈ C := C.add_mem
    (C.sub_mem (C.div_mem (C.mul_mem (by norm_num) (C.pow_mem hB 3)) (by norm_num))
      (C.div_mem (C.mul_mem hB h1) (C.mul_mem (by norm_num) h3))) (C.div_mem h0 h3)
  have hv : v^3+p*v+q=0 := by
    have heq : v^3+p*v+q=(b0+b1*u+b2*u^2+b3*u^3)/b3 := by
      dsimp [v, p, q, B]
      field_simp [h30]
      ring
    rw [heq, hu, zero_div]
  have hvm := depressed_mem C hc hp hq hv
  have heq : u=v-B/3 := by dsimp [v]; ring
  rw [heq]
  exact C.sub_mem hvm (C.div_mem hB (by norm_num))

end RMCQuintic


set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RMCQuintic

noncomputable section

variable {F : Type*} [Field F] [CharZero F]
set_option linter.unusedSimpArgs false
def e1 {F : Type*} [CommRing F] (x : Fin 5 → F) : F := x 0 + x 1 + x 2 + x 3 + x 4
def e2 {F : Type*} [CommRing F] (x : Fin 5 → F) : F := x 0*x 1 + x 0*x 2 + x 0*x 3 + x 0*x 4 + x 1*x 2 + x 1*x 3 + x 1*x 4 + x 2*x 3 + x 2*x 4 + x 3*x 4
def e3 {F : Type*} [CommRing F] (x : Fin 5 → F) : F := x 0*x 1*x 2 + x 0*x 1*x 3 + x 0*x 1*x 4 + x 0*x 2*x 3 + x 0*x 2*x 4 + x 0*x 3*x 4 + x 1*x 2*x 3 + x 1*x 2*x 4 + x 1*x 3*x 4 + x 2*x 3*x 4
def e4 {F : Type*} [CommRing F] (x : Fin 5 → F) : F := x 0*x 1*x 2*x 3 + x 0*x 1*x 2*x 4 + x 0*x 1*x 3*x 4 + x 0*x 2*x 3*x 4 + x 1*x 2*x 3*x 4
def e5 {F : Type*} [CommRing F] (x : Fin 5 → F) : F := x 0*x 1*x 2*x 3*x 4

def rot {F : Type*} [CommRing F] (x : Fin 5 → F) : Fin 5 → F := ![x 1, x 2, x 3, x 4, x 0]
def g {F : Type*} [CommRing F] (x : Fin 5 → F) (u : F) : Fin 5 → F := fun i => 1+u*x i
def adjacent {F : Type*} [CommRing F] (x : Fin 5 → F) : Fin 5 → F :=
  ![x 0*x 1, x 1*x 2, x 2*x 3, x 3*x 4, x 4*x 0]
def beta {F : Type*} [CommRing F] (x : Fin 5 → F) (u : F) := adjacent (g x u)
def triples {F : Type*} [CommRing F] (x : Fin 5 → F) : F :=
  x 0*x 1*x 2+x 1*x 2*x 3+x 2*x 3*x 4+x 3*x 4*x 0+x 4*x 0*x 1
def cyclicV {F : Type*} [CommRing F] (x : Fin 5 → F) : F :=
  x 0*(x 1)^2*x 2+x 1*(x 2)^2*x 3+x 2*(x 3)^2*x 4+
  x 3*(x 4)^2*x 0+x 4*(x 0)^2*x 1
def cyclicA32 {F : Type*} [CommRing F] (x : Fin 5 → F) : F :=
  (x 0)^3*(x 1)^2+(x 0)^2*(x 1)^3 +
  (x 1)^3*(x 2)^2+(x 1)^2*(x 2)^3 +
  (x 2)^3*(x 3)^2+(x 2)^2*(x 3)^3 +
  (x 3)^3*(x 4)^2+(x 3)^2*(x 4)^3 +
  (x 4)^3*(x 0)^2+(x 4)^2*(x 0)^3
def cyclicA33 {F : Type*} [CommRing F] (x : Fin 5 → F) : F :=
  (x 0)^3*(x 1)^3 + (x 1)^3*(x 2)^3 + (x 2)^3*(x 3)^3 + (x 3)^3*(x 4)^3 + (x 4)^3*(x 0)^3

def t {F : Type*} [CommRing F] (x : Fin 5 → F) := e1 (adjacent x)
def C0 {F : Type*} [CommRing F] (x : Fin 5 → F) := 4*((t x)^2-4*cyclicV x)
def C1 {F : Type*} [CommRing F] (x : Fin 5 → F) := 4*cyclicA32 x-2*e1 x*(t x)^2+
  2*t x*(triples x+e3 x)+4*e1 x*e4 x+4*e5 x
def C2 (x : Fin 5 → F) := (4*cyclicA33 x-(t x)^3)/3+
  2*t x*e4 x+4*e1 x*e5 x
def C3 {F : Type*} [CommRing F] (x : Fin 5 → F) := 2*t x*e5 x
def H (x : Fin 5 → F) (u : F) := C0 x+C1 x*u+C2 x*u^2+C3 x*u^3

def P {F : Type*} [CommRing F] (x : Fin 5 → F) (u : F) := e5 (g x u)
def T {F : Type*} [CommRing F] (x : Fin 5 → F) (u : F) := e1 (beta x u)
def D {F : Type*} [CommRing F] (x : Fin 5 → F) (u : F) := T x u+1
def R {F : Type*} [CommRing F] (x : Fin 5 → F) (u : F) := triples (g x u)
def lam (x : Fin 5 → F) (u : F) := 2/D x u

def a2 (x : Fin 5 → F) (u : F) := (lam x u)^2*(e2 (beta x u)+T x u)
def a3 (x : Fin 5 → F) (u : F) := -(lam x u)^3*(e3 (beta x u)+e2 (beta x u))
def a4 (x : Fin 5 → F) (u : F) := (lam x u)^4*(e4 (beta x u)+e3 (beta x u))
def a5 (x : Fin 5 → F) (u : F) := -(lam x u)^5*(e5 (beta x u)+e4 (beta x u))
def h (x : Fin 5 → F) (u : F) := -(lam x u)^3*P x u
def m (x : Fin 5 → F) (u : F) := 2-2*a2 x u-a3 x u
def cSq (x : Fin 5 → F) (u : F) := (a3 x u-m x u-4*h x u)/8
def aSq (x : Fin 5 → F) (u : F) :=
  (a4 x u-(h x u+m x u/2)^2+2*h x u+4*cSq x u)/(4*cSq x u)
def rSq (x : Fin 5 → F) (u : F) :=
  h x u+(m x u)^2/(16*aSq x u)+cSq x u

theorem adjacent_e5 (x : Fin 5 → F) : e5 (adjacent x) = (e5 x)^2 := by
  norm_num [e5, adjacent, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one]
  ring

theorem adjacent_e4 (x : Fin 5 → F) : e4 (adjacent x) = e5 x*triples x := by
  norm_num [e4, e5, triples, adjacent, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one]
  ring

theorem residual_identity (x : Fin 5 → F) (u : F) :
    (D x u)^3-4*(e2 (beta x u)+T x u)*D x u+
    4*(e3 (beta x u)+e2 (beta x u))+2*(P x u+R x u)*D x u-8*P x u =
    u^4*H x u := by
  norm_num [D, T, P, R, beta, g, H, C0, C1, C2, C3, t,
    e1, e2, e3, e4, e5, adjacent, triples, cyclicV, cyclicA32, cyclicA33,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one]
  ring

theorem C0_rot (x : Fin 5 → F) : C0 (rot x) = C0 x := by
  norm_num [C0, C0, C1, C2, C3, t, e1, e2, e3, e4, e5, rot,
    adjacent, triples, cyclicV, cyclicA32, cyclicA33,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one]
  ring

theorem C1_rot (x : Fin 5 → F) : C1 (rot x) = C1 x := by
  norm_num [C1, C0, C1, C2, C3, t, e1, e2, e3, e4, e5, rot,
    adjacent, triples, cyclicV, cyclicA32, cyclicA33,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one]
  ring

theorem C2_rot (x : Fin 5 → F) : C2 (rot x) = C2 x := by
  norm_num [C2, C0, C1, C2, C3, t, e1, e2, e3, e4, e5, rot,
    adjacent, triples, cyclicV, cyclicA32, cyclicA33,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one]
  ring

theorem C3_rot (x : Fin 5 → F) : C3 (rot x) = C3 x := by
  norm_num [C3, C0, C1, C2, C3, t, e1, e2, e3, e4, e5, rot,
    adjacent, triples, cyclicV, cyclicA32, cyclicA33,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one]
  ring

theorem e1_rot {F : Type*} [CommRing F] (x : Fin 5 → F) : e1 (rot x) = e1 x := by
  norm_num [e1, C0, C1, C2, C3, t, e1, e2, e3, e4, e5, rot,
    adjacent, triples, cyclicV, cyclicA32, cyclicA33,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one]
  ring

theorem e2_rot {F : Type*} [CommRing F] (x : Fin 5 → F) : e2 (rot x) = e2 x := by
  norm_num [e2, C0, C1, C2, C3, t, e1, e2, e3, e4, e5, rot,
    adjacent, triples, cyclicV, cyclicA32, cyclicA33,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one]
  ring

theorem e3_rot {F : Type*} [CommRing F] (x : Fin 5 → F) : e3 (rot x) = e3 x := by
  norm_num [e3, C0, C1, C2, C3, t, e1, e2, e3, e4, e5, rot,
    adjacent, triples, cyclicV, cyclicA32, cyclicA33,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one]
  ring

theorem e4_rot {F : Type*} [CommRing F] (x : Fin 5 → F) : e4 (rot x) = e4 x := by
  norm_num [e4, C0, C1, C2, C3, t, e1, e2, e3, e4, e5, rot,
    adjacent, triples, cyclicV, cyclicA32, cyclicA33,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one]
  ring

theorem e5_rot {F : Type*} [CommRing F] (x : Fin 5 → F) : e5 (rot x) = e5 x := by
  norm_num [e5, C0, C1, C2, C3, t, e1, e2, e3, e4, e5, rot,
    adjacent, triples, cyclicV, cyclicA32, cyclicA33,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one]
  ring


theorem beta_rot {F : Type*} [CommRing F] (x : Fin 5 → F) (u : F) :
    beta (rot x) u = rot (beta x u) := by
  ext i
  fin_cases i <;> simp [beta, g, adjacent, rot]

theorem g_rot {F : Type*} [CommRing F] (x : Fin 5 → F) (u : F) :
    g (rot x) u = rot (g x u) := by
  ext i
  fin_cases i <;> simp [g, rot]

theorem e1_map {F G : Type*} [CommRing F] [CommRing G]
    (f : F →+* G) (x : Fin 5 → F) : f (e1 x) = e1 (fun i => f (x i)) := by
  simp [e1, C0, C1, C2, C3, t, e1, e2, e3, e4, e5,
    adjacent, triples, cyclicV, cyclicA32, cyclicA33, map_ofNat]

theorem e2_map {F G : Type*} [CommRing F] [CommRing G]
    (f : F →+* G) (x : Fin 5 → F) : f (e2 x) = e2 (fun i => f (x i)) := by
  simp [e2, C0, C1, C2, C3, t, e1, e2, e3, e4, e5,
    adjacent, triples, cyclicV, cyclicA32, cyclicA33, map_ofNat]

theorem e3_map {F G : Type*} [CommRing F] [CommRing G]
    (f : F →+* G) (x : Fin 5 → F) : f (e3 x) = e3 (fun i => f (x i)) := by
  simp [e3, C0, C1, C2, C3, t, e1, e2, e3, e4, e5,
    adjacent, triples, cyclicV, cyclicA32, cyclicA33, map_ofNat]

theorem e4_map {F G : Type*} [CommRing F] [CommRing G]
    (f : F →+* G) (x : Fin 5 → F) : f (e4 x) = e4 (fun i => f (x i)) := by
  simp [e4, C0, C1, C2, C3, t, e1, e2, e3, e4, e5,
    adjacent, triples, cyclicV, cyclicA32, cyclicA33, map_ofNat]

theorem e5_map {F G : Type*} [CommRing F] [CommRing G]
    (f : F →+* G) (x : Fin 5 → F) : f (e5 x) = e5 (fun i => f (x i)) := by
  simp [e5, C0, C1, C2, C3, t, e1, e2, e3, e4, e5,
    adjacent, triples, cyclicV, cyclicA32, cyclicA33, map_ofNat]

theorem C0_map {F G : Type*} [Field F] [Field G] [CharZero F] [CharZero G]
    (f : F →+* G) (x : Fin 5 → F) : f (C0 x) = C0 (fun i => f (x i)) := by
  norm_num [C0, C0, C1, C2, C3, t, e1, e2, e3, e4, e5,
    adjacent, triples, cyclicV, cyclicA32, cyclicA33, map_ofNat]

theorem C1_map {F G : Type*} [Field F] [Field G] [CharZero F] [CharZero G]
    (f : F →+* G) (x : Fin 5 → F) : f (C1 x) = C1 (fun i => f (x i)) := by
  norm_num [C1, C0, C1, C2, C3, t, e1, e2, e3, e4, e5,
    adjacent, triples, cyclicV, cyclicA32, cyclicA33, map_ofNat]

theorem C2_map {F G : Type*} [Field F] [Field G] [CharZero F] [CharZero G]
    (f : F →+* G) (x : Fin 5 → F) : f (C2 x) = C2 (fun i => f (x i)) := by
  norm_num [C2, C0, C1, C2, C3, t, e1, e2, e3, e4, e5,
    adjacent, triples, cyclicV, cyclicA32, cyclicA33, map_ofNat]

theorem C3_map {F G : Type*} [Field F] [Field G] [CharZero F] [CharZero G]
    (f : F →+* G) (x : Fin 5 → F) : f (C3 x) = C3 (fun i => f (x i)) := by
  norm_num [C3, C0, C1, C2, C3, t, e1, e2, e3, e4, e5,
    adjacent, triples, cyclicV, cyclicA32, cyclicA33, map_ofNat]

theorem beta_map {F G : Type*} [CommRing F] [CommRing G]
    (f : F →+* G) (x : Fin 5 → F) (u : F) :
    (fun i => f (beta x u i)) = beta (fun i => f (x i)) (f u) := by
  ext i
  fin_cases i <;> simp [beta, g, adjacent]

theorem g_map {F G : Type*} [CommRing F] [CommRing G]
    (f : F →+* G) (x : Fin 5 → F) (u : F) :
    (fun i => f (g x u i)) = g (fun i => f (x i)) (f u) := by
  ext i
  simp [g]

theorem signed_obstruction (x : Fin 5 → F) (u : F) (hD : D x u ≠ 0) :
    a5 x u+m x u*h x u+2*(h x u)^2 =
    -16*P x u*u^4*H x u/(D x u)^6 := by
  have hi := residual_identity x u
  have he5 := adjacent_e5 (g x u)
  have he4 := adjacent_e4 (g x u)
  change e5 (beta x u)=(P x u)^2 at he5
  change e4 (beta x u)=P x u*R x u at he4
  norm_num [a5, m, a2, a3, h, lam]
  rw [he5, he4]
  field_simp [hD]
  linear_combination -16*P x u*hi

def sextic (x : Fin 5 → F) (u z : F) :=
  z^6-2*z^5+a2 x u*z^4+a3 x u*z^3+a4 x u*z^2+a5 x u*z+(h x u)^2

theorem sextic_factor (x : Fin 5 → F) (u z : F) (hD : D x u ≠ 0) :
    sextic x u z = (z-lam x u)*
      ((z-lam x u*beta x u 0)*(z-lam x u*beta x u 1)*
       (z-lam x u*beta x u 2)*(z-lam x u*beta x u 3)*(z-lam x u*beta x u 4)) := by
  have he5 := adjacent_e5 (g x u)
  change e5 (beta x u)=(P x u)^2 at he5
  have hsum : lam x u*(T x u+1)=2 := by dsimp [D] at hD; dsimp [lam, D]; field_simp [hD]
  dsimp [sextic, a2, a3, a4, a5, h]
  simp only [mul_pow, neg_sq, pow_mul]
  rw [← he5]
  dsimp [T, e1, e2, e3, e4, e5] at *
  linear_combination z^5*hsum

theorem beta_sextic_root (x : Fin 5 → F) (u : F) (hD : D x u ≠ 0) (i : Fin 5) :
    sextic x u (lam x u*beta x u i)=0 := by
  rw [sextic_factor x u _ hD]
  fin_cases i <;> simp

def template : Fin 5 → ℝ := ![-3,-1,1,4,2]
def lo : ℝ := -167710/100000
def hi : ℝ := -167709/100000

theorem template_residual (u : ℝ) : H template u=24*(16*u^3+33*u^2+33*u+38) := by
  norm_num [H, C0, C1, C2, C3, t, template, e1, e2, e3, e4, e5,
    adjacent, triples, cyclicV, cyclicA32, cyclicA33]
  ring

theorem template_signs : H template lo < 0 ∧ 0 < H template hi := by
  rw [template_residual, template_residual]
  norm_num [lo, hi]

theorem template_good (u : ℝ) (hlo : lo ≤ u) (hhi : u ≤ hi) :
    0 < D template u ∧ P template u < 0 ∧
    0 < cSq template u ∧ 0 < aSq template u ∧ 0 < rSq template u := by
  have hloR : ((-167710/100000:ℚ):ℝ) ≤ u := by norm_num [lo] at *; exact hlo
  have hhiR : u ≤ ((-167709/100000:ℚ):ℝ) := by norm_num [hi] at *; exact hhi
  have hD : D template u ∈ Set.Icc (((288098/15625:ℚ):ℝ)) (((18438951/1000000:ℚ):ℝ)) := by
    dsimp [D, T, e1, beta, adjacent, g, template]
    dyadic_interval [prec := 64]
  have hP : P template u ∈ Set.Icc (((-918261/6250:ℚ):ℝ)) (((-36729003/250000:ℚ):ℝ)) := by
    dsimp [P, e5, g, template]
    dyadic_interval [prec := 64]
  have hT : T template u ∈ Set.Icc (((272473/15625:ℚ):ℝ)) (((17438951/1000000:ℚ):ℝ)) := by
    dsimp [T, e1, beta, adjacent, g, template]
    dyadic_interval [prec := 64]
  have hE2 : e2 (beta template u) ∈ Set.Icc (((-89262429/500000:ℚ):ℝ)) (((-178500467/1000000:ℚ):ℝ)) := by
    dsimp [e2, beta, adjacent, g, template]
    dyadic_interval [prec := 64]
  have hE3 : e3 (beta template u) ∈ Set.Icc (((-901421453/250000:ℚ):ℝ)) (((-1802694241/500000:ℚ):ℝ)) := by
    dsimp [e3, beta, adjacent, g, template]
    dyadic_interval [prec := 64]
  have hE4 : e4 (beta template u) ∈ Set.Icc (((-4901290439/1000000:ℚ):ℝ)) (((-76562151/15625:ℚ):ℝ)) := by
    dsimp [e4, beta, adjacent, g, template]
    dyadic_interval [prec := 64]
  have hD0 : 0 < D template u := by have := hD.1; norm_num at this ⊢; linarith
  have hL : lam template u ∈ Set.Icc (((13557/125000:ℚ):ℝ)) (((108481/1000000:ℚ):ℝ)) := by
    unfold lam
    constructor
    · apply (le_div_iff₀ hD0).2
      nlinarith [hD.2]
    · apply (div_le_iff₀ hD0).2
      nlinarith [hD.1]
  have h2 : a2 template u ∈ Set.Icc (((-947849/500000:ℚ):ℝ)) (((-473627/250000:ℚ):ℝ)) := by
    unfold a2
    simp only [pow_succ, pow_zero, mul_one, div_eq_mul_inv]
    generalize lam template u=v0 at *
    generalize e2 (beta template u)=v1 at *
    generalize T template u=v2 at *
    dyadic_interval [prec := 64]
  have h3 : a3 template u ∈ Set.Icc (((150851/31250:ℚ):ℝ)) (((4831003/1000000:ℚ):ℝ)) := by
    unfold a3
    simp only [pow_succ, pow_zero, mul_one, div_eq_mul_inv]
    generalize lam template u=v0 at *
    generalize e3 (beta template u)=v1 at *
    generalize e2 (beta template u)=v2 at *
    dyadic_interval [prec := 64]
  have h4 : a4 template u ∈ Set.Icc (((-294533/250000:ℚ):ℝ)) (((-588401/500000:ℚ):ℝ)) := by
    unfold a4
    simp only [pow_succ, pow_zero, mul_one, div_eq_mul_inv]
    generalize lam template u=v0 at *
    generalize e4 (beta template u)=v1 at *
    generalize e3 (beta template u)=v2 at *
    dyadic_interval [prec := 64]
  have hh : h template u ∈ Set.Icc (((23427/125000:ℚ):ℝ)) (((187573/1000000:ℚ):ℝ)) := by
    unfold h
    simp only [pow_succ, pow_zero, mul_one, div_eq_mul_inv]
    generalize lam template u=v0 at *
    generalize P template u=v1 at *
    dyadic_interval [prec := 64]
  have hm : m template u ∈ Set.Icc (((958003/1000000:ℚ):ℝ)) (((482087/500000:ℚ):ℝ)) := by
    unfold m
    simp only [pow_succ, pow_zero, mul_one, div_eq_mul_inv]
    dyadic_interval [prec := 64]
  have hq : cSq template u ∈ Set.Icc (((77817/200000:ℚ):ℝ)) (((390427/1000000:ℚ):ℝ)) := by
    unfold cSq
    simp only [pow_succ, pow_zero, mul_one, div_eq_mul_inv]
    rw [show (8:ℝ)⁻¹=((1/8:ℚ):ℝ) by norm_num]
    dyadic_interval [prec := 64]
  have hq0 : 0 < cSq template u := by have := hq.1; norm_num at this ⊢; linarith
  have hh0 : 0 < h template u := by have := hh.1; norm_num at this ⊢; linarith
  have hnum : 0 < a4 template u-(h template u+m template u/2)^2+2*h template u+4*cSq template u := by
    simp only [pow_succ, pow_zero, mul_one, div_eq_mul_inv]
    rw [show (2:ℝ)⁻¹=((1/2:ℚ):ℝ) by norm_num]
    dyadic_interval [prec := 64]
  have hA0 : 0 < aSq template u := div_pos hnum (mul_pos (by norm_num) hq0)
  have hr0 : 0 < rSq template u := by
    unfold rSq
    have hnonneg : 0 ≤ (m template u)^2/(16*aSq template u) :=
      div_nonneg (sq_nonneg _) (le_of_lt (mul_pos (by norm_num) hA0))
    linarith
  exact ⟨hD0, by have := hP.2; norm_num at this ⊢; linarith, hq0, hA0, hr0⟩

end
end RMCQuintic

namespace CyclicQuintic
noncomputable section
def ratCoeffFiveToFun
    (q : RatCoeffFive) :
    Fin 5 → ℚ :=
  ![
    q.1,
    q.2.1,
    q.2.2.1,
    q.2.2.2.1,
    q.2.2.2.2
  ]

theorem ratCoeffFiveToFun_zero
    (q : RatCoeffFive) :
    ratCoeffFiveToFun q 0 = q.1 := by
  rfl

theorem ratCoeffFiveToFun_one
    (q : RatCoeffFive) :
    ratCoeffFiveToFun q 1 = q.2.1 := by
  rfl

theorem ratCoeffFiveToFun_two
    (q : RatCoeffFive) :
    ratCoeffFiveToFun q 2 = q.2.2.1 := by
  rfl

theorem ratCoeffFiveToFun_three
    (q : RatCoeffFive) :
    ratCoeffFiveToFun q 3 = q.2.2.2.1 := by
  rfl

theorem ratCoeffFiveToFun_four
    (q : RatCoeffFive) :
    ratCoeffFiveToFun q 4 = q.2.2.2.2 := by
  rfl

/-!
The real coefficient function previously used by the density argument
is exactly the coordinatewise real cast of this rational function.
-/

theorem castCoeffFiveFun_apply
    (q : RatCoeffFive)
    (i : Fin 5) :
    castCoeffFiveFun q i =
      (ratCoeffFiveToFun q i : ℝ) := by
  fin_cases i <;>
    rfl

theorem castCoeffFiveFun_eq_ratCast
    (q : RatCoeffFive) :
    castCoeffFiveFun q =
      fun i : Fin 5 =>
        (ratCoeffFiveToFun q i : ℝ) := by
  funext i
  exact castCoeffFiveFun_apply q i

/-!
## 2. Construct the actual field element

The rational numbers are cast directly into L. Every field
automorphism fixes these rational scalars.
-/

noncomputable def rationalBasisElement
    {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    [CharZero L]
    (b : Module.Basis (Fin 5) K L)
    (q : RatCoeffFive) :
    L :=
  ∑ j : Fin 5,
    (ratCoeffFiveToFun q j : L) * b j

theorem rationalBasisElement_def
    {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    [CharZero L]
    (b : Module.Basis (Fin 5) K L)
    (q : RatCoeffFive) :
    rationalBasisElement b q =
      ∑ j : Fin 5,
        (ratCoeffFiveToFun q j : L) *
          b j := by
  rfl

/-!
## 3. Embedded conjugates of the rational basis element

Applying sigma^i distributes through the sum and product. Since every
ring homomorphism between fields fixes rational constants, both sigma^i
and the real embedding send q_j to the corresponding rational number.
-/

theorem embedded_conjugate_rationalBasisElement
    {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    [CharZero L]
    (ι : L →+* ℝ)
    (sigma : L ≃ₐ[K] L)
    (b : Module.Basis (Fin 5) K L)
    (q : RatCoeffFive)
    (i : Fin 5) :
    ι
      ((sigma ^ (i : ℕ))
        (rationalBasisElement b q)) =
      ∑ j : Fin 5,
        ι ((sigma ^ (i : ℕ)) (b j)) *
          castCoeffFiveFun q j := by

  have hsigma_rat
      (r : ℚ) :
      (sigma ^ (i : ℕ)) (r : L) =
        (r : L) := by
    exact
      map_ratCast (sigma ^ (i : ℕ)) r

  have hiota_rat
      (r : ℚ) :
      ι (r : L) = (r : ℝ) := by
    exact map_ratCast ι r

  simp only [
    rationalBasisElement,
    map_sum,
    map_mul,
    castCoeffFiveFun_apply
  ]

  apply Finset.sum_congr rfl

  intro j hj

  rw [
    hsigma_rat
      (ratCoeffFiveToFun q j),
    hiota_rat
      (ratCoeffFiveToFun q j)
  ]

  ring

/-!
Consequently, the complete embedded orbit is definitionally the
rational conjugate tuple produced by the density argument.
-/

theorem rationalBasisElement_realOrbit_apply
    {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    [CharZero L]
    (ι : L →+* ℝ)
    (sigma : L ≃ₐ[K] L)
    (horder : orderOf sigma = 5)
    (b : Module.Basis (Fin 5) K L)
    (q : RatCoeffFive)
    (i : Fin 5) :
    ι
      ((sigma ^ (i : ℕ))
        (rationalBasisElement b q)) =
      rationalConjugateTuple
        ι sigma horder b q i := by
  rw [
    rationalConjugateTuple_apply
      ι sigma horder b q i
  ]

  exact
    embedded_conjugate_rationalBasisElement
      ι sigma b q i

theorem rationalBasisElement_realOrbit
    {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    [CharZero L]
    (ι : L →+* ℝ)
    (sigma : L ≃ₐ[K] L)
    (horder : orderOf sigma = 5)
    (b : Module.Basis (Fin 5) K L)
    (q : RatCoeffFive) :
    (fun i : Fin 5 =>
      ι
        ((sigma ^ (i : ℕ))
          (rationalBasisElement b q))) =
      rationalConjugateTuple
        ι sigma horder b q := by
  funext i

  exact
    rationalBasisElement_realOrbit_apply
      ι sigma horder b q i

/-!
## 4. A rational tuple in the distinctness region is primitive

This is already a complete existence-to-field-element bridge for the
original element x(q).
-/


end
end CyclicQuintic


namespace RMCQuintic

open Set Filter Topology

@[fun_prop] theorem continuous_e1 : Continuous (e1 : (Fin 5 → ℝ) → ℝ) := by unfold e1; fun_prop
@[fun_prop] theorem continuous_e2 : Continuous (e2 : (Fin 5 → ℝ) → ℝ) := by unfold e2; fun_prop
@[fun_prop] theorem continuous_e3 : Continuous (e3 : (Fin 5 → ℝ) → ℝ) := by unfold e3; fun_prop
@[fun_prop] theorem continuous_e4 : Continuous (e4 : (Fin 5 → ℝ) → ℝ) := by unfold e4; fun_prop
@[fun_prop] theorem continuous_e5 : Continuous (e5 : (Fin 5 → ℝ) → ℝ) := by unfold e5; fun_prop
@[fun_prop] theorem continuous_triples : Continuous (triples : (Fin 5 → ℝ) → ℝ) := by unfold triples; fun_prop
@[fun_prop] theorem continuous_g : Continuous (fun p : (Fin 5 → ℝ) × ℝ => g p.1 p.2) := by
  apply continuous_pi
  intro i
  dsimp [g]
  fun_prop
@[fun_prop] theorem continuous_beta : Continuous (fun p : (Fin 5 → ℝ) × ℝ => beta p.1 p.2) := by
  apply continuous_pi
  intro i
  fin_cases i <;> dsimp [beta, adjacent, g] <;> fun_prop
@[fun_prop] theorem continuous_D : Continuous (fun p : (Fin 5 → ℝ) × ℝ => D p.1 p.2) := by
  unfold D T
  fun_prop
@[fun_prop] theorem continuous_P : Continuous (fun p : (Fin 5 → ℝ) × ℝ => P p.1 p.2) := by
  unfold P
  fun_prop
@[fun_prop] theorem continuous_C0 : Continuous (C0 : (Fin 5 → ℝ) → ℝ) := by
  change Continuous (fun x : Fin 5 → ℝ => C0 x)
  dsimp [C0, t, e1, adjacent, cyclicV]
  fun_prop
@[fun_prop] theorem continuous_C1 : Continuous (C1 : (Fin 5 → ℝ) → ℝ) := by
  change Continuous (fun x : Fin 5 → ℝ => C1 x)
  dsimp [C1, t, e1, adjacent, cyclicA32, triples, e3, e4, e5]
  fun_prop
@[fun_prop] theorem continuous_C2 : Continuous (C2 : (Fin 5 → ℝ) → ℝ) := by
  change Continuous (fun x : Fin 5 → ℝ => C2 x)
  dsimp [C2, t, e1, adjacent, cyclicA33, e4, e5]
  fun_prop
@[fun_prop] theorem continuous_C3 : Continuous (C3 : (Fin 5 → ℝ) → ℝ) := by
  change Continuous (fun x : Fin 5 → ℝ => C3 x)
  dsimp [C3, t, e1, e5, adjacent]
  fun_prop
@[fun_prop] theorem continuous_H : Continuous (fun p : (Fin 5 → ℝ) × ℝ => H p.1 p.2) := by
  unfold H
  fun_prop

/-- All positivity conditions are imposed at the actual pair (conjugates, auxiliary). -/
def Good : Set ((Fin 5 → ℝ) × ℝ) :=
  {p | 0 < D p.1 p.2 ∧ P p.1 p.2 < 0 ∧ 0 < cSq p.1 p.2 ∧
    0 < aSq p.1 p.2 ∧ 0 < rSq p.1 p.2}

theorem good_open : IsOpen Good := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  rcases hp with ⟨hD, hP, hq, hA, hr⟩
  have hDz : D p.1 p.2 ≠ 0 := ne_of_gt hD
  have hqz : cSq p.1 p.2 ≠ 0 := ne_of_gt hq
  have hAz : aSq p.1 p.2 ≠ 0 := ne_of_gt hA
  have hlam : ContinuousAt (fun p : (Fin 5 → ℝ) × ℝ => lam p.1 p.2) p := by
    unfold lam
    exact continuousAt_const.div continuous_D.continuousAt hDz
  have h2 : ContinuousAt (fun p : (Fin 5 → ℝ) × ℝ => a2 p.1 p.2) p := by
    unfold a2 T
    fun_prop
  have h3 : ContinuousAt (fun p : (Fin 5 → ℝ) × ℝ => a3 p.1 p.2) p := by
    unfold a3
    fun_prop
  have h4 : ContinuousAt (fun p : (Fin 5 → ℝ) × ℝ => a4 p.1 p.2) p := by
    unfold a4
    fun_prop
  have hh : ContinuousAt (fun p : (Fin 5 → ℝ) × ℝ => h p.1 p.2) p := by
    unfold h
    fun_prop
  have hm : ContinuousAt (fun p : (Fin 5 → ℝ) × ℝ => m p.1 p.2) p := by
    unfold m
    fun_prop
  have hcs : ContinuousAt (fun p : (Fin 5 → ℝ) × ℝ => cSq p.1 p.2) p := by
    unfold cSq
    fun_prop
  have has : ContinuousAt (fun p : (Fin 5 → ℝ) × ℝ => aSq p.1 p.2) p := by
    unfold aSq
    fun_prop (disch := positivity)
  have hrs : ContinuousAt (fun p : (Fin 5 → ℝ) × ℝ => rSq p.1 p.2) p := by
    unfold rSq
    fun_prop (disch := positivity)
  filter_upwards [continuousAt_const.eventually_lt continuous_D.continuousAt hD,
    continuous_P.continuousAt.eventually_lt continuousAt_const hP,
    continuousAt_const.eventually_lt hcs hq,
    continuousAt_const.eventually_lt has hA,
    continuousAt_const.eventually_lt hrs hr] with q h1 h2 h3 h4 h5
  exact ⟨h1,h2,h3,h4,h5⟩

def EndpointRegion : Set (Fin 5 → ℝ) :=
  {x | H x lo < 0 ∧ 0 < H x hi ∧ 0 < C3 x ∧ x 0 < x 1}

theorem endpointRegion_open : IsOpen EndpointRegion := by
  have hl : Continuous (fun x : Fin 5 → ℝ => H x lo) := by unfold H; fun_prop
  have hh : Continuous (fun x : Fin 5 → ℝ => H x hi) := by unfold H; fun_prop
  exact (isOpen_lt hl continuous_const).and
    ((isOpen_lt continuous_const hh).and
      ((isOpen_lt continuous_const continuous_C3).and (isOpen_lt (continuous_apply 0) (continuous_apply 1))))

theorem template_endpoint : template ∈ EndpointRegion := by
  refine ⟨template_signs.1, template_signs.2, ?_, ?_⟩
  · norm_num [C3, t, e1, e5, adjacent, template]
  · norm_num [template]

/-- Compactness keeps every possible root in the selected interval geometrically valid. -/
theorem choose_good_conjugates
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (ι : L →+* ℝ) (σ : L ≃ₐ[K] L) (hσ : orderOf σ=5)
    (b : Module.Basis (Fin 5) K L) :
    ∃ q : CyclicQuintic.RatCoeffFive, ∃ u : ℝ,
      let x := CyclicQuintic.rationalConjugateTuple ι σ hσ b q
      (x,u) ∈ Good ∧ x 0 < x 1 ∧ 0 < C3 x ∧ lo < u ∧ u < hi ∧ H x u=0 := by
  have htube : ({template} : Set (Fin 5 → ℝ)) ×ˢ Icc lo hi ⊆ Good := by
    rintro ⟨x,u⟩ ⟨hx,hu⟩
    have hx' : x=template := Set.mem_singleton_iff.mp hx
    subst x
    exact template_good u hu.1 hu.2
  obtain ⟨V,W,hV,hW,hxV,hIW,hVW⟩ := generalized_tube_lemma
    isCompact_singleton isCompact_Icc good_open htube
  let N := V ∩ EndpointRegion
  have hN : IsOpen N := hV.inter endpointRegion_open
  have htN : template ∈ N := ⟨hxV (by simp), template_endpoint⟩
  obtain ⟨q,hq⟩ := CyclicQuintic.rationalConjugateTuple_hits_open ι σ hσ b N hN ⟨template,htN⟩
  let x := CyclicQuintic.rationalConjugateTuple ι σ hσ b q
  have hxn : x ∈ N := hq
  obtain ⟨u,hlu,huh,hroot⟩ := CyclicQuintic.exists_root_between_of_sign_change
    (H x) lo hi (by norm_num [lo,hi]) (by unfold H; fun_prop) hxn.2.1 hxn.2.2.1
  exact ⟨q,u,hVW ⟨hxn.1,hIW ⟨le_of_lt hlu,le_of_lt huh⟩⟩,
    hxn.2.2.2.2,hxn.2.2.2.1,hlu,huh,hroot⟩

end RMCQuintic


namespace RMCQuintic

open Polynomial

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [CharZero L]

/-- An order-five automorphism generates the degree-five Galois group. -/
theorem fixed_of_generator (σ : L ≃ₐ[K] L) (hσ : orderOf σ=5)
    (hdegree : Module.finrank K L=5) {x : L} (hx : σ x=x)
    (τ : L ≃ₐ[K] L) : τ x=x := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hcard : Nat.card (L ≃ₐ[K] L)=5 := by rw [IsGalois.card_aut_eq_finrank, hdegree]
  have hne : σ ≠ 1 := by intro H; rw [H, orderOf_one] at hσ; norm_num at hσ
  have ht : τ ∈ Subgroup.zpowers σ := mem_zpowers_of_prime_card hcard hne
  obtain ⟨n,hn,heq⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp ht)
  rw [← heq]
  have hpow : ∀ n : ℕ, (σ^n) x=x := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ, AlgEquiv.mul_apply, hx, ih]
  exact hpow n

theorem fixed_image_mem (C : Subfield ℝ) (ι : L →+* ℝ)
    (σ : L ≃ₐ[K] L) (hσ : orderOf σ=5) (hdegree : Module.finrank K L=5)
    (hK : ∀ k : K, ι (algebraMap K L k) ∈ C) {x : L} (hx : σ x=x) : ι x ∈ C := by
  obtain ⟨k,hk⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F:=K) (E:=L) x).2
    (fixed_of_generator σ hσ hdegree hx)
  rw [← hk]
  exact hK k

def orbit (σ : L ≃ₐ[K] L) (γ : L) : Fin 5 → L := fun i => (σ^(i:ℕ)) γ

theorem orbit_rot (σ : L ≃ₐ[K] L) (hσ : orderOf σ=5) (γ : L) :
    (fun i => σ (orbit σ γ i))=rot (orbit σ γ) := by
  have h5 : σ^5=1 := by simpa [hσ] using pow_orderOf_eq_one σ
  have hh : σ (σ (σ (σ (σ γ))))=γ := by
    have := congrArg (fun f : L ≃ₐ[K] L => f γ) h5
    simpa [pow_succ, AlgEquiv.mul_apply] using this
  ext i
  fin_cases i <;> simp [orbit, rot, pow_succ, AlgEquiv.mul_apply, hh]

theorem rot_mapfun {A B : Type*} [CommRing A] [CommRing B] (f : A → B) (x : Fin 5 → A) :
    (fun i => f (rot x i))=rot (fun i => f (x i)) := by
  ext i
  fin_cases i <;> rfl

/-- Fixed polynomial coefficients descend before the external auxiliary is evaluated. -/
theorem invariant_eval_mem (C : Subfield ℝ) (ι : L →+* ℝ)
    (σ : L ≃ₐ[K] L) (hσ : orderOf σ=5) (hdegree : Module.finrank K L=5)
    (hK : ∀ k : K, ι (algebraMap K L k) ∈ C)
    {u : ℝ} (hu : u ∈ C) (p : Polynomial L) (hp : p.map σ.toRingHom=p) :
    p.eval₂ ι u ∈ C := by
  have hc : ∀ n, σ (p.coeff n)=p.coeff n := by
    intro n
    have := congrArg (fun q : Polynomial L => q.coeff n) hp
    simpa using this
  rw [Polynomial.eval₂_eq_sum]
  exact C.sum_mem fun n hn => C.mul_mem (fixed_image_mem C ι σ hσ hdegree hK (hc n)) (C.pow_mem hu n)

theorem C0_orbit_mem (C : Subfield ℝ) (ι : L →+* ℝ)
    (σ : L ≃ₐ[K] L) (hσ : orderOf σ=5) (hdegree : Module.finrank K L=5)
    (hK : ∀ k : K, ι (algebraMap K L k) ∈ C) (γ : L) :
    C0 (fun i => ι (orbit σ γ i)) ∈ C := by
  rw [← C0_map ι]
  apply fixed_image_mem C ι σ hσ hdegree hK
  change σ.toRingHom (C0 (orbit σ γ))=C0 (orbit σ γ)
  rw [C0_map σ.toRingHom]
  change C0 (fun i => σ (orbit σ γ i))=C0 (orbit σ γ)
  rw [orbit_rot σ hσ γ, C0_rot]

theorem C1_orbit_mem (C : Subfield ℝ) (ι : L →+* ℝ)
    (σ : L ≃ₐ[K] L) (hσ : orderOf σ=5) (hdegree : Module.finrank K L=5)
    (hK : ∀ k : K, ι (algebraMap K L k) ∈ C) (γ : L) :
    C1 (fun i => ι (orbit σ γ i)) ∈ C := by
  rw [← C1_map ι]
  apply fixed_image_mem C ι σ hσ hdegree hK
  change σ.toRingHom (C1 (orbit σ γ))=C1 (orbit σ γ)
  rw [C1_map σ.toRingHom]
  change C1 (fun i => σ (orbit σ γ i))=C1 (orbit σ γ)
  rw [orbit_rot σ hσ γ, C1_rot]

theorem C2_orbit_mem (C : Subfield ℝ) (ι : L →+* ℝ)
    (σ : L ≃ₐ[K] L) (hσ : orderOf σ=5) (hdegree : Module.finrank K L=5)
    (hK : ∀ k : K, ι (algebraMap K L k) ∈ C) (γ : L) :
    C2 (fun i => ι (orbit σ γ i)) ∈ C := by
  rw [← C2_map ι]
  apply fixed_image_mem C ι σ hσ hdegree hK
  change σ.toRingHom (C2 (orbit σ γ))=C2 (orbit σ γ)
  rw [C2_map σ.toRingHom]
  change C2 (fun i => σ (orbit σ γ i))=C2 (orbit σ γ)
  rw [orbit_rot σ hσ γ, C2_rot]

theorem C3_orbit_mem (C : Subfield ℝ) (ι : L →+* ℝ)
    (σ : L ≃ₐ[K] L) (hσ : orderOf σ=5) (hdegree : Module.finrank K L=5)
    (hK : ∀ k : K, ι (algebraMap K L k) ∈ C) (γ : L) :
    C3 (fun i => ι (orbit σ γ i)) ∈ C := by
  rw [← C3_map ι]
  apply fixed_image_mem C ι σ hσ hdegree hK
  change σ.toRingHom (C3 (orbit σ γ))=C3 (orbit σ γ)
  rw [C3_map σ.toRingHom]
  change C3 (fun i => σ (orbit σ γ i))=C3 (orbit σ γ)
  rw [orbit_rot σ hσ γ, C3_rot]

theorem e1_aux_mem (C : Subfield ℝ) (ι : L →+* ℝ)
    (σ : L ≃ₐ[K] L) (hσ : orderOf σ=5) (hdegree : Module.finrank K L=5)
    (hK : ∀ k : K, ι (algebraMap K L k) ∈ C) (γ : L)
    {u : ℝ} (hu : u ∈ C) : e1 (beta (fun i => ι (orbit σ γ i)) u) ∈ C := by
  let o : Fin 5 → Polynomial L := fun i => Polynomial.C (orbit σ γ i)
  let p := e1 (beta o X)
  have ho : (fun i => (Polynomial.mapRingHom σ.toRingHom) (o i))=rot o := by
    calc
      (fun i => (Polynomial.mapRingHom σ.toRingHom) (o i)) =
          (fun i => Polynomial.C (σ (orbit σ γ i))) := by simp [o]
      _ = (fun i => Polynomial.C (rot (orbit σ γ) i)) := by rw [← orbit_rot σ hσ γ]
      _ = rot o := rot_mapfun Polynomial.C (orbit σ γ)
  have hp : p.map σ.toRingHom=p := by
    change (Polynomial.mapRingHom σ.toRingHom) (e1 (beta o X))=e1 (beta o X)
    rw [e1_map, beta_map, ho]
    simp only [Polynomial.coe_mapRingHom, Polynomial.map_X]
    rw [beta_rot, e1_rot]
  have hm := invariant_eval_mem C ι σ hσ hdegree hK hu p hp
  have heval : p.eval₂ ι u=e1 (beta (fun i => ι (orbit σ γ i)) u) := by
    change (Polynomial.eval₂RingHom ι u) (e1 (beta o X))=_
    rw [e1_map, beta_map]
    simp [o]
  rw [← heval]
  exact hm

theorem e2_aux_mem (C : Subfield ℝ) (ι : L →+* ℝ)
    (σ : L ≃ₐ[K] L) (hσ : orderOf σ=5) (hdegree : Module.finrank K L=5)
    (hK : ∀ k : K, ι (algebraMap K L k) ∈ C) (γ : L)
    {u : ℝ} (hu : u ∈ C) : e2 (beta (fun i => ι (orbit σ γ i)) u) ∈ C := by
  let o : Fin 5 → Polynomial L := fun i => Polynomial.C (orbit σ γ i)
  let p := e2 (beta o X)
  have ho : (fun i => (Polynomial.mapRingHom σ.toRingHom) (o i))=rot o := by
    calc
      (fun i => (Polynomial.mapRingHom σ.toRingHom) (o i)) =
          (fun i => Polynomial.C (σ (orbit σ γ i))) := by simp [o]
      _ = (fun i => Polynomial.C (rot (orbit σ γ) i)) := by rw [← orbit_rot σ hσ γ]
      _ = rot o := rot_mapfun Polynomial.C (orbit σ γ)
  have hp : p.map σ.toRingHom=p := by
    change (Polynomial.mapRingHom σ.toRingHom) (e2 (beta o X))=e2 (beta o X)
    rw [e2_map, beta_map, ho]
    simp only [Polynomial.coe_mapRingHom, Polynomial.map_X]
    rw [beta_rot, e2_rot]
  have hm := invariant_eval_mem C ι σ hσ hdegree hK hu p hp
  have heval : p.eval₂ ι u=e2 (beta (fun i => ι (orbit σ γ i)) u) := by
    change (Polynomial.eval₂RingHom ι u) (e2 (beta o X))=_
    rw [e2_map, beta_map]
    simp [o]
  rw [← heval]
  exact hm

theorem e3_aux_mem (C : Subfield ℝ) (ι : L →+* ℝ)
    (σ : L ≃ₐ[K] L) (hσ : orderOf σ=5) (hdegree : Module.finrank K L=5)
    (hK : ∀ k : K, ι (algebraMap K L k) ∈ C) (γ : L)
    {u : ℝ} (hu : u ∈ C) : e3 (beta (fun i => ι (orbit σ γ i)) u) ∈ C := by
  let o : Fin 5 → Polynomial L := fun i => Polynomial.C (orbit σ γ i)
  let p := e3 (beta o X)
  have ho : (fun i => (Polynomial.mapRingHom σ.toRingHom) (o i))=rot o := by
    calc
      (fun i => (Polynomial.mapRingHom σ.toRingHom) (o i)) =
          (fun i => Polynomial.C (σ (orbit σ γ i))) := by simp [o]
      _ = (fun i => Polynomial.C (rot (orbit σ γ) i)) := by rw [← orbit_rot σ hσ γ]
      _ = rot o := rot_mapfun Polynomial.C (orbit σ γ)
  have hp : p.map σ.toRingHom=p := by
    change (Polynomial.mapRingHom σ.toRingHom) (e3 (beta o X))=e3 (beta o X)
    rw [e3_map, beta_map, ho]
    simp only [Polynomial.coe_mapRingHom, Polynomial.map_X]
    rw [beta_rot, e3_rot]
  have hm := invariant_eval_mem C ι σ hσ hdegree hK hu p hp
  have heval : p.eval₂ ι u=e3 (beta (fun i => ι (orbit σ γ i)) u) := by
    change (Polynomial.eval₂RingHom ι u) (e3 (beta o X))=_
    rw [e3_map, beta_map]
    simp [o]
  rw [← heval]
  exact hm

theorem e4_aux_mem (C : Subfield ℝ) (ι : L →+* ℝ)
    (σ : L ≃ₐ[K] L) (hσ : orderOf σ=5) (hdegree : Module.finrank K L=5)
    (hK : ∀ k : K, ι (algebraMap K L k) ∈ C) (γ : L)
    {u : ℝ} (hu : u ∈ C) : e4 (beta (fun i => ι (orbit σ γ i)) u) ∈ C := by
  let o : Fin 5 → Polynomial L := fun i => Polynomial.C (orbit σ γ i)
  let p := e4 (beta o X)
  have ho : (fun i => (Polynomial.mapRingHom σ.toRingHom) (o i))=rot o := by
    calc
      (fun i => (Polynomial.mapRingHom σ.toRingHom) (o i)) =
          (fun i => Polynomial.C (σ (orbit σ γ i))) := by simp [o]
      _ = (fun i => Polynomial.C (rot (orbit σ γ) i)) := by rw [← orbit_rot σ hσ γ]
      _ = rot o := rot_mapfun Polynomial.C (orbit σ γ)
  have hp : p.map σ.toRingHom=p := by
    change (Polynomial.mapRingHom σ.toRingHom) (e4 (beta o X))=e4 (beta o X)
    rw [e4_map, beta_map, ho]
    simp only [Polynomial.coe_mapRingHom, Polynomial.map_X]
    rw [beta_rot, e4_rot]
  have hm := invariant_eval_mem C ι σ hσ hdegree hK hu p hp
  have heval : p.eval₂ ι u=e4 (beta (fun i => ι (orbit σ γ i)) u) := by
    change (Polynomial.eval₂RingHom ι u) (e4 (beta o X))=_
    rw [e4_map, beta_map]
    simp [o]
  rw [← heval]
  exact hm

theorem e5_aux_mem (C : Subfield ℝ) (ι : L →+* ℝ)
    (σ : L ≃ₐ[K] L) (hσ : orderOf σ=5) (hdegree : Module.finrank K L=5)
    (hK : ∀ k : K, ι (algebraMap K L k) ∈ C) (γ : L)
    {u : ℝ} (hu : u ∈ C) : e5 (beta (fun i => ι (orbit σ γ i)) u) ∈ C := by
  let o : Fin 5 → Polynomial L := fun i => Polynomial.C (orbit σ γ i)
  let p := e5 (beta o X)
  have ho : (fun i => (Polynomial.mapRingHom σ.toRingHom) (o i))=rot o := by
    calc
      (fun i => (Polynomial.mapRingHom σ.toRingHom) (o i)) =
          (fun i => Polynomial.C (σ (orbit σ γ i))) := by simp [o]
      _ = (fun i => Polynomial.C (rot (orbit σ γ) i)) := by rw [← orbit_rot σ hσ γ]
      _ = rot o := rot_mapfun Polynomial.C (orbit σ γ)
  have hp : p.map σ.toRingHom=p := by
    change (Polynomial.mapRingHom σ.toRingHom) (e5 (beta o X))=e5 (beta o X)
    rw [e5_map, beta_map, ho]
    simp only [Polynomial.coe_mapRingHom, Polynomial.map_X]
    rw [beta_rot, e5_rot]
  have hm := invariant_eval_mem C ι σ hσ hdegree hK hu p hp
  have heval : p.eval₂ ι u=e5 (beta (fun i => ι (orbit σ γ i)) u) := by
    change (Polynomial.eval₂RingHom ι u) (e5 (beta o X))=_
    rw [e5_map, beta_map]
    simp [o]
  rw [← heval]
  exact hm

theorem P_aux_mem (C : Subfield ℝ) (ι : L →+* ℝ)
    (σ : L ≃ₐ[K] L) (hσ : orderOf σ=5) (hdegree : Module.finrank K L=5)
    (hK : ∀ k : K, ι (algebraMap K L k) ∈ C) (γ : L)
    {u : ℝ} (hu : u ∈ C) : P (fun i => ι (orbit σ γ i)) u ∈ C := by
  let o : Fin 5 → Polynomial L := fun i => Polynomial.C (orbit σ γ i)
  let p := e5 (g o X)
  have ho : (fun i => (Polynomial.mapRingHom σ.toRingHom) (o i))=rot o := by
    calc
      (fun i => (Polynomial.mapRingHom σ.toRingHom) (o i)) =
          (fun i => Polynomial.C (σ (orbit σ γ i))) := by simp [o]
      _ = (fun i => Polynomial.C (rot (orbit σ γ) i)) := by rw [← orbit_rot σ hσ γ]
      _ = rot o := rot_mapfun Polynomial.C (orbit σ γ)
  have hp : p.map σ.toRingHom=p := by
    change (Polynomial.mapRingHom σ.toRingHom) (e5 (g o X))=e5 (g o X)
    rw [e5_map, g_map, ho]
    simp only [Polynomial.coe_mapRingHom, Polynomial.map_X]
    rw [g_rot, e5_rot]
  have hm := invariant_eval_mem C ι σ hσ hdegree hK hu p hp
  have heval : p.eval₂ ι u=P (fun i => ι (orbit σ γ i)) u := by
    change (Polynomial.eval₂RingHom ι u) (e5 (g o X))=_
    rw [e5_map, g_map]
    simp [o, P]
  rw [← heval]
  exact hm

end RMCQuintic


namespace RMCQuintic

/-- The odd adjacent-product cycle recovers the original coordinate without a
compositum-generation assumption. -/
theorem adjacent_recover {F : Type*} [Field F] (g : Fin 5 → F) (hP : e5 g ≠ 0) :
    e5 g/(adjacent g 1*adjacent g 3)=g 0 := by
  have h : g 1 ≠ 0 ∧ g 2 ≠ 0 ∧ g 3 ≠ 0 ∧ g 4 ≠ 0 := by
    dsimp [e5] at hP
    aesop
  dsimp [e5, adjacent]
  field_simp [h.1,h.2.1,h.2.2.1,h.2.2.2]

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [CharZero L]

theorem generator_of_moved (σ : L ≃ₐ[K] L) (hdegree : Module.finrank K L=5)
    {γ : L} (hγ : σ γ ≠ γ) : IntermediateField.adjoin K {γ}=⊤ := by
  letI := IntermediateField.isSimpleOrder_of_finrank_prime K L (by rw [hdegree]; decide)
  rcases IsSimpleOrder.eq_bot_or_eq_top (IntermediateField.adjoin K {γ}) with hbot | htop
  · have hg : γ ∈ (⊥ : IntermediateField K L) := by
      rw [← hbot]
      exact IntermediateField.subset_adjoin K {γ} (by simp)
    obtain ⟨k,hk⟩ := IntermediateField.mem_bot.mp hg
    apply False.elim
    apply hγ
    rw [← hk]
    exact σ.commutes k
  · exact htop

/-- Main closure theorem. Every construction input is descended from the base;
the unknown quintic conjugates are used only in the existence proof. -/
theorem cyclic_quintic_closed (C : Subfield ℝ) (hc : Closed C)
    (ι : L →+* ℝ) (hK : ∀ k : K, ι (algebraMap K L k) ∈ C)
    (σ : L ≃ₐ[K] L) (hσ : orderOf σ=5) (hdegree : Module.finrank K L=5)
    (y : L) : ι y ∈ C := by
  classical
  let b : Module.Basis (Fin 5) K L := (Module.finBasis K L).reindex (finCongr hdegree)
  obtain ⟨q,u,hgood,hxlt,hC3,hlu,huhi,hroot⟩ := choose_good_conjugates ι σ hσ b
  let x := CyclicQuintic.rationalConjugateTuple ι σ hσ b q
  let γ := CyclicQuintic.rationalBasisElement b q
  change H x u=0 at hroot
  have hx : x=(fun i => ι (orbit σ γ i)) := by
    symm
    exact CyclicQuintic.rationalBasisElement_realOrbit ι σ hσ b q
  have h0 : C0 x ∈ C := by rw [hx]; exact C0_orbit_mem C ι σ hσ hdegree hK γ
  have h1 : C1 x ∈ C := by rw [hx]; exact C1_orbit_mem C ι σ hσ hdegree hK γ
  have h2 : C2 x ∈ C := by rw [hx]; exact C2_orbit_mem C ι σ hσ hdegree hK γ
  have h3 : C3 x ∈ C := by rw [hx]; exact C3_orbit_mem C ι σ hσ hdegree hK γ
  have hum : u ∈ C := cubic_mem C hc h0 h1 h2 h3 (ne_of_gt hC3) hroot
  have hT : T x u ∈ C := by rw [hx]; exact e1_aux_mem C ι σ hσ hdegree hK γ hum
  have hE2 : e2 (beta x u) ∈ C := by rw [hx]; exact e2_aux_mem C ι σ hσ hdegree hK γ hum
  have hE3 : e3 (beta x u) ∈ C := by rw [hx]; exact e3_aux_mem C ι σ hσ hdegree hK γ hum
  have hE4 : e4 (beta x u) ∈ C := by rw [hx]; exact e4_aux_mem C ι σ hσ hdegree hK γ hum
  have hPm : P x u ∈ C := by rw [hx]; exact P_aux_mem C ι σ hσ hdegree hK γ hum
  have hD : D x u ∈ C := C.add_mem hT C.one_mem
  have hLm : lam x u ∈ C := C.div_mem (by norm_num) hD
  have hLpos : 0 < lam x u := div_pos (by norm_num) hgood.1
  have hLne : lam x u ≠ 0 := ne_of_gt hLpos
  have h2m : a2 x u ∈ C := C.mul_mem (C.pow_mem hLm 2) (C.add_mem hE2 hT)
  have h3m : a3 x u ∈ C := C.mul_mem (C.neg_mem (C.pow_mem hLm 3)) (C.add_mem hE3 hE2)
  have h4m : a4 x u ∈ C := C.mul_mem (C.pow_mem hLm 4) (C.add_mem hE4 hE3)
  have hhm : h x u ∈ C := C.mul_mem (C.neg_mem (C.pow_mem hLm 3)) hPm
  have hhpos : 0 < h x u := by
    unfold h
    exact mul_pos_of_neg_of_neg (neg_lt_zero.mpr (pow_pos hLpos 3)) hgood.2.1
  have hDne : D x u ≠ 0 := ne_of_gt hgood.1
  have h5 : a5 x u=-(2-2*a2 x u-a3 x u)*h x u-2*(h x u)^2 := by
    have hobs : a5 x u+m x u*h x u+2*(h x u)^2=
        -16*P x u*u^4*H x u/(D x u)^6 := signed_obstruction x u hDne
    rw [hroot] at hobs
    simp only [mul_zero, zero_div] at hobs
    dsimp [m] at hobs
    linarith
  have hzm : ∀ i : Fin 5, lam x u*beta x u i ∈ C := by
    intro i
    exact sextic_root_mem C hc h2m h3m h4m hhm (ne_of_gt hhpos) h5
      hgood.2.2.1 hgood.2.2.2.1 hgood.2.2.2.2 (beta_sextic_root x u hDne i)
  have hbm : ∀ i : Fin 5, beta x u i ∈ C := by
    intro i
    have H := C.div_mem (hzm i) hLm
    simpa [hLne] using H
  have hg0 : g x u 0 ∈ C := by
    have H := C.div_mem hPm (C.mul_mem (hbm 1) (hbm 3))
    have Hrec := adjacent_recover (g x u) (ne_of_lt hgood.2.1)
    change P x u/(beta x u 1*beta x u 3)=g x u 0 at Hrec
    rw [Hrec] at H
    exact H
  have hu0 : u ≠ 0 := by
    have huhi' : u < -1 := by have := huhi; norm_num [hi] at this; linarith
    exact ne_of_lt (lt_trans huhi' (by norm_num))
  have hx0 : x 0 ∈ C := by
    have H := C.div_mem (C.sub_mem hg0 C.one_mem) hum
    have Hrec : (g x u 0-1)/u=x 0 := by dsimp [g]; field_simp [hu0]; ring
    rw [Hrec] at H
    exact H
  have hγm : ι γ ∈ C := by simpa [hx,orbit] using hx0
  have hγmove : σ γ ≠ γ := by
    intro H
    have hlt : ι γ < ι (σ γ) := by simpa [x,hx,orbit] using hxlt
    rw [H] at hlt
    exact lt_irrefl _ hlt
  have hgen := generator_of_moved σ hdegree hγmove
  let I : IntermediateField K L :=
    { toSubalgebra := { (C.comap ι).toSubring.toSubsemiring with algebraMap_mem' := hK }
      inv_mem' := (C.comap ι).inv_mem' }
  have hle : IntermediateField.adjoin K {γ} ≤ I := IntermediateField.adjoin_le_iff.mpr (by
    intro z hz
    have hz' : z=γ := Set.mem_singleton_iff.mp hz
    subst z
    exact hγm)
  rw [hgen] at hle
  exact hle (show y ∈ (⊤ : IntermediateField K L) by trivial)

/-- Finite constructions, with no general cubic/sextic root constructor. -/
inductive Constructible (K : Subfield ℝ) : ℝ → Prop
  | base {x} : x ∈ K → Constructible K x
  | add {x y} : Constructible K x → Constructible K y → Constructible K (x+y)
  | neg {x} : Constructible K x → Constructible K (-x)
  | mul {x y} : Constructible K x → Constructible K y → Constructible K (x*y)
  | inv {x} : Constructible K x → Constructible K x⁻¹
  | sqrt {x} : Constructible K x → 0 ≤ x → Constructible K (Real.sqrt x)
  | vergeX {a b c r X Y V W} :
      Constructible K a → Constructible K b → Constructible K c → Constructible K r →
      a ≠ 0 → 0 < r → V=a → (X-b)^2+(Y-c)^2=r^2 →
      X*W=Y*V → (X-V)^2+(Y-W)^2=1 → Constructible K X
  | vergeY {a b c r X Y V W} :
      Constructible K a → Constructible K b → Constructible K c → Constructible K r →
      a ≠ 0 → 0 < r → V=a → (X-b)^2+(Y-c)^2=r^2 →
      X*W=Y*V → (X-V)^2+(Y-W)^2=1 → Constructible K Y

noncomputable def generated (K : Subfield ℝ) : Subfield ℝ where
  carrier := {x : ℝ | Constructible K x}
  zero_mem' := Constructible.base K.zero_mem
  one_mem' := Constructible.base K.one_mem
  add_mem' := fun hx hy => Constructible.add hx hy
  neg_mem' := fun hx => Constructible.neg hx
  mul_mem' := fun hx hy => Constructible.mul hx hy
  inv_mem' := fun _ hx => Constructible.inv hx

@[simp] theorem mem_generated (K : Subfield ℝ) (x : ℝ) :
    x ∈ generated K ↔ Constructible K x := Iff.rfl

theorem generated_closed (K : Subfield ℝ) : Closed (generated K) where
  sqrt_mem := by
    intro x hx hnonneg
    exact (mem_generated K _).mpr
      (Constructible.sqrt ((mem_generated K _).mp hx) hnonneg)
  verge_mem := by
    intro a b c r X Y V W ha hb hc hr ha0 hr0 hl hcircle hcol hdist
    have ha' : Constructible K a := (mem_generated K a).mp ha
    have hb' : Constructible K b := (mem_generated K b).mp hb
    have hc' : Constructible K c := (mem_generated K c).mp hc
    have hr' : Constructible K r := (mem_generated K r).mp hr
    exact ⟨(mem_generated K X).mpr
        (Constructible.vergeX ha' hb' hc' hr' ha0 hr0 hl hcircle hcol hdist),
      (mem_generated K Y).mpr
        (Constructible.vergeY ha' hb' hc' hr' ha0 hr0 hl hcircle hcol hdist)⟩

noncomputable def baseField (ι : L →+* ℝ) : Subfield ℝ :=
  (⊤ : Subfield K).map (ι.comp (algebraMap K L))

/-- Every real Galois quintic is constructible by the explicitly defined operations. -/
theorem real_galois_quintic_constructible (ι : L →+* ℝ)
    (hdegree : Module.finrank K L=5) (y : L) : Constructible (baseField (K:=K) ι) (ι y) := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hcard : Nat.card (L ≃ₐ[K] L)=5 := by rw [IsGalois.card_aut_eq_finrank, hdegree]
  obtain ⟨σ,hσ⟩ := exists_prime_orderOf_dvd_card' (G:=L ≃ₐ[K] L) 5 (by rw [hcard])
  apply (mem_generated (baseField (K:=K) ι) (ι y)).mp
  apply cyclic_quintic_closed (generated (baseField (K:=K) ι)) (generated_closed _) ι ?_ σ hσ hdegree y
  intro k
  apply (mem_generated (baseField (K:=K) ι) _).mpr
  apply Constructible.base
  exact ⟨k, by trivial, rfl⟩

#print axioms real_galois_quintic_constructible

end RMCQuintic
