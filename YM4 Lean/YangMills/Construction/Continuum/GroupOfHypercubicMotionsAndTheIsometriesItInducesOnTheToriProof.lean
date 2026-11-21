import YangMills.Construction.GrowingTori.InducedIsometriesNestedLatticesAndTheMirrorsOfATorusProof
import YangMills.Construction.Continuum.GroupOfHypercubicMotionsAndTheIsometriesItInducesOnTheTori
import Mathlib
set_option autoImplicit false
open Matrix
noncomputable section
namespace YangMills.Construction.TorusTransport.AffineGroup
open TorusLifts (signedCoordinateEquiv)
def signedPermMatrix (p : Equiv.Perm (Fin 4)) (σ : Fin 4 → ℤˣ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => if j = p i then ((σ i : ℤ) : ℝ) else 0
theorem signedPermMatrix_mulVec (p : Equiv.Perm (Fin 4)) (σ : Fin 4 → ℤˣ) (x : Fin 4 → ℝ) :
    signedPermMatrix p σ *ᵥ x = signedCoordinateEquiv p σ x := by
  funext i
  rw [signedCoordinateEquiv_apply]
  simp [Matrix.mulVec, dotProduct, signedPermMatrix]
theorem intUnit_cast_mul_self (u : ℤˣ) : ((u : ℤ) : ℝ) * ((u : ℤ) : ℝ) = 1 := by
  rcases Int.units_eq_one_or u with h | h <;> simp [h]
theorem signedPermMatrix_mem_orthogonalGroup (p : Equiv.Perm (Fin 4)) (σ : Fin 4 → ℤˣ) :
    signedPermMatrix p σ ∈ Matrix.orthogonalGroup (Fin 4) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff]
  ext i k
  simp only [Matrix.mul_apply, Matrix.transpose_apply, signedPermMatrix, Matrix.one_apply]
  by_cases h : i = k
  · subst h
    simp [intUnit_cast_mul_self]
  · have hp : p i ≠ p k := fun hik => h (p.injective hik)
    rw [if_neg h]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : j = p i
    · subst hj
      simp [hp]
    · simp [hj]
theorem hyperoctahedral_isOrthogonalLinear (w : hyperoctahedral) : IsOrthogonalLinear w.1 := by
  obtain ⟨_, p, σ, rfl⟩ := w
  exact ⟨signedPermMatrix p σ, signedPermMatrix_mem_orthogonalGroup p σ,
    fun x => (signedPermMatrix_mulVec p σ x).symm⟩
theorem euclidNorm_hyperoctahedral (w : hyperoctahedral) (x : Fin 4 → ℝ) :
    euclidNorm (w.1 x) = euclidNorm x := by apply _root_.YangMills.Construction.GrowingTori.LatticeMotions.euclidNormVec_hyperoctahedral <;> assumption
theorem image_eq_of_forall_mapsTo {A : Set (Fin 4 → ℝ)}
    (h : ∀ (w : hyperoctahedral), ∀ x ∈ A, w.1 x ∈ A)
    (w : hyperoctahedral) : w.1 '' A = A := by
  refine Set.Subset.antisymm ?_ fun y hy => ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact h w x hx
  · refine ⟨(w⁻¹ : hyperoctahedral).1 y, h w⁻¹ y hy, ?_⟩
    exact show (w * w⁻¹ : hyperoctahedral).1 y = y from by simp
theorem hyperoctahedral_mapsTo_integerPoints (w : hyperoctahedral) :
    ∀ x ∈ integerPoints, w.1 x ∈ integerPoints := by
  obtain ⟨_, p, σ, rfl⟩ := w
  rintro _ ⟨k, rfl⟩
  refine ⟨fun μ => (σ μ : ℤ) * k (p μ), ?_⟩
  funext μ
  change (((σ μ : ℤ) * k (p μ) : ℤ) : ℝ) = signedCoordinateEquiv p σ _ μ
  rw [signedCoordinateEquiv_apply]
  push_cast
  rfl
theorem preservesLattices (D : TransportData) : HyperoctahedralPreservesLattices D := by
  intro w
  refine ⟨hyperoctahedral_isOrthogonalLinear w,
    image_eq_of_forall_mapsTo hyperoctahedral_mapsTo_integerPoints w,
    image_eq_of_forall_mapsTo (fun w x hx => D.hyperoctahedral_mem_periods w hx) w,
    fun ρ _ => ?_⟩
  refine image_eq_of_forall_mapsTo (fun w x hx => ?_) w
  change euclidNorm (w.1 x) < ρ
  rw [euclidNorm_hyperoctahedral]
  exact hx
theorem hyperoctahedral_add (w : hyperoctahedral) (x y : Fin 4 → ℝ) :
    w.1 (x + y) = w.1 x + w.1 y :=
  map_add (hyperoctahedralLinear w) x y
theorem hyperoctahedral_sub (w : hyperoctahedral) (x y : Fin 4 → ℝ) :
    w.1 (x - y) = w.1 x - w.1 y :=
  map_sub (hyperoctahedralLinear w) x y
theorem affinePair_comp (v v' : Fin 4 → ℝ) (w w' : hyperoctahedral) :
    affinePair v w ∘ affinePair v' w' = affinePair (w.1 v' + v) (w * w') := by
  funext x
  simp only [Function.comp, affinePair, hyperoctahedral_add, add_assoc]
  rfl
theorem affinePair_zero_one : affinePair 0 (1 : hyperoctahedral) = id := by
  funext x
  simp [affinePair]
theorem affineMotionsGroup_holds : AffineMotionsGroup := by
  refine ⟨fun s => ⟨?_, ?_⟩, ⟨⟨1, 0, affinePair_zero_one.symm⟩, ?_, ?_⟩, fun v => ?_,
    coe_mem_affineHyperoctahedral, hyperplaneReflect_mem_affineHyperoctahedral⟩
  · rintro ⟨w, v, rfl⟩
    obtain ⟨S, hS, h⟩ := hyperoctahedral_isOrthogonalLinear w
    exact ⟨S, hS, v, funext fun x => by simp [affinePair, orthoAffine, h], w, h⟩
  · rintro ⟨S, _, v, rfl, w, h⟩
    exact ⟨w, v, funext fun x => by simp [affinePair, orthoAffine, h]⟩
  · rintro _ ⟨w, v, rfl⟩ _ ⟨w', v', rfl⟩
    exact ⟨w * w', w.1 v' + v, affinePair_comp v v' w w'⟩
  · rintro _ ⟨w, v, rfl⟩
    have hl : w * w⁻¹ = 1 := mul_inv_cancel w
    have hr : w⁻¹ * w = 1 := inv_mul_cancel w
    have hwv : w.1 ((w⁻¹ : hyperoctahedral).1 v) = v := by
      exact show (w * w⁻¹ : hyperoctahedral).1 v = v from by simp
    refine ⟨_, ⟨w⁻¹, -(w⁻¹ : hyperoctahedral).1 v, rfl⟩, ?_, ?_⟩
    · rw [affinePair_comp, hl, ← affinePair_zero_one]
      congr 1
      have hneg : w.1 (-(w⁻¹ : hyperoctahedral).1 v) = -w.1 ((w⁻¹ : hyperoctahedral).1 v) :=
        map_neg (hyperoctahedralLinear w) _
      rw [hneg, hwv]
      simp
    · rw [affinePair_comp, hr, ← affinePair_zero_one]
      congr 1
      simp
  · exact ⟨1, v, funext fun x => by simp [affinePair]⟩
theorem periodDistances_hyperoctahedral (D : TransportData) (S : hyperoctahedral)
    (u : Fin 4 → ℝ) : D.periodDistances (S.1 u) = D.periodDistances u := by
  have key : ∀ (T : hyperoctahedral) (y : Fin 4 → ℝ),
      D.periodDistances y ⊆ D.periodDistances (T.1 y) := by
    rintro T y _ ⟨γ, hγ, rfl⟩
    refine ⟨T.1 γ, D.hyperoctahedral_mem_periods T hγ, ?_⟩
    change euclidNorm (T.1 y - T.1 γ) = euclidNorm (y - γ)
    rw [← hyperoctahedral_sub, euclidNorm_hyperoctahedral]
  refine Set.Subset.antisymm ?_ (key S u)
  have h := key S⁻¹ (S.1 u)
  have hu : (S⁻¹ : hyperoctahedral).1 (S.1 u) = u := by
    exact show (S⁻¹ * S : hyperoctahedral).1 u = u from by simp
  rwa [hu] at h
theorem motionsDescendToIsometries_holds (D : TransportData) : MotionsDescendToIsometries D := by
  intro s hs S v hsv
  have hd : ∀ x, D.torusMap s (D.projHom x) = D.projHom (s x) :=
    D.torusMap_projHom hs
  refine ⟨(preservesLattices D S).2.2.1, ⟨D.torusMap s, funext hd, fun Φ hΦ => ?_⟩,
    funext hd, fun ξ η => ?_⟩
  · exact D.eq_torusMap hs fun x => congrFun hΦ x
  · obtain ⟨x, rfl⟩ := D.projHom_surjective ξ
    obtain ⟨y, rfl⟩ := D.projHom_surjective η
    rw [hd, hd]
    have hxy : s x - s y = S.1 (x - y) := by
      subst hsv
      simp [affinePair, hyperoctahedral_sub]
    have h₁ := D.isLeast_torusDist (s x) (s y)
    rw [hxy, periodDistances_hyperoctahedral] at h₁
    exact h₁.unique (D.isLeast_torusDist x y)
theorem translationEquiv_mem (v : Fin 4 → ℝ) : ⇑(translationEquiv v) ∈ affineHyperoctahedral :=
  ⟨1, v, funext fun x => by simp [affinePair]⟩
theorem descendedGenerators_holds (D : TransportData) : DescendedGenerators D := by
  refine ⟨fun v => funext fun ξ => ?_, fun w => ⟨D.torusMap_hyperoctahedral w,
    D.torusMap_projHom (coe_mem_affineHyperoctahedral w)⟩, fun μ c => ⟨rfl,
    D.torusMap_projHom (hyperplaneReflect_mem_affineHyperoctahedral μ c)⟩⟩
  obtain ⟨x, rfl⟩ := D.projHom_surjective ξ
  rw [D.torusMap_projHom (translationEquiv_mem v), translationEquiv_apply, map_add]
theorem affineGroupOnTori_holds : AffineGroupOnTori := fun D =>
  ⟨preservesLattices D, affineMotionsGroup_holds, motionsDescendToIsometries_holds D,
    descendedGenerators_holds D⟩
end YangMills.Construction.TorusTransport.AffineGroup
end
