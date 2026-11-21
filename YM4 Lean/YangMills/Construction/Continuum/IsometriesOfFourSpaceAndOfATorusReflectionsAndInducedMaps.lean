import YangMills.Construction.Continuum.OperationsOnFunctionsOfSeveralPoints
import YangMills.Construction.Continuum.PeriodLatticeCoveringMapAndFlatDistance
import YangMills.Construction.Torus.LiftsAndInducedMaps
import YangMills.Construction.Towers.TowersOfLattices
import Mathlib
set_option autoImplicit false
open Matrix
noncomputable section
namespace YangMills.Construction
namespace TorusTransport
open YangMills.Construction.TorusMetric YangMills.Construction.TestFunctions
open YangMills.Construction.TorusLifts (hyperoctahedralGroupEuclidean signedCoordinateEquiv)
def orthoAffine (S : Matrix (Fin 4) (Fin 4) ℝ) (v x : Fin 4 → ℝ) : Fin 4 → ℝ := S *ᵥ x + v
def IsEuclideanMotion (s : (Fin 4 → ℝ) → Fin 4 → ℝ) : Prop :=
  ∃ S ∈ Matrix.orthogonalGroup (Fin 4) ℝ, ∃ v : Fin 4 → ℝ, s = orthoAffine S v
theorem euclidNorm_mulVec {S : Matrix (Fin 4) (Fin 4) ℝ}
    (hS : S ∈ Matrix.orthogonalGroup (Fin 4) ℝ) (x : Fin 4 → ℝ) :
    euclidNorm (S *ᵥ x) = euclidNorm x := by apply _root_.YangMills.Construction.ConfigSpace.euclidNormVec_orth_mulVec <;> assumption
theorem IsEuclideanMotion.isDistancePreserving {s : (Fin 4 → ℝ) → Fin 4 → ℝ}
    (hs : IsEuclideanMotion s) : YangMills.Construction.Tower.FullSpace.IsDistancePreserving s := by
  obtain ⟨S, hS, v, rfl⟩ := hs
  intro x y
  have e : orthoAffine S v x - orthoAffine S v y = S *ᵥ (x - y) := by
    simp [orthoAffine, Matrix.mulVec_sub]
  rw [e]
  exact euclidNorm_mulVec hS _
theorem orthoAffine_inverse {S : Matrix (Fin 4) (Fin 4) ℝ}
    (hS : S ∈ Matrix.orthogonalGroup (Fin 4) ℝ) (v : Fin 4 → ℝ) :
    Function.LeftInverse (fun y => Sᵀ *ᵥ (y - v)) (orthoAffine S v) ∧
      Function.RightInverse (fun y => Sᵀ *ᵥ (y - v)) (orthoAffine S v) := by
  have hT : Sᵀ * S = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin 4) ℝ).mp hS
  have hT' : S * Sᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (Fin 4) ℝ).mp hS
  constructor
  · intro x
    simp [orthoAffine, Matrix.mulVec_mulVec, hT]
  · intro y
    simp [orthoAffine, Matrix.mulVec_mulVec, hT']
theorem IsEuclideanMotion.bijective {s : (Fin 4 → ℝ) → Fin 4 → ℝ}
    (hs : IsEuclideanMotion s) : Function.Bijective s := by
  obtain ⟨S, hS, v, rfl⟩ := hs
  obtain ⟨h₁, h₂⟩ := orthoAffine_inverse hS v
  exact ⟨h₁.injective, h₂.surjective⟩
def IsEuclideanMotion.toPerm {s : (Fin 4 → ℝ) → Fin 4 → ℝ} (hs : IsEuclideanMotion s) :
    Equiv.Perm (Fin 4 → ℝ) :=
  Equiv.ofBijective s hs.bijective
@[simp] theorem IsEuclideanMotion.coe_toPerm {s : (Fin 4 → ℝ) → Fin 4 → ℝ}
    (hs : IsEuclideanMotion s) : ⇑hs.toPerm = s :=
  rfl
theorem isEuclideanMotion_orthoAffine {S : Matrix (Fin 4) (Fin 4) ℝ}
    (hS : S ∈ Matrix.orthogonalGroup (Fin 4) ℝ) (v : Fin 4 → ℝ) :
    IsEuclideanMotion (orthoAffine S v) :=
  ⟨S, hS, v, rfl⟩
theorem IsEuclideanMotion.symm {s : (Fin 4 → ℝ) → Fin 4 → ℝ}
    (hs : IsEuclideanMotion s) : IsEuclideanMotion hs.toPerm.symm := by
  obtain ⟨S, hS, v, rfl⟩ := id hs
  have hST : Sᵀ ∈ Matrix.orthogonalGroup (Fin 4) ℝ := by
    rw [Matrix.mem_orthogonalGroup_iff]
    simpa using (Matrix.mem_orthogonalGroup_iff' (Fin 4) ℝ).mp hS
  refine ⟨Sᵀ, hST, -(Sᵀ *ᵥ v), funext fun y => ?_⟩
  rw [Equiv.symm_apply_eq]
  have h := (orthoAffine_inverse hS v).2 y
  have e : orthoAffine Sᵀ (-(Sᵀ *ᵥ v)) y = Sᵀ *ᵥ (y - v) := by
    rw [Matrix.mulVec_sub, sub_eq_add_neg]
    rfl
  rw [e]
  exact h.symm
def translationEquiv (v : Fin 4 → ℝ) : Equiv.Perm (Fin 4 → ℝ) := Equiv.addRight v
@[simp] theorem translationEquiv_apply (v x : Fin 4 → ℝ) : translationEquiv v x = x + v :=
  rfl
namespace TransportData
variable (D : TransportData)
def IsTorusIsometry (f : D.Torus → D.Torus) : Prop :=
  ∀ ξ η, D.torusDist (f ξ) (f η) = D.torusDist ξ η
end TransportData
section Families
variable {ι E : Type*}
def familyComp (h : ι → (Fin 4 → ℝ) → E) (s : (Fin 4 → ℝ) → Fin 4 → ℝ) :
    ι → (Fin 4 → ℝ) → E :=
  fun i => h i ∘ s
def familyAct {s : (Fin 4 → ℝ) → Fin 4 → ℝ} (hs : IsEuclideanMotion s)
    (h : ι → (Fin 4 → ℝ) → E) : ι → (Fin 4 → ℝ) → E :=
  fun i => h i ∘ hs.toPerm.symm
end Families
def Domain.translateFn {E : Type*} (D : TransportData) :
    (Y : Domain) → Y.Point D → (Y.Point D → E) → Y.Point D → E
  | .euclidean, a, h => fun x => h ((x : Fin 4 → ℝ) - (a : Fin 4 → ℝ))
  | .torus, a, h => fun ξ => h ((ξ : D.Torus) - (a : D.Torus))
abbrev hyperoctahedral : Subgroup (Equiv.Perm (Fin 4 → ℝ)) := hyperoctahedralGroupEuclidean
theorem signedCoordinateEquiv_apply (π : Equiv.Perm (Fin 4)) (s : Fin 4 → ℤˣ) (x : Fin 4 → ℝ)
    (μ : Fin 4) : signedCoordinateEquiv π s x μ = ((s μ : ℤ) : ℝ) * x (π μ) :=
  rfl
theorem mem_hyperoctahedral_iff (w : Equiv.Perm (Fin 4 → ℝ)) :
    w ∈ hyperoctahedral ↔ ∃ (π : Equiv.Perm (Fin 4)) (ε : Fin 4 → ℝ),
      (∀ μ, ε μ = 1 ∨ ε μ = -1) ∧ ∀ (x : Fin 4 → ℝ) (μ : Fin 4), w x (π μ) = ε μ * x μ := by
  constructor
  · rintro ⟨p, s, rfl⟩
    refine ⟨p⁻¹, fun μ => ((s (p⁻¹ μ) : ℤ) : ℝ), fun μ => ?_, fun x μ => ?_⟩
    · show (((s (p⁻¹ μ) : ℤˣ) : ℤ) : ℝ) = 1 ∨ (((s (p⁻¹ μ) : ℤˣ) : ℤ) : ℝ) = -1
      rcases Int.units_eq_one_or (s (p⁻¹ μ)) with h | h
      · left
        rw [h]
        simp
      · right
        rw [h]
        simp
    · simp [signedCoordinateEquiv_apply]
  · rintro ⟨π, ε, hε, h⟩
    refine ⟨π⁻¹, fun ν => if ε (π⁻¹ ν) = 1 then 1 else -1, Equiv.ext fun x => ?_⟩
    funext ν
    have hν := h x (π⁻¹ ν)
    rw [show π (π⁻¹ ν) = ν from π.apply_symm_apply ν] at hν
    rw [hν, signedCoordinateEquiv_apply]
    show ε (π⁻¹ ν) * x (π⁻¹ ν) =
      (((if ε (π⁻¹ ν) = 1 then (1 : ℤˣ) else -1 : ℤˣ) : ℤ) : ℝ) * x (π⁻¹ ν)
    congr 1
    rcases hε (π⁻¹ ν) with e | e
    · rw [if_pos e, e]
      simp
    · rw [if_neg (by rw [e]; norm_num), e]
      simp
theorem mem_hyperoctahedral_iff_signedFrame (w : Equiv.Perm (Fin 4 → ℝ)) :
    w ∈ hyperoctahedral ↔
      ∃ r : YangMills.Construction.PeriodicLattice.SignedFrame, ⇑w = r.actOnVector := by
  constructor
  · rintro ⟨p, s, rfl⟩
    exact ⟨(p, s), rfl⟩
  · rintro ⟨r, h⟩
    exact ⟨r.1, r.2, Equiv.ext fun x => congrFun h x⟩
def hyperoctahedralLinear (w : hyperoctahedral) : (Fin 4 → ℝ) →ₗ[ℝ] Fin 4 → ℝ where
  toFun := w.1
  map_add' x y := by
    obtain ⟨_, p, s, rfl⟩ := w
    funext μ
    simp [signedCoordinateEquiv_apply, mul_add]
  map_smul' c x := by
    obtain ⟨_, p, s, rfl⟩ := w
    funext μ
    simp [signedCoordinateEquiv_apply, mul_left_comm]
@[simp] theorem coe_hyperoctahedralLinear (w : hyperoctahedral) :
    ⇑(hyperoctahedralLinear w) = w.1 :=
  rfl
def hyperplaneReflect (μ : Fin 4) (c : ℝ) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  x + (2 * (c - x μ)) • basisVec μ
theorem hyperplaneReflect_apply_self (μ : Fin 4) (c : ℝ) (x : Fin 4 → ℝ) :
    hyperplaneReflect μ c x μ = 2 * c - x μ := by
  simp [hyperplaneReflect, basisVec, YangMills.Construction.PeriodicLattice.coordVec]
  ring
theorem hyperplaneReflect_apply_of_ne {μ ν : Fin 4} (h : ν ≠ μ) (c : ℝ) (x : Fin 4 → ℝ) :
    hyperplaneReflect μ c x ν = x ν := by
  simp [hyperplaneReflect, basisVec, YangMills.Construction.PeriodicLattice.coordVec,
    Pi.single_eq_of_ne h]
def timeReflect : (Fin 4 → ℝ) → Fin 4 → ℝ := hyperplaneReflect 3 0
theorem timeReflect_apply (x : Fin 4 → ℝ) : timeReflect x = ![x 0, x 1, x 2, -x 3] := by
  funext ν
  fin_cases ν
  · exact hyperplaneReflect_apply_of_ne (by decide) 0 x
  · exact hyperplaneReflect_apply_of_ne (by decide) 0 x
  · exact hyperplaneReflect_apply_of_ne (by decide) 0 x
  · have h := hyperplaneReflect_apply_self 3 0 x
    simpa [timeReflect] using h
def coordNegation (μ : Fin 4) : hyperoctahedral :=
  ⟨signedCoordinateEquiv 1 fun ν => if ν = μ then -1 else 1, ⟨_, _, rfl⟩⟩
theorem coe_coordNegation (μ : Fin 4) : ⇑(coordNegation μ).1 = hyperplaneReflect μ 0 := by
  funext x ν
  by_cases h : ν = μ
  · subst h
    rw [hyperplaneReflect_apply_self]
    simp [coordNegation, signedCoordinateEquiv_apply]
  · rw [hyperplaneReflect_apply_of_ne h]
    simp [coordNegation, signedCoordinateEquiv_apply, h]
theorem exists_hyperoctahedral_eq_timeReflect : ∃ w : hyperoctahedral, ⇑w.1 = timeReflect :=
  ⟨coordNegation 3, coe_coordNegation 3⟩
def affinePair (v : Fin 4 → ℝ) (w : hyperoctahedral) (x : Fin 4 → ℝ) : Fin 4 → ℝ := w.1 x + v
def affineHyperoctahedral : Set ((Fin 4 → ℝ) → Fin 4 → ℝ) :=
  {s | ∃ (w : hyperoctahedral) (v : Fin 4 → ℝ), s = affinePair v w}
theorem coe_mem_affineHyperoctahedral (w : hyperoctahedral) : ⇑w.1 ∈ affineHyperoctahedral :=
  ⟨w, 0, funext fun x => by simp [affinePair]⟩
theorem hyperplaneReflect_eq (μ : Fin 4) (c : ℝ) (x : Fin 4 → ℝ) :
    hyperplaneReflect μ c x = hyperplaneReflect μ 0 x + (2 * c) • basisVec μ := by
  simp only [hyperplaneReflect]
  rw [add_assoc, ← add_smul]
  congr 2
  ring
theorem hyperplaneReflect_mem_affineHyperoctahedral (μ : Fin 4) (c : ℝ) :
    hyperplaneReflect μ c ∈ affineHyperoctahedral := by
  refine ⟨coordNegation μ, (2 * c) • basisVec μ, funext fun x => ?_⟩
  rw [affinePair, coe_coordNegation]
  exact hyperplaneReflect_eq μ c x
namespace TransportData
variable (D : TransportData)
theorem hyperoctahedral_mem_periods (w : hyperoctahedral) {γ : Fin 4 → ℝ}
    (hγ : γ ∈ D.periods) : w.1 γ ∈ D.periods := by
  obtain ⟨_, p, s, rfl⟩ := w
  obtain ⟨k, rfl⟩ := hγ
  refine ⟨fun μ => (s μ : ℤ) * k (p μ), ?_⟩
  funext μ
  simp only [YangMills.Construction.TestFunctions.latticeTranslate, signedCoordinateEquiv_apply,
    Int.cast_mul]
  ring
theorem projHom_affinePair_eq (w : hyperoctahedral) (v : Fin 4 → ℝ) {x y : Fin 4 → ℝ}
    (h : D.projHom x = D.projHom y) :
    D.projHom (affinePair v w x) = D.projHom (affinePair v w y) := by
  rw [projHom_eq_iff] at h ⊢
  have e : affinePair v w x - affinePair v w y = w.1 (x - y) := by
    have := map_sub (hyperoctahedralLinear w) x y
    simp only [coe_hyperoctahedralLinear] at this
    simp [affinePair, this]
  rw [e]
  exact D.hyperoctahedral_mem_periods w h
def torusMap (s : (Fin 4 → ℝ) → Fin 4 → ℝ) : D.Torus → D.Torus :=
  YangMills.Construction.TorusLifts.descendedMap
    (YangMills.Construction.PeriodicLattice.torusSide D.L D.m)
    (YangMills.Construction.PeriodicLattice.torusSide D.L D.m) s
theorem torusMap_projHom {s : (Fin 4 → ℝ) → Fin 4 → ℝ} (hs : s ∈ affineHyperoctahedral)
    (x : Fin 4 → ℝ) : D.torusMap s (D.projHom x) = D.projHom (s x) := by
  obtain ⟨w, v, rfl⟩ := hs
  exact D.projHom_affinePair_eq w v
    (YangMills.Construction.TestFunctions.torusProj_liftPoint (D.projHom x))
theorem eq_torusMap {s : (Fin 4 → ℝ) → Fin 4 → ℝ} (hs : s ∈ affineHyperoctahedral)
    {Φ : D.Torus → D.Torus} (h : ∀ x, Φ (D.projHom x) = D.projHom (s x)) :
    Φ = D.torusMap s := by
  funext ξ
  obtain ⟨x, rfl⟩ := D.projHom_surjective ξ
  rw [h, D.torusMap_projHom hs]
def hyperoctahedralOnTorus (w : hyperoctahedral) : D.Torus → D.Torus :=
  YangMills.Construction.TorusLifts.descendedMap
    (YangMills.Construction.PeriodicLattice.torusSide D.L D.m)
    (YangMills.Construction.PeriodicLattice.torusSide D.L D.m) w.1
theorem torusMap_hyperoctahedral (w : hyperoctahedral) :
    D.torusMap w.1 = D.hyperoctahedralOnTorus w :=
  rfl
def torusReflect (μ : Fin 4) (c : ℝ) : D.Torus → D.Torus := D.torusMap (hyperplaneReflect μ c)
end TransportData
end TorusTransport
end YangMills.Construction
end
