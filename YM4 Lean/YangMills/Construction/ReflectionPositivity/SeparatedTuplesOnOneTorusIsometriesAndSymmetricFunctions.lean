import YangMills.Construction.Lattice.SignedPermutationMatricesAndAffineHypercubicMaps
import YangMills.Construction.ReflectionPositivity.IsometriesCentringTuplesAndTheTwoFunctionals
import YangMills.Construction.ReflectionPositivity.OneTorusAllCutoffsPointsAndTheClassC1
import Mathlib
set_option autoImplicit false
open scoped ENNReal Matrix
noncomputable section
namespace YangMills.Construction
namespace ReflectionPositivity.TorusTuples
open ReflectionPositivity.TorusCutoffs
variable (s : Conventions.StandingParameters)
abbrev unitData : ReflectionPositivity.CutoffMirrors.MirrorData :=
  { toStandingParameters := s, coupling := 1, coupling_pos := one_pos, dir := 0 }
abbrev FnTuple (E : Type*) : Type _ := (unitData s).FunTuple E
variable {s}
abbrev supp {E : Type*} [Zero E] (h : s.Torus → E) : Set s.Torus := (unitData s).supp h
theorem mem_supp_iff {E : Type*} [Zero E] (h : s.Torus → E) (x : s.Torus) :
    x ∈ supp h ↔ ∀ r : ℝ, 0 < r → ∃ y, h y ≠ 0 ∧ (unitData s).torusDist x y < r :=
  Iff.rfl
def IsLipschitzReal (h : s.Torus → ℝ) : Prop :=
  TestFunctions.IsLipschitzFor (unitData s).torusDist h
def IsDisjointFamily {n : ℕ} (h : Fin n → s.Torus → ℝ) : Prop :=
  ReflectionPositivity.CutoffMirrors.MirrorData.IsAdmissibleArg (D := unitData s) h
def IsDisjointTuple (X : FnTuple s ℝ) : Prop := IsDisjointFamily (s := s) X.get
theorem isDisjointTuple_ofFn {n : ℕ} (f : Fin n → s.Torus → ℝ) :
    IsDisjointTuple (s := s) (List.ofFn f) ↔ IsDisjointFamily f := by
  have e : ∀ l : Fin (List.ofFn f).length,
      (List.ofFn f).get l = f (l.cast List.length_ofFn) := fun l => by
    simp only [List.get_eq_getElem, List.getElem_ofFn]
    rfl
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun l => ?_, fun l l' hl => ?_⟩
    · have := h₁ (l.cast List.length_ofFn.symm)
      rwa [e, Fin.cast_cast, Fin.cast_eq_self] at this
    · have := h₂ (l.cast List.length_ofFn.symm) (l'.cast List.length_ofFn.symm)
        (fun c => hl (Fin.cast_injective _ c))
      rwa [e, e, Fin.cast_cast, Fin.cast_cast, Fin.cast_eq_self, Fin.cast_eq_self] at this
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun l => ?_, fun l l' hl => ?_⟩
    · rw [e]
      exact h₁ _
    · rw [e, e]
      exact h₂ _ _ (fun c => hl (Fin.cast_injective _ c))
variable (s)
def disjointTuples (q : ℕ) : Set (FnTuple s ℝ) := {X | IsDisjointTuple X ∧ X.length = q}
variable {s}
def IsC1Tuple (X : FnTuple s ℝ) : Prop := ∀ h ∈ X, IsC1 (s := s) h
variable (s)
def disjointC1Tuples (q : ℕ) : Set (FnTuple s ℝ) :=
  {X | X ∈ disjointTuples s q ∧ IsC1Tuple X}
variable {s}
def gap (X : FnTuple s ℝ) : ℝ≥0∞ :=
  (Finset.univ.offDiag : Finset (Fin X.length × Fin X.length)).inf fun p =>
    setDist (supp (s := s) (X.get p.1)) (supp (s := s) (X.get p.2))
theorem exists_gap_eq {X : FnTuple s ℝ} (h : 2 ≤ X.length) :
    ∃ l l' : Fin X.length, l ≠ l' ∧
      gap X = setDist (supp (s := s) (X.get l)) (supp (s := s) (X.get l')) := by
  have hne : (Finset.univ.offDiag : Finset (Fin X.length × Fin X.length)).Nonempty :=
    ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp [Finset.mem_offDiag, Fin.ext_iff]⟩
  obtain ⟨p, hp, e⟩ := Finset.exists_mem_eq_inf _ hne fun p : Fin X.length × Fin X.length =>
    setDist (supp (s := s) (X.get p.1)) (supp (s := s) (X.get p.2))
  exact ⟨p.1, p.2, (Finset.mem_offDiag.mp hp).2.2, e⟩
def restrictTuple {E : Type*} (X : FnTuple s E) (J : Finset (Fin X.length)) : FnTuple s E :=
  List.ofFn fun k : Fin J.card => X.get (J.orderEmbOfFin rfl k)
def IsRestriction {E : Type*} (Y X : FnTuple s E) : Prop := ∃ J, Y = restrictTuple X J
variable (s)
def IsTorusIsometry (r : s.Torus → s.Torus) : Prop := (unitData s).IsDistPreserving r
variable {s}
def transport {E : Type*} (r : s.Torus ≃ s.Torus) (h : s.Torus → E) : s.Torus → E := h ∘ r.symm
def transportTuple {E : Type*} (r : s.Torus ≃ s.Torus) (X : FnTuple s E) : FnTuple s E :=
  X.map (transport r)
def shiftBy (v : s.Torus) : s.Torus ≃ s.Torus := Equiv.addRight v
theorem shiftBy_symm (v : s.Torus) : (shiftBy v).symm = shiftBy (-v) := by
  ext x : 1
  simp [shiftBy]
theorem transport_shiftBy {E : Type*} (v : s.Torus) (h : s.Torus → E) (x : s.Torus) :
    transport (shiftBy v) h x = h (x - v) := by
  simp [transport, shiftBy, sub_eq_add_neg]
variable (s)
def shiftByVector (v : Fin 4 → ℝ) : s.Torus ≃ s.Torus := shiftBy (proj s v)
def signedMatrixMap (w : Matrix (Fin 4) (Fin 4) ℝ) (x : s.Torus) : s.Torus :=
  proj s (w *ᵥ lift s x)
theorem proj_frame_mulVec (r : PeriodicLattice.SignedFrame) (y : Fin 4 → ℝ) :
    proj s (r.toMatrix *ᵥ y) =
      PeriodicLattice.signedCoordinatePerm s.L s.m r.1 r.2 (proj s y) := by
  rw [PeriodicLattice.SignedFrame.toMatrix_mulVec]
  funext μ
  change (((((r.2 μ : ℤˣ) : ℤ) : ℝ) * y (r.1 μ) : ℝ) :
      AddCircle (PeriodicLattice.torusSide s.L s.m)) =
    ((r.2 μ : ℤˣ) : ℤ) • ((y (r.1 μ) : ℝ) : AddCircle (PeriodicLattice.torusSide s.L s.m))
  rw [← zsmul_eq_mul]
  rfl
theorem signedMatrixMap_proj {w : Matrix (Fin 4) (Fin 4) ℝ}
    (hw : w ∈ PeriodicLattice.signedPermMatrices) (y : Fin 4 → ℝ) :
    signedMatrixMap s w (proj s y) = proj s (w *ᵥ y) := by
  obtain ⟨r, rfl⟩ := (PeriodicLattice.mem_signedPermMatrices_iff w).mp hw
  rw [signedMatrixMap, proj_frame_mulVec, proj_frame_mulVec, proj_lift]
theorem frame_invMatrix_mul (r : PeriodicLattice.SignedFrame) :
    PeriodicLattice.SignedFrame.toMatrix (r.1⁻¹, fun μ => r.2 (r.1⁻¹ μ)) * r.toMatrix = 1 := by
  apply Matrix.mulVec_injective
  funext x
  rw [← Matrix.mulVec_mulVec, PeriodicLattice.SignedFrame.toMatrix_mulVec,
    PeriodicLattice.SignedFrame.toMatrix_mulVec, Matrix.one_mulVec]
  funext μ
  have e : ∀ u : ℤˣ, ((u : ℤ) : ℝ) * ((u : ℤ) : ℝ) = 1 := fun u => by
    rcases Int.units_eq_one_or u with rfl | rfl <;> simp
  change ((r.2 (r.1⁻¹ μ) : ℤ) : ℝ) * (((r.2 (r.1⁻¹ μ) : ℤ) : ℝ) * x (r.1 (r.1⁻¹ μ))) = x μ
  rw [← mul_assoc, e, one_mul]
  exact congrArg x (r.1.apply_symm_apply μ)
theorem inv_mul_of_mem_signedPermMatrices {w : Matrix (Fin 4) (Fin 4) ℝ}
    (hw : w ∈ PeriodicLattice.signedPermMatrices) : w⁻¹ * w = 1 := by
  obtain ⟨r, rfl⟩ := (PeriodicLattice.mem_signedPermMatrices_iff w).mp hw
  rw [Matrix.inv_eq_left_inv (frame_invMatrix_mul r)]
  exact frame_invMatrix_mul r
theorem inv_mem_signedPermMatrices {w : Matrix (Fin 4) (Fin 4) ℝ}
    (hw : w ∈ PeriodicLattice.signedPermMatrices) :
    w⁻¹ ∈ PeriodicLattice.signedPermMatrices := by
  obtain ⟨r, rfl⟩ := (PeriodicLattice.mem_signedPermMatrices_iff w).mp hw
  rw [Matrix.inv_eq_left_inv (frame_invMatrix_mul r)]
  exact (PeriodicLattice.mem_signedPermMatrices_iff _).mpr ⟨_, rfl⟩
def signedMatrixEquiv {w : Matrix (Fin 4) (Fin 4) ℝ}
    (hw : w ∈ PeriodicLattice.signedPermMatrices) : s.Torus ≃ s.Torus where
  toFun := signedMatrixMap s w
  invFun := signedMatrixMap s w⁻¹
  left_inv x := by
    obtain ⟨y, rfl⟩ := exists_proj_eq s x
    rw [signedMatrixMap_proj s hw, signedMatrixMap_proj s (inv_mem_signedPermMatrices hw),
      Matrix.mulVec_mulVec, inv_mul_of_mem_signedPermMatrices hw, Matrix.one_mulVec]
  right_inv x := by
    obtain ⟨y, rfl⟩ := exists_proj_eq s x
    rw [signedMatrixMap_proj s (inv_mem_signedPermMatrices hw), signedMatrixMap_proj s hw,
      Matrix.mulVec_mulVec, mul_eq_one_comm.mp (inv_mul_of_mem_signedPermMatrices hw),
      Matrix.one_mulVec]
theorem signedMatrixEquiv_mem_hyperoctahedralGroup {w : Matrix (Fin 4) (Fin 4) ℝ}
    (hw : w ∈ PeriodicLattice.signedPermMatrices) :
    signedMatrixEquiv s hw ∈ PeriodicLattice.hyperoctahedralGroup s.L s.m := by
  obtain ⟨r, rfl⟩ := (PeriodicLattice.mem_signedPermMatrices_iff w).mp hw
  refine ⟨r.1, r.2, Equiv.ext fun x => ?_⟩
  obtain ⟨y, rfl⟩ := exists_proj_eq s x
  exact (signedMatrixMap_proj s hw y).trans (proj_frame_mulVec s r y)
variable {s}
theorem IsLipschitzReal.add {g g' : s.Torus → ℝ} (h : IsLipschitzReal g)
    (h' : IsLipschitzReal g') : IsLipschitzReal (g + g') := by
  obtain ⟨C, hC, hg⟩ := h
  obtain ⟨C', hC', hg'⟩ := h'
  refine ⟨C + C', add_nonneg hC hC', fun x y => ?_⟩
  calc ‖(g + g') x - (g + g') y‖ = ‖(g x - g y) + (g' x - g' y)‖ := by
        congr 1
        simp only [Pi.add_apply]
        ring
    _ ≤ ‖g x - g y‖ + ‖g' x - g' y‖ := norm_add_le _ _
    _ ≤ C * (unitData s).torusDist x y + C' * (unitData s).torusDist x y :=
        add_le_add (hg x y) (hg' x y)
    _ = (C + C') * (unitData s).torusDist x y := by ring
theorem IsLipschitzReal.smul {g : s.Torus → ℝ} (h : IsLipschitzReal g) (c : ℝ) :
    IsLipschitzReal (c • g) := by
  obtain ⟨C, hC, hg⟩ := h
  refine ⟨‖c‖ * C, mul_nonneg (norm_nonneg c) hC, fun x y => ?_⟩
  calc ‖(c • g) x - (c • g) y‖ = ‖c • (g x - g y)‖ := by
        simp only [Pi.smul_apply, smul_sub]
    _ = ‖c‖ * ‖g x - g y‖ := norm_smul _ _
    _ ≤ ‖c‖ * (C * (unitData s).torusDist x y) :=
        mul_le_mul_of_nonneg_left (hg x y) (norm_nonneg c)
    _ = ‖c‖ * C * (unitData s).torusDist x y := by ring
theorem supp_add_subset (g g' : s.Torus → ℝ) :
    supp (g + g') ⊆ supp g ∪ supp g' := by
  intro x hx
  by_contra hc
  rw [Set.mem_union, not_or, mem_supp_iff, mem_supp_iff] at hc
  obtain ⟨h₁, h₂⟩ := hc
  push Not at h₁ h₂
  obtain ⟨r, hr, h₁⟩ := h₁
  obtain ⟨r', hr', h₂⟩ := h₂
  obtain ⟨y, hy, hd⟩ := (mem_supp_iff _ x).mp hx (min r r') (lt_min hr hr')
  by_cases hgy : g y = 0
  · have hg'y : g' y ≠ 0 := fun e => hy (by simp [hgy, e])
    exact absurd (lt_of_lt_of_le hd (min_le_right _ _)) (not_lt.mpr (h₂ y hg'y))
  · exact absurd (lt_of_lt_of_le hd (min_le_left _ _)) (not_lt.mpr (h₁ y hgy))
theorem supp_smul_subset (g : s.Torus → ℝ) (c : ℝ) : supp (c • g) ⊆ supp g := by
  intro x hx
  refine (mem_supp_iff _ x).mpr fun r hr => ?_
  obtain ⟨y, hy, hd⟩ := (mem_supp_iff _ x).mp hx r hr
  exact ⟨y, fun e => hy (by simp [e]), hd⟩
theorem IsDisjointFamily.update_of_supp_subset {n : ℕ} {f : Fin n → s.Torus → ℝ} {i : Fin n}
    {g g' G : s.Torus → ℝ} (h : IsDisjointFamily (Function.update f i g))
    (h' : IsDisjointFamily (Function.update f i g')) (hG : IsLipschitzReal G)
    (hs : supp G ⊆ supp g ∪ supp g') : IsDisjointFamily (Function.update f i G) := by
  have key : ∀ l, l ≠ i → supp G ∩ supp (f l) = ∅ := by
    intro l hl
    have a := h.2 i l hl.symm
    have b := h'.2 i l hl.symm
    rw [Function.update_self, Function.update_of_ne hl] at a b
    refine Set.eq_empty_of_forall_notMem fun x hx => ?_
    rcases hs hx.1 with p | p
    · exact Set.eq_empty_iff_forall_notMem.mp a x ⟨p, hx.2⟩
    · exact Set.eq_empty_iff_forall_notMem.mp b x ⟨p, hx.2⟩
  refine ⟨fun l => ?_, fun l l' hl => ?_⟩
  · by_cases e : l = i
    · subst e
      rw [Function.update_self]
      exact hG
    · have a := h.1 l
      rw [Function.update_of_ne e] at a ⊢
      exact a
  · by_cases e : l = i
    · subst e
      rw [Function.update_self, Function.update_of_ne hl.symm]
      exact key l' hl.symm
    · by_cases e' : l' = i
      · subst e'
        rw [Function.update_self, Function.update_of_ne e, Set.inter_comm]
        exact key l e
      · have a := h.2 l l' hl
        rw [Function.update_of_ne e, Function.update_of_ne e'] at a ⊢
        exact a
theorem IsDisjointFamily.update_add {n : ℕ} {f : Fin n → s.Torus → ℝ} {i : Fin n}
    {g g' : s.Torus → ℝ} (h : IsDisjointFamily (Function.update f i g))
    (h' : IsDisjointFamily (Function.update f i g')) :
    IsDisjointFamily (Function.update f i (g + g')) := by
  have a : IsLipschitzReal g := by
    have e := h.1 i
    rwa [Function.update_self] at e
  have b : IsLipschitzReal g' := by
    have e := h'.1 i
    rwa [Function.update_self] at e
  exact h.update_of_supp_subset h' (a.add b) (supp_add_subset g g')
theorem IsDisjointFamily.update_smul {n : ℕ} {f : Fin n → s.Torus → ℝ} {i : Fin n}
    {g : s.Torus → ℝ} (h : IsDisjointFamily (Function.update f i g)) (c : ℝ) :
    IsDisjointFamily (Function.update f i (c • g)) := by
  have a : IsLipschitzReal g := by
    have e := h.1 i
    rwa [Function.update_self] at e
  exact h.update_of_supp_subset h (a.smul c)
    ((supp_smul_subset g c).trans Set.subset_union_left)
def disjointTupleOf {n : ℕ} (f : Fin n → s.Torus → ℝ) (hf : IsDisjointFamily f) :
    disjointTuples s n :=
  ⟨List.ofFn f, (isDisjointTuple_ofFn f).mpr hf, List.length_ofFn⟩
def IsMultilinear {n : ℕ} (Φ : disjointTuples s n → ℝ) : Prop :=
  ∀ (i : Fin n) (f : Fin n → s.Torus → ℝ) (g g' : s.Torus → ℝ), (∀ l, IsLipschitzReal (f l)) →
    IsLipschitzReal g → IsLipschitzReal g' →
    ∀ (hg : IsDisjointFamily (Function.update f i g))
      (hg' : IsDisjointFamily (Function.update f i g')),
      Φ (disjointTupleOf _ (hg.update_add hg')) =
          Φ (disjointTupleOf _ hg) + Φ (disjointTupleOf _ hg') ∧
        ∀ c : ℝ, Φ (disjointTupleOf _ (hg.update_smul c)) = c * Φ (disjointTupleOf _ hg)
def componentFamily {E : Type*} {n : ℕ} (X : FnTuple s E) (h : X.length = n) :
    Fin n → s.Torus → E :=
  fun l => X.get (l.cast h.symm)
theorem ofFn_componentFamily {E : Type*} {n : ℕ} (X : FnTuple s E) (h : X.length = n) :
    List.ofFn (componentFamily X h) = X := by
  subst h
  exact List.ofFn_get X
theorem isDisjointFamily_componentFamily {n : ℕ} (X : disjointTuples s n) :
    IsDisjointFamily (componentFamily X.1 X.2.2) :=
  (isDisjointTuple_ofFn _).mp (by rw [ofFn_componentFamily]; exact X.2.1)
variable (s)
end ReflectionPositivity.TorusTuples
end YangMills.Construction
end
