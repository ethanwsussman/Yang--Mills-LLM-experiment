import YangMills.Construction.InfiniteLattice.BondsPlaquettesCircuitsAndConfigurationsOfTheLatticeOfACutoff
import YangMills.Construction.Lattice.ElementarySquareCorners
import YangMills.Construction.Lattice.LatticeIsometriesAsMapsOfPairs
import Mathlib
set_option autoImplicit false
open Function Set
noncomputable section
namespace YangMills.Construction
namespace RefinedLatticeSymmetries
open InfiniteLattice CutoffLatticeStates
section
variable {a : ℝ}
theorem comp_mem_hypercubicGroup {w w' : AmbientSpace →ₗ[ℝ] AmbientSpace} (hw : w ∈ hypercubicGroup)
    (hw' : w' ∈ hypercubicGroup) : w ∘ₗ w' ∈ hypercubicGroup := by
  obtain ⟨σ, h⟩ := hw
  obtain ⟨σ', h'⟩ := hw'
  refine ⟨σ'.trans σ, fun κ => ?_⟩
  rcases h' κ with e | e <;> rcases h (σ' κ) with f | f <;>
    simp [LinearMap.comp_apply, e, f, map_neg]
theorem exists_inverse_of_mem_hypercubicGroup {w : AmbientSpace →ₗ[ℝ] AmbientSpace}
    (hw : w ∈ hypercubicGroup) :
    ∃ w₁ ∈ hypercubicGroup, w₁ ∘ₗ w = LinearMap.id ∧ w ∘ₗ w₁ = LinearMap.id := by
  obtain ⟨f, rfl⟩ := exists_frameLinearMap_eq_of_mem_hypercubicGroup hw
  have hunit : ∀ μ, ((f.2 μ : ℤ) : ℝ) * ((f.2 μ : ℤ) : ℝ) = 1 := fun μ => by
    rcases Int.units_eq_one_or (f.2 μ) with hs | hs <;> simp [hs]
  have e₁ : ∀ ν, f.1 (f.1⁻¹ ν) = ν := fun ν => f.1.apply_symm_apply ν
  have e₂ : ∀ μ, f.1⁻¹ (f.1 μ) = μ := fun μ => f.1.symm_apply_apply μ
  refine ⟨frameLinearMap (f.1⁻¹, fun ν => f.2 (f.1⁻¹ ν)), frameLinearMap_mem_hypercubicGroup _,
    LinearMap.ext fun x => funext fun ν => ?_, LinearMap.ext fun x => funext fun μ => ?_⟩
  · simp only [frameLinearMap, PeriodicLattice.SignedFrame.actOnVector, LinearMap.comp_apply,
      LinearMap.coe_mk, AddHom.coe_mk, LinearMap.id_apply, e₁]
    rw [← mul_assoc, hunit, one_mul]
  · simp only [frameLinearMap, PeriodicLattice.SignedFrame.actOnVector, LinearMap.comp_apply,
      LinearMap.coe_mk, AddHom.coe_mk, LinearMap.id_apply, e₂]
    rw [← mul_assoc, hunit, one_mul]
theorem apply_mem_latticeSubgroup {w : AmbientSpace →ₗ[ℝ] AmbientSpace} (hw : w ∈ hypercubicGroup)
    {x : AmbientSpace} (hx : x ∈ latticeSubgroup a) : w x ∈ latticeSubgroup a := by
  have hr : (fun y => w y) ∈ latticeMotions a :=
    ⟨w, hw, 0, zero_mem _, fun y => by simp⟩
  have h : (fun y => w y) x ∈ (fun y => w y) '' (latticeSubgroup a : Set AmbientSpace) :=
    ⟨x, hx, rfl⟩
  rw [LatticeMotion.image_latticeSubgroup hr] at h
  exact h
theorem exists_isAffineDecomposition (r : latticeMotions a) :
    ∃ (w : AmbientSpace →ₗ[ℝ] AmbientSpace) (v : AmbientSpace),
      IsAffineDecomposition a r.1 (w, v) := by
  obtain ⟨w, hw, v, hv, h⟩ := r.2
  exact ⟨w, v, hw, hv, h⟩
theorem isAffineDecomposition_unique {r : AmbientSpace → AmbientSpace}
    {q q' : (AmbientSpace →ₗ[ℝ] AmbientSpace) × AmbientSpace}
    (h : IsAffineDecomposition a r q) (h' : IsAffineDecomposition a r q') : q = q' := by
  have hv : q.2 = q'.2 := by
    have h₁ := h.2.2 0
    have h₂ := h'.2.2 0
    simp only [map_zero, zero_add] at h₁ h₂
    rw [← h₁, ← h₂]
  refine Prod.ext (LinearMap.ext fun x => ?_) hv
  have h₁ := h.2.2 x
  have h₂ := h'.2.2 x
  rw [h₁, hv] at h₂
  exact add_right_cancel h₂
theorem apply_add_of_decomposition {r : AmbientSpace → AmbientSpace}
    {w : AmbientSpace →ₗ[ℝ] AmbientSpace} {v : AmbientSpace}
    (h : IsAffineDecomposition a r (w, v)) (y ζ : AmbientSpace) : r (y + ζ) = r y + w ζ := by
  have h₁ := h.2.2 (y + ζ)
  have h₂ := h.2.2 y
  simp only at h₁ h₂
  rw [h₁, h₂, map_add]
  abel
theorem id_mem_latticeMotions : (id : AmbientSpace → AmbientSpace) ∈ latticeMotions a :=
  ⟨LinearMap.id, ⟨1, fun κ => Or.inl rfl⟩, 0, zero_mem _, fun x => by simp⟩
theorem isAffineDecomposition_comp {r r' : AmbientSpace → AmbientSpace}
    {w w' : AmbientSpace →ₗ[ℝ] AmbientSpace} {v v' : AmbientSpace}
    (h : IsAffineDecomposition a r (w, v)) (h' : IsAffineDecomposition a r' (w', v')) :
    IsAffineDecomposition a (r ∘ r') (w ∘ₗ w', w v' + v) := by
  refine ⟨comp_mem_hypercubicGroup h.1 h'.1,
    add_mem (apply_mem_latticeSubgroup h.1 h'.2.1) h.2.1, fun x => ?_⟩
  have h₁ := h'.2.2 x
  simp only at h₁
  simp only [comp_apply, LinearMap.comp_apply, h₁, h.2.2 (w' x + v'), map_add]
  abel
theorem comp_mem_latticeMotions {t t' : AmbientSpace → AmbientSpace} (ht : t ∈ latticeMotions a)
    (ht' : t' ∈ latticeMotions a) : t ∘ t' ∈ latticeMotions a := by
  obtain ⟨w, hw, v, hv, h⟩ := ht
  obtain ⟨w', hw', v', hv', h'⟩ := ht'
  have hp := isAffineDecomposition_comp (a := a) (r := t) (r' := t') (w := w) (w' := w')
    (v := v) (v' := v') ⟨hw, hv, h⟩ ⟨hw', hv', h'⟩
  exact ⟨_, hp.1, _, hp.2.1, hp.2.2⟩
theorem exists_inverse_of_decomposition {r : AmbientSpace → AmbientSpace}
    {w : AmbientSpace →ₗ[ℝ] AmbientSpace} {v : AmbientSpace}
    (h : IsAffineDecomposition a r (w, v)) :
    ∃ w₁ : AmbientSpace →ₗ[ℝ] AmbientSpace, w₁ ∘ₗ w = LinearMap.id ∧ w ∘ₗ w₁ = LinearMap.id ∧
      IsAffineDecomposition a (fun x => w₁ x + -w₁ v) (w₁, -w₁ v) ∧
      LeftInverse (fun x => w₁ x + -w₁ v) r ∧ RightInverse (fun x => w₁ x + -w₁ v) r := by
  obtain ⟨w₁, hw₁, h₁, h₂⟩ := exists_inverse_of_mem_hypercubicGroup h.1
  have hl : ∀ x, w₁ (w x) = x := fun x => LinearMap.congr_fun h₁ x
  have hr : ∀ x, w (w₁ x) = x := fun x => LinearMap.congr_fun h₂ x
  have hrx : ∀ x, r x = w x + v := h.2.2
  refine ⟨w₁, h₁, h₂, ⟨hw₁, neg_mem (apply_mem_latticeSubgroup hw₁ h.2.1), fun x => rfl⟩,
    fun x => ?_, fun x => ?_⟩
  · simp [hrx, hl]
  · simp [hrx, hr]
theorem bijective_latticeMotion (r : latticeMotions a) : Bijective r.1 := by
  obtain ⟨w, v, h⟩ := exists_isAffineDecomposition r
  obtain ⟨w₁, -, -, -, hl, hr⟩ := exists_inverse_of_decomposition h
  exact ⟨hl.injective, hr.surjective⟩
theorem motionInverse_leftInverse (r : latticeMotions a) : LeftInverse (motionInverse r) r.1 :=
  leftInverse_invFun (bijective_latticeMotion r).1
theorem motionInverse_rightInverse (r : latticeMotions a) : RightInverse (motionInverse r) r.1 :=
  rightInverse_invFun (bijective_latticeMotion r).2
theorem motionInverse_eq_of_rightInverse {r : latticeMotions a} {g : AmbientSpace → AmbientSpace}
    (hr : RightInverse g r.1) : motionInverse r = g :=
  funext fun x => by
    have h := motionInverse_leftInverse r (g x)
    rwa [hr x] at h
theorem motionInverse_mem (r : latticeMotions a) :
    motionInverse r ∈ latticeMotions a := by
  obtain ⟨w, v, h⟩ := exists_isAffineDecomposition r
  obtain ⟨w₁, -, -, hp, -, hr⟩ := exists_inverse_of_decomposition h
  rw [motionInverse_eq_of_rightInverse hr]
  exact ⟨_, hp.1, _, hp.2.1, hp.2.2⟩
def latticeMotionInv (r : latticeMotions a) : latticeMotions a :=
  ⟨motionInverse r, motionInverse_mem r⟩
end
open InfiniteLattice CutoffLatticeStates
theorem motionsActOnSpace_holds (L m K : ℕ) : MotionsActOnSpace L m K := by
  refine ⟨id_mem_latticeMotions, fun t ht t' ht' => comp_mem_latticeMotions ht ht', fun r => ?_⟩
  obtain ⟨w₀, v₀, h₀⟩ := exists_isAffineDecomposition r
  refine ⟨⟨(w₀, v₀), h₀, fun q hq => isAffineDecomposition_unique hq h₀⟩,
    bijective_latticeMotion r, LatticeMotion.euclidNormVec_sub r.2,
    LatticeMotion.image_latticeSubgroup r.2, motionInverse_mem r, motionInverse_leftInverse r,
    motionInverse_rightInverse r, fun x => ?_, fun w v h => ?_⟩
  · have hp := isAffineDecomposition_affineDecomposition r
    rw [hp.2.2 x]
    exact (torusAffineMap_torusProj L m hp.1 _ x).symm
  · obtain ⟨w₁, h₁, h₂, hp, -, hr⟩ := exists_inverse_of_decomposition h
    refine ⟨apply_add_of_decomposition h, fun r' w' v' h' => isAffineDecomposition_comp h h',
      w₁, h₁, h₂, ?_⟩
    rw [motionInverse_eq_of_rightInverse hr]
    exact hp
section
variable {L K : ℕ}
theorem meshSite_neg (e : MeshStep L K) : meshSite (-e) = -meshSite e := Subtype.ext rfl
theorem meshStep_neg_neg (e : MeshStep L K) : -(-e) = e := Subtype.ext (neg_neg e.1)
theorem meshSite_axisStep (μ : Fin 4) :
    meshSite (RefinedLatticeSymmetries.axisStep L K μ) =
      InfiniteLattice.axisStep (refinedSpacing L K) μ := Subtype.ext rfl
theorem exists_meshStep_terminal (b : Link (refinedSpacing L K)) :
    ∃ e : MeshStep L K, b.terminal = b.initial + meshSite e := by
  obtain ⟨μ, h | h⟩ := b.isAdjacent
  · refine ⟨RefinedLatticeSymmetries.axisStep L K μ, ?_⟩
    rw [meshSite_axisStep, ← h]
    abel
  · refine ⟨-RefinedLatticeSymmetries.axisStep L K μ, ?_⟩
    rw [meshSite_neg, meshSite_axisStep, ← h]
    abel
theorem linkAlong_inj {y y' : LatticePoint (refinedSpacing L K)} {e e' : MeshStep L K}
    (h : linkAlong y e = linkAlong y' e') : y = y' ∧ e = e' := by
  have h₁ : y = y' := congrArg Link.initial h
  have h₂ : y + meshSite e = y' + meshSite e' := congrArg Link.terminal h
  subst h₁
  have h₃ : meshSite e = meshSite e' := add_left_cancel h₂
  have h₄ : ((meshSite e : LatticePoint _) : AmbientSpace) = meshSite e' :=
    congrArg Subtype.val h₃
  exact ⟨rfl, Subtype.ext h₄⟩
theorem opposite_linkAlong (y : LatticePoint (refinedSpacing L K)) (e : MeshStep L K) :
    (linkAlong y e).opposite = linkAlong (y + meshSite e) (-e) := by
  refine Link.ext rfl ?_
  change y = y + meshSite e + meshSite (-e)
  rw [meshSite_neg]
  abel
theorem isPositivelyOriented_linkAlong (y : LatticePoint (refinedSpacing L K)) (e : MeshStep L K) :
    (linkAlong y e).IsPositivelyOriented ↔ ∃ μ, e = RefinedLatticeSymmetries.axisStep L K μ := by
  have hd : (linkAlong y e).terminal - (linkAlong y e).initial = meshSite e := by
    change y + meshSite e - y = meshSite e
    abel
  constructor
  · rintro ⟨μ, hμ⟩
    rw [hd] at hμ
    have h₄ : ((meshSite e : LatticePoint _) : AmbientSpace) =
        InfiniteLattice.axisStep (refinedSpacing L K) μ :=
      congrArg Subtype.val hμ
    exact ⟨μ, Subtype.ext h₄⟩
  · rintro ⟨μ, rfl⟩
    exact ⟨μ, by rw [hd, meshSite_axisStep]⟩
theorem linkImage_comp (r r' t : RefinedMotion L K) (h : t.1 = r.1 ∘ r'.1)
    (b : Link (refinedSpacing L K)) : linkImage t b = linkImage r (linkImage r' b) :=
  Link.ext (Subtype.ext (congrFun h b.initial)) (Subtype.ext (congrFun h b.terminal))
theorem linkImage_leftInverse (r t : RefinedMotion L K) (h : t.1 = motionInverse r) :
    LeftInverse (linkImage t) (linkImage r) := fun b =>
  Link.ext (Subtype.ext (by
      change t.1 (r.1 b.initial) = b.initial
      rw [h]
      exact motionInverse_leftInverse r _))
    (Subtype.ext (by
      change t.1 (r.1 b.terminal) = b.terminal
      rw [h]
      exact motionInverse_leftInverse r _))
theorem linkImage_rightInverse (r t : RefinedMotion L K) (h : t.1 = motionInverse r) :
    RightInverse (linkImage t) (linkImage r) := fun b =>
  Link.ext (Subtype.ext (by
      change r.1 (t.1 b.initial) = b.initial
      rw [h]
      exact motionInverse_rightInverse r _))
    (Subtype.ext (by
      change r.1 (t.1 b.terminal) = b.terminal
      rw [h]
      exact motionInverse_rightInverse r _))
theorem meshVector_eq_smul (j : ℤ) (μ : Fin 4) :
    PeriodicLattice.PlaquetteCircuits.meshVector L j μ =
      PeriodicLattice.meshSize L j • basisVector μ := by
  funext ν
  by_cases h : ν = μ
  · subst h
    simp [PeriodicLattice.PlaquetteCircuits.meshVector, basisVector]
  · simp [PeriodicLattice.PlaquetteCircuits.meshVector, basisVector, Pi.single_eq_of_ne h]
theorem isAlongAxis_map {w : AmbientSpace →ₗ[ℝ] AmbientSpace} {j : ℤ} {κ ρ : Fin 4}
    {e : AmbientSpace}
    (hκ : w (basisVector κ) = basisVector ρ ∨ w (basisVector κ) = -basisVector ρ)
    (he : PeriodicLattice.PlaquetteCircuits.IsAlongAxis e L j κ) :
    PeriodicLattice.PlaquetteCircuits.IsAlongAxis (w e) L j ρ := by
  unfold PeriodicLattice.PlaquetteCircuits.IsAlongAxis at he ⊢
  rcases he with rfl | rfl <;> rcases hκ with h | h <;>
    simp [meshVector_eq_smul, map_smul, map_neg, h]
theorem map_mem_meshVectors {w : AmbientSpace →ₗ[ℝ] AmbientSpace} (hw : w ∈ hypercubicGroup)
    {j : ℤ} {e : AmbientSpace} (he : e ∈ PeriodicLattice.PlaquetteCircuits.meshVectors L j) :
    w e ∈ PeriodicLattice.PlaquetteCircuits.meshVectors L j := by
  obtain ⟨σ, h⟩ := hw
  obtain ⟨μ, hμ⟩ := he
  exact ⟨σ μ, isAlongAxis_map (h μ) hμ⟩
theorem image_meshVectors {w : AmbientSpace →ₗ[ℝ] AmbientSpace} (hw : w ∈ hypercubicGroup)
    (j : ℤ) :
    w '' PeriodicLattice.PlaquetteCircuits.meshVectors L j =
      PeriodicLattice.PlaquetteCircuits.meshVectors L j := by
  obtain ⟨w₁, hw₁, -, h₂⟩ := exists_inverse_of_mem_hypercubicGroup hw
  ext x
  constructor
  · rintro ⟨e, he, rfl⟩
    exact map_mem_meshVectors hw he
  · intro hx
    exact ⟨w₁ x, map_mem_meshVectors hw₁ hx, LinearMap.congr_fun h₂ x⟩
theorem linkImage_linkAlong (r : RefinedMotion L K) {w : AmbientSpace →ₗ[ℝ] AmbientSpace}
    {v : AmbientSpace} (h : IsAffineDecomposition (refinedSpacing L K) r.1 (w, v))
    (y : LatticePoint (refinedSpacing L K)) (e f : MeshStep L K) (hf : f.1 = w e.1) :
    linkImage r (linkAlong y e) = linkAlong (pointImage r y) f := by
  refine Link.ext rfl (Subtype.ext ?_)
  change r.1 ((y : AmbientSpace) + e.1) = r.1 y + f.1
  rw [apply_add_of_decomposition h, hf]
end
theorem linksUnderMotions_holds (L K : ℕ) : LinksUnderMotions L K := by
  refine ⟨fun b => ?_, isPositivelyOriented_linkAlong, opposite_linkAlong, fun r =>
    ⟨fun b => rfl, linkImage_comp r, ?_, fun t h => ⟨linkImage_leftInverse r t h,
      linkImage_rightInverse r t h⟩, fun w v h => ⟨image_meshVectors h.1 _,
        fun y e f hf => linkImage_linkAlong r h y e f hf⟩⟩⟩
  · obtain ⟨e, he⟩ := exists_meshStep_terminal b
    refine ⟨(b.initial, e), Link.ext rfl he.symm, ?_⟩
    rintro ⟨y, e'⟩ hq
    have hb : linkAlong y e' = linkAlong b.initial e := hq.trans (Link.ext rfl he)
    obtain ⟨h₁, h₂⟩ := linkAlong_inj hb
    exact Prod.ext h₁ h₂
  · have hl := linkImage_leftInverse r (latticeMotionInv r) rfl
    have hr := linkImage_rightInverse r (latticeMotionInv r) rfl
    exact ⟨hl.injective, hr.surjective⟩
section
variable {a : ℝ}
theorem corner_plaquetteOfAxes (x : LatticePoint a) (μ ν : Fin 4) (h : μ ≠ ν) :
    (plaquetteOfAxes x μ ν h).corner = x := by
  unfold plaquetteOfAxes
  split_ifs <;> rfl
theorem axes_plaquetteOfAxes (x : LatticePoint a) (μ ν : Fin 4) (h : μ ≠ ν) :
    s((plaquetteOfAxes x μ ν h).lowAxis, (plaquetteOfAxes x μ ν h).highAxis) = s(μ, ν) := by
  unfold plaquetteOfAxes
  split_ifs
  · rfl
  · exact Sym2.eq_swap
theorem plaquetteOfAxes_self (p : ElementaryPlaquette a) :
    plaquetteOfAxes p.corner p.lowAxis p.highAxis p.lowAxis_lt_highAxis.ne = p := by
  unfold plaquetteOfAxes
  rw [dif_pos p.lowAxis_lt_highAxis]
theorem center_plaquetteOfAxes (x : LatticePoint a) (μ ν : Fin 4) (h : μ ≠ ν) :
    (plaquetteOfAxes x μ ν h).center =
      (x : AmbientSpace) + Pi.single μ (a / 2) + Pi.single ν (a / 2) := by
  unfold plaquetteOfAxes ElementaryPlaquette.center
  split_ifs
  · rfl
  · exact add_right_comm _ _ _
theorem center_injective (ha : a ≠ 0) :
    Injective (ElementaryPlaquette.center : ElementaryPlaquette a → AmbientSpace) := by
  intro p q h
  obtain ⟨n, hn⟩ := p.corner.2
  obtain ⟨n', hn'⟩ := q.corner.2
  have key : ∀ i, 2 * n i + (if i = p.lowAxis then 1 else 0) +
      (if i = p.highAxis then 1 else 0) =
      2 * n' i + (if i = q.lowAxis then 1 else 0) + (if i = q.highAxis then 1 else 0) := by
    intro i
    have hi := congrFun h i
    simp only [ElementaryPlaquette.center, Pi.add_apply, hn, hn', Pi.single_apply] at hi
    have hz : ((2 * n i + (if i = p.lowAxis then 1 else 0) +
        (if i = p.highAxis then 1 else 0) : ℤ) : ℝ) * a =
        ((2 * n' i + (if i = q.lowAxis then 1 else 0) +
          (if i = q.highAxis then 1 else 0) : ℤ) : ℝ) * a := by
      push_cast
      split_ifs at hi ⊢ <;> linarith
    exact_mod_cast mul_right_cancel₀ ha hz
  have hp := p.lowAxis_lt_highAxis
  have hq := q.lowAxis_lt_highAxis
  have hmem : ∀ i, (i = p.lowAxis ∨ i = p.highAxis) ↔ (i = q.lowAxis ∨ i = q.highAxis) := by
    intro i
    have hk := key i
    have hp' := hp.ne
    have hq' := hq.ne
    grind
  have e₁ := (hmem p.lowAxis).1 (Or.inl rfl)
  have e₂ := (hmem p.highAxis).1 (Or.inr rfl)
  have hfs : p.lowAxis = q.lowAxis ∧ p.highAxis = q.highAxis := by
    rcases e₁ with e₁ | e₁ <;> rcases e₂ with e₂ | e₂
    · exact absurd hp (by rw [e₁, e₂]; exact lt_irrefl _)
    · exact ⟨e₁, e₂⟩
    · exact absurd hp (by rw [e₁, e₂]; exact hq.not_gt)
    · exact absurd hp (by rw [e₁, e₂]; exact lt_irrefl _)
  refine ElementaryPlaquette.ext (Subtype.ext (funext fun i => ?_)) hfs.1 hfs.2
  have hk := key i
  rw [← hfs.1, ← hfs.2] at hk
  have hni : n i = n' i := by omega
  rw [hn, hn', hni]
end
theorem closedSquare_injective {L : ℕ} (hc : ElementarySquare.ElementarySquareStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (K : ℕ) :
    Injective (ElementaryPlaquette.closedSquare :
      ElementaryPlaquette (refinedSpacing L K) → Set AmbientSpace) := by
  intro p q h
  have hA := (hc L hL 1 0 K le_rfl (Nat.zero_le K)).2
  have hd : PeriodicLattice.levelDepth K 0 = (K : ℤ) := by simp [PeriodicLattice.levelDepth]
  rw [hd] at hA
  have hsq : ∀ p : ElementaryPlaquette (refinedSpacing L K),
      ElementarySquare.filledSquare (fun μ t => (Pi.single μ t : AmbientSpace))
        (refinedSpacing L K) p.corner p.lowAxis p.highAxis = p.closedSquare := by
    intro p
    have key : ∀ s t : ℝ, (p.corner : AmbientSpace) + Pi.single p.lowAxis (s * refinedSpacing L K) +
        Pi.single p.highAxis (t * refinedSpacing L K) = (p.corner : AmbientSpace) +
          refinedSpacing L K • (s • (Pi.single p.lowAxis 1 : AmbientSpace) +
            t • (Pi.single p.highAxis 1 : AmbientSpace)) := by
      intro s t
      funext σ
      simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
      split_ifs <;> ring
    ext y
    constructor
    · rintro ⟨s, t, h₁, h₂, h₃, h₄, rfl⟩
      exact ⟨s, ⟨h₁, h₂⟩, t, ⟨h₃, h₄⟩, key s t⟩
    · rintro ⟨s, hs, t, ht, rfl⟩
      exact ⟨s, t, hs.1, hs.2, ht.1, ht.2, (key s t).symm⟩
  obtain ⟨h₁, h₂, h₃⟩ := (hA p.corner p.corner.2 q.corner q.corner.2 p.lowAxis p.highAxis
    q.lowAxis q.highAxis p.lowAxis_lt_highAxis q.lowAxis_lt_highAxis).2.2.2.2
      (by rw [hsq, hsq, h])
  exact ElementaryPlaquette.ext (Subtype.ext h₁) h₂ h₃
section
variable {L K : ℕ}
theorem isFrame_plaquetteOfAxes_iff (x : LatticePoint (refinedSpacing L K)) (μ ν : Fin 4)
    (h : μ ≠ ν) (e e' : MeshStep L K) : IsFrame (plaquetteOfAxes x μ ν h) e e' ↔
      (PeriodicLattice.PlaquetteCircuits.IsAlongAxis e.1 L (K : ℤ) μ ∧
        PeriodicLattice.PlaquetteCircuits.IsAlongAxis e'.1 L (K : ℤ) ν) ∨
      (PeriodicLattice.PlaquetteCircuits.IsAlongAxis e.1 L (K : ℤ) ν ∧
        PeriodicLattice.PlaquetteCircuits.IsAlongAxis e'.1 L (K : ℤ) μ) := by
  unfold IsFrame plaquetteOfAxes
  split_ifs
  · rfl
  · exact or_comm
theorem half_single_sub_mem {κ : Fin 4} {e : AmbientSpace}
    (he : PeriodicLattice.PlaquetteCircuits.IsAlongAxis e L (K : ℤ) κ) :
    (Pi.single κ (refinedSpacing L K / 2) : AmbientSpace) - (1 / 2 : ℝ) • e ∈
      refinedLattice L K := by
  have hv : (1 / 2 : ℝ) • PeriodicLattice.PlaquetteCircuits.meshVector L (K : ℤ) κ =
      (Pi.single κ (refinedSpacing L K / 2) : AmbientSpace) := by
    funext σ
    by_cases hσ : σ = κ
    · subst hσ
      simp [PeriodicLattice.PlaquetteCircuits.meshVector]
      ring
    · simp [PeriodicLattice.PlaquetteCircuits.meshVector, Pi.single_eq_of_ne hσ]
  rcases he with rfl | rfl
  · rw [hv, sub_self]
    exact zero_mem _
  · rw [smul_neg, hv, sub_neg_eq_add, ← Pi.single_add, add_halves]
    exact (InfiniteLattice.axisStep (refinedSpacing L K) κ).2
theorem frameBase_mem {p : ElementaryPlaquette (refinedSpacing L K)} {e e' : MeshStep L K}
    (h : IsFrame p e e') : frameBase p e e' ∈ refinedLattice L K := by
  unfold frameBase ElementaryPlaquette.center
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · have hm := add_mem (add_mem p.corner.2 (half_single_sub_mem h₁)) (half_single_sub_mem h₂)
    convert hm using 1
    abel
  · have hm := add_mem (add_mem p.corner.2 (half_single_sub_mem h₂)) (half_single_sub_mem h₁)
    convert hm using 1
    abel
theorem faceHolonomy_eq_loopHolonomy (x : LatticePoint (refinedSpacing L K)) (μ ν : Fin 4)
    (h : μ < ν) (U : GaugeField (refinedSpacing L K)) :
    faceHolonomy U ⟨x, μ, ν, h⟩ =
      loopHolonomy U (circuitFrom x (RefinedLatticeSymmetries.axisStep L K μ)
        (RefinedLatticeSymmetries.axisStep L K ν)) := by
  have e₂ : linkAlong (x + meshSite (RefinedLatticeSymmetries.axisStep L K μ) +
      meshSite (RefinedLatticeSymmetries.axisStep L K ν))
      (-RefinedLatticeSymmetries.axisStep L K μ) =
        (Link.forwardFrom (x + InfiniteLattice.axisStep _ ν) μ).opposite := by
    refine Link.ext ?_ ?_
    · change x + meshSite (RefinedLatticeSymmetries.axisStep L K μ) +
        meshSite (RefinedLatticeSymmetries.axisStep L K ν) =
          x + InfiniteLattice.axisStep _ ν + InfiniteLattice.axisStep _ μ
      rw [meshSite_axisStep, meshSite_axisStep]
      abel
    · change x + meshSite (RefinedLatticeSymmetries.axisStep L K μ) +
        meshSite (RefinedLatticeSymmetries.axisStep L K ν) +
        meshSite (-RefinedLatticeSymmetries.axisStep L K μ) = x + InfiniteLattice.axisStep _ ν
      rw [meshSite_neg, meshSite_axisStep, meshSite_axisStep]
      abel
  have e₃ : linkAlong (x + meshSite (RefinedLatticeSymmetries.axisStep L K ν))
      (-RefinedLatticeSymmetries.axisStep L K ν) = (Link.forwardFrom x ν).opposite := by
    refine Link.ext ?_ ?_
    · change x + meshSite (RefinedLatticeSymmetries.axisStep L K ν) =
        x + InfiniteLattice.axisStep _ ν
      rw [meshSite_axisStep]
    · change x + meshSite (RefinedLatticeSymmetries.axisStep L K ν) +
        meshSite (-RefinedLatticeSymmetries.axisStep L K ν) = x
      rw [meshSite_neg]
      abel
  change _ = U (linkAlong x (RefinedLatticeSymmetries.axisStep L K μ)) *
    U (linkAlong (x + meshSite (RefinedLatticeSymmetries.axisStep L K μ))
      (RefinedLatticeSymmetries.axisStep L K ν)) *
    U (linkAlong (x + meshSite (RefinedLatticeSymmetries.axisStep L K μ) +
      meshSite (RefinedLatticeSymmetries.axisStep L K ν))
      (-RefinedLatticeSymmetries.axisStep L K μ)) *
    U (linkAlong (x + meshSite (RefinedLatticeSymmetries.axisStep L K ν))
      (-RefinedLatticeSymmetries.axisStep L K ν))
  rw [e₂, e₃, U.2, U.2]
  rfl
end
theorem plaquetteFrames_holds {L K : ℕ} (ha : refinedSpacing L K ≠ 0)
    (hsq : Injective (ElementaryPlaquette.closedSquare :
      ElementaryPlaquette (refinedSpacing L K) → Set AmbientSpace)) :
    PlaquetteFrames L K := by
  have pair : ∀ (x x' : LatticePoint (refinedSpacing L K)) (μ ν μ' ν' : Fin 4) (h : μ ≠ ν)
      (h' : μ' ≠ ν'), plaquetteOfAxes x μ ν h = plaquetteOfAxes x' μ' ν' h' →
        x = x' ∧ s(μ, ν) = s(μ', ν') := by
    intro x x' μ ν μ' ν' h h' e
    have e₁ := congrArg ElementaryPlaquette.corner e
    have e₂ := congrArg (fun p => s(ElementaryPlaquette.lowAxis p,
      ElementaryPlaquette.highAxis p)) e
    simp only [corner_plaquetteOfAxes, axes_plaquetteOfAxes] at e₁ e₂
    exact ⟨e₁, e₂⟩
  refine ⟨fun x x' μ ν μ' ν' h h' hs => pair x x' μ ν μ' ν' h h' (hsq hs),
    fun x x' μ ν μ' ν' h h' hb => pair x x' μ ν μ' ν' h h' (center_injective ha hb),
    fun p e e' hf => ?_, faceHolonomy_eq_loopHolonomy⟩
  have hc := frameBase_mem hf
  have h₁ := add_mem hc (meshSite e).2
  have h₂ := add_mem h₁ (meshSite e').2
  have h₃ := add_mem hc (meshSite e').2
  exact ⟨hc, h₁, h₂, h₃⟩
section
variable {a : ℝ}
theorem single_eq_smul_basisVector (κ : Fin 4) (t : ℝ) :
    (Pi.single κ t : AmbientSpace) = t • basisVector κ := by
  funext σ
  by_cases h : σ = κ
  · subst h
    simp [basisVector]
  · simp [basisVector, Pi.single_eq_of_ne h]
theorem map_single_of_basisVector {w : AmbientSpace →ₗ[ℝ] AmbientSpace} {κ ρ : Fin 4} {u : ℝ}
    (h : w (basisVector κ) = u • basisVector ρ) (t : ℝ) :
    w (Pi.single κ t) = u • (Pi.single ρ t : AmbientSpace) := by
  rw [single_eq_smul_basisVector, map_smul, h, single_eq_smul_basisVector, smul_comm]
theorem reflect_mem_Icc {u s : ℝ} (hu : u = 1 ∨ u = -1) (hs : s ∈ Icc (0 : ℝ) 1) :
    (1 + u * (2 * s - 1)) / 2 ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨h₀, h₁⟩ := hs
  rcases hu with rfl | rfl <;> constructor <;> linarith
theorem shift_mem_latticeSubgroup {u : ℝ} (hu : u = 1 ∨ u = -1) (κ : Fin 4) :
    ((u - 1) / 2) • (Pi.single κ a : AmbientSpace) ∈ latticeSubgroup a := by
  rcases hu with rfl | rfl
  · simp
  · have h : ((-1 - 1) / 2 : ℝ) • (Pi.single κ a : AmbientSpace) =
        -(InfiniteLattice.axisStep a κ : AmbientSpace) := by
      funext σ
      by_cases hσ : σ = κ
      · subst hσ
        simp [InfiniteLattice.axisStep]
        ring
      · simp [InfiniteLattice.axisStep, Pi.single_eq_of_ne hσ]
    rw [h]
    exact neg_mem (InfiniteLattice.axisStep a κ).2
theorem image_squareOfAxes {r : AmbientSpace → AmbientSpace}
    {w : AmbientSpace →ₗ[ℝ] AmbientSpace} {v : AmbientSpace}
    (h : IsAffineDecomposition a r (w, v)) (x x' : LatticePoint a) {μ ν μ' ν' : Fin 4} {u u' : ℝ}
    (hu : u = 1 ∨ u = -1) (hu' : u' = 1 ∨ u' = -1)
    (h₁ : w (basisVector μ) = u • basisVector μ') (h₂ : w (basisVector ν) = u' • basisVector ν')
    (hx : (x' : AmbientSpace) = r x + ((u - 1) / 2) • (Pi.single μ' a : AmbientSpace) +
      ((u' - 1) / 2) • (Pi.single ν' a : AmbientSpace)) :
    r '' squareOfAxes x μ ν = squareOfAxes x' μ' ν' := by
  have hr : ∀ s t : ℝ, r ((x : AmbientSpace) + s • (Pi.single μ a : AmbientSpace) +
      t • (Pi.single ν a : AmbientSpace)) = r x + (u * s) • (Pi.single μ' a : AmbientSpace) +
        (u' * t) • (Pi.single ν' a : AmbientSpace) := by
    intro s t
    rw [add_assoc, apply_add_of_decomposition h, map_add, map_smul, map_smul,
      map_single_of_basisVector h₁, map_single_of_basisVector h₂]
    module
  have hsq : u * u = 1 := by rcases hu with rfl | rfl <;> norm_num
  have hsq' : u' * u' = 1 := by rcases hu' with rfl | rfl <;> norm_num
  ext q
  constructor
  · rintro ⟨_, ⟨s, hs, t, ht, rfl⟩, rfl⟩
    refine ⟨(1 + u * (2 * s - 1)) / 2, reflect_mem_Icc hu hs, (1 + u' * (2 * t - 1)) / 2,
      reflect_mem_Icc hu' ht, ?_⟩
    rw [hr, hx]
    module
  · rintro ⟨s, hs, t, ht, rfl⟩
    refine ⟨_, ⟨(1 + u * (2 * s - 1)) / 2, reflect_mem_Icc hu hs, (1 + u' * (2 * t - 1)) / 2,
      reflect_mem_Icc hu' ht, rfl⟩, ?_⟩
    have e₁ : u * ((1 + u * (2 * s - 1)) / 2) = (u - 1) / 2 + s := by
      linear_combination ((2 * s - 1) / 2) * hsq
    have e₂ : u' * ((1 + u' * (2 * t - 1)) / 2) = (u' - 1) / 2 + t := by
      linear_combination ((2 * t - 1) / 2) * hsq'
    rw [hr, hx, e₁, e₂]
    module
theorem ne_of_basisVector_images {w : AmbientSpace →ₗ[ℝ] AmbientSpace} (hw : w ∈ hypercubicGroup)
    {μ ν μ' ν' : Fin 4} {u u' : ℝ} (hu' : u' = 1 ∨ u' = -1) (hμν : μ ≠ ν)
    (h₁ : w (basisVector μ) = u • basisVector μ') (h₂ : w (basisVector ν) = u' • basisVector ν') :
    μ' ≠ ν' := by
  rintro rfl
  obtain ⟨w₁, -, hl, -⟩ := exists_inverse_of_mem_hypercubicGroup hw
  have hl' : ∀ x, w₁ (w x) = x := fun x => LinearMap.congr_fun hl x
  have a₁ : basisVector μ = u • w₁ (basisVector μ') := by
    rw [← map_smul, ← h₁, hl']
  have a₂ : basisVector ν = u' • w₁ (basisVector μ') := by
    rw [← map_smul, ← h₂, hl']
  have hsq' : u' * u' = 1 := by rcases hu' with rfl | rfl <;> norm_num
  have a₃ : basisVector μ = (u * u') • basisVector ν := by
    rw [a₁, a₂, smul_smul, mul_assoc, hsq', mul_one]
  have a₄ := congrFun a₃ μ
  simp [basisVector, Pi.single_eq_of_ne hμν] at a₄
theorem image_plaquetteOfAxes {r : AmbientSpace → AmbientSpace}
    {w : AmbientSpace →ₗ[ℝ] AmbientSpace} {v : AmbientSpace}
    (h : IsAffineDecomposition a r (w, v)) (x : LatticePoint a) {μ ν μ' ν' : Fin 4} (hμν : μ ≠ ν)
    {u u' : ℝ} (hu : u = 1 ∨ u = -1) (hu' : u' = 1 ∨ u' = -1)
    (h₁ : w (basisVector μ) = u • basisVector μ') (h₂ : w (basisVector ν) = u' • basisVector ν') :
    ∃ (h' : μ' ≠ ν') (x' : LatticePoint a),
      (x' : AmbientSpace) = r x + ((u - 1) / 2) • (Pi.single μ' a : AmbientSpace) +
        ((u' - 1) / 2) • (Pi.single ν' a : AmbientSpace) ∧
      (plaquetteOfAxes x' μ' ν' h').closedSquare = (plaquetteOfAxes x μ ν hμν).squareImage r ∧
      (plaquetteOfAxes x' μ' ν' h').center = r (plaquetteOfAxes x μ ν hμν).center := by
  have h' := ne_of_basisVector_images h.1 hu' hμν h₁ h₂
  have hrx : r x ∈ latticeSubgroup a := by
    rw [h.2.2 x]
    exact add_mem (apply_mem_latticeSubgroup h.1 x.2) h.2.1
  let x' : LatticePoint a := ⟨r x + ((u - 1) / 2) • (Pi.single μ' a : AmbientSpace) +
    ((u' - 1) / 2) • (Pi.single ν' a : AmbientSpace),
    add_mem (add_mem hrx (shift_mem_latticeSubgroup hu μ')) (shift_mem_latticeSubgroup hu' ν')⟩
  refine ⟨h', x', rfl, ?_, ?_⟩
  · rw [closedSquare_plaquetteOfAxes, ElementaryPlaquette.squareImage,
      closedSquare_plaquetteOfAxes]
    exact (image_squareOfAxes h x x' hu hu' h₁ h₂ rfl).symm
  · rw [center_plaquetteOfAxes, center_plaquetteOfAxes, add_assoc (x : AmbientSpace),
      apply_add_of_decomposition h, map_add, map_single_of_basisVector h₁,
      map_single_of_basisVector h₂]
    change r x + ((u - 1) / 2) • (Pi.single μ' a : AmbientSpace) +
      ((u' - 1) / 2) • (Pi.single ν' a : AmbientSpace) + _ + _ = _
    have e : ∀ (κ : Fin 4), (Pi.single κ (a / 2) : AmbientSpace) =
        (1 / 2 : ℝ) • Pi.single κ a := by
      intro κ
      funext σ
      by_cases hσ : σ = κ
      · subst hσ
        simp
        ring
      · simp [Pi.single_eq_of_ne hσ]
    rw [e μ', e ν']
    module
theorem exists_sign {w : AmbientSpace →ₗ[ℝ] AmbientSpace} {κ ρ : Fin 4}
    (h : w (basisVector κ) = basisVector ρ ∨ w (basisVector κ) = -basisVector ρ) :
    ∃ u : ℝ, (u = 1 ∨ u = -1) ∧ w (basisVector κ) = u • basisVector ρ := by
  rcases h with h | h
  · exact ⟨1, Or.inl rfl, by rw [h, one_smul]⟩
  · exact ⟨-1, Or.inr rfl, by rw [h, neg_one_smul]⟩
theorem exists_plaquette_of_image {r : AmbientSpace → AmbientSpace}
    {w : AmbientSpace →ₗ[ℝ] AmbientSpace} {v : AmbientSpace}
    (h : IsAffineDecomposition a r (w, v)) (σ : Equiv.Perm (Fin 4))
    (hσ : ∀ κ, w (basisVector κ) = basisVector (σ κ) ∨ w (basisVector κ) = -basisVector (σ κ))
    (p : ElementaryPlaquette a) :
    ∃ (h' : σ p.lowAxis ≠ σ p.highAxis) (x' : LatticePoint a),
      (plaquetteOfAxes x' (σ p.lowAxis) (σ p.highAxis) h').closedSquare = p.squareImage r ∧
      (plaquetteOfAxes x' (σ p.lowAxis) (σ p.highAxis) h').center = r p.center := by
  obtain ⟨u, hu, h₁⟩ := exists_sign (hσ p.lowAxis)
  obtain ⟨u', hu', h₂⟩ := exists_sign (hσ p.highAxis)
  obtain ⟨h', x', -, hs, hb⟩ :=
    image_plaquetteOfAxes h p.corner p.lowAxis_lt_highAxis.ne hu hu' h₁ h₂
  rw [plaquetteOfAxes_self] at hs hb
  exact ⟨h', x', hs, hb⟩
theorem closedSquare_mapPlaquette (r : latticeMotions a) (p : ElementaryPlaquette a) :
    (mapPlaquette r p).closedSquare = p.squareImage r.1 := by
  obtain ⟨w, v, h⟩ := exists_isAffineDecomposition r
  obtain ⟨σ, hσ⟩ := h.1
  obtain ⟨h', x', hs, -⟩ := exists_plaquette_of_image h σ hσ p
  have hex : ∃ q : ElementaryPlaquette a, q.closedSquare = p.squareImage r.1 := ⟨_, hs⟩
  have e : mapPlaquette r p = hex.choose := dif_pos hex
  rw [e]
  exact hex.choose_spec
end
section
variable {L K : ℕ}
theorem pointImage_add_meshSite (r : RefinedMotion L K) {w : AmbientSpace →ₗ[ℝ] AmbientSpace}
    {v : AmbientSpace} (h : IsAffineDecomposition (refinedSpacing L K) r.1 (w, v))
    (y : LatticePoint (refinedSpacing L K)) (e f : MeshStep L K) (hf : f.1 = w e.1) :
    pointImage r (y + meshSite e) = pointImage r y + meshSite f := by
  refine Subtype.ext ?_
  change r.1 ((y : AmbientSpace) + e.1) = r.1 y + f.1
  rw [apply_add_of_decomposition h, hf]
theorem mapLoop_circuitFrom (r : RefinedMotion L K) {w : AmbientSpace →ₗ[ℝ] AmbientSpace}
    {v : AmbientSpace} (h : IsAffineDecomposition (refinedSpacing L K) r.1 (w, v))
    (c : LatticePoint (refinedSpacing L K)) (e e' f f' : MeshStep L K) (hf : f.1 = w e.1)
    (hf' : f'.1 = w e'.1) :
    mapLoop r (circuitFrom c e e') = circuitFrom (pointImage r c) f f' := by
  have hn : (-f).1 = w (-e).1 := by
    change -f.1 = w (-e.1)
    rw [map_neg, hf]
  have hn' : (-f').1 = w (-e').1 := by
    change -f'.1 = w (-e'.1)
    rw [map_neg, hf']
  funext i
  fin_cases i
  · exact linkImage_linkAlong r h c e f hf
  · change linkImage r (linkAlong (c + meshSite e) e') =
      linkAlong (pointImage r c + meshSite f) f'
    rw [linkImage_linkAlong r h _ e' f' hf', pointImage_add_meshSite r h c e f hf]
  · change linkImage r (linkAlong (c + meshSite e + meshSite e') (-e)) =
      linkAlong (pointImage r c + meshSite f + meshSite f') (-f)
    rw [linkImage_linkAlong r h _ (-e) (-f) hn, pointImage_add_meshSite r h _ e' f' hf',
      pointImage_add_meshSite r h c e f hf]
  · change linkImage r (linkAlong (c + meshSite e') (-e')) =
      linkAlong (pointImage r c + meshSite f') (-f')
    rw [linkImage_linkAlong r h _ (-e') (-f') hn', pointImage_add_meshSite r h c e' f' hf']
end
theorem plaquettesUnderMotions_holds {L K : ℕ}
    (hsq : Injective (ElementaryPlaquette.closedSquare :
      ElementaryPlaquette (refinedSpacing L K) → Set AmbientSpace)) :
    PlaquettesUnderMotions L K := by
  intro r
  have hcomp : ∀ (r' t : RefinedMotion L K), t.1 = r.1 ∘ r'.1 → ∀ p,
      mapPlaquette t p = mapPlaquette r (mapPlaquette r' p) := by
    intro r' t h p
    apply hsq
    rw [closedSquare_mapPlaquette, closedSquare_mapPlaquette, ElementaryPlaquette.squareImage,
      ElementaryPlaquette.squareImage, closedSquare_mapPlaquette, ElementaryPlaquette.squareImage,
      h, image_comp]
  have hleft : ∀ t : RefinedMotion L K, t.1 = motionInverse r →
      LeftInverse (mapPlaquette t) (mapPlaquette r) := by
    intro t h p
    apply hsq
    rw [closedSquare_mapPlaquette, ElementaryPlaquette.squareImage, closedSquare_mapPlaquette,
      ElementaryPlaquette.squareImage, ← image_comp, h,
      (motionInverse_leftInverse r).comp_eq_id, image_id]
  have hright : ∀ t : RefinedMotion L K, t.1 = motionInverse r →
      RightInverse (mapPlaquette t) (mapPlaquette r) := by
    intro t h p
    apply hsq
    rw [closedSquare_mapPlaquette, ElementaryPlaquette.squareImage, closedSquare_mapPlaquette,
      ElementaryPlaquette.squareImage, ← image_comp, h,
      (motionInverse_rightInverse r).comp_eq_id, image_id]
  have hbary : ∀ p : ElementaryPlaquette (refinedSpacing L K),
      (mapPlaquette r p).center = r.1 p.center := by
    intro p
    obtain ⟨w, v, h⟩ := exists_isAffineDecomposition r
    obtain ⟨σ, hσ⟩ := h.1
    obtain ⟨h', x', hs, hb⟩ := exists_plaquette_of_image h σ hσ p
    rw [← hb]
    exact congrArg ElementaryPlaquette.center
      (hsq ((closedSquare_mapPlaquette r p).trans hs.symm))
  refine ⟨fun p => ⟨mapPlaquette r p, closedSquare_mapPlaquette r p,
      fun q hq => hsq (hq.trans (closedSquare_mapPlaquette r p).symm)⟩,
    closedSquare_mapPlaquette r, hbary, hcomp, ?_, fun t h => ⟨hleft t h, hright t h⟩,
    fun w v h => ⟨fun x μ ν μ' ν' hμν u u' h₁ h₂ => ?_,
      fun p e e' f f' c hfr hc hf hf' => ?_⟩⟩
  · exact ⟨(hleft (latticeMotionInv r) rfl).injective,
      (hright (latticeMotionInv r) rfl).surjective⟩
  · have hsign : ∀ u : ℤˣ, (((u : ℤ) : ℝ)) = 1 ∨ (((u : ℤ) : ℝ)) = -1 := fun u => by
      rcases Int.units_eq_one_or u with hs | hs <;> simp [hs]
    obtain ⟨h', x', hx, hs, -⟩ := image_plaquetteOfAxes h x hμν (hsign u) (hsign u') h₁ h₂
    exact ⟨h', x', hx, hsq ((closedSquare_mapPlaquette r _).trans hs.symm)⟩
  · obtain ⟨σ, hσ⟩ := h.1
    obtain ⟨h', x', hs, hb⟩ := exists_plaquette_of_image h σ hσ p
    have hrp : mapPlaquette r p = plaquetteOfAxes x' (σ p.lowAxis) (σ p.highAxis) h' :=
      hsq ((closedSquare_mapPlaquette r p).trans hs.symm)
    refine ⟨?_, ?_, mapLoop_circuitFrom r h c e e' f f' hf hf'⟩
    · rw [hrp, isFrame_plaquetteOfAxes_iff]
      rcases hfr with ⟨a₁, a₂⟩ | ⟨a₁, a₂⟩
      · left
        rw [hf, hf']
        exact ⟨isAlongAxis_map (hσ _) a₁, isAlongAxis_map (hσ _) a₂⟩
      · right
        rw [hf, hf']
        exact ⟨isAlongAxis_map (hσ _) a₁, isAlongAxis_map (hσ _) a₂⟩
    · have hc' : p.center = (c : AmbientSpace) + ((1 / 2 : ℝ) • e.1 + (1 / 2 : ℝ) • e'.1) := by
        rw [hc, frameBase]
        abel
      unfold frameBase
      rw [hbary, hc', apply_add_of_decomposition h, map_add, map_smul, map_smul, ← hf, ← hf']
      abel
section
variable {L K : ℕ}
theorem circuitFrom_rotate (c : LatticePoint (refinedSpacing L K)) (e e' : MeshStep L K) :
    ![circuitFrom c e e' 1, circuitFrom c e e' 2, circuitFrom c e e' 3, circuitFrom c e e' 0] =
      circuitFrom (c + meshSite e) e' (-e) := by
  have h₂ : c + meshSite e + meshSite e' + meshSite (-e) = c + meshSite e' := by
    rw [meshSite_neg]
    abel
  have h₃ : c + meshSite e + meshSite (-e) = c := by
    rw [meshSite_neg]
    abel
  funext i
  fin_cases i
  · rfl
  · rfl
  · change linkAlong (c + meshSite e') (-e') =
      linkAlong (c + meshSite e + meshSite e' + meshSite (-e)) (-e')
    rw [h₂]
  · change linkAlong c e = linkAlong (c + meshSite e + meshSite (-e)) (-(-e))
    rw [h₃, meshStep_neg_neg]
theorem circuitFrom_reverse (c : LatticePoint (refinedSpacing L K)) (e e' : MeshStep L K) :
    ![(circuitFrom c e e' 3).opposite, (circuitFrom c e e' 2).opposite,
      (circuitFrom c e e' 1).opposite, (circuitFrom c e e' 0).opposite] =
        circuitFrom c e' e := by
  have h₁ : c + meshSite e' + meshSite (-e') = c := by
    rw [meshSite_neg]
    abel
  have h₂ : c + meshSite e + meshSite e' + meshSite (-e) = c + meshSite e' := by
    rw [meshSite_neg]
    abel
  funext i
  fin_cases i
  · change (linkAlong (c + meshSite e') (-e')).opposite = linkAlong c e'
    rw [opposite_linkAlong, h₁, meshStep_neg_neg]
  · change (linkAlong (c + meshSite e + meshSite e') (-e)).opposite =
      linkAlong (c + meshSite e') e
    rw [opposite_linkAlong, h₂, meshStep_neg_neg]
  · change (linkAlong (c + meshSite e) e').opposite =
      linkAlong (c + meshSite e' + meshSite e) (-e')
    rw [opposite_linkAlong, add_right_comm]
  · change (linkAlong c e).opposite = linkAlong (c + meshSite e) (-e)
    rw [opposite_linkAlong]
theorem isAlongAxis_neg {e : MeshStep L K} {κ : Fin 4}
    (h : PeriodicLattice.PlaquetteCircuits.IsAlongAxis e.1 L (K : ℤ) κ) :
    PeriodicLattice.PlaquetteCircuits.IsAlongAxis (-e).1 L (K : ℤ) κ := by
  change PeriodicLattice.PlaquetteCircuits.IsAlongAxis (-e.1) L (K : ℤ) κ
  rcases h with h | h
  · exact Or.inr (by rw [h])
  · exact Or.inl (by rw [h, neg_neg])
theorem isFrame_rotate {p : ElementaryPlaquette (refinedSpacing L K)} {e e' : MeshStep L K}
    (h : IsFrame p e e') : IsFrame p e' (-e) := by
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact Or.inr ⟨h₂, isAlongAxis_neg h₁⟩
  · exact Or.inl ⟨h₂, isAlongAxis_neg h₁⟩
theorem isFrame_swap {p : ElementaryPlaquette (refinedSpacing L K)} {e e' : MeshStep L K}
    (h : IsFrame p e e') : IsFrame p e' e := by
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact Or.inr ⟨h₂, h₁⟩
  · exact Or.inl ⟨h₂, h₁⟩
theorem frameBase_rotate (p : ElementaryPlaquette (refinedSpacing L K)) (e e' : MeshStep L K) :
    frameBase p e' (-e) = frameBase p e e' + e.1 := by
  have hn : (-e).1 = -e.1 := rfl
  unfold frameBase
  rw [hn]
  module
theorem frameBase_swap (p : ElementaryPlaquette (refinedSpacing L K)) (e e' : MeshStep L K) :
    frameBase p e' e = frameBase p e e' := by
  unfold frameBase
  abel
theorem realTraceLoop_rotate (U : GaugeField (refinedSpacing L K))
    (c : LatticePoint (refinedSpacing L K)) (e e' : MeshStep L K) :
    realTraceLoop U (circuitFrom (c + meshSite e) e' (-e)) =
      realTraceLoop U (circuitFrom c e e') := by
  rw [← circuitFrom_rotate]
  unfold realTraceLoop loopHolonomy
  congr 1
  change Matrix.trace ((U (circuitFrom c e e' 1) : Matrices.ComplexMatrix2) *
      (U (circuitFrom c e e' 2) : Matrices.ComplexMatrix2) *
      (U (circuitFrom c e e' 3) : Matrices.ComplexMatrix2) *
      (U (circuitFrom c e e' 0) : Matrices.ComplexMatrix2)) =
    Matrix.trace ((U (circuitFrom c e e' 0) : Matrices.ComplexMatrix2) *
      (U (circuitFrom c e e' 1) : Matrices.ComplexMatrix2) *
      (U (circuitFrom c e e' 2) : Matrices.ComplexMatrix2) *
      (U (circuitFrom c e e' 3) : Matrices.ComplexMatrix2))
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]
theorem re_fullTrace_inv (W : Matrices.ComplexMatrix2.specialUnitary) :
    (Matrices.ComplexMatrix2.fullTrace
      ((W⁻¹ : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2)).re =
    (Matrices.ComplexMatrix2.fullTrace (W : Matrices.ComplexMatrix2)).re := by
  have hu := Matrix.specialUnitaryGroup_le_unitaryGroup W.2
  have hinv : (W : Matrices.ComplexMatrix2)⁻¹ = star (W : Matrices.ComplexMatrix2) :=
    Matrix.inv_eq_right_inv (Matrix.mem_unitaryGroup_iff.mp hu)
  rw [specialUnitary_coe_inv, hinv, Matrix.star_eq_conjTranspose,
    Matrices.ComplexMatrix2.fullTrace, Matrix.trace_conjTranspose]
  simp
theorem realTraceLoop_swap (U : GaugeField (refinedSpacing L K))
    (c : LatticePoint (refinedSpacing L K)) (e e' : MeshStep L K) :
    realTraceLoop U (circuitFrom c e' e) = realTraceLoop U (circuitFrom c e e') := by
  rw [← circuitFrom_reverse]
  unfold realTraceLoop
  rw [← re_fullTrace_inv (loopHolonomy U (circuitFrom c e e'))]
  congr 3
  unfold loopHolonomy
  change U (circuitFrom c e e' 3).opposite * U (circuitFrom c e e' 2).opposite *
      U (circuitFrom c e e' 1).opposite * U (circuitFrom c e e' 0).opposite = _
  rw [U.2, U.2, U.2, U.2]
  simp only [mul_inv_rev, mul_assoc]
def signedFrame (p : ElementaryPlaquette (refinedSpacing L K)) (d : Bool × Bool × Bool) :
    MeshStep L K × MeshStep L K :=
  match d with
  | (true, s, t) => (bif s then RefinedLatticeSymmetries.axisStep L K p.lowAxis
        else -RefinedLatticeSymmetries.axisStep L K p.lowAxis,
      bif t then RefinedLatticeSymmetries.axisStep L K p.highAxis
        else -RefinedLatticeSymmetries.axisStep L K p.highAxis)
  | (false, s, t) => (bif s then RefinedLatticeSymmetries.axisStep L K p.highAxis
        else -RefinedLatticeSymmetries.axisStep L K p.highAxis,
      bif t then RefinedLatticeSymmetries.axisStep L K p.lowAxis
        else -RefinedLatticeSymmetries.axisStep L K p.lowAxis)
theorem isAlongAxis_axisStep (κ : Fin 4) :
    PeriodicLattice.PlaquetteCircuits.IsAlongAxis (RefinedLatticeSymmetries.axisStep L K κ).1 L
      (K : ℤ) κ := Or.inl rfl
theorem signedFrame_isFrame (p : ElementaryPlaquette (refinedSpacing L K))
    (d : Bool × Bool × Bool) : IsFrame p (signedFrame p d).1 (signedFrame p d).2 := by
  obtain ⟨o, s, t⟩ := d
  cases o <;> cases s <;> cases t
  · exact Or.inr ⟨isAlongAxis_neg (isAlongAxis_axisStep _), isAlongAxis_neg (isAlongAxis_axisStep _)⟩
  · exact Or.inr ⟨isAlongAxis_neg (isAlongAxis_axisStep _), isAlongAxis_axisStep _⟩
  · exact Or.inr ⟨isAlongAxis_axisStep _, isAlongAxis_neg (isAlongAxis_axisStep _)⟩
  · exact Or.inr ⟨isAlongAxis_axisStep _, isAlongAxis_axisStep _⟩
  · exact Or.inl ⟨isAlongAxis_neg (isAlongAxis_axisStep _), isAlongAxis_neg (isAlongAxis_axisStep _)⟩
  · exact Or.inl ⟨isAlongAxis_neg (isAlongAxis_axisStep _), isAlongAxis_axisStep _⟩
  · exact Or.inl ⟨isAlongAxis_axisStep _, isAlongAxis_neg (isAlongAxis_axisStep _)⟩
  · exact Or.inl ⟨isAlongAxis_axisStep _, isAlongAxis_axisStep _⟩
theorem eq_cond_of_isAlongAxis {e : MeshStep L K} {κ : Fin 4}
    (h : PeriodicLattice.PlaquetteCircuits.IsAlongAxis e.1 L (K : ℤ) κ) :
    ∃ s : Bool, e = bif s then RefinedLatticeSymmetries.axisStep L K κ
      else -RefinedLatticeSymmetries.axisStep L K κ := by
  rcases h with h | h
  · exact ⟨true, Subtype.ext h⟩
  · exact ⟨false, Subtype.ext h⟩
theorem exists_signedFrame_eq {p : ElementaryPlaquette (refinedSpacing L K)} {e e' : MeshStep L K}
    (h : IsFrame p e e') : ∃ d, signedFrame p d = (e, e') := by
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · obtain ⟨s, rfl⟩ := eq_cond_of_isAlongAxis h₁
    obtain ⟨t, rfl⟩ := eq_cond_of_isAlongAxis h₂
    exact ⟨(true, s, t), rfl⟩
  · obtain ⟨s, rfl⟩ := eq_cond_of_isAlongAxis h₁
    obtain ⟨t, rfl⟩ := eq_cond_of_isAlongAxis h₂
    exact ⟨(false, s, t), rfl⟩
theorem signedFrame_injective (ha : refinedSpacing L K ≠ 0)
    (p : ElementaryPlaquette (refinedSpacing L K)) : Injective (signedFrame p) := by
  have hne : p.lowAxis ≠ p.highAxis := p.lowAxis_lt_highAxis.ne
  have val : ∀ (κ ρ : Fin 4), (RefinedLatticeSymmetries.axisStep L K κ).1 ρ =
      if ρ = κ then refinedSpacing L K else 0 := fun κ ρ => by
    change (Pi.single κ (refinedSpacing L K) : AmbientSpace) ρ = _
    rw [Pi.single_apply]
  have neg : ∀ (κ ρ : Fin 4), (-RefinedLatticeSymmetries.axisStep L K κ).1 ρ =
      -(if ρ = κ then refinedSpacing L K else 0) := fun κ ρ => by
    change -(Pi.single κ (refinedSpacing L K) : AmbientSpace) ρ = _
    rw [Pi.single_apply]
  have haa : refinedSpacing L K ≠ -refinedSpacing L K := fun h =>
    ha (by linarith)
  have n₁ : RefinedLatticeSymmetries.axisStep L K p.lowAxis ≠
      RefinedLatticeSymmetries.axisStep L K p.highAxis := fun h => by
    have := congrFun (congrArg Subtype.val h) p.lowAxis
    simp [val, hne, ha] at this
  have n₂ : RefinedLatticeSymmetries.axisStep L K p.lowAxis ≠
      -RefinedLatticeSymmetries.axisStep L K p.highAxis := fun h => by
    have := congrFun (congrArg Subtype.val h) p.lowAxis
    simp [val, neg, hne, ha] at this
  have n₃ : -RefinedLatticeSymmetries.axisStep L K p.lowAxis ≠
      RefinedLatticeSymmetries.axisStep L K p.highAxis := fun h => by
    have := congrFun (congrArg Subtype.val h) p.lowAxis
    simp [val, neg, hne, ha] at this
  have n₄ : -RefinedLatticeSymmetries.axisStep L K p.lowAxis ≠
      -RefinedLatticeSymmetries.axisStep L K p.highAxis := fun h => by
    have := congrFun (congrArg Subtype.val h) p.lowAxis
    simp [neg, hne, ha] at this
  have n₅ : ∀ κ, RefinedLatticeSymmetries.axisStep L K κ ≠
      -RefinedLatticeSymmetries.axisStep L K κ := fun κ h => by
    have := congrFun (congrArg Subtype.val h) κ
    simp only [val, neg, if_true] at this
    exact haa this
  rintro ⟨o, s, t⟩ ⟨o', s', t'⟩ h
  cases o <;> cases s <;> cases t <;> cases o' <;> cases s' <;> cases t' <;>
    first
    | rfl
    | (exfalso
       simp only [signedFrame, cond_true, cond_false, Prod.mk.injEq] at h
       have n₁' := n₁.symm
       have n₂' := n₂.symm
       have n₃' := n₃.symm
       have n₄' := n₄.symm
       have n₅₁ := n₅ p.lowAxis
       have n₅₂ := n₅ p.highAxis
       have n₅₁' := n₅₁.symm
       have n₅₂' := n₅₂.symm
       tauto)
def signedCircuit (p : ElementaryPlaquette (refinedSpacing L K)) (d : Bool × Bool × Bool) :
    Fin 4 → Link (refinedSpacing L K) :=
  circuitFrom ⟨frameBase p (signedFrame p d).1 (signedFrame p d).2,
    frameBase_mem (signedFrame_isFrame p d)⟩ (signedFrame p d).1 (signedFrame p d).2
theorem signedCircuit_injective (ha : refinedSpacing L K ≠ 0)
    (p : ElementaryPlaquette (refinedSpacing L K)) : Injective (signedCircuit p) := by
  intro d d' h
  have h₀ := linkAlong_inj (congrFun h 0)
  have he := h₀.2
  have h₁ := linkAlong_inj (congrFun h 1)
  exact signedFrame_injective ha p (Prod.ext he h₁.2)
theorem setOf_isCircuit_eq_range (p : ElementaryPlaquette (refinedSpacing L K)) :
    {γ | IsCircuit p γ} = range (signedCircuit p) := by
  ext γ
  constructor
  · rintro ⟨e, e', hf, c, hc, rfl⟩
    obtain ⟨d, hd⟩ := exists_signedFrame_eq hf
    refine ⟨d, ?_⟩
    unfold signedCircuit
    simp only [hd]
    congr 1
    exact Subtype.ext hc.symm
  · rintro ⟨d, rfl⟩
    exact ⟨_, _, signedFrame_isFrame p d, _, rfl, rfl⟩
def HasLoopTrace (U : GaugeField (refinedSpacing L K)) (p : ElementaryPlaquette (refinedSpacing L K))
    (T : ℝ) (e e' : MeshStep L K) : Prop :=
  IsFrame p e e' ∧ ∀ c : LatticePoint (refinedSpacing L K), (c : AmbientSpace) = frameBase p e e' →
    realTraceLoop U (circuitFrom c e e') = T
theorem HasLoopTrace.rotate {U : GaugeField (refinedSpacing L K)}
    {p : ElementaryPlaquette (refinedSpacing L K)} {T : ℝ} {e e' : MeshStep L K}
    (h : HasLoopTrace U p T e e') : HasLoopTrace U p T e' (-e) := by
  refine ⟨isFrame_rotate h.1, fun c hc => ?_⟩
  have hc₀ : c = (⟨frameBase p e e', frameBase_mem h.1⟩ : LatticePoint (refinedSpacing L K)) +
      meshSite e := Subtype.ext (by rw [hc, frameBase_rotate]; rfl)
  rw [hc₀, realTraceLoop_rotate]
  exact h.2 _ rfl
theorem HasLoopTrace.swap {U : GaugeField (refinedSpacing L K)}
    {p : ElementaryPlaquette (refinedSpacing L K)} {T : ℝ} {e e' : MeshStep L K}
    (h : HasLoopTrace U p T e e') : HasLoopTrace U p T e' e := by
  refine ⟨isFrame_swap h.1, fun c hc => ?_⟩
  rw [realTraceLoop_swap]
  exact h.2 c (hc.trans (frameBase_swap p e e').symm.symm)
theorem hasLoopTrace_axisSteps (U : GaugeField (refinedSpacing L K))
    (p : ElementaryPlaquette (refinedSpacing L K)) :
    HasLoopTrace U p
      (Matrices.ComplexMatrix2.fullTrace (faceHolonomy U p : Matrices.ComplexMatrix2)).re
      (RefinedLatticeSymmetries.axisStep L K p.lowAxis)
      (RefinedLatticeSymmetries.axisStep L K p.highAxis) := by
  refine ⟨Or.inl ⟨isAlongAxis_axisStep _, isAlongAxis_axisStep _⟩, fun c hc => ?_⟩
  have hc₀ : c = p.corner := Subtype.ext (by
    rw [hc]
    unfold frameBase ElementaryPlaquette.center
    have hv : ∀ κ, (1 / 2 : ℝ) • (RefinedLatticeSymmetries.axisStep L K κ).1 =
        (Pi.single κ (refinedSpacing L K / 2) : AmbientSpace) := fun κ => by
      funext σ
      by_cases hσ : σ = κ
      · subst hσ
        change (1 / 2 : ℝ) • (Pi.single σ (refinedSpacing L K) : AmbientSpace) σ = _
        simp
        ring
      · change (1 / 2 : ℝ) • (Pi.single κ (refinedSpacing L K) : AmbientSpace) σ = _
        simp [Pi.single_eq_of_ne hσ]
    rw [hv, hv]
    abel)
  subst hc₀
  unfold realTraceLoop
  have hp : faceHolonomy U p = faceHolonomy U ⟨p.corner, p.lowAxis, p.highAxis,
      p.lowAxis_lt_highAxis⟩ := rfl
  rw [hp, faceHolonomy_eq_loopHolonomy]
theorem hasLoopTrace_signedFrame (U : GaugeField (refinedSpacing L K))
    (p : ElementaryPlaquette (refinedSpacing L K)) (d : Bool × Bool × Bool) :
    HasLoopTrace U p
      (Matrices.ComplexMatrix2.fullTrace (faceHolonomy U p : Matrices.ComplexMatrix2)).re
      (signedFrame p d).1 (signedFrame p d).2 := by
  have h₀ := hasLoopTrace_axisSteps U p
  have h₁ := h₀.rotate
  have h₂ := h₁.rotate
  have h₃ := h₂.rotate
  rw [meshStep_neg_neg] at h₃
  obtain ⟨o, s, t⟩ := d
  cases o <;> cases s <;> cases t
  · exact h₂.swap
  · exact h₃
  · exact h₁
  · exact h₀.swap
  · exact h₂
  · exact h₁.swap
  · exact h₃.swap
  · exact h₀
theorem realTraceLoop_eq_of_isCircuit (U : GaugeField (refinedSpacing L K))
    {p : ElementaryPlaquette (refinedSpacing L K)} {γ : Fin 4 → Link (refinedSpacing L K)}
    (h : IsCircuit p γ) :
    realTraceLoop U γ =
      (Matrices.ComplexMatrix2.fullTrace (faceHolonomy U p : Matrices.ComplexMatrix2)).re := by
  obtain ⟨e, e', hf, c, hc, rfl⟩ := h
  obtain ⟨d, hd⟩ := exists_signedFrame_eq hf
  have ht := hasLoopTrace_signedFrame U p d
  simp only [hd] at ht
  exact ht.2 c hc
theorem continuous_linkValue {a : ℝ} (b : Link a) :
    Continuous fun U : GaugeField a => (U b : Matrices.ComplexMatrix2) :=
  continuous_subtype_val.comp ((continuous_apply b).comp continuous_subtype_val)
theorem continuous_faceHolonomy {a : ℝ} (p : ElementaryPlaquette a) :
    Continuous fun U : GaugeField a => (faceHolonomy U p : Matrices.ComplexMatrix2) := by
  have h : (fun U : GaugeField a => (faceHolonomy U p : Matrices.ComplexMatrix2)) = fun U =>
      (U (Link.forwardFrom p.corner p.lowAxis) : Matrices.ComplexMatrix2) *
        (U (Link.forwardFrom (p.corner + InfiniteLattice.axisStep a p.lowAxis) p.highAxis) :
          Matrices.ComplexMatrix2) *
        (U (Link.forwardFrom (p.corner + InfiniteLattice.axisStep a p.highAxis)
          p.lowAxis).opposite : Matrices.ComplexMatrix2) *
        (U (Link.forwardFrom p.corner p.highAxis).opposite : Matrices.ComplexMatrix2) := by
    funext U
    rw [U.2, U.2]
    rfl
  rw [h]
  exact (((continuous_linkValue _).matrix_mul (continuous_linkValue _)).matrix_mul
    (continuous_linkValue _)).matrix_mul (continuous_linkValue _)
theorem faceEnergy_mem_Icc {a : ℝ} (U : GaugeField a) (p : ElementaryPlaquette a) :
    faceEnergy U p ∈ Icc (0 : ℝ) 2 := by
  have hu := Matrix.specialUnitaryGroup_le_unitaryGroup (faceHolonomy U p).2
  have hb : ∀ i : Fin 2, |((faceHolonomy U p : Matrices.ComplexMatrix2) i i).re| ≤ 1 := fun i =>
    (Complex.abs_re_le_norm _).trans (entry_norm_bound_of_unitary hu i i)
  have h₀ := abs_le.mp (hb 0)
  have h₁ := abs_le.mp (hb 1)
  unfold faceEnergy
  rw [Matrices.ComplexMatrix2.fullTrace, Matrix.trace_fin_two, Complex.add_re]
  constructor <;> linarith [h₀.1, h₀.2, h₁.1, h₁.2]
end
theorem circuitsOfPlaquette_holds {L K : ℕ} (ha : refinedSpacing L K ≠ 0) :
    CircuitsOfPlaquette L K := by
  intro p
  refine ⟨fun e e' c hf hc => ?_, ?_, fun U γ γ' h h' => ?_, fun U γ h => ?_, ?_,
    fun U => faceEnergy_mem_Icc U p⟩
  · refine ⟨circuitFrom_rotate c e e', circuitFrom_reverse c e e', ?_, ?_⟩
    · exact ⟨e', -e, isFrame_rotate hf, c + meshSite e, by
        rw [frameBase_rotate, ← hc]
        rfl, rfl⟩
    · exact ⟨e', e, isFrame_swap hf, c, hc.trans (frameBase_swap p e e').symm, rfl⟩
  · rw [setOf_isCircuit_eq_range, ← image_univ,
      ncard_image_of_injective _ (signedCircuit_injective ha p), ncard_univ,
      Nat.card_eq_fintype_card]
    rfl
  · rw [realTraceLoop_eq_of_isCircuit U h, realTraceLoop_eq_of_isCircuit U h']
  · rw [realTraceLoop_eq_of_isCircuit U h]
    rfl
  · unfold faceEnergy
    exact continuous_const.sub (continuous_const.mul (Complex.continuous_re.comp
      (continuous_faceHolonomy p).matrix_trace))
theorem fieldsUnderMotions_holds (L K : ℕ) : FieldsUnderMotions L K := by
  intro r
  refine ⟨fun r' t h => funext fun U => Subtype.ext (funext fun b => ?_), fun t h => ?_,
    fun U γ => rfl⟩
  · change U.1 (linkImage t b) = U.1 (linkImage r (linkImage r' b))
    rw [linkImage_comp r r' t h]
  · refine ⟨{ toFun := latticeMotionField r
              invFun := latticeMotionField t
              left_inv := fun U => Subtype.ext (funext fun b => ?_)
              right_inv := fun U => Subtype.ext (funext fun b => ?_)
              continuous_toFun := continuous_latticeMotionField r
              continuous_invFun := continuous_latticeMotionField t }, rfl, rfl⟩
    · change U.1 (linkImage r (linkImage t b)) = U.1 b
      rw [linkImage_rightInverse r t h b]
    · change U.1 (linkImage t (linkImage r b)) = U.1 b
      rw [linkImage_leftInverse r t h b]
section
variable {L m K : ℕ}
theorem projectPoint_pointImage (r : RefinedMotion L K)
    (s : PeriodicLattice.TorusLatticeSymmetry L m K) (hs : s.toFun = inducedTorusMap L m r)
    (x : LatticePoint (refinedSpacing L K)) :
    projectPoint L m (K : ℤ) (pointImage r x) = s.pointMap (projectPoint L m (K : ℤ) x) := by
  refine Subtype.ext ?_
  change TorusMetric.torusProj (PeriodicLattice.torusSide L m) (r.1 x) =
    s.toFun (TorusMetric.torusProj (PeriodicLattice.torusSide L m) x)
  have hp := isAffineDecomposition_affineDecomposition r
  rw [hs, hp.2.2 x]
  exact (torusAffineMap_torusProj L m hp.1 _ _).symm
theorem projectLink_linkImage (r : RefinedMotion L K)
    (s : PeriodicLattice.TorusLatticeSymmetry L m K) (hs : s.toFun = inducedTorusMap L m r)
    (b : Link (refinedSpacing L K)) :
    projectLink L m (K : ℤ) (linkImage r b) = s.bondMap (projectLink L m (K : ℤ) b) := by
  have him : s.IsBondImage (projectLink L m (K : ℤ) b)
      (projectLink L m (K : ℤ) (linkImage r b)) :=
    Prod.ext (projectPoint_pointImage r s hs b.initial) (projectPoint_pointImage r s hs b.terminal)
  have hex : ∃ b', s.IsBondImage (projectLink L m (K : ℤ) b) b' := ⟨_, him⟩
  have e : s.bondMap (projectLink L m (K : ℤ) b) = hex.choose := dif_pos hex
  rw [e]
  exact s.isBondImage_unique him hex.choose_spec
end
theorem projectionOfLinksAndFields_holds {L m K : ℕ}
    (hI : ∀ w ∈ hypercubicGroup, ∀ v ∈ latticeSubgroup (refinedSpacing L K),
      ∃ s : PeriodicLattice.TorusLatticeSymmetry L m K, s.toFun = torusAffineMap L m w v) :
    ProjectionOfLinksAndFields L m K := by
  refine ⟨fun y e => ?_, fun b => rfl, continuous_liftCompactField, fun r => ⟨?_, fun s hs =>
    ⟨projectLink_linkImage r s hs, fun V => ?_⟩⟩⟩
  · refine PeriodicLattice.Bond.ext rfl (Subtype.ext (funext fun μ => ?_))
    simp [projectLink, projectPoint, TorusMetric.torusProj,
      PeriodicLattice.PlaquetteCircuits.bondFrom, PeriodicLattice.PlaquetteCircuits.meshVectorSite,
      linkAlong, meshSite]
  · have hp := isAffineDecomposition_affineDecomposition r
    exact hI _ hp.1 _ hp.2.1
  · refine Subtype.ext (funext fun b => ?_)
    have e₁ : liftCompactField V (linkImage r b) =
        V.linkValue (projectLink L m (K : ℤ) (linkImage r b)) := liftCompactField_apply V _
    have e₂ := liftCompactField_apply (L := L) (m := m) (j := (K : ℤ)) (s.pullback V) b
    have e₃ : V.linkValue (projectLink L m (K : ℤ) (linkImage r b)) =
        PeriodicLattice.CompactGaugeField.linkValue (s.pullback V)
          (projectLink L m (K : ℤ) b) := by
      rw [projectLink_linkImage r s hs b]
      rfl
    exact e₁.trans (e₃.trans e₂.symm)
theorem refinedLatticeSymmetryTheorem_holds (hc : ElementarySquare.ElementarySquareStatement)
    (hI : Conventions.StandingParameters.AffineDescriptionOfIsometries) :
    RefinedLatticeSymmetryTheorem := by
  intro s
  have hpos : refinedSpacing s.L s.K ≠ 0 := by
    have hL : (s.L : ℝ) ≠ 0 := by
      have := s.isAdmissible.2
      exact_mod_cast (by omega : s.L ≠ 0)
    exact zpow_ne_zero _ hL
  have hsq := closedSquare_injective hc s.isAdmissible s.K
  refine ⟨motionsActOnSpace_holds _ _ _, linksUnderMotions_holds _ _, plaquetteFrames_holds hpos hsq,
    plaquettesUnderMotions_holds hsq, circuitsOfPlaquette_holds hpos, fieldsUnderMotions_holds _ _,
    projectionOfLinksAndFields_holds fun w hw v hv => ?_⟩
  obtain ⟨r, hr, e⟩ := (hI s).1.1 w hw v hv
  exact ⟨⟨r, hr.1, hr.2⟩, e⟩
end RefinedLatticeSymmetries
end YangMills.Construction
end
