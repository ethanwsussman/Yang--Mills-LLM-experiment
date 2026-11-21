import YangMills.Construction.LawInAState.TheLeastTorusLawUnderLatticeIsometriesProof
import YangMills.Construction.DirichletOperator.BondsCarriedToTheTorusOfACubeProof
import YangMills.Construction.DirichletOperator.DifferenceOperatorsAgreeOnTheLocalTorus
import YangMills.Construction.RegionSequence.GradientAdjointsOnTorus
import YangMills.Construction.RegionSequence.TorusHodgeIdentity
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Dirichlet YangMills.Construction.Torus YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions YangMills.Construction.PartitionCubes.CubeTorus
noncomputable section
namespace YangMills.Construction.PartitionCubes.LocalTorusOperators
section Matching
variable {𝒮 : NestedRegions}
structure LatticeChart (𝔏 : CubeSystem 𝒮) (O I : Set 𝒮.Point) : Prop where
  spacing_eq : 𝔏.setting.ξ = 𝒮.ξ
  subset : O ⊆ I
  coe_mapSite : ∀ x : 𝒮.FineSite, (x : 𝒮.Point) ∈ I →
    ((𝔏.mapSite x : 𝔏.setting.FineSite) : 𝔏.setting.Point) = 𝔏.embed x
  injective : ∀ x x' : 𝒮.FineSite, (x : 𝒮.Point) ∈ I → (x' : 𝒮.Point) ∈ I →
    𝔏.mapSite x = 𝔏.mapSite x' → x = x'
  forward : ∀ (x : 𝒮.FineSite) (ν : Fin 4), (x : 𝒮.Point) ∈ O →
    ((x + unitStep 4 𝒮.side 𝒮.ξ ν : 𝒮.FineSite) : 𝒮.Point) ∈ I ∧
      𝔏.mapSite (x + unitStep 4 𝒮.side 𝒮.ξ ν) =
        𝔏.mapSite x + unitStep 4 𝔏.setting.side 𝔏.setting.ξ ν
  backward : ∀ (x : 𝒮.FineSite) (ν : Fin 4), (x : 𝒮.Point) ∈ O →
    ((x - unitStep 4 𝒮.side 𝒮.ξ ν : 𝒮.FineSite) : 𝒮.Point) ∈ I ∧
      𝔏.mapSite (x - unitStep 4 𝒮.side 𝒮.ξ ν) =
        𝔏.mapSite x - unitStep 4 𝔏.setting.side 𝔏.setting.ξ ν
structure Matched (𝔏 : CubeSystem 𝒮) (W : Set 𝒮.Point) (u : 𝒮.FineSite → ℝ)
    (v : 𝔏.setting.FineSite → ℝ) : Prop where
  vanish : ∀ x : 𝒮.FineSite, (x : 𝒮.Point) ∉ W → u x = 0
  vanish_image : ∀ y : 𝔏.setting.FineSite,
    (∀ x : 𝒮.FineSite, (x : 𝒮.Point) ∈ W → 𝔏.mapSite x ≠ y) → v y = 0
  eq_on : ∀ x : 𝒮.FineSite, (x : 𝒮.Point) ∈ W → u x = v (𝔏.mapSite x)
structure OneStepWider (O W W' : Set 𝒮.Point) : Prop where
  subset : W ⊆ W'
  within : W' ⊆ O
  add_step : ∀ (x : 𝒮.FineSite) (ν : Fin 4), (x : 𝒮.Point) ∈ W →
    ((x + unitStep 4 𝒮.side 𝒮.ξ ν : 𝒮.FineSite) : 𝒮.Point) ∈ W'
  sub_step : ∀ (x : 𝒮.FineSite) (ν : Fin 4), (x : 𝒮.Point) ∈ W →
    ((x - unitStep 4 𝒮.side 𝒮.ξ ν : 𝒮.FineSite) : 𝒮.Point) ∈ W'
variable {𝔏 : CubeSystem 𝒮} {O I W W' : Set 𝒮.Point} {u u' : 𝒮.FineSite → ℝ}
  {v v' : 𝔏.setting.FineSite → ℝ}
theorem Matched.eq_of_mem (h : Matched 𝔏 W u v) (hc : LatticeChart 𝔏 O I) (hW : W ⊆ I)
    {x : 𝒮.FineSite} (hx : (x : 𝒮.Point) ∈ I) : u x = v (𝔏.mapSite x) := by
  by_cases hxW : (x : 𝒮.Point) ∈ W
  · exact h.eq_on x hxW
  · rw [h.vanish x hxW, h.vanish_image _ fun x' hx' e => hxW ?_]
    rwa [← hc.injective x' x (hW hx') hx e]
theorem Matched.mono (h : Matched 𝔏 W u v) (hc : LatticeChart 𝔏 O I) (hW : W ⊆ W')
    (hW' : W' ⊆ I) : Matched 𝔏 W' u v where
  vanish x hx := h.vanish x fun hxW => hx (hW hxW)
  vanish_image y hy := h.vanish_image y fun x hx => hy x (hW hx)
  eq_on _ hx := h.eq_of_mem hc (hW.trans hW') (hW' hx)
theorem Matched.translate_forward (h : Matched 𝔏 W u v) (hc : LatticeChart 𝔏 O I)
    (hw : OneStepWider O W W') (ν : Fin 4) :
    Matched 𝔏 W' (translateForward ν u) (translateForward ν v) where
  vanish x hx := h.vanish _ fun hxW => hx (by
    have := hw.sub_step _ ν hxW
    rwa [add_sub_cancel_right] at this)
  vanish_image y hy := h.vanish_image _ fun x hx e => by
    have hb := (hc.backward x ν (hw.within (hw.subset hx))).2
    refine hy _ (hw.sub_step x ν hx) ?_
    rw [hb, e, add_sub_cancel_right]
  eq_on x hx := by
    have hf := hc.forward x ν (hw.within hx)
    change u _ = v _
    rw [← hf.2]
    exact h.eq_of_mem hc ((hw.subset.trans hw.within).trans hc.subset) hf.1
theorem Matched.translate_backward (h : Matched 𝔏 W u v) (hc : LatticeChart 𝔏 O I)
    (hw : OneStepWider O W W') (ν : Fin 4) :
    Matched 𝔏 W' (translateBackward ν u) (translateBackward ν v) where
  vanish x hx := h.vanish _ fun hxW => hx (by
    have := hw.add_step _ ν hxW
    rwa [sub_add_cancel] at this)
  vanish_image y hy := h.vanish_image _ fun x hx e => by
    have hb := (hc.forward x ν (hw.within (hw.subset hx))).2
    refine hy _ (hw.add_step x ν hx) ?_
    rw [hb, e, sub_add_cancel]
  eq_on x hx := by
    have hf := hc.backward x ν (hw.within hx)
    change u _ = v _
    rw [← hf.2]
    exact h.eq_of_mem hc ((hw.subset.trans hw.within).trans hc.subset) hf.1
theorem Matched.sub (h : Matched 𝔏 W u v) (h' : Matched 𝔏 W u' v') :
    Matched 𝔏 W (fun x => u x - u' x) (fun y => v y - v' y) where
  vanish x hx := by simp [h.vanish x hx, h'.vanish x hx]
  vanish_image y hy := by simp [h.vanish_image y hy, h'.vanish_image y hy]
  eq_on x hx := by simp only [h.eq_on x hx, h'.eq_on x hx]
theorem Matched.const_mul (h : Matched 𝔏 W u v) (c : ℝ) :
    Matched 𝔏 W (fun x => c * u x) (fun y => c * v y) where
  vanish x hx := by simp [h.vanish x hx]
  vanish_image y hy := by simp [h.vanish_image y hy]
  eq_on x hx := by simp only [h.eq_on x hx]
theorem Matched.sum_fin {F : Fin 4 → 𝒮.FineSite → ℝ} {G : Fin 4 → 𝔏.setting.FineSite → ℝ}
    (h : ∀ ν, Matched 𝔏 W (F ν) (G ν)) :
    Matched 𝔏 W (fun x => ∑ ν, F ν x) (fun y => ∑ ν, G ν y) where
  vanish x hx := Finset.sum_eq_zero fun ν _ => (h ν).vanish x hx
  vanish_image y hy := Finset.sum_eq_zero fun ν _ => (h ν).vanish_image y hy
  eq_on x hx := Finset.sum_congr rfl fun ν _ => (h ν).eq_on x hx
theorem Matched.forward_diff (h : Matched 𝔏 W u v) (hc : LatticeChart 𝔏 O I)
    (hw : OneStepWider O W W') (ν : Fin 4) :
    Matched 𝔏 W' (Dirichlet.forwardDiff ν u) (Dirichlet.forwardDiff ν v) := by
  have hWI := hw.within.trans hc.subset
  have key := ((h.translate_forward hc hw ν).sub (h.mono hc hw.subset hWI)).const_mul 𝒮.ξ⁻¹
  have e : Dirichlet.forwardDiff ν v = fun y => 𝒮.ξ⁻¹ * (translateForward ν v y - v y) := by
    funext y
    exact congrArg (fun t : ℝ => t⁻¹ * (translateForward ν v y - v y)) hc.spacing_eq
  rw [e]
  exact key
theorem Matched.backward_diff (h : Matched 𝔏 W u v) (hc : LatticeChart 𝔏 O I)
    (hw : OneStepWider O W W') (ν : Fin 4) :
    Matched 𝔏 W' (Dirichlet.backwardDiff ν u) (Dirichlet.backwardDiff ν v) := by
  have hWI := hw.within.trans hc.subset
  have key := ((h.translate_backward hc hw ν).sub (h.mono hc hw.subset hWI)).const_mul 𝒮.ξ⁻¹
  have e : Dirichlet.backwardDiff ν v = fun y => 𝒮.ξ⁻¹ * (translateBackward ν v y - v y) := by
    funext y
    exact congrArg (fun t : ℝ => t⁻¹ * (translateBackward ν v y - v y)) hc.spacing_eq
  rw [e]
  exact key
theorem Matched.lattice_laplacian {W'' : Set 𝒮.Point} (h : Matched 𝔏 W u v)
    (hc : LatticeChart 𝔏 O I) (hw : OneStepWider O W W') (hw' : OneStepWider O W' W'') :
    Matched 𝔏 W'' (latticeLaplacian u) (latticeLaplacian v) :=
  Matched.sum_fin fun μ => (h.forward_diff hc hw μ).backward_diff hc hw' μ
theorem matched_pullSites {R : Set 𝒮.Point} (hc : LatticeChart 𝔏 O I)
    (hcl : tsupport (indicator R (1 : 𝒮.Point → ℝ)) ⊆ I) (hWR : W ⊆ R) (f : 𝒮.FineSite → ℝ)
    (hf : VanishesOff W f) : Matched 𝔏 W f (𝔏.pullSites (indicator R 1) f) where
  vanish := hf
  vanish_image y hy := by
    refine finsum_mem_of_eqOn_zero fun x hx => ?_
    change _ * f x = 0
    by_cases hxW : (x : 𝒮.Point) ∈ W
    · exact absurd hx.2 (hy x hxW)
    · rw [hf x hxW, mul_zero]
  eq_on x hx := by
    have hxR : (x : 𝒮.Point) ∈ R := hWR hx
    have hone : indicator R (1 : 𝒮.Point → ℝ) (x : 𝒮.Point) = 1 := by simp [hxR]
    have hts : (x : 𝒮.Point) ∈ tsupport (indicator R (1 : 𝒮.Point → ℝ)) :=
      subset_tsupport _ (by rw [Function.mem_support, hone]; exact one_ne_zero)
    have hset : {x' : 𝒮.FineSite | (x' : 𝒮.Point) ∈ tsupport (indicator R (1 : 𝒮.Point → ℝ)) ∧
        𝔏.mapSite x' = 𝔏.mapSite x} = {x} := by
      ext x'
      constructor
      · rintro ⟨h₁, h₂⟩
        exact hc.injective x' x (hcl h₁) (hcl hts) h₂
      · rintro rfl
        exact ⟨hts, rfl⟩
    simp only [CubeSystem.pullSites]
    rw [hset, finsum_mem_singleton, hone, one_mul]
theorem matched_pullBonds {R : Set 𝒮.Point} (hc : LatticeChart 𝔏 O I)
    (hcl : tsupport (indicator R (1 : 𝒮.Point → ℝ)) ⊆ I) (hWR : W ⊆ R) (A : 𝒮.FineBond → ℝ)
    (hA : ∀ b : 𝒮.FineBond, (b.source : 𝒮.Point) ∉ W → A b = 0) (ν : Fin 4) :
    Matched 𝔏 W (comp A ν) (comp (𝔏.pullBonds (indicator R 1) A) ν) where
  vanish x hx := hA ⟨x, ν⟩ hx
  vanish_image y hy := by
    refine finsum_mem_of_eqOn_zero fun b hb => ?_
    change _ * A b = 0
    by_cases hbW : (b.source : 𝒮.Point) ∈ W
    · exact absurd (congrArg LatticeBond.source hb.2) (hy b.source hbW)
    · rw [hA b hbW, mul_zero]
  eq_on x hx := by
    have hxR : (x : 𝒮.Point) ∈ R := hWR hx
    have hone : indicator R (1 : 𝒮.Point → ℝ) (x : 𝒮.Point) = 1 := by simp [hxR]
    have hts : (x : 𝒮.Point) ∈ tsupport (indicator R (1 : 𝒮.Point → ℝ)) :=
      subset_tsupport _ (by rw [Function.mem_support, hone]; exact one_ne_zero)
    have hset : {b : 𝒮.FineBond | (b.source : 𝒮.Point) ∈ tsupport (indicator R (1 : 𝒮.Point → ℝ)) ∧
        𝔏.mapBond b = ⟨𝔏.mapSite x, ν⟩} = {⟨x, ν⟩} := by
      ext b
      constructor
      · rintro ⟨h₁, h₂⟩
        have e₁ : b.source = x :=
          hc.injective _ x (hcl h₁) (hcl hts) (congrArg LatticeBond.source h₂)
        have e₂ : b.dir = ν := congrArg LatticeBond.dir h₂
        cases b
        simp only at e₁ e₂
        subst e₁ e₂
        rfl
      · rintro rfl
        exact ⟨hts, rfl⟩
    simp only [NestedRegions.comp, CubeSystem.pullBonds]
    rw [hset, finsum_mem_singleton, hone, one_mul]
end Matching
section Lengths
variable {T : ℝ}
theorem proj_add (u w : Fin 4 → ℝ) : torusProj 4 T (u + w) = torusProj 4 T u + torusProj 4 T w := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.torusProj_add <;> assumption
theorem proj_neg (u : Fin 4 → ℝ) : torusProj 4 T (-u) = -torusProj 4 T u := by apply _root_.YangMills.Construction.PartitionCubes.TorusTransfer.torusProj_neg <;> assumption
theorem supNorm_proj_le (w : Fin 4 → ℝ) : supNorm (torusProj 4 T w) ≤ ‖w‖ :=
  csInf_le ⟨0, by rintro r ⟨v, -, rfl⟩; exact norm_nonneg v⟩ ⟨w, rfl, rfl⟩
theorem abs_apply_le_pi_norm (v : Fin 4 → ℝ) (μ : Fin 4) : |v μ| ≤ ‖v‖ := by
  simpa [Real.norm_eq_abs] using norm_le_pi_norm v μ
theorem norm_pi_single_le {ξ : ℝ} (hξ : 0 ≤ ξ) (ν : Fin 4) :
    ‖(Pi.single ν ξ : Fin 4 → ℝ)‖ ≤ ξ := by apply _root_.YangMills.DeltaSharedProofs.p1897 <;> assumption
theorem exists_proj_eq_norm_le (x : PeriodicTorus 4 T) :
    ∃ v : Fin 4 → ℝ, torusProj 4 T v = x ∧ ‖v‖ ≤ supNorm x := by
  choose v hv hn using fun μ => TorusMetric.exists_coe_eq_abs_eq_norm (x μ)
  refine ⟨v, funext hv, le_csInf ⟨‖v‖, v, funext hv, rfl⟩ ?_⟩
  rintro r ⟨u, hu, rfl⟩
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg u)).2 fun μ => ?_
  rw [Real.norm_eq_abs, hn, ← hu]
  exact (TorusMetric.addCircle_norm_coe_le_abs (u μ)).trans (abs_apply_le_pi_norm u μ)
theorem supNorm_add_proj_le (p : PeriodicTorus 4 T) (w : Fin 4 → ℝ) :
    supNorm (p + torusProj 4 T w) ≤ supNorm p + ‖w‖ := by
  obtain ⟨v, hv, hn⟩ := exists_proj_eq_norm_le p
  calc supNorm (p + torusProj 4 T w) = supNorm (torusProj 4 T (v + w)) := by rw [proj_add, hv]
    _ ≤ ‖v + w‖ := supNorm_proj_le _
    _ ≤ ‖v‖ + ‖w‖ := norm_add_le _ _
    _ ≤ supNorm p + ‖w‖ := by linarith
end Lengths
section Adjoint
variable {𝒯 : NestedRegions}
theorem finite_fineSite (hT : TorusLengthsStatement) (𝒯 : NestedRegions) :
    Finite 𝒯.FineSite := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineSite <;> assumption
theorem innerSum_comm (f g : 𝒯.FineSite → ℝ) : innerSum f g = innerSum g f := by apply _root_.YangMills.Construction.RegionSequence.GradientAdjointsOnTorus.innerSum_comm <;> assumption
theorem innerSum_sum_left (hF : Finite 𝒯.FineSite) (f : Fin 4 → 𝒯.FineSite → ℝ)
    (g : 𝒯.FineSite → ℝ) : innerSum (fun x => ∑ ν, f ν x) g = ∑ ν, innerSum (f ν) g := by apply _root_.YangMills.Construction.RegionSequence.GradientAdjointsOnTorus.innerSum_sum_left <;> assumption
theorem innerSum_pi_single [DecidableEq 𝒯.FineSite] (hF : Finite 𝒯.FineSite)
    (f : 𝒯.FineSite → ℝ) (x : 𝒯.FineSite) : innerSum f (Pi.single x 1) = 𝒯.ξ ^ 4 * f x := by
  have := Fintype.ofFinite 𝒯.FineSite
  simp only [innerSum, finsum_eq_sum_of_fintype]
  congr 1
  rw [Finset.sum_eq_single x (fun y _ hy => by simp [Pi.single_eq_of_ne hy]) (by simp)]
  simp
theorem bondInner_eq_sum_comp (hF : Finite 𝒯.FineSite) (A B : 𝒯.FineBond → ℝ) :
    bondInner A B = ∑ ν, innerSum (comp A ν) (comp B ν) := by apply _root_.YangMills.Construction.RegionSequence.GradientAdjointsOnTorus.bondInner_eq_sum_comp <;> assumption
theorem dTorusAdj_eq (hD : DifferenceAdjointsHold) (hT : TorusLengthsStatement)
    (A : 𝒯.FineBond → ℝ) :
    dTorusAdj A = fun x => ∑ ν, backwardDiff ν (comp A ν) x := by
  classical
  have hF := finite_fineSite hT 𝒯
  have hg : ∀ u : 𝒯.FineSite → ℝ,
      innerSum (fun x => ∑ ν, backwardDiff ν (comp A ν) x) u =
        bondInner A (dTorus u) := by
    intro u
    rw [innerSum_sum_left hF, bondInner_eq_sum_comp hF]
    refine Finset.sum_congr rfl fun ν _ => ?_
    have hc : comp (dTorus u) ν = forwardDiff ν u := rfl
    rw [hc, innerSum_comm (comp A ν), (hD 𝒯).site_inner_forwardDiff, innerSum_comm]
  have hspec := Classical.epsilon_spec
    (p := fun v : 𝒯.FineSite → ℝ => v ∈ (univ : Set (𝒯.FineSite → ℝ)) ∧
      ∀ u ∈ (univ : Set (𝒯.FineSite → ℝ)), innerSum v u = bondInner A (dTorus u))
    ⟨_, mem_univ _, fun u _ => hg u⟩
  funext x
  have h₁ : innerSum (dTorusAdj A) (Pi.single x 1) =
      bondInner A (dTorus (Pi.single x 1)) := hspec.2 _ (mem_univ _)
  rw [← hg, innerSum_pi_single hF, innerSum_pi_single hF] at h₁
  exact mul_left_cancel₀ (pow_ne_zero 4 𝒯.ξ_pos.ne') h₁
theorem curlTorusAdj_curlTorus (hH : HodgeFactsHold) (A : 𝒯.FineBond → ℝ) :
    curlTorusAdj (curlTorus A) = bondLap A - dTorus (dTorusAdj A) :=
  eq_sub_of_add_eq ((hH 𝒯).curl_add_grad A)
end Adjoint
section Cube
variable {𝒮 : NestedRegions} {M : ℕ}
theorem coe_circleCentredRep {S : ℝ} (hS : 0 < S) (θ : AddCircle S) :
    ((circleCentredRep θ : ℝ) : AddCircle S) = θ := by
  have h : ∃ v : ℝ, v ∈ Ico (-(S / 2)) (S / 2) ∧ (v : AddCircle S) = θ := by
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective θ
    refine ⟨toIcoMod hS (-(S / 2)) u, ?_, ?_⟩
    · have h₁ := toIcoMod_mem_Ico hS (-(S / 2)) u
      have e : -(S / 2) + S = S / 2 := by ring
      rwa [e] at h₁
    · have h₀ : ((toIcoDiv hS (-(S / 2)) u • S : ℝ) : AddCircle S) = 0 :=
        (AddCircle.coe_eq_zero_iff S).2 ⟨_, rfl⟩
      have h₁ : toIcoMod hS (-(S / 2)) u = u - toIcoDiv hS (-(S / 2)) u • S :=
        (self_sub_toIcoDiv_zsmul hS _ _).symm
      rw [h₁, AddCircle.coe_sub, h₀, sub_zero]
  exact (Classical.epsilon_spec h).2
theorem proj_liftedCentre (Q : LevelCube 𝒮 M) : torusProj 4 𝒮.side Q.liftedCentre = Q.centre := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.torusProj_liftedCentre <;> assumption
theorem scale_zero : 𝒮.scale 0 = 𝒮.ξ := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.scale_zero <;> assumption
theorem ξ_le_scale_succ (n : ℕ) : 𝒮.ξ ≤ 𝒮.scale (n + 1) := by
  have hL : (1 : ℝ) ≤ 𝒮.L := by
    have := 𝒮.thirteen_le_L
    exact_mod_cast (by omega : 1 ≤ 𝒮.L)
  have h := one_le_pow₀ hL (n := n + 1)
  simp only [NestedRegions.scale, scaleSpacing, zpow_natCast]
  exact le_mul_of_one_le_left 𝒮.ξ_pos.le h
theorem thicken_mono (Q : LevelCube 𝒮 M) (hr : 0 ≤ mollifyRadius 𝒮 M Q.level) {a b : ℝ}
    (hab : a ≤ b) : Q.thicken a ⊆ Q.thicken b :=
  fun _ hx => le_trans hx (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hab hr))
theorem oneStepWider_thicken (Q : LevelCube 𝒮 M) {O : Set 𝒮.Point} {c : ℝ}
    (hr : 100 * 𝒮.ξ ≤ mollifyRadius 𝒮 M Q.level)
    (hnear : ∀ x ∈ Q.thicken c, ∃ y ∈ Q.supp,
      supNorm (x - y) ≤ c * mollifyRadius 𝒮 M Q.level)
    (hO : Q.thicken (c + 1 / 100) ⊆ O) :
    OneStepWider O (Q.thicken c) (Q.thicken (c + 1 / 100)) := by
  have hξ := 𝒮.ξ_pos
  have hr₀ : 0 ≤ mollifyRadius 𝒮 M Q.level := by linarith
  have hn := norm_pi_single_le hξ.le
  have key : ∀ (x : 𝒮.Point) (w : Fin 4 → ℝ), x ∈ Q.thicken c → ‖w‖ ≤ 𝒮.ξ →
      x + torusProj 4 𝒮.side w ∈ Q.thicken (c + 1 / 100) := by
    intro x w hx hw
    obtain ⟨y, hy, hd⟩ := hnear x hx
    change supSetDist {_} Q.supp ≤ _
    unfold supSetDist
    refine iInf₂_le_of_le _ (mem_singleton _) (iInf₂_le_of_le y hy (ENNReal.ofReal_le_ofReal ?_))
    have e : x + torusProj 4 𝒮.side w - y = (x - y) + torusProj 4 𝒮.side w := by abel
    rw [e]
    have h₁ := supNorm_add_proj_le (x - y) w
    nlinarith
  refine ⟨thicken_mono Q hr₀ (by norm_num), hO, fun x ν hx => key x _ hx (hn ν),
    fun x ν hx => ?_⟩
  have h := key x (-Pi.single ν 𝒮.ξ) hx (by rw [norm_neg]; exact hn ν)
  rw [proj_neg] at h
  exact h
theorem mem_Ω_zero_of_near (Q : LevelCube 𝒮 M) (hM : 1 ≤ M)
    (haway : ENNReal.ofReal ((M : ℝ) * 𝒮.ξ) <
      supSetDist (Q.thicken (5 / 6)) (𝒮.cubeComplementAt 0 (𝒮.Ω 0)))
    {p : 𝒮.Point} (hp : p ∈ Q.thicken (5 / 6)) (y : 𝒮.FineSite)
    (hd : supNorm (p - (y : 𝒮.Point)) ≤ 𝒮.ξ) : (y : 𝒮.Point) ∈ 𝒮.Ω 0 := by
  by_contra hy
  have hself : (y : 𝒮.Point) ∈ cubeAt (y : 𝒮.Point) (𝒮.scale 0) := by
    change supNorm ((y : 𝒮.Point) - (y : 𝒮.Point)) ≤ _ / 2
    rw [sub_self, scale_zero]
    have h₀ := supNorm_proj_le (T := 𝒮.side) 0
    have e : torusProj 4 𝒮.side 0 = 0 := by
      funext μ
      simp [torusProj]
    rw [e, norm_zero] at h₀
    have := 𝒮.ξ_pos
    linarith
  have hyc : (y : 𝒮.Point) ∈ 𝒮.cubeComplementAt 0 (𝒮.Ω 0) := by
    refine ⟨cubeAt (y : 𝒮.Point) (𝒮.scale 0), ⟨⟨y, ?_, rfl⟩, ?_⟩, hself⟩
    · rw [scale_zero]
      exact y.2
    · exact fun hsub => hy (hsub hself)
  have h₁ : supSetDist (Q.thicken (5 / 6)) (𝒮.cubeComplementAt 0 (𝒮.Ω 0)) ≤
      ENNReal.ofReal (supNorm (p - (y : 𝒮.Point))) := by
    unfold supSetDist
    exact iInf₂_le_of_le p hp (iInf₂_le_of_le _ hyc le_rfl)
  have h₃ : ENNReal.ofReal ((M : ℝ) * 𝒮.ξ) < ENNReal.ofReal 𝒮.ξ :=
    lt_of_lt_of_le haway (h₁.trans (ENNReal.ofReal_le_ofReal hd))
  have h₄ := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg
    (mul_nonneg (Nat.cast_nonneg _) 𝒮.ξ_pos.le)).1 h₃
  have h₅ : (1 : ℝ) ≤ M := by exact_mod_cast hM
  nlinarith [𝒮.ξ_pos]
theorem latticeChart (Q : LevelCube 𝒮 M)
    (hmaps : let O : Set (Fin 4 → ℝ) :=
        {p | ∀ μ, |p μ - Q.liftedCentre μ| < cubeSide 𝒮 M Q.level}
      let localProj : (Fin 4 → ℝ) → Q.system.setting.Point := torusProj 4 Q.system.setting.side
      (∃ h : Q.IsAdmissible, Q.system.setting = Q.torusSetting h) ∧
      BijOn (torusProj 4 𝒮.side) O Q.strictPts ∧
      InjOn localProj (closedCube Q.liftedCentre (6 * cubeSide 𝒮 M Q.level)) ∧
      (∀ p ∈ O, Q.system.embed (torusProj 4 𝒮.side p) = localProj p) ∧
      BijOn Q.system.embed Q.strictPts (localProj '' O) ∧
      ∀ p v : Fin 4 → ℝ, p ∈ O → p + v ∈ O →
        Q.system.embed (torusProj 4 𝒮.side p + torusProj 4 𝒮.side v) =
          Q.system.embed (torusProj 4 𝒮.side p) + localProj v)
    (hlat : Q.system.embed '' ((spacingLattice 4 𝒮.side (𝒮.scale 0) : Set 𝒮.Point) ∩ Q.strictPts) ⊆
      (spacingLattice 4 Q.system.setting.side (𝒮.scale 0) : Set Q.system.setting.Point))
    (hB : 6 * 𝒮.ξ ≤ cubeSide 𝒮 M Q.level) (hξ : Q.system.setting.ξ = 𝒮.ξ) :
    LatticeChart Q.system {x | supNorm (x - Q.centre) < 5 / 6 * cubeSide 𝒮 M Q.level}
      Q.strictPts := by
  obtain ⟨-, hbij, -, -, hbij₂, htrans⟩ := hmaps
  have hξ₀ := 𝒮.ξ_pos
  have hcoe : ∀ x : 𝒮.FineSite, (x : 𝒮.Point) ∈ Q.strictPts →
      ((Q.system.mapSite x : Q.system.setting.FineSite) : Q.system.setting.Point) =
        Q.system.embed x := by
    intro x hx
    have hmem : Q.system.embed x ∈
        (spacingLattice 4 Q.system.setting.side (𝒮.scale 0) : Set Q.system.setting.Point) :=
      hlat ⟨x, ⟨by rw [scale_zero]; exact x.2, hx⟩, rfl⟩
    have hmem' : Q.system.embed x ∈
        (spacingLattice 4 Q.system.setting.side Q.system.setting.ξ :
          Set Q.system.setting.Point) := by
      have e : Q.system.setting.ξ = 𝒮.scale 0 := hξ.trans scale_zero.symm
      rw [e]
      exact hmem
    exact Classical.epsilon_spec
      (p := fun y : Q.system.setting.FineSite =>
        (y : Q.system.setting.Point) = Q.system.embed x) ⟨⟨_, hmem'⟩, rfl⟩
  have hlift : ∀ x : 𝒮.Point, supNorm (x - Q.centre) < 5 / 6 * cubeSide 𝒮 M Q.level →
      ∃ v : Fin 4 → ℝ, torusProj 4 𝒮.side (Q.liftedCentre + v) = x ∧
        ‖v‖ < 5 / 6 * cubeSide 𝒮 M Q.level := by
    intro x hx
    obtain ⟨v, hv, hn⟩ := exists_proj_eq_norm_le (x - Q.centre)
    refine ⟨v, ?_, hn.trans_lt hx⟩
    rw [proj_add, proj_liftedCentre, hv]
    abel
  have hbox : ∀ v : Fin 4 → ℝ, ‖v‖ < cubeSide 𝒮 M Q.level →
      Q.liftedCentre + v ∈
        {p : Fin 4 → ℝ | ∀ μ, |p μ - Q.liftedCentre μ| < cubeSide 𝒮 M Q.level} := by
    intro v hv μ
    simp only [Pi.add_apply, add_sub_cancel_left]
    exact (abs_apply_le_pi_norm v μ).trans_lt hv
  have hmove : ∀ (x : 𝒮.Point) (w : Fin 4 → ℝ),
      supNorm (x - Q.centre) < 5 / 6 * cubeSide 𝒮 M Q.level → ‖w‖ ≤ 𝒮.ξ →
      x + torusProj 4 𝒮.side w ∈ Q.strictPts ∧
        Q.system.embed (x + torusProj 4 𝒮.side w) =
          Q.system.embed x + torusProj 4 Q.system.setting.side w := by
    intro x w hx hw
    obtain ⟨v, hv, hn⟩ := hlift x hx
    have hp := hbox v (by nlinarith)
    have hpw : Q.liftedCentre + v + w ∈
        {p : Fin 4 → ℝ | ∀ μ, |p μ - Q.liftedCentre μ| < cubeSide 𝒮 M Q.level} := by
      rw [add_assoc]
      exact hbox (v + w) ((norm_add_le v w).trans_lt (by nlinarith))
    have h₁ := htrans (Q.liftedCentre + v) w hp hpw
    rw [hv] at h₁
    refine ⟨?_, h₁⟩
    have h₂ := hbij.mapsTo hpw
    rwa [proj_add, hv] at h₂
  refine ⟨hξ, fun x hx => ?_, hcoe, fun x x' hx hx' e => ?_, fun x ν hx => ?_,
    fun x ν hx => ?_⟩
  · obtain ⟨v, hv, hn⟩ := hlift x hx
    have h₂ := hbij.mapsTo (hbox v (by nlinarith))
    rwa [hv] at h₂
  · refine Subtype.ext (hbij₂.injOn hx hx' ?_)
    rw [← hcoe x hx, ← hcoe x' hx', e]
  · have h := hmove x (Pi.single ν 𝒮.ξ) hx (norm_pi_single_le hξ₀.le ν)
    have hin : ((x + unitStep 4 𝒮.side 𝒮.ξ ν : 𝒮.FineSite) : 𝒮.Point) ∈ Q.strictPts := h.1
    refine ⟨hin, Subtype.ext ?_⟩
    rw [hcoe _ hin]
    refine h.2.trans ?_
    have hx' : (x : 𝒮.Point) ∈ Q.strictPts := by
      obtain ⟨v, hv, hn⟩ := hlift x hx
      have h₂ := hbij.mapsTo (hbox v (by nlinarith))
      rwa [hv] at h₂
    change _ = ((Q.system.mapSite x : Q.system.setting.FineSite) : Q.system.setting.Point) +
      torusProj 4 Q.system.setting.side (Pi.single ν Q.system.setting.ξ)
    rw [hcoe x hx', hξ]
  · have h := hmove x (-Pi.single ν 𝒮.ξ) hx
      (by rw [norm_neg]; exact norm_pi_single_le hξ₀.le ν)
    rw [proj_neg, proj_neg] at h
    have hin : ((x - unitStep 4 𝒮.side 𝒮.ξ ν : 𝒮.FineSite) : 𝒮.Point) ∈ Q.strictPts := h.1
    refine ⟨hin, Subtype.ext ?_⟩
    rw [hcoe _ hin]
    refine h.2.trans ?_
    have hx' : (x : 𝒮.Point) ∈ Q.strictPts := by
      obtain ⟨v, hv, hn⟩ := hlift x hx
      have h₂ := hbij.mapsTo (hbox v (by nlinarith))
      rwa [hv] at h₂
    change _ = ((Q.system.mapSite x : Q.system.setting.FineSite) : Q.system.setting.Point) -
      torusProj 4 Q.system.setting.side (Pi.single ν Q.system.setting.ξ)
    rw [hcoe x hx', hξ, sub_eq_add_neg]
end Cube
section Agreement
variable {𝒮 : NestedRegions} {M : ℕ} {Q : LevelCube 𝒮 M} {O W : Set 𝒮.Point}
structure NearCube (Q : LevelCube 𝒮 M) (O : Set 𝒮.Point) : Prop where
  chart : LatticeChart Q.system O Q.strictPts
  thicken_subset : Q.thicken (5 / 6) ⊆ Q.strictPts
  near_mem : ∀ p ∈ Q.thicken (5 / 6), ∀ y : 𝒮.FineSite,
    supNorm (p - (y : 𝒮.Point)) ≤ 𝒮.ξ → (y : 𝒮.Point) ∈ 𝒮.Ω 0
  local_Ω_zero : Q.system.setting.Ω 0 = univ
theorem supNorm_zero_le {T : ℝ} : supNorm (0 : PeriodicTorus 4 T) ≤ 0 := by
  have h₀ := supNorm_proj_le (T := T) 0
  have e : torusProj 4 T 0 = 0 := by
    funext μ
    simp [torusProj]
  rwa [e, norm_zero] at h₀
theorem NearCube.mem_Ω_zero (hn : NearCube Q O) (x : 𝒮.FineSite)
    (hx : (x : 𝒮.Point) ∈ Q.thicken (5 / 6)) : (x : 𝒮.Point) ∈ 𝒮.Ω 0 := by
  refine hn.near_mem _ hx x ?_
  rw [sub_self]
  exact supNorm_zero_le.trans 𝒮.ξ_pos.le
theorem NearCube.projSites_eq (hn : NearCube Q O) (hWR : W ⊆ Q.thicken (5 / 6))
    {u : 𝒮.FineSite → ℝ} (hu : ∀ x : 𝒮.FineSite, (x : 𝒮.Point) ∉ W → u x = 0) :
    projSites u = u := by
  funext x
  by_cases hx : (x : 𝒮.Point) ∈ 𝒮.Ω 0
  · simp [projSites, restrictTo, hx]
  · have hxW : (x : 𝒮.Point) ∉ W := fun h => hx (hn.mem_Ω_zero x (hWR h))
    simp [projSites, restrictTo, hx, hu x hxW]
theorem NearCube.siteFunctionsMatch (hn : NearCube Q O) (hWR : W ⊆ Q.thicken (5 / 6))
    {u : 𝒮.FineSite → ℝ} {v : Q.system.setting.FineSite → ℝ} (h : Matched Q.system W u v) :
    SiteFunctionsMatch Q (projSites u) v := by
  rw [hn.projSites_eq hWR h.vanish]
  have hRI := hn.thicken_subset
  refine ⟨fun x hx => h.vanish x fun hW => hx (hWR hW),
    fun y hy => h.vanish_image y fun x hx e => hy ?_,
    fun x hx => h.eq_of_mem hn.chart (hWR.trans hRI) (hRI hx)⟩
  exact ⟨x, hWR hx, by rw [← hn.chart.coe_mapSite x (hRI (hWR hx)), e]⟩
theorem NearCube.anchor_eq_and_mem_bonds (hn : NearCube Q O) (b : 𝒮.FineBond)
    (hb : AnchoredIn (Q.thicken (5 / 6)) b) : 𝒮.anchor b = b.source ∧ b ∈ 𝒮.bonds := by
  have hn₁ := norm_pi_single_le 𝒮.ξ_pos.le b.dir
  have hb' : ((𝒮.anchor b : 𝒮.FineSite) : 𝒮.Point) ∈ Q.thicken (5 / 6) := hb
  by_cases hcond : (b.source : 𝒮.Point) ∉ 𝒮.Ω 0 ∧ (b.target : 𝒮.Point) ∈ 𝒮.Ω 0
  · have hbp : 𝒮.anchor b = b.target := if_pos hcond
    rw [hbp] at hb'
    refine absurd (hn.near_mem _ hb' b.source ?_) hcond.1
    have e : (b.target : 𝒮.Point) - (b.source : 𝒮.Point) =
        torusProj 4 𝒮.side (Pi.single b.dir 𝒮.ξ) := by
      change (b.source : 𝒮.Point) + torusProj 4 𝒮.side (Pi.single b.dir 𝒮.ξ) - _ = _
      abel
    rw [e]
    exact (supNorm_proj_le _).trans hn₁
  · have hbp : 𝒮.anchor b = b.source := if_neg hcond
    rw [hbp] at hb'
    refine ⟨hbp, 𝒮.mem_bonds_of_mem b (hn.mem_Ω_zero _ hb') (hn.near_mem _ hb' b.target ?_)⟩
    have e : (b.source : 𝒮.Point) - (b.target : 𝒮.Point) =
        torusProj 4 𝒮.side (-Pi.single b.dir 𝒮.ξ) := by
      rw [proj_neg]
      change _ - ((b.source : 𝒮.Point) + torusProj 4 𝒮.side (Pi.single b.dir 𝒮.ξ)) = _
      abel
    rw [e]
    exact (supNorm_proj_le _).trans (by rw [norm_neg]; exact hn₁)
theorem NearCube.bondFunctionsMatch (hn : NearCube Q O) (hWR : W ⊆ Q.thicken (5 / 6))
    {G : 𝒮.FineBond → ℝ} {B : Q.system.setting.FineBond → ℝ}
    (h : ∀ ν, Matched Q.system W (comp G ν) (comp B ν)) :
    BondFunctionsMatch Q (projBonds G) B := by
  have hRI := hn.thicken_subset
  refine ⟨fun b hb => ?_, fun c hc => ?_, fun b hb => ?_⟩
  · by_cases hbb : b ∈ 𝒮.bonds
    · have hG : G b = 0 := (h b.dir).vanish b.source fun hW => hb ?_
      · simp [projBonds, hbb, hG]
      · have hbp : 𝒮.anchor b = b.source :=
          if_neg fun hcond => hcond.1 (hn.mem_Ω_zero _ (hWR hW))
        change ((𝒮.anchor b : 𝒮.FineSite) : 𝒮.Point) ∈ _
        rw [hbp]
        exact hWR hW
    · simp [projBonds, hbb]
  · refine (h c.dir).vanish_image c.source fun x hx e => hc ?_
    have hbp : Q.system.setting.anchor c = c.source :=
      if_neg fun hcond => hcond.1 (by rw [hn.local_Ω_zero]; exact mem_univ _)
    change ((Q.system.setting.anchor c : Q.system.setting.FineSite) :
      Q.system.setting.Point) ∈ _
    rw [hbp]
    exact ⟨x, hWR hx, by rw [← hn.chart.coe_mapSite x (hRI (hWR hx)), e]⟩
  · obtain ⟨hbp, hbb⟩ := hn.anchor_eq_and_mem_bonds b hb
    have hsrc : (b.source : 𝒮.Point) ∈ Q.thicken (5 / 6) := by
      have hb' : ((𝒮.anchor b : 𝒮.FineSite) : 𝒮.Point) ∈ Q.thicken (5 / 6) := hb
      rwa [hbp] at hb'
    have hpb : projBonds G b = G b := by simp [projBonds, hbb]
    rw [hpb]
    exact (h b.dir).eq_of_mem hn.chart (hWR.trans hRI) (hRI hsrc)
theorem NearCube.eq_zero_of_source_not_mem (hn : NearCube Q O) (hWR : W ⊆ Q.thicken (5 / 6))
    {A : 𝒮.FineBond → ℝ} (hA : AnchorSupported W A) (b : 𝒮.FineBond)
    (hb : (b.source : 𝒮.Point) ∉ W) : A b = 0 := by
  by_contra hne
  have hin : AnchoredIn W b := by
    by_contra h
    exact hne (hA b h)
  have hin' : ((𝒮.anchor b : 𝒮.FineSite) : 𝒮.Point) ∈ W := hin
  rw [(hn.anchor_eq_and_mem_bonds b (hWR hin)).1] at hin'
  exact hb hin'
end Agreement
theorem claim_holds (hD : DifferenceAdjointsHold) (hH : HodgeFactsHold)
    (hT : TorusLengthsStatement) (hMaps : FirstTypeMaps.Statement)
    (hSites : FirstTypeLattice.Statement) (hKind : PositionByType.Statement)
    (hThick : ThickenedCubeLocation.Claim) (hSep : DistanceSeparation.Statement) : Claim := by
  intro K m M R₁ 𝒮 hs hM Q hQ
  have hsep := hSep K m M R₁ 𝒮 hs hM
  have hpos := (hKind K m M R₁ 𝒮 hs hM).firstType Q hQ
  have hthick := hThick K m M R₁ 𝒮 hs hM Q hQ.1
  have hmaps := hMaps 𝒮 K m M R₁ hs Q hQ
  have hsites := hSites 𝒮 K m M R₁ hs Q hQ 0 (Or.inl (Nat.zero_le _))
  have hξ := 𝒮.ξ_pos
  have hr : 100 * 𝒮.ξ ≤ mollifyRadius 𝒮 M Q.level := by
    have h₁ := hsep.scale_succ_le Q.level
    have h₂ := ξ_le_scale_succ (𝒮 := 𝒮) Q.level
    linarith
  have hr₀ : 0 ≤ mollifyRadius 𝒮 M Q.level := by linarith
  have hB₀ := hsep.mollifyRadius_le Q.level
  have hB : 6 * 𝒮.ξ ≤ cubeSide 𝒮 M Q.level := by linarith
  have hM₁ : 1 ≤ M := (Nat.one_le_pow _ _ (by have := 𝒮.thirteen_le_L; omega)).trans hM
  obtain ⟨hadm, hset⟩ : ∃ h : Q.IsAdmissible, Q.system.setting = Q.torusSetting h :=
    hmaps.1
  have hξ' : Q.system.setting.ξ = 𝒮.ξ := by
    have key : ∀ 𝒰 : NestedRegions, 𝒰 = Q.torusSetting hadm → 𝒰.ξ = 𝒮.ξ := by
      rintro _ rfl
      rfl
    exact key _ hset
  have hfirst : Q.system.setting.Ω 0 = univ := by
    have key : ∀ 𝒰 : NestedRegions, 𝒰 = Q.torusSetting hadm → 𝒰.Ω 0 = univ := by
      rintro _ rfl
      simp [LevelCube.torusSetting, LevelCube.torusRegions]
    exact key _ hset
  have hc := latticeChart Q hmaps (hsites.1.subset.trans inter_subset_left) hB hξ'
  have hRO := hthick.near_centre
  have hRI : Q.thicken (5 / 6) ⊆ Q.strictPts := hRO.trans hc.subset
  have hcl : tsupport (indicator (Q.thicken (5 / 6)) (1 : 𝒮.Point → ℝ)) ⊆ Q.strictPts := by
    have hcont : Continuous fun x : 𝒮.Point => supNorm (x - Q.centre) :=
      ((hT 4 𝒮.side 𝒮.side_pos).1.continuous_supNorm).comp
        (continuous_id.sub continuous_const)
    have hclosed : IsClosed {x : 𝒮.Point | supNorm (x - Q.centre) ≤
        5 / 6 * cubeSide 𝒮 M Q.level} := isClosed_le hcont continuous_const
    intro x hx
    have hle : supNorm (x - Q.centre) ≤ 5 / 6 * cubeSide 𝒮 M Q.level :=
      closure_minimal (fun p hp => by
        by_cases hpR : p ∈ Q.thicken (5 / 6)
        · have h' : supNorm (p - Q.centre) < 5 / 6 * cubeSide 𝒮 M Q.level := hRO hpR
          exact h'.le
        · exact absurd (indicator_of_notMem hpR _) hp) hclosed hx
    change supNorm (x - Q.centre) < cubeSide 𝒮 M Q.level
    linarith
  have hn : NearCube Q {x | supNorm (x - Q.centre) < 5 / 6 * cubeSide 𝒮 M Q.level} :=
    ⟨hc, hRI, fun p hp y hd => mem_Ω_zero_of_near Q hM₁ hpos.far_from_outside hp y hd, hfirst⟩
  have hW₀R : Q.thicken (2 / 3) ⊆ Q.thicken (5 / 6) := thicken_mono Q hr₀ (by norm_num)
  have hW₁R : Q.thicken (2 / 3 + 1 / 100) ⊆ Q.thicken (5 / 6) :=
    thicken_mono Q hr₀ (by norm_num)
  have hW₂R : Q.thicken (2 / 3 + 1 / 100 + 1 / 100) ⊆ Q.thicken (5 / 6) :=
    thicken_mono Q hr₀ (by norm_num)
  have hw₀ := oneStepWider_thicken Q (c := 2 / 3) hr
    (hsep.exists_near_supp Q _ (by norm_num)) (hW₁R.trans hRO)
  have hw₁ := oneStepWider_thicken Q (c := 2 / 3 + 1 / 100) hr
    (hsep.exists_near_supp Q _ (by norm_num)) (hW₂R.trans hRO)
  have hsite : ∀ f ∈ 𝒮.siteFns, projSites f = f := by
    intro f hf
    funext x
    by_cases hx : (x : 𝒮.Point) ∈ 𝒮.Ω 0
    · simp [projSites, restrictTo, hx]
    · simp [projSites, restrictTo, hx, hf x hx]
  have hform : ∀ A ∈ 𝒮.oneForms, projBonds A = A := by
    intro A hA
    funext b
    by_cases hb : b ∈ 𝒮.bonds
    · simp [projBonds, hb]
    · simp [projBonds, hb, hA b hb]
  have hadj : ∀ A : 𝒮.FineBond → ℝ, AnchorSupported (Q.thicken (2 / 3)) A →
      Matched Q.system (Q.thicken (2 / 3 + 1 / 100)) (dTorusAdj A)
        (dTorusAdj (restrictBonds Q A)) := by
    intro A hA
    rw [dTorusAdj_eq hD hT A, dTorusAdj_eq hD hT (restrictBonds Q A)]
    exact Matched.sum_fin fun ν =>
      (matched_pullBonds hc hcl hW₀R A (hn.eq_zero_of_source_not_mem hW₀R hA) ν).backward_diff
        hc hw₀ ν
  refine ⟨fun f hf hfW => ?_, fun f hf hfW => ?_, fun A hA hAW => ?_, fun A hA hAW => ?_⟩
  · have hrel : Matched Q.system (Q.thicken (2 / 3)) f (restrictSites Q f) :=
      matched_pullSites hc hcl hW₀R f hfW
    unfold dirichletLap
    rw [hsite f hf]
    exact hn.siteFunctionsMatch hW₂R (hrel.lattice_laplacian hc hw₀ hw₁)
  · have hrel : Matched Q.system (Q.thicken (2 / 3)) f (restrictSites Q f) :=
      matched_pullSites hc hcl hW₀R f hfW
    unfold dDir
    rw [hsite f hf]
    exact hn.bondFunctionsMatch hW₁R fun ν => hrel.forward_diff hc hw₀ ν
  · unfold dDirAdj
    rw [hform A hA]
    exact hn.siteFunctionsMatch hW₁R (hadj A hAW)
  · unfold curlSqDir
    rw [hform A hA, curlTorusAdj_curlTorus hH A, curlTorusAdj_curlTorus hH (restrictBonds Q A)]
    refine hn.bondFunctionsMatch hW₂R fun ν => ?_
    have hrel : Matched Q.system (Q.thicken (2 / 3)) (comp A ν)
        (comp (restrictBonds Q A) ν) :=
      matched_pullBonds hc hcl hW₀R A (hn.eq_zero_of_source_not_mem hW₀R hAW) ν
    have key := (hrel.lattice_laplacian hc hw₀ hw₁).sub ((hadj A hAW).forward_diff hc hw₁ ν)
    have e₁ : comp (bondLap A - dTorus (dTorusAdj A)) ν =
        fun x => latticeLaplacian (comp A ν) x - forwardDiff ν (dTorusAdj A) x := by
      funext x
      rw [← (hH 𝒮).comp_bondLap A ν]
      rfl
    have e₂ : comp (bondLap (restrictBonds Q A) -
        dTorus (dTorusAdj (restrictBonds Q A))) ν =
        fun y => latticeLaplacian (comp (restrictBonds Q A) ν) y -
          forwardDiff ν (dTorusAdj (restrictBonds Q A)) y := by
      funext y
      rw [← (hH Q.system.setting).comp_bondLap (restrictBonds Q A) ν]
      rfl
    rw [e₁, e₂]
    exact key
end YangMills.Construction.PartitionCubes.LocalTorusOperators
