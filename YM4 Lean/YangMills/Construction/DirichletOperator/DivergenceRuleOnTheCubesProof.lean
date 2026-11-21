import YangMills.Construction.DirichletOperator.DifferenceOperatorsAgreeOnTheLocalTorusProof
import YangMills.Construction.DirichletOperator.DivergenceRuleOnTheCubes
import YangMills.Construction.RegionSequence.CellsAndAdjoints
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Dirichlet Torus RegionSequence RegionSequence.NestedRegions PartitionCubes
namespace CubeDivergence
variable {𝒮 : NestedRegions} {M : ℕ}
theorem supNorm_eq_norm {S : ℝ} (p : PeriodicTorus 4 S) : supNorm p = ‖p‖ := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.supNorm_eq_norm <;> assumption
theorem norm_torusProj_le {S ξ : ℝ} (hξ : 0 ≤ ξ) (v : Fin 4 → ℝ) (hv : ‖v‖ ≤ ξ) :
    ‖torusProj 4 S v‖ ≤ ξ :=
  (pi_norm_le_iff_of_nonneg hξ).2 fun μ =>
    (TorusMetric.addCircle_norm_coe_le_abs (v μ)).trans ((norm_le_pi_norm v μ).trans hv)
theorem norm_piSingle_le {ξ : ℝ} (hξ : 0 ≤ ξ) (ν : Fin 4) :
    ‖(Pi.single ν ξ : Fin 4 → ℝ)‖ ≤ ξ := by apply _root_.YangMills.Construction.PartitionCubes.LocalTorusOperators.norm_pi_single_le <;> assumption
theorem norm_unitStep_le (ν : Fin 4) : ‖(unitStep 4 𝒮.side 𝒮.ξ ν : 𝒮.Point)‖ ≤ 𝒮.ξ :=
  norm_torusProj_le 𝒮.ξ_pos.le _ (norm_piSingle_le 𝒮.ξ_pos.le ν)
theorem nine_mul_ξ_lt_cubeSide (hM : 𝒮.L ^ 5 ≤ M) (n : ℕ) : 9 * 𝒮.ξ < cubeSide 𝒮 M n := by
  have hL : (13 : ℝ) ≤ 𝒮.L := by exact_mod_cast 𝒮.thirteen_le_L
  have hL1 : (1 : ℝ) ≤ 𝒮.L := by linarith
  have hM' : (𝒮.L : ℝ) ^ 5 ≤ M := by exact_mod_cast hM
  have h5 : (13 : ℝ) ≤ (𝒮.L : ℝ) ^ 5 := by
    calc (13 : ℝ) ≤ 𝒮.L := hL
      _ = (𝒮.L : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (𝒮.L : ℝ) ^ 5 := pow_le_pow_right₀ hL1 (by norm_num)
  have hn : (1 : ℝ) ≤ (𝒮.L : ℝ) ^ n := one_le_pow₀ hL1
  have hξ := 𝒮.ξ_pos
  have hs : 𝒮.ξ ≤ 𝒮.scale n := by
    simp only [RegionSequence.NestedRegions.scale, scaleSpacing, zpow_natCast]
    nlinarith
  have : (13 : ℝ) * 𝒮.scale n ≤ cubeSide 𝒮 M n := by
    simp only [cubeSide]
    have : 0 < 𝒮.scale n := lt_of_lt_of_le hξ hs
    nlinarith
  linarith
theorem finite_fineBond (hl : TorusLengthsStatement) (𝒯 : NestedRegions) : Finite 𝒯.FineBond := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineBond <;> assumption
theorem bondInner_comm {𝒯 : NestedRegions} (A B : 𝒯.FineBond → ℝ) : bondInner A B = bondInner B A := by apply _root_.YangMills.Construction.RegionSequence.GradientAdjointsOnTorus.bondInner_comm <;> assumption
theorem tensorInner_comm {𝒯 : NestedRegions} {r : ℕ} (J J' : 𝒯.Tensor r) :
    tensorInner J J' = tensorInner J' J :=
  Finset.sum_congr rfl fun _ _ => bondInner_comm _ _
theorem adjointValue_eq_of_forall (hl : TorusLengthsStatement) {𝒯 : NestedRegions}
    (F : Submodule ℝ (𝒯.FineBond → ℝ)) (w : 𝒯.Tensor 1) (v₀ : 𝒯.FineBond → ℝ) (h₀ : v₀ ∈ F)
    (hv : ∀ u ∈ F, bondInner v₀ u = tensorInner w (nablaOne u)) :
    adjointValue (F : Set (𝒯.FineBond → ℝ)) bondInner tensorInner nablaOne w = v₀ := by
  have hspec := Classical.epsilon_spec
    (p := fun v => v ∈ (F : Set (𝒯.FineBond → ℝ)) ∧ ∀ u ∈ (F : Set (𝒯.FineBond → ℝ)),
      bondInner v u = tensorInner w (nablaOne u)) ⟨v₀, h₀, hv⟩
  change adjointValue (F : Set (𝒯.FineBond → ℝ)) bondInner tensorInner nablaOne w ∈
    (F : Set (𝒯.FineBond → ℝ)) ∧ ∀ u ∈ (F : Set (𝒯.FineBond → ℝ)),
      bondInner (adjointValue (F : Set (𝒯.FineBond → ℝ)) bondInner tensorInner nablaOne w) u =
        tensorInner w (nablaOne u) at hspec
  generalize adjointValue (F : Set (𝒯.FineBond → ℝ)) bondInner tensorInner nablaOne w = v₁ at hspec ⊢
  obtain ⟨h₁, h₂⟩ := hspec
  have := finite_fineBond hl 𝒯
  have := Fintype.ofFinite 𝒯.FineBond
  have hd : v₁ - v₀ ∈ F := F.sub_mem h₁ h₀
  have e₁ := h₂ _ hd
  have e₀ := hv _ hd
  simp only [bondInner, finsum_eq_sum_of_fintype] at e₁ e₀
  have hξ : 𝒯.ξ ^ 4 ≠ 0 := (pow_pos 𝒯.ξ_pos 4).ne'
  have hsum : ∑ b, (v₁ - v₀) b ^ 2 = 0 := by
    have : 𝒯.ξ ^ 4 * ∑ b, (v₁ - v₀) b ^ 2 = 0 := by
      have e : ∑ b, (v₁ - v₀) b ^ 2 =
          (∑ b, v₁ b * (v₁ - v₀) b) - ∑ b, v₀ b * (v₁ - v₀) b := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun b _ => by simp only [Pi.sub_apply]; ring
      rw [e, mul_sub, e₁, e₀, sub_self]
    exact (mul_eq_zero.mp this).resolve_left hξ
  have hz := (Finset.sum_eq_zero_iff_of_nonneg fun b _ => sq_nonneg ((v₁ - v₀) b)).mp hsum
  funext b
  have := hz b (Finset.mem_univ b)
  have h' : v₁ b - v₀ b = 0 := by simpa using this
  linarith
theorem pullBonds_apply_of_unique (C : CubeSystem 𝒮) (φ : 𝒮.Point → ℝ) (A : 𝒮.FineBond → ℝ)
    (b₀ : 𝒮.FineBond) (d : C.setting.FineBond) (hE : C.mapBond b₀ = d)
    (hu : ∀ b : 𝒮.FineBond, (b.source : 𝒮.Point) ∈ tsupport φ → C.mapBond b = d → b = b₀) :
    C.pullBonds φ A d = φ (b₀.source : 𝒮.Point) * A b₀ := by
  unfold CubeSystem.pullBonds
  by_cases h₀ : (b₀.source : 𝒮.Point) ∈ tsupport φ
  · have : {b : 𝒮.FineBond | (b.source : 𝒮.Point) ∈ tsupport φ ∧ C.mapBond b = d} = {b₀} := by
      ext b
      constructor
      · rintro ⟨h₁, h₂⟩
        exact hu b h₁ h₂
      · rintro rfl
        exact ⟨h₀, hE⟩
    rw [this, finsum_mem_singleton]
  · have : {b : 𝒮.FineBond | (b.source : 𝒮.Point) ∈ tsupport φ ∧ C.mapBond b = d} = ∅ := by
      ext b
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro h₁ h₂
      exact h₀ (hu b h₁ h₂ ▸ h₁)
    rw [this, finsum_mem_empty, image_eq_zero_of_notMem_tsupport h₀, zero_mul]
theorem pullBonds_apply_eq_zero (C : CubeSystem 𝒮) (φ : 𝒮.Point → ℝ) (A : 𝒮.FineBond → ℝ)
    (d : C.setting.FineBond)
    (hn : ∀ b : 𝒮.FineBond, (b.source : 𝒮.Point) ∈ tsupport φ → C.mapBond b ≠ d) :
    C.pullBonds φ A d = 0 := by
  unfold CubeSystem.pullBonds
  have : {b : 𝒮.FineBond | (b.source : 𝒮.Point) ∈ tsupport φ ∧ C.mapBond b = d} = ∅ := by
    ext b
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
    exact hn b
  rw [this, finsum_mem_empty]
theorem pushBonds_apply_of_unique (C : CubeSystem 𝒮) (g : 𝒮.FineBond → ℝ) (b₀ : 𝒮.FineBond)
    (d : C.setting.FineBond) (hE : C.mapBond b₀ = d)
    (hu : ∀ b : 𝒮.FineBond, g b ≠ 0 → C.mapBond b = d → b = b₀) :
    pushBonds C g d = g b₀ := by
  unfold pushBonds
  rw [← finsum_mem_inter_support]
  by_cases h₀ : g b₀ = 0
  · have : {b : 𝒮.FineBond | C.mapBond b = d} ∩ Function.support g = ∅ := by
      ext b
      simp only [mem_inter_iff, mem_ofPred_eq, Function.mem_support, mem_empty_iff_false, iff_false,
        not_and]
      intro h₁ h₂
      exact h₂ (hu b h₂ h₁ ▸ h₀)
    rw [this, finsum_mem_empty, h₀]
  · have : {b : 𝒮.FineBond | C.mapBond b = d} ∩ Function.support g = {b₀} := by
      ext b
      simp only [mem_inter_iff, mem_ofPred_eq, Function.mem_support, mem_singleton_iff]
      constructor
      · rintro ⟨h₁, h₂⟩
        exact hu b h₂ h₁
      · rintro rfl
        exact ⟨hE, h₀⟩
    rw [this, finsum_mem_singleton]
theorem pushBonds_apply_eq_zero (C : CubeSystem 𝒮) (g : 𝒮.FineBond → ℝ) (d : C.setting.FineBond)
    (hn : ∀ b : 𝒮.FineBond, g b ≠ 0 → C.mapBond b ≠ d) : pushBonds C g d = 0 := by
  unfold pushBonds
  rw [← finsum_mem_inter_support]
  have : {b : 𝒮.FineBond | C.mapBond b = d} ∩ Function.support g = ∅ := by
    ext b
    simp only [mem_inter_iff, mem_ofPred_eq, Function.mem_support, mem_empty_iff_false, iff_false,
      not_and]
    intro h₁ h₂
    exact hn b h₂ h₁
  rw [this, finsum_mem_empty]
theorem leibnizRemainder_apply (Φ : 𝒮.FineSite → ℝ) (J : 𝒮.Tensor 1) (b : 𝒮.FineBond) :
    leibnizRemainder Φ J b = ∑ ν, 𝒮.ξ⁻¹ * (Φ b.source - Φ (b.source - unitStep 4 𝒮.side 𝒮.ξ ν)) *
      J (constIdx ν) (shiftDown ν b) := by
  simp only [leibnizRemainder, Finset.sum_apply, smulSiteBond, translateBackward, forwardDiff,
    smul_eq_mul, sub_add_cancel]
theorem mul_sum_bwdDiff_eq (Φ : 𝒮.FineSite → ℝ) (J : 𝒮.Tensor 1) (b : 𝒮.FineBond) :
    Φ b.source * ∑ ν, bwdDiff ν (J (constIdx ν)) b =
      (∑ ν, 𝒮.ξ⁻¹ * (Φ (b.source - unitStep 4 𝒮.side 𝒮.ξ ν) * J (constIdx ν) (shiftDown ν b) -
        Φ b.source * J (constIdx ν) b)) + leibnizRemainder Φ J b := by
  rw [leibnizRemainder_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  simp only [bwdDiff]
  ring
theorem leibnizRemainder_eq_zero (Φ : 𝒮.FineSite → ℝ) (J : 𝒮.Tensor 1) (b : 𝒮.FineBond)
    (h₀ : Φ b.source = 0) (h₁ : ∀ ν, Φ (b.source - unitStep 4 𝒮.side 𝒮.ξ ν) = 0) :
    leibnizRemainder Φ J b = 0 := by
  rw [leibnizRemainder_apply]
  exact Finset.sum_eq_zero fun ν _ => by rw [h₀, h₁ ν]; simp
theorem formDiv_eq_of_forms_eq (hl : TorusLengthsStatement)
    (hcell : CellStructure.CellStructureClaim) (C : CubeSystem 𝒮)
    (hf : C.forms = C.setting.oneForms) (hb : ∀ b : C.setting.FineBond, b ∈ C.setting.bonds)
    (w : C.setting.Tensor 1) :
    formDiv C w = fun c => ∑ ν, bwdDiff ν (w (constIdx ν)) c := by
  have A := (hcell C.setting).2.2.2.1
  have : formDiv C w = divOne w := by
    unfold formDiv
    apply adjointValue_eq_of_forall hl
    · rw [hf]
      exact (A.nabla_adjoint w).1
    · intro u hu
      rw [hf] at hu
      rw [bondInner_comm, tensorInner_comm]
      exact ((A.nabla_adjoint w).2 u hu).symm
  rw [this]
  funext c
  exact A.divOne_apply w c (hb c)
theorem pullBonds_divOne_of_mapSite (C : CubeSystem 𝒮) (φ : 𝒮.Point → ℝ) (J : 𝒮.Tensor 1)
    (P₀ P₁ P₂ : 𝒮.FineSite → Prop) (hξ : C.setting.ξ = 𝒮.ξ)
    (hdiv : ∀ w : C.setting.Tensor 1,
      formDiv C w = fun c => ∑ ν, bwdDiff ν (w (constIdx ν)) c)
    (hsupp : ∀ x : 𝒮.FineSite, (x : 𝒮.Point) ∈ tsupport φ → P₀ x)
    (h₀₁ : ∀ x, P₀ x → P₁ x) (h₁₂ : ∀ x, P₁ x → P₂ x)
    (hplus : ∀ x ν, P₀ x → P₁ (x + unitStep 4 𝒮.side 𝒮.ξ ν))
    (hminus : ∀ x ν, P₁ x → P₂ (x - unitStep 4 𝒮.side 𝒮.ξ ν))
    (hinj : ∀ x y, P₂ x → P₂ y → C.mapSite x = C.mapSite y → x = y)
    (hEplus : ∀ x ν, P₀ x → C.mapSite (x + unitStep 4 𝒮.side 𝒮.ξ ν) =
      C.mapSite x + unitStep 4 C.setting.side C.setting.ξ ν)
    (hEminus : ∀ x ν, P₁ x → C.mapSite (x - unitStep 4 𝒮.side 𝒮.ξ ν) =
      C.mapSite x - unitStep 4 C.setting.side C.setting.ξ ν)
    (hbond : ∀ b : 𝒮.FineBond, φ (b.source : 𝒮.Point) ≠ 0 → b ∈ 𝒮.bonds) :
    C.pullBonds φ (divOne J) =
      formDiv C (C.pullTensor φ J) + pushBonds C (leibnizRemainder (fun x => φ x) J) := by
  have hm : ∀ b : 𝒮.FineBond, leibnizRemainder (fun x : 𝒮.FineSite => φ x) J b ≠ 0 →
      P₁ b.source := by
    intro b hb
    by_contra hP
    apply hb
    apply leibnizRemainder_eq_zero
    · by_contra h
      exact hP (h₀₁ _ (hsupp _ (subset_tsupport _ h)))
    · intro ν
      by_contra h
      have := hplus _ ν (hsupp _ (subset_tsupport _ h))
      rw [sub_add_cancel] at this
      exact hP this
  have hbu : ∀ b b' : 𝒮.FineBond, P₂ b.source → P₂ b'.source → C.mapBond b = C.mapBond b' →
      b = b' := by
    rintro ⟨t, μ⟩ ⟨t', μ'⟩ h h' e
    simp only [CubeSystem.mapBond, LatticeBond.mk.injEq] at e
    rw [hinj t t' h h' e.1, e.2]
  have hev : ∀ (A : 𝒮.FineBond → ℝ) (b₀ : 𝒮.FineBond), P₂ b₀.source →
      C.pullBonds φ A (C.mapBond b₀) = φ (b₀.source : 𝒮.Point) * A b₀ :=
    fun A b₀ h => pullBonds_apply_of_unique C φ A b₀ _ rfl fun b hb e =>
      hbu b b₀ (h₁₂ _ (h₀₁ _ (hsupp _ hb))) h e
  have hback : ∀ (b : 𝒮.FineBond) (ν : Fin 4), P₁ b.source →
      shiftDown ν (C.mapBond b) = C.mapBond (shiftDown ν b) := by
    intro b ν h
    simp only [shiftDown, CubeSystem.mapBond, hEminus _ ν h]
  funext c
  rw [hdiv]
  simp only [Pi.add_apply, bwdDiff, CubeSystem.pullTensor]
  by_cases hx : ∃ x, P₁ x ∧ C.mapSite x = c.source
  · obtain ⟨x, hx₁, hxc⟩ := hx
    obtain ⟨b, hbP, rfl⟩ : ∃ b : 𝒮.FineBond, P₁ b.source ∧ C.mapBond b = c :=
      ⟨⟨x, c.dir⟩, hx₁, by simp only [CubeSystem.mapBond, hxc]⟩
    rw [hev _ b (h₁₂ _ hbP), pushBonds_apply_of_unique C _ b _ rfl fun b' h e =>
      hbu b' b (h₁₂ _ (hm _ h)) (h₁₂ _ hbP) e]
    have hL : φ (b.source : 𝒮.Point) * divOne J b =
        φ (b.source : 𝒮.Point) * ∑ ν, bwdDiff ν (J (constIdx ν)) b := by
      by_cases h : φ (b.source : 𝒮.Point) = 0
      · rw [h, zero_mul, zero_mul]
      · simp only [divOne, projBonds, indicator_of_mem (hbond b h)]
    rw [hL]
    refine (mul_sum_bwdDiff_eq (fun x : 𝒮.FineSite => φ x) J b).trans ?_
    congr 1
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [hξ, hback b ν hbP, hev _ _ (hminus _ ν hbP), hev _ b (h₁₂ _ hbP)]
    rfl
  · have hn : ∀ b : 𝒮.FineBond, (b.source : 𝒮.Point) ∈ tsupport φ → C.mapBond b ≠ c :=
      fun b hb e => hx ⟨b.source, h₀₁ _ (hsupp _ hb), by rw [← e]; rfl⟩
    have hn' : ∀ (ν : Fin 4) (b : 𝒮.FineBond), (b.source : 𝒮.Point) ∈ tsupport φ →
        C.mapBond b ≠ shiftDown ν c := by
      intro ν b hb e
      apply hx
      refine ⟨b.source + unitStep 4 𝒮.side 𝒮.ξ ν, hplus _ ν (hsupp _ hb), ?_⟩
      rw [hEplus _ ν (hsupp _ hb)]
      have : C.mapSite b.source = c.source - unitStep 4 C.setting.side C.setting.ξ ν :=
        congrArg LatticeBond.source e
      rw [this, sub_add_cancel]
    rw [pullBonds_apply_eq_zero C φ _ c hn,
      pushBonds_apply_eq_zero C _ c fun b h e => hx ⟨b.source, hm b h, by rw [← e]; rfl⟩, add_zero]
    symm
    refine Finset.sum_eq_zero fun ν _ => ?_
    rw [pullBonds_apply_eq_zero C φ _ _ (hn' ν), pullBonds_apply_eq_zero C φ _ c hn]
    simp
theorem torusProj_liftedCentre (Q : LevelCube 𝒮 M) : torusProj 4 𝒮.side Q.liftedCentre = Q.centre := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.torusProj_liftedCentre <;> assumption
theorem abs_sub_liftedCentre_le (Q : LevelCube 𝒮 M) (hside : 2 * cubeSide 𝒮 M Q.level ≤ 𝒮.side)
    {p : Fin 4 → ℝ} (hp : p ∈ Q.liftedOpenCube) (μ : Fin 4) :
    |p μ - Q.liftedCentre μ| ≤ ‖torusProj 4 𝒮.side p - Q.centre‖ := by
  have hS := 𝒮.side_pos
  have h1 : |p μ - Q.liftedCentre μ| ≤ |𝒮.side| / 2 := by
    rw [abs_of_pos hS]
    linarith [hp μ]
  have h2 := (AddCircle.norm_coe_eq_abs_iff 𝒮.side hS.ne').2 h1
  rw [← h2]
  have : ((p μ - Q.liftedCentre μ : ℝ) : AddCircle 𝒮.side) = (torusProj 4 𝒮.side p - Q.centre) μ := by
    rw [← torusProj_liftedCentre Q]
    simp [torusProj]
  rw [this]
  exact norm_le_pi_norm _ μ
theorem embed_add_torusProj (Q : LevelCube 𝒮 M) (F : Q.FirstTypeProperties)
    (hside : 2 * cubeSide 𝒮 M Q.level ≤ 𝒮.side) (x : 𝒮.Point) (v : Fin 4 → ℝ) (hx : x ∈ Q.strictPts)
    (hv : ‖x - Q.centre‖ + ‖v‖ < cubeSide 𝒮 M Q.level) :
    Q.system.embed (x + torusProj 4 𝒮.side v) = Q.system.embed x + Q.localProj v := by
  obtain ⟨p, hp, rfl⟩ := F.cover_bijective.surjOn hx
  refine F.embed_add p v hp fun μ => ?_
  have h1 := abs_sub_liftedCentre_le Q hside hp μ
  have h2 := norm_le_pi_norm v μ
  rw [Real.norm_eq_abs] at h2
  have e : (p + v) μ - Q.liftedCentre μ = (p μ - Q.liftedCentre μ) + v μ := by
    simp only [Pi.add_apply]
    ring
  rw [e]
  exact lt_of_le_of_lt (abs_add_le _ _) (by linarith)
theorem coe_mapSite (Q : LevelCube 𝒮 M) (F : Q.FirstTypeProperties) (hξ : Q.system.setting.ξ = 𝒮.ξ)
    (x : 𝒮.FineSite) (hx : (x : 𝒮.Point) ∈ Q.strictPts) :
    ((Q.system.mapSite x : Q.system.setting.FineSite) : Q.system.setting.Point) =
      Q.system.embed x := by
  have h0 : 𝒮.scale 0 = 𝒮.ξ := by simp [RegionSequence.NestedRegions.scale, scaleSpacing]
  have hm : Q.system.embed x ∈ spacingLattice 4 Q.system.setting.side Q.system.setting.ξ := by
    have h2 : Q.system.embed x ∈ Q.system.embed ''
        ((spacingLattice 4 𝒮.side (𝒮.scale 0) : Set 𝒮.Point) ∩ Q.strictPts) :=
      ⟨x, ⟨by rw [h0]; exact x.2, hx⟩, rfl⟩
    rw [F.embed_sites 0 (Or.inl (Nat.zero_le _))] at h2
    rw [hξ.trans h0.symm]
    exact h2.1
  exact Classical.epsilon_spec
    (p := fun y : Q.system.setting.FineSite => (y : Q.system.setting.Point) = Q.system.embed x)
    ⟨⟨_, hm⟩, rfl⟩
theorem mem_bonds_of_partitionFn_ne_zero (Q : LevelCube 𝒮 M)
    (hpos : CubeGeometry.FirstTypePlacement Q)
    (hM : 𝒮.L ^ 5 ≤ M) (b : 𝒮.FineBond) (h : Q.partitionFn (b.source : 𝒮.Point) ≠ 0) :
    b ∈ 𝒮.bonds := by
  have hξ := 𝒮.ξ_pos
  have hM1 : (1 : ℝ) ≤ M := by
    have h13 : 13 ≤ 𝒮.L := 𝒮.thirteen_le_L
    have : 1 ≤ M := le_trans (Nat.one_le_pow _ _ (by omega)) hM
    exact_mod_cast this
  have hx : (b.source : 𝒮.Point) ∈ Q.thicken (5 / 6) := by
    have h₁ : supSetDist {(b.source : 𝒮.Point)} Q.supp ≤
        ENNReal.ofReal (supNorm ((b.source : 𝒮.Point) - (b.source : 𝒮.Point))) :=
      iInf₂_le_of_le _ rfl (iInf₂_le _ (subset_tsupport _ h))
    rw [sub_self, supNorm_eq_norm, norm_zero, ENNReal.ofReal_zero] at h₁
    exact h₁.trans zero_le
  have h0 : 𝒮.scale 0 = 𝒮.ξ := by simp [RegionSequence.NestedRegions.scale, scaleSpacing]
  have hcomp : ∀ y : 𝒮.FineSite, (y : 𝒮.Point) ∉ 𝒮.Ω 0 →
      (y : 𝒮.Point) ∈ 𝒮.cubeComplementAt 0 (𝒮.Ω 0) := by
    intro y hy
    have hy0 : (y : 𝒮.Point) ∈ cubeAt (y : 𝒮.Point) (𝒮.scale 0) := by
      change supNorm ((y : 𝒮.Point) - (y : 𝒮.Point)) ≤ 𝒮.scale 0 / 2
      rw [sub_self, supNorm_eq_norm, norm_zero, h0]
      positivity
    exact ⟨cubeAt (y : 𝒮.Point) (𝒮.scale 0),
      ⟨⟨y, by rw [h0]; exact y.2, rfl⟩, fun hsub => hy (hsub hy0)⟩, hy0⟩
  have hfar : ∀ y : 𝒮.FineSite, ‖(b.source : 𝒮.Point) - (y : 𝒮.Point)‖ ≤ 𝒮.ξ →
      (y : 𝒮.Point) ∈ 𝒮.Ω 0 := by
    intro y hle
    by_contra hy
    have h₁ : supSetDist (Q.thicken (5 / 6)) (𝒮.cubeComplementAt 0 (𝒮.Ω 0)) ≤
        ENNReal.ofReal (supNorm ((b.source : 𝒮.Point) - (y : 𝒮.Point))) :=
      iInf₂_le_of_le _ hx (iInf₂_le _ (hcomp y hy))
    rw [supNorm_eq_norm] at h₁
    have h₂ := lt_of_lt_of_le hpos.away h₁
    have h₃ : ENNReal.ofReal ‖(b.source : 𝒮.Point) - (y : 𝒮.Point)‖ ≤
        ENNReal.ofReal ((M : ℝ) * 𝒮.ξ) :=
      ENNReal.ofReal_le_ofReal (by nlinarith)
    exact absurd h₂ (not_lt.mpr h₃)
  refine 𝒮.mem_bonds_of_mem b (hfar _ ?_) (hfar _ ?_)
  · rw [sub_self, norm_zero]
    exact hξ.le
  · have e : (b.source : 𝒮.Point) - (b.target : 𝒮.Point) =
        -(unitStep 4 𝒮.side 𝒮.ξ b.dir : 𝒮.Point) := by
      change (b.source : 𝒮.Point) - ((b.source : 𝒮.Point) + (unitStep 4 𝒮.side 𝒮.ξ b.dir : 𝒮.Point)) = _
      abel
    rw [e, norm_neg]
    exact norm_unitStep_le _
theorem pullBonds_divOne_firstType (hl : TorusLengthsStatement) (hcell : CellStructure.CellStructureClaim)
    (Q : LevelCube 𝒮 M) (hM : 𝒮.L ^ 5 ≤ M) (hk : ¬Q.IsSecondType) (F : Q.FirstTypeProperties)
    (hside : 2 * cubeSide 𝒮 M Q.level ≤ 𝒮.side)
    (hsupp : ∀ x ∈ tsupport Q.partitionFn, ‖x - Q.centre‖ < 2 / 3 * cubeSide 𝒮 M Q.level)
    (hbond : ∀ b : 𝒮.FineBond, Q.partitionFn (b.source : 𝒮.Point) ≠ 0 → b ∈ 𝒮.bonds)
    (J : 𝒮.Tensor 1) :
    Q.system.pullBonds Q.partitionFn (divOne J) =
      formDiv Q.system (Q.system.pullTensor Q.partitionFn J) +
        pushBonds Q.system (leibnizRemainder (fun x => Q.partitionFn x) J) := by
  obtain ⟨hadm, hset⟩ := F.setting_eq
  have hξ : Q.system.setting.ξ = 𝒮.ξ := by
    rw [hset]
    rfl
  have hall : ∀ 𝒯 : NestedRegions, 𝒯 = Q.torusSetting hadm → ∀ b : 𝒯.FineBond, b ∈ 𝒯.bonds := by
    rintro _ rfl b
    exact mem_univ _
  have hsys : Q.system = Q.firstTypeSystem := if_neg hk
  have hforms : ∀ C : CubeSystem 𝒮, C = Q.firstTypeSystem → C.forms = C.setting.oneForms := by
    rintro _ rfl
    rfl
  have h9 := nine_mul_ξ_lt_cubeSide hM Q.level
  have hξ0 := 𝒮.ξ_pos
  have hNp : ∀ (r : ℝ) (x : 𝒮.FineSite) (ν : Fin 4), ‖(x : 𝒮.Point) - Q.centre‖ < r →
      ‖((x + unitStep 4 𝒮.side 𝒮.ξ ν : 𝒮.FineSite) : 𝒮.Point) - Q.centre‖ < r + 𝒮.ξ := by
    intro r x ν h
    have e : ((x + unitStep 4 𝒮.side 𝒮.ξ ν : 𝒮.FineSite) : 𝒮.Point) - Q.centre =
        ((x : 𝒮.Point) - Q.centre) + (unitStep 4 𝒮.side 𝒮.ξ ν : 𝒮.Point) := by
      rw [AddSubgroup.coe_add]
      abel
    rw [e]
    linarith [norm_add_le ((x : 𝒮.Point) - Q.centre) (unitStep 4 𝒮.side 𝒮.ξ ν : 𝒮.Point),
      norm_unitStep_le (𝒮 := 𝒮) ν]
  have hNm : ∀ (r : ℝ) (x : 𝒮.FineSite) (ν : Fin 4), ‖(x : 𝒮.Point) - Q.centre‖ < r →
      ‖((x - unitStep 4 𝒮.side 𝒮.ξ ν : 𝒮.FineSite) : 𝒮.Point) - Q.centre‖ < r + 𝒮.ξ := by
    intro r x ν h
    have e : ((x - unitStep 4 𝒮.side 𝒮.ξ ν : 𝒮.FineSite) : 𝒮.Point) - Q.centre =
        ((x : 𝒮.Point) - Q.centre) - (unitStep 4 𝒮.side 𝒮.ξ ν : 𝒮.Point) := by
      rw [AddSubgroup.coe_sub]
      abel
    rw [e]
    linarith [norm_sub_le ((x : 𝒮.Point) - Q.centre) (unitStep 4 𝒮.side 𝒮.ξ ν : 𝒮.Point),
      norm_unitStep_le (𝒮 := 𝒮) ν]
  have hin : ∀ x : 𝒮.FineSite,
      ‖(x : 𝒮.Point) - Q.centre‖ < 2 / 3 * cubeSide 𝒮 M Q.level + 3 * 𝒮.ξ →
      (x : 𝒮.Point) ∈ Q.strictPts := by
    intro x h
    change supNorm ((x : 𝒮.Point) - Q.centre) < cubeSide 𝒮 M Q.level
    rw [supNorm_eq_norm]
    linarith
  have hE : ∀ (y : 𝒮.FineSite) (ν : Fin 4),
      ‖(y : 𝒮.Point) - Q.centre‖ < 2 / 3 * cubeSide 𝒮 M Q.level + 2 * 𝒮.ξ →
      Q.system.mapSite (y + unitStep 4 𝒮.side 𝒮.ξ ν) =
        Q.system.mapSite y + unitStep 4 Q.system.setting.side Q.system.setting.ξ ν := by
    intro y ν h
    have hy := hin y (by linarith)
    have hy' := hin (y + unitStep 4 𝒮.side 𝒮.ξ ν) (by linarith [hNp _ y ν h])
    apply Subtype.ext
    rw [AddSubgroup.coe_add, coe_mapSite Q F hξ _ hy', coe_mapSite Q F hξ _ hy]
    change Q.system.embed ((y : 𝒮.Point) + torusProj 4 𝒮.side (Pi.single ν 𝒮.ξ)) =
      Q.system.embed y + torusProj 4 Q.system.setting.side (Pi.single ν Q.system.setting.ξ)
    rw [hξ]
    exact embed_add_torusProj Q F hside _ _ hy
      (by linarith [norm_piSingle_le hξ0.le ν])
  refine pullBonds_divOne_of_mapSite Q.system Q.partitionFn J
    (fun x => ‖(x : 𝒮.Point) - Q.centre‖ < 2 / 3 * cubeSide 𝒮 M Q.level)
    (fun x => ‖(x : 𝒮.Point) - Q.centre‖ < 2 / 3 * cubeSide 𝒮 M Q.level + 𝒮.ξ)
    (fun x => ‖(x : 𝒮.Point) - Q.centre‖ < 2 / 3 * cubeSide 𝒮 M Q.level + 2 * 𝒮.ξ)
    hξ (formDiv_eq_of_forms_eq hl hcell _ (hforms _ hsys) (hall _ hset))
    (fun x hx => hsupp _ hx) (fun x h => by linarith) (fun x h => by linarith)
    (fun x ν h => hNp _ x ν h)
    (fun x ν h => by linarith [hNm _ x ν h])
    ?_ (fun x ν h => hE x ν (by linarith)) ?_ hbond
  · intro x y hx hy e
    have e' := congrArg (fun s : Q.system.setting.FineSite => (s : Q.system.setting.Point)) e
    simp only [coe_mapSite Q F hξ _ (hin x (by linarith)),
      coe_mapSite Q F hξ _ (hin y (by linarith))] at e'
    exact Subtype.ext (F.embed_bijective.injOn (hin x (by linarith)) (hin y (by linarith)) e')
  · intro x ν h
    have e := hE (x - unitStep 4 𝒮.side 𝒮.ξ ν) ν (by linarith [hNm _ x ν h])
    rw [sub_add_cancel] at e
    exact eq_sub_of_add_eq e.symm
theorem pullBonds_divOne_secondType (hl : TorusLengthsStatement)
    (hcell : CellStructure.CellStructureClaim)
    (Q : LevelCube 𝒮 M) (hM : 𝒮.L ^ 5 ≤ M) (hk : Q.IsSecondType)
    (hsupp : ∀ x ∈ tsupport Q.partitionFn, ‖x - Q.centre‖ < 2 / 3 * cubeSide 𝒮 M Q.level)
    (J : 𝒮.Tensor 1) :
    Q.system.pullBonds Q.partitionFn (divOne J) =
      formDiv Q.system (Q.system.pullTensor Q.partitionFn J) +
        pushBonds Q.system (projBonds (leibnizRemainder (fun x => Q.partitionFn x) J)) := by
  have key : ∀ C : CubeSystem 𝒮, C = Q.secondTypeSystem →
      C.pullBonds Q.partitionFn (divOne J) = formDiv C (C.pullTensor Q.partitionFn J) +
        pushBonds C (projBonds (leibnizRemainder (fun x => Q.partitionFn x) J)) := by
    rintro _ rfl
    have hid : ∀ b : 𝒮.FineBond, Q.secondTypeSystem.mapBond b = b := by
      rintro ⟨t, μ⟩
      have : Q.secondTypeSystem.mapSite t = t := by
        apply Subtype.ext
        exact Classical.epsilon_spec (p := fun y : 𝒮.FineSite => (y : 𝒮.Point) = (t : 𝒮.Point))
          ⟨t, rfl⟩
      change (⟨Q.secondTypeSystem.mapSite t, μ⟩ : 𝒮.FineBond) = _
      rw [this]
    have hev : ∀ (A : 𝒮.FineBond → ℝ) (c : 𝒮.FineBond),
        Q.secondTypeSystem.pullBonds Q.partitionFn A c = Q.partitionFn (c.source : 𝒮.Point) * A c :=
      fun A c => pullBonds_apply_of_unique Q.secondTypeSystem Q.partitionFn A c c (hid c)
        fun b _ e => (hid b).symm.trans e
    have A := (hcell 𝒮).2.2.2.1
    have hdiv : ∀ w : 𝒮.Tensor 1, formDiv Q.secondTypeSystem w =
        Q.coreProj fun c => ∑ ν, bwdDiff ν (w (constIdx ν)) c := by
      intro w
      refine adjointValue_eq_of_forall hl Q.coreForms w _ ⟨?_, ?_⟩ ?_
      · intro b hb
        exact indicator_of_notMem (fun h => hb h.1) _
      · intro b hb
        exact indicator_of_notMem (fun h => hb h.2) _
      · intro u hu
        rw [tensorInner_comm, (A.nabla_adjoint w).2 u hu.1, bondInner_comm u]
        simp only [bondInner]
        congr 1
        refine finsum_congr fun b => ?_
        by_cases hb : b ∈ Q.coreBonds
        · simp only [LevelCube.coreProj, indicator_of_mem hb, divOne, projBonds,
            indicator_of_mem hb.1]
        · have hu0 : u b = 0 := by
            by_cases hb' : b ∈ 𝒮.bonds
            · exact hu.2 b fun h => hb ⟨hb', h.1, h.2⟩
            · exact hu.1 b hb'
          rw [hu0, mul_zero, mul_zero]
    have h9 := nine_mul_ξ_lt_cubeSide hM Q.level
    have hξ0 := 𝒮.ξ_pos
    have hzero : ∀ y : 𝒮.FineSite, 2 / 3 * cubeSide 𝒮 M Q.level ≤ ‖(y : 𝒮.Point) - Q.centre‖ →
        Q.partitionFn (y : 𝒮.Point) = 0 := by
      intro y hy
      by_contra h
      exact absurd (hsupp _ (subset_tsupport _ h)) (not_lt.mpr hy)
    refine funext fun c : 𝒮.FineBond => ?_
    have e₂ := congrFun (hdiv (Q.secondTypeSystem.pullTensor Q.partitionFn J)) c
    have e₃ : pushBonds Q.secondTypeSystem
        (projBonds (leibnizRemainder (fun x : 𝒮.FineSite => Q.partitionFn x) J)) c =
          projBonds (leibnizRemainder (fun x : 𝒮.FineSite => Q.partitionFn x) J) c :=
      pushBonds_apply_of_unique Q.secondTypeSystem _ c c (hid c) fun b _ e => (hid b).symm.trans e
    refine (hev _ c).trans (Eq.trans ?_ (congrArg₂ (· + ·) e₂.symm e₃.symm))
    have hw : ∀ ν, Q.secondTypeSystem.pullTensor Q.partitionFn J (constIdx ν) =
        fun c : 𝒮.FineBond => Q.partitionFn (c.source : 𝒮.Point) * J (constIdx ν) c :=
      fun ν => funext fun c => hev _ c
    by_cases hb : c ∈ 𝒮.bonds
    · by_cases hin : c ∈ Q.coreBonds
      · simp only [LevelCube.coreProj, indicator_of_mem hin, divOne, projBonds,
          indicator_of_mem hb, hw]
        refine (mul_sum_bwdDiff_eq (fun x : 𝒮.FineSite => Q.partitionFn x) J c).trans ?_
        rfl
      · have hfar : 4 * cubeSide 𝒮 M Q.level - 𝒮.ξ < ‖(c.source : 𝒮.Point) - Q.centre‖ := by
          by_contra hle
          have hle' := not_lt.mp hle
          apply hin
          refine ⟨hb, ?_, ?_⟩
          · change supNorm ((c.source : 𝒮.Point) - Q.centre) ≤ _
            rw [supNorm_eq_norm]
            push_cast
            linarith
          · change supNorm ((c.target : 𝒮.Point) - Q.centre) ≤ _
            rw [supNorm_eq_norm]
            have e : (c.target : 𝒮.Point) - Q.centre = ((c.source : 𝒮.Point) - Q.centre) +
                (unitStep 4 𝒮.side 𝒮.ξ c.dir : 𝒮.Point) := by
              change ((c.source : 𝒮.Point) + (unitStep 4 𝒮.side 𝒮.ξ c.dir : 𝒮.Point)) - _ = _
              abel
            rw [e]
            push_cast
            linarith [norm_add_le ((c.source : 𝒮.Point) - Q.centre)
              (unitStep 4 𝒮.side 𝒮.ξ c.dir : 𝒮.Point), norm_unitStep_le (𝒮 := 𝒮) c.dir]
        have h₀ := hzero c.source (by linarith)
        have h₁ : ∀ ν, Q.partitionFn ((c.source - unitStep 4 𝒮.side 𝒮.ξ ν : 𝒮.FineSite) : 𝒮.Point) = 0 := by
          intro ν
          apply hzero
          have e : ((c.source : 𝒮.Point) - Q.centre) =
              (((c.source - unitStep 4 𝒮.side 𝒮.ξ ν : 𝒮.FineSite) : 𝒮.Point) - Q.centre) +
                (unitStep 4 𝒮.side 𝒮.ξ ν : 𝒮.Point) := by
            rw [AddSubgroup.coe_sub]
            abel
          have := norm_add_le (((c.source - unitStep 4 𝒮.side 𝒮.ξ ν : 𝒮.FineSite) : 𝒮.Point) - Q.centre)
            (unitStep 4 𝒮.side 𝒮.ξ ν : 𝒮.Point)
          rw [← e] at this
          linarith [norm_unitStep_le (𝒮 := 𝒮) ν]
        have hr := leibnizRemainder_eq_zero (fun x : 𝒮.FineSite => Q.partitionFn x) J c h₀ h₁
        simp only [LevelCube.coreProj, indicator_of_notMem hin, projBonds,
          indicator_of_mem hb, hr, h₀, zero_mul, add_zero]
    · have hin : c ∉ Q.coreBonds := fun h => hb h.1
      simp only [LevelCube.coreProj, indicator_of_notMem hin, divOne, projBonds,
        indicator_of_notMem hb, mul_zero, add_zero]
  exact key _ (if_pos hk)
theorem claim_holds (hc : cubeFunctionsAndMaps) (hg : CubeGeometry.GeometryStatement)
    (hcell : CellStructure.CellStructureClaim) (hl : TorusLengthsStatement) : Claim := by
  intro K m M R₁ 𝒮 hs hM Q hQ J
  obtain ⟨hblock, -, -, hsf, -, hfk, -⟩ := hc.2 𝒮 K m M R₁ hs
  have hsupp : ∀ x ∈ tsupport Q.partitionFn, ‖x - Q.centre‖ < 2 / 3 * cubeSide 𝒮 M Q.level := by
    intro x hx
    have := ((hsf Q).support_subset hx).1.1
    rw [mem_ofPred_eq, supNorm_eq_norm] at this
    exact this
  unfold pushedRemainder
  by_cases hk : Q.IsSecondType
  · rw [if_pos hk]
    exact pullBonds_divOne_secondType hl hcell Q hM hk hsupp J
  · rw [if_neg hk]
    have hfirst : Q.IsFirstType := ⟨hQ, hk⟩
    have hpos := (hg.2 K m M R₁ 𝒮 hs hM).positions.first_kind Q hfirst
    exact pullBonds_divOne_firstType hl hcell Q hM hk (hfk Q hfirst)
      (hblock Q.level Q.level_le).side_ge hsupp
      (fun b h => mem_bonds_of_partitionFn_ne_zero Q hpos hM b h) J
end CubeDivergence
end YangMills.Construction
