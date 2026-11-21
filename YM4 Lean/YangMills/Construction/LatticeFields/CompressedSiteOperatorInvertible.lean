import YangMills.Construction.LatticeFields.BlockMomentInverseProof
import YangMills.Construction.LatticeFields.CompressedLaplacianInverseProof
import YangMills.Construction.LatticeFields.CompressedSiteOperator
import YangMills.Construction.LatticeFields.ProjGradDecayProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFields.CompressedSiteOperator
theorem finite_latticeSite_torus {d : ℕ} (N : ℕ) [NeZero N] (ℓ : Fin d → ℕ) (hℓ : ∀ μ, 1 ≤ ℓ μ) :
    Finite (LatticeSite N (LatticeShape.torus ℓ hℓ)) := by apply _root_.YangMills.Construction.LatticeFields.WeightConjProjComplProof.finite_torusSites <;> assumption
section Inner
variable {d N : ℕ} {κ : LatticeShape d} {I : Type}
theorem fieldInner_comm (F G : LatticeField N κ I) : fieldInner F G = fieldInner G F :=
  tsum_congr fun p => by ring
theorem fieldInner_self_nonneg (F : LatticeField N κ I) : 0 ≤ fieldInner F F := by apply _root_.YangMills.Construction.LatticeFields.CompressedGreenDecayProof.fieldInner_self_nonneg <;> assumption
theorem fieldNorm_sq (F : LatticeField N κ I) : fieldNorm F ^ 2 = fieldInner F F := by apply _root_.YangMills.Construction.LatticeFields.CompressedGreenDecayProof.fieldNorm_sq_eq <;> assumption
theorem fieldNorm_nonneg (F : LatticeField N κ I) : 0 ≤ fieldNorm F := Real.sqrt_nonneg _
theorem fieldInner_restrictSites (Ω : Set (LatticeSite N κ)) (F G : LatticeField N κ I) :
    fieldInner F (restrictSites Ω G) = fieldInner (restrictSites Ω F) G :=
  tsum_congr fun p => by simp only [restrictSites, mulBase]; ring
theorem fieldInner_smul_right (t : ℝ) (F G : LatticeField N κ I) :
    fieldInner F (t • G) = t * fieldInner F G := by apply _root_.YangMills.Construction.LatticeFields.CompressedGreenDecayProof.fieldInner_smul <;> assumption
variable [Finite (LatticeSite N κ)] [Finite I]
theorem fieldSquareSummable_of_finite (F : LatticeField N κ I) : FieldSquareSummable F :=
  Summable.of_finite
theorem fieldInner_add_right (F G H : LatticeField N κ I) :
    fieldInner F (G + H) = fieldInner F G + fieldInner F H := by apply _root_.YangMills.Construction.LatticeFields.CompressedGreenDecayProof.fieldInner_add <;> assumption
theorem fieldInner_sub_right (F G H : LatticeField N κ I) :
    fieldInner F (G - H) = fieldInner F G - fieldInner F H := by apply _root_.YangMills.Construction.LatticeFields.CompressedGreenDecayProof.fieldInner_sub <;> assumption
theorem eq_zero_of_fieldInner_self [NeZero N] (F : LatticeField N κ I) (h : fieldInner F F = 0) :
    F = 0 := by apply _root_.YangMills.Construction.LatticeFields.CompressedGreenProof.eq_zero_of_fieldInner_self <;> assumption
end Inner
section Linear
variable {d N : ℕ} {κ : LatticeShape d}
theorem tensorLaplacian_add (F G : ScalarField N κ) :
    tensorLaplacian (F + G) = tensorLaplacian F + tensorLaplacian G := by apply _root_.YangMills.Construction.LatticeFields.BlockMomentInverse.tensorLaplacian_add <;> assumption
theorem tensorLaplacian_smul (c : ℝ) (F : ScalarField N κ) :
    tensorLaplacian (c • F) = c • tensorLaplacian F := by apply _root_.YangMills.Construction.LatticeFields.BlockMomentInverse.tensorLaplacian_smul <;> assumption
theorem siteBlockAvg_add [Finite (LatticeSite N κ)] (f g : ScalarField N κ) :
    siteBlockAvg (f + g) = siteBlockAvg f + siteBlockAvg g := by apply _root_.YangMills.Construction.LatticeFields.BlockMomentInverse.siteBlockAvg_add <;> assumption
theorem siteBlockAvg_smul [Finite (LatticeSite N κ)] (c : ℝ) (f : ScalarField N κ) :
    siteBlockAvg (c • f) = c • siteBlockAvg f := by apply _root_.YangMills.Construction.LatticeFields.BlockMomentInverse.siteBlockAvg_smul <;> assumption
theorem siteBlockAvgAdj_add [Finite (LatticeSite 1 κ)] (ω ω' : ScalarField 1 κ) :
    (siteBlockAvgAdj (ω + ω') : ScalarField N κ) =
      siteBlockAvgAdj ω + siteBlockAvgAdj ω' := by
  funext x i
  simp only [siteBlockAvgAdj, fieldAdjointAt, Pi.add_apply, fieldInner_add_right, mul_add]
theorem siteBlockAvgAdj_smul [Finite (LatticeSite 1 κ)] (c : ℝ) (ω : ScalarField 1 κ) :
    (siteBlockAvgAdj (c • ω) : ScalarField N κ) = c • siteBlockAvgAdj ω := by
  funext x i
  simp only [siteBlockAvgAdj, fieldAdjointAt, Pi.smul_apply, smul_eq_mul,
    fieldInner_smul_right]
  ring
theorem restrictSites_add (Ω : Set (LatticeSite N κ)) (f g : ScalarField N κ) :
    restrictSites Ω (f + g) = restrictSites Ω f + restrictSites Ω g := by apply _root_.YangMills.Construction.LatticeFields.BlockMomentInverse.restrictSites_add <;> assumption
theorem restrictSites_smul (Ω : Set (LatticeSite N κ)) (c : ℝ) (f : ScalarField N κ) :
    restrictSites Ω (c • f) = c • restrictSites Ω f := by apply _root_.YangMills.Construction.LatticeFields.BlockMomentInverse.restrictSites_smul <;> assumption
theorem restrictSites_of_vanishesOutside {Ω : Set (LatticeSite N κ)} {f : ScalarField N κ}
    (hf : VanishesOutside Ω f) : restrictSites Ω f = f := by
  funext x i
  have hi : i = scalarIndex := Subsingleton.elim _ _
  subst hi
  by_cases hx : x ∈ Ω
  · simp [restrictSites, mulBase, hx]
  · have h0 : f x scalarIndex = 0 := hf x hx
    simp [restrictSites, mulBase, hx, h0]
theorem vanishesOutside_restrictSites (Ω : Set (LatticeSite N κ)) (f : ScalarField N κ) :
    VanishesOutside Ω (restrictSites Ω f) := by
  intro x hx
  simp [ScalarField.eval, restrictSites, mulBase, hx]
theorem tensorLaplacian_eq_latticeDiv_latticeGrad (f : ScalarField N κ) :
    tensorLaplacian f = latticeDiv (latticeGrad f) := by apply _root_.YangMills.Construction.LatticeFields.ProjGradDecayProof.tensorLaplacian_eq_div_grad <;> assumption
variable [Finite (LatticeSite N κ)] [Finite (LatticeSite 1 κ)]
def compressedSiteOpLinear (a : ℝ) (Ω : Set (LatticeSite N κ)) :
    ScalarField N κ →ₗ[ℝ] ScalarField N κ where
  toFun := compressedSiteOp a Ω
  map_add' f g := by
    simp only [compressedSiteOp, restrictSites_add, tensorLaplacian_add, siteBlockAvg_add,
      siteBlockAvgAdj_add, smul_add]
    abel_nf
  map_smul' c f := by
    simp only [compressedSiteOp, restrictSites_smul, tensorLaplacian_smul, siteBlockAvg_smul,
      siteBlockAvgAdj_smul, restrictSites_add, RingHom.id_apply, smul_add]
    rw [smul_comm a c]
def vanishingSubmodule (Ω : Set (LatticeSite N κ)) : Submodule ℝ (ScalarField N κ) where
  carrier := {f | VanishesOutside Ω f}
  add_mem' := by
    intro f g hf hg x hx
    have h1 : f x scalarIndex = 0 := hf x hx
    have h2 : g x scalarIndex = 0 := hg x hx
    simp [ScalarField.eval, h1, h2]
  zero_mem' := fun _ _ => rfl
  smul_mem' := by
    intro c f hf x hx
    have h1 : f x scalarIndex = 0 := hf x hx
    simp [ScalarField.eval, h1]
end Linear
section Form
variable {d N : ℕ} {κ : LatticeShape d}
structure OperatorHyps (N : ℕ) (κ : LatticeShape d) : Prop where
  grad_adjoint : ∀ (f : ScalarField N κ) (B : LatticeOneForm N κ),
    fieldInner (latticeGrad f) B = fieldInner f (latticeDiv B)
  blockAvg_adjoint : ∀ (f : ScalarField N κ) (ω : ScalarField 1 κ),
    fieldInner (siteBlockAvg f) ω = fieldInner f (siteBlockAvgAdj ω)
  blockAvgAdj_norm_le : ∀ ω : ScalarField 1 κ,
    fieldNorm (siteBlockAvgAdj ω : ScalarField N κ) ≤ fieldNorm ω
  isOrthProj_blockProj : ∀ f : ScalarField N κ,
    IsOrthProj (blockConstantFields N κ) f (siteBlockProj f)
  norm_sub_blockProj_sq_le : ∀ f : ScalarField N κ,
    fieldNorm (f - siteBlockProj f) ^ 2 ≤ (d : ℝ) / 2 * fieldNorm (latticeGrad f) ^ 2
variable [Finite (LatticeSite N κ)]
theorem fieldInner_compressedSiteOp (H : OperatorHyps N κ) (a : ℝ) {Ω : Set (LatticeSite N κ)}
    {u v : ScalarField N κ} (hu : VanishesOutside Ω u) (hv : VanishesOutside Ω v) :
    fieldInner v (compressedSiteOp a Ω u) =
      fieldInner (latticeGrad v) (latticeGrad u) + a * fieldInner (siteBlockAvg v) (siteBlockAvg u) := by
  unfold compressedSiteOp
  rw [fieldInner_restrictSites, restrictSites_of_vanishesOutside hv, restrictSites_of_vanishesOutside hu,
    fieldInner_add_right, fieldInner_smul_right, tensorLaplacian_eq_latticeDiv_latticeGrad,
    H.grad_adjoint, H.blockAvg_adjoint]
theorem min_mul_fieldNorm_sq_le_energy (H : OperatorHyps N κ) (hd : 0 < d) {a : ℝ} (ha : 0 < a)
    (v : ScalarField N κ) :
    min (2 / (d : ℝ)) a * fieldNorm v ^ 2 ≤
      fieldInner (latticeGrad v) (latticeGrad v) + a * fieldInner (siteBlockAvg v) (siteBlockAvg v) := by
  set g := siteBlockProj v with hg
  have horth : fieldInner (v - g) g = 0 :=
    (H.isOrthProj_blockProj v).2 g (H.isOrthProj_blockProj v).1
  have hsplit : fieldInner v v = fieldInner (v - g) (v - g) + fieldInner g g := by
    have h1 : fieldInner g (v - g) = 0 := by rw [fieldInner_comm]; exact horth
    rw [fieldInner_sub_right] at h1
    rw [fieldInner_sub_right, fieldInner_comm (v - g) v, fieldInner_comm (v - g) g,
      fieldInner_sub_right, fieldInner_sub_right, fieldInner_comm v g]
    linarith
  have hadj : fieldNorm g ^ 2 ≤ fieldNorm (siteBlockAvg v) ^ 2 :=
    pow_le_pow_left₀ (fieldNorm_nonneg _) (H.blockAvgAdj_norm_le _) 2
  have hoff := H.norm_sub_blockProj_sq_le v
  rw [← hg] at hoff
  rw [fieldNorm_sq v, hsplit, ← fieldNorm_sq (latticeGrad v), ← fieldNorm_sq (siteBlockAvg v),
    ← fieldNorm_sq (v - g), ← fieldNorm_sq g]
  have hm0 : 0 < min (2 / (d : ℝ)) a := lt_min (by positivity) ha
  have hm1 : min (2 / (d : ℝ)) a ≤ 2 / d := min_le_left _ _
  have hm2 : min (2 / (d : ℝ)) a ≤ a := min_le_right _ _
  have hB : 0 ≤ fieldNorm (siteBlockAvg v) ^ 2 := sq_nonneg _
  have e1 : min (2 / (d : ℝ)) a * fieldNorm (v - g) ^ 2 ≤ fieldNorm (latticeGrad v) ^ 2 := by
    calc min (2 / (d : ℝ)) a * fieldNorm (v - g) ^ 2
        ≤ min (2 / (d : ℝ)) a * ((d : ℝ) / 2 * fieldNorm (latticeGrad v) ^ 2) :=
          mul_le_mul_of_nonneg_left hoff hm0.le
      _ ≤ 2 / d * ((d : ℝ) / 2 * fieldNorm (latticeGrad v) ^ 2) :=
          mul_le_mul_of_nonneg_right hm1 (by positivity)
      _ = fieldNorm (latticeGrad v) ^ 2 := by field_simp
  have e2 : min (2 / (d : ℝ)) a * fieldNorm g ^ 2 ≤ a * fieldNorm (siteBlockAvg v) ^ 2 :=
    (mul_le_mul_of_nonneg_left hadj hm0.le).trans (mul_le_mul_of_nonneg_right hm2 hB)
  rw [mul_add]
  exact add_le_add e1 e2
theorem compressedSiteOp_symm_coercive_bijective [NeZero N] [Finite (LatticeSite 1 κ)]
    (H : OperatorHyps N κ) (hd : 0 < d) {a : ℝ} (ha : 0 < a) (Ω : Set (LatticeSite N κ)) :
    (∀ u v : ScalarField N κ, VanishesOutside Ω u → VanishesOutside Ω v →
        fieldInner v (compressedSiteOp a Ω u) = fieldInner (compressedSiteOp a Ω v) u) ∧
      (∀ v : ScalarField N κ, VanishesOutside Ω v →
        min (2 / (d : ℝ)) a * fieldNorm v ^ 2 ≤ fieldInner v (compressedSiteOp a Ω v)) ∧
      (∀ f : ScalarField N κ, VanishesOutside Ω f →
        ∃! u : ScalarField N κ, VanishesOutside Ω u ∧ compressedSiteOp a Ω u = f) := by
  have hlower : ∀ v : ScalarField N κ, VanishesOutside Ω v →
      min (2 / (d : ℝ)) a * fieldNorm v ^ 2 ≤ fieldInner v (compressedSiteOp a Ω v) :=
    fun v hv => by
      rw [fieldInner_compressedSiteOp H a hv hv]
      exact min_mul_fieldNorm_sq_le_energy H hd ha v
  have hm0 : 0 < min (2 / (d : ℝ)) a := lt_min (by positivity) ha
  have hzero : ∀ v : ScalarField N κ, VanishesOutside Ω v → compressedSiteOp a Ω v = 0 →
      v = 0 := fun v hv h0 => by
    have h1 := hlower v hv
    have h2 : fieldInner v (0 : ScalarField N κ) = 0 := by simp [fieldInner]
    rw [h0, h2, fieldNorm_sq] at h1
    have h3 : fieldInner v v ≤ 0 := nonpos_of_mul_nonpos_right h1 hm0
    exact eq_zero_of_fieldInner_self v (le_antisymm h3 (fieldInner_self_nonneg v))
  refine ⟨fun u v hu hv => ?_, hlower, fun f hf => ?_⟩
  · rw [fieldInner_comm (compressedSiteOp a Ω v) u, fieldInner_compressedSiteOp H a hu hv,
      fieldInner_compressedSiteOp H a hv hu, fieldInner_comm (latticeGrad v),
      fieldInner_comm (siteBlockAvg v)]
  · let T : vanishingSubmodule Ω →ₗ[ℝ] vanishingSubmodule Ω :=
      (compressedSiteOpLinear a Ω).restrict fun u _ => vanishesOutside_restrictSites Ω _
    have hinj : Function.Injective T := by
      rw [injective_iff_map_eq_zero]
      intro u hu
      exact Subtype.ext (hzero u.1 u.2 (congrArg Subtype.val hu))
    obtain ⟨u, hu⟩ := (LinearMap.injective_iff_surjective.mp hinj) ⟨f, hf⟩
    have hTu : compressedSiteOp a Ω u.1 = f := congrArg Subtype.val hu
    refine ⟨u.1, ⟨u.2, hTu⟩, fun w hw => ?_⟩
    have hsub : VanishesOutside Ω (w - u.1) := (vanishingSubmodule Ω).sub_mem hw.1 u.2
    have hTw : compressedSiteOp a Ω (w - u.1) = 0 := by
      have := (compressedSiteOpLinear a Ω).map_sub w u.1
      change compressedSiteOp a Ω (w - u.1) =
        compressedSiteOp a Ω w - compressedSiteOp a Ω u.1 at this
      rw [this, hw.2, hTu, sub_self]
    exact sub_eq_zero.mp (hzero _ hsub hTw)
end Form
theorem claim_holds (hAverages : BlockAveragingBounds)
    (hAdjoint : BlockAvgAdjointFacts)
    (hLaws : MetricAdjointCubes.BasicLatticeFacts) : Claim := by
  intro d L k hd hL ℓ hℓ a ha Ω
  have hN : NeZero (L ^ k) := ⟨pow_ne_zero _ (by omega)⟩
  have hfin := finite_latticeSite_torus (L ^ k) ℓ hℓ
  have hfin1 := finite_latticeSite_torus 1 ℓ hℓ
  obtain ⟨⟨-, -, hQ', hP, -⟩, -, -, hoff, -⟩ := hAverages d L k hd hL ℓ hℓ
  have hO := (hLaws d L k (L ^ k) hd hL rfl (LatticeShape.torus ℓ hℓ)).2.1
  have hA := hAdjoint d (L ^ k) (LatticeShape.torus ℓ hℓ)
  refine compressedSiteOp_symm_coercive_bijective
    { grad_adjoint := fun f B =>
        hO.grad_adjoint f B (fieldSquareSummable_of_finite f) (fieldSquareSummable_of_finite B)
      blockAvg_adjoint := fun f ω =>
        hA.2.2.1 f ω (fieldSquareSummable_of_finite f) (fieldSquareSummable_of_finite ω)
      blockAvgAdj_norm_le := fun ω => by
        have h := hQ'.1.2 ω
        rwa [one_mul] at h
      isOrthProj_blockProj := hP
      norm_sub_blockProj_sq_le := hoff } (by omega) ha Ω
end YangMills.Construction.LatticeFields.CompressedSiteOperator
