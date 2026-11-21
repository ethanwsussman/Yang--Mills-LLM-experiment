import YangMills.Construction.ChessboardTori.GroupOnTheTorusAsAQuotient
import YangMills.Construction.MirrorGridsOfEverySide.SimilaritiesOfTheLatticesProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.MirrorGridsAllSides.ScalingTorusCells
open ChessboardTori (ReflectionGrid orientationSign)
variable {D : GridSetup} (S : ScalingMap D)
theorem image_torusSide :
    PeriodicLattice.torusSide S.image.L S.image.m = S.scale * PeriodicLattice.torusSide D.L D.m := by apply _root_.YangMills.SharedProofs.p15016 <;> assumption
theorem gridImage_cellSide (g : ReflectionGrid D) : (S.gridImage g).cellSide = S.scale * g.cellSide := by apply _root_.YangMills.Construction.MirrorGridsAllSides.ScalingProof.cellSide_gridImage <;> assumption
theorem gridImage_cellsAcross (g : ReflectionGrid D) :
    (S.gridImage g).cellsAcross = g.cellsAcross := by
  have hne := S.scale_pos.ne'
  change PeriodicLattice.torusSide S.image.L S.image.m / (S.gridImage g).cellSide =
    PeriodicLattice.torusSide D.L D.m / g.cellSide
  rw [image_torusSide, gridImage_cellSide, mul_div_mul_left _ _ hne]
variable {S}
theorem torusInv_proj (hm : S.IsTorusLift S.torusMap) (hb : Function.Bijective S.torusMap)
    (y : InfiniteLattice.AmbientSpace) :
    S.torusInv (S.image.proj y) = D.proj (S.toPerm⁻¹ y) := by
  have hy : S.torusMap (D.proj (S.toPerm⁻¹ y)) = S.image.proj y := by
    have e1 : S.torusMap (D.proj (S.toPerm⁻¹ y)) =
        S.image.proj (S.toFun (S.toPerm⁻¹ y)) := congrFun hm (S.toPerm⁻¹ y)
    have e2 : S.toFun (S.toPerm⁻¹ y) = y := S.toPerm.apply_symm_apply y
    rw [e1, e2]
  rw [← hy]
  exact Function.leftInverse_invFun hb.1 _
theorem conjTorus_lifts (hm : S.IsTorusLift S.torusMap) (hb : Function.Bijective S.torusMap)
    {f : Equiv.Perm InfiniteLattice.AmbientSpace} {f' : D.Torus → D.Torus}
    (hf : D.proj ∘ f = f' ∘ D.proj) :
    S.image.proj ∘ (S.toPerm * f * S.toPerm⁻¹ : Equiv.Perm InfiniteLattice.AmbientSpace) =
      S.conjTorus f' ∘ S.image.proj := by
  funext y
  have e1 := congrFun hm (f (S.toPerm⁻¹ y))
  have e2 := congrFun hf (S.toPerm⁻¹ y)
  simp only [Function.comp] at e1 e2
  change S.image.proj (S.toFun (f (S.toPerm⁻¹ y))) =
    S.torusMap (f' (S.torusInv (S.image.proj y)))
  rw [torusInv_proj hm hb, ← e2, e1]
theorem lifts_of_conjTorus_lifts (hm : S.IsTorusLift S.torusMap)
    (hb : Function.Bijective S.torusMap)
    {f : Equiv.Perm InfiniteLattice.AmbientSpace} {f' : D.Torus → D.Torus}
    (hf : S.image.proj ∘ (S.toPerm * f * S.toPerm⁻¹ : Equiv.Perm InfiniteLattice.AmbientSpace) =
      S.conjTorus f' ∘ S.image.proj) :
    D.proj ∘ f = f' ∘ D.proj := by
  funext x
  apply hb.1
  have e1 := congrFun hm (f x)
  have e2 := congrFun hm x
  have e3 := congrFun hf (S.toFun x)
  simp only [Function.comp] at e1 e2 e3
  have e4 : S.toPerm⁻¹ (S.toFun x) = x := S.toPerm.symm_apply_apply x
  have e5 : (S.toPerm * f * S.toPerm⁻¹ : Equiv.Perm InfiniteLattice.AmbientSpace) (S.toFun x) =
      S.toFun (f x) := by
    change S.toFun (f (S.toPerm⁻¹ (S.toFun x))) = _
    rw [e4]
  rw [e5] at e3
  change S.torusMap (D.proj (f x)) = S.torusMap (f' (D.proj x))
  rw [e1, e3]
  change S.torusMap (f' (S.torusInv (S.image.proj (S.toFun x)))) = _
  rw [torusInv_proj hm hb, e4]
theorem conjTorus_conj_inv (hb : Function.Bijective S.torusMap) (f : S.image.Torus → S.image.Torus) :
    S.conjTorus (S.torusInv ∘ f ∘ S.torusMap) = f := by
  funext y
  have hr : ∀ z, S.torusMap (S.torusInv z) = z := Function.rightInverse_invFun hb.2
  change S.torusMap (S.torusInv (f (S.torusMap (S.torusInv y)))) = f y
  rw [hr, hr]
theorem conjTorus_injective (hb : Function.Bijective S.torusMap) :
    Function.Injective (S.conjTorus) := by
  intro f f₂ hff
  funext x
  have hl : ∀ z, S.torusInv (S.torusMap z) = z := Function.leftInverse_invFun hb.1
  have hx := congrFun hff (S.torusMap x)
  change S.torusMap (f (S.torusInv (S.torusMap x))) =
    S.torusMap (f₂ (S.torusInv (S.torusMap x))) at hx
  rw [hl] at hx
  exact hb.1 hx
theorem conjTorus_comp (hb : Function.Bijective S.torusMap) (f f₂ : D.Torus → D.Torus) :
    S.conjTorus (f ∘ f₂) = S.conjTorus f ∘ S.conjTorus f₂ := by
  funext y
  have hl : ∀ z, S.torusInv (S.torusMap z) = z := Function.leftInverse_invFun hb.1
  change S.torusMap (f (f₂ (S.torusInv y))) =
    S.torusMap (f (S.torusInv (S.torusMap (f₂ (S.torusInv y)))))
  rw [hl]
theorem image_torusCellSet (hm : S.IsTorusLift S.torusMap) {g : ReflectionGrid D}
    (hc : ∀ k, S.toFun '' g.cell k = (S.gridImage g).cell k) :
    (fun C : Set D.Torus => S.torusMap '' C) '' g.torusCellSet = (S.gridImage g).torusCellSet := by
  have key : ∀ k, S.torusMap '' (D.proj '' g.cell k) =
      S.image.proj '' (S.gridImage g).cell k := by
    intro k
    rw [← hc k, image_image, image_image]
    exact image_congr fun x _ => congrFun hm x
  ext C
  constructor
  · rintro ⟨_, ⟨_, ⟨k, rfl⟩, rfl⟩, rfl⟩
    exact ⟨_, ⟨k, rfl⟩, (key k).symm⟩
  · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
    exact ⟨_, ⟨_, ⟨k, rfl⟩, rfl⟩, key k⟩
theorem ln (hT : ScalingPreservesTorus)
    (hC : ScalingPreservesCellsAndGroup)
    (hG : ChessboardTori.TorusReflectionGroup.Statement) : ScalingPreservesCellsAndGroupTorus := by
  intro D S g hs h2
  obtain ⟨-, hm, hb, -⟩ := hT D S
  obtain ⟨hcell, -, -, -, φ, hφ⟩ := hC D S g hs
  have hsign : ∀ u v : g.reflectionGroup, ∀ f' : D.Torus → D.Torus,
      D.proj ∘ u.1 = f' ∘ D.proj → D.proj ∘ v.1 = f' ∘ D.proj →
        orientationSign u.1 = orientationSign v.1 := by
    obtain ⟨-, -, -, hh, -⟩ := hG D g h2
    exact fun u v f' hu hv => hh u.1 u.2 v.1 v.2 f' hu hv
  have hmaps : ∀ f' ∈ g.inducedTorusMaps, S.conjTorus f' ∈ (S.gridImage g).inducedTorusMaps := by
    rintro f' ⟨f, hf, hind⟩
    refine ⟨(φ ⟨f, hf⟩).1, (φ ⟨f, hf⟩).2, ?_⟩
    rw [(hφ ⟨f, hf⟩).1]
    exact conjTorus_lifts hm hb hind
  refine ⟨?_, gridImage_cellsAcross S g, ?_, image_torusCellSet hm hcell, ⟨hmaps, ?_, ?_⟩,
    fun f _ f₂ _ => conjTorus_comp hb f f₂, ?_⟩
  · rw [← mul_assoc, mul_comm 2 S.scale, mul_assoc]
    exact mul_le_mul_of_nonneg_left h2 S.scale_pos.le
  · simp only [ReflectionGrid.cellNumber, gridImage_cellsAcross S g]
  · exact (conjTorus_injective hb).injOn
  · rintro f₂ ⟨ρ, hρ, hind⟩
    obtain ⟨f, hf⟩ := φ.surjective ⟨ρ, hρ⟩
    have hf1 : (S.toPerm * f.1 * S.toPerm⁻¹ : Equiv.Perm InfiniteLattice.AmbientSpace) = ρ := by
      rw [← (hφ f).1, hf]
    have hback := conjTorus_conj_inv hb f₂
    refine ⟨S.torusInv ∘ f₂ ∘ S.torusMap, ⟨f.1, f.2, ?_⟩, hback⟩
    apply lifts_of_conjTorus_lifts hm hb
    rw [hf1, hback]
    exact hind
  · intro f' hf'
    have hfG := hf'
    obtain ⟨f, hf, hind⟩ := hfG
    refine (S.gridImage g).torusSign_eq_of_hasTorusParity (hmaps f' hf') ?_
    intro ρ hρ
    obtain ⟨f₁, hf₁⟩ := φ.surjective ρ
    have hf1 : (S.toPerm * f₁.1 * S.toPerm⁻¹ : Equiv.Perm InfiniteLattice.AmbientSpace) = ρ.1 := by
      rw [← (hφ f₁).1, hf₁]
    have hind₁ : D.proj ∘ f₁.1 = f' ∘ D.proj := by
      apply lifts_of_conjTorus_lifts hm hb
      rw [hf1]
      exact hρ
    have hspec : D.proj ∘ (g.inducingElement f').1 = f' ∘ D.proj :=
      Classical.epsilon_spec (p := fun u : g.reflectionGroup => D.proj ∘ u.1 = f' ∘ D.proj)
        ⟨⟨f, hf⟩, hind⟩
    rw [← hf₁, (hφ f₁).2]
    exact hsign f₁ (g.inducingElement f') f' hind₁ hspec
end YangMills.Construction.MirrorGridsAllSides.ScalingTorusCells
end
