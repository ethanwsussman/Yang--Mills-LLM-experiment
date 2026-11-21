import YangMills.Construction.ChessboardTori.GroupCoordinateByCoordinate
import YangMills.Construction.MirrorGridsOfEverySide.SimilarityCarriesCellFunctions
import YangMills.Construction.MirrorGridsOfEverySide.SimilarityCarriesCellsAndGroup
import YangMills.Construction.MirrorGridsOfEverySide.SimilarityCarriesTheInfiniteLattice
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.MirrorGridsAllSides
open ChessboardTori (ReflectionGrid orientationSign)
namespace ScalingCellObservables
variable {D : GridSetup} (S : ScalingMap D)
theorem injective_toFun : Function.Injective S.toFun := S.toPerm.injective
theorem linkMap_mem_interiorLinks_iff {C : Set InfiniteLattice.AmbientSpace}
    (hint : S.toFun '' interior C = interior (S.toFun '' C)) (e : D.Link) :
    e ∈ ReflectionGrid.interiorLinks (D := D) C ↔
      S.linkMap e ∈ ReflectionGrid.interiorLinks (D := S.image) (S.toFun '' C) := by
  have key : ∀ x : InfiniteLattice.AmbientSpace,
      x ∈ interior C ↔ S.toFun x ∈ interior (S.toFun '' C) := fun x => by
    rw [← hint, (injective_toFun S).mem_set_image]
  exact and_congr (key _) (key _)
theorem comp_pullback_mem_cellObservables {C : Set InfiniteLattice.AmbientSpace}
    (hint : S.toFun '' interior C = interior (S.toFun '' C)) {F : D.GaugeField → ℂ}
    (hF : F ∈ ReflectionGrid.cellObservables (D := D) C) :
    F ∘ S.pullback ∈ ReflectionGrid.cellObservables (D := S.image) (S.toFun '' C) := by
  obtain ⟨f, hf, ⟨c, hc⟩, rfl⟩ := hF
  refine ⟨fun u => f fun e => u ⟨S.linkMap e.1, (linkMap_mem_interiorLinks_iff S hint e.1).1 e.2⟩,
    hf.comp (measurable_pi_lambda _ fun e => measurable_pi_apply _), ⟨c, fun u => hc _⟩, ?_⟩
  rfl
theorem exists_comp_pullback_eq {C : Set InfiniteLattice.AmbientSpace}
    (hint : S.toFun '' interior C = interior (S.toFun '' C))
    (hbij : Function.Bijective S.linkMap) {G : S.image.GaugeField → ℂ}
    (hG : G ∈ ReflectionGrid.cellObservables (D := S.image) (S.toFun '' C)) :
    ∃ F ∈ ReflectionGrid.cellObservables (D := D) C, F ∘ S.pullback = G := by
  obtain ⟨g, hg, ⟨c, hc⟩, rfl⟩ := hG
  let σ : D.Link ≃ S.image.Link := Equiv.ofBijective S.linkMap hbij
  have hσ : ∀ e', S.linkMap (σ.symm e') = e' := fun e' => σ.apply_symm_apply e'
  have hmem : ∀ e' : ReflectionGrid.interiorLinks (D := S.image) (S.toFun '' C),
      σ.symm e'.1 ∈ ReflectionGrid.interiorLinks (D := D) C := fun e' =>
    (linkMap_mem_interiorLinks_iff S hint _).2 (by rw [hσ]; exact e'.2)
  refine ⟨(fun u => g fun e' => u ⟨σ.symm e'.1, hmem e'⟩) ∘ ReflectionGrid.restrictField C,
    ⟨_, hg.comp (measurable_pi_lambda _ fun e => measurable_pi_apply _),
      ⟨c, fun u => hc _⟩, rfl⟩, ?_⟩
  funext V
  refine congrArg g (funext fun e' => ?_)
  change V (S.linkMap (σ.symm e'.1)) = V e'.1
  rw [hσ]
theorem pullbackField_pullback (r : D.LatticeSym) (r' : S.image.LatticeSym)
    (h : ∀ x, r'.toFun (S.toFun x) = S.toFun (r.toFun x)) (V : S.image.GaugeField) :
    r.pullbackField (S.pullback V) = S.pullback (r'.pullbackField V) := by
  apply Subtype.ext
  funext e
  have he : S.linkMap (r.linkMap e) = r'.linkMap (S.linkMap e) :=
    InfiniteLattice.Link.ext (Subtype.ext (h _).symm) (Subtype.ext (h _).symm)
  exact congrArg V.1 he
end ScalingCellObservables
theorem scalingPreservesCellObservables_holds
    (hLattice : ScalingPreservesGridPoints)
    (hCells : ScalingPreservesCellsAndGroup)
    (hGroup : ChessboardTori.ReflectionGroupCoordinates.Statement) :
    ScalingPreservesCellObservables := by
  intro D S g hg
  obtain ⟨hcell, hint, -, -, φ, hφ⟩ := hCells D S g hg
  have hbij : Function.Bijective S.linkMap := (hLattice D S).2.1
  have hinterior : ∀ C ∈ g.cellSet, S.toFun '' interior C = interior (S.toFun '' C) := by
    rintro _ ⟨k, rfl⟩
    rw [hint, hcell]
  refine ⟨fun C hC => ?_, fun C hC C' hC' F _ => ?_⟩
  · apply Subset.antisymm
    · rintro _ ⟨F, hF, rfl⟩
      exact ScalingCellObservables.comp_pullback_mem_cellObservables S (hinterior C hC) hF
    · intro G hG
      exact ScalingCellObservables.exists_comp_pullback_eq S (hinterior C hC) hbij hG
  · have hcells : ∀ C ∈ g.cellSet, S.toFun '' C ∈ (S.gridImage g).cellSet := by
      rintro _ ⟨k, rfl⟩
      exact ⟨k, (hcell k).symm⟩
    have hr : (g.mover C C').1 '' C = C' :=
      Classical.epsilon_spec (p := fun r : g.reflectionGroup => r.1 '' C = C')
        ((hGroup D g).2.2.2.2.2.2.1 C hC C' hC').exists
    set r := g.mover C C' with hrdef
    obtain ⟨hconj, hsgn⟩ := hφ r
    have hact : ∀ x, (φ r).1 (S.toFun x) = S.toFun (r.1 x) := fun x => by
      have h := congrArg (fun p : Equiv.Perm InfiniteLattice.AmbientSpace => p (S.toPerm x)) hconj
      have hx : S.toPerm⁻¹ (S.toPerm x) = x := S.toPerm.symm_apply_apply x
      have h' : (S.toPerm * r.1 * S.toPerm⁻¹) (S.toPerm x) = S.toPerm (r.1 x) := by
        simp only [Equiv.Perm.mul_apply, hx]
      exact h.trans h'
    have himg : (φ r).1 '' (S.toFun '' C) = S.toFun '' C' := by
      rw [← hr, image_image, image_image]
      exact image_congr fun x _ => hact x
    have hcarry : (S.gridImage g).mover (S.toFun '' C) (S.toFun '' C') = φ r :=
      ((hGroup S.image (S.gridImage g)).2.2.2.2.2.2.1 _ (hcells C hC) _ (hcells C' hC')).unique
        (Classical.epsilon_spec (p := fun s : (S.gridImage g).reflectionGroup =>
          s.1 '' (S.toFun '' C) = S.toFun '' C') ⟨φ r, himg⟩) himg
    funext V
    simp only [ReflectionGrid.transportTo, hcarry, ← hrdef, ReflectionGrid.transport,
      Function.comp_apply]
    change Conventions.signedConj (orientationSign r.1) (F _) =
      Conventions.signedConj (orientationSign (φ r).1) (F _)
    rw [hsgn]
    congr 2
    exact ScalingCellObservables.pullbackField_pullback S _ _ hact V
end YangMills.Construction.MirrorGridsAllSides
end
