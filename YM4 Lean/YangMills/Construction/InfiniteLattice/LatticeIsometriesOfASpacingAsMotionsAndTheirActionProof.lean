import YangMills.Construction.InfiniteLattice.LatticeIsometriesOfASpacingAsMotionsAndTheirAction
import YangMills.Construction.InfiniteLattice.PeriodicGibbsStatesAndCopies
import YangMills.Construction.InfiniteLattice.SpacePlaquettesFunctionsOfPlaquettesAndLatticeIsometries
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.InfiniteLattice.SymmetriesAsMotions
open CutoffStructure
variable {a : ℝ}
theorem pointMap_pointMap {t r : LatticeSymmetry a} (hinv : Function.LeftInverse t.toFun r.toFun)
    (x : LatticePoint a) : t.pointMap (r.pointMap x) = x :=
  Subtype.ext (hinv x)
theorem plaquetteMap_plaquetteMap (ha : 0 < a) {t r : LatticeSymmetry a}
    (ht : ∀ p : ElementaryPlaquette a, (t.plaquetteMap p).cornerSet = t.pointMap '' p.cornerSet)
    (hr : ∀ p : ElementaryPlaquette a, (r.plaquetteMap p).cornerSet = r.pointMap '' p.cornerSet)
    (hinv : Function.LeftInverse t.toFun r.toFun) (p : ElementaryPlaquette a) :
    t.plaquetteMap (r.plaquetteMap p) = p := by
  apply ElementaryPlaquette.cornerSet_injective ha
  rw [ht, hr, image_image]
  simp only [pointMap_pointMap hinv, image_id']
theorem pullbackField_pullbackField {t r : LatticeSymmetry a}
    (hinv : Function.LeftInverse r.toFun t.toFun) (U : GaugeField a) :
    t.pullbackField (r.pullbackField U) = U :=
  Subtype.ext (funext fun e => congrArg U.1
    (Link.ext (Subtype.ext (hinv e.initial)) (Subtype.ext (hinv e.terminal))))
theorem pullbackField_comp (r r' : LatticeSymmetry a) :
    (r.comp r').pullbackField = r'.pullbackField ∘ r.pullbackField :=
  funext fun U => Subtype.ext (funext fun _ => congrArg U.1 (Link.ext rfl rfl))
theorem exists_link_of_euclidNormVec_eq (ha : 0 < a) {x y : LatticePoint a}
    (hxy : TorusMetric.euclidNormVec ((x : AmbientSpace) - y) = a) :
    ∃ e : Link a, e.initial = x ∧ e.terminal = y := by
  have hswap : TorusMetric.euclidNormVec ((y : AmbientSpace) - x) =
      TorusMetric.euclidNormVec ((x : AmbientSpace) - y) := by
    unfold TorusMetric.euclidNormVec
    congr 1
    refine Finset.sum_congr rfl fun μ _ => ?_
    simp only [Pi.sub_apply]
    ring
  exact ⟨⟨x, y, isAdjacent_of_euclidNormVec x y (by rw [hswap, hxy, abs_of_pos ha])⟩, rfl, rfl⟩
theorem faceEnergy_around_corners (ha : 0 < a) (hf : FaceEnergyProperties a)
    (p : ElementaryPlaquette a) : FaceEnergyAroundCorners p := by
  intro y₀ y₁ y₂ y₃ hc d₀ d₁ d₂ d₃
  obtain ⟨e₀, s₀, f₀⟩ := exists_link_of_euclidNormVec_eq ha d₀
  obtain ⟨e₁, s₁, f₁⟩ := exists_link_of_euclidNormVec_eq ha d₁
  obtain ⟨e₂, s₂, f₂⟩ := exists_link_of_euclidNormVec_eq ha d₂
  obtain ⟨e₃, s₃, f₃⟩ := exists_link_of_euclidNormVec_eq ha d₃
  refine ⟨e₀, e₁, e₂, e₃, s₀, f₀, s₁, f₁, s₂, f₂, s₃, f₃, fun U => ?_⟩
  have hrange : range (![y₀, y₁, y₂, y₃] : Fin 4 → LatticePoint a) = p.cornerSet := by
    rw [hc]
    ext x
    simp only [Matrix.range_cons, Matrix.range_empty, union_empty, mem_union, mem_singleton_iff,
      mem_insert_iff]
  have hcycle : IsBoundaryCycle p ![y₀, y₁, y₂, y₃] ![e₀, e₁, e₂, e₃] := by
    refine ⟨hrange, fun i => ?_⟩
    fin_cases i
    · exact ⟨s₀, f₀⟩
    · exact ⟨s₁, f₁⟩
    · exact ⟨s₂, f₂⟩
    · exact ⟨s₃, f₃⟩
  have hval : (1 / 2 : ℝ) * (Matrices.ComplexMatrix2.fullTrace
      ((U e₀ * U e₁ * U e₂ * U e₃ : Matrices.ComplexMatrix2.specialUnitary) :
        Matrices.ComplexMatrix2)).re =
      (1 / 2) * (Matrices.ComplexMatrix2.fullTrace
        (faceHolonomy U p : Matrices.ComplexMatrix2)).re :=
    (hf p).1 U ![y₀, y₁, y₂, y₃] ![e₀, e₁, e₂, e₃] hcycle
  unfold faceEnergy
  rw [hval]
theorem holds (h₁ : SymmetryActionOnObservables) (h₂ : FieldSpaceAndSymmetries) : Statement := by
  intro a ha r r'
  obtain ⟨-, hHomeo, hObs, hComp, -, hLin, hGrow, -, hLoc, hInv, hState⟩ := h₁ ⟨a, ha⟩
  obtain ⟨-, -, hFun, hSym, hCov, -⟩ := h₂ a ha
  obtain ⟨hMotion, hEach⟩ := hSym
  have hCorners : ∀ s : LatticeSymmetry a, ∀ p : ElementaryPlaquette a,
      (s.plaquetteMap p).cornerSet = s.pointMap '' p.cornerSet :=
    fun s => (hEach s).2.2.1
  refine ⟨⟨?_, ?_⟩, ⟨rfl, (hInv r).2.1⟩, fun e => ⟨r.linkMap e, rfl, rfl⟩, ⟨?_, (hEach r).2.2.2.1, ?_,
    (hEach r).2.2.2.2.1⟩, ⟨(hHomeo r).1, pullbackField_comp r r', (hHomeo r).2, ?_⟩, ?_, ?_, ?_⟩
  · obtain ⟨w, hw, v, hv⟩ := (hMotion r.toFun).mp ⟨r, rfl⟩
    exact ⟨w, hw, v, fun x => by rw [hv]; rfl⟩
  · intro R hR v
    obtain ⟨t, ht⟩ := (hMotion (latticeMotion R v)).mpr ⟨R, hR, v, rfl⟩
    exact ⟨t, fun x => by rw [ht]; rfl⟩
  · intro p q
    constructor
    · rintro rfl
      exact hCorners r p
    · intro hpq
      exact ElementaryPlaquette.cornerSet_injective ha (hpq.trans (hCorners r p).symm)
  · intro t ht
    exact ⟨plaquetteMap_plaquetteMap ha (hCorners t) (hCorners r) ht.1,
      plaquetteMap_plaquetteMap ha (hCorners r) (hCorners t) ht.2⟩
  · intro t ht
    exact ⟨pullbackField_pullbackField ht.2, pullbackField_pullbackField ht.1⟩
  · refine ⟨rfl, fun F F' hF hF' => ?_⟩
    obtain ⟨hOF, hMul, hConj⟩ := (hObs r).1 F F' hF hF'
    obtain ⟨hAdd, hSmul, -, hNorm⟩ := (hLin r).2 F hF
    refine ⟨hOF, hNorm, hAdd F' hF', hSmul, hMul, hConj, (hComp r r').2 F hF, ?_, ?_, ?_⟩
    · intro hc
      exact hc.comp (hHomeo r).2.continuous
    · intro S hS
      exact show r.actOn F ∈ boundedRegionObservables a (r.setImage S) from by
        rw [← (hObs r).2 S]
        exact mem_image_of_mem _ hS
    · rintro ⟨S, hb, hm⟩
      have hF₁ : F ∈ localRegionObservables a S := by
        rw [← hGrow.2.2 S hb]
        exact ⟨hF, hm⟩
      have hF₂ : r.actOn F ∈ localRegionObservables a (r.setImage S) := by
        rw [← hLoc.1 r S]
        exact mem_image_of_mem _ hF₁
      simp only [localRegionObservables, mem_iUnion] at hF₂
      obtain ⟨Q, hQ, hQ'⟩ := hF₂
      exact ⟨r.setImage S ∩ Q, Bornology.IsBounded.subset hQ inter_subset_right, hQ'.2⟩
  · intro p
    refine ⟨faceEnergy_around_corners ha hFun p, ?_⟩
    exact funext fun U => hCov.1 r p U
  · intro ν hν hr hr'
    exact ⟨fun t ht => (hInv r).2.2 t ht |>.2 ν hν hr, (hState ν hν).1 r r' hr hr'⟩
end YangMills.Construction.InfiniteLattice.SymmetriesAsMotions
end
