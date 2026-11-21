import YangMills.Construction.LawOnABoxOfTheFlow.BorelFillingOfTheOutside
import YangMills.Construction.LawOnABoxOfTheFlow.LeastFillingIsBorel
import YangMills.Construction.LawOnABoxOfTheFlow.ToolsOfAChart
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.BoxGaussian
open TorusFields ResponseInTheExpansion
private def quaternionCoords (g : BlockAverages.UnitQuaternion) : Fin 4 → ℝ :=
  ![((g : BlockAverages.UnitQuaternion) : ℍ[ℝ]).re, ((g : BlockAverages.UnitQuaternion) : ℍ[ℝ]).imI,
    ((g : BlockAverages.UnitQuaternion) : ℍ[ℝ]).imJ, ((g : BlockAverages.UnitQuaternion) : ℍ[ℝ]).imK]
private theorem continuous_quaternionCoords : Continuous quaternionCoords := by
  have hv : Continuous fun g : BlockAverages.UnitQuaternion => ((g : BlockAverages.UnitQuaternion) : ℍ[ℝ]) :=
    continuous_subtype_val
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact Quaternion.continuous_re.comp hv
  · exact Quaternion.continuous_imI.comp hv
  · exact Quaternion.continuous_imJ.comp hv
  · exact Quaternion.continuous_imK.comp hv
private theorem quaternionCoords_injective : Function.Injective quaternionCoords := by
  intro g h e
  have h0 := congrFun e 0
  have h1 := congrFun e 1
  have h2 := congrFun e 2
  have h3 := congrFun e 3
  simp only [quaternionCoords, Matrix.cons_val] at h0 h1 h2 h3
  exact Subtype.ext (Quaternion.ext _ _ h0 h1 h2 h3)
private theorem exists_continuous_injective_euclidean (B : Type) [Finite B] :
    ∃ (m : ℕ) (ι : (B → BlockAverages.UnitQuaternion) → Fin m → ℝ), Continuous ι ∧ Function.Injective ι := by
  let e := Finite.equivFin (B × Fin 4)
  refine ⟨_, fun w k => quaternionCoords (w (e.symm k).1) (e.symm k).2, ?_, ?_⟩
  · refine continuous_pi fun k => ?_
    exact (continuous_apply _).comp (continuous_quaternionCoords.comp (continuous_apply _))
  · intro w w' h
    funext b
    refine quaternionCoords_injective (funext fun i => ?_)
    have := congrFun h (e (b, i))
    simpa using this
private theorem exists_measurable_section (hL : BoxLaws.LexLeastSectionMeasurable)
    {U W : Type} [TopologicalSpace U] [T2Space U] [SecondCountableTopology U] [CompactSpace U]
    [MeasurableSpace U] [BorelSpace U] [TopologicalSpace W] [CompactSpace W]
    [MeasurableSpace W] [BorelSpace W] [Nonempty W]
    {m : ℕ} {ι : W → Fin m → ℝ} (hc : Continuous ι) (hi : Function.Injective ι)
    {C : Set (U × W)} (hC : IsClosed C) :
    ∃ f : U → W, MeasurableSet (Prod.fst '' C) ∧
      Measurable (fun u : (Prod.fst '' C : Set U) => f u) ∧
      ∀ u ∈ Prod.fst '' C, (u, f u) ∈ C := by
  have hcm : Continuous (Prod.map id ι : U × W → U × (Fin m → ℝ)) := continuous_id.prodMap hc
  have hK : IsCompact ((Prod.map id ι : U × W → U × (Fin m → ℝ)) '' C) :=
    hC.isCompact.image hcm
  obtain ⟨g, hg, hgm⟩ := hL U m _ hK
  have hproj : Prod.fst '' ((Prod.map id ι : U × W → U × (Fin m → ℝ)) '' C) = Prod.fst '' C := by
    rw [Set.image_image]
    rfl
  rw [hproj] at hg hgm
  have hleft : Function.LeftInverse (Function.invFun ι) ι := Function.leftInverse_invFun hi
  have hin : ∀ u ∈ Prod.fst '' C, ι (Function.invFun ι (g u)) = g u ∧ (u, Function.invFun ι (g u)) ∈ C := by
    intro u hu
    obtain ⟨⟨⟨u', w⟩, hw, he⟩, -⟩ := hg u hu
    have h1 : u' = u := congrArg Prod.fst he
    have h2 : ι w = g u := congrArg Prod.snd he
    subst h1
    rw [← h2, hleft w]
    exact ⟨rfl, hw⟩
  refine ⟨fun u => Function.invFun ι (g u),
    (hC.isCompact.image continuous_fst).isClosed.measurableSet, ?_, fun u hu => (hin u hu).2⟩
  have hme : MeasurableEmbedding ι := (hc.isClosedEmbedding hi).measurableEmbedding
  refine hme.measurable_comp_iff.mp ?_
  have : (ι ∘ fun u : (Prod.fst '' C : Set U) => Function.invFun ι (g u)) =
      fun u : (Prod.fst '' C : Set U) => g u := funext fun u => (hin u u.2).1
  rw [this]
  exact hgm
variable {n : ℕ} [NeZero n]
omit [NeZero n] in
private theorem continuous_curvature_apply (x : TorusSite n) (μ ν : Fin 4) :
    Continuous fun W : TorusField n => curvature W x μ ν := by apply _root_.YangMills.Construction.TorusFields.continuous_curvature <;> assumption
theorem borelOuterFilling (hL : BoxLaws.LexLeastSectionMeasurable) :
    borelOuterFillingStatement := by
  intro n _ o R δ
  obtain ⟨m, ι, hc, hi⟩ := exists_continuous_injective_euclidean {b : TorusBond n // b ∈ bondsTouching o R}
  let C : Set (OuterField o R × InnerField o R) := {p | ∀ q ∈ plaquettesIn (supBall o (2 * R)),
    curvature (glueField p.1 p.2) q.1 q.2.1 q.2.2 ≤ δ}
  have hC : IsClosed C := by
    have : C = ⋂ q ∈ plaquettesIn (supBall o (2 * R)),
        {p : OuterField o R × InnerField o R | curvature (glueField p.1 p.2) q.1 q.2.1 q.2.2 ≤ δ} := by
      ext p
      simp [C]
    rw [this]
    refine isClosed_biInter fun q _ => isClosed_le ?_ continuous_const
    exact (continuous_curvature_apply q.1 q.2.1 q.2.2).comp (continuous_glueField o R)
  obtain ⟨f, h1, h2, h3⟩ := exists_measurable_section hL hc hi hC
  have hF : Prod.fst '' C = {u : OuterField o R | ∃ w, ∀ p ∈ plaquettesIn (supBall o (2 * R)),
      curvature (glueField u w) p.1 p.2.1 p.2.2 ≤ δ} := by
    ext u
    constructor
    · rintro ⟨⟨u', w⟩, hw, rfl⟩
      exact ⟨w, hw⟩
    · rintro ⟨w, hw⟩
      exact ⟨(u, w), hw, rfl⟩
  rw [hF] at h1 h2 h3
  exact ⟨f, h1, h2, fun u hu p hp => h3 u hu p hp⟩
end YangMills.Construction.BoxGaussian
end
