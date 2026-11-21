import YangMills.Construction.SixteenPointsOnASmallTorus.CopiesAboutASite
import YangMills.Construction.SixteenPointsOnASmallTorus.MeanOfTheCopiesAtNoLevelProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.SmallTorusCopies
open TorusFields WeightedResponses BlockAverages TestFunctions
variable {m : ℕ} [NeZero m]
private theorem mem_plaquettesIn_univ (p : TorusPlaquette m) :
    p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)) ↔ p.2.1 < p.2.2 := by
  simp [plaquettesIn]
private theorem sum_plaquettesIn_translate (u : TorusSite m) (G : TorusPlaquette m → ℝ) :
    ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)), G (p.1 + u, p.2) = ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)), G p := by
  refine Finset.sum_bij' (fun p _ => (p.1 + u, p.2)) (fun p _ => (p.1 - u, p.2)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    exact (mem_plaquettesIn_univ _).2 ((mem_plaquettesIn_univ p).1 hp)
  · intro p hp
    exact (mem_plaquettesIn_univ _).2 ((mem_plaquettesIn_univ p).1 hp)
  · intro p _
    simp
  · intro p _
    simp
  · intro p _
    rfl
omit [NeZero m] in
private theorem plaquetteEnergyOf_translate (u : TorusSite m) (U : TorusField m) (p : TorusPlaquette m) :
    plaquetteEnergyOf (TorusFields.translate u U) p = plaquetteEnergyOf U (p.1 + u, p.2) := by
  obtain ⟨x, μ, ν⟩ := p
  simp only [plaquetteEnergyOf, plaquetteEnergy, holonomy, TorusFields.translate]
  rw [add_right_comm x (unitStep m μ) u, add_right_comm x (unitStep m ν) u]
private theorem curvatureObservable_translateWeight (z : TorusSite m) (w : PlaquetteWeight m) (U : TorusField m) :
    curvatureObservable (translateWeight (-z) w) U = curvatureObservable w (TorusFields.translate z U) := by apply _root_.YangMills.SharedProofs.p30727 <;> assumption
private theorem wilsonAction_translate (z : TorusSite m) (U : TorusField m) :
    TorusFields.wilsonAction (Finset.univ : Finset (TorusSite m)) (TorusFields.translate z U) =
      TorusFields.wilsonAction Finset.univ U := by
  unfold TorusFields.wilsonAction
  rw [← sum_plaquettesIn_translate z fun p => plaquetteEnergy U p.1 p.2.1 p.2.2]
  refine Finset.sum_congr rfl fun p _ => ?_
  exact plaquetteEnergyOf_translate z U p
abbrev _root_.YangMills.SharedProofs.p7329 := @wilsonAction_translate
private def translateEquiv (z : TorusSite m) : TorusField m ≃ᵐ TorusField m :=
  MeasurableEquiv.piCongrLeft (fun _ : TorusSite m => Fin 4 → UnitQuaternion) (Equiv.addRight (-z))
omit [NeZero m] in
private theorem translateEquiv_apply (z : TorusSite m) (U : TorusField m) : translateEquiv z U = TorusFields.translate z U := by
  funext y
  have h := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : TorusSite m => Fin 4 → UnitQuaternion) (Equiv.addRight (-z)) U (y + z)
  show translateEquiv z U y = U (y + z)
  simpa [translateEquiv] using h
abbrev _root_.YangMills.DeltaSharedProofs.p502299 := @translateEquiv_apply
private theorem measurePreserving_translateEquiv_fieldHaar (z : TorusSite m) :
    MeasurePreserving (translateEquiv z) (fieldHaar m) (fieldHaar m) := by
  unfold fieldHaar translateEquiv
  exact measurePreserving_piCongrLeft (fun _ : TorusSite m => Measure.pi fun _ : Fin 4 => haarUnit) (Equiv.addRight (-z))
abbrev _root_.YangMills.DeltaSharedProofs.p500734 := @measurePreserving_translateEquiv_fieldHaar
private theorem measurePreserving_translateEquiv_wilsonLaw (β : ℝ) (z : TorusSite m) :
    MeasurePreserving (translateEquiv z) (wilsonLaw β m) (wilsonLaw β m) := by
  refine ⟨(translateEquiv z).measurable, ?_⟩
  refine Measure.ext fun s hs => ?_
  rw [(translateEquiv z).map_apply]
  unfold wilsonLaw
  rw [withDensity_apply _ hs, withDensity_apply _ ((translateEquiv z).measurable hs)]
  have key := (measurePreserving_translateEquiv_fieldHaar z).setLIntegral_comp_preimage_emb (translateEquiv z).measurableEmbedding
    (fun U => ENNReal.ofReal (Real.exp (-β * TorusFields.wilsonAction Finset.univ U) /
      ∫ U', Real.exp (-β * TorusFields.wilsonAction Finset.univ U') ∂(fieldHaar m))) s
  rw [← key]
  simp only [translateEquiv_apply, wilsonAction_translate]
theorem reflectedMeanTranslation : reflectedMeanTranslationStatement := by
  intro β a₀ M c _ _ z h e
  unfold reflectedProductMean
  have hw : ∀ U : TorusField (c * M), (∏ k : Fin 4 → Fin c, (curvatureObservable (reflectedWeightAbout a₀ M z (fun μ => (k μ : ℕ)) h) U - e)) =
      ∏ k : Fin 4 → Fin c, (curvatureObservable (reflectedWeightAbout a₀ M 0 (fun μ => (k μ : ℕ)) h) (translateEquiv z U) - e) := by
    intro U
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [translateEquiv_apply]
    unfold reflectedWeightAbout
    rw [curvatureObservable_translateWeight]
    congr 2
    funext p
    simp [translateWeight]
  simp_rw [hw]
  exact (measurePreserving_translateEquiv_wilsonLaw β z).integral_comp' (g := fun U => ∏ k : Fin 4 → Fin c, (curvatureObservable (reflectedWeightAbout a₀ M 0 (fun μ => (k μ : ℕ)) h) U - e))
end YangMills.Construction.SmallTorusCopies
end
