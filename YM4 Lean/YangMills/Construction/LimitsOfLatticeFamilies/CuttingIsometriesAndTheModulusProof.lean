import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import YangMills.Construction.InfiniteLattice.FactsOfTheSignsAtACutoffProof
import YangMills.Construction.LimitsOfLatticeFamilies.CompactlySupportedClassC1FunctionsAreLipschitzProof
import YangMills.Construction.LimitsOfLatticeFamilies.CuttingIsometriesAndTheModulus
import YangMills.Construction.LimitsOfLatticeFamilies.FactsOfTheSetting
import YangMills.Construction.ReflectionPositivity.ReflectionOfAMirrorOfOneTorusProof
import YangMills.Construction.SystemOfAdmissibleConstants.TentsOfASmallSideProof
import Mathlib
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal NNReal
noncomputable section
namespace YangMills.Construction.LatticeLimits.CutoffAndSymmetry
open ModelSpace TorusMetric MetricNotions TestFunctions
theorem euclidNormVec_sq (v : Fin 4 → ℝ) : euclidNormVec v ^ 2 = ∑ μ, v μ ^ 2 := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.euclidNormVec_sq <;> assumption
theorem euclidNormVec_nonneg (v : Fin 4 → ℝ) : 0 ≤ euclidNormVec v := Real.sqrt_nonneg _
theorem euclidNormVec_zero : euclidNormVec (0 : Fin 4 → ℝ) = 0 := by simp [euclidNormVec]
theorem euclidNormVec_neg (v : Fin 4 → ℝ) : euclidNormVec (-v) = euclidNormVec v := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_neg <;> assumption
theorem abs_apply_le_euclidNormVec (v : Fin 4 → ℝ) (μ : Fin 4) : |v μ| ≤ euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
theorem norm_le_euclidNormVec (v : Fin 4 → ℝ) : ‖v‖ ≤ euclidNormVec v := by apply _root_.YangMills.Construction.SeparatedTuplesR4.norm_le_euclidNormVec <;> assumption
theorem euclidNormVec_le_two_mul_norm (v : Fin 4 → ℝ) : euclidNormVec v ≤ 2 * ‖v‖ := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.euclidNormVec_le_two_mul_norm <;> assumption
theorem continuous_euclidNormVec : Continuous euclidNormVec := by apply _root_.YangMills.Construction.SeparatedTuples.continuous_euclidNormVec <;> assumption
theorem eq_zero_of_euclidNormVec_eq_zero {v : Fin 4 → ℝ} (h : euclidNormVec v = 0) : v = 0 := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.eq_zero_of_euclidNormVec_eq_zero <;> assumption
theorem euclidNormVec_sub_sq (u v : Fin 4 → ℝ) :
    euclidNormVec (u - v) ^ 2 = euclidNormVec u ^ 2 + euclidNormVec v ^ 2 - 2 * dotProduct u v := by
  simp only [euclidNormVec_sq, dotProduct, Fin.sum_univ_four, Pi.sub_apply]
  ring
theorem dotProduct_pi_single_pi_single (ε : ℝ) (μ ν : Fin 4) :
    dotProduct (Pi.single μ ε : Fin 4 → ℝ) (Pi.single ν ε) = if μ = ν then ε * ε else 0 := by
  by_cases h : μ = ν
  · subst h
    simp
  · simp [h]
theorem exists_matrix_of_isometric_on_ball {ρ : ℝ} (hρ : 0 < ρ) (γ : (Fin 4 → ℝ) → Fin 4 → ℝ)
    (h0 : γ 0 = 0)
    (hd : ∀ z z', euclidNormVec z < ρ → euclidNormVec z' < ρ →
      euclidNormVec (γ z - γ z') = euclidNormVec (z - z')) :
    ∃ W : Matrix (Fin 4) (Fin 4) ℝ, ∀ z, euclidNormVec z < ρ → γ z = W.mulVec z := by
  have hz0 : euclidNormVec (0 : Fin 4 → ℝ) < ρ := by rwa [euclidNormVec_zero]
  have hn : ∀ z, euclidNormVec z < ρ → euclidNormVec (γ z) = euclidNormVec z := fun z hz => by
    simpa [h0] using hd z 0 hz hz0
  have hdot : ∀ z z', euclidNormVec z < ρ → euclidNormVec z' < ρ →
      dotProduct (γ z) (γ z') = dotProduct z z' := by
    intro z z' hz hz'
    have h1 := euclidNormVec_sub_sq (γ z) (γ z')
    have h2 := euclidNormVec_sub_sq z z'
    rw [hd z z' hz hz', hn z hz, hn z' hz', h2] at h1
    linarith
  obtain ⟨ε, hε, hερ⟩ : ∃ ε : ℝ, 0 < ε ∧ ε < ρ := ⟨ρ / 2, by positivity, by linarith⟩
  let e : Fin 4 → Fin 4 → ℝ := fun μ => Pi.single μ ε
  have he : ∀ μ, euclidNormVec (e μ) < ρ := by
    intro μ
    have hs : ∑ ν, (e μ) ν ^ 2 = ε ^ 2 := by
      simp [e, Pi.single_apply]
    have : euclidNormVec (e μ) = ε := by
      rw [euclidNormVec, hs, Real.sqrt_sq hε.le]
    rwa [this]
  let V : Matrix (Fin 4) (Fin 4) ℝ := fun μ ν => ε⁻¹ * γ (e μ) ν
  have hVdot : ∀ (μ : Fin 4) (u : Fin 4 → ℝ),
      V.mulVec u μ = ε⁻¹ * dotProduct (γ (e μ)) u := by
    intro μ u
    simp only [Matrix.mulVec, dotProduct, V, Finset.mul_sum, mul_assoc]
  have hVV : V * V.transpose = 1 := by
    ext μ ν
    have h1 : (V * V.transpose) μ ν = ε⁻¹ * ε⁻¹ * dotProduct (γ (e μ)) (γ (e ν)) := by
      rw [Matrix.mul_apply]
      simp only [Matrix.transpose_apply, dotProduct, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by
        show (ε⁻¹ * γ (e μ) j) * (ε⁻¹ * γ (e ν) j) = _
        ring
    rw [h1, hdot _ _ (he μ) (he ν), dotProduct_pi_single_pi_single, Matrix.one_apply]
    by_cases h : μ = ν
    · simp only [h, if_true]
      field_simp
    · simp [h]
  have hVV' : V.transpose * V = 1 := mul_eq_one_comm.1 hVV
  refine ⟨V.transpose, fun z hz => ?_⟩
  have hV : V.mulVec (γ z) = z := by
    funext μ
    rw [hVdot, hdot _ _ (he μ) hz]
    simp only [e, single_dotProduct]
    field_simp
  calc γ z = (V.transpose * V).mulVec (γ z) := by rw [hVV', Matrix.one_mulVec]
    _ = V.transpose.mulVec (V.mulVec (γ z)) := (Matrix.mulVec_mulVec _ _ _).symm
    _ = V.transpose.mulVec z := by rw [hV]
section Distance
variable {X : Type*} {d : X → X → ℝ}
theorem subset_closureWrt (hd : ∀ x, d x x = 0) (Z : Set X) : Z ⊆ closureWrt d Z :=
  fun x hx r hr => ⟨x, hx, by rwa [hd]⟩
theorem closureWrt_mono {Z Z' : Set X} (h : Z ⊆ Z') : closureWrt d Z ⊆ closureWrt d Z' := by apply _root_.YangMills.Construction.AtCutoff.SignFacts.closureWrt_mono <;> assumption
theorem isClosedWrt_closureWrt (tri : ∀ x y w, d x y ≤ d x w + d w y) (Z : Set X) :
    IsClosedWrt d (closureWrt d Z) := by apply _root_.YangMills.Construction.LatticeLimits.LipschitzOfC1.isOpenWrt_compl_closureWrt <;> assumption
theorem isCompactWrt_of_isClosedWrt_subset {S T : Set X} (hS : IsCompactWrt d S)
    (hT : IsClosedWrt d T) (hTS : T ⊆ S) : IsCompactWrt d T := by apply _root_.YangMills.SharedProofs.p5019 <;> assumption
theorem image_closureWrt (e : X ≃ X) (he : ∀ x y, d (e x) (e y) = d x y) (Z : Set X) :
    e '' closureWrt d Z = closureWrt d (e '' Z) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩ r hr
    obtain ⟨w, hw, hxw⟩ := hx r hr
    exact ⟨e w, ⟨w, hw, rfl⟩, by rwa [he]⟩
  · intro hy
    refine ⟨e.symm y, fun r hr => ?_, by simp⟩
    obtain ⟨w, ⟨u, hu, rfl⟩, hyw⟩ := hy r hr
    refine ⟨u, hu, ?_⟩
    have h := he (e.symm y) u
    rw [e.apply_symm_apply] at h
    linarith
theorem isCompactWrt_image (e : X ≃ X) (he : ∀ x y, d (e x) (e y) = d x y) {S : Set X}
    (hS : IsCompactWrt d S) : IsCompactWrt d (e '' S) := by apply _root_.YangMills.Construction.AtCutoff.SignFacts.IsCompactWrt.image <;> assumption
theorem bestLipschitzConstant_nonneg (f : X → ℝ) : 0 ≤ bestLipschitzConstant d f :=
  Real.sInf_nonneg fun _ hC => hC.1
theorem bestLipschitzConstant_le {f : X → ℝ} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x y, ‖f x - f y‖ ≤ C * d x y) : bestLipschitzConstant d f ≤ C :=
  csInf_le ⟨0, fun _ h => h.1⟩ ⟨hC0, hC⟩
theorem norm_sub_le_bestLipschitzConstant_mul (hd : ∀ x y, 0 ≤ d x y) {f : X → ℝ}
    (hf : IsLipschitzFor d f) (x y : X) : ‖f x - f y‖ ≤ bestLipschitzConstant d f * d x y := by apply _root_.YangMills.SharedProofs.p9400 <;> assumption
end Distance
section OnTheSpace
variable {s : Conventions.StandingParameters} {M : BlockScale s} {Y : ModelSpace}
theorem cutoffBound (F : SettingFactsHold s M Y) : CutoffBound s M Y := by
  intro A h χ hh hχ hχ01
  have d0 : ∀ x y, 0 ≤ ModelSpace.dist s Y x y := F.dist_invariant.2.2.1
  have tri : ∀ x y w, ModelSpace.dist s Y x y ≤ ModelSpace.dist s Y x w + ModelSpace.dist s Y w y :=
    F.dist_invariant.2.2.2.2.2.1
  have hC1 : IsC1 s Y (fun y => χ y * h y) := (F.isC1_iff.2.2 χ h hχ.1 hh.1).2
  have hsub1 : supportIn s Y (fun y => χ y * h y) ⊆ supportIn s Y χ :=
    closureWrt_mono fun y hy => left_ne_zero_of_mul hy
  have hsub2 : supportIn s Y (fun y => χ y * h y) ⊆ supportIn s Y h :=
    closureWrt_mono fun y hy => right_ne_zero_of_mul hy
  have hcomp : IsCompactIn s Y (supportIn s Y (fun y => χ y * h y)) :=
    isCompactWrt_of_isClosedWrt_subset hh.2.1 (isClosedWrt_closureWrt tri _) hsub2
  refine ⟨⟨hC1, hcomp, fun y hy => ⟨hh.2.2 (hsub2 hy), hsub1 hy⟩⟩, ?_⟩
  have hh' : h ∈ c1CompactSupp s Y univ := ⟨hh.1, hh.2.1, subset_univ _⟩
  obtain ⟨⟨C, hC⟩, hLip⟩ := F.submodules.2.2.1 h (F.c1_lipschitz.2 univ hh')
  have hLipχ : IsLipschitzReal s Y χ := (F.c1_lipschitz.2 univ hχ).1
  have hbd : ∀ y, |h y| ≤ uniformNorm h := fun y =>
    le_ciSup (f := fun y => ‖h y‖) ⟨C, by rintro _ ⟨y, rfl⟩; exact hC y⟩ y
  have hH0 : 0 ≤ uniformNorm h := (abs_nonneg _).trans (hbd 0)
  have hχabs : ∀ y, |χ y| ≤ 1 := fun y => by
    rw [abs_of_nonneg (hχ01 y).1]
    exact (hχ01 y).2
  have hsup : uniformNorm (fun y => χ y * h y) ≤ uniformNorm h := by
    refine ciSup_le fun y => ?_
    rw [Real.norm_eq_abs, abs_mul]
    calc |χ y| * |h y| ≤ 1 * |h y| :=
          mul_le_mul_of_nonneg_right (hχabs y) (abs_nonneg _)
      _ ≤ uniformNorm h := by rw [one_mul]; exact hbd y
  have hLχ0 : 0 ≤ lipNumber s Y χ := by
    rw [lipNumber_eq_bestLipschitzConstant]
    exact bestLipschitzConstant_nonneg _
  have hLip' : lipNumber s Y (fun y => χ y * h y) ≤
      lipNumber s Y h + uniformNorm h * lipNumber s Y χ := by
    rw [lipNumber_eq_bestLipschitzConstant, lipNumber_eq_bestLipschitzConstant,
      lipNumber_eq_bestLipschitzConstant]
    refine bestLipschitzConstant_le (add_nonneg (bestLipschitzConstant_nonneg _)
      (mul_nonneg hH0 (bestLipschitzConstant_nonneg _))) fun x y => ?_
    have h1 := norm_sub_le_bestLipschitzConstant_mul d0 hLip x y
    have h2 := norm_sub_le_bestLipschitzConstant_mul d0 hLipχ x y
    rw [Real.norm_eq_abs] at h1 h2 ⊢
    have hid : χ x * h x - χ y * h y = χ x * (h x - h y) + (χ x - χ y) * h y := by ring
    rw [hid]
    calc |χ x * (h x - h y) + (χ x - χ y) * h y|
        ≤ |χ x * (h x - h y)| + |(χ x - χ y) * h y| := abs_add_le _ _
      _ = |χ x| * |h x - h y| + |χ x - χ y| * |h y| := by rw [abs_mul, abs_mul]
      _ ≤ 1 * |h x - h y| + |χ x - χ y| * uniformNorm h := by
          gcongr
          · exact hχabs x
          · exact hbd y
      _ ≤ 1 * (bestLipschitzConstant (ModelSpace.dist s Y) h * ModelSpace.dist s Y x y) +
            (bestLipschitzConstant (ModelSpace.dist s Y) χ * ModelSpace.dist s Y x y) *
              uniformNorm h := by
          gcongr
      _ = _ := by ring
  rw [sharpNorm_eq_max, sharpNorm_eq_max]
  set N := max (uniformNorm h) (40 * (M.1 : ℝ) * lipNumber s Y h) with hN
  have hN1 : uniformNorm h ≤ N := le_max_left _ _
  have hN2 : 40 * (M.1 : ℝ) * lipNumber s Y h ≤ N := le_max_right _ _
  have ha : 0 ≤ 40 * (M.1 : ℝ) * lipNumber s Y χ := by positivity
  have hN0 : 0 ≤ N := hH0.trans hN1
  refine max_le ?_ ?_
  · have : 0 ≤ 40 * (M.1 : ℝ) * lipNumber s Y χ * N := mul_nonneg ha hN0
    nlinarith
  · have h1 : 40 * (M.1 : ℝ) * lipNumber s Y (fun y => χ y * h y) ≤
        40 * (M.1 : ℝ) * (lipNumber s Y h + uniformNorm h * lipNumber s Y χ) :=
      mul_le_mul_of_nonneg_left hLip' (by positivity)
    have h2 : 0 ≤ 40 * (M.1 : ℝ) * lipNumber s Y χ * (N - uniformNorm h) :=
      mul_nonneg ha (by linarith)
    nlinarith
theorem standingSide_pos (s : Conventions.StandingParameters) : 0 < s.side := by apply _root_.YangMills.Construction.ReflectionPositivity.TorusMirrors.AxisReflection.side_pos <;> assumption
theorem supportIn_pushFun (r : SpaceIsometry s Y) (h : Y.Carrier s → ℝ) :
    supportIn s Y (r.pushFun h) = r.toEquiv '' supportIn s Y h := by
  have hset : {y | r.pushFun h y ≠ 0} = r.toEquiv '' {y | h y ≠ 0} := by
    ext y
    constructor
    · intro hy
      exact ⟨r.toEquiv.symm y, hy, by simp⟩
    · rintro ⟨x, hx, rfl⟩
      simpa [ModelSpace.SpaceIsometry.pushFun] using hx
  show closureWrt (ModelSpace.dist s Y) _ = r.toEquiv '' closureWrt (ModelSpace.dist s Y) _
  rw [hset, image_closureWrt r.toEquiv r.dist_eq]
theorem isC1_pushFun (E : SettingFactsHold s M euclidean)
    (F : SettingFactsHold s M Y) (r : SpaceIsometry s Y) {h : Y.Carrier s → ℝ}
    (hh : IsC1 s Y h) : IsC1 s Y (r.pushFun h) := by
  have hC : ContDiff ℝ 1 (h ∘ proj s Y) := (F.isC1_iff.1 h).1 hh
  refine (F.isC1_iff.1 _).2 ?_
  show ContDiff ℝ 1 _
  rw [contDiff_iff_contDiffAt]
  intro x0
  have hadd : ∀ x x', proj s Y (x + x') = proj s Y x + proj s Y x' :=
    F.proj_lifts.1
  let φ : (Fin 4 → ℝ) →+ Y.Carrier s := AddMonoidHom.mk' (proj s Y) hadd
  have hsub : ∀ x x', proj s Y (x - x') = proj s Y x - proj s Y x' :=
    fun x x' => φ.map_sub x x'
  have hside := standingSide_pos s
  have hlen : ∀ x, euclidNormVec x < s.side / 2 →
      ModelSpace.norm s Y (proj s Y x) = euclidNormVec x := by
    intro x hx
    cases Y with
    | euclidean => exact F.proj_lifts.2.2.2.2.2 x (Or.inl rfl)
    | torus => exact F.proj_lifts.2.2.2.2.2 x (Or.inr ⟨rfl, hx⟩)
  obtain ⟨ρ, hρ, hρs⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ = s.side / 4 := ⟨_, by positivity, rfl⟩
  have hsym : ∀ a b, ModelSpace.dist s Y (r.toEquiv.symm a) (r.toEquiv.symm b) =
      ModelSpace.dist s Y a b := by
    intro a b
    have h1 := r.dist_eq (r.toEquiv.symm a) (r.toEquiv.symm b)
    simpa using h1.symm
  have hsubE : ∀ u v : Fin 4 → ℝ, euclidNormVec (u - v) ≤ euclidNormVec u + euclidNormVec v := by
    intro u v
    have h1 : ModelSpace.norm s euclidean (u + -v) ≤
        ModelSpace.norm s euclidean u + ModelSpace.norm s euclidean (-v) :=
      E.dist_invariant.1 u (-v)
    have h2 : euclidNormVec (u + -v) ≤ euclidNormVec u + euclidNormVec (-v) := h1
    rwa [euclidNormVec_neg, ← sub_eq_add_neg] at h2
  have hlt : ∀ z z' : Fin 4 → ℝ, euclidNormVec z < ρ → euclidNormVec z' < ρ →
      euclidNormVec (z - z') < s.side / 2 := by
    intro z z' hz hz'
    have := hsubE z z'
    linarith
  let w : (Fin 4 → ℝ) → Y.Carrier s := fun z =>
    r.toEquiv.symm (proj s Y (x0 + z)) - r.toEquiv.symm (proj s Y x0)
  have hw : ∀ z z', euclidNormVec z < ρ → euclidNormVec z' < ρ →
      ModelSpace.norm s Y (w z - w z') = euclidNormVec (z - z') := by
    intro z z' hz hz'
    have e1 : w z - w z' = r.toEquiv.symm (proj s Y (x0 + z)) -
        r.toEquiv.symm (proj s Y (x0 + z')) := sub_sub_sub_cancel_right _ _ _
    have e2 : ModelSpace.norm s Y (proj s Y (x0 + z) - proj s Y (x0 + z')) =
        euclidNormVec (z - z') := by
      rw [← hsub, add_sub_add_left_eq_sub, hlen _ (hlt z z' hz hz')]
    rw [e1, ← e2]
    exact hsym _ _
  choose γ hγ using fun z => F.proj_lifts.2.2.1 (w z)
  have hγp : ∀ z, proj s Y (γ z) = w z := fun z => (hγ z).1
  have hγl : ∀ z, euclidNormVec (γ z) = ModelSpace.norm s Y (w z) := fun z => (hγ z).2
  have hw0 : w 0 = 0 := by simp [w]
  have hl0 : ModelSpace.norm s Y 0 = 0 := by
    have h1 : ModelSpace.dist s Y 0 0 = 0 := (F.dist_invariant.2.2.2.1 0 0).2 rfl
    simpa [ModelSpace.dist] using h1
  have hγ0 : γ 0 = 0 := eq_zero_of_euclidNormVec_eq_zero (by rw [hγl, hw0, hl0])
  have hz0 : euclidNormVec (0 : Fin 4 → ℝ) < ρ := by rwa [euclidNormVec_zero]
  have hγn : ∀ z, euclidNormVec z < ρ → euclidNormVec (γ z) = euclidNormVec z := fun z hz => by
    have h1 := hw z 0 hz hz0
    rw [hw0, sub_zero, sub_zero] at h1
    rw [hγl, h1]
  have hγd : ∀ z z', euclidNormVec z < ρ → euclidNormVec z' < ρ →
      euclidNormVec (γ z - γ z') = euclidNormVec (z - z') := by
    intro z z' hz hz'
    have h1 : euclidNormVec (γ z - γ z') < s.side / 2 :=
      hlt _ _ (by rwa [hγn z hz]) (by rwa [hγn z' hz'])
    rw [← hlen _ h1, hsub, hγp, hγp, hw z z' hz hz']
  obtain ⟨W, hW⟩ := exists_matrix_of_isometric_on_ball hρ γ hγ0 hγd
  obtain ⟨y0, hy0⟩ := F.proj_lifts.2.1 (r.toEquiv.symm (proj s Y x0))
  have key : ∀ z, euclidNormVec z < ρ →
      r.pushFun h (proj s Y (x0 + z)) = (h ∘ proj s Y) (y0 + W.mulVec z) := by
    intro z hz
    show h (r.toEquiv.symm (proj s Y (x0 + z))) = h (proj s Y (y0 + W.mulVec z))
    rw [← hW z hz, hadd y0, hy0, hγp]
    congr 1
    simp [w]
  have hlin : ContDiff ℝ 1 fun x : Fin 4 → ℝ => W.mulVec x :=
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin W)).contDiff
  have hG : ContDiff ℝ 1 fun x : Fin 4 → ℝ => (h ∘ proj s Y) (y0 + W.mulVec (x - x0)) :=
    hC.comp (contDiff_const.add (hlin.comp (contDiff_id.sub contDiff_const)))
  refine hG.contDiffAt.congr_of_eventuallyEq ?_
  have hnb : {x : Fin 4 → ℝ | euclidNormVec (x - x0) < ρ} ∈ 𝓝 x0 :=
    (isOpen_lt (continuous_euclidNormVec.comp (continuous_id.sub continuous_const))
      continuous_const).mem_nhds (by simpa using hz0)
  filter_upwards [hnb] with x hx
  have h1 := key (x - x0) hx
  rwa [add_sub_cancel] at h1
theorem isometryInvariance (E : SettingFactsHold s M euclidean) (F : SettingFactsHold s M Y) :
    IsometryInvariance s Y := by
  intro r
  have hcomp : ∀ h : Y.Carrier s → ℝ, IsCompactIn s Y (supportIn s Y h) →
      IsCompactIn s Y (supportIn s Y (r.pushFun h)) := fun h hh => by
    rw [supportIn_pushFun]
    exact isCompactWrt_image r.toEquiv r.dist_eq hh
  refine ⟨⟨⟨r.toEquiv.symm, fun x y => ?_⟩, rfl⟩, fun h hh => ?_, fun n _ f hf => ?_⟩
  · have h1 := r.dist_eq (r.toEquiv.symm x) (r.toEquiv.symm y)
    simpa using h1.symm
  · exact ⟨⟨isC1_pushFun E F r hh.1, hcomp h hh.2.1, subset_univ _⟩,
      supportIn_pushFun r h⟩
  · refine ⟨fun i => isC1_pushFun E F r (hf.1 i), fun i => hcomp _ (hf.2.1 i),
      fun i k hik => ?_⟩
    show Disjoint (supportIn s Y (r.pushFun (f i))) (supportIn s Y (r.pushFun (f k)))
    rw [supportIn_pushFun, supportIn_pushFun]
    exact (disjoint_image_iff r.toEquiv.injective).2 (hf.2.2 i k hik)
theorem continuous_gradR4 {G : (Fin 4 → ℝ) → ℝ} (hG : ContDiff ℝ 1 G) :
    Continuous (gradR4 G) := by apply _root_.YangMills.Construction.LatticeLimits.LipschitzOfC1.continuous_gradR4 <;> assumption
theorem gradR4_eq_zero_of_eventually {G : (Fin 4 → ℝ) → ℝ} {x : Fin 4 → ℝ}
    (h : ∀ᶠ y in 𝓝 x, G y = 0) : gradR4 G x = 0 := by
  funext μ
  show deriv (fun t : ℝ => G (x + t • Pi.single μ (1 : ℝ))) 0 = 0
  have hc : Tendsto (fun t : ℝ => x + t • Pi.single μ (1 : ℝ)) (𝓝 0) (𝓝 x) := by
    have h1 : Continuous fun t : ℝ => x + t • Pi.single μ (1 : ℝ) := by fun_prop
    simpa using h1.tendsto 0
  have he : (fun t : ℝ => G (x + t • Pi.single μ (1 : ℝ))) =ᶠ[𝓝 0] fun _ => 0 := hc.eventually h
  rw [he.deriv_eq]
  simp
theorem exists_bounded_lifts (F : SettingFactsHold s M Y) (f : c1CompactSupp s Y univ) :
    ∃ C : ℝ, ∀ x y : Y.Carrier s, ModelSpace.dist s Y x y ≤ 1 →
      grad s Y f.1 x = grad s Y f.1 y ∨
      ∃ u v, proj s Y u = x ∧ proj s Y v = y ∧
        euclidNormVec (u - v) = ModelSpace.dist s Y x y ∧ (∀ μ, |u μ| ≤ C) ∧ ∀ μ, |v μ| ≤ C := by
  have dsymm : ∀ x y, ModelSpace.dist s Y x y = ModelSpace.dist s Y y x :=
    F.dist_invariant.2.2.2.2.1
  cases Y with
  | torus =>
    refine ⟨s.side / 2 + 1, fun x y hxy => Or.inr ?_⟩
    obtain ⟨u, hu, hc⟩ := F.torus_compact.1 x
    obtain ⟨w, hw, hl⟩ := F.proj_lifts.2.2.1 (y - x)
    have hadd := F.proj_lifts.1
    have hlen : euclidNormVec w = ModelSpace.dist s torus x y := by
      rw [hl, dsymm]
      rfl
    have hu' : ∀ μ, |u μ| ≤ s.side / 2 := fun μ => abs_le.2 (hc μ)
    refine ⟨u, u + w, hu, ?_, ?_, fun μ => (hu' μ).trans (by linarith), fun μ => ?_⟩
    · rw [hadd, show proj s torus u = x from hu, show proj s torus w = y - x from hw]
      exact add_sub_cancel _ _
    · rw [sub_add_cancel_left, euclidNormVec_neg, hlen]
    · have h1 := abs_apply_le_euclidNormVec w μ
      have h2 := abs_add_le (u μ) (w μ)
      have h3 := hu' μ
      have h4 : |(u + w) μ| = |u μ + w μ| := rfl
      rw [h4]
      linarith [hlen ▸ h1]
  | euclidean =>
    obtain ⟨ρ, hρ, hS⟩ := (F.compact_bounded _ f.2.2.1).1
    have dself : ∀ x, ModelSpace.dist s euclidean x x = 0 :=
      fun x => (F.dist_invariant.2.2.2.1 x x).2 rfl
    have hzero : ∀ x : Fin 4 → ℝ, ρ < euclidNormVec x → f.1 x = 0 := by
      intro x hx
      by_contra hne
      have h1 : x ∈ supportIn s euclidean f.1 :=
        subset_closureWrt dself _ (show x ∈ {y | f.1 y ≠ 0} from hne)
      have h2 := hS h1
      rw [ballAtBase_ofReal s euclidean hρ] at h2
      exact absurd (show euclidNormVec x < ρ from h2) (not_lt.2 hx.le)
    have hgrad : ∀ x : Fin 4 → ℝ, ρ < euclidNormVec x → grad s euclidean f.1 x = 0 := by
      intro x hx
      refine gradR4_eq_zero_of_eventually ?_
      have hop : {y : Fin 4 → ℝ | ρ < euclidNormVec y} ∈ 𝓝 x :=
        (isOpen_lt continuous_const continuous_euclidNormVec).mem_nhds hx
      filter_upwards [hop] with y hy
      exact hzero y hy
    have htri : ∀ x y : (euclidean : ModelSpace).Carrier s,
        ModelSpace.norm s euclidean x ≤
          ModelSpace.norm s euclidean y + ModelSpace.dist s euclidean x y := by
      intro x y
      have h1 := F.dist_invariant.1 y (x - y)
      rwa [add_sub_cancel] at h1
    refine ⟨ρ + 2, fun x y hxy => ?_⟩
    by_cases hx : ModelSpace.norm s euclidean x ≤ ρ + 1
    · refine Or.inr ⟨x, y, rfl, rfl, rfl, fun μ => ?_, fun μ => ?_⟩
      · have h1 : |(show Fin 4 → ℝ from x) μ| ≤ euclidNormVec x := abs_apply_le_euclidNormVec x μ
        have h2 : euclidNormVec x = ModelSpace.norm s euclidean x := rfl
        linarith
      · have h1 : |(show Fin 4 → ℝ from y) μ| ≤ euclidNormVec y := abs_apply_le_euclidNormVec y μ
        have h2 : euclidNormVec y = ModelSpace.norm s euclidean y := rfl
        have h3 := htri y x
        rw [dsymm y x] at h3
        linarith
    · refine Or.inl ?_
      have h0 := not_le.1 hx
      have h3 := htri x y
      rw [hgrad x (show ρ < ModelSpace.norm s euclidean x by linarith),
        hgrad y (show ρ < ModelSpace.norm s euclidean y by linarith)]
theorem gradOscillation_tendsto_zero (F : SettingFactsHold s M Y) (f : c1CompactSupp s Y univ) :
    Tendsto (gradOscillation f) (𝓝 0) (𝓝 0) := by
  obtain ⟨C, hC⟩ := exists_bounded_lifts F f
  have hcont : Continuous (gradR4 (f.1 ∘ proj s Y)) :=
    continuous_gradR4 ((F.isC1_iff.1 f.1).1 f.2.1)
  have hgrad := (F.isC1_iff.2.1 f.1 f.2.1).1
  have hQ : IsCompact (Icc (fun _ => -C) (fun _ => C) : Set (Fin 4 → ℝ)) := isCompact_Icc
  have huc := hQ.uniformContinuousOn_of_continuous hcont.continuousOn
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨e, he0, heε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hε
  have he0' : (0 : ℝ) < e := by exact_mod_cast he0
  obtain ⟨η, hη, hu⟩ := Metric.uniformContinuousOn_iff.1 huc ((e : ℝ) / 2) (by positivity)
  obtain ⟨δ₀, hδ₀, hδ₁, hδη⟩ : ∃ δ₀ : ℝ≥0, 0 < δ₀ ∧ (δ₀ : ℝ) ≤ 1 ∧ (δ₀ : ℝ) < η := by
    refine ⟨(min 1 (η / 2)).toNNReal, Real.toNNReal_pos.2 (by positivity), ?_, ?_⟩
    · rw [Real.coe_toNNReal _ (by positivity)]
      exact min_le_left _ _
    · rw [Real.coe_toNNReal _ (by positivity)]
      exact (min_le_right _ _).trans_lt (by linarith)
  filter_upwards [Iio_mem_nhds hδ₀] with δ hδ
  refine le_trans ?_ heε.le
  unfold gradOscillation
  refine iSup_le fun x => iSup_le fun y => iSup_le fun hxy => ?_
  have hδ' : (δ : ℝ) < δ₀ := by exact_mod_cast hδ
  rcases hC x y (by linarith) with heq | ⟨u, v, hux, hvy, huv, huC, hvC⟩
  · rw [heq, sub_self, euclidNormVec_zero]
    simp
  · have hgu : grad s Y f.1 x = gradR4 (f.1 ∘ proj s Y) u := by
      rw [← hux]
      exact congrFun hgrad u
    have hgv : grad s Y f.1 y = gradR4 (f.1 ∘ proj s Y) v := by
      rw [← hvy]
      exact congrFun hgrad v
    have hdist : Dist.dist u v < η := by
      rw [dist_eq_norm]
      have h1 := norm_le_euclidNormVec (u - v)
      linarith
    have hmem : ∀ w : Fin 4 → ℝ, (∀ μ, |w μ| ≤ C) → w ∈ Icc (fun _ => -C) (fun _ => C) :=
      fun w hw => ⟨fun μ => (abs_le.1 (hw μ)).1, fun μ => (abs_le.1 (hw μ)).2⟩
    have h2 := hu u (hmem u huC) v (hmem v hvC) hdist
    rw [dist_eq_norm] at h2
    rw [hgu, hgv]
    have h3 := euclidNormVec_le_two_mul_norm (gradR4 (f.1 ∘ proj s Y) u -
      gradR4 (f.1 ∘ proj s Y) v)
    have h4 : euclidNormVec (gradR4 (f.1 ∘ proj s Y) u -
        gradR4 (f.1 ∘ proj s Y) v) ≤ e := by linarith
    exact (ENNReal.ofReal_le_ofReal h4).trans ENNReal.ofReal_coe_nnreal.le
theorem modulusVanishesAtZero (E : SettingFactsHold s M euclidean) (F : SettingFactsHold s M Y)
    (f : c1CompactSupp s Y univ) : ModulusVanishesAtZero M f := by
  have hG : gradSup f < ⊤ := (F.c1_lipschitz.1 f).1
  have hle : ∀ y, ENNReal.ofReal (euclidNormVec (grad s Y f.1 y)) ≤ gradSup f :=
    fun y => le_iSup (fun y => ENNReal.ofReal (euclidNormVec (grad s Y f.1 y))) y
  have hsubE : ∀ u v : Fin 4 → ℝ, euclidNormVec (u - v) ≤ euclidNormVec u + euclidNormVec v := by
    intro u v
    have h1 : ModelSpace.norm s euclidean (u + -v) ≤
        ModelSpace.norm s euclidean u + ModelSpace.norm s euclidean (-v) :=
      E.dist_invariant.1 u (-v)
    have h2 : euclidNormVec (u + -v) ≤ euclidNormVec u + euclidNormVec (-v) := h1
    rwa [euclidNormVec_neg, ← sub_eq_add_neg] at h2
  have hω : ∀ δ : ℝ≥0, gradOscillation f δ ≤ 2 * gradSup f := by
    intro δ
    unfold gradOscillation
    refine iSup_le fun x => iSup_le fun y => iSup_le fun _ => ?_
    calc ENNReal.ofReal (euclidNormVec (grad s Y f.1 x - grad s Y f.1 y))
        ≤ ENNReal.ofReal (euclidNormVec (grad s Y f.1 x) +
            euclidNormVec (grad s Y f.1 y)) := ENNReal.ofReal_le_ofReal (hsubE _ _)
      _ = ENNReal.ofReal (euclidNormVec (grad s Y f.1 x)) +
            ENNReal.ofReal (euclidNormVec (grad s Y f.1 y)) :=
          ENNReal.ofReal_add (euclidNormVec_nonneg _) (euclidNormVec_nonneg _)
      _ ≤ gradSup f + gradSup f := add_le_add (hle x) (hle y)
      _ = 2 * gradSup f := (two_mul _).symm
  have hM : (40 * (M.1 : ℝ≥0∞)) ≠ ⊤ := ENNReal.mul_ne_top (by simp) (ENNReal.natCast_ne_top _)
  refine ⟨fun δ => ⟨hω δ, ?_⟩, ?_⟩
  · refine max_lt (ENNReal.mul_lt_top hG ENNReal.coe_lt_top) ?_
    exact ENNReal.mul_lt_top hM.lt_top
      ((hω δ).trans_lt (ENNReal.mul_lt_top (by simp) hG))
  · have h1 : Tendsto (fun δ : ℝ≥0 => gradSup f * (δ : ℝ≥0∞)) (𝓝 0) (𝓝 0) := by
      have h2 : Tendsto (fun δ : ℝ≥0 => (δ : ℝ≥0∞)) (𝓝 0) (𝓝 ((0 : ℝ≥0) : ℝ≥0∞)) :=
        ENNReal.continuous_coe.tendsto 0
      have h3 := ENNReal.Tendsto.const_mul h2 (Or.inr hG.ne)
      simpa using h3
    have h2 : Tendsto (fun δ : ℝ≥0 => 40 * (M.1 : ℝ≥0∞) * gradOscillation f δ) (𝓝 0) (𝓝 0) := by
      have h3 := ENNReal.Tendsto.const_mul (gradOscillation_tendsto_zero F f) (Or.inr hM)
      simpa using h3
    exact show Tendsto (fun δ : ℝ≥0 => max (gradSup f * (δ : ℝ≥0∞))
        (40 * (M.1 : ℝ≥0∞) * gradOscillation f δ)) (𝓝 0) (𝓝 0) from by
      simpa using h1.max h2
end OnTheSpace
theorem assertions_of_settingFacts (h₁ : SettingFactsHold.statement) : Assertions := fun s M Y =>
  ⟨cutoffBound (h₁ s M Y), isometryInvariance (h₁ s M euclidean) (h₁ s M Y),
    fun f => modulusVanishesAtZero (h₁ s M euclidean) (h₁ s M Y) f⟩
end YangMills.Construction.LatticeLimits.CutoffAndSymmetry
end
