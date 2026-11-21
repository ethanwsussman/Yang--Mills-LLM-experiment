import YangMills.Construction.Torus.BallOfTheTorusAndTheBallOverItProof
import YangMills.Construction.ReflectionPositivity.FactsOnSeparatedTuplesAndIsometriesOfOneTorus
import YangMills.Construction.ReflectionPositivity.FunctionsOfClassC1OnOneTorus
import YangMills.Construction.ReflectionPositivity.ModulusAndTwoParallelMirrors
import YangMills.Construction.ReflectionPositivity.TorusAsAMetricSpaceAndClassesOfTestFunctions
import YangMills.Construction.Torus.CollinearQuadruplesProof
import Mathlib
set_option autoImplicit false
open Filter Set Topology YangMills.Construction.TorusMetric
open scoped ENNReal Matrix
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.TorusCutoffs.ParallelMirrors
private theorem euclidNormVec_nonneg' (u : Fin 4 → ℝ) : 0 ≤ euclidNormVec u := Real.sqrt_nonneg _
private theorem euclidNormVec_sub_le' (u w : Fin 4 → ℝ) :
    euclidNormVec (u - w) ≤ euclidNormVec u + euclidNormVec w := by apply _root_.YangMills.Construction.QuadrupleClasses.Collinear.euclidNormVec_sub_le <;> assumption
private theorem euclidNormVec_transpose_mulVec' {R : Matrix (Fin 4) (Fin 4) ℝ}
    (hR : R ∈ Matrix.orthogonalGroup (Fin 4) ℝ) (u : Fin 4 → ℝ) :
    euclidNormVec (Rᵀ *ᵥ u) = euclidNormVec u := by
  have hRR : R * Rᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (Fin 4) ℝ).mp hR
  have hdot : Rᵀ *ᵥ u ⬝ᵥ Rᵀ *ᵥ u = u ⬝ᵥ u := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.transpose_transpose,
      Matrix.mulVec_mulVec, hRR, Matrix.one_mulVec]
  unfold euclidNormVec
  congr 1
  simpa [dotProduct, sq] using hdot
private theorem mul_lt_of_le_half_div {a ε t : ℝ} (ha : 0 ≤ a) (hε : 0 < ε) (ht₀ : 0 ≤ t)
    (ht : t ≤ ε / (2 * (a + 1))) : a * t < ε := by
  have hhalf : (a + 1) * (ε / (2 * (a + 1))) = ε / 2 := by
    field_simp
  calc a * t ≤ (a + 1) * t := by nlinarith
    _ ≤ (a + 1) * (ε / (2 * (a + 1))) := mul_le_mul_of_nonneg_left ht (by linarith)
    _ = ε / 2 := hhalf
    _ < ε := by linarith
section GradientBounds
variable {s : Conventions.StandingParameters} {f : s.Torus → ℝ}
private theorem gradOscillation_lt_top' (hf : gradSupNorm f < ∞) (δ : ℝ) :
    gradOscillation f δ < ∞ := by
  have hle : gradOscillation f δ ≤ gradSupNorm f + gradSupNorm f := by
    unfold gradOscillation
    refine iSup_le fun x => iSup_le fun x' => iSup_le fun _ => ?_
    calc ENNReal.ofReal (euclidNormVec (grad f x - grad f x'))
        ≤ ENNReal.ofReal (euclidNormVec (grad f x) + euclidNormVec (grad f x')) :=
          ENNReal.ofReal_le_ofReal (euclidNormVec_sub_le' _ _)
      _ = ENNReal.ofReal (euclidNormVec (grad f x)) +
            ENNReal.ofReal (euclidNormVec (grad f x')) :=
          ENNReal.ofReal_add (euclidNormVec_nonneg' _) (euclidNormVec_nonneg' _)
      _ ≤ gradSupNorm f + gradSupNorm f :=
          add_le_add (le_iSup (fun x => ENNReal.ofReal (euclidNormVec (grad f x))) x)
            (le_iSup (fun x => ENNReal.ofReal (euclidNormVec (grad f x))) x')
  exact hle.trans_lt (ENNReal.add_lt_top.mpr ⟨hf, hf⟩)
private theorem euclidNormVec_grad_sub_le (hf : gradSupNorm f < ∞) {δ : ℝ} {x x' : s.Torus}
    (hd : torusDist x x' ≤ δ) :
    euclidNormVec (grad f x - grad f x') ≤ (gradOscillation f δ).toReal := by
  have hle : ENNReal.ofReal (euclidNormVec (grad f x - grad f x')) ≤
      gradOscillation f δ := by
    unfold gradOscillation
    exact le_iSup_of_le x (le_iSup_of_le x' (le_iSup_of_le hd le_rfl))
  exact (ENNReal.ofReal_le_iff_le_toReal (gradOscillation_lt_top' hf δ).ne).mp hle
private theorem gradOscillation_mono' {δ δ' : ℝ} (h : δ ≤ δ') :
    gradOscillation f δ ≤ gradOscillation f δ' := by
  unfold gradOscillation
  exact iSup_mono fun x => iSup_mono fun x' => iSup_le fun hd => le_iSup_of_le (hd.trans h) le_rfl
end GradientBounds
section ModulusFacts
variable (D : TorusData) {f : D.Torus → ℝ}
private theorem sharpScale_nonneg' : 0 ≤ D.sharpScale := by
  unfold TorusData.sharpScale
  positivity
private theorem c1Modulus_eq_max (hf : gradSupNorm f < ∞) {δ : ℝ} (hδ : 0 ≤ δ) :
    D.c1Modulus f δ =
      max ((gradSupNorm f).toReal * δ) (40 * D.sharpScale * (gradOscillation f δ).toReal) := by
  have h₁ : gradSupNorm f * ENNReal.ofReal δ ≠ ∞ := ENNReal.mul_ne_top hf.ne ENNReal.ofReal_ne_top
  have h₂ : ENNReal.ofReal (40 * D.sharpScale) * gradOscillation f δ ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (gradOscillation_lt_top' hf δ).ne
  have h₃ : 0 ≤ 40 * D.sharpScale := mul_nonneg (by norm_num) (sharpScale_nonneg' D)
  unfold TorusData.c1Modulus TorusData.c1ModulusExt
  rw [ENNReal.toReal_max h₁ h₂, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hδ, ENNReal.toReal_ofReal h₃]
private theorem c1Modulus_monotoneOn (hf : gradSupNorm f < ∞) :
    MonotoneOn (D.c1Modulus f) (Ici 0) := by
  intro δ hδ δ' hδ' h
  rw [c1Modulus_eq_max D hf hδ, c1Modulus_eq_max D hf hδ']
  exact max_le_max (mul_le_mul_of_nonneg_left h ENNReal.toReal_nonneg)
    (mul_le_mul_of_nonneg_left
      (ENNReal.toReal_mono (gradOscillation_lt_top' hf δ').ne (gradOscillation_mono' h))
      (mul_nonneg (by norm_num) (sharpScale_nonneg' D)))
private theorem c1Modulus_tendsto_zero (hf : gradSupNorm f < ∞)
    (hu : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x x' : D.Torus, torusDist x x' ≤ δ →
      euclidNormVec (grad f x - grad f x') ≤ ε) :
    Tendsto (D.c1Modulus f) (𝓝[Ici 0] 0) (𝓝 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hM : 0 ≤ 40 * D.sharpScale := mul_nonneg (by norm_num) (sharpScale_nonneg' D)
  have hG : 0 ≤ (gradSupNorm f).toReal := ENNReal.toReal_nonneg
  have hε₁ : 0 < ε / (2 * (40 * D.sharpScale + 1)) := by positivity
  have hε₂ : 0 < ε / (2 * ((gradSupNorm f).toReal + 1)) := by positivity
  obtain ⟨δ₁, hδ₁, h₁⟩ := hu _ hε₁
  refine ⟨min δ₁ (ε / (2 * ((gradSupNorm f).toReal + 1))), lt_min hδ₁ hε₂, fun δ hδ hd => ?_⟩
  have hδ' : (0 : ℝ) ≤ δ := hδ
  have hlt : δ < min δ₁ (ε / (2 * ((gradSupNorm f).toReal + 1))) := by
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg hδ'] at hd
  have hb : (gradOscillation f δ).toReal ≤ ε / (2 * (40 * D.sharpScale + 1)) := by
    refine ENNReal.toReal_le_of_le_ofReal hε₁.le ?_
    unfold gradOscillation
    exact iSup_le fun x => iSup_le fun x' => iSup_le fun h =>
      ENNReal.ofReal_le_ofReal (h₁ x x' (h.trans (hlt.le.trans (min_le_left _ _))))
  have h₂ : (gradSupNorm f).toReal * δ < ε :=
    mul_lt_of_le_half_div hG hε hδ' (hlt.le.trans (min_le_right _ _))
  have h₃ : 40 * D.sharpScale * (gradOscillation f δ).toReal < ε :=
    mul_lt_of_le_half_div hM hε ENNReal.toReal_nonneg hb
  rw [Real.dist_eq, sub_zero, c1Modulus_eq_max D hf hδ',
    abs_of_nonneg (le_max_of_le_left (mul_nonneg hG hδ'))]
  exact max_lt h₂ h₃
end ModulusFacts
private theorem sharpNormShiftLe_of (hC : TorusC1.C1Properties)
    (hT : TorusTuples.SeparationAndSymmetry.Statement) (D : TorusData)
    (hd : FamilyTopology.IsMetricFunction
      (TorusTuples.unitData D.toStandingParameters).torusDist)
    {f : D.Torus → ℝ} (hf : IsC1 (s := D.toStandingParameters) f) :
    SharpNormShiftLe D f := by
  intro u u'
  obtain ⟨⟨hG, -⟩, ⟨hLip, hRL, -⟩, ⟨-, hgrad⟩, -⟩ := hC _ f hf
  obtain ⟨-, -, -, -, -, ⟨-, htr⟩, -, hfun, -⟩ := hT D.toStandingParameters
  have hc1 : ∀ v : D.Torus, IsC1 (s := D.toStandingParameters)
      (TorusTuples.transport (TorusTuples.shiftBy v) f) := fun v =>
    (hfun _ (htr v) f hRL).2.2.2.2.2 hf
  obtain ⟨-, -, -, hdiff⟩ := hC _ _ (hc1 u)
  obtain ⟨hgC1, hgg⟩ := hdiff _ (hc1 u')
  obtain ⟨-, ⟨-, -, hglip⟩, -, -⟩ := hC _ _ hgC1
  have hδ : 0 ≤ torusDist u u' := hd.nonneg u u'
  have hpts : ∀ x : D.Torus, torusDist (x - u) (x - u') = torusDist u u' := fun x => by
    have hswap : torusDist (x - u) (x - u') = torusDist u' u := by
      unfold torusDist
      rw [sub_sub_sub_cancel_left]
    rw [hswap]
    exact hd.symm u' u
  have hb : gradSupNorm (TorusTuples.transport (TorusTuples.shiftBy u) f -
      TorusTuples.transport (TorusTuples.shiftBy u') f) ≤
      ENNReal.ofReal (gradOscillation f (torusDist u u')).toReal := by
    refine iSup_le fun x => ENNReal.ofReal_le_ofReal ?_
    rw [hgg, Pi.sub_apply, hgrad, hgrad]
    exact euclidNormVec_grad_sub_le hG (hpts x).le
  have hlip := hglip.trans (ENNReal.toReal_le_of_le_ofReal ENNReal.toReal_nonneg hb)
  have hsup : TestFunctions.uniformNorm
      (TorusTuples.transport (TorusTuples.shiftBy u) f -
        TorusTuples.transport (TorusTuples.shiftBy u') f) ≤
        (gradSupNorm f).toReal * torusDist u u' := by
    refine ciSup_le fun x => ?_
    rw [Pi.sub_apply, TorusTuples.transport_shiftBy, TorusTuples.transport_shiftBy,
      Real.norm_eq_abs, ← hpts x]
    exact hLip _ _
  rw [c1Modulus_eq_max D hG hδ]
  exact max_le_max hsup (mul_le_mul_of_nonneg_left hlip
    (mul_nonneg (by norm_num) (sharpScale_nonneg' D)))
private theorem modulusIsometryInvariant_of (hC : TorusC1.C1Properties)
    (hT : TorusTuples.SeparationAndSymmetry.Statement) (D : TorusData)
    {f : D.Torus → ℝ} (hf : IsC1 (s := D.toStandingParameters) f) :
    ModulusIsometryInvariant D f := by
  intro r hr δ _
  obtain ⟨-, -, -, -, -, -, hmot, -, -⟩ := hT D.toStandingParameters
  obtain ⟨e, he, hsymm, -⟩ := hmot r hr
  obtain rfl : e = r := Equiv.coe_fn_injective he
  obtain ⟨-, -, -, R, hR, w, hw⟩ := hmot e.symm hsymm
  obtain ⟨-, -, ⟨hact, -⟩, -⟩ := hC _ f hf
  obtain ⟨-, hg⟩ := hact e hr R w hR hw
  have hdist : ∀ x x' : D.Torus, torusDist (e.symm x) (e.symm x') = torusDist x x' := hsymm
  have h₁ : gradSupNorm (TorusTuples.transport e f) = gradSupNorm f := by
    unfold gradSupNorm
    simp only [hg, euclidNormVec_transpose_mulVec' hR]
    exact e.symm.iSup_comp (g := fun x => ENNReal.ofReal (euclidNormVec (grad f x)))
  have h₂ : gradOscillation (TorusTuples.transport e f) δ = gradOscillation f δ := by
    let F : D.Torus → D.Torus → ℝ≥0∞ := fun y y' => ⨆ (_ : torusDist y y' ≤ δ),
      ENNReal.ofReal (euclidNormVec (grad f y - grad f y'))
    have hF : ∀ x x' : D.Torus, (⨆ (_ : torusDist x x' ≤ δ), ENNReal.ofReal
        (euclidNormVec (grad (TorusTuples.transport e f) x -
          grad (TorusTuples.transport e f) x'))) =
          F (e.symm x) (e.symm x') := fun x x' => by
      simp only [F, hg, ← Matrix.mulVec_sub, euclidNormVec_transpose_mulVec' hR, hdist]
    calc gradOscillation (TorusTuples.transport e f) δ = ⨆ x, ⨆ x', F (e.symm x) (e.symm x') := by
          unfold gradOscillation
          simp only [hF]
      _ = ⨆ x, ⨆ y', F (e.symm x) y' := iSup_congr fun x => e.symm.iSup_comp (g := F (e.symm x))
      _ = ⨆ y, ⨆ y', F y y' := e.symm.iSup_comp (g := fun y => ⨆ y', F y y')
      _ = gradOscillation f δ := rfl
  unfold TorusData.c1Modulus TorusData.c1ModulusExt
  rw [h₁, h₂]
section AxisMirrors
variable (s : Conventions.StandingParameters)
private theorem affineReflect_eq_add_shift (μ : Fin 4) (c c' : ℝ) (y : Fin 4 → ℝ) :
    (TorusMirrors.AxisLevel.mk μ c').affineReflect y =
      (TorusMirrors.AxisLevel.mk μ c).affineReflect y + mirrorShift μ c c' := by
  funext ν
  by_cases h : ν = μ
  · subst h
    simp [TorusMirrors.AxisLevel.affineReflect, mirrorShift, PeriodicLattice.coordVec]
    ring
  · simp [TorusMirrors.AxisLevel.affineReflect, mirrorShift, PeriodicLattice.coordVec,
      Pi.single_eq_of_ne h]
private theorem affineReflect_eq_sub_shift (μ : Fin 4) (c c' : ℝ) (y : Fin 4 → ℝ) :
    (TorusMirrors.AxisLevel.mk μ c').affineReflect y =
      (TorusMirrors.AxisLevel.mk μ c).affineReflect (y - mirrorShift μ c c') := by
  funext ν
  by_cases h : ν = μ
  · subst h
    simp [TorusMirrors.AxisLevel.affineReflect, mirrorShift, PeriodicLattice.coordVec]
    ring
  · simp [TorusMirrors.AxisLevel.affineReflect, mirrorShift, PeriodicLattice.coordVec,
      Pi.single_eq_of_ne h]
private theorem proj_sub_eq (y w : Fin 4 → ℝ) :
    proj s (y - w) = proj s y - proj s w := by apply _root_.YangMills.Construction.TorusMeasure.BallProjection.proj_map_sub <;> assumption
variable {s}
private theorem reflect_eq_add_proj (hM : TorusMirrors.AxisReflection.AxisReflectionProperties)
    (μ : Fin 4) (c c' : ℝ) (x : s.Torus) :
    (TorusMirrors.AxisLevel.mk μ c').reflect s x =
      (TorusMirrors.AxisLevel.mk μ c).reflect s x + proj s (mirrorShift μ c c') := by
  obtain ⟨y, rfl⟩ := exists_proj_eq s x
  obtain ⟨⟨-, h, -⟩, -⟩ := hM s (TorusMirrors.AxisLevel.mk μ c)
  obtain ⟨⟨-, h', -⟩, -⟩ := hM s (TorusMirrors.AxisLevel.mk μ c')
  rw [h, h', affineReflect_eq_add_shift μ c c', proj_add]
private theorem reflect_eq_sub_proj (hM : TorusMirrors.AxisReflection.AxisReflectionProperties)
    (μ : Fin 4) (c c' : ℝ) (x : s.Torus) :
    (TorusMirrors.AxisLevel.mk μ c').reflect s x =
      (TorusMirrors.AxisLevel.mk μ c).reflect s (x - proj s (mirrorShift μ c c')) := by
  obtain ⟨y, rfl⟩ := exists_proj_eq s x
  obtain ⟨⟨-, h, -⟩, -⟩ := hM s (TorusMirrors.AxisLevel.mk μ c)
  obtain ⟨⟨-, h', -⟩, -⟩ := hM s (TorusMirrors.AxisLevel.mk μ c')
  rw [← proj_sub_eq, h, h', affineReflect_eq_sub_shift μ c c']
private theorem mem_supp_comp_involution {E : Type} [Zero E] {t : s.Torus → s.Torus}
    (ht : TorusTuples.IsTorusIsometry s t) (hinv : t ∘ t = id) (g : s.Torus → E) (x : s.Torus) :
    x ∈ TorusTuples.supp (s := s) (g ∘ t) ↔ t x ∈ TorusTuples.supp (s := s) g := by
  have hi : ∀ y, t (t y) = y := fun y => congrFun hinv y
  rw [TorusTuples.mem_supp_iff, TorusTuples.mem_supp_iff]
  constructor
  · intro h r hr
    obtain ⟨y, hy, hd⟩ := h r hr
    refine ⟨t y, hy, ?_⟩
    rw [ht x y]
    exact hd
  · intro h r hr
    obtain ⟨z, hz, hd⟩ := h r hr
    refine ⟨t z, by simpa [hi z] using hz, ?_⟩
    have hxz := ht (t x) z
    rw [hi x] at hxz
    rw [hxz]
    exact hd
end AxisMirrors
private theorem parallelMirrorShift_of (hM : TorusMirrors.AxisReflection.AxisReflectionProperties)
    (D : TorusData) (μ : Fin 4) (c c' : ℝ) : ParallelMirrorShift D μ c c' := by
  obtain ⟨⟨-, -, -, -, hact⟩, -⟩ := hM D.toStandingParameters (TorusMirrors.AxisLevel.mk μ c)
  obtain ⟨⟨-, -, hiso', hinv', hact'⟩, -⟩ :=
    hM D.toStandingParameters (TorusMirrors.AxisLevel.mk μ c')
  have hi : ∀ y, (TorusMirrors.AxisLevel.mk μ c').reflect D.toStandingParameters
      ((TorusMirrors.AxisLevel.mk μ c').reflect D.toStandingParameters y) = y :=
    fun y => congrFun hinv' y
  refine ⟨fun E g => ?_, fun E _ g => ?_⟩
  · have ha' : TorusTuples.transport (axisReflectPerm D μ c') g =
        g ∘ (TorusMirrors.AxisLevel.mk μ c').reflect D.toStandingParameters := hact' E g
    have ha : TorusTuples.transport (axisReflectPerm D μ c) g =
        g ∘ (TorusMirrors.AxisLevel.mk μ c).reflect D.toStandingParameters := hact E g
    funext x
    rw [ha', ha, TorusTuples.shiftByVector, TorusTuples.transport_shiftBy, Function.comp_apply,
      Function.comp_apply, reflect_eq_sub_proj hM μ c c' x]
  · have ha' : TorusTuples.transport (axisReflectPerm D μ c') g =
        g ∘ (TorusMirrors.AxisLevel.mk μ c').reflect D.toStandingParameters := hact' E g
    ext x
    rw [ha', mem_supp_comp_involution hiso' hinv' g x]
    constructor
    · intro hx
      refine ⟨(TorusMirrors.AxisLevel.mk μ c).reflect D.toStandingParameters
        ((TorusMirrors.AxisLevel.mk μ c').reflect D.toStandingParameters x), ⟨_, hx, rfl⟩, ?_⟩
      have hx' := reflect_eq_add_proj (s := D.toStandingParameters) hM μ c c'
        ((TorusMirrors.AxisLevel.mk μ c').reflect D.toStandingParameters x)
      rw [hi x] at hx'
      exact hx'.symm
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      have hz' : addVec D.toStandingParameters (axisReflectPerm D μ c z) (mirrorShift μ c c') =
          (TorusMirrors.AxisLevel.mk μ c').reflect D.toStandingParameters z :=
        (reflect_eq_add_proj (s := D.toStandingParameters) hM μ c c' z).symm
      beta_reduce
      rw [hz', hi z]
      exact hz
private theorem torusDist_proj_mirrorShift_le (D : TorusData)
    (hK : CutoffMirrors.TorusMetricSpace.CompactMetricTorus
      (TorusTuples.unitData D.toStandingParameters)) (μ : Fin 4) (c c' : ℝ) :
    torusDist (proj D.toStandingParameters (mirrorShift μ c c')) (0 : D.Torus) ≤ 2 * |c' - c| := by
  have hzero : proj D.toStandingParameters 0 = 0 := by
    have hadd := proj_add D.toStandingParameters 0 0
    rw [add_zero] at hadd
    exact left_eq_add.mp hadd
  have h₃ : torusDist (proj D.toStandingParameters (mirrorShift μ c c'))
      (proj D.toStandingParameters 0) ≤ euclidNormVec (mirrorShift μ c c' - 0) :=
    hK.2.2.1 _ 0
  have hsingle : mirrorShift μ c c' = Pi.single μ (2 * (c' - c)) := by
    funext ν
    by_cases h : ν = μ
    · subst h
      simp [mirrorShift, PeriodicLattice.coordVec]
    · simp [mirrorShift, PeriodicLattice.coordVec, Pi.single_eq_of_ne h]
  rw [hzero, sub_zero, hsingle, InfiniteLattice.euclidNormVec_single, abs_mul, abs_two,
    ← hsingle] at h₃
  exact h₃
private theorem sharpNormParallelLe_of (hC : TorusC1.C1Properties)
    (hM : TorusMirrors.AxisReflection.AxisReflectionProperties)
    (hT : TorusTuples.SeparationAndSymmetry.Statement) (D : TorusData)
    (hK : CutoffMirrors.TorusMetricSpace.CompactMetricTorus
      (TorusTuples.unitData D.toStandingParameters))
    {h : D.Torus → ℝ} (hh : IsC1 (s := D.toStandingParameters) h) (μ : Fin 4) (c c' : ℝ) :
    SharpNormParallelLe D h μ c c' := by
  obtain ⟨⟨hG, -⟩, ⟨-, hRL, -⟩, -, -⟩ := hC _ h hh
  obtain ⟨-, -, -, -, -, -, -, hfun, -⟩ := hT D.toStandingParameters
  obtain ⟨⟨-, -, hiso, -, -⟩, -⟩ := hM D.toStandingParameters (TorusMirrors.AxisLevel.mk μ c)
  have hiso' : TorusTuples.IsTorusIsometry D.toStandingParameters (axisReflectPerm D μ c) := hiso
  have hθ : IsC1 (s := D.toStandingParameters)
      (TorusTuples.transport (axisReflectPerm D μ c) h) :=
    (hfun _ hiso' h hRL).2.2.2.2.2 hh
  have hd := hK.2.1
  have hshift0 : TorusTuples.transport (TorusTuples.shiftBy (0 : D.Torus))
      (TorusTuples.transport (axisReflectPerm D μ c) h) =
      TorusTuples.transport (axisReflectPerm D μ c) h := by
    funext x
    rw [TorusTuples.transport_shiftBy, sub_zero]
  have hdiff : TorusTuples.transport (axisReflectPerm D μ c') h -
      TorusTuples.transport (axisReflectPerm D μ c) h =
      TorusTuples.transport (TorusTuples.shiftBy (proj D.toStandingParameters (mirrorShift μ c c')))
          (TorusTuples.transport (axisReflectPerm D μ c) h) -
        TorusTuples.transport (TorusTuples.shiftBy (0 : D.Torus))
          (TorusTuples.transport (axisReflectPerm D μ c) h) := by
    rw [hshift0, (parallelMirrorShift_of hM D μ c c').1 ℝ h]
    rfl
  have hb := sharpNormShiftLe_of hC hT D hd hθ
    (proj D.toStandingParameters (mirrorShift μ c c')) 0
  unfold SharpNormParallelLe
  rw [hdiff]
  refine hb.trans ?_
  have hle := torusDist_proj_mirrorShift_le D hK μ c c'
  have h0 : 0 ≤ torusDist (proj D.toStandingParameters (mirrorShift μ c c')) (0 : D.Torus) :=
    hd.nonneg _ _
  rw [modulusIsometryInvariant_of hC hT D hh _ hiso' h0]
  exact c1Modulus_monotoneOn D hG h0 (h0.trans hle) hle
theorem modulusProperties_of (h₁ : TorusC1.C1Properties)
    (h₂ : TorusMirrors.AxisReflection.AxisReflectionProperties)
    (h₃ : TorusTuples.SeparationAndSymmetry.Statement)
    (h₄ : CutoffMirrors.TorusMetricSpace.MetricTorusFacts) :
    ModulusProperties := by
  intro D
  have hK := (h₄ (TorusTuples.unitData D.toStandingParameters)).1
  refine ⟨fun f hf => ?_, parallelMirrorShift_of h₂ D, fun h hh μ c c' =>
    sharpNormParallelLe_of h₁ h₂ h₃ D hK hh μ c c'⟩
  obtain ⟨⟨hG, hu⟩, -⟩ := h₁ _ f hf
  exact ⟨⟨c1Modulus_monotoneOn D hG, c1Modulus_tendsto_zero D hG hu⟩,
    sharpNormShiftLe_of h₁ h₃ D hK.2.1 hf, modulusIsometryInvariant_of h₁ h₃ D hf⟩
end YangMills.Construction.ReflectionPositivity.TorusCutoffs.ParallelMirrors
end
