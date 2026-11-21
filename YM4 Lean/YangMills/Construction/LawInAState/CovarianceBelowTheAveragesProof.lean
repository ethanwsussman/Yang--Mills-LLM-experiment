import YangMills.Construction.LawInAState.CovarianceBelowTheAverages
import YangMills.Construction.LawInAState.DominationOnTheLeastTorus
import YangMills.Construction.LawInAState.LawsAreInvariantUnderTranslations
import YangMills.Construction.LawInAState.WilsonsLawIsAProbability
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace YangMills.Construction.StateLaws.CovarianceBoundProof
open ChessboardTori CellAverages
open InfiniteLattice (AmbientSpace)
section Lattice
open InfiniteLattice
variable {a : ℝ}
private def shiftFace (w : LatticePoint a) (p : ElementaryPlaquette a) : ElementaryPlaquette a :=
  ⟨p.corner + w, p.lowAxis, p.highAxis, p.lowAxis_lt_highAxis⟩
private def shiftFaceEquiv (w : LatticePoint a) : ElementaryPlaquette a ≃ ElementaryPlaquette a where
  toFun := shiftFace w
  invFun := shiftFace (-w)
  left_inv p := ElementaryPlaquette.ext (by simp [shiftFace]) rfl rfl
  right_inv p := ElementaryPlaquette.ext (by simp [shiftFace]) rfl rfl
private theorem center_shiftFace (w : LatticePoint a) (p : ElementaryPlaquette a) :
    (shiftFace w p).center = p.center + (w : AmbientSpace) := by
  simp only [shiftFace, ElementaryPlaquette.center, AddSubgroup.coe_add]
  abel
private theorem linkMap_forwardFrom (w x : LatticePoint a) (ν : Fin 4) :
    (InfiniteLattice.shift w).linkMap (Link.forwardFrom x ν) = Link.forwardFrom (x + w) ν := by
  refine Link.ext rfl (Subtype.ext ?_)
  change ((x + axisStep a ν : LatticePoint a) : AmbientSpace) + (w : AmbientSpace) =
    ((x + w + axisStep a ν : LatticePoint a) : AmbientSpace)
  simp only [AddSubgroup.coe_add]
  abel
abbrev _root_.YangMills.SharedProofs.p433 := @linkMap_forwardFrom
private theorem faceHolonomy_pullback (w : LatticePoint a) (U : GaugeField a)
    (p : ElementaryPlaquette a) :
    faceHolonomy ((InfiniteLattice.shift w).pullbackField U) p =
      faceHolonomy U (shiftFace w p) := by
  have e₁ : p.corner + axisStep a p.lowAxis + w = p.corner + w + axisStep a p.lowAxis :=
    add_right_comm _ _ _
  have e₂ : p.corner + axisStep a p.highAxis + w = p.corner + w + axisStep a p.highAxis :=
    add_right_comm _ _ _
  have h : ∀ b, ((InfiniteLattice.shift w).pullbackField U) b =
      U ((InfiniteLattice.shift w).linkMap b) := fun _ => rfl
  unfold faceHolonomy
  simp only [h, linkMap_forwardFrom, e₁, e₂, shiftFace]
private theorem smearedEnergy_pullback (f : AmbientSpace → ℝ) (w : LatticePoint a)
    (U : GaugeField a) :
    smearedEnergy f ((InfiniteLattice.shift w).pullbackField U) =
      smearedEnergy (fun x => f (x - (w : AmbientSpace))) U := by
  unfold smearedEnergy
  rw [← finsum_comp_equiv (shiftFaceEquiv w)
    (f := fun p => faceEnergy U p • f (p.center - (w : AmbientSpace)))]
  refine finsum_congr fun p => ?_
  change _ = faceEnergy U (shiftFace w p) •
    f ((shiftFace w p).center - (w : AmbientSpace))
  rw [center_shiftFace, add_sub_cancel_right]
  unfold faceEnergy
  rw [faceHolonomy_pullback]
private theorem center_apply (p : ElementaryPlaquette a) (ν : Fin 4) :
    p.center ν = (p.corner : AmbientSpace) ν + (if ν = p.lowAxis then a / 2 else 0) +
      (if ν = p.highAxis then a / 2 else 0) := by
  simp [ElementaryPlaquette.center, Pi.single_apply]
private theorem axisStep_apply (i ν : Fin 4) :
    ((axisStep a i : LatticePoint a) : AmbientSpace) ν = if ν = i then a else 0 := by
  simp [axisStep, Pi.single_apply]
abbrev _root_.YangMills.SharedProofs.p59492 := @axisStep_apply
private theorem corners_near_center (ha : 0 < a) (p : ElementaryPlaquette a) (ν : Fin 4) :
    |((p.corner : LatticePoint a) : AmbientSpace) ν - p.center ν| ≤ a ∧
    |((p.corner + axisStep a p.lowAxis : LatticePoint a) : AmbientSpace) ν - p.center ν| ≤ a ∧
    |((p.corner + axisStep a p.highAxis : LatticePoint a) : AmbientSpace) ν - p.center ν| ≤ a ∧
    |((p.corner + axisStep a p.lowAxis + axisStep a p.highAxis : LatticePoint a) : AmbientSpace) ν -
      p.center ν| ≤ a ∧
    |((p.corner + axisStep a p.highAxis + axisStep a p.lowAxis : LatticePoint a) : AmbientSpace) ν -
      p.center ν| ≤ a := by
  have hb := center_apply p ν
  simp only [AddSubgroup.coe_add, Pi.add_apply, axisStep_apply]
  rw [hb]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> split_ifs <;> rw [abs_le] <;> constructor <;> linarith
private theorem finite_faces_in_box (ha : 0 < a) (lo hi : AmbientSpace) :
    {p : ElementaryPlaquette a | ∀ ν, lo ν ≤ p.center ν ∧ p.center ν ≤ hi ν}.Finite := by
  classical
  let T : Finset (Fin 4 → ℤ) :=
    Fintype.piFinset fun ν => Finset.Icc ⌈(lo ν - a) / a⌉ ⌊hi ν / a⌋
  let ι : ElementaryPlaquette a → AmbientSpace × Fin 4 × Fin 4 :=
    fun p => ((p.corner : AmbientSpace), p.lowAxis, p.highAxis)
  refine Set.Finite.of_finite_image (f := ι) ?_ (Function.Injective.injOn ?_)
  · have hT : ((fun n : Fin 4 → ℤ => (fun ν => (n ν : ℝ) * a : AmbientSpace)) ''
        (T : Set _)).Finite :=
      T.finite_toSet.image _
    refine (hT.prod (Set.finite_univ (α := Fin 4 × Fin 4))).subset ?_
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨n, hn⟩ := p.corner.2
    refine ⟨⟨n, ?_, funext fun ν => (hn ν).symm⟩, mem_univ _⟩
    simp only [T, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc]
    intro ν
    have hb := center_apply p ν
    have hp' := hp ν
    have hn' := hn ν
    have hs : 0 ≤ (if ν = p.lowAxis then a / 2 else 0) + (if ν = p.highAxis then a / 2 else 0) ∧
        (if ν = p.lowAxis then a / 2 else 0) + (if ν = p.highAxis then a / 2 else 0) ≤ a := by
      split_ifs <;> constructor <;> linarith
    constructor
    · rw [Int.ceil_le, div_le_iff₀ ha]
      linarith [hp'.1, hs.2]
    · rw [Int.le_floor, le_div_iff₀ ha]
      linarith [hp'.2, hs.1]
  · intro p q h
    simp only [ι, Prod.mk.injEq] at h
    exact ElementaryPlaquette.ext (Subtype.ext h.1) h.2.1 h.2.2
end Lattice
section Algebra
open InfiniteLattice (ElementaryPlaquette faceEnergy faceHolonomy smearedEnergy axisStep)
variable {D : ChessboardSetup} {O : Set AmbientSpace}
private def RealObs (D : ChessboardSetup) (O : Set AmbientSpace) (G : D.GaugeField → ℝ) : Prop :=
  (fun U => (G U : ℂ)) ∈ D.linkAlgebra O
private theorem RealObs.const (c : ℝ) : RealObs D O fun _ => c :=
  ⟨fun _ => (c : ℂ), measurable_const, ⟨‖(c : ℂ)‖, fun _ => le_rfl⟩, fun _ => rfl⟩
private theorem RealObs.add {G H : D.GaugeField → ℝ} (hG : RealObs D O G) (hH : RealObs D O H) :
    RealObs D O fun U => G U + H U := by
  obtain ⟨Φ, hΦ, ⟨C, hC⟩, e⟩ := hG
  obtain ⟨Ψ, hΨ, ⟨C', hC'⟩, e'⟩ := hH
  refine ⟨fun u => Φ u + Ψ u, hΦ.add hΨ,
    ⟨C + C', fun u => (norm_add_le _ _).trans (add_le_add (hC u) (hC' u))⟩, fun U => ?_⟩
  change ((G U + H U : ℝ) : ℂ) = _
  rw [Complex.ofReal_add]
  exact congrArg₂ (· + ·) (e U) (e' U)
private theorem RealObs.mul {G H : D.GaugeField → ℝ} (hG : RealObs D O G) (hH : RealObs D O H) :
    RealObs D O fun U => G U * H U := by
  obtain ⟨Φ, hΦ, ⟨C, hC⟩, e⟩ := hG
  obtain ⟨Ψ, hΨ, ⟨C', hC'⟩, e'⟩ := hH
  refine ⟨fun u => Φ u * Ψ u, hΦ.mul hΨ, ⟨|C| * |C'|, fun u => (norm_mul_le _ _).trans
    (mul_le_mul ((hC u).trans (le_abs_self C)) ((hC' u).trans (le_abs_self C')) (norm_nonneg _)
      (abs_nonneg _))⟩, fun U => ?_⟩
  change ((G U * H U : ℝ) : ℂ) = _
  rw [Complex.ofReal_mul]
  exact congrArg₂ (· * ·) (e U) (e' U)
private theorem RealObs.sub_const {G : D.GaugeField → ℝ} (hG : RealObs D O G) (c : ℝ) :
    RealObs D O fun U => G U - c := by
  simpa [sub_eq_add_neg] using hG.add (RealObs.const (-c))
private theorem RealObs.sum {ι : Type*} (s : Finset ι) {G : ι → D.GaugeField → ℝ}
    (h : ∀ i ∈ s, RealObs D O (G i)) : RealObs D O fun U => ∑ i ∈ s, G i U := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using RealObs.const (D := D) (O := O) 0
  | insert i s hi ih =>
    have := (h i (Finset.mem_insert_self i s)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
    simpa [Finset.sum_insert hi] using this
private theorem RealObs.shiftAverage (m : ℕ) {G : (Fin 4 → ℤ) → D.GaugeField → ℝ}
    (h : ∀ v ∈ shiftSet m, RealObs D O (G v)) :
    RealObs D O fun U => CellAverages.shiftAverage m fun v => G v U := by
  unfold CellAverages.shiftAverage
  exact (RealObs.const _).mul (RealObs.sum _ h)
private theorem RealObs.integrable {G : D.GaugeField → ℝ} (hG : RealObs D O G)
    (μ : Measure D.GaugeField) [IsProbabilityMeasure μ] : Integrable G μ := by
  obtain ⟨hm, C, hC⟩ := D.isBoundedObservable_of_mem_linkAlgebra hG
  have hm' : Measurable fun U => ((G U : ℂ)).re := Complex.measurable_re.comp hm
  have hm'' : Measurable G := by simpa using hm'
  exact Integrable.of_bound hm''.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun U => by simpa using hC U)
private def wilsonEnergy (V : Matrices.ComplexMatrix2.specialUnitary) : ℝ :=
  1 - (1 / 2) * (Matrices.ComplexMatrix2.fullTrace (V : Matrices.ComplexMatrix2)).re
private theorem continuous_wilsonEnergy : Continuous wilsonEnergy :=
  continuous_const.sub (continuous_const.mul
    (Complex.continuous_re.comp continuous_subtype_val.matrix_trace))
private theorem abs_wilsonEnergy_le (V : Matrices.ComplexMatrix2.specialUnitary) :
    |wilsonEnergy V| ≤ 2 := by
  have hU : (V : Matrices.ComplexMatrix2) ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    (Matrix.mem_specialUnitaryGroup_iff.1 V.2).1
  have h0 := entry_norm_bound_of_unitary hU 0 0
  have h1 := entry_norm_bound_of_unitary hU 1 1
  have htr : Matrices.ComplexMatrix2.fullTrace (V : Matrices.ComplexMatrix2) =
      (V : Matrices.ComplexMatrix2) 0 0 + (V : Matrices.ComplexMatrix2) 1 1 := by
    simp [Matrices.ComplexMatrix2.fullTrace, Matrix.trace_fin_two]
  have hre : |(Matrices.ComplexMatrix2.fullTrace (V : Matrices.ComplexMatrix2)).re| ≤ 2 := by
    rw [htr, Complex.add_re]
    have a0 := Complex.abs_re_le_norm ((V : Matrices.ComplexMatrix2) 0 0)
    have a1 := Complex.abs_re_le_norm ((V : Matrices.ComplexMatrix2) 1 1)
    exact (abs_add_le _ _).trans (by linarith)
  have := abs_le.1 hre
  unfold wilsonEnergy
  rw [abs_le]
  constructor <;> linarith [this.1, this.2]
private theorem realObs_faceEnergy (p : ElementaryPlaquette D.mesh)
    (h₁ : InfiniteLattice.Link.forwardFrom p.corner p.lowAxis ∈ D.positiveLinksOn O)
    (h₂ : InfiniteLattice.Link.forwardFrom (p.corner + axisStep D.mesh p.lowAxis) p.highAxis ∈
      D.positiveLinksOn O)
    (h₃ : InfiniteLattice.Link.forwardFrom (p.corner + axisStep D.mesh p.highAxis) p.lowAxis ∈
      D.positiveLinksOn O)
    (h₄ : InfiniteLattice.Link.forwardFrom p.corner p.highAxis ∈ D.positiveLinksOn O) :
    RealObs D O fun U => faceEnergy U p := by
  have : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  have : SecondCountableTopology Matrices.ComplexMatrix2.specialUnitary :=
    TopologicalSpace.Subtype.secondCountableTopology _
  let b₁ : D.positiveLinksOn O := ⟨_, h₁⟩
  let b₂ : D.positiveLinksOn O := ⟨_, h₂⟩
  let b₃ : D.positiveLinksOn O := ⟨_, h₃⟩
  let b₄ : D.positiveLinksOn O := ⟨_, h₄⟩
  let w : Matrices.ComplexMatrix2.specialUnitary × Matrices.ComplexMatrix2.specialUnitary ×
      Matrices.ComplexMatrix2.specialUnitary × Matrices.ComplexMatrix2.specialUnitary → ℝ :=
    fun q => wilsonEnergy (q.1 * q.2.1 * q.2.2.1⁻¹ * q.2.2.2⁻¹)
  have hw : Continuous w := continuous_wilsonEnergy.comp (by fun_prop)
  let r : (D.positiveLinksOn O → Conventions.StandingParameters.gaugeGroup) →
      Matrices.ComplexMatrix2.specialUnitary × Matrices.ComplexMatrix2.specialUnitary ×
        Matrices.ComplexMatrix2.specialUnitary × Matrices.ComplexMatrix2.specialUnitary :=
    fun u => (u b₁, u b₂, u b₃, u b₄)
  have hr : Measurable r := (measurable_pi_apply b₁).prodMk ((measurable_pi_apply b₂).prodMk
    ((measurable_pi_apply b₃).prodMk (measurable_pi_apply b₄)))
  refine ⟨fun u => (w (r u) : ℂ), ?_, ⟨2, fun u => ?_⟩, fun U => rfl⟩
  · exact Complex.measurable_ofReal.comp (hw.measurable.comp hr)
  · simpa using abs_wilsonEnergy_le _
private theorem realObs_smearedEnergy (f : AmbientSpace → ℝ)
    (hfin : {p : ElementaryPlaquette D.mesh | f p.center ≠ 0}.Finite)
    (hp : ∀ p : ElementaryPlaquette D.mesh, f p.center ≠ 0 → ∀ x : AmbientSpace,
      (∀ ν, |x ν - p.center ν| ≤ D.mesh) → x ∈ O) :
    RealObs D O fun U => smearedEnergy f U := by
  have e : ∀ U : D.GaugeField, smearedEnergy f U =
      ∑ p ∈ hfin.toFinset, faceEnergy U p * f p.center := by
    intro U
    unfold InfiniteLattice.smearedEnergy
    refine finsum_eq_sum_of_support_subset _ fun p hp' => ?_
    simp only [Set.Finite.coe_toFinset, Set.mem_ofPred_eq]
    intro h0
    apply hp'
    simp [h0]
  have hlink : ∀ (x : InfiniteLattice.LatticePoint D.mesh) (i : Fin 4), (x : AmbientSpace) ∈ O →
      ((InfiniteLattice.Link.forwardFrom x i).terminal : AmbientSpace) ∈ O →
      InfiniteLattice.Link.forwardFrom x i ∈ D.positiveLinksOn O :=
    fun x i h h' => D.mem_positiveLinksOn_iff.2 ⟨⟨x, i, rfl⟩, h, h'⟩
  have hs : RealObs D O fun U => ∑ p ∈ hfin.toFinset, faceEnergy U p * f p.center := by
    refine RealObs.sum _ fun p hmem => ?_
    have hne : f p.center ≠ 0 := by simpa using hmem
    have c := fun ν => corners_near_center D.mesh_pos p ν
    have o₀ := hp p hne _ fun ν => (c ν).1
    have o₁ := hp p hne _ fun ν => (c ν).2.1
    have o₂ := hp p hne _ fun ν => (c ν).2.2.1
    have o₃ := hp p hne _ fun ν => (c ν).2.2.2.1
    have o₄ := hp p hne _ fun ν => (c ν).2.2.2.2
    exact (realObs_faceEnergy p (hlink _ _ o₀ o₁) (hlink _ _ o₁ o₃) (hlink _ _ o₂ o₄)
      (hlink _ _ o₀ o₂)).mul (RealObs.const _)
  have he : (fun U : D.GaugeField => smearedEnergy f U) =
      fun U : D.GaugeField => ∑ p ∈ hfin.toFinset, faceEnergy U p * f p.center :=
    funext e
  rw [he]
  exact hs
private theorem realObs_of_isDeepInCell (g : ReflectionGrid D) (hq : g.q = 0)
    {f : AmbientSpace → ℝ} (hf : IsDeepInCell g f) :
    RealObs D (interior (g.cell 0)) (smearedObservable D.L D.K f) := by
  have ha := D.mesh_pos
  have hside : g.cellSide = 1 := by simp [ReflectionGrid.cellSide, hq]
  have hsub : {x : AmbientSpace | ∀ ν, 0 < x ν - g.origin ν ∧ x ν - g.origin ν < 1} ⊆
      interior (g.cell 0) := by
    refine interior_maximal (fun x hx => ?_) ?_
    · change ∀ ν, x ν - (g.origin ν + g.cellSide * (((0 : Fin 4 → ℤ) ν : ℤ) : ℝ)) ∈
        Icc 0 g.cellSide
      intro ν
      simp only [hside, Pi.zero_apply, Int.cast_zero, mul_zero, add_zero]
      exact ⟨(hx ν).1.le, (hx ν).2.le⟩
    · have e : {x : AmbientSpace | ∀ ν, 0 < x ν - g.origin ν ∧ x ν - g.origin ν < 1} =
          ⋂ ν, (fun x : AmbientSpace => x ν - g.origin ν) ⁻¹' Ioo 0 1 := by
        ext x
        simp [Set.mem_iInter]
      rw [e]
      exact isOpen_iInter_of_finite fun ν =>
        isOpen_Ioo.preimage ((continuous_apply ν).sub continuous_const)
  have hin : ∀ p : ElementaryPlaquette D.mesh, f p.center ≠ 0 → ∀ ν,
      2 * D.mesh ≤ p.center ν - g.origin ν ∧ p.center ν - g.origin ν ≤ 1 - 2 * D.mesh :=
    fun p hp => hf _ (subset_tsupport f hp)
  refine realObs_smearedEnergy f
    ((finite_faces_in_box ha g.origin fun ν => g.origin ν + 1).subset fun p hp ν => ?_)
    fun p hp x hx => hsub fun ν => ?_
  · have h1 := hin p hp ν
    constructor <;> linarith [h1.1, h1.2]
  · have h1 := hin p hp ν
    have h2 := abs_le.1 (hx ν)
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
private def shiftPoint (D : ChessboardSetup) (k : ℕ) (v : Fin 4 → ℤ) :
    InfiniteLattice.LatticePoint D.mesh :=
  ⟨latticeShift D.L D.K k v, fun ν => v ν * (D.L : ℤ) ^ k, fun ν => by
    simp only [latticeShift, ChessboardSetup.mesh, PeriodicLattice.meshSize, zpow_neg,
      zpow_natCast]
    push_cast
    ring⟩
private theorem smearedObservable_translateBy (D : ChessboardSetup) (k : ℕ) (v : Fin 4 → ℤ)
    (f : AmbientSpace → ℝ) (U : D.GaugeField) :
    smearedObservable D.L D.K (translateBy D.L D.K k v f) U =
      smearedObservable D.L D.K f
        ((InfiniteLattice.shift (shiftPoint D k v)).pullbackField U) :=
  (smearedEnergy_pullback f (shiftPoint D k v) U).symm
private theorem integral_pullback {μ : Measure D.GaugeField}
    {s : InfiniteLattice.LatticeSymmetry D.mesh} (hinv : InfiniteLattice.IsSymmetricUnder μ s)
    {G : D.GaugeField → ℝ} (hG : RealObs D O G) :
    ∫ U, G (s.pullbackField U) ∂μ = ∫ U, G U ∂μ := by
  have h : ∫ U, ((G (s.pullbackField U) : ℝ) : ℂ) ∂μ = ∫ U, ((G U : ℝ) : ℂ) ∂μ :=
    hinv (fun U => (G U : ℂ)) (D.isBoundedObservable_of_mem_linkAlgebra hG)
  rw [integral_complex_ofReal, integral_complex_ofReal] at h
  exact_mod_cast h
end Algebra
section Means
variable {Ω : Type*} [MeasurableSpace Ω]
private theorem zero_mem_shiftSet (m : ℕ) : (0 : Fin 4 → ℤ) ∈ shiftSet m := by
  simp [shiftSet, Fintype.mem_piFinset]
private theorem shiftAverage_eq_const (m : ℕ) {F : (Fin 4 → ℤ) → ℝ} {c : ℝ}
    (h : ∀ v ∈ shiftSet m, F v = c) : CellAverages.shiftAverage m F = c := by
  have hc : ((shiftSet m).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.2 ⟨0, zero_mem_shiftSet m⟩).ne'
  unfold CellAverages.shiftAverage
  rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul]
  field_simp
private theorem integral_shiftAverage (μ : Measure Ω) (m : ℕ)
    {G : (Fin 4 → ℤ) → Ω → ℝ} (h : ∀ v ∈ shiftSet m, Integrable (G v) μ) :
    ∫ ω, CellAverages.shiftAverage m (fun v => G v ω) ∂μ =
      CellAverages.shiftAverage m fun v => ∫ ω, G v ω ∂μ := by
  unfold CellAverages.shiftAverage
  rw [integral_const_mul, integral_finsetSum _ h]
private theorem covariance_eq_of_shifted (μ : Measure Ω) [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (c c' : ℝ) (hX : Integrable X μ) (hY : Integrable Y μ)
    (hP : Integrable (fun ω => (X ω - c) * (Y ω - c')) μ) :
    cov[X, Y; μ] =
      (∫ ω, (X ω - c) * (Y ω - c') ∂μ) - (∫ ω, (X ω - c) ∂μ) * ∫ ω, (Y ω - c') ∂μ := by
  have hT : Integrable (fun ω => X ω - c) μ := hX.sub (integrable_const c)
  have hT' : Integrable (fun ω => Y ω - c') μ := hY.sub (integrable_const c')
  have eT : ∫ ω, (X ω - c) ∂μ = (∫ ω, X ω ∂μ) - c := by
    rw [integral_sub hX (integrable_const c)]
    simp
  have eT' : ∫ ω, (Y ω - c') ∂μ = (∫ ω, Y ω ∂μ) - c' := by
    rw [integral_sub hY (integrable_const c')]
    simp
  obtain ⟨α, hα⟩ : ∃ α, α = ∫ ω, (X ω - c) ∂μ := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β, β = ∫ ω, (Y ω - c') ∂μ := ⟨_, rfl⟩
  have hXe : ∫ ω, X ω ∂μ = α + c := by linarith
  have hYe : ∫ ω, Y ω ∂μ = β + c' := by linarith
  have e : ∀ ω, (X ω - ∫ x, X x ∂μ) * (Y ω - ∫ x, Y x ∂μ) =
      (X ω - c) * (Y ω - c') - α * (Y ω - c') - β * (X ω - c) + α * β := by
    intro ω
    rw [hXe, hYe]
    ring
  unfold covariance
  simp only [e]
  have i₁ : Integrable (fun ω => (X ω - c) * (Y ω - c') - α * (Y ω - c')) μ :=
    hP.sub (hT'.const_mul α)
  have i₂ : Integrable
      (fun ω => (X ω - c) * (Y ω - c') - α * (Y ω - c') - β * (X ω - c)) μ :=
    i₁.sub (hT.const_mul β)
  rw [integral_add i₂ (integrable_const _), integral_sub i₁ (hT.const_mul β),
    integral_sub hP (hT'.const_mul α), integral_const_mul, integral_const_mul, ← hα, ← hβ]
  simp
  ring
end Means
private theorem holdsOnParameters_mono {P Q : RenormalizationStepParameters.ParameterAssignment → ℝ → Prop}
    (h : ResponseInTheExpansion.HoldsOnParameterFamilies P) (hPQ : ∀ T y, P T y → Q T y) :
    ResponseInTheExpansion.HoldsOnParameterFamilies Q := by
  intro a ha
  obtain ⟨L₀, rt₀, C₀, h0, h1⟩ := h a ha
  refine ⟨L₀, rt₀, C₀, h0, fun L hL hL0 T e₁ e₂ e₃ e₄ e₅ e₆ e₇ => ?_⟩
  obtain ⟨y₀, hy⟩ := h1 L hL hL0 T e₁ e₂ e₃ e₄ e₅ e₆ e₇
  exact ⟨y₀, fun y e₈ e₉ e₁₀ => hPQ T y (hy y e₈ e₉ e₁₀)⟩
abbrev _root_.YangMills.SharedProofs.p25084 := @holdsOnParameters_mono
private theorem averages_mem_and_means {D : ChessboardSetup} (g : ReflectionGrid D) (hg : g.q = 0)
    (k m : ℕ) (f h : AmbientSpace → ℝ) (cf ch κ : ℝ)
    (hwell : ∀ v ∈ shiftSet m, IsDeepInCell g (translateBy D.L D.K k v f) ∧
      IsDeepInCell g (translateBy D.L D.K k v h))
    (μ : Measure D.GaugeField) [IsProbabilityMeasure μ]
    (hinv : ∀ v : Fin 4 → ℤ,
      InfiniteLattice.IsSymmetricUnder μ (InfiniteLattice.shift (shiftPoint D k v))) :
    RealObs D (interior (g.cell 0)) (smearedObservable D.L D.K f) ∧
    RealObs D (interior (g.cell 0)) (smearedObservable D.L D.K h) ∧
    RealObs D (interior (g.cell 0)) (fun U : D.GaugeField => CellAverages.shiftAverage m fun v =>
      (smearedObservable D.L D.K (translateBy D.L D.K k v f) U - cf) *
        (smearedObservable D.L D.K (translateBy D.L D.K k v h) U - ch) - κ) ∧
    RealObs D (interior (g.cell 0)) (fun U : D.GaugeField => CellAverages.shiftAverage m fun v =>
      smearedObservable D.L D.K (translateBy D.L D.K k v f) U - cf) ∧
    RealObs D (interior (g.cell 0)) (fun U : D.GaugeField => CellAverages.shiftAverage m fun v =>
      smearedObservable D.L D.K (translateBy D.L D.K k v h) U - ch) ∧
    (∫ U : D.GaugeField, (CellAverages.shiftAverage m fun v =>
      (smearedObservable D.L D.K (translateBy D.L D.K k v f) U - cf) *
        (smearedObservable D.L D.K (translateBy D.L D.K k v h) U - ch) - κ) ∂μ) =
      (∫ U : D.GaugeField, (smearedObservable D.L D.K f U - cf) *
        (smearedObservable D.L D.K h U - ch) ∂μ) - κ ∧
    (∫ U : D.GaugeField, (CellAverages.shiftAverage m fun v =>
      smearedObservable D.L D.K (translateBy D.L D.K k v f) U - cf) ∂μ) =
      ∫ U : D.GaugeField, (smearedObservable D.L D.K f U - cf) ∂μ ∧
    (∫ U : D.GaugeField, (CellAverages.shiftAverage m fun v =>
      smearedObservable D.L D.K (translateBy D.L D.K k v h) U - ch) ∂μ) =
      ∫ U : D.GaugeField, (smearedObservable D.L D.K h U - ch) ∂μ := by
  have hs0 : latticeShift D.L D.K k 0 = 0 := funext fun i => by simp [latticeShift]
  have hv0 : ∀ φ : AmbientSpace → ℝ, translateBy D.L D.K k 0 φ = φ := fun φ => funext fun x => by
    simp [translateBy, hs0]
  have h0 := zero_mem_shiftSet m
  have hOf : ∀ v ∈ shiftSet m, RealObs D (interior (g.cell 0))
      (smearedObservable D.L D.K (translateBy D.L D.K k v f)) :=
    fun v hv => realObs_of_isDeepInCell g hg (hwell v hv).1
  have hOh : ∀ v ∈ shiftSet m, RealObs D (interior (g.cell 0))
      (smearedObservable D.L D.K (translateBy D.L D.K k v h)) :=
    fun v hv => realObs_of_isDeepInCell g hg (hwell v hv).2
  have hf0 : RealObs D (interior (g.cell 0)) (smearedObservable D.L D.K f) := by
    have := hOf 0 h0
    rwa [hv0] at this
  have hh0 : RealObs D (interior (g.cell 0)) (smearedObservable D.L D.K h) := by
    have := hOh 0 h0
    rwa [hv0] at this
  have hT := hf0.sub_const cf
  have hT' := hh0.sub_const ch
  have hA : ∀ v ∈ shiftSet m, RealObs D (interior (g.cell 0)) (fun U : D.GaugeField =>
      smearedObservable D.L D.K (translateBy D.L D.K k v f) U - cf) :=
    fun v hv => (hOf v hv).sub_const cf
  have hB : ∀ v ∈ shiftSet m, RealObs D (interior (g.cell 0)) (fun U : D.GaugeField =>
      smearedObservable D.L D.K (translateBy D.L D.K k v h) U - ch) :=
    fun v hv => (hOh v hv).sub_const ch
  have hAB : ∀ v ∈ shiftSet m, RealObs D (interior (g.cell 0)) (fun U : D.GaugeField =>
      (smearedObservable D.L D.K (translateBy D.L D.K k v f) U - cf) *
        (smearedObservable D.L D.K (translateBy D.L D.K k v h) U - ch)) :=
    fun v hv => (hA v hv).mul (hB v hv)
  refine ⟨hf0, hh0, RealObs.shiftAverage m fun v hv => (hAB v hv).sub_const κ,
    RealObs.shiftAverage m hA, RealObs.shiftAverage m hB, ?_, ?_, ?_⟩
  · rw [integral_shiftAverage μ m fun v hv => ((hAB v hv).sub_const κ).integrable μ]
    refine shiftAverage_eq_const m fun v hv => ?_
    rw [integral_sub ((hAB v hv).integrable μ) (integrable_const κ)]
    have := integral_pullback (hinv v) (hT.mul hT')
    simp only [← smearedObservable_translateBy] at this
    rw [this]
    simp
  · rw [integral_shiftAverage μ m fun v hv => (hA v hv).integrable μ]
    refine shiftAverage_eq_const m fun v hv => ?_
    have := integral_pullback (hinv v) hT
    simpa only [← smearedObservable_translateBy] using this
  · rw [integral_shiftAverage μ m fun v hv => (hB v hv).integrable μ]
    refine shiftAverage_eq_const m fun v hv => ?_
    have := integral_pullback (hinv v) hT'
    simpa only [← smearedObservable_translateBy] using this
private theorem abs_sub_mul_le {IF IA IB Rn mF mA mB : ℝ} (bF : |IF| ≤ Rn * mF)
    (bA : |IA| ≤ Rn * mA) (bB : |IB| ≤ Rn * mB) :
    |IF - IA * IB| ≤ Rn * mF + Rn ^ 2 * mA * mB := by
  have h1 : |IA * IB| ≤ (Rn * mA) * (Rn * mB) := by
    rw [abs_mul]
    exact mul_le_mul bA bB (abs_nonneg _) ((abs_nonneg _).trans bA)
  have h2 := abs_add_le IF (-(IA * IB))
  rw [abs_neg, ← sub_eq_add_neg] at h2
  calc |IF - IA * IB| ≤ |IF| + |IA * IB| := h2
    _ ≤ Rn * mF + (Rn * mA) * (Rn * mB) := add_le_add bF h1
    _ = Rn * mF + Rn ^ 2 * mA * mB := by ring
private theorem covariance_sub_eq {c P Tf Th κ IF IA IB : ℝ} (hc : c = P - Tf * Th)
    (eF : IF = P - κ) (eA : IA = Tf) (eB : IB = Th) : c - κ = IF - IA * IB := by
  rw [hc, eF, eA, eB]
  ring
theorem covarianceBoundByAverages (hDom : cellDominationStatement)
    (hInv : translationInvarianceStatement)
    (hProb : WilsonLaw.LiftedWilsonMeasureIsProbability) :
    covarianceBoundByAveragesStatement := by
  have h₁ : ResponseInTheExpansion.HoldsOnParameterFamilies _ := hDom
  refine holdsOnParameters_mono h₁ fun Tb y hTb Xi hXi => ?_
  obtain ⟨Rn, hRn, hD⟩ := hTb Xi hXi
  refine ⟨Rn, hRn, fun D hL hdat g hg k m d vt _ _ _ _ f h _ hwell μ hμ => ?_⟩
  have hL1 : 1 < D.L := by
    have := D.isAdmissible.2
    omega
  have : IsProbabilityMeasure μ := by
    rcases hμ with h' | ⟨e, he⟩
    · exact (show InfiniteLattice.IsPeriodicGibbs _ _ from h').1.1
    · have h2 := hProb D.L e D.K D.β hL1
      rw [← he] at h2
      exact h2
  obtain ⟨hf, hh, hF, hA, hB, eF, eA, eB⟩ := averages_mem_and_means g hg k m f h
    (unitTorusMean D.L D.K D.β f) (unitTorusMean D.L D.K D.β h)
    (unitTorusCovariance D.L D.K D.β f h) hwell μ
    (fun v => hInv D μ hμ (shiftPoint D k v))
  have bF := hD D hL hdat g hg (averagedCovarianceDefect D.L D.K k m D.β f h) hF μ hμ
  have bA := hD D hL hdat g hg (averagedCenteredObservable D.L D.K k m D.β f) hA μ hμ
  have bB := hD D hL hdat g hg (averagedCenteredObservable D.L D.K k m D.β h) hB μ hμ
  have hc := covariance_eq_of_shifted μ (unitTorusMean D.L D.K D.β f)
    (unitTorusMean D.L D.K D.β h) (hf.integrable μ) (hh.integrable μ)
    (((hf.sub_const _).mul (hh.sub_const _)).integrable μ)
  exact le_of_eq_of_le (congrArg abs (covariance_sub_eq hc eF eA eB)) (abs_sub_mul_le bF bA bB)
end YangMills.Construction.StateLaws.CovarianceBoundProof
end
