import YangMills.Construction.TwoPoints.FormAtMollifiedFunctionsProof
import YangMills.Construction.TwoPoints.FormIsTheIntegralOfALocalKernel
import YangMills.Construction.TwoPoints.LocalKernelOfAFormProof
import Mathlib
set_option autoImplicit false
open Set MeasureTheory Filter Metric
open scoped ContDiff Topology Manifold
noncomputable section
namespace YangMills.Construction.TwoPoints
open YangMills.Construction.InfiniteLattice (AmbientSpace)
namespace KernelRepresentsForm
theorem mem_compactlySupportedIn_iff {k : WithTop ℕ∞} {O : Set AmbientSpace} {f : AmbientSpace → ℂ} :
    f ∈ compactlySupportedIn k O ↔ ContDiff ℝ k f ∧ IsCompact (tsupport f) ∧ tsupport f ⊆ O :=
  Iff.rfl
theorem mem_compactC1Complex_of_mem_ccInfIn {O : Set AmbientSpace} {f : AmbientSpace → ℂ}
    (hf : f ∈ ccInfIn O) : f ∈ compactC1Complex :=
  mem_compactlySupportedIn_iff.2 ⟨hf.1.of_le (by exact_mod_cast le_top), hf.2.1, subset_univ _⟩
theorem norm_le_euclidNorm (z : AmbientSpace) : ‖z‖ ≤ euclidNorm z := by apply _root_.YangMills.Construction.TwoPoints.AdmissibleFormConsequences.norm_le_euclidNorm <;> assumption
theorem isOpen_euclidOpenBall (a : AmbientSpace) (r : ℝ) : IsOpen (euclidOpenBall a r) := by apply _root_.YangMills.Construction.TwoPoints.LocalFormKernel.isOpen_euclidOpenBall <;> assumption
theorem mem_euclidOpenBall_self (a : AmbientSpace) {r : ℝ} (hr : 0 < r) : a ∈ euclidOpenBall a r := by
  simpa [euclidOpenBall, euclidNorm] using hr
def kernelDoubleIntegral (K f g : AmbientSpace → ℂ) : ℂ :=
  lebesgueIntegral fun y : AmbientSpace => lebesgueIntegral fun x : AmbientSpace => f x * g y * K (y - x)
def kernelIntegrand (K f g : AmbientSpace → ℂ) (p : AmbientSpace × AmbientSpace) : ℂ :=
  f p.2 * g p.1 * K (p.1 - p.2)
variable {S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ} {K : AmbientSpace → ℂ}
theorem kernelIntegrand_eq_zero_of_snd {f g : AmbientSpace → ℂ} {p : AmbientSpace × AmbientSpace}
    (hp : p.2 ∉ tsupport f) : kernelIntegrand K f g p = 0 := by
  simp [kernelIntegrand, image_eq_zero_of_notMem_tsupport hp]
theorem kernelIntegrand_eq_zero_of_fst {f g : AmbientSpace → ℂ} {p : AmbientSpace × AmbientSpace}
    (hp : p.1 ∉ tsupport g) : kernelIntegrand K f g p = 0 := by
  simp [kernelIntegrand, image_eq_zero_of_notMem_tsupport hp]
theorem continuous_kernelIntegrand (hK : ContinuousOn K {0}ᶜ) {f g : AmbientSpace → ℂ}
    (hf : Continuous f) (hg : Continuous g) (hd : DisjointSupports f g) :
    Continuous (kernelIntegrand K f g) := by
  rw [continuous_iff_continuousAt]
  intro p
  by_cases h2 : p.2 ∈ tsupport f
  · by_cases h1 : p.1 ∈ tsupport g
    · have hne : p.1 - p.2 ≠ 0 := by
        intro e
        have he : p.1 = p.2 := sub_eq_zero.1 e
        exact disjoint_left.1 hd h2 (he ▸ h1)
      have hKat : ContinuousAt K (p.1 - p.2) :=
        hK.continuousAt (isOpen_compl_singleton.mem_nhds hne)
      have h3 : ContinuousAt (fun q : AmbientSpace × AmbientSpace => K (q.1 - q.2)) p :=
        ContinuousAt.comp (f := fun q : AmbientSpace × AmbientSpace => q.1 - q.2) hKat
          (continuous_fst.sub continuous_snd).continuousAt
      exact ((hf.comp continuous_snd).continuousAt.mul
        (hg.comp continuous_fst).continuousAt).mul h3
    · have hz : ∀ᶠ q in 𝓝 p, kernelIntegrand K f g q = 0 := by
        have ho : IsOpen {q : AmbientSpace × AmbientSpace | q.1 ∉ tsupport g} :=
          (isClosed_tsupport g).isOpen_compl.preimage continuous_fst
        filter_upwards [ho.mem_nhds h1] with q hq using kernelIntegrand_eq_zero_of_fst hq
      exact (continuousAt_const (y := (0 : ℂ))).congr (hz.mono fun q hq => hq.symm)
  · have hz : ∀ᶠ q in 𝓝 p, kernelIntegrand K f g q = 0 := by
      have ho : IsOpen {q : AmbientSpace × AmbientSpace | q.2 ∉ tsupport f} :=
        (isClosed_tsupport f).isOpen_compl.preimage continuous_snd
      filter_upwards [ho.mem_nhds h2] with q hq using kernelIntegrand_eq_zero_of_snd hq
    exact (continuousAt_const (y := (0 : ℂ))).congr (hz.mono fun q hq => hq.symm)
theorem hasCompactSupport_kernelIntegrand {f g : AmbientSpace → ℂ} (hf : IsCompact (tsupport f))
    (hg : IsCompact (tsupport g)) : HasCompactSupport (kernelIntegrand K f g) :=
  HasCompactSupport.intro (hg.prod hf) fun p hp => by
    by_cases h1 : p.1 ∈ tsupport g
    · exact kernelIntegrand_eq_zero_of_snd fun h2 => hp ⟨h1, h2⟩
    · exact kernelIntegrand_eq_zero_of_fst h1
theorem integrable_kernelIntegrand (hK : ContinuousOn K {0}ᶜ) {f g : AmbientSpace → ℂ}
    (hp : IsDisjointSupportPair f g) :
    Integrable (kernelIntegrand K f g) ((volume : Measure AmbientSpace).prod volume) :=
  (continuous_kernelIntegrand hK hp.1.1.continuous hp.2.1.1.continuous hp.2.2).integrable_of_hasCompactSupport
    (hasCompactSupport_kernelIntegrand hp.1.2.1 hp.2.1.2.1)
theorem kernelDoubleIntegral_eq_integral_prod (hK : ContinuousOn K {0}ᶜ) {f g : AmbientSpace → ℂ}
    (hp : IsDisjointSupportPair f g) :
    kernelDoubleIntegral K f g =
      ∫ p, kernelIntegrand K f g p ∂((volume : Measure AmbientSpace).prod volume) := by
  rw [integral_prod _ (integrable_kernelIntegrand hK hp)]
  rfl
theorem kernelDoubleIntegral_add_left (hK : ContinuousOn K {0}ᶜ) {f₁ f₂ g : AmbientSpace → ℂ}
    (h₁ : IsDisjointSupportPair f₁ g) (h₂ : IsDisjointSupportPair f₂ g)
    (h₃ : IsDisjointSupportPair (f₁ + f₂) g) :
    kernelDoubleIntegral K (f₁ + f₂) g = kernelDoubleIntegral K f₁ g + kernelDoubleIntegral K f₂ g := by
  rw [kernelDoubleIntegral_eq_integral_prod hK h₁, kernelDoubleIntegral_eq_integral_prod hK h₂,
    kernelDoubleIntegral_eq_integral_prod hK h₃,
    ← integral_add (integrable_kernelIntegrand hK h₁) (integrable_kernelIntegrand hK h₂)]
  congr 1
  funext p
  simp only [kernelIntegrand, Pi.add_apply]
  ring
theorem kernelDoubleIntegral_add_right (hK : ContinuousOn K {0}ᶜ) {f g₁ g₂ : AmbientSpace → ℂ}
    (p₁ : IsDisjointSupportPair f g₁) (p₂ : IsDisjointSupportPair f g₂)
    (p₃ : IsDisjointSupportPair f (g₁ + g₂)) :
    kernelDoubleIntegral K f (g₁ + g₂) = kernelDoubleIntegral K f g₁ + kernelDoubleIntegral K f g₂ := by
  rw [kernelDoubleIntegral_eq_integral_prod hK p₁, kernelDoubleIntegral_eq_integral_prod hK p₂,
    kernelDoubleIntegral_eq_integral_prod hK p₃,
    ← integral_add (integrable_kernelIntegrand hK p₁) (integrable_kernelIntegrand hK p₂)]
  congr 1
  funext p
  simp only [kernelIntegrand, Pi.add_apply]
  ring
theorem isDisjointSupportPair_swap {f g : AmbientSpace → ℂ} (hp : IsDisjointSupportPair f g) :
    IsDisjointSupportPair g f :=
  ⟨hp.2.1, hp.1, Disjoint.symm hp.2.2⟩
def FormMatchesKernel (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ) (K f g : AmbientSpace → ℂ) :
    Prop :=
  IsDisjointSupportPair f g ∧ complexifyForm S f g = kernelDoubleIntegral K f g
theorem FormMatchesKernel.add_left (hlin : ComplexifyLinear S) (hK : ContinuousOn K {0}ᶜ)
    {f₁ f₂ g : AmbientSpace → ℂ} (h₁ : FormMatchesKernel S K f₁ g) (h₂ : FormMatchesKernel S K f₂ g) :
    FormMatchesKernel S K (f₁ + f₂) g := by
  obtain ⟨hp, he, -⟩ := hlin 1 1 f₁ f₂ g h₁.1 h₂.1
  simp only [one_smul, one_mul] at hp he
  exact ⟨hp, by rw [he, h₁.2, h₂.2, kernelDoubleIntegral_add_left hK h₁.1 h₂.1 hp]⟩
theorem FormMatchesKernel.add_right (hlin : ComplexifyLinear S) (hK : ContinuousOn K {0}ᶜ)
    {f g₁ g₂ : AmbientSpace → ℂ} (p₁ : FormMatchesKernel S K f g₁) (p₂ : FormMatchesKernel S K f g₂) :
    FormMatchesKernel S K f (g₁ + g₂) := by
  obtain ⟨hp, -, he⟩ := hlin 1 1 g₁ g₂ f (isDisjointSupportPair_swap p₁.1)
    (isDisjointSupportPair_swap p₂.1)
  simp only [one_smul, one_mul] at hp he
  have hp' := isDisjointSupportPair_swap hp
  exact ⟨hp', by rw [he, p₁.2, p₂.2, kernelDoubleIntegral_add_right hK p₁.1 p₂.1 hp']⟩
theorem formMatchesKernel_zero_left (hlin : ComplexifyLinear S) {g : AmbientSpace → ℂ}
    (hg : g ∈ compactC1Complex) : FormMatchesKernel S K 0 g := by
  have hp : IsDisjointSupportPair 0 g :=
    ⟨Submodule.zero_mem _, hg, disjointSupports_zero_left g⟩
  have he := (hlin 0 0 0 0 g hp hp).2.1
  simp only [smul_zero, add_zero, zero_mul] at he
  refine ⟨hp, ?_⟩
  rw [he]
  simp [kernelDoubleIntegral, lebesgueIntegral, integralWrt]
theorem formMatchesKernel_zero_right (hlin : ComplexifyLinear S) {f : AmbientSpace → ℂ}
    (hf : f ∈ compactC1Complex) : FormMatchesKernel S K f 0 := by
  have hp : IsDisjointSupportPair 0 f :=
    ⟨Submodule.zero_mem _, hf, disjointSupports_zero_left f⟩
  have he := (hlin 0 0 0 0 f hp hp).2.2
  simp only [smul_zero, add_zero, zero_mul] at he
  refine ⟨isDisjointSupportPair_swap hp, ?_⟩
  rw [he]
  simp [kernelDoubleIntegral, lebesgueIntegral, integralWrt]
theorem FormMatchesKernel.sum_left {ι : Type*} (hlin : ComplexifyLinear S)
    (hK : ContinuousOn K {0}ᶜ) (s : Finset ι) (u : ι → AmbientSpace → ℂ) {g : AmbientSpace → ℂ}
    (hg : g ∈ compactC1Complex) (H : ∀ i ∈ s, FormMatchesKernel S K (u i) g) :
    FormMatchesKernel S K (∑ i ∈ s, u i) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using formMatchesKernel_zero_left hlin hg
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (H a (Finset.mem_insert_self a s)).add_left hlin hK
      (ih fun i hi => H i (Finset.mem_insert_of_mem hi))
theorem FormMatchesKernel.sum_right {ι : Type*} (hlin : ComplexifyLinear S)
    (hK : ContinuousOn K {0}ᶜ) (s : Finset ι) (u : ι → AmbientSpace → ℂ) {f : AmbientSpace → ℂ}
    (hf : f ∈ compactC1Complex) (H : ∀ i ∈ s, FormMatchesKernel S K f (u i)) :
    FormMatchesKernel S K f (∑ i ∈ s, u i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using formMatchesKernel_zero_right hlin hf
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (H a (Finset.mem_insert_self a s)).add_right hlin hK
      (ih fun i hi => H i (Finset.mem_insert_of_mem hi))
theorem translate_mem_ccInfIn (a : AmbientSpace) {c : AmbientSpace} {ρ : ℝ} {f : AmbientSpace → ℂ}
    (hf : f ∈ ccInfIn (euclidOpenBall c ρ)) :
    (fun x => f (x + a)) ∈ ccInfIn (euclidOpenBall (c - a) ρ) := by
  have hsub : tsupport (fun x => f (x + a)) ⊆ (fun x => x + a) ⁻¹' tsupport f :=
    tsupport_comp_subset_preimage f (continuous_id.add continuous_const)
  have hcomp : IsCompact ((fun x => x + a) ⁻¹' tsupport f) :=
    (Homeomorph.addRight a).isCompact_preimage.2 hf.2.1
  refine mem_compactlySupportedIn_iff.2 ⟨hf.1.comp (contDiff_id.add contDiff_const),
    hcomp.of_isClosed_subset (isClosed_tsupport _) hsub, fun x hx => ?_⟩
  have h1 : x + a ∈ euclidOpenBall c ρ := hf.2.2 (hsub hx)
  have he : x - (c - a) = x + a - c := by abel
  show euclidNorm (x - (c - a)) < ρ
  rw [he]
  exact h1
theorem formMatchesKernel_of_near (hinv : ComplexifyInvariant S)
    (hloc : ∀ ξ : AmbientSpace, ξ ≠ 0 → IsLocalKernelNear S ξ K) {a b : AmbientSpace} (hab : b - a ≠ 0)
    {f g : AmbientSpace → ℂ}
    (hf : f ∈ ccInfIn (euclidOpenBall a (euclidNorm (b - a) / 32)))
    (hg : g ∈ ccInfIn (euclidOpenBall b (euclidNorm (b - a) / 32)))
    (hd : DisjointSupports f g) : FormMatchesKernel S K f g := by
  have hp : IsDisjointSupportPair f g :=
    ⟨mem_compactC1Complex_of_mem_ccInfIn hf, mem_compactC1Complex_of_mem_ccInfIn hg, hd⟩
  refine ⟨hp, ?_⟩
  have hr₀ : (Equiv.addRight a : Equiv.Perm AmbientSpace) ∈ euclideanMotions :=
    ⟨1, hyperoctahedralPerms.one_mem, a, fun x => by simp⟩
  have hr := euclideanMotions.inv_mem hr₀
  have hon : ∀ u : AmbientSpace → ℂ,
      actOn (Equiv.addRight a : Equiv.Perm AmbientSpace)⁻¹ u = fun x => u (x + a) := by
    intro u
    funext x
    simp [actOn]
  have hinv' := (hinv _ hr f g hp).2
  rw [hon, hon] at hinv'
  have hf' := translate_mem_ccInfIn a hf
  rw [sub_self] at hf'
  have hg' := translate_mem_ccInfIn a hg
  have hl := hloc (b - a) hab _ hf' _ hg'
  rw [← hinv', hl]
  have inner : ∀ z₂ : AmbientSpace,
      (lebesgueIntegral fun z₁ : AmbientSpace => f (z₁ + a) * g (z₂ + a) * K (z₂ - z₁)) =
        (fun y : AmbientSpace => lebesgueIntegral fun x : AmbientSpace => f x * g y * K (y - x))
          (z₂ + a) := by
    intro z₂
    simp only [lebesgueIntegral, integralWrt]
    rw [← integral_add_right_eq_self (fun x : AmbientSpace => f x * g (z₂ + a) * K (z₂ + a - x)) a]
    simp only [add_sub_add_right_eq_sub]
  simp only [inner]
  simp only [kernelDoubleIntegral, lebesgueIntegral, integralWrt]
  exact integral_add_right_eq_self
    (fun y : AmbientSpace => ∫ x : AmbientSpace, f x * g y * K (y - x)) a
theorem exists_smooth_ballPartition {A : Set AmbientSpace} (hA : IsCompact A) {r : ℝ} (hr : 0 < r) :
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → AmbientSpace) (ρ : ι → AmbientSpace → ℝ),
      (∀ i, c i ∈ A) ∧ (∀ i, ContDiff ℝ ∞ (ρ i)) ∧ (∀ i, tsupport (ρ i) ⊆ euclidOpenBall (c i) r) ∧
        ∀ x ∈ A, ∑ i, ρ i x = 1 := by
  obtain ⟨t, htA, hcov⟩ := hA.elim_nhds_subcover (fun a => euclidOpenBall a r)
    fun a _ => (isOpen_euclidOpenBall a r).mem_nhds (mem_euclidOpenBall_self a hr)
  have hU : A ⊆ ⋃ i : t, euclidOpenBall (i : AmbientSpace) r := by
    intro x hx
    obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.1 (hcov hx)
    exact mem_iUnion.2 ⟨⟨a, ha⟩, hxa⟩
  obtain ⟨p, hp⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, AmbientSpace) hA.isClosed
    (fun i : t => euclidOpenBall (i : AmbientSpace) r) (fun i => isOpen_euclidOpenBall _ r) hU
  refine ⟨t, inferInstance, fun i => i, fun i x => p i x, fun i => htA i i.2, fun i => ?_,
    fun i => hp i, fun x hx => ?_⟩
  · exact (p i).contMDiff.contDiff
  · have h1 := p.sum_eq_one hx
    rwa [finsum_eq_sum_of_fintype] at h1
theorem eq_sum_partition_mul {ι : Type*} [Fintype ι] {ρ : ι → AmbientSpace → ℝ} {f : AmbientSpace → ℂ}
    (hsum : ∀ x ∈ tsupport f, ∑ i, ρ i x = 1) :
    f = ∑ i, fun x => (ρ i x : ℂ) * f x := by
  funext x
  rw [Finset.sum_apply, ← Finset.sum_mul, ← Complex.ofReal_sum]
  by_cases hx : x ∈ tsupport f
  · simp [hsum x hx]
  · simp [image_eq_zero_of_notMem_tsupport hx]
theorem tsupport_ofReal_mul_subset {ρ : AmbientSpace → ℝ} {f : AmbientSpace → ℂ} :
    tsupport (fun x => (ρ x : ℂ) * f x) ⊆ tsupport f :=
  closure_mono fun _ hx => right_ne_zero_of_mul hx
theorem ofReal_mul_mem_ccInfIn {ρ : AmbientSpace → ℝ} {f : AmbientSpace → ℂ} {O : Set AmbientSpace}
    (hρ : ContDiff ℝ ∞ ρ) (hsub : tsupport ρ ⊆ O) (hf : f ∈ ccInfIn (univ : Set AmbientSpace)) :
    (fun x => (ρ x : ℂ) * f x) ∈ ccInfIn O := by
  have h1 : tsupport (fun x => (ρ x : ℂ) * f x) ⊆ tsupport ρ := by
    refine closure_mono fun x hx => ?_
    have h2 : (ρ x : ℂ) ≠ 0 := left_ne_zero_of_mul hx
    exact fun e => h2 (by simp [e])
  exact mem_compactlySupportedIn_iff.2 ⟨(Complex.ofRealCLM.contDiff.comp hρ).mul hf.1,
    hf.2.1.of_isClosed_subset (isClosed_tsupport _) tsupport_ofReal_mul_subset, h1.trans hsub⟩
theorem formMatchesKernel_sum_sum {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (hlin : ComplexifyLinear S) (hK : ContinuousOn K {0}ᶜ) {u : ι₁ → AmbientSpace → ℂ}
    {v : ι₂ → AmbientSpace → ℂ} (hu : ∀ i, u i ∈ compactC1Complex) (hv : ∀ j, v j ∈ compactC1Complex)
    (H : ∀ i j, FormMatchesKernel S K (u i) (v j)) : FormMatchesKernel S K (∑ i, u i) (∑ j, v j) :=
  FormMatchesKernel.sum_left hlin hK _ _ (Submodule.sum_mem _ fun j _ => hv j) fun i _ =>
    FormMatchesKernel.sum_right hlin hK _ _ (hu i) fun j _ => H i j
theorem le_euclidNorm_of_disjoint_cthickening {A B : Set AmbientSpace} {δ : ℝ} (hδ : 0 < δ)
    (hdis : Disjoint (cthickening δ A) (cthickening δ B)) {a b : AmbientSpace} (ha : a ∈ A)
    (hb : b ∈ B) : δ ≤ euclidNorm (b - a) := by
  by_contra hc
  have h1 : dist b a ≤ δ := by
    rw [dist_eq_norm]
    exact (norm_le_euclidNorm _).trans (not_le.1 hc).le
  exact disjoint_left.1 hdis (mem_cthickening_of_dist_le b a δ A ha h1)
    (mem_cthickening_of_dist_le b b δ B hb (by simpa using hδ.le))
theorem formMatchesKernel_of_smooth (hinv : ComplexifyInvariant S) (hlin : ComplexifyLinear S)
    (hloc : ∀ ξ : AmbientSpace, ξ ≠ 0 → IsLocalKernelNear S ξ K) (hK : ContinuousOn K {0}ᶜ)
    {f g : AmbientSpace → ℂ} (hf : f ∈ ccInfIn (univ : Set AmbientSpace))
    (hg : g ∈ ccInfIn (univ : Set AmbientSpace)) (hd : DisjointSupports f g) :
    FormMatchesKernel S K f g := by
  obtain ⟨δ, hδ, hdis⟩ := Disjoint.exists_cthickenings (show Disjoint (tsupport f) (tsupport g)
    from hd) hf.2.1 hg.2.1.isClosed
  have hr : 0 < δ / 32 := by positivity
  obtain ⟨ι₁, _, c₁, ρ₁, hc₁, hρ₁, hs₁, hsum₁⟩ := exists_smooth_ballPartition hf.2.1 hr
  obtain ⟨ι₂, _, c₂, ρ₂, hc₂, hρ₂, hs₂, hsum₂⟩ := exists_smooth_ballPartition hg.2.1 hr
  rw [eq_sum_partition_mul hsum₁, eq_sum_partition_mul hsum₂]
  refine formMatchesKernel_sum_sum hlin hK
    (fun i => mem_compactC1Complex_of_mem_ccInfIn (ofReal_mul_mem_ccInfIn (hρ₁ i) (subset_univ _) hf))
    (fun j => mem_compactC1Complex_of_mem_ccInfIn (ofReal_mul_mem_ccInfIn (hρ₂ j) (subset_univ _) hg))
    fun i j => ?_
  have hfar := le_euclidNorm_of_disjoint_cthickening hδ hdis (hc₁ i) (hc₂ j)
  have hne : c₂ j - c₁ i ≠ 0 := by
    intro e
    rw [e] at hfar
    simp [euclidNorm] at hfar
    linarith
  have h32 : δ / 32 ≤ euclidNorm (c₂ j - c₁ i) / 32 := by linarith
  have hball : ∀ (c : AmbientSpace), euclidOpenBall c (δ / 32) ⊆
      euclidOpenBall c (euclidNorm (c₂ j - c₁ i) / 32) := fun c x hx =>
    lt_of_lt_of_le (show euclidNorm (x - c) < δ / 32 from hx) h32
  exact formMatchesKernel_of_near hinv hloc hne
    (ofReal_mul_mem_ccInfIn (hρ₁ i) ((hs₁ i).trans (hball _)) hf)
    (ofReal_mul_mem_ccInfIn (hρ₂ j) ((hs₂ j).trans (hball _)) hg)
    (Disjoint.mono tsupport_ofReal_mul_subset tsupport_ofReal_mul_subset hd)
theorem contDiff_convolve {O : Set AmbientSpace} {k f : AmbientSpace → ℂ} (hk : k ∈ ccInfIn O)
    (hf : f ∈ compactC1Complex) : ContDiff ℝ ∞ (convolve k f) := by
  have he : convolve k f = MeasureTheory.convolution k f (ContinuousLinearMap.mul ℝ ℂ) volume := by
    funext x
    rfl
  rw [he]
  exact HasCompactSupport.contDiff_convolution_left _ hk.2.1 hk.1
    hf.1.continuous.locallyIntegrable
theorem norm_convolve_sub_le (St : FixedScale) (hB : ∀ f ∈ compactC1Complex, TestFunctions.IsBoundedFun f)
    (hR : RiemannSumConvApprox St) {δ : ℝ} (hδ : 0 < δ) {k f : AmbientSpace → ℂ}
    (hk : k ∈ realValuedPart (ccInfIn (euclidOpenBall (0 : AmbientSpace) δ)))
    (hnn : ∀ x, IsRealNonneg (k x)) (hint : lebesgueIntegral k = 1) (hf : f ∈ compactC1Complex)
    (x : AmbientSpace) :
    ‖convolve k f x - f x‖ ≤ St.translationModulus f δ := by
  have hkc : k ∈ ccIn (univ : Set AmbientSpace) :=
    (mem_ccIn_iff _ _).2 ⟨hk.1.1.continuous, hk.1.2.1, subset_univ _⟩
  obtain ⟨hconv, -, -, -, -, -, hclose⟩ := hR k hkc f hf δ hδ
  have h1 := hclose hnn hint (hk.1.2.2.trans fun y hy =>
    show euclidNorm (y - (0 : AmbientSpace)) ≤ δ from le_of_lt hy)
  have hmem : convolve k f - f ∈ compactC1Complex := Submodule.sub_mem _ hconv hf
  obtain ⟨C, hC⟩ := hB _ hmem
  have hbdd : BddAbove (range fun y => ‖(convolve k f - f) y‖) :=
    ⟨C, by rintro _ ⟨y, rfl⟩; exact hC y⟩
  have h2 : ‖(convolve k f - f) x‖ ≤ St.sharpNorm (convolve k f - f) := by
    unfold FixedScale.sharpNorm TestFunctions.sharpNormR4 TestFunctions.uniformNorm
    exact (le_ciSup hbdd x).trans (le_max_left _ _)
  exact h2.trans h1
theorem tsupport_convolve_subset_cthickening {k f : AmbientSpace → ℂ} {ρ δ : ℝ}
    (hsub : tsupport (convolve k f) ⊆ minkowskiSum (tsupport k) (tsupport f))
    (hk : tsupport k ⊆ euclidOpenBall (0 : AmbientSpace) ρ) (hρ : ρ ≤ δ) :
    tsupport (convolve k f) ⊆ cthickening δ (tsupport f) := by apply _root_.YangMills.Construction.TwoPoints.MollifiedFormLimit.tsupport_convolve_subset_cthickening <;> assumption
theorem complexifyForm_eq_of_compactC1 (St : FixedScale)
    (hB : ∀ f ∈ compactC1Complex, TestFunctions.IsBoundedFun f)
    (hR : RiemannSumConvApprox St) (hT : TranslateModulusBound St)
    (hsmooth : ∀ f g : AmbientSpace → ℂ, f ∈ ccInfIn (univ : Set AmbientSpace) →
      g ∈ ccInfIn (univ : Set AmbientSpace) → DisjointSupports f g → FormMatchesKernel S K f g)
    (hK : ContinuousOn K {0}ᶜ) {f g : AmbientSpace → ℂ} (hf : f ∈ compactC1Complex)
    (hg : g ∈ compactC1Complex) (hd : DisjointSupports f g) {j : ℕ → AmbientSpace → ℂ}
    (hj : IsMollifierSeq j) {n₀ : ℕ}
    (hn₀ : ∀ n : ℕ, n₀ ≤ n → DisjointSupports (convolve (j n) f) (convolve (j n) g))
    (hlim : Tendsto (fun n : ℕ => complexifyForm S (convolve (j n) f) (convolve (j n) g))
      atTop (𝓝 (complexifyForm S f g))) :
    complexifyForm S f g = kernelDoubleIntegral K f g := by
  obtain ⟨δ, hδ, hdis⟩ := Disjoint.exists_cthickenings (show Disjoint (tsupport f) (tsupport g)
    from hd) hf.2.1 hg.2.1.isClosed
  have hD : IsCompact (cthickening δ (tsupport g) ×ˢ cthickening δ (tsupport f)) :=
    hg.2.1.cthickening.prod hf.2.1.cthickening
  have hKD : ContinuousOn (fun p : AmbientSpace × AmbientSpace => K (p.1 - p.2))
      (cthickening δ (tsupport g) ×ˢ cthickening δ (tsupport f)) := by
    refine hK.comp (continuous_fst.sub continuous_snd).continuousOn fun p hp e => ?_
    have he : p.1 = p.2 := sub_eq_zero.1 (mem_singleton_iff.1 e)
    exact disjoint_left.1 hdis hp.2 (he ▸ hp.1)
  obtain ⟨Km, hKm⟩ := hD.exists_bound_of_continuousOn hKD
  obtain ⟨Cf, hCf⟩ := hB f hf
  obtain ⟨Cg, hCg⟩ := hB g hg
  have hpos : ∀ n : ℕ, 1 ≤ n → 0 < 1 / (n : ℝ) := fun n hn =>
    one_div_pos.2 (by exact_mod_cast hn)
  have hzero : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 1
  have hright : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hzero, (eventually_ge_atTop 1).mono hpos⟩
  have hef := ((hT f hf).2.2.2.2.2).comp hright
  have heg := ((hT g hg).2.2.2.2.2).comp hright
  have hconv : ∀ n : ℕ, 1 ≤ n → ∀ u ∈ compactC1Complex,
      convolve (j n) u ∈ ccInfIn (univ : Set AmbientSpace) ∧
        convolve (j n) u ∈ compactC1Complex ∧
          tsupport (convolve (j n) u) ⊆ minkowskiSum (tsupport (j n)) (tsupport u) := by
    intro n hn u hu
    have hkc : j n ∈ ccIn (univ : Set AmbientSpace) :=
      (mem_ccIn_iff _ _).2
        ⟨(hj n hn).1.1.1.continuous, (hj n hn).1.1.2.1, subset_univ _⟩
    obtain ⟨h1, h2, -⟩ := hR (j n) hkc u hu (1 / (n : ℝ)) (hpos n hn)
    exact ⟨mem_compactlySupportedIn_iff.2 ⟨contDiff_convolve (hj n hn).1.1 hu, h1.2.1, subset_univ _⟩,
      h1, h2⟩
  have hclose : ∀ n : ℕ, 1 ≤ n → ∀ u ∈ compactC1Complex, ∀ x,
      ‖convolve (j n) u x - u x‖ ≤ St.translationModulus u (1 / (n : ℝ)) :=
    fun n hn u hu x => norm_convolve_sub_le St hB hR (hpos n hn) (hj n hn).1 (hj n hn).2.1
      (hj n hn).2.2 hu x
  have hptf : ∀ x, Tendsto (fun n : ℕ => convolve (j n) f x) atTop (𝓝 (f x)) := by
    intro x
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      ((eventually_ge_atTop 1).mono fun n hn => hclose n hn f hf x) hef
  have hptg : ∀ x, Tendsto (fun n : ℕ => convolve (j n) g x) atTop (𝓝 (g x)) := by
    intro x
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      ((eventually_ge_atTop 1).mono fun n hn => hclose n hn g hg x) heg
  have hev : ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧ n₀ ≤ n ∧ 1 / (n : ℝ) ≤ δ ∧
      St.translationModulus f (1 / (n : ℝ)) ≤ 1 ∧ St.translationModulus g (1 / (n : ℝ)) ≤ 1 := by
    filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop n₀,
      hzero.eventually_lt_const hδ, hef.eventually_lt_const one_pos,
      heg.eventually_lt_const one_pos] with n a b c d e
    exact ⟨a, b, c.le, le_of_lt d, le_of_lt e⟩
  have hlim2 : Tendsto (fun n : ℕ => ∫ p, kernelIntegrand K (convolve (j n) f) (convolve (j n) g) p
      ∂((volume : Measure AmbientSpace).prod volume)) atTop
      (𝓝 (∫ p, kernelIntegrand K f g p ∂((volume : Measure AmbientSpace).prod volume))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      ((cthickening δ (tsupport g) ×ˢ cthickening δ (tsupport f)).indicator
        fun _ => (|Cf| + 1) * (|Cg| + 1) * |Km|) ?_ ?_ ?_ ?_
    · exact hev.mono fun n hn => (continuous_kernelIntegrand hK (hconv n hn.1 f hf).2.1.1.continuous
        (hconv n hn.1 g hg).2.1.1.continuous (hn₀ n hn.2.1)).aestronglyMeasurable
    · refine hev.mono fun n hn => Eventually.of_forall fun p => ?_
      obtain ⟨h1, -, h3, h4, h5⟩ := hn
      have hsf := tsupport_convolve_subset_cthickening (hconv n h1 f hf).2.2 (hj n h1).1.1.2.2 h3
      have hsg := tsupport_convolve_subset_cthickening (hconv n h1 g hg).2.2 (hj n h1).1.1.2.2 h3
      by_cases hp : p ∈ cthickening δ (tsupport g) ×ˢ cthickening δ (tsupport f)
      · rw [indicator_of_mem hp]
        have b1 : ‖convolve (j n) f p.2‖ ≤ |Cf| + 1 := by
          have t := norm_add_le (convolve (j n) f p.2 - f p.2) (f p.2)
          rw [sub_add_cancel] at t
          linarith [hclose n h1 f hf p.2, hCf p.2, le_abs_self Cf]
        have b2 : ‖convolve (j n) g p.1‖ ≤ |Cg| + 1 := by
          have t := norm_add_le (convolve (j n) g p.1 - g p.1) (g p.1)
          rw [sub_add_cancel] at t
          linarith [hclose n h1 g hg p.1, hCg p.1, le_abs_self Cg]
        have b3 : ‖K (p.1 - p.2)‖ ≤ |Km| := (hKm p hp).trans (le_abs_self _)
        simp only [kernelIntegrand, norm_mul]
        gcongr
      · rw [indicator_of_notMem hp]
        have hz : kernelIntegrand K (convolve (j n) f) (convolve (j n) g) p = 0 := by
          by_cases h2 : p.1 ∈ cthickening δ (tsupport g)
          · have h6 : p.2 ∉ cthickening δ (tsupport f) := fun h7 => hp ⟨h2, h7⟩
            exact kernelIntegrand_eq_zero_of_snd fun h7 => h6 (hsf h7)
          · exact kernelIntegrand_eq_zero_of_fst fun h7 => h2 (hsg h7)
        rw [hz, norm_zero]
    · exact (continuousOn_const.integrableOn_compact hD).integrable_indicator hD.measurableSet
    · exact Eventually.of_forall fun p => ((hptf p.2).mul (hptg p.1)).mul_const _
  have hlim3 : Tendsto (fun n : ℕ => complexifyForm S (convolve (j n) f) (convolve (j n) g))
      atTop (𝓝 (kernelDoubleIntegral K f g)) := by
    rw [kernelDoubleIntegral_eq_integral_prod hK
      (show IsDisjointSupportPair f g from ⟨hf, hg, hd⟩)]
    refine hlim2.congr' ?_
    refine hev.mono fun n hn => ?_
    have ha := hsmooth _ _ (hconv n hn.1 f hf).1 (hconv n hn.1 g hg).1 (hn₀ n hn.2.1)
    exact (kernelDoubleIntegral_eq_integral_prod hK ha.1).symm.trans ha.2.symm
  exact tendsto_nhds_unique hlim hlim3
theorem proof (h₁ : AdmissibleFormConsequences.Statement) (h₂ : SharpNormTranslates)
    (h₃ : MollifierTranslatesDisjoint.Statement) : KernelRepresentsForm.Statement := by
  intro St S hS hP K hK hloc f hf g hg hd
  obtain ⟨C₂, hC₂⟩ := hP.ballDecay
  obtain ⟨⟨-, hlin, hinv, -, -⟩, -⟩ := h₁.2.2.2.2 St S C₂ hS hP hC₂
  obtain ⟨hT, hR, -, hL⟩ := h₂ St
  obtain ⟨j, hj⟩ := h₃.1
  obtain ⟨⟨n₀, hn₀⟩, hlim⟩ := hL S hS hP f hf g hg hd j hj
  exact complexifyForm_eq_of_compactC1 (K := fun x => (K x : ℂ)) St (fun u hu => (h₁.2.2.1 u hu).1)
    hR hT (fun _ _ a b c => formMatchesKernel_of_smooth hinv hlin hloc hK a b c) hK hf hg hd hj hn₀ hlim
end KernelRepresentsForm
end YangMills.Construction.TwoPoints
end
