import YangMills.Construction.InfiniteLattice.MeasurabilityIsDependenceOnVariablesAtEverySpacing
import YangMills.Construction.TransferOperators.InsertionObservableIsRealLocalAndGaugeInvariant
import YangMills.Construction.TransferOperators.OperatorBetweenTwoSquareRootsOfTheBondKernel
import YangMills.Construction.TransferOperators.SymmetryBoundsAndInvarianceOfTheBondKernelAndTheLayerEnergy
import YangMills.Construction.TransferOperators.TemporalGaugeOfAStack
import Mathlib
set_option autoImplicit false
open Set
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction
open InfiniteLattice SpinHarmonics
namespace TransferOperators.LogKernelRatio
variable {μ : Fin 4}
theorem finite_vertices (B : Block μ) : B.vertices.Finite := by
  refine ((B.links.finite_toSet.image SliceLink.source).union
    (B.links.finite_toSet.image SliceLink.target)).subset ?_
  rintro y ⟨b, hb, rfl | rfl⟩
  · exact Or.inl ⟨b, hb, rfl⟩
  · exact Or.inr ⟨b, hb, rfl⟩
theorem log_div_im_eq_zero {k c : ℂ} (hkre : 0 < k.re) (hkim : k.im = 0) (hcre : 0 < c.re)
    (hcim : c.im = 0) : (Complex.log (k / c)).im = 0 := by
  have hq : k / c = ((k.re / c.re : ℝ) : ℂ) := by
    have hk : k = (k.re : ℂ) := Complex.ext (by simp) (by simp [hkim])
    have hc : c = (c.re : ℂ) := Complex.ext (by simp) (by simp [hcim])
    rw [hk, hc]
    simp
  rw [hq, Complex.log_im, Complex.arg_ofReal_of_nonneg (div_pos hkre hcre).le]
theorem div_mem_slitPlane_of_pos {k c : ℂ} (hkre : 0 < k.re) (hkim : k.im = 0) (hcre : 0 < c.re)
    (hcim : c.im = 0) : k / c ∈ Complex.slitPlane := by
  have hq : k / c = ((k.re / c.re : ℝ) : ℂ) := by
    have hk : k = (k.re : ℂ) := Complex.ext (by simp) (by simp [hkim])
    have hc : c = (c.re : ℂ) := Complex.ext (by simp) (by simp [hcim])
    rw [hk, hc]
    simp
  rw [hq]
  exact Complex.ofReal_mem_slitPlane.2 (div_pos hkre hcre)
abbrev twoLayerStack (i : ℤ) : Stack := ⟨i, i + 1, lt_add_one i⟩
theorem parallelTransport_lower (i : ℤ) (U : GaugeField 1) (y : SliceSite μ) :
    (twoLayerStack i).parallelTransport μ U i y = 1 := by
  simp [Stack.parallelTransport]
theorem parallelTransport_upper (i : ℤ) (U : GaugeField 1) (y : SliceSite μ) :
    (twoLayerStack i).parallelTransport μ U (i + 1) y = temporalLinkVariable μ U i y := by
  simp [Stack.parallelTransport]
theorem insertionLinks_finite (B : Block μ) (i : ℤ) : (B.insertionLinks i).Finite := by
  refine (((B.links.finite_toSet.image fun b => (spatialLink μ i b).1).union
    (B.links.finite_toSet.image fun b => (spatialLink μ (i + 1) b).1)).union
    ((finite_vertices B).image fun y => (temporalLink μ i y).1)).subset ?_
  rintro c (⟨b, hb, rfl | rfl⟩ | ⟨y, hy, rfl⟩)
  · exact Or.inl (Or.inl ⟨b, hb, rfl⟩)
  · exact Or.inl (Or.inr ⟨b, hb, rfl⟩)
  · exact Or.inr ⟨y, hy, rfl⟩
theorem isLinkSet_insertionLinks (B : Block μ) (i : ℤ) :
    IsLinkSet (B.insertionLinks i) := by
  rintro c (⟨b, -, rfl | rfl⟩ | ⟨y, -, rfl⟩)
  · exact (spatialLink μ i b).2
  · exact (spatialLink μ (i + 1) b).2
  · exact (temporalLink μ i y).2
theorem dependsOnly_logKernelRatio (B : Block μ) (β : ℝ) (Ξ : B.L2Operator) (i : ℤ) :
    DependsOnlyOn (B.insertionLinks i) (B.logKernelRatio β Ξ i) := by
  intro U V hUV
  have hsp : ∀ j, (j = i ∨ j = i + 1) → ∀ b ∈ B.links,
      spatialLinkVariable μ U j b = spatialLinkVariable μ V j b := by
    rintro j (rfl | rfl) b hb
    · exact hUV _ (Or.inl ⟨b, hb, Or.inl rfl⟩)
    · exact hUV _ (Or.inl ⟨b, hb, Or.inr rfl⟩)
  have htm : ∀ y ∈ B.vertices, temporalLinkVariable μ U i y = temporalLinkVariable μ V i y :=
    fun y hy => hUV _ (Or.inr ⟨y, hy, rfl⟩)
  have hlow : (twoLayerStack i).transportedRestriction μ U i (B.links : Set (SliceLink μ)) =
      (twoLayerStack i).transportedRestriction μ V i (B.links : Set (SliceLink μ)) := by
    funext b
    simp only [Stack.transportedRestriction, Stack.transportedLinkVariable,
      parallelTransport_lower]
    rw [hsp i (Or.inl rfl) b.1 b.2]
  have hup : (twoLayerStack i).transportedRestriction μ U (i + 1) (B.links : Set (SliceLink μ)) =
      (twoLayerStack i).transportedRestriction μ V (i + 1) (B.links : Set (SliceLink μ)) := by
    funext b
    simp only [Stack.transportedRestriction, Stack.transportedLinkVariable,
      parallelTransport_upper]
    rw [hsp (i + 1) (Or.inr rfl) b.1 b.2, htm _ ⟨b.1, b.2, Or.inl rfl⟩,
      htm _ ⟨b.1, b.2, Or.inr rfl⟩]
  simp only [Block.logKernelRatio]
  rw [hlow, hup]
theorem mem_indexPairs_lower (B : Block μ) (i : ℤ) (b : ↥(B.links : Set (SliceLink μ))) :
    (i, b.1) ∈ (twoLayerStack i).indexPairs B.vertices :=
  ⟨le_rfl, (lt_add_one i).le, B.links_subset_linksWithin b.2⟩
theorem mem_indexPairs_upper (B : Block μ) (i : ℤ) (b : ↥(B.links : Set (SliceLink μ))) :
    (i + 1, b.1) ∈ (twoLayerStack i).indexPairs B.vertices :=
  ⟨(lt_add_one i).le, le_rfl, B.links_subset_linksWithin b.2⟩
def lowerSlice (B : Block μ) (i : ℤ)
    (u : (twoLayerStack i).indexPairs B.vertices → Matrices.ComplexMatrix2.specialUnitary) :
    ↥(B.links : Set (SliceLink μ)) → Matrices.ComplexMatrix2.specialUnitary :=
  fun b => u ⟨(i, b.1), mem_indexPairs_lower B i b⟩
def upperSlice (B : Block μ) (i : ℤ)
    (u : (twoLayerStack i).indexPairs B.vertices → Matrices.ComplexMatrix2.specialUnitary) :
    ↥(B.links : Set (SliceLink μ)) → Matrices.ComplexMatrix2.specialUnitary :=
  fun b => u ⟨(i + 1, b.1), mem_indexPairs_upper B i b⟩
theorem continuous_lowerSlice (B : Block μ) (i : ℤ) : Continuous (lowerSlice B i) :=
  continuous_pi fun _ => continuous_apply _
theorem continuous_upperSlice (B : Block μ) (i : ℤ) : Continuous (upperSlice B i) :=
  continuous_pi fun _ => continuous_apply _
theorem isBoundedObservable_of_invariant (hTemp : TemporalGauge.MainStatement) (B : Block μ)
    (i : ℤ)
    (Ψ : (↥(B.links : Set (SliceLink μ)) → Matrices.ComplexMatrix2.specialUnitary) ×
      (↥(B.links : Set (SliceLink μ)) → Matrices.ComplexMatrix2.specialUnitary) → ℂ)
    (hΨ : Continuous Ψ)
    (hinv : ∀ (g : B.vertices → Matrices.ComplexMatrix2.specialUnitary)
      (u v : ↥(B.links : Set (SliceLink μ)) → Matrices.ComplexMatrix2.specialUnitary),
      Ψ (gaugeAct B.links_subset_linksWithin g u,
        gaugeAct B.links_subset_linksWithin g v) = Ψ (u, v)) :
    IsBoundedObservable
        (fun U => Ψ ((twoLayerStack i).transportedRestriction μ U i (B.links : Set (SliceLink μ)),
          (twoLayerStack i).transportedRestriction μ U (i + 1) (B.links : Set (SliceLink μ)))) ∧
      IsGaugeInvariantFunction
        (fun U => Ψ ((twoLayerStack i).transportedRestriction μ U i (B.links : Set (SliceLink μ)),
          (twoLayerStack i).transportedRestriction μ U (i + 1) (B.links : Set (SliceLink μ)))) ∧
      Continuous
        (fun U => Ψ ((twoLayerStack i).transportedRestriction μ U i (B.links : Set (SliceLink μ)),
          (twoLayerStack i).transportedRestriction μ U (i + 1) (B.links : Set (SliceLink μ)))) := by
  have : Finite B.vertices := (finite_vertices B).to_subtype
  have hcont : Continuous fun u => Ψ (lowerSlice B i u, upperSlice B i u) :=
    hΨ.comp ((continuous_lowerSlice B i).prodMk (continuous_upperSlice B i))
  have hbdd : ∃ C : ℝ, ∀ u, ‖Ψ (lowerSlice B i u, upperSlice B i u)‖ ≤ C := by
    obtain ⟨C, hC⟩ := (isCompact_range hcont).isBounded.exists_norm_le
    exact ⟨C, fun u => hC _ (mem_range_self u)⟩
  have hdiag : IsDiagonalGaugeInvariant
      ((twoLayerStack i).snd_mem_linksWithin_of_mem_indexPairs B.vertices)
      fun u => Ψ (lowerSlice B i u, upperSlice B i u) := fun g u =>
    hinv g (lowerSlice B i u) (upperSlice B i u)
  have hne : (linksWithin B.vertices).Nonempty := by
    obtain ⟨b, hb⟩ := B.links_nonempty
    exact ⟨b, B.links_subset_linksWithin hb⟩
  obtain ⟨hobs, hgauge, -, hc, -⟩ :=
    ((hTemp μ (twoLayerStack i)).1 B.vertices hne).2 _ hcont.measurable hbdd hdiag
  exact ⟨hobs, hgauge, hc hcont⟩
theorem realLocalInvariantStatement_holds
    (hSand : SandwichOperatorStatement)
    (hKer : KernelSymmetryAndGaugeInvariance.Statement)
    (hTemp : TemporalGauge.MainStatement)
    (hMeas : InfiniteLattice.MeasurableIffDependsOnlyAllSpacings) :
    RealLocalInvariantStatement := by
  intro β hβ μ B Ξ _ _ hcomm hpos i
  have : Nonempty ↥(B.links : Set (SliceLink μ)) := by
    obtain ⟨b, hb⟩ := B.links_nonempty
    exact ⟨⟨b, hb⟩⟩
  obtain ⟨hS₁, hS₂, hS₃, -, -⟩ := hSand β hβ
  obtain ⟨hK₁, hK₂, -, -⟩ := hKer β hβ
  have hkc : Continuous fun p : (↥(B.links : Set (SliceLink μ)) →
      Matrices.ComplexMatrix2.specialUnitary) ×
      (↥(B.links : Set (SliceLink μ)) → Matrices.ComplexMatrix2.specialUnitary) =>
      sqrtKernelSandwich β Ξ p.1 p.2 :=
    (hS₁ ↥(B.links : Set (SliceLink μ)) Ξ).1.2.1
  have hcc : Continuous fun p : (↥(B.links : Set (SliceLink μ)) →
      Matrices.ComplexMatrix2.specialUnitary) ×
      (↥(B.links : Set (SliceLink μ)) → Matrices.ComplexMatrix2.specialUnitary) =>
      linkProductKernel β p.1 p.2 := by
    have h₁ := (hS₁ ↥(B.links : Set (SliceLink μ)) 1).1.2.1
    have heq : (fun p : (↥(B.links : Set (SliceLink μ)) →
        Matrices.ComplexMatrix2.specialUnitary) ×
        (↥(B.links : Set (SliceLink μ)) → Matrices.ComplexMatrix2.specialUnitary) =>
        sqrtKernelSandwich β 1 p.1 p.2) = fun p => linkProductKernel β p.1 p.2 := by
      funext p
      exact (hS₂ ↥(B.links : Set (SliceLink μ))).2.1 p.1 p.2
    rwa [heq] at h₁
  have hkp : ∀ u v : ↥(B.links : Set (SliceLink μ)) → Matrices.ComplexMatrix2.specialUnitary,
      0 < (sqrtKernelSandwich β Ξ u v).re ∧ (sqrtKernelSandwich β Ξ u v).im = 0 := by
    intro u v
    obtain ⟨h₁, h₂⟩ := Complex.pos_iff.1 (hpos u v)
    exact ⟨h₁, h₂.symm⟩
  have hcp : ∀ u v : ↥(B.links : Set (SliceLink μ)) → Matrices.ComplexMatrix2.specialUnitary,
      0 < (linkProductKernel β u v).re ∧ (linkProductKernel β u v).im = 0 := by
    intro u v
    obtain ⟨-, h₂, h₃, -⟩ := (hK₁ ↥(B.links : Set (SliceLink μ))).1 u v
    exact ⟨(Real.exp_pos _).trans_le h₃, h₂⟩
  have hΨ : Continuous fun p : (↥(B.links : Set (SliceLink μ)) →
      Matrices.ComplexMatrix2.specialUnitary) ×
      (↥(B.links : Set (SliceLink μ)) → Matrices.ComplexMatrix2.specialUnitary) =>
      Complex.log (sqrtKernelSandwich β Ξ p.1 p.2 / linkProductKernel β p.1 p.2) := by
    refine Continuous.clog (hkc.div hcc fun p h0 => ?_) fun p => ?_
    · have h₁ := (hcp p.1 p.2).1
      rw [h0] at h₁
      simp at h₁
    · exact div_mem_slitPlane_of_pos (hkp _ _).1 (hkp _ _).2 (hcp _ _).1 (hcp _ _).2
  have hinv : ∀ (g : B.vertices → Matrices.ComplexMatrix2.specialUnitary)
      (u v : ↥(B.links : Set (SliceLink μ)) → Matrices.ComplexMatrix2.specialUnitary),
      Complex.log (sqrtKernelSandwich β Ξ (gaugeAct B.links_subset_linksWithin g u)
          (gaugeAct B.links_subset_linksWithin g v) /
        linkProductKernel β (gaugeAct B.links_subset_linksWithin g u)
          (gaugeAct B.links_subset_linksWithin g v)) =
      Complex.log (sqrtKernelSandwich β Ξ u v / linkProductKernel β u v) := by
    intro g u v
    have e₁ := hS₃ μ B Ξ hcomm g u v
    have e₂ : linkProductKernel β (gaugeAct B.links_subset_linksWithin g u)
        (gaugeAct B.links_subset_linksWithin g v) = linkProductKernel β u v := hK₂ μ B g u v
    rw [e₁, e₂]
  obtain ⟨hobs, hgauge, hcont⟩ := isBoundedObservable_of_invariant hTemp B i
    (fun p => Complex.log (sqrtKernelSandwich β Ξ p.1 p.2 / linkProductKernel β p.1 p.2)) hΨ hinv
  have hdep := dependsOnly_logKernelRatio B β Ξ i
  refine ⟨⟨hobs, ?_, hcont⟩, fun U => ?_, hgauge, hdep⟩
  · exact ((hMeas 1 one_pos).2.2.2 _ hobs).2
      ⟨_, isLinkSet_insertionLinks B i, insertionLinks_finite B i, hdep⟩
  · exact log_div_im_eq_zero (hkp _ _).1 (hkp _ _).2 (hcp _ _).1 (hcp _ _).2
end TransferOperators.LogKernelRatio
end YangMills.Construction
end
