import YangMills.Construction.TransferOperators.FactsOfTheOperatorsOfACubicTorus
import YangMills.Construction.TransferOperators.KernelBetweenTwoSquareRootsIsGaugeInvariant
import YangMills.Construction.TransferOperators.PeriodicStatesHaarMeasureCubicLatticesAndIntegralOperators
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.SpinHarmonics YangMills.Construction.InfiniteLattice YangMills.Construction.TransferOperators.SandwichConditions
open YangMills.Construction.TransferOperators.GibbsHaarKernels (HaarPiInvariance)
noncomputable section
namespace YangMills.Construction.TransferOperators.SandwichKernelGauge
variable {β : ℝ}
theorem slice_ae_eq {ι : Type} [Finite ι]
    (hc : Continuous fun p : (ι → Matrices.ComplexMatrix2.specialUnitary) ×
      (ι → Matrices.ComplexMatrix2.specialUnitary) => sqrtLinkKernel β p.1 p.2)
    (u : ι → Matrices.ComplexMatrix2.specialUnitary) :
    ((sqrtLinkKernelSlice β u : HaarL2 ι) : (ι → Matrices.ComplexMatrix2.specialUnitary) → ℂ)
      =ᵐ[Matrices.ComplexMatrix2.haarPi ι] fun w => sqrtLinkKernel β w u := by
  have hm : Continuous fun w : ι → Matrices.ComplexMatrix2.specialUnitary => (w, u) :=
    Continuous.prodMk continuous_id continuous_const
  have hcomp := hc.comp hm
  have hf : Continuous fun w : ι → Matrices.ComplexMatrix2.specialUnitary => sqrtLinkKernel β w u :=
    hcomp
  let ψ : C(ι → Matrices.ComplexMatrix2.specialUnitary, ℂ) := ⟨_, hf⟩
  have hmem : MemLp (fun w => sqrtLinkKernel β w u) 2 (Matrices.ComplexMatrix2.haarPi ι) :=
    MemLp.of_bound hf.aestronglyMeasurable ‖ψ‖
      (Filter.Eventually.of_forall fun w => ψ.norm_coe_le_norm w)
  have hs : sqrtLinkKernelSlice β u = hmem.toLp _ := dif_pos hmem
  rw [hs]
  exact hmem.coeFn_toLp
variable {μ : Fin 4} (B : Block μ)
theorem gaugeAct_gaugeAct_inv (g : B.vertices → Matrices.ComplexMatrix2.specialUnitary)
    (w : B.LinkType → Matrices.ComplexMatrix2.specialUnitary) :
    gaugeAct B.links_subset_linksWithin g
      (gaugeAct B.links_subset_linksWithin g⁻¹ w) = w := by
  funext b
  simp [gaugeAct, mul_assoc]
theorem blockGaugeRep_slice (hF : B.OperatorProperties β) (hH : HaarPiInvariance B.LinkType)
    (g : B.vertices → Matrices.ComplexMatrix2.specialUnitary)
    (u : B.LinkType → Matrices.ComplexMatrix2.specialUnitary) :
    blockGaugeRep B g (sqrtLinkKernelSlice β u) =
      sqrtLinkKernelSlice β (gaugeAct B.links_subset_linksWithin g u) := by
  have hp : MeasurePreserving (gaugeAct B.links_subset_linksWithin g⁻¹)
      (Matrices.ComplexMatrix2.haarPi B.LinkType) (Matrices.ComplexMatrix2.haarPi B.LinkType) :=
    hH.1 (fun b => g⁻¹ ⟨b.1.source, (B.links_subset_linksWithin b.2).1⟩)
      fun b => (g⁻¹ ⟨b.1.target, (B.links_subset_linksWithin b.2).2⟩)⁻¹
  have h₂ := hp.quasiMeasurePreserving.ae_eq_comp (slice_ae_eq hF.sqrt_continuous u)
  apply Lp.ext
  filter_upwards [hF.rep_formula g (sqrtLinkKernelSlice β u), h₂,
    slice_ae_eq hF.sqrt_continuous (gaugeAct B.links_subset_linksWithin g u)]
    with w e₁ e₂ e₃
  have e₄ := hF.sqrt_invariant g (gaugeAct B.links_subset_linksWithin g⁻¹ w) u
  simp only [gaugeAct_gaugeAct_inv] at e₄
  simp only [Function.comp_apply] at e₂
  rw [e₁, e₃, e₂, e₄]
theorem sandwich_gauge_invariant (hF : B.OperatorProperties β) (hH : HaarPiInvariance B.LinkType)
    (X : HaarL2 B.LinkType →L[ℂ] HaarL2 B.LinkType) :
    KernelGaugeInvariant β B X := by
  intro hX g u u'
  have hc : X (blockGaugeRep B g (sqrtLinkKernelSlice β u')) =
      blockGaugeRep B g (X (sqrtLinkKernelSlice β u')) :=
    congrArg (fun A : HaarL2 B.LinkType →L[ℂ] HaarL2 B.LinkType =>
      A (sqrtLinkKernelSlice β u')) (hX g).eq
  simp only [sqrtKernelSandwich]
  rw [← blockGaugeRep_slice B hF hH g u, ← blockGaugeRep_slice B hF hH g u', hc]
  exact (hF.rep_unitary g).2 _ _
theorem holds (h : CubicTorusOperators.Statement) (h' : GibbsHaarKernels.Statement) :
    SandwichKernelGaugeStatement := by
  intro β hβ μ B X
  have : Nonempty B.LinkType := by
    obtain ⟨b, hb⟩ := B.links_nonempty
    exact ⟨⟨b, hb⟩⟩
  exact sandwich_gauge_invariant B ((h β hβ).2 μ B) (h'.2.1 _) X
end YangMills.Construction.TransferOperators.SandwichKernelGauge
end
