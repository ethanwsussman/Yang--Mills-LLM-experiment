import YangMills.Construction.InfiniteLattice.TraceOnTheGroupAndOneBondWeightProof
import YangMills.Construction.TransferOperators.EnergyOfTheOrbitsOfACubicTorus
import YangMills.Construction.TransferOperators.SymmetryBoundsAndInvarianceOfTheBondKernelAndTheLayerEnergy
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.InfiniteLattice YangMills.Construction.Matrices
noncomputable section
namespace YangMills.Construction.TransferOperators.SliceEnergyProperties
variable {Γ : CubicPeriodSublattice} {μ : Fin 4}
theorem continuous_holonomyOfFamily (p : SlicePlaquette μ) :
    Continuous (Γ.holonomyOfFamily p) := by
  unfold CubicPeriodSublattice.holonomyOfFamily plaquetteHolonomy
  fun_prop
theorem fullTrace_conj (a w : ComplexMatrix2.specialUnitary) :
    ComplexMatrix2.fullTrace ((a * w * a⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) =
      ComplexMatrix2.fullTrace (w : ComplexMatrix2) := by apply _root_.YangMills.Construction.InfiniteLattice.SUTwoTrace.fullTrace_conj <;> assumption
theorem holonomyOfFamily_orbitGaugeAct
    (h : ∀ (p : SlicePlaquette μ) (v : p.links → ComplexMatrix2.specialUnitary)
      (g : p.cornerSites → ComplexMatrix2.specialUnitary),
      plaquetteHolonomy p Subset.rfl (gaugeAct p.links_subset_linksWithin_cornerSites g v) =
        g ⟨p.origin, p.origin_mem_cornerSites⟩ * plaquetteHolonomy p Subset.rfl v *
          (g ⟨p.origin, p.origin_mem_cornerSites⟩)⁻¹)
    (g : Γ.VertexOrbits μ → ComplexMatrix2.specialUnitary)
    (v : Γ.LinkOrbits μ → ComplexMatrix2.specialUnitary) (p : SlicePlaquette μ) :
    Γ.holonomyOfFamily p (Γ.orbitGaugeAct g v) =
      g (Γ.vertexClass p.origin) * Γ.holonomyOfFamily p v * (g (Γ.vertexClass p.origin))⁻¹ := by
  have e : (fun b : p.links => Γ.orbitGaugeAct g v (Γ.linkClass b.1)) =
      gaugeAct p.links_subset_linksWithin_cornerSites
        (fun y => g (Γ.vertexClass y.1)) fun b => v (Γ.linkClass b.1) := by
    funext b
    rw [Γ.orbitGaugeAct_linkClass]
    rfl
  have hv := h p (fun b => v (Γ.linkClass b.1)) fun y => g (Γ.vertexClass y.1)
  rw [← e] at hv
  exact hv
theorem sliceEnergy_eq_sum [Fintype (Γ.FaceOrbits μ)] (β : ℝ)
    (v : Γ.LinkOrbits μ → ComplexMatrix2.specialUnitary) :
    Γ.sliceEnergy β v = (β : ℂ) * ∑ c : Γ.FaceOrbits μ,
      (1 - (1 / 2 : ℂ) *
        ComplexMatrix2.fullTrace ((Γ.orbitHolonomy c v : ComplexMatrix2.specialUnitary) :
          ComplexMatrix2)) := by
  rw [CubicPeriodSublattice.sliceEnergy, finsum_eq_sum_of_fintype]
theorem holds (ht : TraceAndSingleBondWeight)
    (hk : KernelSymmetryAndGaugeInvariance.Statement) : Statement := by
  intro β hβ Γ μ
  classical
  have : Fintype (Γ.FaceOrbits μ) := Fintype.ofFinite _
  have hhol := fun ν => (hk β hβ).2.2.1 ν
  have him : ∀ w : ComplexMatrix2.specialUnitary,
      (ComplexMatrix2.fullTrace (w : ComplexMatrix2)).im = 0 := fun w =>
    (ht.1.2 w).2.2.2.2.2.1
  have hnorm : ∀ w : ComplexMatrix2.specialUnitary,
      ‖ComplexMatrix2.fullTrace (w : ComplexMatrix2)‖ ≤ 2 := fun w =>
    (ht.1.2 w).2.2.2.2.2.2.2
  have hterm : ∀ w : ComplexMatrix2.specialUnitary,
      (1 - (1 / 2 : ℂ) * ComplexMatrix2.fullTrace (w : ComplexMatrix2)) =
      ((1 - 1 / 2 * (ComplexMatrix2.fullTrace (w : ComplexMatrix2)).re : ℝ) : ℂ) := by
    intro w
    apply Complex.ext
    · simp
    · simp [him w]
  refine ⟨?_, fun v => ?_, fun g v => ?_⟩
  · have e : Γ.sliceEnergy (μ := μ) β = fun v => (β : ℂ) * ∑ c : Γ.FaceOrbits μ,
        (1 - (1 / 2 : ℂ) *
          ComplexMatrix2.fullTrace ((Γ.orbitHolonomy c v : ComplexMatrix2.specialUnitary) :
            ComplexMatrix2)) :=
      funext (sliceEnergy_eq_sum β)
    rw [e]
    refine continuous_const.mul (continuous_finsetSum _ fun c _ =>
      continuous_const.sub (continuous_const.mul ?_))
    exact (continuous_subtype_val.comp
      (continuous_holonomyOfFamily _)).matrix_trace
  · have e : Γ.sliceEnergy β v = ((β * ∑ c : Γ.FaceOrbits μ,
        (1 - 1 / 2 * (ComplexMatrix2.fullTrace
          ((Γ.orbitHolonomy c v : ComplexMatrix2.specialUnitary) : ComplexMatrix2)).re) : ℝ) : ℂ) := by
      rw [sliceEnergy_eq_sum, Complex.ofReal_mul, Complex.ofReal_sum]
      exact congrArg _ (Finset.sum_congr rfl fun c _ => hterm _)
    rw [e, Complex.ofReal_im, Complex.ofReal_re]
    refine ⟨rfl, mul_nonneg hβ.le (Finset.sum_nonneg fun c _ => ?_)⟩
    have h₁ := (abs_le.mp ((Complex.abs_re_le_norm _).trans
      (hnorm (Γ.orbitHolonomy c v)))).2
    linarith
  · rw [sliceEnergy_eq_sum, sliceEnergy_eq_sum]
    refine congrArg _ (Finset.sum_congr rfl fun c _ => ?_)
    rw [CubicPeriodSublattice.orbitHolonomy, CubicPeriodSublattice.orbitHolonomy,
      holonomyOfFamily_orbitGaugeAct (hhol μ), fullTrace_conj]
end YangMills.Construction.TransferOperators.SliceEnergyProperties
end
