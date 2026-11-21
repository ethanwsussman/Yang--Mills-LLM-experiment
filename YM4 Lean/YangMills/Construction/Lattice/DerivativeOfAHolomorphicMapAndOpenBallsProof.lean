import YangMills.Construction.Coordinates.PowerSeriesHolomorphy
import YangMills.Construction.DirichletOperator.DerivativeBoundsOfTheFunctionsOfACubeProof
import YangMills.Construction.Lattice.DerivativeOfAHolomorphicMapAndOpenBalls
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped ContDiff Topology
noncomputable section
namespace YangMills.Construction.Coordinates.ComplexCoordinates
section SecondDerivative
theorem two_le_smooth_order : (2 : WithTop ℕ∞) ≤ ∞ := by apply _root_.YangMills.Construction.PartitionCubes.CubeFunctionDerivBounds.two_le_infty <;> assumption
variable {n n' : ℕ} {U : Set (ComplexCoordinates n)} {g : ComplexCoordinates n → ComplexCoordinates n'}
theorem hasFDerivAt_fderiv_apply (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U)
    {x : ComplexCoordinates n} (hx : x ∈ U) (v : ComplexCoordinates n) :
    HasFDerivAt (fun y => fderiv ℝ g y v)
      ((ContinuousLinearMap.apply ℝ (ComplexCoordinates n') v).comp
        (fderiv ℝ (fderiv ℝ g) x)) x := by
  have hc : ContDiffOn ℝ 1 (fderiv ℝ g) U :=
    hg.fderiv_of_isOpen hU (by rw [one_add_one_eq_two]; exact two_le_smooth_order)
  have hD : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hc.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  exact (ContinuousLinearMap.apply ℝ (ComplexCoordinates n') v).hasFDerivAt.comp x hD.hasFDerivAt
theorem hasDerivAt_derivAlongLine (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U)
    {x : ComplexCoordinates n} (hx : x ∈ U) (w v : ComplexCoordinates n) :
    HasDerivAt (derivAlongLine g x w v) (fderiv ℝ (fderiv ℝ g) x w v) 0 := by
  have hl : HasDerivAt (fun s : ℝ => x + s • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add x
  have hd : HasFDerivAt (fun y => fderiv ℝ g y v)
      ((ContinuousLinearMap.apply ℝ (ComplexCoordinates n') v).comp
        (fderiv ℝ (fderiv ℝ g) x)) (x + (0 : ℝ) • w) := by
    simpa using hasFDerivAt_fderiv_apply hU hg hx v
  exact hd.comp_hasDerivAt (0 : ℝ) hl
theorem fderiv_fderiv_smul_right (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U)
    (hlin : ∀ y ∈ U, ∀ (c : ℂ) (u : ComplexCoordinates n), fderiv ℝ g y (c • u) = c • fderiv ℝ g y u)
    {x : ComplexCoordinates n} (hx : x ∈ U) (c : ℂ) (w v : ComplexCoordinates n) :
    fderiv ℝ (fderiv ℝ g) x w (c • v) = c • fderiv ℝ (fderiv ℝ g) x w v := by
  have e : (fun y => c • fderiv ℝ g y v) =ᶠ[𝓝 x] fun y => fderiv ℝ g y (c • v) :=
    Filter.eventually_of_mem (hU.mem_nhds hx) fun y hy => (hlin y hy c v).symm
  have d1 := hasFDerivAt_fderiv_apply hU hg hx (c • v)
  have d2 := ((hasFDerivAt_fderiv_apply hU hg hx v).const_smul c).congr_of_eventuallyEq e.symm
  have d3 := DFunLike.congr_fun (d1.unique d2) w
  simpa using d3
theorem fderiv_fderiv_symm (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U)
    {x : ComplexCoordinates n} (hx : x ∈ U) (w v : ComplexCoordinates n) :
    fderiv ℝ (fderiv ℝ g) x w v = fderiv ℝ (fderiv ℝ g) x v w := by
  have hc : ContDiffAt ℝ ∞ g x := hg.contDiffAt (hU.mem_nhds hx)
  exact (hc.isSymmSndFDerivAt (by simpa using two_le_smooth_order)).eq w v
theorem fderiv_fderiv_smul_left (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U)
    (hlin : ∀ y ∈ U, ∀ (c : ℂ) (u : ComplexCoordinates n), fderiv ℝ g y (c • u) = c • fderiv ℝ g y u)
    {x : ComplexCoordinates n} (hx : x ∈ U) (c : ℂ) (w v : ComplexCoordinates n) :
    fderiv ℝ (fderiv ℝ g) x (c • w) v = c • fderiv ℝ (fderiv ℝ g) x w v := by
  rw [fderiv_fderiv_symm hU hg hx, fderiv_fderiv_smul_right hU hg hlin hx,
    fderiv_fderiv_symm hU hg hx]
theorem isHolomorphicIn_fderiv_apply (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U)
    (hlin : ∀ y ∈ U, ∀ (c : ℂ) (u : ComplexCoordinates n), fderiv ℝ g y (c • u) = c • fderiv ℝ g y u)
    (v : ComplexCoordinates n) : IsHolomorphicIn U fun x => fderiv ℝ g x v := by
  refine ⟨hU, fun x hx =>
    (hasFDerivAt_fderiv_apply hU hg hx v).continuousAt.continuousWithinAt, ?_⟩
  intro p hp i
  have hline : Continuous fun ζ : ℂ => p + ζ • stdBasisVector i := by fun_prop
  have hnear : ∀ᶠ ζ in 𝓝 (0 : ℂ), p + ζ • stdBasisVector i ∈ U :=
    hline.continuousAt.eventually_mem (by simpa using hU.mem_nhds hp)
  filter_upwards [hnear] with ζ hζ
  let T : ComplexCoordinates n →ₗ[ℂ] ComplexCoordinates n' :=
    { toFun := fun w => fderiv ℝ (fderiv ℝ g) (p + ζ • stdBasisVector i) w v
      map_add' := fun w w' => by simp
      map_smul' := fun c w => by simpa using fderiv_fderiv_smul_left hU hg hlin hζ c w v }
  have hT : HasFDerivAt (fun y => fderiv ℝ g y v) (LinearMap.toContinuousLinearMap T)
      (p + ζ • stdBasisVector i) :=
    hasFDerivAt_of_restrictScalars ℝ (hasFDerivAt_fderiv_apply hU hg hζ v)
      (ContinuousLinearMap.ext fun _ => rfl)
  have hlineC : DifferentiableAt ℂ (fun ζ : ℂ => p + ζ • stdBasisVector i) ζ := by fun_prop
  exact hT.differentiableAt.comp ζ hlineC
end SecondDerivative
end YangMills.Construction.Coordinates.ComplexCoordinates
namespace YangMills.Construction.SeparatedFrame
theorem holomorphicDerivatives_claim
    (hPS : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties) :
    HolomorphicDerivatives.Claim := by
  intro n n' U g hg
  have hU : IsOpen U := hg.1
  obtain ⟨-, hsm, hdiff, -, -⟩ := (hPS.1 n U hU).1 n' g hg
  have hlin : ∀ y ∈ U, ∀ (c : ℂ) (u : Coordinates.ComplexCoordinates n),
      fderiv ℝ g y (c • u) = c • fderiv ℝ g y u := by
    intro y hy c u
    obtain ⟨Ty, hTy⟩ := hdiff y hy
    rw [hTy.fderiv]
    simp
  refine ⟨Coordinates.ComplexCoordinates.isHolomorphicIn_fderiv_apply hU hsm hlin,
    fun x hx => ⟨?_, ?_, ?_⟩⟩
  · intro w v
    exact (Coordinates.ComplexCoordinates.hasDerivAt_derivAlongLine hU hsm hx w v).differentiableAt
  · have hval : ∀ w v, Coordinates.ComplexCoordinates.secondDeriv g x w v =
        fderiv ℝ (fderiv ℝ g) x w v := fun w v =>
      (Coordinates.ComplexCoordinates.hasDerivAt_derivAlongLine hU hsm hx w v).deriv
    refine ⟨LinearMap.mk₂ ℂ (fun w v => fderiv ℝ (fderiv ℝ g) x w v) ?_ ?_ ?_ ?_, ?_⟩
    · intro w w' v
      simp
    · intro c w v
      simpa using Coordinates.ComplexCoordinates.fderiv_fderiv_smul_left hU hsm hlin hx c w v
    · intro w v v'
      simp
    · intro c w v
      simpa using Coordinates.ComplexCoordinates.fderiv_fderiv_smul_right hU hsm hlin hx c w v
    · intro w v
      rw [hval]
      rfl
  · intro w v
    have e1 : Coordinates.ComplexCoordinates.secondDeriv g x w v = fderiv ℝ (fderiv ℝ g) x w v :=
      (Coordinates.ComplexCoordinates.hasDerivAt_derivAlongLine hU hsm hx w v).deriv
    have e2 : Coordinates.ComplexCoordinates.secondDeriv g x v w = fderiv ℝ (fderiv ℝ g) x v w :=
      (Coordinates.ComplexCoordinates.hasDerivAt_derivAlongLine hU hsm hx v w).deriv
    rw [e1, e2]
    exact Coordinates.ComplexCoordinates.fderiv_fderiv_symm hU hsm hx w v
end YangMills.Construction.SeparatedFrame
