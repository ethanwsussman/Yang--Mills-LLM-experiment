import YangMills.Construction.HilbertSpaces.FormAndItsCompletion
import YangMills.Construction.HilbertSpaces.GeneratorOfASemigroupOfPositiveContractions
import YangMills.Construction.HilbertSpaces.KernelOfTheHamiltonianUnderClustering
import YangMills.Construction.HilbertSpaces.SemigroupOnTheCompletion
import Mathlib
set_option autoImplicit false
open Set Filter Topology
open scoped NNReal ComplexOrder InnerProductSpace
open YangMills.Construction.FormsOperators (IsHilbertCompletion isDenseSet_iff_dense ker complexLine
  formRadical formOnQuotient)
noncomputable section
namespace YangMills.Construction.PositiveFormReconstruction.ClusteringVacuumKernel
theorem holds (hQuot : QuotientCompletion.Statement)
    (hSemi : SemigroupOnCompletion.TransferSemigroupSpec)
    (hGen : PositiveContractionGenerator.Statement) : Statement := by
  intro V _ _ S h H _ _ _ j hj hClust
  obtain ⟨-, hDesc, -⟩ := (hQuot V S h).1
  obtain ⟨hExt, hCont, hPos, hFix⟩ := hSemi V S h H j hj
  obtain ⟨-, -, -, -, hFixKer, hProj, hLim⟩ :=
    hGen H (transferOp S h.hermitian.toIsSesquilinear j) hCont hPos
  change ker (semigroupGenerator (transferOp S h.hermitian.toIsSesquilinear j)) = _
  set P := kerProjection (semigroupGenerator (transferOp S h.hermitian.toIsSesquilinear j)) with hP
  set Ω : H := vacuum S h.hermitian.toIsSesquilinear j with hΩ
  have hEmb : ∀ F F' : V, ⟪embed S h.hermitian.toIsSesquilinear j F,
      embed (H := H) S h.hermitian.toIsSesquilinear j F'⟫_ℂ = S.form F F' := fun F F' => by
    rw [embed, embed, hj.inner_map, hDesc]
  have hDense : DenseRange (embed (H := H) S h.hermitian.toIsSesquilinear j) := by
    have hd : Dense (range j) := (isDenseSet_iff_dense _).1 hj.dense_range
    have hr : range (embed (H := H) S h.hermitian.toIsSesquilinear j) = range j := by
      ext ψ
      constructor
      · rintro ⟨F, rfl⟩
        exact ⟨_, rfl⟩
      · rintro ⟨x, rfl⟩
        obtain ⟨F, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        exact ⟨F, rfl⟩
    rw [DenseRange, hr]
    exact hd
  have hPair : ∀ F F' : V, ⟪embed S h.hermitian.toIsSesquilinear j F,
      P (embed S h.hermitian.toIsSesquilinear j F')⟫_ℂ =
      ⟪embed S h.hermitian.toIsSesquilinear j F, Ω⟫_ℂ *
        ⟪Ω, embed S h.hermitian.toIsSesquilinear j F'⟫_ℂ := by
    intro F F'
    have hStrong : Tendsto (fun t => transferOp S h.hermitian.toIsSesquilinear j t
        (embed S h.hermitian.toIsSesquilinear j F')) atTop
        (𝓝 (P (embed (H := H) S h.hermitian.toIsSesquilinear j F'))) :=
      tendsto_iff_norm_sub_tendsto_zero.2 (hLim _)
    have hIn := (tendsto_const_nhds (x := embed (H := H) S h.hermitian.toIsSesquilinear j F)).inner
      (𝕜 := ℂ) hStrong
    have hEq : (fun t => ⟪embed (H := H) S h.hermitian.toIsSesquilinear j F,
        transferOp S h.hermitian.toIsSesquilinear j t (embed S h.hermitian.toIsSesquilinear j F')⟫_ℂ) =
        fun t => S.form F (S.semigroupMap t F') := by
      funext t
      rw [hExt t F', hEmb]
    rw [hEq] at hIn
    have hv : Ω = embed S h.hermitian.toIsSesquilinear j S.unitVec := rfl
    rw [hv, hEmb, hEmb]
    exact tendsto_nhds_unique hIn (hClust F F')
  have hOnEmb : ∀ F' : V, P (embed S h.hermitian.toIsSesquilinear j F') =
      ⟪Ω, embed S h.hermitian.toIsSesquilinear j F'⟫_ℂ • Ω := by
    intro F'
    have hOrth : ∀ φ : H, ⟪φ, P (embed S h.hermitian.toIsSesquilinear j F') -
        ⟪Ω, embed S h.hermitian.toIsSesquilinear j F'⟫_ℂ • Ω⟫_ℂ = 0 := by
      intro φ
      have hCl : IsClosed {φ : H | ⟪φ, P (embed S h.hermitian.toIsSesquilinear j F') -
          ⟪Ω, embed S h.hermitian.toIsSesquilinear j F'⟫_ℂ • Ω⟫_ℂ = 0} :=
        isClosed_eq (by fun_prop) continuous_const
      refine hDense.induction_on (p := fun φ => ⟪φ, P (embed S h.hermitian.toIsSesquilinear j F') -
          ⟪Ω, embed S h.hermitian.toIsSesquilinear j F'⟫_ℂ • Ω⟫_ℂ = 0) φ hCl fun F => ?_
      rw [inner_sub_right, inner_smul_right, hPair, mul_comm, sub_self]
    exact inner_self_eq_zero.1 (hOrth _) |> sub_eq_zero.1
  have hAll : ∀ ψ : H, P ψ = ⟪Ω, ψ⟫_ℂ • Ω := by
    intro ψ
    have hCl : IsClosed {ψ : H | P ψ = ⟪Ω, ψ⟫_ℂ • Ω} :=
      isClosed_eq P.continuous (by fun_prop)
    exact hDense.induction_on (p := fun ψ => P ψ = ⟪Ω, ψ⟫_ℂ • Ω) ψ hCl hOnEmb
  have hΩker : Ω ∈ ker (semigroupGenerator (transferOp S h.hermitian.toIsSesquilinear j)) :=
    hFixKer Ω (hFix 1)
  rw [← hProj.2] at hΩker ⊢
  ext φ
  constructor
  · rintro ⟨ψ, rfl⟩
    exact ⟨_, hAll ψ⟩
  · rintro ⟨c, rfl⟩
    obtain ⟨ψ, hψ⟩ := hΩker
    exact ⟨c • ψ, by rw [map_smul, hψ]⟩
end YangMills.Construction.PositiveFormReconstruction.ClusteringVacuumKernel
