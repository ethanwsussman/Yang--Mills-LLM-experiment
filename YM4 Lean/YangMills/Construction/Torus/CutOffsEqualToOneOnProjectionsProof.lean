import YangMills.Construction.Torus.CutOffsEqualToOneOnProjections
import YangMills.Construction.Torus.FiniteSmoothPartitionsOfUnity
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
noncomputable section
namespace YangMills.Construction.AmbientPoints.ProjectionCutoffs
variable {s : Conventions.StandingParameters}
theorem const_apply_zero (y : Tuple s .euclidean 1) : (fun _ => y 0) = y := by
  funext j
  rw [Subsingleton.elim j 0]
theorem isCompact_singletonTuples {A : Set (Pt s .euclidean)} (hA : IsCompact A) :
    IsCompact (singletonTuples A) := by
  have himg : singletonTuples A = (fun x : Pt s .euclidean => (fun _ => x : Tuple s .euclidean 1)) '' A := by
    ext y
    constructor
    · intro hy
      exact ⟨y 0, hy, const_apply_zero y⟩
    · rintro ⟨x, hx, rfl⟩
      exact hx
  rw [himg]
  exact hA.image (continuous_pi fun _ => continuous_id)
theorem isOpen_singletonTuples {A : Set (Pt s .euclidean)} (hA : IsOpen A) :
    IsOpen (singletonTuples A) :=
  hA.preimage (continuous_apply 0)
theorem exists_real_bump_eq_one (hP : SmoothPartitionOfUnityStatement)
    {K U : Set (Pt s .euclidean)} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ c : Pt s .euclidean → ℝ,
      asFunctionOnOnePoint c ∈ testFns (singletonTuples U) ∧ ∀ y ∈ K, c y = 1 := by
  obtain ⟨φ, hφ, hreal, N, ⟨V, -, hKV, hVN⟩, hone⟩ := (hP s .euclidean 1 le_rfl).2 (singletonTuples K)
    (singletonTuples U) (isCompact_singletonTuples hK) (isOpen_singletonTuples hU)
    (fun y hy => hKU hy)
  have heq : asFunctionOnOnePoint (fun x => (φ fun _ => x).re) = φ := by
    funext y
    obtain ⟨t, -, ht⟩ := hreal y
    change (((φ fun _ => y 0).re : ℝ) : ℂ) = φ y
    rw [const_apply_zero y, ht, Complex.ofReal_re]
  refine ⟨fun x => (φ fun _ => x).re, heq ▸ hφ, fun y hy => ?_⟩
  have hmem : (fun _ => y : Tuple s .euclidean 1) ∈ N := hVN (hKV hy)
  change (φ fun _ => y).re = 1
  rw [hone _ hmem, Complex.one_re]
theorem isCutoffFor_of_oneOnProjections {n : ℕ} {U : Fin n → Set (Pt s .euclidean)}
    (F : testFns (boxSet U)) {χ : Fin n → Pt s .euclidean → ℝ}
    (hχ : IsCutoff U χ) (hone : CutOffIsOneOnProjections F.1 χ) : IsCutoffFor χ F := by
  refine ⟨hχ, ?_⟩
  funext y
  by_cases hy : F.1 y = 0
  · simp [hy]
  · have hsupp : y ∈ closedSupport F.1 := subset_closure hy
    have htensor : cutoffTensor χ y = 1 := by
      change ∏ i, ((χ i (y i) : ℝ) : ℂ) = 1
      refine Finset.prod_eq_one fun i _ => ?_
      rw [hone i (y i) ⟨y, hsupp, rfl⟩]
      simp
    simp [htensor]
theorem cutoffsEqualOneOnProjections (hP : SmoothPartitionOfUnityStatement) :
    CutoffsEqualOneOnProjections := by
  intro s n ρ U hU
  refine ⟨fun K hK hKU => ?_, fun F χ hχ hone => isCutoffFor_of_oneOnProjections F hχ hone⟩
  have hbump : ∀ i, ∃ c : Pt s .euclidean → ℝ,
      asFunctionOnOnePoint c ∈ testFns (singletonTuples (U i)) ∧
        ∀ y ∈ factorProjection i K, c y = 1 := by
    intro i
    refine exists_real_bump_eq_one hP (hK.image (continuous_apply i)) (hU.2.2 i).1 ?_
    rintro _ ⟨y, hy, rfl⟩
    exact hKU hy i (mem_univ i)
  choose χ hχ hone using hbump
  exact ⟨χ, hχ, hone⟩
end YangMills.Construction.AmbientPoints.ProjectionCutoffs
