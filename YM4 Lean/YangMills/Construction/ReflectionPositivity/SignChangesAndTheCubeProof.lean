import YangMills.Construction.ReflectionPositivity.ActionOfTheLatticeIsometriesTheTwoFieldsAndTheReflections
import YangMills.Construction.ReflectionPositivity.SignChangesAndTheCube
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures.SignFlips
open YangMills.Construction.InfiniteLattice (GaugeField IsLocalObservable AmbientSpace LatticePoint
  UnitLatticeSymmetry axisStep shift halfSpaceLocalObservables observableSupNorm regionSigma_mono
  unitRegionObservables closedHalfSpace)
open YangMills.Construction.ReflectionPositivity.MirrorHyperplanes (siteReflect)
theorem sign_mul_sign_mul (s : ℤˣ) (t : ℝ) : ((s : ℤ) : ℝ) * (((s : ℤ) : ℝ) * t) = t := by
  rcases Int.units_eq_one_or s with h | h <;> simp [h]
theorem abs_sign_mul (s : ℤˣ) (t : ℝ) : |((s : ℤ) : ℝ) * t| = |t| := by
  rcases Int.units_eq_one_or s with h | h <;> simp [h]
def axisFactor (ε : Fin 4 → ℤˣ) (i : Fin 4) : Equiv.Perm AmbientSpace :=
  if ε i = 1 then 1 else siteReflectPerm i
theorem axisFactor_mem (ε : Fin 4 → ℤˣ) (i : Fin 4) : axisFactor ε i ∈ axisReflectionGroup := by
  unfold axisFactor
  split_ifs
  · exact one_mem _
  · exact Subgroup.subset_closure ⟨i, rfl⟩
theorem axisFactor_apply (ε : Fin 4 → ℤˣ) (i : Fin 4) (x : AmbientSpace) (j : Fin 4) :
    axisFactor ε i x j = (if j = i then ((ε i : ℤ) : ℝ) else 1) * x j := by
  unfold axisFactor
  rcases Int.units_eq_one_or (ε i) with e | e
  · simp [e]
  · have hne : (-1 : ℤˣ) ≠ 1 := by decide
    rw [e, if_neg hne]
    change (siteReflect i).toFun x j = _
    rw [siteReflect_coord]
    by_cases h : j = i <;> simp [h]
theorem exists_mem_of_signs (ε : Fin 4 → ℤˣ) :
    ∃ g ∈ axisReflectionGroup, ⇑g = fun (x : AmbientSpace) i => ((ε i : ℤ) : ℝ) * x i := by
  refine ⟨axisFactor ε 0 * axisFactor ε 1 * axisFactor ε 2 * axisFactor ε 3,
    mul_mem (mul_mem (mul_mem (axisFactor_mem ε 0) (axisFactor_mem ε 1)) (axisFactor_mem ε 2))
      (axisFactor_mem ε 3), ?_⟩
  funext x j
  simp only [Equiv.Perm.mul_apply, axisFactor_apply]
  fin_cases j <;> simp
theorem mem_axisReflectionGroup_iff (g : Equiv.Perm AmbientSpace) : g ∈ axisReflectionGroup ↔
    ∃ ε : Fin 4 → ℤˣ, ⇑g = fun x i => ((ε i : ℤ) : ℝ) * x i := by
  constructor
  · intro hg
    obtain ⟨ε, hε⟩ := exists_signs_of_mem_axisReflectionGroup hg
    exact ⟨ε, funext fun x => funext fun i => hε x i⟩
  · rintro ⟨ε, hε⟩
    obtain ⟨h, hh, hs⟩ := exists_mem_of_signs ε
    have e : g = h := Equiv.ext fun x => by rw [hε, hs]
    exact e ▸ hh
theorem card_axisReflectionGroup : Nat.card axisReflectionGroup = 16 := by
  choose g hg hs using exists_mem_of_signs
  have hb : Function.Bijective
      (fun ε => (⟨g ε, hg ε⟩ : axisReflectionGroup)) := by
    constructor
    · intro ε ε' e
      funext i
      have h : g ε (fun _ => 1) i = g ε' (fun _ => 1) i :=
        congrFun (congrArg (fun γ : axisReflectionGroup => γ.1 (fun _ => 1)) e) i
      rw [hs, hs] at h
      have h' : ((ε i : ℤ) : ℝ) = ((ε' i : ℤ) : ℝ) := by simpa using h
      exact Units.ext (by exact_mod_cast h')
    · intro γ
      obtain ⟨ε, hε⟩ := (mem_axisReflectionGroup_iff γ.1).mp γ.2
      refine ⟨ε, Subtype.ext (Equiv.ext fun x => ?_)⟩
      change g ε x = γ.1 x
      rw [hs, hε]
  rw [← Nat.card_congr (Equiv.ofBijective _ hb)]
  simp [Nat.card_eq_fintype_card]
theorem mem_cubeOfRadius_iff (r : ℕ+) (x : AmbientSpace) :
    x ∈ cubeOfRadius r ↔ ∀ i, |x i| ≤ (r : ℝ) := by
  simp only [cubeOfRadius, Set.mem_ofPred_eq, mem_Icc, abs_le]
theorem imageSet_cubeOfRadius (γ : axisReflectionGroup) (r : ℕ+) :
    (axisReflectionGroup.toUnitLatticeSymmetry γ).setImage (cubeOfRadius r) = cubeOfRadius r := by
  obtain ⟨ε, hε⟩ := exists_signs_of_mem_axisReflectionGroup γ.2
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_cubeOfRadius_iff] at hx ⊢
    intro i
    change |γ.1 x i| ≤ _
    rw [hε, abs_sign_mul]
    exact hx i
  · intro hy
    rw [mem_cubeOfRadius_iff] at hy
    refine ⟨fun i => ((ε i : ℤ) : ℝ) * y i, ?_, ?_⟩
    · rw [mem_cubeOfRadius_iff]
      intro i
      simp only [abs_sign_mul]
      exact hy i
    · funext i
      change γ.1 _ i = y i
      rw [hε]
      exact sign_mul_sign_mul _ _
theorem isBounded_cubeOfRadius (r : ℕ+) : Bornology.IsBounded (cubeOfRadius r) :=
  (Metric.isBounded_Icc (fun _ : Fin 4 => -(r : ℝ)) fun _ => (r : ℝ)).subset
    fun _ hx => ⟨fun i => (hx i).1, fun i => (hx i).2⟩
theorem unitRegionObservables_mono {S S' : Set AmbientSpace} (h : S ⊆ S') :
    unitRegionObservables S ⊆ unitRegionObservables S' :=
  fun _ hA => ⟨hA.1, hA.2.mono (regionSigma_mono h) le_rfl⟩
theorem coe_nsmul_axisStep_self (r : ℕ+) (μ : Fin 4) :
    (((r : ℕ) • axisStep (1 : ℝ) μ : LatticePoint (1 : ℝ)) : AmbientSpace) μ = (r : ℝ) := by
  simp [axisStep]
theorem imageSet_shift_subset (r : ℕ+) (μ : Fin 4) :
    (shift ((r : ℕ) • axisStep (1 : ℝ) μ)).setImage (cubeOfRadius r) ⊆
      {x | 0 ≤ x μ ∧ x μ ≤ 2 * (r : ℝ)} := by
  rintro _ ⟨x, hx, rfl⟩
  have hv : (shift ((r : ℕ) • axisStep (1 : ℝ) μ)).toFun x μ = x μ + (r : ℝ) := by
    change x μ + (((r : ℕ) • axisStep (1 : ℝ) μ : LatticePoint (1 : ℝ)) : AmbientSpace) μ = _
    rw [coe_nsmul_axisStep_self]
  have h := hx μ
  refine ⟨?_, ?_⟩ <;> rw [hv]
  · linarith [h.1]
  · linarith [h.2]
theorem signFlipsPreserveCube_of
    (hAction : MirrorHyperplanes.SymmetryActionAndReflections)
    (hPairs : ReflectionPairTheorem) :
    SignFlipsPreserveCube := by
  intro ν μ r
  have carried : ∀ (s : UnitLatticeSymmetry) (D : Set AmbientSpace) (A : GaugeField (1 : ℝ) → ℂ),
      A ∈ unitRegionObservables D → s.actOn A ∈ unitRegionObservables (s.setImage D) := by
    intro s D A hA
    rw [← hAction.2.1 s D]
    exact ⟨A, hA, rfl⟩
  refine ⟨mem_axisReflectionGroup_iff, card_axisReflectionGroup, fun ε => ?_,
    fun γ => imageSet_cubeOfRadius γ r, fun γ A hA => ?_, fun A hA => ?_⟩
  · obtain ⟨g, hg, hs⟩ := exists_mem_of_signs ε
    exact ⟨axisReflectionGroup.toUnitLatticeSymmetry ⟨g, hg⟩, hs⟩
  · have h := carried (axisReflectionGroup.toUnitLatticeSymmetry γ) _ A hA
    rwa [imageSet_cubeOfRadius] at h
  · have hIn := carried (shift ((r : ℕ) • axisStep (1 : ℝ) μ)) _ A hA
    have hNorm := hAction.2.2.2.2.1 (shift ((r : ℕ) • axisStep (1 : ℝ) μ)) A hA.1
    have hLocal : IsLocalObservable A := ⟨cubeOfRadius r, isBounded_cubeOfRadius r, hA.2⟩
    have hStrip := unitRegionObservables_mono (imageSet_shift_subset r μ) hIn
    have hHalf : (shift ((r : ℕ) • axisStep (1 : ℝ) μ)).actOn A ∈
        halfSpaceLocalObservables μ :=
      ⟨unitRegionObservables_mono (fun _ hx => hx.1) hStrip, hNorm.2.2 hLocal⟩
    refine ⟨hStrip, hHalf, ?_⟩
    have hBound := (hPairs ν μ ReflectionPair.site).1.2.2 _ hHalf
    rw [hNorm.2.1] at hBound
    exact hBound
end YangMills.Construction.ReflectionPositivity.DirectionPictures.SignFlips
