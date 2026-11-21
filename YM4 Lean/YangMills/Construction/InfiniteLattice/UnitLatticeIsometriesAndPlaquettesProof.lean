import YangMills.Construction.InfiniteLattice.ActionsOfALatticeIsometry
import YangMills.Construction.InfiniteLattice.LocalObservablesDetermineMeasuresAndIsometriesOnIntegrableFunctions
import YangMills.Construction.InfiniteLattice.PositivityAtAMirrorExtendsFromContinuousLocalObservablesProof
import YangMills.Construction.ReflectionPositivity.BoundedMomentumDensityWithReflectionSizesProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ComplexConjugate ComplexOrder Matrix
noncomputable section
namespace YangMills.Construction.InfiniteLattice.UnitSymmetriesAndFaces
open YangMills.Construction.ReflectionPositivity.MirrorHyperplanes (basisVec unitPositiveClass UnitMirrorPair
  MirrorPair IsReflectionPositiveAcross latticeSymmetry_ext)
open YangMills.Construction.InfiniteLattice.CutoffStructure
def coordPermutation (σ : Equiv.Perm (Fin 4)) : AmbientSpace ≃ₗ[ℝ] AmbientSpace :=
  LinearEquiv.funCongrLeft ℝ ℝ σ
theorem coordPermutation_apply (σ : Equiv.Perm (Fin 4)) (x : AmbientSpace) (i : Fin 4) :
    coordPermutation σ x i = x (σ i) := rfl
theorem signFlip_apply (ε : Fin 4 → ℤˣ) (x : AmbientSpace) (i : Fin 4) :
    signFlip ε x i = ((ε i : ℤ) : ℝ) * x i := rfl
theorem coordPermutation_mem (σ : Equiv.Perm (Fin 4)) :
    coordPermutation σ ∈ hyperoctahedralLinearGroup :=
  (mem_hyperoctahedralLinearGroup_iff _).mpr ⟨σ, 1, fun x μ => by simp [coordPermutation_apply]⟩
theorem signFlip_mulSingle_eq_reflect (μ : Fin 4) :
    ⇑(signFlip (Pi.mulSingle μ (-1))) = hyperplaneReflect (basisVec μ) 0 := by
  funext x i
  rw [signFlip_apply]
  by_cases h : i = μ
  · subst h
    simp [hyperplaneReflect, basisVec, single_dotProduct]
    ring
  · simp [hyperplaneReflect, basisVec, single_dotProduct, Pi.mulSingle_eq_of_ne h,
      Pi.single_eq_of_ne h]
theorem coordPermutation_swap_eq_reflect {μ ν : Fin 4} (hne : μ ≠ ν) :
    ⇑(coordPermutation (Equiv.swap μ ν)) = hyperplaneReflect (basisVec μ - basisVec ν) 0 := by
  funext x i
  rw [coordPermutation_apply]
  have hn : (basisVec μ - basisVec ν) ⬝ᵥ (basisVec μ - basisVec ν) = 2 := by
    simp [dotProduct_sub, basisVec, Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hne.symm]
    norm_num
  have hx : (basisVec μ - basisVec ν) ⬝ᵥ x = x μ - x ν := by
    simp [sub_dotProduct, basisVec, single_dotProduct]
  simp only [hyperplaneReflect, hn, hx, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_zero]
  by_cases h1 : i = μ
  · subst h1
    simp [basisVec, Pi.single_eq_of_ne hne]
  · by_cases h2 : i = ν
    · subst h2
      simp [basisVec, Pi.single_eq_of_ne h1]
    · simp [basisVec, Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2, Equiv.swap_apply_of_ne_of_ne h1 h2]
theorem signFlip_mulSingle_mem_closure (μ : Fin 4) (u : ℤˣ) :
    signFlip (Pi.mulSingle μ u) ∈ Subgroup.closure axisAndDiagonalReflections := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · have h : signFlip (Pi.mulSingle μ (1 : ℤˣ)) = 1 :=
      LinearEquiv.ext fun x => funext fun i => by simp [signFlip_apply]
    rw [h]
    exact one_mem _
  · exact Subgroup.subset_closure (Or.inl ⟨μ, signFlip_mulSingle_eq_reflect μ⟩)
theorem signFlip_mem_closure (ε : Fin 4 → ℤˣ) :
    signFlip ε ∈ Subgroup.closure axisAndDiagonalReflections := by
  have h : signFlip ε =
      signFlip (Pi.mulSingle 0 (ε 0)) * signFlip (Pi.mulSingle 1 (ε 1)) *
        signFlip (Pi.mulSingle 2 (ε 2)) * signFlip (Pi.mulSingle 3 (ε 3)) := by
    refine LinearEquiv.ext fun x => funext fun i => ?_
    simp only [LinearEquiv.mul_apply, signFlip_apply]
    fin_cases i <;> simp
  rw [h]
  exact mul_mem (mul_mem (mul_mem (signFlip_mulSingle_mem_closure _ _)
    (signFlip_mulSingle_mem_closure _ _)) (signFlip_mulSingle_mem_closure _ _))
    (signFlip_mulSingle_mem_closure _ _)
theorem coordPermutation_mem_closure (σ : Equiv.Perm (Fin 4)) :
    coordPermutation σ ∈ Subgroup.closure axisAndDiagonalReflections := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one =>
    have h : coordPermutation 1 = 1 := LinearEquiv.ext fun x => funext fun i => rfl
    rw [h]
    exact one_mem _
  | swap_mul f x y hne ih =>
    have h : coordPermutation (Equiv.swap x y * f) =
        coordPermutation f * coordPermutation (Equiv.swap x y) :=
      LinearEquiv.ext fun z => funext fun i => rfl
    rw [h]
    exact mul_mem ih (Subgroup.subset_closure
      (Or.inr ⟨x, y, hne, coordPermutation_swap_eq_reflect hne⟩))
theorem hyperoctahedralLinearGroup_eq_closure :
    hyperoctahedralLinearGroup = Subgroup.closure axisAndDiagonalReflections := by
  apply le_antisymm
  · intro w hw
    obtain ⟨σ, s, h⟩ := (mem_hyperoctahedralLinearGroup_iff w).mp hw
    have e : w = signFlip s * coordPermutation σ :=
      LinearEquiv.ext fun x => funext fun μ => by
        rw [h, LinearEquiv.mul_apply, signFlip_apply, coordPermutation_apply]
    rw [e]
    exact mul_mem (signFlip_mem_closure s) (coordPermutation_mem_closure σ)
  · rw [Subgroup.closure_le]
    rintro w (⟨μ, h⟩ | ⟨μ, ν, hne, h⟩)
    · have e : w = signFlip (Pi.mulSingle μ (-1)) :=
        LinearEquiv.ext fun x => by rw [h, signFlip_mulSingle_eq_reflect]
      rw [e]
      exact signFlipGroup_le_hyperoctahedralLinearGroup ⟨_, rfl⟩
    · have e : w = coordPermutation (Equiv.swap μ ν) :=
        LinearEquiv.ext fun x => by rw [h, coordPermutation_swap_eq_reflect hne]
      rw [e]
      exact coordPermutation_mem _
section Symmetry
variable (ν : Measure (GaugeField (1 : ℝ))) [IsProbabilityMeasure ν]
theorem integrable_of_isBoundedObservable {F : GaugeField (1 : ℝ) → ℂ}
    (hF : IsBoundedObservable F) : Integrable F ν := by apply _root_.YangMills.Construction.InfiniteLattice.ReflectionPositivityExtension.integrable_of_isBoundedObservable <;> assumption
theorem IsBoundedObservable.conj_mul {F H : GaugeField (1 : ℝ) → ℂ} (hF : IsBoundedObservable F)
    (hH : IsBoundedObservable H) : IsBoundedObservable fun U => conj (F U) * H U := by apply _root_.YangMills.Construction.ReflectionPositivity.DirectionPictures.MomentumDensityBound.isBoundedObservable_conj_mul <;> assumption
theorem IsBoundedObservable.conj {F : GaugeField (1 : ℝ) → ℂ} (hF : IsBoundedObservable F) :
    IsBoundedObservable fun U => conj (F U) := by
  obtain ⟨m, C, hC⟩ := hF
  exact ⟨Complex.continuous_conj.measurable.comp m, C, fun U => by
    rw [RCLike.norm_conj]
    exact hC U⟩
theorem isBoundedObservable_const (a : ℂ) :
    IsBoundedObservable fun _ : GaugeField (1 : ℝ) => a :=
  ⟨measurable_const, ‖a‖, fun _ => le_rfl⟩
variable {ν}
theorem integral_reflect_eq_of_halfSpace
    (hA : ReflectionPositivity.MirrorHyperplanes.SymmetryActionAndReflections)
    (P : UnitMirrorPair) (hP : IsReflectionPositiveAcross ν P)
    (H : GaugeField (1 : ℝ) → ℂ) (hobs : IsBoundedObservable H) (hloc : IsLocalObservable H)
    (hm : IsRegionMeasurable {x | P.height ≤ P.normal ⬝ᵥ x} H) :
    ∫ U, P.reflect.actOn H U ∂ν = ∫ U, H U ∂ν := by
  obtain ⟨-, -, -, -, hNorm, -, -, -, -, -⟩ := hA
  set T := P.reflect.actOn H with hT
  have hside : {x : AmbientSpace | P.height ≤ P.normal ⬝ᵥ x} ∈ P.halfSpaces := Or.inl rfl
  have hTobs : IsBoundedObservable T := ((hNorm P.reflect) H hobs).1
  have iH := integrable_of_isBoundedObservable ν hobs
  have iC := integrable_of_isBoundedObservable ν (IsBoundedObservable.conj_mul hTobs hobs)
  set A := ∫ U, H U ∂ν with hAdef
  set B := ∫ U, T U ∂ν with hBdef
  set C := ∫ U, conj (T U) * H U ∂ν with hCdef
  have hconj : ∫ U, conj (T U) ∂ν = conj B := integral_conj
  have key : ∀ z : ℂ, 0 ≤ 1 + z * A + conj z * conj B + conj z * z * C := by
    intro z
    have hFobs : IsBoundedObservable fun U => 1 + z * H U := by
      have := (isBoundedObservable_const (1 : ℂ)).add (hobs.const_smul z)
      exact this
    have hFloc : IsLocalObservable fun U => 1 + z * H U := by
      obtain ⟨S, bS, mS⟩ := hloc
      exact ⟨S, bS, Measurable.add measurable_const (Measurable.const_smul mS z)⟩
    have hFm : IsRegionMeasurable {x | P.height ≤ P.normal ⬝ᵥ x} fun U => 1 + z * H U :=
      Measurable.add measurable_const (Measurable.const_smul hm z)
    have h := hP.2 _ hside _ hFobs hFloc hFm
    have e : (fun U => conj (P.reflect.actOn (fun U => 1 + z * H U) U) * (1 + z * H U)) =
        fun U => 1 + z * H U + conj z * conj (T U) + conj z * z * (conj (T U) * H U) := by
      funext U
      have : P.reflect.actOn (fun U => 1 + z * H U) U = 1 + z * T U := rfl
      rw [this]
      simp only [map_add, map_mul, map_one]
      ring
    rw [e] at h
    have i1 : Integrable (fun U => 1 + z * H U) ν :=
      (integrable_const (1 : ℂ)).add (iH.const_mul z)
    have i2 : Integrable (fun U => conj z * conj (T U)) ν :=
      (integrable_of_isBoundedObservable ν (IsBoundedObservable.conj hTobs)).const_mul _
    have i3 : Integrable (fun U => conj z * z * (conj (T U) * H U)) ν := iC.const_mul _
    have i12 : Integrable (fun U => 1 + z * H U + conj z * conj (T U)) ν := i1.add i2
    have iz : Integrable (fun U => z * H U) ν := iH.const_mul z
    rw [integral_add i12 i3, integral_add i1 i2, integral_add (integrable_const _) iz,
      integral_const_mul, integral_const_mul, integral_const_mul, hconj] at h
    simpa using h
  have hC0 : 0 ≤ C := hP.2 _ hside H hobs hloc hm
  have k1 := (Complex.le_def.mp (key 1)).2
  have kI := (Complex.le_def.mp (key Complex.I)).2
  have kC := (Complex.le_def.mp hC0).2
  simp at k1 kI kC
  apply Complex.ext
  · linarith
  · linarith
theorem isSymmetricUnder_reflect
    (hA : ReflectionPositivity.MirrorHyperplanes.SymmetryActionAndReflections)
    (hM : LocalDeterminationAndIntegrableAction)
    (htr : IsShiftInvariant ν) (P : UnitMirrorPair) (hP : IsReflectionPositiveAcross ν P) :
    IsSymmetricUnder ν P.reflect := by
  refine (hM ν P.reflect).1.2 fun H hobs hloc => ?_
  obtain ⟨-, hImg, -, -, hNorm, hRules, -, -, hRefl, -⟩ := id hA
  obtain ⟨Q, bQ, mQ⟩ := hloc
  obtain ⟨-, -, -, -, hnS, hn0, -, hrel⟩ := hRefl P
  set n := P.normal with hn
  set t := P.height with ht
  have hnn : 0 < n ⬝ᵥ n := by
    have h0 : n ⬝ᵥ n ≠ 0 := P.normal_dotProduct_self_ne_zero
    have h1 : 0 ≤ n ⬝ᵥ n := Finset.sum_nonneg fun i _ => mul_self_nonneg _
    exact lt_of_le_of_ne h1 h0.symm
  obtain ⟨M, hM'⟩ := bQ.exists_norm_le
  have hbound : ∀ x ∈ Q, -((∑ i, |n i|) * M) ≤ n ⬝ᵥ x := by
    intro x hx
    have h1 : |n ⬝ᵥ x| ≤ (∑ i, |n i|) * M := by
      rw [dotProduct, Finset.sum_mul]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (((Real.norm_eq_abs _).symm.le.trans
        (norm_le_pi_norm x i)).trans (hM' x hx)) (abs_nonneg _)
    exact (abs_le.mp h1).1
  obtain ⟨k, hk⟩ := exists_nat_ge ((t + (∑ i, |n i|) * M) / (n ⬝ᵥ n))
  have hk' : t + (∑ i, |n i|) * M ≤ (k : ℝ) * (n ⬝ᵥ n) := (div_le_iff₀ hnn).mp hk
  let v : LatticePoint (1 : ℝ) := ⟨(k : ℤ) • n, (latticeSubgroup (1 : ℝ)).zsmul_mem hnS _⟩
  have hv : (v : AmbientSpace) = (((k : ℤ) : ℝ)) • n := (Int.cast_smul_eq_zsmul ℝ (k : ℤ) n).symm
  set G := (shift v).actOn H with hG
  have hGmem : G ∈ unitRegionObservables ((shift v).setImage Q) := by
    rw [← hImg]
    exact ⟨H, ⟨hobs, mQ⟩, rfl⟩
  have hsub : (shift v).setImage Q ⊆ {x | t ≤ n ⬝ᵥ x} := by
    rintro _ ⟨x, hx, rfl⟩
    change t ≤ n ⬝ᵥ (x + (v : AmbientSpace))
    rw [dotProduct_add, hv, dotProduct_smul, smul_eq_mul]
    have := hbound x hx
    push_cast
    linarith
  have hGm : IsRegionMeasurable {x | t ≤ n ⬝ᵥ x} G := hGmem.2.mono (regionSigma_mono hsub) le_rfl
  have hGn := hNorm (shift v) H hobs
  have hGl : IsLocalObservable G := hGn.2.2 ⟨Q, bQ, mQ⟩
  have hside := integral_reflect_eq_of_halfSpace hA P hP G hGn.1 hGl hGm
  have hTobs := ((hNorm P.reflect) H hobs).1
  have hcomm : P.reflect.actOn G = (shift (-v)).actOn (P.reflect.actOn H) := by
    have h1 := hrel (-(k : ℤ)) (-v) (by
      rw [AddSubgroup.coe_neg, hv]
      push_cast
      rw [neg_smul])
    rw [neg_neg] at h1
    have h2 := (hRules P.reflect (shift v) H H hobs hobs).1
    have h3 := (hRules (shift (-v)) P.reflect H H hobs hobs).1
    rw [← h2, h1, h3]
  rw [hcomm] at hside
  calc ∫ U, P.reflect.actOn H U ∂ν
      = ∫ U, (shift (-v)).actOn (P.reflect.actOn H) U ∂ν := (htr (-v) _ hTobs).symm
    _ = ∫ U, G U ∂ν := hside
    _ = ∫ U, H U ∂ν := htr v H hobs
theorem isSymmetricUnder_of_mem_closure
    (hI : SymmetryProperties (1 : ℝ))
    (hA : ReflectionPositivity.MirrorHyperplanes.SymmetryActionAndReflections)
    (hM : LocalDeterminationAndIntegrableAction)
    (htr : IsShiftInvariant ν) (hrp : ∀ P : UnitMirrorPair, IsReflectionPositiveAcross ν P)
    {w : AmbientSpace ≃ₗ[ℝ] AmbientSpace} (hw : w ∈ Subgroup.closure axisAndDiagonalReflections) :
    ∀ r : UnitLatticeSymmetry, r.toFun = ⇑w → IsSymmetricUnder ν r := by
  have hgroup := (hM ν (LatticeSymmetry.refl 1)).2.2.1
  have hex : ∀ u : AmbientSpace ≃ₗ[ℝ] AmbientSpace,
      u ∈ Subgroup.closure axisAndDiagonalReflections →
      ∃ r : UnitLatticeSymmetry, r.toFun = ⇑u := fun u hu => by
    rw [← hyperoctahedralLinearGroup_eq_closure] at hu
    obtain ⟨r, hr⟩ := (hI.1 (latticeMotion u (0 : LatticePoint (1 : ℝ)))).mpr ⟨u, hu, 0, rfl⟩
    exact ⟨r, hr.trans (funext fun x => by simp [latticeMotion])⟩
  induction hw using Subgroup.closure_induction with
  | mem u hu =>
    intro r hr
    rcases hu with ⟨μ, h⟩ | ⟨μ, κ, hne, h⟩
    · let P : UnitMirrorPair := ⟨basisVec μ, 0, Or.inl ⟨⟨μ, rfl⟩, 0, by simp⟩⟩
      have e : r = P.reflect := latticeSymmetry_ext (hr.trans h)
      rw [e]
      exact isSymmetricUnder_reflect hA hM htr P (hrp P)
    · let P : UnitMirrorPair :=
        ⟨basisVec μ - basisVec κ, 0, Or.inr ⟨⟨μ, κ, hne, Or.inr rfl⟩, 0, by simp⟩⟩
      have e : r = P.reflect := latticeSymmetry_ext (hr.trans h)
      rw [e]
      exact isSymmetricUnder_reflect hA hM htr P (hrp P)
  | one =>
    intro r hr
    have e : r = LatticeSymmetry.refl 1 := latticeSymmetry_ext hr
    rw [e]
    exact hgroup.1
  | mul u u' hu hu' ih ih' =>
    intro r hr
    obtain ⟨r₁, h₁⟩ := hex u hu
    obtain ⟨r₂, h₂⟩ := hex u' hu'
    have e : r = r₁ * r₂ := latticeSymmetry_ext (by
      rw [hr]
      change _ = r₁.toFun ∘ r₂.toFun
      rw [h₁, h₂]
      rfl)
    rw [e]
    exact hgroup.2.1 r₁ r₂ (ih r₁ h₁) (ih' r₂ h₂)
  | inv u hu ih =>
    intro r hr
    obtain ⟨r₁, h₁⟩ := hex u hu
    refine (hgroup.2.2 r₁ (ih r₁ h₁)).2 r ⟨fun x => ?_, fun x => ?_⟩
    · rw [hr, h₁]
      exact u.symm_apply_apply x
    · rw [hr, h₁]
      exact u.apply_symm_apply x
end Symmetry
theorem exists_perm_apply_pair {α β α' β' : Fin 4} (h : α ≠ β) (h' : α' ≠ β') :
    ∃ σ : Equiv.Perm (Fin 4), σ α = α' ∧ σ β = β' := by
  refine ⟨Equiv.swap (Equiv.swap α α' β) β' * Equiv.swap α α', ?_, ?_⟩
  · have h1 : α' ≠ Equiv.swap α α' β := by
      intro e
      have : Equiv.swap α α' α = Equiv.swap α α' β := by rw [Equiv.swap_apply_left]; exact e
      exact h ((Equiv.swap α α').injective this)
    simp [Equiv.swap_apply_of_ne_of_ne h1 h']
  · simp
theorem exists_symmetry_mapping_face (hI : SymmetryProperties (1 : ℝ))
    (p p' : ElementaryPlaquette (1 : ℝ)) :
    ∃ r : UnitLatticeSymmetry, p'.cornerSet = r.pointMap '' p.cornerSet := by
  obtain ⟨σ, h1, h2⟩ := exists_perm_apply_pair p.lowAxis_lt_highAxis.ne p'.lowAxis_lt_highAxis.ne
  set w := coordPermutation σ⁻¹ with hw
  have hstep : ∀ μ, w (axisStep 1 μ : AmbientSpace) = (axisStep 1 (σ μ) : AmbientSpace) := by
    intro μ
    funext i
    rw [hw, coordPermutation_apply]
    simp only [axisStep, Pi.single_apply]
    by_cases e : i = σ μ
    · subst e
      simp
    · have : σ.symm i ≠ μ := fun h => e (by rw [← h]; simp)
      simp [this, e]
  have hcorner : w (p.corner : AmbientSpace) ∈ latticeSubgroup (1 : ℝ) := by
    obtain ⟨m, hm⟩ := p.corner.2
    exact ⟨fun i => m (σ⁻¹ i), fun i => by rw [hw, coordPermutation_apply, hm]⟩
  let v : LatticePoint (1 : ℝ) := p'.corner - ⟨w (p.corner : AmbientSpace), hcorner⟩
  obtain ⟨r, hr⟩ := (hI.1 (latticeMotion w v)).mpr ⟨w, coordPermutation_mem _, v, rfl⟩
  refine ⟨r, ?_⟩
  have hmap : ∀ x : LatticePoint (1 : ℝ),
      (r.pointMap x : AmbientSpace) = w (x : AmbientSpace) + (v : AmbientSpace) := fun x => by
    change r.toFun (x : AmbientSpace) = _
    rw [hr]
    rfl
  have e0 : r.pointMap p.corner = p'.corner := Subtype.ext (by
    rw [hmap]
    simp [v])
  have e1 : ∀ (x : LatticePoint (1 : ℝ)) (μ : Fin 4),
      r.pointMap (x + axisStep 1 μ) = r.pointMap x + axisStep 1 (σ μ) := fun x μ =>
    Subtype.ext (by
      rw [AddSubgroup.coe_add, hmap, hmap, AddSubgroup.coe_add, map_add, hstep]
      abel)
  simp only [ElementaryPlaquette.cornerSet, image_insert_eq, image_singleton, e1, e0, h1, h2]
theorem summary_holds
    (hS : FieldSpaceAndSymmetries)
    (hA : ReflectionPositivity.MirrorHyperplanes.SymmetryActionAndReflections)
    (hM : LocalDeterminationAndIntegrableAction)
    (hAct : LatticeSymmetryActions) : Summary := by
  obtain ⟨-, -, hF, hI, hCov, -⟩ := hS 1 one_pos
  have hmem : ∀ r : UnitLatticeSymmetry, r.toFun ∈ affineHyperoctahedralMaps 1 :=
    fun r => (hI.1 r.toFun).mp ⟨r, rfl⟩
  have hunique : ∀ (r : UnitLatticeSymmetry) (p : ElementaryPlaquette (1 : ℝ)),
      ∃! q : ElementaryPlaquette (1 : ℝ), q.cornerSet = r.pointMap '' p.cornerSet :=
    fun r p => (hAct 1 one_pos r r (hmem r) (hmem r)).2.1.1 p
  have hcorners : ∀ (r : UnitLatticeSymmetry) (p : ElementaryPlaquette (1 : ℝ)),
      (r.plaquetteMap p).cornerSet = r.pointMap '' p.cornerSet :=
    fun r p => (hI.2 r).2.2.1 p
  have hinv : PositiveMeasuresAreSymmetric := by
    rintro ν ⟨hprob, htr, hrp⟩ r
    obtain ⟨w, hw, v, hr⟩ := hmem r
    rw [hyperoctahedralLinearGroup_eq_closure] at hw
    obtain ⟨r₁, h₁⟩ : ∃ r₁ : UnitLatticeSymmetry, r₁.toFun = ⇑w := by
      rw [← hyperoctahedralLinearGroup_eq_closure] at hw
      obtain ⟨r₁, h⟩ := (hI.1 (latticeMotion w (0 : LatticePoint (1 : ℝ)))).mpr ⟨w, hw, 0, rfl⟩
      exact ⟨r₁, h.trans (funext fun x => by simp [latticeMotion])⟩
    have hg := (hM ν (LatticeSymmetry.refl 1)).2.2.1
    have e : r = shift v * r₁ := latticeSymmetry_ext (by
      rw [hr]
      change _ = (shift v).toFun ∘ r₁.toFun
      rw [h₁]
      rfl)
    rw [e]
    exact hg.2.1 _ _ (htr v) (isSymmetricUnder_of_mem_closure hI hA hM htr hrp hw r₁ h₁)
  have htrans : SymmetriesActTransitivelyOnFaces := by
    intro p p'
    obtain ⟨r, hr⟩ := exists_symmetry_mapping_face hI p p'
    exact ⟨r, (hunique r p).unique (hcorners r p) hr⟩
  refine ⟨⟨hI.1, hyperoctahedralLinearGroup_eq_closure⟩, hinv, ?_, ?_, htrans, ?_⟩
  · exact fun p => ⟨(hF p).2.2.2, fun U => (hF p).2.1 U⟩
  · exact fun r p => ⟨hunique r p, hcorners r p, (hI.2 r).2.2.2.2.1 p,
      funext fun U => hCov.1 r p U⟩
  · intro ν hν p p'
    obtain ⟨r, rfl⟩ := htrans p p'
    have hcont : Continuous fun U : GaugeField (1 : ℝ) => ((faceEnergy U p : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (hF p).2.2.1
    have hobs : IsBoundedObservable fun U : GaugeField (1 : ℝ) => ((faceEnergy U p : ℝ) : ℂ) := by
      refine ⟨hcont.measurable, 2, fun U => ?_⟩
      obtain ⟨h0, h2⟩ := (hF p).2.1 U
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
      exact h2
    have h := hinv ν hν r _ hobs
    have hreal : ∀ q : ElementaryPlaquette (1 : ℝ),
        ∫ U : GaugeField (1 : ℝ), ((faceEnergy U q : ℝ) : ℂ) ∂ν =
          ((∫ U : GaugeField (1 : ℝ), faceEnergy U q ∂ν : ℝ) : ℂ) := fun q =>
      integral_complex_ofReal (f := fun U : GaugeField (1 : ℝ) => faceEnergy U q)
    have e : ∫ U, r.actOn (fun U : GaugeField (1 : ℝ) => ((faceEnergy U p : ℝ) : ℂ)) U ∂ν =
        ∫ U : GaugeField (1 : ℝ), ((faceEnergy U (r.plaquetteMap p) : ℝ) : ℂ) ∂ν :=
      integral_congr_ae (Filter.Eventually.of_forall fun U => by
        change ((faceEnergy (r.pullbackField U) p : ℝ) : ℂ) = _
        rw [hCov.1 r p U])
    rw [e, hreal, hreal] at h
    exact (Complex.ofReal_injective h).symm
end YangMills.Construction.InfiniteLattice.UnitSymmetriesAndFaces
end
