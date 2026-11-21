import YangMills.Construction.RunningCouplingSlope.DensityOfTheStepIsAnalyticAtParametersProof
import YangMills.Construction.ClusterExpansionOfAStep.PlaquettesUnderGaugesAndMoves
import YangMills.Construction.ColdStepAtMirrorFrames.CompositesAtAPoint
import YangMills.Construction.ResponseInTheExpansion.KernelsOfAShare
import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenAndTheirLaws
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation Calculus
namespace WeightedResponses
section Bonds
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem bondGradNorm_le_of_line_derivs {A : BondField ι → ℝ} {η : BondField ι} {b : ι} {B : ℝ} (hB : 0 ≤ B)
    (hd : DifferentiableAt ℝ A η)
    (h : ∀ e : BondVector, ‖e‖ = 1 → |deriv (fun τ : ℝ => A (η + Pi.single b (τ • e))) 0| ≤ B) :
    bondGradNorm A b η ≤ B := by
  unfold bondGradNorm
  refine ContinuousLinearMap.opNorm_le_bound _ hB fun e => ?_
  by_cases he : e = 0
  · simp [he]
  have hn : ‖e‖ ≠ 0 := norm_ne_zero_iff.2 he
  set u : BondVector := ‖e‖⁻¹ • e with hu
  have hu1 : ‖u‖ = 1 := by
    rw [hu, norm_smul, norm_inv, norm_norm]
    field_simp
  have hl : HasDerivAt (fun τ : ℝ => η + Pi.single b (τ • u)) (Pi.single b u) 0 := by
    have e1 : (fun τ : ℝ => η + Pi.single b (τ • u)) = fun τ : ℝ => η + τ • (Pi.single b u : BondField ι) := by
      funext τ
      rw [Pi.single_smul]
    rw [e1]
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single b u : BondField ι)).const_add η
  have hd' : HasFDerivAt A (fderiv ℝ A η) (η + Pi.single b ((0 : ℝ) • u)) := by
    simpa using hd.hasFDerivAt
  have h1 := (hd'.comp_hasDerivAt (0 : ℝ) hl).deriv
  have h2 := h u hu1
  have h3 : deriv (A ∘ fun τ : ℝ => η + Pi.single b (τ • u)) 0 =
      deriv (fun τ : ℝ => A (η + Pi.single b (τ • u))) 0 := rfl
  rw [h3] at h1
  rw [h1] at h2
  have e2 : e = ‖e‖ • u := by
    rw [hu, smul_smul, mul_inv_cancel₀ hn, one_smul]
  show ‖fderiv ℝ A η (Pi.single b e)‖ ≤ B * ‖e‖
  rw [e2, Pi.single_smul, map_smul, norm_smul, norm_norm, Real.norm_eq_abs, mul_comm]
  simp only [norm_smul, norm_norm, hu1, mul_one]
  exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
end Bonds
section Lines
variable {F : BlockFrame}
private theorem toImaginary_add_smul (v e : BondVector) (τ : ℝ) :
    toImaginary (v + τ • e) = toImaginary v + τ • toImaginary e := by apply _root_.YangMills.DeltaSharedProofs.p501185 <;> assumption
theorem stepCoordinates_add_single (η : StepVariable (finiteCells F)) (b : ↥(chordBonds (finiteCells F)))
    (e : BondVector) (τ : ℝ) (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (η + Pi.single b (τ • e)) x i =
      stepCoordinates η x i +
        τ • directionCoordinate (Sum.inl (b.1.1, b.1.2, toImaginary e) : ChartDirection F) x i := by
  by_cases hb : b.1.1 = x ∧ b.1.2 = i
  · obtain ⟨rfl, rfl⟩ := hb
    have h : (b.1.1, b.1.2) ∈ chordBonds (finiteCells F) := b.2
    have hbb : (⟨(b.1.1, b.1.2), h⟩ : ↥(chordBonds (finiteCells F))) = b := Subtype.ext rfl
    simp only [stepCoordinates, dif_pos h, directionCoordinate, and_self, if_true, Pi.add_apply, hbb,
      Pi.single_eq_same, toImaginary_add_smul]
  · have hsl : directionCoordinate (Sum.inl (b.1.1, b.1.2, toImaginary e) : ChartDirection F) x i = 0 := by
      simp only [directionCoordinate]
      exact if_neg hb
    rw [hsl, smul_zero, add_zero]
    by_cases h : (x, i) ∈ chordBonds (finiteCells F)
    · have hne : (⟨(x, i), h⟩ : ↥(chordBonds (finiteCells F))) ≠ b := fun hh => hb (by
        rw [← hh]
        exact ⟨rfl, rfl⟩)
      simp only [stepCoordinates, dif_pos h, Pi.add_apply, Pi.single_eq_of_ne hne, add_zero]
    · simp only [stepCoordinates, dif_neg h]
theorem interpolatedCoords_add_single (s a ρA : ℝ) (m : ℕ) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) (b : ↥(chordBonds (finiteCells F))) (e : BondVector) (τ : ℝ) :
    interpolatedCoords s a ρA m V (η + Pi.single b (τ • e)) = fun x i =>
      interpolatedCoords s a ρA m V η x i +
        τ • directionCoordinate (Sum.inl (b.1.1, b.1.2, toImaginary e) : ChartDirection F) x i := by
  funext x i
  simp only [interpolatedCoords]
  rw [stepCoordinates_add_single, add_assoc]
theorem extendByZero_add_single {ι : Type} [Fintype ι] [DecidableEq ι]
    (j : ι → ↥(chordBonds (finiteCells F))) (Λ : Finset ι) {i : ι} (hi : i ∈ Λ) (ζ : BondField ι)
    (u : BondVector) :
    _root_.YangMills.Construction.Interpolation.extendByZero j Λ (ζ + Pi.single i u) = _root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ + Pi.single (j i) u := by
  funext b
  simp only [_root_.YangMills.Construction.Interpolation.extendByZero, Pi.add_apply]
  have e1 : ∀ i' : ι, (if j i' = b then ζ i' + (Pi.single i u : BondField ι) i' else 0) =
      (if j i' = b then ζ i' else 0) + (if j i' = b then (Pi.single i u : BondField ι) i' else 0) := by
    intro i'
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun i' _ => e1 i', Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single i]
  · by_cases hb : j i = b
    · subst hb
      simp
    · have hne : b ≠ j i := fun h => hb h.symm
      simp [hb]
  · intro i' _ hne
    simp [Pi.single_eq_of_ne hne]
  · intro h
    exact absurd hi h
def chartLine (E : (F.Site F.depth → Fin 4 → imaginaryQuaternions) → ℝ)
    (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (b : F.Site F.depth × Fin 4)
    (X : imaginaryQuaternions) (τ : ℝ) : ℝ :=
  E fun x i => w x i + τ • directionCoordinate (Sum.inl (b.1, b.2, X) : ChartDirection F) x i
theorem comp_interpolatedCoords_add_single (E : (F.Site F.depth → Fin 4 → imaginaryQuaternions) → ℝ)
    (s a ρA : ℝ) (m : ℕ) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) (b : ↥(chordBonds (finiteCells F))) (e : BondVector) (τ : ℝ) :
    E (interpolatedCoords s a ρA m V (η + Pi.single b (τ • e))) =
      chartLine E (interpolatedCoords s a ρA m V η) b.1 (toImaginary e) τ := by
  rw [interpolatedCoords_add_single]
  rfl
theorem iteratedFDeriv_comp_sum (hc : CompositeDerivativesAtPoint) {φ : ℝ → ℝ} (hφ : AnalyticAt ℝ φ 0)
    (k : ℕ) :
    iteratedFDeriv ℝ k (fun σ : Fin k → ℝ => φ (∑ l, σ l)) 0 (fun l => Pi.single l 1) =
      iteratedDeriv k φ 0 := by
  let g : (Fin k → ℝ) →L[ℝ] ℝ := ∑ l, ContinuousLinearMap.proj l
  have hg : ∀ σ, g σ = ∑ l, σ l := by
    intro σ
    simp [g]
  have h := hc.1 k (Fin k → ℝ) ℝ ℝ g φ 0 (by rwa [map_zero]) fun l => Pi.single l 1
  have e : (φ ∘ g) = fun σ : Fin k → ℝ => φ (∑ l, σ l) := by
    funext σ
    simp [hg]
  rw [e] at h
  rw [h, map_zero, iteratedDeriv_eq_iteratedFDeriv]
  congr 1
  funext m
  simp [hg]
private theorem chartLine_derivs_of_repeated (hc : CompositeDerivativesAtPoint) {φ : ℝ → ℝ}
    {G : ∀ k : ℕ, (Fin k → ℝ) → ℝ}
    (hG : ∀ k σ, G k σ = φ (∑ l, σ l)) (hA : AnalyticAt ℝ (G 1) 0) :
    AnalyticAt ℝ φ 0 ∧ iteratedFDeriv ℝ 1 (G 1) 0 (fun l => Pi.single l 1) = deriv φ 0 ∧
      iteratedFDeriv ℝ 2 (G 2) 0 (fun l => Pi.single l 1) = deriv (deriv φ) 0 := by
  have han : AnalyticAt ℝ φ 0 := by
    have e : φ = G 1 ∘ (ContinuousLinearMap.pi fun _ : Fin 1 => ContinuousLinearMap.id ℝ ℝ) := by
      funext τ
      simp [hG]
    rw [e]
    refine AnalyticAt.comp ?_ (ContinuousLinearMap.analyticAt _ _)
    exact hA
  have e1 : G 1 = fun σ : Fin 1 → ℝ => φ (∑ l, σ l) := funext (hG 1)
  have e2 : G 2 = fun σ : Fin 2 → ℝ => φ (∑ l, σ l) := funext (hG 2)
  refine ⟨han, ?_, ?_⟩
  · rw [e1, iteratedFDeriv_comp_sum hc han 1, iteratedDeriv_one]
  · rw [e2, iteratedFDeriv_comp_sum hc han 2, iteratedDeriv_succ, iteratedDeriv_one]
private theorem expUnit_zero_aux : expUnit (0 : imaginaryQuaternions) = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
private theorem leftTranslate_repeated {k : ℕ} (σ : Fin k → ℝ)
    (p : F.Site F.depth × Fin 4 × imaginaryQuaternions) (V : F.GaugeField F.top) :
    leftTranslate
      (fun y i => ∑ l, σ l • directionMove ((fun _ : Fin k => (Sum.inl p : ChartDirection F)) l) y i) V = V := by
  funext y i
  simp [leftTranslate, directionMove, expUnit_zero_aux]
private theorem directionCoordinate_repeated_sum {k : ℕ} (σ : Fin k → ℝ) (q : ChartDirection F)
    (x : F.Site F.depth) (i : Fin 4) :
    ∑ l, σ l • directionCoordinate ((fun _ : Fin k => q) l) x i = (∑ l, σ l) • directionCoordinate q x i :=
  Finset.sum_smul.symm
private theorem directionReach_const {k : ℕ} (hk : 1 ≤ k) (Y : F.Cell) (q : ChartDirection F) :
    directionReach Y (fun _ : Fin k => q) = cellSupDist Y (directionCell q) := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  exact Finset.sup_const Finset.univ_nonempty _
theorem cellEnergyShare_line_bounds (hc : CompositeDerivativesAtPoint) {a δ : ℝ} {Y : F.Cell}
    {w : F.Site F.depth → Fin 4 → imaginaryQuaternions} {V : F.GaugeField F.top} {Ck : ℕ → ℝ}
    (hk : ∀ (k : ℕ) (q : Fin k → ChartDirection F), AnalyticAt ℝ (cellEnergyAlong a Y w V q) 0 ∧
      (1 ≤ k → (∀ l, ‖directionVector (q l)‖ = 1) →
        |cellEnergyKernel a Y w V q| ≤ Ck k * Real.exp (-(δ * directionReach Y q))))
    (b : F.Site F.depth × Fin 4) {X : imaginaryQuaternions} (hX : ‖X‖ = 1) :
    AnalyticAt ℝ (chartLine (fun u => cellEnergyShare a Y u V) w b X) 0 ∧
      |deriv (chartLine (fun u => cellEnergyShare a Y u V) w b X) 0| ≤
        Ck 1 * Real.exp (-(δ * cellSupDist Y (enclosingCell b.1))) ∧
      |deriv (deriv (chartLine (fun u => cellEnergyShare a Y u V) w b X)) 0| ≤
        Ck 2 * Real.exp (-(δ * cellSupDist Y (enclosingCell b.1))) := by
  set q₀ : ChartDirection F := Sum.inl (b.1, b.2, X) with hq₀
  have hG : ∀ (k : ℕ) (σ : Fin k → ℝ), cellEnergyAlong a Y w V (fun _ : Fin k => q₀) σ =
      chartLine (fun u => cellEnergyShare a Y u V) w b X (∑ l, σ l) := by
    intro k σ
    unfold cellEnergyAlong chartLine
    rw [hq₀, leftTranslate_repeated]
    simp only [directionCoordinate_repeated_sum]
  obtain ⟨h0, h1, h2⟩ :=
    chartLine_derivs_of_repeated hc (G := fun k => cellEnergyAlong a Y w V (fun _ : Fin k => q₀)) hG (hk 1 _).1
  have hu : ∀ (k : ℕ) (l : Fin k), ‖directionVector ((fun _ : Fin k => q₀) l)‖ = 1 := fun _ _ => hX
  have b1 := (hk 1 _).2 le_rfl (hu 1)
  have b2 := (hk 2 _).2 (by norm_num) (hu 2)
  rw [directionReach_const le_rfl] at b1
  rw [directionReach_const (by norm_num)] at b2
  unfold cellEnergyKernel at b1 b2
  rw [h1] at b1
  rw [h2] at b2
  exact ⟨h0, b1, b2⟩
theorem minimalSiteShare_line_bounds (hc : CompositeDerivativesAtPoint) {a δ : ℝ} {y : F.Site F.depth}
    {w : F.Site F.depth → Fin 4 → imaginaryQuaternions} {V : F.GaugeField F.top} {Ck : ℕ → ℝ}
    (hk : ∀ (k : ℕ) (q : Fin k → ChartDirection F), AnalyticAt ℝ (siteShareAlong a y w V q) 0 ∧
      (1 ≤ k → (∀ l, ‖directionVector (q l)‖ = 1) →
        |siteShareMixedDeriv a y w V q| ≤ Ck k * Real.exp (-(δ * directionReach (enclosingCell y) q))))
    (b : F.Site F.depth × Fin 4) {X : imaginaryQuaternions} (hX : ‖X‖ = 1) :
    AnalyticAt ℝ (chartLine (fun u => minimalSiteShare a y (chartedField u V)) w b X) 0 ∧
      |deriv (chartLine (fun u => minimalSiteShare a y (chartedField u V)) w b X) 0| ≤
        Ck 1 * Real.exp (-(δ * cellSupDist (enclosingCell y) (enclosingCell b.1))) ∧
      |deriv (deriv (chartLine (fun u => minimalSiteShare a y (chartedField u V)) w b X)) 0| ≤
        Ck 2 * Real.exp (-(δ * cellSupDist (enclosingCell y) (enclosingCell b.1))) := by
  set q₀ : ChartDirection F := Sum.inl (b.1, b.2, X) with hq₀
  have hG : ∀ (k : ℕ) (σ : Fin k → ℝ), siteShareAlong a y w V (fun _ : Fin k => q₀) σ =
      chartLine (fun u => minimalSiteShare a y (chartedField u V)) w b X (∑ l, σ l) := by
    intro k σ
    unfold siteShareAlong chartLine
    rw [hq₀, leftTranslate_repeated]
    simp only [directionCoordinate_repeated_sum]
  obtain ⟨h0, h1, h2⟩ :=
    chartLine_derivs_of_repeated hc (G := fun k => siteShareAlong a y w V (fun _ : Fin k => q₀)) hG (hk 1 _).1
  have hu : ∀ (k : ℕ) (l : Fin k), ‖directionVector ((fun _ : Fin k => q₀) l)‖ = 1 := fun _ _ => hX
  have b1 := (hk 1 _).2 le_rfl (hu 1)
  have b2 := (hk 2 _).2 (by norm_num) (hu 2)
  rw [directionReach_const le_rfl] at b1
  rw [directionReach_const (by norm_num)] at b2
  unfold siteShareMixedDeriv at b1 b2
  rw [h1] at b1
  rw [h2] at b2
  exact ⟨h0, b1, b2⟩
private theorem chartLine_shift (E : (F.Site F.depth → Fin 4 → imaginaryQuaternions) → ℝ)
    (u : F.Site F.depth → Fin 4 → imaginaryQuaternions) (b : F.Site F.depth × Fin 4)
    (X : imaginaryQuaternions) (θ τ : ℝ) :
    chartLine E (fun x i => u x i + θ • directionCoordinate (Sum.inl (b.1, b.2, X) : ChartDirection F) x i) b X τ =
      chartLine E u b X (θ + τ) := by
  unfold chartLine
  congr 1
  funext x i
  rw [add_assoc, add_smul]
private theorem abs_chartLine_sub_le {E : (F.Site F.depth → Fin 4 → imaginaryQuaternions) → ℝ}
    {u : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    {b : F.Site F.depth × Fin 4} {X : imaginaryQuaternions} {B t : ℝ} (ht : 0 ≤ t)
    (hk : ∀ θ, 0 ≤ θ → θ ≤ t →
      AnalyticAt ℝ (chartLine E
        (fun x i => u x i + θ • directionCoordinate (Sum.inl (b.1, b.2, X) : ChartDirection F) x i) b X) 0 ∧
      |deriv (chartLine E
        (fun x i => u x i + θ • directionCoordinate (Sum.inl (b.1, b.2, X) : ChartDirection F) x i) b X) 0| ≤ B) :
    |chartLine E u b X t - chartLine E u b X 0| ≤ B * t := by
  set φ := chartLine E u b X with hφ
  have e : ∀ θ, chartLine E
      (fun x i => u x i + θ • directionCoordinate (Sum.inl (b.1, b.2, X) : ChartDirection F) x i) b X =
      fun τ => φ (θ + τ) := fun θ => funext fun τ => chartLine_shift E u b X θ τ
  have han : ∀ θ, 0 ≤ θ → θ ≤ t → AnalyticAt ℝ φ θ := by
    intro θ h0 h1
    have h := (hk θ h0 h1).1
    rw [e] at h
    have e2 : φ = (fun τ => φ (θ + τ)) ∘ fun v => v - θ := by
      funext v
      simp
    rw [e2]
    refine AnalyticAt.comp (g := fun τ => φ (θ + τ)) (f := fun v => v - θ) ?_
      (analyticAt_id.sub analyticAt_const)
    simpa using h
  have hder : ∀ θ ∈ Set.Icc (0 : ℝ) t, HasDerivWithinAt φ (deriv φ θ) (Set.Icc 0 t) θ := fun θ hθ =>
    (han θ hθ.1 hθ.2).differentiableAt.hasDerivAt.hasDerivWithinAt
  have hbound : ∀ θ ∈ Set.Ico (0 : ℝ) t, ‖deriv φ θ‖ ≤ B := by
    intro θ hθ
    have h := (hk θ hθ.1 hθ.2.le).2
    rw [e] at h
    have e3 : deriv (fun τ => φ (θ + τ)) 0 = deriv φ (θ + 0) := deriv_comp_const_add φ θ 0
    rwa [e3, add_zero, ← Real.norm_eq_abs] at h
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' (f := φ) hder hbound t (Set.right_mem_Icc.2 ht)
  rwa [sub_zero, Real.norm_eq_abs] at hmv
theorem abs_sub_le_sum_of_line_derivs {E : (F.Site F.depth → Fin 4 → imaginaryQuaternions) → ℝ}
    {D : Set (F.Site F.depth → Fin 4 → imaginaryQuaternions)}
    {B₁ : F.Site F.depth × Fin 4 → ℝ} {w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (S : Finset (F.Site F.depth × Fin 4))
    (hline : ∀ u ∈ D, ∀ b ∈ S, ∀ X : imaginaryQuaternions, ‖X‖ = 1 →
      AnalyticAt ℝ (chartLine E u b X) 0 ∧ |deriv (chartLine E u b X) 0| ≤ B₁ b)
    (hoff : ∀ b, b ∉ S → w' b.1 b.2 = w b.1 b.2)
    (hseg : ∀ u : F.Site F.depth → Fin 4 → imaginaryQuaternions,
      (∀ z i, ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ u z i = w z i + θ • (w' z i - w z i)) → u ∈ D) :
    |E w' - E w| ≤ ∑ b ∈ S, B₁ b * ‖w' b.1 b.2 - w b.1 b.2‖ := by
  classical
  set hyb : Finset (F.Site F.depth × Fin 4) → F.Site F.depth → Fin 4 → imaginaryQuaternions :=
    fun A z i => if (z, i) ∈ A then w' z i else w z i with hhyb
  have hstep : ∀ A : Finset (F.Site F.depth × Fin 4), A ⊆ S →
      |E (hyb A) - E w| ≤ ∑ b ∈ A, B₁ b * ‖w' b.1 b.2 - w b.1 b.2‖ := by
    intro A
    induction A using Finset.induction_on with
    | empty =>
      intro _
      have : hyb ∅ = w := by
        funext z i
        simp [hhyb]
      simp [this]
    | insert b₀ A hb₀ ih =>
      intro hsub
      have hb₀S : b₀ ∈ S := hsub (Finset.mem_insert_self _ _)
      have ihA := ih fun b hb => hsub (Finset.mem_insert_of_mem hb)
      rw [Finset.sum_insert hb₀]
      set t := ‖w' b₀.1 b₀.2 - w b₀.1 b₀.2‖ with ht
      have hone : |E (hyb (insert b₀ A)) - E (hyb A)| ≤ B₁ b₀ * t := by
        by_cases ht0 : t = 0
        · have h0 : w' b₀.1 b₀.2 = w b₀.1 b₀.2 := sub_eq_zero.1 (norm_eq_zero.1 (ht ▸ ht0))
          have e1 : hyb (insert b₀ A) = hyb A := by
            funext z i
            by_cases hz : (z, i) = b₀
            · subst hz
              simp [hhyb, hb₀, h0]
            · simp [hhyb, Finset.mem_insert, hz]
          rw [e1, ht0]
          simp
        · have htp : 0 < t := lt_of_le_of_ne (norm_nonneg _) (Ne.symm ht0)
          set X : imaginaryQuaternions := t⁻¹ • (w' b₀.1 b₀.2 - w b₀.1 b₀.2) with hX
          have hX1 : ‖X‖ = 1 := by
            rw [hX, norm_smul, norm_inv, Real.norm_of_nonneg htp.le, ← ht]
            field_simp
          have hA0 : hyb A b₀.1 b₀.2 = w b₀.1 b₀.2 := by simp [hhyb, hb₀]
          set sh : ℝ → F.Site F.depth → Fin 4 → imaginaryQuaternions := fun θ x i =>
            hyb A x i + θ • directionCoordinate (Sum.inl (b₀.1, b₀.2, X) : ChartDirection F) x i with hsh'
          have hsh : ∀ θ : ℝ, ∀ z i,
              sh θ z i = if (z, i) = b₀ then w b₀.1 b₀.2 + θ • X else hyb A z i := by
            intro θ z i
            by_cases hz : (z, i) = b₀
            · subst hz
              simp only [hsh', directionCoordinate, if_true]
              simp [hA0]
            · have hne : ¬ (b₀.1 = z ∧ b₀.2 = i) := fun h => hz (by
                rw [← h.1, ← h.2])
              simp [hsh', directionCoordinate, hz, hne]
          have e1 : sh t = hyb (insert b₀ A) := by
            funext z i
            rw [hsh]
            by_cases hz : (z, i) = b₀
            · subst hz
              simp only [if_true]
              have : t • X = w' (z, i).1 (z, i).2 - w (z, i).1 (z, i).2 := by
                rw [hX, smul_smul, mul_inv_cancel₀ ht0, one_smul]
              rw [this]
              simp [hhyb]
            · simp [hhyb, Finset.mem_insert, hz]
          have e0 : sh 0 = hyb A := by
            funext z i
            simp [hsh']
          have hk : ∀ θ, 0 ≤ θ → θ ≤ t → AnalyticAt ℝ (chartLine E (sh θ) b₀ X) 0 ∧
              |deriv (chartLine E (sh θ) b₀ X) 0| ≤ B₁ b₀ := by
            intro θ h0 h1
            refine hline _ (hseg _ fun z i => ?_) b₀ hb₀S X hX1
            rw [hsh]
            by_cases hz : (z, i) = b₀
            · subst hz
              refine ⟨θ / t, by positivity, (div_le_one htp).2 h1, ?_⟩
              simp only [if_true]
              have : θ • X = (θ / t) • (w' (z, i).1 (z, i).2 - w (z, i).1 (z, i).2) := by
                rw [hX, smul_smul, div_eq_mul_inv]
              rw [this]
            · simp only [hz, if_false, hhyb]
              by_cases hzA : (z, i) ∈ A
              · exact ⟨1, zero_le_one, le_rfl, by simp [hzA]⟩
              · exact ⟨0, le_rfl, zero_le_one, by simp [hzA]⟩
          have hm := abs_chartLine_sub_le (E := E) (u := hyb A) (b := b₀) (X := X) htp.le hk
          have e2 : chartLine E (hyb A) b₀ X t = E (hyb (insert b₀ A)) := by
            rw [← e1]
            rfl
          have e3 : chartLine E (hyb A) b₀ X 0 = E (hyb A) := by
            show E (sh 0) = E (hyb A)
            rw [e0]
          rwa [e2, e3] at hm
      calc |E (hyb (insert b₀ A)) - E w|
          ≤ |E (hyb (insert b₀ A)) - E (hyb A)| + |E (hyb A) - E w| := abs_sub_le _ _ _
        _ ≤ _ := add_le_add hone ihA
  have hfin : hyb S = w' := by
    funext z i
    by_cases hz : (z, i) ∈ S
    · simp [hhyb, hz]
    · simp only [hhyb, hz, if_false]
      exact (hoff (z, i) hz).symm
  have := hstep S subset_rfl
  rwa [hfin] at this
end Lines
end WeightedResponses
end YangMills.Construction
end
