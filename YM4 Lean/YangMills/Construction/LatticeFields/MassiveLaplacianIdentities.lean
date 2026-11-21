import YangMills.Construction.LatticeFields.CompressedGreenDecayProof
import YangMills.Construction.LatticeFields.KernelProjectionUnique
import YangMills.Construction.LatticeFields.MassiveLaplacianForms
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFields.MassiveLaplacianForms
variable {d N : ℕ}
private theorem torus_finite (N : ℕ) [NeZero N] (ℓ : Fin d → ℕ) (hℓ : ∀ μ, 1 ≤ ℓ μ) :
    Finite (LatticeSite N (LatticeShape.torus ℓ hℓ)) := by apply _root_.YangMills.Construction.LatticeFields.WeightConjProjComplProof.finite_torusSites <;> assumption
private theorem sum_plaquetteDirection_ite (ρ : Fin d) (G : Fin d → ℝ) :
    ∑ p : PlaquetteDirection d,
        ((if p.1.2 = ρ then G p.1.1 else 0) + (if p.1.1 = ρ then G p.1.2 else 0)) =
      ∑ μ, G μ - G ρ := by
  classical
  have hsub : ∀ f : Fin d × Fin d → ℝ,
      ∑ p : PlaquetteDirection d, f p.1 = ∑ μ, ∑ ν, if μ < ν then f (μ, ν) else 0 := by
    intro f
    rw [← Finset.sum_subtype (Finset.univ.filter fun q : Fin d × Fin d => q.1 < q.2)
      (by simp) f, Finset.sum_filter, Fintype.sum_prod_type]
  rw [hsub fun q => (if q.2 = ρ then G q.1 else 0) + (if q.1 = ρ then G q.2 else 0)]
  have hfirst : ∀ μ, ∑ ν, (if μ < ν then (if ν = ρ then G μ else 0) else 0) =
      if μ < ρ then G μ else 0 := by
    intro μ
    rw [Finset.sum_eq_single ρ]
    · simp
    · intro ν _ hν
      simp [hν]
    · simp
  have hsecond : ∑ μ, ∑ ν, (if μ < ν then (if μ = ρ then G ν else 0) else 0) =
      ∑ ν, if ρ < ν then G ν else 0 := by
    rw [Finset.sum_eq_single ρ]
    · simp
    · intro μ _ hμ
      simp [hμ]
    · simp
  have hsplit : ∀ μ ν : Fin d,
      (if μ < ν then ((if ν = ρ then G μ else 0) + (if μ = ρ then G ν else 0)) else 0) =
        (if μ < ν then (if ν = ρ then G μ else 0) else 0) +
          (if μ < ν then (if μ = ρ then G ν else 0) else 0) := by
    intro μ ν
    split_ifs <;> simp
  simp only [hsplit, Finset.sum_add_distrib, hfirst, hsecond]
  have hall : ∑ μ, G μ = ∑ μ, (if μ < ρ then G μ else 0) + ∑ μ, (if ρ < μ then G μ else 0) +
      G ρ := by
    have : G ρ = ∑ μ, if μ = ρ then G μ else 0 := by simp
    rw [this, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rcases lt_trichotomy μ ρ with h | h | h
    · simp [h, h.ne, h.le.not_gt]
    · simp [h]
    · simp [h, h.ne', h.le.not_gt]
  linarith
private theorem curlAdjoint_curl_add_grad_div {κ : LatticeShape d} (A : LatticeOneForm N κ) :
    latticeCurlAdjoint (latticeCurl A) + latticeGrad (latticeDiv A) = tensorLaplacian A := by
  funext x i
  have hi : i = directionIndex (i 0) := by
    funext j
    rw [Subsingleton.elim j 0]
    rfl
  obtain ⟨ρ, rfl⟩ : ∃ ρ, i = directionIndex ρ := ⟨i 0, hi⟩
  set e := (latticeSpacing N)⁻¹ with he
  let s : Fin d → LatticeSite N κ := unitStep N κ
  let a : Fin d → LatticeSite N κ → ℝ := fun ν y => A y (directionIndex ν)
  let c : Fin d → Fin d → LatticeSite N κ → ℝ := fun μ ν y =>
    e * (a ν (y + s μ) - a ν y) - e * (a μ (y + s ν) - a μ y)
  let G : Fin d → ℝ := fun μ => e * (c μ ρ (x - s μ) - c μ ρ x)
  have hGρ : G ρ = 0 := by simp [G, c]
  have hcurl : latticeCurlAdjoint (latticeCurl A) x (directionIndex ρ) = ∑ μ, G μ - G ρ := by
    rw [← sum_plaquetteDirection_ite ρ G]
    refine Finset.sum_congr rfl fun p _ => ?_
    change ((if p.1.2 = ρ then e * (c p.1.1 p.1.2 (x - s p.1.1) - c p.1.1 p.1.2 x) else 0) -
      (if p.1.1 = ρ then e * (c p.1.1 p.1.2 (x - s p.1.2) - c p.1.1 p.1.2 x) else 0)) = _
    by_cases h2 : p.1.2 = ρ
    · have h1 : p.1.1 ≠ ρ := fun h => absurd p.2 (by rw [h, h2]; exact lt_irrefl _)
      simp only [h2, h1, if_true, if_false, G, sub_zero, add_zero]
    · by_cases h1 : p.1.1 = ρ
      · simp only [h2, h1, if_true, if_false, G, zero_sub, zero_add, c]
        ring
      · simp [h1, h2]
  have hlap : tensorLaplacian A x (directionIndex ρ) =
      ∑ μ, e * (e * (a ρ (x - s μ + s μ) - a ρ (x - s μ)) - e * (a ρ (x + s μ) - a ρ x)) := rfl
  have hgrad : latticeGrad (latticeDiv A) x (directionIndex ρ) =
      e * (∑ μ, e * (a μ (x + s ρ - s μ) - a μ (x + s ρ)) -
        ∑ μ, e * (a μ (x - s μ) - a μ x)) := rfl
  rw [Pi.add_apply, Pi.add_apply, hcurl, hgrad, hlap, hGρ, sub_zero, ← Finset.sum_sub_distrib,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have hswap : x + s ρ - s μ = x - s μ + s ρ := by abel
  simp only [G, c, hswap]
  ring
section Inner
variable {κ : LatticeShape d} {I : Type}
private theorem fieldInner_comm (F G : LatticeField N κ I) : fieldInner F G = fieldInner G F :=
  tsum_congr fun p => by ring
private theorem fieldInner_add_right [Finite (LatticeSite N κ)] [Finite I]
    (F G H : LatticeField N κ I) :
    fieldInner F (G + H) = fieldInner F G + fieldInner F H := by apply _root_.YangMills.Construction.LatticeFields.CompressedGreenDecayProof.fieldInner_add <;> assumption
private theorem fieldInner_smul_right [Finite (LatticeSite N κ)] [Finite I]
    (F G : LatticeField N κ I) (t : ℝ) :
    fieldInner F (t • G) = t * fieldInner F G := by
  unfold fieldInner
  rw [← tsum_mul_left]
  exact tsum_congr fun p => by simp only [Pi.smul_apply, smul_eq_mul]; ring
private theorem fieldInner_sub_left [Finite (LatticeSite N κ)] [Finite I]
    (F G H : LatticeField N κ I) :
    fieldInner (F - G) H = fieldInner F H - fieldInner G H := by
  unfold fieldInner
  rw [← Summable.tsum_sub Summable.of_finite Summable.of_finite]
  exact tsum_congr fun p => by simp only [Pi.sub_apply]; ring
abbrev _root_.YangMills.SharedProofs.p65939 := @fieldInner_sub_left
private theorem fieldNorm_sq (F : LatticeField N κ I) : fieldNorm F ^ 2 = fieldInner F F := by apply _root_.YangMills.Construction.LatticeFields.CompressedGreenDecayProof.fieldNorm_sq_eq <;> assumption
private theorem fieldSquareSummable_of_finite [Finite (LatticeSite N κ)] [Finite I]
    (F : LatticeField N κ I) : FieldSquareSummable F :=
  Summable.of_finite
end Inner
private theorem fieldInner_massiveLaplacian [NeZero N] {ℓ : Fin d → ℕ} {hℓ : ∀ μ, 1 ≤ ℓ μ}
    [Finite (LatticeSite N (LatticeShape.torus ℓ hℓ))] [Finite (LatticeSite 1 (LatticeShape.torus ℓ hℓ))]
    (hgrad : IsFieldAdjoint (latticeGrad : ScalarField N (LatticeShape.torus ℓ hℓ) → _) latticeDiv)
    (hproj : ∀ f : ScalarField N (LatticeShape.torus ℓ hℓ),
      IsOrthProj (laplacianImageKer N ℓ hℓ) f (kerLaplacianProj f))
    (hadj : ∀ (A : LatticeOneForm N (LatticeShape.torus ℓ hℓ))
      (B : LatticeOneForm 1 (LatticeShape.torus ℓ hℓ)),
      FieldSquareSummable A → FieldSquareSummable B →
        fieldInner (bondBlockAvg A) B = fieldInner A (bondBlockAvgAdj B))
    (m : ℝ) (A' A : LatticeOneForm N (LatticeShape.torus ℓ hℓ)) :
    fieldInner A' (massiveLaplacian m A) =
      fieldInner (latticeCurl A') (latticeCurl A) +
        fieldInner (kerLaplacianProj (latticeDiv A')) (kerLaplacianProj (latticeDiv A)) +
          m * fieldInner (bondBlockAvg A') (bondBlockAvg A) := by
  have hcurl : fieldInner A' (latticeCurlAdjoint (latticeCurl A)) =
      fieldInner (latticeCurl A') (latticeCurl A) :=
    (latticeCurl_isFieldAdjoint A' (latticeCurl A) (fieldSquareSummable_of_finite _)
      (fieldSquareSummable_of_finite _)).symm
  have hR : fieldInner A' (latticeGrad (kerLaplacianProj (latticeDiv A))) =
      fieldInner (kerLaplacianProj (latticeDiv A')) (kerLaplacianProj (latticeDiv A)) := by
    have h1 := hgrad (kerLaplacianProj (latticeDiv A)) A' (fieldSquareSummable_of_finite _)
      (fieldSquareSummable_of_finite _)
    have h2 := (hproj (latticeDiv A')).2 _ (hproj (latticeDiv A)).1
    rw [fieldInner_sub_left] at h2
    rw [fieldInner_comm, h1, fieldInner_comm]
    linarith
  have hQ : fieldInner A' (bondBlockAvgAdj (bondBlockAvg A)) =
      fieldInner (bondBlockAvg A') (bondBlockAvg A) :=
    (hadj A' (bondBlockAvg A) (fieldSquareSummable_of_finite _)
      (fieldSquareSummable_of_finite _)).symm
  unfold massiveLaplacian
  rw [fieldInner_add_right, fieldInner_add_right, fieldInner_smul_right, hcurl, hR, hQ]
theorem claim_holds (hR : KernelProjectionUnique.Claim)
    (hB : BlockAvgAdjointFacts) (hD : MetricAdjointCubes.BasicLatticeFacts) :
    Claim := by
  intro d L k hd hL ℓ hℓ
  have : NeZero (L ^ k) := ⟨pow_ne_zero _ (by omega)⟩
  have := torus_finite (L ^ k) ℓ hℓ
  have := torus_finite 1 ℓ hℓ
  have hgrad := (hD d L k (L ^ k) hd hL rfl (LatticeShape.torus ℓ hℓ)).2.1.grad_adjoint
  have hproj := fun f => (hR d (L ^ k) ℓ hℓ f).1
  have hadj := (hB d (L ^ k) (LatticeShape.torus ℓ hℓ)).2.2.2
  refine ⟨curlAdjoint_curl_add_grad_div, fun m _ => ⟨fun A => ?_, fun A A' => ?_, fun A => ?_⟩⟩
  · have h := curlAdjoint_curl_add_grad_div A
    unfold massiveLaplacian massiveLaplacianAlt kerLaplacianProjCompl
    rw [← h]
    funext x i
    have hsub : latticeGrad (latticeDiv A - kerLaplacianProj (latticeDiv A)) x i =
        latticeGrad (latticeDiv A) x i - latticeGrad (kerLaplacianProj (latticeDiv A)) x i := by
      simp only [latticeGrad, forwardDiff, shiftForward, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      ring
    simp only [Pi.add_apply, Pi.sub_apply, hsub]
    ring
  · rw [fieldInner_massiveLaplacian hgrad hproj hadj, fieldInner_comm (massiveLaplacian m A') A,
      fieldInner_massiveLaplacian hgrad hproj hadj, fieldInner_comm (latticeCurl A'),
      fieldInner_comm (bondBlockAvg A'), fieldInner_comm (kerLaplacianProj (latticeDiv A'))]
  · rw [fieldInner_massiveLaplacian hgrad hproj hadj, fieldNorm_sq, fieldNorm_sq, fieldNorm_sq]
end YangMills.Construction.LatticeFields.MassiveLaplacianForms
