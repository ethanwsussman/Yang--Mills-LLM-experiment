import YangMills.Construction.ColdChainAtEveryLevel.HomotopyFormulaProof
import YangMills.Construction.ColdChainAtEveryLevel.LeastQuarticGaugeProof
import YangMills.Construction.ColdChainAtEveryLevel.UnitPartsOfQuaternions
import YangMills.Construction.HoleBesideASecondHole.GaugeOnAnOrthantOfAShell
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open LatticeFractionalIntegration BlockAverages ShellOrthant ShellFilling
namespace OrthantSymmetry
abbrev Site : Type := LatticeFractionalIntegration.Lattice4
theorem norm_coe_unitQuaternion (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
def distOne (g : UnitQuaternion) : ℝ := ‖(g : ℍ[ℝ]) - 1‖
theorem distOne_inv (g : UnitQuaternion) : distOne g⁻¹ = distOne g := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_inv_sub_one <;> assumption
theorem distOne_conj (a g : UnitQuaternion) : distOne (a⁻¹ * g * a) = distOne g := by
  unfold distOne
  have h1 : ((a⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (a : ℍ[ℝ]) = 1 := by
    rw [← Submonoid.coe_mul, inv_mul_cancel]
    rfl
  have e : ((a⁻¹ * g * a : UnitQuaternion) : ℍ[ℝ]) - 1 =
      ((a⁻¹ : UnitQuaternion) : ℍ[ℝ]) * ((g : ℍ[ℝ]) - 1) * (a : ℍ[ℝ]) := by
    simp only [Submonoid.coe_mul]
    rw [mul_sub, sub_mul, mul_one, h1]
  rw [e, norm_mul, norm_mul, _root_.YangMills.Construction.OrthantSymmetry.norm_coe_unitQuaternion, _root_.YangMills.Construction.OrthantSymmetry.norm_coe_unitQuaternion]
  ring
theorem basisVector_apply (j k : Fin 4) : basisVector j k = if k = j then 1 else 0 := by apply _root_.YangMills.Construction.LatticeFractionalIntegration.StaircaseHomotopy.basisVector_apply <;> assumption
theorem mem_bondsOf {P : Finset Site} {b : Site × Fin 4} :
    b ∈ bondsOf P ↔ b.1 ∈ P ∧ b.1 + basisVector b.2 ∈ P := by apply _root_.YangMills.Construction.LeastQuarticGauge.mem_bondsOf <;> assumption
theorem mem_orientedPlaquettesOf {P : Finset Site} {p : Site × Fin 4 × Fin 4} :
    p ∈ orientedPlaquettesOf P ↔ p.1 ∈ P ∧ p.2.1 ≠ p.2.2 ∧ p.1 + basisVector p.2.1 ∈ P ∧
      p.1 + basisVector p.2.2 ∈ P ∧ p.1 + basisVector p.2.1 + basisVector p.2.2 ∈ P := by
  simp [orientedPlaquettesOf]
theorem latticePlaquette_swap (X : Site → Fin 4 → UnitQuaternion) (y : Site) (μ ν : Fin 4) :
    latticePlaquette X y μ ν = (latticePlaquette X y ν μ)⁻¹ := by
  unfold latticePlaquette
  group
section Translation
variable (v : Site) (X : Site → Fin 4 → UnitQuaternion)
def translate : Site → Fin 4 → UnitQuaternion := fun y j => X (y - v) j
theorem latticePlaquette_translate (y : Site) (μ ν : Fin 4) :
    latticePlaquette (translate v X) y μ ν = latticePlaquette X (y - v) μ ν := by
  unfold latticePlaquette translate
  rw [sub_add_eq_add_sub y v (basisVector μ) |>.symm, sub_add_eq_add_sub y v (basisVector ν) |>.symm]
theorem plaquetteDefect_translate (P P' : Finset Site) (h : ∀ x, x ∈ P' ↔ x - v ∈ P) :
    _root_.YangMills.Construction.ShellFilling.plaquetteDefect P' (translate v X) = _root_.YangMills.Construction.ShellFilling.plaquetteDefect P X := by
  unfold _root_.YangMills.Construction.ShellFilling.plaquetteDefect
  have hh : ∀ x, x + v ∈ P' ↔ x ∈ P := fun x => by rw [h]; simp
  refine Finset.sum_nbij' (fun p => (p.1 - v, p.2)) (fun p => (p.1 + v, p.2)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [mem_orientedPlaquettesOf] at hp ⊢
    obtain ⟨h1, h2, h3, h4, h5⟩ := hp
    refine ⟨(h _).1 h1, h2, ?_, ?_, ?_⟩
    · have hx := (h _).1 h3
      simpa [sub_add_eq_add_sub] using hx
    · have hx := (h _).1 h4
      simpa [sub_add_eq_add_sub] using hx
    · have hx := (h _).1 h5
      simpa [sub_add_eq_add_sub] using hx
  · intro p hp
    rw [mem_orientedPlaquettesOf] at hp ⊢
    obtain ⟨h1, h2, h3, h4, h5⟩ := hp
    refine ⟨(hh _).2 h1, h2, ?_, ?_, ?_⟩
    · have hx := (hh _).2 h3
      simpa [add_right_comm] using hx
    · have hx := (hh _).2 h4
      simpa [add_right_comm] using hx
    · have hx := (hh _).2 h5
      have e : p.1 + basisVector p.2.1 + basisVector p.2.2 + v =
          p.1 + v + basisVector p.2.1 + basisVector p.2.2 := by abel
      rwa [e] at hx
  · intro p _
    simp
  · intro p _
    simp
  · intro p _
    simp only
    rw [latticePlaquette_translate]
theorem bondSum_translate (P P' : Finset Site) (h : ∀ x, x ∈ P' ↔ x - v ∈ P) (γ : Site → UnitQuaternion) :
    ∑ b ∈ bondsOf P, ‖((latticeGaugeTransform (fun x => γ (x + v)) X b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4 =
      ∑ b ∈ bondsOf P', ‖((latticeGaugeTransform γ (translate v X) b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4 := by
  have hh : ∀ x, x + v ∈ P' ↔ x ∈ P := fun x => by rw [h]; simp
  refine Finset.sum_nbij' (fun b => (b.1 + v, b.2)) (fun b => (b.1 - v, b.2)) ?_ ?_ ?_ ?_ ?_
  · intro b hb
    rw [mem_bondsOf] at hb ⊢
    refine ⟨(hh _).2 hb.1, ?_⟩
    have hx := (hh _).2 hb.2
    simpa [add_right_comm] using hx
  · intro b hb
    rw [mem_bondsOf] at hb ⊢
    refine ⟨(h _).1 hb.1, ?_⟩
    have hx := (h _).1 hb.2
    simpa [sub_add_eq_add_sub] using hx
  · intro b _
    simp
  · intro b _
    simp
  · intro b _
    have e : latticeGaugeTransform (fun x => γ (x + v)) X b.1 b.2 =
        latticeGaugeTransform γ (translate v X) (b.1 + v) b.2 := by
      unfold latticeGaugeTransform translate
      simp only [add_sub_cancel_right]
      rw [add_right_comm]
    simp only
    rw [e]
end Translation
section Reflection
variable (k : Fin 4)
def reflectCoord (x : Site) : Site := Function.update x k (-x k)
theorem reflectCoord_apply (x : Site) (m : Fin 4) :
    reflectCoord k x m = if m = k then -x k else x m := by
  simp [reflectCoord, Function.update_apply]
theorem reflectCoord_reflectCoord (x : Site) : reflectCoord k (reflectCoord k x) = x := by
  funext m
  by_cases h : m = k
  · subst h
    simp [reflectCoord_apply]
  · simp [reflectCoord_apply, h]
theorem reflectCoord_add_basis_of_ne {j : Fin 4} (hj : j ≠ k) (x : Site) :
    reflectCoord k (x + basisVector j) = reflectCoord k x + basisVector j := by
  funext m
  by_cases h : m = k
  · subst h
    simp [reflectCoord_apply, basisVector_apply, hj.symm]
  · simp [reflectCoord_apply, basisVector_apply, h]
theorem reflectCoord_add_basis_self (x : Site) :
    reflectCoord k (x + basisVector k) = reflectCoord k x - basisVector k := by
  funext m
  by_cases h : m = k
  · subst h
    simp [reflectCoord_apply, basisVector_apply]
    ring
  · simp [reflectCoord_apply, basisVector_apply, h]
def reflectField (X : Site → Fin 4 → UnitQuaternion) : Site → Fin 4 → UnitQuaternion :=
  fun y j => if j = k then (X (reflectCoord k (y + basisVector k)) k)⁻¹ else X (reflectCoord k y) j
variable {k}
theorem latticePlaquette_reflectField_of_ne (X : Site → Fin 4 → UnitQuaternion) (y : Site) {μ ν : Fin 4}
    (hμ : μ ≠ k) (hν : ν ≠ k) :
    latticePlaquette (reflectField k X) y μ ν = latticePlaquette X (reflectCoord k y) μ ν := by
  unfold latticePlaquette reflectField
  simp only [hμ, hν, if_false, reflectCoord_add_basis_of_ne k hμ, reflectCoord_add_basis_of_ne k hν]
theorem latticePlaquette_reflectField_self (X : Site → Fin 4 → UnitQuaternion) (y : Site) {ν : Fin 4}
    (hν : ν ≠ k) :
    latticePlaquette (reflectField k X) y k ν =
      (X (reflectCoord k y - basisVector k) k)⁻¹ *
        latticePlaquette X (reflectCoord k y - basisVector k) ν k * X (reflectCoord k y - basisVector k) k := by
  unfold latticePlaquette reflectField
  simp only [hν, if_false, if_true, reflectCoord_add_basis_self, reflectCoord_add_basis_of_ne k hν]
  have e1 : reflectCoord k y - basisVector k + basisVector ν =
      reflectCoord k y + basisVector ν - basisVector k := by abel
  have e2 : reflectCoord k y - basisVector k + basisVector k = reflectCoord k y := by abel
  rw [e1, e2]
  group
theorem distOne_latticePlaquette_swap (X : Site → Fin 4 → UnitQuaternion) (y : Site) (μ ν : Fin 4) :
    distOne (latticePlaquette X y μ ν) = distOne (latticePlaquette X y ν μ) := by
  rw [latticePlaquette_swap X y μ ν, distOne_inv]
def plaquetteImage (k : Fin 4) (p : Site × Fin 4 × Fin 4) : Site × Fin 4 × Fin 4 :=
  if p.2.1 ≠ k ∧ p.2.2 ≠ k then (reflectCoord k p.1, p.2.1, p.2.2)
  else (reflectCoord k p.1 - basisVector k, p.2.2, p.2.1)
theorem distOne_plaquetteImage (X : Site → Fin 4 → UnitQuaternion) (p : Site × Fin 4 × Fin 4)
    (hp : p.2.1 ≠ p.2.2) :
    distOne (latticePlaquette (reflectField k X) p.1 p.2.1 p.2.2) =
      distOne (latticePlaquette X (plaquetteImage k p).1 (plaquetteImage k p).2.1 (plaquetteImage k p).2.2) := by
  obtain ⟨y, μ, ν⟩ := p
  simp only at hp
  by_cases h1 : μ = k
  · subst h1
    have h2 : ν ≠ μ := fun h => hp h.symm
    simp only [plaquetteImage, ne_eq, not_true_eq_false, false_and, if_false]
    rw [latticePlaquette_reflectField_self X y h2, distOne_conj]
  · by_cases h2 : ν = k
    · subst h2
      simp only [plaquetteImage, ne_eq, not_true_eq_false, and_false, if_false]
      rw [distOne_latticePlaquette_swap, latticePlaquette_reflectField_self X y h1, distOne_conj,
        distOne_latticePlaquette_swap]
    · simp only [plaquetteImage, ne_eq, h1, h2, not_false_eq_true, and_self, if_true]
      rw [latticePlaquette_reflectField_of_ne X y h1 h2]
theorem plaquetteImage_injective : Function.Injective (plaquetteImage k) := by
  rintro ⟨y, μ, ν⟩ ⟨y', μ', ν'⟩ h
  have hinj : Function.Injective (reflectCoord k) := fun a b hab => by
    have hr := congrArg (reflectCoord k) hab
    rwa [reflectCoord_reflectCoord, reflectCoord_reflectCoord] at hr
  unfold plaquetteImage at h
  simp only at h
  split_ifs at h with h1 h2 h3
  · simp only [Prod.mk.injEq] at h
    obtain ⟨a, b, c⟩ := h
    rw [hinj a, b, c]
  · exfalso
    simp only [Prod.mk.injEq] at h
    obtain ⟨_, b, c⟩ := h
    apply h2
    rw [← b, ← c]
    exact ⟨h1.2, h1.1⟩
  · exfalso
    simp only [Prod.mk.injEq] at h
    obtain ⟨_, b, c⟩ := h
    apply h1
    rw [b, c]
    exact ⟨h3.2, h3.1⟩
  · simp only [Prod.mk.injEq] at h
    obtain ⟨a, b, c⟩ := h
    rw [hinj (sub_left_injective a), b, c]
theorem plaquetteDefect_reflectField_le (X : Site → Fin 4 → UnitQuaternion) (P P' : Finset Site)
    (h : ∀ x, x ∈ P' ↔ reflectCoord k x ∈ P) :
    _root_.YangMills.Construction.ShellFilling.plaquetteDefect P' (reflectField k X) ≤ _root_.YangMills.Construction.ShellFilling.plaquetteDefect P X := by
  classical
  unfold _root_.YangMills.Construction.ShellFilling.plaquetteDefect
  have hmap : ∀ p ∈ orientedPlaquettesOf P', plaquetteImage k p ∈ orientedPlaquettesOf P := by
    rintro ⟨y, μ, ν⟩ hp
    rw [mem_orientedPlaquettesOf] at hp ⊢
    obtain ⟨a1, a2, a3, a4, a5⟩ := hp
    simp only at a1 a2 a3 a4 a5
    have b1 := (h _).1 a1
    have b3 := (h _).1 a3
    have b4 := (h _).1 a4
    have b5 := (h _).1 a5
    by_cases h1 : μ = k
    · subst h1
      have h2 : ν ≠ μ := fun h => a2 h.symm
      simp only [plaquetteImage, ne_eq, not_true_eq_false, false_and, if_false]
      rw [reflectCoord_add_basis_self] at b3
      rw [reflectCoord_add_basis_of_ne μ h2, reflectCoord_add_basis_self] at b5
      rw [reflectCoord_add_basis_of_ne μ h2] at b4
      refine ⟨b3, h2, b5, ?_, ?_⟩
      · have e : reflectCoord μ y - basisVector μ + basisVector μ = reflectCoord μ y := by abel
        rwa [e]
      · have e : reflectCoord μ y - basisVector μ + basisVector ν + basisVector μ =
            reflectCoord μ y + basisVector ν := by abel
        rwa [e]
    · by_cases h2 : ν = k
      · subst h2
        simp only [plaquetteImage, ne_eq, not_true_eq_false, and_false, if_false]
        rw [reflectCoord_add_basis_self] at b4
        rw [reflectCoord_add_basis_self, reflectCoord_add_basis_of_ne ν h1] at b5
        rw [reflectCoord_add_basis_of_ne ν h1] at b3
        refine ⟨b4, h1 ∘ Eq.symm, ?_, ?_, ?_⟩
        · have e : reflectCoord ν y - basisVector ν + basisVector ν = reflectCoord ν y := by abel
          rwa [e]
        · have e : reflectCoord ν y - basisVector ν + basisVector μ =
              reflectCoord ν y + basisVector μ - basisVector ν := by abel
          rwa [e]
        · have e : reflectCoord ν y - basisVector ν + basisVector ν + basisVector μ =
              reflectCoord ν y + basisVector μ := by abel
          rwa [e]
      · simp only [plaquetteImage, ne_eq, h1, h2, not_false_eq_true, and_self, if_true]
        rw [reflectCoord_add_basis_of_ne k h1] at b3
        rw [reflectCoord_add_basis_of_ne k h2] at b4
        rw [reflectCoord_add_basis_of_ne k h2, reflectCoord_add_basis_of_ne k h1] at b5
        exact ⟨b1, a2, b3, b4, b5⟩
  calc ∑ p ∈ orientedPlaquettesOf P',
        ‖((latticePlaquette (reflectField k X) p.1 p.2.1 p.2.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 2
      = ∑ p ∈ orientedPlaquettesOf P', (fun q : Site × Fin 4 × Fin 4 =>
          ‖((latticePlaquette X q.1 q.2.1 q.2.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 2) (plaquetteImage k p) := by
        refine Finset.sum_congr rfl fun p hp => ?_
        have hd := distOne_plaquetteImage (k := k) X p (mem_orientedPlaquettesOf.1 hp).2.1
        unfold distOne at hd
        simp only
        rw [hd]
    _ = ∑ q ∈ (orientedPlaquettesOf P').image (plaquetteImage k),
          ‖((latticePlaquette X q.1 q.2.1 q.2.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 2 := by
        rw [Finset.sum_image fun a _ b _ hab => plaquetteImage_injective hab]
    _ ≤ _ := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
        intro q hq
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hq
        exact hmap p hp
def bondImage (k : Fin 4) (b : Site × Fin 4) : Site × Fin 4 :=
  if b.2 = k then (reflectCoord k b.1 - basisVector k, k) else (reflectCoord k b.1, b.2)
theorem distOne_bondImage (X : Site → Fin 4 → UnitQuaternion) (γ : Site → UnitQuaternion) (b : Site × Fin 4) :
    distOne (latticeGaugeTransform (fun x => γ (reflectCoord k x)) X b.1 b.2) =
      distOne (latticeGaugeTransform γ (reflectField k X) (bondImage k b).1 (bondImage k b).2) := by
  obtain ⟨x, j⟩ := b
  by_cases h : j = k
  · subst h
    simp only [bondImage, if_true]
    have e : latticeGaugeTransform γ (reflectField j X) (reflectCoord j x - basisVector j) j =
        (latticeGaugeTransform (fun x => γ (reflectCoord j x)) X x j)⁻¹ := by
      unfold latticeGaugeTransform reflectField
      simp only [if_true]
      have e2 : reflectCoord j x - basisVector j + basisVector j = reflectCoord j x := by abel
      rw [e2, reflectCoord_reflectCoord, reflectCoord_add_basis_self]
      group
    rw [e, distOne_inv]
  · simp only [bondImage, h, if_false]
    have e : latticeGaugeTransform γ (reflectField k X) (reflectCoord k x) j =
        latticeGaugeTransform (fun x => γ (reflectCoord k x)) X x j := by
      unfold latticeGaugeTransform reflectField
      simp only [h, if_false]
      rw [reflectCoord_reflectCoord, reflectCoord_add_basis_of_ne k h]
    rw [e]
theorem bondImage_injective : Function.Injective (bondImage k) := by
  rintro ⟨x, j⟩ ⟨x', j'⟩ h
  have hinj : Function.Injective (reflectCoord k) := fun a b hab => by
    have hr := congrArg (reflectCoord k) hab
    rwa [reflectCoord_reflectCoord, reflectCoord_reflectCoord] at hr
  unfold bondImage at h
  simp only at h
  split_ifs at h with h1 h2 h3
  · simp only [Prod.mk.injEq] at h
    rw [hinj (sub_left_injective h.1), h1, h2]
  · simp only [Prod.mk.injEq] at h
    exact absurd h.2.symm h2
  · simp only [Prod.mk.injEq] at h
    exact absurd h.2 h1
  · simp only [Prod.mk.injEq] at h
    rw [hinj h.1, h.2]
theorem hasQuarticGaugeOn_of_reflect {c K : ℝ} (P P' : Finset Site)
    (h : ∀ x, x ∈ P' ↔ reflectCoord k x ∈ P)
    (hg : HasQuarticGaugeOn c K P') : HasQuarticGaugeOn c K P := by
  classical
  intro X ε h0 h1 h2
  obtain ⟨γ, hγ⟩ := hg (reflectField k X) ε h0 h1 ((plaquetteDefect_reflectField_le X P P' h).trans h2)
  refine ⟨fun x => γ (reflectCoord k x), le_trans ?_ hγ⟩
  have hmap : ∀ b ∈ bondsOf P, bondImage k b ∈ bondsOf P' := by
    rintro ⟨x, j⟩ hb
    rw [mem_bondsOf] at hb ⊢
    obtain ⟨a1, a2⟩ := hb
    simp only at a1 a2
    by_cases hj : j = k
    · subst hj
      simp only [bondImage, if_true]
      constructor
      · rw [h, ← reflectCoord_add_basis_self, reflectCoord_reflectCoord]
        exact a2
      · have e : reflectCoord j x - basisVector j + basisVector j = reflectCoord j x := by abel
        rw [e, h, reflectCoord_reflectCoord]
        exact a1
    · simp only [bondImage, hj, if_false]
      constructor
      · rw [h, reflectCoord_reflectCoord]
        exact a1
      · rw [h, reflectCoord_add_basis_of_ne k hj, reflectCoord_reflectCoord]
        exact a2
  calc ∑ b ∈ bondsOf P,
        ‖((latticeGaugeTransform (fun x => γ (reflectCoord k x)) X b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4
      = ∑ b ∈ bondsOf P, (fun b' : Site × Fin 4 =>
          ‖((latticeGaugeTransform γ (reflectField k X) b'.1 b'.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4)
            (bondImage k b) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        have hd := distOne_bondImage (k := k) X γ b
        unfold distOne at hd
        simp only
        rw [hd]
    _ = ∑ b' ∈ (bondsOf P).image (bondImage k),
          ‖((latticeGaugeTransform γ (reflectField k X) b'.1 b'.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4 := by
        rw [Finset.sum_image fun a _ b _ hab => bondImage_injective hab]
    _ ≤ _ := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
        intro q hq
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hq
        exact hmap p hp
end Reflection
theorem hasQuarticGaugeOn_positive_orthant (C c : ℝ)
    (hLQ : ∀ (N : ℕ) (A P : Finset Site) (X : Site → Fin 4 → UnitQuaternion) (ε : ℝ), 1 ≤ N →
      A.Nonempty → (∀ a ∈ A, ∀ i, -(10 * (N : ℤ)) ≤ a i ∧ a i ≤ 12 * (N : ℤ)) →
      (∀ x, x ∈ P ↔ (∀ i, x i ≤ 21 * (N : ℤ) - 1) ∧ ∃ a ∈ A, ∀ i, a i ≤ x i) →
      0 ≤ ε → ε ≤ c →
      ∑ p ∈ orientedPlaquettesOf P, ‖((latticePlaquette X p.1 p.2.1 p.2.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 2
        ≤ ε ^ 2 →
      ∃ γ : Site → UnitQuaternion,
        ∑ b ∈ bondsOf P, ‖((latticeGaugeTransform γ X b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4 ≤ (C * ε) ^ 4)
    (l : ℝ) (o : Fin 4 → ℝ) (P : Finset Site) (hl : 100 ≤ l)
    (hP : ∀ x, x ∈ P ↔ IsInShellOrthant o l (fun _ => 1) x) : HasQuarticGaugeOn c C P := by
  classical
  set N : ℕ := ⌈(2.4 * l + 1) / 31⌉₊ with hN
  have hN1 : (2.4 * l + 1) / 31 ≤ N := Nat.le_ceil _
  have hN2 : (N : ℝ) < (2.4 * l + 1) / 31 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hNpos : 1 ≤ N := by
    have hpos : (0 : ℝ) < N := by
      linarith
    exact_mod_cast hpos
  set T : Site := fun k => ⌊o k + 1.9 * l⌋ with hT
  set m : Site := fun k => ⌈o k - l / 2⌉ with hm
  set M : Site := fun k => ⌈o k + 1.1 * l⌉ with hMd
  set v : Site := fun k => 21 * (N : ℤ) - 1 - T k with hv
  have hT1 : ∀ k, (T k : ℝ) ≤ o k + 1.9 * l := fun k => Int.floor_le _
  have hT2 : ∀ k, o k + 1.9 * l < T k + 1 := fun k => Int.lt_floor_add_one _
  have hm1 : ∀ k, o k - l / 2 ≤ m k := fun k => Int.le_ceil _
  have hM1 : ∀ k, o k + 1.1 * l ≤ M k := fun k => Int.le_ceil _
  have hM2 : ∀ k, (M k : ℝ) < o k + 1.1 * l + 1 := fun k => Int.ceil_lt_add_one _
  set corner : Fin 4 → Site := fun j k => if k = j then M k + v k else m k + v k with hcorner
  set A : Finset Site := Finset.univ.image corner with hA
  set P' : Finset Site := P.image (fun x => x + v) with hP'
  have hmem' : ∀ x, x ∈ P' ↔ x - v ∈ P := by
    intro x
    simp only [hP', Finset.mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro h
      exact ⟨_, h, by simp⟩
  have hlow : ∀ k, (T k - m k : ℝ) ≤ 31 * N - 1 := by
    intro k
    have := hT1 k
    have := hm1 k
    have : 2.4 * l + 1 ≤ 31 * (N : ℝ) := by
      have := hN1
      rw [div_le_iff₀ (by norm_num)] at this
      linarith
    linarith
  have hup : ∀ k, (9 * N - 1 : ℝ) ≤ T k - M k := by
    intro k
    have := hT2 k
    have := hM2 k
    have : 9 * (N : ℝ) ≤ 0.8 * l - 1 := by
      have h1 := hN2
      have h2 : 9 * (N : ℝ) < 9 * ((2.4 * l + 1) / 31 + 1) := by linarith
      have h3 : 9 * ((2.4 * l + 1) / 31 + 1) ≤ 0.8 * l - 1 := by
        rw [show (9 : ℝ) * ((2.4 * l + 1) / 31 + 1) = (9 * (2.4 * l + 1) + 279) / 31 by ring,
          div_le_iff₀ (by norm_num)]
        nlinarith
      linarith
    linarith
  have hmM : ∀ k, m k ≤ M k := by
    intro k
    exact Int.ceil_le_ceil (by linarith)
  have hlowZ : ∀ k, T k - m k ≤ 31 * (N : ℤ) - 1 := by
    intro k
    have := hlow k
    exact_mod_cast this
  have hupZ : ∀ k, 9 * (N : ℤ) - 1 ≤ T k - M k := by
    intro k
    have := hup k
    exact_mod_cast this
  have hmemP : ∀ x, (∀ i, x i ≤ 21 * (N : ℤ) - 1) ∧ (∃ a ∈ A, ∀ i, a i ≤ x i) ↔ x ∈ P' := by
    intro x
    rw [hmem', hP]
    have hcoord : ∀ i, x i ≤ 21 * (N : ℤ) - 1 ↔ ((x - v) i : ℝ) ≤ o i + 1.9 * l := by
      intro i
      rw [← Int.le_floor]
      simp only [Pi.sub_apply, hv, hT]
      constructor <;> intro h <;> omega
    constructor
    · rintro ⟨h1, a, ha, h2⟩
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 ha
      have hlowx : ∀ i, m i ≤ (x - v) i := by
        intro i
        have h3 := h2 i
        simp only [hcorner, Pi.sub_apply] at h3 ⊢
        by_cases hij : i = j
        · simp only [hij, if_true] at h3 ⊢
          have := hmM j
          omega
        · simp only [hij, if_false] at h3
          omega
      have hMj : M j ≤ (x - v) j := by
        have h3 := h2 j
        simp only [hcorner, if_true, Pi.sub_apply] at h3 ⊢
        omega
      have hL : orthantLower l 1 = -(l / 2) := by simp [orthantLower]
      have hH : orthantUpper l 1 = 1.9 * l := by norm_num [orthantUpper]
      refine ⟨fun i => ?_, j, ?_⟩
      · show orthantLower l 1 ≤ _ ∧ _ ≤ orthantUpper l 1
        rw [hL, hH]
        constructor
        · have : (m i : ℝ) ≤ ((x - v) i : ℝ) := by exact_mod_cast hlowx i
          have := hm1 i
          linarith
        · have := (hcoord i).1 (h1 i)
          linarith
      · have h4 : (M j : ℝ) ≤ ((x - v) j : ℝ) := by exact_mod_cast hMj
        have := hM1 j
        refine le_trans ?_ (le_abs_self _)
        linarith
    · rintro ⟨h1, j, hj⟩
      have hco : ∀ i, -(l / 2) ≤ ((x - v) i : ℝ) - o i ∧ ((x - v) i : ℝ) - o i ≤ 1.9 * l := by
        intro i
        have := h1 i
        simpa [orthantLower, orthantUpper] using this
      have huj : 1.1 * l ≤ ((x - v) j : ℝ) - o j := by
        rcases le_abs'.1 hj with h | h
        · have := (hco j).1
          linarith
        · exact h
      refine ⟨fun i => (hcoord i).2 (by have := (hco i).2; linarith), corner j,
        Finset.mem_image_of_mem _ (Finset.mem_univ j), fun i => ?_⟩
      have hgoal : (if i = j then M i else m i) ≤ (x - v) i := by
        by_cases hij : i = j
        · subst hij
          simp only [if_true]
          exact Int.ceil_le.2 (by linarith)
        · simp only [hij, if_false]
          exact Int.ceil_le.2 (by have := (hco i).1; linarith)
      simp only [hcorner, Pi.sub_apply] at hgoal ⊢
      by_cases hij : i = j
      · simp only [hij, if_true] at hgoal ⊢
        omega
      · simp only [hij, if_false] at hgoal ⊢
        omega
  intro X ε h0 h1 h2
  have hsum : _root_.YangMills.Construction.ShellFilling.plaquetteDefect P' (translate v X) ≤ ε ^ 2 := by
    rw [plaquetteDefect_translate v X P P' hmem']
    exact h2
  obtain ⟨γ, hγ⟩ := hLQ N A P' (translate v X) ε hNpos
    ⟨corner 0, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
    (by
      intro a ha i
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 ha
      have h3 := hlowZ i
      have h4 := hupZ i
      have h5 := hmM i
      simp only [hcorner, hv]
      by_cases hij : i = j
      · simp only [hij, if_true]
        subst hij
        constructor <;> omega
      · simp only [hij, if_false]
        constructor <;> omega)
    (fun x => (hmemP x).symm) h0 h1 hsum
  refine ⟨fun x => γ (x + v), ?_⟩
  rw [bondSum_translate v X P P' hmem' γ]
  exact hγ
end OrthantSymmetry
open OrthantSymmetry in
theorem ShellOrthant.orthantQuarticGauge_of_quarticGauge (hLQ : quarticGaugeStatement) :
    orthantQuarticGaugeStatement := by
  classical
  obtain ⟨C, c, hC, hc, h⟩ := hLQ
  refine ⟨c, C, hc, hC, ?_⟩
  have key : ∀ (n : ℕ) (l : ℝ) (o : Fin 4 → ℝ) (s : Fin 4 → ℤ) (P : Finset Site), 100 ≤ l →
      (∀ k, s k = 1 ∨ s k = -1) → (Finset.univ.filter fun k => s k = -1).card = n →
      (∀ x, x ∈ P ↔ IsInShellOrthant o l s x) → HasQuarticGaugeOn c C P := by
    intro n
    induction n with
    | zero =>
      intro l o s P hl hs hn hP
      have hs1 : s = fun _ => 1 := by
        funext k
        rcases hs k with h1 | h1
        · exact h1
        · exfalso
          have hk : k ∈ Finset.univ.filter fun k => s k = -1 := by simp [h1]
          rw [Finset.card_eq_zero.1 hn] at hk
          simp at hk
      subst hs1
      exact hasQuarticGaugeOn_positive_orthant C c h l o P hl hP
    | succ n ih =>
      intro l o s P hl hs hn hP
      obtain ⟨k, hk⟩ : ∃ k, k ∈ Finset.univ.filter fun k => s k = -1 := by
        apply Finset.card_pos.1
        omega
      have hk1 : s k = -1 := by simpa using hk
      set s' := Function.update s k 1 with hs'
      set o' := Function.update o k (-o k) with ho'
      set P' := P.image (reflectCoord k) with hP'
      have hmem : ∀ x, x ∈ P' ↔ reflectCoord k x ∈ P := by
        intro x
        simp only [hP', Finset.mem_image]
        constructor
        · rintro ⟨y, hy, rfl⟩
          rwa [reflectCoord_reflectCoord]
        · intro hx
          exact ⟨_, hx, reflectCoord_reflectCoord k x⟩
      refine hasQuarticGaugeOn_of_reflect (k := k) P P' hmem (ih l o' s' P' hl ?_ ?_ ?_)
      · intro m
        by_cases hm : m = k
        · subst hm
          simp [hs']
        · simpa [hs', Function.update_of_ne hm] using hs m
      · have hfilter : (Finset.univ.filter fun m => s' m = -1) =
            (Finset.univ.filter fun m => s m = -1).erase k := by
          ext m
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
          by_cases hm : m = k
          · subst hm
            simp [hs']
          · simp [hs', Function.update_of_ne hm, hm]
        rw [hfilter, Finset.card_erase_of_mem hk, hn]
        rfl
      · intro x
        rw [hmem, hP]
        unfold IsInShellOrthant IsBeyondSupDist
        have hval : ∀ m, (((reflectCoord k x) m : ℤ) : ℝ) - o m =
            if m = k then -((x k : ℝ) - o' k) else (x m : ℝ) - o' m := by
          intro m
          by_cases hm : m = k
          · subst hm
            simp [reflectCoord_apply, ho']
            ring
          · simp [reflectCoord_apply, ho', hm, Function.update_of_ne hm]
        constructor
        · rintro ⟨h1, j, hj⟩
          refine ⟨fun m => ?_, j, ?_⟩
          · have h2 := h1 m
            rw [hval] at h2
            by_cases hm : m = k
            · subst hm
              simp only [if_true, hk1, orthantLower, orthantUpper, hs', Function.update_self] at h2 ⊢
              norm_num at h2 ⊢
              constructor <;> linarith [h2.1, h2.2]
            · simp only [hm, if_false] at h2
              simpa [hs', Function.update_of_ne hm] using h2
          · rw [hval] at hj
            by_cases hm : j = k
            · subst hm
              simp only [↓reduceIte, abs_neg] at hj
              exact hj
            · simpa [hm] using hj
        · rintro ⟨h1, j, hj⟩
          refine ⟨fun m => ?_, j, ?_⟩
          · have h2 := h1 m
            rw [hval]
            by_cases hm : m = k
            · subst hm
              simp only [if_true, hk1, orthantLower, orthantUpper, hs', Function.update_self] at h2 ⊢
              norm_num at h2 ⊢
              constructor <;> linarith [h2.1, h2.2]
            · simp only [hm, if_false]
              simpa [hs', Function.update_of_ne hm] using h2
          · rw [hval]
            by_cases hm : j = k
            · subst hm
              simp only [↓reduceIte, abs_neg]
              exact hj
            · simpa [hm] using hj
  intro l o s P hl hs hP
  exact key _ l o s P hl hs rfl hP
end YangMills.Construction
end
