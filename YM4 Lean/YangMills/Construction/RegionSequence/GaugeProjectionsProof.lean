import YangMills.Construction.DirichletOperator.MapsOfACubeOfTheFirstKindProof
import YangMills.Construction.RegionSequence.GaugeConditionProjections
import YangMills.Construction.RegionSequence.GaugeLaplacianPositivityProof
import YangMills.Construction.RegionSequence.PartitionConsequences
import YangMills.Construction.SeparatedSequences.ClassGeometryInASettingOfRegionsProof
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Dirichlet YangMills.Construction.Torus
noncomputable section
namespace YangMills.Construction.RegionSequence.GaugeProjections
structure IsPosBilin {W : Type} [AddCommGroup W] [Module ℝ W] (p : W → W → ℝ) : Prop where
  symm : ∀ a b, p a b = p b a
  add_left : ∀ a b c, p (a + b) c = p a c + p b c
  smul_left : ∀ (r : ℝ) a b, p (r • a) b = r * p a b
  pos : ∀ a, a ≠ 0 → 0 < p a a
namespace IsPosBilin
variable {W : Type} [AddCommGroup W] [Module ℝ W] {p : W → W → ℝ}
theorem add_right (h : IsPosBilin p) (a b c : W) : p a (b + c) = p a b + p a c := by
  rw [h.symm, h.add_left, h.symm b, h.symm c]
theorem smul_right (h : IsPosBilin p) (r : ℝ) (a b : W) : p a (r • b) = r * p a b := by
  rw [h.symm, h.smul_left, h.symm b]
theorem zero_left (h : IsPosBilin p) (a : W) : p 0 a = 0 := by
  simpa using h.smul_left 0 0 a
theorem zero_right (h : IsPosBilin p) (a : W) : p a 0 = 0 := by
  rw [h.symm, h.zero_left]
theorem sub_left (h : IsPosBilin p) (a b c : W) : p (a - b) c = p a c - p b c := by
  have := h.add_left (a - b) b c
  rw [sub_add_cancel] at this
  linarith
theorem sub_right (h : IsPosBilin p) (a b c : W) : p a (b - c) = p a b - p a c := by
  rw [h.symm, h.sub_left, h.symm b, h.symm c]
theorem eq_zero_of_self_eq_zero (h : IsPosBilin p) {a : W} (ha : p a a = 0) : a = 0 := by
  by_contra hne
  exact (h.pos a hne).ne' ha
theorem ext_of_mem (h : IsPosBilin p) {X : Submodule ℝ W} {a b : W} (ha : a ∈ X)
    (hb : b ∈ X) (hab : ∀ u ∈ X, p a u = p b u) : a = b := by
  apply sub_eq_zero.1
  apply h.eq_zero_of_self_eq_zero
  rw [h.sub_left, hab _ (X.sub_mem ha hb), sub_self]
theorem ext (h : IsPosBilin p) {a b : W} (hab : ∀ u, p a u = p b u) : a = b :=
  h.ext_of_mem (X := ⊤) trivial trivial fun u _ => hab u
theorem exists_repr [FiniteDimensional ℝ W] (h : IsPosBilin p) (l : W →ₗ[ℝ] ℝ) :
    ∃ v, ∀ u, p v u = l u := by
  let B : W →ₗ[ℝ] Module.Dual ℝ W := LinearMap.mk₂ ℝ p h.add_left
    (fun r a b => by rw [h.smul_left, smul_eq_mul]) h.add_right
    (fun r a b => by rw [h.smul_right, smul_eq_mul])
  have hinj : Function.Injective B := by
    refine (injective_iff_map_eq_zero B).2 fun a ha => h.eq_zero_of_self_eq_zero ?_
    exact LinearMap.congr_fun ha a
  have hsurj : Function.Surjective B :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq (K := ℝ) (V := W)).symm).1 hinj
  obtain ⟨v, hv⟩ := hsurj l
  exact ⟨v, fun u => LinearMap.congr_fun hv u⟩
theorem subtype (h : IsPosBilin p) (X : Submodule ℝ W) :
    IsPosBilin (fun a b : X => p a b) where
  symm a b := h.symm _ _
  add_left a b c := h.add_left _ _ _
  smul_left r a b := h.smul_left _ _ _
  pos a ha := h.pos _ (by simpa using ha)
theorem exists_repr_mem (h : IsPosBilin p) (X : Submodule ℝ W) [FiniteDimensional ℝ X]
    (l : W →ₗ[ℝ] ℝ) : ∃ v ∈ X, ∀ u ∈ X, p v u = l u := by
  obtain ⟨v, hv⟩ := (h.subtype X).exists_repr (l ∘ₗ X.subtype)
  exact ⟨v, v.2, fun u hu => hv ⟨u, hu⟩⟩
theorem orthProjValue_eq [Nonempty W] (h : IsPosBilin p) {Z : Set W} {f r : W} (hr : r ∈ Z)
    (hr' : ∀ w ∈ Z, p (f - r) w = 0) : orthProjValue Z p f = r := by
  have spec := Classical.epsilon_spec (p := fun r => r ∈ Z ∧ ∀ w ∈ Z, p (f - r) w = 0)
    ⟨r, hr, hr'⟩
  change orthProjValue Z p f ∈ Z ∧ ∀ w ∈ Z, p (f - orthProjValue Z p f) w = 0 at spec
  generalize orthProjValue Z p f = r' at spec
  apply sub_eq_zero.1
  apply h.eq_zero_of_self_eq_zero
  have e : ∀ x ∈ Z, p (r' - r) x = 0 := fun x hx => by
    have : r' - r = (f - r) - (f - r') := by abel
    rw [this, h.sub_left, hr' x hx, spec.2 x hx, sub_self]
  rw [h.sub_right, e r' spec.1, e r hr, sub_self]
end IsPosBilin
section ProjFrameSection
variable {V Y : Type} [AddCommGroup V] [Module ℝ V] [AddCommGroup Y] [Module ℝ Y]
structure ProjFrame (p : V → V → ℝ) (q : Y → Y → ℝ) (X : Submodule ℝ V) (Q : V → Y) (Qs : Y → V)
    (G A D : V → V) : Prop where
  pForm : IsPosBilin p
  qForm : IsPosBilin q
  adj_mem : ∀ ω, Qs ω ∈ X
  adj_spec : ∀ ω, ∀ u ∈ X, p (Qs ω) u = q ω (Q u)
  adj_inj : Function.Injective Qs
  green_mem : ∀ f ∈ X, G f ∈ X
  op_mem : ∀ f ∈ X, A f ∈ X
  op_green : ∀ f ∈ X, A (G f) = f
  green_op : ∀ f ∈ X, G (A f) = f
  green_symm : ∀ u ∈ X, ∀ v ∈ X, p (G u) v = p u (G v)
  ker_eq : ∀ n ∈ X, Q n = 0 → D n = A n
def frameTransfer (G : V → V) (Qs : Y → V) (ω : Y) : V := G (Qs ω)
def frameTransferAdj (p : V → V → ℝ) (q : Y → Y → ℝ) (G : V → V) (Qs : Y → V) (f : V) : Y :=
  adjointValue univ q p (frameTransfer G Qs) f
def frameGram (p : V → V → ℝ) (q : Y → Y → ℝ) (G : V → V) (Qs : Y → V) (ω : Y) : Y :=
  frameTransferAdj p q G Qs (frameTransfer G Qs ω)
def kerImage (X : Submodule ℝ V) (Q : V → Y) (D : V → V) : Set V := D '' {f | f ∈ X ∧ Q f = 0}
namespace ProjFrame
variable {p : V → V → ℝ} {q : Y → Y → ℝ} {X : Submodule ℝ V} {Q : V → Y} {Qs : Y → V}
  {G A D : V → V}
theorem adj_add (F : ProjFrame p q X Q Qs G A D) (a b : Y) : Qs (a + b) = Qs a + Qs b := by
  refine F.pForm.ext_of_mem (X := X) (F.adj_mem _) (X.add_mem (F.adj_mem _) (F.adj_mem _))
    fun u hu => ?_
  rw [F.pForm.add_left, F.adj_spec _ u hu, F.adj_spec _ u hu, F.adj_spec _ u hu, F.qForm.add_left]
theorem adj_smul (F : ProjFrame p q X Q Qs G A D) (r : ℝ) (a : Y) : Qs (r • a) = r • Qs a := by
  refine F.pForm.ext_of_mem (X := X) (F.adj_mem _) (X.smul_mem _ (F.adj_mem _))
    fun u hu => ?_
  rw [F.pForm.smul_left, F.adj_spec _ u hu, F.adj_spec _ u hu, F.qForm.smul_left]
theorem green_add (F : ProjFrame p q X Q Qs G A D) {f g : V} (hf : f ∈ X) (hg : g ∈ X) :
    G (f + g) = G f + G g := by
  refine F.pForm.ext_of_mem (X := X) (F.green_mem _ (X.add_mem hf hg))
    (X.add_mem (F.green_mem _ hf) (F.green_mem _ hg)) fun u hu => ?_
  rw [F.pForm.add_left, F.green_symm _ (X.add_mem hf hg) _ hu, F.green_symm _ hf _ hu,
    F.green_symm _ hg _ hu, F.pForm.add_left]
theorem green_smul (F : ProjFrame p q X Q Qs G A D) (r : ℝ) {f : V} (hf : f ∈ X) :
    G (r • f) = r • G f := by
  refine F.pForm.ext_of_mem (X := X) (F.green_mem _ (X.smul_mem _ hf))
    (X.smul_mem _ (F.green_mem _ hf)) fun u hu => ?_
  rw [F.pForm.smul_left, F.green_symm _ (X.smul_mem _ hf) _ hu, F.green_symm _ hf _ hu,
    F.pForm.smul_left]
theorem transfer_mem (F : ProjFrame p q X Q Qs G A D) (ω : Y) : frameTransfer G Qs ω ∈ X :=
  F.green_mem _ (F.adj_mem ω)
def transferLin (F : ProjFrame p q X Q Qs G A D) : Y →ₗ[ℝ] V where
  toFun := frameTransfer G Qs
  map_add' a b := by
    simp only [frameTransfer]
    rw [F.adj_add, F.green_add (F.adj_mem _) (F.adj_mem _)]
  map_smul' r a := by
    simp only [frameTransfer, RingHom.id_apply]
    rw [F.adj_smul, F.green_smul _ (F.adj_mem _)]
theorem transfer_injective (F : ProjFrame p q X Q Qs G A D) :
    Function.Injective (frameTransfer G Qs) := by
  intro a b hab
  apply F.adj_inj
  have := congrArg A hab
  simpa only [frameTransfer, F.op_green _ (F.adj_mem _)] using this
theorem transferAdj_spec [FiniteDimensional ℝ Y] (F : ProjFrame p q X Q Qs G A D) (f : V) (u : Y) :
    q (frameTransferAdj p q G Qs f) u = p f (frameTransfer G Qs u) := by
  let l : Y →ₗ[ℝ] ℝ :=
    { toFun := fun u => p f (F.transferLin u)
      map_add' := fun a b => by rw [map_add, F.pForm.add_right]
      map_smul' := fun r a => by
        rw [map_smul, F.pForm.smul_right, RingHom.id_apply, smul_eq_mul] }
  obtain ⟨v, hv⟩ := F.qForm.exists_repr l
  have spec := Classical.epsilon_spec
    (p := fun v => v ∈ (univ : Set Y) ∧ ∀ u ∈ (univ : Set Y), q v u = p f (frameTransfer G Qs u))
    ⟨v, mem_univ _, fun u _ => hv u⟩
  exact spec.2 u (mem_univ _)
theorem gram_spec [FiniteDimensional ℝ Y] (F : ProjFrame p q X Q Qs G A D) (ω u : Y) :
    q (frameGram p q G Qs ω) u = p (frameTransfer G Qs ω) (frameTransfer G Qs u) :=
  F.transferAdj_spec _ u
def gramLin [FiniteDimensional ℝ Y] (F : ProjFrame p q X Q Qs G A D) : Y →ₗ[ℝ] Y where
  toFun := frameGram p q G Qs
  map_add' a b := F.qForm.ext fun u => by
    rw [F.qForm.add_left, F.gram_spec, F.gram_spec, F.gram_spec, ← F.pForm.add_left]
    congr 1
    exact F.transferLin.map_add a b
  map_smul' r a := F.qForm.ext fun u => by
    rw [RingHom.id_apply, F.qForm.smul_left, F.gram_spec, F.gram_spec, ← F.pForm.smul_left]
    congr 1
    exact F.transferLin.map_smul r a
theorem gram_injective [FiniteDimensional ℝ Y] (F : ProjFrame p q X Q Qs G A D) :
    Function.Injective (frameGram p q G Qs) := by
  refine (injective_iff_map_eq_zero F.gramLin).2 fun a ha => ?_
  have h0 : q (frameGram p q G Qs a) a = 0 := by
    have : frameGram p q G Qs a = 0 := ha
    rw [this, F.qForm.zero_left]
  rw [F.gram_spec] at h0
  have h1 := F.pForm.eq_zero_of_self_eq_zero h0
  apply F.transfer_injective
  rw [h1]
  exact (F.transferLin.map_zero).symm
theorem gram_bijective [FiniteDimensional ℝ Y] (F : ProjFrame p q X Q Qs G A D) :
    Function.Bijective (frameGram p q G Qs) :=
  ⟨F.gram_injective, (LinearMap.injective_iff_surjective (f := F.gramLin)).1 F.gram_injective⟩
theorem gram_eq [FiniteDimensional ℝ Y] (F : ProjFrame p q X Q Qs G A D) :
    frameGram p q G Qs = fun ω => Q (G (G (Qs ω))) := by
  funext ω
  refine F.qForm.ext fun u => ?_
  rw [F.gram_spec, F.qForm.symm _ u]
  change _ = q u (Q (G (frameTransfer G Qs ω)))
  rw [← F.adj_spec _ _ (F.green_mem _ (F.transfer_mem ω)), F.pForm.symm (Qs u),
    F.green_symm _ (F.transfer_mem ω) _ (F.adj_mem u)]
  rfl
theorem transferAdj_eq [FiniteDimensional ℝ Y] (F : ProjFrame p q X Q Qs G A D) {f : V}
    (hf : f ∈ X) : frameTransferAdj p q G Qs f = Q (G f) := by
  refine F.qForm.ext fun u => ?_
  rw [F.transferAdj_spec, F.qForm.symm _ u, ← F.adj_spec _ _ (F.green_mem _ hf),
    F.pForm.symm (Qs u), F.green_symm _ hf _ (F.adj_mem u)]
  rfl
theorem gram_inverseValue [FiniteDimensional ℝ Y] (F : ProjFrame p q X Q Qs G A D) (w : Y) :
    frameGram p q G Qs (inverseValue univ (frameGram p q G Qs) w) = w := by
  obtain ⟨g, hg⟩ := F.gram_bijective.2 w
  have spec := Classical.epsilon_spec
    (p := fun g => g ∈ (univ : Set Y) ∧ frameGram p q G Qs g = w) ⟨g, mem_univ _, hg⟩
  exact spec.2
theorem orth_decomp [FiniteDimensional ℝ Y] (F : ProjFrame p q X Q Qs G A D) {f : V} (hf : f ∈ X) :
    f - frameTransfer G Qs (inverseValue univ (frameGram p q G Qs) (frameTransferAdj p q G Qs f)) ∈
        kerImage X Q D ∧
      ∀ w ∈ kerImage X Q D,
        p (frameTransfer G Qs (inverseValue univ (frameGram p q G Qs)
          (frameTransferAdj p q G Qs f))) w = 0 := by
  set c := inverseValue univ (frameGram p q G Qs) (frameTransferAdj p q G Qs f) with hc
  have hg : frameTransfer G Qs c ∈ X := F.transfer_mem c
  have hr : f - frameTransfer G Qs c ∈ X := X.sub_mem hf hg
  have hperp : ∀ u, p (f - frameTransfer G Qs c) (frameTransfer G Qs u) = 0 := fun u => by
    rw [F.pForm.sub_left, ← F.gram_spec, F.gram_inverseValue, F.transferAdj_spec, sub_self]
  constructor
  · refine ⟨G (f - frameTransfer G Qs c), ⟨F.green_mem _ hr, ?_⟩, ?_⟩
    · have hQ : Q (G (f - frameTransfer G Qs c)) = 0 := by
        apply F.qForm.eq_zero_of_self_eq_zero
        rw [F.qForm.symm, ← F.adj_spec _ _ (F.green_mem _ hr), F.pForm.symm,
          F.green_symm _ hr _ (F.adj_mem _)]
        exact hperp _
      exact hQ
    · have hQ : Q (G (f - frameTransfer G Qs c)) = 0 := by
        apply F.qForm.eq_zero_of_self_eq_zero
        rw [F.qForm.symm, ← F.adj_spec _ _ (F.green_mem _ hr), F.pForm.symm,
          F.green_symm _ hr _ (F.adj_mem _)]
        exact hperp _
      rw [F.ker_eq _ (F.green_mem _ hr) hQ, F.op_green _ hr]
  · rintro w ⟨n, ⟨hn, hQn⟩, rfl⟩
    rw [F.ker_eq n hn hQn]
    change p (G (Qs c)) (A n) = 0
    rw [F.green_symm _ (F.adj_mem c) _ (F.op_mem n hn), F.green_op n hn, F.adj_spec _ _ hn, hQn,
      F.qForm.zero_right]
theorem orthProjValue_eq [Nonempty V] [FiniteDimensional ℝ Y] (F : ProjFrame p q X Q Qs G A D)
    {f : V} (hf : f ∈ X) :
    orthProjValue (kerImage X Q D) p f =
      f - frameTransfer G Qs (inverseValue univ (frameGram p q G Qs)
        (frameTransferAdj p q G Qs f)) := by
  obtain ⟨h1, h2⟩ := F.orth_decomp hf
  refine F.pForm.orthProjValue_eq h1 fun w hw => ?_
  rw [sub_sub_cancel]
  exact h2 w hw
theorem orthProjValue_spec [Nonempty V] [FiniteDimensional ℝ Y] (F : ProjFrame p q X Q Qs G A D)
    {f : V} (hf : f ∈ X) :
    orthProjValue (kerImage X Q D) p f ∈ kerImage X Q D ∧
      ∀ w ∈ kerImage X Q D, p (f - orthProjValue (kerImage X Q D) p f) w = 0 := by
  obtain ⟨h1, h2⟩ := F.orth_decomp hf
  rw [F.orthProjValue_eq hf]
  refine ⟨h1, fun w hw => ?_⟩
  rw [sub_sub_cancel]
  exact h2 w hw
theorem orthProjValue_transfer [Nonempty V] [FiniteDimensional ℝ Y]
    (F : ProjFrame p q X Q Qs G A D) (ω : Y) :
    orthProjValue (kerImage X Q D) p (frameTransfer G Qs ω) = 0 := by
  rw [F.orthProjValue_eq (F.transfer_mem ω)]
  have : inverseValue univ (frameGram p q G Qs)
      (frameTransferAdj p q G Qs (frameTransfer G Qs ω)) = ω :=
    F.gram_injective (F.gram_inverseValue _)
  rw [this, sub_self]
end ProjFrame
end ProjFrameSection
theorem spacingLattice_finite {σ S : ℝ} (K : ℤ) (hK : K ≠ 0) (hS : S = K * σ) :
    (spacingLattice 4 S σ : Set (PeriodicTorus 4 S)).Finite := by
  have hfin : {k : Fin 4 → ℤ | ∀ μ, k μ ∈ Set.Ico (0 : ℤ) |K|}.Finite :=
    Set.Finite.pi' fun _ => Set.finite_Ico _ _
  refine (hfin.image fun k => torusProj 4 S fun μ => (k μ : ℝ) * σ).subset ?_
  rintro x ⟨k, rfl⟩
  refine ⟨fun μ => k μ % K, fun μ => ⟨Int.emod_nonneg _ hK, Int.emod_lt_abs _ hK⟩, ?_⟩
  funext μ
  simp only [torusProj]
  rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
  refine ⟨-(k μ / K), ?_⟩
  have hk : (k μ : ℝ) = ((k μ % K : ℤ) : ℝ) + (K : ℝ) * ((k μ / K : ℤ) : ℝ) := by
    exact_mod_cast (Int.emod_add_mul_ediv (k μ) K).symm
  rw [zsmul_eq_mul, hS]
  rw [hk]
  push_cast
  ring
variable (𝒮 : NestedRegions)
theorem L_pos_real : (0 : ℝ) < 𝒮.L := by apply _root_.YangMills.Construction.RegionSequence.ShellDecomposition.blockFactor_pos <;> assumption
theorem scaleSpacing_pos (n : ℤ) : 0 < scaleSpacing 𝒮.L 𝒮.ξ n := by apply _root_.YangMills.Construction.PartitionCubes.FirstTypeMaps.scaleSpacing_pos <;> assumption
theorem scale_zero : 𝒮.scale 0 = 𝒮.ξ := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.scale_zero <;> assumption
theorem side_eq_int_mul :
    ∃ k : ℤ, 0 < k ∧ 𝒮.side = (k : ℝ) * (2 * ((𝒮.L : ℝ) ^ 𝒮.s * 𝒮.ξ)) := by
  obtain ⟨k, hk⟩ := 𝒮.side_mem_zmultiples
  have hs : scaleSpacing 𝒮.L 𝒮.ξ 𝒮.s = (𝒮.L : ℝ) ^ 𝒮.s * 𝒮.ξ := by
    simp [scaleSpacing]
  rw [hs] at hk
  refine ⟨k, ?_, hk⟩
  have hpos : (0 : ℝ) < 2 * ((𝒮.L : ℝ) ^ 𝒮.s * 𝒮.ξ) :=
    mul_pos two_pos (mul_pos (pow_pos (L_pos_real 𝒮) _) 𝒮.ξ_pos)
  have h0 := 𝒮.side_pos
  rw [hk] at h0
  have : (0 : ℝ) < k := (mul_pos_iff_of_pos_right hpos).1 h0
  exact_mod_cast this
instance instFiniteFineSite : Finite 𝒮.FineSite := by
  obtain ⟨k, hk, hside⟩ := side_eq_int_mul 𝒮
  have hne : k * 2 * (𝒮.L : ℤ) ^ 𝒮.s ≠ 0 := by
    have : (𝒮.L : ℤ) ≠ 0 := by
      have := 𝒮.thirteen_le_L
      omega
    positivity
  refine (spacingLattice_finite (k * 2 * (𝒮.L : ℤ) ^ 𝒮.s) hne ?_).to_subtype
  rw [hside]
  push_cast
  ring
theorem mem_spacingLattice_of_scale (n : ℕ) {y : 𝒮.Point}
    (hy : y ∈ spacingLattice 4 𝒮.side (𝒮.scale n)) : y ∈ spacingLattice 4 𝒮.side 𝒮.ξ := by
  obtain ⟨k, rfl⟩ := hy
  refine ⟨fun μ => k μ * (𝒮.L : ℤ) ^ n, ?_⟩
  congr 1
  funext μ
  simp only [NestedRegions.scale, scaleSpacing, zpow_natCast]
  push_cast
  ring
instance instFiniteAllCentres : Finite 𝒮.allCentres := by
  have hf : (spacingLattice 4 𝒮.side 𝒮.ξ : Set 𝒮.Point).Finite :=
    Set.finite_coe_iff.1 (instFiniteFineSite 𝒮)
  refine (hf.subset ?_).to_subtype
  rintro y ⟨n, _, hy⟩
  exact mem_spacingLattice_of_scale 𝒮 n hy.2.1
instance instFinDimCoarse : FiniteDimensional ℝ 𝒮.Coarse := by
  infer_instance
theorem weightedSum_isPosBilin {ι : Type} [Finite ι] (w : ι → ℝ) (hw : ∀ i, 0 < w i) :
    IsPosBilin (fun a b : ι → ℝ => ∑ᶠ i, w i * a i * b i) := by
  let _ := Fintype.ofFinite ι
  refine ⟨fun a b => ?_, fun a b c => ?_, fun r a b => ?_, fun a ha => ?_⟩
  · simp only [finsum_eq_sum_of_fintype]
    exact Finset.sum_congr rfl fun i _ => by ring
  · simp only [finsum_eq_sum_of_fintype, Pi.add_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  · simp only [finsum_eq_sum_of_fintype, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  · simp only [finsum_eq_sum_of_fintype]
    obtain ⟨i, hi⟩ := Function.ne_iff.1 ha
    refine Finset.sum_pos' (fun j _ => ?_) ⟨i, Finset.mem_univ _, ?_⟩
    · have := (hw j).le
      have := mul_self_nonneg (a j)
      nlinarith
    · have h1 : 0 < a i * a i := mul_self_pos.2 hi
      have := mul_pos (hw i) h1
      nlinarith
theorem innerSum_isPosBilin :
    IsPosBilin (innerSum : (𝒮.FineSite → ℝ) → (𝒮.FineSite → ℝ) → ℝ) := by
  have e : (innerSum : (𝒮.FineSite → ℝ) → (𝒮.FineSite → ℝ) → ℝ) =
      fun a b => ∑ᶠ x, 𝒮.ξ ^ 4 * a x * b x := by
    funext a b
    let _ := Fintype.ofFinite 𝒮.FineSite
    simp only [innerSum, finsum_eq_sum_of_fintype, Finset.mul_sum, mul_assoc]
  rw [e]
  exact weightedSum_isPosBilin _ fun _ => pow_pos 𝒮.ξ_pos 4
theorem coarseInner_isPosBilin : IsPosBilin (NestedRegions.coarseInner (𝒮 := 𝒮)) :=
  weightedSum_isPosBilin _ fun _ => pow_pos (scaleSpacing_pos 𝒮 _) 4
variable {𝒮}
theorem blockAvg_add (f g : 𝒮.FineSite → ℝ) :
    NestedRegions.blockAvg (f + g) = NestedRegions.blockAvg f + NestedRegions.blockAvg g := by
  funext y
  simp only [NestedRegions.blockAvg, Pi.add_apply]
  rw [finsum_mem_add_distrib (Set.toFinite _), mul_add]
theorem blockAvg_smul (r : ℝ) (f : 𝒮.FineSite → ℝ) :
    NestedRegions.blockAvg (r • f) = r • NestedRegions.blockAvg f := by
  funext y
  simp only [NestedRegions.blockAvg, Pi.smul_apply, smul_eq_mul]
  rw [finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _),
    finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _), ← Finset.mul_sum]
  ring
theorem blockAvgAdj_spec (ω : 𝒮.Coarse) :
    NestedRegions.blockAvgAdj ω ∈ 𝒮.siteFns ∧
      ∀ u ∈ 𝒮.siteFns, innerSum (NestedRegions.blockAvgAdj ω) u =
        NestedRegions.coarseInner ω (NestedRegions.blockAvg u) := by
  let l : (𝒮.FineSite → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun u => NestedRegions.coarseInner ω (NestedRegions.blockAvg u)
      map_add' := fun a b => by rw [blockAvg_add, (coarseInner_isPosBilin 𝒮).add_right]
      map_smul' := fun r a => by
        rw [blockAvg_smul, (coarseInner_isPosBilin 𝒮).smul_right, RingHom.id_apply,
          smul_eq_mul] }
  obtain ⟨v, hv, hv'⟩ := (innerSum_isPosBilin 𝒮).exists_repr_mem 𝒮.siteFns l
  have spec := Classical.epsilon_spec
    (p := fun v => v ∈ (𝒮.siteFns : Set (𝒮.FineSite → ℝ)) ∧
      ∀ u ∈ (𝒮.siteFns : Set (𝒮.FineSite → ℝ)),
        innerSum v u = NestedRegions.coarseInner ω (NestedRegions.blockAvg u))
    ⟨v, hv, hv'⟩
  exact spec
theorem projFrame (h : CellStructure.CellStructureClaim) (𝒮 : NestedRegions) :
    ProjFrame innerSum NestedRegions.coarseInner 𝒮.siteFns NestedRegions.blockAvg
      NestedRegions.blockAvgAdj NestedRegions.gaugeGreenOp NestedRegions.gaugeLap
      NestedRegions.dirichletLap := by
  obtain ⟨-, -, -, hA, -, -, -, hP, -⟩ := h 𝒮
  have hzero : NestedRegions.blockAvgAdj (0 : 𝒮.Coarse) = 0 := by
    refine (innerSum_isPosBilin 𝒮).ext_of_mem (X := 𝒮.siteFns) (blockAvgAdj_spec 0).1
      (Submodule.zero_mem _) fun u hu => ?_
    rw [(blockAvgAdj_spec 0).2 u hu, (coarseInner_isPosBilin 𝒮).zero_left,
      (innerSum_isPosBilin 𝒮).zero_left]
  refine
    { pForm := innerSum_isPosBilin 𝒮
      qForm := coarseInner_isPosBilin 𝒮
      adj_mem := fun ω => (blockAvgAdj_spec ω).1
      adj_spec := fun ω => (blockAvgAdj_spec ω).2
      adj_inj := hA.avgAdj_injective
      green_mem := fun f hf => (hP.green_exists f hf).1
      op_mem := hP.gauge_symmetric.1
      op_green := fun f hf => (hP.green_exists f hf).2.1
      green_op := fun f hf => (hP.green_exists f hf).2.2
      green_symm := hP.green_symmetric.2
      ker_eq := fun n _ hn => ?_ }
  have hw : NestedRegions.weightMul (0 : 𝒮.Coarse) = 0 := by
    funext y
    simp [NestedRegions.weightMul]
  simp only [NestedRegions.gaugeLap, hn, hw, hzero, add_zero]
theorem transferRange (h : CellStructure.CellStructureClaim) (𝒮 : NestedRegions) :
    TransferRange 𝒮 := by
  have F := projFrame h 𝒮
  have hsq : (NestedRegions.transferGram (𝒮 := 𝒮)) = NestedRegions.avgGreenSq := F.gram_eq
  refine
    { transferOp_mem := F.transfer_mem
      transferOp_injective := F.transfer_injective
      transferGram_bijective := F.gram_bijective
      avgGreenSq_bijective := hsq ▸ F.gram_bijective
      transferGramInv_eq := fun ω => ?_
      complProj_eq_transfer := fun f hf => ?_
      complProj_eq_green := fun f hf => ?_
      rangeProj_transferOp := F.orthProjValue_transfer }
  · simp only [NestedRegions.transferGramInv, NestedRegions.avgGreenSqInv, hsq]
  · have := F.orthProjValue_eq hf
    change f - NestedRegions.rangeProj f = _
    rw [show NestedRegions.rangeProj f = _ from this, sub_sub_cancel]
    rfl
  · have := F.orthProjValue_eq hf
    change f - NestedRegions.rangeProj f = _
    rw [show NestedRegions.rangeProj f = _ from this, sub_sub_cancel, F.transferAdj_eq hf]
    change _ = NestedRegions.gaugeGreenOp (NestedRegions.blockAvgAdj
      (inverseValue univ NestedRegions.avgGreenSq _))
    rw [← hsq]
    rfl
theorem isPartitionLevel_of_le (𝒮 : NestedRegions) {i : ℕ} (hi : i ≤ 𝒮.s) :
    𝒮.IsPartitionLevel i := by apply _root_.YangMills.Construction.RegionSequence.PartitionConsequences.isPartitionLevel_of_le_s <;> assumption
theorem Ω_antitone (𝒮 : NestedRegions) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ 𝒮.s) :
    𝒮.Ω b ⊆ 𝒮.Ω a := by apply _root_.YangMills.Construction.RegionSequence.ShellDecomposition.Ω_antitone <;> assumption
theorem le_s_of_mem_centresAt (𝒮 : NestedRegions) {n : ℕ} {y : 𝒮.Point} (hy : y ∈ 𝒮.centresAt n) :
    n ≤ 𝒮.s := by apply _root_.YangMills.Construction.RegionSequence.ShellDecomposition.le_s_of_mem_centresAt <;> assumption
theorem mem_Ω_of_mem_centresAt (h : CellStructure.CellStructureClaim) (𝒮 : NestedRegions) {n : ℕ}
    {y : 𝒮.Point} (hy : y ∈ 𝒮.centresAt n) : y ∈ 𝒮.Ω n := by
  obtain ⟨-, hC, -⟩ := h 𝒮
  have hn := le_s_of_mem_centresAt 𝒮 hy
  exact ((hC.cell_subset n hn y hy).2 hy.2.2).1
theorem not_mem_Ω_succ (h : CellStructure.CellStructureClaim) (𝒮 : NestedRegions) {n : ℕ}
    {y : 𝒮.Point} (hy : y ∈ 𝒮.centresAt n) : y ∉ 𝒮.Ω (n + 1) := by
  obtain ⟨hP, hC, -⟩ := h 𝒮
  have hn := le_s_of_mem_centresAt 𝒮 hy
  have hlay : y ∈ 𝒮.shellOf n := hy.2.2
  rw [hC.shell_eq n hn] at hlay
  obtain ⟨Qc, hQ, hyQ⟩ := hlay
  obtain ⟨Q0, hQ0, hint, huniq⟩ :=
    hP.site_interior n n le_rfl (isPartitionLevel_of_le 𝒮 hn) y hy.2.1
  have e : Qc = Q0 := huniq Qc hQ.1 hyQ
  subst e
  exact Set.disjoint_left.1 (hC.interior_disjoint n hn Qc hQ) hint
theorem level_eq (h : CellStructure.CellStructureClaim) (𝒮 : NestedRegions) {n : ℕ}
    {y : 𝒮.Point} (hy : y ∈ 𝒮.centresAt n) : 𝒮.level y = n := by
  have hmem : n ∈ {m | y ∈ shellSites 𝒮.L 𝒮.ξ 𝒮.Ω m} := hy
  have hle : 𝒮.level y ≤ n := Nat.sInf_le hmem
  refine le_antisymm hle ?_
  by_contra hlt
  have hm : 𝒮.level y ∈ {m | y ∈ shellSites 𝒮.L 𝒮.ξ 𝒮.Ω m} := Nat.sInf_mem ⟨n, hmem⟩
  have hn := le_s_of_mem_centresAt 𝒮 hy
  exact not_mem_Ω_succ h 𝒮 (n := 𝒮.level y) hm
    (Ω_antitone 𝒮 (by omega) hn (mem_Ω_of_mem_centresAt h 𝒮 hy))
theorem supNorm_zero_le {S : ℝ} {σ : ℝ} (hσ : 0 ≤ σ) : supNorm (0 : PeriodicTorus 4 S) ≤ σ / 2 := by
  have h0 : supNorm (0 : PeriodicTorus 4 S) ≤ 0 := by
    refine csInf_le ⟨0, ?_⟩ ⟨0, ?_, by simp⟩
    · rintro r ⟨v, -, rfl⟩
      exact norm_nonneg v
    · funext μ
      simp [torusProj]
  linarith
theorem fineBlock_zero (h : CellStructure.CellStructureClaim) (𝒮 : NestedRegions)
    (x : 𝒮.FineSite) : 𝒮.fineBlock 0 (x : 𝒮.Point) = {x} := by
  obtain ⟨hP, -⟩ := h 𝒮
  have hx : (x : 𝒮.Point) ∈ spacingLattice 4 𝒮.side (𝒮.scale 0) := by
    rw [scale_zero]
    exact x.2
  have hcard := (hP.block_sites 0 (Nat.zero_le _) x hx).2
  simp only [zero_mul, pow_zero] at hcard
  obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 hcard
  have hxm : x ∈ 𝒮.fineBlock 0 (x : 𝒮.Point) := by
    change supNorm ((x : 𝒮.Point) - (x : 𝒮.Point)) ≤ _
    rw [sub_self]
    exact supNorm_zero_le (scaleSpacing_pos 𝒮 _).le
  rw [ha] at hxm ⊢
  rw [Set.mem_singleton_iff.1 hxm]
theorem blockAvg_of_level_zero (h : CellStructure.CellStructureClaim) (𝒮 : NestedRegions)
    (x : 𝒮.FineSite) (hy : (x : 𝒮.Point) ∈ 𝒮.allCentres) (h0 : 𝒮.level x = 0)
    (f : 𝒮.FineSite → ℝ) : NestedRegions.blockAvg f ⟨x, hy⟩ = f x := by
  simp only [NestedRegions.blockAvg, h0, fineBlock_zero h 𝒮 x, finsum_mem_singleton]
  simp
theorem avgKernel_eq (h : CellStructure.CellStructureClaim) (𝒮 : NestedRegions)
    (hΩ : ∀ x ∈ 𝒮.innerNbhd, (x : 𝒮.Point) ∈ 𝒮.Ω 0) :
    𝒮.avgKernel = 𝒮.zeroMeanOnInner := by
  ext f
  constructor
  · rintro ⟨hfX, hQ⟩
    refine ⟨fun x hx => ?_, fun n hn y hy => ?_⟩
    · by_cases hx0 : (x : 𝒮.Point) ∈ 𝒮.Ω 0
      · have hy : (x : 𝒮.Point) ∈ 𝒮.centresAt 0 := by
          refine ⟨Nat.zero_le _, ?_, subset_closure ⟨hx0, hx⟩⟩
          change (x : 𝒮.Point) ∈ spacingLattice 4 𝒮.side (𝒮.scale 0)
          rw [scale_zero]
          exact x.2
        have hs : (x : 𝒮.Point) ∈ 𝒮.allCentres := ⟨0, Nat.zero_le _, hy⟩
        have := congrFun hQ ⟨x, hs⟩
        rwa [blockAvg_of_level_zero h 𝒮 x hs (level_eq h 𝒮 hy)] at this
      · exact hfX x hx0
    · have hs : y ∈ 𝒮.allCentres := ⟨n, le_s_of_mem_centresAt 𝒮 hy, hy⟩
      have := congrFun hQ ⟨y, hs⟩
      simp only [NestedRegions.blockAvg, level_eq h 𝒮 hy, Pi.zero_apply] at this
      exact this
  · rintro ⟨hf1, hf2⟩
    refine ⟨fun x hx => hf1 x fun h1 => hx (hΩ x (Or.inl h1)), ?_⟩
    funext ⟨y, hs⟩
    obtain ⟨n, hn, hy⟩ := id hs
    have hy' : y ∈ 𝒮.centresAt n := hy
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · have hl : y ∈ spacingLattice 4 𝒮.side 𝒮.ξ := mem_spacingLattice_of_scale 𝒮 0 hy'.2.1
      have := blockAvg_of_level_zero h 𝒮 ⟨y, hl⟩ hs (level_eq h 𝒮 hy') f
      refine this.trans (hf1 ⟨y, hl⟩ (not_mem_Ω_succ h 𝒮 hy'))
    · have := hf2 n hpos y hy'
      simp only [NestedRegions.blockAvg, level_eq h 𝒮 hy', Pi.zero_apply]
      exact this
theorem mem_centresAt_iff (𝒮 : NestedRegions) {n : ℕ} {y : 𝒮.Point} :
    y ∈ 𝒮.centresAt n ↔ y ∈ spacingLattice 4 𝒮.side (𝒮.scale n) ∧ y ∈ 𝒮.shellOf n := by apply _root_.YangMills.Construction.SeparatedClasses.NestedGeometryOfClass.mem_centresAt_iff <;> assumption
end YangMills.Construction.RegionSequence.GaugeProjections
