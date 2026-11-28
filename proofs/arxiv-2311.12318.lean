import OMAStatements.S_arxiv_2311_12318
import Mathlib

-- Problem: A note on cube-free problems (Yuchen Meng, arXiv:2311.12318).
-- Proof idea for the upper bound: if 3|A| > 2N then some x has x and 2x in A
-- (doubling is at most two-to-one on Z_N), and some z has z, z+x, z+2x in A
-- (three translates of the complement cannot cover Z_N); then the cube of x, x, z lies in A.

namespace OMA.Helpers

open Finset

theorem two_torsion {N : ℕ} [NeZero N] (d : ZMod N) (h : d + d = 0) :
    d = 0 ∨ d = ((N / 2 : ℕ) : ZMod N) := by
  have hv : ((d.val : ℕ) : ZMod N) = d := ZMod.natCast_zmod_val d
  have hlt : d.val < N := ZMod.val_lt d
  have h2 : ((2 * d.val : ℕ) : ZMod N) = 0 := by
    rw [Nat.cast_mul, hv, Nat.cast_two, two_mul]
    exact h
  rw [ZMod.natCast_eq_zero_iff] at h2
  obtain ⟨k, hk⟩ := h2
  have hk2 : k < 2 := by
    by_contra hc
    push_neg at hc
    have : N * 2 ≤ N * k := Nat.mul_le_mul_left N hc
    nlinarith
  interval_cases k
  · left
    have : d.val = 0 := by omega
    rw [← hv, this, Nat.cast_zero]
  · right
    have : d.val = N / 2 := by omega
    rw [← hv, this]

theorem upper {N : ℕ} [NeZero N] (A : Finset (ZMod N))
    (hA : OMA.S_arxiv_2311_12318.CubeFree (A : Set (ZMod N))) : 3 * A.card ≤ 2 * N := by
  classical
  by_contra hcon
  push_neg at hcon
  set C : Finset (ZMod N) := Finset.univ \ A with hC
  have hAle : A.card ≤ N := by
    have := Finset.card_le_univ A
    rwa [ZMod.card] at this
  have hcardC : C.card + A.card = N := by
    rw [hC, Finset.card_sdiff_of_subset (Finset.subset_univ A), Finset.card_univ, ZMod.card]
    omega
  have memC : ∀ x, x ∈ C ↔ x ∉ A := by
    intro x
    simp [hC]
  have huniv : (Finset.univ : Finset (ZMod N)).card = N := by
    rw [Finset.card_univ, ZMod.card]
  -- step 1: some x with x and x + x in A
  have step1 : ∃ x, x ∈ A ∧ x + x ∈ A := by
    by_contra hne
    push_neg at hne
    let g : ZMod N → ZMod N := fun c => if h : ∃ x, x + x = c then h.choose else 0
    have hg : ∀ x, g (x + x) + g (x + x) = x + x := by
      intro x
      have h : ∃ y, y + y = x + x := ⟨x, rfl⟩
      simp only [g, dif_pos h]
      exact h.choose_spec
    have cover : (Finset.univ : Finset (ZMod N)) ⊆
        C ∪ (C.image g ∪ C.image (fun c => g c + ((N / 2 : ℕ) : ZMod N))) := by
      intro x _
      by_cases hx : x ∈ A
      · have h2 : x + x ∈ C := (memC _).2 (hne x hx)
        have hd : (x - g (x + x)) + (x - g (x + x)) = 0 := by
          rw [show (x - g (x + x)) + (x - g (x + x)) = (x + x) - (g (x + x) + g (x + x)) by ring,
            hg x, sub_self]
        rcases two_torsion (x - g (x + x)) hd with h0 | h1
        · refine mem_union_right _ (mem_union_left _ (mem_image.2 ⟨x + x, h2, ?_⟩))
          exact (sub_eq_zero.1 h0).symm
        · refine mem_union_right _ (mem_union_right _ (mem_image.2 ⟨x + x, h2, ?_⟩))
          show g (x + x) + ((N / 2 : ℕ) : ZMod N) = x
          rw [← h1]
          ring
      · exact mem_union_left _ ((memC x).2 hx)
    have h1 := Finset.card_le_card cover
    have h2 := Finset.card_union_le C (C.image g ∪ C.image (fun c => g c + ((N / 2 : ℕ) : ZMod N)))
    have h3 := Finset.card_union_le (C.image g) (C.image (fun c => g c + ((N / 2 : ℕ) : ZMod N)))
    have h4 := Finset.card_image_le (s := C) (f := g)
    have h5 := Finset.card_image_le (s := C) (f := fun c => g c + ((N / 2 : ℕ) : ZMod N))
    omega
  obtain ⟨x, hx1, hx2⟩ := step1
  -- step 2: some z with z, z + x, z + (x + x) in A
  have step2 : ∃ z, z ∉ C ∪ (C.image (fun c => c - x) ∪ C.image (fun c => c - (x + x))) := by
    by_contra hne
    push_neg at hne
    have cover : (Finset.univ : Finset (ZMod N)) ⊆
        C ∪ (C.image (fun c => c - x) ∪ C.image (fun c => c - (x + x))) := fun z _ => hne z
    have h1 := Finset.card_le_card cover
    have h2 := Finset.card_union_le C (C.image (fun c => c - x) ∪ C.image (fun c => c - (x + x)))
    have h3 := Finset.card_union_le (C.image (fun c => c - x)) (C.image (fun c => c - (x + x)))
    have h4 := Finset.card_image_le (s := C) (f := fun c => c - x)
    have h5 := Finset.card_image_le (s := C) (f := fun c => c - (x + x))
    omega
  obtain ⟨z, hz⟩ := step2
  have hz1 : z ∈ A := by
    by_contra h
    exact hz (mem_union_left _ ((memC z).2 h))
  have hz2 : x + z ∈ A := by
    by_contra h
    apply hz
    refine mem_union_right _ (mem_union_left _ (mem_image.2 ⟨x + z, (memC _).2 h, ?_⟩))
    show x + z - x = z
    ring
  have hz3 : x + x + z ∈ A := by
    by_contra h
    apply hz
    refine mem_union_right _ (mem_union_right _ (mem_image.2 ⟨x + x + z, (memC _).2 h, ?_⟩))
    show x + x + z - (x + x) = z
    ring
  apply hA x x z
  intro w hw
  simp only [OMA.S_arxiv_2311_12318.cube, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Finset.mem_coe.2 hx1
  · exact Finset.mem_coe.2 hx1
  · exact Finset.mem_coe.2 hz1
  · exact Finset.mem_coe.2 hx2
  · exact Finset.mem_coe.2 hz2
  · exact Finset.mem_coe.2 hz2
  · exact Finset.mem_coe.2 hz3

theorem count_range (m : ℕ) :
    ((Finset.range (3 * m)).filter (fun i => i % 3 = 1 ∨ i % 3 = 2)).card = 2 * m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.card_filter] at ih ⊢
    rw [show 3 * (m + 1) = 3 * m + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, ih]
    have e1 : (3 * m) % 3 = 0 := by omega
    have e2 : (3 * m + 1) % 3 = 1 := by omega
    have e3 : (3 * m + 1 + 1) % 3 = 2 := by omega
    simp only [e1, e2, e3]
    norm_num
    ring

theorem tight {N : ℕ} [NeZero N] (h3 : 3 ∣ N) : ∃ A : Finset (ZMod N),
      (∀ a : ZMod N, a ∈ A ↔ a.val % 3 = 1 ∨ a.val % 3 = 2) ∧
      OMA.S_arxiv_2311_12318.CubeFree (A : Set (ZMod N)) ∧ 3 * A.card = 2 * N := by
  classical
  refine ⟨Finset.univ.filter (fun a : ZMod N => a.val % 3 = 1 ∨ a.val % 3 = 2), ?_, ?_, ?_⟩
  · intro a
    simp
  · intro x y z hsub
    have key : ∀ a : ZMod N, (a.val % 3 = 1 ∨ a.val % 3 = 2) →
        ZMod.castHom h3 (ZMod 3) a ≠ 0 := by
      intro a ha
      rw [ZMod.castHom_apply, ZMod.cast_eq_val, Ne, ← ZMod.val_eq_zero, ZMod.val_natCast]
      omega
    have mem : ∀ a, a ∈ OMA.S_arxiv_2311_12318.cube x y z → ZMod.castHom h3 (ZMod 3) a ≠ 0 := by
      intro a ha
      have := hsub ha
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at this
      exact key a this
    have hx := mem x (by simp [OMA.S_arxiv_2311_12318.cube])
    have hy := mem y (by simp [OMA.S_arxiv_2311_12318.cube])
    have hz := mem z (by simp [OMA.S_arxiv_2311_12318.cube])
    have hxy := mem (x + y) (by simp [OMA.S_arxiv_2311_12318.cube])
    have hyz := mem (y + z) (by simp [OMA.S_arxiv_2311_12318.cube])
    have hxyz := mem (x + y + z) (by simp [OMA.S_arxiv_2311_12318.cube])
    rw [map_add] at hxy hyz
    rw [map_add, map_add] at hxyz
    generalize ZMod.castHom h3 (ZMod 3) x = X at *
    generalize ZMod.castHom h3 (ZMod 3) y = Y at *
    generalize ZMod.castHom h3 (ZMod 3) z = Z at *
    revert X Y Z
    decide
  · have hcard : (Finset.univ.filter (fun a : ZMod N => a.val % 3 = 1 ∨ a.val % 3 = 2)).card
        = ((Finset.range N).filter (fun i => i % 3 = 1 ∨ i % 3 = 2)).card := by
      apply Finset.card_bij' (fun (a : ZMod N) _ => a.val) (fun (i : ℕ) _ => (i : ZMod N))
      · intro a ha
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
        simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨ZMod.val_lt a, ha⟩
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_range] at hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [ZMod.val_cast_of_lt hi.1]
        exact hi.2
      · intro a _
        exact ZMod.natCast_zmod_val a
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_range] at hi
        exact ZMod.val_cast_of_lt hi.1
    obtain ⟨m, rfl⟩ := h3
    rw [hcard, count_range]
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_arxiv_2311_12318.main := by
  intro N _
  exact ⟨fun A hA => OMA.Helpers.upper A hA, fun h3 => OMA.Helpers.tight h3⟩
