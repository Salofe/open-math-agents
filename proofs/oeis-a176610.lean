import OMAStatements.S_oeis_a176610
import Mathlib

namespace OMA.Helpers

open PowerSeries OMA.S_oeis_a176610

theorem coeff_ofNat_mul' (c : ℕ) [c.AtLeastTwo] (f : ℤ⟦X⟧) (n : ℕ) :
    coeff n ((no_index (OfNat.ofNat c : ℤ⟦X⟧)) * f) = (OfNat.ofNat c : ℤ) * coeff n f := by
  rw [← map_ofNat (C (R := ℤ)) c, coeff_C_mul]

theorem coeff_ofNat' (c : ℕ) [c.AtLeastTwo] (n : ℕ) :
    coeff n (no_index (OfNat.ofNat c : ℤ⟦X⟧)) = if n = 0 then (OfNat.ofNat c : ℤ) else 0 := by
  rw [← map_ofNat (C (R := ℤ)) c, coeff_C]

theorem deriv_ofNat' (c : ℕ) [c.AtLeastTwo] :
    d⁄dX ℤ (no_index (OfNat.ofNat c : ℤ⟦X⟧)) = 0 := by
  rw [← map_ofNat (C (R := ℤ)) c, derivative_C]

theorem cc_ofNat' (c : ℕ) [c.AtLeastTwo] :
    constantCoeff (no_index (OfNat.ofNat c : ℤ⟦X⟧)) = (OfNat.ofNat c : ℤ) :=
  map_ofNat _ c

theorem aList_length : ∀ n, (aList n).length = n + 1
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
    show (aList (n + 1) ++ [_]).length = _
    rw [List.length_append, aList_length (n + 1)]
    rfl

theorem aList_succ_getD (n k : ℕ) (hk : k ≤ n) :
    (aList (n + 1)).getD k 0 = (aList n).getD k 0 := by
  rcases n with _ | n
  · interval_cases k; rfl
  · show (aList (n + 1) ++ [_]).getD k 0 = _
    exact List.getD_append _ _ _ _ (by rw [aList_length]; omega)

theorem aList_getD (n k : ℕ) (hk : k ≤ n) : (aList n).getD k 0 = a k := by
  induction n with
  | zero => interval_cases k; rfl
  | succ n ih =>
    rcases Nat.lt_or_ge k (n + 1) with h | h
    · rw [aList_succ_getD n k (by omega), ih (by omega)]
    · have : k = n + 1 := by omega
      subst this; rfl

theorem a_rec (n : ℕ) : a (n + 2) =
    (∑ p ∈ Finset.range (n + 2), a p * a (n + 1 - p)) + ((n : ℤ) + 2) + 1 := by
  show (aList (n + 1) ++ [_]).getD (n + 2) 0 = _
  rw [List.getD_append_right _ _ _ _ (by rw [aList_length]), aList_length,
    Nat.sub_self, List.getD_cons_zero]
  congr 2
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mem_range] at hp
  rw [aList_getD _ _ (by omega), aList_getD _ _ (by omega)]

theorem a_zero : a 0 = 1 := rfl
theorem a_one : a 1 = 0 := rfl

noncomputable def GA : ℤ⟦X⟧ := PowerSeries.mk a

theorem coeff_GA (n : ℕ) : coeff n GA = a n := coeff_mk _ _

theorem ccGA : constantCoeff GA = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_GA]; rfl

theorem coeff_sq (m : ℕ) : coeff m (GA ^ 2) = ∑ p ∈ Finset.range (m + 1), a p * a (m - p) := by
  rw [pow_two, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_GA]

noncomputable def GB : ℤ⟦X⟧ := GA - X * GA ^ 2

theorem coeffGB (n : ℕ) : coeff n GB = if n = 0 then 1 else if n = 1 then -1 else (n : ℤ) + 1 := by
  match n with
  | 0 => simp [GB, ccGA]
  | 1 =>
    rw [GB, map_sub, coeff_succ_X_mul, coeff_sq, coeff_GA]
    simp [a_zero, a_one]
  | m + 2 =>
    rw [GB, map_sub, coeff_succ_X_mul, coeff_sq, coeff_GA, a_rec]
    simp only [show m + 2 ≠ 0 from by omega, show m + 2 ≠ 1 from by omega, if_false]
    push_cast
    ring

theorem ccGB : constantCoeff GB = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeffGB]; rfl

theorem FE : (1 - X) ^ 2 * GB = 1 - 3 * X + 6 * X ^ 2 - 3 * X ^ 3 := by
  have e : (1 - X) ^ 2 * GB = GB - (X * GB + X * GB) + X ^ 2 * GB := by ring
  rw [e]
  ext n
  match n with
  | 0 => simp [coeff_X_pow_mul', ccGB]
  | 1 => simp [coeff_X_pow_mul', coeffGB, ccGB, coeff_ofNat_mul', coeff_ofNat', cc_ofNat', coeff_X_pow, coeff_X]
  | 2 => simp [coeff_X_pow_mul', coeffGB, ccGB, coeff_ofNat_mul', coeff_ofNat', cc_ofNat', coeff_X_pow, coeff_X]
  | 3 => simp [coeff_X_pow_mul', coeffGB, ccGB, coeff_ofNat_mul', coeff_ofNat', cc_ofNat', coeff_X_pow, coeff_X]
  | m + 4 =>
    simp [coeff_X_pow_mul', coeffGB, ccGB, coeff_ofNat_mul', coeff_ofNat', cc_ofNat', coeff_X_pow, coeff_X]
    push_cast
    ring

theorem hF : (1 - X) ^ 2 * (GA - X * GA ^ 2) = 1 - 3 * X + 6 * X ^ 2 - 3 * X ^ 3 := FE

theorem hdF : d⁄dX ℤ ((1 - X) ^ 2 * (GA - X * GA ^ 2)) =
    d⁄dX ℤ (1 - 3 * X + 6 * X ^ 2 - 3 * X ^ 3 : ℤ⟦X⟧) := congrArg _ hF

theorem ODE0 : (4 : ℤ⟦X⟧) * (X - 1) ^ 3 *
    ((1 - 7 * X + 19 * X ^ 2 - 37 * X ^ 3 + 36 * X ^ 4 - 12 * X ^ 5) * (X * d⁄dX ℤ GA)
      + (1 - 5 * X + 9 * X ^ 2 - X ^ 3) * GA
      - (1 - 5 * X + 18 * X ^ 2 - 18 * X ^ 3 + 6 * X ^ 4)) = 0 := by
  have hd := hdF
  simp only [Derivation.leibniz, Derivation.leibniz_pow, map_sub, map_add,
    Derivation.map_one_eq_zero, derivative_X, deriv_ofNat', smul_eq_mul, nsmul_eq_mul] at hd
  norm_num at hd
  linear_combination
    (4 * (2 * (-X * (1 - X) ^ 2) * GA + (1 - X) ^ 2) * (-(1 - X) ^ 2 + 2 * X * (1 - X))
      - 8 * (2 * (-(1 - X) ^ 2 + 2 * X * (1 - X)) * GA + 2 * (-X * (1 - X) ^ 2) * d⁄dX ℤ GA
        + (-2 * (1 - X))) * (-X * (1 - X) ^ 2)) * hF
    + (4 * (2 * (-X * (1 - X) ^ 2) * GA + (1 - X) ^ 2) * (-X * (1 - X) ^ 2)) * hd

theorem ODE : (1 - 7 * X + 19 * X ^ 2 - 37 * X ^ 3 + 36 * X ^ 4 - 12 * X ^ 5) * (X * d⁄dX ℤ GA)
      + (1 - 5 * X + 9 * X ^ 2 - X ^ 3) * GA
      - (1 - 5 * X + 18 * X ^ 2 - 18 * X ^ 3 + 6 * X ^ 4) = 0 := by
  have hne : (4 : ℤ⟦X⟧) * (X - 1) ^ 3 ≠ 0 := by
    intro h
    have := congrArg constantCoeff h
    simp [cc_ofNat'] at this
  exact (mul_eq_zero.mp ODE0).resolve_left hne

theorem XdGA : X * d⁄dX ℤ GA = PowerSeries.mk (fun n => (n : ℤ) * a n) := by
  ext n
  rcases n with _ | n
  · simp
  · rw [coeff_succ_X_mul, coeff_derivative, coeff_GA, coeff_mk]
    push_cast
    ring

end OMA.Helpers

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a176610.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  have h := congrArg (coeff (m + 5)) OMA.Helpers.ODE
  rw [OMA.Helpers.XdGA] at h
  simp only [add_mul, sub_mul, mul_assoc, one_mul, map_add, map_sub, map_zero,
    OMA.Helpers.coeff_ofNat_mul', coeff_X_pow_mul', coeff_succ_X_mul, coeff_mk,
    OMA.Helpers.coeff_GA, coeff_X_pow, coeff_X, coeff_one, OMA.Helpers.coeff_ofNat'] at h
  simp at h
  simp only [show m + 5 - 1 = m + 4 from rfl, show m + 5 - 2 = m + 3 from rfl,
    show m + 5 - 3 = m + 2 from rfl, show m + 5 - 4 = m + 1 from rfl,
    show m + 5 - 5 = m from rfl]
  push_cast at h ⊢
  linear_combination h
