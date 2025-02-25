import NatNormalForm.Term
import NatNormalForm.Normal


theorem NatTerm.plus_Z_eq_normal {n: NatTerm}:
  n.normal -> n.plus .Z = n := by
    intros H
    induction n with
    | Z =>
      simp [plus]
    | S m IHm =>
      simp [plus]
      apply IHm
      cases H
      assumption
    | Plus n1 n2 IHn1 IHn2 =>
      apply H.not_sum
    | Mult =>
      apply H.not_prod


theorem NatTerm.plus_Z_eq {n: NatTerm}: (n + 0).Eq1 n := by
  apply NatTerm.eq_normal.mp
  simp [normalize]
  let E := n.normalize.plus_Z_eq_normal
  specialize (E n.normalize_normal)
  rewrite [E]
  eq_refl


theorem NatTerm.plus_S_eq_normal {m n: NatTerm}:
  m.normal -> (m.plus n.S) = (m.plus n).S := by
    intros Nm
    induction m with
    | Z =>
      simp [plus]
    | S m' IHm' =>
      simp [plus]
      apply IHm'
      apply Nm.pred
    | Plus =>
      apply Nm.not_sum
    | Mult =>
      apply Nm.not_prod


theorem NatTerm.plus_S_eq {m n: NatTerm}: (m + n.S).Eq1 (m + n).S := by
  apply NatTerm.eq_normal.mp
  simp [normalize]
  apply NatTerm.plus_S_eq_normal
  . apply m.normalize_normal


theorem NatTerm.plus_comm_normal {m n: NatTerm}:
  m.normal -> n.normal ->
  (m.plus n) = (n.plus m) := by
    intros Nm Nn
    induction m with
    | Z =>
      simp [plus]
      symm
      apply n.plus_Z_eq_normal
      apply Nn
    | S m' IHm' =>
      simp [plus]
      specialize (IHm' Nm.pred)
      rewrite [IHm']
      symm
      apply NatTerm.plus_S_eq_normal
      apply Nn
    | Plus =>
      apply Nm.not_sum
    | Mult =>
      apply Nm.not_prod


theorem NatTerm.plus_comm {m n: NatTerm}: (m + n).Eq1 (n + m) := by
  apply NatTerm.eq_normal.mp
  simp [normalize]
  apply NatTerm.plus_comm_normal
  . apply m.normalize_normal
  . apply n.normalize_normal
