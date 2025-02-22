import NatNormalForm.Term


theorem NatTerm.plus_zero_eq: forall {n: NatTerm}, (n + 0).Eq1 n := by
  intros n
  induction n with
  | Z =>
    apply NatTerm.R1.inclusion
    apply NatTerm.R1.ZPlus
  | S n' IHn' =>
    apply NatTerm.Eq1.trans
    . /- (n'.S + 0).Eq1 (n' + 0).S -/
      apply NatTerm.R1.inclusion
      apply NatTerm.R1.SPlus
    . /- (n' + 0).S.Eq1 n'.S -/
      apply NatTerm.Eq1.SCong
      apply IHn'
  | Plus n1 n2 IHn1 IHn2 =>
    cases n1 with
    | Z =>
      have H: (Z.Plus n2 + 0).Eq1 (n2 + 0) := by
        apply NatTerm.Eq1.PlusCong (.inclusion .ZPlus) .refl
      apply NatTerm.Eq1.trans H
      apply NatTerm.Eq1.trans IHn2
      apply NatTerm.Eq1.symm (.inclusion .ZPlus)
    | S m =>
      admit
    | _ => admit
  | _ => admit
