import NatNormalForm.Term


def NatTerm.R1_normal (n: NatTerm) := Not (exists m, n.R1 m)


def NatTerm.MR1_normal (n: NatTerm) := forall {m}, n.MR1 m -> n = m


theorem NatTerm.MR1_normal.R1_normal:
  forall {n: NatTerm}, n.MR1_normal -> n.R1_normal := by
  intros n HMR1 Hm
  let ⟨m, pm⟩ := Hm
  have H: n.MR1 m := NatTerm.R1.inclusion pm
  have E := HMR1 H
  rewrite [E] at pm
  apply NatTerm.R1.irrefl pm


theorem NatTerm.R1_normal.MR1_normal:
  forall {n: NatTerm}, n.R1_normal -> n.MR1_normal := by
  intros n HR1 m HMR1
  induction HMR1 with
  | @inclusion a b H =>
    exfalso
    apply HR1
    exists b
  | @refl x =>
    eq_refl
  | @trans a b c r1 r2 IHr1 IHr2 =>
    have E1 := IHr1 HR1
    rewrite [E1]
    rewrite [E1] at HR1
    have E2 := IHr2 HR1
    exact E2


theorem NatTerm.R1_normal_unique {n m1 m2: NatTerm}:
  m1.R1_normal -> m2.R1_normal ->
  (n.MR1 m1) -> (n.MR1 m2) ->
  (m1 = m2) := by
    intros N1 N2 r1 r2
    have ⟨m4, ⟨H14, H24 ⟩⟩ := NatTerm.R1.confl r1 r2
    have E1 := N1.MR1_normal H14
    have E2 := N2.MR1_normal H24
    rewrite [E1]
    rewrite [E2]
    eq_refl


theorem NatTerm.R1_normal.S_normal_inverse {n: NatTerm}:
  n.S.R1_normal -> n.R1_normal := by
  intros H
  intros contra
  let ⟨x, Hx⟩ := contra
  apply H
  exists x.S
  apply NatTerm.R1.SCong
  exact Hx


theorem NatTerm.R1_normal.not_sum_prod {m n: NatTerm}:
  (exists p, (m + n).R1 p) /\ (exists q, (m * n).R1 q) := by
  revert n
  induction m with
  | Z =>
    intros n
    apply And.intro
    . exists n
      apply NatTerm.R1.ZPlus
    . exists 0
      apply NatTerm.R1.ZMult
  | S m' IHm' =>
    intros n
    apply And.intro
    . exists (m' + n).S
      apply NatTerm.R1.SPlus
    . exists (m' * n + n)
      apply NatTerm.R1.SMult
  | Plus m1 m2 IHm1 IHm2 =>
    intros n
    let ⟨⟨p, Hp⟩, _⟩ := @IHm1 m2
    apply And.intro
    .
      exists p + n
      apply NatTerm.R1.PlusCong1
      exact Hp
    . exists p * n
      apply NatTerm.R1.MultCong1
      exact Hp
  | Mult m1 m2 IHm1 IHm2 =>
    intros n
    let ⟨_, ⟨q, Hq⟩⟩ := @IHm1 m2
    apply And.intro
    . exists q + n
      apply NatTerm.R1.PlusCong1
      exact Hq
    . exists q * n
      apply NatTerm.R1.MultCong1
      exact Hq


def NatTerm.R1_normal.not_sum {m n} := (@NatTerm.R1_normal.not_sum_prod m n).left
def NatTerm.R1_normal.not_prod {m n} := (@NatTerm.R1_normal.not_sum_prod m n).right


inductive NatTerm.normal: NatTerm -> Prop where
  | Z_normal: Z.normal
  | S_normal {n: NatTerm}: n.normal -> n.S.normal


theorem NatTerm.normal.R1 {n: NatTerm}:
  n.normal -> n.R1_normal := by
  intros H
  induction H with
  | Z_normal =>
    intro contra
    let ⟨x, Hx⟩ := contra
    cases Hx
  | @S_normal n Hn IHn =>
    intro contra
    let ⟨x, Hx⟩ := contra
    cases Hx
    case SCong m H =>
      apply IHn
      exists m


theorem NatTerm.R1_normal.normal {n: NatTerm}:
  n.R1_normal -> n.normal := by
  intros H
  induction n with
  | Z =>
    apply NatTerm.normal.Z_normal
  | S m IHm =>
    apply NatTerm.normal.S_normal
    apply IHm
    apply H.S_normal_inverse
  | Plus n1 n2 IHn1 IHn2 =>
    exfalso
    apply H
    apply NatTerm.R1_normal.not_sum
  | Mult n1 n2 IHn1 IHn2 =>
    exfalso
    apply H
    apply NatTerm.R1_normal.not_prod


def NatTerm.is_normal_b (n: NatTerm): Bool := match n with
  | Z => .true
  | S n' => n'.is_normal_b
  | _ => .false


theorem NatTerm.normal.decide {n: NatTerm}:
  n.is_normal_b <-> n.normal := by
  apply Iff.intro
  . /- -> -/
    intros H
    induction n with
    | Z =>
      apply NatTerm.normal.Z_normal
    | S n' IHn' =>
      apply NatTerm.normal.S_normal
      apply IHn'
      apply H
    | Plus n1 n2 =>
      cases H
    | Mult n1 n2 =>
      cases H
  . /- <- -/
    intros H
    induction H with
    | Z_normal =>
      simp [is_normal_b]
    | @S_normal n Hn IHn =>
      simp [is_normal_b]
      apply IHn


instance: DecidablePred NatTerm.normal := fun n => by
  generalize E: n.is_normal_b = t
  match t with
  | true =>
    apply Decidable.isTrue
    apply NatTerm.normal.decide.mp E
  | false =>
    apply Decidable.isFalse
    intros contra
    have H2 := NatTerm.normal.decide.mpr contra
    rewrite [H2] at E
    contradiction
