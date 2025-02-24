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
  | ZNormal: Z.normal
  | SNormal {n: NatTerm}: n.normal -> n.S.normal


theorem NatTerm.normal.R1 {n: NatTerm}:
  n.normal -> n.R1_normal := by
  intros H
  induction H with
  | ZNormal =>
    intro contra
    let ⟨x, Hx⟩ := contra
    cases Hx
  | @SNormal n Hn IHn =>
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
    apply NatTerm.normal.ZNormal
  | S m IHm =>
    apply NatTerm.normal.SNormal
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


theorem NatTerm.normal.not_sum {P: Prop} {m n: NatTerm}
  (H: (m + n).normal): P := by
    cases H.R1 NatTerm.R1_normal.not_sum


theorem NatTerm.normal.not_prod {P: Prop} {m n: NatTerm}
  (H: (m * n).normal): P := by
    cases H.R1 NatTerm.R1_normal.not_prod


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
      apply NatTerm.normal.ZNormal
    | S n' IHn' =>
      apply NatTerm.normal.SNormal
      apply IHn'
      apply H
    | Plus n1 n2 =>
      cases H
    | Mult n1 n2 =>
      cases H
  . /- <- -/
    intros H
    induction H with
    | ZNormal =>
      simp [is_normal_b]
    | @SNormal n Hn IHn =>
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



def NatTerm.plus (m n: NatTerm): NatTerm :=
  match m with
  | .Z => n
  | .S m' => (m'.plus n).S
  | o => o + n


theorem NatTerm.MR1.plus_cong1 {m n1 n2: NatTerm}
  (r: n1.MR1 n2): (m.Plus n1).MR1 (m.plus n2) := by
    induction m with
    | Z =>
      simp [plus]
      apply NatTerm.MR1.trans
      . apply NatTerm.MR1.ZPlus
      . exact r
    | S m' IHm' =>
      simp [plus]
      apply NatTerm.MR1.trans
      . apply NatTerm.MR1.SPlus
      . apply NatTerm.MR1.SCong
        exact IHm'
    | Plus m1 m2 IHm1 IHm2 =>
      simp [plus]
      apply NatTerm.MR1.PlusCong1
      exact r
    | Mult =>
      simp [plus]
      apply NatTerm.MR1.PlusCong1
      exact r


theorem NatTerm.MR1.plus_cong2 {m1 m2 n: NatTerm}
  (r: m1.MR1 m2): (m1.Plus n).MR1 (m2.plus n) := by
    revert r m1
    induction m2 with
    | Z =>
      intros m1 r
      simp [plus]
      apply NatTerm.MR1.trans (b := Z + n)
      . apply NatTerm.MR1.PlusCong
        . exact r
        . apply NatTerm.MR1.refl
      . apply NatTerm.MR1.ZPlus
    | S m' IHm' =>
      intros m1 r
      simp [plus]
      apply NatTerm.MR1.trans (b := m'.S + n)
      . apply NatTerm.MR1.PlusCong2
        exact r
      . apply NatTerm.MR1.trans
        . apply NatTerm.MR1.SPlus
        . apply NatTerm.MR1.SCong
          apply IHm'
          apply NatTerm.MR1.refl
    | Plus m1 m2 IHm1 IHm2 =>
      intros m1 r
      simp [plus]
      apply NatTerm.MR1.PlusCong2
      exact r
    | Mult =>
      intros m1 r
      simp [plus]
      apply NatTerm.MR1.PlusCong2
      exact r

theorem NatTerm.MR1.plus_cong {m1 m2: NatTerm}: forall {n1 n2: NatTerm},
  m1.MR1 m2 -> n1.MR1 n2 -> (m1.Plus n1).MR1 (m2.plus n2) := by
    cases m2 with
    | Z =>
      intros n1 n2 r1 r2
      simp [plus]
      apply NatTerm.MR1.trans (b := 0 + n1)
      . apply NatTerm.MR1.PlusCong2
        exact r1
      . apply NatTerm.MR1.trans
        . apply NatTerm.MR1.ZPlus
        . exact r2
    | S m =>
      intros n1 n2 r1 r2
      simp [plus]
      apply NatTerm.MR1.trans (b := m.S + n2)
      . apply NatTerm.MR1.PlusCong
        . exact r1
        . exact r2
      . apply NatTerm.MR1.trans
        . apply NatTerm.MR1.SPlus
        . apply NatTerm.MR1.SCong
          apply NatTerm.MR1.plus_cong1
          apply NatTerm.MR1.refl
    | Plus =>
      simp [plus]
      intros n1 n2 r1 r2
      . apply NatTerm.MR1.PlusCong
        . exact r1
        . exact r2
    | Mult =>
      simp [plus]
      intros n1 n2 r1 r2
      . apply NatTerm.MR1.PlusCong
        . exact r1
        . exact r2


def NatTerm.mult (m n: NatTerm): NatTerm :=
  match m with
  | .Z => .Z
  | .S m' => (m'.mult n).plus n
  | o => o * n


theorem NatTerm.MR1.mult_cong1 {m n1 n2: NatTerm}
  (r: n1.MR1 n2): (m.Mult n1).MR1 (m.mult n2) := by
    induction m with
    | Z =>
      simp [mult]
      apply NatTerm.MR1.ZMult
    | S m' IHm' =>
      simp [mult]
      apply NatTerm.MR1.trans
      . apply NatTerm.MR1.SMult
      . apply NatTerm.MR1.plus_cong
        . exact IHm'
        . exact r
    | Plus m1 m2 IHm1 IHm2 =>
      simp [mult]
      apply NatTerm.MR1.MultCong1
      exact r
    | Mult =>
      simp [mult]
      apply NatTerm.MR1.MultCong1
      exact r


theorem NatTerm.MR1.mult_cong {m1 m2: NatTerm}: forall {n1 n2: NatTerm},
  m1.MR1 m2 -> n1.MR1 n2 -> (m1.Mult n1).MR1 (m2.mult n2) := by
    cases m2 with
    | Z =>
      intros n1 n2 r1 r2
      simp [mult]
      apply NatTerm.MR1.trans (b := 0 * n1)
      . apply NatTerm.MR1.MultCong2
        exact r1
      . apply NatTerm.MR1.ZMult
    | S m =>
      intros n1 n2 r1 r2
      simp [mult]
      apply NatTerm.MR1.trans (b := m * n1 + n1)
      . apply NatTerm.MR1.trans (b := m.S * n1)
        . apply NatTerm.MR1.MultCong2
          exact r1
        . apply NatTerm.MR1.SMult
      . apply NatTerm.MR1.plus_cong
        . apply NatTerm.MR1.mult_cong1
          exact r2
        . exact r2
    | Plus t1 t2 =>
      simp [mult]
      intros n1 n2 r1 r2
      . apply NatTerm.MR1.MultCong
        . exact r1
        . exact r2
    | Mult t1 t2 =>
      simp [mult]
      intros n1 n2 r1 r2
      . apply NatTerm.MR1.MultCong
        . exact r1
        . exact r2


def NatTerm.normalize (m: NatTerm): NatTerm :=
  match m with
  | .Z => .Z
  | .S m' => m'.normalize.S
  | .Plus m1 m2 => m1.normalize.plus m2.normalize
  | .Mult m1 m2 => m1.normalize.mult m2.normalize


theorem NatTerm.MR1_normalize {n: NatTerm}:
  n.MR1 n.normalize := by
  induction n with
  | Z =>
    simp [normalize]
    apply NatTerm.MR1.refl
  | S n' IHm' =>
    simp [normalize]
    apply NatTerm.MR1.SCong
    assumption
  | Plus n1 n2 IHn1 IHn2 =>
    simp [normalize]
    apply NatTerm.MR1.plus_cong
    . exact IHn1
    . exact IHn2
  | Mult n1 n2 IHn1 IHn2 =>
    simp [normalize]
    apply NatTerm.MR1.mult_cong
    . exact IHn1
    . exact IHn2


theorem NatTerm.normal.sum {m n: NatTerm}:
  m.normal -> n.normal -> (m.plus n).normal := by
  intro Hm Hn
  induction m with
  | Z =>
    simp [plus]
    apply Hn
  | S m' IHm' =>
    simp [plus]
    apply NatTerm.normal.SNormal
    apply IHm'
    cases Hm
    assumption
  | Plus =>
    apply Hm.not_sum
  | Mult =>
    apply Hm.not_prod


theorem NatTerm.normal.prod {m n: NatTerm}:
  m.normal -> n.normal -> (m.mult n).normal := by
  intros Hm Hn
  induction m with
  | Z =>
    simp [mult]
    apply NatTerm.normal.ZNormal
  | S m' IHm' =>
    simp [mult]
    apply NatTerm.normal.sum
    . apply IHm'
      cases Hm
      assumption
    . exact Hn
  | Plus =>
    apply Hm.not_sum
  | Mult =>
    apply Hm.not_prod


theorem NatTerm.normalize_normal {n: NatTerm}:
  n.normalize.normal := by
    induction n with
    | Z =>
      simp [normalize]
      apply NatTerm.normal.ZNormal
    | S n' IHn' =>
      simp [normalize]
      apply NatTerm.normal.SNormal
      assumption
    | Plus n1 n2 IHn1 IHn2 =>
      simp [normalize]
      apply NatTerm.normal.sum
      . assumption
      . assumption
    | Mult n1 n2 IHn1 IHn2 =>
      simp [normalize]
      apply NatTerm.normal.prod
      . assumption
      . assumption


theorem RTCl.split {m n: NatTerm}:
  m.MR1 n -> m = n \/ exists k, m.R1 k /\ k.MR1 n := by
    intros H
    induction H with
    | @inclusion a b r =>
      right
      exists b
      apply And.intro
      . exact r
      . exact NatTerm.MR1.refl
    | @refl x =>
      left
      eq_refl
    | @trans a b c Hab Hbc IHab IHbc =>
      cases IHab with
      | inl Eab => /- a = b -/
        cases IHbc with
        | inl Ebc => /- b = c -/
          left
          rewrite [Eab]
          exact Ebc
        | inr H => /- b -> k -/
          let ⟨k, Hk⟩ := H
          right
          exists k
          apply And.intro
          . rewrite [Eab]
            apply Hk.left
          . apply Hk.right
      | inr H => /- a -> k -/
        let ⟨k, Hk⟩ := H
        right
        exists k
        apply And.intro
        . exact Hk.left
        . apply NatTerm.MR1.trans
          . apply Hk.right
          . apply Hbc


theorem and3 {A B C: Prop} (a: A) (b: B) (c: C): A /\ B /\ C := by
  apply And.intro
  . apply a
  . apply And.intro
    . apply b
    . apply c


theorem NatTerm.MR1.S_inverse_lemma_E {m n: NatTerm}:
  m.MR1 n ->
  (exists p: NatTerm, m = p.S) ->
  exists t1 t2: NatTerm, m = t1.S /\ n = t2.S /\ t1.MR1 t2 := by
  intros H
  induction H with
  | @inclusion a b r =>
    intros H
    let ⟨x, E⟩ := H
    rewrite [E] at r
    cases r with
    | @SCong n1 n2 r =>
      exists x
      exists n2
      apply and3
      . apply E
      . eq_refl
      . apply NatTerm.R1.inclusion
        exact r
  | @refl x =>
    intros H
    let ⟨y, E⟩ := H
    exists y
    exists y
    apply and3
    . exact E
    . exact E
    . apply NatTerm.MR1.refl
  | @trans a b c Hab Hbc IHab IHbc =>
    intros H
    let ⟨x, E⟩ := H
    specialize (IHab H)
    let ⟨t1, ⟨t2, ⟨Ea, ⟨Eb, H12⟩⟩⟩⟩ := IHab
    specialize (IHbc ⟨t2, Eb⟩)
    let ⟨t2', ⟨t3, ⟨Eb', ⟨Ec, H23⟩⟩⟩⟩ := IHbc
    rewrite [Eb] at Eb'
    cases Eb'
    exists t1
    exists t3
    apply and3
    . exact Ea
    . exact Ec
    . apply NatTerm.MR1.trans
      . apply H12
      . apply H23


theorem NatTerm.MR1.S_inverse_lemma {m n: NatTerm}:
  m.S.MR1 n -> exists t: NatTerm, n = t.S /\ m.MR1 t := by
    intros H
    let E := H.S_inverse_lemma_E ⟨m, Eq.refl m.S⟩
    let ⟨t1, ⟨t2, ⟨E1, ⟨E2, K⟩⟩⟩⟩ := E
    cases E1
    cases E2
    exists t2


theorem NatTerm.MR1.S_inverse {m n: NatTerm}:
  m.S.MR1 n.S -> m.MR1 n := by
    intros H
    let E := H.S_inverse_lemma_E ⟨m, Eq.refl m.S⟩
    let ⟨t1, ⟨t2, ⟨E1, ⟨E2, H⟩⟩⟩⟩ := E
    cases E1
    cases E2
    apply H


def NatTerm.Eq1.church_rosser {m n: NatTerm}
  (H: m.Eq1 n): exists p: NatTerm, m.MR1 p /\ n.MR1 p
    := NatTerm.R1.church_rosser H


theorem NatTerm.Eq1.S_inverse {m n: NatTerm}:
  m.S.Eq1 n.S -> m.Eq1 n := by
    intros H
    let ⟨p, ⟨H1, H2⟩⟩ := H.church_rosser
    let ⟨t1, ⟨E1, K1⟩⟩ := H1.S_inverse_lemma
    let ⟨t2, ⟨E2, K2⟩⟩ := H2.S_inverse_lemma
    cases E1
    cases E2
    apply NatTerm.Eq1.trans
    . apply NatTerm.MR1.inclusion
      apply K1
    . apply NatTerm.Eq1.symm
      apply NatTerm.MR1.inclusion
      apply K2
