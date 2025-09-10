import NatNormalForm.Relation


inductive NatTerm: Type where
  | Z: NatTerm
  | S: NatTerm -> NatTerm
  | Plus: NatTerm -> NatTerm -> NatTerm
  | Mult: NatTerm -> NatTerm -> NatTerm
  deriving Repr


instance : Add NatTerm where
  add := .Plus


instance : Mul NatTerm where
  mul := .Mult


instance castNat (n: Nat): OfNat NatTerm n := .mk $ match n with
  | .zero => .Z
  | .succ m => .S (castNat m).ofNat


def NatTerm.toNat (t: NatTerm): Nat := match t with
  | .Z => 0
  | .S n => n.toNat.succ
  | .Plus n1 n2 => n1.toNat + n2.toNat
  | .Mult n1 n2 => n1.toNat + n2.toNat


def NatTerm.eval1 (t: NatTerm): NatTerm := match t with
  | .Z => .Z
  | .S n => .S (.eval1 n)
  | .Plus n1 n2 => match n1 with
    | .Z => n2.eval1
    | .S m => S (m.eval1.Plus n2.eval1)
    | o => o.eval1 + n2.eval1
  | .Mult n1 n2 => match n1 with
    | .Z => .Z
    | .S m => (m.eval1.Mult n2.eval1) + n2.eval1
    | o => o.eval1 * n2.eval1


inductive NatTerm.R1: Relation NatTerm where
  | ZPlus {n: NatTerm}: NatTerm.R1 (0 + n) n
  | SPlus {m n}: NatTerm.R1 (m.S + n) (m + n).S
  | ZMult {n}: NatTerm.R1 (0 * n) 0
  | SMult {m n}: NatTerm.R1 (m.S * n) ((m * n) + n)
  -- for congruence
  | SCong {m n}: NatTerm.R1 m n -> NatTerm.R1 m.S n.S
  | PlusCong1 {m1 m2 n}: NatTerm.R1 m1 m2 -> NatTerm.R1 (m1 + n) (m2 + n)
  | PlusCong2 {m n1 n2}: NatTerm.R1 n1 n2 -> NatTerm.R1 (m + n1) (m + n2)
  | MultCong1 {m1 m2 n}: NatTerm.R1 m1 m2 -> NatTerm.R1 (m1 * n) (m2 * n)
  | MultCong2 {m n1 n2}: NatTerm.R1 n1 n2 -> NatTerm.R1 (m * n1) (m * n2)


theorem NatTerm.R1.irrefl: forall {n: NatTerm}, Not (n.R1 n) := by
  intros n H
  induction n with
  | Z =>
    cases H
  | S n' IHn' =>
    apply IHn'
    cases H with
    | SCong H' =>
      apply H'
  | Plus n1 n2 IHn1 IHn2 =>
    cases H with
    | PlusCong1 H' =>
      apply IHn1
      apply H'
    | PlusCong2 H' =>
      apply IHn2
      apply H'
  | Mult n1 n2 IHn1 IHn2 =>
    cases H with
    | MultCong1 H' =>
      apply IHn1
      apply H'
    | MultCong2 H' =>
      apply IHn2
      apply H'


theorem NatTerm.R1.S_inverse {m n: NatTerm}: m.S.R1 n.S -> m.R1 n := by
  intros H
  cases H with
  | SCong H' =>
    apply H'


theorem NatTerm.PM_reduce: forall m n: NatTerm, (exists k, (m + n).R1 k) ∧ (exists k, (m * n).R1 k) := by
  intro m
  induction m with (intro n)
  | Z =>
    apply And.intro
    . exists n
      constructor
    . exists .Z
      constructor
  | S t IH =>
    apply And.intro
    . exists (t + n).S
      constructor
    . exists (t * n + n)
      constructor
  | Plus m1 m2 IH1 IH2 =>
    let ⟨t, Ht⟩ := (IH1 m2).left
    apply And.intro
    . exists (t + n)
      constructor
      exact Ht
    . exists (t * n)
      constructor
      exact Ht
  | Mult m1 m2 IH1 IH2 =>
    let ⟨t, Ht⟩ := (IH1 m2).right
    apply And.intro
    . exists (t + n)
      constructor
      exact Ht
    . exists (t * n)
      constructor
      exact Ht

theorem NatTerm.S_step_step: forall n: NatTerm, (exists p, n.S.R1 p) -> (exists q, n.R1 q) := by
  intro n H
  let ⟨p, Hp⟩ := H
  cases Hp with
  | @SCong _ t P =>
    exists t

inductive NatTerm.R2: Relation NatTerm where
  | Refl {x}: NatTerm.R2 x x
  -- congruence
  | SCong {m n}: NatTerm.R2 m n -> NatTerm.R2 m.S n.S
  | PlusCong {m1 m2 n1 n2}: NatTerm.R2 m1 m2 -> NatTerm.R2 n1 n2 -> NatTerm.R2 (m1 + n1) (m2 + n2)
  | MultCong {m1 m2 n1 n2}: NatTerm.R2 m1 m2 -> NatTerm.R2 n1 n2 -> NatTerm.R2 (m1 * n1) (m2 * n2)
  -- computation
  | ZPlus {n1 n2}: NatTerm.R2 n1 n2 -> NatTerm.R2 (0 + n1) n2
  | SPlus {m1 m2 n1 n2}: NatTerm.R2 m1 m2 -> NatTerm.R2 n1 n2 -> NatTerm.R2 (m1.S + n1) (m2 + n2).S
  | ZMult {n}: NatTerm.R2 (0 * n) .Z
  | SMult {m1 m2 n1 n2}: NatTerm.R2 m1 m2 -> NatTerm.R2 n1 n2 -> NatTerm.R2 (m1.S * n1) (m2 * n2 + n2)



instance R2_imp_R1: SubRel NatTerm.R1 NatTerm.R2 where
  inclusion := by
    intros m n r1
    induction r1 with
    | ZPlus =>
      apply NatTerm.R2.ZPlus .Refl
    | @SPlus m n =>
      apply @NatTerm.R2.SPlus m m n n .Refl .Refl
    | ZMult =>
      apply NatTerm.R2.ZMult
    | @SMult m n =>
      apply @NatTerm.R2.SMult m m n n .Refl .Refl
    | SCong _ IH =>
      apply NatTerm.R2.SCong IH
    | @PlusCong1 m1 m2 n r IH =>
      apply @NatTerm.R2.PlusCong m1 m2 n n IH .Refl
    | @PlusCong2 m n1 n2 r IH =>
      apply @NatTerm.R2.PlusCong m m n1 n2 .Refl IH
    | @MultCong1 m1 m2 n r IH =>
      apply @NatTerm.R2.MultCong m1 m2 n n IH .Refl
    | @MultCong2 m n1 n2 r IH =>
      apply @NatTerm.R2.MultCong m m n1 n2 .Refl IH


theorem NatTerm.R2.S_inverse: forall {m n: NatTerm},
  m.S.R2 n.S -> m.R2 n := by
  intros m n H
  cases H
  case Refl =>
    apply NatTerm.R2.Refl
  case SCong H =>
    apply H


theorem NatTerm.R2.eval1: forall {m: NatTerm}, m.R2 m.eval1 := by
  intros m
  induction m with
  | Z =>
    unfold NatTerm.eval1
    apply NatTerm.R2.Refl
  | S n IHn =>
    unfold NatTerm.eval1
    apply NatTerm.R2.SCong IHn
  | Plus m n IHm IHn =>
    unfold NatTerm.eval1
    cases m
    case Z =>
      simp
      apply NatTerm.R2.ZPlus IHn
    case S m' =>
      simp
      unfold NatTerm.eval1 at IHm
      have H2 := NatTerm.R2.S_inverse IHm
      apply NatTerm.R2.SPlus H2 IHn
    case Plus m1 m2 =>
      simp
      apply NatTerm.R2.PlusCong IHm IHn
    case Mult m1 m2 =>
      simp
      apply NatTerm.R2.PlusCong IHm IHn
  | Mult m n IHm IHn =>
    unfold NatTerm.eval1
    cases m
    case Z =>
      simp
      apply NatTerm.R2.ZMult
    case S m' =>
      simp
      unfold NatTerm.eval1 at IHm
      have H2 := NatTerm.R2.S_inverse IHm
      apply NatTerm.R2.SMult H2 IHn
    case Plus m1 m2 =>
      simp
      apply NatTerm.R2.MultCong IHm IHn
    case Mult m1 m2 =>
      simp
      apply NatTerm.R2.MultCong IHm IHn


theorem NatTerm.R2.eval1_left: forall {m n: NatTerm}, m.R2 n -> n.R2 m.eval1 := by
  intros m n r
  induction r with
  | Refl => apply NatTerm.R2.eval1
  | SCong r' IHr' =>
    unfold NatTerm.eval1
    apply NatTerm.R2.SCong IHr'
  | @PlusCong m1 m2 n1 n2 r1 r2 IHr1 IHr2 =>
    cases m1
    case Z =>
      cases r1
      unfold NatTerm.eval1; simp
      apply NatTerm.R2.ZPlus IHr2
    case S m1' =>
      cases r1
      case Refl =>
        unfold NatTerm.eval1; simp
        apply NatTerm.R2.SPlus R2.eval1 IHr2
      case SCong t H =>
        unfold NatTerm.eval1; simp
        unfold NatTerm.eval1 at IHr1
        have IHr1 := NatTerm.R2.S_inverse IHr1
        apply NatTerm.R2.SPlus IHr1 IHr2
    case Plus t1 t2 =>
      unfold NatTerm.eval1; simp
      apply NatTerm.R2.PlusCong IHr1 IHr2
    case Mult t1 t2 =>
      unfold NatTerm.eval1; simp
      cases r1 with
      | _ =>
        apply NatTerm.R2.PlusCong IHr1 IHr2
  | @MultCong m1 m2 n1 n2 r1 r2 IHr1 IHr2 =>
    cases m1
    case Z =>
      cases r1
      unfold NatTerm.eval1; simp
      apply NatTerm.R2.ZMult
    case S m1' =>
      cases r1
      case Refl =>
        unfold NatTerm.eval1; simp
        unfold NatTerm.eval1 at IHr1
        have IHr1 := NatTerm.R2.S_inverse IHr1
        apply NatTerm.R2.SMult IHr1 IHr2
      case SCong t H =>
        unfold NatTerm.eval1; simp
        unfold NatTerm.eval1 at IHr1
        have IHr1 := NatTerm.R2.S_inverse IHr1
        apply NatTerm.R2.SMult IHr1 IHr2
    case Plus t1 t2 =>
      unfold NatTerm.eval1; simp
      apply NatTerm.R2.MultCong IHr1 IHr2
    case Mult t1 t2 =>
      unfold NatTerm.eval1; simp
      cases r1 with
      | _ =>
        apply NatTerm.R2.MultCong IHr1 IHr2
  | @ZPlus n1 n2 r IHr =>
    unfold NatTerm.eval1; simp
    apply IHr
  | @SPlus m1 m2 n1 n2 r1 r2 IHr1 IHr2 =>
    unfold NatTerm.eval1; simp
    apply NatTerm.R2.SCong
    apply NatTerm.R2.PlusCong IHr1 IHr2
  | @ZMult t =>
    unfold NatTerm.eval1; simp
    apply NatTerm.R2.Refl
  | @SMult m1 m2 n1 n2 r1 r2 IHr1 IHr2 =>
    unfold NatTerm.eval1; simp
    apply NatTerm.R2.PlusCong
    . apply NatTerm.R2.MultCong IHr1 IHr2
    . apply IHr2


/--
Multi-step reduction
-/
abbrev NatTerm.MR1 := RTCl NatTerm.R1
abbrev NatTerm.Eq1 := ECl NatTerm.R1


theorem NatTerm.MR1.ZPlus {n: NatTerm}: (Z + n).MR1 n := by
  apply NatTerm.R1.inclusion
  apply NatTerm.R1.ZPlus


theorem NatTerm.MR1.SPlus {m n: NatTerm}: (m.S + n).MR1 (m + n).S := by
  apply NatTerm.R1.inclusion
  apply NatTerm.R1.SPlus


theorem NatTerm.MR1.ZMult {n: NatTerm}: (Z * n).MR1 0 := by
  apply NatTerm.R1.inclusion
  apply NatTerm.R1.ZMult


theorem NatTerm.MR1.SMult {m n: NatTerm}: (m.S * n).MR1 (m * n + n) := by
  apply NatTerm.R1.inclusion
  apply NatTerm.R1.SMult


theorem NatTerm.MR1.SCong {m n: NatTerm} (r: m.MR1 n) : m.S.MR1 n.S := by
  apply NatTerm.R1.keep_cong NatTerm.S
  . apply NatTerm.R1.SCong
  . apply r


theorem NatTerm.MR1.PlusCong {m1 m2 n1 n2: NatTerm}
  (r1: m1.MR1 m2) (r2: n1.MR1 n2): (m1 + n1).MR1 (m2 + n2) := by
  apply NatTerm.MR1.trans (b := m1 + n2)
  . /- (m1 + n1).MR1 (m1 + n2) -/
    apply NatTerm.R1.keep_cong
    . apply NatTerm.R1.PlusCong2
    . apply r2
  . /- (m1 + n2).MR1 (m2 + n2) -/
    apply NatTerm.R1.keep_cong (fun x => x + n2)
    . intros a b H
      apply NatTerm.R1.PlusCong1 H
    . apply r1


theorem NatTerm.MR1.PlusCong1 {m n1 n2: NatTerm}
  (r: n1.MR1 n2): (m + n1).MR1 (m + n2) := by
    apply NatTerm.MR1.PlusCong
    . apply NatTerm.MR1.refl
    . exact r


theorem NatTerm.MR1.PlusCong2 {m1 m2 n: NatTerm}
  (r: m1.MR1 m2): (m1 + n).MR1 (m2 + n) := by
    apply NatTerm.MR1.PlusCong
    . exact r
    . apply NatTerm.MR1.refl


theorem NatTerm.MR1.MultCong {m1 m2 n1 n2: NatTerm}
  (r1: m1.MR1 m2) (r2: n1.MR1 n2): (m1 * n1).MR1 (m2 * n2) := by
  apply NatTerm.MR1.trans (b := m1 * n2)
  . /- (m1 * n1).MR1 (m1 * n2) -/
    apply NatTerm.R1.keep_cong
    . apply NatTerm.R1.MultCong2
    . apply r2
  . /- (m1 * n2).MR1 (m2 * n2) -/
    apply NatTerm.R1.keep_cong (fun x => x * n2)
    . intros a b H
      apply NatTerm.R1.MultCong1 H
    . apply r1


theorem NatTerm.MR1.MultCong1 {m n1 n2: NatTerm}
  (r: n1.MR1 n2): (m * n1).MR1 (m * n2) := by
    apply NatTerm.MR1.MultCong
    . apply NatTerm.MR1.refl
    . exact r

theorem NatTerm.MR1.MultCong2 {m1 m2 n: NatTerm}
  (r: m1.MR1 m2): (m1 * n).MR1 (m2 * n) := by
    apply NatTerm.MR1.MultCong
    . exact r
    . apply NatTerm.MR1.refl


instance R2_sub_MR1: NatTerm.R2 sub_rel NatTerm.MR1 where
  inclusion := by
    intros a b r
    induction r with
    | @Refl x =>
      apply NatTerm.MR1.refl
    | @SCong m n r IHr =>
      apply NatTerm.MR1.SCong IHr
    | @PlusCong m1 m2 n1 n2 r1 r2 IHr1 IHr2 =>
      apply NatTerm.MR1.PlusCong IHr1 IHr2
    | @MultCong m1 m2 n1 n2 r1 r2 IHr1 IHr2 =>
      apply NatTerm.MR1.MultCong IHr1 IHr2
    | @ZPlus n1 n2 r IHr =>
      apply NatTerm.MR1.trans (b := n1)
      . apply NatTerm.R1.inclusion
        apply NatTerm.R1.ZPlus
      . apply IHr
    | @SPlus m1 m2 n1 n2 r1 r2 IHr1 IHr2 =>
      apply NatTerm.MR1.trans (b := (m1 + n1).S)
      . apply NatTerm.R1.inclusion
        apply NatTerm.R1.SPlus
      . apply NatTerm.MR1.SCong
        apply NatTerm.MR1.PlusCong IHr1 IHr2
    | @ZMult n =>
      apply NatTerm.R1.inclusion
      apply NatTerm.R1.ZMult
    | @SMult m1 m2 n1 n2 r1 r2 IHr1 IHr2 =>
      apply NatTerm.MR1.trans (b := (m1 * n1 + n1))
      . /- (m1.S * n1).MR1 (m1 * n1 + n1) -/
        apply NatTerm.R1.inclusion
        apply NatTerm.R1.SMult
      . /- (m1 * n1 + n1).MR1 (m2 * n2 + n2) -/
        apply NatTerm.MR1.PlusCong
        . /- (m1 * n1).MR1 (m2 * n2) -/
          apply NatTerm.MR1.MultCong IHr1 IHr2
        . exact IHr2


instance: KeepCong NatTerm.R2 NatTerm.MR1 where
  keep_cong := by
    intros f HR2 a b HMR1
    induction HMR1 with
    | @inclusion a b r =>
      apply NatTerm.R2.inclusion
      apply HR2
      apply NatTerm.R1.inclusion
      exact r
    | @refl x =>
      apply NatTerm.MR1.refl
    | @trans a b c r1 r2 IHr1 IHr2 =>
      apply NatTerm.MR1.trans
      . apply IHr1
      . apply IHr2


theorem NatTerm.R2.eval1_cong:
  forall {a b: NatTerm}, a.R2 b -> a.eval1.R2 b.eval1 := by
    intros a b H
    apply NatTerm.R2.eval1_left
    apply H.eval1_left


theorem NatTerm.MR1.eval1_cong:
  forall {a b: NatTerm}, a.MR1 b -> a.eval1.MR1 b.eval1 := by
    intros a b H
    apply NatTerm.R2.keep_cong
    . apply NatTerm.R2.eval1_cong
    . apply H


instance NatTerm.R1.semi_confluence: SemiConfluent NatTerm.R1 where
  semi_confl := by
    intros m1 m2 m3 H12 H13
    exists m3.eval1
    apply And.intro
    . /- m2.MR1 m3.eval1 -/
      apply NatTerm.MR1.trans (b := m1.eval1)
      . /- m2.MR1 m1.eval1 -/
        apply NatTerm.R2.inclusion
        apply NatTerm.R2.eval1_left
        apply NatTerm.R1.inclusion
        exact H12
      . /- m1.eval1.MR1 m3.eval1 -/
        apply NatTerm.MR1.eval1_cong
        exact H13
    . /- m3.MR1 m3.eval1 -/
      apply NatTerm.R2.inclusion
      apply NatTerm.R2.eval1


theorem NatTerm.Eq1.ZPlus {n: NatTerm}: (Z + n).Eq1 n := by
  apply NatTerm.R1.inclusion
  apply NatTerm.R1.ZPlus


theorem NatTerm.Eq1.SPlus {m n: NatTerm}: (m.S + n).Eq1 (m + n).S := by
  apply NatTerm.R1.inclusion
  apply NatTerm.R1.SPlus


theorem NatTerm.Eq1.ZMult {n: NatTerm}: (Z * n).Eq1 0 := by
  apply NatTerm.R1.inclusion
  apply NatTerm.R1.ZMult


theorem NatTerm.Eq1.SMult {m n: NatTerm}: (m.S * n).Eq1 (m * n + n) := by
  apply NatTerm.R1.inclusion
  apply NatTerm.R1.SMult


theorem NatTerm.Eq1.SCong {m n: NatTerm} (r: m.Eq1 n) : m.S.Eq1 n.S := by
  apply NatTerm.R1.keep_cong NatTerm.S
  . apply NatTerm.R1.SCong
  . apply r


theorem NatTerm.Eq1.PlusCong {m1 m2 n1 n2: NatTerm}
  (r1: m1.Eq1 m2) (r2: n1.Eq1 n2): (m1 + n1).Eq1 (m2 + n2) := by
  apply NatTerm.Eq1.trans (b := m1 + n2)
  . /- (m1 + n1).MR1 (m1 + n2) -/
    apply NatTerm.R1.keep_cong
    . apply NatTerm.R1.PlusCong2
    . apply r2
  . /- (m1 + n2).MR1 (m2 + n2) -/
    apply NatTerm.R1.keep_cong (fun x => x + n2)
    . intros a b H
      apply NatTerm.R1.PlusCong1 H
    . apply r1


theorem NatTerm.Eq1.MultCong {m1 m2 n1 n2: NatTerm}
  (r1: m1.Eq1 m2) (r2: n1.Eq1 n2): (m1 * n1).Eq1 (m2 * n2) := by
  apply NatTerm.Eq1.trans (b := m1 * n2)
  . /- (m1 * n1).MR1 (m1 * n2) -/
    apply NatTerm.R1.keep_cong
    . apply NatTerm.R1.MultCong2
    . apply r2
  . /- (m1 * n2).MR1 (m2 * n2) -/
    apply NatTerm.R1.keep_cong (fun x => x * n2)
    . intros a b H
      apply NatTerm.R1.MultCong1 H
    . apply r1


instance: KeepCong NatTerm.MR1 NatTerm.Eq1 where
  keep_cong := by
    intros f HC a b H
    induction H with
    | @inclusion a b r =>
      apply NatTerm.MR1.inclusion
      apply HC
      apply NatTerm.R1.inclusion
      exact r
    | @refl x =>
      apply NatTerm.Eq1.refl
    | @trans a b c Hab Hac IHab IHac =>
      apply IHab.trans IHac
    | @symm a b Hab IHab =>
      apply NatTerm.Eq1.symm
      exact IHab


theorem NatTerm.Eq1.eval1_cong {m n: NatTerm}:
  m.Eq1 n -> m.eval1.Eq1 n.eval1 := by
    intros H
    apply NatTerm.MR1.keep_cong
    . apply NatTerm.MR1.eval1_cong
    . apply H
