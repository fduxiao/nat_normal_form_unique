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


inductive TermReduce: NatTerm -> NatTerm -> Prop where
  | ZPlus {n: NatTerm}: TermReduce (0 + n) n
  | SPlus {m n}: TermReduce (m.S + n) (m + n).S
  | ZMult {n}: TermReduce (0 * n) 0
  | SMult {m n}: TermReduce (m.S * n) ((m * n) + n)
  -- for congruence
  | SCong {m n}: TermReduce m n -> TermReduce m.S n.S
  | PlusCong1 {m1 m2 n}: TermReduce m1 m2 -> TermReduce (m1 + n) (m2 + n)
  | PlusCong2 {m n1 n2}: TermReduce n1 n2 -> TermReduce (m + n1) (m + n2)
  | MultCong1 {m1 m2 n}: TermReduce m1 m2 -> TermReduce (m1 * n) (m2 * n)
  | MultCong2 {m n1 n2}: TermReduce n1 n2 -> TermReduce (m * n1) (m * n2)


abbrev NatTerm.R1 := TermReduce


inductive TermReduce2: NatTerm -> NatTerm -> Prop where
  | Refl {x}: TermReduce2 x x
  -- congruence
  | SCong {m n}: TermReduce2 m n -> TermReduce2 m.S n.S
  | PlusCong {m1 m2 n1 n2}: TermReduce2 m1 m2 -> TermReduce2 n1 n2 -> TermReduce2 (m1 + n1) (m2 + n2)
  | MultCong {m1 m2 n1 n2}: TermReduce2 m1 m2 -> TermReduce2 n1 n2 -> TermReduce2 (m1 * n1) (m2 * n2)
  -- computation
  | ZPlus {n1 n2}: TermReduce2 n1 n2 -> TermReduce2 (0 + n1) n2
  | SPlus {m1 m2 n1 n2}: TermReduce2 m1 m2 -> TermReduce2 n1 n2 -> TermReduce2 (m1.S + n1) (m2 + n2).S
  | ZMult {n}: TermReduce2 (0 * n) .Z
  | SMult {m1 m2 n1 n2}: TermReduce2 m1 m2 -> TermReduce2 n1 n2 -> TermReduce2 (m1.S * n1) (m2 * n2 + n2)


abbrev NatTerm.R2 := TermReduce2

theorem R2_imp_R1: forall {m n}, NatTerm.R1 m n -> NatTerm.R2 m n := by
  intros m n r1
  induction r1 with
  | ZPlus =>
    apply TermReduce2.ZPlus .Refl
  | @SPlus m n =>
    apply @TermReduce2.SPlus m m n n .Refl .Refl
  | ZMult =>
    apply TermReduce2.ZMult
  | @SMult m n =>
    apply @TermReduce2.SMult m m n n .Refl .Refl
  | SCong _ IH =>
    apply TermReduce2.SCong IH
  | @PlusCong1 m1 m2 n r IH =>
    apply @TermReduce2.PlusCong m1 m2 n n IH .Refl
  | @PlusCong2 m n1 n2 r IH =>
    apply @TermReduce2.PlusCong m m n1 n2 .Refl IH
  | @MultCong1 m1 m2 n r IH =>
    apply @TermReduce2.MultCong m1 m2 n n IH .Refl
  | @MultCong2 m n1 n2 r IH =>
    apply @TermReduce2.MultCong m m n1 n2 .Refl IH


theorem R2_S_inverse: forall {m n: NatTerm},
  m.S.R2 n.S -> m.R2 n := by
  intros m n H
  cases H
  case Refl =>
    apply TermReduce2.Refl
  case SCong H =>
    apply H


theorem R2_eval1: forall (m: NatTerm), m.R2 m.eval1 := by
  intros m
  induction m with
  | Z =>
    unfold NatTerm.eval1
    apply TermReduce2.Refl
  | S n IHn =>
    unfold NatTerm.eval1
    apply TermReduce2.SCong IHn
  | Plus m n IHm IHn =>
    unfold NatTerm.eval1
    cases m
    case Z =>
      simp
      apply TermReduce2.ZPlus IHn
    case S m' =>
      simp
      unfold NatTerm.eval1 at IHm
      have H2 := R2_S_inverse IHm
      apply TermReduce2.SPlus H2 IHn
    case Plus m1 m2 =>
      simp
      apply TermReduce2.PlusCong IHm IHn
    case Mult m1 m2 =>
      simp
      apply TermReduce2.PlusCong IHm IHn
  | Mult m n IHm IHn =>
    unfold NatTerm.eval1
    cases m
    case Z =>
      simp
      apply TermReduce2.ZMult
    case S m' =>
      simp
      unfold NatTerm.eval1 at IHm
      have H2 := R2_S_inverse IHm
      apply TermReduce2.SMult H2 IHn
    case Plus m1 m2 =>
      simp
      apply TermReduce2.MultCong IHm IHn
    case Mult m1 m2 =>
      simp
      apply TermReduce2.MultCong IHm IHn


theorem R2_mn_R2_nm_eval1: forall (m n: NatTerm), m.R2 n -> n.R2 m.eval1 := by
  intros m n r
  induction r with
  | Refl => apply R2_eval1
  | SCong r' IHr' =>
    unfold NatTerm.eval1
    apply TermReduce2.SCong IHr'
  | @PlusCong m1 m2 n1 n2 r1 r2 IHr1 IHr2 =>
    cases m1
    case Z =>
      cases r1
      unfold NatTerm.eval1; simp
      apply TermReduce2.ZPlus IHr2
    case S m1' =>
      cases r1
      case Refl =>
        unfold NatTerm.eval1; simp
        unfold NatTerm.eval1 at IHr1
        have IHr1 := R2_S_inverse IHr1
        apply TermReduce2.SPlus IHr1 IHr2
      case SCong t H =>
        unfold NatTerm.eval1; simp
        unfold NatTerm.eval1 at IHr1
        have IHr1 := R2_S_inverse IHr1
        apply TermReduce2.SPlus IHr1 IHr2
    case Plus t1 t2 =>
      unfold NatTerm.eval1; simp
      apply TermReduce2.PlusCong IHr1 IHr2
    case Mult t1 t2 =>
      unfold NatTerm.eval1; simp
      cases r1 with
      | _ =>
        apply TermReduce2.PlusCong IHr1 IHr2
  | @MultCong m1 m2 n1 n2 r1 r2 IHr1 IHr2 =>
    cases m1
    case Z =>
      cases r1
      unfold NatTerm.eval1; simp
      apply TermReduce2.ZMult
    case S m1' =>
      cases r1
      case Refl =>
        unfold NatTerm.eval1; simp
        unfold NatTerm.eval1 at IHr1
        have IHr1 := R2_S_inverse IHr1
        apply TermReduce2.SMult IHr1 IHr2
      case SCong t H =>
        unfold NatTerm.eval1; simp
        unfold NatTerm.eval1 at IHr1
        have IHr1 := R2_S_inverse IHr1
        apply TermReduce2.SMult IHr1 IHr2
    case Plus t1 t2 =>
      unfold NatTerm.eval1; simp
      apply TermReduce2.MultCong IHr1 IHr2
    case Mult t1 t2 =>
      unfold NatTerm.eval1; simp
      cases r1 with
      | _ =>
        apply TermReduce2.MultCong IHr1 IHr2
  | @ZPlus n1 n2 r IHr =>
    unfold NatTerm.eval1; simp
    apply IHr
  | @SPlus m1 m2 n1 n2 r1 r2 IHr1 IHr2 =>
    unfold NatTerm.eval1; simp
    apply TermReduce2.SCong
    apply TermReduce2.PlusCong IHr1 IHr2
  | @ZMult t =>
    unfold NatTerm.eval1; simp
    apply TermReduce2.Refl
  | @SMult m1 m2 n1 n2 r1 r2 IHr1 IHr2 =>
    unfold NatTerm.eval1; simp
    apply TermReduce2.PlusCong
    . apply TermReduce2.MultCong IHr1 IHr2
    . apply IHr2
