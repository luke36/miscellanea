Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import FunctionalExtensionality.
Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import compcert.lib.Integers.
Require Import PV.InductiveType.
Require Import PV.RecurProp.
Require Import PV.Syntax.
Require Import PV.DenotationalSemantics.
Require Import PV.RelsAsDenotations.
Require Import PV.FixedPoint.
Require Import PV.PracticalDenotations.
Local Open Scope string.
Local Open Scope Z.
Local Open Scope sets.

Module Lang_SimpleProc.

Definition proc_name: Type := string.

Inductive expr_int : Type :=
  | EConst (n: Z): expr_int
  | EProcAddr (p: proc_name): expr_int
  | EVar (x: var_name): expr_int
  | EAdd (e1 e2: expr_int): expr_int
  | ESub (e1 e2: expr_int): expr_int
  | EMul (e1 e2: expr_int): expr_int.

Inductive expr_bool: Type :=
  | ETrue: expr_bool
  | EFalse: expr_bool
  | ELt (e1 e2: expr_int): expr_bool
  | EAnd (e1 e2: expr_bool): expr_bool
  | ENot (e: expr_bool): expr_bool.

Inductive com : Type :=
  | CSkip: com
  | CAsgn (x: var_name) (e: expr_int): com
  | CSeq (c1 c2: com): com
  | CIf (e: expr_bool) (c1 c2: com): com
  | CWhile (e: expr_bool) (c: com): com
  | CProcCall (e: expr_int): com.

Record proc: Type := {
  name_of_proc: proc_name;
  body_of_proc: com;
}.

Definition prog := list proc.

(** 在Coq中，可以利用_[Notation]_使得这些表达式和程序语句更加易读。*)

Definition EVar': string -> expr_int := EVar.
Coercion EConst: Z >-> expr_int.
Coercion EVar: var_name >-> expr_int.
Coercion EVar': string >-> expr_int.
Notation "[[ e ]]" := e
  (at level 0, e custom prog_lang_entry at level 99).
Notation "( x )" := x
  (in custom prog_lang_entry, x custom prog_lang_entry at level 99).
Notation "x" := x
  (in custom prog_lang_entry at level 0, x constr at level 0).
Notation "& x" := (EProcAddr x)
  (in custom prog_lang_entry at level 0, x constr at level 1).
Notation "f x" := (f x)
  (in custom prog_lang_entry at level 1, only parsing,
   f custom prog_lang_entry,
   x custom prog_lang_entry at level 0).
Notation "x * y" := (EMul x y)
  (in custom prog_lang_entry at level 11, left associativity).
Notation "x + y" := (EAdd x y)
  (in custom prog_lang_entry at level 12, left associativity).
Notation "x - y" := (ESub x y)
  (in custom prog_lang_entry at level 12, left associativity).
Notation "x < y" := (ELt x y)
  (in custom prog_lang_entry at level 13, no associativity).
Notation "x && y" := (EAnd x y)
  (in custom prog_lang_entry at level 14, left associativity).
Notation "! x" := (ENot x)
  (in custom prog_lang_entry at level 10).
Notation "x = e" := (CAsgn x e)
  (in custom prog_lang_entry at level 18, no associativity).
Notation "x ()" := (CProcCall x)
  (in custom prog_lang_entry at level 18, no associativity).
Notation "c1 ; c2" := (CSeq c1 c2)
  (in custom prog_lang_entry at level 20, right associativity).
Notation "'skip'" := (CSkip)
  (in custom prog_lang_entry at level 10).
Notation "'if' e 'then' '{' c1 '}' 'else' '{' c2 '}'" := (CIf e c1 c2)
  (in custom prog_lang_entry at level 19,
   e custom prog_lang_entry at level 5,
   c1 custom prog_lang_entry at level 99,
   c2 custom prog_lang_entry at level 99,
   format  "'if'  e  'then'  '{'  c1  '}'  'else'  '{'  c2  '}'").
Notation "'while' e 'do' '{' c1 '}'" := (CWhile e c1)
  (in custom prog_lang_entry at level 19,
   e custom prog_lang_entry at level 5,
   c1 custom prog_lang_entry at level 99).

(** 使用_[Notation]_的效果如下：*)

Check [[1 + "x"]].
Check [["x" * ("a" + "b" + 1)]].
Check [[1 + "x" < "x"]].
Check [["x" < 0 && 0 < "y"]].
Check [["x" = "x" + 1]].
Check [[while (0 < "x") do { "x" = "x" - 1}]].
Check [[& "f"]].
Check [[& "f" ()]].


End Lang_SimpleProc.

Module DntSem_SimpleProc.

Import Lang_SimpleProc
       KleeneFix KTFix Sets_CPO Sets_CL.

Record state: Type := {
  env: var_name -> Z;
  mem: Z -> proc_name;
}.

Definition add_sem (D1 D2: state -> Z -> Prop) (s: state): Z -> Prop :=
  fun n => exists n1 n2, n = n1 + n2 /\ D1 s n1 /\ D2 s n2.

Definition sub_sem (D1 D2: state -> Z -> Prop) (s: state): Z -> Prop :=
  fun n => exists n1 n2, n = n1 - n2 /\ D1 s n1 /\ D2 s n2.

Definition mul_sem (D1 D2: state -> Z -> Prop) (s: state): Z -> Prop :=
  fun n => exists n1 n2, n = n1 * n2 /\ D1 s n1 /\ D2 s n2.

Definition const_sem (n: Z): state -> Z -> Prop := 
  fun s n' => n = n'.

Definition var_sem (X: var_name): state -> Z -> Prop :=
  fun s n' => s.(env) X = n'.

Definition proc_addr_sem (p: proc_name): state -> Z -> Prop :=
  fun s n => s.(mem) n = p.

Fixpoint eval_expr_int (e: expr_int): state -> Z -> Prop :=
  match e with
  | EConst n =>
      const_sem n
  | EProcAddr p =>
      proc_addr_sem p
  | EVar X =>
      var_sem X
  | EAdd e1 e2 =>
      add_sem (eval_expr_int e1) (eval_expr_int e2)
  | ESub e1 e2 =>
      sub_sem (eval_expr_int e1) (eval_expr_int e2)
  | EMul e1 e2 =>
      mul_sem (eval_expr_int e1) (eval_expr_int e2)
  end.

(** 下面我们同样引入_[⟦ e ⟧]_这个Notation，并且_[unfold_sem]_这个证明指令用于展开
    语义相关的定义。*)

Notation "⟦ e ⟧" := (eval_expr_int e)
  (at level 0, only printing, e custom prog_lang_entry at level 99).

Ltac get_prog_syntax x :=
  match type of x with
  | expr_int => constr:(x)
  | Z => constr:(EConst x)
  | string => constr:(EVar' x)
  | var_name => constr:(EVar x)
  end.

Ltac any_eval' x :=
  match goal with
  | |- _ -> Z => exact (eval_expr_int x)
  | _         => 
    match type of x with
    | expr_int => exact (eval_expr_int x)
    end
  end.

Ltac any_eval x :=
  let x' := get_prog_syntax x in
  any_eval' x'.

Notation "⟦ x ⟧" := (ltac:(any_eval x))
  (at level 0, only parsing, x custom prog_lang_entry at level 99).

Ltac unfold_expr_int_sem :=
  cbv [add_sem sub_sem mul_sem const_sem var_sem proc_addr_sem].

Ltac unfold_expr_int_sem_in_hyp H :=
  cbv [add_sem sub_sem mul_sem const_sem var_sem proc_addr_sem] in H.

Ltac ___unfold_sem :=
  simpl eval_expr_int; unfold_expr_int_sem.

Ltac ___unfold_sem_in_hyp H :=
  simpl eval_expr_int in H; unfold_expr_int_sem_in_hyp H.

Tactic Notation "unfold_sem" :=
  ___unfold_sem.

Tactic Notation "unfold_sem" "in" hyp(H) :=
  ___unfold_sem_in_hyp H.

Definition true_sem: state -> bool -> Prop :=
  fun s b => b = true.

Definition false_sem: state -> bool -> Prop :=
  fun s b => b = false.

Definition lt_sem (D1 D2: state -> Z -> Prop):
  state -> bool -> Prop :=
  fun s b =>
    if b then exists n1 n2, D1 s n1 /\ D2 s n2 /\ n1 < n2
    else exists n1 n2, D1 s n1 /\ D2 s n2 /\ n1 >= n2.

Definition and_sem (D1 D2: state -> bool -> Prop):
  state -> bool -> Prop :=
  fun s b => exists b1 b2, b = andb b1 b2 /\ D1 s b1 /\ D2 s b2.

Definition not_sem (D: state -> bool -> Prop):
  state -> bool -> Prop :=
  fun s b => exists b', b = negb b' /\ D s b'.

Fixpoint eval_expr_bool (e: expr_bool): state -> bool -> Prop :=
  match e with
  | ETrue =>
      true_sem
  | EFalse =>
      false_sem
  | ELt e1 e2 =>
      lt_sem (eval_expr_int e1) (eval_expr_int e2)
  | EAnd e1 e2 =>
      and_sem (eval_expr_bool e1) (eval_expr_bool e2)
  | ENot e1 =>
      not_sem (eval_expr_bool e1)
  end.

Notation "⟦ e ⟧" := (eval_expr_bool e)
  (at level 0, only printing, e custom prog_lang_entry at level 99).

Ltac get_prog_syntax x ::=
  match type of x with
  | expr_int => constr:(x)
  | Z => constr:(EConst x)
  | string => constr:(EVar' x)
  | var_name => constr:(EVar x)
  | expr_bool => constr:(x)
  end.

Ltac any_eval' x ::=
  match goal with
  | |- _ -> Z    => exact (eval_expr_int x)
  | |- _ -> bool => exact (eval_expr_bool x)
  | _            =>
    match type of x with
    | expr_int  => exact (eval_expr_int x)
    | expr_bool => exact (eval_expr_bool x)
    end
  end.

Ltac unfold_expr_bool_sem :=
  cbv [true_sem false_sem lt_sem and_sem not_sem].

Ltac unfold_expr_bool_sem_in_hyp H :=
  cbv [true_sem false_sem lt_sem and_sem not_sem] in H.

Ltac ___unfold_sem ::=
  simpl eval_expr_bool; simpl eval_expr_int;
  unfold_expr_bool_sem; unfold_expr_int_sem.

Ltac ___unfold_sem_in_hyp H ::=
  simpl eval_expr_bool in H; simpl eval_expr_int in H;
  unfold_expr_bool_sem_in_hyp H; unfold_expr_int_sem_in_hyp H.

(* Notation "H '.(asgn_sem_asgn_var)'" := *)
(*   (asgn_sem_asgn_var _ _ _ _ H) *)
(*   (at level 1). *)

(* Notation "H '.(asgn_sem_other_var)'" := *)
(*   (asgn_sem_other_var _ _ _ _ H) *)
(*   (at level 1). *)

Section eval_com.

Variable chi: proc_name -> state -> state -> Prop.

Definition skip_sem: state -> state -> Prop :=
  Rels.id.

Definition seq_sem (D1 D2: state -> state -> Prop):
  state -> state -> Prop :=
  D1 ∘ D2.

Definition test_true
             (D: state -> bool -> Prop):
  state -> state -> Prop :=
  Rels.test (fun s => D s true).

Definition test_false
             (D: state -> bool -> Prop):
  state -> state -> Prop :=
  Rels.test (fun s => D s false).

Definition asgn_sem
         (X: var_name)
         (D: state -> Z -> Prop)
         (s1 s2: state): Prop :=
  exists n, D s1 n /\
       s2.(env) X = n /\
       (forall Y, X <> Y -> s2.(env) Y = s1.(env) Y) /\
       s2.(mem) = s1.(mem).

Definition if_sem
             (D0: state -> bool -> Prop)
             (D1 D2: state -> state -> Prop):
  state -> state -> Prop :=
  (test_true D0 ∘ D1) ∪ (test_false D0 ∘ D2).

Definition while_sem
             (D0: state -> bool -> Prop)
             (D: state -> state -> Prop):
  state -> state -> Prop :=
  Kleene_LFix (fun X => (test_true(D0) ∘ D ∘ X) ∪ test_false(D0)).

Definition proc_call_sem (D: state -> Z -> Prop): state -> state -> Prop :=
  fun s1 s2 => exists x f, D s1 x /\ s1.(mem) x = f /\ chi f s1 s2.

Fixpoint eval_com (c: com): state -> state -> Prop :=
  match c with
  | CSkip =>
      skip_sem
  | CAsgn X e =>
      asgn_sem X (eval_expr_int e)
  | CSeq c1 c2 =>
      seq_sem (eval_com c1) (eval_com c2)
  | CIf e c1 c2 =>
      if_sem (eval_expr_bool e) (eval_com c1) (eval_com c2)
  | CWhile e c1 =>
      while_sem (eval_expr_bool e) (eval_com c1)
  | CProcCall e =>
      proc_call_sem (eval_expr_int e)
  end.

Notation "⟦ c ⟧" := (eval_com c)
  (at level 0, only printing, c custom prog_lang_entry at level 99).

Ltac get_prog_syntax x ::=
  match type of x with
  | expr_int => constr:(x)
  | Z => constr:(EConst x)
  | string => constr:(EVar' x)
  | var_name => constr:(EVar x)
  | expr_bool => constr:(x)
  | com => constr:(x)
  end.

Ltac any_eval' x ::=
  match goal with
  | |- _ -> Z    => exact (eval_expr_int x)
  | |- _ -> bool => exact (eval_expr_bool x)
  | |- _ -> Prop => exact (eval_com x)
  | _            =>
    match type of x with
    | expr_int  => exact (eval_expr_int x)
    | expr_bool => exact (eval_expr_bool x)
    | com       => exact (eval_com x)
    end
  end.

Ltac unfold_com_sem :=
  cbv [seq_sem if_sem while_sem skip_sem proc_call_sem].

Ltac unfold_com_sem_in_hyp H :=
  cbv [seq_sem if_sem while_sem skip_sem proc_call_sem] in H.

Ltac ___unfold_sem ::=
  simpl eval_com; simpl eval_expr_bool; simpl eval_expr_int;
  unfold_com_sem; unfold_expr_bool_sem; unfold_expr_int_sem.

Ltac ___unfold_sem_in_hyp H ::=
  simpl eval_com in H;
  simpl eval_expr_bool in H;
  simpl eval_expr_int in H;
  unfold_com_sem_in_hyp H;
  unfold_expr_bool_sem_in_hyp H;
  unfold_expr_int_sem_in_hyp H.

Ltac unfold_sem1_tac T :=
  match T with
  | context G [eval_com (CIf ?e ?c1 ?c2)] =>
      let if_sem' := eval cbv [if_sem] in if_sem in
      let ret := eval cbv beta iota in (if_sem' ⟦ e ⟧ ⟦ c1 ⟧ ⟦ c2 ⟧) in
      let T' := context G [ret] in
      T'
  | context G [eval_com (CSeq ?c1 ?c2)] =>
      let seq_sem' := eval cbv [seq_sem] in seq_sem in
      let ret := eval cbv beta iota in (seq_sem' ⟦ c1 ⟧ ⟦ c2 ⟧) in
      let T' := context G [ret] in
      T'
  end.

Ltac unfold_sem1_in_hypo_tac H :=
  match type of H with
  | ?T => let T' := unfold_sem1_tac T in
          change T' in H
  end.

Tactic Notation "unfold_sem1" "in" constr(H) :=
  unfold_sem1_in_hypo_tac H.

End eval_com.

Section eval_proc.

Variable chi: proc_name -> state -> state -> Prop.

Definition test_proc_name (p1 p2: proc_name):
  state -> state -> Prop :=
  fun s1 s2 => s1 = s2 /\ p1 = p2.

Definition eval_proc (P: proc): proc_name -> state -> state -> Prop :=
  fun p => test_proc_name p P.(name_of_proc) ∘ eval_com chi P.(body_of_proc).

Fixpoint eval_prog (Ps: prog): proc_name -> state -> state -> Prop :=
  match Ps with
  | nil => Sets.empty
  | cons P Ps' => eval_proc P ∪ eval_prog Ps'
  end.

End eval_proc.

Definition prog_sem (Ps: prog): proc_name -> state -> state -> Prop :=
  Kleene_LFix (fun chi => eval_prog chi Ps).

End DntSem_SimpleProc.

Module HoareSimpleProc.

Import Lang_SimpleProc DntSem_SimpleProc
       KleeneFix KTFix Sets_CPO Sets_CL.

Definition pure_assn := state -> Prop.

Inductive assertion :=
| MkAssn: pure_assn -> list (expr_int * spec) -> assertion
with spec :=
| MkSpec: forall (A: Type), (A -> assertion) -> (A -> assertion) -> spec.

Definition proc_assn := list (expr_int * spec).

Definition prog_spec := proc_name -> spec -> Prop.

Definition eval_proc_assn_one (e: expr_int) (X: spec) (D: prog_spec): state -> Prop :=
  fun s => (forall x, ⟦ e ⟧ s x -> D (s.(mem) x) X).

Fixpoint eval_proc_assn (F: proc_assn) (D: prog_spec): state -> Prop :=
  match F with
  | nil => Sets.full
  | cons (e, X) F' =>
      fun s => eval_proc_assn_one e X D s /\ eval_proc_assn F' D s
  end.

Definition eval_assn (A: assertion) (D: prog_spec): state -> Prop :=
  match A with
  | MkAssn P F =>
      fun s => P s /\ eval_proc_assn F D s
  end.

Definition eval_spec (S: spec) (D: prog_spec): state -> state -> Prop :=
  match S with
  | MkSpec A P Q =>
      fun s1 s2 => forall a, eval_assn (P a) D s1 -> eval_assn (Q a) D s2
  end.

Definition derives D (P Q: assertion) :=
  forall s, eval_assn P D s -> eval_assn Q D s.

Definition logic_equiv D (P Q: assertion) :=
  derives D P Q /\ derives D Q P.

Definition satisfies
  (chi: proc_name -> state -> state -> Prop)
  (D: prog_spec): Prop :=
  forall p X, D p X -> chi p ⊆ eval_spec X D.

Inductive HoareTriple: Type :=
| BuildHoareTriple: assertion -> com -> assertion -> HoareTriple.

Definition valid (D: prog_spec): HoareTriple -> Prop :=
  fun ht =>
  match ht with
  | BuildHoareTriple P c Q =>
      forall s1 s2 chi,
        eval_assn P D s1 -> satisfies chi D ->
        (s1, s2) ∈ eval_com chi c ->
        eval_assn Q D s2
  end.

Lemma hoare_discard_sound:
  forall D P eX F, derives D (MkAssn P (cons eX F)) (MkAssn P F).
Proof.
  intros ? ? ? ? ?.
  unfold derives; unfold eval_assn.
  destruct eX as [e X].
  simpl; intros [Hpure Hproc].
  tauto.
Qed.

Lemma hoare_proc_subst_proc_sound:
  forall {P: pure_assn} {e1 e2: expr_int} {F} {D: prog_spec} {X},
    (forall s, P s -> ⟦ e2 ⟧ s ⊆ ⟦ e1 ⟧ s) ->
    derives D
      (MkAssn P (cons (e1, X) F))
      (MkAssn P (cons (e2, X) F)).
Proof.
  unfold derives; simpl.
  intros P E1 E2 F D X Hsafe s H.
  split; [tauto|split; [|tauto] ].
  intros ? He.
  destruct H as [Hpure [Hf _] ].
  apply Hf.
  apply Hsafe; assumption.
Qed.

Lemma hoare_permutation_sound:
  forall D P E F, Permutation E F ->
    logic_equiv D (MkAssn P E) (MkAssn P F).
Proof.
  intros ? ? ? ? HP.
  induction HP; split; unfold derives; intros; try tauto.
  - unfold logic_equiv in IHHP; destruct IHHP as [IH _].
    unfold derives in IH.
    specialize (IH s).
    unfold eval_assn in IH.
    simpl in H; simpl.
    destruct x as (e, X).
    split; [tauto|split; [tauto|] ].
    apply IH.
    tauto.
  - unfold logic_equiv in IHHP; destruct IHHP as [_ IH].
    unfold derives in IH.
    specialize (IH s).
    unfold eval_assn in IH.
    simpl in H; simpl.
    destruct x as (e, X).
    split; [tauto|split; [tauto|] ].
    apply IH.
    tauto.
  - simpl in H; simpl.
    destruct x as (e, X); destruct y as (f, Y).
    split; [tauto| split; tauto].
  - simpl in H; simpl.
    destruct x as (e, X); destruct y as (f, Y).
    split; [tauto| split; tauto].
  - destruct IHHP1 as [IH1 _].
    destruct IHHP2 as [IH2 _].
    apply IH2; apply IH1; exact H.
  - destruct IHHP1 as [_ IH1].
    destruct IHHP2 as [_ IH2].
    apply IH1; apply IH2; exact H.
Qed.

Lemma hoare_proc_call_sound_lem:
  forall {P F D s e A X Y},
    eval_assn (MkAssn P F) D s ->
    In (e, MkSpec A X Y) F ->
    (forall x : Z, ⟦ e ⟧ s x -> D (s.(mem) x) (MkSpec A X Y)).
Proof.
  intros P F; generalize dependent P.
  induction F.
  - intros ? ? ? ? ? ? ? He HIn.
    exfalso; exact HIn.
  - intros ? ? ? ? ? ? ? Hs HIn ? He.
    simpl In in HIn; destruct HIn.
    + simpl eval_assn in Hs; destruct a as [e0 X0].
      destruct Hs as [_ [thm _] ].
      inversion H; subst e0; subst X0; clear H.
      apply (thm _ He).
    + eapply IHF.
      * pose proof hoare_discard_sound D P a F.
        unfold derives in H0.
        apply (H0 s); exact Hs.
      * exact H.
      * exact He.
Qed.

Lemma hoare_proc_call_sound:
  forall {D F X P A a X' Y e},
    X = (MkAssn P F) ->
    In (e, (MkSpec A X' Y)) F ->
    derives D X (X' a) ->
    valid D
      (BuildHoareTriple
         X (CProcCall e) (Y a)).
Proof.
  unfold valid.
  intros ? ? ? ? ? ? ? ? ? HX HIn Hderive ? ? ? Hpre Hsat Hnrm.
  subst X.
  destruct Hnrm as [? [f [He [Hf Hchi] ] ] ].
  simpl eval_assn in Hpre; simpl eval_proc_assn in Hpre.
  pose proof hoare_proc_call_sound_lem Hpre HIn as Hproc.
  unfold satisfies in Hsat.
  specialize (Hproc _ He).
  specialize (Hsat _ _ Hproc).
  subst f.
  unfold eval_spec in Hsat; Sets_unfold in Hsat;
    unfold SetsEle.In in Hsat; simpl in Hsat.
  apply (Hsat _ _ Hchi).
  unfold derives in Hderive; apply Hderive; clear Hderive.
  exact Hpre.
Qed.

Lemma hoare_proc_addr_sound:
  forall {P F} {D: prog_spec} {p X}, D p X -> derives D
    (MkAssn P F)
    (MkAssn P (cons (EProcAddr p, X) F)).
Proof.
  unfold derives; unfold eval_assn.
  intros ? ? ? ? ? HX s [Hpure Hproc].
  split; [exact Hpure |].
  unfold eval_proc_assn; split; [|exact Hproc].
  intros ? He; unfold_sem in He.
  rewrite He; exact HX.
Qed.

Definition state_subst (s: state) (x: var_name) (v: Z): state :=
  {| env := fun y =>
             if String.eqb x y
             then v
             else s.(env) y;
     mem := s.(mem); |}.

Fixpoint expr_int_subst
  (e: expr_int) (x: var_name) (v: expr_int): expr_int :=
  match e with
  | EConst _ => e
  | EProcAddr _ => e
  | EVar y => if String.eqb x y then v else e
  | EAdd e1 e2 => EAdd (expr_int_subst e1 x v) (expr_int_subst e2 x v)
  | ESub e1 e2 => ESub (expr_int_subst e1 x v) (expr_int_subst e2 x v)
  | EMul e1 e2 => EMul (expr_int_subst e1 x v) (expr_int_subst e2 x v)
  end.

Fixpoint proc_assn_subst
  (F: proc_assn) (x: var_name) (v: expr_int): proc_assn :=
  match F with
  | nil => nil
  | cons (E, X) F' =>
      cons ((expr_int_subst E x v), X) (proc_assn_subst F' x v)
  end.

Definition pure_assn_subst
  (P: pure_assn) (x: var_name) (v: state -> Z -> Prop): pure_assn :=
  fun s => forall z, v s z -> P (state_subst s x z).

Lemma hoare_asgn_state:
  forall {D x e s1 s2},
    (s1, s2) ∈ eval_com D (CAsgn x e) ->
    s2 = {| env := fun y : var_name => if (x =? y)%string then s2.(env) x else env s1 y;
            mem := s1.(mem) |}.
Proof.
  intros ? ? ? ? ? Hnrm.
  destruct Hnrm as [z [He [Hsame Hdiff] ] ].
  assert (s2.(env) = fun y : var_name => if (x =? y)%string then s2.(env) x else env s1 y).
  { apply functional_extensionality; intros x1.
    destruct (String.eqb_spec x x1).
    + subst x1; tauto.
    + apply Hdiff; assumption. }
  assert (s2.(mem) = s1.(mem)) by tauto.
  destruct s2 as [env2 mem2].
  simpl in H, H0.
  rewrite H, H0; simpl.
  rewrite eqb_refl; reflexivity.
Qed.

Lemma hoare_asgn_backward_pure_sound:
  forall {D P x e s1 s2},
    (s1, s2) ∈ eval_com D (CAsgn x e) ->
    (pure_assn_subst P x (eval_expr_int e)) s1 ->
    P s2.
Proof.
  intros ? ? ? ? ? ? Hnrm Hpre.
  pose proof hoare_asgn_state Hnrm.
  destruct Hnrm as [z [He [Hsame _] ] ].
  unfold pure_assn_subst, state_subst in Hpre.
  specialize (Hpre _ He); clear He.
  rewrite Hsame in H; subst s2.
  assumption.
Qed.

Lemma hoare_expr_int_subst_sound:
  forall e {chi x v s1 s2},
    (s1, s2) ∈ eval_com chi (CAsgn x v) ->
    eval_expr_int e s2 ⊆
    eval_expr_int (expr_int_subst e x v) s1.
Proof.
  intros e chi.
  induction e;
    intros ? ? ? ? Hnrm;
    pose proof Hnrm as Hnrm1;
    simpl in Hnrm; unfold asgn_sem in Hnrm;
    destruct Hnrm as [z [Hv [Hsame [Hdiff Hmem] ] ] ].
  - reflexivity.
  - simpl; unfold proc_addr_sem.
    Sets_unfold; intros n H.
    rewrite <- Hmem. exact H.
  - simpl. destruct (String.eqb_spec x0 x).
    + unfold var_sem.
      Sets_unfold; intros n H.
      simpl in H.
      rewrite <- H; rewrite e in Hsame; rewrite Hsame.
      exact Hv.
    + unfold var_sem.
      Sets_unfold; intros n' H.
      simpl; unfold var_sem.
      simpl in H.
      rewrite <- H.
      symmetry; exact (Hdiff _ n).
  - specialize (IHe1 x v s1 s2 Hnrm1).
    specialize (IHe2 x v s1 s2 Hnrm1).
    simpl; unfold add_sem.
    Sets_unfold; intros n H.
    simpl; simpl in H; destruct H as [n1 [n2 H] ].
    exists n1; exists n2.
    split; [tauto|].
    split; [apply IHe1; tauto|apply IHe2; tauto].
  - specialize (IHe1 x v s1 s2 Hnrm1).
    specialize (IHe2 x v s1 s2 Hnrm1).
    simpl; unfold add_sem.
    Sets_unfold; intros n H.
    simpl; simpl in H; destruct H as [n1 [n2 H] ].
    exists n1; exists n2.
    split; [tauto|].
    split; [apply IHe1; tauto|apply IHe2; tauto].
  - specialize (IHe1 x v s1 s2 Hnrm1).
    specialize (IHe2 x v s1 s2 Hnrm1).
    simpl; unfold add_sem.
    Sets_unfold; intros n H.
    simpl; simpl in H; destruct H as [n1 [n2 H] ].
    exists n1; exists n2.
    split; [tauto|].
    split; [apply IHe1; tauto|apply IHe2; tauto].
Qed.

Lemma hoare_asgn_backward_proc_sound_lem:
  forall {s1 s2 chi x v e X D},
    (s1, s2) ∈ eval_com chi (CAsgn x v) ->
    eval_proc_assn_one (expr_int_subst e x v) X D s1 ->
    eval_proc_assn_one e X D s2.
Proof.
  intros ? ? ? ? ? ? ? ? Hnrm Hpre.
  pose proof (hoare_expr_int_subst_sound e Hnrm) as Hs.
  unfold eval_proc_assn_one; unfold eval_proc_assn_one in Hpre.
  intros z He.
  destruct Hnrm as [_ [_ [_ [_ Hmem] ] ] ].
  apply Hs in He.
  specialize (Hpre _ He).
  rewrite Hmem; exact Hpre.
Qed.

Lemma hoare_asgn_backward_proc_sound:
  forall {F s1 s2 chi x v D},
    (s1, s2) ∈ eval_com chi (CAsgn x v) ->
    eval_proc_assn (proc_assn_subst F x v) D s1 ->
    eval_proc_assn F D s2.
Proof.
  intro F; induction F;
    intros ? ? ? ? ? ? Hnrm Hpre; [tauto|].
  destruct a as [e X].
  simpl; simpl in Hpre.
  split.
  - apply (hoare_asgn_backward_proc_sound_lem Hnrm).
    tauto.
  - eapply IHF.
    + apply Hnrm.
    + tauto.
Qed.

Lemma hoare_asgn_backward_sound:
  forall D P F x (e: expr_int),
    valid D
      (BuildHoareTriple
         (MkAssn (pure_assn_subst P x ⟦ e ⟧) (proc_assn_subst F x e))
         (CAsgn x e)
         (MkAssn P F)).
Proof.
  intros ? ? ? ? ? ? ? ? Hpre Hsat Hnrm.
  simpl; simpl in Hpre.
  split.
  - apply (hoare_asgn_backward_pure_sound Hnrm).
    tauto.
  - apply (hoare_asgn_backward_proc_sound Hnrm).
    tauto.
Qed.

Lemma hoare_skip_sound:
  forall D P,
    valid D (BuildHoareTriple P CSkip P).
Proof.
  unfold valid.
  unfold eval_com, skip_sem.
  sets_unfold.
  intros ? ? ? ? ? Hpre Hsat H.
  rewrite <- H; assumption.
Qed.

Lemma hoare_seq_sound:
  forall {D} {P Q R: assertion} {c1 c2: com},
    valid D (BuildHoareTriple P c1 Q) ->
    valid D (BuildHoareTriple Q c2 R) ->
    valid D (BuildHoareTriple P (CSeq c1 c2) R).
Proof.
  unfold valid.
  intros ? ? ? ? ? ? H1 H2 ? ? ? Hpre Hsat Hnrm.
  simpl in Hnrm; unfold seq_sem in Hnrm.
  Sets_unfold in Hnrm; destruct Hnrm as [s1' [Hn1 Hn2] ].
  specialize (H1 _ _ _ Hpre Hsat Hn1).
  specialize (H2 _ _ _ H1 Hsat Hn2).
  exact H2.
Qed.

Definition hoare_assert_true (P: assertion) (e: expr_bool): assertion :=
  match P with
  | MkAssn P F =>
      MkAssn (fun s => ⟦ e ⟧ s true /\ P s) F
  end.

Definition hoare_assert_false (P: assertion) (e: expr_bool): assertion :=
  match P with
  | MkAssn P F =>
      MkAssn (fun s => ⟦ e ⟧ s false /\ P s) F
  end.

Lemma hoare_if_sound:
  forall {D} {P Q: assertion} {e: expr_bool} {c1 c2: com},
    valid D (BuildHoareTriple (hoare_assert_true P e) c1 Q) ->
    valid D (BuildHoareTriple (hoare_assert_false P e) c2 Q) ->
    valid D (BuildHoareTriple P (CIf e c1 c2) Q).
Proof.
  unfold valid.
  intros ? ? ? ? ? ? Ht Hf s1 s2 ? Hpre Hsat Hnrm.
  destruct P as [P F].
  simpl in Ht, Hf.
  simpl in Hnrm; unfold if_sem in Hnrm.
  simpl in Hpre.
  Sets_unfold in Hnrm; destruct Hnrm.
  - destruct H as [s1' [He Htn] ]; simpl in He.
    simpl in He; unfold test_true in He; simpl in He.
    destruct He as [He Heq]; Sets_unfold in Heq.
    subst s1'.
    apply (Ht s1 s2 chi).
    split; try tauto.
    exact Hsat.
    exact Htn.
  - destruct H as [s1' [He Hfn] ]; simpl in He.
    simpl in He; unfold test_false in He; simpl in He.
    destruct He as [He Heq]; Sets_unfold in Heq.
    subst s1'.
    apply (Hf s1 s2 chi).
    split; try tauto.
    exact Hsat.
    exact Hfn.
Qed.

Lemma hoare_while_sound:
  forall {D} {P: assertion} {e: expr_bool} {c: com},
    valid D (BuildHoareTriple (hoare_assert_true P e) c P) ->
    valid D (BuildHoareTriple P (CWhile e c) (hoare_assert_false P e)).
Proof.
  unfold valid.
  intros ? ? ? ? Hinv ? ? ? Hpre Hsat Hnrm.
  destruct P as [P F].
  simpl in Hinv.
  simpl in Hnrm; unfold while_sem in Hnrm.
  simpl in Hpre.
  unfold
    KleeneFix.Kleene_LFix,
    KleeneFix.omega_lub,
    Sets_CPO.oLub_sets in Hnrm;
    Sets_unfold in Hnrm.
  destruct Hnrm as [i Hn].
  revert s1 s2 Hpre Hn; induction i.
  - intros ? ? Hpre Hnrm.
    simpl in Hnrm.
    unfold KleeneFix.bot, Sets_CPO.Bot_sets in Hnrm.
    exfalso; exact Hnrm.
  - intros ? ? Hpre Hnrm.
    simpl in Hnrm. destruct Hnrm.
    + destruct H as [s' [Ht [s'' [Hn H] ] ] ].
      destruct Ht as [Ht Heq]; Sets_unfold in Heq; simpl in Ht.
      subst s'.
      apply (IHi s'' s2).
      * apply (Hinv s1 _ chi); tauto.
      * exact H.
    + simpl.
      unfold test_false in H; Sets_unfold in H; destruct H as [Hf Heq].
      subst s1.
      tauto.
Qed.

Inductive provable (D: prog_spec): HoareTriple -> Prop :=
| hoare_skip:
  forall P, provable D (BuildHoareTriple P CSkip P)
| hoare_seq:
  forall {P Q R: assertion} {c1 c2: com},
    provable D (BuildHoareTriple P c1 Q) ->
    provable D (BuildHoareTriple Q c2 R) ->
    provable D (BuildHoareTriple P (CSeq c1 c2) R)
| hoare_if:
  forall {P Q: assertion} {e: expr_bool} {c1 c2: com},
    provable D (BuildHoareTriple (hoare_assert_true P e) c1 Q) ->
    provable D (BuildHoareTriple (hoare_assert_false P e) c2 Q) ->
    provable D (BuildHoareTriple P (CIf e c1 c2) Q)
| hoare_while:
  forall {P: assertion} {e: expr_bool} {c: com},
    provable D (BuildHoareTriple (hoare_assert_true P e) c P) ->
    provable D (BuildHoareTriple P (CWhile e c) (hoare_assert_false P e))
| hoare_asgn_backward:
  forall P F x (e: expr_int),
    provable D
      (BuildHoareTriple
         (MkAssn (pure_assn_subst P x ⟦ e ⟧) (proc_assn_subst F x e))
         (CAsgn x e)
         (MkAssn P F))
| hoare_proc_call:
  forall {F X P A a X' Y e},
    X = (MkAssn P F) ->
    In (e, (MkSpec A X' Y)) F ->
    derives D X (X' a) ->
    provable D
      (BuildHoareTriple
         X (CProcCall e) (Y a))
| hoare_conseq:
  forall {P P' Q Q' c},
    provable D (BuildHoareTriple P c Q) ->
    derives D P' P ->
    derives D Q Q' ->
    provable D (BuildHoareTriple P' c Q').

Theorem hoare_com_sound: forall D ht,
  provable D ht -> valid D ht.
Proof.
  intros D ht Hp.
  induction Hp.
  - apply hoare_skip_sound.
  - apply (hoare_seq_sound IHHp1 IHHp2).
  - apply (hoare_if_sound IHHp1 IHHp2).
  - apply (hoare_while_sound IHHp).
  - apply hoare_asgn_backward_sound.
  - apply (hoare_proc_call_sound H H0 H1).
  - unfold valid; unfold valid in IHHp.
    unfold derives in H, H0.
    intros ? ? ? Hpre Hsat Hnrm.
    specialize (H _ Hpre).
    specialize (H0 s2).
    specialize (IHHp s1 s2 chi H Hsat Hnrm).
    apply H0.
    exact IHHp.
Qed.

Fixpoint prog_provable (D: prog_spec) (P: prog): Prop :=
  match P with
  | nil => Sets.full
  | cons {| name_of_proc := name; body_of_proc := body; |} P' =>
      (forall A P Q, D name (MkSpec A P Q) ->
       forall x, provable D (BuildHoareTriple (P x) body (Q x))) /\ prog_provable D P'
  end.

Lemma eval_prog_sound:
  forall D Ps,
    prog_provable D Ps ->
    forall chi,
      satisfies chi D ->
      satisfies (eval_prog chi Ps) D.
Proof.
  intros ? ? Hp ? Hpre.
  induction Ps.
  - unfold satisfies. simpl.
    intros ? ? _.
    Sets_unfold.
    intros s1 s2 fls.
    simpl in fls.
    exfalso; exact fls.
  - destruct a as [name body].
    simpl eval_prog; simpl prog_provable in Hp.
    unfold satisfies, eval_proc; simpl.
    intros p X H.
    destruct Hp as [Hcom HP].
    specialize (IHPs HP).
    apply Sets_union_included.
    + unfold test_proc_name.
      Sets_unfold.
      intros s1 s2 [s1' [ [Heq Hname] Hbody] ].
      subst s1'; subst p.
      destruct X as [A P Q].
      simpl; intros x Hpr.
      specialize (Hcom _ _ _ H x).
      apply hoare_com_sound in Hcom.
      unfold valid in Hcom.
      specialize (Hcom s1 s2 chi Hpr Hpre Hbody).
      exact Hcom.
    + apply IHPs.
      exact H.
Qed.

Lemma rephrase_satisfy:
  forall chi D, satisfies chi D <->
           chi ⊆ (fun p s1 s2 => forall X, D p X -> eval_spec X D s1 s2).
Proof.
  intros chi D; split; unfold satisfies.
  - intro H.
    Sets_unfold.
    intros p s1 s2 Hn.
    simpl.
    intros X HD.
    specialize (H p X HD).
    apply H; tauto.
  - intros H p X HD.
    Sets_unfold; intros s1 s2 Hn.
    Sets_unfold in H; simpl in H.
    specialize (H p s1 s2 Hn X HD).
    tauto.
Qed.

Theorem hoare_sound_prog:
  forall D Ps, prog_provable D Ps -> satisfies (prog_sem Ps) D.
Proof.
  intros D Ps Hp.
  pose proof (eval_prog_sound D Ps Hp).
  apply <- rephrase_satisfy.
  assert
    (forall chi,
        chi ⊆ (fun p s1 s2 => forall X, D p X -> eval_spec X D s1 s2) ->
        (eval_prog chi Ps) ⊆ (fun p s1 s2 => forall X, D p X -> eval_spec X D s1 s2)).
  { intros chi H0.
    apply rephrase_satisfy.
    apply H.
    apply <- rephrase_satisfy.
    exact H0. }
  clear H; rename H0 into H.
  unfold prog_sem, Kleene_LFix, omega_lub, oLub_sets.
  apply Sets_indexed_union_included.
  intro n; induction n.
  - simpl.
    apply Sets_empty_included.
  - simpl.
    apply H.
    exact IHn.
Qed.

End HoareSimpleProc.

