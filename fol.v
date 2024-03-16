Require Import Logic.Eqdep_dec.
Require Import Arith.Peano_dec.

Axiom exclude_middle : forall P, P \/ ~P.

Inductive vect (T : Type) : nat -> Type :=
  | nil : vect T O
  | cons : forall n, T -> vect T n -> vect T (S n).

Arguments nil {T}.
Arguments cons {T} {n} _ _.

Class Sig := {
  func : Type;
  func_ar : func -> nat;
  rel : Type;
  rel_ar : rel -> nat;
}.

Inductive term (S : Sig) :=
  | var : nat -> term S
  | app (f : func) (args : vect (term S) (func_ar f)).

Arguments var {S}.
Arguments app {S} _ _.

Inductive formula (S : Sig) :=
  | neg : formula S -> formula S
  | disjunc : formula S -> formula S -> formula S
  | equal (l : term S) (r : term S)
  | relation (r : rel) (args : vect (term S) (rel_ar r))
  | ext : nat -> formula S -> formula S.

Arguments neg {S} _.
Arguments disjunc {S} _ _.
Arguments equal {S} _ _.
Arguments relation {S} _ _.
Arguments ext {S} _ _.

Fixpoint nary_f_type T n :=
  match n with
  | O => T
  | S n' => T -> (nary_f_type T n')
  end.

Fixpoint nary_r_type T n : Type :=
  match n with
  | O => Prop
  | S n' => T -> (nary_r_type T n')
  end.

Class Structure (S : Sig) := {
  universe : Type;
  itp_f (f : func) : nary_f_type universe (func_ar f);
  itp_r (r : rel) : nary_r_type universe (rel_ar r);
}.

Class Interpretation (S : Sig) := {
  structure : Structure S;
  asgn : nat -> universe
}.

Definition app_nary_func {T} {n} (f : nary_f_type T n)
                               (args : vect T n) : T.
  induction args.
  - unfold nary_f_type in f. apply f.
  - unfold nary_f_type in f. apply f in t.
    fold nary_f_type in t. apply IHargs. apply t.
  Defined.

Definition app_nary_rel {T} {n} (r : nary_r_type T n)
                               (args : vect T n) : Prop.
  induction args.
  - unfold nary_r_type in r. apply r.
  - unfold nary_r_type in r. apply r in t.
    fold nary_r_type in r. apply IHargs. apply t.
  Defined.

Inductive Forall {A} (P: A -> Type): forall {n} (v: vect A n), Type :=
  | Forall_nil: Forall P nil
  | Forall_cons {n} x (v: vect A n): P x -> Forall P v -> Forall P (cons x v).

Inductive Forall' {A} (P: A -> Prop): forall {n} (v: vect A n), Prop :=
  | Forall_nil': Forall' P nil
  | Forall_cons' {n} x (v: vect A n): P x -> Forall' P v -> Forall' P (cons x v).

Fixpoint strong_term_rect (S : Sig) (P : term S -> Type)
  (HV : forall x, P (var x))
  (HF : forall f args, Forall P args -> P (app f args))
  (t : term S) : P t :=
    match t with
    | var i => HV i
    | app f args => 
        let H :=
          (fix fold {n} (v : vect (term S) n) :
            Forall P v :=
            match v with
            | nil => Forall_nil _
            | cons x v' => Forall_cons _ _ _
                           (strong_term_rect S P HV HF x)
                           (fold v')
            end
          ) _ args in
        HF _ _ H
    end.

Fixpoint strong_term_ind (S : Sig) (P : term S -> Prop)
  (HV : forall x, P (var x))
  (HF : forall f args, Forall' P args -> P (app f args))
  (t : term S) : P t :=
    match t with
    | var i => HV i
    | app f args => 
        let H :=
          (fix fold {n} (v : vect (term S) n) :
            Forall' P v :=
            match v with
            | nil => Forall_nil' _
            | cons x v' => Forall_cons' _ _ _
                           (strong_term_ind S P HV HF x)
                           (fold v')
            end
          ) _ args in
        HF _ _ H
    end.

Inductive In {A} (x : A) : forall {n} (v : vect A n), Type :=
  | In_hd {m} (v : vect A m) : In x (cons x v)
  | In_tl {m} (v : vect A m) (H : In x v) (y : A) : In x (cons y v).

Lemma In_nil : forall {A} (x : A) (T : Type), In x nil -> T.
Proof.
  intros. inversion X.
Defined.

(*Lemma In_cons : forall {A} {n} (t : A) (P : A -> Type) (v : vect A n),
                (forall x, In x v -> P x) -> (P t) ->
                (forall x, In x (cons x v) -> P x).
Proof.
  intros. *)

Fixpoint map {T U : Type} {n : nat} (f : T -> U)
             (v : vect T n) : vect U n :=
  match v with
  | nil => nil
  | cons x v' => cons (f x) (map f v')
  end.

Definition eval_term (S : Sig) (itp : Interpretation S)
                     (t : term S) : @universe S (@structure S itp).
Proof.
  revert t.
  eapply strong_term_rect.
  - apply asgn.
  - intros. eapply app_nary_func.
    + apply (itp_f f).
    + induction args.
      * apply nil.
      * apply cons.
        --inversion X. auto.
        --apply IHargs. inversion X. subst.
          apply inj_pair2_eq_dec in H2. subst. auto.
          apply eq_nat_dec. 
Defined.

Instance Update   (S : Sig) (itp : Interpretation S)
                  (a : @universe S (@structure S itp)) 
                  (x : nat)  :
                  Interpretation S := {
    structure := @structure S itp;
    asgn := fun i => if (Nat.eqb x i) then a else @asgn S itp i;
  }.

Definition eval_formula (S : Sig) (itp : Interpretation S)
                        (f : formula S) : Prop.
Proof.
  revert itp.
  induction f; intros.
  - apply (~ (IHf itp)).
  - apply (IHf1 itp \/ IHf2 itp).
  - apply (eval_term _ _ l = eval_term _ _ r).
  - apply (app_nary_rel (itp_r r) (map (eval_term _ _) args)).
  - apply (exists (t : universe), IHf (Update S itp t n)).
Defined.

Inductive list (A : Type) :=
  | nil_l
  | cons_l : A -> list A -> list A.

Arguments nil_l {A}.
Arguments cons_l {A} _ _.

Inductive In_l {A} (x : A) : forall (v : list A), Prop :=
  | In_l_hd (l : list A) : In_l x (cons_l x l)
  | In_l_tl (l : list A) (H : In_l x l) (y : A) : In_l x (cons_l y l).

Definition subst_t (S : Sig) (t s : term S) (i : nat) : term S.
Proof.
  eapply strong_term_rect.
  - intros.
    apply (if (Nat.eqb x i) then s else t).
  - intros. apply (app f). induction args.
    + apply nil.
    + apply cons.
      * clear t s IHargs. inversion X. subst. apply X0.
      * apply IHargs. inversion X. subst.
        apply inj_pair2_eq_dec in H2. subst. auto.
        apply eq_nat_dec. 
  - apply t.
Defined.

Definition subst_f (S : Sig) (t : term S) (x : nat) (f : formula S) : formula S.
Proof.
  induction f.
  - apply (neg IHf).
  - apply (disjunc IHf1 IHf2).
  - apply (equal (subst_t S l t x) (subst_t S r t x)).
  - apply (relation r (map (fun s => subst_t S s t x) args)).
  - apply (ext n IHf).
Defined.

Inductive free_t {S : Sig} (x : nat) : term S -> Prop :=
  | free_var (i : nat) (H : i <> x) : free_t x (var i)
  | free_app f args `(Forall' (fun t => free_t x t) args) :
             free_t x (app f args).

Inductive free_f {S : Sig} (x : nat) : formula S -> Prop :=
  | free_neg f `(free_f x f) : free_f x (neg f)
  | free_disj f g `(free_f x f) `(free_f x g) :
              free_f x (disjunc f g)
  | free_equal t s `(free_t x t) `(free_t x s) :
               free_f x (equal t s)
  | free_rel r args `(Forall' (fun t => free_t x t) args) :
             free_f x (relation r args)
  | free_ext i f `(free_f x f) `(i <> x) :
              free_f x (ext i f).

Inductive free_f_l {S : Sig} (x : nat) : list (formula S) -> Prop :=
  | free_nil : free_f_l x nil_l
  | free_cons f l `(free_f x f) `(free_f_l x l) : free_f_l x (cons_l f l).

Inductive derivable (S : Sig) :
  list (formula S) -> Prop :=
  | ant (gamma gamma' : list (formula S))
        (H : forall f, In_l f gamma -> In_l f gamma')
        (I : derivable S  gamma)
        : derivable S  gamma'
  | assm (gamma : list (formula S)) (f : formula S)
         (H : In_l f gamma) : derivable S  (cons_l f gamma)
  | pc gamma f g
       `(derivable S  (cons_l f (cons_l g gamma)))
       `(derivable S  (cons_l f (cons_l (neg g) gamma))) :
       derivable S  (cons_l f gamma)
  | ctr gamma f g
        `(derivable S  (cons_l f (cons_l (neg g) gamma)))
        `(derivable S  (cons_l (neg f) (cons_l (neg g) gamma))) :
        derivable S  (cons_l g gamma)
  | disj_a gamma f g h
           `(derivable S  (cons_l f (cons_l h gamma)))
           `(derivable S  (cons_l f (cons_l g gamma))) :
           derivable S  (cons_l f (cons_l (disjunc g h) gamma))
  | disj_s1 gamma f g
            `(derivable S  (cons_l f gamma)) :
            `(derivable S  (cons_l (disjunc f g) gamma))
  | disj_s2 gamma f g
            `(derivable S  (cons_l f gamma)) :
            `(derivable S  (cons_l (disjunc g f) gamma))
  | refl t : derivable S (cons_l (equal t t) nil_l)
  | exist_s gamma f t x
            `(derivable S (cons_l (subst_f S t x f) gamma)) :
            `(derivable S (cons_l (ext x f) gamma))
  | sub gamma t t' x f
        `(derivable S (cons_l (subst_f S t x f) gamma)) :
        `(derivable S (cons_l (subst_f S t' x f) (cons_l (equal t t') gamma)))
  | exist_a gamma x y f g
            `(derivable S (cons_l f (cons_l (subst_f S (var y) x g) gamma)))
            `(~(free_f_l y gamma))
            `(~(free_f x f))
            `(~(free_f x (ext x g))) :
            `(derivable S (cons_l f (cons_l (ext x g) gamma))).
