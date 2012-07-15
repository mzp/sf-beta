SfLib\_J: Software Foundations ライブラリ
=========================================

Here we collect together several useful definitions and theoremsfrom
Basics.v, List.v, Poly.v, Ind.v, and Logic.v that are notalready in the
Coq standard library. From now on we
can\ ``Import``\ or\ ``Export``\ this file, instead of cluttering our
environment withall the examples and false starts in those files.

ここでは、Basics.v, List.v, Poly.v, Ind.v, and
Logic.vの中から、使い勝手のよい定義や定理でCoqのスタンダードライブラリに含まれていないものをを集めてみました。これ以降、環境を色々な証明で散らかす代わりに、このライブラリファイルを\ ``Import``\ 、\ ``Export``\ するだけで済むようになります。

Coq スタンダードライブラリから
------------------------------

::

    Require Omega.

Basics.vから
------------

::

    Definition admit {T: Type} : T.  Admitted.

    Require String. Open Scope string_scope.

    Ltac move_to_top x :=
      match reverse goal with
      | H : _ |- _ => try move x after H
      end.

    Tactic Notation "assert_eq" ident(x) constr(v) :=
      let H := fresh in
      assert (x = v) as H by reflexivity;
      clear H.

    Tactic Notation "Case_aux" ident(x) constr(name) :=
      first [
        set (x := name); move_to_top x
      | assert_eq x name; move_to_top x
      | fail 1 "because we are working on a different case" ].

    Tactic Notation "Case" constr(name) := Case_aux Case name.
    Tactic Notation "SCase" constr(name) := Case_aux SCase name.
    Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
    Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
    Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
    Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
    Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
    Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

    Fixpoint ble_nat (n m : nat) : bool :=
      match n with
      | O => true
      | S n' =>
          match m with
          | O => false
          | S m' => ble_nat n' m'
          end
      end.

    Theorem andb_true_elim1 : forall b c,
      andb b c = true -> b = true.
    Proof.
      intros b c H.
      destruct b.
      Case "b = true".
        reflexivity.
      Case "b = false".
        rewrite <- H. reflexivity.  Qed.

    Theorem andb_true_elim2 : forall b c,
      andb b c = true -> c = true.
    Proof.


    Notation "[ ]" := nil.
    Notation "[ x , .. , y ]" := (cons x .. (cons y []) ..).
    Notation "x ++ y" := (app x y) 
                         (at level 60, right associativity).

Props.vから
-----------

::

    Inductive ev : nat -> Prop :=
      | ev_0 : ev O
      | ev_SS : forall n:nat, ev n -> ev (S (S n)).

Logic.vから
-----------

::

    Theorem andb_true : forall b c,
      andb b c = true -> b = true /\ c = true.
    Proof.
      intros b c H.
      destruct b.
        destruct c.
          apply conj. reflexivity. reflexivity.
          inversion H.
        inversion H.  Qed.

    Theorem not_eq_beq_false : forall n n' : nat,
         n <> n' ->
         beq_nat n n' = false.
    Proof. 

    Inductive id : Type := 
      Id : nat -> id.

    Definition beq_id id1 id2 :=
      match (id1, id2) with
        (Id n1, Id n2) => beq_nat n1 n2
      end.

    Theorem beq_id_refl : forall i,
      true = beq_id i i.
    Proof.
      intros. destruct i.
      apply beq_nat_refl.  Qed.

    Theorem beq_id_eq : forall i1 i2,
      true = beq_id i1 i2 -> i1 = i2.
    Proof.
      intros i1 i2 H.
      destruct i1. destruct i2.
      apply beq_nat_eq in H. subst.
      reflexivity.  Qed.

    Theorem beq_id_false_not_eq : forall i1 i2,
      beq_id i1 i2 = false -> i1 <> i2.
    Proof.
      intros i1 i2 H.
      destruct i1. destruct i2.
      apply beq_nat_false in H.
      intros C. apply H. inversion C. reflexivity.  Qed.

    Theorem not_eq_beq_id_false : forall i1 i2,
      i1 <> i2 -> beq_id i1 i2 = false.
    Proof.
      intros i1 i2 H.
      destruct i1. destruct i2.
      assert (n <> n0).
        intros C. subst. apply H. reflexivity.
      apply not_eq_beq_false. assumption.  Qed.

    Theorem beq_id_sym: forall i1 i2,
      beq_id i1 i2 = beq_id i2 i1.
    Proof.
      intros i1 i2. destruct i1. destruct i2. apply beq_nat_sym. Qed.


    Definition partial_map (A:Type) := id -> option A.

    Definition empty {A:Type} : partial_map A := (fun _ => None). 

    Definition extend {A:Type} (Gamma : partial_map A) (x:id) (T : A) :=
      fun x' => if beq_id x x' then Some T else Gamma x'.

    Lemma extend_eq : forall A (ctxt: partial_map A) x T,
      (extend ctxt x T) x = Some T.
    Proof.
      intros. unfold extend. rewrite <- beq_id_refl. auto.
    Qed.

    Lemma extend_neq : forall A (ctxt: partial_map A) x1 T x2,
      beq_id x2 x1 = false ->
      (extend ctxt x2 T) x1 = ctxt x1.
    Proof.
      intros. unfold extend. rewrite H. auto.
    Qed.

    Lemma extend_shadow : forall A (ctxt: partial_map A) t1 t2 x1 x2,
      extend (extend ctxt x2 t1) x2 t2 x1 = extend ctxt x2 t2 x1.
    Proof with auto.
      intros. unfold extend. destruct (beq_id x2 x1)...
    Qed.

使い勝手のいいタクティックをいくつか
------------------------------------

::

    Tactic Notation "solve_by_inversion_step" tactic(t) :=  
      match goal with  
      | H : _ |- _ => solve [ inversion H; subst; t ] 
      end
      || fail "because the goal is not solvable by inversion.".

    Tactic Notation "solve" "by" "inversion" "1" :=
      solve_by_inversion_step idtac.
    Tactic Notation "solve" "by" "inversion" "2" :=
      solve_by_inversion_step (solve by inversion 1).
    Tactic Notation "solve" "by" "inversion" "3" :=
      solve_by_inversion_step (solve by inversion 2).
    Tactic Notation "solve" "by" "inversion" :=
      solve by inversion 1.

